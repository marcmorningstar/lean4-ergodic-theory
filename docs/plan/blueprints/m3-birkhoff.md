# Blueprint M3 — pointwise (Birkhoff) ergodic theorem + `condExp ∘ measure-preserving`

Target file: `ErgodicTheory/Ergodic/Birkhoff.lean`
Layer `L1.2` (= `condExp_invariants_comp`, milestone M2) and `L1.3`
(= `tendsto_birkhoffAverage_ae` + ergodic corollary, milestone M3).

Everything here rests on the **maximal ergodic inequality** `M1`
(`ErgodicTheory.setIntegral_birkhoffSum_pos_nonneg`, in
`ErgodicTheory/Ergodic/MaximalErgodic.lean`, currently `sorry`) and on the Mathlib
`condExp` substrate. All Mathlib declaration names below were grepped on disk in the
pinned tree (`v4.30.0-rc2`); file paths are given so they can be re-checked.

The reference proof for L1.3 is **Walkden, MATH41112/61112 Ergodic Theory, Lecture 21**
(`personalpages.manchester.ac.uk/staff/charles.walkden/ergodic-theory/lecture21.pdf`),
Theorem 21.2 + Corollary 21.5 ("the conditional-expectation form"). This is the
classical maximal-inequality → Birkhoff derivation requested in the task. The
ergodic-case derivation (limit `= ∫ g`) follows Robertson's Manchester notes
(Theorem 14.0.1).

---

## 0. The three Lean statements (exactly as in the repo, fixed)

```lean
open MeasureTheory Filter Topology
namespace ErgodicTheory
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

-- (a)  M2 / L1.2
theorem condExp_invariants_comp
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : X → ℝ} (hg : Integrable g μ) :
    μ[g ∘ T | MeasurableSpace.invariants T] =ᵐ[μ]
      (μ[g | MeasurableSpace.invariants T]) ∘ T

-- (b)  M3 / L1.3
theorem tendsto_birkhoffAverage_ae
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop
      (𝓝 ((μ[g | MeasurableSpace.invariants T]) x))

-- (c)  ergodic corollary
theorem tendsto_birkhoffAverage_ae_integral
    [IsProbabilityMeasure μ] (hT : Ergodic T μ) {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ))
```

`MeasurableSpace.invariants T` and `invariants_le T : invariants T ≤ ‹MeasurableSpace X›`
are in `Mathlib/MeasureTheory/MeasurableSpace/Invariants.lean`. Abbreviate
`I := MeasurableSpace.invariants T`, `hI := MeasurableSpace.invariants_le T`.

---

## ⚠ Load-bearing measurability/finiteness caveat (READ FIRST)

`condExp m μ f` is **defined to be the zero function** unless `m ≤ m₀` *and*
`SigmaFinite (μ.trim hm)` hold (`condExp_of_not_le`, `condExp_of_not_sigmaFinite`,
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:123,125`). For
`m = I` we always have `hI : I ≤ m₀`, but **`SigmaFinite (μ.trim hI)` is NOT free** —
it is supplied by `instance isFiniteMeasure_trim`
(`Mathlib/MeasureTheory/Measure/Trim.lean:115`) only when `μ` is a finite measure.

Consequences, by statement:

- **(a)** has *no* finiteness hypothesis. It is nevertheless **true as stated**: if
  `SigmaFinite (μ.trim hI)` fails then *both* sides reduce to `0` (LHS by
  `condExp_of_not_sigmaFinite`; RHS is `0 ∘ T = 0`), and `0 =ᵐ 0`. So the proof must
  `by_cases hσ : SigmaFinite (μ.trim hI)` and dispatch the negative branch with
  `condExp_of_not_sigmaFinite` + `Function.comp`. The **mathematical content lives
  entirely in the `hσ` branch**, which in practice means a finite measure. *Risk:* do
  not forget the degenerate branch or the build fails to typecheck the `=ᵐ`.
- **(b)** likewise has no finiteness hypothesis but a genuine Birkhoff proof needs a
  probability/finite measure (the maximal-inequality argument, dominated convergence,
  and integrability of `E[g|I]` all use it; `birkhoffAverage` itself does not). The
  honest reading: **the real theorem needs `[IsFiniteMeasure μ]`** (equivalently
  `IsProbabilityMeasure`). Either (i) the proof works in the `SigmaFinite (μ.trim hI)`
  branch and the non-σ-finite branch is vacuous *only if the conclusion still holds* —
  but with no finiteness the conclusion is a real convergence claim that the maximal
  inequality does not give. **Recommendation / flag:** add `[IsFiniteMeasure μ]` to
  (b) when filling it (the MET only ever uses a probability measure), or prove it as a
  private lemma with `[IsFiniteMeasure μ]` and keep the public signature by noting M1
  itself (`setIntegral_birkhoffSum_pos_nonneg`) is only useful/true on a finite
  measure. **This is the single biggest discrepancy between the stated signature and
  the provable content; surface it before filling.**
- **(c)** already carries `[IsProbabilityMeasure μ]`, so `SigmaFinite (μ.trim hI)` is
  automatic and `condExp_bot`-style collapses apply.

Throughout the substantive proof assume `[IsFiniteMeasure μ]` (probability in (c)) so
that `SigmaFinite (μ.trim hI)` is an instance and every `condExp` lemma fires.

---

## 1. Auxiliary lemmas to build first (in dependency order)

These should be *private* lemmas in `Birkhoff.lean` (or a small `CondExpComp.lean`
per the module layout). Statements are written against `[IsFiniteMeasure μ]`.

### A1 — set-integral invariance under a measure-preserving map (the workhorse for (a))

```lean
lemma setIntegral_comp_of_invariants
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ)
    {s : Set X} (hs : MeasurableSet s) (hsinv : T ⁻¹' s = s) :
    ∫ x in s, (g ∘ T) x ∂μ = ∫ x in s, g x ∂μ
```

Proof: `∫ x in s, g x ∂μ = ∫ x in s, g x ∂(Measure.map T μ)` by `hT.map_eq` rewritten
backwards; then `setIntegral_map hs hg.1.aestronglyMeasurable hT.aemeasurable` gives
`∫ y in s, g y ∂(map T μ) = ∫ x in T ⁻¹' s, g (T x) ∂μ`; rewrite `T ⁻¹' s = s` with
`hsinv`. NB: `setIntegral_map` wants `AEStronglyMeasurable g (map T μ)`; obtain it from
`hg.aestronglyMeasurable` and `hT.map_eq ▸`. **This does not need `T` injective/an
embedding** — the embedding-flavoured `MeasurePreserving.setIntegral_preimage_emb` is
the wrong tool here (false generality trap; do not use it).

- `setIntegral_map` : `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:540`.
- `MeasurePreserving.map_eq`, `.aemeasurable` :
  `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:48,59`.
- `Integrable.aestronglyMeasurable` : `Mathlib/MeasureTheory/Function/L1Space/*`.

### A2 — `g ∘ T` integrable

```lean
lemma integrable_comp (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) :
    Integrable (g ∘ T) μ
```
= `hT.integrable_comp_of_integrable hg`.
`MeasurePreserving.integrable_comp_of_integrable` :
`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:387`.

### A3 — `E[g|I]` is a.e. `T`-invariant (a *consequence* of (a), used in (b))

```lean
lemma condExp_invariants_comp_self
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : X → ℝ} (hg : Integrable g μ) :
    (μ[g | MeasurableSpace.invariants T]) ∘ T =ᵐ[μ] μ[g | MeasurableSpace.invariants T]
```
Proof: combine (a) with `condExp(g∘T|I) =ᵐ condExp(g|I)`. The latter is *itself* an
application of the uniqueness lemma (A4 below with `f := g∘T`, comparing to
`condExp(g|I)`): for every `I`-measurable `s` (so `MeasurableSet s ∧ T⁻¹'s=s`),
`∫_s g∘T = ∫_s g = ∫_s condExp(g|I)` by A1 + `setIntegral_condExp`. Then
`(μ[g|I]) ∘ T =ᵐ μ[g∘T|I] =ᵐ μ[g|I]` (first step is (a).symm, second is this).

> **Subtle point on `T`-invariance:** the *clean* algebraic fact "an `I`-measurable
> function `φ` satisfies `φ ∘ T = φ`" is `comp_eq_of_measurable_invariants`
> (`Invariants.lean:`, the `comp_eq_of_measurable_invariants` decl) — but it requires
> `[MeasurableSingletonClass X]`, which a general probability space does **not** have.
> So do **not** route through it; get the `=ᵐ` version through (a) as above. This is a
> deliberate a.e.-vs-everywhere choice and a classic trap.

### A4 — repackage the uniqueness lemma against `I` (convenience)

This is just `ae_eq_condExp_of_forall_setIntegral_eq` specialised to `m = I`. State
inline rather than as a lemma; signature:
```lean
ae_eq_condExp_of_forall_setIntegral_eq (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
  {f h : X → ℝ} (hf : Integrable f μ)
  (h_int : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn h s μ)
  (h_eq  : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, h x ∂μ = ∫ x in s, f x ∂μ)
  (hhm   : AEStronglyMeasurable[m] h μ) : h =ᵐ[μ] μ[f | m]
```
`ae_eq_condExp_of_forall_setIntegral_eq` :
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:245`. The membership
predicate `MeasurableSet[I] s` unfolds via `measurableSet_invariants`
(`Invariants.lean`) to `MeasurableSet s ∧ T⁻¹'s = s` — exactly what A1 consumes.

### A5 — maximal inequality, the "`> α` over an invariant set" repackaging (Walkden Cor 21.5)

The repo's M1 is the **Garsia form**
```lean
setIntegral_birkhoffSum_pos_nonneg (hT) (hf : Integrable f μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum T f (n + 1) x}, f x ∂μ
```
(`ErgodicTheory/Ergodic/MaximalErgodic.lean:28`). Build the Walkden corollary on top:

```lean
lemma setIntegral_sup_birkhoffAverage_gt_nonneg
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Integrable g μ) (α : ℝ)
    {A : Set X} (hA : MeasurableSet A) (hAinv : T ⁻¹' A = A) :
    0 ≤ ∫ x in {x ∈ A | ∃ n : ℕ, α < birkhoffAverage ℝ T g (n+1) x}, (g x - α) ∂μ
```

Proof outline:
- Set `f := (g - α) restricted via indicator-on-`A``, or work with the m.p. system
  `T` restricted to `A` (Walkden restricts `T : A → A`). The cleaner Lean route is to
  apply M1 to `f := (A.indicator (g - fun _ => α))`: it is integrable
  (`hg.sub (integrable_const α)` then `.indicator hA`), and on the invariant set `A`,
  `0 < birkhoffSum T f (n+1) x ↔ α < birkhoffAverage ℝ T g (n+1) x` for `x ∈ A`
  (because for `x ∈ A`, `T^[k] x ∈ A` by `hAinv`, so the indicator is transparent and
  `birkhoffSum T (g - α) (n+1) x = birkhoffSum T g (n+1) x - (n+1)·α =
  (n+1)·(birkhoffAverage ℝ T g (n+1) x - α)`).
- `0 < birkhoffSum T f (n+1) x ↔ α < birkhoffAverage ℝ T g (n+1) x` then
  `{x | ∃ n, 0 < birkhoffSum T f (n+1) x} =ᵐ {x ∈ A | ∃ n, α < birkhoffAverage …}`.
- Conclude with M1 and `setIntegral_congr` over the indicator.

Key Birkhoff-sum algebra:
- `birkhoffSum_sub` : `Mathlib/Dynamics/BirkhoffSum/Basic.lean:91`
  (`birkhoffSum f g n - birkhoffSum f g' n`).
- `birkhoffSum (fun _ => α)` over `n` is `n • α`: derive from `birkhoffSum` def
  (`= ∑ k ∈ range n, α`) via `Finset.sum_const`, `birkhoffSum` :
  `Mathlib/Dynamics/BirkhoffSum/Basic.lean:31`.
- `birkhoffAverage R f g n x = (n:R)⁻¹ • birkhoffSum f g n x` : def at
  `Mathlib/Dynamics/BirkhoffSum/Average.lean:46`.
- `birkhoffSum_of_comp_eq` (`φ ∘ f = φ ⇒ birkhoffSum f φ n = n • φ`) :
  `Mathlib/Dynamics/BirkhoffSum/Basic.lean:74` — handy if needed for the indicator
  transparency on `A`.

> **Trap:** in M1 the set is `{∃ n, 0 < birkhoffSum (n+1)}` (`n+1` so `N ≥ 1`); match
> the `(n+1)` exactly and never use `birkhoffSum … 0 = 0` (`birkhoffSum_zero`,
> `Basic.lean:33`) as a "positive" term.

---

## 2. Proof of (a) `condExp_invariants_comp`  — dependency-ordered

Goal: `μ[g ∘ T | I] =ᵐ[μ] (μ[g | I]) ∘ T`.

Strategy (mirrors `ContinuousLinearMap.comp_condExp_comm`,
`ConditionalExpectation/Basic.lean:351`, which is the structural template — a
`ae_eq_condExp_of_forall_setIntegral_eq` proof with three side goals).

Step a0. `by_cases hσ : SigmaFinite (μ.trim hI)`.
  - **`¬hσ` branch:** `condExp_of_not_sigmaFinite hI hσ` rewrites the LHS to `0`; the
    RHS `(μ[g|I]) ∘ T = (0) ∘ T = 0` by the same lemma + `Function.comp`. Close with
    `EventuallyEq.refl`/`rfl`. (`condExp_of_not_sigmaFinite` :
    `ConditionalExpectation/Basic.lean:125`.)
  - **`hσ` branch:** continue (this is where `[IsFiniteMeasure μ]` makes `hσ` an
    instance; if `[IsFiniteMeasure μ]` is in scope, skip the `by_cases` and let
    `isFiniteMeasure_trim` provide it).

We prove the equivalent goal `(μ[g | I]) ∘ T =ᵐ[μ] μ[g ∘ T | I]` then `.symm`. Apply
the uniqueness lemma A4 with `m := I`, `f := g ∘ T`, `h := (μ[g | I]) ∘ T`:

Step a1 (`hf`). `Integrable (g ∘ T) μ` = A2.

Step a2 (`h_int`, integrability of `h` on finite-measure `I`-sets). `(μ[g|I]) ∘ T` is
integrable on `μ` (whole space): `IntegrableOn` then follows by `.restrict`.
`Integrable ((μ[g|I]) ∘ T) μ` from A2 applied to `g := μ[g|I]` (which is integrable by
`integrable_condExp`, `Basic.lean:214`) — i.e. `hT.integrable_comp_of_integrable
integrable_condExp`.

Step a3 (`h_eq`, the set-integral identity — the heart). For `I`-measurable `s`
(unfold to `hs.1 : MeasurableSet s`, `hs.2 : T⁻¹'s = s` via `measurableSet_invariants`)
with `μ s < ∞`:
```
∫ x in s, ((μ[g|I]) ∘ T) x ∂μ
  = ∫ x in s, (μ[g|I]) x ∂μ          -- A1 with `g := μ[g|I]`, invariance hs.2
  = ∫ x in s, g x ∂μ                 -- setIntegral_condExp hI hg hs
  = ∫ x in s, (g ∘ T) x ∂μ           -- A1 with `g := g`, invariance hs.2  (this is f)
```
i.e. `∫_s h = ∫_s f`. The middle equality is
`setIntegral_condExp hI hg hs` (`Basic.lean:223`); note `setIntegral_condExp` wants
`MeasurableSet[I] s` which is exactly `hs`. The first and third equalities are A1.

Step a4 (`hhm`, `I`-strong-measurability of `h = (μ[g|I]) ∘ T`). This is the trickiest
measurability side-goal. `μ[g|I]` is `StronglyMeasurable[I] (μ[g|I])`
(`stronglyMeasurable_condExp`, `Basic.lean:181`). We need `(μ[g|I]) ∘ T` to be
`AEStronglyMeasurable[I] _ μ`. Use that `T` is `(I,I)`-measurable:
`MeasurableSpace.measurable_invariants_of_semiconj` with `fa = fb = T`, `g = T`,
`Semiconj T T T` (= `T ∘ T = T ∘ T`, `Function.Semiconj.refl`-style/`fun _ => rfl`),
giving `@Measurable X X I I T`. Then `StronglyMeasurable[I] (μ[g|I])` composed with the
`(I,I)`-measurable `T` is `StronglyMeasurable[I] ((μ[g|I]) ∘ T)`:
`StronglyMeasurable.comp_measurable`. Take `.aestronglyMeasurable`.
- `measurable_invariants_of_semiconj` : `Invariants.lean` (verified present).
- `StronglyMeasurable.comp_measurable` : `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`.

Step a5. The uniqueness lemma yields `h =ᵐ[μ] μ[g ∘ T | I]`, i.e.
`(μ[g|I]) ∘ T =ᵐ μ[g∘T|I]`; take `.symm` for the stated direction.

> **Risk register for (a):**
> - a.4 is the measurability bookkeeping that most often fails; the
>   `measurable_invariants_of_semiconj` step to get `Measurable[I] T` is the linchpin
>   (do not try to prove `T` `(I,I)`-measurable by hand). Verify the `Semiconj T T T`
>   obligation is literally `rfl`.
> - The σ-finite `by_cases` (a0) is mandatory given the bare signature.
> - `setIntegral_condExp`'s `s`-argument must be the `I`-measurable witness, not the
>   ambient `MeasurableSet s`.

---

## 3. Proof of (b) `tendsto_birkhoffAverage_ae`  — dependency-ordered

Assume `[IsFiniteMeasure μ]` (see §0 caveat; recommend adding it to the signature).
Write `Aₙ x := birkhoffAverage ℝ T g n x = (n:ℝ)⁻¹ • birkhoffSum T g n x`,
`L := μ[g | I]`. Reference: Walkden Lecture 21, proof of Thm 21.2.

The skeleton produces `limsup Aₙ ≤ L` a.e. and `L ≤ liminf Aₙ` a.e., then sandwiches.

Step b0 — `limsup`/`liminf` are `T`-invariant a.e. From
`(n+1)·A_{n+1}(x) = n·Aₙ(T x) + g(x)` (the cocycle recursion; in Lean derive from
`birkhoffSum_succ'`, `Basic.lean:51`: `birkhoffSum f g (n+1) x =
birkhoffSum f g n (f x) + g x`), divide by `n+1` and pass to `limsup`/`liminf`:
`limsup Aₙ (T x) = limsup Aₙ x` and same for `liminf`, for **every** `x` where the
`g(Tⁿx)/n → 0` tail vanishes — which is a.e. by Borel–Cantelli (Walkden's
`|f(Tᴺx)|/N → 0` a.e. argument; Mathlib `measure_setOf_frequently_eq_zero` /
`ae_tendsto` from summability of `∑ μ{|g∘Tᴺ| ≥ Nε}` using `hT`-invariance of measure).
Define `f⁺ := limsup Aₙ`, `f₋ := liminf Aₙ`; these are `I`-measurable (a.e.) limits.
- `birkhoffSum_succ'` : `Mathlib/Dynamics/BirkhoffSum/Basic.lean:51`.
- limsup/liminf push-forward: `Filter.limsup`, `Filter.liminf` API in
  `Mathlib/Order/LiminfLimsup.lean` + `Mathlib/Topology/Order/LiminfLimsup.lean`.

Step b1 — the core sandwich (`limsup Aₙ ≤ L` a.e.). Fix rationals `α > β`; following
Walkden define `E_{α,β} := {x | f⁺ x < β?}` — but in the *conditional-expectation*
form we instead compare to `L = E[g|I]` directly. The cleanest formal route (Walkden
final paragraph) is the **two-sided maximal-set argument**:

  For ε > 0 and the invariant set `A := {x | L x ≤ c}` (`c` rational, `A` is
  `I`-measurable since `L` is `I`-measurable, hence `T⁻¹'A = A` a.e.), apply A5 to
  `g - L - ε` on `A`... *however* `g - L - ε` is not of the form needed unless we know
  `∫_A (g - L) = 0`, which is exactly `setIntegral_condExp` (`∫_A L = ∫_A g`).

  Concretely: define `B := {x | ∃ n, α < A_{n+1} x}` (the maximal set, Walkden `B_α`).
  Intersect with an invariant `A`. A5 gives `0 ≤ ∫_{B ∩ A} (g - α)`. Take
  `A := E_{α,β} := {x | f₋ x < β ∧ β < f⁺ x?}`... For the **conditional** target the
  decisive lemma is Walkden Cor 21.5 used twice:
  - apply A5 with `α` and invariant set `A` to get `α·μ(B∩A) ≤ ∫_{B∩A} g`;
  - on the invariant set `E := {f⁺ > L + ε}` (which has `E ⊆ B_{L+ε}` because
    `sup Aₙ ≥ limsup Aₙ = f⁺ > L + ε`), the maximal inequality applied "fibrewise over
    `I`" gives `∫_E (g - L - ε) ≥ 0`, while `∫_E (g - L) = 0` by `setIntegral_condExp`
    (since `E` is `I`-measurable). Hence `-ε·μ(E) ≥ 0`, forcing `μ(E) = 0`. Let ε ↓ 0
    over a countable sequence ⇒ `f⁺ ≤ L` a.e.

  The "fibrewise" maximal inequality over `I` is the genuinely delicate step: it is A5
  **applied with `g` replaced by `g - L`** and `α := ε`, restricted to the invariant
  set `E`. Because `L` is `I`-measurable, `L ∘ T = L` a.e. (A3!), so the Birkhoff sums
  of `g - L` satisfy `birkhoffAverage T (g-L) n = birkhoffAverage T g n - L` a.e.
  (using `birkhoffAverage_of_comp_eq` / `birkhoffSum_of_comp_eq` for the `L` part:
  `birkhoffSum T L n x = n • L x` when `L ∘ T = L`). Thus
  `{∃ n, ε < A_{n+1}(g-L)} = {∃ n, L + ε < A_{n+1}(g)} ⊇ {f⁺ > L + ε} = E` a.e., and A5
  yields `0 ≤ ∫_E (g - L - ε) = ∫_E (g-L) - ε μ(E) = -ε μ(E)`. ⇒ `μ(E)=0`.

  - `birkhoffSum_of_comp_eq` (`φ∘f = φ ⇒ birkhoffSum f φ n = n • φ`) :
    `Mathlib/Dynamics/BirkhoffSum/Basic.lean:74`.
  - `birkhoffAverage_of_comp_eq` : `Mathlib/Dynamics/BirkhoffSum/Average.lean:87`.
  - A3 supplies `L ∘ T =ᵐ L`. **This is exactly where (a) is consumed.**
  - `setIntegral_condExp hI hg hE.1` gives `∫_E L = ∫_E g`, i.e. `∫_E (g-L)=0`.

Step b2 — the mirror bound (`L ≤ f₋` a.e.). Repeat b1 with `-g` (so `L` becomes
`-L = μ[-g|I]` by `condExp_neg`, `Basic.lean:321`) and use
`liminf Aₙ = - limsup (-A)ₙ`. Yields `f₋ ≥ L` a.e.

Step b3 — sandwich to a genuine limit. On the a.e. set where `f₋ ≥ L ≥ f⁺` and
`f⁺ ≥ f₋` (the latter always, `liminf ≤ limsup`), conclude `f₋ = f⁺ = L`, hence
`Tendsto Aₙ atTop (𝓝 (L x))` by `tendsto_of_le_liminf_of_limsup_le`
(`Mathlib/Topology/Order/LiminfLimsup.lean:306`) with
`hinf : L x ≤ liminf Aₙ`, `hsup : limsup Aₙ ≤ L x`. The boundedness side-goals
(`IsBoundedUnder (· ≤ ·)` / `(· ≥ ·)`) hold because `Aₙ x` is a real sequence with
finite limsup/liminf established a.e. (provide `BddAbove`/`BddBelow` of the eventual
range from `f⁺, f₋` finite a.e. — finiteness from `g, L ∈ L¹` and Walkden's Fatou
argument that `f⁺ ∈ L¹`, using `Integrable` of `|Aₙ|` bounded by `(1/n)Σ|g∘Tʲ|`).

> **Risk register for (b):**
> - **a.e. vs everywhere everywhere.** Every equality (`L∘T = L`, the maximal-set
>   equality, the cocycle recursion's tail) is only a.e.; intersect the (countably
>   many, indexed by ε ∈ {1/k}) full-measure sets with `ae_all_iff` /
>   `MeasureTheory.ae_all_iff` and `measure_iUnion_null`. Keep all `EventuallyEq`
>   manipulations under `filter_upwards`.
> - The **`{f⁺ > L + ε} ⊆ B_{ε}(g-L)`** inclusion needs `sup Aₙ ≥ limsup Aₙ` (the sup
>   over `N ≥ 1` dominates the limsup) — formalize via `le_limsup`-style or directly:
>   if `limsup Aₙ x > L x + ε` then `∃ n, A_{n+1} x > L x + ε` (a value exceeding a
>   number `< limsup` exists frequently). Use `Filter.frequently_lt_of_lt_limsup` /
>   `Filter.eventually_lt_of_limsup_lt` mirror. Get the `∃ n` from frequently.
> - **Integrability of `f⁺`/finiteness of limsup** (Walkden step (ii)) via Fatou:
>   `MeasureTheory.lintegral_liminf_le` / `Integrable` bound
>   `|Aₙ| ≤ birkhoffAverage ℝ T |g| n`; then `f⁺` finite a.e.
> - The maximal inequality M1 itself is currently `sorry`; (b) is *blocked on M1*.
>   Mark `sorry -- BLOCKED: M1 (setIntegral_birkhoffSum_pos_nonneg)` until M1 lands.

---

## 4. Proof of (c) ergodic corollary

`[IsProbabilityMeasure μ]` (so σ-finiteness automatic), `hT : Ergodic T μ`.

Step c1. From (b) (instantiated at `hT.toMeasurePreserving`), a.e.
`Aₙ x → (μ[g|I]) x`.

Step c2. Show `μ[g|I] =ᵐ[μ] fun _ => ∫ y, g y ∂μ`. Two routes:
  - **Route via ergodicity ⇒ `I` trivial:** Ergodicity means every `I`-measurable
    set has measure 0 or 1 (`PreErgodic.ae_empty_or_univ` /
    `Ergodic.ae_empty_or_univ`; `Mathlib/Dynamics/Ergodic/Ergodic.lean`). An
    `I`-measurable integrable function with that property is a.e. constant equal to its
    integral. Cleanest: `μ[g|I]` is `I`-strongly-measurable and `T`-a.e.-invariant
    (A3), so by `Ergodic.ae_eq_const_of_ae_eq_comp_ae`
    (`Mathlib/Dynamics/Ergodic/Function.lean`; needs `AEStronglyMeasurable (μ[g|I]) μ`
    — have it) there is `c` with `μ[g|I] =ᵐ c`. Identify `c` by integrating:
    `∫ μ[g|I] = ∫ g` (`integral_condExp`, `Basic.lean:228`) and `∫ (fun _ => c) = c`
    (probability measure), so `c = ∫ g`.
  - `Ergodic.ae_eq_const_of_ae_eq_comp_ae` signature (api-notes.md:43): needs
    `AEStronglyMeasurable g' μ` and `g' ∘ T =ᵐ g'`; supply `g' := μ[g|I]`,
    measurability from `stronglyMeasurable_condExp.aestronglyMeasurable`, invariance
    from A3.

Step c3. Rewrite the limit in c1 with c2: `𝓝 ((μ[g|I]) x) = 𝓝 (∫ y, g y ∂μ)` a.e. via
`Filter.Tendsto.congr'` / `tendsto_congr'`. Done.

- `integral_condExp` : `Basic.lean:228`.
- `Ergodic` / `PreErgodic.ae_empty_or_univ` : `Mathlib/Dynamics/Ergodic/Ergodic.lean`.
- `Ergodic.ae_eq_const_of_ae_eq_comp_ae` : `Mathlib/Dynamics/Ergodic/Function.lean`.

> **Risk for (c):** the identification `c = ∫ g` uses `IsProbabilityMeasure` for
> `∫ (fun _ => c) ∂μ = c` (`integral_const`, `measure_univ`). With a non-probability
> finite measure it would be `c · μ univ`. The signature already pins
> `IsProbabilityMeasure`, so fine.

---

## 5. Trickiest steps & Lean-specific risk summary

1. **σ-finiteness of `μ.trim hI`** is not free; the bare signatures of (a),(b) hide a
   finiteness assumption. (a) is salvageable by the degenerate-branch trick; (b)
   should gain `[IsFiniteMeasure μ]`. — **Flag to the human before filling (b).**
2. **a.e. vs everywhere for `T`-invariance of `E[g|I]`**: must come from (a) (lemma
   A3), NOT from `comp_eq_of_measurable_invariants` (that needs
   `MeasurableSingletonClass`). This is *why* (a) is a prerequisite of (b).
3. **The set-integral identity in (a)** rests on `setIntegral_map` (non-embedding
   change of variables), not on `MeasurePreserving.setIntegral_preimage_emb` (which
   would wrongly demand `T` injective).
4. **`I`-measurability side goal in (a)** via `measurable_invariants_of_semiconj`
   (`Semiconj T T T = rfl`) + `StronglyMeasurable.comp_measurable`.
5. **Maximal-set ⊆ `B_α`** inclusion in (b) needs the `sup ≥ limsup` / "value
   exceeding a sub-limsup number occurs" frequently-lemma; mind the `(n+1)` indexing of
   M1's set.
6. **Integrability/Fatou bookkeeping** in (b): `f⁺ ∈ L¹` via Fatou
   (`lintegral_liminf_le`), needed so `limsup`/`liminf` are finite a.e. and the
   `tendsto_of_le_liminf_of_limsup_le` boundedness side-goals discharge.
7. **(b) is BLOCKED on M1** (`setIntegral_birkhoffSum_pos_nonneg` is itself `sorry`).
   The blueprint above is the derivation *given* M1.

## 6. Dependency graph (within this file)

```
M1: setIntegral_birkhoffSum_pos_nonneg            [sorry, MaximalErgodic.lean]
        │
        ▼
A5 (Walkden Cor 21.5 maximal-set form)  ──┐
                                          │
A1 setIntegral_comp_of_invariants ──┐     │
A2 integrable_comp ─────────────────┤     │
A4 = ae_eq_condExp_of_forall_setIntegral_eq (Mathlib)
        │                            │     │
        ▼                            │     │
(a) condExp_invariants_comp  ◀───────┘     │
        │                                  │
        ▼                                  │
A3 condExp_invariants_comp_self (L∘T=ᵐL)   │
        │                                  │
        └────────────┬─────────────────────┘
                     ▼
       (b) tendsto_birkhoffAverage_ae   [BLOCKED on M1]
                     │
                     ▼  (+ Ergodic.ae_eq_const_of_ae_eq_comp_ae, integral_condExp)
       (c) tendsto_birkhoffAverage_ae_integral
```
