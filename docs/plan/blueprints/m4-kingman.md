# Blueprint — M4: Kingman's subadditive ergodic theorem (`tendsto_kingman`)

**Target file:** `ErgodicTheory/Ergodic/Kingman.lean`
**Layer / milestone:** L2.6 / M4 (the analytic engine of the MET).
**Depends on (in-repo):** M3 pointwise Birkhoff (`tendsto_birkhoffAverage_ae`,
`tendsto_birkhoffAverage_ae_integral`) and, transitively, M1
(`setIntegral_birkhoffSum_pos_nonneg`) and M2 (`condExp_invariants_comp`), all in
`ErgodicTheory/Ergodic/{MaximalErgodic,Birkhoff}.lean`. **All three currently carry
`sorry`** — this blueprint assumes them as black boxes with the signatures already
stated in the repo.

All Mathlib declaration names below were grepped and read on disk in the pinned
tree (`/workspaces/lean4-oseledets/.lake/packages/mathlib`, toolchain
`v4.30.0-rc2`). Lines are cited where read.

---

## 1. The exact Lean statement (fixed; do NOT edit)

From `ErgodicTheory/Ergodic/Kingman.lean` as it stands:

```lean
open MeasureTheory Filter Topology

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

structure IsSubadditiveCocycle (T : X → X) (g : ℕ → X → ℝ) : Prop where
  apply_add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)

theorem tendsto_kingman
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, (G ∘ T =ᵐ[μ] G) ∧ Integrable G μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 (G x))) := by
  sorry
```

The ergodic corollary `tendsto_kingman_ergodic` (probability measure + `Ergodic T μ`
⇒ the limit is an a.e. *constant*) is a short rider; see §6.

### 1.1 What the statement commits us to (read these off carefully)

- **Conclusion is in `ℝ`, not `EReal`.** The hypothesis `hbdd` (`BddBelow` of the
  normalized integral sequence `aₙ₊₁/(n+1)` with `aₙ := ∫ gₙ dμ`) is exactly the
  Fekete boundedness proviso that keeps the Lyapunov limit finite. So we are in the
  finite regime and **never need `EReal`** for *this* statement. See §7 for the
  EReal decision and why we keep it out of M4.
- **Indexing.** `g : ℕ → X → ℝ` is defined at `0` too. Subadditivity at `m=n=0`
  gives `g 0 x ≤ 2 g 0 x`, i.e. `0 ≤ g 0 x`; nothing forces `g 0 = 0`. The limit
  object is `(n:ℝ)⁻¹ * g n x`. At `n = 0`, `(0:ℝ)⁻¹ = 0`, so the `n=0` term is `0`
  and irrelevant to `atTop` convergence. **All real content lives at `n ≥ 1`**; the
  cleanest internal reformulation is in terms of `g (n+1)` (matching `hbdd`, which is
  phrased with `n+1`). Translate once, at the top, between `(n:ℝ)⁻¹ * g n` and
  `g (n+1)/(n+1)`, and stay in the latter.
- **`G ∘ T =ᵐ[μ] G`**, i.e. genuine `T`-invariance a.e. (not just `=ᵐ` up to a
  Birkhoff cocycle). This is delivered by Step 2.
- **`Integrable G μ`.** Under `hbdd`, `G` is bounded below by `inf aₙ/n` (finite) and
  above by the Birkhoff limit of `g₁` (integrable), so `G ∈ L¹`. See §5.4.
- **`IsProbabilityMeasure μ` is NOT a hypothesis of `tendsto_kingman`.** It *is* on
  the ergodic corollary. Birkhoff (M3) as stated only needs `MeasurePreserving`.
  **Risk:** several measure-theoretic steps below (e.g. `tendsto_measure_iInter`,
  `integral_indicator`, finiteness of `∫`) want a *finite* measure. Decide early
  whether to (a) thread `[IsFiniteMeasure μ]` through the private lemmas — Furstenberg–
  Kesten always supplies a probability measure, so this costs nothing downstream — or
  (b) keep full generality. **Recommendation: prove the private lemmas under
  `[IsFiniteMeasure μ]`**, and if `tendsto_kingman` must hold for σ-finite `μ`, note
  it as a documented generalization (the MET only ever calls it with a probability
  measure). This is the single most important framing decision after the EReal one.

---

## 2. Recommended route: **Katznelson–Weiss**, not Steele

The task asks to blueprint both candidate proofs and recommend one.

### 2.1 Steele 1989 (route ii) — what it costs in Lean

Steele's proof (transcribed in `docs/research/digests/web-kingman-furstenberg-kesten.md`
§1.4, Steps 0–6) uses **only pointwise Birkhoff (M3)** plus a *greedy covering /
stopping-time partition* combinatorial core (Step 4). Its analytic dependency is
minimal and exactly matches what we will have built (M3). **But** its Step 4 is the
single most error-prone piece in the whole MET development: a greedy block-selection
on `Finset.range n`, three interval *types* (fit / forced-singleton-near-right-end /
bad-set-singleton), and the length lower bound
`(1/n) Σ_{type1} ℓᵢ ≥ 1 − (L−1)/n − (1/n) Σ_{k<n} 1_{B_L}(T^k x)`. Formalizing a
"partition of `range n` into consecutive blocks" + the greedy stopping rule + the
counting is genuine index-bookkeeping pain (the digest itself flags it: "expect this
to dominate the effort").

### 2.2 Katznelson–Weiss 1982 (route i) — what it costs in Lean

Katznelson–Weiss prove Kingman from a **maximal ergodic inequality + a truncation**,
*with no greedy partition*. We already plan to build the maximal ergodic inequality
(M1) as the gate to Birkhoff, so the heavy analytic input is *already on the table*.
The combinatorial core is replaced by a clean stopping-time/Markov argument that is
far friendlier to `omega`/`Finset` reasoning. The structure:

- Define `G₋ := liminf (gₙ/n)`, `G₊ := limsup (gₙ/n)`.
- Show both are `T`-invariant a.e. (Step 2; identical in both routes).
- The easy direction `∫ G₋ ≥ inf aₙ/n` (or its dual) is Fatou + Fekete.
- The **hard direction** `∫ G₊ ≤ inf aₙ/n` is the one place the routes differ:
  Katznelson–Weiss get it from a **truncation + maximal/stopping argument** rather
  than the greedy cover.
- Conclude `∫ (G₊ − G₋) ≤ 0` with `G₊ ≥ G₋` pointwise, hence `G₊ = G₋` a.e., hence
  the limit exists a.e.

### 2.3 Recommendation

**Use Katznelson–Weiss (route i).** Rationale, in order of weight:

1. **It reuses M1 (the maximal ergodic inequality) we are building anyway**, instead of
   demanding a bespoke greedy-partition combinatorial lemma that has *no* Mathlib
   analog and is the acknowledged worst index-bookkeeping risk in the project.
2. The "hard direction" reduces to a stopping-time set `Eₙ = {x : ∃ k ≤ n, g_k(x)/k ≤ G₊(x)+ε}`
   plus the maximal inequality, which is structurally close to the M1 statement
   `setIntegral_birkhoffSum_pos_nonneg` we already have — high reuse.
3. The squeeze `liminf = limsup` at the end is one Mathlib lemma
   (`tendsto_of_le_liminf_of_limsup_le`), shared by both routes.

**However**, the actual choice of *internal lemma to lean on* is constrained by what
M1 gives. Our M1 (`setIntegral_birkhoffSum_pos_nonneg`) is the *Hopf/Garsia* form. The
Katznelson–Weiss hard direction is classically run through a slightly different
"maximal function over the first `N` averages" statement. **Build the bridge lemma A4
(§4) to derive the stopping-time bound we need from M1.** If A4 turns out to need a
genuinely new maximal estimate (not derivable from M1 in a page), *fall back to
Steele Step 4* — that is the documented contingency.

The ordered steps below follow Katznelson–Weiss. Steele's Steps 0–2 (partition
inequality, reduction to ≤ 0, invariance) are reused verbatim as auxiliary lemmas A1,
A2 because they are useful no matter which hard-direction argument wins, so they are
listed first.

---

## 3. Dependency-ordered proof outline (Katznelson–Weiss)

Notation inside the proof: `a n := ∫ x, g n x ∂μ`; `α := ⨅ n, a (n+1)/(n+1)` (the
Fekete infimum, finite by `hbdd`); `G₋ x := liminf atTop (fun n => g (n+1) x / (n+1))`,
`G₊ x := limsup atTop (fun n => g (n+1) x / (n+1))`.

### Step 0 — index normalization (translate `(n:ℝ)⁻¹ * g n` ↔ `g (n+1)/(n+1)`)

- The two sequences `fun n => (n:ℝ)⁻¹ * g n x` and `fun n => g (n+1) x / (n+1)` have
  the same `atTop` behavior (the second is the first reindexed by `n ↦ n+1`, and the
  `n=0` term of the first is `0`). Convergence transfers by
  **`Filter.tendsto_add_atTop_iff_nat`** (`Mathlib/Order/Filter/AtTopBot/Basic.lean`)
  / `Filter.Tendsto.comp` with `tendsto_atTop_add_const`/`tendsto_add_atTop_nat`.
  *Verify the exact reindex lemma name when writing; candidate
  `Filter.tendsto_add_atTop_iff_nat` is used in Mathlib's own `Subadditive.lean`
  (line 74: `(tendsto_add_atTop_iff_nat 1).2 …`).*
- Also rewrite `(↑(n+1))⁻¹ * g (n+1) x = g (n+1) x / (n+1)` by `div_eq_inv_mul`
  / `mul_comm`. Trivial; keep it to one `simp only`.
- **Output:** it suffices to produce `G` with `∀ᵐ x, Tendsto (fun n => g (n+1) x/(n+1)) atTop (𝓝 (G x))`,
  plus invariance and integrability.

### Step 1 — Fekete on the integral sequence (`α` is finite, `aₙ` subadditive)

- `a` is a subadditive real sequence: from `hsub.apply_add_le m n x` integrate over `μ`
  and use **`∫ g n (T^[m] x) dμ = ∫ g n dμ`**. Concretely
  `a (m+n) ≤ a m + a n`.
  - The composition-integral fact: `(hT.iterate m).integral_comp …` —
    **`MeasurePreserving.integral_comp`** (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1123`)
    needs a `MeasurableEmbedding`, which `T^[m]` may not be. **Use instead
    `MeasureTheory.integral_map`** (`…/Bochner/Basic.lean:1089`): with
    `(hT.iterate m).map_eq` and `AEMeasurable (T^[m]) μ` (from
    `hT.iterate m |>.aemeasurable`), `∫ g n (T^[m] x) ∂μ = ∫ y, g n y ∂μ`. The
    `AEStronglyMeasurable (g n)` side-goal comes from `(hint n).aestronglyMeasurable`.
  - Integrate the inequality with **`integral_mono`**
    (`…/Bochner/Basic.lean:653`); side-goals: `Integrable (g (m+n)) μ` (= `hint _`) and
    `Integrable (fun x => g m x + g n (T^[m] x)) μ` (`Integrable.add` + the
    composition integrability `MeasurePreserving.integrable_comp`,
    `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:381`).
- Build `Subadditive a` (Mathlib's `Subadditive`, `Mathlib/Analysis/Subadditive.lean:34`:
  `∀ m n, u (m+n) ≤ u m + u n` — note **no shift by `T`**, exactly matching `a`).
- `hbdd` is `BddBelow (range fun n => a (n+1)/(n+1))`. Mathlib's
  **`Subadditive.tendsto_lim`** (`Mathlib/Analysis/Subadditive.lean:87`) wants
  `BddBelow (range fun n => a n / n)`; these differ only by the `n=0` point
  (`a 0 / 0 = 0`, since `(0:ℝ)⁻¹ = 0`). **NOTE: `BddBelow.insert` does NOT exist** in
  the pinned tree (grepped — only `Finite.bddBelow_range`,
  `Mathlib/Data/Fintype/Order.lean:222`, and `IsBoundedUnder.bddBelow_range`,
  `Mathlib/Order/Filter/IsBounded.lean:196`). Bridge the `n=0` point *by hand*:
  `range (fun n => a n/n) = insert (a 0/0) (range (fun n => a (n+1)/(n+1)))` (or
  `⊆ {0} ∪ shifted-range`), and `BddBelow` of a one-point-extended bounded-below set
  via `⟨min lb 0, …⟩` with `mem_lowerBounds` unfolded by `rcases`/`omega`. ~10 lines;
  do NOT cite a phantom lemma. Then `Tendsto (fun n => a n/n) atTop (𝓝 hSub.lim)` and
  `hSub.lim = ⨅ … = α`.
  - `Subadditive.lim_le_div` (`…/Subadditive.lean:47`) gives `hSub.lim ≤ a n / n` for
    `n ≠ 0`; this is the lower-bound clause `∀ n, α ≤ aₙ/n`.
- **Output:** finite real `α := hSub.lim`, with `α ≤ a (n+1)/(n+1)` for all `n` and
  `Tendsto (a (·+1)/(·+1)) atTop (𝓝 α)`.

### Step 2 — `T`-invariance of `G₋` and `G₊` (a.e.)

This is shared with Steele (digest Step 2) and is the same argument for both
liminf and limsup.

- **Pointwise sub-cocycle estimate.** From `hsub.apply_add_le 1 n x`:
  `g (n+1) x ≤ g 1 x + g n (T x)`. Divide by `n+1` and take `liminf`/`limsup` along
  `atTop`. Since `g 1 x/(n+1) → 0` and `(n)/(n+1) → 1`, one gets the pointwise
  inequalities
  - `G₋ x ≤ G₋ (T x)` and `G₊ x ≤ G₊ (T x)` for *every* `x` (no a.e. needed yet).
  - Tools: **`Filter.liminf_le_liminf`** / **`Filter.limsup_le_limsup`**
    (`Mathlib/Order/LiminfLimsup.lean:205` / `:198`) plus the limit-arithmetic that
    `g n (T x)/(n+1)` and `g (n) (T x)/n` have the same liminf/limsup (reindex /
    ratio `n/(n+1) → 1`). The cleanest packaging: show
    `liminf (fun n => g (n+1) x/(n+1)) = liminf (fun n => g n (Tx)/n)` is NOT needed;
    just bound `G₋ x ≤ liminf (fun n => (g 1 x + g n (Tx))/(n+1)) = G₋ (Tx)` using
    `liminf` monotonicity and that the additive/scaling perturbations vanish
    (`Filter.Tendsto`-based congruence; see Risk R3).
- **Measurability.** `G₋, G₊` are measurable via **`Measurable.liminf`** /
  **`Measurable.limsup`** (over `ℕ`, `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:1058,1065`),
  given each `fun x => g (n+1) x/(n+1)` is measurable. The per-`n` measurability comes
  from `(hint (n+1)).aestronglyMeasurable.measurable_mk`-style — but note `hint`
  gives `AEStronglyMeasurable`, not `Measurable`. *Either* assume/derive genuine
  `Measurable (g n)` (clean if `g` is built measurable, as Furstenberg–Kesten's
  `log‖φₙ‖` is), *or* use the `'` general-filter a.e. variants and work with
  `AEMeasurable` throughout. **Side-goal risk:** thread `Measurable (g n)` from a
  strengthened hypothesis or `.mk`-representatives. Needed for
  `ae_eq_of_subset_of_measure_ge` (level sets `NullMeasurableSet`) and for `Integrable`.
- **`g ≤ g∘T` pointwise ⟹ `g =ᵐ g∘T`** under measure preservation. For each rational
  `c`, the set `s_c := {x | c ≤ G₋ x}` satisfies `s_c ⊆ T⁻¹ s_c` (from `G₋ ≤ G₋∘T`)
  and `μ (T⁻¹ s_c) = μ s_c` by **`MeasurePreserving.measure_preimage`**
  (`Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:143`; needs
  `NullMeasurableSet s_c μ`, from measurability of `G₋`). Hence
  `s_c =ᵐ T⁻¹ s_c` by **`MeasureTheory.ae_eq_of_subset_of_measure_ge`**
  (`Mathlib/MeasureTheory/Measure/MeasureSpace.lean:333`; needs `μ (T⁻¹ s_c) ≠ ∞`,
  i.e. **`[IsFiniteMeasure μ]`** → `measure_ne_top`). Intersect over `c ∈ ℚ` using
  **`MeasureTheory.ae_all_iff`** (`Mathlib/MeasureTheory/OuterMeasure/AE.lean:95`,
  `ℚ` countable) to get `G₋ ∘ T =ᵐ[μ] G₋`. Same for `G₊`.
  - *Alternative packaging:* there may be a ready-made "monotone-under-T ⟹ invariant"
    lemma; grep `MeasurePreserving` + `ae_eq` (we already saw
    `aeconst_comp`/`aeconst_preimage` nearby at lines 169–177, but those are for
    *constancy*, not invariance, so build the rational-exhaustion argument by hand).
- **Output:** `G₋ ∘ T =ᵐ[μ] G₋`, `G₊ ∘ T =ᵐ[μ] G₊`, both measurable.

### Step 3 — easy direction: `α ≤ ∫ G₋` (Fatou)

- Pointwise `G₋ x = liminf (g(n+1)x/(n+1))`. By **Fatou for liminf**,
  `∫ G₋ ≤ liminf (∫ g(n+1)/(n+1)) = α` — *wrong direction for this step!* The clean
  direction here is the **lower bound** `∫ G₋ ≥ α`: each `g(n+1)/(n+1)` has integral
  `a(n+1)/(n+1) ≥ α` (Step 1), and `liminf` of nonneg... — actually the inequality we
  *can* get freely is the reverse-Fatou-style `α ≤ ∫ G₋` only via the hard direction.
  **Reconcile:** the genuinely easy bound is `∫ G₋ ≥ α`? No. Let us be precise:
  - Fatou (`MeasureTheory.lintegral_liminf_le` / the integrable version
    **`MeasureTheory.integral_liminf_le_liminf`** if it exists — grep; otherwise via
    `lintegral` on `g + bound`) gives, when applicable,
    `∫ liminf fₙ ≤ liminf ∫ fₙ`. With `fₙ = g(n+1)/(n+1)`, `liminf ∫ fₙ = α` (Step 1
    is a genuine limit so liminf = α). So **`∫ G₋ ≤ α`**. This is the *easy* bound and
    it points the *right* way for the squeeze below.
  - **Fatou needs a uniform lower bound** on `fₙ` (an integrable minorant) to apply
    to non-nonneg functions. Provide it after Step 4's reduction-to-≤0 (A2): once
    `gₙ ≤ Σ_{j<n} g₁∘Tʲ` and `g₁ ∈ L¹`, the negative parts are dominated. This is why
    A2 (reduction to a nonpositive process) is sequenced before the Fatou step in the
    actual proof. **Risk R4: Fatou minorant bookkeeping.**
- **Output:** `∫ G₋ ≤ α`. (And trivially `G₋ ≤ G₊` pointwise, from
  **`Filter.liminf_le_limsup`**, `Mathlib/Order/LiminfLimsup.lean:180`, needs
  `IsBoundedUnder` both ways — supplied by the A1/A2 sandwich.)

### Step 4 — hard direction: `∫ G₊ ≤ α` (truncation + maximal/stopping)

This is the crux and the only place Katznelson–Weiss and Steele diverge.

- **A2 reduction (shared).** Replace `gₙ` by `g̃ₙ := gₙ − birkhoffSum T g₁ n` (the
  Birkhoff sum `Σ_{j<n} g₁(Tʲx)`, **`Dynamics.BirkhoffSum.birkhoffSum`**,
  `Mathlib/Dynamics/BirkhoffSum/Basic.lean`). By the singleton partition (A1) `g̃ₙ ≤ 0`;
  `g̃` is still a subadditive cocycle; and by **M3** `birkhoffSum T g₁ n / n →`
  `condExp` (a.e.), so `gₙ/n` converges iff `g̃ₙ/n` does, with limit shifted by the
  Birkhoff limit `B(x) := μ[g₁ | invariants T] x`. **So WLOG `gₙ ≤ 0`** and the target
  becomes `∫ G̃₊ ≤ α̃` with `α̃ = α − ∫ g₁` (since `∫ B = ∫ g₁` by
  **`integral_condExp`**, `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:228`).
- **Truncation.** For `ε > 0`, `M > 0`, set `G' := max G₊ (−M)` — `T`-invariant
  (Step 2 + `max` of invariants), integrable (bounded below by `−M`, above by `≤ 0`),
  and `G' ≥ G₊`. Suffices to prove `∫ G₊ ≤ ∫ G' ≤ α + ε` and let `ε↓0`, `M→∞`
  (monotone/dominated convergence — **`MeasureTheory.tendsto_integral_of_dominated_convergence`**,
  `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:58`; or
  `integral_tendsto_of_tendsto_of_antitone` if present).
- **Stopping time.** For `x` and `N`, since `G₊ x = limsup (gₙx/n) ≥ G' x − ε`
  infinitely often, there is a least `τ(x) ≤ N` (or the bad event) with
  `g_{τ(x)}(x)/τ(x) ≤ G'(x) + ε`. Define the stopping/bad set
  `Eₙ := {x : ∀ k, 1 ≤ k → k ≤ n → g_k(x)/k > G'(x)+ε}`. These shrink to a null set as
  `n→∞` because `G' ≥ G₊ ≥ liminf` … (use `G₊` reached infinitely often).
- **Maximal inequality bridge (A4).** Apply M1
  (`setIntegral_birkhoffSum_pos_nonneg`) to `f := g₁ − G' − ε` (integrable: `g₁∈L¹`,
  `G'∈L¹`, const). The set where some forward Birkhoff partial sum of `f` is positive
  contains (modulo the stopping rule) the complement of the bad set; the maximal
  inequality then yields `∫_{good} (g₁ − G' − ε) ≥ 0`, i.e.
  `∫ G' ≤ ∫ g₁ − ε·μ(good) + (correction on bad set)`. Telescoping the cocycle along
  the stopping times converts `∫ g₁` into `α̃`-type terms. **This is the lemma whose
  exact form must be pinned against our M1 (A4 in §4).** The Katznelson–Weiss device
  here replaces Steele's greedy length-counting with a single application of M1 to a
  cleverly chosen `f`; the algebra is the subadditive telescoping
  `gₙ ≤ Σ over stopping blocks g_{τ}(T^· x)` (A1), but the *counting* is now an
  integral identity, not a `Finset` cardinality argument.
- **Output:** `∫ G' ≤ α + ε` for every `ε, M`; pass to the limit ⇒ `∫ G₊ ≤ α`.

### Step 5 — squeeze: `G₊ = G₋` a.e. and conclude

- From Steps 3+4: `∫ G₊ ≤ α ≤ ... ` and we also have `∫ G₋ ≤ α`. We need the
  *combination* `∫ (G₊ − G₋) ≤ 0` with `G₊ − G₋ ≥ 0` pointwise. Re-deriving: Step 4
  gives `∫ G₊ ≤ α`. The companion easy bound `α ≤ ∫ G₋` comes from
  `α ≤ a(n+1)/(n+1) = ∫ (g(n+1)/(n+1))` and Fatou-for-liminf in the *other* sign once
  the process is normalized; concretely run Step 3's Fatou on `−g̃` (a *super*additive,
  nonneg-after-shift process) to get `α ≤ ∫ G₋`. **This sign-matching is Risk R5** —
  the two Fatou applications must land on opposite sides; verify the minorant/majorant
  for each.
- With `α ≤ ∫ G₋ ≤ ∫ G₊ ≤ α` (middle from `G₋ ≤ G₊` + monotone integral) all are
  equal, so `∫ (G₊ − G₋) = 0`. Since `G₊ − G₋ ≥ 0` and integrable,
  **`MeasureTheory.integral_eq_zero_iff_of_nonneg`** (grep exact name in
  `…/Bochner/Basic.lean`; candidate `integral_eq_zero_iff_of_nonneg_ae`) gives
  `G₊ − G₋ =ᵐ[μ] 0`, i.e. `G₊ =ᵐ[μ] G₋`.
- **Pointwise convergence.** On the full-measure set where `G₊ x = G₋ x`, apply
  **`Filter.tendsto_of_le_liminf_of_limsup_le`**
  (`Mathlib/Topology/Order/LiminfLimsup.lean:306`) with `a := G₋ x = G₊ x`:
  `Tendsto (fun n => g(n+1)x/(n+1)) atTop (𝓝 (G x))`. The two `IsBoundedUnder`
  side-goals are discharged by the A1/A2 sandwich (`isBoundedDefault`-friendly:
  bounded below by `α`-ish, above by `0` after A2; before A2 by the Birkhoff limit).
- Set `G := G₋` (measurable, `T`-invariant from Step 2). Undo the A2 shift: the true
  limit is `G̃ + B` where `B = μ[g₁ | invariants T]`; `B` is `T`-invariant
  (it is `invariants T`-measurable, hence `B∘T =ᵐ B` — needs M2-style commutation or
  `condExp_of_aestronglyMeasurable` + invariance of the σ-algebra) and integrable
  (`integrable_condExp`). So the final `G := G̃₋ + B` is invariant and integrable.
- Reindex back to `(n:ℝ)⁻¹ * g n` via Step 0.

### Step 6 — integrability of `G`

`G = G̃₋ + B`. `B ∈ L¹` (`MeasureTheory.integrable_condExp`,
`…/ConditionalExpectation/Basic.lean`). `G̃₋ ∈ L¹`: it is measurable, `≤ 0`
(after A2), and `∫ G̃₋ ≥ α̃ > −∞` (Step 5), so its negative part is `L¹` and it is
nonpositive ⇒ integrable (use **`MeasureTheory.integrable_of_integral_eq...`** /
`Integrable` from `∫|G̃₋| = −∫G̃₋ < ∞`; combine `integrable_neg_iff` + nonneg).
Then `G ∈ L¹` by `Integrable.add`.

---

## 4. Auxiliary lemmas to build first (private to `Kingman.lean`)

Stated with the repo's `variable {X} [MeasurableSpace X] {μ} {T}` in scope. Suggest
they live as `private lemma`s above `tendsto_kingman`.

- **A1 — partition / block subadditivity (Steele Step 0).** Reused by both routes; it
  is the algebraic backbone of Step 4.
  ```lean
  private lemma IsSubadditiveCocycle.le_sum_blocks
      (hsub : IsSubadditiveCocycle T g) (x : X) :
      ∀ (k : ℕ) (ℓ : Fin k → ℕ),
        g (∑ i, ℓ i) x ≤ ∑ i, g (ℓ i) (T^[∑ j ∈ Finset.Iio i, ℓ j] x)
  ```
  Proof: induction on `k` using `hsub.apply_add_le`. **Index bookkeeping risk R1.**
  *(Minimal form actually needed for A2: the singleton partition `ℓ ≡ 1`, giving
  `g n x ≤ birkhoffSum T (g 1) n x`. Prove that special case first; it suffices for the
  A2 reduction and may suffice for the whole Katznelson–Weiss Step 4.)*

- **A1' — `g n x ≤ birkhoffSum T (g 1) n x`** (the singleton specialization of A1).
  ```lean
  private lemma IsSubadditiveCocycle.le_birkhoffSum_one
      (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
      g n x ≤ birkhoffSum T (g 1) n x
  ```
  Proof: induction on `n`; `birkhoffSum_succ` (`Mathlib/Dynamics/BirkhoffSum/Basic.lean`)
  + `hsub.apply_add_le n 1` (or `1 n`). Watch the cocycle direction:
  `g (n+1) x ≤ g n x + g 1 (T^[n] x)` is `hsub.apply_add_le n 1`.

- **A2 — integral subadditivity of `aₙ = ∫ gₙ`.**
  ```lean
  private lemma integral_subadditive (hT : MeasurePreserving T μ μ)
      (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
      Subadditive (fun n => ∫ x, g n x ∂μ)
  ```
  Proof: §3 Step 1 (`integral_mono` + `integral_map` via `(hT.iterate m).map_eq` +
  `MeasurePreserving.integrable_comp`).

- **A3 — `T`-invariance from `G ≤ G∘T` (measure preservation).**
  ```lean
  private lemma ae_eq_comp_of_le_comp [IsFiniteMeasure μ]
      (hT : MeasurePreserving T μ μ) {F : X → ℝ} (hF : Measurable F)
      (hle : ∀ x, F x ≤ F (T x)) : F ∘ T =ᵐ[μ] F
  ```
  Proof: §3 Step 2 rational-exhaustion (`measure_preimage` + `ae_eq_of_subset_of_measure_ge`
  + `ae_all_iff`). Genuinely reusable; consider upstreaming. **Note the `≤`/`∘T`
  orientation:** `F ≤ F∘T` with `μ` preserved forces equality a.e. because preimages
  of upper level sets only grow yet keep their measure.

- **A4 — stopping-time maximal bound (the Katznelson–Weiss crux).** The lemma that
  turns M1 into `∫ G' ≤ α + ε`. Its precise statement must be reverse-engineered from
  what M1 (`setIntegral_birkhoffSum_pos_nonneg`) actually gives. Sketch target:
  ```lean
  private lemma setIntegral_stopping_le [IsFiniteMeasure μ]
      (hT : MeasurePreserving T μ μ) (hsub : IsSubadditiveCocycle T g)
      (hint : ∀ n, Integrable (g n) μ) {G' : X → ℝ} (hG'inv : G' ∘ T =ᵐ[μ] G')
      (hG'int : Integrable G' μ) (hG'ge : ∀ᵐ x ∂μ, G' x ≥ G₊ x) {ε : ℝ} (hε : 0 < ε) :
      ∫ x, G' x ∂μ ≤ (⨅ n, (∫ x, g (n+1) x ∂μ)/(n+1)) + ε
  ```
  **This is the one lemma with real mathematical risk** (R2). If it cannot be
  discharged from M1 in a self-contained way, the documented fallback is to build
  Steele's greedy-covering Step 4 lemma instead (a `Finset.range n` consecutive-block
  partition with the length lower bound), feeding the same `∫ G' ≤ α + ε` conclusion.

---

## 5. Which Mathlib pieces EXIST vs must be BUILT

### 5.1 EXIST (verified on disk — reuse)

| Need | Mathlib decl | File:line |
|---|---|---|
| Fekete limit of subadditive seq | `Subadditive`, `Subadditive.tendsto_lim`, `Subadditive.lim`, `Subadditive.lim_le_div` | `Mathlib/Analysis/Subadditive.lean:34,87,44,47` |
| liminf ≤ limsup | `Filter.liminf_le_limsup` | `Mathlib/Order/LiminfLimsup.lean:180` |
| liminf/limsup monotone in the function | `Filter.liminf_le_liminf`, `Filter.limsup_le_limsup` | `Mathlib/Order/LiminfLimsup.lean:205,198` |
| squeeze `liminf=limsup ⇒ Tendsto` | `tendsto_of_le_liminf_of_limsup_le`, `tendsto_of_liminf_eq_limsup` | `Mathlib/Topology/Order/LiminfLimsup.lean:306,299` |
| `∫ g∘φ = ∫ g` for measure-preserving `φ` | `MeasureTheory.integral_map` (+ `MeasurePreserving.map_eq`) | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1089` |
| integrability of `g∘φ` | `MeasurePreserving.integrable_comp` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:381` |
| `∫` monotone | `integral_mono` | `…/Bochner/Basic.lean:653` |
| measure of preimage under MP map | `MeasurePreserving.measure_preimage` | `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:143` |
| MP iterate | `MeasurePreserving.iterate` | `…/MeasurePreserving.lean:193` |
| `s ⊆ t`, `μ t ≤ μ s` ⇒ `s =ᵐ t` | `MeasureTheory.ae_eq_of_subset_of_measure_ge` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:333` |
| countable ∀ a.e. | `MeasureTheory.ae_all_iff` | `Mathlib/MeasureTheory/OuterMeasure/AE.lean:95` |
| continuity from above of measure | `tendsto_measure_iInter_atTop` | `…/MeasureSpace.lean:637` |
| dominated convergence of `∫` | `MeasureTheory.tendsto_integral_of_dominated_convergence` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:58` |
| `∫ μ[f|m] = ∫ f` | `integral_condExp` | `…/ConditionalExpectation/Basic.lean:228` |
| `condExp` monotone | `condExp_mono` | `…/ConditionalExpectation/Basic.lean:482` |
| `condExp` integrable | `integrable_condExp` | `…/ConditionalExpectation/Basic.lean` (grep) |
| `setIntegral_condExp` | `setIntegral_condExp` | `…/ConditionalExpectation/Basic.lean:223` |
| indicator integral (Step 4/5 if needed) | `integral_indicator`, `setIntegral_indicator` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:164,188` |
| `birkhoffSum`, `birkhoffSum_succ/add` | `Dynamics.birkhoffSum`, `birkhoffSum_add` | `Mathlib/Dynamics/BirkhoffSum/Basic.lean` |
| reindex `atTop` by `+1` | `Filter.tendsto_add_atTop_iff_nat` | `Mathlib/Order/Filter/AtTopBot/Basic.lean` (used in `Subadditive.lean:74`) |
| ergodic ⇒ invariant function const | `Ergodic.ae_eq_const_of_ae_eq_comp_ae` (needs `AEStronglyMeasurable`) | `Mathlib/Dynamics/Ergodic/Function.lean:103` |

### 5.2 EXIST in-repo (M1/M2/M3 — currently `sorry`, treat as given)

- `ErgodicTheory.setIntegral_birkhoffSum_pos_nonneg` (M1) — `ErgodicTheory/Ergodic/MaximalErgodic.lean:28`.
- `ErgodicTheory.condExp_invariants_comp` (M2) — `ErgodicTheory/Ergodic/Birkhoff.lean:30`.
- `ErgodicTheory.tendsto_birkhoffAverage_ae` (M3) — `ErgodicTheory/Ergodic/Birkhoff.lean:39`.
- `ErgodicTheory.tendsto_birkhoffAverage_ae_integral` (M3, ergodic) — `…/Birkhoff.lean:47`.

### 5.3 Must BUILD

- **A1 / A1'** block- and singleton-partition subadditivity (no Mathlib analog).
- **A2** integral subadditivity wrapper (thin; glue of existing lemmas).
- **A3** invariance-from-monotone-under-`T` (no direct analog; reusable, upstreamable).
- **A4** the stopping-time maximal bound (the real new analytic lemma; route-defining).
- The two **Fatou applications** (Step 3 & Step 5 companion). **VERIFIED: there is NO
  Bochner-`integral` Fatou in the pinned tree** — only the Lebesgue form
  `MeasureTheory.lintegral_liminf_le` / `lintegral_liminf_le'`
  (`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231,214`). So the `+M`-shift to a
  nonneg integrand and conversion `∫ = ∫⁻ − …` is **mandatory**, not optional
  (this is exactly Risk R4). Build a small private `integral_liminf_le` wrapper for the
  shifted process.

### 5.4 Verified names (this pass)

- `integrable_condExp` — **EXISTS**, `…/ConditionalExpectation/Basic.lean:214`.
- `integral_eq_zero_iff_of_nonneg_ae` — **EXISTS**, `…/Bochner/Basic.lean:744`
  (signature `(hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) : ∫ = 0 ↔ f =ᵐ 0`).
- `tendsto_add_atTop_iff_nat` — **EXISTS**, `Mathlib/Order/Filter/AtTopBot/Basic.lean:438`.
- Bochner `integral` Fatou — **ABSENT**; only `lintegral_liminf_le`
  (`…/Lebesgue/Add.lean:231`). `+M`-shift workaround mandatory (R4).
- `BddBelow.insert` — **ABSENT**; bridge the `n=0` point by hand (R7).

---

## 6. The ergodic corollary `tendsto_kingman_ergodic`

Hypotheses add `[IsProbabilityMeasure μ]` and replace `MeasurePreserving` by
`Ergodic T μ` (which `extends MeasurePreserving`, so `hT.toMeasurePreserving` feeds
`tendsto_kingman`).

- Run `tendsto_kingman hT.toMeasurePreserving hsub hint hbdd` to get `G`, invariance
  `G∘T =ᵐ G`, integrability, and a.e. convergence.
- `G` is `T`-invariant a.e. and `AEStronglyMeasurable` (from `Integrable G μ`), so
  **`Ergodic.ae_eq_const_of_ae_eq_comp_ae`** (`Mathlib/Dynamics/Ergodic/Function.lean:103`)
  gives `∃ c, G =ᵐ[μ] fun _ => c`. **Watch the hypothesis name on
  `ae_eq_const_of_ae_eq_comp_ae`: it wants `g ∘ f =ᵐ g`**, matching our
  `G ∘ T =ᵐ[μ] G` exactly. Supply `hG.aestronglyMeasurable`.
- Combine the a.e.-convergence-to-`G` with `G =ᵐ c` to get
  a.e.-convergence-to-`c`; reindex via Step 0.
- (The identification `c = ⨅ n, (∫ g_{n+1})/(n+1)` is **deferred** — the docstring
  already says so; not part of this statement.)

---

## 7. The EReal / −∞ decision (settled for M4)

- **Keep M4 entirely in `ℝ`.** The statement carries `hbdd` (Fekete boundedness),
  which pins `α := ⨅ aₙ/n` finite and bounds `G` below by `α`. There is **no `−∞`**
  in the conclusion as written. Introducing `EReal` here would only add coercion
  noise to every `liminf`/`limsup`/`integral` line.
- The general `EReal`-valued Kingman (limit possibly `−∞`, no `hbdd`) is a **separate,
  later** statement (the module docstring calls it "a planned refinement"). Do NOT
  attempt it inside `tendsto_kingman`. If it is ever needed, it is a new theorem
  `tendsto_kingman_ereal` consuming the EReal `liminf`/`limsup` API
  (`Mathlib/Order/LiminfLimsup.lean`, `EReal` is a `CompleteLinearOrder`).
- The MET-facing application (Furstenberg–Kesten) always supplies `hbdd` via
  `log⁺‖A⁻¹‖ ∈ L¹`, so the `ℝ` version is exactly what M5+ consume. **No downstream
  cost to staying in `ℝ`.**

---

## 8. Trickiest steps & Lean-specific risks

- **R1 — index bookkeeping in A1 (block partition).** `∑ i ∈ Iio i, ℓ j` offsets,
  off-by-one in `T^[·]` exponents, and matching `Finset.range n` to consecutive
  blocks. *Mitigation:* prove A1' (singleton case, induction on `n`) first; it may be
  all Step 4 needs. Reach for `Finset.sum_range_succ`, `birkhoffSum_succ`, `omega` for
  the arithmetic of offsets. This is the worst combinatorial risk if the full A1 is
  required.
- **R2 — A4 is the genuine mathematical risk.** Deriving `∫ G' ≤ α+ε` from our M1
  (Hopf/Garsia form) is the load-bearing analytic step and the reason Katznelson–Weiss
  was chosen (it reuses M1). If A4 does not fall out of M1 cleanly, **fall back to
  Steele's greedy-covering Step 4** (documented contingency). Budget the most time
  here; do not exceed the 30-minute-per-`sorry` rule before flagging.
- **R3 — a.e. vs everywhere in Step 2.** `hsub.apply_add_le` is stated **for all `x`**
  (the repo's `IsSubadditiveCocycle` is everywhere, not a.e. — good, simpler). So the
  pointwise `G₋ ≤ G₋∘T` holds *everywhere*, and only the *equality* `G₋∘T =ᵐ G₋` is
  a.e. Keep the everywhere/a.e. boundary at exactly this line. The liminf/limsup
  perturbation lemmas (`g₁x/(n+1)→0`, `n/(n+1)→1`) are pure-limit facts, no a.e.
- **R4 — Fatou minorant / which integral-Fatou exists.** Bochner `∫` may lack a direct
  liminf-Fatou; the `lintegral` form needs a nonneg integrand. *Mitigation:* after A2
  the process is `≤ 0`; shift by a fixed integrable bound to make it nonneg, apply
  `lintegral` Fatou, shift back. Verify the exact Mathlib name before committing
  (could be `integral_liminf_le_liminf` or only `lintegral_liminf_le`).
- **R5 — sign matching in the two Fatou applications (Steps 3 & 5).** One application
  bounds `∫ G₊ ≤ α`, the companion bounds `α ≤ ∫ G₋`; they sit on opposite sides and
  use minorant vs majorant respectively. Mixing them up silently gives a vacuous
  squeeze. Write both with explicit `liminf`/`limsup` and check the inequality
  directions against `liminf_le_limsup`.
- **R6 — `[IsFiniteMeasure μ]` threading.** `ae_eq_of_subset_of_measure_ge` needs
  `μ t ≠ ∞`; `tendsto_measure_iInter` and `integral_indicator` want finiteness. The
  *outer* `tendsto_kingman` does not assume it. *Decision (recommended):* prove the
  private lemmas under `[IsFiniteMeasure μ]` and either (a) add `[IsFiniteMeasure μ]`
  to `tendsto_kingman` if the upstream skeleton allows it, or (b) keep the signature
  and add it only where the lemma is invoked — but then `tendsto_kingman` as stated
  (no finiteness) is *not provable by this route* for infinite `μ`. **Flag to the
  caller:** confirm whether the fixed statement may gain `[IsFiniteMeasure μ]`. Since
  every MET call site has a probability measure, this is the pragmatic choice.
- **R7 — `n=0` and `Nat.cast` zeros.** `(0:ℝ)⁻¹ = 0`, `a 0 / 0 = 0`. The `hbdd`
  range is over `n+1` while `Subadditive.tendsto_lim` is over `n`. **`BddBelow.insert`
  does not exist** — the `BddBelow` bridge across the `n=0` point must be done by hand
  (~10 lines: lower bound `min lb 0`, `mem_lowerBounds`, `rcases` the `n=0` vs `n+1`).
  Discharge the `Nat.cast`/`div_zero` arithmetic with `simp`/`omega`.
- **R8 — `condExp` σ-finiteness side-conditions.** `setIntegral_condExp`/`integral_condExp`
  carry `[SigmaFinite (μ.trim hm)]`. With `[IsFiniteMeasure μ]` and `hm : invariants T ≤ ⊤`
  this is automatic (`invariants_le`, finite ⇒ σ-finite trim). Provide the `hm` from
  `MeasurableSpace.invariants_le T` (api-notes line 50) and the `SigmaFinite` instance.

---

## 9. Recommended Lean assembly order (smallest verifiable increments)

1. A1' (`le_birkhoffSum_one`) — pure induction, no measure theory.
2. A2 (`integral_subadditive`) + the `Subadditive a` / `α` finiteness (Step 1), incl.
   the R7 `BddBelow` bridge. *Self-contained; gives the deterministic skeleton.*
3. A3 (`ae_eq_comp_of_le_comp`) — the reusable invariance lemma.
4. Step 2 wiring: define `G₋,G₊`, prove measurability + invariance via A3.
5. A2-reduction (Step 4 preamble) to `gₙ ≤ 0` using M3 + `birkhoffSum`/`condExp`.
6. The two Fatou bounds (Steps 3 & 5 companion) — `∫G₊ ≤ α` *minus the A4 core* first
   as a `sorry -- BLOCKED: A4`, to get the squeeze skeleton compiling.
7. A4 (the maximal/stopping core) — the hard lemma; fill the `sorry`.
8. Step 5 squeeze + Step 6 integrability + Step 0 reindex ⇒ close `tendsto_kingman`.
9. `tendsto_kingman_ergodic` via `Ergodic.ae_eq_const_of_ae_eq_comp_ae`.

Each of A1', A2, A3 is independently `lake build`-able with its own `sorry`-free body;
the only persistent `sorry` should be A4 until step 7.
