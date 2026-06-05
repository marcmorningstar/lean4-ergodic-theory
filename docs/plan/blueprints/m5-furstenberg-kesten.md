# Blueprint — M5: Furstenberg–Kesten (extremal Lyapunov exponents)

**Layer:** L3 / milestone M5. **File:** `Oseledets/Cocycle/FurstenbergKesten.lean`.
**Goal:** discharge the two `sorry`s

- `furstenbergKesten_top`  : `∃ lam, ∀ᵐ x, (1/n) log‖A⁽ⁿ⁾(x)‖ → lam`  (top exponent),
- `furstenbergKesten_bot`  : `∃ lam, ∀ᵐ x, (1/n) log‖(A⁽ⁿ⁾(x))⁻¹‖ → lam`  (bottom).

This is the **first application of Kingman** (`tendsto_kingman` /
`tendsto_kingman_ergodic`, assumed available with the signatures in
`Oseledets/Ergodic/Kingman.lean`). It is pure plumbing on top of Kingman: build the
subadditive cocycle `gₙ = log‖A⁽ⁿ⁾‖`, check the three Kingman hypotheses
(subadditive / integrable / bounded-below), then collapse to a constant.

All declarations and lemma names below were spot-verified against the pinned Mathlib
source under `.lake/packages/mathlib/Mathlib`. Verified names carry **[V]**.

---

## 0. Conventions and the convention-mismatch we must respect

Project cocycle identity (`Oseledets/Cocycle/Basic.lean`, **[V]**):

```
cocycle_add : cocycle A T (m + n) x = cocycle A T m (T^[n] x) * cocycle A T n x
```

(newest factor on the **left**; the shift `T^[n]` is on the **first/left** factor.)

Kingman's subadditive-cocycle predicate (`Oseledets/Ergodic/Kingman.lean`, **[V]**):

```
structure IsSubadditiveCocycle (T : X → X) (g : ℕ → X → ℝ) : Prop where
  apply_add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)
```

i.e. the shift `T^[m]` is on the **second** summand and indexed by the **first** index `m`.

**Reconciliation (load-bearing — get the indices right).** We want
`g (m+n) x ≤ g m x + g n (T^[m] x)` with `gₖ = log‖A⁽ᵏ⁾‖`. Rewrite the target index
`m + n` as `n + m` and apply `cocycle_add` with `(m := n, n := m)`:

```
cocycle A T (m + n) x = cocycle A T (n + m) x          -- Nat.add_comm
                      = cocycle A T n (T^[m] x) * cocycle A T m x   -- cocycle_add
```

so by submultiplicativity (`Matrix.l2_opNorm_mul` **[V]**) and monotone `log`,

```
log‖A⁽ᵐ⁺ⁿ⁾(x)‖ = log‖A⁽ⁿ⁾(T^[m] x) · A⁽ᵐ⁾(x)‖
              ≤ log( ‖A⁽ⁿ⁾(T^[m] x)‖ · ‖A⁽ᵐ⁾(x)‖ )
              = log‖A⁽ᵐ⁾(x)‖ + log‖A⁽ⁿ⁾(T^[m] x)‖.    -- = g m x + g n (T^[m] x). ✓
```

The `log` of a product splits as a **sum** (not just `≤`) via `Real.log_mul` **[V]**
once both norms are nonzero; the nonzero-ness of `‖A⁽ᵏ⁾‖` needs `det ≠ 0` (see §1.2).
For the **top** exponent we only need the `≤` direction, so we can avoid `log_mul` and
use `Real.log_le_log` **[V]** with the submultiplicative bound directly — but the
product still has to be `> 0` to apply `log_le_log` (which needs `0 < ‖A⁽ᵐ⁾‖·‖A⁽ⁿ⁾‖`).
This forces a positivity hypothesis on the norms even in the top case; see Risk R3.

The Kingman `hbdd` proviso is `BddBelow (range fun n => (∫ g (n+1)) / (n+1))`. For the
top exponent this lower bound is supplied by the **bottom integrability**
`IntegrableLogNorm (A⁻¹)`; see §2.3 and Risk R4.

---

## 1. New Lean statements / defs this layer needs

These are auxiliary lemmas to add to `Oseledets/Cocycle/` (a new section in
`FurstenbergKesten.lean`, or — preferred — a small new file
`Oseledets/Cocycle/Norm.lean` imported by it, to keep the measurability bridge reusable
for M6+). Signatures use the project conventions: `Matrix (Fin d) (Fin d) ℝ`, the
scoped `Matrix.Norms.L2Operator` norm, `instMeasurableSpaceMatrix` (the Pi structure).

```lean
open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace Oseledets
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X} {d : ℕ}

/-- **Measurability bridge.** The L2 operator norm is measurable as a function on the
entry/Pi measurable structure on matrices. (Needed because `Measurable.norm` in Mathlib
is stated for a `BorelSpace`, but our matrix σ-algebra is the Pi structure, not the
Borel structure of the L2 norm topology.) -/
theorem measurable_l2_opNorm :
    Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => ‖M‖)

/-- `x ↦ log‖A⁽ⁿ⁾(x)‖` is measurable. -/
theorem measurable_logNorm_cocycle
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A)
    (hTmeas : Measurable T) (n : ℕ) :
    Measurable (fun x => Real.log ‖cocycle A T n x‖)

/-- The norm of every cocycle iterate is strictly positive when the generator is in
`GL` (so `log` is well-behaved and `log_mul`/`log_le_log` apply). -/
theorem norm_cocycle_pos
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) [NeZero d]
    (n : ℕ) (x : X) : 0 < ‖cocycle A T n x‖

/-- `det (cocycle A T n x) ≠ 0` when `det (A ·) ≠ 0` (so the inverse cocycle is in GL). -/
theorem det_cocycle_ne_zero
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (n : ℕ) (x : X) :
    (cocycle A T n x).det ≠ 0

/-- **The top subadditive cocycle.** `gₙ = log‖A⁽ⁿ⁾‖` is subadditive over `T`. -/
theorem isSubadditiveCocycle_logNorm
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) [NeZero d] :
    IsSubadditiveCocycle T (fun n x => Real.log ‖cocycle A T n x‖)

/-- **The bottom subadditive cocycle.** `gₙ = log‖(A⁽ⁿ⁾)⁻¹‖` is subadditive over `T`. -/
theorem isSubadditiveCocycle_logNorm_inv
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) [NeZero d] :
    IsSubadditiveCocycle T (fun n x => Real.log ‖(cocycle A T n x)⁻¹‖)

/-- **Upper Fekete bound on the iterate norm** (drives integrability + Birkhoff
domination): `log‖A⁽ⁿ⁾(x)‖ ≤ birkhoffSum T (fun y => log⁺‖A y‖) n x`. -/
theorem logNorm_cocycle_le_birkhoffSum
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) [NeZero d] (n : ℕ) (x : X) :
    Real.log ‖cocycle A T n x‖ ≤ birkhoffSum T (fun y => Real.posLog ‖A y‖) n x

/-- Symmetric lower bound via the inverse cocycle:
`- birkhoffSum T (log⁺‖A⁻¹‖) n x ≤ log‖A⁽ⁿ⁾(x)‖`. -/
theorem neg_birkhoffSum_le_logNorm_cocycle
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) [NeZero d] (n : ℕ) (x : X) :
    - birkhoffSum T (fun y => Real.posLog ‖(A y)⁻¹‖) n x ≤ Real.log ‖cocycle A T n x‖

/-- Integrability of each top term `gₙ = log‖A⁽ⁿ⁾‖`. -/
theorem integrable_logNorm_cocycle
    (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) [NeZero d]
    (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (n : ℕ) : Integrable (fun x => Real.log ‖cocycle A T n x‖) μ
```

The final two theorems `furstenbergKesten_top` / `furstenbergKesten_bot` keep their
existing signatures (do not change them). Note `furstenbergKesten_top` as currently
stated takes only `hint : IntegrableLogNorm A μ`; **we must add `hint'`** (the inverse
integrability) to it, or accept an `EReal`/possibly-`-∞` limit — see Risk R4 and §2.3.

---

## 2. Proof outline (dependency-ordered)

### 2.0 Add `NeZero d` (or case-split on `d = 0`)

For `d = 0` the matrix algebra is trivial: `‖M‖ = 0` for every `M`, so
`log‖A⁽ⁿ⁾‖ = log 0 = 0` (`Real.log_zero` **[V]**) for all `n`, the limit is the
constant `0`, and both theorems are immediate (`lam := 0`, `tendsto_const_nhds` after
`simp`). Handle `d = 0` first by `rcases Nat.eq_zero_or_pos d`; in the `0 < d` branch
introduce `haveI : NeZero d := ⟨h.ne'⟩` and run the main argument. (`NeZero d` ⇒
`Nontrivial (EuclideanSpace ℝ (Fin d))` ⇒ `‖(1 : Matrix)‖ = 1`; see §2.1.)

### 2.1 `measurable_l2_opNorm` — the measurability bridge  (Risk R1, do FIRST)

The L2 operator norm `‖·‖ : Matrix (Fin d) (Fin d) ℝ → ℝ` is **continuous** for the
norm topology, and the norm topology on a finite product is the product topology, so
`‖·‖` is continuous from the entrywise product topology. Combined with
`Pi.opensMeasurableSpace` **[V]** / `borel_eq_borel_pi`-style identification
(`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`, lines ~357, ~617–640
**[V]**: `MeasurableSpace.pi = borel (Π i, X i)` for second-countable `Xᵢ`), one gets
measurability w.r.t. the Pi structure.

Concrete route:
1. `‖·‖` is continuous: `continuous_norm` (general normed group) gives continuity for
   the L2-norm topology on `Matrix`. (Verify the exact name; `Continuous.norm` /
   `continuous_norm` exist in `Mathlib/Analysis/Normed/Group/Basic.lean`.)
2. The L2-norm topology on `Matrix (Fin d) (Fin d) ℝ` equals the product/Pi topology
   (finite-dimensional, all norms equivalent). The matrix metric is
   `Matrix.instL2OpMetricSpace` whose topology is *defined* by `replaceTopology` to be
   the inherited/induced one — check `Matrix.instL2OpMetricSpace` (line ~157 **[V]**):
   its `replaceTopology` argument forces the topology to agree with the entrywise one.
   If the defeq is not immediate, fall back to: a function `f : Matrix → ℝ` continuous
   for the *entry* topology is measurable for the Pi σ-algebra via `Continuous.measurable`
   + `borel_eq_borel_pi`.
3. Conclude `Measurable (‖·‖)` for `instMeasurableSpaceMatrix`.

**Fallback if topology defeq is painful:** prove `measurable_l2_opNorm` from
`l2_opNorm_def` by writing `‖M‖` as `‖toContinuousLinearMap (toEuclideanLin M)‖` and
using that `M ↦ toEuclideanLin M` is linear (hence entrywise-continuous, hence Pi-
measurable into the CLM `BorelSpace` **[V]** — `BorelSpace (E →L[𝕜] F)` exists in
`Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`) composed
with `Measurable.norm` on the CLM. This sidesteps the matrix-topology defeq entirely.

Mathlib lemmas: `continuous_norm`, `Continuous.measurable`, `Pi.opensMeasurableSpace`
**[V]**, `borel_eq_borel_pi` (verify name), `Measurable.norm` **[V]** (on the CLM side).

### 2.2 `measurable_logNorm_cocycle`

`Real.log ‖cocycle A T n x‖ = Real.log (‖·‖ (cocycle A T n x))`:
`(Real.measurable_log).comp (measurable_l2_opNorm.comp (measurable_cocycle hA hTmeas n))`.

- `Real.measurable_log` **[V]** (`Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:39`).
- `measurable_cocycle` **[V]** (`Oseledets/Cocycle/Basic.lean`).
- gives `AEStronglyMeasurable` via `Measurable.aestronglyMeasurable` /
  `.stronglyMeasurable.aestronglyMeasurable` **[V]** (real codomain).

For the inverse cocycle, additionally need `Measurable (fun x => (cocycle A T n x)⁻¹)`:
matrix inverse `M ↦ M⁻¹` is entrywise a ratio of polynomials in entries (adjugate /
det), hence Pi-measurable; build `measurable_inv_matrix` as a small aux (or note
`Matrix.inv` is `Ring.inverse`-based and measurability follows from continuity of
`adjugate` and `det` plus measurability of division — `det ≠ 0` everywhere here).

### 2.3 `det_cocycle_ne_zero`, `norm_cocycle_pos`

`det (cocycle A T n x) ≠ 0`: induct on `n`. Base `cocycle_zero`: `det 1 = 1 ≠ 0`.
Step `cocycle_succ`: `det (M * A x) = det M * det (A x)` via `Matrix.det_mul` **[V]
(L0.8)**; both factors nonzero by IH and `hA`.

`norm_cocycle_pos` (needs `NeZero d`): a matrix with `det ≠ 0` is invertible, hence
`≠ 0`, hence (norm) `‖cocycle‖ ≠ 0`; with `norm_nonneg`, `0 < ‖cocycle‖`. Use
`norm_pos_iff` and `Matrix.isUnit_iff_isUnit_det` / the fact `det ≠ 0 ⇒ M ≠ 0` when
`d ≥ 1` (a zero matrix has zero det when `d ≥ 1`). For `d = 0` the claim is false
(`‖1‖ = 0`), which is exactly why `NeZero d` is required and why `d = 0` is handled
separately in §2.0.

### 2.4 `isSubadditiveCocycle_logNorm`  (the heart)

Provide `⟨fun m n x => ?_⟩`. Goal:
`log‖A⁽ᵐ⁺ⁿ⁾(x)‖ ≤ log‖A⁽ᵐ⁾(x)‖ + log‖A⁽ⁿ⁾(T^[m] x)‖`.

1. `rw [Nat.add_comm m n, cocycle_add]` to get
   `cocycle A T (m+n) x = cocycle A T n (T^[m] x) * cocycle A T m x`. **[V]**
2. `‖A⁽ⁿ⁾(T^[m]x) · A⁽ᵐ⁾(x)‖ ≤ ‖A⁽ⁿ⁾(T^[m]x)‖ · ‖A⁽ᵐ⁾(x)‖` : `Matrix.l2_opNorm_mul`. **[V]**
3. Both norms positive (`norm_cocycle_pos`, §2.3), so the product is positive.
4. `Real.log_le_log (by positivity) (step 2)` **[V]** :
   `log‖A⁽ᵐ⁺ⁿ⁾‖ ≤ log(‖A⁽ⁿ⁾(T^[m]x)‖ · ‖A⁽ᵐ⁾(x)‖)`.
5. `Real.log_mul (ne_of_gt …) (ne_of_gt …)` **[V]** :
   `log(‖A⁽ⁿ⁾(T^[m]x)‖·‖A⁽ᵐ⁾(x)‖) = log‖A⁽ⁿ⁾(T^[m]x)‖ + log‖A⁽ᵐ⁾(x)‖`.
6. `linarith` / `add_comm` to match the goal `... ≤ g m x + g n (T^[m] x)`.

### 2.5 `logNorm_cocycle_le_birkhoffSum` and `neg_birkhoffSum_le_logNorm_cocycle`

Upper: induct on `n`.
- `n = 0`: LHS `log‖1‖ = 0` (since `‖1‖ = 1` for `NeZero d`, `Real.log_one`; or
  `log 0 = 0` for `d=0`). RHS `birkhoffSum T _ 0 x = 0` (`birkhoffSum` over `range 0`).
  `0 ≤ 0`. **[V]** (`birkhoffSum` def, `Real.log_one`/`Real.log_zero`).
- `n+1`: `cocycle_succ`: `A⁽ⁿ⁺¹⁾(x) = A⁽ⁿ⁾(T x) * A x`. Submultiplicative +
  `Real.log_le_log` + `Real.log_mul` give
  `log‖A⁽ⁿ⁺¹⁾(x)‖ ≤ log‖A⁽ⁿ⁾(T x)‖ + log‖A x‖`. Bound `log‖A x‖ ≤ log⁺‖A x‖ =
  posLog‖A x‖` via `le_max_right` (`posLog_def` **[V]**). Then peel `birkhoffSum`.
  (Index bookkeeping with `birkhoffSum_succ`/`birkhoffSum_add` — verify which
  `birkhoffSum` recursion lemma exists; `birkhoffSum_add` is **[V]** in api-notes.)

  *Caveat:* this particular induction lands `A⁽ⁿ⁾(Tx)` whereas `birkhoffSum` accumulates
  `f(T^[k] x)`; the natural matching uses the `cocycle = A(T^[n-1]x)···A(x)` expansion,
  i.e. expand `log‖A⁽ⁿ⁾(x)‖ ≤ Σ_{k<n} log⁺‖A(T^[k] x)‖` directly by the
  *partition/telescoping* form of subadditivity. Cleanest: derive it from
  `isSubadditiveCocycle_logNorm` applied `n` times (a `Finset.sum` telescoping lemma —
  this is exactly Kingman's "Step 0" partition lemma `L2.2`; if that lemma is exposed by
  the Kingman build, reuse it; otherwise prove the `n`-fold bound by induction here).

Lower: same with the inverse. Use
`log‖A⁽ⁿ⁾(x)‖ = - log‖(A⁽ⁿ⁾(x))⁻¹‖` ... no — instead bound
`log‖A⁽ⁿ⁾(x)‖ ≥ - log‖(A⁽ⁿ⁾(x))⁻¹‖` from `1 = ‖A⁽ⁿ⁾ · (A⁽ⁿ⁾)⁻¹‖ ≤ ‖A⁽ⁿ⁾‖·‖(A⁽ⁿ⁾)⁻¹‖`
(submult + `‖(1:Matrix)‖ = 1`), giving `0 ≤ log‖A⁽ⁿ⁾‖ + log‖(A⁽ⁿ⁾)⁻¹‖`, then bound
`log‖(A⁽ⁿ⁾)⁻¹‖ ≤ Σ_{k<n} log⁺‖(A(T^[k]x))⁻¹‖ = birkhoffSum T (log⁺‖A⁻¹‖) n x` by the
inverse subadditive cocycle (§2.4'). This is where `‖(1:Matrix)‖ = 1` (NeZero d) is
load-bearing.

### 2.6 `integrable_logNorm_cocycle`

`gₙ` is sandwiched: `-Bₙ⁻ ≤ gₙ ≤ Bₙ⁺` where `Bₙ⁺ = birkhoffSum T (log⁺‖A‖) n`,
`Bₙ⁻ = birkhoffSum T (log⁺‖A⁻¹‖) n` (§2.5). Both `Bₙ±` are integrable:
`birkhoffSum` is a finite sum of `(log⁺‖A‖) ∘ T^[k]`, each integrable because
`T^[k]` is measure-preserving (`hT.iterate k` — `MeasurePreserving.iterate` **[V] L0.1**)
and `IntegrableLogNorm` = `Integrable (log⁺‖A‖)` is preserved by precomposition with a
m.p. map (`Integrable.comp_measurePreserving` / `MeasurePreserving.integrable_comp`;
verify exact name). Sum via `integrable_finset_sum`.

Then `gₙ` is integrable by `Integrable.mono'` **[V]** (or `MemLp`/`Integrable.mono`):
`gₙ` is `AEStronglyMeasurable` (§2.2) and `|gₙ| ≤ max(Bₙ⁺, Bₙ⁻) ≤ Bₙ⁺ + Bₙ⁻` a.e.
(both `≥ 0` since `log⁺ ≥ 0` ⇒ `birkhoffSum ≥ 0`), and `Bₙ⁺ + Bₙ⁻` integrable. Use
`Integrable.mono'` with the dominating function `Bₙ⁺ + Bₙ⁻` and the bound
`‖gₙ x‖ = |gₙ x| ≤ Bₙ⁺ x + Bₙ⁻ x`.

`IsFiniteMeasure μ` is needed here (constants/finite-sum integrability), and is supplied
by `IsProbabilityMeasure μ` in the theorem hypotheses.

### 2.7 `hbdd` — the bounded-below proviso for Kingman

`hbdd : BddBelow (range fun n => (∫ g (n+1) x ∂μ) / (n+1))`. Lower-bound each
normalized integral:

```
∫ gₙ ≥ ∫ (-Bₙ⁻) = - ∫ birkhoffSum T (log⁺‖A⁻¹‖) n = - n · ∫ log⁺‖A⁻¹‖ dμ
```

using §2.5 (lower bound, monotone integral) and the **Birkhoff-sum integral identity**
`∫ birkhoffSum T f n dμ = n · ∫ f dμ` for measure-preserving `T` (each
`∫ f∘T^[k] = ∫ f` by `MeasurePreserving.integral_comp` / `…integral_map`; verify name).
Hence `(∫ g_{n+1})/(n+1) ≥ - ∫ log⁺‖A⁻¹‖ dμ =: -C`, a constant lower bound, so
`BddBelow` holds with witness `-C`. (`C = ∫ log⁺‖A⁻¹‖ dμ` is finite because `hint'`.)

**This is exactly the place `IntegrableLogNorm (A⁻¹)` enters the top exponent** — without
it the limit could be `-∞` and `tendsto_kingman` (the `ℝ`-valued version) would not
apply. See Risk R4.

### 2.8 Assemble `furstenbergKesten_top`

```
rcases Nat.eq_zero_or_pos d with hd | hd
· -- d = 0 branch (§2.0): lam := 0, simp [‖_‖ = 0, Real.log_zero], tendsto_const_nhds
· haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨c, hc⟩ :=
    tendsto_kingman_ergodic hT
      (isSubadditiveCocycle_logNorm hA)                 -- §2.4
      (integrable_logNorm_cocycle hT.toMeasurePreserving hA hAmeas hT.measurable hint hint')  -- §2.6
      (hbdd …)                                           -- §2.7
  exact ⟨c, hc⟩
```

- `tendsto_kingman_ergodic` **[V] (assumed; Kingman phase)** already returns
  `∃ c, ∀ᵐ x, Tendsto (fun n => (n:ℝ)⁻¹ * g n x) atTop (𝓝 c)`, which is *exactly* the
  goal shape (`g n x = log‖A⁽ⁿ⁾(x)‖`). No separate `Ergodic.ae_eq_const_of_ae_eq_comp_ae`
  call is needed — the ergodic Kingman corollary already does the constant collapse.
  (If only the non-ergodic `tendsto_kingman` is available, instead obtain the invariant
  `G`, note `G ∘ T =ᵐ G`, apply `Ergodic.ae_eq_const_of_ae_eq_comp_ae` **[V] L0.2** to
  `G` — which needs `AEStronglyMeasurable G`, supplied by `tendsto_kingman`'s
  `Integrable G` — then transfer the a.e. limit. Prefer the ergodic corollary.)
- `hT.measurable` : `Ergodic ⊇ MeasurePreserving`; `MeasurePreserving.measurable` gives
  `Measurable T` (verify field/accessor name; m.p. carries `measurable`).
- `hT.toMeasurePreserving` : `Ergodic.toMeasurePreserving` (Ergodic extends
  MeasurePreserving) **[V] L0.1**.

**Required signature change:** add `(hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)` and
`(hA : ∀ x, (A x).det ≠ 0)` to `furstenbergKesten_top` (currently it has neither). See R4.

### 2.9 Assemble `furstenbergKesten_bot`

Identical, with the **inverse** subadditive cocycle `gₙ = log‖(A⁽ⁿ⁾(x))⁻¹‖`
(`isSubadditiveCocycle_logNorm_inv`, §2.4'). The subadditivity uses `Matrix.mul_inv_rev`
**[V]**:

```
(cocycle A T (m+n) x)⁻¹ = (cocycle A T n (T^[m] x) * cocycle A T m x)⁻¹   -- after add_comm + cocycle_add
                        = (cocycle A T m x)⁻¹ * (cocycle A T n (T^[m] x))⁻¹  -- mul_inv_rev
```

so `‖(A⁽ᵐ⁺ⁿ⁾)⁻¹‖ ≤ ‖(A⁽ᵐ⁾(x))⁻¹‖ · ‖(A⁽ⁿ⁾(T^[m]x))⁻¹‖` (submult), and `log`-split as
in §2.4 (positivity of `‖(A⁽ᵏ⁾)⁻¹‖` from `det((A⁽ᵏ⁾)⁻¹) = (det A⁽ᵏ⁾)⁻¹ ≠ 0`, via
`Matrix.det_nonsing_inv` **[V]** and `det_cocycle_ne_zero`). Integrability and `hbdd`:
the inverse cocycle's `g₁ = log‖A⁻¹‖` has integrable `log⁺` (= `hint'`), and the lower
bound for `hbdd` is symmetric, supplied by `hint` (`log⁺‖A‖`). The roles of `hint` and
`hint'` swap relative to the top case. `furstenbergKesten_bot` already carries both
`hint`, `hint'`, and `hA`, so no signature change is needed there.

---

## 3. Auxiliary lemmas to build (checklist, in build order)

1. `measurable_l2_opNorm`  — §2.1 (Risk R1). **Reusable in M6+; put in a shared file.**
2. `measurable_inv_matrix` (Pi-measurability of `M ↦ M⁻¹`) — §2.2 (only for the bottom).
3. `measurable_logNorm_cocycle` (+ inverse variant) — §2.2.
4. `det_cocycle_ne_zero` — §2.3.
5. `norm_cocycle_pos` (+ inverse variant `norm_inv_cocycle_pos`) — §2.3 (needs `NeZero d`).
6. `norm_one_matrix` : `‖(1 : Matrix (Fin d) (Fin d) ℝ)‖ = 1` for `NeZero d` — §2.5/R2.
7. `isSubadditiveCocycle_logNorm` — §2.4.
8. `isSubadditiveCocycle_logNorm_inv` — §2.4'/§2.9.
9. `logNorm_cocycle_le_birkhoffSum` / `neg_birkhoffSum_le_logNorm_cocycle` (+ inverse
   variants) — §2.5. (Or reuse Kingman's partition lemma L2.2 if exposed.)
10. `integrable_logNorm_cocycle` (+ inverse) — §2.6.
11. `birkhoffSum` integral identity `∫ birkhoffSum T f n = n • ∫ f` under m.p. — §2.7
    (check Mathlib: `integral_birkhoffSum`? if absent, prove from
    `MeasurePreserving.integral_comp`).
12. `hbdd` lemma — §2.7.

---

## 4. Key Mathlib lemmas (all spot-verified unless noted)

| decl | file | use |
|---|---|---|
| `Matrix.l2_opNorm_mul` | `Analysis/CStarAlgebra/Matrix.lean:216` | submultiplicativity (subadditivity of `gₙ`) |
| `Matrix.l2_opNorm_toEuclideanCLM` | `…/Matrix.lean:228` (`rfl`) | `‖M‖ = ‖toEuclideanCLM M‖` bridge |
| `Matrix.mul_inv_rev` | `LinearAlgebra/Matrix/NonsingularInverse.lean:642` | inverse of a product (bottom cocycle) |
| `Matrix.det_nonsing_inv` | `…/NonsingularInverse.lean:412` | `det M⁻¹ = (det M)⁻¹` ≠ 0 (bottom positivity) |
| `Matrix.det_mul` | `LinearAlgebra/Matrix/Determinant/Basic.lean` (L0.8) | `det_cocycle_ne_zero` induction |
| `Real.log_mul` | `Analysis/SpecialFunctions/Log/Basic.lean:132` | split `log(ab)=log a+log b` |
| `Real.log_le_log` | `…/Log/Basic.lean` (`(0<x)(x≤y)`) | monotone `log` on the submult bound |
| `Real.log_one` / `Real.log_zero` | `…/Log/Basic.lean:106/102` | `n=0` term `log‖1‖=0` |
| `Real.measurable_log` | `MeasureTheory/Function/SpecialFunctions/Basic.lean:39` | measurability of `log∘…` |
| `Real.posLog_def` / `posLog_nonneg` / `posLog_le_posLog` | `…/Log/PosLog.lean:42/67/108` | `log ≤ log⁺`, monotone, `≥0` |
| `birkhoffSum_add` | `Dynamics/BirkhoffSum/Basic.lean` (api-notes) | telescoping the upper bound |
| `MeasurePreserving.iterate` | `Dynamics/Ergodic/MeasurePreserving.lean` (L0.1) | each `f∘T^[k]` integrable / same integral |
| `Ergodic.toMeasurePreserving` | `Dynamics/Ergodic/Ergodic.lean` (L0.1) | feed Kingman |
| `Ergodic.ae_eq_const_of_ae_eq_comp_ae` | `Dynamics/Ergodic/Function.lean` (L0.2) | constant collapse (fallback if non-ergodic Kingman) |
| `Integrable.mono'` | `MeasureTheory/Function/L1Space/Integrable.lean:100` | dominate `gₙ` by `Bₙ⁺+Bₙ⁻` |
| `Pi.opensMeasurableSpace` / `borel_eq_borel_pi` | `…/BorelSpace/Basic.lean:357/634` | Pi = Borel for the norm bridge |
| `BorelSpace (E →L[𝕜] F)` | `…/BorelSpace/ContinuousLinearMap.lean` | fallback route for `measurable_l2_opNorm` |
| `tendsto_kingman_ergodic` | `Oseledets/Ergodic/Kingman.lean` (assumed) | the engine — returns the constant directly |
| `measurable_cocycle` | `Oseledets/Cocycle/Basic.lean` | measurability of iterates |
| `cocycle_add` / `cocycle_succ` / `cocycle_zero` | `Oseledets/Cocycle/Basic.lean` | cocycle identity |

(Names without a line number are referenced from `docs/plan/api-notes.md` / the L0
ladder and should be re-confirmed against the green build; the matrix/log/posLog ones
above were read directly from disk.)

---

## 5. Lean-specific risks

- **R1 — measurability bridge (Pi vs Borel) is the real obstacle, not the math.**
  `Measurable.norm` is for `BorelSpace`; our matrix σ-algebra is the *Pi* structure
  (`instMeasurableSpaceMatrix`), and there is **no registered `BorelSpace (Matrix …)`**
  for the scoped L2 norm (verified: zero hits). `measurable_l2_opNorm` must be proved by
  hand (continuity for the entry topology + `Pi = Borel`, or the CLM-`BorelSpace`
  fallback in §2.1). This blocks integrability and so the whole layer; build it first.
  *Note:* `IntegrableLogNorm A` already bundles `Integrable (log⁺‖A·‖)` ⇒
  `AEStronglyMeasurable`, so the **generator's** norm-measurability is free from the
  hypothesis; only the **iterates** `cocycle A T n` need the bridge — but they do need it.

- **R2 — `‖(1 : Matrix)‖ = 1` requires `NeZero d`.** There is **no `NormOneClass`
  instance** for the L2 operator norm on matrices (verified). For `NeZero d`,
  `Nontrivial (EuclideanSpace ℝ (Fin d))` ⇒ `ContinuousLinearMap.norm_id` **[V]**
  (`‖id‖ = 1`) via `map_one` of `toEuclideanCLM` (star-alg equiv) + `l2_opNorm_toEuclideanCLM`.
  For `d = 0`, `‖1‖ = 0` and `log‖1‖ = log 0 = 0` — *still 0*, so the `n=0` cocycle term
  `g 0 = 0` either way. But subadditivity demands `g 0 ≥ 0` (set `m=0` or `n=0` in
  `apply_add_le`), which holds since `g 0 = 0`. Handle `d=0` by the separate trivial
  branch (§2.0) to avoid fighting `norm_cocycle_pos` (which is false at `d=0`).

- **R3 — positivity needed for `log_mul`/`log_le_log`.** `Real.log_le_log` needs
  `0 < x` and `Real.log_mul` needs both factors `≠ 0`. So subadditivity of `gₙ` is not
  purely formal: it uses `0 < ‖A⁽ᵏ⁾‖`, i.e. `det ≠ 0` (`norm_cocycle_pos`). Without
  `det ≠ 0` a factor could be the zero matrix (`‖·‖ = 0`, `log 0 = 0`) and the clean
  `log(ab) = log a + log b` split fails (it becomes only `≤` with junk values). This is
  why `furstenbergKesten_top` should also carry `hA : det ≠ 0` (see R4). If one wants the
  Ruelle generality (real matrices, no `GL`), the right statement is `EReal`-valued; out
  of scope for M5.

- **R4 — `furstenbergKesten_top` is under-hypothesized as currently stated.** It takes
  only `hint : IntegrableLogNorm A` and **no `hA`/`hint'`**, but with the `ℝ`-valued
  ergodic Kingman corollary (`tendsto_kingman_ergodic`, which needs `hbdd` to keep the
  limit in `ℝ`), the bounded-below proviso requires `IntegrableLogNorm (A⁻¹)` (§2.7), and
  the subadditivity/positivity require `det ≠ 0` (R3). **Recommended fix:** change
  `furstenbergKesten_top` to take `(hA : ∀ x, (A x).det ≠ 0)` and
  `(hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)` (matching `furstenbergKesten_bot`
  and the target `oseledets_filtration`, which already pass both `hA` and `hint'`). The
  alternative — keep the lean hypotheses and state the limit in `EReal` allowing `-∞` —
  is mathematically the honest Ruelle/Filip top-exponent statement but requires an
  `EReal` Kingman, which the current `Oseledets/Ergodic/Kingman.lean` does **not**
  provide (it is `ℝ`-valued with `hbdd`). So: **add the two hypotheses** to keep M5 on
  the `ℝ`-valued Kingman. Flag this to the caller — it is a deliberate strengthening of
  the existing `sorry`'d signature.

- **R5 — `IsFiniteMeasure`/`IsProbabilityMeasure` is needed (as for Birkhoff/Kingman).**
  Both theorems already assume `[IsProbabilityMeasure μ]`, which gives `IsFiniteMeasure`.
  This is used for (i) integrability of finite Birkhoff sums and (ii) the `∫ birkhoffSum
  = n·∫` identity. No new measure hypothesis is required beyond what is present. (Confirm
  `tendsto_kingman_ergodic`'s `[IsProbabilityMeasure μ]` matches.)

- **R6 — the `n+1` vs `n` index in `tendsto_kingman`/`hbdd`.** Kingman's `hbdd` ranges
  over `fun n => (∫ g (n+1))/(n+1)` (avoids `n=0` division), and the conclusion is about
  `(n:ℝ)⁻¹ * g n x`. The cocycle `g 0 = log‖1‖ = 0`, so the `n=0` term of the
  conclusion is `0⁻¹ * 0 = 0`; harmless. Just make sure `hbdd` is proved for the `n+1`
  shifted family, not the raw one (§2.7 lower bound is uniform in `n`, so this is fine).

- **R7 — Birkhoff-sum integral identity may be absent under this exact name.** §2.7 needs
  `∫ birkhoffSum T f n dμ = n • ∫ f dμ`. If `integral_birkhoffSum` does not exist, derive
  it from `∫ f∘T^[k] dμ = ∫ f dμ` (`MeasurePreserving.integral_comp`, verify name) +
  `integral_finset_sum`. Low risk, modest plumbing.

- **R8 — partition/telescoping bound (§2.5) duplication.** The `n`-fold expansion
  `log‖A⁽ⁿ⁾‖ ≤ Σ_{k<n} log⁺‖A(T^[k]x)‖` is morally Kingman's Step-0 partition lemma
  (`L2.2`). If the Kingman build exports a general `IsSubadditiveCocycle` ⇒ partition-sum
  lemma, reuse it (apply with the trivial all-singletons partition). Otherwise prove the
  special case here by induction. Decide once to avoid duplicate work with M4.
