/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.OseledetsLimit
import Oseledets.Cocycle.FurstenbergKesten
import Oseledets.Ergodic.Kingman

/-!
# Singular (one-sided) cocycles: top-exponent upper bounds without invertibility

This module develops the one-sided Lyapunov data available for a
**possibly-singular** matrix cocycle, i.e. a generator `A : X → Matrix (Fin d) (Fin d) ℝ`
that is **not** assumed everywhere invertible (no `det A ≠ 0`) and for which only
the *forward* integrability `IntegrableLogNorm A μ` (`log⁺‖A‖ ∈ L¹`) is assumed (no inverse
integrability `IntegrableLogNorm (fun x => (A x)⁻¹) μ`).

Submultiplicativity of the operator norm holds with **no invertibility hypothesis**
(`Matrix.l2_opNorm_mul`), and the positive part `log⁺ = Real.posLog` of a product is
subadditive (`Real.posLog_mul`). Hence the **non-negative** cocycle
`gₙ x = log⁺‖A⁽ⁿ⁾(x)‖` is a genuine subadditive cocycle (Kingman index convention) that is
automatically bounded below by `0`, so its normalized integrals are bounded below for free —
no `log⁺‖A⁻¹‖` is needed to keep the Furstenberg–Kesten/Kingman limit finite from below.
Feeding it to `tendsto_kingman_ergodic` produces an a.e.-constant **forward top value**
`λ₁⁺ := lim (1/n) log⁺‖A⁽ⁿ⁾(x)‖`, and since `log t ≤ log⁺ t` this yields the upper bound

`∀ᵐ x, limsup (fun n => (1/n) log‖A⁽ⁿ⁾(x)‖) ≤ λ₁⁺`.

The same `log⁺`-of-a-non-negative-subadditive-quantity argument applies to the top-`k`
singular-value product `sprod` (whose submultiplicativity `sprod_submul` *also* needs no
invertibility), giving an a.e.-constant top-`k` volume value `Γ_k⁺` with the matching
upper bound `limsup (1/n) log sprod_k ≤ Γ_k⁺`.

## Main results

* `Oseledets.isSubadditiveCocycle_posLogNorm` — `log⁺‖A⁽ⁿ⁾‖` is a subadditive cocycle, no
  invertibility.
* `Oseledets.integrable_posLogNorm_cocycle`, `Oseledets.bddBelow_posLogNorm` — the Kingman
  provisos, discharged from `IntegrableLogNorm A μ` alone.
* `Oseledets.tendsto_top_posLogNorm` — the a.e.-constant forward top value `λ₁⁺`.
* `Oseledets.limsup_logNorm_le_top` — the upper bound
  `limsup (1/n) log‖A⁽ⁿ⁾‖ ≤ λ₁⁺`.
* `Oseledets.isSubadditiveCocycle_posLogSprod`, `Oseledets.integrable_posLogSprod`,
  `Oseledets.tendsto_top_posLogSprod`, `Oseledets.limsup_logSprod_le_top` — the analogous
  top-`k` volume statements via `sprod_submul`.

## Implementation notes

* These are **one-sided upper bounds only**. There is no Oseledets filtration, no exact
  exponents, and no lower bound for a singular cocycle: a singular generator can collapse
  directions, so `(1/n) log‖A⁽ⁿ⁾‖` need not converge, and the limit may live in
  `[-∞, ∞)`. The `limsup` is bounded above by the *forward* top value `λ₁⁺`, which is the
  `log⁺` (not `log`) Furstenberg–Kesten constant.
* `λ₁⁺` and `Γ_k⁺` are the limits of the **positive parts** `log⁺‖A⁽ⁿ⁾‖`, `log⁺ sprod_k`. They
  coincide with the usual exponents whenever the latter are `≥ 0`; when the cocycle is
  asymptotically contracting they are pinned at `0` and the bound `limsup log-growth ≤ λ₁⁺`
  remains correct (the true growth is then `≤ 0`).
* The development uses neither `∀ x, (A x).det ≠ 0` nor `IntegrableLogNorm (fun x => (A x)⁻¹) μ`;
  only the forward hypothesis `IntegrableLogNorm A μ` is needed.
* Ergodicity (via `tendsto_kingman_ergodic`) makes `λ₁⁺`, `Γ_k⁺` a.e. constant; a non-ergodic
  variant replaces these by invariant measurable functions (`tendsto_kingman`).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-! ### Real-analysis helpers: `log ≤ log⁺`, measurability of `log⁺` -/

/-- `Real.log t ≤ Real.posLog t` (the positive part dominates the logarithm). -/
private theorem log_le_posLog (t : ℝ) : Real.log t ≤ Real.posLog t := by
  rw [Real.posLog_def]; exact le_max_right _ _

/-- `Real.posLog = fun x => max 0 (log x)` is measurable. -/
private theorem measurable_posLog : Measurable Real.posLog :=
  measurable_const.max Real.measurable_log

/-- **`EReal`-`limsup` transfer.** If a dominating real sequence `b` converges to `lam` and
`a n ≤ b n` for all `n`, then the `EReal`-coerced `limsup` of `a` is `≤ ↑lam`. Working in
`EReal` (a complete linear order) makes the `limsup` total and the boundedness side-conditions
automatic, so the bound is unconditional even when `a` tends to `−∞` (the genuinely singular
case, where the true growth rate lives in `[−∞, ∞)`). Packaged for both the norm and the
`sprod` upper bounds. -/
private theorem ereal_limsup_le_of_tendsto_dom {a b : ℕ → ℝ} {lam : ℝ}
    (hb : Tendsto b atTop (𝓝 lam)) (hab : ∀ n, a n ≤ b n) :
    Filter.limsup (fun n => ((a n : EReal))) atTop ≤ (lam : EReal) := by
  have hbe : Tendsto (fun n => ((b n : EReal))) atTop (𝓝 (lam : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hb
  calc Filter.limsup (fun n => ((a n : EReal))) atTop
      ≤ Filter.limsup (fun n => ((b n : EReal))) atTop :=
        Filter.limsup_le_limsup
          (Filter.Eventually.of_forall fun n => EReal.coe_le_coe_iff.2 (hab n))
    _ = (lam : EReal) := hbe.limsup_eq

/-! ### The non-negative subadditive cocycle `log⁺‖A⁽ⁿ⁾‖` (no invertibility) -/

omit [MeasurableSpace X] in
/-- **The forward `log⁺`-norm cocycle is subadditive with NO invertibility hypothesis.**
`gₙ = log⁺‖A⁽ⁿ⁾‖` satisfies the Kingman bound `g (m+n) x ≤ g m x + g n (T^[m] x)`, using only
submultiplicativity of the L2 operator norm (`Matrix.l2_opNorm_mul`) and subadditivity of the
positive part of the logarithm (`Real.posLog_mul`). No `det A ≠ 0` is required. -/
theorem isSubadditiveCocycle_posLogNorm (A : X → Matrix (Fin d) (Fin d) ℝ) :
    IsSubadditiveCocycle T (fun n x => Real.posLog ‖cocycle A T n x‖) := by
  refine ⟨fun m n x => ?_⟩
  -- symmetric split `cocycle (m+n) x = cocycle n (T^[m] x) * cocycle m x`.
  have hcoc : cocycle A T (m + n) x = cocycle A T n (T^[m] x) * cocycle A T m x := by
    rw [show m + n = n + m by ring, cocycle_add]
  have hmono : Real.posLog ‖cocycle A T (m + n) x‖
      ≤ Real.posLog (‖cocycle A T n (T^[m] x)‖ * ‖cocycle A T m x‖) := by
    apply Real.posLog_le_posLog (norm_nonneg _)
    rw [hcoc]; exact Matrix.l2_opNorm_mul _ _
  calc Real.posLog ‖cocycle A T (m + n) x‖
      ≤ Real.posLog (‖cocycle A T n (T^[m] x)‖ * ‖cocycle A T m x‖) := hmono
    _ ≤ Real.posLog ‖cocycle A T n (T^[m] x)‖ + Real.posLog ‖cocycle A T m x‖ :=
        Real.posLog_mul
    _ = Real.posLog ‖cocycle A T m x‖ + Real.posLog ‖cocycle A T n (T^[m] x)‖ := by ring

variable {μ : Measure X}

omit [MeasurableSpace X] in
/-- Upper bound by a Birkhoff sum: `log⁺‖A⁽ⁿ⁾(x)‖ ≤ birkhoffSum T (log⁺‖A‖) n x`. This is the
subadditive-cocycle bound `g (n) ≤ birkhoffSum (g 1) n` specialised to `gₙ = log⁺‖A⁽ⁿ⁾‖`. -/
theorem posLogNorm_cocycle_le_birkhoffSum (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) :
    Real.posLog ‖cocycle A T n x‖ ≤ birkhoffSum T (fun y => Real.posLog ‖A y‖) n x := by
  induction n generalizing x with
  | zero =>
    simp only [cocycle_zero, birkhoffSum_zero]
    -- `posLog ‖1‖ = 0` since `‖(1 : Matrix)‖ ≤ 1`.
    rw [Real.posLog_def]
    refine max_le_iff.2 ⟨le_refl 0, ?_⟩
    refine Real.log_nonpos (norm_nonneg _) ?_
    rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [cocycle_succ, birkhoffSum_succ']
    calc Real.posLog ‖cocycle A T n (T x) * A x‖
        ≤ Real.posLog (‖cocycle A T n (T x)‖ * ‖A x‖) :=
          Real.posLog_le_posLog (norm_nonneg _) (Matrix.l2_opNorm_mul _ _)
      _ ≤ Real.posLog ‖cocycle A T n (T x)‖ + Real.posLog ‖A x‖ := Real.posLog_mul
      _ ≤ birkhoffSum T (fun y => Real.posLog ‖A y‖) n (T x) + Real.posLog ‖A x‖ := by
          gcongr; exact ih (T x)
      _ = Real.posLog ‖A x‖ + birkhoffSum T (fun y => Real.posLog ‖A y‖) n (T x) := by ring

/-- **Integrability of each level `gₙ = log⁺‖A⁽ⁿ⁾‖`** from the forward hypothesis alone:
`0 ≤ gₙ ≤ birkhoffSum (log⁺‖A‖) n`, the upper bound integrable since `log⁺‖A‖ ∈ L¹`. No
inverse integrability is used. -/
theorem integrable_posLogNorm_cocycle (hT : MeasurePreserving T μ μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (n : ℕ) :
    Integrable (fun x => Real.posLog ‖cocycle A T n x‖) μ := by
  have hB_int : Integrable (fun x => birkhoffSum T (fun y => Real.posLog ‖A y‖) n x) μ :=
    integrable_birkhoffSum hT hint n
  have hmeas : AEStronglyMeasurable (fun x => Real.posLog ‖cocycle A T n x‖) μ :=
    ((measurable_posLog.comp
      (measurable_l2_opNorm.comp (measurable_cocycle hAmeas hTmeas n)))).aestronglyMeasurable
  refine Integrable.mono' hB_int hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg Real.posLog_nonneg]
  exact posLogNorm_cocycle_le_birkhoffSum A n x

/-- **Bounded-below proviso for free.** Since `gₙ = log⁺‖A⁽ⁿ⁾‖ ≥ 0`, its normalized integrals
are bounded below by `0` — no `log⁺‖A⁻¹‖ ∈ L¹` is needed (contrast with
`Oseledets.furstenbergKesten_norm`). -/
theorem bddBelow_posLogNorm (A : X → Matrix (Fin d) (Fin d) ℝ) :
    BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.posLog ‖cocycle A T (n + 1) x‖ ∂μ) / (n + 1)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply div_nonneg _ hpos.le
  exact integral_nonneg fun x => Real.posLog_nonneg

/-! ### The a.e.-constant forward top value `λ₁⁺` and the upper bound -/

/-- **The forward top value `λ₁⁺` (Furstenberg–Kesten with `log⁺`, no invertibility).** For an
ergodic measure-preserving `T` and a possibly-singular measurable generator with
`log⁺‖A‖ ∈ L¹`, the normalized positive-part log-norms `(1/n) log⁺‖A⁽ⁿ⁾(x)‖` converge `μ`-a.e.
to a constant `λ₁⁺`. This uses **only** the forward integrability hypothesis. -/
theorem tendsto_top_posLogNorm [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖) atTop (𝓝 lam) := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  exact tendsto_kingman_ergodic hT (isSubadditiveCocycle_posLogNorm A)
    (fun n => integrable_posLogNorm_cocycle hmp hAmeas hTmeas hint n)
    (bddBelow_posLogNorm A)

/-- **Upper bound on the singular top exponent.** For an ergodic measure-preserving `T` and
a **possibly-singular** measurable generator with `log⁺‖A‖ ∈ L¹` (and *no* invertibility, *no*
inverse integrability), there is a constant `λ₁⁺` such that for `μ`-a.e. `x`

`limsup (fun n => ((1/n) log‖A⁽ⁿ⁾(x)‖ : EReal)) ≤ λ₁⁺`.

Here `λ₁⁺` is the a.e. limit of `(1/n) log⁺‖A⁽ⁿ⁾‖` (`tendsto_top_posLogNorm`). The proof bounds
each term using `log ≤ log⁺` and passes to the `EReal` `limsup` (the `log⁺` sequence converges,
so its `limsup` equals `λ₁⁺`). The `limsup` is taken in `EReal` so that the statement is
unconditional even when the growth rate tends to `−∞` (the genuinely singular case): the true
top growth rate lives in `[−∞, ∞)` and is bounded above by `λ₁⁺`. This is a one-sided UPPER
bound only — the `liminf` is unbounded below in general (a singular cocycle may collapse
directions), so no two-sided exponent is claimed. -/
theorem limsup_logNorm_le_top [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ,
      Filter.limsup
        (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
        ≤ (lam : EReal) := by
  obtain ⟨lam, hlam⟩ := tendsto_top_posLogNorm hT hAmeas hint
  refine ⟨lam, ?_⟩
  filter_upwards [hlam] with x hx
  -- Termwise domination `(1/n) log ≤ (1/n) log⁺`, then `EReal`-limsup transfer.
  refine ereal_limsup_le_of_tendsto_dom hx (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · exact mul_le_mul_of_nonneg_left (log_le_posLog _) (by positivity)

/-! ### Top-`k` volume upper bound via `sprod` (still no invertibility)

`sprod A T k n x = ∏_{i<k} σᵢ(A⁽ⁿ⁾)` is the top-`k` singular-value product (the `k`-volume
growth). Its submultiplicativity `sprod_submul` holds with **no invertibility**, and
`sprod ≥ 0` always, so the same `log⁺`-of-a-non-negative-subadditive-quantity construction
gives an a.e.-constant forward top-`k` volume value `Γ_k⁺` and the matching upper bound. -/

omit [MeasurableSpace X] in
/-- `0 ≤ sprod A T k n x` (a product of non-negative singular values), with no invertibility. -/
theorem sprod_nonneg (A : X → Matrix (Fin d) (Fin d) ℝ) (k n : ℕ) (x : X) :
    0 ≤ sprod A T k n x :=
  Finset.prod_nonneg fun _ _ =>
    (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg _

/-- **`log⁺ sprod_k` is a subadditive cocycle with NO invertibility.** From `sprod_submul`
(submultiplicativity of the top-`k` singular-value product, which needs no `det ≠ 0`) and
`Real.posLog_mul`, with the symmetric Kingman split. -/
theorem isSubadditiveCocycle_posLogSprod (A : X → Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    IsSubadditiveCocycle T (fun n x => Real.posLog (sprod A T k n x)) := by
  refine ⟨fun m n x => ?_⟩
  -- symmetric submultiplicative split `sprod (m+n) x ≤ sprod n (T^[m] x) * sprod m x`.
  have hsub : sprod A T k (m + n) x ≤ sprod A T k n (T^[m] x) * sprod A T k m x := by
    have := sprod_submul A T k n m x
    rwa [show n + m = m + n by ring] at this
  have hmono : Real.posLog (sprod A T k (m + n) x)
      ≤ Real.posLog (sprod A T k n (T^[m] x) * sprod A T k m x) :=
    Real.posLog_le_posLog (sprod_nonneg A k (m + n) x) hsub
  calc Real.posLog (sprod A T k (m + n) x)
      ≤ Real.posLog (sprod A T k n (T^[m] x) * sprod A T k m x) := hmono
    _ ≤ Real.posLog (sprod A T k n (T^[m] x)) + Real.posLog (sprod A T k m x) := Real.posLog_mul
    _ = Real.posLog (sprod A T k m x) + Real.posLog (sprod A T k n (T^[m] x)) := by ring

omit [MeasurableSpace X] in
/-- Birkhoff-sum upper bound for `log⁺ sprod_k`: `log⁺ sprod_k(n) ≤ k · birkhoffSum (log⁺‖A‖) n`.
Each singular value is `≤ ‖A⁽ⁿ⁾‖`, so `sprod_k ≤ ‖A⁽ⁿ⁾‖^k`, and `log⁺` is monotone with
`log⁺ (t^k) = k · log⁺ t`. -/
theorem posLogSprod_le_birkhoffSum (A : X → Matrix (Fin d) (Fin d) ℝ) (k n : ℕ) (x : X) :
    Real.posLog (sprod A T k n x)
      ≤ (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) n x := by
  -- `sprod_k ≤ ‖A⁽ⁿ⁾‖^k`.
  have hle : sprod A T k n x ≤ ‖cocycle A T n x‖ ^ k := by
    rw [sprod]
    calc ∏ i ∈ Finset.range k,
          (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i
        ≤ ∏ _i ∈ Finset.range k, ‖cocycle A T n x‖ :=
          Finset.prod_le_prod
            (fun i _ => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg i)
            (fun i _ => sigma_le_opNorm _ i)
      _ = ‖cocycle A T n x‖ ^ k := by rw [Finset.prod_const, Finset.card_range]
  -- `log⁺ sprod_k ≤ log⁺ (‖A⁽ⁿ⁾‖^k) = k · log⁺‖A⁽ⁿ⁾‖`.
  calc Real.posLog (sprod A T k n x)
      ≤ Real.posLog (‖cocycle A T n x‖ ^ k) :=
        Real.posLog_le_posLog (sprod_nonneg A k n x) hle
    _ = (k : ℝ) * Real.posLog ‖cocycle A T n x‖ := Real.posLog_pow k _
    _ ≤ (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) n x :=
        mul_le_mul_of_nonneg_left (posLogNorm_cocycle_le_birkhoffSum A n x) (Nat.cast_nonneg k)

/-- **Integrability of each level `log⁺ sprod_k`** from the forward hypothesis alone:
`0 ≤ log⁺ sprod_k ≤ k · birkhoffSum (log⁺‖A‖) n`. No invertibility, no inverse integrability. -/
theorem integrable_posLogSprod [NeZero d] (hT : MeasurePreserving T μ μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (k n : ℕ) :
    Integrable (fun x => Real.posLog (sprod A T k n x)) μ := by
  have hB_int : Integrable
      (fun x => (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) n x) μ :=
    (integrable_birkhoffSum hT hint n).const_mul _
  have hmeas : AEStronglyMeasurable (fun x => Real.posLog (sprod A T k n x)) μ :=
    (measurable_posLog.comp (measurable_sprod hAmeas hTmeas k n)).aestronglyMeasurable
  refine Integrable.mono' hB_int hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg Real.posLog_nonneg]
  exact posLogSprod_le_birkhoffSum A k n x

/-- **Bounded-below proviso for free** (`log⁺ sprod_k ≥ 0`). -/
theorem bddBelow_posLogSprod (A : X → Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.posLog (sprod A T k (n + 1) x) ∂μ) / (n + 1)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact div_nonneg (integral_nonneg fun x => Real.posLog_nonneg) hpos.le

/-- **The forward top-`k` volume value `Γ_k⁺`.** For an ergodic measure-preserving `T` and a
possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹`, the normalized positive-part log
volumes `(1/n) log⁺ sprod_k(x)` converge `μ`-a.e. to a constant `Γ_k⁺`, using only the forward
integrability. -/
theorem tendsto_top_posLogSprod [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∃ gam : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog (sprod A T k n x)) atTop (𝓝 gam) := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  exact tendsto_kingman_ergodic hT (isSubadditiveCocycle_posLogSprod A k)
    (fun n => integrable_posLogSprod hmp hAmeas hTmeas hint k n)
    (bddBelow_posLogSprod A k)

/-- **Top-`k` volume upper bound (singular cocycle).** For an ergodic measure-preserving `T` and
a possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹` (no invertibility, no inverse
integrability), there is a constant `Γ_k⁺` such that for `μ`-a.e. `x`

`limsup (fun n => ((1/n) log sprod_k(x) : EReal)) ≤ Γ_k⁺`,

i.e. the top-`k` volume growth rate is bounded above by the forward top-`k` value. The `limsup`
is taken in `EReal` so the bound is unconditional even when the volume collapses
(`sprod_k → 0`, growth `→ −∞`). One-sided UPPER bound only. Carries `[NeZero d]` (the `d = 0`
algebra is trivial). -/
theorem limsup_logSprod_le_top [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∃ gam : ℝ, ∀ᵐ x ∂μ,
      Filter.limsup
        (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log (sprod A T k n x) : ℝ) : EReal)) atTop
        ≤ (gam : EReal) := by
  obtain ⟨gam, hgam⟩ := tendsto_top_posLogSprod hT hAmeas hint k
  refine ⟨gam, ?_⟩
  filter_upwards [hgam] with x hx
  refine ereal_limsup_le_of_tendsto_dom hx (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · exact mul_le_mul_of_nonneg_left (log_le_posLog _) (by positivity)

/-! ### `EReal`-limit packaging and the exact `limsup` of the genuine log

The results above bound `limsup (1/n) log‖A⁽ⁿ⁾‖ ≤ λ₁⁺` in `EReal`. The `log⁺` sequence has an
`ℝ`-limit (`tendsto_top_posLogNorm`), so its `EReal`-coercion also converges
(`tendsto_top_posLogNorm_ereal`), and its `EReal`-`limsup` and `liminf` both equal `λ₁⁺`
(`limsup_eq_liminf_posLogNorm`). The sharper statement `limsup_logNorm_eq_top_of_pos` shows that,
when the forward top value `λ₁⁺` is **strictly positive**, the `limsup` of the *genuine*
`(1/n) log‖A⁽ⁿ⁾‖` (not `log⁺`) is exactly `λ₁⁺`. A genuine *limit* of `(1/n) log‖A⁽ⁿ⁾‖` is false in
general for a singular cocycle (the liminf may be strictly below the limsup, even `−∞`), so only
the `limsup` is identified, and only when `λ₁⁺ > 0`: the contracting case `λ₁⁺ = 0` breaks the
equality, so the positivity hypothesis is essential. -/

/-- When `log t` is already non-negative, its positive part is itself:
`log⁺ t = log t`. From `Real.posLog_def` and `max_eq_right`. -/
private theorem posLog_eq_log_of_log_nonneg {t : ℝ} (h : 0 ≤ Real.log t) :
    Real.posLog t = Real.log t := by
  rw [Real.posLog_def, max_eq_right h]

/-- **`EReal`-valued limit of the normalized `log⁺`-norms.** Lifts the genuine `ℝ`-limit
`tendsto_top_posLogNorm` through the embedding `ℝ ↪ EReal` (`continuous_coe_real_ereal`): the
`EReal`-coerced sequence `((1/n) log⁺‖A⁽ⁿ⁾‖ : EReal)` converges `μ`-a.e. to `(λ₁⁺ : EReal)`. -/
theorem tendsto_top_posLogNorm_ereal [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
        (𝓝 (lam : EReal)) := by
  obtain ⟨lam, hlam⟩ := tendsto_top_posLogNorm hT hAmeas hint
  refine ⟨lam, ?_⟩
  filter_upwards [hlam] with x hx
  exact (continuous_coe_real_ereal.tendsto _).comp hx

/-- **The `limsup`/`liminf` of the `EReal` log⁺-norm sequence coincide (both equal `λ₁⁺`).**
Since the `EReal`-coerced sequence converges (`tendsto_top_posLogNorm_ereal`), its `limsup` and
`liminf` coincide with the limit. The `EReal`-`limsup`/`liminf` are unconditional (`EReal` is a
complete linear order). -/
theorem limsup_eq_liminf_posLogNorm [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ,
      Filter.limsup
          (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
          = (lam : EReal)
      ∧ Filter.liminf
          (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
          = (lam : EReal) := by
  obtain ⟨lam, hlam⟩ := tendsto_top_posLogNorm_ereal hT hAmeas hint
  refine ⟨lam, ?_⟩
  filter_upwards [hlam] with x hx
  exact ⟨hx.limsup_eq, hx.liminf_eq⟩

/-- **The canonical forward top value `λ₁⁺`, and the exact `limsup` of the genuine log-norm
growth when it is positive.** For an ergodic measure-preserving `T` and a possibly-singular
measurable generator with `log⁺‖A‖ ∈ L¹`, there is a constant `λ₁⁺` that is the `μ`-a.e. limit
of the normalized positive-part log-norms `(1/n) log⁺‖A⁽ⁿ⁾‖` (this pins `λ₁⁺` to the genuine
top value, not an arbitrary witness), and such that, **whenever `λ₁⁺ > 0`**, for `μ`-a.e. `x`

`limsup (fun n => ((1/n) log‖A⁽ⁿ⁾(x)‖ : EReal)) = λ₁⁺`.

This sharpens `limsup_logNorm_le_top` from `≤` to `=`. The `≤` half reuses the body of
`limsup_logNorm_le_top` (`ereal_limsup_le_of_tendsto_dom`). The `≥` half is the new content:
on the a.e. set where `(1/n) log⁺‖A⁽ⁿ⁾‖ → λ₁⁺ > 0`, the sequence is eventually positive, forcing
`log⁺‖A⁽ⁿ⁾‖ > 0`, hence `log‖A⁽ⁿ⁾‖ > 0` and so `log⁺‖A⁽ⁿ⁾‖ = log‖A⁽ⁿ⁾‖`
(`posLog_eq_log_of_log_nonneg`); the two `EReal` sequences are thus eventually equal, so their
`limsup`s agree (`Filter.limsup_congr`), and the latter equals `λ₁⁺` (`limsup_eq_liminf_posLogNorm`
/ `tendsto_top_posLogNorm_ereal`). The positivity hypothesis is essential: in the contracting
case `λ₁⁺ = 0` the genuine `log`-growth may tend to `−∞`, so its `limsup` can be strictly below
`λ₁⁺` and the equality fails. -/
theorem limsup_logNorm_eq_top_of_pos [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ) :
    ∃ lam : ℝ,
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖) atTop (𝓝 lam)) ∧
      (0 < lam → ∀ᵐ x ∂μ,
        Filter.limsup
          (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
          = (lam : EReal)) := by
  obtain ⟨lam, hlam⟩ := tendsto_top_posLogNorm hT hAmeas hint
  refine ⟨lam, hlam, fun hpos => ?_⟩
  filter_upwards [hlam] with x hx
  -- the `EReal`-coerced `log⁺` sequence; its `limsup` is `(lam : EReal)`.
  have hxE : Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal))
      atTop (𝓝 (lam : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hx
  have hlamLimsup :
      Filter.limsup
        (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
        = (lam : EReal) := hxE.limsup_eq
  refine le_antisymm ?_ ?_
  · -- `≤`: `limsup (log) ≤ limsup (log⁺) = lam` (body of `limsup_logNorm_le_top`).
    rw [← hlamLimsup]
    refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
    refine EReal.coe_le_coe_iff.2 ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · exact mul_le_mul_of_nonneg_left (log_le_posLog _) (by positivity)
  · -- `≥`: the two `EReal` sequences are eventually equal, so their `limsup`s agree `= lam`.
    -- Step 1: eventually `(1/n) log⁺‖A⁽ⁿ⁾‖ > 0`, since the real limit `lam > 0`.
    have hev_pos : ∀ᶠ n : ℕ in atTop,
        0 < (n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ :=
      hx.eventually (eventually_gt_nhds hpos)
    -- Step 2: from positivity of the normalized term, deduce `log⁺‖A⁽ⁿ⁾‖ = log‖A⁽ⁿ⁾‖`.
    have hev_eq : ∀ᶠ n : ℕ in atTop,
        (((n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ : ℝ) : EReal)
          = (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal) := by
      filter_upwards [hev_pos, eventually_gt_atTop 0] with n hn hn0
      have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
      -- `0 < (1/n) log⁺‖A⁽ⁿ⁾‖` and `0 < 1/n` give `0 < log⁺‖A⁽ⁿ⁾‖`.
      have hposLog_pos : 0 < Real.posLog ‖cocycle A T n x‖ :=
        (mul_pos_iff_of_pos_left hninv).1 hn
      -- `0 < max 0 (log ‖…‖)` forces `0 < log ‖…‖` (else the max is `0`).
      have hlog_pos : 0 < Real.log ‖cocycle A T n x‖ := by
        rw [Real.posLog_def] at hposLog_pos
        rcases max_cases (0 : ℝ) (Real.log ‖cocycle A T n x‖) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he] at hposLog_pos; exact absurd hposLog_pos (lt_irrefl 0)
        · rwa [he] at hposLog_pos
      rw [posLog_eq_log_of_log_nonneg hlog_pos.le]
    -- Step 3: equal eventually ⟹ equal `limsup`; the `log⁺`-limsup is `lam`.
    refine le_of_eq ?_
    calc (lam : EReal)
        = Filter.limsup
            (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop :=
          hlamLimsup.symm
      _ = Filter.limsup
            (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ : ℝ) : EReal)) atTop :=
          (Filter.limsup_congr hev_eq).symm

/-! ### Top-`k` analogues: `EReal`-limit packaging and exact `limsup` of `log sprod_k` -/

/-- **`EReal`-valued limit of the normalized `log⁺ sprod_k`.** Top-`k` mirror of
`tendsto_top_posLogNorm_ereal`: lifts the genuine `ℝ`-limit `tendsto_top_posLogSprod` through
`continuous_coe_real_ereal`, so `((1/n) log⁺ sprod_k(x) : EReal)` converges `μ`-a.e. to
`(Γ_k⁺ : EReal)`. -/
theorem tendsto_top_posLogSprod_ereal [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∃ gam : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal)) atTop
        (𝓝 (gam : EReal)) := by
  obtain ⟨gam, hgam⟩ := tendsto_top_posLogSprod hT hAmeas hint k
  refine ⟨gam, ?_⟩
  filter_upwards [hgam] with x hx
  exact (continuous_coe_real_ereal.tendsto _).comp hx

/-- **The canonical forward top-`k` value `Γ_k⁺`, and the exact `limsup` of the genuine top-`k`
log-volume growth when it is positive.** Top-`k` mirror of `limsup_logNorm_eq_top_of_pos`. For
an ergodic measure-preserving `T` and a possibly-singular measurable generator with
`log⁺‖A‖ ∈ L¹`, there is a constant `Γ_k⁺` that is the `μ`-a.e. limit of the normalized
positive-part log-volumes `(1/n) log⁺ sprod_k` (this pins `Γ_k⁺` to the genuine top-`k` value),
and such that, **whenever `Γ_k⁺ > 0`**, for `μ`-a.e. `x`

`limsup (fun n => ((1/n) log sprod_k(x) : EReal)) = Γ_k⁺`.

This sharpens `limsup_logSprod_le_top` from `≤` to `=`. The `≤` half reuses the body of
`limsup_logSprod_le_top`; the `≥` half uses that on the a.e. set where `(1/n) log⁺ sprod_k →
Γ_k⁺ > 0`, the sequence is eventually positive, forcing `log⁺ sprod_k > 0`, hence `log sprod_k > 0`
and `log⁺ sprod_k = log sprod_k` (`posLog_eq_log_of_log_nonneg`); the two `EReal` sequences are
eventually equal so their `limsup`s agree (`Filter.limsup_congr`). The positivity hypothesis is
essential (the contracting case `Γ_k⁺ = 0` breaks the equality). Carries `[NeZero d]`. -/
theorem limsup_logSprod_eq_top_of_pos [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∃ gam : ℝ,
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog (sprod A T k n x)) atTop
        (𝓝 gam)) ∧
      (0 < gam → ∀ᵐ x ∂μ,
        Filter.limsup
          (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log (sprod A T k n x) : ℝ) : EReal)) atTop
          = (gam : EReal)) := by
  obtain ⟨gam, hgam⟩ := tendsto_top_posLogSprod hT hAmeas hint k
  refine ⟨gam, hgam, fun hpos => ?_⟩
  filter_upwards [hgam] with x hx
  have hxE : Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal))
      atTop (𝓝 (gam : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hx
  have hgamLimsup :
      Filter.limsup
        (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal)) atTop
        = (gam : EReal) := hxE.limsup_eq
  refine le_antisymm ?_ ?_
  · -- `≤`: `limsup (log) ≤ limsup (log⁺) = gam` (body of `limsup_logSprod_le_top`).
    rw [← hgamLimsup]
    refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
    refine EReal.coe_le_coe_iff.2 ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · exact mul_le_mul_of_nonneg_left (log_le_posLog _) (by positivity)
  · -- `≥`: the two `EReal` sequences are eventually equal, so their `limsup`s agree `= gam`.
    have hev_pos : ∀ᶠ n : ℕ in atTop,
        0 < (n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) :=
      hx.eventually (eventually_gt_nhds hpos)
    have hev_eq : ∀ᶠ n : ℕ in atTop,
        (((n : ℝ)⁻¹ * Real.log (sprod A T k n x) : ℝ) : EReal)
          = (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal) := by
      filter_upwards [hev_pos, eventually_gt_atTop 0] with n hn _
      have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
      have hposLog_pos : 0 < Real.posLog (sprod A T k n x) :=
        (mul_pos_iff_of_pos_left hninv).1 hn
      have hlog_pos : 0 < Real.log (sprod A T k n x) := by
        rw [Real.posLog_def] at hposLog_pos
        rcases max_cases (0 : ℝ) (Real.log (sprod A T k n x)) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he] at hposLog_pos; exact absurd hposLog_pos (lt_irrefl 0)
        · rwa [he] at hposLog_pos
      rw [posLog_eq_log_of_log_nonneg hlog_pos.le]
    refine le_of_eq ?_
    calc (gam : EReal)
        = Filter.limsup
            (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal)) atTop :=
          hgamLimsup.symm
      _ = Filter.limsup
            (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log (sprod A T k n x) : ℝ) : EReal)) atTop :=
          (Filter.limsup_congr hev_eq).symm

end Oseledets
