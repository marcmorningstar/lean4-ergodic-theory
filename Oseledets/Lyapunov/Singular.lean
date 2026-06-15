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

This module records the **honest, one-sided** Lyapunov data available for a
**possibly-singular** matrix cocycle, i.e. a generator `A : X → Matrix (Fin d) (Fin d) ℝ`
that is **not** assumed everywhere invertible (`det A ≠ 0` is *dropped*) and for which only
the *forward* integrability `IntegrableLogNorm A μ` (`log⁺‖A‖ ∈ L¹`) is assumed (the inverse
integrability `IntegrableLogNorm (fun x => (A x)⁻¹) μ` is *dropped*).

Submultiplicativity of the operator norm holds with **no invertibility hypothesis**
(`Matrix.l2_opNorm_mul`), and the positive part `log⁺ = Real.posLog` of a product is
subadditive (`Real.posLog_mul`). Hence the **non-negative** cocycle
`gₙ x = log⁺‖A⁽ⁿ⁾(x)‖` is a genuine subadditive cocycle (Kingman index convention) that is
automatically bounded below by `0`, so its normalized integrals are bounded below for free —
no `log⁺‖A⁻¹‖` is needed to keep the Furstenberg–Kesten/Kingman limit finite from below.
Feeding it to `tendsto_kingman_ergodic` produces an a.e.-constant **forward top value**
`λ₁⁺ := lim (1/n) log⁺‖A⁽ⁿ⁾(x)‖`, and since `log t ≤ log⁺ t` we obtain the genuine upper bound

`∀ᵐ x, limsup (fun n => (1/n) log‖A⁽ⁿ⁾(x)‖) ≤ λ₁⁺`.

The same `log⁺`-of-a-non-negative-subadditive-quantity argument applies to the top-`k`
singular-value product `Sprod` (whose submultiplicativity `Sprod_submul` *also* needs no
invertibility), giving an a.e.-constant top-`k` volume value `Γ_k⁺` with the matching
upper bound `limsup (1/n) log Sprod_k ≤ Γ_k⁺`.

## Scope and caveats (read carefully)

* These are **one-sided UPPER bounds only**. There is **no Oseledets filtration**, **no exact
  exponents**, and **no lower bound** for a singular cocycle: a singular generator can collapse
  directions, so `(1/n) log‖A⁽ⁿ⁾‖` need not converge, and the *true* limit may live in
  `[-∞, ∞)`. We bound the `limsup` from above by the *forward* top value `λ₁⁺`, which is the
  `log⁺` (not `log`) Furstenberg–Kesten constant.
* `λ₁⁺` and `Γ_k⁺` are the limits of the **positive parts** `log⁺‖A⁽ⁿ⁾‖`, `log⁺ Sprod_k`. They
  coincide with the usual exponents whenever the latter are `≥ 0`; when the cocycle is
  asymptotically contracting they are pinned at `0` and the bound `limsup log-growth ≤ λ₁⁺`
  remains correct (the true growth is then `≤ 0`).
* This module **drops** both `∀ x, (A x).det ≠ 0` and `IntegrableLogNorm (fun x => (A x)⁻¹) μ`.
  Everything here uses *only* the forward hypothesis `IntegrableLogNorm A μ`.
* Ergodicity (via `tendsto_kingman_ergodic`) is still used to make `λ₁⁺`, `Γ_k⁺` a.e.
  constant; a non-ergodic variant would replace these by invariant measurable functions
  (`tendsto_kingman`), not pursued here.

## Main results

* `Oseledets.isSubadditiveCocycle_posLogNorm` — `log⁺‖A⁽ⁿ⁾‖` is a subadditive cocycle, no
  invertibility.
* `Oseledets.integrable_posLogNorm_cocycle`, `Oseledets.bddBelow_posLogNorm` — the Kingman
  provisos, discharged from `IntegrableLogNorm A μ` alone.
* `Oseledets.tendsto_top_posLogNorm` — the a.e.-constant forward top value `λ₁⁺`.
* `Oseledets.limsup_logNorm_le_top` — **the headline upper bound**
  `limsup (1/n) log‖A⁽ⁿ⁾‖ ≤ λ₁⁺`.
* `Oseledets.isSubadditiveCocycle_posLogSprod`, `Oseledets.integrable_posLogSprod`,
  `Oseledets.tendsto_top_posLogSprod`, `Oseledets.limsup_logSprod_le_top` — the analogous
  top-`k` volume statements via `Sprod_submul`.
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
`Sprod` upper bounds. -/
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
`Oseledets.furstenbergKesten_top`). -/
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

/-- **Headline upper bound (singular top exponent).** For an ergodic measure-preserving `T` and
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

/-! ### Top-`k` volume upper bound via `Sprod` (still no invertibility)

`Sprod A T k n x = ∏_{i<k} σᵢ(A⁽ⁿ⁾)` is the top-`k` singular-value product (the `k`-volume
growth). Its submultiplicativity `Sprod_submul` holds with **no invertibility**, and
`Sprod ≥ 0` always, so the same `log⁺`-of-a-non-negative-subadditive-quantity construction
gives an a.e.-constant forward top-`k` volume value `Γ_k⁺` and the matching upper bound. -/

omit [MeasurableSpace X] in
/-- `0 ≤ Sprod A T k n x` (a product of non-negative singular values), with no invertibility. -/
theorem Sprod_nonneg (A : X → Matrix (Fin d) (Fin d) ℝ) (k n : ℕ) (x : X) :
    0 ≤ Sprod A T k n x :=
  Finset.prod_nonneg fun _ _ =>
    (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg _

/-- **`log⁺ Sprod_k` is a subadditive cocycle with NO invertibility.** From `Sprod_submul`
(submultiplicativity of the top-`k` singular-value product, which needs no `det ≠ 0`) and
`Real.posLog_mul`, with the symmetric Kingman split. -/
theorem isSubadditiveCocycle_posLogSprod (A : X → Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    IsSubadditiveCocycle T (fun n x => Real.posLog (Sprod A T k n x)) := by
  refine ⟨fun m n x => ?_⟩
  -- symmetric submultiplicative split `Sprod (m+n) x ≤ Sprod n (T^[m] x) * Sprod m x`.
  have hsub : Sprod A T k (m + n) x ≤ Sprod A T k n (T^[m] x) * Sprod A T k m x := by
    have := Sprod_submul A T k n m x
    rwa [show n + m = m + n by ring] at this
  have hmono : Real.posLog (Sprod A T k (m + n) x)
      ≤ Real.posLog (Sprod A T k n (T^[m] x) * Sprod A T k m x) :=
    Real.posLog_le_posLog (Sprod_nonneg A k (m + n) x) hsub
  calc Real.posLog (Sprod A T k (m + n) x)
      ≤ Real.posLog (Sprod A T k n (T^[m] x) * Sprod A T k m x) := hmono
    _ ≤ Real.posLog (Sprod A T k n (T^[m] x)) + Real.posLog (Sprod A T k m x) := Real.posLog_mul
    _ = Real.posLog (Sprod A T k m x) + Real.posLog (Sprod A T k n (T^[m] x)) := by ring

omit [MeasurableSpace X] in
/-- Birkhoff-sum upper bound for `log⁺ Sprod_k`: `log⁺ Sprod_k(n) ≤ k · birkhoffSum (log⁺‖A‖) n`.
Each singular value is `≤ ‖A⁽ⁿ⁾‖`, so `Sprod_k ≤ ‖A⁽ⁿ⁾‖^k`, and `log⁺` is monotone with
`log⁺ (t^k) = k · log⁺ t`. -/
theorem posLogSprod_le_birkhoffSum (A : X → Matrix (Fin d) (Fin d) ℝ) (k n : ℕ) (x : X) :
    Real.posLog (Sprod A T k n x)
      ≤ (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) n x := by
  -- `Sprod_k ≤ ‖A⁽ⁿ⁾‖^k`.
  have hle : Sprod A T k n x ≤ ‖cocycle A T n x‖ ^ k := by
    rw [Sprod]
    calc ∏ i ∈ Finset.range k,
          (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i
        ≤ ∏ _i ∈ Finset.range k, ‖cocycle A T n x‖ :=
          Finset.prod_le_prod
            (fun i _ => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg i)
            (fun i _ => sigma_le_opNorm _ i)
      _ = ‖cocycle A T n x‖ ^ k := by rw [Finset.prod_const, Finset.card_range]
  -- `log⁺ Sprod_k ≤ log⁺ (‖A⁽ⁿ⁾‖^k) = k · log⁺‖A⁽ⁿ⁾‖`.
  calc Real.posLog (Sprod A T k n x)
      ≤ Real.posLog (‖cocycle A T n x‖ ^ k) :=
        Real.posLog_le_posLog (Sprod_nonneg A k n x) hle
    _ = (k : ℝ) * Real.posLog ‖cocycle A T n x‖ := Real.posLog_pow k _
    _ ≤ (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) n x :=
        mul_le_mul_of_nonneg_left (posLogNorm_cocycle_le_birkhoffSum A n x) (Nat.cast_nonneg k)

/-- **Integrability of each level `log⁺ Sprod_k`** from the forward hypothesis alone:
`0 ≤ log⁺ Sprod_k ≤ k · birkhoffSum (log⁺‖A‖) n`. No invertibility, no inverse integrability. -/
theorem integrable_posLogSprod [NeZero d] (hT : MeasurePreserving T μ μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (k n : ℕ) :
    Integrable (fun x => Real.posLog (Sprod A T k n x)) μ := by
  have hB_int : Integrable
      (fun x => (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) n x) μ :=
    (integrable_birkhoffSum hT hint n).const_mul _
  have hmeas : AEStronglyMeasurable (fun x => Real.posLog (Sprod A T k n x)) μ :=
    (measurable_posLog.comp (measurable_Sprod hAmeas hTmeas k n)).aestronglyMeasurable
  refine Integrable.mono' hB_int hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg Real.posLog_nonneg]
  exact posLogSprod_le_birkhoffSum A k n x

/-- **Bounded-below proviso for free** (`log⁺ Sprod_k ≥ 0`). -/
theorem bddBelow_posLogSprod (A : X → Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.posLog (Sprod A T k (n + 1) x) ∂μ) / (n + 1)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact div_nonneg (integral_nonneg fun x => Real.posLog_nonneg) hpos.le

/-- **The forward top-`k` volume value `Γ_k⁺`.** For an ergodic measure-preserving `T` and a
possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹`, the normalized positive-part log
volumes `(1/n) log⁺ Sprod_k(x)` converge `μ`-a.e. to a constant `Γ_k⁺`, using only the forward
integrability. -/
theorem tendsto_top_posLogSprod [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∃ gam : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog (Sprod A T k n x)) atTop (𝓝 gam) := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  exact tendsto_kingman_ergodic hT (isSubadditiveCocycle_posLogSprod A k)
    (fun n => integrable_posLogSprod hmp hAmeas hTmeas hint k n)
    (bddBelow_posLogSprod A k)

/-- **Top-`k` volume upper bound (singular cocycle).** For an ergodic measure-preserving `T` and
a possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹` (no invertibility, no inverse
integrability), there is a constant `Γ_k⁺` such that for `μ`-a.e. `x`

`limsup (fun n => ((1/n) log Sprod_k(x) : EReal)) ≤ Γ_k⁺`,

i.e. the top-`k` volume growth rate is bounded above by the forward top-`k` value. The `limsup`
is taken in `EReal` so the bound is unconditional even when the volume collapses
(`Sprod_k → 0`, growth `→ −∞`). One-sided UPPER bound only. Carries `[NeZero d]` (the `d = 0`
algebra is trivial). -/
theorem limsup_logSprod_le_top [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∃ gam : ℝ, ∀ᵐ x ∂μ,
      Filter.limsup
        (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log (Sprod A T k n x) : ℝ) : EReal)) atTop
        ≤ (gam : EReal) := by
  obtain ⟨gam, hgam⟩ := tendsto_top_posLogSprod hT hAmeas hint k
  refine ⟨gam, ?_⟩
  filter_upwards [hgam] with x hx
  refine ereal_limsup_le_of_tendsto_dom hx (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · exact mul_le_mul_of_nonneg_left (log_le_posLog _) (by positivity)

end Oseledets
