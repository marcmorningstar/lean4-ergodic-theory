/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Smooth.DerivativeCocycle
import Oseledets.Lyapunov.Extensions.DetIdentity

/-!
# Expanding maps and the Rokhlin/Pesin right-hand-side identity

For a differentiable self-map `T : E → E` of `E := EuclideanSpace ℝ (Fin d)` we call `T`
**uniformly expanding** when there is an expansion constant `K > 1` with
`K · ‖v‖ ≤ ‖Dₓ T v‖` for every base point `x` and every tangent vector `v`. By the chain rule
this expansion compounds along the orbit: the derivative of the `n`-th iterate satisfies
`Kⁿ · ‖v‖ ≤ ‖D(T^[n]) v‖`. Consequently every singular value of the cocycle iterate is at least
`Kⁿ`, so every Lyapunov exponent of the tangent cocycle is at least `log K > 0`.

When **all** Lyapunov exponents are positive the positive-part filter is everything, so the sum of
the strictly positive exponents `∑λ⁺` (the **Pesin / Margulis–Ruelle right-hand side**, the entropy
of an SRB measure) coincides with the sum of all exponents, which by the trace–determinant identity
equals `∫ log|det Dₓ T| dμ` (the **Rokhlin right-hand side**, the integrated volume distortion).
This is the honest, foliation-free version of the Ledrappier–Young/Rokhlin entropy formula in the
expanding case: no stable foliation, no SRB-density machinery — just the all-positive-spectrum
collapse of the positive-part sum onto the determinant integral.

## Main results

* `Oseledets.cocycle_expanding_bound` — the compounded bound `Kⁿ‖v‖ ≤ ‖D(T^[n]) v‖`.
* `Oseledets.expanding_pow_le_singularValues` — `Kⁿ ≤ σᵢ(A⁽ⁿ⁾)` for every `i < d`.
* `Oseledets.log_le_exponents_of_expanding` — every Lyapunov exponent is `≥ log K`.
* `Oseledets.exponents_pos_of_expanding` — every Lyapunov exponent is strictly positive.
* `Oseledets.sumPosExp_eq_sumAllExp_of_expanding` — for an expanding map `∑λ⁺ = ∑λ`.
* `Oseledets.sumPosExp_eq_integral_log_abs_det_of_expanding` — the **Pesin = Rokhlin** identity
  `∑λ⁺ = ∫ log|det Dₓ T| dμ`.

## References

* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The compounded expansion bound.** For a differentiable uniformly expanding map with
expansion constant `K`, the derivative of the `n`-th iterate stretches every vector by at least
`Kⁿ`: `Kⁿ · ‖v‖ ≤ ‖D(T^[n]) v‖`. Proved by induction on `n`, using the chain rule
`D(T^[n+1]) x = D(T^[n]) (T x) ∘ Dₓ T` to peel off one expanding factor at each step. -/
theorem cocycle_expanding_bound
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin d)) :
    K ^ n * ‖v‖ ≤ ‖fderiv ℝ (T^[n]) x v‖ := by
  have hKnn : (0 : ℝ) ≤ K := le_of_lt (lt_trans one_pos hK)
  induction n generalizing x v with
  | zero =>
    simp only [pow_zero, one_mul, Function.iterate_zero, fderiv_id]
    rw [ContinuousLinearMap.id_apply]
  | succ n ih =>
    -- `T^[n+1] = T^[n] ∘ T`, so `D(T^[n+1]) x = D(T^[n]) (T x) ∘ Dₓ T`.
    rw [Function.iterate_succ, fderiv_comp x (hdiff.iterate n (T x)) (hdiff x),
      ContinuousLinearMap.comp_apply]
    -- `Kⁿ⁺¹ ‖v‖ = Kⁿ · (K‖v‖) ≤ Kⁿ · ‖Dₓ T v‖ ≤ ‖D(T^[n]) (T x) (Dₓ T v)‖`.
    calc K ^ (n + 1) * ‖v‖
        = K ^ n * (K * ‖v‖) := by ring
      _ ≤ K ^ n * ‖fderiv ℝ T x v‖ := by
          gcongr
          exact hexp x v
      _ ≤ ‖fderiv ℝ (T^[n]) (T x) (fderiv ℝ T x v)‖ := ih (T x) (fderiv ℝ T x v)

omit [NeZero d] in
/-- **Compounded expansion in cocycle form.** The matrix cocycle iterate
`toEuclideanCLM (cocycle (derivativeCocycle T) T n x)` stretches every vector by at least `Kⁿ`.
This is `cocycle_expanding_bound` transported through the chain-rule cocycle identity
`chainRule_cocycle`. -/
theorem cocycle_expanding_bound_clm
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin d)) :
    K ^ n * ‖v‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (derivativeCocycle T) T n x) v‖ := by
  rw [chainRule_cocycle hdiff n x]
  exact cocycle_expanding_bound hdiff hK hexp n x v

/-! ## A uniform lower bound on the norm implies a lower bound on all singular values -/

omit [NeZero d] in
/-- A uniform lower bound on the stretching of a linear endomorphism of `EuclideanSpace ℝ (Fin d)`
forces every one of its `d` singular values to be at least that bound: if `c · ‖v‖ ≤ ‖f v‖` for
every `v`, then `c ≤ σᵢ(f)` for each `i < d`. The proof evaluates `f` on the (unit-norm) right
singular vector `uᵢ`, where `σᵢ(f) = ‖f uᵢ‖ ≥ c · ‖uᵢ‖ = c`. -/
theorem le_singularValues_of_forall_le
    {f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)} {c : ℝ}
    (hf : ∀ v, c * ‖v‖ ≤ ‖f v‖) {i : ℕ} (hi : i < d) :
    c ≤ f.singularValues i := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set u := f.isSymmetric_adjoint_comp_self.eigenvectorBasis hfin with hu
  -- `σᵢ(f) = ‖f uᵢ‖`, for the orthonormal eigenvector `uᵢ` of `adjoint f ∘ₗ f`.
  have hσ : f.singularValues i = ‖f (u ⟨i, hi⟩)‖ :=
    (f.norm_apply_eigenvectorBasis_eq_singularValues hfin ⟨i, hi⟩).symm
  have hu1 : ‖u ⟨i, hi⟩‖ = 1 := u.orthonormal.1 _
  have hle := hf (u ⟨i, hi⟩)
  rw [hu1, mul_one] at hle
  rw [hσ]; exact hle

omit [NeZero d] in
/-- **Every singular value is at least `Kⁿ`.** For a differentiable uniformly expanding map with
constant `K`, every singular value of the cocycle iterate `A⁽ⁿ⁾ = cocycle (derivativeCocycle T) T n`
is at least `Kⁿ` (for `i < d`). Combines `cocycle_expanding_bound_clm` (the uniform stretching
bound) with `le_singularValues_of_forall_le`, identifying `toEuclideanCLM` with `toEuclideanLin`. -/
theorem expanding_pow_le_singularValues
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) {i : ℕ} (hi : i < d) :
    K ^ n ≤ (Matrix.toEuclideanLin (cocycle (derivativeCocycle T) T n x)).singularValues i := by
  refine le_singularValues_of_forall_le (f := Matrix.toEuclideanLin
    (cocycle (derivativeCocycle T) T n x)) (c := K ^ n) (fun v => ?_) hi
  -- `toEuclideanLin M v = toEuclideanCLM M v`, so the compounded bound applies.
  have hcoe : (Matrix.toEuclideanLin (cocycle (derivativeCocycle T) T n x)) v
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (derivativeCocycle T) T n x) v := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
  rw [hcoe]
  exact cocycle_expanding_bound_clm hdiff hK hexp n x v

/-! ## Every Lyapunov exponent is at least `log K`, hence positive -/

section Exponents

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hT : Ergodic T μ)
    (hdet : ∀ x, (derivativeCocycle T x).det ≠ 0)
    (hint : IntegrableLogNorm (derivativeCocycle T) μ)
    (hint' : IntegrableLogNorm (fun x => (derivativeCocycle T x)⁻¹) μ)

/-- **Every Lyapunov exponent is at least `log K`.** For an ergodic, log-integrable, differentiable
uniformly expanding map with constant `K`, each Lyapunov exponent of the tangent cocycle is at
least `log K`. The per-index σ-limit `(1/n) log σᵢ(A⁽ⁿ⁾) → exponents i` holds `μ`-a.e.
(`exponents_tendsto_log_singularValue`); by `expanding_pow_le_singularValues` the pre-limit terms
are `≥ (1/n) log Kⁿ = log K`, so the limit inherits the bound. -/
theorem log_le_exponents_of_expanding (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖) (i : Fin d) :
    Real.log K
      ≤ exponents hT hdet (measurable_derivativeCocycle T) hint hint' i := by
  have hKpos : (0 : ℝ) < K := lt_trans one_pos hK
  -- Pick a base point where the per-index σ-limit holds.
  obtain ⟨x, hx⟩ := (exponents_tendsto_log_singularValue hT hdet
    (measurable_derivativeCocycle T) hint hint' i).exists
  -- The pre-limit terms are bounded below by `log K` for every `n ≥ 1`.
  refine ge_of_tendsto hx ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  -- `Kⁿ ≤ σᵢ`, so `log Kⁿ ≤ log σᵢ`, i.e. `n · log K ≤ log σᵢ`.
  have hbound : K ^ n
      ≤ (Matrix.toEuclideanLin (cocycle (derivativeCocycle T) T n x)).singularValues i :=
    expanding_pow_le_singularValues hdiff hK hexp n x i.isLt
  have hlog : Real.log (K ^ n)
      ≤ Real.log ((Matrix.toEuclideanLin (cocycle (derivativeCocycle T) T n x)).singularValues i) :=
    Real.log_le_log (by positivity) hbound
  rw [Real.log_pow] at hlog
  -- `log K ≤ (1/n) log σᵢ`: rewrite the RHS as a quotient and clear the denominator.
  rw [inv_mul_eq_div, le_div_iff₀ hnpos]
  calc Real.log K * (n : ℝ)
      = (n : ℝ) * Real.log K := by ring
    _ ≤ Real.log
          ((Matrix.toEuclideanLin (cocycle (derivativeCocycle T) T n x)).singularValues i) := hlog

/-- **Every Lyapunov exponent of an expanding map is strictly positive.** Since each exponent is
at least `log K` and `K > 1` gives `log K > 0`, every exponent is positive. -/
theorem exponents_pos_of_expanding (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖) (i : Fin d) :
    0 < exponents hT hdet (measurable_derivativeCocycle T) hint hint' i :=
  lt_of_lt_of_le (Real.log_pos hK)
    (log_le_exponents_of_expanding hT hdet hint hint' hdiff hK hexp i)

/-- **For an expanding map, the positive-exponent sum is the full exponent sum.** Because every
Lyapunov exponent is strictly positive, the positive-part filter `{i | 0 < exponents i}` is all of
`Finset.univ`, so `∑λ⁺ = ∑λ`. -/
theorem sumPosExp_eq_sumAllExp_of_expanding (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖) :
    sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint'
      = sumAllExp hT hdet (measurable_derivativeCocycle T) hint hint' := by
  rw [sumPosExp, sumAllExp]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  rw [Finset.filter_true_of_mem (fun i _ =>
    exponents_pos_of_expanding hT hdet hint hint' hdiff hK hexp i)]

/-- **The Pesin = Rokhlin right-hand-side identity for an expanding map.** For an ergodic,
log-integrable, differentiable uniformly expanding self-map `T`, the sum of the strictly positive
Lyapunov exponents — the **Pesin / Margulis–Ruelle right-hand side** `∑λ⁺` — equals the integral
of `log|det Dₓ T|` — the **Rokhlin right-hand side** (integrated volume distortion):
`∑λ⁺ = ∫ log|det Dₓ T| dμ`.

This is the honest, foliation-free instance of the entropy formula: since *all* exponents are
positive, `∑λ⁺ = ∑λ` (`sumPosExp_eq_sumAllExp_of_expanding`), and the trace–determinant identity
`sumAllExp_eq_integral_log_abs_det` rewrites `∑λ` as `∫ log|det A|`. -/
theorem sumPosExp_eq_integral_log_abs_det_of_expanding (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖) :
    sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint'
      = ∫ x, Real.log |(derivativeCocycle T x).det| ∂μ := by
  rw [sumPosExp_eq_sumAllExp_of_expanding hT hdet hint hint' hdiff hK hexp,
    sumAllExp_eq_integral_log_abs_det hT hdet (measurable_derivativeCocycle T) hint hint']

end Exponents

end Oseledets
