/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.StrictOperatorConvex

/-!
# Strict operator convexity of `-log` (Petz equality, keystone B)
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Set Filter Topology

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

/-- The resolvent integrand `t ↦ (x+t)⁻¹ - (1+t)⁻¹` whose integral over `Ioi 0` equals `-log x`. -/
def resIntegrand (t x : ℝ) : ℝ := (x + t)⁻¹ - (1 + t)⁻¹

/-- The positive kernel `t ↦ ((c+t)(1+t))⁻¹` is integrable on `(0, ∞)` for `c > 0`. -/
lemma integrableOn_resKernel {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t => ((c + t) * (1 + t))⁻¹) (Ioi (0 : ℝ)) := by
  -- integrability of `(1+t)⁻² = ((1+t)⁻¹)^2` on `Ioi 0` via FTC (antiderivative `-(1+t)⁻¹ → 0`)
  have hsq : IntegrableOn (fun t => ((1 + t)⁻¹) ^ 2) (Ioi (0 : ℝ)) := by
    apply integrableOn_Ioi_deriv_of_nonneg (g := fun t => -(1 + t)⁻¹) (l := 0)
    · -- continuity at 0
      apply ContinuousWithinAt.neg
      apply ContinuousWithinAt.inv₀
      · fun_prop
      · norm_num
    · intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have h1 : (1 : ℝ) + t ≠ 0 := by positivity
      have hd : HasDerivAt (fun t => (1 + t)⁻¹) (-((1 + t)⁻¹) ^ 2) t := by
        have hu : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
          simpa using (hasDerivAt_id t).const_add 1
        have := (hasDerivAt_inv h1).comp t hu
        simpa using this
      simpa using hd.neg
    · intro t ht; positivity
    · -- tendsto -(1+t)⁻¹ → 0
      have : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (𝓝 0) := by
        apply Filter.Tendsto.comp tendsto_inv_atTop_zero
        exact tendsto_atTop_add_const_left atTop 1 tendsto_id
      simpa using this.neg
  -- dominate the kernel by `(min c 1)⁻¹ • (1+t)⁻²`
  set K : ℝ := (min c 1)⁻¹ with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  apply Integrable.mono' (g := fun t => K * ((1 + t)⁻¹) ^ 2) (hsq.const_mul K)
  · apply Measurable.aestronglyMeasurable
    apply Measurable.inv
    fun_prop
  · -- a.e. bound
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hct : (0 : ℝ) < c + t := by linarith
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hmin : min c 1 * (1 + t) ≤ c + t := by
      rcases le_total c 1 with hcle | hcle
      · rw [min_eq_left hcle]; nlinarith
      · rw [min_eq_right hcle]; nlinarith
    have hminpos : (0 : ℝ) < min c 1 := lt_min hc one_pos
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hK]
    -- ((c+t)(1+t))⁻¹ ≤ (min c 1)⁻¹ (1+t)⁻²
    rw [mul_inv]
    have hle : (c + t)⁻¹ ≤ (min c 1)⁻¹ * (1 + t)⁻¹ := by
      rw [← mul_inv]
      exact inv_anti₀ (by positivity) hmin
    calc (c + t)⁻¹ * (1 + t)⁻¹ ≤ ((min c 1)⁻¹ * (1 + t)⁻¹) * (1 + t)⁻¹ := by
          gcongr
      _ = (min c 1)⁻¹ * ((1 + t)⁻¹) ^ 2 := by ring

/-- `resIntegrand · x` is integrable on `(0, ∞)` for `x > 0`. -/
lemma integrableOn_resIntegrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => resIntegrand t x) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun t => (1 - x) * ((x + t) * (1 + t))⁻¹) (Ioi (0 : ℝ)) :=
    (integrableOn_resKernel hx).const_mul (1 - x)
  refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  have hx1 : x + t ≠ 0 := by positivity
  have h1 : (1 : ℝ) + t ≠ 0 := by positivity
  simp only [resIntegrand]
  field_simp
  ring

/-- **Scalar integral representation of `-log`.** For `x > 0`,
`-log x = ∫ t in (0,∞), ((x+t)⁻¹ - (1+t)⁻¹)`. -/
lemma neg_log_eq_integral_resIntegrand {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), resIntegrand t x = -Real.log x := by
  set F : ℝ → ℝ := fun t => Real.log (x + t) - Real.log (1 + t) with hF
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (resIntegrand t x) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hx1 : x + t ≠ 0 := by positivity
    have h1 : (1 : ℝ) + t ≠ 0 := by positivity
    have hu1 : HasDerivAt (fun t : ℝ => x + t) 1 t := by simpa using (hasDerivAt_id t).const_add x
    have hu2 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by simpa using (hasDerivAt_id t).const_add 1
    have hd1 : HasDerivAt (fun t => Real.log (x + t)) ((x + t)⁻¹) t := by
      have := (Real.hasDerivAt_log hx1).comp t hu1
      simpa using this
    have hd2 : HasDerivAt (fun t => Real.log (1 + t)) ((1 + t)⁻¹) t := by
      have := (Real.hasDerivAt_log h1).comp t hu2
      simpa using this
    simpa [resIntegrand] using hd1.sub hd2
  have hcont : ContinuousWithinAt F (Ici (0 : ℝ)) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · exact (Real.continuousAt_log (by simpa using hx.ne')).comp (by fun_prop)
    · exact (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
  have htends : Tendsto F atTop (𝓝 0) := by
    have hraw : Tendsto (fun t : ℝ => (x + t) / (1 + t)) atTop (𝓝 1) := by
      have heq : (fun t : ℝ => (x + t) / (1 + t)) =ᶠ[atTop] (fun t => 1 + (x - 1) * (1 + t)⁻¹) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        have h1 : (1 : ℝ) + t ≠ 0 := by positivity
        field_simp
        ring
      rw [tendsto_congr' heq]
      have h0 : Tendsto (fun t : ℝ => (x - 1) * (1 + t)⁻¹) atTop (𝓝 0) := by
        have hinv : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
        simpa using hinv.const_mul (x - 1)
      simpa using tendsto_const_nhds.add h0
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hraw
    rw [Real.log_one] at hlog
    refine hlog.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hxpos : (0 : ℝ) < x + t := by positivity
    have h1pos : (0 : ℝ) < 1 + t := by positivity
    simp only [Function.comp_apply, hF]
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt h1pos)]
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (integrableOn_resIntegrand hx)
    htends
  rw [key]
  simp [hF, Real.log_one]

/-! ## Matrix integral representation via diagonalization -/

/-- The `ℝ`-linear continuous "diagonalize–conjugate" map `w ↦ U · diag(w) · U⋆` on a real
vector, sending a real spectral vector to the corresponding matrix. -/
noncomputable def diagConjCLM {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap <|
    (LinearMap.mulLeft ℝ U) ∘ₗ (LinearMap.mulRight ℝ (star U)) ∘ₗ
      (Matrix.diagonalLinearMap (Fin N) ℝ ℂ) ∘ₗ
      ((RCLike.ofRealCLM (K := ℂ) : ℝ →L[ℝ] ℂ).toLinearMap.compLeft (Fin N))

@[simp] lemma diagConjCLM_apply {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℝ) :
    diagConjCLM U w = U * diagonal (fun i => (RCLike.ofReal (w i) : ℂ)) * star U := by
  rw [mul_assoc]
  rfl

/-- `cfc f M` is `diagConjCLM` applied to the eigenvalue vector `f ∘ eigenvalues`. -/
lemma cfc_eq_diagConj {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f M = diagConjCLM (hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      (fun i => f (hM.eigenvalues i)) := by
  rw [hM.cfc_eq f]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, diagConjCLM_apply,
    Function.comp_def]

/-- The eigenvalue-integrand vector family is integrable on `(0, ∞)`. -/
lemma integrableOn_eigenVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.PosDef) :
    IntegrableOn (fun t => (fun i => resIntegrand t (hM.1.eigenvalues i))) (Ioi (0 : ℝ)) :=
  Integrable.of_eval (fun i => integrableOn_resIntegrand (hM.eigenvalues_pos i))

/-- **Matrix integral representation of `-log`.** For positive definite `M`,
`cfc (-log) M = ∫ t in (0,∞), cfc (resIntegrand t) M`. -/
lemma cfc_neg_log_eq_integral {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.PosDef) :
    cfc (fun x => -Real.log x) M = ∫ t in Ioi (0 : ℝ), cfc (resIntegrand t) M := by
  have hint := integrableOn_eigenVec M hM
  have hvec : (∫ t in Ioi (0 : ℝ), (fun i => resIntegrand t (hM.1.eigenvalues i)))
      = fun i => -Real.log (hM.1.eigenvalues i) := by
    funext i
    have hc := ContinuousLinearMap.integral_comp_comm
      (LinearMap.toContinuousLinearMap (LinearMap.proj i : (Fin N → ℝ) →ₗ[ℝ] ℝ)) hint
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.proj_apply] at hc
    rw [← hc]
    exact neg_log_eq_integral_resIntegrand (hM.eigenvalues_pos i)
  calc cfc (fun x => -Real.log x) M
      = diagConjCLM (hM.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (fun i => -Real.log (hM.1.eigenvalues i)) := cfc_eq_diagConj M hM.1 (fun x => -Real.log x)
    _ = diagConjCLM (hM.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (∫ t in Ioi (0 : ℝ), (fun i => resIntegrand t (hM.1.eigenvalues i))) := by rw [hvec]
    _ = ∫ t in Ioi (0 : ℝ), diagConjCLM (hM.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (fun i => resIntegrand t (hM.1.eigenvalues i)) :=
        (ContinuousLinearMap.integral_comp_comm _ hint).symm
    _ = ∫ t in Ioi (0 : ℝ), cfc (resIntegrand t) M := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        exact (cfc_eq_diagConj M hM.1 (resIntegrand t)).symm

/-- The resolvent-integrand family `t ↦ cfc (resIntegrand t) M` is integrable on `(0, ∞)`. -/
lemma integrableOn_cfc_resIntegrand {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.PosDef) :
    IntegrableOn (fun t => cfc (resIntegrand t) M) (Ioi (0 : ℝ)) := by
  have hint := integrableOn_eigenVec M hM
  have heq : (fun t => cfc (resIntegrand t) M)
      = fun t => diagConjCLM (hM.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (fun i => resIntegrand t (hM.1.eigenvalues i)) := by
    funext t; exact cfc_eq_diagConj M hM.1 (resIntegrand t)
  rw [heq]
  exact ContinuousLinearMap.integrable_comp _ hint

/-! ## Resolvent form of the integrand and scalar shift positivity -/

/-- The resolvent form of `cfc (resIntegrand t)`: for positive definite `M` and `t > 0`,
`cfc (resIntegrand t) M = (M + t)⁻¹ − (1+t)⁻¹`. -/
lemma cfc_resIntegrand_eq {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.PosDef) {t : ℝ}
    (ht : 0 < t) :
    cfc (resIntegrand t) M
      = (M + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹
        - algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) ((1 + t)⁻¹) := by
  have hsa : IsSelfAdjoint M := hM.1
  have hne : ∀ x ∈ spectrum ℝ M, x + t ≠ 0 := by
    intro x hx
    rw [hM.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hM.eigenvalues_pos i
    positivity
  have hcont_add : ContinuousOn (fun x : ℝ => x + t) (spectrum ℝ M) := by fun_prop
  have hcont_inv : ContinuousOn (fun x : ℝ => (x + t)⁻¹) (spectrum ℝ M) :=
    hcont_add.inv₀ hne
  have hadd : cfc (fun x : ℝ => x + t) M = M + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t := by
    have h1 := cfc_add_const t (fun y : ℝ => y) M (continuousOn_id' (spectrum ℝ M)) hsa
    rw [cfc_id' ℝ M] at h1
    simpa using h1
  have hinv : cfc (fun x : ℝ => (x + t)⁻¹) M
      = (M + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ := by
    rw [cfc_inv (fun x => x + t) M hne hcont_add hsa, hadd, nonsing_inv_eq_ringInverse]
  rw [show (resIntegrand t : ℝ → ℝ) = fun x => (x + t)⁻¹ - (1 + t)⁻¹ from rfl,
    cfc_sub (fun x => (x + t)⁻¹) (fun _ => (1 + t)⁻¹) M hcont_inv continuousOn_const, hinv,
    cfc_const (1 + t)⁻¹ M]

/-- The scalar shift `algebraMap ℝ … t = t • 1` is positive definite for `t > 0`. -/
lemma posDef_algebraMap {N : ℕ} {t : ℝ} (ht : 0 < t) :
    (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t).PosDef := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Matrix.PosDef.one.smul ht

end Oseledets.OperatorEntropy.Lieb
