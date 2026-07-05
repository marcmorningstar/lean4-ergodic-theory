/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessing

/-!
# Issue #22 — the data-processing inequality for ARBITRARY input states

The faithful data-processing inequality `relEntropyMonotone_partialTrace_faithful`
(`DataProcessing.lean`) requires the first state `ρ` to be positive **definite**.  This module
removes that restriction, discharging the exact target `Prop`

`RelEntropyMonotoneUnderPartialTrace` : partial-trace monotonicity of Umegaki relative entropy for
*arbitrary* `ρ` (only the second argument `σ` must be faithful).

The bridge is **continuity of the relative entropy in its first argument**, obtained through a
Weierstrass polynomial approximation of the von Neumann entropy: for a Hermitian matrix `M` with
spectrum in `[0,1]` the entropy term `Tr(M · log M) = ∑ᵢ λᵢ log λᵢ` is a uniform-on-density-matrices
limit of the *polynomial* traces `Tr(p(M))` (which are manifestly continuous in `M`), so the entropy
term — and hence `M ↦ relEntropyMat M σ` — is continuous on the (compact) set of density matrices.

Given this, the general case follows by an `ε`-regularization: applying the faithful inequality to
`ρ_ε := (1-ε)ρ + ε·(𝟙/d)` (positive definite for `ε ∈ (0,1]`) and letting `ε → 0⁺`, both sides
converge — by the continuity above and the continuity of the partial trace — to the values for `ρ`.

## Main results

* `ErgodicTheory.OperatorEntropy.Lieb.trace_cfc_re_eq_sum` — `Tr(f(M)) = ∑ᵢ f(λᵢ(M))`
  for Hermitian `M`.
* `ErgodicTheory.OperatorEntropy.Lieb.continuousOn_traceMulCfcLog` — the entropy term is
  continuous on
  the density matrices (the Weierstrass step).
* `ErgodicTheory.OperatorEntropy.Lieb.relEntropyMonotone_partialTrace` — the target `Prop`.
-/

open Matrix Real Polynomial Filter Topology
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Density-matrix mixtures and continuity of the partial trace -/

/-- The convex mixture `(1-ε)·ρ + ε·τ` of two density matrices, again a density matrix. -/
def DensityMatrix.mix (ρ τ : DensityMatrix n) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    DensityMatrix n where
  val := (1 - ε) • ρ.val + ε • τ.val
  posSemidef := (ρ.posSemidef.smul (by linarith)).add (τ.posSemidef.smul h0)
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.trace_one, τ.trace_one]
    simp only [Complex.real_smul, mul_one]
    push_cast
    ring

/-- For `ε ∈ (0,1]` the mixture with a faithful state is positive definite. -/
lemma mix_posDef {ρ τ : DensityMatrix n} (hτ : τ.val.PosDef) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (ρ.mix τ ε h0.le h1).val.PosDef :=
  Matrix.PosDef.posSemidef_add (ρ.posSemidef.smul (by linarith)) (hτ.smul h0)

/-- The right partial trace is continuous as a map on raw matrices. -/
lemma continuous_partialTraceRight {nA nB : Type*} [Fintype nB] :
    Continuous (partialTraceRight : Matrix (nA × nB) (nA × nB) ℂ → Matrix nA nA ℂ) := by
  refine continuous_matrix fun i i' => ?_
  simp only [partialTraceRight_apply]
  exact continuous_finsetSum _ fun j _ => continuous_id.matrix_elem (i, j) (i', j)

/-- The eigenvalues of a density-matrix value lie in `[0,1]`. -/
lemma eigenvalues_mem_Icc {M : Matrix n n ℂ} (hpsd : M.PosSemidef) (htr : M.trace = 1) (i : n) :
    hpsd.1.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hpsd.eigenvalues_nonneg i, ?_⟩
  have hsum : ∑ j, hpsd.1.eigenvalues j = 1 := by
    have h := hpsd.1.trace_eq_sum_eigenvalues
    rw [htr] at h
    have h2 : ((∑ j, hpsd.1.eigenvalues j : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; push_cast; simpa using h.symm
    exact_mod_cast h2
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hpsd.eigenvalues_nonneg j) (Finset.mem_univ i)

end ErgodicTheory.OperatorEntropy

namespace ErgodicTheory.OperatorEntropy.Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Trace of a Hermitian functional calculus as a sum over eigenvalues -/

/-- **Trace of the continuous functional calculus.**  For a Hermitian matrix `M` and any function
`g`, the trace of `f(M)` is the sum of `g` over the eigenvalues of `M`. -/
lemma trace_cfc_re_eq_sum {M : Matrix n n ℂ} (hM : M.IsHermitian) (g : ℝ → ℝ) :
    (cfc g M).trace.re = ∑ i, g (hM.eigenvalues i) := by
  rw [hM.cfc_eq g]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  exact Complex.ofReal_re _

/-- **Entropy integrand as a functional calculus.**  For Hermitian `M`,
`M · log M = (x ↦ x log x)(M)`. -/
lemma mul_cfc_log {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M * cfc Real.log M = cfc (fun x => x * Real.log x) M := by
  have hsa : IsSelfAdjoint M := hM
  have hfin : (spectrum ℝ M).Finite := by
    rw [hM.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  have hcont : ContinuousOn Real.log (spectrum ℝ M) := hfin.continuousOn _
  calc M * cfc Real.log M
      = cfc (id : ℝ → ℝ) M * cfc Real.log M := by rw [cfc_id ℝ M hsa]
    _ = cfc (fun x => id x * Real.log x) M :=
        (cfc_mul id Real.log M continuousOn_id hcont).symm
    _ = cfc (fun x => x * Real.log x) M := rfl

/-! ## The entropy term is continuous on density matrices (Weierstrass) -/

/-- **Continuity of the von Neumann entropy term.**  The map `M ↦ Tr(M · log M).re` is continuous on
the set of density matrices (positive semidefinite, unit trace).  This is the Weierstrass step:
`Tr(M · log M) = ∑ λᵢ log λᵢ` is a uniform-on-density-matrices limit of the *polynomial* traces
`Tr(p(M))`, each of which is continuous in `M`. -/
lemma continuousOn_traceMulCfcLog :
    ContinuousOn (fun M : Matrix n n ℂ => (M * cfc Real.log M).trace.re)
      {M | M.PosSemidef ∧ M.trace = 1} := by
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro u hu
  obtain ⟨ε, εpos, Hε⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => x * Real.log x)
    Real.continuous_mul_log.continuousOn (ε / (Fintype.card n + 1))
    (div_pos εpos (by positivity))
  refine ⟨fun M => (aeval M q).trace.re,
    (Complex.continuous_re.comp
      ((Polynomial.continuous_aeval (A := Matrix n n ℂ) q).matrix_trace)).continuousOn, ?_⟩
  intro M hM
  obtain ⟨hpsd, htr⟩ := hM
  have hHerm := hpsd.1
  have hsa : IsSelfAdjoint M := hHerm
  apply Hε
  simp only [Real.dist_eq]
  rw [mul_cfc_log hHerm, trace_cfc_re_eq_sum hHerm, ← cfc_polynomial q M hsa,
    trace_cfc_re_eq_sum hHerm, ← Finset.sum_sub_distrib]
  have hbound : |∑ i, ((fun x => x * Real.log x) (hHerm.eigenvalues i)
      - Polynomial.eval (hHerm.eigenvalues i) q)| ≤ ∑ _i : n, ε / (Fintype.card n + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have hi := hq (hHerm.eigenvalues i) (eigenvalues_mem_Icc hpsd htr i)
    rw [abs_sub_comm] at hi
    exact le_of_lt hi
  refine lt_of_le_of_lt hbound ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show ((Fintype.card n : ℝ) * (ε / (Fintype.card n + 1)))
      = ((Fintype.card n : ℝ) * ε) / (Fintype.card n + 1) from by ring,
    div_lt_iff₀ (by positivity : (0 : ℝ) < (Fintype.card n : ℝ) + 1)]
  nlinarith [εpos, Nat.cast_nonneg (α := ℝ) (Fintype.card n)]

/-- **Continuity of the relative entropy in its first argument.**  For a fixed faithful state `σ`,
`M ↦ relEntropyMat M σ` is continuous on the set of density matrices. -/
lemma continuousOn_relEntropyMat_left (σ : DensityMatrix n) :
    ContinuousOn (fun M : Matrix n n ℂ => relEntropyMat M σ.val)
      {M | M.PosSemidef ∧ M.trace = 1} := by
  have hL : Continuous (fun M : Matrix n n ℂ => (M * cfc Real.log σ.val).trace.re) :=
    Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)
  have hrw : ∀ M : Matrix n n ℂ, relEntropyMat M σ.val
      = (M * cfc Real.log M).trace.re - (M * cfc Real.log σ.val).trace.re := by
    intro M
    rw [relEntropyMat, mul_sub, Matrix.trace_sub, Complex.sub_re]
  simp only [hrw]
  exact continuousOn_traceMulCfcLog.sub hL.continuousOn

/-! ## The general data-processing inequality -/

set_option maxHeartbeats 800000 in -- heavy defeq elaboration; regularization limit argument
/-- **Data-processing inequality (general case).**  Discharges the target `Prop`: the partial trace
never increases Umegaki relative entropy, for an *arbitrary* first state `ρ` (faithful `σ`). -/
theorem relEntropyMonotone_partialTrace : RelEntropyMonotoneUnderPartialTrace := by
  intro nA nE _ _ _ _ ρ σ hσ
  haveI hne : Nonempty (nA × nE) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    haveI := hcon
    have ht := σ.trace_one
    simp only [Matrix.trace, Matrix.diag_apply, Finset.univ_eq_empty, Finset.sum_empty] at ht
    exact one_ne_zero ht.symm
  haveI hnE : Nonempty nE := hne.map Prod.snd
  set τ : DensityMatrix (nA × nE) := DensityMatrix.maximallyMixed with hτdef
  set d := Fintype.card (nA × nE) with hd
  have hdpos : (0 : ℝ) < d := by rw [hd]; exact_mod_cast Fintype.card_pos
  have hτpd : τ.val.PosDef := by
    have hval : τ.val = ((d : ℝ)⁻¹) • (1 : Matrix (nA × nE) (nA × nE) ℂ) := by
      rw [hτdef]; simp only [DensityMatrix.maximallyMixed, ← hd]
    rw [hval]
    have hcx : ((d : ℝ)⁻¹) • (1 : Matrix (nA × nE) (nA × nE) ℂ)
        = diagonal (fun _ => ((d : ℝ)⁻¹ : ℂ)) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
      by_cases h : i = j
      · simp [h, Complex.real_smul]
      · simp [h]
    rw [hcx, Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast inv_pos.mpr hdpos
  have hptrσ : (DensityMatrix.partialTraceRight σ).val.PosDef := posDef_partialTraceRight hσ
  -- Continuity of the two affine paths.
  have hpathR_cont : Continuous (fun ε : ℝ => (1 - ε) • ρ.val + ε • τ.val) :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  -- Eventually-in-`𝓝[>]0` facts.
  have h0ev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (0 : ℝ) < ε :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun _ hx => hx)
  have h1ev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), ε < 1 :=
    ((isOpen_Iio.eventually_mem (by norm_num : (0 : ℝ) ∈ Set.Iio (1 : ℝ))).filter_mono
      nhdsWithin_le_nhds).mono (fun _ hx => hx)
  have hSmemR : ∀ᶠ ε in (𝓝[>] (0 : ℝ)),
      ((1 - ε) • ρ.val + ε • τ.val)
        ∈ {M : Matrix (nA × nE) (nA × nE) ℂ | M.PosSemidef ∧ M.trace = 1} := by
    filter_upwards [h0ev, h1ev] with ε ha hb
    exact ⟨(ρ.mix τ ε ha.le hb.le).posSemidef, (ρ.mix τ ε ha.le hb.le).trace_one⟩
  have hSmemL : ∀ᶠ ε in (𝓝[>] (0 : ℝ)),
      partialTraceRight ((1 - ε) • ρ.val + ε • τ.val)
        ∈ {M : Matrix nA nA ℂ | M.PosSemidef ∧ M.trace = 1} := by
    filter_upwards [h0ev, h1ev] with ε ha hb
    exact ⟨(DensityMatrix.partialTraceRight (ρ.mix τ ε ha.le hb.le)).posSemidef,
      (DensityMatrix.partialTraceRight (ρ.mix τ ε ha.le hb.le)).trace_one⟩
  -- Right-hand-side limit.
  have htRHS : Tendsto (fun ε : ℝ => relEntropyMat ((1 - ε) • ρ.val + ε • τ.val) σ.val)
      (𝓝[>] (0 : ℝ)) (𝓝 (relEntropyMat ρ.val σ.val)) := by
    have hcwa : Tendsto (fun M : Matrix (nA × nE) (nA × nE) ℂ => relEntropyMat M σ.val)
        (𝓝[{M | M.PosSemidef ∧ M.trace = 1}] ρ.val) (𝓝 (relEntropyMat ρ.val σ.val)) :=
      (continuousOn_relEntropyMat_left σ).continuousWithinAt ⟨ρ.posSemidef, ρ.trace_one⟩
    have hpath : Tendsto (fun ε : ℝ => (1 - ε) • ρ.val + ε • τ.val) (𝓝[>] (0 : ℝ))
        (𝓝[{M : Matrix (nA × nE) (nA × nE) ℂ | M.PosSemidef ∧ M.trace = 1}] ρ.val) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, hSmemR⟩
      have h := hpathR_cont.tendsto 0
      simp only [sub_zero, one_smul, zero_smul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact hcwa.comp hpath
  -- Left-hand-side limit.
  have htLHS : Tendsto (fun ε : ℝ => relEntropyMat (partialTraceRight ((1 - ε) • ρ.val + ε • τ.val))
        (DensityMatrix.partialTraceRight σ).val) (𝓝[>] (0 : ℝ))
      (𝓝 (relEntropyMat (partialTraceRight ρ.val) (DensityMatrix.partialTraceRight σ).val)) := by
    have hcwa : Tendsto
        (fun M : Matrix nA nA ℂ => relEntropyMat M (DensityMatrix.partialTraceRight σ).val)
        (𝓝[{M | M.PosSemidef ∧ M.trace = 1}] (partialTraceRight ρ.val))
        (𝓝 (relEntropyMat (partialTraceRight ρ.val) (DensityMatrix.partialTraceRight σ).val)) :=
      (continuousOn_relEntropyMat_left (DensityMatrix.partialTraceRight σ)).continuousWithinAt
        ⟨(DensityMatrix.partialTraceRight ρ).posSemidef,
          (DensityMatrix.partialTraceRight ρ).trace_one⟩
    have hpath : Tendsto (fun ε : ℝ => partialTraceRight ((1 - ε) • ρ.val + ε • τ.val))
        (𝓝[>] (0 : ℝ))
        (𝓝[{M : Matrix nA nA ℂ | M.PosSemidef ∧ M.trace = 1}] (partialTraceRight ρ.val)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, hSmemL⟩
      have h := (continuous_partialTraceRight.comp hpathR_cont).tendsto 0
      simp only [Function.comp_apply, sub_zero, one_smul, zero_smul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact hcwa.comp hpath
  -- The faithful inequality along the regularized path.
  have hdpi : ∀ᶠ ε in (𝓝[>] (0 : ℝ)),
      relEntropyMat (partialTraceRight ((1 - ε) • ρ.val + ε • τ.val))
          (DensityMatrix.partialTraceRight σ).val
        ≤ relEntropyMat ((1 - ε) • ρ.val + ε • τ.val) σ.val := by
    filter_upwards [h0ev, h1ev] with ε ha hb
    have hfaith := relEntropyMonotone_partialTrace_faithful (ρ.mix τ ε ha.le hb.le) σ
      (mix_posDef hτpd ha hb.le) hσ
    rw [← relEntropyMat_eq_relEntropy _ _ hσ, ← relEntropyMat_eq_relEntropy _ _ hptrσ] at hfaith
    exact hfaith
  -- Pass to the limit and translate back to `relEntropy`.
  rw [← relEntropyMat_eq_relEntropy (DensityMatrix.partialTraceRight ρ)
      (DensityMatrix.partialTraceRight σ) hptrσ, ← relEntropyMat_eq_relEntropy ρ σ hσ]
  exact le_of_tendsto_of_tendsto htLHS htRHS hdpi

end ErgodicTheory.OperatorEntropy.Lieb
