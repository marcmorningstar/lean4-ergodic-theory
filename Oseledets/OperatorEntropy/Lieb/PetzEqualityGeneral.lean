/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.PetzChannelContraction
import Oseledets.OperatorEntropy.Lieb.ContractionRigiditySkeleton
import Oseledets.OperatorEntropy.Lieb.PetzEqualitySufficiency
import Oseledets.OperatorEntropy.Lieb.PetzKadison

/-!
# Petz equality — sufficiency for a general Kraus channel (issue #28, route b″)

This module clones the *mixed-ancilla sufficiency chain* of `PetzEqualitySufficiency` but with the
**channel contraction** `W = petzWChanVec Λ ρ` (from `PetzChannelContraction`) in place of the
isometric reconciliation `petzWvec`.  For a general Kraus channel `Λ` with all four states faithful
(`ρ, σ, Λρ, Λσ` positive definite), if data processing is saturated
(`D(ρ‖σ) = D(Λρ‖Λσ)`), then the channel adjoint intertwines the modular flows (`IntertwinesIt`),
whence the Petz recovery map reconstructs the input state (`petz σ Λ (Λρ) = ρ`).

## Contraction vs. isometry

The isometric spine `RigidityTail.isometry_resolvent_intertwine_of_neg_log_eq` is replaced by the
contraction spine `ContractionRigiditySkeleton.contraction_resolvent_intertwine_of_neg_log_eq`.  Two
structural adaptations are needed relative to the isometric clone:

* The compression is an **inequality** `Wᴴ Δ W ≤ Δout` (`petzWChanVec_modular_le`), not the exact
  compression of the isometry; the output modular operator `Δout = (Λσ) ⊗ₖ ((Λρ)⁻¹)ᵀ` is a genuinely
  separate operator (not `Wᴴ Δ W`).
* The `-log` **saturation is scalar** (`channel_modular_gap`): the entropy equality gives only the
  equality of the two `-log` modular *quadratic forms* at the output cyclic vector, not the vector
  equation `(Wᴴ (−log Δ) W) ξ = (−log Δout) ξ` (which is unavailable — the whole-space Loewner
  `Wᴴ (−log Δ) W ⪰ −log Δout` fails for a contraction).  The scalar variant
  `contraction_resolvent_intertwine_of_re_eq` sources the vanishing integral from this scalar
  equality directly (the only place the isometric/contraction spines used the vector `hgap`).

## Injectivity caveat

The contraction spine requires the vectorised Petz map to be **injective** (`hWinj`), used to invert
the compression `Wᴴ (Δ+t) W`.  This is *not* automatic from faithfulness of the four states:
for an information-losing channel (e.g. the completely depolarising channel, whose adjoint
`Λ†(Y) = (tr Y / n) · 1` collapses everything onto scalars) the map `petzWChanVec Λ ρ` is far from
injective, even though `Λρ = 1/n` is faithful.  Accordingly the chain below carries `hWinj` as an
explicit hypothesis.  It is satisfiable for injective channels (unitary/isometric embeddings,
partial traces, …); de-hypothesising it in full generality requires a support restriction outside
the current green infrastructure.
-/

open Matrix Real MeasureTheory Set
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

open Oseledets.OperatorEntropy

/-! ## The scalar-sourced contraction rigidity spine (`Fin`-indexed) -/

section FinSkeleton

variable {M N : ℕ}

/-- **Contraction rigidity tail (scalar-sourced resolvent form).**  Identical to
`ContractionRigiditySkeleton.contraction_resolvent_intertwine_of_neg_log_eq`, except the `-log`
saturation is supplied as the *scalar* equality of the two `-log` modular quadratic forms at `ξ`
(`hReEq`) rather than the vector equation `(Wᴴ (−log Δ) W) ξ = (−log Δout) ξ`.  The scalar suffices
because the spine only ever used the vector saturation to certify that the resolvent-gap integral
vanishes. -/
theorem contraction_resolvent_intertwine_of_re_eq (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (Δout : Matrix (Fin N) (Fin N) ℂ) (ξ : Fin N → ℂ)
    (hWinj : Function.Injective W.mulVec) (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ)
    (hReEq : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
              = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) Δout *ᵥ ξ).re) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ) := by
  classical
  have hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0 := contraction_defect_mulVec_eq_zero W ξ hWc hsat
  have hWWξ : (Wᴴ * W) *ᵥ ξ = ξ := by
    have h := hdefect
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  have hregvec : ∀ c : ℝ, (Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c * W) *ᵥ ξ
      = algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) c *ᵥ ξ := by
    intro c
    have hmat : Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c * W = c • (Wᴴ * W) := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [hmat, Matrix.smul_mulVec, hWWξ, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  set LMre : Matrix (Fin M) (Fin M) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (qformCLM (W *ᵥ ξ)) with hLMre
  set LNre : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (qformCLM ξ) with hLNre
  set F : ℝ → ℝ := fun t => LMre (cfc (resIntegrand t) Δ)
    - LNre (cfc (resIntegrand t) Δout) with hF
  have hXt : ∀ t : ℝ, 0 < t → (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t).PosDef :=
    fun t ht => hΔ.add_posSemidef (posDef_algebraMap ht).posSemidef
  have hintM : IntegrableOn (fun t => cfc (resIntegrand t) Δ) (Ioi 0) :=
    integrableOn_cfc_resIntegrand Δ hΔ
  have hintN : IntegrableOn (fun t => cfc (resIntegrand t) Δout) (Ioi 0) :=
    integrableOn_cfc_resIntegrand Δout hΔout
  have hg1int : IntegrableOn (fun t => LMre (cfc (resIntegrand t) Δ)) (Ioi 0) :=
    LMre.integrable_comp hintM
  have hg2int : IntegrableOn (fun t => LNre (cfc (resIntegrand t) Δout)) (Ioi 0) :=
    LNre.integrable_comp hintN
  have hFeq : ∀ t : ℝ, 0 < t → F t
      = (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
          - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)).re := by
    intro t ht
    have hLMval : LMre (cfc (resIntegrand t) Δ)
        = (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W) *ᵥ ξ)).re
          - (star ξ ⬝ᵥ (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) ((1 + t)⁻¹) *ᵥ ξ)).re := by
      rw [hLMre, ContinuousLinearMap.comp_apply, cfc_resIntegrand_eq Δ hΔ ht,
        map_sub, qformCLM_conj, qformCLM_conj, hregvec ((1 + t)⁻¹),
        Complex.reCLM_apply, Complex.sub_re]
    have hLNval : LNre (cfc (resIntegrand t) Δout)
        = (star ξ ⬝ᵥ ((Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ)).re
          - (star ξ ⬝ᵥ (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) ((1 + t)⁻¹) *ᵥ ξ)).re := by
      rw [hLNre, ContinuousLinearMap.comp_apply, cfc_resIntegrand_eq Δout hΔout ht,
        map_sub, qformCLM_apply, qformCLM_apply, Complex.reCLM_apply, Complex.sub_re]
    simp only [hF]
    rw [hLMval, hLNval, sub_mulVec, dotProduct_sub, Complex.sub_re]
    ring
  have hFnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F t := by
    intro t ht
    rw [hFeq t ht]
    have hX := hXt t ht
    have hY : (Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W).PosDef :=
      hX.conjTranspose_mul_mul_same hWinj
    have hOut : (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t).PosDef :=
      hΔout.add_posSemidef (posDef_algebraMap ht).posSemidef
    have hle : Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W
        ≤ Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t :=
      compression_shift_le W Δ Δout hWc hcompLe ht
    have hBps : ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W)⁻¹
        - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹).PosSemidef :=
      Matrix.le_iff.mp (posDef_inv_le_inv hY hOut hle)
    have hA : 0 ≤ (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
        - (Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W)⁻¹) *ᵥ ξ)).re :=
      contraction_resolvent_gap_nonneg W ξ hWinj hX hdefect
    have hB : 0 ≤ (star ξ ⬝ᵥ (((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W)⁻¹
        - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)).re :=
      (Complex.nonneg_iff.mp (hBps.dotProduct_mulVec_nonneg ξ)).1
    have hGsplit : star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
          - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)
        = star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
            - (Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W)⁻¹) *ᵥ ξ)
          + star ξ ⬝ᵥ (((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W)⁻¹
              - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ) := by
      rw [← dotProduct_add, ← add_mulVec]
      congr 2
      abel
    rw [hGsplit, Complex.add_re]
    exact add_nonneg hA hB
  have hFcont : ContinuousOn F (Ioi 0) := by
    simp only [hF]
    exact (LMre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand Δ hΔ)).sub
      (LNre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand Δout hΔout))
  have hFint : IntegrableOn F (Ioi 0) := by simp only [hF]; exact hg1int.sub hg2int
  have hInt0 : ∫ t in Ioi 0, F t = 0 := by
    have hI1 : ∫ t in Ioi 0, LMre (cfc (resIntegrand t) Δ)
        = LMre (cfc (fun x => -Real.log x) Δ) := by
      rw [LMre.integral_comp_comm hintM, ← cfc_neg_log_eq_integral Δ hΔ]
    have hI2 : ∫ t in Ioi 0, LNre (cfc (resIntegrand t) Δout)
        = LNre (cfc (fun x => -Real.log x) Δout) := by
      rw [LNre.integral_comp_comm hintN, ← cfc_neg_log_eq_integral Δout hΔout]
    have hLeq : LMre (cfc (fun x => -Real.log x) Δ) = LNre (cfc (fun x => -Real.log x) Δout) := by
      rw [hLMre, hLNre, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        qformCLM_conj, qformCLM_apply, Complex.reCLM_apply, Complex.reCLM_apply]
      exact hReEq
    simp only [hF]
    rw [integral_sub hg1int hg2int, hI1, hI2, hLeq, sub_self]
  have hae0 : F =ᵐ[volume.restrict (Ioi 0)] 0 := by
    have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi 0)] F :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hFnn)
    exact (setIntegral_eq_zero_iff_of_nonneg_ae hnn_ae hFint).mp hInt0
  have hFzero : Set.EqOn F 0 (Ioi 0) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae0 isOpen_Ioi hFcont continuousOn_const
  intro t ht
  have hGzero : (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
      - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)).re = 0 := by
    rw [← hFeq t ht]; exact hFzero ht
  exact contraction_resolvent_perT_intertwine W Δ Δout ξ hWinj hWc hΔ hΔout hcompLe hdefect ht
    hGzero

end FinSkeleton

/-! ## The scalar `-log` modular gap for the channel contraction -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Channel `-log` modular gap (scalar).**  For a Kraus channel `Λ` with all four states faithful,
if data processing is saturated (`D(ρ‖σ) = D(Λρ‖Λσ)`), then the two `-log` modular quadratic forms
agree at the output cyclic vector `ξ = vec((Λρ)^{1/2})`:

`Re ⟪ξ, Wᴴ (−log Δ) W ξ⟫ = Re ⟪ξ, (−log Δout) ξ⟫`,

with `W = petzWChanVec Λ ρ`, `Δ = σ ⊗ₖ (ρ⁻¹)ᵀ`, `Δout = (Λσ) ⊗ₖ ((Λρ)⁻¹)ᵀ`.  The left form is
`D(ρ‖σ)` (via `qform_conj`, `petzWChan_cyclic`, `kronForm_re_eq_relEntropy`); the right is
`D(Λρ‖Λσ)`. -/
theorem channel_modular_gap (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    (star (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
        ⬝ᵥ ((petzWChanVec Λ ρ)ᴴ * cfc (fun x => -Real.log x) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ)
              * petzWChanVec Λ ρ) *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))).re
      = (star (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
        ⬝ᵥ cfc (fun x => -Real.log x) ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ)
              *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))).re := by
  rw [qform_conj (petzWChanVec Λ ρ)
        (cfc (fun x => -Real.log x) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ))
        (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))),
      petzWChan_cyclic Λ ρ hΛρ,
      kronForm_re_eq_relEntropy ρ σ hρ hσ,
      kronForm_re_eq_relEntropy (Λ.toDM ρ) (Λ.toDM σ) hΛρ hΛσ]
  exact hEq

/-! ## The scalar-sourced contraction rigidity, at arbitrary finite index -/

/-- **Contraction rigidity (general square index).**  The `Fin`-indexed scalar spine
`contraction_resolvent_intertwine_of_re_eq` transported to an arbitrary finite square index type
`p` via the `Fintype.equivFin` reindexing. -/
lemma contraction_resolvent_intertwine_general {p : Type*} [Fintype p] [DecidableEq p]
    (W Δ Δout : Matrix p p ℂ) (ξ : p → ℂ)
    (hWinj : Function.Injective W.mulVec) (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ)
    (hReEq : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
              = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) Δout *ᵥ ξ).re) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Δout + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ ξ) := by
  classical
  intro t ht
  set e : p ≃ Fin (Fintype.card p) := Fintype.equivFin p with he
  set W' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ :=
    W.submatrix e.symm e.symm with hW'def
  set Δ' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ :=
    Δ.submatrix e.symm e.symm with hΔ'def
  set Δout' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ :=
    Δout.submatrix e.symm e.symm with hΔout'def
  set ξ' : Fin (Fintype.card p) → ℂ := ξ ∘ e.symm with hξ'def
  have hW'H : W'ᴴ = Wᴴ.submatrix e.symm e.symm := by rw [hW'def, conjTranspose_submatrix]
  have hcompS : ∀ S : Matrix p p ℂ,
      W'ᴴ * S.submatrix e.symm e.symm * W' = (Wᴴ * S * W).submatrix e.symm e.symm := by
    intro S
    rw [hW'H, hW'def, submatrix_mul_equiv, submatrix_mul_equiv]
  have hW'W' : W'ᴴ * W' = (Wᴴ * W).submatrix e.symm e.symm := by
    rw [hW'H, hW'def, submatrix_mul_equiv]
  have hmulVecQ : ∀ A : Matrix p p ℂ, A.submatrix e.symm e.symm *ᵥ ξ' = (A *ᵥ ξ) ∘ e.symm := by
    intro A
    rw [hξ'def, submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hmulVecP : ∀ (A : Matrix p p ℂ) (v : p → ℂ),
      A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
    intro A v
    rw [submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hmulVecWq : ∀ u : p → ℂ, W' *ᵥ (u ∘ e.symm) = (W *ᵥ u) ∘ e.symm := by
    intro u
    rw [hW'def, submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hWξ : W' *ᵥ ξ' = (W *ᵥ ξ) ∘ e.symm := by rw [hξ'def]; exact hmulVecWq ξ
  have hdot : ∀ u v : p → ℂ, star (u ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = star u ⬝ᵥ v := by
    intro u v
    simp only [dotProduct, Pi.star_apply, Function.comp_apply]
    exact Equiv.sum_comp e.symm (fun j => star (u j) * v j)
  have hsubeq : ∀ A B : Matrix p p ℂ,
      A.submatrix e.symm e.symm - B.submatrix e.symm e.symm = (A - B).submatrix e.symm e.symm := by
    intro A B; ext i j; simp [Matrix.submatrix_apply, Matrix.sub_apply]
  have hΔ'pd : Δ'.PosDef := by rw [hΔ'def]; exact hΔ.submatrix e.symm.injective
  have hΔout'pd : Δout'.PosDef := by rw [hΔout'def]; exact hΔout.submatrix e.symm.injective
  have hW'inj : Function.Injective W'.mulVec := by
    intro a b hab
    have hab' : W' *ᵥ a = W' *ᵥ b := hab
    have ha : a = (a ∘ e) ∘ e.symm := by funext i; simp [Function.comp_apply]
    have hb : b = (b ∘ e) ∘ e.symm := by funext i; simp [Function.comp_apply]
    have hcomp : (W *ᵥ (a ∘ e)) ∘ e.symm = (W *ᵥ (b ∘ e)) ∘ e.symm := by
      rw [← hmulVecWq (a ∘ e), ← hmulVecWq (b ∘ e), ← ha, ← hb]; exact hab'
    have h2 : W *ᵥ (a ∘ e) = W *ᵥ (b ∘ e) := by
      funext i; have := congrFun hcomp (e i); simpa [Function.comp_apply] using this
    have h3 : a ∘ e = b ∘ e := hWinj h2
    funext i; have := congrFun h3 (e.symm i); simpa [Function.comp_apply] using this
  have hW'c : W'ᴴ * W' ≤ 1 := by
    rw [Matrix.le_iff]
    have h := (Matrix.le_iff.mp hWc).submatrix e.symm
    have heq : (1 : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) - W'ᴴ * W'
        = (1 - Wᴴ * W).submatrix e.symm e.symm := by
      rw [hW'W', ← hsubeq 1 (Wᴴ * W), Matrix.submatrix_one_equiv]
    rw [heq]; exact h
  have hcompLe' : W'ᴴ * Δ' * W' ≤ Δout' := by
    rw [Matrix.le_iff]
    have h := (Matrix.le_iff.mp hcompLe).submatrix e.symm
    have heq : Δout' - W'ᴴ * Δ' * W' = (Δout - Wᴴ * Δ * W).submatrix e.symm e.symm := by
      rw [hΔout'def, hΔ'def, hcompS Δ, hsubeq]
    rw [heq]; exact h
  have hsat' : star (W' *ᵥ ξ') ⬝ᵥ (W' *ᵥ ξ') = star ξ' ⬝ᵥ ξ' := by
    rw [hWξ, hξ'def, hdot (W *ᵥ ξ) (W *ᵥ ξ), hdot ξ ξ]; exact hsat
  have hcfcΔ : cfc (fun x => -Real.log x) Δ'
      = (cfc (fun x => -Real.log x) Δ).submatrix e.symm e.symm := by
    have hlog : ContinuousOn (fun x => -Real.log x) (spectrum ℝ Δ) :=
      (Matrix.finite_real_spectrum (A := Δ)).continuousOn _
    have hbridge : ∀ X : Matrix p p ℂ, eqvFin p X = X.submatrix e.symm e.symm := fun _ => rfl
    have hE := eqvFin_cfc (fun x => -Real.log x) hΔ.1 hlog
    rw [hbridge, hbridge] at hE
    rw [hΔ'def]; exact hE.symm
  have hcfcΔout : cfc (fun x => -Real.log x) Δout'
      = (cfc (fun x => -Real.log x) Δout).submatrix e.symm e.symm := by
    have hlog : ContinuousOn (fun x => -Real.log x) (spectrum ℝ Δout) :=
      (Matrix.finite_real_spectrum (A := Δout)).continuousOn _
    have hbridge : ∀ X : Matrix p p ℂ, eqvFin p X = X.submatrix e.symm e.symm := fun _ => rfl
    have hE := eqvFin_cfc (fun x => -Real.log x) hΔout.1 hlog
    rw [hbridge, hbridge] at hE
    rw [hΔout'def]; exact hE.symm
  have hqform_reindex : ∀ A : Matrix p p ℂ,
      star ξ' ⬝ᵥ A.submatrix e.symm e.symm *ᵥ ξ' = star ξ ⬝ᵥ A *ᵥ ξ := by
    intro A
    rw [hmulVecQ A, hξ'def]; exact hdot ξ (A *ᵥ ξ)
  have hReEq' : (star ξ' ⬝ᵥ (W'ᴴ * cfc (fun x => -Real.log x) Δ' * W') *ᵥ ξ').re
      = (star ξ' ⬝ᵥ cfc (fun x => -Real.log x) Δout' *ᵥ ξ').re := by
    rw [hcfcΔ, hcompS (cfc (fun x => -Real.log x) Δ), hcfcΔout,
      hqform_reindex (Wᴴ * cfc (fun x => -Real.log x) Δ * W),
      hqform_reindex (cfc (fun x => -Real.log x) Δout)]
    exact hReEq
  have hFin := contraction_resolvent_intertwine_of_re_eq W' Δ' Δout' ξ'
    hW'inj hW'c hΔ'pd hΔout'pd hcompLe' hsat' hReEq' t ht
  have hΔam : Δ' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t
      = (Δ + algebraMap ℝ (Matrix p p ℂ) t).submatrix e.symm e.symm := by
    rw [hΔ'def]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Algebra.algebraMap_eq_smul_one,
      Matrix.one_apply, Matrix.smul_apply]
  have hΔoutam : Δout' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t
      = (Δout + algebraMap ℝ (Matrix p p ℂ) t).submatrix e.symm e.symm := by
    rw [hΔout'def]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Algebra.algebraMap_eq_smul_one,
      Matrix.one_apply, Matrix.smul_apply]
  have hLtrans : (Δ' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t)⁻¹
        *ᵥ (W' *ᵥ ξ')
      = ((Δ + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)) ∘ e.symm := by
    rw [hΔam, inv_submatrix_equiv, hWξ, hmulVecP]
  have hRtrans : W' *ᵥ ((Δout'
          + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t)⁻¹ *ᵥ ξ')
      = (W *ᵥ ((Δout + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ ξ)) ∘ e.symm := by
    rw [hΔoutam, inv_submatrix_equiv, hmulVecQ, hmulVecWq]
  rw [hLtrans, hRtrans] at hFin
  funext i
  have hi := congrFun hFin (e i)
  simpa [Function.comp_def, Equiv.symm_apply_apply] using hi

/-- **Contraction cfc-intertwining (general square index).**  Under the scalar `-log` saturation
`hReEq`, the contraction `W` intertwines every continuous function of the modular operator:
`W (cfc g Δout ξ) = cfc g Δ (W ξ)`.  The resolvent intertwining
(`contraction_resolvent_intertwine_general`) is upgraded via `exists_resolvent_combo`. -/
lemma contraction_cfc_intertwine {p : Type*} [Fintype p] [DecidableEq p]
    (W Δ Δout : Matrix p p ℂ) (ξ : p → ℂ)
    (hWinj : Function.Injective W.mulVec) (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ)
    (hReEq : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
              = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) Δout *ᵥ ξ).re)
    (g : ℝ → ℝ) :
    W *ᵥ (cfc g Δout *ᵥ ξ) = cfc g Δ *ᵥ (W *ᵥ ξ) := by
  classical
  have hres := contraction_resolvent_intertwine_general W Δ Δout ξ
    hWinj hWc hΔ hΔout hcompLe hsat hReEq
  have hΔpos : ∀ x ∈ spectrum ℝ Δ, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos Δ hΔ.1).mp hΔ.isStrictlyPositive x hx
  have hΔoutpos : ∀ x ∈ spectrum ℝ Δout, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos Δout hΔout.1).mp
      hΔout.isStrictlyPositive x hx
  have hUpos : ∀ i : ↥(spectrum ℝ Δ ∪ spectrum ℝ Δout), 0 < (i : ℝ) := by
    rintro ⟨x, hx | hx⟩
    · exact hΔpos x hx
    · exact hΔoutpos x hx
  haveI : Finite ↥(spectrum ℝ Δ ∪ spectrum ℝ Δout) :=
    ((Matrix.finite_real_spectrum (A := Δ)).union
      (Matrix.finite_real_spectrum (A := Δout))).to_subtype
  obtain ⟨c, hc⟩ := exists_resolvent_combo
    (ι := ↥(spectrum ℝ Δ ∪ spectrum ℝ Δout))
    (fun i => (i : ℝ)) Subtype.coe_injective hUpos (fun i => ((g (i : ℝ) : ℂ)))
  have hcombo : ∀ y ∈ spectrum ℝ Δ ∪ spectrum ℝ Δout,
      g y = ∑ t ∈ c.support, (c t).re * (y + (t : ℝ))⁻¹ := by
    intro y hy
    have hci := hc ⟨y, hy⟩
    dsimp only at hci
    have hre := congrArg Complex.re hci
    rw [Complex.ofReal_re, Complex.re_sum] at hre
    rw [hre]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hz : ((y : ℂ) + ((t : ℝ) : ℂ)) = (((y + (t : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [hz, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hL : W *ᵥ (cfc g Δout *ᵥ ξ)
      = ∑ t ∈ c.support, (c t).re •
          (W *ᵥ ((Δout + algebraMap ℝ (Matrix p p ℂ) (t : ℝ))⁻¹ *ᵥ ξ)) := by
    rw [cfc_eq_resolvent_combo g Δout hΔout c _ Set.subset_union_right hcombo,
      Matrix.sum_mulVec, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hR : cfc g Δ *ᵥ (W *ᵥ ξ)
      = ∑ t ∈ c.support, (c t).re •
          ((Δ + algebraMap ℝ (Matrix p p ℂ) (t : ℝ))⁻¹ *ᵥ (W *ᵥ ξ)) := by
    rw [cfc_eq_resolvent_combo g Δ hΔ c _ Set.subset_union_left hcombo, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.smul_mulVec]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hres (t : ℝ) t.2]

/-! ## The channel unitary-power intertwining and the `it`-cocycle intertwining -/

/-- **Channel unitary-power intertwining.**  Under entropy saturation (and injectivity of the
channel Petz map), the contraction intertwines the unitary power of the modular operator on the
output cyclic vector:
`W (Δout^{it} ξ) = Δ^{it} (W ξ)`, with `W ξ = vec(ρ^{1/2})`. -/
theorem channel_upow_intertwine (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hWinj : Function.Injective (petzWChanVec Λ ρ).mulVec)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) (t : ℝ)
    (hΔoutpd : ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ).PosDef)
    (hΔpd : (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ).PosDef) :
    petzWChanVec Λ ρ *ᵥ (upow hΔoutpd t *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
      = upow hΔpd t *ᵥ vec (ρ.val ^ (1 / 2 : ℝ)) := by
  have hWc := petzWChanVec_contraction Λ ρ hρ hΛρ
  have hcompLe := petzWChanVec_modular_le Λ ρ σ hρ hσ hΛρ hΛσ
  have hsat := petzWChan_cyclic_norm Λ ρ hρ hΛρ
  have hReEq := channel_modular_gap Λ ρ σ hρ hσ hΛρ hΛσ hEq
  have hIc := contraction_cfc_intertwine (petzWChanVec Λ ρ) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ)
    ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ) (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
    hWinj hWc hΔpd hΔoutpd hcompLe hsat hReEq (fun x => Real.cos (t * Real.log x))
  have hIs := contraction_cfc_intertwine (petzWChanVec Λ ρ) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ)
    ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ) (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
    hWinj hWc hΔpd hΔoutpd hcompLe hsat hReEq (fun x => Real.sin (t * Real.log x))
  rw [petzWChan_cyclic Λ ρ hΛρ] at hIc hIs
  have hu1 : upow hΔoutpd t = cpow hΔoutpd ((t : ℂ) * Complex.I) := rfl
  have hu2 : upow hΔpd t = cpow hΔpd ((t : ℂ) * Complex.I) := rfl
  rw [hu1, hu2, cpow_eq_cfc_cos_sin hΔoutpd t, cpow_eq_cfc_cos_sin hΔpd t]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hIc, hIs]

/-- **Channel `it`-cocycle intertwining (`IntertwinesIt`).**  Under entropy saturation
`D(ρ‖σ) = D(Λρ‖Λσ)` and injectivity of `petzWChanVec Λ ρ`, the channel adjoint intertwines the
modular `it`-flows: `Λ†((Λρ)^{it}(Λσ)^{-it}) = ρ^{it} σ^{-it}` for all `t`.  Read off *directly*
(the vectorised Petz map already contains `Λ†`, so no ampliation is needed). -/
theorem channel_equality_imp_intertwinesIt (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hWinj : Function.Injective (petzWChanVec Λ ρ).mulVec)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    IntertwinesIt hρ hσ hΛρ hΛσ := by
  intro t
  have hρinv : (ρ.val ^ (-1 : ℝ)).PosDef :=
    (IsStrictlyPositive.rpow ρ.val (-1) hρ.isStrictlyPositive).posDef
  have hΛρinv : ((Λ.toDM ρ).val ^ (-1 : ℝ)).PosDef :=
    (IsStrictlyPositive.rpow (Λ.toDM ρ).val (-1) hΛρ.isStrictlyPositive).posDef
  have hΔpd : (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ).PosDef := hσ.kronecker hρinv.transpose
  have hΔoutpd : ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ).PosDef :=
    hΛσ.kronecker hΛρinv.transpose
  have hstar := channel_upow_intertwine Λ ρ σ hρ hσ hΛρ hΛσ hWinj hEq t hΔoutpd hΔpd
  rw [modArg_upow_mulVec hΛσ hΛρ hΔoutpd t ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)),
      modArg_upow_mulVec hσ hρ hΔpd t (ρ.val ^ (1 / 2 : ℝ)),
      ← vec_petzWChan] at hstar
  have hbase : petzWChan Λ ρ (upow hΛσ t * (Λ.toDM ρ).val ^ (1 / 2 : ℝ) * upow hΛρ (-t))
      = upow hσ t * ρ.val ^ (1 / 2 : ℝ) * upow hρ (-t) := by
    apply Matrix.ext
    intro i j
    have := congrFun hstar (i, j)
    simpa only [vec_apply] using this
  -- collapse the `(Λρ)^{±1/2}` twist on the input column and commute `ρ^{1/2}`
  have hΛρcol : upow hΛσ t * (Λ.toDM ρ).val ^ (1 / 2 : ℝ) * upow hΛρ (-t)
          * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ)
        = upow hΛσ t * upow hΛρ (-t) := by
    rw [rpow_eq_cpow_ofReal hΛρ (1 / 2), rpow_eq_cpow_ofReal hΛρ (-(1 / 2)),
        show upow hΛρ (-t) = cpow hΛρ (((-t : ℝ) : ℂ) * Complex.I) from rfl]
    rw [show upow hΛσ t * cpow hΛρ ((1 / 2 : ℝ) : ℂ) * cpow hΛρ (((-t : ℝ) : ℂ) * Complex.I)
            * cpow hΛρ ((-(1 / 2) : ℝ) : ℂ)
          = upow hΛσ t * (cpow hΛρ ((1 / 2 : ℝ) : ℂ) * cpow hΛρ (((-t : ℝ) : ℂ) * Complex.I)
            * cpow hΛρ ((-(1 / 2) : ℝ) : ℂ)) from by noncomm_ring,
        cpow_mul_cpow, cpow_mul_cpow]
    congr 2
    push_cast; ring
  have hRHScol : upow hσ t * ρ.val ^ (1 / 2 : ℝ) * upow hρ (-t)
        = upow hσ t * upow hρ (-t) * ρ.val ^ (1 / 2 : ℝ) := by
    rw [rpow_eq_cpow_ofReal hρ (1 / 2),
        show upow hρ (-t) = cpow hρ (((-t : ℝ) : ℂ) * Complex.I) from rfl,
        mul_assoc, mul_assoc, cpow_mul_cpow, cpow_mul_cpow]
    congr 2
    push_cast; ring
  unfold petzWChan at hbase
  rw [hΛρcol, hRHScol] at hbase
  -- cancel `ρ^{1/2}`
  have hsqrtInv : ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ) = 1 :=
    CFC.rpow_mul_rpow_neg (1 / 2) hρ.isStrictlyPositive
  have hcancel : Λ.adj (upow hΛσ t * upow hΛρ (-t)) = upow hσ t * upow hρ (-t) :=
    calc Λ.adj (upow hΛσ t * upow hΛρ (-t))
        = Λ.adj (upow hΛσ t * upow hΛρ (-t))
            * (ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ)) := by rw [hsqrtInv, mul_one]
      _ = Λ.adj (upow hΛσ t * upow hΛρ (-t))
            * ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ) := by rw [mul_assoc]
      _ = upow hσ t * upow hρ (-t) * ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ) := by rw [hbase]
      _ = upow hσ t * upow hρ (-t)
            * (ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ)) := by rw [mul_assoc]
      _ = upow hσ t * upow hρ (-t) := by rw [hsqrtInv, mul_one]
  calc Λ.adj (upow hΛρ t * upow hΛσ (-t))
      = Λ.adj (star (upow hΛσ t * upow hΛρ (-t))) := by
        rw [star_mul, star_upow, star_upow, neg_neg]
    _ = star (Λ.adj (upow hΛσ t * upow hΛρ (-t))) := by
        simp only [Matrix.star_eq_conjTranspose]; exact Λ.adj_conjTranspose _
    _ = star (upow hσ t * upow hρ (-t)) := by rw [hcancel]
    _ = upow hρ t * upow hσ (-t) := by rw [star_mul, star_upow, star_upow, neg_neg]

/-- **General Petz recovery from equality (issue #28).**  For a Kraus channel `Λ` with all four
states faithful and an injective vectorised Petz map, saturation of data processing
`D(ρ‖σ) = D(Λρ‖Λσ)` forces the Petz recovery map to reconstruct the input state:
`petz σ Λ (Λ ρ) = ρ`. -/
theorem petz_equality_recovery_general (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hWinj : Function.Injective (petzWChanVec Λ ρ).mulVec)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    petz σ Λ (Λ.toDM ρ).val = ρ.val :=
  intertwinesIt_imp_recovery ρ σ Λ hρ hσ hΛρ hΛσ
    (channel_equality_imp_intertwinesIt Λ ρ σ hρ hσ hΛρ hΛσ hWinj hEq)

end Oseledets.OperatorEntropy.Lieb

end
