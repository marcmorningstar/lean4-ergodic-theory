/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.PetzSufficiencyClosed
import Oseledets.OperatorEntropy.Lieb.PetzEqualityIntertwine
import Oseledets.OperatorEntropy.Subadditivity

/-!
# Petz equality — sufficiency for the partial-trace channel (issue #28)

This module closes the sufficiency (`⟹`) direction of the finite-dimensional Petz-equality theorem
for the **partial-trace channel** `Λ = Tr_B : Matrix (nA × nB) → Matrix nA` with **faithful dilated
states** `ω, τ : DensityMatrix (nA × nB)` (so that `Tr_B ω`, `Tr_B τ` are also faithful).  This is
the clean core of the reconciliation (`petzW` uses `ω_A = Tr_B ω`): all states are faithful, so
there is no support obstruction.

## The modular convention

The vectorisation bridge `PetzVecBridge` works in the `modArgVec τ ω = τ ⊗ₖ (ω⁻¹)ᵀ` convention
(the vectorised relative modular map `Z ↦ τ Z ω⁻¹`).  Its three identities `petzWvec_isometry`,
`petzWvec_cyclic`, `petzWvec_modular_compression` feed the abstract rigidity spine.  The modular
realisation of the relative entropy in *this* convention is `kronForm_re_eq_relEntropy` below:

`D(ρ‖σ) = Re ⟪vec(ρ^{1/2}), (−log)(σ ⊗ₖ (ρ⁻¹)ᵀ) · vec(ρ^{1/2})⟫`.

## Main results

* `kronForm_re_eq_relEntropy` — the `modArgVec`-convention modular realisation of relative entropy.
* `partialTrace_modular_gap` — the `−log` operator-Jensen gap for `petzWvec ω` annihilates the
  output cyclic vector `vec((Tr_B ω)^{1/2})` under the entropy equality (the analytic linchpin).
* `partialTrace_equality_imp_intertwinesIt` — the terminal audited headline: preservation of the
  Umegaki relative entropy under `Tr_B` forces the channel to intertwine the modular `it`-flows,
  `((Tr_B ω)^{it}(Tr_B τ)^{-it}) ⊗ₖ 1 = ω^{it} τ^{-it}`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

open Oseledets.OperatorEntropy

/-! ## Hilbert–Schmidt inner product in the `vec` picture -/

/-- **The `vec`/Hilbert–Schmidt inner product.** `⟪vec X, vec Y⟫ = Tr (Xᴴ Y)`. -/
lemma vec_dotProduct {m : Type*} [Fintype m] (X Y : Matrix m m ℂ) :
    star (vec X) ⬝ᵥ vec Y = (Xᴴ * Y).trace := by
  simp only [dotProduct, Pi.star_apply, vec_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **Right Kronecker negation.** `A ⊗ₖ (-B) = -(A ⊗ₖ B)`. -/
lemma kron_neg {m : Type*} (A B : Matrix m m ℂ) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  rw [← neg_one_smul ℂ B, Matrix.kronecker_smul, neg_one_smul]

/-! ## The `modArgVec`-convention modular realisation of the relative entropy -/

/-- **Closed form of the `−log` `modArgVec` quadratic form (complex).** For faithful `ρ, σ`,
`⟪vec(ρ^{1/2}), (−log)(σ ⊗ₖ (ρ⁻¹)ᵀ) · vec(ρ^{1/2})⟫ = Tr (ρ (log ρ − log σ))`.

The key computation: `(−log)(σ ⊗ₖ (ρ⁻¹)ᵀ) = −(log σ) ⊗ₖ 1 + 1 ⊗ₖ (log ρ)ᵀ` (via `cfc_log_kron`,
`cfc_log_rpow_neg_one`, `cfc_transpose`), applied to `vec(ρ^{1/2})` by the vec/Kronecker trick, then
read off through the HS inner product and trace cyclicity. -/
lemma kronForm_trace {m : Type*} [Fintype m] [DecidableEq m] {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    star (vec (ρ ^ (1 / 2 : ℝ)))
        ⬝ᵥ cfc (fun x => -Real.log x) (σ ⊗ₖ (ρ ^ (-1 : ℝ))ᵀ) *ᵥ vec (ρ ^ (1 / 2 : ℝ))
      = (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace := by
  set Lρ := cfc Real.log ρ with hLρ
  set Lσ := cfc Real.log σ with hLσ
  set sq := ρ ^ (1 / 2 : ℝ) with hsq
  -- `ρ^{-1}` positive definite (needed for `cfc_log_kron` and `cfc_transpose`)
  have hρinv : (ρ ^ (-1 : ℝ)).PosDef := by
    rw [← CFC.rpow_eq_pow]; exact (IsStrictlyPositive.rpow ρ (-1) hρ.isStrictlyPositive).posDef
  have hρinvT : ((ρ ^ (-1 : ℝ))ᵀ).PosDef := hρinv.transpose
  have hcontlog : ContinuousOn Real.log (spectrum ℝ (ρ ^ (-1 : ℝ))) :=
    (Matrix.finite_real_spectrum (A := ρ ^ (-1 : ℝ))).continuousOn Real.log
  -- STEP 1: the closed form of the `−log` functional calculus.
  have hcfc : cfc (fun x => -Real.log x) (σ ⊗ₖ (ρ ^ (-1 : ℝ))ᵀ)
      = -(Lσ ⊗ₖ (1 : Matrix m m ℂ)) + (1 : Matrix m m ℂ) ⊗ₖ Lρᵀ := by
    rw [cfc_neg Real.log, cfc_log_kron hσ hρinvT, cfc_transpose Real.log hρinv.1 hcontlog]
    rw [show ρ ^ (-1 : ℝ) = CFC.rpow ρ (-1) from CFC.rpow_eq_pow.symm,
      cfc_log_rpow_neg_one hρ, ← hLρ, ← hLσ]
    rw [Matrix.transpose_neg, kron_neg]
    abel
  -- STEP 2: apply to `vec(ρ^{1/2})` via the vec/Kronecker trick.
  rw [hcfc, Matrix.add_mulVec, dotProduct_add]
  have hA : (-(Lσ ⊗ₖ (1 : Matrix m m ℂ))) *ᵥ vec sq = vec (-(Lσ * sq)) := by
    rw [show -(Lσ ⊗ₖ (1 : Matrix m m ℂ)) = (-Lσ) ⊗ₖ ((1 : Matrix m m ℂ)ᵀ) by
        rw [Matrix.transpose_one, neg_kron], ← vec_mul_mul, Matrix.mul_one, Matrix.neg_mul]
  have hB : ((1 : Matrix m m ℂ) ⊗ₖ Lρᵀ) *ᵥ vec sq = vec (sq * Lρ) := by
    rw [← vec_mul_mul, Matrix.one_mul]
  rw [hA, hB, vec_dotProduct, vec_dotProduct]
  -- STEP 3: `(ρ^{1/2})ᴴ = ρ^{1/2}` and `ρ^{1/2} ρ^{1/2} = ρ`, then trace cyclicity.
  have hsqH : sqᴴ = sq := by
    rw [hsq, ← CFC.rpow_eq_pow]
    exact ((IsStrictlyPositive.rpow ρ (1 / 2) hρ.isStrictlyPositive).posDef).1.eq
  have hsqsq : sq * sq = ρ := by
    rw [hsq, ← CFC.rpow_eq_pow, rpowHalfMul hρ]
  rw [hsqH]
  have h1 : (sq * (-(Lσ * sq))).trace = -(ρ * Lσ).trace := by
    rw [Matrix.mul_neg, Matrix.trace_neg]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (sq * Lσ) sq, ← Matrix.mul_assoc, hsqsq]
  have h2 : (sq * (sq * Lρ)).trace = (ρ * Lρ).trace := by
    rw [← Matrix.mul_assoc, hsqsq]
  rw [h1, h2, Matrix.mul_sub, Matrix.trace_sub]
  ring

/-- **The `modArgVec`-convention modular realisation of the relative entropy.** For faithful density
matrices, `D(ρ‖σ) = Re ⟪vec(ρ^{1/2}), (−log)(σ ⊗ₖ (ρ⁻¹)ᵀ) · vec(ρ^{1/2})⟫`. -/
lemma kronForm_re_eq_relEntropy {m : Type*} [Fintype m] [DecidableEq m] (ρ σ : DensityMatrix m)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) :
    (star (vec (ρ.val ^ (1 / 2 : ℝ)))
        ⬝ᵥ cfc (fun x => -Real.log x) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ)
          *ᵥ vec (ρ.val ^ (1 / 2 : ℝ))).re
      = relEntropy ρ σ := by
  rw [kronForm_trace hρ hσ, ← relEntropyMat_eq_relEntropy ρ σ hσ, relEntropyMat]

/-! ## The modular `−log` gap-vanishing at the output cyclic vector -/

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- **Partial-trace modular gap-vanishing** (the analytic linchpin).  For faithful dilated states
`ω, τ : DensityMatrix (nA × nB)` with faithful marginals `Tr_B ω`, `Tr_B τ`, if the partial-trace
relative entropy is preserved (`D(Tr_B ω ‖ Tr_B τ) = D(ω ‖ τ)`), then the rectangular `−log`
operator-Jensen gap for the vectorised Petz isometry `W = petzWvec ω` annihilates the output cyclic
vector `ξ = vec((Tr_B ω)^{1/2})`:

`(Wᴴ (−log Δ) W) ξ = (−log)(Wᴴ Δ W) ξ`,   `Δ = modArgVec τ ω = τ ⊗ₖ (ω⁻¹)ᵀ`.

This is the exact saturation hypothesis fed to
`RigidityTail.isometry_resolvent_intertwine_of_neg_log_eq`. -/
theorem partialTrace_modular_gap (ω τ : DensityMatrix (nA × nB))
    (hω : ω.val.PosDef) (hτ : τ.val.PosDef)
    (hωA : (partialTraceRight ω.val).PosDef) (hτA : (partialTraceRight τ.val).PosDef)
    (hEq : relEntropy ω.partialTraceRight τ.partialTraceRight = relEntropy ω τ) :
    ((petzWvec ω.val)ᴴ * cfc (fun x => -Real.log x) (modArgVec τ.val ω.val) * petzWvec ω.val)
        *ᵥ vec ((partialTraceRight ω.val) ^ (1 / 2 : ℝ))
      = cfc (fun x => -Real.log x)
          ((petzWvec ω.val)ᴴ * modArgVec τ.val ω.val * petzWvec ω.val)
        *ᵥ vec ((partialTraceRight ω.val) ^ (1 / 2 : ℝ)) := by
  classical
  set W := petzWvec ω.val with hW
  set Δd := modArgVec τ.val ω.val with hΔd
  set ξo : (nA × nA) → ℂ := vec ((partialTraceRight ω.val) ^ (1 / 2 : ℝ)) with hξo
  have hWiso : Wᴴ * W = 1 := petzWvec_isometry ω.val hω hωA
  have hΔpd : Δd.PosDef := modArgVec_posDef hτ hω
  have hΔsa : IsSelfAdjoint Δd := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]; exact hΔpd.1
  have hΔsp : spectrum ℝ Δd ⊆ Set.Ioi 0 := modArgVec_spectrum hτ hω
  have hcomp : Wᴴ * Δd * W
      = (partialTraceRight τ.val) ⊗ₖ ((partialTraceRight ω.val) ^ (-1 : ℝ))ᵀ :=
    petzWvec_modular_compression τ.val ω.val hω hωA
  have hcyc : W *ᵥ ξo = vec (ω.val ^ (1 / 2 : ℝ)) := petzWvec_cyclic ω.val hωA
  have hle := rect_isometry_neg_log_loewner W Δd hWiso hΔsa hΔsp
  set A := cfc (fun x => -Real.log x) (Wᴴ * Δd * W) with hA
  set B := Wᴴ * cfc (fun x => -Real.log x) Δd * W with hB
  have hps : (B - A).PosSemidef := Matrix.le_iff.mp hle
  have hAexp : (star ξo ⬝ᵥ A *ᵥ ξo).re
      = relEntropy ω.partialTraceRight τ.partialTraceRight := by
    rw [hA, hcomp, hξo]
    exact kronForm_re_eq_relEntropy ω.partialTraceRight τ.partialTraceRight hωA hτA
  have hBexp : (star ξo ⬝ᵥ B *ᵥ ξo).re = relEntropy ω τ := by
    rw [hB, qform_conj W (cfc (fun x => -Real.log x) Δd) ξo, hcyc, hΔd]
    exact kronForm_re_eq_relEntropy ω τ hω hτ
  have hre : (star ξo ⬝ᵥ (B - A) *ᵥ ξo).re = 0 := by
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re, hBexp, hAexp, hEq, sub_self]
  have hzero : (B - A) *ᵥ ξo = 0 := posSemidef_vec_expectation_re_zero hps hre
  have hfinal : B *ᵥ ξo - A *ᵥ ξo = 0 := by rw [← sub_mulVec]; exact hzero
  exact sub_eq_zero.mp hfinal

/-! ## STEP 5: from the modular gap to the continuous-functional-calculus intertwining

The rectangular rigidity tail `isometry_resolvent_intertwine_of_neg_log_eq` (Fin-indexed) is first
transported to arbitrary finite index types (`resolvent_intertwine_general`), and its resolvent
output is upgraded — via the finite-spectrum resolvent readoff `exists_resolvent_combo` — to the
intertwining of *every* continuous function of the modular operator
(`cfc_intertwine_of_neg_log_gap`).  Applied to `partialTrace_modular_gap`, this is the STEP-5
conclusion `partialTrace_cfc_intertwine`. -/

/-- **Resolvent as functional calculus.**  For a positive-definite matrix `M` and `t > 0`,
`cfc (fun x => (x + t)⁻¹) M = (M + t)⁻¹`. -/
lemma cfc_resolvent_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.PosDef) {t : ℝ} (ht : 0 < t) :
    cfc (fun x : ℝ => (x + t)⁻¹) M = (M + algebraMap ℝ (Matrix ι ι ℂ) t)⁻¹ := by
  have hsa : IsSelfAdjoint M := hM.1
  have hne : ∀ x ∈ spectrum ℝ M, x + t ≠ 0 := by
    intro x hx
    rw [hM.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hM.eigenvalues_pos i
    positivity
  have hcont_add : ContinuousOn (fun x : ℝ => x + t) (spectrum ℝ M) := by fun_prop
  have hadd : cfc (fun x : ℝ => x + t) M = M + algebraMap ℝ (Matrix ι ι ℂ) t := by
    have h1 := cfc_add_const t (fun y : ℝ => y) M (continuousOn_id' (spectrum ℝ M)) hsa
    rw [cfc_id' ℝ M] at h1
    simpa using h1
  rw [cfc_inv (fun x => x + t) M hne hcont_add hsa, hadd, nonsing_inv_eq_ringInverse]

/-- **Resolvent intertwining (general index).**  The `Fin`-indexed rigidity tail
`isometry_resolvent_intertwine_of_neg_log_eq` transported to arbitrary finite index types via the
`Fintype.equivFin` reindexing.  Under isometry `W`, positive-definite `Δ`, and the `-log`
operator-Jensen saturation `hgap` at `ξ`, the isometry intertwines every resolvent of `Δ` on `ξ`. -/
lemma resolvent_intertwine_general {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] (W : Matrix p q ℂ) (Δ : Matrix p p ℂ) (ξ : q → ℂ)
    (hW : Wᴴ * W = 1) (hΔ : Δ.PosDef)
    (hgap : (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ
              = cfc (fun x => -Real.log x) (Wᴴ * Δ * W) *ᵥ ξ) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Wᴴ * Δ * W + algebraMap ℝ (Matrix q q ℂ) t)⁻¹ *ᵥ ξ) := by
  classical
  intro t ht
  set eP : p ≃ Fin (Fintype.card p) := Fintype.equivFin p with heP
  set eQ : q ≃ Fin (Fintype.card q) := Fintype.equivFin q with heQ
  set W' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card q)) ℂ :=
    W.submatrix eP.symm eQ.symm with hW'def
  set Δ' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ :=
    Δ.submatrix eP.symm eP.symm with hΔ'def
  set ξ' : Fin (Fintype.card q) → ℂ := ξ ∘ eQ.symm with hξ'def
  -- adjoint / isometry / PosDef of the reindexed data
  have hW'H : W'ᴴ = Wᴴ.submatrix eQ.symm eP.symm := by rw [hW'def, conjTranspose_submatrix]
  have hW'iso : W'ᴴ * W' = 1 := by
    rw [hW'H, hW'def, submatrix_mul_equiv, hW, submatrix_one_equiv]
  have hΔ'pd : Δ'.PosDef := by rw [hΔ'def]; exact hΔ.submatrix eP.symm.injective
  -- generic square-compression reindex
  have hcompS : ∀ S : Matrix p p ℂ,
      W'ᴴ * S.submatrix eP.symm eP.symm * W' = (Wᴴ * S * W).submatrix eQ.symm eQ.symm := by
    intro S
    rw [hW'H, hW'def, submatrix_mul_equiv, submatrix_mul_equiv]
  have hcomp : W'ᴴ * Δ' * W' = (Wᴴ * Δ * W).submatrix eQ.symm eQ.symm := by
    rw [hΔ'def]; exact hcompS Δ
  -- generic vector reindexings
  have hmulVecQ : ∀ A : Matrix q q ℂ,
      A.submatrix eQ.symm eQ.symm *ᵥ ξ' = (A *ᵥ ξ) ∘ eQ.symm := by
    intro A
    rw [hξ'def, submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hmulVecP : ∀ (A : Matrix p p ℂ) (v : p → ℂ),
      A.submatrix eP.symm eP.symm *ᵥ (v ∘ eP.symm) = (A *ᵥ v) ∘ eP.symm := by
    intro A v
    rw [submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hmulVecWq : ∀ u : q → ℂ, W' *ᵥ (u ∘ eQ.symm) = (W *ᵥ u) ∘ eP.symm := by
    intro u
    rw [hW'def, submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hWξ : W' *ᵥ ξ' = (W *ᵥ ξ) ∘ eP.symm := by rw [hξ'def]; exact hmulVecWq ξ
  -- shifted-matrix reindexings
  have hΔam : Δ' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t
      = (Δ + algebraMap ℝ (Matrix p p ℂ) t).submatrix eP.symm eP.symm := by
    rw [hΔ'def]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Algebra.algebraMap_eq_smul_one,
      Matrix.one_apply, Matrix.smul_apply]
  have hYam : W'ᴴ * Δ' * W'
        + algebraMap ℝ (Matrix (Fin (Fintype.card q)) (Fin (Fintype.card q)) ℂ) t
      = (Wᴴ * Δ * W + algebraMap ℝ (Matrix q q ℂ) t).submatrix eQ.symm eQ.symm := by
    rw [hcomp]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Algebra.algebraMap_eq_smul_one,
      Matrix.one_apply, Matrix.smul_apply]
  -- cfc reindexings (needs continuity of `-log` on the spectra)
  have hcfcΔ : cfc (fun x => -Real.log x) Δ'
      = (cfc (fun x => -Real.log x) Δ).submatrix eP.symm eP.symm := by
    have hlog : ContinuousOn (fun x => -Real.log x) (spectrum ℝ Δ) :=
      (Matrix.finite_real_spectrum (A := Δ)).continuousOn _
    have hbridge : ∀ X : Matrix p p ℂ, eqvFin p X = X.submatrix eP.symm eP.symm := fun _ => rfl
    have hE := eqvFin_cfc (fun x => -Real.log x) hΔ.1 hlog
    rw [hbridge, hbridge] at hE
    rw [hΔ'def]; exact hE.symm
  have hYpd : (Wᴴ * Δ * W).PosDef := by
    have hinj : Function.Injective W.mulVec := by
      intro a b hab
      have h : Wᴴ *ᵥ (W *ᵥ a) = Wᴴ *ᵥ (W *ᵥ b) := by rw [hab]
      rwa [mulVec_mulVec, mulVec_mulVec, hW, one_mulVec, one_mulVec] at h
    exact hΔ.conjTranspose_mul_mul_same hinj
  have hcfcY : cfc (fun x => -Real.log x) ((Wᴴ * Δ * W).submatrix eQ.symm eQ.symm)
      = (cfc (fun x => -Real.log x) (Wᴴ * Δ * W)).submatrix eQ.symm eQ.symm := by
    have hlog : ContinuousOn (fun x => -Real.log x) (spectrum ℝ (Wᴴ * Δ * W)) :=
      (Matrix.finite_real_spectrum (A := Wᴴ * Δ * W)).continuousOn _
    have hbridge : ∀ X : Matrix q q ℂ, eqvFin q X = X.submatrix eQ.symm eQ.symm := fun _ => rfl
    have hE := eqvFin_cfc (fun x => -Real.log x) hYpd.1 hlog
    rw [hbridge, hbridge] at hE
    exact hE.symm
  -- transported gap hypothesis
  have hgap' : (W'ᴴ * cfc (fun x => -Real.log x) Δ' * W') *ᵥ ξ'
      = cfc (fun x => -Real.log x) (W'ᴴ * Δ' * W') *ᵥ ξ' := by
    rw [hcfcΔ, hcompS (cfc (fun x => -Real.log x) Δ), hcomp, hcfcY, hmulVecQ, hmulVecQ, hgap]
  -- apply the Fin-indexed rigidity tail
  have hFin := isometry_resolvent_intertwine_of_neg_log_eq W' Δ' ξ' hW'iso hΔ'pd hgap' t ht
  -- transport both sides back
  have hLtrans : (Δ' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t)⁻¹
        *ᵥ (W' *ᵥ ξ')
      = ((Δ + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)) ∘ eP.symm := by
    rw [hΔam, inv_submatrix_equiv, hWξ, hmulVecP]
  have hRtrans : W' *ᵥ ((W'ᴴ * Δ' * W'
          + algebraMap ℝ (Matrix (Fin (Fintype.card q)) (Fin (Fintype.card q)) ℂ) t)⁻¹ *ᵥ ξ')
      = (W *ᵥ ((Wᴴ * Δ * W + algebraMap ℝ (Matrix q q ℂ) t)⁻¹ *ᵥ ξ)) ∘ eP.symm := by
    rw [hYam, inv_submatrix_equiv, hmulVecQ, hmulVecWq]
  rw [hLtrans, hRtrans] at hFin
  funext i
  have hi := congrFun hFin (eP i)
  simpa [Function.comp_def, Equiv.symm_apply_apply] using hi

/-- **`cfc` as a resolvent combination.**  If `g` agrees on a set `S ⊇ spectrum M` with a finite
real-coefficient combination of resolvents `∑ t, (c t).re · (x + t)⁻¹`, then `cfc g M` is the same
combination of the operator resolvents `(M + t)⁻¹`. -/
lemma cfc_eq_resolvent_combo {r : Type*} [Fintype r] [DecidableEq r]
    (g : ℝ → ℝ) (M : Matrix r r ℂ) (hM : M.PosDef) (c : {t : ℝ // 0 < t} →₀ ℂ) (S : Set ℝ)
    (hsub : spectrum ℝ M ⊆ S)
    (hcombo : ∀ y ∈ S, g y = ∑ t ∈ c.support, (c t).re * (y + (t : ℝ))⁻¹) :
    cfc g M = ∑ t ∈ c.support, (c t).re • (M + algebraMap ℝ (Matrix r r ℂ) (t : ℝ))⁻¹ := by
  have hMpos : ∀ x ∈ spectrum ℝ M, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos M hM.1).mp hM.isStrictlyPositive x hx
  have hcong : cfc g M = cfc (fun x => ∑ t ∈ c.support, (c t).re * (x + (t : ℝ))⁻¹) M := by
    apply cfc_congr
    intro x hx
    exact hcombo x (hsub hx)
  have hfun : (fun x : ℝ => ∑ t ∈ c.support, (c t).re * (x + (t : ℝ))⁻¹)
      = ∑ t ∈ c.support, (fun x : ℝ => (c t).re * (x + (t : ℝ))⁻¹) := by
    funext x; rw [Finset.sum_apply]
  have hcont : ∀ t ∈ c.support,
      ContinuousOn (fun x : ℝ => (c t).re * (x + (t : ℝ))⁻¹) (spectrum ℝ M) := by
    intro t _
    have hne : ∀ x ∈ spectrum ℝ M, x + (t : ℝ) ≠ 0 := by
      intro x hx; have := hMpos x hx; have := t.2; positivity
    exact continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) hne)
  rw [hcong, hfun, cfc_sum _ M c.support hcont]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hne : ∀ x ∈ spectrum ℝ M, x + (t : ℝ) ≠ 0 := by
    intro x hx; have := hMpos x hx; have := t.2; positivity
  rw [cfc_const_mul (c t).re (fun x => (x + (t : ℝ))⁻¹) M
      (ContinuousOn.inv₀ (by fun_prop) hne), cfc_resolvent_inv M hM t.2]

/-- **STEP 5 (abstract).**  If a rectangular isometry `W` saturates the `-log` operator-Jensen
inequality at `ξ` (`hgap`), then it intertwines *every* continuous function of the modular operator
`Δ` on `ξ`: `W (cfc g (Wᴴ Δ W) ξ) = cfc g Δ (W ξ)`.  The resolvent intertwining
(`resolvent_intertwine_general`) is upgraded via the finite-spectrum resolvent readoff
(`exists_resolvent_combo`). -/
lemma cfc_intertwine_of_neg_log_gap {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] (W : Matrix p q ℂ) (Δ : Matrix p p ℂ) (ξ : q → ℂ)
    (hW : Wᴴ * W = 1) (hΔ : Δ.PosDef)
    (hgap : (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ
              = cfc (fun x => -Real.log x) (Wᴴ * Δ * W) *ᵥ ξ)
    (g : ℝ → ℝ) :
    W *ᵥ (cfc g (Wᴴ * Δ * W) *ᵥ ξ) = cfc g Δ *ᵥ (W *ᵥ ξ) := by
  classical
  have hres := resolvent_intertwine_general W Δ ξ hW hΔ hgap
  have hYpd : (Wᴴ * Δ * W).PosDef := by
    have hinj : Function.Injective W.mulVec := by
      intro a b hab
      have h : Wᴴ *ᵥ (W *ᵥ a) = Wᴴ *ᵥ (W *ᵥ b) := by rw [hab]
      rwa [mulVec_mulVec, mulVec_mulVec, hW, one_mulVec, one_mulVec] at h
    exact hΔ.conjTranspose_mul_mul_same hinj
  have hΔpos : ∀ x ∈ spectrum ℝ Δ, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos Δ hΔ.1).mp hΔ.isStrictlyPositive x hx
  have hYpos : ∀ x ∈ spectrum ℝ (Wᴴ * Δ * W), 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (Wᴴ * Δ * W) hYpd.1).mp
      hYpd.isStrictlyPositive x hx
  have hUpos : ∀ i : ↥(spectrum ℝ Δ ∪ spectrum ℝ (Wᴴ * Δ * W)), 0 < (i : ℝ) := by
    rintro ⟨x, hx | hx⟩
    · exact hΔpos x hx
    · exact hYpos x hx
  haveI : Finite ↥(spectrum ℝ Δ ∪ spectrum ℝ (Wᴴ * Δ * W)) :=
    ((Matrix.finite_real_spectrum (A := Δ)).union
      (Matrix.finite_real_spectrum (A := Wᴴ * Δ * W))).to_subtype
  obtain ⟨c, hc⟩ := exists_resolvent_combo
    (ι := ↥(spectrum ℝ Δ ∪ spectrum ℝ (Wᴴ * Δ * W)))
    (fun i => (i : ℝ)) Subtype.coe_injective hUpos (fun i => ((g (i : ℝ) : ℂ)))
  -- real-coefficient combination valid on the union of the two spectra
  have hcombo : ∀ y ∈ spectrum ℝ Δ ∪ spectrum ℝ (Wᴴ * Δ * W),
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
  -- assemble the intertwining from the resolvent readoff
  have hL : W *ᵥ (cfc g (Wᴴ * Δ * W) *ᵥ ξ)
      = ∑ t ∈ c.support, (c t).re •
          (W *ᵥ ((Wᴴ * Δ * W + algebraMap ℝ (Matrix q q ℂ) (t : ℝ))⁻¹ *ᵥ ξ)) := by
    rw [cfc_eq_resolvent_combo g (Wᴴ * Δ * W) hYpd c _ Set.subset_union_right hcombo,
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

/-- **STEP 5 (partial-trace channel).**  Under the entropy-preservation hypothesis, the vectorised
Petz isometry `W = petzWvec ω` intertwines *every* continuous function of the modular operator
`Δ = modArgVec τ ω` on the output cyclic vector `ξ = vec((Tr_B ω)^{1/2})`:

`W (cfc g (Wᴴ Δ W) ξ) = cfc g Δ (W ξ)`   for all continuous `g`.

This is `cfc_intertwine_of_neg_log_gap` fed with the linchpin `partialTrace_modular_gap`. -/
theorem partialTrace_cfc_intertwine (ω τ : DensityMatrix (nA × nB))
    (hω : ω.val.PosDef) (hτ : τ.val.PosDef)
    (hωA : (partialTraceRight ω.val).PosDef) (hτA : (partialTraceRight τ.val).PosDef)
    (hEq : relEntropy ω.partialTraceRight τ.partialTraceRight = relEntropy ω τ)
    (g : ℝ → ℝ) :
    (petzWvec ω.val)
        *ᵥ (cfc g ((petzWvec ω.val)ᴴ * modArgVec τ.val ω.val * petzWvec ω.val)
              *ᵥ vec ((partialTraceRight ω.val) ^ (1 / 2 : ℝ)))
      = cfc g (modArgVec τ.val ω.val)
          *ᵥ (petzWvec ω.val *ᵥ vec ((partialTraceRight ω.val) ^ (1 / 2 : ℝ))) :=
  cfc_intertwine_of_neg_log_gap (petzWvec ω.val) (modArgVec τ.val ω.val)
    (vec ((partialTraceRight ω.val) ^ (1 / 2 : ℝ)))
    (petzWvec_isometry ω.val hω hωA) (modArgVec_posDef hτ hω)
    (partialTrace_modular_gap ω τ hω hτ hωA hτA hEq) g

/-! ## STEP 6: from the cfc-intertwining to the modular `it`-cocycle intertwining

The STEP-5 conclusion `partialTrace_cfc_intertwine` is upgraded to the modular `it`-cocycle
intertwining `(Tr_B).adj((Tr_Bω)^{it}(Tr_Bτ)^{-it}) = ω^{it}τ^{-it}`.  The complex power `A^{it}`
(`cpow`/`upow`) is bridged to the real functional calculus through the cos–sin decomposition
`cpow_eq_cfc_cos_sin`, from which the basis-independence (`upow_conj_diag`), the transpose, inverse
and Kronecker laws of the unitary power (`upow_transpose`, `upow_inv`, `upow_kron`) and the
real-power bridge (`rpow_eq_cpow_ofReal`) follow. -/

/-- Entrywise `exp(t·I·log)` identity: `exp((t·I)·r) = cos(t·r) + I·sin(t·r)` for real `r`. -/
private lemma cexp_tI_ofReal (t r : ℝ) :
    Complex.exp (((t : ℂ) * Complex.I) * (r : ℂ))
      = (Real.cos (t * r) : ℂ) + Complex.I * (Real.sin (t * r) : ℂ) := by
  have h1 : ((t : ℂ) * Complex.I) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring

/-- Entrywise `exp(y·r) = e^{yr}` (real exponent). -/
private lemma cexp_ofReal_mul (y r : ℝ) :
    Complex.exp (((y : ℂ)) * (r : ℂ)) = ((Real.exp (y * r) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, Complex.ofReal_exp]

/-- **Complex-power / cos–sin bridge.**  For positive-definite `A` and real `t`, the unitary power
`A^{it} = cpow A (t·I)` is the real functional-calculus combination
`cfc (cos(t·log·)) A + I • cfc (sin(t·log·)) A`. -/
lemma cpow_eq_cfc_cos_sin {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    cpow hA ((t : ℂ) * Complex.I)
      = cfc (fun x => Real.cos (t * Real.log x)) A
        + Complex.I • cfc (fun x => Real.sin (t * Real.log x)) A := by
  classical
  set hAh := hA.1 with hAhdef
  set UA : Matrix n n ℂ := (hAh.eigenvectorUnitary : Matrix n n ℂ) with hUA
  set eA : n → ℝ := hAh.eigenvalues with heA
  have hUAs1 : star UA * UA = 1 := Unitary.coe_star_mul_self _
  have hUAs2 : UA * star UA = 1 := Unitary.coe_mul_star_self _
  have hDsa : IsSelfAdjoint (diagonal (fun i => (eA i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact Complex.conj_ofReal (eA i)
  have hspecA : A = UA * diagonal (fun i => (eA i : ℂ)) * star UA := by
    have h := hAh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hAh.eigenvalues) = fun i => (eA i : ℂ) := by funext i; rfl
    rw [hRC] at h; exact h
  have hgc : cfc (fun x => Real.cos (t * Real.log x)) A
      = UA * diagonal (fun i => (Real.cos (t * Real.log (eA i)) : ℂ)) * star UA := by
    conv_lhs => rw [hspecA]
    rw [cfc_conj UA (diagonal (fun i => (eA i : ℂ))) hUAs1 hUAs2 hDsa, cfc_diagonal]
  have hgs : cfc (fun x => Real.sin (t * Real.log x)) A
      = UA * diagonal (fun i => (Real.sin (t * Real.log (eA i)) : ℂ)) * star UA := by
    conv_lhs => rw [hspecA]
    rw [cfc_conj UA (diagonal (fun i => (eA i : ℂ))) hUAs1 hUAs2 hDsa, cfc_diagonal]
  have hI : UA * (Complex.I • diagonal (fun i => (Real.sin (t * Real.log (eA i)) : ℂ))) * star UA
      = Complex.I • (UA * diagonal (fun i => (Real.sin (t * Real.log (eA i)) : ℂ)) * star UA) := by
    rw [mul_smul_comm, smul_mul_assoc]
  have hcpow : cpow hA ((t : ℂ) * Complex.I)
      = UA * diagonal (fun i => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (eA i) : ℂ)))
        * star UA := rfl
  have hdiag : diagonal (fun i => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (eA i) : ℂ)))
      = diagonal (fun i => (Real.cos (t * Real.log (eA i)) : ℂ))
        + Complex.I • diagonal (fun i => (Real.sin (t * Real.log (eA i)) : ℂ)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with h
    · exact cexp_tI_ofReal t (Real.log (eA i))
    · rw [mul_zero, add_zero]
  rw [hcpow, hgc, hgs, ← hI, ← add_mul, ← mul_add, hdiag]

/-- **Conjugation form of the unitary power.**  If `A = W diag(d) W⋆` with `W` unitary, then
`A^{it} = W diag(exp(it·log d)) W⋆` (basis-independence of `upow`). -/
lemma upow_conj_diag {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ)
    {W : Matrix n n ℂ} {d : n → ℝ}
    (hW1 : star W * W = 1) (hW2 : W * star W = 1)
    (hAWD : A = W * diagonal (fun i => (d i : ℂ)) * star W) :
    upow hA t
      = W * diagonal (fun i => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (d i) : ℂ)))
        * star W := by
  have hDsa : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact Complex.conj_ofReal (d i)
  have hgc : cfc (fun x => Real.cos (t * Real.log x)) A
      = W * diagonal (fun i => (Real.cos (t * Real.log (d i)) : ℂ)) * star W := by
    conv_lhs => rw [hAWD]
    rw [cfc_conj W (diagonal (fun i => (d i : ℂ))) hW1 hW2 hDsa, cfc_diagonal]
  have hgs : cfc (fun x => Real.sin (t * Real.log x)) A
      = W * diagonal (fun i => (Real.sin (t * Real.log (d i)) : ℂ)) * star W := by
    conv_lhs => rw [hAWD]
    rw [cfc_conj W (diagonal (fun i => (d i : ℂ))) hW1 hW2 hDsa, cfc_diagonal]
  have hI : W * (Complex.I • diagonal (fun i => (Real.sin (t * Real.log (d i)) : ℂ))) * star W
      = Complex.I • (W * diagonal (fun i => (Real.sin (t * Real.log (d i)) : ℂ)) * star W) := by
    rw [mul_smul_comm, smul_mul_assoc]
  have hdiag : diagonal (fun i => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (d i) : ℂ)))
      = diagonal (fun i => (Real.cos (t * Real.log (d i)) : ℂ))
        + Complex.I • diagonal (fun i => (Real.sin (t * Real.log (d i)) : ℂ)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with h
    · exact cexp_tI_ofReal t (Real.log (d i))
    · rw [mul_zero, add_zero]
  have hupow : upow hA t = cpow hA ((t : ℂ) * Complex.I) := rfl
  rw [hupow, cpow_eq_cfc_cos_sin hA t, hgc, hgs, ← hI, ← add_mul, ← mul_add, hdiag]

/-- **Conjugation form of a real power.**  If `A = W diag(d) W⋆` with `W` unitary, then
`A^y = W diag(d^y) W⋆`. -/
lemma rpow_conj_diag {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (y : ℝ)
    {W : Matrix n n ℂ} {d : n → ℝ}
    (hW1 : star W * W = 1) (hW2 : W * star W = 1)
    (hAWD : A = W * diagonal (fun i => (d i : ℂ)) * star W) :
    A ^ (y : ℝ) = W * diagonal (fun i => (((d i) ^ y : ℝ) : ℂ)) * star W := by
  have hDsa : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact Complex.conj_ofReal (d i)
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  conv_lhs => rw [hAWD]
  rw [cfc_conj W (diagonal (fun i => (d i : ℂ))) hW1 hW2 hDsa, cfc_diagonal]

/-- **Real power as complex power.**  For positive-definite `A` and real `y`, `A^y = A^{(y:ℂ)}`. -/
lemma rpow_eq_cpow_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (y : ℝ) :
    A ^ (y : ℝ) = cpow hA (y : ℂ) := by
  classical
  set hAh := hA.1 with hAhdef
  set UA : Matrix n n ℂ := (hAh.eigenvectorUnitary : Matrix n n ℂ) with hUA
  set eA : n → ℝ := hAh.eigenvalues with heA
  have hUs1 : star UA * UA = 1 := Unitary.coe_star_mul_self _
  have hUs2 : UA * star UA = 1 := Unitary.coe_mul_star_self _
  have hpos : ∀ i, 0 < eA i := fun i => hA.eigenvalues_pos i
  have hspecA : A = UA * diagonal (fun i => (eA i : ℂ)) * star UA := by
    have h := hAh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hAh.eigenvalues) = fun i => (eA i : ℂ) := by funext i; rfl
    rw [hRC] at h; exact h
  have hcpow : cpow hA (y : ℂ)
      = UA * diagonal (fun i => Complex.exp ((y : ℂ) * (Real.log (eA i) : ℂ))) * star UA := rfl
  have hfun : (fun i => (((eA i) ^ y : ℝ) : ℂ))
      = (fun i => Complex.exp ((y : ℂ) * (Real.log (eA i) : ℂ))) := by
    funext i
    rw [cexp_ofReal_mul y (Real.log (eA i)), Real.rpow_def_of_pos (hpos i)]
    congr 2; ring
  rw [rpow_conj_diag hA y hUs1 hUs2 hspecA, hcpow, hfun]

/-- **Transpose of a unitary power.**  `(Mᵀ)^{it} = (M^{it})ᵀ`. -/
lemma upow_transpose {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosDef) (hMT : (Mᵀ).PosDef) (t : ℝ) :
    upow hMT t = (upow hM t)ᵀ := by
  have hcgc : ContinuousOn (fun x => Real.cos (t * Real.log x)) (spectrum ℝ M) :=
    (Matrix.finite_real_spectrum (A := M)).continuousOn _
  have hcgs : ContinuousOn (fun x => Real.sin (t * Real.log x)) (spectrum ℝ M) :=
    (Matrix.finite_real_spectrum (A := M)).continuousOn _
  have h1 : upow hMT t = cpow hMT ((t : ℂ) * Complex.I) := rfl
  have h2 : upow hM t = cpow hM ((t : ℂ) * Complex.I) := rfl
  rw [h1, cpow_eq_cfc_cos_sin hMT t,
    cfc_transpose (fun x => Real.cos (t * Real.log x)) hM.1 hcgc,
    cfc_transpose (fun x => Real.sin (t * Real.log x)) hM.1 hcgs,
    h2, cpow_eq_cfc_cos_sin hM t, Matrix.transpose_add, Matrix.transpose_smul]

/-- **Inverse of a unitary power.**  `(M⁻¹)^{it} = M^{-it}`. -/
lemma upow_inv {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosDef) (hMinv : (M ^ (-1 : ℝ)).PosDef) (t : ℝ) :
    upow hMinv t = upow hM (-t) := by
  classical
  set hMh := hM.1 with hMhdef
  set UM : Matrix n n ℂ := (hMh.eigenvectorUnitary : Matrix n n ℂ) with hUM
  set eM : n → ℝ := hMh.eigenvalues with heM
  have hUs1 : star UM * UM = 1 := Unitary.coe_star_mul_self _
  have hUs2 : UM * star UM = 1 := Unitary.coe_mul_star_self _
  have hpos : ∀ i, 0 < eM i := fun i => hM.eigenvalues_pos i
  have hspecM : M = UM * diagonal (fun i => (eM i : ℂ)) * star UM := by
    have h := hMh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hMh.eigenvalues) = fun i => (eM i : ℂ) := by funext i; rfl
    rw [hRC] at h; exact h
  have hWD : M ^ (-1 : ℝ) = UM * diagonal (fun i => (((eM i) ^ (-1 : ℝ) : ℝ) : ℂ)) * star UM :=
    rpow_conj_diag hM (-1) hUs1 hUs2 hspecM
  have hrhs : upow hM (-t)
      = UM * diagonal (fun i => Complex.exp (((-t : ℝ) : ℂ) * Complex.I * (Real.log (eM i) : ℂ)))
        * star UM := rfl
  have hfun : (fun i => Complex.exp (((t : ℂ) * Complex.I) * (Real.log ((eM i) ^ (-1 : ℝ)) : ℂ)))
      = (fun i => Complex.exp (((-t : ℝ) : ℂ) * Complex.I * (Real.log (eM i) : ℂ))) := by
    funext i
    rw [Real.rpow_neg_one, Real.log_inv]
    congr 1; push_cast; ring
  rw [upow_conj_diag hMinv t hUs1 hUs2 hWD, hrhs, hfun]

/-- **Kronecker of a unitary power.**  `(A ⊗ₖ B)^{it} = A^{it} ⊗ₖ B^{it}`. -/
lemma upow_kron {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {A : Matrix p p ℂ} {B : Matrix q q ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (A ⊗ₖ B).PosDef) (t : ℝ) :
    upow hAB t = upow hA t ⊗ₖ upow hB t := by
  classical
  set UA : Matrix p p ℂ := (hA.1.eigenvectorUnitary : Matrix p p ℂ) with hUA
  set UB : Matrix q q ℂ := (hB.1.eigenvectorUnitary : Matrix q q ℂ) with hUB
  set eA : p → ℝ := hA.1.eigenvalues with heA
  set eB : q → ℝ := hB.1.eigenvalues with heB
  have hUAs1 : star UA * UA = 1 := Unitary.coe_star_mul_self _
  have hUAs2 : UA * star UA = 1 := Unitary.coe_mul_star_self _
  have hUBs1 : star UB * UB = 1 := Unitary.coe_star_mul_self _
  have hUBs2 : UB * star UB = 1 := Unitary.coe_mul_star_self _
  have hpos_A : ∀ i, (0 : ℝ) < eA i := fun i => hA.eigenvalues_pos i
  have hpos_B : ∀ j, (0 : ℝ) < eB j := fun j => hB.eigenvalues_pos j
  have hWstar : star (UA ⊗ₖ UB) = star UA ⊗ₖ star UB := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]
  have hW1 : star (UA ⊗ₖ UB) * (UA ⊗ₖ UB) = 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, hUAs1, hUBs1, Matrix.one_kronecker_one]
  have hW2 : (UA ⊗ₖ UB) * star (UA ⊗ₖ UB) = 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, hUAs2, hUBs2, Matrix.one_kronecker_one]
  have hspecA : A = UA * diagonal (fun i => (eA i : ℂ)) * star UA := by
    have h := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hA.1.eigenvalues) = fun i => (eA i : ℂ) := by funext i; rfl
    rw [hRC] at h; exact h
  have hspecB : B = UB * diagonal (fun j => (eB j : ℂ)) * star UB := by
    have h := hB.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hB.1.eigenvalues) = fun j => (eB j : ℂ) := by funext j; rfl
    rw [hRC] at h; exact h
  have hdd : (diagonal (fun i => (eA i : ℂ))) ⊗ₖ (diagonal (fun j => (eB j : ℂ)))
      = diagonal (fun r : p × q => ((eA r.1 * eB r.2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1; funext r; push_cast; ring
  have hABdecomp : A ⊗ₖ B = (UA ⊗ₖ UB)
      * diagonal (fun r : p × q => ((eA r.1 * eB r.2 : ℝ) : ℂ)) * star (UA ⊗ₖ UB) := by
    rw [hspecA, hspecB, hWstar, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, hdd]
  rw [upow_conj_diag hAB t hW1 hW2 hABdecomp]
  have hUpA : upow hA t
      = UA * diagonal (fun i => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (eA i) : ℂ)))
        * star UA := rfl
  have hUpB : upow hB t
      = UB * diagonal (fun j => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (eB j) : ℂ)))
        * star UB := rfl
  have hdsplit : diagonal
        (fun r : p × q => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (eA r.1 * eB r.2) : ℂ)))
      = (diagonal (fun i => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (eA i) : ℂ))))
        ⊗ₖ (diagonal (fun j => Complex.exp (((t : ℂ) * Complex.I) * (Real.log (eB j) : ℂ)))) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1; funext r
    rw [← Complex.exp_add]
    congr 1
    rw [Real.log_mul (hpos_A r.1).ne' (hpos_B r.2).ne']
    push_cast; ring
  rw [hUpA, hUpB, hdsplit, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, hWstar]

/-- **Action of the modular unitary flow on a vectorised matrix.**  For `Δ = P ⊗ₖ (R⁻¹)ᵀ`,
`Δ^{it} · vec X = vec(P^{it} · X · R^{-it})`. -/
lemma modArg_upow_mulVec {m : Type*} [Fintype m] [DecidableEq m]
    {P R : Matrix m m ℂ} (hP : P.PosDef) (hR : R.PosDef)
    (hPR : (P ⊗ₖ (R ^ (-1 : ℝ))ᵀ).PosDef) (t : ℝ) (X : Matrix m m ℂ) :
    upow hPR t *ᵥ vec X = vec (upow hP t * X * upow hR (-t)) := by
  have hRinv : (R ^ (-1 : ℝ)).PosDef := by
    rw [← CFC.rpow_eq_pow]
    exact (IsStrictlyPositive.rpow R (-1) hR.isStrictlyPositive).posDef
  have hRinvT : ((R ^ (-1 : ℝ))ᵀ).PosDef := hRinv.transpose
  rw [upow_kron hP hRinvT hPR t, upow_transpose hRinv hRinvT t, upow_inv hR hRinv t]
  exact (vec_mul_mul (upow hP t) X (upow hR (-t))).symm

/-- **STEP 6 (unitary-power intertwining).**  The vectorised Petz isometry `W = petzWvec ω`
intertwines the unitary power (`it`-flow) of the modular operator on the output cyclic vector:
`W (ΔA^{it} ξ) = Δ^{it} (W ξ)`, where `ξ = vec(ω_A^{1/2})`, `ΔA = τ_A ⊗ₖ (ω_A⁻¹)ᵀ`,
`Δ = τ ⊗ₖ (ω⁻¹)ᵀ` and `W ξ = vec(ω^{1/2})`. -/
theorem partialTrace_upow_intertwine (ω τ : DensityMatrix (nA × nB))
    (hω : ω.val.PosDef) (hτ : τ.val.PosDef)
    (hωA : (partialTraceRight ω.val).PosDef) (hτA : (partialTraceRight τ.val).PosDef)
    (hEq : relEntropy ω.partialTraceRight τ.partialTraceRight = relEntropy ω τ) (t : ℝ)
    (hΔApd : ((partialTraceRight τ.val) ⊗ₖ ((partialTraceRight ω.val) ^ (-1 : ℝ))ᵀ).PosDef)
    (hΔpd : (τ.val ⊗ₖ (ω.val ^ (-1 : ℝ))ᵀ).PosDef) :
    petzWvec ω.val *ᵥ (upow hΔApd t *ᵥ vec ((partialTraceRight ω.val) ^ (1 / 2 : ℝ)))
      = upow hΔpd t *ᵥ vec (ω.val ^ (1 / 2 : ℝ)) := by
  have hIc := partialTrace_cfc_intertwine ω τ hω hτ hωA hτA hEq (fun x => Real.cos (t * Real.log x))
  have hIs := partialTrace_cfc_intertwine ω τ hω hτ hωA hτA hEq (fun x => Real.sin (t * Real.log x))
  rw [petzWvec_modular_compression τ.val ω.val hω hωA, petzWvec_cyclic ω.val hωA] at hIc hIs
  unfold modArgVec at hIc hIs
  have hu1 : upow hΔApd t = cpow hΔApd ((t : ℂ) * Complex.I) := rfl
  have hu2 : upow hΔpd t = cpow hΔpd ((t : ℂ) * Complex.I) := rfl
  rw [hu1, hu2, cpow_eq_cfc_cos_sin hΔApd t, cpow_eq_cfc_cos_sin hΔpd t]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hIc, hIs]

/-- **STEP 6 (final): partial-trace sufficiency it-intertwining.**  Under entropy preservation, the
ampliation (`Tr_B`-adjoint) of the *output* modular `it`-cocycle equals the *input* modular
`it`-cocycle:  `((Tr_B ω)^{it}(Tr_B τ)^{-it}) ⊗ₖ 1 = ω^{it} τ^{-it}` for all `t`. -/
theorem partialTrace_equality_imp_intertwinesIt (ω τ : DensityMatrix (nA × nB))
    (hω : ω.val.PosDef) (hτ : τ.val.PosDef)
    (hωA : (partialTraceRight ω.val).PosDef) (hτA : (partialTraceRight τ.val).PosDef)
    (hEq : relEntropy ω.partialTraceRight τ.partialTraceRight = relEntropy ω τ) :
    ∀ t : ℝ, (upow hωA t * upow hτA (-t)) ⊗ₖ (1 : Matrix nB nB ℂ)
      = upow hω t * upow hτ (-t) := by
  intro t
  have hωAinv : ((partialTraceRight ω.val) ^ (-1 : ℝ)).PosDef := by
    rw [← CFC.rpow_eq_pow]
    exact (IsStrictlyPositive.rpow (partialTraceRight ω.val) (-1) hωA.isStrictlyPositive).posDef
  have hωinv : (ω.val ^ (-1 : ℝ)).PosDef := by
    rw [← CFC.rpow_eq_pow]
    exact (IsStrictlyPositive.rpow ω.val (-1) hω.isStrictlyPositive).posDef
  have hΔApd : ((partialTraceRight τ.val) ⊗ₖ ((partialTraceRight ω.val) ^ (-1 : ℝ))ᵀ).PosDef :=
    hτA.kronecker hωAinv.transpose
  have hΔpd : (τ.val ⊗ₖ (ω.val ^ (-1 : ℝ))ᵀ).PosDef := hτ.kronecker hωinv.transpose
  -- (★): the unitary-power intertwining at `t`, with the vec-actions read off.
  have hstar := partialTrace_upow_intertwine ω τ hω hτ hωA hτA hEq t hΔApd hΔpd
  rw [modArg_upow_mulVec hτA hωA hΔApd t ((partialTraceRight ω.val) ^ (1 / 2 : ℝ)),
      modArg_upow_mulVec hτ hω hΔpd t (ω.val ^ (1 / 2 : ℝ)),
      ← vec_petzW] at hstar
  -- strip the vec functor.
  have hbase : petzW ω.val
        (upow hτA t * (partialTraceRight ω.val) ^ (1 / 2 : ℝ) * upow hωA (-t))
      = upow hτ t * ω.val ^ (1 / 2 : ℝ) * upow hω (-t) := by
    apply Matrix.ext
    intro i j
    have := congrFun hstar (i, j)
    simpa only [vec_apply] using this
  -- collapse the `ω_A^{±1/2}` twist (input column) and commute `ω^{1/2}` past `ω^{-it}`.
  have hYcol :
      upow hτA t * (partialTraceRight ω.val) ^ (1 / 2 : ℝ) * upow hωA (-t)
          * (partialTraceRight ω.val) ^ (-(1 / 2) : ℝ)
        = upow hτA t * upow hωA (-t) := by
    rw [rpow_eq_cpow_ofReal hωA (1 / 2), rpow_eq_cpow_ofReal hωA (-(1 / 2)),
        show upow hωA (-t) = cpow hωA (((-t : ℝ) : ℂ) * Complex.I) from rfl]
    rw [show upow hτA t * cpow hωA ((1 / 2 : ℝ) : ℂ) * cpow hωA (((-t : ℝ) : ℂ) * Complex.I)
            * cpow hωA ((-(1 / 2) : ℝ) : ℂ)
          = upow hτA t * (cpow hωA ((1 / 2 : ℝ) : ℂ) * cpow hωA (((-t : ℝ) : ℂ) * Complex.I)
            * cpow hωA ((-(1 / 2) : ℝ) : ℂ)) from by noncomm_ring,
        cpow_mul_cpow, cpow_mul_cpow]
    congr 2
    push_cast; ring
  have hRHScol :
      upow hτ t * ω.val ^ (1 / 2 : ℝ) * upow hω (-t)
        = upow hτ t * upow hω (-t) * ω.val ^ (1 / 2 : ℝ) := by
    rw [rpow_eq_cpow_ofReal hω (1 / 2),
        show upow hω (-t) = cpow hω (((-t : ℝ) : ℂ) * Complex.I) from rfl,
        mul_assoc, mul_assoc, cpow_mul_cpow, cpow_mul_cpow]
    congr 2
    push_cast; ring
  -- unfold the Petz isometry and cancel `ω^{1/2}`.
  unfold petzW at hbase
  rw [hYcol, hRHScol] at hbase
  -- `hbase : (coc_out ⊗ₖ 1) * ω^{1/2} = (coc_in) * ω^{1/2}`.
  have hsqrtInv : ω.val ^ (1 / 2 : ℝ) * ω.val ^ (-(1 / 2) : ℝ) = 1 :=
    CFC.rpow_mul_rpow_neg (1 / 2) hω.isStrictlyPositive
  have hcancel : (upow hτA t * upow hωA (-t)) ⊗ₖ (1 : Matrix nB nB ℂ)
      = upow hτ t * upow hω (-t) :=
    calc (upow hτA t * upow hωA (-t)) ⊗ₖ (1 : Matrix nB nB ℂ)
        = ((upow hτA t * upow hωA (-t)) ⊗ₖ (1 : Matrix nB nB ℂ))
            * (ω.val ^ (1 / 2 : ℝ) * ω.val ^ (-(1 / 2) : ℝ)) := by rw [hsqrtInv, mul_one]
      _ = ((upow hτA t * upow hωA (-t)) ⊗ₖ (1 : Matrix nB nB ℂ))
            * ω.val ^ (1 / 2 : ℝ) * ω.val ^ (-(1 / 2) : ℝ) := by rw [mul_assoc]
      _ = upow hτ t * upow hω (-t) * ω.val ^ (1 / 2 : ℝ) * ω.val ^ (-(1 / 2) : ℝ) := by rw [hbase]
      _ = upow hτ t * upow hω (-t)
            * (ω.val ^ (1 / 2 : ℝ) * ω.val ^ (-(1 / 2) : ℝ)) := by rw [mul_assoc]
      _ = upow hτ t * upow hω (-t) := by rw [hsqrtInv, mul_one]
  -- take adjoints to pass from the `τω⁻¹`-convention cocycle to the target.
  calc (upow hωA t * upow hτA (-t)) ⊗ₖ (1 : Matrix nB nB ℂ)
      = star ((upow hτA t * upow hωA (-t)) ⊗ₖ (1 : Matrix nB nB ℂ)) := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
          ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_one,
          star_mul, star_upow, star_upow, neg_neg]
    _ = star (upow hτ t * upow hω (-t)) := by rw [hcancel]
    _ = upow hω t * upow hτ (-t) := by
        rw [star_mul, star_upow, star_upow, neg_neg]

end Oseledets.OperatorEntropy.Lieb

end
