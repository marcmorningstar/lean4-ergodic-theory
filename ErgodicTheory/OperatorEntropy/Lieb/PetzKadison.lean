/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.PetzAnalyticContinuation

/-!
# Kadison–Schwarz multiplicative domain and the Petz recovery equality

This module closes the finite-dimensional **Petz recovery / sufficiency** implication: the
imaginary-axis modular intertwining `IntertwinesIt` forces the Petz recovery map to reconstruct
the input state, `petz σ Λ (Λ ρ) = ρ`.

The mathematical content is the **Kadison–Schwarz multiplicative domain** for the Heisenberg
adjoint `Λ†` of a Kraus channel. In concrete Kraus/Gram form we prove the algebraic identity

  `Λ†(Xᴴ X) - (Λ† X)ᴴ (Λ† X) = ∑ᵢ (X Kᵢ - Kᵢ Λ†X)ᴴ (X Kᵢ - Kᵢ Λ†X)`,

which is manifestly positive semidefinite (Kadison–Schwarz). When the difference vanishes — as it
does for a unitary `U` whose image `Λ†U` is again unitary — every summand vanishes, giving the
**intertwining relations** `U Kᵢ = Kᵢ Λ†U`. Propagating these off the imaginary axis by the M4
analytic-continuation machinery yields `W Kᵢ = Kᵢ Λ†W` at the KMS point
`W = (Λρ)^{1/2}(Λσ)^{-1/2}`, whence

  `Λ†(Wᴴ W) = (Λ†W)ᴴ (Λ†W)`,

the multiplicative-domain equality at `W`. Combined with the KMS-point intertwining
`Λ†W = ρ^{1/2}σ^{-1/2}` (`intertwinesIt_rpow_half`) and the `CFC.conjSqrt` calculus this collapses
the Petz map to `ρ`.

## Main results

* `KrausChannel.kadison_schwarz_eq`: the concrete Gram identity for `Λ†`.
* `KrausChannel.intertwine_of_adj_eq`: vanishing Kadison–Schwarz defect gives `X Kᵢ = Kᵢ Λ†X`.
* `ErgodicTheory.OperatorEntropy.Lieb.cpow_conjTranspose` / `upow_mem_unitary`: the
  spectral cocycle facts.
* `intertwinesIt_imp_recovery`: **the Petz recovery equality** `petz σ Λ (Λ ρ) = ρ`.
-/

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Heisenberg adjoint is `*`-preserving -/

/-- The Heisenberg adjoint commutes with the matrix adjoint: `Λ†(Xᴴ) = (Λ† X)ᴴ`. -/
theorem KrausChannel.adj_conjTranspose (Λ : KrausChannel n) (X : Matrix n n ℂ) :
    Λ.adj Xᴴ = (Λ.adj X)ᴴ := by
  unfold KrausChannel.adj
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]

/-! ## The concrete Kadison–Schwarz (Gram) identity -/

/-- **Kadison–Schwarz Gram identity** for the Heisenberg adjoint. The Kadison–Schwarz defect is a
manifest Gram matrix over the Kraus operators:
`Λ†(Xᴴ X) - (Λ†X)ᴴ (Λ†X) = ∑ᵢ (X Kᵢ - Kᵢ Λ†X)ᴴ (X Kᵢ - Kᵢ Λ†X)`. -/
theorem KrausChannel.kadison_schwarz_eq (Λ : KrausChannel n) (X : Matrix n n ℂ) :
    Λ.adj (Xᴴ * X) - (Λ.adj X)ᴴ * Λ.adj X
      = ∑ i, (X * Λ.K i - Λ.K i * Λ.adj X)ᴴ * (X * Λ.K i - Λ.K i * Λ.adj X) := by
  set P := Λ.adj X with hP
  have hexpand : ∀ i, (X * Λ.K i - Λ.K i * P)ᴴ * (X * Λ.K i - Λ.K i * P)
      = (Λ.K i)ᴴ * (Xᴴ * X) * Λ.K i - ((Λ.K i)ᴴ * Xᴴ * Λ.K i) * P
        - Pᴴ * ((Λ.K i)ᴴ * X * Λ.K i) + Pᴴ * ((Λ.K i)ᴴ * Λ.K i) * P := by
    intro i
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [Finset.sum_congr rfl fun i _ => hexpand i,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hT1 : ∑ i, (Λ.K i)ᴴ * (Xᴴ * X) * Λ.K i = Λ.adj (Xᴴ * X) := rfl
  have hT2 : ∑ i, ((Λ.K i)ᴴ * Xᴴ * Λ.K i) * P = Pᴴ * P := by
    rw [← Finset.sum_mul]
    have h : ∑ i, (Λ.K i)ᴴ * Xᴴ * Λ.K i = Λ.adj Xᴴ := rfl
    rw [h, Λ.adj_conjTranspose, ← hP]
  have hT3 : ∑ i, Pᴴ * ((Λ.K i)ᴴ * X * Λ.K i) = Pᴴ * P := by
    rw [← Finset.mul_sum]
    have h : ∑ i, (Λ.K i)ᴴ * X * Λ.K i = Λ.adj X := rfl
    rw [h, ← hP]
  have hT4 : ∑ i, Pᴴ * ((Λ.K i)ᴴ * Λ.K i) * P = Pᴴ * P := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, Λ.htp, Matrix.mul_one]
  rw [hT1, hT2, hT3, hT4]
  abel

omit [DecidableEq n] in
/-- A finite sum of Gram matrices `∑ (Y i)ᴴ (Y i)` vanishes only if each `Y i` does. -/
theorem sum_conjTranspose_mul_self_eq_zero {ι : Type*} [Fintype ι] {Y : ι → Matrix n n ℂ}
    (h : ∑ i, (Y i)ᴴ * (Y i) = 0) (i : ι) : Y i = 0 := by
  have htr : ∑ j, ((Y j)ᴴ * Y j).trace = 0 := by
    rw [← Matrix.trace_sum, h, Matrix.trace_zero]
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ ((Y j)ᴴ * Y j).trace :=
    fun j _ => (Matrix.posSemidef_conjTranspose_mul_self (Y j)).trace_nonneg
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htr i (Finset.mem_univ i)
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzero

/-- **Multiplicative domain from a vanishing Kadison–Schwarz defect.** If the Kadison–Schwarz
inequality is an equality at `X` (`Λ†(Xᴴ X) = (Λ†X)ᴴ Λ†X`), then each Kraus operator intertwines
`X` with its image: `X Kᵢ = Kᵢ Λ†X`. -/
theorem KrausChannel.intertwine_of_adj_eq (Λ : KrausChannel n) {X : Matrix n n ℂ}
    (h : Λ.adj (Xᴴ * X) = (Λ.adj X)ᴴ * Λ.adj X) (i : Λ.ι) :
    X * Λ.K i = Λ.K i * Λ.adj X := by
  have hsum : ∑ i, (X * Λ.K i - Λ.K i * Λ.adj X)ᴴ * (X * Λ.K i - Λ.K i * Λ.adj X) = 0 := by
    rw [← Λ.kadison_schwarz_eq X, h, sub_self]
  have := sum_conjTranspose_mul_self_eq_zero hsum i
  rwa [sub_eq_zero] at this

end ErgodicTheory.OperatorEntropy

namespace ErgodicTheory.OperatorEntropy.Lieb

open ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Spectral cocycle facts for `cpow` / `upow` -/

/-- **Conjugate transpose of the entire power**: `(A^z)ᴴ = A^{conj z}`. -/
lemma cpow_conjTranspose {A : Matrix n n ℂ} (hA : A.PosDef) (z : ℂ) :
    (cpow hA z)ᴴ = cpow hA (starRingEnd ℂ z) := by
  unfold cpow
  set U := (hA.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hstar : (star U)ᴴ = U := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hstar, Matrix.diagonal_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  have hd : (star (fun i => Complex.exp (z * (Real.log (hA.1.eigenvalues i) : ℂ))) : n → ℂ)
      = fun i => Complex.exp (starRingEnd ℂ z * (Real.log (hA.1.eigenvalues i) : ℂ)) := by
    funext i
    rw [Pi.star_apply, ← starRingEnd_apply, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [hd, Matrix.mul_assoc]

/-- **The modular power is unitary**: `A^{it} ∈ unitary`. -/
lemma upow_mem_unitary {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    upow hA t ∈ unitary (Matrix n n ℂ) := by
  have hconj : star (upow hA t) = cpow hA (-((t : ℂ) * Complex.I)) := by
    rw [Matrix.star_eq_conjTranspose]
    simp only [upow]
    rw [cpow_conjTranspose]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [hconj]; simp only [upow]; rw [cpow_mul_cpow, neg_add_cancel, cpow_zero]
  · rw [hconj]; simp only [upow]; rw [cpow_mul_cpow, add_neg_cancel, cpow_zero]

/-! ## The analytic continuation of the intertwining relation -/

variable {ρ σ : DensityMatrix n} {Λ : KrausChannel n}

/-- **Kraus intertwining at the KMS point.** Analytic continuation of the imaginary-axis
multiplicative-domain relations to `z = 1/2`: each Kraus operator intertwines the modular
half-power cocycle `W = (Λρ)^{1/2}(Λσ)^{-1/2}` with its image under `Λ†`. -/
theorem kraus_intertwine_rpow_half (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hInt : IntertwinesIt hρ hσ hΛρ hΛσ) (i : Λ.ι) :
    ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ)) * Λ.K i
      = Λ.K i * Λ.adj ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ)) := by
  set C : ℂ → Matrix n n ℂ := fun z => cpow hΛρ z * cpow hΛσ (-z) with hC
  set G : ℂ → Matrix n n ℂ := fun z => C z * Λ.K i - Λ.K i * Λ.adj (C z) with hG
  have hCdiff : EntriesDifferentiable C :=
    (cpow_comp_entriesDifferentiable hΛρ differentiable_id).mul
      (cpow_comp_entriesDifferentiable hΛσ differentiable_id.neg)
  have hdiff : EntriesDifferentiable G :=
    (hCdiff.mul (EntriesDifferentiable.const (Λ.K i))).sub
      ((EntriesDifferentiable.const (Λ.K i)).mul (EntriesDifferentiable.adj Λ hCdiff))
  have hvan : ∀ t : ℝ, G ((t : ℂ) * Complex.I) = 0 := by
    intro t
    simp only [hG, hC]
    have hCit : cpow hΛρ ((t : ℂ) * Complex.I) * cpow hΛσ (-((t : ℂ) * Complex.I))
        = upow hΛρ t * upow hΛσ (-t) := by
      have e : (-((t : ℂ) * Complex.I)) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [e]; rfl
    rw [hCit, sub_eq_zero]
    set U := upow hΛρ t * upow hΛσ (-t) with hU
    have hUmem : U ∈ unitary (Matrix n n ℂ) :=
      mul_mem (upow_mem_unitary hΛρ t) (upow_mem_unitary hΛσ (-t))
    have hAdjU : Λ.adj U = upow hρ t * upow hσ (-t) := hInt t
    have hAdjUmem : Λ.adj U ∈ unitary (Matrix n n ℂ) := by
      rw [hAdjU]; exact mul_mem (upow_mem_unitary hρ t) (upow_mem_unitary hσ (-t))
    have hks : Λ.adj (Uᴴ * U) = (Λ.adj U)ᴴ * Λ.adj U := by
      have h1 : Uᴴ * U = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hUmem.1
      have h2 : (Λ.adj U)ᴴ * Λ.adj U = 1 := by
        rw [← Matrix.star_eq_conjTranspose]; exact hAdjUmem.1
      rw [h1, h2, Λ.adj_unital]
    exact Λ.intertwine_of_adj_eq hks i
  have hzero := matrix_eq_zero_of_entriesDifferentiable_of_imagAxis hdiff hvan (1 / 2 : ℂ)
  simp only [hG, hC] at hzero
  have e1 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  have e2 : ((-(1 / 2) : ℝ) : ℂ) = -(1 / 2 : ℂ) := by push_cast; ring
  rw [← cpow_ofReal_eq_rpow hΛρ (1 / 2), ← cpow_ofReal_eq_rpow hΛσ (-(1 / 2)), e1, e2]
  rw [sub_eq_zero] at hzero
  exact hzero

/-- **Multiplicative-domain equality at the KMS point.** The Kadison–Schwarz inequality is an
equality at `W = (Λρ)^{1/2}(Λσ)^{-1/2}`. -/
theorem adj_wStar_w_eq (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hInt : IntertwinesIt hρ hσ hΛρ hΛσ) :
    Λ.adj (((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ))ᴴ
        * ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ)))
      = (Λ.adj ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ)))ᴴ
        * Λ.adj ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ)) := by
  set W := (Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ) with hW
  have hInter : ∀ i, W * Λ.K i = Λ.K i * Λ.adj W :=
    fun i => kraus_intertwine_rpow_half hρ hσ hΛρ hΛσ hInt i
  have hInterH : ∀ i, (Λ.K i)ᴴ * Wᴴ = (Λ.adj W)ᴴ * (Λ.K i)ᴴ := by
    intro i
    rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hInter i]
  have hstep : ∀ i, (Λ.K i)ᴴ * (Wᴴ * W) * Λ.K i
      = (Λ.adj W)ᴴ * ((Λ.K i)ᴴ * Λ.K i) * Λ.adj W := by
    intro i
    have hL : (Λ.K i)ᴴ * (Wᴴ * W) * Λ.K i = ((Λ.K i)ᴴ * Wᴴ) * (W * Λ.K i) := by
      simp only [Matrix.mul_assoc]
    rw [hL, hInterH i, hInter i]
    simp only [Matrix.mul_assoc]
  rw [show Λ.adj (Wᴴ * W) = ∑ i, (Λ.K i)ᴴ * (Wᴴ * W) * Λ.K i from rfl,
    Finset.sum_congr rfl fun i _ => hstep i, ← Finset.sum_mul, ← Finset.mul_sum, Λ.htp,
    Matrix.mul_one]

/-- **Petz recovery from the modular intertwining.** If the channel `Λ` satisfies the imaginary-axis
modular intertwining condition `IntertwinesIt`, then its Petz recovery map reconstructs the input
state from its image: `petz σ Λ (Λ ρ) = ρ`. This is the sufficiency direction of the finite-
dimensional Petz recovery theorem. -/
theorem intertwinesIt_imp_recovery (ρ σ : DensityMatrix n) (Λ : KrausChannel n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) (hΛρ : (Λ.toDM ρ).val.PosDef)
    (hΛσ : (Λ.toDM σ).val.PosDef) (hInt : IntertwinesIt hρ hσ hΛρ hΛσ) :
    petz σ Λ (Λ.toDM ρ).val = ρ.val := by
  have hσsp : IsStrictlyPositive σ.val := hσ.isStrictlyPositive
  have hΛσsp : IsStrictlyPositive (Λ.toDM σ).val := hΛσ.isStrictlyPositive
  have hHermΛρ : ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))ᴴ = (Λ.toDM ρ).val ^ (1 / 2 : ℝ) :=
    (CFC.rpow_nonneg (a := (Λ.toDM ρ).val) (y := (1 / 2 : ℝ))).posSemidef.1
  have hHermΛσ : ((Λ.toDM σ).val ^ (-(1 / 2) : ℝ))ᴴ = (Λ.toDM σ).val ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg (a := (Λ.toDM σ).val) (y := (-(1 / 2) : ℝ))).posSemidef.1
  have hHermρ : (ρ.val ^ (1 / 2 : ℝ))ᴴ = ρ.val ^ (1 / 2 : ℝ) :=
    (CFC.rpow_nonneg (a := ρ.val) (y := (1 / 2 : ℝ))).posSemidef.1
  have hHermσ : (σ.val ^ (-(1 / 2) : ℝ))ᴴ = σ.val ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg (a := σ.val) (y := (-(1 / 2) : ℝ))).posSemidef.1
  have hAdjW : Λ.adj ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ))
      = ρ.val ^ (1 / 2 : ℝ) * σ.val ^ (-(1 / 2) : ℝ) :=
    intertwinesIt_rpow_half hρ hσ hΛρ hΛσ hInt
  have hrr : (Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM ρ).val ^ (1 / 2 : ℝ) = (Λ.toDM ρ).val := by
    rw [← CFC.rpow_add hΛρ.isStrictlyPositive.isUnit, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num,
      CFC.rpow_one _ hΛρ.posSemidef.nonneg]
  have hrr2 : ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (1 / 2 : ℝ) = ρ.val := by
    rw [← CFC.rpow_add hρ.isStrictlyPositive.isUnit, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num,
      CFC.rpow_one _ hρ.posSemidef.nonneg]
  have hsqrtinv : CFC.sqrt (Ring.inverse (Λ.toDM σ).val) = (Λ.toDM σ).val ^ (-(1 / 2) : ℝ) := by
    rw [CFC.sqrt_eq_rpow, CFC.inverse_eq_rpow_neg_one hΛσsp,
      CFC.rpow_rpow _ _ _ (by norm_num) hΛσsp, show ((-1 : ℝ) * (1 / 2)) = -(1 / 2) by norm_num]
  -- the inner argument of the Petz map equals Wᴴ * W
  have hInner : CFC.conjSqrt (Ring.inverse (Λ.toDM σ).val) (Λ.toDM ρ).val
      = ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ))ᴴ
        * ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ)) := by
    rw [CFC.conjSqrt_apply, hsqrtinv, Matrix.conjTranspose_mul, hHermΛρ, hHermΛσ,
      Matrix.mul_assoc ((Λ.toDM σ).val ^ (-(1 / 2) : ℝ)) ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))
        ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ)),
      ← Matrix.mul_assoc ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)) ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))
        ((Λ.toDM σ).val ^ (-(1 / 2) : ℝ)), hrr]
    simp only [Matrix.mul_assoc]
  -- final cancellations
  have hcancelL : σ.val ^ (1 / 2 : ℝ) * σ.val ^ (-(1 / 2) : ℝ) = 1 :=
    CFC.rpow_mul_rpow_neg (1 / 2) hσsp
  have hcancelR : σ.val ^ (-(1 / 2) : ℝ) * σ.val ^ (1 / 2 : ℝ) = 1 :=
    CFC.rpow_neg_mul_rpow (1 / 2) hσsp
  unfold petz
  rw [hInner, adj_wStar_w_eq hρ hσ hΛρ hΛσ hInt, hAdjW, CFC.conjSqrt_apply, CFC.sqrt_eq_rpow,
    Matrix.conjTranspose_mul, hHermρ, hHermσ]
  calc σ.val ^ (1 / 2 : ℝ)
        * (σ.val ^ (-(1 / 2) : ℝ) * ρ.val ^ (1 / 2 : ℝ)
          * (ρ.val ^ (1 / 2 : ℝ) * σ.val ^ (-(1 / 2) : ℝ)))
        * σ.val ^ (1 / 2 : ℝ)
      = (σ.val ^ (1 / 2 : ℝ) * σ.val ^ (-(1 / 2) : ℝ))
          * (ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (1 / 2 : ℝ))
          * (σ.val ^ (-(1 / 2) : ℝ) * σ.val ^ (1 / 2 : ℝ)) := by
        simp only [Matrix.mul_assoc]
    _ = ρ.val := by rw [hcancelL, hcancelR, hrr2, Matrix.one_mul, Matrix.mul_one]

end ErgodicTheory.OperatorEntropy.Lieb

end

