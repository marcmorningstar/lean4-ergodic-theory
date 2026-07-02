/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib

/-!
# Strict operator convexity of `-log` (Petz equality, Lieb foundations)

This module proves the **equality/strict case** of the operator convexity of `x ↦ -Real.log x`
needed for the Petz equality theorem (issue #28).

The analytic heart is the **resolvent (ring-inverse) equality case**: for positive definite
matrices `X, Y`, the midpoint operator-convexity gap of the inverse vanishes iff `X = Y`.
Concretely, if `X⁻¹ + Y⁻¹ = 4 • (X + Y)⁻¹` (harmonic mean equals arithmetic mean at the
midpoint) then `X = Y`. The proof uses the explicit congruence identity
`(X - Y) (X + Y)⁻¹ (X - Y) = 0` together with positive-definiteness of `(X + Y)⁻¹`.

## Main results

* `Oseledets.OperatorEntropy.Lieb.posDef_eq_of_harmonic_eq_arithmetic`: the resolvent equality
  core — `X⁻¹ + Y⁻¹ = 4 • (X + Y)⁻¹` forces `X = Y` for positive definite `X, Y`.
* `Oseledets.OperatorEntropy.Lieb.posDef_eq_of_inv_midpoint_eq`: the same in midpoint (`2⁻¹ •`)
  form — strict midpoint operator convexity of the ring inverse.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {N : ℕ}

/-- If `D` is Hermitian, `S` is positive definite and `D * S * D = 0`, then `D = 0`.
This is the non-degeneracy of a `*`-congruence by a positive definite matrix. -/
lemma isHermitian_mul_posDef_mul_eq_zero {D S : Matrix (Fin N) (Fin N) ℂ}
    (hD : D.IsHermitian) (hS : S.PosDef) (h : D * S * D = 0) : D = 0 := by
  have hv : ∀ x : Fin N → ℂ, D *ᵥ x = 0 := by
    intro x
    by_contra hx
    have hzero : star (D *ᵥ x) ⬝ᵥ (S *ᵥ (D *ᵥ x)) = 0 := by
      have h1 : star x ⬝ᵥ ((Dᴴ * S * D) *ᵥ x) = star (D *ᵥ x) ⬝ᵥ (S *ᵥ (D *ᵥ x)) := by
        simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
      rw [← h1, hD, h]
      simp
    exact absurd hzero (ne_of_gt (hS.dotProduct_mulVec_pos hx))
  ext i j
  have hij := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using hij

/-- **Resolvent equality core.** For positive definite `X, Y`, if the harmonic mean equals the
arithmetic mean at the midpoint, i.e. `X⁻¹ + Y⁻¹ = 4 • (X + Y)⁻¹`, then `X = Y`. -/
theorem posDef_eq_of_harmonic_eq_arithmetic (X Y : Matrix (Fin N) (Fin N) ℂ)
    (hX : X.PosDef) (hY : Y.PosDef)
    (heq : X⁻¹ + Y⁻¹ = (4 : ℝ) • (X + Y)⁻¹) : X = Y := by
  have hM : (X + Y).PosDef := hX.add hY
  have hXdet : IsUnit X.det := X.isUnit_iff_isUnit_det.mp hX.isUnit
  have hYdet : IsUnit Y.det := Y.isUnit_iff_isUnit_det.mp hY.isUnit
  have hMdet : IsUnit (X + Y).det := (X + Y).isUnit_iff_isUnit_det.mp hM.isUnit
  -- [†]  4 • (X (X+Y)⁻¹ Y) = X + Y
  have key1 : (4 : ℝ) • (X * (X + Y)⁻¹ * Y) = X + Y := by
    have hL : X * (X⁻¹ + Y⁻¹) * Y = X + Y := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_nonsing_inv _ hXdet, Matrix.one_mul,
        mul_assoc, Matrix.nonsing_inv_mul _ hYdet, Matrix.mul_one, add_comm]
    calc (4 : ℝ) • (X * (X + Y)⁻¹ * Y)
          = X * ((4 : ℝ) • (X + Y)⁻¹) * Y := by rw [mul_smul_comm, smul_mul_assoc]
      _ = X * (X⁻¹ + Y⁻¹) * Y := by rw [← heq]
      _ = X + Y := hL
  -- [‡]  4 • (Y (X+Y)⁻¹ X) = X + Y
  have key2 : (4 : ℝ) • (Y * (X + Y)⁻¹ * X) = X + Y := by
    have hL2 : Y * (X⁻¹ + Y⁻¹) * X = X + Y := by
      rw [Matrix.mul_add, Matrix.add_mul, mul_assoc, Matrix.nonsing_inv_mul _ hXdet,
        Matrix.mul_one, Matrix.mul_nonsing_inv _ hYdet, Matrix.one_mul, add_comm]
    calc (4 : ℝ) • (Y * (X + Y)⁻¹ * X)
          = Y * ((4 : ℝ) • (X + Y)⁻¹) * X := by rw [mul_smul_comm, smul_mul_assoc]
      _ = Y * (X⁻¹ + Y⁻¹) * X := by rw [← heq]
      _ = X + Y := hL2
  -- R1  X (X+Y)⁻¹ X + X (X+Y)⁻¹ Y = X
  have R1 : X * (X + Y)⁻¹ * X + X * (X + Y)⁻¹ * Y = X := by
    rw [← Matrix.mul_add, mul_assoc, Matrix.nonsing_inv_mul _ hMdet, Matrix.mul_one]
  -- R2  Y (X+Y)⁻¹ Y + Y (X+Y)⁻¹ X = Y
  have R2 : Y * (X + Y)⁻¹ * Y + Y * (X + Y)⁻¹ * X = Y := by
    rw [← Matrix.mul_add, mul_assoc, add_comm Y X, Matrix.nonsing_inv_mul _ hMdet, Matrix.mul_one]
  -- express the two diagonal congruence blocks
  have ea : X * (X + Y)⁻¹ * X = X - X * (X + Y)⁻¹ * Y := eq_sub_of_add_eq R1
  have ed : Y * (X + Y)⁻¹ * Y = Y - Y * (X + Y)⁻¹ * X := eq_sub_of_add_eq R2
  -- the off-diagonal blocks as ℝ-multiples of X + Y
  have hb : X * (X + Y)⁻¹ * Y = (4 : ℝ)⁻¹ • (X + Y) :=
    (eq_inv_smul_iff₀ (by norm_num : (4 : ℝ) ≠ 0)).mpr key1
  have hc : Y * (X + Y)⁻¹ * X = (4 : ℝ)⁻¹ • (X + Y) :=
    (eq_inv_smul_iff₀ (by norm_num : (4 : ℝ) ≠ 0)).mpr key2
  -- the congruence expands and, using the block relations, `4 •` of it vanishes
  have hexp : (X - Y) * (X + Y)⁻¹ * (X - Y)
      = X * (X + Y)⁻¹ * X - X * (X + Y)⁻¹ * Y
        - Y * (X + Y)⁻¹ * X + Y * (X + Y)⁻¹ * Y := by
    noncomm_ring
  have hz : (X - Y) * (X + Y)⁻¹ * (X - Y) = 0 := by
    have h4 : (4 : ℝ) • ((X - Y) * (X + Y)⁻¹ * (X - Y)) = 0 := by
      rw [hexp, ea, ed, hb, hc]
      module
    exact (smul_eq_zero.mp h4).resolve_left (by norm_num)
  have hDsub : X - Y = 0 :=
    isHermitian_mul_posDef_mul_eq_zero (hX.isHermitian.sub hY.isHermitian) hM.inv hz
  exact sub_eq_zero.mp hDsub

/-- For an invertible matrix `M` and a nonzero real scalar `c`, `(c • M)⁻¹ = c⁻¹ • M⁻¹`. -/
lemma inv_real_smul {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsUnit M.det) {c : ℝ} (hc : c ≠ 0) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.mul_nonsing_inv _ hM]

/-- **Strict midpoint operator convexity of the ring inverse.** For positive definite `X, Y`,
if the inverse of the midpoint `(X + Y)/2` equals the midpoint `(X⁻¹ + Y⁻¹)/2` of the inverses,
then `X = Y`. This is the equality case of the operator convexity of `Ring.inverse`. -/
theorem posDef_eq_of_inv_midpoint_eq (X Y : Matrix (Fin N) (Fin N) ℂ)
    (hX : X.PosDef) (hY : Y.PosDef)
    (heq : ((2 : ℝ)⁻¹ • X + (2 : ℝ)⁻¹ • Y)⁻¹ = (2 : ℝ)⁻¹ • X⁻¹ + (2 : ℝ)⁻¹ • Y⁻¹) :
    X = Y := by
  have hM : (X + Y).PosDef := hX.add hY
  have hMdet : IsUnit (X + Y).det := (X + Y).isUnit_iff_isUnit_det.mp hM.isUnit
  have heqForm : (2 : ℝ) • (X + Y)⁻¹ = (2 : ℝ)⁻¹ • X⁻¹ + (2 : ℝ)⁻¹ • Y⁻¹ := by
    rw [← heq, ← smul_add, inv_real_smul (c := (2 : ℝ)⁻¹) hMdet (by norm_num), inv_inv]
  refine posDef_eq_of_harmonic_eq_arithmetic X Y hX hY ?_
  calc X⁻¹ + Y⁻¹
      = (2 : ℝ) • ((2 : ℝ)⁻¹ • X⁻¹ + (2 : ℝ)⁻¹ • Y⁻¹) := by module
    _ = (2 : ℝ) • ((2 : ℝ) • (X + Y)⁻¹) := by rw [heqForm]
    _ = (4 : ℝ) • (X + Y)⁻¹ := by rw [smul_smul]; norm_num

end Oseledets.OperatorEntropy.Lieb
