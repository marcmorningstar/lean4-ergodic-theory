/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.RigidityTail
import Oseledets.OperatorEntropy.Lieb.PetzSufficiencyClosed

/-!
# Contraction rigidity spine (issue #28, GENERAL case — route b″)

This module is the **contraction refactor** of `RigidityTail`.  In the general Petz-sufficiency case
(any `KrausChannel Λ`, all four states faithful) the vectorised Petz map `W` is a *contraction*
(`Wᴴ W ≤ 1`), no longer an isometry (`Wᴴ W = 1`), but it stays in faithful `PosDef` land
(Petz 2003, Thm 2).  The rigidity spine must therefore be refactored from
`RigidityTail.isometry_resolvent_intertwine_of_neg_log_eq` (isometry, exact compression) to the
contraction form proved here.

## The geometry (directions, carefully)

* `W : Matrix (Fin M) (Fin N) ℂ` maps the **output** space `Fin N` into the **input** space `Fin M`;
  `Wᴴ W : Fin N → Fin N` is a contraction `≤ 1`, and `W` is *injective* (faithful state).
* `Δ : Matrix (Fin M) (Fin M) ℂ` is the **input** relative modular operator (`PosDef`).
* `Δout : Matrix (Fin N) (Fin N) ℂ` is the **output** relative modular operator (`PosDef`).
* `ξ : Fin N → ℂ` is the **output cyclic vector**; `W *ᵥ ξ` is the input cyclic vector.

## The two-piece gap split

Set `X := Δ + t` (`PosDef`), `Y := Wᴴ X W = Wᴴ Δ W + t·WᴴW` (`PosDef`, needs `W` injective).
The per-`t` gap quadratic form at `ξ`,

`G t := ⟪ξ, (Wᴴ (Δ+t)⁻¹ W − (Δout+t)⁻¹) ξ⟫`,

splits through the intermediate resolvent `Y⁻¹`:

`Wᴴ (Δ+t)⁻¹ W − (Δout+t)⁻¹ = [Wᴴ X⁻¹ W − Y⁻¹] + [Y⁻¹ − (Δout+t)⁻¹] = A(t) + B(t)`.

* **A(t) — contraction resolvent-Jensen gap** (`contraction_resolvent_gap_nonneg`).  Equal, at `ξ`,
  to the `X`-weighted square of the error vector `a := X⁻¹(Wξ) − W(Y⁻¹ξ)` via the
  `contraction_quadratic_gap_identity`.  The isometry identity `Wᴴ W = 1` fails, but the *defect*
  correction is **annihilated** by `(1 − WᴴW) ξ = 0` (`contraction_defect_mulVec_eq_zero`).
* **B(t) — operator-antitone gap** (`compression_shift_le` + `posDef_inv_le_inv`).  Since
  `WᴴΔW ≤ Δout` and `1 − WᴴW ⪰ 0`, one has `Y = Wᴴ(Δ+t)W ≤ Δout + t`, so by antitone-inverse
  `(Δout+t)⁻¹ ≤ Y⁻¹`, i.e. `B(t) ⪰ 0` as an *operator*.

Both nonneg ⟹ `G t ≥ 0`; the `(1+t)⁻¹(1−WᴴW)` regulariser term of `resIntegrand` vanishes at `ξ`,
so `∫₀^∞ G t = ⟪ξ, (Wᴴ(−log Δ)W − (−log Δout)) ξ⟫`.  The `−log` saturation `hgap` makes this `0`;
a nonnegative continuous integrand with zero integral is pointwise zero, so `G t = 0`, forcing
`A(t) = 0` **and** `⟪ξ, B(t) ξ⟫ = 0`, chaining to the recovery intertwining
`(Δ+t)⁻¹(Wξ) = W((Δout+t)⁻¹ξ)`.
-/

open Matrix MeasureTheory Set
open scoped MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {M N : ℕ}

/-! ## Step 0 — the saturation defect vanishes at `ξ` -/

/-- **Defect annihilation.**  For a contraction `W` (`Wᴴ W ≤ 1`), the norm-saturation
`⟪Wξ, Wξ⟫ = ⟪ξ, ξ⟫` forces the contraction defect `E := 1 − WᴴW ⪰ 0` to annihilate `ξ`:
`(1 − WᴴW) *ᵥ ξ = 0`. -/
lemma contraction_defect_mulVec_eq_zero (W : Matrix (Fin M) (Fin N) ℂ) (ξ : Fin N → ℂ)
    (hWc : Wᴴ * W ≤ 1)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ) :
    (1 - Wᴴ * W) *ᵥ ξ = 0 := by
  have hE : (1 - Wᴴ * W).PosSemidef := Matrix.le_iff.mp hWc
  have hqf : star ξ ⬝ᵥ (Wᴴ * W) *ᵥ ξ = star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) := by
    have h := qform_conj W 1 ξ
    rw [Matrix.mul_one, Matrix.one_mulVec] at h
    exact h
  have hzero : star ξ ⬝ᵥ (1 - Wᴴ * W) *ᵥ ξ = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hqf, hsat, sub_self]
  exact posSemidef_vec_expectation_zero hE hzero

/-! ## Step 1 — the CRUX: the contraction quadratic-gap identity -/

/-- **CRUX — contraction quadratic-gap identity.**  For a contraction/injective `W`, positive
definite `X`, compression `Y := Wᴴ X W`, and the error vector `a := X⁻¹(Wξ) − W(Y⁻¹ξ)`, *under the
defect condition* `(1 − WᴴW) ξ = 0`,

`⟪a, X a⟫ = ⟪ξ, (Wᴴ X⁻¹ W − Y⁻¹) ξ⟫`.

The pure matrix identity `Pᴴ X P = Wᴴ X⁻¹ W − Y⁻¹(WᴴW) − (WᴴW)Y⁻¹ + Y⁻¹` (with
`P := X⁻¹ W − W Y⁻¹`) holds always; the two defect terms collapse to `−2⟪ξ, Y⁻¹ ξ⟫` after pairing
with `ξ`, using `WᴴW ξ = ξ` and the Hermitian symmetry of `WᴴW`. -/
lemma contraction_quadratic_gap_identity (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} (ξ : Fin N → ℂ)
    (hWinj : Function.Injective W.mulVec) (hX : X.PosDef)
    (hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0) :
    star (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ))
        ⬝ᵥ (X *ᵥ (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ)))
      = star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ) := by
  set Y := Wᴴ * X * W with hYdef
  have hY : Y.PosDef := hX.conjTranspose_mul_mul_same hWinj
  have hXdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit
  have hYdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  have hX1 : X⁻¹ * X = 1 := nonsing_inv_mul X hXdet
  have hX2 : X * X⁻¹ = 1 := mul_nonsing_inv X hXdet
  have hXinvH : X⁻¹ᴴ = X⁻¹ := hX.1.inv
  have hYinvH : Y⁻¹ᴴ = Y⁻¹ := hY.1.inv
  -- the defect facts
  have hWWξ : (Wᴴ * W) *ᵥ ξ = ξ := by
    have h := hdefect
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  have hWWH : (Wᴴ * W)ᴴ = Wᴴ * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  set P : Matrix (Fin M) (Fin N) ℂ := X⁻¹ * W - W * Y⁻¹ with hPdef
  have hPH : Pᴴ = Wᴴ * X⁻¹ - Y⁻¹ * Wᴴ := by
    rw [hPdef]
    simp only [conjTranspose_sub, conjTranspose_mul, hXinvH, hYinvH]
  have hYWXW : Wᴴ * X * W = Y := hYdef.symm
  -- the pure matrix identity (no defect used)
  have hPXP : Pᴴ * X * P = Wᴴ * X⁻¹ * W - Y⁻¹ * (Wᴴ * W) - Wᴴ * W * Y⁻¹ + Y⁻¹ := by
    have hPXe : Pᴴ * X = Wᴴ - Y⁻¹ * Wᴴ * X := by
      rw [hPH, Matrix.sub_mul, Matrix.mul_assoc Wᴴ X⁻¹ X, hX1, Matrix.mul_one]
    rw [hPXe, hPdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
    have t1 : Wᴴ * (X⁻¹ * W) = Wᴴ * X⁻¹ * W := (Matrix.mul_assoc Wᴴ X⁻¹ W).symm
    have t2 : Y⁻¹ * Wᴴ * X * (X⁻¹ * W) = Y⁻¹ * (Wᴴ * W) := by
      rw [Matrix.mul_assoc (Y⁻¹ * Wᴴ) X (X⁻¹ * W), ← Matrix.mul_assoc X X⁻¹ W, hX2,
        Matrix.one_mul, Matrix.mul_assoc Y⁻¹ Wᴴ W]
    have t3 : Wᴴ * (W * Y⁻¹) = Wᴴ * W * Y⁻¹ := (Matrix.mul_assoc Wᴴ W Y⁻¹).symm
    have t4 : Y⁻¹ * Wᴴ * X * (W * Y⁻¹) = Y⁻¹ := by
      have hreassoc : Y⁻¹ * Wᴴ * X * (W * Y⁻¹) = Y⁻¹ * (Wᴴ * X * W) * Y⁻¹ := by
        simp only [Matrix.mul_assoc]
      rw [hreassoc, hYWXW, nonsing_inv_mul Y hYdet, Matrix.one_mul]
    rw [t1, t2, t3, t4]
    abel
  -- rewrite the error vector as `P *ᵥ ξ`
  have ha_eq : X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Y⁻¹ *ᵥ ξ) = P *ᵥ ξ := by
    rw [hPdef, sub_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [ha_eq]
  -- the defect-collapse of the two middle terms
  have hS2 : star ξ ⬝ᵥ ((Y⁻¹ * (Wᴴ * W)) *ᵥ ξ) = star ξ ⬝ᵥ (Y⁻¹ *ᵥ ξ) := by
    rw [← Matrix.mulVec_mulVec, hWWξ]
  have hS3 : star ξ ⬝ᵥ ((Wᴴ * W * Y⁻¹) *ᵥ ξ) = star ξ ⬝ᵥ (Y⁻¹ *ᵥ ξ) := by
    rw [← Matrix.mulVec_mulVec, ← hWWH, ← star_mulVec_dotProduct, hWWξ]
  have hstep : star (P *ᵥ ξ) ⬝ᵥ (X *ᵥ (P *ᵥ ξ))
      = star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - Y⁻¹ * (Wᴴ * W) - Wᴴ * W * Y⁻¹ + Y⁻¹) *ᵥ ξ) := by
    calc star (P *ᵥ ξ) ⬝ᵥ (X *ᵥ (P *ᵥ ξ))
        = star (P *ᵥ ξ) ⬝ᵥ ((X * P) *ᵥ ξ) := by rw [mulVec_mulVec]
      _ = star ξ ⬝ᵥ (Pᴴ *ᵥ ((X * P) *ᵥ ξ)) := star_mulVec_dotProduct P ξ _
      _ = star ξ ⬝ᵥ ((Pᴴ * (X * P)) *ᵥ ξ) := by rw [mulVec_mulVec]
      _ = star ξ ⬝ᵥ ((Pᴴ * X * P) *ᵥ ξ) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hPXP]
  rw [hstep]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add]
  rw [hS2, hS3]
  ring

/-! ## Step 2 — nonnegativity and rigidity of the contraction resolvent-Jensen gap `A(t)` -/

/-- **Contraction resolvent-Jensen nonnegativity at `ξ`** (piece `A`). -/
lemma contraction_resolvent_gap_nonneg (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} (ξ : Fin N → ℂ)
    (hWinj : Function.Injective W.mulVec) (hX : X.PosDef)
    (hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0) :
    0 ≤ (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)).re := by
  rw [← contraction_quadratic_gap_identity W ξ hWinj hX hdefect]
  have := hX.posSemidef.dotProduct_mulVec_nonneg
    (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ))
  exact (Complex.nonneg_iff.mp this).1

/-- **Contraction resolvent rigidity** (piece `A` saturation). -/
lemma contraction_resolvent_saturation_intertwines (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} (ξ : Fin N → ℂ)
    (hWinj : Function.Injective W.mulVec) (hX : X.PosDef)
    (hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0)
    (hsat0 : (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)).re = 0) :
    X⁻¹ *ᵥ (W *ᵥ ξ) = W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ) := by
  set a := X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ) with hadef
  have hid : (star a ⬝ᵥ (X *ᵥ a)).re = 0 := by
    rw [hadef, contraction_quadratic_gap_identity W ξ hWinj hX hdefect]; exact hsat0
  by_contra hne
  have ha : a ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < star a ⬝ᵥ (X *ᵥ a) := hX.dotProduct_mulVec_pos ha
  have : 0 < (star a ⬝ᵥ (X *ᵥ a)).re := (Complex.pos_iff.mp hpos).1
  rw [hid] at this
  exact lt_irrefl 0 this

/-! ## Step 3 — the operator-antitone gap `B(t)` -/

section InvAntitone

variable {k : ℕ}

/-- The `ℝ`-linear star-algebra equivalence `Matrix ≃ CStarMatrix` (identity carrier), transporting
the Loewner order and the ring structure onto the `C⋆`-algebra where the antitone-inverse lemma
lives.  (A local copy of the transport used in `OperatorConvex`.) -/
private def toCStarK : Matrix (Fin k) (Fin k) ℂ ≃⋆ₐ[ℝ] CStarMatrix (Fin k) (Fin k) ℂ :=
  (CStarMatrix.ofMatrixStarAlgEquiv).restrictScalars ℝ

private lemma nonneg_toCStarK (a : Matrix (Fin k) (Fin k) ℂ) :
    (0 : CStarMatrix (Fin k) (Fin k) ℂ) ≤ toCStarK a ↔ (0 : Matrix (Fin k) (Fin k) ℂ) ≤ a := by
  rw [StarOrderedRing.nonneg_iff, StarOrderedRing.nonneg_iff]
  exact Iff.rfl

private lemma toCStarK_mono {a b : Matrix (Fin k) (Fin k) ℂ} (h : a ≤ b) :
    toCStarK a ≤ toCStarK b := by
  rw [← sub_nonneg] at h ⊢
  rw [show toCStarK b - toCStarK a = toCStarK (b - a) from (map_sub toCStarK b a).symm,
    nonneg_toCStarK (b - a)]
  exact h

private lemma toCStarK_symm_mono {u v : CStarMatrix (Fin k) (Fin k) ℂ} (h : u ≤ v) :
    toCStarK.symm u ≤ toCStarK.symm v := by
  rw [← sub_nonneg] at h ⊢
  rw [show toCStarK.symm v - toCStarK.symm u = toCStarK.symm (v - u) from
      (map_sub toCStarK.symm v u).symm,
    ← nonneg_toCStarK (toCStarK.symm (v - u)), toCStarK.apply_symm_apply]
  exact h

private lemma isStrictlyPositive_toCStarK {a : Matrix (Fin k) (Fin k) ℂ} (ha : a.PosDef) :
    IsStrictlyPositive (toCStarK a) := by
  rw [IsStrictlyPositive.iff_of_unital]
  refine ⟨(nonneg_toCStarK a).mpr ?_, IsUnit.map toCStarK ha.isUnit⟩
  rw [Matrix.le_iff]
  simpa using ha.posSemidef

private lemma toCStarK_ringInverse {a : Matrix (Fin k) (Fin k) ℂ} (ha : IsUnit a) :
    Ring.inverse (toCStarK a) = toCStarK (Ring.inverse a) := by
  have hb : IsUnit (toCStarK a) := IsUnit.map toCStarK ha
  have hmul : (↑hb.unit : CStarMatrix (Fin k) (Fin k) ℂ) * toCStarK (Ring.inverse a) = 1 := by
    rw [hb.unit_spec, ← map_mul toCStarK, Ring.mul_inverse_cancel a ha, map_one]
  rw [Ring.inverse_of_isUnit hb]
  exact Units.inv_eq_of_mul_eq_one_right hmul

/-- **Antitone inverse.**  For positive definite `A ≤ B`, the inverses reverse: `B⁻¹ ≤ A⁻¹`.
Transports `CStarAlgebra.antitoneOn_ringInverse` through the `toCStarK` order equivalence. -/
lemma posDef_inv_le_inv {A B : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have hApos : IsStrictlyPositive (toCStarK A) := isStrictlyPositive_toCStarK hA
  have hBpos : IsStrictlyPositive (toCStarK B) := isStrictlyPositive_toCStarK hB
  have hab' : toCStarK A ≤ toCStarK B := toCStarK_mono hAB
  have hinv : Ring.inverse (toCStarK B) ≤ Ring.inverse (toCStarK A) :=
    CStarAlgebra.antitoneOn_ringInverse hApos hBpos hab'
  rw [toCStarK_ringInverse hB.isUnit, toCStarK_ringInverse hA.isUnit,
    ← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse] at hinv
  have hsymm := toCStarK_symm_mono hinv
  rwa [toCStarK.symm_apply_apply, toCStarK.symm_apply_apply] at hsymm

end InvAntitone

/-- **Compression shift inequality** (piece `B`).  Since `WᴴΔW ≤ Δout` and `1 − WᴴW ⪰ 0`,
`Wᴴ (Δ + t) W ≤ Δout + t`, because
`(Δout + t) − Wᴴ(Δ+t)W = (Δout − WᴴΔW) + t·(1 − WᴴW) ⪰ 0`. -/
lemma compression_shift_le (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (Δout : Matrix (Fin N) (Fin N) ℂ)
    (hWc : Wᴴ * W ≤ 1) (hcompLe : Wᴴ * Δ * W ≤ Δout) {t : ℝ} (ht : 0 < t) :
    Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W
      ≤ Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t := by
  have hE : (1 - Wᴴ * W).PosSemidef := Matrix.le_iff.mp hWc
  have hcomp : (Δout - Wᴴ * Δ * W).PosSemidef := Matrix.le_iff.mp hcompLe
  have hreg : Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t * W = t • (Wᴴ * W) := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [Matrix.le_iff]
  have hexpand : (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)
      - Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W
      = (Δout - Wᴴ * Δ * W) + t • (1 - Wᴴ * W) := by
    rw [Matrix.mul_add, Matrix.add_mul, hreg, Algebra.algebraMap_eq_smul_one, smul_sub]
    abel
  rw [hexpand]
  exact hcomp.add (hE.smul ht.le)

/-! ## Step 4 — the per-`t` two-piece rigidity -/

/-- **Per-`t` recovery intertwining.**  If the full per-`t` gap `G t` vanishes at `ξ`, then both
pieces vanish and chaining the two saturations gives `(Δ+t)⁻¹(Wξ) = W((Δout+t)⁻¹ξ)`. -/
lemma contraction_resolvent_perT_intertwine (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (Δout : Matrix (Fin N) (Fin N) ℂ) (ξ : Fin N → ℂ)
    (hWinj : Function.Injective W.mulVec) (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0) {t : ℝ} (ht : 0 < t)
    (hGzero : (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
        - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)).re = 0) :
    (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
      = W *ᵥ ((Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ) := by
  set X := Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t with hXdef
  set Out := Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t with hOutdef
  have hX : X.PosDef := hΔ.add_posSemidef (posDef_algebraMap ht).posSemidef
  have hOut : Out.PosDef := hΔout.add_posSemidef (posDef_algebraMap ht).posSemidef
  have hY : (Wᴴ * X * W).PosDef := hX.conjTranspose_mul_mul_same hWinj
  have hle : Wᴴ * X * W ≤ Out := compression_shift_le W Δ Δout hWc hcompLe ht
  have hBps : ((Wᴴ * X * W)⁻¹ - Out⁻¹).PosSemidef :=
    Matrix.le_iff.mp (posDef_inv_le_inv hY hOut hle)
  have hA : 0 ≤ (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)).re :=
    contraction_resolvent_gap_nonneg W ξ hWinj hX hdefect
  have hB : 0 ≤ (star ξ ⬝ᵥ (((Wᴴ * X * W)⁻¹ - Out⁻¹) *ᵥ ξ)).re :=
    (Complex.nonneg_iff.mp (hBps.dotProduct_mulVec_nonneg ξ)).1
  have hGsplit : star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - Out⁻¹) *ᵥ ξ)
      = star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)
        + star ξ ⬝ᵥ (((Wᴴ * X * W)⁻¹ - Out⁻¹) *ᵥ ξ) := by
    rw [← dotProduct_add, ← add_mulVec]
    congr 2
    abel
  have hGre : (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - Out⁻¹) *ᵥ ξ)).re
      = (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)).re
        + (star ξ ⬝ᵥ (((Wᴴ * X * W)⁻¹ - Out⁻¹) *ᵥ ξ)).re := by
    rw [hGsplit, Complex.add_re]
  rw [hGre] at hGzero
  have hA0 : (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)).re = 0 := by linarith
  have hB0 : (star ξ ⬝ᵥ (((Wᴴ * X * W)⁻¹ - Out⁻¹) *ᵥ ξ)).re = 0 := by linarith
  have hAint : X⁻¹ *ᵥ (W *ᵥ ξ) = W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ) :=
    contraction_resolvent_saturation_intertwines W ξ hWinj hX hdefect hA0
  have hBint : ((Wᴴ * X * W)⁻¹ - Out⁻¹) *ᵥ ξ = 0 := posSemidef_vec_expectation_re_zero hBps hB0
  have hBeq : (Wᴴ * X * W)⁻¹ *ᵥ ξ = Out⁻¹ *ᵥ ξ := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hBint; exact hBint
  rw [hAint, hBeq]

/-! ## Step 5 — the main contraction rigidity theorem -/

/-- **Contraction rigidity tail (resolvent form).**  If the *contraction* `W` (`Wᴴ W ≤ 1`,
injective), with input modular `Δ` and output modular `Δout` satisfying the monotone compression
bound `Wᴴ Δ W ≤ Δout`, saturates the operator-Jensen inequality for `−log` at the norm-saturating
cyclic vector `ξ` (`hgap`, `hsat`), then it intertwines every resolvent on `ξ`:  for all `t > 0`,

`(Δ + t)⁻¹ (W ξ) = W ((Δout + t)⁻¹ ξ)`. -/
theorem contraction_resolvent_intertwine_of_neg_log_eq (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (Δout : Matrix (Fin N) (Fin N) ℂ) (ξ : Fin N → ℂ)
    (hWinj : Function.Injective W.mulVec) (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ)
    (hgap : (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ
              = cfc (fun x => -Real.log x) Δout *ᵥ ξ) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ) := by
  classical
  have hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0 := contraction_defect_mulVec_eq_zero W ξ hWc hsat
  have hWWξ : (Wᴴ * W) *ᵥ ξ = ξ := by
    have h := hdefect
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  -- the contraction regulariser is annihilated at `ξ`
  have hregvec : ∀ c : ℝ, (Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c * W) *ᵥ ξ
      = algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) c *ᵥ ξ := by
    intro c
    have hmat : Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c * W = c • (Wᴴ * W) := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [hmat, Matrix.smul_mulVec, hWWξ, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  -- The two real-linear functionals composed with `Re`.
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
  -- `F t` equals the gap quadratic form at the shift `Δ + t`.
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
  -- Nonnegativity of `F` on `(0, ∞)`.
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
  -- Continuity of `F` on `(0, ∞)`.
  have hFcont : ContinuousOn F (Ioi 0) := by
    simp only [hF]
    exact (LMre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand Δ hΔ)).sub
      (LNre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand Δout hΔout))
  have hFint : IntegrableOn F (Ioi 0) := by simp only [hF]; exact hg1int.sub hg2int
  -- The integral of `F` vanishes (from the `-log` saturation `hgap`).
  have hInt0 : ∫ t in Ioi 0, F t = 0 := by
    have hI1 : ∫ t in Ioi 0, LMre (cfc (resIntegrand t) Δ)
        = LMre (cfc (fun x => -Real.log x) Δ) := by
      rw [LMre.integral_comp_comm hintM, ← cfc_neg_log_eq_integral Δ hΔ]
    have hI2 : ∫ t in Ioi 0, LNre (cfc (resIntegrand t) Δout)
        = LNre (cfc (fun x => -Real.log x) Δout) := by
      rw [LNre.integral_comp_comm hintN, ← cfc_neg_log_eq_integral Δout hΔout]
    have hLeq : LMre (cfc (fun x => -Real.log x) Δ)
        = LNre (cfc (fun x => -Real.log x) Δout) := by
      rw [hLMre, hLNre, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        qformCLM_conj, qformCLM_apply, hgap]
    simp only [hF]
    rw [integral_sub hg1int hg2int, hI1, hI2, hLeq, sub_self]
  -- Nonnegative continuous integrand with zero integral ⟹ pointwise zero.
  have hae0 : F =ᵐ[volume.restrict (Ioi 0)] 0 := by
    have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi 0)] F :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hFnn)
    exact (setIntegral_eq_zero_iff_of_nonneg_ae hnn_ae hFint).mp hInt0
  have hFzero : Set.EqOn F 0 (Ioi 0) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae0 isOpen_Ioi hFcont continuousOn_const
  -- Conclude the resolvent intertwining pointwise via the per-`t` rigidity.
  intro t ht
  have hGzero : (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
      - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)).re = 0 := by
    rw [← hFeq t ht]; exact hFzero ht
  exact contraction_resolvent_perT_intertwine W Δ Δout ξ hWinj hWc hΔ hΔout hcompLe hdefect ht
    hGzero

/-! ## PART A evidence — `hpj_affine` instantiates at the resolvent `(·+t)⁻¹` -/
example (t : ℝ) (I : Set ℝ) (hf : OperatorConvexOn I (fun x => (x + t)⁻¹))
    {n : ℕ} (A B X Y : Matrix (Fin n) (Fin n) ℂ) (hAB : star A * A + star B * B = 1)
    (hX : IsSelfAdjoint X ∧ spectrum ℝ X ⊆ I) (hY : IsSelfAdjoint Y ∧ spectrum ℝ Y ⊆ I) :
    cfc (fun x => (x + t)⁻¹) (star A * X * A + star B * Y * B)
      ≤ star A * cfc (fun x => (x + t)⁻¹) X * A + star B * cfc (fun x => (x + t)⁻¹) Y * B :=
  hpj_affine (fun x => (x + t)⁻¹) I hf A B X Y hAB hX hY

end Oseledets.OperatorEntropy.Lieb

end
