import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Fischer's inequality for real Gram matrices

For a real matrix `Y = [Y_F | Y_S]` partitioned into column blocks, the Gram determinant of the
whole block is at most the product of the diagonal-block Gram determinants:
`det (Yᵀ Y) ≤ det (Y_Fᵀ Y_F) · det (Y_Sᵀ Y_S)`.

The route is the **Schur complement + positive-semidefinite determinant monotonicity**:
* `det_le_one_of_le_one`: a PSD matrix dominated by `1` in the Loewner order has determinant `≤ 1`.
* `posDef_exists_whitening`: every positive definite matrix `C` admits a *whitening* `B` with
  `Bᴴ C B = 1` (built from the spectral theorem: `B = U · diag(1/√λ)`).
* `PosSemidef.det_le_det_of_le`: positive-semidefinite determinant monotonicity
  `0 ⪯ S ⪯ C, C ≻ 0 ⟹ det S ≤ det C`, by whitening `C` to `1` and applying `det_le_one_of_le_one`.
* The Schur complement determinant formula `Matrix.det_fromBlocks₁₁` then yields Fischer.
-/

open scoped MatrixOrder
open Matrix

namespace Fischer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Each eigenvalue of a symmetric real matrix dominated by `1` in the Loewner order is `≤ 1`. -/
lemma eigenvalue_le_one_of_le_one {X : Matrix n n ℝ} (hX : X.IsHermitian) (hX1 : X ≤ 1)
    (j : n) : hX.eigenvalues j ≤ 1 := by
  have hPSD : (1 - X).PosSemidef := Matrix.le_iff.mp hX1
  set v : n → ℝ := ⇑(hX.eigenvectorBasis j) with hv
  have key := hPSD.dotProduct_mulVec_nonneg v
  have hμ : hX.eigenvalues j = star v ⬝ᵥ (X *ᵥ v) := by
    have h := hX.eigenvalues_eq j
    rw [← hv] at h
    simpa using h
  have hnorm : star v ⬝ᵥ v = 1 := by
    rw [hv, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      real_inner_self_eq_norm_sq]
    have := hX.eigenvectorBasis.orthonormal.1 j
    rw [this]; norm_num
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hnorm] at key
  rw [hμ]; linarith

/-- A positive-semidefinite matrix dominated by `1` in the Loewner order has determinant `≤ 1`. -/
lemma det_le_one_of_le_one {X : Matrix n n ℝ} (hX : X.PosSemidef) (hX1 : X ≤ 1) :
    X.det ≤ 1 := by
  rw [hX.isHermitian.det_eq_prod_eigenvalues]
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
  · exact hX.eigenvalues_nonneg i
  · exact eigenvalue_le_one_of_le_one hX.isHermitian hX1 i

/-- **Whitening.** Every positive definite real matrix `C` admits a matrix `B` with `Bᴴ C B = 1`.
Constructed from the spectral theorem: with `C = U · diag(λ) · Uᴴ` (`U` orthogonal, `λ > 0`),
take `B = U · diag(1/√λ)`. -/
lemma posDef_exists_whitening {C : Matrix n n ℝ} (hC : C.PosDef) :
    ∃ B : Matrix n n ℝ, Bᴴ * C * B = 1 := by
  classical
  set U : Matrix n n ℝ := (hC.isHermitian.eigenvectorUnitary : Matrix n n ℝ) with hU
  set s : n → ℝ := fun i => (Real.sqrt (hC.isHermitian.eigenvalues i))⁻¹ with hs
  refine ⟨U * diagonal s, ?_⟩
  -- Uᴴ C U = diag(λ)
  have hUstar : (Uᴴ : Matrix n n ℝ) = star U := rfl
  have hdiag : Uᴴ * C * U = diagonal hC.isHermitian.eigenvalues := by
    have h := hC.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
    -- h : star ↑U' * C * ↑U' = diagonal (RCLike.ofReal ∘ eigenvalues)
    rw [RCLike.ofReal_real_eq_id, Function.id_comp] at h
    rw [← hU] at h
    rw [hUstar]
    exact h
  -- Bᴴ = diag(s)ᴴ * Uᴴ = diag(s) * Uᴴ
  rw [Matrix.conjTranspose_mul, diagonal_conjTranspose]
  have hss : (star s : n → ℝ) = s := by ext i; simp [hs]
  rw [hss]
  -- (diag s * Uᴴ) * C * (U * diag s) = diag s * (Uᴴ C U) * diag s
  have hregroup : diagonal s * Uᴴ * C * (U * diagonal s)
      = diagonal s * (Uᴴ * C * U) * diagonal s := by
    simp only [Matrix.mul_assoc]
  rw [hregroup, hdiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  rw [show (1 : Matrix n n ℝ) = diagonal (fun _ => (1 : ℝ)) from (diagonal_one).symm]
  congr 1
  ext i
  have hpos : 0 < hC.isHermitian.eigenvalues i := hC.eigenvalues_pos i
  have hsq : Real.sqrt (hC.isHermitian.eigenvalues i) ^ 2 = hC.isHermitian.eigenvalues i :=
    Real.sq_sqrt hpos.le
  have hsqrt_pos : 0 < Real.sqrt (hC.isHermitian.eigenvalues i) := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (hC.isHermitian.eigenvalues i) ≠ 0 := ne_of_gt hsqrt_pos
  show s i * hC.isHermitian.eigenvalues i * s i = 1
  have hsi : s i = (Real.sqrt (hC.isHermitian.eigenvalues i))⁻¹ := by rw [hs]
  rw [hsi]
  rw [mul_comm ((Real.sqrt (hC.isHermitian.eigenvalues i))⁻¹) (hC.isHermitian.eigenvalues i),
    mul_assoc, ← mul_inv, ← sq, hsq, mul_inv_cancel₀ (ne_of_gt hpos)]

/-- **Positive-semidefinite determinant monotonicity.** If `0 ⪯ S ⪯ C` in the Loewner order with
`C ≻ 0`, then `det S ≤ det C`. -/
lemma PosSemidef.det_le_det_of_le {S C : Matrix n n ℝ} (hS : S.PosSemidef) (hC : C.PosDef)
    (hSC : S ≤ C) : S.det ≤ C.det := by
  obtain ⟨B, hB⟩ := posDef_exists_whitening hC
  -- X := Bᴴ S B is PSD and ≤ Bᴴ C B = 1.
  set X : Matrix n n ℝ := Bᴴ * S * B with hX
  have hXpsd : X.PosSemidef := hS.conjTranspose_mul_mul_same B
  have hXle1 : X ≤ 1 := by
    rw [Matrix.le_iff, ← hB]
    have : Bᴴ * C * B - Bᴴ * S * B = Bᴴ * (C - S) * B := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [this]
    exact (Matrix.le_iff.mp hSC).conjTranspose_mul_mul_same B
  have hXdet : X.det ≤ 1 := det_le_one_of_le_one hXpsd hXle1
  -- det X = det(Bᴴ B) · det S, and det(Bᴴ C B) = 1 = det(Bᴴ B) · det C.
  have hdetX : X.det = (Bᴴ * B).det * S.det := by
    rw [hX, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]; ring
  have hdetBCB : (1 : Matrix n n ℝ).det = (Bᴴ * B).det * C.det := by
    rw [← hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]; ring
  rw [Matrix.det_one] at hdetBCB
  -- det C > 0, so det(Bᴴ B) = 1 / det C > 0.
  have hCpos : 0 < C.det := hC.det_pos
  have hBB_pos : 0 < (Bᴴ * B).det := by
    rcases lt_trichotomy ((Bᴴ * B).det) 0 with h | h | h
    · nlinarith [hdetBCB, hCpos]
    · rw [h] at hdetBCB; simp at hdetBCB
    · exact h
  -- det S ≤ det C ⟺ det(Bᴴ B) det S ≤ det(Bᴴ B) det C = 1, and det X = det(Bᴴ B) det S ≤ 1.
  have : (Bᴴ * B).det * S.det ≤ (Bᴴ * B).det * C.det := by
    rw [← hdetBCB, ← hdetX]; exact hXdet
  exact le_of_mul_le_mul_left this hBB_pos

/-- **Positive-semidefinite determinant monotonicity (general).** If `0 ⪯ S ⪯ C` in the Loewner
order with both `S` and `C` positive semidefinite, then `det S ≤ det C`. The positive definite case
is `PosSemidef.det_le_det_of_le`; the singular case `det C = 0` forces `det S = 0` because any null
vector of `C` is a null vector of `S`. -/
lemma PosSemidef.det_le_det_of_le' {S C : Matrix n n ℝ} (hS : S.PosSemidef) (hC : C.PosSemidef)
    (hSC : S ≤ C) : S.det ≤ C.det := by
  by_cases hCpd : C.PosDef
  · exact PosSemidef.det_le_det_of_le hS hCpd hSC
  · -- C singular: det C = 0, and det S = 0.
    have hCdet : C.det = 0 := by
      by_contra h
      exact hCpd (hC.posDef_iff_det_ne_zero.mpr h)
    rw [hCdet]
    obtain ⟨x, hx, hCx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hCdet
    have hCS : (C - S).PosSemidef := Matrix.le_iff.mp hSC
    have hquad : star x ⬝ᵥ S *ᵥ x = 0 := by
      have hle : star x ⬝ᵥ S *ᵥ x ≤ 0 := by
        have h0 := hCS.dotProduct_mulVec_nonneg x
        rw [Matrix.sub_mulVec, dotProduct_sub, hCx, dotProduct_zero] at h0
        linarith
      have hge : 0 ≤ star x ⬝ᵥ S *ᵥ x := hS.dotProduct_mulVec_nonneg x
      linarith
    have hSx : S *ᵥ x = 0 := (hS.dotProduct_mulVec_zero_iff x).mp hquad
    exact le_of_eq (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hSx⟩)

variable {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-- **Fischer's inequality (block form).** For a real positive semidefinite block matrix
`G = [[A, B], [Bᵀ, D]]`, the determinant is at most the product of the diagonal-block determinants:
`det G ≤ det A · det D`. Proved by the Schur complement determinant formula when `A` is positive
definite, and by a kernel argument (`det G = 0`) when `A` is singular. -/
theorem det_fromBlocks_le (A : Matrix m m ℝ) (B : Matrix m p ℝ) (D : Matrix p p ℝ)
    (hG : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).det ≤ A.det * D.det := by
  classical
  have hAeq : (Matrix.fromBlocks A B Bᴴ D).submatrix Sum.inl Sum.inl = A := by
    ext i j; simp [Matrix.submatrix_apply]
  have hDeq : (Matrix.fromBlocks A B Bᴴ D).submatrix Sum.inr Sum.inr = D := by
    ext i j; simp [Matrix.submatrix_apply]
  have hA : A.PosSemidef := hAeq ▸ hG.submatrix (Sum.inl : m → m ⊕ p)
  have hD : D.PosSemidef := hDeq ▸ hG.submatrix (Sum.inr : p → m ⊕ p)
  by_cases hApd : A.PosDef
  · -- A positive definite: Schur complement.
    letI := hApd.isUnit.invertible
    have hSc : (D - Bᴴ * A⁻¹ * B).PosSemidef := (Matrix.PosDef.fromBlocks₁₁ B D hApd).mp hG
    have hScle : (D - Bᴴ * A⁻¹ * B) ≤ D := by
      rw [Matrix.le_iff]
      have : D - (D - Bᴴ * A⁻¹ * B) = Bᴴ * A⁻¹ * B := by abel
      rw [this]
      exact (hApd.posSemidef.inv).conjTranspose_mul_mul_same B
    have hdetmono : (D - Bᴴ * A⁻¹ * B).det ≤ D.det :=
      PosSemidef.det_le_det_of_le' hSc hD hScle
    have hform : (Matrix.fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * ⅟A * B).det :=
      Matrix.det_fromBlocks₁₁ A B Bᴴ D
    rw [hform, Matrix.invOf_eq_nonsing_inv]
    exact mul_le_mul_of_nonneg_left hdetmono hApd.det_pos.le
  · -- A singular: det A = 0 and det G = 0.
    have hAdet : A.det = 0 := by
      by_contra h
      exact hApd (hA.posDef_iff_det_ne_zero.mpr h)
    rw [hAdet, zero_mul]
    obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hAdet
    -- the lifted vector (x, 0) is a null vector of G.
    set y : m ⊕ p → ℝ := Sum.elim x 0 with hy
    have hquad : star y ⬝ᵥ (Matrix.fromBlocks A B Bᴴ D) *ᵥ y = 0 := by
      rw [hy, Matrix.fromBlocks_mulVec]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero,
        Function.star_sumElim, star_zero, sumElim_dotProduct_sumElim, hAx, dotProduct_zero,
        zero_dotProduct, add_zero]
    have hGy : (Matrix.fromBlocks A B Bᴴ D) *ᵥ y = 0 :=
      (hG.dotProduct_mulVec_zero_iff y).mp hquad
    have hyne : y ≠ 0 := by
      intro h
      apply hx
      ext i
      have := congrFun h (Sum.inl i)
      simpa [hy] using this
    have : (Matrix.fromBlocks A B Bᴴ D).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hyne, hGy⟩
    rw [this]

variable {r : Type*} [Fintype r] [DecidableEq r]

omit [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] [DecidableEq r] in
/-- For a column-block matrix `Y` indexed by `m ⊕ p`, the cross-Gram matrix `Yᴴ Y` is the block
matrix `[[Y_Fᴴ Y_F, Y_Fᴴ Y_S], [Y_Sᴴ Y_F, Y_Sᴴ Y_S]]` of the block cross-Grams, where
`Y_F = Y.submatrix id Sum.inl` and `Y_S = Y.submatrix id Sum.inr`. -/
lemma gram_eq_fromBlocks (Y : Matrix r (m ⊕ p) ℝ) :
    Yᴴ * Y = Matrix.fromBlocks
      ((Y.submatrix id Sum.inl)ᴴ * Y.submatrix id Sum.inl)
      ((Y.submatrix id Sum.inl)ᴴ * Y.submatrix id Sum.inr)
      ((Y.submatrix id Sum.inr)ᴴ * Y.submatrix id Sum.inl)
      ((Y.submatrix id Sum.inr)ᴴ * Y.submatrix id Sum.inr) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Matrix.fromBlocks, Matrix.submatrix_apply]

omit [DecidableEq r] in
/-- **Fischer's inequality (column-block Gram form).** For any real matrix `Y` whose columns are
indexed by `m ⊕ p`, splitting the columns into the two blocks `Y_F` (indexed by `m`) and `Y_S`
(indexed by `p`), the full Gram determinant is at most the product of the two block Gram
determinants:
`det (Yᴴ Y) ≤ det (Y_Fᴴ Y_F) · det (Y_Sᴴ Y_S)`. -/
theorem det_gram_le (Y : Matrix r (m ⊕ p) ℝ) :
    (Yᴴ * Y).det
      ≤ ((Y.submatrix id Sum.inl)ᴴ * Y.submatrix id Sum.inl).det
        * ((Y.submatrix id Sum.inr)ᴴ * Y.submatrix id Sum.inr).det := by
  set YF := Y.submatrix id Sum.inl with hYF
  set YS := Y.submatrix id Sum.inr with hYS
  have hblock : Yᴴ * Y = Matrix.fromBlocks (YFᴴ * YF) (YFᴴ * YS) (YFᴴ * YS)ᴴ (YSᴴ * YS) := by
    rw [gram_eq_fromBlocks Y]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hblock]
  have hG : (Matrix.fromBlocks (YFᴴ * YF) (YFᴴ * YS) (YFᴴ * YS)ᴴ (YSᴴ * YS)).PosSemidef := by
    rw [← hblock]; exact Matrix.posSemidef_conjTranspose_mul_self Y
  exact det_fromBlocks_le (YFᴴ * YF) (YFᴴ * YS) (YSᴴ * YS) hG

omit [DecidableEq r] in
/-- **Inter-block sine bound (`sin² ≤ 1`).** With the inter-block squared sine defined as the ratio
`det(Yᴴ Y) / (det(Y_Fᴴ Y_F) · det(Y_Sᴴ Y_S))`, Fischer's inequality says it is at most `1`, and it
is always nonnegative; when both diagonal Gram blocks are nonsingular the denominator is positive so
the ratio is a genuine number in `[0, 1]`. -/
theorem sin_sq_le_one (Y : Matrix r (m ⊕ p) ℝ)
    (hF : 0 < ((Y.submatrix id Sum.inl)ᴴ * Y.submatrix id Sum.inl).det)
    (hS : 0 < ((Y.submatrix id Sum.inr)ᴴ * Y.submatrix id Sum.inr).det) :
    (Yᴴ * Y).det
        / (((Y.submatrix id Sum.inl)ᴴ * Y.submatrix id Sum.inl).det
          * ((Y.submatrix id Sum.inr)ᴴ * Y.submatrix id Sum.inr).det) ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact det_gram_le Y

omit [DecidableEq r] in
/-- The inter-block squared sine is nonnegative (the full Gram determinant is `≥ 0`). -/
theorem sin_sq_nonneg (Y : Matrix r (m ⊕ p) ℝ) :
    0 ≤ (Yᴴ * Y).det
        / (((Y.submatrix id Sum.inl)ᴴ * Y.submatrix id Sum.inl).det
          * ((Y.submatrix id Sum.inr)ᴴ * Y.submatrix id Sum.inr).det) := by
  apply div_nonneg
  · exact (Matrix.posSemidef_conjTranspose_mul_self Y).det_nonneg
  · exact mul_nonneg (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg

end Fischer
