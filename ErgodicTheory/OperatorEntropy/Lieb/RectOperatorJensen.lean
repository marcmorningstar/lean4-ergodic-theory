/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.Dilation

/-!
# Rectangular operator-Jensen inequality for `-log` (Petz sufficiency crux, issue #28)

Given a **rectangular** isometry `W : Matrix p q ℂ` (`Wᴴ W = 1`, columns orthonormal, forcing
`|q| ≤ |p|`) and a positive-definite `X : Matrix p p ℂ`, the compression map `Φ(Y) = Wᴴ Y W`
is unital (`Φ 1 = 1`) and completely positive, but — unlike a *square* isometry, which is a
unitary and yields equality — genuinely loses information.  The Choi / Hansen–Pedersen–Jensen
operator-Jensen inequality for the operator-convex function `-log` reads

`cfc (-log) (Wᴴ X W) ≤ Wᴴ (cfc (-log) X) W`.

This is the real data-processing / Loewner crux that unblocks the sufficiency direction of
the Petz recovery theorem (#28): the square case is trivial equality, the rectangular case
carries the DPI loss.

## Route

The heart of the argument is a **corner-pinching** inequality on a `q ⊕ r` block matrix
(`sum_corner_loewner`): for operator-convex `f` and a self-adjoint `M` with spectrum in `I`,

`cfc f (M.submatrix Sum.inl Sum.inl) ≤ (cfc f M).submatrix Sum.inl Sum.inl`,

proved by the Effros pinching `½ M + ½ V M V = diag(M₁₁, M₂₂)` with the self-adjoint unitary
involution `V = diag(1, -1)` and operator convexity at dimension `|q ⊕ r|`.  The rectangular
theorem then follows by extending the columns of `W` to a unitary `U : Matrix p p ℂ`
(`exists_unitary_extend`), so `Wᴴ X W = (Uᴴ X U).submatrix ι ι` is a corner of the
conjugate `M = Uᴴ X U` (with `spectrum M = spectrum X`), and reindexing `p ≃ q ⊕ r`.

## Main results

* `ErgodicTheory.OperatorEntropy.Lieb.sum_corner_loewner`: the block corner-pinching inequality.
* `ErgodicTheory.OperatorEntropy.Lieb.rect_isometry_neg_log_loewner`: the rectangular `-log`
  operator-Jensen inequality (issue #28 crux).
-/

open Matrix
open scoped MatrixOrder ComplexOrder InnerProductSpace

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

/-! ## General-index reindexing star-algebra equivalence -/

section GeneralIndex

variable {s t : Type*} [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]

/-- Reindexing along `e : s ≃ t` as an `ℂ`-star-algebra equivalence of matrix algebras. -/
def reIx (e : s ≃ t) : Matrix s s ℂ ≃⋆ₐ[ℂ] Matrix t t ℂ :=
  StarAlgEquiv.ofAlgEquiv (reindexAlgEquiv ℂ ℂ e) fun M => by
    simp only [reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose]
    exact (conjTranspose_reindex e e M).symm

lemma reIx_apply (e : s ≃ t) (M : Matrix s s ℂ) : reIx e M = M.submatrix e.symm e.symm := rfl

lemma reIx_continuous (e : s ≃ t) :
    Continuous (reIx e : Matrix s s ℂ → Matrix t t ℂ) := by
  refine continuous_matrix fun i j => ?_
  simp only [reIx_apply, Matrix.submatrix_apply]
  exact (continuous_apply (e.symm j)).comp (continuous_apply (e.symm i))

lemma reIx_smul (e : s ≃ t) (r : ℝ) (P : Matrix s s ℂ) :
    reIx e (r • P) = r • reIx e P := by ext i j; rfl

/-- Reindexing by an equiv preserves the real spectrum. -/
lemma spectrum_reIx (e : s ≃ t) (M : Matrix s s ℂ) :
    spectrum ℝ (M.submatrix e.symm e.symm) = spectrum ℝ M := by
  have hval : (M.submatrix e.symm e.symm) = reindexAlgEquiv ℝ ℂ e M := by ext i j; rfl
  rw [hval, AlgEquiv.spectrum_eq]

/-- The continuous functional calculus commutes with reindexing by an equiv. -/
lemma cfc_reIx (e : s ≃ t) (M : Matrix s s ℂ) (hM : IsSelfAdjoint M) (f : ℝ → ℝ) :
    cfc f (M.submatrix e.symm e.symm) = (cfc f M).submatrix e.symm e.symm := by
  have hcont : ContinuousOn f (spectrum ℝ M) :=
    (Matrix.finite_real_spectrum (A := M)).continuousOn f
  have hsa' : IsSelfAdjoint (reIx e M) := by
    rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hM]
  have h := StarAlgHomClass.map_cfc (reIx e) f M hcont (reIx_continuous e) hM hsa'
  simp only [reIx_apply] at h
  exact h.symm

omit [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t] in
/-- Reindexing by an equiv reflects the Loewner order. -/
lemma reIx_le_reflect (e : s ≃ t) {A B : Matrix s s ℂ}
    (h : A.submatrix e.symm e.symm ≤ B.submatrix e.symm e.symm) : A ≤ B := by
  rw [Matrix.le_iff] at h ⊢
  have hsub : (B.submatrix e.symm e.symm - A.submatrix e.symm e.symm)
      = (B - A).submatrix e.symm e.symm := by
    ext i j; simp [Matrix.sub_apply, Matrix.submatrix_apply]
  rw [hsub] at h
  exact (posSemidef_submatrix_equiv e.symm).mp h

set_option maxHeartbeats 400000 in -- reindex-transport of operator convexity
/-- Operator convexity transported to an arbitrary finite index type (midpoint form). -/
lemma operatorConvex_index {I : Set ℝ} {f : ℝ → ℝ} (hf : OperatorConvexOn I f)
    (P Q : Matrix s s ℂ)
    (hP : IsSelfAdjoint P ∧ spectrum ℝ P ⊆ I) (hQ : IsSelfAdjoint Q ∧ spectrum ℝ Q ⊆ I) :
    cfc f ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)
      ≤ (1 / 2 : ℝ) • cfc f P + (1 / 2 : ℝ) • cfc f Q := by
  have hcontP : ContinuousOn f (spectrum ℝ P) :=
    (Matrix.finite_real_spectrum (A := P)).continuousOn f
  have hcontQ : ContinuousOn f (spectrum ℝ Q) :=
    (Matrix.finite_real_spectrum (A := Q)).continuousOn f
  set e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s with he
  have hΦPsa : IsSelfAdjoint (reIx e P) := by
    rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hP.1]
  have hΦQsa : IsSelfAdjoint (reIx e Q) := by
    rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hQ.1]
  have hΦPsp : spectrum ℝ (reIx e P) ⊆ I := by
    rw [reIx_apply, spectrum_reIx]; exact hP.2
  have hΦQsp : spectrum ℝ (reIx e Q) ⊆ I := by
    rw [reIx_apply, spectrum_reIx]; exact hQ.2
  have hmcP : reIx e (cfc f P) = cfc f (reIx e P) :=
    StarAlgHomClass.map_cfc (reIx e) f P hcontP (reIx_continuous e) hP.1 hΦPsa
  have hmcQ : reIx e (cfc f Q) = cfc f (reIx e Q) :=
    StarAlgHomClass.map_cfc (reIx e) f Q hcontQ (reIx_continuous e) hQ.1 hΦQsa
  have hconv := (hf (Fintype.card s)).2 (Set.mem_setOf.mpr ⟨hΦPsa, hΦPsp⟩)
    (Set.mem_setOf.mpr ⟨hΦQsa, hΦQsp⟩) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have eL : (1 / 2 : ℝ) • reIx e P + (1 / 2 : ℝ) • reIx e Q
      = reIx e ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q) := by
    rw [map_add, reIx_smul, reIx_smul]
  have eR : (1 / 2 : ℝ) • cfc f (reIx e P) + (1 / 2 : ℝ) • cfc f (reIx e Q)
      = reIx e ((1 / 2 : ℝ) • cfc f P + (1 / 2 : ℝ) • cfc f Q) := by
    rw [map_add, reIx_smul, reIx_smul, hmcP, hmcQ]
  have hcontPQ : ContinuousOn f (spectrum ℝ ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)) :=
    (Matrix.finite_real_spectrum (A := (1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)).continuousOn f
  have hPQsa : IsSelfAdjoint ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q) := by
    rw [isSelfAdjoint_iff, star_add, star_smul, star_smul,
      isSelfAdjoint_iff.mp hP.1, isSelfAdjoint_iff.mp hQ.1, star_trivial]
  have hΦPQsa : IsSelfAdjoint (reIx e ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)) := by
    rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hPQsa]
  have hconv' : cfc f ((1 / 2 : ℝ) • reIx e P + (1 / 2 : ℝ) • reIx e Q)
      ≤ (1 / 2 : ℝ) • cfc f (reIx e P) + (1 / 2 : ℝ) • cfc f (reIx e Q) := hconv
  rw [eL, ← StarAlgHomClass.map_cfc (reIx e) f _ hcontPQ (reIx_continuous e) hPQsa hΦPQsa, eR]
    at hconv'
  exact reIx_le_reflect e hconv'

/-- Spectrum invariance under unitary conjugation (general index, right form). -/
lemma spectrum_conj_gen {n : Type*} [Fintype n] [DecidableEq n] {W a : Matrix n n ℂ}
    (hW1 : star W * W = 1) (hW2 : W * star W = 1) :
    spectrum ℝ (W * a * star W) = spectrum ℝ a := by
  have hmem : W ∈ unitary (Matrix n n ℂ) := Unitary.mem_iff.mpr ⟨hW1, hW2⟩
  exact Unitary.spectrum_star_right_conjugate (R := ℝ) (a := a) (U := ⟨W, hmem⟩)

end GeneralIndex

/-! ## Corner-pinching on a `q ⊕ r` block matrix -/

section SumBlock

variable {q r : Type*} [Fintype q] [DecidableEq q] [Fintype r] [DecidableEq r]

/-- The `±1` sign vector on `q ⊕ r`. -/
def sgn (q r : Type*) : q ⊕ r → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

omit [Fintype q] [DecidableEq q] [Fintype r] [DecidableEq r] in
@[simp] lemma sgn_inl (j : q) : sgn q r (Sum.inl j) = 1 := rfl

omit [Fintype q] [Fintype r] in
/-- The involution `V = diag(1, -1)` is self-adjoint. -/
lemma diagonal_sgn_star : star (diagonal (sgn q r)) = diagonal (sgn q r) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1; funext x; cases x <;> simp [sgn]

/-- The involution `V = diag(1, -1)` squares to `1`. -/
lemma diagonal_sgn_mul_self :
    diagonal (sgn q r) * diagonal (sgn q r) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun i => sgn q r i * sgn q r i) = (fun _ => (1 : ℂ)) by
    funext x; cases x <;> simp [sgn]]
  exact Matrix.diagonal_one

/-- `f` of a block-diagonal `q ⊕ r` matrix is block-diagonal. -/
lemma cfc_fromBlocks_diag {A : Matrix q q ℂ} {B : Matrix r r ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (f : ℝ → ℝ) :
    cfc f (fromBlocks A 0 0 B) = fromBlocks (cfc f A) 0 0 (cfc f B) := by
  have hAh : A.IsHermitian := hA
  have hBh : B.IsHermitian := hB
  -- unitary of the block-diagonal eigenvector matrices
  have hUas2 : (hAh.eigenvectorUnitary : Matrix q q ℂ)
      * star (hAh.eigenvectorUnitary : Matrix q q ℂ) = 1 := Unitary.coe_mul_star_self _
  have hUas1 : star (hAh.eigenvectorUnitary : Matrix q q ℂ)
      * (hAh.eigenvectorUnitary : Matrix q q ℂ) = 1 := Unitary.coe_star_mul_self _
  have hUbs2 : (hBh.eigenvectorUnitary : Matrix r r ℂ)
      * star (hBh.eigenvectorUnitary : Matrix r r ℂ) = 1 := Unitary.coe_mul_star_self _
  have hUbs1 : star (hBh.eigenvectorUnitary : Matrix r r ℂ)
      * (hBh.eigenvectorUnitary : Matrix r r ℂ) = 1 := Unitary.coe_star_mul_self _
  set W : Matrix (q ⊕ r) (q ⊕ r) ℂ :=
    fromBlocks (hAh.eigenvectorUnitary : Matrix q q ℂ) 0 0
      (hBh.eigenvectorUnitary : Matrix r r ℂ) with hWdef
  have hWstar : star W = fromBlocks (star (hAh.eigenvectorUnitary : Matrix q q ℂ)) 0 0
      (star (hBh.eigenvectorUnitary : Matrix r r ℂ)) := by
    rw [hWdef, Matrix.star_eq_conjTranspose, fromBlocks_conjTranspose]
    simp [Matrix.star_eq_conjTranspose]
  have hW1 : star W * W = 1 := by
    rw [hWstar, hWdef, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hUas1, hUbs1]
    exact fromBlocks_one
  have hW2 : W * star W = 1 := by
    rw [hWstar, hWdef, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hUas2, hUbs2]
    exact fromBlocks_one
  -- spectral decompositions of A and B
  have hspecA : A = (hAh.eigenvectorUnitary : Matrix q q ℂ)
      * diagonal (fun i => (hAh.eigenvalues i : ℂ))
      * star (hAh.eigenvectorUnitary : Matrix q q ℂ) := by
    have h := hAh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hAh.eigenvalues) = fun i => (hAh.eigenvalues i : ℂ) := by
      funext i; rfl
    rw [hRC] at h; exact h
  have hspecB : B = (hBh.eigenvectorUnitary : Matrix r r ℂ)
      * diagonal (fun i => (hBh.eigenvalues i : ℂ))
      * star (hBh.eigenvectorUnitary : Matrix r r ℂ) := by
    have h := hBh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hBh.eigenvalues) = fun i => (hBh.eigenvalues i : ℂ) := by
      funext i; rfl
    rw [hRC] at h; exact h
  have hDsa : IsSelfAdjoint (fromBlocks (diagonal (fun i => (hAh.eigenvalues i : ℂ))) 0 0
      (diagonal (fun i => (hBh.eigenvalues i : ℂ)))) := by
    rw [fromBlocks_diagonal, isSelfAdjoint_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]
    congr 1; funext x; cases x <;> simp [Complex.conj_ofReal]
  -- fromBlocks A 0 0 B = W * D * star W
  have hdecomp : fromBlocks A 0 0 B = W * fromBlocks (diagonal (fun i => (hAh.eigenvalues i : ℂ)))
      0 0 (diagonal (fun i => (hBh.eigenvalues i : ℂ))) * star W := by
    rw [hWstar, hWdef, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [← hspecA, ← hspecB]
  rw [hdecomp, ErgodicTheory.OperatorEntropy.cfc_conj W _ hW1 hW2 hDsa f, fromBlocks_diagonal]
  rw [show (Sum.elim (fun i => (hAh.eigenvalues i : ℂ)) (fun i => (hBh.eigenvalues i : ℂ)))
      = (fun x => ((Sum.elim hAh.eigenvalues hBh.eigenvalues x : ℝ) : ℂ)) by
    funext x; cases x <;> rfl]
  rw [cfc_diagonal]
  rw [show (fun x => (f ((Sum.elim hAh.eigenvalues hBh.eigenvalues) x) : ℂ))
      = Sum.elim (fun i => (f (hAh.eigenvalues i) : ℂ)) (fun i => (f (hBh.eigenvalues i) : ℂ)) by
    funext x; cases x <;> rfl]
  rw [← fromBlocks_diagonal, hWstar, hWdef, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← cfc_hermitian_eq hAh, ← cfc_hermitian_eq hBh]

/-- The `(0,0)`-corner of `fromBlocks A B C D` is `A`. -/
lemma fromBlocks_submatrix_inl_inl {α β l m : Type*} (A : Matrix α l ℂ) (B : Matrix α m ℂ)
    (C : Matrix β l ℂ) (D : Matrix β m ℂ) :
    (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by
  ext i j; simp [Matrix.submatrix_apply]

/-- The pinching identity `½ M + ½ V M V = diag(M₁₁, M₂₂)` for `V = diag(1, -1)`. -/
lemma pinch_sum (M : Matrix (q ⊕ r) (q ⊕ r) ℂ) :
    (1 / 2 : ℝ) • M + (1 / 2 : ℝ) • (diagonal (sgn q r) * M * diagonal (sgn q r))
      = fromBlocks (M.submatrix Sum.inl Sum.inl) 0 0 (M.submatrix Sum.inr Sum.inr) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Complex.real_smul]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [sgn, fromBlocks, Matrix.submatrix_apply] <;> ring

/-- Conjugation by `V = diag(1, -1)` fixes the `(inl, inl)`-corner. -/
lemma Vconj_sub_inl (Y : Matrix (q ⊕ r) (q ⊕ r) ℂ) :
    (diagonal (sgn q r) * Y * diagonal (sgn q r)).submatrix Sum.inl Sum.inl
      = Y.submatrix Sum.inl Sum.inl := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, sgn_inl]
  ring

set_option maxHeartbeats 800000 in -- large block-pinch / cfc dilation assembly
/-- **Corner-pinching Loewner inequality.**  For operator-convex `f` and self-adjoint `M`
with spectrum in `I`, the compression to the `inl`-corner satisfies
`cfc f (M₁₁) ≤ (cfc f M)₁₁`.  This is the genuine data-processing loss of the rectangular
operator-Jensen inequality. -/
theorem sum_corner_loewner {I : Set ℝ} {f : ℝ → ℝ} (hf : OperatorConvexOn I f)
    (M : Matrix (q ⊕ r) (q ⊕ r) ℂ) (hMsa : IsSelfAdjoint M) (hMsp : spectrum ℝ M ⊆ I) :
    cfc f (M.submatrix Sum.inl Sum.inl) ≤ (cfc f M).submatrix Sum.inl Sum.inl := by
  have hVsa : star (diagonal (sgn q r)) = diagonal (sgn q r) := diagonal_sgn_star
  have hVV : diagonal (sgn q r) * diagonal (sgn q r) = 1 := diagonal_sgn_mul_self
  have hVdiagsa : IsSelfAdjoint (diagonal (sgn q r)) := isSelfAdjoint_iff.mpr hVsa
  have hVMVsa : IsSelfAdjoint (diagonal (sgn q r) * M * diagonal (sgn q r)) :=
    hMsa.conjugate_self hVdiagsa
  have hVMVsp : spectrum ℝ (diagonal (sgn q r) * M * diagonal (sgn q r)) ⊆ I := by
    have h := spectrum_conj_gen (W := diagonal (sgn q r)) (a := M)
      (by rw [hVsa]; exact hVV) (by rw [hVsa]; exact hVV)
    rw [hVsa] at h; rw [h]; exact hMsp
  have hconv := operatorConvex_index hf M (diagonal (sgn q r) * M * diagonal (sgn q r))
    ⟨hMsa, hMsp⟩ ⟨hVMVsa, hVMVsp⟩
  -- self-adjointness of the corner blocks
  have hMh : M.IsHermitian := hMsa
  have hM11sa : IsSelfAdjoint (M.submatrix (Sum.inl : q → q ⊕ r) Sum.inl) :=
    hMh.submatrix Sum.inl
  have hM22sa : IsSelfAdjoint (M.submatrix (Sum.inr : r → q ⊕ r) Sum.inr) :=
    hMh.submatrix Sum.inr
  -- LHS block
  have hLHS : (cfc f ((1 / 2 : ℝ) • M + (1 / 2 : ℝ)
        • (diagonal (sgn q r) * M * diagonal (sgn q r)))).submatrix Sum.inl Sum.inl
      = cfc f (M.submatrix Sum.inl Sum.inl) := by
    rw [pinch_sum, cfc_fromBlocks_diag hM11sa hM22sa f, fromBlocks_submatrix_inl_inl]
  -- `cfc f (V M V) = V (cfc f M) V`
  have hcfcVMV : cfc f (diagonal (sgn q r) * M * diagonal (sgn q r))
      = diagonal (sgn q r) * cfc f M * diagonal (sgn q r) := by
    have h := ErgodicTheory.OperatorEntropy.cfc_conj (diagonal (sgn q r)) M
      (by rw [hVsa]; exact hVV) (by rw [hVsa]; exact hVV) hMsa f
    rw [hVsa] at h; exact h
  -- RHS block
  have hRHS : ((1 / 2 : ℝ) • cfc f M + (1 / 2 : ℝ)
        • cfc f (diagonal (sgn q r) * M * diagonal (sgn q r))).submatrix Sum.inl Sum.inl
      = (cfc f M).submatrix Sum.inl Sum.inl := by
    rw [hcfcVMV]
    have key : ((1 / 2 : ℝ) • cfc f M + (1 / 2 : ℝ)
          • (diagonal (sgn q r) * cfc f M * diagonal (sgn q r))).submatrix Sum.inl Sum.inl
        = (1 / 2 : ℝ) • (cfc f M).submatrix Sum.inl Sum.inl
          + (1 / 2 : ℝ) • (diagonal (sgn q r) * cfc f M
              * diagonal (sgn q r)).submatrix Sum.inl Sum.inl := rfl
    rw [key, Vconj_sub_inl, ← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
  -- monotonicity of the corner
  have hmono : (cfc f ((1 / 2 : ℝ) • M + (1 / 2 : ℝ)
        • (diagonal (sgn q r) * M * diagonal (sgn q r)))).submatrix Sum.inl Sum.inl
      ≤ ((1 / 2 : ℝ) • cfc f M + (1 / 2 : ℝ)
        • cfc f (diagonal (sgn q r) * M * diagonal (sgn q r))).submatrix Sum.inl Sum.inl := by
    rw [Matrix.le_iff] at hconv ⊢
    have hsub : (((1 / 2 : ℝ) • cfc f M + (1 / 2 : ℝ)
          • cfc f (diagonal (sgn q r) * M * diagonal (sgn q r)))
          - cfc f ((1 / 2 : ℝ) • M + (1 / 2 : ℝ)
          • (diagonal (sgn q r) * M * diagonal (sgn q r)))).submatrix Sum.inl Sum.inl
        = (((1 / 2 : ℝ) • cfc f M + (1 / 2 : ℝ)
          • cfc f (diagonal (sgn q r) * M * diagonal (sgn q r))).submatrix Sum.inl Sum.inl
          - (cfc f ((1 / 2 : ℝ) • M + (1 / 2 : ℝ)
          • (diagonal (sgn q r) * M * diagonal (sgn q r)))).submatrix Sum.inl Sum.inl) := by
      ext i j; simp [Matrix.sub_apply, Matrix.submatrix_apply]
    rw [← hsub]; exact hconv.submatrix Sum.inl
  rw [hLHS, hRHS] at hmono
  exact hmono

end SumBlock

end ErgodicTheory.OperatorEntropy.Lieb

end
