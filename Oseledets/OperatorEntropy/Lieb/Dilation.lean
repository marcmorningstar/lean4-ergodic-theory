/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.OperatorConvex
import Oseledets.OperatorEntropy.Lieb.DilationProto
import Oseledets.OperatorEntropy.RelEntropyAdditivity

/-!
# Hansen–Pedersen–Jensen operator-Jensen inequality (Lieb keystone)

Given an operator-convex `f` on an interval `I`, a "contraction pair" `A, B` with
`star A * A + star B * B = 1`, and self-adjoint `X, Y` with spectra in `I`, the
Hansen–Pedersen–Jensen inequality reads

`cfc f (star A * X * A + star B * Y * B) ≤ star A * cfc f X * A + star B * cfc f Y * B`.

We prove it by the Effros / Hansen–Pedersen **unitary dilation** method: work in the doubled
algebra `Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ`, form the block diagonal `D = diag(X, Y)`,
dilate `[A; B]` to a unitary `U` (from `exists_unitary_firstBlockCol`), and pinch
`M = star U * D * U` with the involution `V = diag(1, -1)`.  Operator convexity at dimension `2N`
applied to `M` and `V M V` yields the inequality on the pinched (block-diagonal) matrix, whose
`(0,0)`-block is exactly the claim.

## Main results

* `Oseledets.OperatorEntropy.Lieb.hpj_affine`: the affine (contraction) form.
* `Oseledets.OperatorEntropy.Lieb.hpj_isometry`: the isometry corollary.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {N : ℕ}

/-! ## The `2 × N` block-diagonal embedding -/

/-- `blockDiag2 P Q` is the block-diagonal matrix `diag(P, Q)` over `Fin 2 × Fin N`, with `P` in the
`0`-block and `Q` in the `1`-block. -/
def blockDiag2 (P Q : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 = 0 then P p.2 q.2 else Q p.2 q.2) else 0

@[simp] lemma blockDiag2_apply (P Q : Matrix (Fin N) (Fin N) ℂ) (p q : Fin 2 × Fin N) :
    blockDiag2 P Q p q = if p.1 = q.1 then (if p.1 = 0 then P p.2 q.2 else Q p.2 q.2) else 0 := rfl

lemma blockDiag2_one : blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) 1 = 1 := by
  ext ⟨a, i⟩ ⟨c, k⟩
  fin_cases a <;> fin_cases c <;>
    simp [blockDiag2, Matrix.one_apply, Prod.ext_iff, eq_comm]

lemma blockDiag2_star (P Q : Matrix (Fin N) (Fin N) ℂ) :
    star (blockDiag2 P Q) = blockDiag2 (star P) (star Q) := by
  ext ⟨a, i⟩ ⟨c, k⟩
  fin_cases a <;> fin_cases c <;>
    simp [blockDiag2, Matrix.star_apply, eq_comm]

lemma blockDiag2_mul (P Q P' Q' : Matrix (Fin N) (Fin N) ℂ) :
    blockDiag2 P Q * blockDiag2 P' Q' = blockDiag2 (P * P') (Q * Q') := by
  ext ⟨a, i⟩ ⟨c, k⟩
  simp only [Matrix.mul_apply, blockDiag2_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> fin_cases c <;> simp

lemma blockDiag2_diagonal (u v : Fin N → ℂ) :
    blockDiag2 (diagonal u) (diagonal v)
      = diagonal (fun p : Fin 2 × Fin N => if p.1 = 0 then u p.2 else v p.2) := by
  ext ⟨a, i⟩ ⟨c, k⟩
  fin_cases a <;> fin_cases c <;>
    simp [blockDiag2, Matrix.diagonal, Prod.ext_iff]

/-- The `(0,0)`-block of `blockDiag2 P Q` is `P`. -/
lemma blockDiag2_submatrix₀₀ (P Q : Matrix (Fin N) (Fin N) ℂ) :
    (blockDiag2 P Q).submatrix (fun j : Fin N => ((0 : Fin 2), j))
        (fun j : Fin N => ((0 : Fin 2), j)) = P := by
  ext i j
  simp [Matrix.submatrix_apply, blockDiag2]

lemma blockDiag2_isSelfAdjoint {P Q : Matrix (Fin N) (Fin N) ℂ}
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q) : IsSelfAdjoint (blockDiag2 P Q) := by
  rw [isSelfAdjoint_iff, blockDiag2_star, isSelfAdjoint_iff.mp hP, isSelfAdjoint_iff.mp hQ]

/-! ## Functional calculus of a real diagonal matrix (general `f`) -/

/-- **Continuous functional calculus of a real diagonal matrix.** For any `e : ι → ℝ`,
`cfc f (diagonal (e ·)) = diagonal (f ∘ e ·)`. Generalizes `cfc_log_diagonal`. -/
lemma cfc_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) (e : ι → ℝ) :
    cfc f (diagonal (fun i => (e i : ℂ))) = diagonal (fun i => (f (e i) : ℂ)) := by
  classical
  have hsa : IsSelfAdjoint (diagonal (fun i => (e i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal (e i)
  set S : Finset ℝ := Finset.image e Finset.univ with hSdef
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hpdef
  have hpeval : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    rw [hpdef]
    have h := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f)
      (Set.injOn_id _) hx
    simpa using h
  have hspec : spectrum ℝ (diagonal (fun i => (e i : ℂ))) ⊆ (S : Set ℝ) := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have hix : e i = x := by
      have hi' : ((e i : ℂ)) = ((x : ℂ)) := hi
      exact_mod_cast hi'
    rw [hSdef]
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hix⟩)
  rw [cfc_congr (a := diagonal (fun i => (e i : ℂ)))
      (fun x hx => (hpeval x (hspec hx)).symm),
    cfc_polynomial p _ hsa]
  have hstep : Polynomial.aeval (diagonal (fun i => (e i : ℂ))) p
      = diagonal (Polynomial.aeval (fun i => (e i : ℂ)) p) := by
    change Polynomial.aeval (Matrix.diagonalAlgHom (R := ℝ) (fun i => (e i : ℂ))) p
      = Matrix.diagonalAlgHom (R := ℝ) (Polynomial.aeval (fun i => (e i : ℂ)) p)
    exact Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom (R := ℝ)) (fun i => (e i : ℂ)) p
  rw [hstep]
  congr 1
  funext i
  have key : (Polynomial.aeval (fun i => (e i : ℂ)) p) i = Polynomial.aeval ((e i : ℂ)) p := by
    have h := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : ι => ℂ) i)
      (fun i => (e i : ℂ)) p
    simpa using h.symm
  rw [key]
  change Polynomial.aeval (algebraMap ℝ ℂ (e i)) p = (f (e i) : ℂ)
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    hpeval (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i))]
  rfl

/-- The spectrum of a real diagonal matrix is contained in the range of its entries. -/
lemma spectrum_diagonal_real_subset {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℝ)
    {I : Set ℝ} (h : ∀ i, e i ∈ I) : spectrum ℝ (diagonal (fun i => (e i : ℂ))) ⊆ I := by
  intro x hx
  rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
  obtain ⟨i, hi⟩ := hx
  have hix : e i = x := by
    have hi' : ((e i : ℂ)) = ((x : ℂ)) := hi
    exact_mod_cast hi'
  rw [← hix]; exact h i

/-! ## Block-corner extraction -/

/-- Multiplying `blockDiag2 P Q` onto the stacked column `[A; B]` acts blockwise. -/
lemma blockDiag2_mul_stacked (P Q A B : Matrix (Fin N) (Fin N) ℂ) :
    blockDiag2 P Q * stacked A B = stacked (P * A) (Q * B) := by
  ext ⟨a, i⟩ j
  simp only [Matrix.mul_apply, blockDiag2_apply, stacked, Matrix.of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> simp

/-- The Gram-type identity: `[A;B]ᴴ diag-mult `. -/
lemma stacked_star_mul_stacked (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    (stacked A B)ᴴ * stacked C D = star A * C + star B * D := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, stacked,
    Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Matrix.star_apply]

/-- **Block-corner extraction.** If `U`'s first block-column is `[A; B]`, then the `(0,0)`-block of
`U⋆ diag(P, Q) U` is `A⋆ P A + B⋆ Q B`. -/
lemma blockCorner (U : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ)
    (A B : Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ (i : Fin 2 × Fin N) (j : Fin N), U i ((0 : Fin 2), j) = stacked A B i j)
    (P Q : Matrix (Fin N) (Fin N) ℂ) :
    (star U * blockDiag2 P Q * U).submatrix (fun j : Fin N => ((0 : Fin 2), j))
        (fun j : Fin N => ((0 : Fin 2), j))
      = star A * P * A + star B * Q * B := by
  have hC : U.submatrix (id : Fin 2 × Fin N → Fin 2 × Fin N)
      (fun j : Fin N => ((0 : Fin 2), j)) = stacked A B := by
    ext p j; exact hU p j
  have hCs : (star U).submatrix (fun j : Fin N => ((0 : Fin 2), j))
      (id : Fin 2 × Fin N → Fin 2 × Fin N) = (stacked A B)ᴴ := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_submatrix, hC]
  rw [submatrix_mul (star U * blockDiag2 P Q) U (fun j : Fin N => ((0 : Fin 2), j))
      (id : Fin 2 × Fin N → Fin 2 × Fin N) (fun j : Fin N => ((0 : Fin 2), j))
      Function.bijective_id,
    submatrix_mul (star U) (blockDiag2 P Q) (fun j : Fin N => ((0 : Fin 2), j))
      (id : Fin 2 × Fin N → Fin 2 × Fin N) (id : Fin 2 × Fin N → Fin 2 × Fin N)
      Function.bijective_id,
    hCs, hC, Matrix.submatrix_id_id,
    Matrix.mul_assoc (stacked A B)ᴴ (blockDiag2 P Q) (stacked A B), blockDiag2_mul_stacked,
    stacked_star_mul_stacked]
  simp only [mul_assoc]

/-! ## Functional calculus of a Hermitian matrix and of `blockDiag2` -/

/-- Functional calculus of a Hermitian matrix via its spectral decomposition. -/
lemma cfc_hermitian_eq {X : Matrix (Fin N) (Fin N) ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * diagonal (fun i => (f (hX.eigenvalues i) : ℂ))
      * star (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
  have hs1 : star (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hs2 : (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self hX.eigenvectorUnitary
  have hLsa : IsSelfAdjoint (diagonal (fun i => (hX.eigenvalues i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact Complex.conj_ofReal _
  have hspec : X = (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * diagonal (fun i => (hX.eigenvalues i : ℂ))
      * star (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    have h := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hX.eigenvalues) = fun i => (hX.eigenvalues i : ℂ) := by
      funext i; rfl
    rw [hRC] at h; exact h
  calc cfc f X = cfc f ((hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * diagonal (fun i => (hX.eigenvalues i : ℂ))
        * star (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) := by rw [← hspec]
    _ = (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          * cfc f (diagonal (fun i => (hX.eigenvalues i : ℂ)))
          * star (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) :=
        Oseledets.OperatorEntropy.cfc_conj _ _ hs1 hs2 hLsa f
    _ = _ := by rw [cfc_diagonal]

/-- Functional calculus of a block-diagonal-of-diagonals matrix. -/
lemma cfc_blockDiag2_diag (f : ℝ → ℝ) (a b : Fin N → ℝ) :
    cfc f (blockDiag2 (diagonal (fun i => (a i : ℂ))) (diagonal (fun i => (b i : ℂ))))
      = blockDiag2 (diagonal (fun i => (f (a i) : ℂ)))
          (diagonal (fun i => (f (b i) : ℂ))) := by
  have key : blockDiag2 (diagonal (fun i => (a i : ℂ))) (diagonal (fun i => (b i : ℂ)))
      = diagonal (fun p : Fin 2 × Fin N =>
          ((if p.1 = 0 then a p.2 else b p.2 : ℝ) : ℂ)) := by
    rw [blockDiag2_diagonal]; congr 1; funext p; split <;> simp
  rw [key, cfc_diagonal, blockDiag2_diagonal]
  congr 1; funext p
  rw [apply_ite f]; split <;> simp

set_option maxHeartbeats 400000 in -- large block-matrix / cfc elaboration
/-- **`f` of a block-diagonal is block-diagonal.** For self-adjoint `X, Y`,
`cfc f (diag(X, Y)) = diag(cfc f X, cfc f Y)`. -/
lemma cfc_blockDiag2 {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : IsSelfAdjoint X)
    (hY : IsSelfAdjoint Y) (f : ℝ → ℝ) :
    cfc f (blockDiag2 X Y) = blockDiag2 (cfc f X) (cfc f Y) := by
  have hXh : X.IsHermitian := hX
  have hYh : Y.IsHermitian := hY
  have hsX1 : star (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hsX2 : (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hsY1 : star (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hsY2 : (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hdXsa : IsSelfAdjoint (diagonal (fun i => (hXh.eigenvalues i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact Complex.conj_ofReal _
  have hdYsa : IsSelfAdjoint (diagonal (fun i => (hYh.eigenvalues i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact Complex.conj_ofReal _
  have hspecX : X = (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * diagonal (fun i => (hXh.eigenvalues i : ℂ))
      * star (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    have h := hXh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hXh.eigenvalues) = fun i => (hXh.eigenvalues i : ℂ) := by
      funext i; rfl
    rw [hRC] at h; exact h
  have hspecY : Y = (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * diagonal (fun i => (hYh.eigenvalues i : ℂ))
      * star (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    have h := hYh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hYh.eigenvalues) = fun i => (hYh.eigenvalues i : ℂ) := by
      funext i; rfl
    rw [hRC] at h; exact h
  have hWs1 : star (blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
      * blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [blockDiag2_star, blockDiag2_mul, hsX1, hsY1, blockDiag2_one]
  have hWs2 : blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) = 1 := by
    rw [blockDiag2_star, blockDiag2_mul, hsX2, hsY2, blockDiag2_one]
  have hΛsa : IsSelfAdjoint (blockDiag2 (diagonal (fun i => (hXh.eigenvalues i : ℂ)))
      (diagonal (fun i => (hYh.eigenvalues i : ℂ)))) :=
    blockDiag2_isSelfAdjoint hdXsa hdYsa
  have hdecomp : blockDiag2 X Y
      = blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * blockDiag2 (diagonal (fun i => (hXh.eigenvalues i : ℂ)))
          (diagonal (fun i => (hYh.eigenvalues i : ℂ)))
        * star (blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) := by
    rw [blockDiag2_star, blockDiag2_mul, blockDiag2_mul, ← hspecX, ← hspecY]
  rw [hdecomp, Oseledets.OperatorEntropy.cfc_conj _ _ hWs1 hWs2 hΛsa f, cfc_blockDiag2_diag,
    blockDiag2_star, blockDiag2_mul, blockDiag2_mul, ← cfc_hermitian_eq hXh,
    ← cfc_hermitian_eq hYh]

/-! ## Spectrum of a block-diagonal -/

/-- Spectrum invariance under unitary conjugation (right form). -/
lemma spectrum_conj_right {W a : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ}
    (hW1 : star W * W = 1) (hW2 : W * star W = 1) :
    spectrum ℝ (W * a * star W) = spectrum ℝ a := by
  have hmem : W ∈ unitary (Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) :=
    Unitary.mem_iff.mpr ⟨hW1, hW2⟩
  exact Unitary.spectrum_star_right_conjugate (R := ℝ) (a := a) (U := ⟨W, hmem⟩)

/-- Spectrum invariance under unitary conjugation (left form). -/
lemma spectrum_conj_left {W a : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ}
    (hW1 : star W * W = 1) (hW2 : W * star W = 1) :
    spectrum ℝ (star W * a * W) = spectrum ℝ a := by
  have hmem : W ∈ unitary (Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) :=
    Unitary.mem_iff.mpr ⟨hW1, hW2⟩
  exact Unitary.spectrum_star_left_conjugate (R := ℝ) (a := a) (U := ⟨W, hmem⟩)

set_option maxHeartbeats 400000 in -- large block-matrix / cfc elaboration
/-- The spectrum of `diag(X, Y)` is contained in `I` when both blocks' spectra are. -/
lemma blockDiag2_spectrum_subset {X Y : Matrix (Fin N) (Fin N) ℂ} {I : Set ℝ}
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (hXsp : spectrum ℝ X ⊆ I) (hYsp : spectrum ℝ Y ⊆ I) :
    spectrum ℝ (blockDiag2 X Y) ⊆ I := by
  have hXh : X.IsHermitian := hX
  have hYh : Y.IsHermitian := hY
  have hsX1 : star (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hsX2 : (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hsY1 : star (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hsY2 : (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hspecX : X = (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * diagonal (fun i => (hXh.eigenvalues i : ℂ))
      * star (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    have h := hXh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hXh.eigenvalues) = fun i => (hXh.eigenvalues i : ℂ) := by
      funext i; rfl
    rw [hRC] at h; exact h
  have hspecY : Y = (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * diagonal (fun i => (hYh.eigenvalues i : ℂ))
      * star (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    have h := hYh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hYh.eigenvalues) = fun i => (hYh.eigenvalues i : ℂ) := by
      funext i; rfl
    rw [hRC] at h; exact h
  have hWs1 : star (blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
      * blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [blockDiag2_star, blockDiag2_mul, hsX1, hsY1, blockDiag2_one]
  have hWs2 : blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) = 1 := by
    rw [blockDiag2_star, blockDiag2_mul, hsX2, hsY2, blockDiag2_one]
  have hbd : blockDiag2 (diagonal (fun i => (hXh.eigenvalues i : ℂ)))
        (diagonal (fun i => (hYh.eigenvalues i : ℂ)))
      = diagonal (fun p : Fin 2 × Fin N =>
          ((if p.1 = 0 then hXh.eigenvalues p.2 else hYh.eigenvalues p.2 : ℝ) : ℂ)) := by
    rw [blockDiag2_diagonal]; congr 1; funext p; split <;> simp
  have hdiageq : blockDiag2 X Y
      = blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * diagonal (fun p : Fin 2 × Fin N =>
          ((if p.1 = 0 then hXh.eigenvalues p.2 else hYh.eigenvalues p.2 : ℝ) : ℂ))
        * star (blockDiag2 (hXh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          (hYh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) := by
    rw [← hbd, blockDiag2_star, blockDiag2_mul, blockDiag2_mul, ← hspecX, ← hspecY]
  rw [hdiageq, spectrum_conj_right hWs1 hWs2]
  refine spectrum_diagonal_real_subset _ (fun p => ?_)
  split
  · exact hXsp (hXh.eigenvalues_mem_spectrum_real _)
  · exact hYsp (hYh.eigenvalues_mem_spectrum_real _)

/-! ## Transporting operator convexity to `Fin 2 × Fin N` -/

/-- The relabelling equivalence `Fin 2 × Fin N ≃ Fin (2 * N)`. -/
private def e2N : (Fin 2 × Fin N) ≃ Fin (2 * N) := finProdFinEquiv

/-- Reindexing along `e2N` as a star-algebra equivalence. -/
private def reIdx : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ ≃⋆ₐ[ℂ]
    Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ :=
  StarAlgEquiv.ofAlgEquiv (reindexAlgEquiv ℂ ℂ e2N) fun M => by
    simp only [reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose]
    exact (conjTranspose_reindex e2N e2N M).symm

private lemma reIdx_continuous :
    Continuous (reIdx : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ →
      Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ) := by
  apply continuous_matrix
  intro i j
  change Continuous fun M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ =>
    M (e2N.symm i) (e2N.symm j)
  exact (continuous_apply _).comp (continuous_apply _)

private lemma reIdx_smul (r : ℝ) (P : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) :
    reIdx (r • P) = r • reIdx P := by
  ext i j; rfl

private lemma real_smul_matrix (r : ℝ) (P : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) :
    r • P = (r : ℂ) • P := by
  ext i j; simp [Matrix.smul_apply, Complex.real_smul]

private lemma reIdx_le_reflect {A B : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ}
    (h : reIdx A ≤ reIdx B) : A ≤ B := by
  rw [Matrix.le_iff] at h ⊢
  have hsub : (reIdx B - reIdx A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ)
      = (B - A).submatrix e2N.symm e2N.symm := by
    rw [← map_sub]; rfl
  rw [hsub] at h
  have h2 := h.submatrix e2N
  rwa [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2

set_option maxHeartbeats 400000 in -- large block-matrix / cfc elaboration
/-- Operator convexity transported to the product index `Fin 2 × Fin N` (midpoint form). -/
lemma operatorConvex_prod {I : Set ℝ} {f : ℝ → ℝ} (hf : OperatorConvexOn I f)
    (P Q : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ)
    (hP : IsSelfAdjoint P ∧ spectrum ℝ P ⊆ I) (hQ : IsSelfAdjoint Q ∧ spectrum ℝ Q ⊆ I) :
    cfc f ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)
      ≤ (1 / 2 : ℝ) • cfc f P + (1 / 2 : ℝ) • cfc f Q := by
  have hcontP : ContinuousOn f (spectrum ℝ P) :=
    (Matrix.finite_real_spectrum (A := P)).continuousOn f
  have hcontQ : ContinuousOn f (spectrum ℝ Q) :=
    (Matrix.finite_real_spectrum (A := Q)).continuousOn f
  have hΦPsa : IsSelfAdjoint (reIdx P) := by
    rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hP.1]
  have hΦQsa : IsSelfAdjoint (reIdx Q) := by
    rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hQ.1]
  have hΦPsp : spectrum ℝ (reIdx P) ⊆ I := by
    have hval : (reIdx P : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ)
        = reindexAlgEquiv ℝ ℂ e2N P := by ext i j; rfl
    rw [hval, AlgEquiv.spectrum_eq]; exact hP.2
  have hΦQsp : spectrum ℝ (reIdx Q) ⊆ I := by
    have hval : (reIdx Q : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ)
        = reindexAlgEquiv ℝ ℂ e2N Q := by ext i j; rfl
    rw [hval, AlgEquiv.spectrum_eq]; exact hQ.2
  have hmcP : reIdx (cfc f P) = cfc f (reIdx P) :=
    StarAlgHomClass.map_cfc reIdx f P hcontP reIdx_continuous hP.1 hΦPsa
  have hmcQ : reIdx (cfc f Q) = cfc f (reIdx Q) :=
    StarAlgHomClass.map_cfc reIdx f Q hcontQ reIdx_continuous hQ.1 hΦQsa
  have hconv := (hf (2 * N)).2 (Set.mem_setOf.mpr ⟨hΦPsa, hΦPsp⟩)
    (Set.mem_setOf.mpr ⟨hΦQsa, hΦQsp⟩) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have eL : (1 / 2 : ℝ) • reIdx P + (1 / 2 : ℝ) • reIdx Q
      = reIdx ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q) := by
    rw [map_add, reIdx_smul, reIdx_smul]
  have eR : (1 / 2 : ℝ) • cfc f (reIdx P) + (1 / 2 : ℝ) • cfc f (reIdx Q)
      = reIdx ((1 / 2 : ℝ) • cfc f P + (1 / 2 : ℝ) • cfc f Q) := by
    rw [map_add, reIdx_smul, reIdx_smul, hmcP, hmcQ]
  have hcontPQ : ContinuousOn f (spectrum ℝ ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)) :=
    (Matrix.finite_real_spectrum (A := (1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)).continuousOn f
  have hPQsa : IsSelfAdjoint ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q) := by
    have h12 : star ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by simp
    rw [real_smul_matrix, real_smul_matrix, isSelfAdjoint_iff, star_add, star_smul, star_smul,
      h12, isSelfAdjoint_iff.mp hP.1, isSelfAdjoint_iff.mp hQ.1]
  have hΦPQsa : IsSelfAdjoint (reIdx ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q)) := by
    rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hPQsa]
  have hconv' : cfc f ((1 / 2 : ℝ) • reIdx P + (1 / 2 : ℝ) • reIdx Q)
      ≤ (1 / 2 : ℝ) • cfc f (reIdx P) + (1 / 2 : ℝ) • cfc f (reIdx Q) := hconv
  rw [eL, ← StarAlgHomClass.map_cfc reIdx f _ hcontPQ reIdx_continuous hPQsa hΦPQsa, eR] at hconv'
  exact reIdx_le_reflect hconv'

/-! ## The pinching identity -/

/-- `blockDiag2 1 (-1)` written as a diagonal. -/
lemma blockDiag2_one_neg_one :
    blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1)
      = diagonal (fun p : Fin 2 × Fin N => if p.1 = 0 then (1 : ℂ) else -1) := by
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) = diagonal (fun _ => (1 : ℂ)) := Matrix.diagonal_one.symm
  have hm1 : (-1 : Matrix (Fin N) (Fin N) ℂ) = diagonal (fun _ => (-1 : ℂ)) := by
    ext i j
    rw [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [hm1, h1, blockDiag2_diagonal]

/-- Conjugation by `V = diag(1, -1)` fixes the `(0,0)`-block. -/
lemma Vconj_submatrix₀₀ (W : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) :
    (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * W
        * blockDiag2 1 (-1)).submatrix (fun j : Fin N => ((0 : Fin 2), j))
        (fun j : Fin N => ((0 : Fin 2), j))
      = W.submatrix (fun j : Fin N => ((0 : Fin 2), j)) (fun j : Fin N => ((0 : Fin 2), j)) := by
  rw [blockDiag2_one_neg_one]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The pinch: `½ M + ½ V M V = diag(M₀₀, M₁₁)`. -/
lemma pinch_eq (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) :
    (1 / 2 : ℝ) • M + (1 / 2 : ℝ)
        • (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M * blockDiag2 1 (-1))
      = blockDiag2 (M.submatrix (fun j : Fin N => ((0 : Fin 2), j))
          (fun j : Fin N => ((0 : Fin 2), j)))
          (M.submatrix (fun j : Fin N => ((1 : Fin 2), j))
          (fun j : Fin N => ((1 : Fin 2), j))) := by
  have hsum : blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M * blockDiag2 1 (-1) + M
      = blockDiag2 (M.submatrix (fun j : Fin N => ((0 : Fin 2), j))
            (fun j : Fin N => ((0 : Fin 2), j)))
          (M.submatrix (fun j : Fin N => ((1 : Fin 2), j))
            (fun j : Fin N => ((1 : Fin 2), j)))
        + blockDiag2 (M.submatrix (fun j : Fin N => ((0 : Fin 2), j))
            (fun j : Fin N => ((0 : Fin 2), j)))
          (M.submatrix (fun j : Fin N => ((1 : Fin 2), j))
            (fun j : Fin N => ((1 : Fin 2), j))) := by
    rw [blockDiag2_one_neg_one]
    ext ⟨a, i⟩ ⟨c, k⟩
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.submatrix_apply, blockDiag2_apply]
    fin_cases a <;> fin_cases c <;> simp
  have hcalc : (1 / 2 : ℝ) • M + (1 / 2 : ℝ)
        • (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M * blockDiag2 1 (-1))
      = (1 / 2 : ℝ)
        • (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M * blockDiag2 1 (-1) + M) := by
    rw [smul_add, add_comm]
  rw [hcalc, hsum, ← two_smul ℝ, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

/-- Monotonicity of the `(0,0)`-block under the Loewner order. -/
lemma submatrix_incl₀_mono {P Q : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ} (h : P ≤ Q) :
    P.submatrix (fun j : Fin N => ((0 : Fin 2), j)) (fun j : Fin N => ((0 : Fin 2), j))
      ≤ Q.submatrix (fun j : Fin N => ((0 : Fin 2), j)) (fun j : Fin N => ((0 : Fin 2), j)) := by
  rw [Matrix.le_iff] at h ⊢
  have hs : Q.submatrix (fun j : Fin N => ((0 : Fin 2), j)) (fun j : Fin N => ((0 : Fin 2), j))
      - P.submatrix (fun j : Fin N => ((0 : Fin 2), j)) (fun j : Fin N => ((0 : Fin 2), j))
      = (Q - P).submatrix (fun j : Fin N => ((0 : Fin 2), j))
          (fun j : Fin N => ((0 : Fin 2), j)) := by
    ext i j; simp [Matrix.sub_apply, Matrix.submatrix_apply]
  rw [hs]; exact h.submatrix _

/-! ## The Hansen–Pedersen–Jensen inequality -/

set_option maxHeartbeats 800000 in -- large dilation assembly
/-- **Hansen–Pedersen–Jensen operator-Jensen inequality (affine form).** For operator-convex `f`,
a contraction pair `A, B` (`A⋆A + B⋆B = 1`), and self-adjoint `X, Y` with spectra in `I`,
`f(A⋆XA + B⋆YB) ≤ A⋆ f(X) A + B⋆ f(Y) B`. -/
theorem hpj_affine (f : ℝ → ℝ) (I : Set ℝ) (hf : OperatorConvexOn I f)
    (A B X Y : Matrix (Fin N) (Fin N) ℂ) (hAB : star A * A + star B * B = 1)
    (hX : IsSelfAdjoint X ∧ spectrum ℝ X ⊆ I) (hY : IsSelfAdjoint Y ∧ spectrum ℝ Y ⊆ I) :
    cfc f (star A * X * A + star B * Y * B)
      ≤ star A * cfc f X * A + star B * cfc f Y * B := by
  obtain ⟨U, hU⟩ := exists_unitary_firstBlockCol A B hAB
  set Uc : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
    (U : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) with hUcdef
  have hU1 : star Uc * Uc = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hU2 : Uc * star Uc = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hDsa : IsSelfAdjoint (blockDiag2 X Y) := blockDiag2_isSelfAdjoint hX.1 hY.1
  have hDsp : spectrum ℝ (blockDiag2 X Y) ⊆ I :=
    blockDiag2_spectrum_subset hX.1 hY.1 hX.2 hY.2
  set M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ := star Uc * blockDiag2 X Y * Uc with hMdef
  have hMsa : IsSelfAdjoint M := by
    rw [hMdef, isSelfAdjoint_iff, star_mul, star_mul, star_star,
      isSelfAdjoint_iff.mp hDsa, ← mul_assoc]
  have hMsp : spectrum ℝ M ⊆ I := by rw [hMdef, spectrum_conj_left hU1 hU2]; exact hDsp
  have hone : IsSelfAdjoint (1 : Matrix (Fin N) (Fin N) ℂ) := by
    rw [isSelfAdjoint_iff, star_one]
  have hVsa : IsSelfAdjoint (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1)) :=
    blockDiag2_isSelfAdjoint hone hone.neg
  have hstarV : star (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1))
      = blockDiag2 1 (-1) := isSelfAdjoint_iff.mp hVsa
  have hVV : blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * blockDiag2 1 (-1) = 1 := by
    rw [blockDiag2_mul, one_mul, neg_one_mul, neg_neg, blockDiag2_one]
  have hVMVsa : IsSelfAdjoint (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M
      * blockDiag2 1 (-1)) := by
    rw [isSelfAdjoint_iff, star_mul, star_mul, hstarV, isSelfAdjoint_iff.mp hMsa, ← mul_assoc]
  have hVMVsp : spectrum ℝ (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M
      * blockDiag2 1 (-1)) ⊆ I := by
    have h := spectrum_conj_left (W := blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1)) (a := M)
      (by rw [hstarV]; exact hVV) (by rw [hstarV]; exact hVV)
    rw [hstarV] at h; rw [h]; exact hMsp
  -- convexity inequality
  have hconv := operatorConvex_prod hf M
    (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M * blockDiag2 1 (-1))
    ⟨hMsa, hMsp⟩ ⟨hVMVsa, hVMVsp⟩
  -- self-adjointness of the corner blocks of `M`
  have hMh : M.IsHermitian := hMsa
  have hM00sa : IsSelfAdjoint (M.submatrix (fun j : Fin N => ((0 : Fin 2), j))
      (fun j : Fin N => ((0 : Fin 2), j))) :=
    hMh.submatrix (fun j : Fin N => ((0 : Fin 2), j))
  have hM11sa : IsSelfAdjoint (M.submatrix (fun j : Fin N => ((1 : Fin 2), j))
      (fun j : Fin N => ((1 : Fin 2), j))) :=
    hMh.submatrix (fun j : Fin N => ((1 : Fin 2), j))
  have hM00 : M.submatrix (fun j : Fin N => ((0 : Fin 2), j))
      (fun j : Fin N => ((0 : Fin 2), j)) = star A * X * A + star B * Y * B := by
    rw [hMdef]; exact blockCorner Uc A B hU X Y
  -- LHS block
  have hLHS : (cfc f ((1 / 2 : ℝ) • M + (1 / 2 : ℝ)
        • (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M
          * blockDiag2 1 (-1)))).submatrix (fun j : Fin N => ((0 : Fin 2), j))
        (fun j : Fin N => ((0 : Fin 2), j))
      = cfc f (star A * X * A + star B * Y * B) := by
    rw [pinch_eq, cfc_blockDiag2 hM00sa hM11sa f, blockDiag2_submatrix₀₀, hM00]
  -- `cfc f M`
  have hcfcM : cfc f M = star Uc * blockDiag2 (cfc f X) (cfc f Y) * Uc := by
    rw [hMdef]
    have h := Oseledets.OperatorEntropy.cfc_conj (star Uc) (blockDiag2 X Y)
      (by rw [star_star]; exact hU2) (by rw [star_star]; exact hU1) hDsa f
    rw [star_star] at h
    rw [h, cfc_blockDiag2 hX.1 hY.1]
  have hcfcM00 : (cfc f M).submatrix (fun j : Fin N => ((0 : Fin 2), j))
      (fun j : Fin N => ((0 : Fin 2), j)) = star A * cfc f X * A + star B * cfc f Y * B := by
    rw [hcfcM]; exact blockCorner Uc A B hU (cfc f X) (cfc f Y)
  -- `cfc f (V M V) = V (cfc f M) V`
  have hcfcVMV : cfc f (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M * blockDiag2 1 (-1))
      = blockDiag2 1 (-1) * cfc f M * blockDiag2 1 (-1) := by
    have h := Oseledets.OperatorEntropy.cfc_conj (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1))
      M (by rw [hstarV]; exact hVV) (by rw [hstarV]; exact hVV) hMsa f
    rw [hstarV] at h; exact h
  -- RHS block
  have hRHS : ((1 / 2 : ℝ) • cfc f M + (1 / 2 : ℝ)
        • cfc f (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * M
          * blockDiag2 1 (-1))).submatrix (fun j : Fin N => ((0 : Fin 2), j))
        (fun j : Fin N => ((0 : Fin 2), j))
      = star A * cfc f X * A + star B * cfc f Y * B := by
    rw [hcfcVMV]
    have hV0 : (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * cfc f M
          * blockDiag2 1 (-1)).submatrix (fun j : Fin N => ((0 : Fin 2), j))
          (fun j : Fin N => ((0 : Fin 2), j))
        = (cfc f M).submatrix (fun j : Fin N => ((0 : Fin 2), j))
          (fun j : Fin N => ((0 : Fin 2), j)) := Vconj_submatrix₀₀ (cfc f M)
    have key : ((1 / 2 : ℝ) • cfc f M + (1 / 2 : ℝ)
          • (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * cfc f M
            * blockDiag2 1 (-1))).submatrix (fun j : Fin N => ((0 : Fin 2), j))
          (fun j : Fin N => ((0 : Fin 2), j))
        = (1 / 2 : ℝ) • (cfc f M).submatrix (fun j : Fin N => ((0 : Fin 2), j))
            (fun j : Fin N => ((0 : Fin 2), j))
          + (1 / 2 : ℝ) • (blockDiag2 (1 : Matrix (Fin N) (Fin N) ℂ) (-1) * cfc f M
              * blockDiag2 1 (-1)).submatrix (fun j : Fin N => ((0 : Fin 2), j))
              (fun j : Fin N => ((0 : Fin 2), j)) := rfl
    rw [key, hV0, ← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul, hcfcM00]
  have hmono := submatrix_incl₀_mono hconv
  rw [hLHS, hRHS] at hmono
  exact hmono

/-- **Hansen–Pedersen–Jensen (isometry form).** For an isometry `V` (`V⋆V = 1`), operator-convex
`f` with `f 0 ≤ 0` and `0 ∈ I`, `f(V⋆XV) ≤ V⋆ f(X) V`. -/
theorem hpj_isometry (f : ℝ → ℝ) (I : Set ℝ) (hf : OperatorConvexOn I f)
    (V X : Matrix (Fin N) (Fin N) ℂ) (hV : star V * V = 1)
    (hX : IsSelfAdjoint X ∧ spectrum ℝ X ⊆ I) (h0 : (0 : ℝ) ∈ I) (_hf0 : f 0 ≤ 0) :
    cfc f (star V * X * V) ≤ star V * cfc f X * V := by
  have hAB : star V * V + star (0 : Matrix (Fin N) (Fin N) ℂ) * 0 = 1 := by
    rw [star_zero, mul_zero, add_zero, hV]
  have hY : IsSelfAdjoint (0 : Matrix (Fin N) (Fin N) ℂ) ∧
      spectrum ℝ (0 : Matrix (Fin N) (Fin N) ℂ) ⊆ I := by
    refine ⟨(by rw [isSelfAdjoint_iff, star_zero] :
      IsSelfAdjoint (0 : Matrix (Fin N) (Fin N) ℂ)), fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · rw [hx0]; exact h0
    · exfalso
      rw [spectrum.mem_iff, sub_zero] at hx
      exact hx ((isUnit_iff_ne_zero.mpr hx0).map (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ)))
  have hkey := hpj_affine f I hf V 0 X 0 hAB hX hY
  simp only [star_zero, mul_zero, zero_mul, add_zero] at hkey
  exact hkey

end Oseledets.OperatorEntropy.Lieb

end
