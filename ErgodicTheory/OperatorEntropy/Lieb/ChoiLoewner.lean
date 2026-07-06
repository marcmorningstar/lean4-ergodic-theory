/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.RectOperatorJensen
import ErgodicTheory.OperatorEntropy.Lieb.OperatorConvex

/-!
# The rectangular `-log` operator-Jensen inequality (Petz sufficiency crux, issue #28)

This module assembles the **corner-pinching Loewner inequality**
`ErgodicTheory.OperatorEntropy.Lieb.sum_corner_loewner` (`RectOperatorJensen.lean`) into the
headline rectangular Loewner inequality `rect_isometry_neg_log_loewner` that unblocks the
sufficiency direction of the Petz recovery equality (it is the piece consumed by
`PetzEqualitySufficiency.lean`).

## Main results

* `ErgodicTheory.OperatorEntropy.Lieb.rect_isometry_neg_log_loewner`: for a **rectangular** isometry
  `W : Matrix p q ℂ` (`Wᴴ W = 1`) and a positive-definite self-adjoint `X : Matrix p p ℂ`,
  `cfc (-log) (Wᴴ X W) ≤ Wᴴ (cfc (-log) X) W`.

## Route

The rectangular theorem extends the orthonormal columns of `W` to an orthonormal basis of
`EuclideanSpace ℂ p` (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), reading off a
unitary `U : Matrix p p ℂ` whose `q`-columns reproduce `W`.  Then `Wᴴ X W` is the `q`-corner of
the unitary conjugate `Uᴴ X U` (reindexing `p ≃ q ⊕ r`), and the corner-pinching inequality
`sum_corner_loewner` applies.
-/

open Matrix
open scoped MatrixOrder ComplexOrder InnerProductSpace

noncomputable section

universe u v

namespace ErgodicTheory.OperatorEntropy.Lieb

/-! ## A corner of a unitary conjugation -/

/-- The `g`-corner of the unitary conjugation `Uᴴ Y U` equals `Wᴴ Y W`, when the `g`-columns of
`U` reproduce `W` (`U i (g a) = W i a`). -/
lemma corner_conj_eq {p q : Type*} [Fintype p] (U Y : Matrix p p ℂ) (W : Matrix p q ℂ)
    (g : q → p) (hUW : ∀ (i : p) (a : q), U i (g a) = W i a) :
    (star U * Y * U).submatrix g g = Wᴴ * Y * W := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hUW k b]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hUW l a]

/-! ## Completing a rectangular isometry to a unitary -/

/-- **Unitary column-extension of a rectangular isometry.** If `Wᴴ W = 1` (the columns of
`W : Matrix p q ℂ` are orthonormal), then `W` extends to a unitary `U : Matrix p p ℂ` (reindexing
`p ≃ q ⊕ r` with `r` the orthogonal complement) whose `Sum.inl`-columns reproduce `W`. -/
lemma exists_unitary_col_ext {p : Type u} {q : Type v} [Fintype p] [DecidableEq p] [Finite q]
    [DecidableEq q] (W : Matrix p q ℂ) (hW : Wᴴ * W = 1) :
    ∃ (r : Type u) (_ : Fintype r) (_ : DecidableEq r) (e : q ⊕ r ≃ p) (U : Matrix p p ℂ),
      star U * U = 1 ∧ U * star U = 1 ∧ ∀ (i : p) (a : q), U i (e (Sum.inl a)) = W i a := by
  classical
  haveI : Fintype q := Fintype.ofFinite q
  -- the columns of `W` as an orthonormal family in `ℂ^p`
  set Wcol : q → EuclideanSpace ℂ p := fun a => (WithLp.toLp 2 fun i => W i a) with hWcoldef
  have hWcolapply : ∀ (a : q) (i : p), Wcol a i = W i a := fun _ _ => rfl
  have hWcol : Orthonormal ℂ Wcol := by
    rw [orthonormal_iff_ite]
    intro a b
    have expand : (⟪Wcol a, Wcol b⟫_ℂ : ℂ) = (Wᴴ * W) a b := by
      rw [PiLp.inner_apply]
      simp only [hWcolapply, RCLike.inner_apply', starRingEnd_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply]
    rw [expand, hW, Matrix.one_apply]
  -- cardinality and an embedding `q ↪ p`
  have hcard : Fintype.card q ≤ Fintype.card p := by
    have hli := hWcol.linearIndependent.fintype_card_le_finrank
    rwa [finrank_euclideanSpace] at hli
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  set e0 : q ≃ ↥(Set.range ⇑g) := Equiv.ofInjective ⇑g g.injective with he0
  -- an extension `v` of `Wcol` to all of `p`, supported on `Set.range g`
  set v : p → EuclideanSpace ℂ p :=
    fun i => if h : i ∈ Set.range ⇑g then Wcol (e0.symm ⟨i, h⟩) else 0 with hvdef
  have hvpos : ∀ x : ↥(Set.range ⇑g), v x.1 = Wcol (e0.symm x) := by
    intro x
    rw [hvdef]
    simp only [dif_pos x.2]
  have hrestr : Orthonormal ℂ (Set.restrict (Set.range ⇑g) v) := by
    have hcomp : Set.restrict (Set.range ⇑g) v = fun x => Wcol (e0.symm x) := by
      funext x; rw [Set.restrict_apply, hvpos x]
    rw [hcomp]
    exact hWcol.comp e0.symm e0.symm.injective
  -- extend to an orthonormal basis of `ℂ^p`
  have hcardι : Module.finrank ℂ (EuclideanSpace ℂ p) = Fintype.card p := finrank_euclideanSpace
  obtain ⟨bas, hbas⟩ := hrestr.exists_orthonormalBasis_extension_of_card_eq hcardι
  have hbasg : ∀ a : q, bas (⇑g a) = Wcol a := by
    intro a
    have hmem : ⇑g a ∈ Set.range ⇑g := Set.mem_range_self a
    rw [hbas (⇑g a) hmem, hvpos ⟨⇑g a, hmem⟩]
    congr 1
    have : (⟨⇑g a, hmem⟩ : ↥(Set.range ⇑g)) = e0 a := by
      rw [he0]; rfl
    rw [this, e0.symm_apply_apply]
  -- the coordinate matrix of `bas` is a unitary reproducing `W`
  set U : Matrix p p ℂ := Matrix.of fun i k => bas k i with hUdef
  have hU1 : star U * U = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hUdef, Matrix.of_apply]
    have hsum : (∑ i, star (bas k i) * bas l i) = (⟪bas k, bas l⟫_ℂ : ℂ) := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply', starRingEnd_apply]
    rw [hsum, orthonormal_iff_ite.mp bas.orthonormal]
  have hU2 : U * star U = 1 := mul_eq_one_comm.mp hU1
  have hUW : ∀ (i : p) (a : q), U i (⇑g a) = W i a := by
    intro i a
    rw [hUdef]
    simp only [Matrix.of_apply]
    rw [hbasg a, hWcolapply]
  -- assemble the equiv `q ⊕ (range g)ᶜ ≃ p`
  refine ⟨↥(Set.range ⇑g)ᶜ, inferInstance, inferInstance,
    (Equiv.sumCongr e0 (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range ⇑g)), U, hU1, hU2, ?_⟩
  intro i a
  have he : ((Equiv.sumCongr e0 (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range ⇑g)))
      (Sum.inl a) = ⇑g a := by
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.Set.sumCompl_apply_inl, he0]
    rfl
  rw [he]
  exact hUW i a

/-! ## The rectangular `-log` operator-Jensen (Loewner) inequality -/

set_option maxHeartbeats 400000 in -- large cfc/reindex/corner-conjugation assembly
/-- **Rectangular operator-Jensen inequality for `-log`.** For a rectangular isometry
`W : Matrix p q ℂ` (`Wᴴ W = 1`) and a self-adjoint `X` with spectrum in `(0, ∞)`,
`cfc (-log) (Wᴴ X W) ≤ Wᴴ (cfc (-log) X) W`. -/
theorem rect_isometry_neg_log_loewner {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] (W : Matrix p q ℂ) (X : Matrix p p ℂ) (hW : Wᴴ * W = 1)
    (hXsa : IsSelfAdjoint X) (hspec : spectrum ℝ X ⊆ Set.Ioi 0) :
    cfc (fun x => -Real.log x) (Wᴴ * X * W) ≤ Wᴴ * cfc (fun x => -Real.log x) X * W := by
  obtain ⟨r, hFr, hDr, e, U, hU1, hU2, hUW⟩ := exists_unitary_col_ext W hW
  haveI : Fintype r := hFr
  haveI : DecidableEq r := hDr
  -- `A := Uᴴ X U`
  set A : Matrix p p ℂ := star U * X * U with hAdef
  have hAsa : IsSelfAdjoint A := by
    rw [hAdef, isSelfAdjoint_iff, star_mul, star_mul, star_star, isSelfAdjoint_iff.mp hXsa,
      ← mul_assoc]
  have hAsp : spectrum ℝ A ⊆ Set.Ioi 0 := by
    rw [hAdef]
    have h := spectrum_conj_gen (W := star U) (a := X) (by rw [star_star]; exact hU2)
      (by rw [star_star]; exact hU1)
    rw [star_star] at h
    rw [h]; exact hspec
  -- reindex `A` to `q ⊕ r`; its `inl`-corner is `Wᴴ X W`
  have hMsa : IsSelfAdjoint (A.submatrix e e) := by
    have hrw : A.submatrix e e = reIx e.symm A := by rw [reIx_apply, Equiv.symm_symm]
    rw [hrw, isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hAsa]
  have hMsp : spectrum ℝ (A.submatrix e e) ⊆ Set.Ioi 0 := by
    have hrw : A.submatrix e e = A.submatrix e.symm.symm e.symm.symm := by rw [Equiv.symm_symm]
    rw [hrw, spectrum_reIx]; exact hAsp
  have key := sum_corner_loewner operatorConvexOn_neg_log (A.submatrix e e) hMsa hMsp
  -- identify both corners
  have hLHS : (A.submatrix e e).submatrix Sum.inl Sum.inl = Wᴴ * X * W := by
    rw [Matrix.submatrix_submatrix, hAdef]
    exact corner_conj_eq U X W (⇑e ∘ Sum.inl) hUW
  have hcfcA : cfc (fun x => -Real.log x) A = star U * cfc (fun x => -Real.log x) X * U := by
    rw [hAdef]
    have h := ErgodicTheory.OperatorEntropy.cfc_conj (star U) X (by rw [star_star]; exact hU2)
      (by rw [star_star]; exact hU1) hXsa (fun x => -Real.log x)
    rw [star_star] at h
    exact h
  have hcfceq : cfc (fun x => -Real.log x) (A.submatrix e e)
      = (cfc (fun x => -Real.log x) A).submatrix e e := by
    have h := cfc_reIx e.symm A hAsa (fun x => -Real.log x)
    simpa only [Equiv.symm_symm] using h
  have hRHS : (cfc (fun x => -Real.log x) (A.submatrix e e)).submatrix Sum.inl Sum.inl
      = Wᴴ * cfc (fun x => -Real.log x) X * W := by
    rw [hcfceq, hcfcA, Matrix.submatrix_submatrix]
    exact corner_conj_eq U (cfc (fun x => -Real.log x) X) W (⇑e ∘ Sum.inl) hUW
  rw [hLHS, hRHS] at key
  exact key

end ErgodicTheory.OperatorEntropy.Lieb

end
