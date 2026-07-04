/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.RingTheory.PicardGroup

/-!
# S1: Unitary dilation of a column-isometric block pair (Lieb keystone prototype)

Given `A B : Matrix (Fin N) (Fin N) ℂ` with `star A * A + star B * B = 1`, the
"stacked" block matrix `[A; B]` (rows indexed by `Fin 2 × Fin N`, with the
`(0, i)` rows carrying `A` and the `(1, i)` rows carrying `B`) has orthonormal
columns in `ℂ^{2N} = EuclideanSpace ℂ (Fin 2 × Fin N)`.  Indeed the `(k, l)`
Gram entry of the columns is `(star A * A + star B * B) k l = δ_{kl}`.

Consequently this orthonormal family extends to an orthonormal basis of `ℂ^{2N}`
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), and reading off the
coordinate matrix of that basis produces a genuine unitary
`U : Matrix.unitaryGroup (Fin 2 × Fin N) ℂ` whose first block-column
`{0} × Fin N` reproduces the stack `[A; B]` **exactly**:
`U i (0, j) = stacked A B i j`.

This is the highest-risk sub-lemma (S1) of the Hansen–Pedersen–Jensen
operator-Jensen theorem / DPI keystone (issue #22): every operator-convexity
dilation argument begins with exactly this "complete the isometric column to a
unitary" step.
-/

open Matrix
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {N : ℕ}

/-- The block "stacked" matrix `[A; B]`: rows indexed by `Fin 2 × Fin N`, with the
`(0, i)` rows carrying `A` and the `(1, i)` rows carrying `B`. -/
def stacked (A B : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin 2 × Fin N) (Fin N) ℂ :=
  Matrix.of fun p j => if p.1 = 0 then A p.2 j else B p.2 j

/-- The `j`-th column of `stacked A B`, viewed as a vector of `ℂ^{2N}`. -/
def stackedCol (A B : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    EuclideanSpace ℂ (Fin 2 × Fin N) :=
  WithLp.toLp 2 fun p => stacked A B p j

@[simp]
theorem stackedCol_apply (A B : Matrix (Fin N) (Fin N) ℂ) (j : Fin N)
    (p : Fin 2 × Fin N) : stackedCol A B j p = stacked A B p j := rfl

/-- The columns of `stacked A B` form an orthonormal family in `ℂ^{2N}` whenever the
block isometry relation `star A * A + star B * B = 1` holds. -/
theorem orthonormal_stackedCol (A B : Matrix (Fin N) (Fin N) ℂ)
    (hAB : star A * A + star B * B = 1) : Orthonormal ℂ (stackedCol A B) := by
  rw [orthonormal_iff_ite]
  intro j l
  have expand : (⟪stackedCol A B j, stackedCol A B l⟫_ℂ : ℂ) =
      (star A * A + star B * B) j l := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [stackedCol_apply, RCLike.inner_apply', starRingEnd_apply, Matrix.add_apply,
      Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    congr 1
  rw [expand, hAB, Matrix.one_apply]

/-- **S1 (unitary dilation of a column isometry).**  If
`star A * A + star B * B = 1`, then the stacked block `[A; B]` extends to a
unitary `U : Matrix.unitaryGroup (Fin 2 × Fin N) ℂ` whose first block-column
`{0} × Fin N` is exactly the stack `[A; B]`, i.e. `U i (0, j) = stacked A B i j`. -/
theorem exists_unitary_firstBlockCol (A B : Matrix (Fin N) (Fin N) ℂ)
    (hAB : star A * A + star B * B = 1) :
    ∃ U : Matrix.unitaryGroup (Fin 2 × Fin N) ℂ,
      ∀ (i : Fin 2 × Fin N) (j : Fin N),
        (U : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) i (0, j) = stacked A B i j := by
  classical
  have hcol : Orthonormal ℂ (stackedCol A B) := orthonormal_stackedCol A B hAB
  -- Extend the orthonormal columns to an orthonormal basis of `ℂ^{2N}`.
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin 2 × Fin N)) =
      Fintype.card (Fin 2 × Fin N) := finrank_euclideanSpace
  have hrestr : Orthonormal ℂ
      (Set.restrict {p : Fin 2 × Fin N | p.1 = 0} (fun p => stackedCol A B p.2)) := by
    have he : Function.Injective
        (fun x : ↥({p : Fin 2 × Fin N | p.1 = 0}) => (x.1.2 : Fin N)) := by
      rintro ⟨⟨a, i⟩, ha⟩ ⟨⟨b, c⟩, hb⟩ h
      simp only [Set.mem_setOf_eq] at ha hb
      subst ha
      subst hb
      obtain rfl : i = c := h
      rfl
    exact hcol.comp _ he
  obtain ⟨bas, hbas⟩ := hrestr.exists_orthonormalBasis_extension_of_card_eq hcard
  -- The coordinate matrix of `bas` is unitary and its first block-column is `[A; B]`.
  refine ⟨⟨Matrix.of fun i k => bas k i, ?_⟩, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply]
    have hsum : (∑ i, star (bas k i) * bas l i) = (⟪bas k, bas l⟫_ℂ : ℂ) := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply', starRingEnd_apply]
    rw [hsum, orthonormal_iff_ite.mp bas.orthonormal]
  · intro i j
    have hmem : ((0 : Fin 2), j) ∈ {p : Fin 2 × Fin N | p.1 = 0} := rfl
    have hbasval : bas ((0 : Fin 2), j) = stackedCol A B j := hbas _ hmem
    change bas ((0 : Fin 2), j) i = stacked A B i j
    rw [hbasval, stackedCol_apply]

end Oseledets.OperatorEntropy.Lieb
