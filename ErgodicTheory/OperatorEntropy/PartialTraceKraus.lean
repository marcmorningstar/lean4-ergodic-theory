import ErgodicTheory.OperatorEntropy.PartialTrace

open Matrix

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-! # Explicit block-inclusion Kraus form of the partial traces

This module gives the literal explicit-Kraus (Stinespring) presentation of the partial traces
defined in `ErgodicTheory.OperatorEntropy.PartialTrace`. Where that module writes the completely
positive decomposition through `Matrix.submatrix` reindexings, here we name the Kraus operators as
honest `def`s with concrete matrix types and express each partial trace as a genuine sum of
matrix conjugations `Eⱼ M Eⱼᴴ`.

Naming the block-inclusion operators as `def`s with concrete `Matrix` types — rather than as bare
lambdas — is the load-bearing point: it resolves the `CStarMatrix` / `Matrix` `HMul` elaboration
ambiguity of issue #25 (a bare lambda does not elaborate against `*`).

Two distinct identities relate the block-inclusion operators to `1`:

* **completeness / trace-preservation:** `∑ⱼ Eⱼᴴ Eⱼ = 1` on the full `A ⊗ B` space;
* **co-isometry:** `Eⱼ Eⱼᴴ = 1` on the `A` factor for *each* `j` individually.

These are not the same statement: summing the co-isometry identity over `j` gives
`∑ⱼ Eⱼ Eⱼᴴ = |nB| • 1`, not `1`. -/

/-! ## Right factor (`Tr_B`) -/

/-- Explicit block-inclusion Kraus matrix `E j : nA → (nA × nB)`, `E j a p = [p = (a,j)]`. -/
def krausInclusionRight (j : nB) : Matrix nA (nA × nB) ℂ :=
  fun a p => if p = (a, j) then 1 else 0

/-- The Kraus conjugation `Eⱼ M Eⱼᴴ` equals the `j`-th block compression (submatrix). -/
theorem krausConjRight_eq_submatrix (M : Matrix (nA × nB) (nA × nB) ℂ) (j : nB) :
    krausInclusionRight j * M * (krausInclusionRight j)ᴴ
      = M.submatrix (fun a => (a, j)) (fun a => (a, j)) := by
  ext i i'
  rw [Matrix.submatrix_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausInclusionRight,
    apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Literal explicit-Kraus form of the right partial trace. -/
theorem partialTraceRight_eq_kraus (M : Matrix (nA × nB) (nA × nB) ℂ) :
    partialTraceRight M = ∑ j : nB, krausInclusionRight j * M * (krausInclusionRight j)ᴴ := by
  simp_rw [krausConjRight_eq_submatrix]
  exact partialTraceRight_eq_sum_submatrix M

/-- Each block-inclusion `Eⱼ` is a co-isometry: `Eⱼ Eⱼᴴ = 1` on the `A` factor. -/
theorem krausInclusionRight_mul_conjTranspose (j : nB) :
    krausInclusionRight j * (krausInclusionRight j)ᴴ = (1 : Matrix nA nA ℂ) := by
  ext i i'
  rw [Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausInclusionRight,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Prod.mk.injEq, and_true]
  exact if_congr eq_comm rfl rfl

/-- Completeness / trace-preservation relation: `∑ⱼ Eⱼᴴ Eⱼ = 1` on the full `A ⊗ B` space. -/
theorem sum_conjTranspose_mul_krausInclusionRight :
    ∑ j : nB, (krausInclusionRight j)ᴴ * krausInclusionRight j
      = (1 : Matrix (nA × nB) (nA × nB) ℂ) := by
  ext p p'
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausInclusionRight,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    Prod.ext_iff, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ## Left factor (`Tr_A`) -/

/-- Explicit block-inclusion Kraus matrix `E i : nB → (nA × nB)`, `E i b p = [p = (i,b)]`. -/
def krausInclusionLeft (i : nA) : Matrix nB (nA × nB) ℂ :=
  fun b p => if p = (i, b) then 1 else 0

/-- The Kraus conjugation `Eᵢ M Eᵢᴴ` equals the `i`-th block compression (submatrix). -/
theorem krausConjLeft_eq_submatrix (M : Matrix (nA × nB) (nA × nB) ℂ) (i : nA) :
    krausInclusionLeft i * M * (krausInclusionLeft i)ᴴ
      = M.submatrix (fun b => (i, b)) (fun b => (i, b)) := by
  ext j j'
  rw [Matrix.submatrix_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausInclusionLeft,
    apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Literal explicit-Kraus form of the left partial trace. -/
theorem partialTraceLeft_eq_kraus (M : Matrix (nA × nB) (nA × nB) ℂ) :
    partialTraceLeft M = ∑ i : nA, krausInclusionLeft i * M * (krausInclusionLeft i)ᴴ := by
  simp_rw [krausConjLeft_eq_submatrix]
  exact partialTraceLeft_eq_sum_submatrix M

/-- Each block-inclusion `Eᵢ` is a co-isometry: `Eᵢ Eᵢᴴ = 1` on the `B` factor. -/
theorem krausInclusionLeft_mul_conjTranspose (i : nA) :
    krausInclusionLeft i * (krausInclusionLeft i)ᴴ = (1 : Matrix nB nB ℂ) := by
  ext j j'
  rw [Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausInclusionLeft,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Prod.mk.injEq, true_and]
  exact if_congr eq_comm rfl rfl

/-- Completeness / trace-preservation relation: `∑ᵢ Eᵢᴴ Eᵢ = 1` on the full `A ⊗ B` space. -/
theorem sum_conjTranspose_mul_krausInclusionLeft :
    ∑ i : nA, (krausInclusionLeft i)ᴴ * krausInclusionLeft i
      = (1 : Matrix (nA × nB) (nA × nB) ℂ) := by
  ext p p'
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausInclusionLeft,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    Prod.ext_iff, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end ErgodicTheory.OperatorEntropy
