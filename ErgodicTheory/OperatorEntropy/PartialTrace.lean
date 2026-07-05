import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-! # Partial traces on raw matrices

This module defines the partial trace of an operator on a bipartite system `nA ⊗ nB`, working
directly with raw `Matrix (nA × nB) (nA × nB) ℂ` (no density-matrix wrapper). We record that the
partial trace preserves the total trace, is Hermitian on Hermitian inputs, and — the operative
fact for quantum information — sends positive semidefinite operators to positive semidefinite
operators.

The positivity is proved through an explicit completely positive decomposition: `Tr_B M` is the
sum over `j` of the compressions of `M` to the `j`-th block, i.e. the conjugations of `M` by the
block-inclusion isometries `Eⱼᴴ : i ↦ (i, j)`. Each compression is positive semidefinite
(`Matrix.PosSemidef.submatrix`), and a finite sum of positive semidefinite matrices is positive
semidefinite. This is the Kraus / Stinespring picture of the partial trace as a CP map. -/

/-- Partial trace over the right (B) factor: `(Tr_B M) i i' = ∑ⱼ M (i,j) (i',j)`. -/
def partialTraceRight (M : Matrix (nA × nB) (nA × nB) ℂ) : Matrix nA nA ℂ :=
  fun i i' => ∑ j : nB, M (i, j) (i', j)

/-- Partial trace over the left (A) factor: `(Tr_A M) j j' = ∑ᵢ M (i,j) (i,j')`. -/
def partialTraceLeft (M : Matrix (nA × nB) (nA × nB) ℂ) : Matrix nB nB ℂ :=
  fun j j' => ∑ i : nA, M (i, j) (i, j')

omit [Fintype nA] [DecidableEq nA] [DecidableEq nB] in
/-- Entrywise formula for the right partial trace. -/
theorem partialTraceRight_apply (M : Matrix (nA × nB) (nA × nB) ℂ) (i i' : nA) :
    partialTraceRight M i i' = ∑ j : nB, M (i, j) (i', j) := rfl

omit [Fintype nB] [DecidableEq nA] [DecidableEq nB] in
/-- Entrywise formula for the left partial trace. -/
theorem partialTraceLeft_apply (M : Matrix (nA × nB) (nA × nB) ℂ) (j j' : nB) :
    partialTraceLeft M j j' = ∑ i : nA, M (i, j) (i, j') := rfl

omit [DecidableEq nA] [DecidableEq nB] in
/-- The partial trace over `B` preserves the total trace: `Tr (Tr_B M) = Tr M`. -/
theorem trace_partialTraceRight (M : Matrix (nA × nB) (nA × nB) ℂ) :
    (partialTraceRight M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceRight_apply, Fintype.sum_prod_type]

omit [DecidableEq nA] [DecidableEq nB] in
/-- The partial trace over `A` preserves the total trace: `Tr (Tr_A M) = Tr M`. -/
theorem trace_partialTraceLeft (M : Matrix (nA × nB) (nA × nB) ℂ) :
    (partialTraceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceLeft_apply, Fintype.sum_prod_type_right]

omit [Fintype nA] [DecidableEq nA] [DecidableEq nB] in
/-- The partial trace over `B` of a Hermitian operator is Hermitian. -/
theorem IsHermitian.partialTraceRight {M : Matrix (nA × nB) (nA × nB) ℂ}
    (hM : M.IsHermitian) : (partialTraceRight M).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [partialTraceRight_apply, star_sum]
  exact Finset.sum_congr rfl fun j _ => hM.apply (a, j) (b, j)

omit [Fintype nB] [DecidableEq nA] [DecidableEq nB] in
/-- The partial trace over `A` of a Hermitian operator is Hermitian. -/
theorem IsHermitian.partialTraceLeft {M : Matrix (nA × nB) (nA × nB) ℂ}
    (hM : M.IsHermitian) : (partialTraceLeft M).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [partialTraceLeft_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => hM.apply (i, a) (i, b)

/-! ## Completely positive (compression) decomposition

`Tr_B M = ∑ⱼ M.submatrix (· ↦ (·, j)) (· ↦ (·, j))`: the partial trace is the sum of the
compressions of `M` to the diagonal `j`-th blocks. The reindexing map `a ↦ (a, j)` is the
block-inclusion isometry, and `M.submatrix e e` is the conjugation `Eᴴ M E`; this is exactly the
Kraus form of the partial trace, written without matrix multiplication. -/

omit [Fintype nA] [DecidableEq nA] [DecidableEq nB] in
/-- Compression / Kraus decomposition of the right partial trace. -/
theorem partialTraceRight_eq_sum_submatrix (M : Matrix (nA × nB) (nA × nB) ℂ) :
    partialTraceRight M = ∑ j : nB, M.submatrix (fun a => (a, j)) (fun a => (a, j)) := by
  ext i i'
  simp only [Matrix.sum_apply, Matrix.submatrix_apply, partialTraceRight_apply]

omit [Fintype nB] [DecidableEq nA] [DecidableEq nB] in
/-- Compression / Kraus decomposition of the left partial trace. -/
theorem partialTraceLeft_eq_sum_submatrix (M : Matrix (nA × nB) (nA × nB) ℂ) :
    partialTraceLeft M = ∑ i : nA, M.submatrix (fun b => (i, b)) (fun b => (i, b)) := by
  ext j j'
  simp only [Matrix.sum_apply, Matrix.submatrix_apply, partialTraceLeft_apply]

omit [Fintype nA] [DecidableEq nA] [DecidableEq nB] in
/-- The partial trace over `B` of a positive semidefinite operator is positive semidefinite. -/
theorem PosSemidef.partialTraceRight {M : Matrix (nA × nB) (nA × nB) ℂ}
    (hM : M.PosSemidef) : (partialTraceRight M).PosSemidef := by
  rw [partialTraceRight_eq_sum_submatrix]
  exact Matrix.posSemidef_sum Finset.univ (fun j _ => hM.submatrix (fun a => (a, j)))

omit [Fintype nB] [DecidableEq nA] [DecidableEq nB] in
/-- The partial trace over `A` of a positive semidefinite operator is positive semidefinite. -/
theorem PosSemidef.partialTraceLeft {M : Matrix (nA × nB) (nA × nB) ℂ}
    (hM : M.PosSemidef) : (partialTraceLeft M).PosSemidef := by
  rw [partialTraceLeft_eq_sum_submatrix]
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => hM.submatrix (fun b => (i, b)))

end ErgodicTheory.OperatorEntropy
