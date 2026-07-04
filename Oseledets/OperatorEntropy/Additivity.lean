import Oseledets.OperatorEntropy.Basic
import Oseledets.OperatorEntropy.KroneckerSpectrum
import Mathlib.Analysis.Matrix.Order

/-!
# Additivity of von Neumann entropy under the tensor (Kronecker) product

For density matrices `ρ` and `σ` over `ℂ`, the von Neumann entropy of their
Kronecker product is the sum of the individual entropies:

`S(ρ ⊗ σ) = S(ρ) + S(σ)`.

The proof passes to the *multiset* of eigenvalues of `ρ ⊗ₖ σ`, which by
`eigenvalues_kronecker_multiset` is the multiset of pairwise products
`λᵢ · μⱼ`.  Writing `negMulLog (λᵢ μⱼ) = μⱼ · negMulLog λᵢ + λᵢ · negMulLog μⱼ`
and using that each eigenvalue family sums to `1` (unit trace) collapses the
double sum to `S(ρ) + S(σ)`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- The Kronecker (tensor) product of two density matrices, again a density
matrix on the product index type `nA × nB`. -/
def DensityMatrix.kron (ρ : DensityMatrix nA) (σ : DensityMatrix nB) :
    DensityMatrix (nA × nB) where
  val := ρ.val ⊗ₖ σ.val
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_one := by rw [Matrix.trace_kronecker, ρ.trace_one, σ.trace_one]; ring

/-- **Additivity of von Neumann entropy under the tensor product.**
`S(ρ ⊗ σ) = S(ρ) + S(σ)`. -/
theorem vonNeumannEntropy_additive_kronecker (ρ : DensityMatrix nA) (σ : DensityMatrix nB) :
    vonNeumannEntropy (ρ.kron σ) = vonNeumannEntropy ρ + vonNeumannEntropy σ := by
  -- Step A: the eigenvalue multiset of `ρ ⊗ₖ σ` is the multiset of pairwise products.
  have e1 : Finset.univ.val.map (ρ.kron σ).posSemidef.1.eigenvalues
      = Finset.univ.val.map
        (fun q : nA × nB =>
          ρ.posSemidef.1.eigenvalues q.1 * σ.posSemidef.1.eigenvalues q.2) :=
    eigenvalues_kronecker_multiset ρ.posSemidef.1 σ.posSemidef.1
  have hStepA : vonNeumannEntropy (ρ.kron σ)
      = ∑ q : nA × nB,
          negMulLog (ρ.posSemidef.1.eigenvalues q.1 * σ.posSemidef.1.eigenvalues q.2) := by
    unfold vonNeumannEntropy
    have h := congrArg (fun m : Multiset ℝ => (m.map negMulLog).sum) e1
    simpa only [Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def] using h
  -- Step B: split the summand and contract each fibrewise sum using unit trace.
  have step : ∀ i : nA,
      (∑ j : nB,
          negMulLog (ρ.posSemidef.1.eigenvalues i * σ.posSemidef.1.eigenvalues j))
        = negMulLog (ρ.posSemidef.1.eigenvalues i)
          + ρ.posSemidef.1.eigenvalues i * vonNeumannEntropy σ := by
    intro i
    simp only [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
    rw [σ.sum_eigenvalues_eq_one, one_mul]
    rfl
  rw [hStepA, Fintype.sum_prod_type]
  simp only [step]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ρ.sum_eigenvalues_eq_one, one_mul]
  rfl

end Oseledets.OperatorEntropy
