import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Real.StarOrdered

/-!
# Density matrices and von Neumann entropy

The foundational layer of the operator-entropy cluster: the `DensityMatrix` structure (a
positive-semidefinite, unit-trace complex matrix) and its von Neumann entropy
`S(ρ) = ∑ᵢ negMulLog(λᵢ)` over the real eigenvalues.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite-dimensional density matrix over `ℂ`: a positive-semidefinite, unit-trace matrix. -/
@[ext]
structure DensityMatrix (n : Type*) [Fintype n] [DecidableEq n] where
  val : Matrix n n ℂ
  posSemidef : val.PosSemidef
  trace_one : val.trace = 1

/-- The von Neumann entropy `S(ρ) = ∑ᵢ negMulLog(λᵢ)` over the (real) eigenvalues of `ρ`. -/
def vonNeumannEntropy (ρ : DensityMatrix n) : ℝ :=
  ∑ i, Real.negMulLog (ρ.posSemidef.1.eigenvalues i)

/-- The eigenvalues of a density matrix are nonnegative. -/
theorem DensityMatrix.eigenvalues_nonneg (ρ : DensityMatrix n) (i : n) :
    0 ≤ ρ.posSemidef.1.eigenvalues i :=
  ρ.posSemidef.eigenvalues_nonneg i

/-- The eigenvalues of a density matrix sum to `1` (its trace). -/
theorem DensityMatrix.sum_eigenvalues_eq_one (ρ : DensityMatrix n) :
    ∑ i, ρ.posSemidef.1.eigenvalues i = 1 := by
  have h := ρ.posSemidef.1.trace_eq_sum_eigenvalues
  rw [ρ.trace_one] at h
  have h2 : ((∑ i, ρ.posSemidef.1.eigenvalues i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simpa using h.symm
  exact_mod_cast h2

/-- Each eigenvalue of a density matrix is at most `1`. -/
theorem DensityMatrix.eigenvalues_le_one (ρ : DensityMatrix n) (i : n) :
    ρ.posSemidef.1.eigenvalues i ≤ 1 := by
  rw [← ρ.sum_eigenvalues_eq_one]
  exact Finset.single_le_sum (fun j _ => ρ.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The von Neumann entropy of a density matrix is nonnegative. -/
theorem vonNeumannEntropy_nonneg (ρ : DensityMatrix n) : 0 ≤ vonNeumannEntropy ρ :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (ρ.eigenvalues_nonneg i) (ρ.eigenvalues_le_one i)

/-- The maximally mixed state `(dim)⁻¹ • I`: a canonical inhabitant of `DensityMatrix n` for
nonempty `n`, witnessing that the density-matrix API and the entropy bounds are non-vacuous. -/
def DensityMatrix.maximallyMixed [Nonempty n] : DensityMatrix n where
  val := ((Fintype.card n : ℝ)⁻¹ : ℝ) • (1 : Matrix n n ℂ)
  posSemidef := (Matrix.PosSemidef.one).smul (by positivity)
  trace_one := by
    have : 0 < Fintype.card n := Fintype.card_pos
    rw [Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]; push_cast; field_simp

instance : Inhabited (DensityMatrix (Fin 1)) := ⟨DensityMatrix.maximallyMixed⟩

/-- Non-vacuity certificate: the von Neumann entropy nonnegativity bound fires on a concrete
state (the maximally mixed state of a two-level system). -/
example : 0 ≤ vonNeumannEntropy (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)) :=
  vonNeumannEntropy_nonneg _

end Oseledets.OperatorEntropy
