import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import ErgodicTheory.Entropy.NegMulLogBound
import ErgodicTheory.OperatorEntropy.Basic

/-!
# Maximum entropy: `S(ρ) ≤ log (rank ρ)`

The von Neumann entropy of a density matrix is bounded above by the logarithm of its rank, and
hence by the logarithm of the ambient dimension.  This is the finite-dimensional maximum-entropy
inequality: among all states supported on a `k`-dimensional subspace the maximally mixed state,
with entropy `log k`, is the most disordered.

The proof restricts the entropy sum `S(ρ) = ∑ᵢ negMulLog(λᵢ)` to the support `s = {i | λᵢ ≠ 0}`
(the off-support terms vanish because `negMulLog 0 = 0`), whose cardinality is the rank
(`Matrix.IsHermitian.rank_eq_card_non_zero_eigs`), and applies the shared uniform-weight Jensen
bound `ErgodicTheory.sum_negMulLog_le_log_card` (`ErgodicTheory.Entropy.NegMulLogBound`).

## Main results

* `ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_rank`
* `ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_card`
-/

open Matrix Real
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A density matrix has positive rank: its eigenvalues sum to `1`, so at least one is nonzero. -/
theorem DensityMatrix.rank_pos (ρ : DensityMatrix n) : 0 < ρ.val.rank := by
  classical
  rw [ρ.posSemidef.1.rank_eq_card_non_zero_eigs, Fintype.card_pos_iff]
  have hz : ∑ i, ρ.posSemidef.1.eigenvalues i ≠ 0 := by
    rw [ρ.sum_eigenvalues_eq_one]; exact one_ne_zero
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact ⟨⟨i, hi⟩⟩

/-- **Maximum entropy bound.** The von Neumann entropy of a density matrix is at most the
logarithm of its rank. -/
theorem vonNeumannEntropy_le_log_rank (ρ : DensityMatrix n) :
    vonNeumannEntropy ρ ≤ Real.log (ρ.val.rank : ℝ) := by
  classical
  set lam : n → ℝ := ρ.posSemidef.1.eigenvalues with hlam
  set s : Finset n := Finset.univ.filter (fun i => lam i ≠ 0) with hs
  -- eigenvalues are nonnegative and sum to one
  have hnn : ∀ i, 0 ≤ lam i := fun i => ρ.eigenvalues_nonneg i
  have hsum : ∑ i, lam i = 1 := ρ.sum_eigenvalues_eq_one
  -- off-support eigenvalues vanish
  have hsub : s ⊆ Finset.univ := by rw [hs]; exact Finset.filter_subset _ _
  have hoff : ∀ i ∈ Finset.univ, i ∉ s → lam i = 0 := by
    intro i _ hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
  -- the support has cardinality equal to the rank
  have hcardnat : s.card = ρ.val.rank := by
    rw [ρ.posSemidef.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype, hs]
  have hcardpos : 0 < s.card := by rw [hcardnat]; exact ρ.rank_pos
  have hcard : (s.card : ℝ) = (ρ.val.rank : ℝ) := by exact_mod_cast hcardnat
  -- restrict the eigenvalue sum and the entropy sum to the support
  have hsum_s : ∑ i ∈ s, lam i = 1 := by
    rw [Finset.sum_subset hsub hoff]; exact hsum
  have hent : vonNeumannEntropy ρ = ∑ i ∈ s, Real.negMulLog (lam i) := by
    have hfull : vonNeumannEntropy ρ = ∑ i, Real.negMulLog (lam i) := rfl
    rw [hfull]
    refine (Finset.sum_subset hsub ?_).symm
    intro i _ hi
    rw [hoff i (Finset.mem_univ i) hi, Real.negMulLog_zero]
  -- the maximum-entropy Jensen bound, factored into `ErgodicTheory.sum_negMulLog_le_log_card`
  rw [hent, ← hcard]
  exact sum_negMulLog_le_log_card (Finset.card_pos.mp hcardpos) (fun i _ => hnn i) hsum_s

/-- The von Neumann entropy of a density matrix is at most the logarithm of the ambient
dimension `Fintype.card n`. -/
theorem vonNeumannEntropy_le_log_card (ρ : DensityMatrix n) :
    vonNeumannEntropy ρ ≤ Real.log (Fintype.card n : ℝ) := by
  refine (vonNeumannEntropy_le_log_rank ρ).trans (Real.log_le_log ?_ ?_)
  · exact_mod_cast ρ.rank_pos
  · exact_mod_cast Matrix.rank_le_card_width ρ.val

end ErgodicTheory.OperatorEntropy
