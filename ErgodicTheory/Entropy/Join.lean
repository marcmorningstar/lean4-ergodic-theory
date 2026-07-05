/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Partition

/-!
# Cell-measure sum and joins of finite measurable partitions

This file continues the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`ErgodicTheory.Entropy.Partition`. It records that the cells of a `MeasurePartition` of a
probability
space have `μ`-measures summing to `1`, and introduces the cell family `joinCells s t` of the
**join** (common refinement) `α ∨ β` of two partitions, whose cells are the intersections
`Aᵢ ∩ Bⱼ`.

Following the Le Maître notes on the Kolmogorov–Sinai theorem, the join keeps all index pairs
`(i, j)` and allows null cells, so it is indexed by `ι × κ`.

## Main definitions

* `ErgodicTheory.Entropy.joinCells`: the family `(i, j) ↦ s i ∩ t j` of intersection cells of two
  families.

## Main results

* `ErgodicTheory.Entropy.MeasurePartition.sum_toReal_measure_eq_one`: the cell measures
  of a partition
  of a probability space sum to `1`.
* `ErgodicTheory.Entropy.entropy_le_log_card_partition`: a partition into `k` cells has
  entropy at most
  `log k`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

/-- The `μ`-measures of the cells of a finite measurable partition of a probability space sum to
the total mass `1`. The cells are measurable, pairwise almost-everywhere disjoint, and cover the
whole space, so finite additivity of `μ` over an a.e.-disjoint null-measurable family gives
`∑ i, μ (cells i) = μ univ = 1`. -/
lemma MeasurePartition.sum_toReal_measure_eq_one [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] (P : MeasurePartition μ ι) :
    ∑ i, (μ (P.cells i)).toReal = 1 := by
  have hadd : μ (⋃ i ∈ (Finset.univ : Finset ι), P.cells i) = ∑ i, μ (P.cells i) :=
    measure_biUnion_finset₀
      (fun i _ j _ hij => P.aedisjoint hij)
      (fun i _ => (P.measurable i).nullMeasurableSet)
  simp only [Finset.mem_univ, Set.iUnion_true] at hadd
  rw [P.cover, measure_univ] at hadd
  have hfin : ∀ i, μ (P.cells i) ≠ ⊤ := fun i => measure_ne_top μ (P.cells i)
  rw [← ENNReal.toReal_sum (fun i _ => hfin i), ← hadd, ENNReal.toReal_one]

/-- **Corollary of Proposition 1 (Le Maître).** A finite measurable partition of a probability
space into `k` cells has Shannon entropy at most `log k`. -/
lemma entropy_le_log_card_partition [Fintype ι] [Nonempty ι] {μ : Measure α}
    [IsProbabilityMeasure μ] (P : MeasurePartition μ ι) :
    entropy μ P.cells ≤ Real.log (Fintype.card ι) :=
  entropy_le_log_card μ P.cells P.sum_toReal_measure_eq_one

/-- The cell family `(i, j) ↦ s i ∩ t j` underlying the join (common refinement) `α ∨ β` of two
families of cells `s : ι → Set α` and `t : κ → Set α`. -/
def joinCells (s : ι → Set α) (t : κ → Set α) : ι × κ → Set α :=
  fun p => s p.1 ∩ t p.2

omit [MeasurableSpace α] in
@[simp]
lemma joinCells_apply (s : ι → Set α) (t : κ → Set α) (p : ι × κ) :
    joinCells s t p = s p.1 ∩ t p.2 := rfl

end ErgodicTheory.Entropy
