/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.Partition

/-!
# Joins of finite measurable partitions and conditional entropy

This file continues the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`Oseledets.Entropy.Partition`. It records that the cells of a `MeasurePartition` of a probability
space have `μ`-measures summing to `1`, constructs the **join** (common refinement) `α ∨ β` of two
partitions, and defines the **conditional entropy** `H(α | β)` together with the **chain rule**
`H(α ∨ β) = H(α | β) + H(β)`.

Following the Le Maître notes on the Kolmogorov–Sinai theorem, the join of partitions
`α = (Aᵢ)` and `β = (Bⱼ)` is the partition whose cells are the nonempty intersections
`Aᵢ ∩ Bⱼ`; here we keep all index pairs `(i, j)` and allow null cells, so the join is indexed by
`ι × κ`. The conditional entropy is defined so that the chain rule holds *unconditionally*, by
taking `H(α | β) := H(α ∨ β) - H(β)`.

## Main definitions

* `Oseledets.Entropy.MeasurePartition.join`: the common refinement of two finite measurable
  partitions, with cells `Aᵢ ∩ Bⱼ`.
* `Oseledets.Entropy.condEntropy`: the conditional entropy `H(α | β)` of one family given another,
  defined as the difference `H(join) - H(β)` so that the chain rule is an identity.

## Main results

* `Oseledets.Entropy.MeasurePartition.sum_toReal_measure_eq_one`: the cell measures of a partition
  of a probability space sum to `1`.
* `Oseledets.Entropy.entropy_le_log_card_partition`: a partition into `k` cells has entropy at most
  `log k`.
* `Oseledets.Entropy.chainRule`: `H(α ∨ β) = H(α | β) + H(β)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function
open scoped ENNReal

namespace Oseledets.Entropy

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

/-- The **join** (common refinement) `α ∨ β` of two finite measurable partitions `α = P` and
`β = Q` of `(α, μ)`: the partition indexed by `ι × κ` whose cell at `(i, j)` is the intersection
`P.cells i ∩ Q.cells j`. Each cell is measurable; the family is pairwise almost-everywhere
disjoint because two distinct index pairs differ in at least one coordinate, where the
corresponding factor partition is a.e. disjoint; and the cells cover the space because both factor
partitions do. -/
noncomputable def MeasurePartition.join [Fintype ι] [Fintype κ] {μ : Measure α}
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) : MeasurePartition μ (ι × κ) where
  cells := fun p => P.cells p.1 ∩ Q.cells p.2
  measurable := fun p => (P.measurable p.1).inter (Q.measurable p.2)
  aedisjoint := by
    intro p q hpq
    simp only [onFun]
    by_cases h1 : p.1 = q.1
    · -- equal first coordinate, so the second coordinates differ
      have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      exact AEDisjoint.mono (Q.aedisjoint h2) Set.inter_subset_right Set.inter_subset_right
    · -- first coordinates differ
      exact AEDisjoint.mono (P.aedisjoint h1) Set.inter_subset_left Set.inter_subset_left
  cover := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hx1 : x ∈ ⋃ i, P.cells i := P.cover ▸ Set.mem_univ x
    have hx2 : x ∈ ⋃ j, Q.cells j := Q.cover ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx2
    exact Set.mem_iUnion.mpr ⟨(i, j), ⟨hi, hj⟩⟩

/-- The cell family `(i, j) ↦ s i ∩ t j` underlying the join of two families of cells. -/
def joinCells (s : ι → Set α) (t : κ → Set α) : ι × κ → Set α :=
  fun p => s p.1 ∩ t p.2

omit [MeasurableSpace α] in
@[simp]
lemma joinCells_apply (s : ι → Set α) (t : κ → Set α) (p : ι × κ) :
    joinCells s t p = s p.1 ∩ t p.2 := rfl

/-- The cells of `MeasurePartition.join P Q` are exactly `joinCells P.cells Q.cells`. -/
@[simp]
lemma MeasurePartition.join_cells [Fintype ι] [Fintype κ] {μ : Measure α}
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    (P.join Q).cells = joinCells P.cells Q.cells := rfl

/-- The **conditional entropy** `H(α | β)` of a finite family of cells `s : ι → Set α` given a
second family `t : κ → Set α`, defined as the difference `H(α ∨ β) - H(β)` of the joint entropy
(the entropy of the join `joinCells s t`, with cell `s i ∩ t j` at `(i, j)`) and the entropy of
`t`. With this definition the chain rule `H(α ∨ β) = H(α | β) + H(β)` holds unconditionally. -/
noncomputable def condEntropy [Fintype ι] [Fintype κ] (μ : Measure α) (s : ι → Set α)
    (t : κ → Set α) : ℝ :=
  entropy μ (joinCells s t) - entropy μ t

/-- **Chain rule for Shannon entropy.** The joint entropy of two families of cells decomposes as
the conditional entropy of the first given the second plus the entropy of the second:
`H(α ∨ β) = H(α | β) + H(β)`. With the difference definition of `condEntropy` this is an
algebraic identity, and in particular holds with no hypotheses on the families. -/
lemma chainRule [Fintype ι] [Fintype κ] (μ : Measure α) (s : ι → Set α) (t : κ → Set α) :
    entropy μ (joinCells s t) = condEntropy μ s t + entropy μ t := by
  rw [condEntropy]; ring

end Oseledets.Entropy
