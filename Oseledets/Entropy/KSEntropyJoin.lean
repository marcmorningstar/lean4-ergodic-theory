/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.KSEntropy
import Mathlib.Logic.Equiv.Prod

/-!
# Dynamical subadditivity of the Kolmogorov–Sinai entropy under joins

For a measure-preserving transformation `T` and two finite measurable partitions `α` and `β`, the
partition-relative Kolmogorov–Sinai entropy is **subadditive under the join**:
`h(α ∨ β, T) ≤ h(α, T) + h(β, T)`.

This is the dynamical refinement of the static join subadditivity `H(α ∨ β) ≤ H(α) + H(β)`
(`entropy_join_le`) into the long-run entropy rate. The mechanism is a structural cell identity:
the `n`-fold dynamical join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ(α ∨ β)` of the join is, cell by cell, the static join of
the `n`-fold dynamical join of `α` with the `n`-fold dynamical join of `β`. Indeed for an index
`f : Fin n → ι × κ`,
`⋂ₖ T⁻ᵏ((α ∨ β)_{f k}) = ⋂ₖ T⁻ᵏ(α_{(f k).1} ∩ β_{(f k).2})`
`= (⋂ₖ T⁻ᵏ α_{(f k).1}) ∩ (⋂ₖ T⁻ᵏ β_{(f k).2})`,
because preimages and finite intersections commute. Reindexing the product index type
`Fin n → ι × κ` by `Equiv.arrowProdEquivProdArrow` (so `f ↦ (g, h)` with `g k = (f k).1`,
`h k = (f k).2`) identifies the `n`-fold join entropy of `α ∨ β` with the static join entropy of
the two `n`-fold joins; `entropy_join_le` then bounds it by `ksEntropySeq α n + ksEntropySeq β n`.
Dividing by `n` and passing both sides to the Fekete limit (`tendsto_ksEntropySeq`,
`le_of_tendsto_of_tendsto'`, with the sum limit from `Tendsto.add`) yields the claim.

## Main definitions

* `Oseledets.Entropy.joinPartition`: the join (common refinement) `α ∨ β` of two finite measurable
  partitions, as a `MeasurePartition μ (ι × κ)` with cells `joinCells α.cells β.cells`.

## Main results

* `Oseledets.Entropy.ksEntropySeq_join_le`: `ksEntropySeq (α ∨ β) n ≤ ksEntropySeq α n +
  ksEntropySeq β n`, the per-`n` cell-level subadditivity.
* `Oseledets.Entropy.ksEntropyPartition_join_le`: `h(α ∨ β, T) ≤ h(α, T) + h(β, T)`, the dynamical
  subadditivity of the Kolmogorov–Sinai entropy under joins.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter Topology

namespace Oseledets.Entropy

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

/-- The **join partition** `α ∨ β`, the common refinement of two finite measurable partitions `P`
(`= α`) and `Q` (`= β`) of a probability space, as a `MeasurePartition μ (ι × κ)` with cell at
`(i, j)` the intersection `Aᵢ ∩ Bⱼ` (`joinCells P.cells Q.cells`). Each cell is measurable as the
intersection of two measurable cells; the cells are pairwise almost-everywhere disjoint because two
distinct pairs `(i, j) ≠ (i', j')` differ in some coordinate, where the corresponding `P`- or
`Q`-cells are a.e. disjoint and the cell is contained in that coordinate's cell; and the cells
cover the space since `⋃_{i,j} Aᵢ ∩ Bⱼ = (⋃ᵢ Aᵢ) ∩ (⋃ⱼ Bⱼ) = univ ∩ univ`. -/
def joinPartition [Fintype ι] [Fintype κ] {μ : Measure α}
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) : MeasurePartition μ (ι × κ) where
  cells := joinCells P.cells Q.cells
  measurable := fun p => (P.measurable p.1).inter (Q.measurable p.2)
  aedisjoint := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hpq
    simp only [onFun, joinCells_apply]
    rcases eq_or_ne i i' with hi | hi
    · -- Same `P`-coordinate, so `j ≠ j'`; the `Q`-coordinate separates the cells.
      subst hi
      have hj : j ≠ j' := fun h => hpq (by rw [h])
      exact AEDisjoint.mono (Q.aedisjoint hj) Set.inter_subset_right Set.inter_subset_right
    · -- Distinct `P`-coordinates; the `P`-coordinate separates the cells.
      exact AEDisjoint.mono (P.aedisjoint hi) Set.inter_subset_left Set.inter_subset_left
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x -- cover via per-coordinate membership
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.cover ▸ Set.mem_univ x)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (Q.cover ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

@[simp]
lemma joinPartition_cells [Fintype ι] [Fintype κ] {μ : Measure α}
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    (joinPartition P Q).cells = joinCells P.cells Q.cells := rfl

omit [MeasurableSpace α] in
/-- **Structural cell identity for the iterated join of a join.** The cell of the `n`-fold
dynamical join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ(α ∨ β)` at an index `f : Fin n → ι × κ` is the intersection of the
cell of the `n`-fold join of `α` at the first-coordinate index `k ↦ (f k).1` with the cell of the
`n`-fold join of `β` at the second-coordinate index `k ↦ (f k).2`. This holds because preimages and
finite intersections commute:
`⋂ₖ T⁻ᵏ(α_{(f k).1} ∩ β_{(f k).2}) = (⋂ₖ T⁻ᵏ α_{(f k).1}) ∩ (⋂ₖ T⁻ᵏ β_{(f k).2})`. -/
lemma ksJoinCells_joinCells (s : ι → Set α) (t : κ → Set α) (T : α → α) (n : ℕ)
    (f : Fin n → ι × κ) :
    ksJoinCells (joinCells s t) T n f
      = ksJoinCells s T n (fun k => (f k).1) ∩ ksJoinCells t T n (fun k => (f k).2) := by
  simp only [ksJoinCells_apply, joinCells_apply, Set.preimage_inter]
  rw [Set.iInter_inter_distrib]

/-- **Per-`n` cell-level subadditivity.** The `n`-fold dynamical-join entropy of the join `α ∨ β` is
at most the sum of the `n`-fold dynamical-join entropies of `α` and `β`:
`H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ(α ∨ β)) ≤ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α) + H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ β)`.

Reindexing the product index `Fin n → ι × κ` by `Equiv.arrowProdEquivProdArrow` and using the cell
identity `ksJoinCells_joinCells`, the `(α ∨ β)`-join entropy equals the *static* join entropy of
the two `n`-fold joins; `entropy_join_le` then bounds it by the sum. -/
lemma ksEntropySeq_join_le [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (Q : MeasurePartition μ κ) (n : ℕ) :
    ksEntropySeq hT (joinPartition P Q) n
      ≤ ksEntropySeq hT P n + ksEntropySeq hT Q n := by
  -- The `n`-fold joins of `α` and `β`, as the two factors of a static join.
  set A : MeasurePartition μ (Fin n → ι) := ksJoin hT P n with hA
  set B : MeasurePartition μ (Fin n → κ) := ksJoin hT Q n with hB
  -- Rewrite the `(α ∨ β)`-join entropy as a static join entropy via the product reindexing.
  have hreindex : ksEntropySeq hT (joinPartition P Q) n
      = entropy μ (joinCells A.cells B.cells) := by
    rw [ksEntropySeq, ksJoin_cells, joinPartition_cells,
      ← entropy_reindex μ (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ)).symm,
      entropy_def, entropy_def]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨g, h⟩ := p
    rw [hA, hB, ksJoin_cells, ksJoin_cells, joinCells_apply]
    have hcell : ksJoinCells (joinCells P.cells Q.cells) T n
        ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ)).symm (g, h))
          = ksJoinCells P.cells T n g ∩ ksJoinCells Q.cells T n h :=
      ksJoinCells_joinCells P.cells Q.cells T n _
    rw [hcell]
  rw [hreindex, ksEntropySeq, ksEntropySeq, ← hA, ← hB]
  exact entropy_join_le A B

/-- **Dynamical subadditivity of the Kolmogorov–Sinai entropy under joins:**
`h(α ∨ β, T) ≤ h(α, T) + h(β, T)`.

The per-`n` bound `ksEntropySeq_join_le` divided by `n` reads
`ksEntropySeq (α ∨ β) n / n ≤ ksEntropySeq α n / n + ksEntropySeq β n / n`. Each averaged sequence
converges to its Kolmogorov–Sinai entropy by `tendsto_ksEntropySeq`, so the right-hand side
converges to `h(α, T) + h(β, T)` (`Tendsto.add`); passing the pointwise inequality to the limits
(`le_of_tendsto_of_tendsto'`) gives the claim. -/
lemma ksEntropyPartition_join_le [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (Q : MeasurePartition μ κ) :
    ksEntropyPartition hT (joinPartition P Q)
      ≤ ksEntropyPartition hT P + ksEntropyPartition hT Q := by
  have hsum : Tendsto
      (fun n => ksEntropySeq hT P n / n + ksEntropySeq hT Q n / n) atTop
      (𝓝 (ksEntropyPartition hT P + ksEntropyPartition hT Q)) :=
    (tendsto_ksEntropySeq hT P).add (tendsto_ksEntropySeq hT Q)
  refine le_of_tendsto_of_tendsto' (tendsto_ksEntropySeq hT (joinPartition P Q)) hsum ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← add_div, div_le_div_iff_of_pos_right hn0]
    exact ksEntropySeq_join_le hT P Q n

end Oseledets.Entropy
