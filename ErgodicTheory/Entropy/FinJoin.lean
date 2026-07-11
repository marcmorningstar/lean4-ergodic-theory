/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropyPow
import ErgodicTheory.Entropy.FactorEntropy

/-!
# The join of a finite family of measurable partitions

Kolmogorov–Sinai entropy is built from the two-family join `joinCells` and its arithmetic iterate
`ksJoin`. Ito's elementary proof of Abramov's flow-entropy theorem (issue #48) instead joins a
single partition pulled back at an *arbitrary finite set of times* — a non-arithmetic subsequence —
so neither `joinCells` (only two families) nor `ksJoin` (an arithmetic orbit) suffices.

This file promotes the join of a finite family `P : Fin N → MeasurePartition μ ι` to a first-class
`MeasurePartition μ (Fin N → ι)`, with cells `f ↦ ⋂ k, (P k).cells (f k)`, and records the API the
downstream Abramov chain needs: a cell-description simp lemma, the subfamily-refinement inequality
`H(⋁_{j} P (e j)) ≤ H(⋁_{k} P k)` for an index embedding `e`, and compatibility with pulling back
along a measure-preserving map.

## Main definitions

* `ErgodicTheory.Entropy.finJoinCells`: the bare cell family `f ↦ ⋂ k, β k (f k)` of the join of a
  finite family of cell families `β : Fin N → ι → Set α`.
* `ErgodicTheory.Entropy.finJoin`: the bundled `MeasurePartition μ (Fin N → ι)` join of a finite
  family `P : Fin N → MeasurePartition μ ι`.

## Main results

* `ErgodicTheory.Entropy.entropy_finJoin_le_of_subfamily`: the Shannon entropy of the join over a
  subfamily selected by an embedding `e : Fin M ↪ Fin N` is at most that of the full join.
* `ErgodicTheory.Entropy.finJoinCells_pulledBack`: pulling back the finite join along a
  measure-preserving map is the finite join of the pulled-back partitions.
-/

open MeasureTheory Function

namespace ErgodicTheory.Entropy

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}

/-- The cell family of the join of a finite family `β : Fin N → (ι → Set α)` of cell families:
`f ↦ ⋂ k, β k (f k)`, indexed by the choice functions `f : Fin N → ι`. -/
def finJoinCells {N : ℕ} (β : Fin N → ι → Set α) : (Fin N → ι) → Set α :=
  fun f => ⋂ k, β k (f k)

omit [MeasurableSpace α] in
@[simp]
lemma finJoinCells_apply {N : ℕ} (β : Fin N → ι → Set α) (f : Fin N → ι) :
    finJoinCells β f = ⋂ k, β k (f k) := rfl

variable [Fintype ι]

/-- The **join of a finite family** `P : Fin N → MeasurePartition μ ι` of finite measurable
partitions: the partition of `α` indexed by the choice functions `f : Fin N → ι` whose cell at `f`
is the intersection `⋂ k, (P k).cells (f k)`. Each cell is measurable (a countable intersection of
measurable cells); the cells are pairwise a.e. disjoint (two distinct choice functions `f ≠ f'`
differ at some coordinate `k₀`, where the corresponding cells are a.e. disjoint); and they cover the
space (choosing, for each `k`, a cell of `P k` containing a given point). -/
noncomputable def finJoin {N : ℕ} (P : Fin N → MeasurePartition μ ι) :
    MeasurePartition μ (Fin N → ι) where
  cells := finJoinCells (fun k => (P k).cells)
  measurable := fun f => MeasurableSet.iInter fun k => (P k).measurable (f k)
  aedisjoint := by
    intro f f' hff'
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hff'
    have hsub : finJoinCells (fun k => (P k).cells) f ∩ finJoinCells (fun k => (P k).cells) f'
        ⊆ (P k₀).cells (f k₀) ∩ (P k₀).cells (f' k₀) :=
      Set.inter_subset_inter (Set.iInter_subset _ k₀) (Set.iInter_subset _ k₀)
    exact measure_mono_null hsub ((P k₀).aedisjoint hk₀)
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hk : ∀ k, ∃ i, x ∈ (P k).cells i := by
      intro k
      have hx : x ∈ ⋃ i, (P k).cells i := by rw [(P k).cover]; trivial
      simpa using hx
    choose f hf using hk
    rw [Set.mem_iUnion]
    exact ⟨f, Set.mem_iInter.mpr hf⟩

@[simp]
lemma finJoin_cells {N : ℕ} (P : Fin N → MeasurePartition μ ι) :
    (finJoin P).cells = finJoinCells (fun k => (P k).cells) := rfl

/-- **Compatibility with pullback.** Pulling back the finite join along a measure-preserving map `π`
is the finite join of the pulled-back partitions: at every choice function `f`,
`(⋁_k π⁻¹(R k)).cells f = π⁻¹ ((⋁_k R k).cells f)`. -/
lemma finJoinCells_pulledBack {β : Type*} [MeasurableSpace β] {ν : Measure β} {π : α → β}
    (hπ : MeasurePreserving π μ ν) {N : ℕ} (R : Fin N → MeasurePartition ν ι) (f : Fin N → ι) :
    (finJoin (fun k => (R k).pulledBack hπ)).cells f = π ⁻¹' (finJoin R).cells f := by
  simp only [finJoin_cells, finJoinCells_apply, MeasurePartition.pulledBack_cells,
    Set.preimage_iInter]

variable [IsProbabilityMeasure μ]

/-- **Subfamily-refinement inequality.** Selecting a subfamily of a finite family of partitions
along an index embedding `e : Fin M ↪ Fin N` can only decrease the Shannon entropy of the join: the
full join `⋁_{k} P k` refines the subfamily join `⋁_{j} P (e j)` (dropping some intersection factors
is a coarsening), so `H(⋁_{j} P (e j)) ≤ H(⋁_{k} P k)`. Proved from static refinement monotonicity
(`entropy_le_of_refines`) with the coarsening map `f ↦ f ∘ e`. -/
lemma entropy_finJoin_le_of_subfamily {M N : ℕ} (P : Fin N → MeasurePartition μ ι)
    (e : Fin M ↪ Fin N) :
    entropy μ (finJoin (fun j => P (e j))).cells ≤ entropy μ (finJoin P).cells := by
  refine entropy_le_of_refines (finJoin (fun j => P (e j))) (finJoin P)
    (fun f j => f (e j)) fun f => ?_
  -- the full-join cell at `f` is contained in the subfamily-join cell at `f ∘ e`
  refine HasSubset.Subset.eventuallyLE ?_
  simp only [finJoin_cells, finJoinCells_apply]
  exact Set.subset_iInter fun j => Set.iInter_subset (fun k => (P k).cells (f k)) (e j)

end ErgodicTheory.Entropy
