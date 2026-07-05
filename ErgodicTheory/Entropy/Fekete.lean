/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Subadditive
import ErgodicTheory.Entropy.Subadditive2

/-!
# Pullback partitions

This file provides the **pullback partition** `T⁻¹ β` of a finite measurable partition `β` along a
measure-preserving transformation `T`, and the `T`-invariance of its Shannon entropy. These feed
the dynamical refinement `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` and the Fekete limit `h(α, T)`, which are built in
`ErgodicTheory.Entropy.KSEntropy` (using the flat `Fin n`-indexed iterated join `ksJoin`).

It continues the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`ErgodicTheory.Entropy.Partition`, `ErgodicTheory.Entropy.Join`, `ErgodicTheory.Entropy.Subadditive`, and
`ErgodicTheory.Entropy.Subadditive2`.

## Main definitions

* `ErgodicTheory.Entropy.MeasurePartition.pullback`: the partition `T⁻¹ β` whose cells are the
  preimages `T⁻¹ Bⱼ`, for a measure-preserving `T`.

## Main results

* `ErgodicTheory.Entropy.entropy_pullback`: the pullback partition has the same entropy as the
  original, `H(T⁻¹ β) = H(β)` (the `T`-invariance of partition entropy).

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- The **pullback partition** `T⁻¹ β` of a finite measurable partition `β = P` along a
measure-preserving transformation `T : α → α`: the partition whose cell at index `i` is the
preimage `T⁻¹ (P.cells i)`. Each cell is measurable (preimage of a measurable set under the
measurable `T`); the family is pairwise almost-everywhere disjoint (the preimage of an
a.e.-disjoint pair is a.e. disjoint, since `T` preserves measures); and the cells cover the space
(the preimage of the cover `⋃ i, P.cells i = univ` is `univ`). -/
noncomputable def MeasurePartition.pullback [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) : MeasurePartition μ ι where
  cells := fun i => T ⁻¹' P.cells i
  measurable := fun i => (P.measurable i).preimage hT.measurable
  aedisjoint := by
    intro i j hij
    simp only [onFun, AEDisjoint, ← Set.preimage_inter]
    rw [hT.measure_preimage ((P.measurable i).inter (P.measurable j)).nullMeasurableSet]
    exact P.aedisjoint hij
  cover := by rw [← Set.preimage_iUnion, P.cover, Set.preimage_univ]

@[simp]
lemma MeasurePartition.pullback_cells [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    (P.pullback hT).cells = fun i => T ⁻¹' P.cells i := rfl

/-- **`T`-invariance of partition entropy.** The pullback partition `T⁻¹ β` along a
measure-preserving `T` has the same Shannon entropy as `β`, since `T` preserves the measure of
each cell. This is `entropy_comp_preimage` specialized to the cells of a partition. -/
lemma entropy_pullback [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    entropy μ (P.pullback hT).cells = entropy μ P.cells := by
  rw [MeasurePartition.pullback_cells]
  exact entropy_comp_preimage hT P.cells (fun i => (P.measurable i).nullMeasurableSet)

end ErgodicTheory.Entropy
