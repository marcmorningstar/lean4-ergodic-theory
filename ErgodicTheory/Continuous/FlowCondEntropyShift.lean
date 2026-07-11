/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondChainRule
import ErgodicTheory.Entropy.FactorEntropy
import ErgodicTheory.Continuous.Flow

/-!
# Invariance of conditional partition entropy under a common pullback, and the flow-shift identity

Ito's elementary proof of Abramov's flow-entropy theorem (issue #48) repeatedly rewrites a
conditional entropy `H(φ_a P | φ_b P)` of a partition pulled back at two flow times as the
"centred" form `H(φ_{a-b} P | P)`. The mechanism is that `condEntropyGivenPartition` depends only
on the measures of the cells and of their pairwise intersections, all of which are preserved when
both partitions are replaced by their preimages under a single measure-preserving map (here the
time-`b` map of the flow). Note this needs only measure-preservation, not invertibility.

## Main results

* `ErgodicTheory.condEntropyGivenPartition_comap_left`: conditional partition entropy is unchanged
  when both cell families are pulled back along one measure-preserving map.
* `ErgodicTheory.condEntropyGivenPartition_flow_shift`: for a measure-preserving flow,
  `H(φ_a P | φ_b P) = H(φ_{a-b} P | P)`.
-/

open MeasureTheory Function

namespace ErgodicTheory

open Entropy

/-! ## W_inv: conditional-entropy invariance under a common measure-preserving pullback -/

/-- **Conditional-entropy invariance under a common measure-preserving pullback.** For a
measure-preserving map `S` and finite families of *measurable* cells `s`, `t`,
`H(S⁻¹s | S⁻¹t) = H(s | t)`: every summand of `condEntropyGivenPartition` is a function of the
measures `μ(sᵢ)` and `μ(sᵢ ∩ tⱼ)`, and `S` preserves these (`MeasurePreserving.measure_preimage`,
using `Set.preimage_inter`). Only measure-preservation is used, not invertibility. -/
lemma condEntropyGivenPartition_comap_left {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι κ : Type*} [Fintype ι] [Fintype κ] {S : α → α} (hS : MeasurePreserving S μ μ)
    (s : ι → Set α) (t : κ → Set α) (hs : ∀ i, MeasurableSet (s i))
    (ht : ∀ j, MeasurableSet (t j)) :
    condEntropyGivenPartition μ (fun i => S ⁻¹' s i) (fun j => S ⁻¹' t j)
      = condEntropyGivenPartition μ s t := by
  simp only [condEntropyGivenPartition, condEntropyOnCell]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hS.measure_preimage (hs i).nullMeasurableSet]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [← Set.preimage_inter, hS.measure_preimage ((hs i).inter (ht j)).nullMeasurableSet]

/-! ## W_shift: the flow-pullback specialisation via flow additivity -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Flow-shift of conditional partition entropy.** For a measure-preserving flow `φ` and times
`a`, `b`, the conditional entropy of the partition pulled back at time `a` given the one pulled back
at time `b` equals the "centred" conditional entropy at the time difference:
`H(φ_a P | φ_b P) = H(φ_{a-b} P | P)`.

Apply `condEntropyGivenPartition_comap_left` with the measure-preserving map `S = φ_b` to the pair
`(φ_{a-b} P, P)`; the `φ_b`-preimages turn `φ_{a-b} P` into `φ_{(a-b)+b} P = φ_a P` (flow
additivity) and `P` into `φ_b P`. -/
lemma condEntropyGivenPartition_flow_shift (φ : MeasurePreservingFlow μ) {ι : Type*} [Fintype ι]
    (P : MeasurePartition μ ι) (a b : ℝ) :
    condEntropyGivenPartition μ (P.pulledBack (φ.measurePreserving a)).cells
        (P.pulledBack (φ.measurePreserving b)).cells
      = condEntropyGivenPartition μ (P.pulledBack (φ.measurePreserving (a - b))).cells P.cells := by
  have hcomp := condEntropyGivenPartition_comap_left (φ.measurePreserving b)
    (P.pulledBack (φ.measurePreserving (a - b))).cells P.cells
    (P.pulledBack (φ.measurePreserving (a - b))).measurable P.measurable
  rw [← hcomp]
  -- `φ_a = φ_{a-b} ∘ φ_b`, so `φ_a P = φ_b⁻¹ (φ_{a-b} P)`.
  have hφa : (φ a : X → X) = φ (a - b) ∘ φ b := by
    rw [← φ.map_add]; congr 1; ring
  have hfam : (P.pulledBack (φ.measurePreserving a)).cells
      = fun i => φ b ⁻¹' (P.pulledBack (φ.measurePreserving (a - b))).cells i := by
    funext i
    simp only [MeasurePartition.pulledBack_cells, hφa, Set.preimage_comp]
  rw [hfam]
  simp only [MeasurePartition.pulledBack_cells]

end ErgodicTheory
