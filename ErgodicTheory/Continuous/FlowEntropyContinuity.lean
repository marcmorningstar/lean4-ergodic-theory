/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.Set.SymmDiff
import ErgodicTheory.Continuous.Flow
import ErgodicTheory.Entropy.CondChainRule
import ErgodicTheory.Entropy.FactorEntropy

/-!
# Continuity of conditional entropy along a measure-continuous flow (issue #48, L1)

For a **measure-continuous** measure-preserving flow `φ` (Ito's condition (D.4): every measurable
`A` has `μ(φ_t A △ A) → 0` as `t → 0`) and any finite measurable partition `P`, the conditional
entropy of the time-`t` pulled-back partition given `P` — and, symmetrically, of `P` given the
pulled-back partition — tends to `0` as `t → 0`. This is Ito's Lemma (2.2), the small-shift control
feeding the analytic heart of the elementary Abramov homogeneity proof.

## Main definitions

* `ErgodicTheory.MeasurePreservingFlow.MeasureContinuous`: Ito's flow measure-continuity (D.4).

## Main results

* `ErgodicTheory.condEntropyGivenPartition_flow_tendsto_zero`: `H(φ_t P | P) → 0` (L1).
* `ErgodicTheory.condEntropyGivenPartition_flow_tendsto_zero'`: `H(P | φ_t P) → 0` (L1, swapped
  conditioning; the symmetric companion of the previous lemma).

## References

* Yuji Ito, *An elementary proof of Abramov's result on the entropy of a flow*, Nagoya Math. J. 41
  (1971), 1–5.
-/

open MeasureTheory Function Filter Topology
open scoped ENNReal

namespace ErgodicTheory

open Entropy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-! ## The keystone predicate: measure-continuity of a flow (Ito's (D.4)) -/

/-- **Flow measure-continuity** (Ito's (D.4)): for every measurable `A`,
`μ(φ_t A △ A) → 0` as `t → 0`. The one analytic hypothesis specific to this route. -/
def MeasurePreservingFlow.MeasureContinuous (φ : MeasurePreservingFlow μ) : Prop :=
  ∀ (A : Set X), MeasurableSet A →
    Tendsto (fun t : ℝ => (μ (symmDiff (φ t ⁻¹' A) A)).toReal) (𝓝 0) (𝓝 0)

/-! ## The pointwise measure convergence feeding the entropy limit -/

/-- **Small-shift convergence of a paired cell measure.** For a measure-continuous flow, the
measure of the intersection `A ∩ φ_t⁻¹ B` converges to that of `A ∩ B` as `t → 0`. The estimate is
`|μ(A ∩ φ_t⁻¹B) − μ(A ∩ B)| ≤ μ((A ∩ φ_t⁻¹B) △ (A ∩ B)) = μ(A ∩ (φ_t⁻¹B △ B)) ≤ μ(φ_t⁻¹B △ B) → 0`,
combining `abs_measureReal_sub_le_measureReal_symmDiff` with the `∩`/`△` distributive law and
measure-continuity, then squeezing. -/
private lemma tendsto_measureReal_inter_preimage (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun t : ℝ => (μ (A ∩ (φ t) ⁻¹' B)).toReal) (𝓝 0)
      (𝓝 (μ (A ∩ B)).toReal) := by
  have hMC : Tendsto (fun t : ℝ => (μ (symmDiff ((φ t) ⁻¹' B) B)).toReal) (𝓝 0) (𝓝 0) := hφ B hB
  have hbnd : ∀ t : ℝ, ‖(μ (A ∩ (φ t) ⁻¹' B)).toReal - (μ (A ∩ B)).toReal‖
      ≤ (μ (symmDiff ((φ t) ⁻¹' B) B)).toReal := by
    intro t
    rw [Real.norm_eq_abs]
    have hApre : MeasurableSet (A ∩ (φ t) ⁻¹' B) := hA.inter (hB.preimage (φ.measurable t))
    have hAB : MeasurableSet (A ∩ B) := hA.inter hB
    have h1 := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
      hApre.nullMeasurableSet hAB.nullMeasurableSet
    rw [measureReal_def, measureReal_def, measureReal_def] at h1
    refine h1.trans ?_
    rw [← Set.inter_symmDiff_distrib_left]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.inter_subset_right)
  have hdiff : Tendsto (fun t : ℝ => (μ (A ∩ (φ t) ⁻¹' B)).toReal - (μ (A ∩ B)).toReal)
      (𝓝 0) (𝓝 0) := squeeze_zero_norm hbnd hMC
  have hadd : Tendsto (fun t : ℝ => ((μ (A ∩ (φ t) ⁻¹' B)).toReal - (μ (A ∩ B)).toReal)
      + (μ (A ∩ B)).toReal) (𝓝 0) (𝓝 (0 + (μ (A ∩ B)).toReal)) :=
    hdiff.add tendsto_const_nhds
  simpa using hadd

/-! ## `H(P | P) = 0` -/

/-- **Conditional entropy of a partition given itself vanishes.** Off-diagonal intersections have
measure `0` (a.e.-disjoint cells) so their `negMulLog` terms vanish; the diagonal ratio is `1` (on
cells of positive measure), and cells of measure `0` are killed by the leading factor. -/
private lemma condEntropyGivenPartition_self {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι) :
    condEntropyGivenPartition μ P.cells P.cells = 0 := by
  rw [condEntropyGivenPartition]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases eq_or_ne (μ (P.cells i)) 0 with h0 | h0
  · rw [h0, ENNReal.toReal_zero, zero_mul]
  · have honcell : condEntropyOnCell μ (P.cells i) P.cells = 0 := by
      rw [condEntropyOnCell]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases eq_or_ne j i with rfl | hji
      · rw [Set.inter_self, div_self (ENNReal.toReal_ne_zero.mpr ⟨h0, measure_ne_top μ _⟩),
          Real.negMulLog_one]
      · have hz : μ (P.cells i ∩ P.cells j) = 0 := P.aedisjoint (Ne.symm hji)
        rw [hz, ENNReal.toReal_zero, zero_div, Real.negMulLog_zero]
    rw [honcell, mul_zero]

/-! ## L1: the partition moves little under a small time shift (Ito's (2.2)) -/

/-- **L1 (Ito (2.2)).** For a measure-continuous flow, `H(φ_t P | P) → 0` as `t → 0`, for every
finite partition `P`. Conditioning is on `P` (first argument); the subject is the pullback `φ_t P`.
Built from `MeasureContinuous` + continuity of Shannon entropy in the cell measures. -/
lemma condEntropyGivenPartition_flow_tendsto_zero (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous) {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι) :
    Tendsto (fun t : ℝ => condEntropyGivenPartition μ P.cells
        (P.pulledBack (φ.measurePreserving t)).cells) (𝓝 0) (𝓝 0) := by
  have hself : condEntropyGivenPartition μ P.cells P.cells = 0 :=
    condEntropyGivenPartition_self P
  have main : Tendsto (fun t : ℝ => condEntropyGivenPartition μ P.cells
      (fun j => (φ t) ⁻¹' P.cells j)) (𝓝 0)
      (𝓝 (condEntropyGivenPartition μ P.cells P.cells)) := by
    simp only [condEntropyGivenPartition, condEntropyOnCell]
    refine tendsto_finsetSum _ fun i _ => ?_
    refine Filter.Tendsto.const_mul _ ?_
    refine tendsto_finsetSum _ fun j _ => ?_
    exact (Real.continuous_negMulLog.tendsto _).comp
      ((tendsto_measureReal_inter_preimage φ hφ (P.measurable i) (P.measurable j)).div_const _)
  rw [hself] at main
  simpa only [MeasurePartition.pulledBack_cells] using main

/-- **L1, swapped conditioning.** For a measure-continuous flow, `H(P | φ_t P) → 0` as `t → 0`.
The conditioning partition is the pullback `φ_t P`; the subject is `P`. This is the swapped-
conditioning companion of `condEntropyGivenPartition_flow_tendsto_zero` (symmetric API; the
Proposition itself consumes the unprimed form and derives swapped variants via the flow-shift
identity). The leading factors `μ(φ_t⁻¹ Pᵢ) = μ(Pᵢ)` are constant by measure-preservation, and the
paired cell measures `μ(φ_t⁻¹ Pᵢ ∩ Pⱼ) → μ(Pᵢ ∩ Pⱼ)` by the same squeeze as L1 (with the moving
factor commuted to the right). -/
lemma condEntropyGivenPartition_flow_tendsto_zero' (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous) {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι) :
    Tendsto (fun t : ℝ => condEntropyGivenPartition μ
        (P.pulledBack (φ.measurePreserving t)).cells P.cells) (𝓝 0) (𝓝 0) := by
  have hself : condEntropyGivenPartition μ P.cells P.cells = 0 :=
    condEntropyGivenPartition_self P
  have main : Tendsto (fun t : ℝ => condEntropyGivenPartition μ
      (fun i => (φ t) ⁻¹' P.cells i) P.cells) (𝓝 0)
      (𝓝 (condEntropyGivenPartition μ P.cells P.cells)) := by
    simp only [condEntropyGivenPartition, condEntropyOnCell]
    refine tendsto_finsetSum _ fun i _ => ?_
    have hpre : ∀ t : ℝ, μ ((φ t) ⁻¹' P.cells i) = μ (P.cells i) := fun t =>
      (φ.measurePreserving t).measure_preimage (P.measurable i).nullMeasurableSet
    simp only [hpre]
    refine Filter.Tendsto.const_mul _ ?_
    refine tendsto_finsetSum _ fun j _ => ?_
    have hc : Tendsto (fun t : ℝ => (μ ((φ t) ⁻¹' P.cells i ∩ P.cells j)).toReal) (𝓝 0)
        (𝓝 (μ (P.cells i ∩ P.cells j)).toReal) := by
      have h0 := tendsto_measureReal_inter_preimage φ hφ (P.measurable j) (P.measurable i)
      simp_rw [Set.inter_comm (P.cells j)] at h0
      exact h0
    exact (Real.continuous_negMulLog.tendsto _).comp (hc.div_const _)
  rw [hself] at main
  simpa only [MeasurePartition.pulledBack_cells] using main

end ErgodicTheory
