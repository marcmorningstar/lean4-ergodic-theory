/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.Monotone
import Oseledets.Multifractal.Degeneracy
import Oseledets.Multifractal.Spectrum
import Oseledets.Entropy.Join
import Oseledets.Continuous.Flow

/-!
# Coarse-grained multifractal analysis: the measure / flow layer

This file specializes the abstract, measure-free multifractal core
(`Oseledets.Multifractal.Defs` and its downstream files) to a genuine **invariant probability
measure** `μ` together with a **finite measurable partition** `P : MeasurePartition μ ι`. Taking
the weight family `p i := (μ (P.cells i)).toReal` turns the abstract quantities into the
multifractal observables of the measure `μ` at the partition scale: the partition function
`Z_q`, the mass exponent `τ(q)`, the Rényi (generalized) dimension `D_q`, and the singularity
spectrum `f(α)` of `μ`.

The point of this layer is that the abstract hypotheses (`0 ≤ p i`, `∑ i, p i = 1`,
`0 < ε < 1`) are now *discharged from the measure*: nonnegativity is `ENNReal.toReal_nonneg`, the
probability normalization `∑ i, p i = 1` is the bridge lemma
`MeasurePartition.sum_toReal_measure_eq_one`, and at least one positive weight follows from the
total mass being `1` (`exists_pos_toReal_measure_cell`). The abstract headlines then transfer
verbatim.

Because the API consumes *any* invariant probability measure, it applies directly to the
invariant measure of a measure-preserving flow: a `MeasurePreservingFlow μ` is, by construction,
a flow whose `μ` it preserves, so `renyiDimMeasure μ P ε q` is the multifractal Rényi dimension
of that flow's invariant measure. The thin connector `renyiDimFlow` records this for flows
explicitly.

## Main definitions

* `Oseledets.Multifractal.partitionFunctionMeasure`: the partition function `Z_q` of `μ`.
* `Oseledets.Multifractal.massExponentMeasure`: the mass exponent `τ(q)` of `μ`.
* `Oseledets.Multifractal.renyiDimMeasure`: the Rényi (generalized) dimension `D_q` of `μ`.
* `Oseledets.Multifractal.singularitySpectrumMeasure`: the singularity spectrum `f(α)` of `μ`.
* `Oseledets.Multifractal.renyiDimFlow`: the Rényi dimension of the invariant measure of a flow.

## Main results

* `Oseledets.Multifractal.exists_pos_toReal_measure_cell`: some cell has positive measure (the
  abstract `∃ i, 0 < p i` guard, discharged from `∑ p i = 1`).
* `Oseledets.Multifractal.renyiDimMeasure_antitone`: `q ↦ D_q` is non-increasing.
* `Oseledets.Multifractal.renyiDimMeasure_one_eq`: the **information dimension** `D_1` equals
  `- H(P) / log ε`, the Shannon entropy of the partition divided by `-log ε`.
* `Oseledets.Multifractal.renyiDimMeasure_equalMeasure`: the uniform-partition (monofractal)
  degeneracy `D_q = log N / (-log ε)`, for every `q`.
* `Oseledets.Multifractal.renyiDimFlow_antitone`: the flow-level transfer of antitonicity.
-/

open Real MeasureTheory

namespace Oseledets.Multifractal

open Oseledets.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- The generalized **partition function** `Z_q = ∑_{i : μ(cellᵢ) > 0} (μ(cellᵢ))^q` of a measure
`μ` with respect to a finite measurable partition `P`. This is the abstract
`partitionFunction` evaluated on the weight family `p i = (μ (P.cells i)).toReal`. -/
noncomputable def partitionFunctionMeasure (μ : Measure α) (P : MeasurePartition μ ι) (q : ℝ) :
    ℝ :=
  partitionFunction (fun i => (μ (P.cells i)).toReal) q

/-- The **mass exponent** `τ(q) = log Z_q / log ε` of a measure `μ` at partition scale `ε`,
i.e. the abstract `massExponent` on the cell-measure weight family. -/
noncomputable def massExponentMeasure (μ : Measure α) (P : MeasurePartition μ ι) (ε q : ℝ) : ℝ :=
  massExponent (fun i => (μ (P.cells i)).toReal) ε q

/-- The **Rényi (generalized) dimension** `D_q` of a measure `μ` at partition scale `ε`, i.e. the
abstract `renyiDim` on the cell-measure weight family. At `q = 1` it is the information dimension
`(∑ i, μ(cellᵢ) log μ(cellᵢ)) / log ε`. -/
noncomputable def renyiDimMeasure (μ : Measure α) (P : MeasurePartition μ ι) (ε q : ℝ) : ℝ :=
  renyiDim (fun i => (μ (P.cells i)).toReal) ε q

/-- The **singularity spectrum** `f(α) = ⨅ q, q α - τ(q)` of a measure `μ` at partition scale
`ε`, i.e. the abstract `singularitySpectrum` (Legendre transform of `τ`) on the cell-measure
weight family. -/
noncomputable def singularitySpectrumMeasure (μ : Measure α) (P : MeasurePartition μ ι)
    (ε α' : ℝ) : ℝ :=
  singularitySpectrum (fun i => (μ (P.cells i)).toReal) ε α'

/-- For a probability measure, **at least one cell of a partition has positive measure**. This is
the abstract `∃ i, 0 < p i` guard discharged from the measure: the cell measures are nonnegative
and sum to `1`, so they cannot all vanish. -/
lemma exists_pos_toReal_measure_cell {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) : ∃ i, 0 < (μ (P.cells i)).toReal := by
  by_contra h
  push Not at h
  have hzero : ∀ i ∈ (Finset.univ : Finset ι), (μ (P.cells i)).toReal = 0 :=
    fun i _ => le_antisymm (h i) ENNReal.toReal_nonneg
  have hsum := P.sum_toReal_measure_eq_one
  rw [Finset.sum_eq_zero hzero] at hsum
  exact zero_ne_one hsum

/-- **Antitonicity of the Rényi dimension of a probability measure.** For a partition `P` of a
probability space and a scale `0 < ε < 1`, the Rényi (generalized) dimension `q ↦ D_q` of `μ` is
non-increasing in `q`. This is the abstract `renyiDim_antitone`, with the hypotheses discharged
from the measure: nonnegativity is `ENNReal.toReal_nonneg`, positivity of some cell is
`exists_pos_toReal_measure_cell`, and the probability normalization is
`MeasurePartition.sum_toReal_measure_eq_one`. -/
theorem renyiDimMeasure_antitone {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Antitone (fun q => renyiDimMeasure μ P ε q) :=
  renyiDim_antitone (fun _ => ENNReal.toReal_nonneg) (exists_pos_toReal_measure_cell P)
    P.sum_toReal_measure_eq_one hε0 hε1

/-- **Information dimension = Shannon entropy / (−log ε).** At `q = 1` the Rényi dimension of a
probability measure `μ` is `D_1 = - H(P) / log ε`, where `H(P) = entropy μ P.cells` is the
Shannon entropy of the partition. Indeed the `q = 1` numerator is
`∑ i, μ(cellᵢ) log μ(cellᵢ) = - ∑ i, negMulLog (μ(cellᵢ)) = - H(P)`. -/
theorem renyiDimMeasure_one_eq {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) (ε : ℝ) :
    renyiDimMeasure μ P ε 1 = - Oseledets.Entropy.entropy μ P.cells / Real.log ε := by
  rw [renyiDimMeasure, renyiDim, if_pos rfl]
  congr 1
  rw [Oseledets.Entropy.entropy_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.negMulLog]
  ring

/-- **Monofractal (uniform-partition) degeneracy at the measure level.** If every cell of the
partition `P` carries the same measure `N⁻¹` (with `N = Fintype.card ι`), then for `0 < ε < 1`
the Rényi dimension of `μ` is `q`-independent: `D_q = log N / (-log ε)` for every `q`, the
box-counting dimension `log N / log (1/ε)`. This is the abstract `renyiDim_equalMeasure`. -/
theorem renyiDimMeasure_equalMeasure {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) [Nonempty ι]
    (huniform : ∀ i, (μ (P.cells i)).toReal = (Fintype.card ι : ℝ)⁻¹)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (q : ℝ) :
    renyiDimMeasure μ P ε q = Real.log (Fintype.card ι) / (- Real.log ε) :=
  renyiDim_equalMeasure huniform hε0 hε1 q

/-! ### Flow connector

A `MeasurePreservingFlow μ` preserves its measure `μ` by construction, so `μ` is the flow's
invariant probability measure. The multifractal API consumes any such `μ`, so the multifractal
Rényi dimension of a flow's invariant measure is just `renyiDimMeasure μ P ε q`. The following
thin wrapper records this for flows explicitly; the flow argument documents (and is enforced by
the type) that `μ` is flow-invariant. -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The multifractal **Rényi (generalized) dimension of the invariant measure** `μ` of a
measure-preserving flow, at partition scale `ε`. The flow `φ` is taken as an explicit (unused)
argument to document, via the type `MeasurePreservingFlow μ`, that `μ` is flow-invariant; the
value is the partition Rényi dimension `renyiDimMeasure μ P ε q`. -/
noncomputable def renyiDimFlow (_φ : Oseledets.MeasurePreservingFlow μ)
    (P : MeasurePartition μ ι) (ε q : ℝ) : ℝ :=
  renyiDimMeasure μ P ε q

/-- **Antitonicity of the Rényi dimension of a flow's invariant measure.** Immediate from the
measure-level transfer `renyiDimMeasure_antitone`, since `renyiDimFlow` unfolds to
`renyiDimMeasure`. -/
theorem renyiDimFlow_antitone (φ : Oseledets.MeasurePreservingFlow μ) [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Antitone (fun q => renyiDimFlow φ P ε q) :=
  renyiDimMeasure_antitone P hε0 hε1

end Oseledets.Multifractal
