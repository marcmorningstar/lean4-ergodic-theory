/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Polish

/-!
# Polishness of the space of probability measures on a compact metric space

This module fills three small gaps in Mathlib's descriptive-set-theory / weak-convergence API that
are consumed by the repo's DST layer (`ErgodicTheory.MeasureTheory`):

* `isCompletelyMetrizableSpace_of_compactSpace` — a compact metrizable space is completely
  metrizable (a compatible metric makes it complete, since a compact uniform space is complete).
  Mathlib has no `[CompactSpace] [MetrizableSpace] → IsCompletelyMetrizableSpace` route.
* `polishSpace_probabilityMeasure` — on a compact metric (Borel) space `X`, the space
  `ProbabilityMeasure X` of Borel probability measures, with the topology of convergence in
  distribution, is Polish. This is the Prokhorov/Lévy–Prokhorov package (`CompactSpace`,
  `MetrizableSpace`, `SecondCountableTopology`) upgraded through the previous lemma.
* `polishSpace_prod` — a binary product of Polish spaces is Polish. Mathlib has
  `IsCompletelyMetrizableSpace.prod` and `Prod.secondCountableTopology` but no catch-all
  `PolishSpace (A × B)` assembling them.

All three are natural **upstream candidates** for Mathlib.

Reference: A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156, §17.E (the space `P(X)` of
Borel probability measures on a compact metrizable space is itself compact metrizable, hence
Polish).
-/

open MeasureTheory TopologicalSpace

namespace ErgodicTheory.MeasureTheory

/-- A compact metrizable space is completely metrizable: pick a compatible metric
(`TopologicalSpace.metrizableSpaceMetric`), and a compact uniform space is complete
(`complete_of_compact`), so the metric is complete.

Kept as a `theorem` (not a global instance) to avoid a typeclass loop with the
`IsCompletelyMetrizableSpace → MetrizableSpace` instance; use it as `haveI := ...` where needed. -/
theorem isCompletelyMetrizableSpace_of_compactSpace {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [MetrizableSpace Y] : IsCompletelyMetrizableSpace Y := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  infer_instance

/-- **The space of probability measures on a compact metric space is Polish** (Kechris §17.E).

On a compact metric Borel space `X`, `ProbabilityMeasure X` (topology of convergence in
distribution) is compact (Prokhorov) and metrizable (Lévy–Prokhorov) with second-countable
topology; `isCompletelyMetrizableSpace_of_compactSpace` upgrades this to Polishness. -/
instance polishSpace_probabilityMeasure {X : Type*} [MeasurableSpace X] [MetricSpace X]
    [BorelSpace X] [CompactSpace X] : PolishSpace (ProbabilityMeasure X) := by
  haveI : IsCompletelyMetrizableSpace (ProbabilityMeasure X) :=
    isCompletelyMetrizableSpace_of_compactSpace
  infer_instance

/-- **A binary product of Polish spaces is Polish.** Assembles
`IsCompletelyMetrizableSpace.prod` with `Prod.secondCountableTopology`. -/
instance polishSpace_prod {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [PolishSpace A] [PolishSpace B] : PolishSpace (A × B) := inferInstance

/-! ### Sanity certificates -/

open scoped unitInterval

example : IsCompletelyMetrizableSpace unitInterval := isCompletelyMetrizableSpace_of_compactSpace

example : PolishSpace (ProbabilityMeasure unitInterval) := inferInstance

example : PolishSpace (ℝ × ℝ) := inferInstance

example :
    PolishSpace (ProbabilityMeasure unitInterval × ProbabilityMeasure unitInterval) := inferInstance

example :
    PolishSpace (ProbabilityMeasure unitInterval × ProbabilityMeasure unitInterval × ℝ) :=
  inferInstance

end ErgodicTheory.MeasureTheory
