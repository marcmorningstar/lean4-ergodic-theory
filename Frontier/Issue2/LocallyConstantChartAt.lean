/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Locally constant charts

This module introduces the honest chart-regularity typeclass `LocallyConstantChartAt H M`, asserting
that the preferred-chart map `chartAt H · : M → OpenPartialHomeomorph M H` is **locally constant**:
near every point `a`, `chartAt H x = chartAt H a`. This is the precise regularity hypothesis that
rules out the pathological unconstrained `chartAt` of a generic `ChartedSpace` and makes the
moving-source-index tangent coordinate change `x ↦ tangentCoordChange I x c x` continuous — the
single residual analytic obligation behind the manifold-derivative measurability chain (issue #9).

The class is **not** vacuous: it holds for the model space `H` over itself (the atlas is a single
identity chart, so `chartAt` is globally constant), recorded as `instLocallyConstantChartAtSelf`.
More generally it holds for any single-chart / clopen-partition atlas. It does **not** hold for an
arbitrary `ChartedSpace`.
-/

open Topology

namespace Frontier.Issue2

/-- A charted space has **locally constant charts** when `chartAt H ·` is locally constant: near
every point `a`, the preferred chart `chartAt H x` agrees with `chartAt H a`. This is the honest
regularity hypothesis ruling out the pathological unconstrained `chartAt`; it makes the
moving-source-index coordinate change continuous. It holds for the model space and for single-chart
or clopen-partition atlases, but **not** for an arbitrary `ChartedSpace`. -/
class LocallyConstantChartAt (H : Type*) (M : Type*)
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] : Prop where
  locallyConstant_chartAt : ∀ a : M, ∀ᶠ x in nhds a, chartAt H x = chartAt H a

/-- The chart map is eventually constant near every point, under `LocallyConstantChartAt`. -/
theorem eventually_chartAt_eq {H : Type*} {M : Type*}
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [LocallyConstantChartAt H M] (a : M) :
    ∀ᶠ x in nhds a, chartAt H x = chartAt H a :=
  LocallyConstantChartAt.locallyConstant_chartAt a

/-- **Non-vacuity.** The model space `H` over itself has locally constant charts: its atlas is the
single identity chart, so `chartAt H x = OpenPartialHomeomorph.refl H` for every `x`
(`chartAt_self_eq`); the chart map is globally constant, a fortiori locally constant. -/
instance instLocallyConstantChartAtSelf (H : Type*) [TopologicalSpace H] :
    LocallyConstantChartAt H H where
  locallyConstant_chartAt a :=
    Filter.Eventually.of_forall (fun x => by rw [chartAt_self_eq, chartAt_self_eq])

end Frontier.Issue2
