/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionCoboundary
import ErgodicTheory.Examples.CatMapSuspensionFlow
import ErgodicTheory.Examples.CatMapClosing

/-!
# A non-vacuity witness for the flow-Livšic obstruction: the cat-map suspension flow

This module (issue #36) records a **non-vacuity witness** for the periodic-orbit obstruction of the
flow-Livšic theory (`ErgodicTheory.Continuous.SuspensionCoboundary`): the constant observable `1` is
*not* a flow coboundary of the suspension (special) flow over the genuine Arnold cat map
`catTorus : 𝕋² → 𝕋²` under the unit roof `τ ≡ 1`.

The witness is the fixed point `0` of the cat map (`catTorus_zero_fixed`): its base period is `1`,
so the induced base observable summed around it is the single lap integral
`∫₀^{τ 0} 1 ds = catRoof 0 = 1 ≠ 0`. By the tier-1 packaged obstruction
`ErgodicTheory.not_isFlowCoboundary_suspensionFlow_of_inducedPeriodicSum_ne_zero` this defeats every
transfer function, so the obstruction of the flow-Livšic layer is genuinely non-vacuous.

## Main results

* `ErgodicTheory.CatMapToral.const_one_not_isFlowCoboundary_catSuspension` — the constant observable
  `1` is not a flow coboundary of the cat-map suspension flow.
-/

open Function MeasureTheory

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `ErgodicTheory/Examples/CatMapToral.lean` so that the
ambient `volume : Measure T2` here is *the same* product Haar probability measure for which
`measurePreserving_catTorusEquiv` is stated. (Uniquely named to avoid colliding with the identical
local instances of the sibling cat-map modules.) -/
noncomputable local instance instMeasureSpaceUnitAddCircleFlowCob :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarUnitAddCircleFlowCob :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityUnitAddCircleFlowCob :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- **Non-vacuity of the flow-Livšic obstruction.** The constant observable `1` is *not* a flow
coboundary of the suspension (special) flow over the Arnold cat map under the unit roof. Its induced
base observable summed around the period-`1` fixed point `0` of `catTorus` is the single lap
integral `∫₀^{catRoof 0} 1 ds = catRoof 0 = 1 ≠ 0`, so by the tier-1 packaged obstruction
`not_isFlowCoboundary_suspensionFlow_of_inducedPeriodicSum_ne_zero` no transfer function can cobound
it. This exhibits a concrete `F` and a genuine nonzero closed-orbit integral, certifying that the
obstruction of `ErgodicTheory.Continuous.SuspensionCoboundary` is non-vacuous. -/
theorem const_one_not_isFlowCoboundary_catSuspension :
    ¬ IsFlowCoboundary (⇑(suspensionFlow catTorusEquiv measurable_catRoof
        measurePreserving_catTorusEquiv catRoof_ge_one one_pos)) (fun _ => (1 : ℝ)) := by
  refine not_isFlowCoboundary_suspensionFlow_of_inducedPeriodicSum_ne_zero
    catTorusEquiv measurable_catRoof measurePreserving_catTorusEquiv catRoof_ge_one one_pos
    (n := 1) (p := 0) ?_ (fun _ => (1 : ℝ)) ?_
  · -- `0` is a period-`1` point of the cat map.
    rw [Function.iterate_one, catTorusEquiv_apply]
    exact catTorus_zero_fixed
  · -- The period-`1` induced sum is the single lap integral `∫₀^{catRoof 0} 1 = catRoof 0 = 1 ≠ 0`.
    have hone : birkhoffSum (⇑catTorusEquiv)
        (inducedBaseCocycle catTorusEquiv measurable_catRoof (fun _ => (1 : ℝ))) 1 0 = 1 := by
      rw [birkhoffSum, Finset.sum_range_one, Function.iterate_zero_apply, inducedBaseCocycle]
      simp only [catRoof, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    rw [hone]
    norm_num

end ErgodicTheory.CatMapToral
