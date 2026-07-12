/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.QuotientFlowCocycle
import ErgodicTheory.Examples.CatMapSuspensionFlowQuotient
import ErgodicTheory.Examples.CatMapDerivativeCocycle

/-!
# The Arnold cat map's genuine quotient flow cocycle and its Lyapunov exponent

This module instantiates `ErgodicTheory.quotientFlowCocycle`
(`ErgodicTheory.Continuous.QuotientFlowCocycle`) for the **Arnold cat map**: over the genuine
ergodic toral automorphism `catTorus` under the constant unit roof `catRoof ≡ 1`, with base
generator the cat map's own derivative cocycle `derivativeCocycle catLift` (the constant hyperbolic
matrix `catℝ`, `derivativeCocycle_catLift`), it produces a genuine `FlowCocycle` on the suspension
whose growth rate is the flow Lyapunov exponent `log((3 + √5)/2)` for `μ̂`-a.e. orbit class.

This is the measurable-trivialization route in action: `catRoof = fun _ => 1` is literally the unit
roof of the general module, so `catQuotientFlowCocycle` is the general `quotientFlowCocycle`
specialised to the cat map, and the descended-exponent chain of
`ErgodicTheory.Examples.CatMapSuspensionFlowQuotient` (`catSuspension_flowExponentAt_eq_log`)
transports through `flowExponentAt_quotientFlowCocycle` to the flow-cocycle growth rate.

## Main definitions

* `ErgodicTheory.CatMapToral.catQuotientFlowCocycle`: the cat map's genuine quotient `FlowCocycle`.

## Main results

* `ErgodicTheory.CatMapToral.catQuotientFlowCocycle_exponent`: for `μ̂`-a.e. orbit class `q`, the
  growth rate of `catQuotientFlowCocycle` converges to `log((3 + √5)/2)`.

## References

* V. I. Arnold, A. Avez, *Ergodic Problems of Classical Mechanics*, Benjamin 1968 (the cat map).
* I. P. Cornfeld, S. V. Fomin, Ya. G. Sinai, *Ergodic Theory*, Springer 1982, Ch. 11
  (special/suspension flows).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `CatMapSuspensionFlowQuotient.lean` so the ambient
`volume : Measure T2` is *the same* product Haar probability measure. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catQFC : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasure_catQFC :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasure_catQFC :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- **The Arnold cat map's genuine quotient flow cocycle.** The general `quotientFlowCocycle`
(`ErgodicTheory.Continuous.QuotientFlowCocycle`) specialised to the cat map: base map the genuine
ergodic toral automorphism `catTorusEquiv` under the unit roof `catRoof ≡ 1`, base generator the cat
map's own derivative cocycle `derivativeCocycle catLift` (the constant hyperbolic matrix `catℝ`,
everywhere invertible by `catSuspension_det_ne_zero`, measurable as a constant). Since `catRoof =
fun _ => 1` is the unit roof, this is a genuine `FlowCocycle` on the cat suspension quotient. -/
noncomputable def catQuotientFlowCocycle :
    FlowCocycle (suspensionFlow catTorusEquiv measurable_catRoof
      measurePreserving_catTorusEquiv catRoof_ge_one one_pos) 2 :=
  quotientFlowCocycle (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
    catSuspension_det_ne_zero measurable_const measurePreserving_catTorusEquiv

/-- **The cat map's quotient flow-cocycle Lyapunov exponent.** For `μ̂ = suspensionMeasure`-a.e.
orbit class `q`, the growth rate of the genuine quotient flow cocycle `catQuotientFlowCocycle`
converges to the flow Lyapunov exponent `log((3 + √5)/2)` — the log of the top eigenvalue of the cat
matrix. Chains the descended cat-suspension exponent `catSuspension_ae_hasFlowExponent` through the
exponent-transport lemma `flowExponentAt_quotientFlowCocycle`. -/
theorem catQuotientFlowCocycle_exponent :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      Tendsto (fun t : ℝ => Real.log ‖catQuotientFlowCocycle t q‖ / t) atTop
        (𝓝 (Real.log ((3 + Real.sqrt 5) / 2))) := by
  filter_upwards [catSuspension_ae_hasFlowExponent] with q hq
  have hL := flowExponentAt_quotientFlowCocycle (fun _ : T2 => derivativeCocycle catLift 0)
    catTorusEquiv catSuspension_det_ne_zero measurable_const measurePreserving_catTorusEquiv hq
  have hval : flowExponentAt (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
      (measurable_unitRoof (X := T2)) catSuspension_det_ne_zero (fun _ => le_refl (1 : ℝ)) one_pos q
      = Real.log ((3 + Real.sqrt 5) / 2) :=
    flowExponentAt_eq_of_hasFlowExponent _ _ _ _ _ _ hq
  rw [hval] at hL
  exact hL

end ErgodicTheory.CatMapToral
