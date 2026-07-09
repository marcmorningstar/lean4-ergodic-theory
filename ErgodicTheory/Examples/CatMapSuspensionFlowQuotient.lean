/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlowExponentQuotient
import ErgodicTheory.Examples.CatMapSuspensionFlow

/-!
# The cat-map suspension flow exponent as a genuine `SuspensionSpace → ℝ` function

`ErgodicTheory.Examples.CatMapSuspensionFlow` (resolving GitHub issue #30) read off the positive
flow Lyapunov exponent `log((3 + √5)/2)` of the Arnold cat map's suspension flow, but only in the
**existential** `HasFlowExponent` phrasing: for `μ̂`-a.e. orbit class `q`, *some* representative
`(x, s)` realises the cover-cocycle growth rate `L`. That module's docstring explicitly flags the
cross-representative uniqueness (and hence the actual representative-free quotient value) as
**deferred**.

This module (issue #37, item 3) discharges that caveat. Using the descended function
`ErgodicTheory.flowExponentAt` from `ErgodicTheory.Continuous.SuspensionFlowExponentQuotient` — the
`Quotient.lift` of the representative-level growth rate, made total by global base-cocycle
invertibility — it upgrades every cat-suspension headline from "some representative realises `L`" to
the genuine equality `flowExponentAt q = L` of the descended flow exponent. The base generator here
is the constant hyperbolic matrix `catℝ = !![2,1;1,1]` (the derivative cocycle
`derivativeCocycle catLift 0`, `derivativeCocycle_catLift`), whose determinant is `1 ≠ 0`
(`derivativeCocycle_catLift_det_ne_zero`), so the descent is total and the caveat vanishes.

## Main results

* `ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_eq_log` — for `μ̂`-a.e. orbit class `q`,
  `flowExponentAt … q = log((3 + √5)/2)`, the representative-free upgrade of
  `catSuspension_ae_hasFlowExponent`.
* `ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_eq_base_div_roof` — the Abramov-style
  quotient reading `flowExponentAt … q = λ_base / ∫τ`, upgrading
  `catSuspension_flowExponent_eq_base_div_roof`.
* `ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_pos` — the positivity headline of issue
  #30 in descended form: for `μ̂`-a.e. `q`, `0 < flowExponentAt … q`.

## References

* L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875 (the
  entropy analogue `h(flow) = h(base)/∫τ`).
* I. P. Cornfeld, S. V. Fomin, Ya. G. Sinai, *Ergodic Theory*, Springer 1982, Ch. 11
  (special/suspension flows; Ambrose–Kakutani).
* L. Barreira, *Lyapunov Exponents*, Birkhäuser 2017, Ch. 3 (Lyapunov exponents under time
  rescaling).
* V. I. Arnold, A. Avez, *Ergodic Problems of Classical Mechanics*, Benjamin 1968 (the cat map).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator ENNReal

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `CatMapSuspensionFlow.lean` so that the ambient
`volume : Measure T2` here is *the same* product Haar probability measure for which the
cat-suspension headlines are stated. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- **The determinant hypothesis for the descended flow exponent.** The constant base generator
`A ≡ derivativeCocycle catLift 0` equals the cat matrix `catℝ` (`derivativeCocycle_catLift`), whose
determinant is `1 ≠ 0`; hence `A` is everywhere invertible. This is exactly the global
invertibility that makes the `Quotient.lift` `flowExponentAt` **total** on every orbit class. -/
theorem catSuspension_det_ne_zero :
    ∀ x : T2, ((fun _ : T2 => derivativeCocycle catLift 0) x).det ≠ 0 :=
  fun _ => derivativeCocycle_catLift_det_ne_zero

/-- **Representative-free cat-suspension flow exponent.** For `μ̂ = suspensionMeasure`-a.e. orbit
class `q` of the suspension over the genuine Arnold cat map under the unit roof, the *descended*
flow Lyapunov exponent of the base's own derivative cocycle equals `log((3 + √5)/2)`.

This is the representative-free upgrade of `catSuspension_ae_hasFlowExponent`: it replaces the
existential "*some* representative realises `L`" with the value of the genuine `Quotient.lift`
`flowExponentAt`. -/
theorem catSuspension_flowExponentAt_eq_log :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      flowExponentAt (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
        measurable_catRoof catSuspension_det_ne_zero catRoof_ge_one one_pos q
        = Real.log ((3 + Real.sqrt 5) / 2) := by
  filter_upwards [catSuspension_ae_hasFlowExponent] with q hq
  exact flowExponentAt_eq_of_hasFlowExponent (fun _ : T2 => derivativeCocycle catLift 0)
    catTorusEquiv measurable_catRoof catSuspension_det_ne_zero catRoof_ge_one one_pos hq

/-- **The `λ_flow = λ_base / ∫τ` reading, descended.** The genuine (representative-free) flow
Lyapunov exponent of the base's own derivative cocycle equals the base top Lyapunov exponent of
`catℝ` (over the genuine ergodic cat map) divided by the mean roof `∫τ`. Since `∫τ = 1` this is the
same numerical value `log((3 + √5)/2)`, exposed here in its Abramov-style quotient form and now as
an honest equality of the descended function rather than an existential over representatives. -/
theorem catSuspension_flowExponentAt_eq_base_div_roof :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      flowExponentAt (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
          measurable_catRoof catSuspension_det_ne_zero catRoof_ge_one one_pos q
        = ErgodicTheory.topExponent ergodic_catTorus
            (ErgodicTheory.const_det_ne_zero catℝ_det_ne_zero)
            (ErgodicTheory.const_measurable catℝ) (ErgodicTheory.const_integrableLogNorm catℝ)
            (ErgodicTheory.const_integrableLogNorm_inv catℝ)
          / ∫ y, catRoof y ∂(volume : Measure T2) := by
  have hbase : ErgodicTheory.topExponent ergodic_catTorus
        (ErgodicTheory.const_det_ne_zero catℝ_det_ne_zero) (ErgodicTheory.const_measurable catℝ)
        (ErgodicTheory.const_integrableLogNorm catℝ)
        (ErgodicTheory.const_integrableLogNorm_inv catℝ)
      = Real.log ((3 + Real.sqrt 5) / 2) := by
    rw [ErgodicTheory.topExponent, catTorus_constCocycle_exponents.1]
  filter_upwards [catSuspension_flowExponentAt_eq_log] with q hq
  rw [hbase, catRoof_integral, div_one]
  exact hq

/-- **Issue #30 positivity headline, descended.** For `μ̂`-a.e. orbit class `q` the genuine
(representative-free) flow Lyapunov exponent is *strictly positive*. Positivity is the hyperbolicity
of the cat map: `(3 + √5)/2 > 1`, so `flowExponentAt … q = log((3 + √5)/2) > 0`. -/
theorem catSuspension_flowExponentAt_pos :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      0 < flowExponentAt (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
        measurable_catRoof catSuspension_det_ne_zero catRoof_ge_one one_pos q := by
  filter_upwards [catSuspension_flowExponentAt_eq_log] with q hq
  rw [hq]
  apply Real.log_pos
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  linarith

end ErgodicTheory.CatMapToral
