/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapDerivativeCocycle
import ErgodicTheory.Continuous.SuspensionFlowExponentFinal
import ErgodicTheory.Continuous.SuspensionStandardBorel

/-!
# The Arnold cat-map suspension flow carries the base's derivative cocycle

This module (resolving GitHub issue #30) builds the **suspension (special) flow over the genuine
Arnold cat map** `catTorus : 𝕋² → 𝕋²` under the constant unit roof `τ ≡ 1`, feeds it the base's
**own derivative cocycle** — the Fréchet-derivative cocycle `derivativeCocycle catLift` of the cat
map's universal-cover lift, which equals the constant hyperbolic generator `catℝ = !![2,1;1,1]`
(`derivativeCocycle_catLift`) — and reads off a **positive** flow Lyapunov exponent

`λ_flow = λ_base / ∫τ = log((3 + √5)/2) > 0`.

## Assembly

The cocycle generator `A := fun _ : 𝕋² => derivativeCocycle catLift 0` is constant in the base
point, so `cocycle A T n x = catℝ ⁿ` (`cocycle_const`, `derivativeCocycle_catLift`) and its discrete
growth rate is the *deterministic* Gelfand limit
`(1/n) log ‖catℝ ⁿ‖ → log((3 + √5)/2)` (`tendsto_catℝ_pow_log`), obtained from
`tendsto_log_opNorm_pow_log_spectralRadius` after identifying the spectral radius of `catℝ` with the
top eigenvalue `(3 + √5)/2` through the genuine ergodic base
(`catℝ_log_spectralRadius`, via `topExponent_constantCocycle_eq_log_spectralRadius` and the Grade-1
spectrum `catTorus_constCocycle_exponents`). For the unit roof, `∫τ = 1` (`catRoof_integral`) and
the roof Birkhoff average tends to `1` (`tendsto_catRoofSum`). Instantiating the fully unconditional
space-level special-flow headline
`ae_suspensionMeasure_hasFlowExponent_of_measurable`
(`ErgodicTheory.Continuous.SuspensionFlowExponentFinal`) at this data yields the flow exponent
`log((3 + √5)/2) / 1 = log((3 + √5)/2)`.

## Honest caveats

* `HasFlowExponent q L` is **existential over representatives**: for `μ̂`-a.e. orbit class `q`,
  *some* representative `(x, s)` realises the cover-cocycle growth rate `L`. The
  representative-free upgrade — the genuine `Quotient.lift` value `flowExponentAt q` and its
  cross-representative uniqueness across a *signed* orbit step — is **provided** in
  `ErgodicTheory/Examples/CatMapSuspensionFlowQuotient.lean`: `catSuspension_flowExponentAt_eq_log`,
  `catSuspension_flowExponentAt_eq_base_div_roof` (the descended `λ_flow = λ_base / ∫τ`), and
  `catSuspension_flowExponentAt_pos`. The base generator here is the constant cat matrix `catℝ`
  (`det = 1 ≠ 0`), which supplies exactly the global invertibility that makes that descent total.
* The tangent cocycle enters as the **Grade-2a universal-cover** reading of the derivative:
  `catLift` is the genuine ℝ²-linear lift of the cat map (`coverProj_comp_catLift`), and its
  Fréchet-derivative cocycle is the constant `catℝ`. The **Grade-2b** chart-native reading through
  `mfderiv` on the `AddCircle` product manifold remains open (Mathlib has no `mfderiv` API for
  `AddCircle` endomorphisms), as documented in `ErgodicTheory.Examples.CatMapDerivativeCocycle`.

## Main results

* `ErgodicTheory.CatMapToral.catSuspension_ae_hasFlowExponent` — for `μ̂`-a.e. orbit class `q`,
  `HasFlowExponent A catTorusEquiv … q (log((3 + √5)/2))`.
* `ErgodicTheory.CatMapToral.catSuspension_ae_hasFlowExponent_flowOrbit` — the flow-tied version:
  a.e. `q` lies on a genuine `suspensionFlow` orbit and carries the same exponent.
* `ErgodicTheory.CatMapToral.catSuspensionFlow_ownExponent_pos` — the positivity headline of issue
  #30: for a.e. `q`, there is `L` with `HasFlowExponent … q L ∧ 0 < L`.
* `ErgodicTheory.CatMapToral.catSuspension_flowExponent_eq_base_div_roof` — the
  `λ_flow = λ_base / ∫τ` reading: the flow exponent equals the base top exponent of `catℝ` divided
  by the mean roof `∫τ`.

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
`MeasureSpace UnitAddCircle` convention of `ErgodicTheory/Examples/CatMapToral.lean` so that the
ambient `volume : Measure T2` here is *the same* product Haar probability measure for which
`ergodic_catTorus` and the Grade-1 spectrum are stated. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## The constant unit roof over the cat-map base -/

/-- The constant unit roof `τ ≡ 1` over the cat-map base `𝕋²`. -/
def catRoof : T2 → ℝ := fun _ => (1 : ℝ)

/-- The unit roof is measurable. -/
theorem measurable_catRoof : Measurable catRoof := measurable_const

/-- The unit roof is bounded below by its lower bound `c = 1`. -/
theorem catRoof_ge_one : ∀ x : T2, (1 : ℝ) ≤ catRoof x := fun _ => le_refl 1

/-- The unit roof is bounded above by its upper bound `C = 1`. -/
theorem catRoof_le_one : ∀ x : T2, catRoof x ≤ (1 : ℝ) := fun _ => le_refl 1

/-- The mean roof over the Haar probability base is `∫τ = 1`. -/
theorem catRoof_integral : (∫ y, catRoof y ∂(volume : Measure T2)) = 1 := by
  simp [catRoof, integral_const]

/-- The mean roof is positive, `0 < ∫τ`. -/
theorem catRoof_integral_pos : 0 < ∫ y, catRoof y ∂(volume : Measure T2) := by
  rw [catRoof_integral]; exact zero_lt_one

/-! ## The deterministic growth rate of the constant cat-map derivative cocycle -/

/-- **The log-spectral-radius of `catℝ` is `log((3 + √5)/2)`.** The top Lyapunov exponent of the
constant cocycle `catℝ` over the genuine ergodic base equals both `log (spectralRadius ℂ catℂ)`
(`topExponent_constantCocycle_eq_log_spectralRadius`, Gelfand) and the Grade-1 spectral value
`log((3 + √5)/2)` (`catTorus_constCocycle_exponents`); comparing the two identifies the spectral
radius. -/
theorem catℝ_log_spectralRadius :
    Real.log (spectralRadius ℂ (catℝ.map (algebraMap ℝ ℂ))).toReal
      = Real.log ((3 + Real.sqrt 5) / 2) := by
  rw [← topExponent_constantCocycle_eq_log_spectralRadius ergodic_catTorus catℝ_det_ne_zero,
    ErgodicTheory.topExponent, catTorus_constCocycle_exponents.1]

/-- **The deterministic Gelfand growth limit of `catℝ`.** `(1/n) log ‖catℝ ⁿ‖ → log((3 + √5)/2)`.
This is Gelfand's formula (`tendsto_log_opNorm_pow_log_spectralRadius`) with the spectral radius
identified through `catℝ_log_spectralRadius`. -/
theorem tendsto_catℝ_pow_log :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖catℝ ^ n‖) atTop
      (𝓝 (Real.log ((3 + Real.sqrt 5) / 2))) := by
  have h := tendsto_log_opNorm_pow_log_spectralRadius (M := catℝ) catℝ_det_ne_zero
  rwa [catℝ_log_spectralRadius] at h

/-- **Base-growth datum for the special-flow headline.** For `volume`-a.e. base point `x`, the
discrete growth rate of the constant derivative cocycle `A ≡ derivativeCocycle catLift 0` under the
cat map is the deterministic limit `log((3 + √5)/2)`. Since the cocycle is constant in `x`
(`cocycle_const`) and equal to `catℝ ⁿ` (`derivativeCocycle_catLift`), this is
`tendsto_catℝ_pow_log` verbatim, promoted to an a.e. statement. -/
theorem tendsto_catCocycle_log :
    ∀ᵐ x ∂(volume : Measure T2),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖cocycle (fun _ : T2 => derivativeCocycle catLift 0)
            (⇑catTorusEquiv) n x‖) atTop
        (𝓝 (Real.log ((3 + Real.sqrt 5) / 2))) := by
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hcong : (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖cocycle (fun _ : T2 => derivativeCocycle catLift 0)
          (⇑catTorusEquiv) n x‖)
      = (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖catℝ ^ n‖) := by
    funext n
    rw [cocycle_const, derivativeCocycle_catLift]
  rw [hcong]
  exact tendsto_catℝ_pow_log

/-- **Roof Birkhoff datum for the special-flow headline.** For the unit roof, the roof Birkhoff
average `(1/n) τ⁽ⁿ⁾ x = (1/n) · n → 1 = ∫τ` (`roofSum_oneRoof`). -/
theorem tendsto_catRoofSum :
    ∀ᵐ x ∂(volume : Measure T2),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          roofSum catTorusEquiv measurable_catRoof (n : ℤ) x) atTop
        (𝓝 (∫ y, catRoof y ∂(volume : Measure T2))) := by
  simp only [catRoof_integral]
  refine Filter.Eventually.of_forall (fun x => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [roofSum_oneRoof catTorusEquiv measurable_catRoof rfl]
  push_cast
  rw [inv_mul_cancel₀ (by exact_mod_cast hn.ne')]

/-! ## The suspension-flow Lyapunov exponent of the cat map's derivative cocycle -/

/-- **The cat-map suspension flow realises the base's derivative-cocycle exponent.** For
`μ̂ = suspensionMeasure`-a.e. orbit class `q` of the suspension over the genuine Arnold cat map
`catTorus` under the unit roof, the flow Lyapunov exponent of the base's own derivative cocycle
`A ≡ derivativeCocycle catLift 0` is `λ_base / ∫τ = log((3 + √5)/2)`.

`HasFlowExponent` is existential over representatives (see the module docstring); this is the
Lyapunov analogue of Abramov's `h(flow) = h(base)/∫τ`. -/
theorem catSuspension_ae_hasFlowExponent :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      HasFlowExponent (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
        measurable_catRoof catRoof_ge_one one_pos q (Real.log ((3 + Real.sqrt 5) / 2)) := by
  have key := ae_suspensionMeasure_hasFlowExponent_of_measurable
    (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv measurable_catRoof
    measurable_const catRoof_ge_one one_pos catRoof_le_one
    tendsto_catCocycle_log tendsto_catRoofSum catRoof_integral_pos
  filter_upwards [key] with q hq
  rwa [catRoof_integral, div_one] at hq

/-- **The flow exponent along genuine suspension-flow orbits.** For `μ̂`-a.e. orbit class `q`, `q`
lies on the `suspensionFlow`-orbit of a base cross-section point and carries the flow exponent
`log((3 + √5)/2)` of the base's own derivative cocycle. -/
theorem catSuspension_ae_hasFlowExponent_flowOrbit :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      ∃ (x : T2) (s : ℝ),
        q = suspensionFlow catTorusEquiv measurable_catRoof
              measurePreserving_catTorusEquiv catRoof_ge_one one_pos s
              (suspensionSection catTorusEquiv measurable_catRoof x) ∧
          HasFlowExponent (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
            measurable_catRoof catRoof_ge_one one_pos q
            (Real.log ((3 + Real.sqrt 5) / 2)) := by
  have key := ae_suspensionMeasure_hasFlowExponent_flowOrbit_of_measurable
    (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv measurable_catRoof
    measurable_const measurePreserving_catTorusEquiv catRoof_ge_one one_pos catRoof_le_one
    tendsto_catCocycle_log tendsto_catRoofSum catRoof_integral_pos
  filter_upwards [key] with q hq
  obtain ⟨x, s, hqeq, hexp⟩ := hq
  refine ⟨x, s, hqeq, ?_⟩
  rwa [catRoof_integral, div_one] at hexp

/-- **Issue #30 headline: the cat-map suspension flow has a positive flow Lyapunov exponent carried
by the base's own derivative cocycle.** For `μ̂`-a.e. orbit class `q`, there is a positive `L` with
`HasFlowExponent A catTorusEquiv … q L`. Positivity is the hyperbolicity of the cat map:
`(3 + √5)/2 > 1`, so `L = log((3 + √5)/2) > 0`. -/
theorem catSuspensionFlow_ownExponent_pos :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      ∃ L : ℝ,
        HasFlowExponent (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
          measurable_catRoof catRoof_ge_one one_pos q L ∧ 0 < L := by
  filter_upwards [catSuspension_ae_hasFlowExponent] with q hq
  refine ⟨Real.log ((3 + Real.sqrt 5) / 2), hq, ?_⟩
  apply Real.log_pos
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  linarith

/-- **The `λ_flow = λ_base / ∫τ` reading.** The flow Lyapunov exponent of the base's own derivative
cocycle equals the base top Lyapunov exponent of `catℝ` (over the genuine ergodic cat map) divided
by the mean roof `∫τ`. Since `∫τ = 1` this is the same numerical value `log((3 + √5)/2)`, exposed
here in its Abramov-style quotient form. -/
theorem catSuspension_flowExponent_eq_base_div_roof :
    ∀ᵐ q ∂suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2),
      HasFlowExponent (fun _ : T2 => derivativeCocycle catLift 0) catTorusEquiv
        measurable_catRoof catRoof_ge_one one_pos q
        (ErgodicTheory.topExponent ergodic_catTorus
            (ErgodicTheory.const_det_ne_zero catℝ_det_ne_zero)
            (ErgodicTheory.const_measurable catℝ) (ErgodicTheory.const_integrableLogNorm catℝ)
            (ErgodicTheory.const_integrableLogNorm_inv catℝ)
          / ∫ y, catRoof y ∂(volume : Measure T2)) := by
  have hbase : ErgodicTheory.topExponent ergodic_catTorus
        (ErgodicTheory.const_det_ne_zero catℝ_det_ne_zero) (ErgodicTheory.const_measurable catℝ)
        (ErgodicTheory.const_integrableLogNorm catℝ)
        (ErgodicTheory.const_integrableLogNorm_inv catℝ)
      = Real.log ((3 + Real.sqrt 5) / 2) := by
    rw [ErgodicTheory.topExponent, catTorus_constCocycle_exponents.1]
  filter_upwards [catSuspension_ae_hasFlowExponent] with q hq
  rw [hbase, catRoof_integral, div_one]
  exact hq

end ErgodicTheory.CatMapToral
