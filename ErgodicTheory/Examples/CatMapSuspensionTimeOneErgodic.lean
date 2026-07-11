/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapEigenfunction
import ErgodicTheory.Continuous.SuspensionTimeOneErgodic
import Mathlib.Data.Real.Sqrt

/-!
# Ergodicity of the time-`1` map of the constant-irrational-roof cat-map suspension flow

This module is **GitHub issue #47's dynamical payoff**: the time-`1` map of the constant-roof
suspension flow over the **genuine Arnold cat map** `catTorus : 𝕋² → 𝕋²` is **ergodic**, provided
the roof height `r` is a positive **irrational**.

It is the cat-map analogue of the Bernoulli-shift headline
`ErgodicTheory.Multifractal.ergodic_suspensionFlow_timeOne_const_irrational`, discharging the same
abstract base-generic theorem `ErgodicTheory.ergodic_suspensionFlowMap_one_const_roof` with:

* **base ergodicity** — `ergodic_catTorus` (the Fourier/character keystone for the hyperbolic toral
  automorphism), bridged to `⇑catTorusEquiv` through `catTorusEquiv_apply`;
* **spectral rigidity** — the cat map has *no nontrivial unimodular eigenfunctions*
  (`catTorus_eigenfunction_ae_zero`, issue #47), which supplies `hspec` directly.

The transform window in the fibre-Fourier proof is the invariance period `1`, not the roof `r`
(Cornfeld–Fomin–Sinai, Ch. 11): the irrational roof advances the fibre by `r`, so the fibre Fourier
coefficients pick up the unimodular twist `e^{2πi n r} ≠ 1`, which base ergodicity + spectral
rigidity annihilate.

## Main results

* `ergodic_catSuspension_timeOne_const_irrational` — the headline, against the raw
  `suspensionFlowMap`.
* `ergodic_catSuspension_packaged_timeOne_const_irrational` — the same against the packaged
  `MeasurePreservingFlow` `suspensionFlow`, applied at time `1`.
* `ergodic_catSuspension_timeOne_sqrtTwo` — the concrete non-vacuity witness `r := √2`.
-/

open MeasureTheory

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `ErgodicTheory/Examples/CatMapToral.lean` so that the
ambient `volume : Measure T2` here is *the same* product Haar probability measure for which
`ergodic_catTorus` and the eigenfunction rigidity are stated. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catSuspT1 :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catSuspT1 :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catSuspT1 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- **The time-`1` map of the constant-irrational-roof cat-map suspension flow is ergodic**
(GitHub issue #47). For the hyperbolic toral automorphism `catTorusEquiv` with Haar `volume` on
`𝕋²`, and any positive **irrational** roof height `r`, the time-`1` map
`suspensionFlowMap catTorusEquiv (τ ≡ r) 1` is ergodic for the invariant suspension probability
measure.

The abstract base-generic theorem `ergodic_suspensionFlowMap_one_const_roof` is discharged by base
ergodicity (`ergodic_catTorus`) and the eigenfunction rigidity `catTorus_eigenfunction_ae_zero`. -/
theorem ergodic_catSuspension_timeOne_const_irrational {r : ℝ} (hr0 : 0 < r) (hr : Irrational r) :
    Ergodic (suspensionFlowMap catTorusEquiv (measurable_const : Measurable fun _ : T2 => r) 1)
      (suspensionMeasure catTorusEquiv (measurable_const : Measurable fun _ : T2 => r) volume) := by
  refine ergodic_suspensionFlowMap_one_const_roof catTorusEquiv hr0 hr
    measurePreserving_catTorusEquiv ?_ ?_
  · -- base ergodicity, bridged `⇑catTorusEquiv = catTorus`
    have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
    rw [hcoe]; exact ergodic_catTorus
  · -- spectral rigidity: no nontrivial unimodular eigenfunctions
    intro g l hg heig hl hl1
    exact catTorus_eigenfunction_ae_zero hg heig hl hl1

/-- **Packaged form** of `ergodic_catSuspension_timeOne_const_irrational`: the same ergodicity of
the time-`1` map, phrased against the bundled `MeasurePreservingFlow`
`suspensionFlow catTorusEquiv (τ ≡ r) …` applied at time `1`. Definitionally the raw
`suspensionFlowMap` statement, since the flow's `CoeFun` is its `toFun` field. -/
theorem ergodic_catSuspension_packaged_timeOne_const_irrational {r : ℝ} (hr0 : 0 < r)
    (hr : Irrational r) :
    Ergodic
      ((suspensionFlow (T := catTorusEquiv) (τ := fun _ => r) measurable_const
          measurePreserving_catTorusEquiv (c := r) (fun _ => le_rfl) hr0) 1)
      (suspensionMeasure catTorusEquiv (τ := fun _ => r) measurable_const volume) :=
  ergodic_catSuspension_timeOne_const_irrational hr0 hr

/-- **Concrete non-vacuity witness** for `ergodic_catSuspension_timeOne_const_irrational`: the
irrational roof `r := √2` (via `irrational_sqrt_two`) yields an ergodic time-`1` map, confirming the
hypothesis `Irrational r` is satisfiable. -/
theorem ergodic_catSuspension_timeOne_sqrtTwo :
    Ergodic (suspensionFlowMap catTorusEquiv
        (measurable_const : Measurable fun _ : T2 => Real.sqrt 2) 1)
      (suspensionMeasure catTorusEquiv
        (measurable_const : Measurable fun _ : T2 => Real.sqrt 2) volume) :=
  ergodic_catSuspension_timeOne_const_irrational
    (Real.sqrt_pos.mpr (by norm_num)) irrational_sqrt_two

end ErgodicTheory.CatMapToral
