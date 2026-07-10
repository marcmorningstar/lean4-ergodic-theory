/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionTimeOneErgodic
import ErgodicTheory.Multifractal.BernoulliTwoSidedMixing
import ErgodicTheory.Ergodic.EigenvalueMixing
import Mathlib.Data.Real.Sqrt

/-!
# Ergodicity of the time-`1` map of the constant-irrational-roof Bernoulli suspension flow

This module is **the tier-1 headline of GitHub issue #35**: the time-`1` map of the constant-roof
suspension flow over the two-sided Bernoulli shift is **ergodic**, provided the roof height `r` is a
positive **irrational**.

It assembles three green pieces into the abstract base-generic ergodicity theorem
`ErgodicTheory.ergodic_suspensionFlowMap_one_const_roof`:

* **base ergodicity** — `ergodic_biShiftEquiv_bernZ` (the mixing/cylinder-approximation keystone for
  the invertible two-sided Bernoulli shift);
* **spectral rigidity** — the base shift has *no nontrivial unimodular eigenfunctions*: strong
  mixing (`tendsto_measureReal_inter_preimage_iterate`, STEP A) kills every eigenvalue `≠ 1` on unit
  circle (`eigenfunction_ae_zero_of_mixing`, STEP B). The two are bridged by
  `coe_biShiftEquiv : ⇑biShiftEquiv = biShiftMap`, which makes the mixing lemma's `biShiftMap^[k]`
  and the eigen lemma's `f^[k]` (with `f = ⇑biShiftEquiv`) definitionally the same;
* **the fibre-Fourier core** — packaged inside `ergodic_suspensionFlowMap_one_const_roof`.

## Contrast with the unit roof

For the **unit** roof `τ ≡ 1` the time-`1` map is *not* ergodic
(`not_ergodic_bernSuspensionFlow_one`): it merely re-bases the height and fixes the fractional
section coordinate, so the saturated half-section `{[x, s] | Int.fract s < 1/2}` is a nontrivial
invariant set. An *irrational* roof breaks this: the invariance period stays `1`, but the deck
translation now advances the fibre by the *irrational* `r`, so the fibre Fourier coefficients pick
up the unimodular twist `e^{2πi n r} ≠ 1`, which base mixing annihilates. This is the constant-roof
special-flow dichotomy of Cornfeld–Fomin–Sinai (*Ergodic Theory*, Grundlehren 245, Ch. 11): the
transform window is the *invariance period* `1`, not the roof `r`, so no lap decomposition is
needed.

**Contrast with the entropy side (issue #38).** The Kolmogorov–Sinai entropy of the same time-`1`
map is computed in `ErgodicTheory.Continuous.SuspensionEntropyDescent` under the *opposite*
arithmetic restriction: `h(ζ^{(r)}_1) = Hnu ν / r` is proved there for **rational** `r`
(`ksEntropy_bernConstSuspension_time_one`). The two conditions are complementary, not
contradictory: the entropy value holds for every `r > 0` (only its proof is restricted to rational
`r`, the documented Abramov wall), so a rational-roof time-`1` map still carries entropy
`Hnu ν / r` while failing ergodicity.

## Main results

* `ergodic_suspensionFlow_timeOne_const_irrational` — the tier-1 headline, stated against the raw
  `suspensionFlowMap`.
* `ergodic_suspensionFlow_packaged_timeOne_const_irrational` — the same result phrased against the
  packaged `MeasurePreservingFlow` `suspensionFlow`, applied at time `1`.
* `ergodic_suspensionFlow_timeOne_sqrtTwo` — the concrete non-vacuity witness `r := √2` (via
  `irrational_sqrt_two`), showing the irrationality hypothesis is satisfiable.
-/

open MeasureTheory

namespace ErgodicTheory

namespace Multifractal

/-- **The time-`1` map of the constant-irrational-roof Bernoulli suspension flow is ergodic**
(issue #35, tier 1). For the invertible two-sided Bernoulli shift `biShiftEquiv` with i.i.d. measure
`bernZ ν`, and any positive **irrational** roof height `r`, the time-`1` map
`suspensionFlowMap biShiftEquiv (τ ≡ r) 1` is ergodic for the invariant suspension probability
measure.

The proof discharges the abstract base-generic theorem
`ergodic_suspensionFlowMap_one_const_roof` with:
* base ergodicity `ergodic_biShiftEquiv_bernZ`;
* the *no-nontrivial-eigenfunctions* spectral input: strong mixing of the Bernoulli shift
  (`tendsto_measureReal_inter_preimage_iterate`) forces every measurable eigenfunction with a
  unimodular eigenvalue `≠ 1` to vanish a.e. (`eigenfunction_ae_zero_of_mixing`); the two are joined
  by `coe_biShiftEquiv`, making `biShiftMap^[k]` and `(⇑biShiftEquiv)^[k]` definitionally equal.

Contrast the **unit** roof, whose time-`1` map is *not* ergodic
(`not_ergodic_bernSuspensionFlow_one`). See Cornfeld–Fomin–Sinai, Ch. 11 (special flows): the
fibre-Fourier transform window is the invariance period `1`, not the roof `r`. -/
theorem ergodic_suspensionFlow_timeOne_const_irrational
    {α₀ : Type*} [MeasurableSpace α₀]
    (ν : Measure α₀) [IsProbabilityMeasure ν] {r : ℝ} (hr0 : 0 < r) (hr : Irrational r) :
    Ergodic (suspensionFlowMap (biShiftEquiv (α₀ := α₀))
        (measurable_const : Measurable (fun _ : BiShift α₀ => r)) 1)
      (suspensionMeasure (biShiftEquiv (α₀ := α₀))
        (measurable_const : Measurable (fun _ : BiShift α₀ => r)) (bernZ ν)) := by
  refine ergodic_suspensionFlowMap_one_const_roof (biShiftEquiv (α₀ := α₀)) hr0 hr
    (measurePreserving_biShiftEquiv_bernZ ν) (ergodic_biShiftEquiv_bernZ ν) ?_
  -- Spectral rigidity: no nontrivial unimodular eigenfunctions, from base mixing.
  intro g l hg heig hl hl1
  refine eigenfunction_ae_zero_of_mixing
    (f := (⇑(biShiftEquiv (α₀ := α₀)) : BiShift α₀ → BiShift α₀)) ?_
    (biShiftEquiv (α₀ := α₀)).measurable hg heig hl hl1
  -- The mixing input; `⇑biShiftEquiv` and `biShiftMap` are defeq (`coe_biShiftEquiv`).
  intro A hA
  exact tendsto_measureReal_inter_preimage_iterate ν hA hA

/-- **Packaged form** of `ergodic_suspensionFlow_timeOne_const_irrational`: the same ergodicity of
the time-`1` map, phrased against the bundled `MeasurePreservingFlow`
`suspensionFlow biShiftEquiv (τ ≡ r) …` applied at time `1`. This is definitionally the raw
`suspensionFlowMap` statement, since the flow's `CoeFun` is its `toFun` field. -/
theorem ergodic_suspensionFlow_packaged_timeOne_const_irrational
    {α₀ : Type*} [MeasurableSpace α₀]
    (ν : Measure α₀) [IsProbabilityMeasure ν] {r : ℝ} (hr0 : 0 < r) (hr : Irrational r) :
    Ergodic
      ((suspensionFlow (T := biShiftEquiv (α₀ := α₀))
          (τ := fun _ => r) measurable_const
          (measurePreserving_biShiftEquiv_bernZ ν)
          (c := r) (fun _ => le_rfl) hr0) 1)
      (suspensionMeasure (biShiftEquiv (α₀ := α₀))
        (τ := fun _ => r) measurable_const (bernZ ν)) :=
  ergodic_suspensionFlow_timeOne_const_irrational ν hr0 hr

/-- **Concrete non-vacuity witness** for `ergodic_suspensionFlow_timeOne_const_irrational`: the
irrational roof `r := √2` (via `irrational_sqrt_two`) yields an ergodic time-`1` map. This gives a
genuine positive-irrational roof, confirming the hypothesis `Irrational r` is satisfiable. -/
theorem ergodic_suspensionFlow_timeOne_sqrtTwo
    {α₀ : Type*} [MeasurableSpace α₀]
    (ν : Measure α₀) [IsProbabilityMeasure ν] :
    Ergodic (suspensionFlowMap (biShiftEquiv (α₀ := α₀))
        (measurable_const : Measurable (fun _ : BiShift α₀ => Real.sqrt 2)) 1)
      (suspensionMeasure (biShiftEquiv (α₀ := α₀))
        (measurable_const : Measurable (fun _ : BiShift α₀ => Real.sqrt 2)) (bernZ ν)) :=
  ergodic_suspensionFlow_timeOne_const_irrational ν
    (Real.sqrt_pos.mpr (by norm_num)) irrational_sqrt_two

end Multifractal

end ErgodicTheory
