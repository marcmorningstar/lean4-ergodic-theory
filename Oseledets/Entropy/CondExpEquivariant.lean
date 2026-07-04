/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Probability.Kernel.Condexp

/-!
# Measure-preserving change-of-variables helpers for conditional entropy

This module collects the elementary measure-preserving change-of-variables facts used by the
conditional-entropy layer of GitHub issue #13: preimages of measurable sets stay measurable, and
integrals — and set-integrals over preimages of measurable sets — are unchanged under
precomposition with a measure-preserving self-map. They are consumed by the joint pull-back of
conditional entropy (`Oseledets.Entropy.CondJointPullback`), where the conditioning σ-algebra is
itself pulled back so no two-sided invariance hypothesis is needed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Oseledets.Entropy

section Helpers
-- These helpers involve ONLY the ambient `mΩ`: no sub-σ-algebra is in scope, so the measurable
-- space is unambiguous for instance synthesis (`integral_map`, `MeasurableSet`, …).
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-- `T⁻¹' B` is measurable when `T` is measure-preserving and `B` is measurable. -/
theorem measurableSet_preimage_of_measurePreserving
    (hT : MeasurePreserving T μ μ) {B : Set Ω} (hB : MeasurableSet B) :
    MeasurableSet (T ⁻¹' B) :=
  hT.measurable hB

/-- Integrability is preserved under precomposition with a measure-preserving self-map. -/
theorem integrable_comp_self
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω => f (T ω)) μ :=
  Integrable.comp_measurable (by rwa [hT.map_eq]) hT.measurable

/-- Change of variables for a measure-preserving self-map: `∫ f(T ω) dμ = ∫ f dμ`. -/
theorem integral_comp_self
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∫ ω, f (T ω) ∂μ = ∫ ω, f ω ∂μ := by
  rw [← integral_map (φ := T) hT.measurable.aemeasurable (hf.mono_ac (by rw [hT.map_eq])),
    hT.map_eq]

/-- The change-of-variables building block on `T`-preimages of measurable sets:
`∫_{T⁻¹A'} f(T ω) dμ = ∫_{A'} f dμ`. -/
theorem setIntegral_comp_preimage
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {A' : Set Ω} (hA' : MeasurableSet A') :
    ∫ ω in T ⁻¹' A', f (T ω) ∂μ = ∫ ω in A', f ω ∂μ := by
  rw [← integral_indicator (hT.measurable hA'), ← integral_indicator hA']
  have hcomp : (T ⁻¹' A').indicator (fun ω => f (T ω))
      = fun ω => (A'.indicator f) (T ω) := by
    funext ω
    by_cases hω : T ω ∈ A'
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  rw [hcomp]
  exact integral_comp_self hT (hf.indicator hA')

end Helpers

end Oseledets.Entropy
