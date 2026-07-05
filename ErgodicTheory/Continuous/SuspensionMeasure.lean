/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.Suspension
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measure-preservation for the suspension construction

This module supplies the measure-theoretic infrastructure that the suspension (mapping-torus)
construction of `ErgodicTheory.Continuous.Suspension` deliberately deferred: the fact that the
generating automorphism of the suspension `ℤ`-action preserves the product measure `μ × volume`.

The key new ingredient is the **shear** map `(x, s) ↦ (x, s − τ x)`. It is a fibered translation:
on each fibre `{x} × ℝ` it is the translation `s ↦ s − τ x`, which preserves Lebesgue measure
because `volume` on `ℝ` is right-invariant. Assembling the fibrewise translations via the
skew-product Fubini lemma `MeasureTheory.MeasurePreserving.skew_product` shows the shear preserves
`μ × volume`. The generating automorphism `suspensionGen T hτ : (x, s) ↦ (T x, s − τ x)` is then
the same skew product over the base map `T`, so it preserves `μ × volume` whenever `T` does.

## Main results

* `ErgodicTheory.measurePreserving_shear`: the shear `(x, s) ↦ (x, s − τ x)` preserves `μ × volume`.
* `ErgodicTheory.measurePreserving_suspensionGen`: the generator `suspensionGen T hτ` preserves
  `μ × volume`, given `MeasurePreserving T μ μ`.
* `ErgodicTheory.suspensionDomain_fiber`: the `x`-fibre of the box is the half-open interval
  `Ico 0 (τ x)`.
* `ErgodicTheory.measure_suspensionDomain`: the box mass equals `ENNReal.ofReal (∫ x, τ x ∂μ)`
  for a nonnegative integrable roof function `τ`.

These are the measure facts from which the suspension's invariant probability measure
`(μ × volume)|_box / ∫ τ` and the per-time measure-preservation of the suspension flow are
subsequently built.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

section Shear

variable {τ : X → ℝ} (hτ : Measurable τ)

include hτ in
/-- The **shear** map `(x, s) ↦ (x, s − τ x)` preserves the product measure `μ × volume`.

It is a fibered translation: on each fibre `{x} × ℝ` it is the Lebesgue-measure-preserving
translation `s ↦ s − τ x` (right-invariance of `volume` on `ℝ`). The skew-product Fubini lemma
`MeasureTheory.MeasurePreserving.skew_product` over the identity base map assembles these into the
product-measure statement. -/
theorem measurePreserving_shear (μ : Measure X) [SFinite μ] :
    MeasurePreserving (fun p : X × ℝ => (p.1, p.2 - τ p.1)) (μ.prod volume) (μ.prod volume) := by
  have hg : Measurable (Function.uncurry fun (x : X) (s : ℝ) => s - τ x) :=
    measurable_snd.sub (hτ.comp measurable_fst)
  have hmap : ∀ᵐ x ∂μ, Measure.map (fun s : ℝ => s - τ x) volume = volume :=
    ae_of_all _ fun x => (measurePreserving_sub_right volume (τ x)).map_eq
  exact (MeasurePreserving.id μ).skew_product hg hmap

include hτ in
/-- The suspension generator `suspensionGen T hτ : (x, s) ↦ (T x, s − τ x)` preserves the product
measure `μ × volume`, given that the base map `T` preserves `μ`.

It is the skew product over `T` whose fibre translation is `s ↦ s − τ x`; equivalently, the shear
`measurePreserving_shear` followed by the base move `(x, s) ↦ (T x, s)`. -/
theorem measurePreserving_suspensionGen {μ : Measure X} [SFinite μ] {T : X ≃ᵐ X}
    (hT : MeasurePreserving T μ μ) :
    MeasurePreserving (suspensionGen T hτ) (μ.prod volume) (μ.prod volume) := by
  have hg : Measurable (Function.uncurry fun (x : X) (s : ℝ) => s - τ x) :=
    measurable_snd.sub (hτ.comp measurable_fst)
  have hmap : ∀ᵐ x ∂μ, Measure.map (fun s : ℝ => s - τ x) volume = volume :=
    ae_of_all _ fun x => (measurePreserving_sub_right volume (τ x)).map_eq
  have h := hT.skew_product hg hmap
  refine h.congr (suspensionGen T hτ).measurable ?_
  filter_upwards with p
  simp only [suspensionGen_apply]

end Shear

section BoxMass

variable {τ : X → ℝ}

omit [MeasurableSpace X] in
/-- The `x`-fibre of the box under the roof is the half-open interval `Ico 0 (τ x)`:
`{s : ℝ | (x, s) ∈ suspensionDomain τ} = Ico 0 (τ x)`. -/
theorem suspensionDomain_fiber (x : X) :
    Prod.mk x ⁻¹' suspensionDomain τ = Ico 0 (τ x) := by
  ext s
  simp only [suspensionDomain, mem_preimage, mem_setOf_eq, mem_Ico]

/-- The mass of the box under the roof equals `ENNReal.ofReal (∫ x, τ x ∂μ)`, for a nonnegative
integrable roof function `τ`. This is the normalising constant for the suspension's invariant
probability measure.

The proof is Fubini: the `x`-fibre of the box is `Ico 0 (τ x)`, whose Lebesgue measure is
`ENNReal.ofReal (τ x)` (as `0 ≤ τ x`), and `∫⁻ x, ofReal (τ x) ∂μ = ofReal (∫ x, τ x ∂μ)` for a
nonnegative integrable function. -/
theorem measure_suspensionDomain {μ : Measure X} [SFinite μ] (hτ : Measurable τ)
    (hτ_nonneg : ∀ x, 0 ≤ τ x) (hτ_int : Integrable τ μ) :
    (μ.prod volume) (suspensionDomain τ) = ENNReal.ofReal (∫ x, τ x ∂μ) := by
  rw [Measure.prod_apply (measurableSet_suspensionDomain hτ)]
  have hfiber : ∀ x, volume (Prod.mk x ⁻¹' suspensionDomain τ)
      = ENNReal.ofReal (τ x) := by
    intro x
    rw [suspensionDomain_fiber, Real.volume_Ico, sub_zero]
  simp only [hfiber]
  rw [ofReal_integral_eq_lintegral_ofReal hτ_int (ae_of_all _ hτ_nonneg)]

end BoxMass

end ErgodicTheory
