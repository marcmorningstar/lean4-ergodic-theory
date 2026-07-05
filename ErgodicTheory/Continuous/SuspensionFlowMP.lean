/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlow
import ErgodicTheory.Continuous.Flow

/-!
# Measure-preservation of the suspension flow

This module supplies the measure-theoretic content that
`ErgodicTheory.Continuous.SuspensionFlow` deliberately deferred: the per-time **measure-preservation**
of the suspension flow `ζ_t` on the suspension probability space, and its packaging as a
`MeasurePreservingFlow`.

The descent argument runs through the fundamental domain. The suspension measure is the
pushforward of `μ × volume` restricted to the half-open box `𝓕 = suspensionDomain τ` along the
quotient projection `π = suspensionMk`. The flow `ζ_t` descends from the vertical translation
`S t (x, s) = (x, s + t)`, which

* preserves `ν = μ × volume` (`measurePreserving_translate`), and
* commutes with the suspension `ℤ`-action (`suspensionAct_translate`),

so the image box `S t '' 𝓕` is again a fundamental domain (`image_of_equiv` for fundamental
domains). Pushing forward, `(ζ_t)_* (ν|_𝓕 ↦ π) = (ν|_(S t '' 𝓕) ↦ π)`, and the
fundamental-domain independence of the quotient measure (`measure_set_eq` applied to the
saturated set `π ⁻¹' U`) identifies this with the original `(ν|_𝓕 ↦ π)`. The normalising
scalar passes through `Measure.map_smul`.

## Main results

* `ErgodicTheory.suspensionTranslateEquiv`: the vertical translation `S t` packaged as a measurable
  equivalence on `X × ℝ` (used to take measurable images of the fundamental domain).
* `ErgodicTheory.suspensionFlowMap_comp_mk`: the descent commutation `ζ_t ∘ π = π ∘ S t`.
* `ErgodicTheory.map_suspensionFlowMap_suspensionMeasure₀`: `(ζ_t)_* μ̂₀ = μ̂₀` for the raw
  (unnormalised) suspension measure.
* `ErgodicTheory.measurePreserving_suspensionFlowMap`: each `ζ_t` preserves the suspension
  probability measure `suspensionMeasure`.
* `ErgodicTheory.suspensionFlow`: the suspension flow packaged as a `MeasurePreservingFlow`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

section TranslateEquiv

/-- The vertical translation `S t (x, s) = (x, s + t)` as a measurable equivalence on `X × ℝ`,
with inverse `S (-t)`. Bundling it as an equivalence lets us take measurable images of the
fundamental domain and invoke the fundamental-domain transport lemma `image_of_equiv`. -/
def suspensionTranslateEquiv (t : ℝ) : (X × ℝ) ≃ᵐ (X × ℝ) where
  toFun := suspensionTranslate t
  invFun := suspensionTranslate (-t)
  left_inv p := by simp [suspensionTranslate]
  right_inv p := by simp [suspensionTranslate]
  measurable_toFun := measurable_suspensionTranslate t
  measurable_invFun := measurable_suspensionTranslate (-t)

@[simp] theorem suspensionTranslateEquiv_apply (t : ℝ) (p : X × ℝ) :
    suspensionTranslateEquiv t p = suspensionTranslate t p := rfl

@[simp] theorem suspensionTranslateEquiv_symm_apply (t : ℝ) (p : X × ℝ) :
    (suspensionTranslateEquiv t).symm p = suspensionTranslate (-t) p := rfl

end TranslateEquiv

section ActionInvariance

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

include hτ in
/-- Each integer iterate of the suspension action is measurable: it is a power of the measurable
generator `suspensionGen`. Proved by induction on `n` from the measurability of the generator and
its inverse. -/
theorem measurable_suspensionAct (n : ℤ) : Measurable (suspensionAct T hτ n) := by
  induction n using Int.induction_on with
  | zero => simpa only [suspensionAct_zero] using measurable_id
  | succ k ih =>
    have hstep : suspensionAct T hτ ((k : ℤ) + 1)
        = suspensionGen T hτ ∘ suspensionAct T hτ (k : ℤ) := by
      funext p; rw [add_comm, suspensionAct_add, suspensionAct_one]; rfl
    rw [hstep]; exact (suspensionGen T hτ).measurable.comp ih
  | pred k ih =>
    have hstep : suspensionAct T hτ (-(k : ℤ) - 1)
        = (suspensionGen T hτ).symm ∘ suspensionAct T hτ (-(k : ℤ)) := by
      funext p
      rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one]; rfl
    rw [hstep]; exact (suspensionGen T hτ).symm.measurable.comp ih

include hτ in
/-- Each integer iterate of the suspension action preserves `μ × volume`: it is a power of the
measure-preserving generator `suspensionGen`, so `suspensionAct n` preserves the product measure
for every `n : ℤ`. Proved by induction on `n` from `measurePreserving_suspensionGen` and the
measure-preservation of its inverse. -/
theorem measurePreserving_suspensionAct {μ : Measure X} [SFinite μ] (hT : MeasurePreserving T μ μ)
    (n : ℤ) :
    MeasurePreserving (suspensionAct T hτ n) (μ.prod volume) (μ.prod volume) := by
  have hgen := measurePreserving_suspensionGen hτ hT
  have hgensymm : MeasurePreserving (suspensionGen T hτ).symm (μ.prod volume) (μ.prod volume) :=
    hgen.symm _
  induction n using Int.induction_on with
  | zero => simpa only [suspensionAct_zero] using MeasurePreserving.id _
  | succ k ih =>
    have hstep : suspensionAct T hτ ((k : ℤ) + 1)
        = suspensionGen T hτ ∘ suspensionAct T hτ (k : ℤ) := by
      funext p; rw [add_comm, suspensionAct_add, suspensionAct_one]; rfl
    rw [hstep]; exact hgen.comp ih
  | pred k ih =>
    have hstep : suspensionAct T hτ (-(k : ℤ) - 1)
        = (suspensionGen T hτ).symm ∘ suspensionAct T hτ (-(k : ℤ)) := by
      funext p
      rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one]; rfl
    rw [hstep]; exact hgensymm.comp ih

include hτ in
/-- The suspension action has measurable constant translations: `n +ᵥ ·` is measurable for each
`n : ℤ` (it is the measurable power of the generator). Packaged as the `MeasurableConstVAdd`
instance needed by the fundamental-domain quotient lemmas. -/
theorem measurableConstVAdd_suspension :
    letI := (suspensionAddAction T hτ).toVAdd
    MeasurableConstVAdd ℤ (X × ℝ) := by
  letI := suspensionAddAction T hτ
  exact ⟨fun n => measurable_suspensionAct T hτ n⟩

include hτ in
/-- The product measure `μ × volume` is invariant under the suspension action: each
`suspensionAct n` preserves it (`measurePreserving_suspensionAct`), so the preimage of any
measurable set has the same measure. Packaged as the `VAddInvariantMeasure` instance needed by
the fundamental-domain quotient lemmas. -/
theorem vaddInvariantMeasure_suspension {μ : Measure X} [SFinite μ] (hT : MeasurePreserving T μ μ) :
    letI := (suspensionAddAction T hτ).toVAdd
    VAddInvariantMeasure ℤ (X × ℝ) (μ.prod volume) := by
  letI := suspensionAddAction T hτ
  refine ⟨fun n s hs => ?_⟩
  change (μ.prod volume) (suspensionAct T hτ n ⁻¹' s) = (μ.prod volume) s
  exact (measurePreserving_suspensionAct T hτ hT n).measure_preimage hs.nullMeasurableSet

end ActionInvariance

section Descent

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The descent commutation `ζ_t ∘ π = π ∘ S t`: the suspension flow map composed with the
quotient projection equals the projection of the vertical translation. -/
theorem suspensionFlowMap_comp_mk (t : ℝ) :
    suspensionFlowMap T hτ t ∘ suspensionMk T hτ
      = suspensionMk T hτ ∘ suspensionTranslate t := by
  funext p
  simp [suspensionFlowMap_mk]

include hτ in
/-- Fundamental-domain independence of the raw quotient measure: pushing `ν = μ × volume`
restricted to the translated box `S t '' 𝓕` along the quotient projection gives the same measure
as pushing it from the original box `𝓕`. This is the additive `quotientMeasure_eq`, proved here
inline from `addMeasure_map_restrict_apply` and the fundamental-domain set-measure equality
`measure_set_eq` applied to the saturated set `π ⁻¹' U`. -/
theorem map_restrict_image_translate_eq {μ : Measure X} [SFinite μ] (hT : MeasurePreserving T μ μ)
    {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) :
    ((μ.prod volume).restrict (suspensionTranslate t '' suspensionDomain τ)).map
        (suspensionMk T hτ)
      = ((μ.prod volume).restrict (suspensionDomain τ)).map (suspensionMk T hτ) := by
  letI := suspensionAddAction T hτ
  have hfund := isAddFundamentalDomain_suspensionDomain T hτ (μ := μ) hc hcpos
  have hqmp : MeasureTheory.MeasurePreserving
      (suspensionTranslate (X := X) (-t)) (μ.prod volume) (μ.prod volume) :=
    measurePreserving_translate μ (-t)
  have hfundT : IsAddFundamentalDomain ℤ (suspensionTranslate t '' suspensionDomain τ)
      (μ.prod volume) := by
    refine hfund.image_of_equiv (suspensionTranslateEquiv t).toEquiv
      hqmp.quasiMeasurePreserving (Equiv.refl ℤ) (fun n p => ?_)
    change suspensionTranslate t (suspensionAct T hτ n p)
      = suspensionAct T hτ n (suspensionTranslate t p)
    rw [suspensionAct_translate T hτ n t p]
  haveI := measurableConstVAdd_suspension T hτ
  haveI := vaddInvariantMeasure_suspension T hτ hT
  have hmπ : Measurable (suspensionMk T hτ) := measurable_suspensionMk T hτ
  have hcomm : ∀ (n : ℤ) (p : X × ℝ), suspensionMk T hτ (n +ᵥ p) = suspensionMk T hτ p :=
    fun n p => Quotient.sound ⟨n, rfl⟩
  ext U meas_U
  have hpreU : MeasurableSet (suspensionMk T hτ ⁻¹' U) := hmπ meas_U
  have hsat : ∀ n : ℤ, (fun x => n +ᵥ x) ⁻¹' (suspensionMk T hτ ⁻¹' U)
      = suspensionMk T hτ ⁻¹' U :=
    fun n => by ext p; simp only [mem_preimage, hcomm n p]
  rw [Measure.map_apply hmπ meas_U, Measure.map_apply hmπ meas_U,
    Measure.restrict_apply hpreU, Measure.restrict_apply hpreU]
  exact hfundT.measure_set_eq hfund hpreU hsat

include hτ in
/-- The raw (unnormalised) suspension measure `μ̂₀` is invariant under the suspension flow:
`(ζ_t)_* μ̂₀ = μ̂₀`. Combining the descent commutation `ζ_t ∘ π = π ∘ S t`, the
measure-preservation of `S t`, and the fundamental-domain independence
`map_restrict_image_translate_eq`. -/
theorem map_suspensionFlowMap_suspensionMeasure₀ {μ : Measure X} [SFinite μ]
    (hT : MeasurePreserving T μ μ) {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) :
    (suspensionMeasure₀ T hτ μ).map (suspensionFlowMap T hτ t) = suspensionMeasure₀ T hτ μ := by
  have hStransl := measurePreserving_translate (X := X) μ t
  have hmS : Measurable (suspensionTranslate (X := X) t) := measurable_suspensionTranslate t
  have hmπ : Measurable (suspensionMk T hτ) := measurable_suspensionMk T hτ
  have hmζ : Measurable (suspensionFlowMap T hτ t) := measurable_suspensionFlowMap T hτ t
  have hSimage : MeasurableSet (suspensionTranslate t '' suspensionDomain τ) :=
    (suspensionTranslateEquiv (X := X) t).measurableSet_image.mpr
      (measurableSet_suspensionDomain hτ)
  have hpre : suspensionTranslate (X := X) t ⁻¹' (suspensionTranslate t '' suspensionDomain τ)
      = suspensionDomain τ :=
    preimage_image_eq _ (suspensionTranslateEquiv (X := X) t).injective
  -- `(ν|_𝓕).map S t = ν|_(S t '' 𝓕)`, using that `S t` preserves `ν = μ × volume`.
  have hrestrict : ((μ.prod volume).restrict (suspensionDomain τ)).map (suspensionTranslate t)
      = (μ.prod volume).restrict (suspensionTranslate t '' suspensionDomain τ) := by
    rw [← hStransl.map_eq, Measure.restrict_map hmS hSimage, hpre, hStransl.map_eq]
  -- Push the descent `ζ_t ∘ π = π ∘ S t` through the quotient, then apply
  -- fundamental-domain independence.
  rw [suspensionMeasure₀, Measure.map_map hmζ hmπ, suspensionFlowMap_comp_mk T hτ t,
    ← Measure.map_map hmπ hmS, hrestrict, map_restrict_image_translate_eq T hτ hT hc hcpos t]

end Descent

section MeasurePreserving

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

include hτ in
/-- **Each suspension flow map preserves the suspension probability measure.** With a
measure-preserving base map `T`, a strictly positive integrable roof function `τ` (bounded
below by `c > 0`), the descended flow `ζ_t` preserves `suspensionMeasure`.

The raw measure `μ̂₀` is `ζ_t`-invariant (`map_suspensionFlowMap_suspensionMeasure₀`); the
normalising scalar passes through `Measure.map_smul`. -/
theorem measurePreserving_suspensionFlowMap {μ : Measure X} [SFinite μ]
    (hT : MeasurePreserving T μ μ) {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) :
    MeasurePreserving (suspensionFlowMap T hτ t)
      (suspensionMeasure T hτ μ) (suspensionMeasure T hτ μ) where
  measurable := measurable_suspensionFlowMap T hτ t
  map_eq := by
    rw [suspensionMeasure, Measure.map_smul,
      map_suspensionFlowMap_suspensionMeasure₀ T hτ hT hc hcpos t]

include hτ in
/-- **The suspension flow as a measure-preserving flow.** Packages the additive, measurable,
measure-preserving family `ζ_t` into a `MeasurePreservingFlow` on the suspension probability
space. The `map_add'` field uses `φ (s + t) = φ s ∘ φ t` (`suspensionFlowMap_add`). -/
def suspensionFlow {μ : Measure X} [SFinite μ] (hT : MeasurePreserving T μ μ)
    {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) :
    MeasurePreservingFlow (suspensionMeasure T hτ μ) where
  toFun := suspensionFlowMap T hτ
  map_zero' := suspensionFlowMap_zero T hτ
  map_add' := suspensionFlowMap_add T hτ
  measurePreserving' t := measurePreserving_suspensionFlowMap T hτ hT hc hcpos t

end MeasurePreserving

end ErgodicTheory
