/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionSpace

/-!
# The suspension flow

This module builds the natural one-parameter flow on the suspension (mapping-torus) space of
`Oseledets.Continuous.SuspensionSpace`. On the product `X × ℝ` the flow is the `ℝ`-translation in
the second (time) coordinate,

`S t (x, s) = (x, s + t)`,

and the suspension flow `ζ_t` is its descent through the orbit quotient:
`ζ_t [x, s] = [x, s + t]`.

The descent is well-defined because `S t` *commutes* with the suspension `ℤ`-action: the generator
`G (x, s) = (T x, s − τ x)` moves the first coordinate by `T` and subtracts a roof value from the
second, while `S t` only adds `t` to the second coordinate, so the two operations on the second
coordinate (subtracting `roofSum n x`, adding `t`) commute. Concretely
`suspensionAct n (S t p) = S t (suspensionAct n p)` (`suspensionAct_translate`), which sends one
orbit onto another and makes `ζ_t` well-defined on the quotient.

## Main definitions

* `Oseledets.suspensionTranslate`: the `ℝ`-translation `S t (x, s) = (x, s + t)` on `X × ℝ`.
* `Oseledets.suspensionFlowMap`: the descended time-`t` map `ζ_t` on the suspension space.

## Main results

* `Oseledets.measurePreserving_translate`: `S t` preserves `μ × volume` (fibrewise translation
  invariance of Lebesgue measure).
* `Oseledets.suspensionAct_translate`: the commutation
  `suspensionAct n (S t p) = S t (suspensionAct n p)` of the action with the translation — the
  well-definedness core.
* `Oseledets.suspensionFlowMap_mk`: the descent identity `ζ_t [p] = [S t p]`.
* `Oseledets.suspensionFlowMap_zero`: `ζ_0 = id`.
* `Oseledets.suspensionFlowMap_add`: `ζ_(s+t) = ζ_s ∘ ζ_t`.
* `Oseledets.measurable_suspensionFlowMap`: each `ζ_t` is measurable.

## What is *not* in this file

The per-time *measure-preservation* of the suspension flow,
`MeasurePreserving (suspensionFlowMap t) suspensionMeasure suspensionMeasure`, and its packaging as
a `MeasurePreservingFlow`, are deliberately left to a follow-up module. Establishing them requires
transporting the fundamental-domain measure-preservation of the `ℝ`-translation through the quotient
map (an `IsAddFundamentalDomain`/`Measure.map` argument), which is a separate piece of
infrastructure. This file stops at the well-defined, additive, measurable flow maps, which are
self-contained and sorry-free.
-/

open MeasureTheory Set

namespace Oseledets

variable {X : Type*} [MeasurableSpace X]

section Translate

/-- The `ℝ`-**translation** in the time coordinate, `S t (x, s) = (x, s + t)`. This is the lift to
`X × ℝ` of the suspension flow; its descent through the orbit quotient is `suspensionFlowMap`. -/
def suspensionTranslate (t : ℝ) (p : X × ℝ) : X × ℝ := (p.1, p.2 + t)

omit [MeasurableSpace X] in
@[simp] theorem suspensionTranslate_apply (t : ℝ) (p : X × ℝ) :
    suspensionTranslate t p = (p.1, p.2 + t) := rfl

omit [MeasurableSpace X] in
@[simp] theorem suspensionTranslate_zero (p : X × ℝ) : suspensionTranslate 0 p = p := by
  simp [suspensionTranslate]

omit [MeasurableSpace X] in
theorem suspensionTranslate_add (s t : ℝ) (p : X × ℝ) :
    suspensionTranslate (s + t) p = suspensionTranslate s (suspensionTranslate t p) := by
  simp only [suspensionTranslate, Prod.mk.injEq, true_and]
  ring

theorem measurable_suspensionTranslate (t : ℝ) :
    Measurable (suspensionTranslate (X := X) t) :=
  measurable_fst.prodMk (measurable_snd.add_const t)

/-- The translation `S t (x, s) = (x, s + t)` preserves the product measure `μ × volume`.

It is a fibered translation: on each fibre `{x} × ℝ` it is the Lebesgue-measure-preserving
translation `s ↦ s + t` (right-invariance of `volume` on `ℝ`). The skew-product Fubini lemma
`MeasureTheory.MeasurePreserving.skew_product` over the identity base map assembles these into the
product-measure statement. -/
theorem measurePreserving_translate (μ : Measure X) [SFinite μ] (t : ℝ) :
    MeasurePreserving (suspensionTranslate (X := X) t) (μ.prod volume) (μ.prod volume) := by
  have hg : Measurable (Function.uncurry fun (_ : X) (s : ℝ) => s + t) :=
    measurable_snd.add_const t
  have hmap : ∀ᵐ x ∂μ, Measure.map (fun s : ℝ => s + t) volume = volume :=
    ae_of_all _ fun _ => (measurePreserving_add_right volume t).map_eq
  exact (MeasurePreserving.id μ).skew_product hg hmap

end Translate

section Commute

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The suspension `ℤ`-action **commutes** with the `ℝ`-translation:
`suspensionAct n (S t p) = S t (suspensionAct n p)`. The action subtracts `roofSum n x` (a quantity
independent of the time coordinate) from the time coordinate and moves the base coordinate by the
iterate of `T`; the translation adds `t` to the time coordinate; these two operations on the time
coordinate commute. This is the key fact making the descended flow well-defined on the quotient. -/
theorem suspensionAct_translate (n : ℤ) (t : ℝ) (p : X × ℝ) :
    suspensionAct T hτ n (suspensionTranslate t p)
      = suspensionTranslate t (suspensionAct T hτ n p) := by
  obtain ⟨x, s⟩ := p
  simp only [suspensionTranslate_apply, suspensionAct_eq]
  ring_nf

end Commute

section FlowMap

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

include hτ in
/-- The `ℝ`-translation `S t` respects the suspension orbit relation: if `p` and `q` are in the same
`ℤ`-orbit then so are `S t p` and `S t q`, with the *same* integer witness, by the commutation
`suspensionAct_translate`. This is the well-definedness obligation for the descended map
`suspensionMk ∘ S t`, phrased so that `≈` is the suspension orbit relation in scope. -/
theorem suspensionTranslate_orbitRel (t : ℝ) (p q : X × ℝ)
    (hpq : letI := suspensionAddAction T hτ; (AddAction.orbitRel ℤ (X × ℝ)).r p q) :
    suspensionMk T hτ (suspensionTranslate t p) = suspensionMk T hτ (suspensionTranslate t q) := by
  letI := suspensionAddAction T hτ
  have hpq' : ∃ n : ℤ, n +ᵥ q = p := hpq
  obtain ⟨n, hn⟩ := hpq'
  have hn' : suspensionAct T hτ n q = p := hn
  refine Quotient.sound ?_
  change ∃ n : ℤ, n +ᵥ suspensionTranslate t q = suspensionTranslate t p
  refine ⟨n, ?_⟩
  change suspensionAct T hτ n (suspensionTranslate t q) = suspensionTranslate t p
  rw [suspensionAct_translate T hτ n t q, hn']

/-- The **suspension flow map** `ζ_t : Xᵗ → Xᵗ`, the descent of the `ℝ`-translation `S t` through
the orbit quotient: `ζ_t [p] = [S t p]`. It is well-defined by `suspensionTranslate_orbitRel`. -/
def suspensionFlowMap (t : ℝ) : SuspensionSpace T hτ → SuspensionSpace T hτ :=
  letI := suspensionAddAction T hτ
  Quotient.lift (fun p => suspensionMk T hτ (suspensionTranslate t p))
    (fun p q h => suspensionTranslate_orbitRel T hτ t p q h)

/-- The descent identity: `ζ_t [p] = [S t p]`. -/
@[simp] theorem suspensionFlowMap_mk (t : ℝ) (p : X × ℝ) :
    suspensionFlowMap T hτ t (suspensionMk T hτ p) = suspensionMk T hτ (suspensionTranslate t p) :=
  rfl

/-- The time-zero flow map is the identity: `ζ_0 = id`. -/
@[simp] theorem suspensionFlowMap_zero : suspensionFlowMap T hτ 0 = id := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  change suspensionFlowMap T hτ 0 (suspensionMk T hτ p) = id (suspensionMk T hτ p)
  rw [suspensionFlowMap_mk, suspensionTranslate_zero, id]

/-- The flow maps are additive in time: `ζ_(s+t) = ζ_s ∘ ζ_t`. -/
theorem suspensionFlowMap_add (s t : ℝ) :
    suspensionFlowMap T hτ (s + t) = suspensionFlowMap T hτ s ∘ suspensionFlowMap T hτ t := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  change suspensionFlowMap T hτ (s + t) (suspensionMk T hτ p)
    = suspensionFlowMap T hτ s (suspensionFlowMap T hτ t (suspensionMk T hτ p))
  rw [suspensionFlowMap_mk, suspensionFlowMap_mk, suspensionFlowMap_mk, suspensionTranslate_add]

include hτ in
/-- Each suspension flow map `ζ_t` is measurable: it is the descent of the measurable translation
`S t`, and measurability out of a quotient is measurability of the composite with the quotient map
(`measurable_from_quotient`), which here equals `suspensionMk ∘ S t`. -/
theorem measurable_suspensionFlowMap (t : ℝ) : Measurable (suspensionFlowMap T hτ t) := by
  letI := suspensionAddAction T hτ
  refine measurable_from_quotient.2 ?_
  exact (measurable_suspensionMk T hτ).comp (measurable_suspensionTranslate t)

end FlowMap

end Oseledets
