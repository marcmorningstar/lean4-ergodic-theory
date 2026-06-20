/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionSpaceExponentValue

/-!
# Measurability of quotient images: discharging the suspension exponent `hmeas`

This module discharges the quotient-image measurability hypothesis `hmeas` carried as an explicit
input by `Oseledets.ae_suspensionMeasure_hasFlowExponent`
(`Oseledets.Continuous.SuspensionSpaceExponentValue`). That hypothesis asks that the *image* under
the quotient projection `suspensionMk` of a measurable base set is a `MeasurableSet` in the
suspension space `SuspensionSpace T hτ`. We prove this unconditionally from the measurable structure
of the orbit quotient, following the special-flow / mapping-torus model of Cornfeld–Fomin–Sinai,
*Ergodic Theory* (Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani).

## Construction

The suspension space carries the canonical *coinduced* measurable structure of an orbit quotient:
a set `U` in `SuspensionSpace T hτ` is measurable **iff** its preimage `suspensionMk ⁻¹' U` is
measurable (`measurableSet_quotient`). For an image `U = suspensionMk '' S`, the preimage is the
orbit-saturation

`suspensionMk ⁻¹' (suspensionMk '' S) = ⋃ n : ℤ, suspensionAct T hτ n '' S`

(`AddAction.quotient_preimage_image_eq_union_add` for the suspension orbit relation), a *countable*
union over `ℤ`. Each translate `suspensionAct T hτ n '' S` is measurable because `suspensionAct n`
is a measurable equivalence (`suspensionActEquiv`, with measurable inverse `suspensionAct (-n)`),
so the saturation is measurable and the image is measurable.

## Main results

* `Oseledets.suspensionActEquiv`: the suspension action `suspensionAct T hτ n` packaged as a
  `MeasurableEquiv` of `X × ℝ`, with inverse `suspensionAct T hτ (-n)`.
* `Oseledets.measurableSet_suspensionAct_image`: `S` measurable ⇒ `suspensionAct T hτ n '' S`
  measurable.
* `Oseledets.preimage_image_suspensionMk`: the orbit-saturation identity
  `suspensionMk ⁻¹' (suspensionMk '' S) = ⋃ n : ℤ, suspensionAct T hτ n '' S`.
* `Oseledets.measurableSet_suspensionMk_image`: `S` measurable ⇒ `suspensionMk T hτ '' S`
  measurable (the general quotient-image measurability lemma).
* `Oseledets.measurableSet_suspensionMk_exponent_image`: the specialisation discharging `hmeas` —
  the lifted exponent set of `ae_suspensionMeasure_hasFlowExponent` is measurable given the base
  exponent set is.

## gap

This is the unconditional measurability fact closing the explicit `hmeas` hypothesis of
`ae_suspensionMeasure_hasFlowExponent`; it does not itself re-derive that exponent theorem (the
statement still takes `hmeas` as an input — `measurableSet_suspensionMk_exponent_image` is the
term one supplies for it). No invariance or a.e.-statement is asserted here beyond the pure
measurability of the quotient image.
-/

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X]

section ActEquiv

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The suspension action `suspensionAct T hτ n` packaged as a **measurable equivalence** of
`X × ℝ`. Its inverse is `suspensionAct T hτ (-n)`: the two compose to `suspensionAct 0 = id` via
the cocycle identity `suspensionAct_add` and `suspensionAct_zero`. Both directions are measurable
by `measurable_suspensionAct`. -/
noncomputable def suspensionActEquiv (n : ℤ) : (X × ℝ) ≃ᵐ (X × ℝ) where
  toFun := suspensionAct T hτ n
  invFun := suspensionAct T hτ (-n)
  left_inv p := by
    rw [← suspensionAct_add, neg_add_cancel, suspensionAct_zero]
  right_inv p := by
    rw [← suspensionAct_add, add_neg_cancel, suspensionAct_zero]
  measurable_toFun := measurable_suspensionAct T hτ n
  measurable_invFun := measurable_suspensionAct T hτ (-n)

@[simp] theorem suspensionActEquiv_apply (n : ℤ) (p : X × ℝ) :
    suspensionActEquiv T hτ n p = suspensionAct T hτ n p := rfl

include hτ in
/-- The image of a measurable set under the suspension action `suspensionAct T hτ n` is measurable:
`suspensionAct n` is a measurable equivalence (`suspensionActEquiv`), hence a measurable embedding,
so it preserves measurability of images. -/
theorem measurableSet_suspensionAct_image (n : ℤ) {S : Set (X × ℝ)} (hS : MeasurableSet S) :
    MeasurableSet (suspensionAct T hτ n '' S) := by
  have himg : suspensionAct T hτ n '' S = suspensionActEquiv T hτ n '' S := rfl
  rw [himg]
  exact (suspensionActEquiv T hτ n).measurableEmbedding.measurableSet_image.mpr hS

end ActEquiv

section QuotientImage

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- **The orbit-saturation identity.** The preimage under the quotient projection `suspensionMk` of
the image `suspensionMk '' S` is the orbit-saturation of `S`: the countable union of the translates
`suspensionAct T hτ n '' S` over `n : ℤ`. This is
`AddAction.quotient_preimage_image_eq_union_add` for the suspension orbit relation, rewritten with
`suspensionAct = (n +ᵥ ·)`. -/
theorem preimage_image_suspensionMk (S : Set (X × ℝ)) :
    suspensionMk T hτ ⁻¹' (suspensionMk T hτ '' S) = ⋃ n : ℤ, suspensionAct T hτ n '' S := by
  letI := suspensionAddAction T hτ
  have hsat := AddAction.quotient_preimage_image_eq_union_add (G := ℤ) (α := X × ℝ) S
  -- `(n +ᵥ ·) = suspensionAct n` as functions, rewrite the saturation union into `suspensionAct`.
  have hact : ∀ n : ℤ, (fun p : X × ℝ => n +ᵥ p) = suspensionAct T hτ n := fun n =>
    funext fun p => suspension_vadd_eq_act T hτ n p
  simp only [hact] at hsat
  -- `suspensionMk = Quotient.mk'` for the suspension orbit relation, so the LHS matches `hsat`.
  exact hsat

include hτ in
/-- **General quotient-image measurability.** The image under the quotient projection `suspensionMk`
of a measurable set `S` in `X × ℝ` is a `MeasurableSet` in the suspension space.

A set in the orbit quotient is measurable iff its `suspensionMk`-preimage is measurable
(`measurableSet_quotient`, the coinduced structure). For `suspensionMk '' S` that preimage is the
orbit-saturation `⋃ n : ℤ, suspensionAct n '' S` (`preimage_image_suspensionMk`), a countable union
of measurable translates (`measurableSet_suspensionAct_image`), hence measurable. -/
theorem measurableSet_suspensionMk_image {S : Set (X × ℝ)} (hS : MeasurableSet S) :
    MeasurableSet (suspensionMk T hτ '' S) := by
  letI := suspensionAddAction T hτ
  -- A quotient set is measurable iff its `suspensionMk`-preimage is (coinduced structure).
  refine measurableSet_quotient (s := AddAction.orbitRel ℤ (X × ℝ))
    (t := suspensionMk T hτ '' S) |>.mpr ?_
  -- `Quotient.mk'' = suspensionMk`, so the preimage is the orbit-saturation: a countable union
  -- of measurable translates.
  have hpre : suspensionMk T hτ ⁻¹' (suspensionMk T hτ '' S)
      = ⋃ n : ℤ, suspensionAct T hτ n '' S := preimage_image_suspensionMk T hτ S
  change MeasurableSet (suspensionMk T hτ ⁻¹' (suspensionMk T hτ '' S))
  rw [hpre]
  exact MeasurableSet.iUnion fun n => measurableSet_suspensionAct_image T hτ n hS

end QuotientImage

section ExponentImage

variable {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X ≃ᵐ X) {τ : X → ℝ}
  (hτ : Measurable τ) {c : ℝ} (μ : Measure X) {lam : ℝ}

open Filter Topology in
include hτ in
/-- **Discharging `hmeas`.** The lifted exponent set of `ae_suspensionMeasure_hasFlowExponent`,

`{q | ∃ p, suspensionMk p = q ∧ <section exponent at p.1>}`,

is exactly the image under `suspensionMk` of the base exponent set
`{p : X × ℝ | <section exponent at p.1>}`; that base set is the measurable cylinder over the base
exponent set `hPmeas` (it ignores the `ℝ`-coordinate), so its quotient image is measurable by
`measurableSet_suspensionMk_image`. This is the `MeasurableSet` term one supplies for the `hmeas`
hypothesis of `ae_suspensionMeasure_hasFlowExponent`. -/
theorem measurableSet_suspensionMk_exponent_image (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hPmeas : MeasurableSet
      {x : X | Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
        atTop (𝓝 (lam / ∫ y, τ y ∂μ))}) :
    MeasurableSet
      {q : SuspensionSpace T hτ | ∃ p : X × ℝ, suspensionMk T hτ p = q ∧
        Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (p.1, 0) t‖ / t)
          atTop (𝓝 (lam / ∫ y, τ y ∂μ))} := by
  -- The base set, as a subset of `X × ℝ`: the section exponent depends only on the first
  -- coordinate, so it is the preimage of the base exponent set under `Prod.fst`.
  set P : Set X :=
    {x : X | Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
      atTop (𝓝 (lam / ∫ y, τ y ∂μ))} with hP
  have hbase : MeasurableSet (Prod.fst ⁻¹' P : Set (X × ℝ)) :=
    measurable_fst hPmeas
  -- The lifted quotient set is the image of that base cylinder under `suspensionMk`.
  have himg : {q : SuspensionSpace T hτ | ∃ p : X × ℝ, suspensionMk T hτ p = q ∧
      Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (p.1, 0) t‖ / t)
        atTop (𝓝 (lam / ∫ y, τ y ∂μ))}
      = suspensionMk T hτ '' (Prod.fst ⁻¹' P) := by
    ext q
    constructor
    · rintro ⟨p, hpq, hp⟩
      exact ⟨p, hp, hpq⟩
    · rintro ⟨p, hp, hpq⟩
      exact ⟨p, hpq, hp⟩
  rw [himg]
  exact measurableSet_suspensionMk_image T hτ hbase

end ExponentImage

end Oseledets
