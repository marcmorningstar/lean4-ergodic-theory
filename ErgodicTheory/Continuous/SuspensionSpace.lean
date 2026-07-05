/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionMeasure

/-!
# The suspension quotient space and its invariant probability measure

This module assembles the *suspension* (mapping-torus) measure space from the fundamental-domain
keystone of `ErgodicTheory.Continuous.Suspension` and the measure facts of
`ErgodicTheory.Continuous.SuspensionMeasure`. The suspension space is the quotient of `X × ℝ` by the
suspension `ℤ`-action `G (x, s) = (T x, s − τ x)`, i.e. the mapping torus of the base map `T` under
the roof function `τ`.

## Construction

The suspension space is the orbit quotient

`SuspensionSpace T hτ := Quotient (AddAction.orbitRel ℤ (X × ℝ))`,

for the action `suspensionAddAction T hτ` of `ErgodicTheory.Continuous.Suspension`.
As a `Quotient` it
carries the canonical pushforward `MeasurableSpace` instance for free.

Its measure is built by *restricting* `μ × volume` to the fundamental box `suspensionDomain τ` and
pushing forward along the quotient map `π = Quotient.mk`:

`suspensionMeasure₀ := ((μ × volume).restrict (suspensionDomain τ)).map π`.

The total mass of this raw measure equals `ENNReal.ofReal (∫ x, τ x ∂μ)` (the box mass, since `π`
is surjective so `π ⁻¹' univ = univ`). Normalising by `(∫ τ)⁻¹` produces the invariant probability
measure `suspensionMeasure`.

## Main definitions

* `ErgodicTheory.SuspensionSpace`: the suspension quotient
  `Quotient (AddAction.orbitRel ℤ (X × ℝ))`.
* `ErgodicTheory.suspensionMeasure₀`: the raw pushforward measure `(restrict box).map π`.
* `ErgodicTheory.suspensionMeasure`: the normalised invariant probability measure
  `(∫ τ)⁻¹ • suspensionMeasure₀`.

## Main results

* `ErgodicTheory.suspensionMeasure₀_univ`: `suspensionMeasure₀ univ = ENNReal.ofReal (∫ x, τ x ∂μ)`.
* `ErgodicTheory.isProbabilityMeasure_suspensionMeasure`: with `0 < ∫ τ` and `Integrable τ`, the
  normalised measure `suspensionMeasure` is a probability measure.

## What is *not* in this file

The per-time measure-preservation of the suspension flow `ζ_t [x, s] = [x, s + t]` through the
quotient — the descent of the `ℝ`-translation via the fundamental domain (the
`IsAddFundamentalDomain.measurePreserving_quotient`-style argument) and its packaging as a
`MeasurePreservingFlow` — is left to a follow-up module. Establishing it requires transporting the
fundamental-domain measure-preservation of the `ℝ`-translation through the quotient map, which is a
separate piece of infrastructure. This file stops at the invariant probability measure, which is
self-contained and sorry-free.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

section Space

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The **suspension (mapping-torus) space** of the base map `T` under the roof function `τ`: the
orbit quotient of `X × ℝ` by the suspension `ℤ`-action `G (x, s) = (T x, s − τ x)`.

The action is the locally-activated `suspensionAddAction T hτ` of
`ErgodicTheory.Continuous.Suspension`;
it is brought into scope by `letI` so that `AddAction.orbitRel ℤ (X × ℝ)` is the suspension orbit
relation. As a `Quotient` the space carries the canonical pushforward `MeasurableSpace` instance. -/
def SuspensionSpace : Type _ :=
  letI := suspensionAddAction T hτ
  Quotient (AddAction.orbitRel ℤ (X × ℝ))

/-- The canonical `MeasurableSpace` on the suspension space, pushed forward from `X × ℝ` along the
quotient map. This is `Quotient.instMeasurableSpace` for the suspension orbit relation. -/
instance : MeasurableSpace (SuspensionSpace T hτ) :=
  letI := suspensionAddAction T hτ
  (inferInstance : MeasurableSpace (Quotient (AddAction.orbitRel ℤ (X × ℝ))))

/-- The quotient projection `π : X × ℝ → SuspensionSpace T hτ`, `π p = [p]`. -/
def suspensionMk (p : X × ℝ) : SuspensionSpace T hτ :=
  letI := suspensionAddAction T hτ
  Quotient.mk (AddAction.orbitRel ℤ (X × ℝ)) p

include hτ in
/-- The quotient projection `suspensionMk` is measurable (it is `Quotient.mk`, which is measurable
for the pushforward `MeasurableSpace` on the quotient). -/
theorem measurable_suspensionMk : Measurable (suspensionMk T hτ) := by
  letI := suspensionAddAction T hτ
  unfold suspensionMk SuspensionSpace
  exact measurable_quotient_mk' (s := AddAction.orbitRel ℤ (X × ℝ))

end Space

section Measure

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) (μ : Measure X)

/-- The **raw suspension measure**: restrict the product measure `μ × volume` to the fundamental
box `suspensionDomain τ` and push it forward along the quotient projection `suspensionMk`. Its
normalisation (see `suspensionMeasure`) is the suspension's invariant probability measure. -/
noncomputable def suspensionMeasure₀ : Measure (SuspensionSpace T hτ) :=
  ((μ.prod volume).restrict (suspensionDomain τ)).map (suspensionMk T hτ)

include hτ in
/-- The total mass of the raw suspension measure equals the box mass `(μ × volume) (box)`.

The quotient map `π` is total, so `π ⁻¹' univ = univ`; hence `((restrict box).map π) univ
= (restrict box) univ = (μ × volume) box` by `Measure.map_apply` and `Measure.restrict_apply_univ`.
-/
theorem suspensionMeasure₀_univ_eq_measure_box :
    suspensionMeasure₀ T hτ μ univ = (μ.prod volume) (suspensionDomain τ) := by
  rw [suspensionMeasure₀,
    Measure.map_apply (measurable_suspensionMk T hτ) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

include hτ in
/-- The total mass of the raw suspension measure equals `ENNReal.ofReal (∫ x, τ x ∂μ)`, for a
nonnegative integrable roof function `τ`. This is the box mass `measure_suspensionDomain` pushed
through the quotient. -/
theorem suspensionMeasure₀_univ [SFinite μ] (hτ_nonneg : ∀ x, 0 ≤ τ x)
    (hτ_int : Integrable τ μ) :
    suspensionMeasure₀ T hτ μ univ = ENNReal.ofReal (∫ x, τ x ∂μ) := by
  rw [suspensionMeasure₀_univ_eq_measure_box T hτ μ,
    measure_suspensionDomain hτ hτ_nonneg hτ_int]

/-- The **suspension invariant probability measure**: the raw measure `suspensionMeasure₀`
normalised by the reciprocal of its total mass `(∫ τ)⁻¹`. When `0 < ∫ τ` (so the mass is positive)
and `τ` is integrable (so the mass is finite), this is a probability measure
(`isProbabilityMeasure_suspensionMeasure`). -/
noncomputable def suspensionMeasure : Measure (SuspensionSpace T hτ) :=
  (ENNReal.ofReal (∫ x, τ x ∂μ))⁻¹ • suspensionMeasure₀ T hτ μ

include hτ in
/-- The suspension invariant probability measure has total mass `1`: with `0 < ∫ τ` (positive mass)
and `τ` integrable (finite mass), `(∫ τ)⁻¹ • suspensionMeasure₀` evaluates to `1` on `univ` via
`ENNReal.inv_mul_cancel`. -/
theorem suspensionMeasure_univ [SFinite μ] (hτ_nonneg : ∀ x, 0 ≤ τ x)
    (hτ_int : Integrable τ μ) (hτ_pos : 0 < ∫ x, τ x ∂μ) :
    suspensionMeasure T hτ μ univ = 1 := by
  have hmass : suspensionMeasure₀ T hτ μ univ = ENNReal.ofReal (∫ x, τ x ∂μ) :=
    suspensionMeasure₀_univ T hτ μ hτ_nonneg hτ_int
  have hne0 : ENNReal.ofReal (∫ x, τ x ∂μ) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hτ_pos
  rw [suspensionMeasure, Measure.smul_apply, hmass, smul_eq_mul,
    ENNReal.inv_mul_cancel hne0 ENNReal.ofReal_ne_top]

include hτ in
/-- With `0 < ∫ τ` and `τ` integrable, the normalised `suspensionMeasure` is a probability measure.
-/
theorem isProbabilityMeasure_suspensionMeasure [SFinite μ] (hτ_nonneg : ∀ x, 0 ≤ τ x)
    (hτ_int : Integrable τ μ) (hτ_pos : 0 < ∫ x, τ x ∂μ) :
    IsProbabilityMeasure (suspensionMeasure T hτ μ) :=
  ⟨suspensionMeasure_univ T hτ μ hτ_nonneg hτ_int hτ_pos⟩

end Measure

end ErgodicTheory
