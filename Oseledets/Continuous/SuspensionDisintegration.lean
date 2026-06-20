/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionMeasureTransfer

/-!
# Transferring base-a.e. facts to the suspension measure

This module supplies the **measure-transfer bridge** that promotes almost-everywhere statements
about the fundamental box `suspensionDomain τ ⊆ X × ℝ` (against the restricted product measure
`(μ × volume)|_𝓕`) and base-a.e. statements about `X` (against `μ`) to almost-everywhere statements
on the suspension quotient space `Oseledets.SuspensionSpace` (against its invariant probability
measure `Oseledets.suspensionMeasure`). It is the disintegration / fundamental-domain Fubini
correspondence flagged as the open keystone in `Oseledets.Continuous.SuspensionMeasureTransfer`.

This is the measure-theoretic half of the Ambrose–Kakutani special-flow / flow-under-a-roof
construction of Cornfeld–Fomin–Sinai, *Ergodic Theory* (Springer 1982), Ch. 11 (special/suspension
flows), the disintegration underlying Abramov's entropy formula `h(flow) = h(base)/∫τ`
(L.M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875). The
Lyapunov-exponent analogue `λ_flow = λ_base / ∫τ` is the headline of Issue #5.

## The transfer chain

The suspension measure is `μ̂ = (∫τ)⁻¹ · π_* ((μ × volume)|_𝓕)` for the quotient projection
`π = suspensionMk` and the fundamental box `𝓕 = suspensionDomain τ`. Two elementary measure facts
move almost-everywhere statements along this construction:

* **Push-forward + normalisation** (`suspensionMeasure_ae_iff`,
  `ae_suspensionMeasure_of_ae_restrict`): for a measurable property `Q` of the quotient,
  `μ̂`-a.e.-`Q` is equivalent to `(μ × volume)|_𝓕`-a.e.-`Q ∘ π` (when `0 < ∫τ`). Pushing forward
  turns `μ̂`-a.e. into a box-a.e. statement via `MeasureTheory.ae_map_iff` (`π` is measurable), and
  the `(∫τ)⁻¹` normalisation is irrelevant to the `ae` filter because `(∫τ)⁻¹` is nonzero and finite
  (`MeasureTheory.Measure.ae_smul_measure_le` in both directions; `0 < ∫τ` so `(∫τ)⁻¹ ≠ 0`, and
  `ENNReal.ofReal _ ≠ ∞` so `∫τ • (∫τ)⁻¹ • · ` cancels back).

* **Fubini over the box** (`ae_restrict_suspensionDomain_of_ae_base`): a base-`μ`-a.e. property of
  `x` that does **not** depend on the flow height `s` lifts to a `(μ × volume)|_𝓕`-a.e. property of
  `(x, s)`. A base-a.e. fact spreads over the whole product `μ × volume`
  (`MeasureTheory.ae_prod_iff_ae_ae`, the inner `s`-quantifier being vacuous), and restricting to
  the box only shrinks the measure (`MeasureTheory.ae_restrict_of_ae`).

Composing the two transfers a base-`μ`-a.e. property of `x` (which factors through the cross-section
coordinate `p.1`) all the way to a `μ̂`-a.e. property on `SuspensionSpace`
(`ae_suspensionMeasure_of_ae_base`).

## Main results

* `Oseledets.suspensionMeasure_ae_iff`: `μ̂`-a.e.-`Q` ↔ box-a.e.-`Q ∘ π`, for measurable `Q`.
* `Oseledets.ae_suspensionMeasure_of_ae_restrict`: box-a.e.-`Q ∘ π` ⇒ `μ̂`-a.e.-`Q`.
* `Oseledets.ae_restrict_suspensionDomain_of_ae_base`: base-`μ`-a.e.-`P` ⇒ box-a.e.-`P ∘ fst`.
* `Oseledets.ae_suspensionMeasure_of_ae_base`: base-`μ`-a.e.-`(Q ∘ π factored through fst)` ⇒
  `μ̂`-a.e.-`Q`.
* `Oseledets.ae_suspensionMeasure_section_exponent_set`: the composition applied to the
  bounded-roof headline — the base-a.e. cross-section exponent set lifts to a `μ̂`-a.e. set on
  `SuspensionSpace`.

## What is *not* in this file — the precise remaining gap

The lifted `μ̂`-a.e. statement of `ae_suspensionMeasure_section_exponent_set` asserts, for `μ̂`-a.e.
`q = [x, s] ∈ SuspensionSpace`, that the **base representative** `x` of the orbit class has the
section exponent `Real.log ‖coverCocycle (x, 0) t‖ / t → λ_base / ∫τ`. This is the genuine
transfer of the base-a.e. *set* to a `μ̂`-a.e. *set*. What it does **not** yet provide is an
exponent function defined intrinsically on `SuspensionSpace` whose value at `q` is read without
naming a representative: that needs the **flow-cocycle descent** — a `FlowCocycle` over
`SuspensionSpace`. As documented in `Oseledets.Continuous.SuspensionMeasureTransfer`, the matrix
cover cocycle does not descend to the quotient (the orbit gluing `(x, τ x) ∼ (T x, 0)` re-bases the
accumulated matrix by the base step `A x`), so only the scalar growth rate is orbit-invariant; the
representative-free exponent function on `SuspensionSpace` requires that growth-rate descent, which
is the remaining open piece. The measure transfer of the underlying a.e. set — the heavy
disintegration infrastructure that `SuspensionMeasureTransfer` flagged as missing — is what this
module supplies.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X]

section Transfer

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) (μ : Measure X)

include hτ in
/-- **Push-forward + normalisation a.e. bridge.** For a measurable property `Q` of the suspension
quotient, holding `μ̂`-a.e. is equivalent to `Q ∘ suspensionMk` holding `(μ × volume)|_𝓕`-a.e. on
the fundamental box `𝓕 = suspensionDomain τ`.

Two steps: the `(∫τ)⁻¹` normalisation is invisible to the `ae` filter — with `0 < ∫τ` the scalar
`(∫τ)⁻¹` is nonzero (so `ae (I⁻¹ • ν) ≤ ae ν` by `MeasureTheory.Measure.ae_smul_measure_le`) and
finite (so `ν = I • (I⁻¹ • ν)`, giving the reverse `ae ν ≤ ae (I⁻¹ • ν)` by a second
`ae_smul_measure_le`); hence `ae μ̂ = ae μ̂₀`. The push-forward along the measurable quotient map
`suspensionMk` then turns the `ae` of `π_* ν` into the `ae` of `ν` on the pulled-back property, via
`MeasureTheory.ae_map_iff`. -/
theorem suspensionMeasure_ae_iff (hτ_pos : 0 < ∫ x, τ x ∂μ) {Q : SuspensionSpace T hτ → Prop}
    (hQ : MeasurableSet {q | Q q}) :
    (∀ᵐ q ∂suspensionMeasure T hτ μ, Q q) ↔
      ∀ᵐ p ∂(μ.prod volume).restrict (suspensionDomain τ), Q (suspensionMk T hτ p) := by
  set ν : Measure (SuspensionSpace T hτ) := suspensionMeasure₀ T hτ μ with hν
  set I : ℝ≥0∞ := ENNReal.ofReal (∫ x, τ x ∂μ) with hI
  have hIne : I ≠ 0 := by rw [hI, Ne, ENNReal.ofReal_eq_zero, not_le]; exact hτ_pos
  have hItop : I ≠ ∞ := by rw [hI]; exact ENNReal.ofReal_ne_top
  -- `I • (I⁻¹ • ν) = ν`: the scalars cancel because `I ≠ 0, ∞`.
  have hcancel : I • (I⁻¹ • ν) = ν := by
    rw [smul_smul, ENNReal.mul_inv_cancel hIne hItop, one_smul]
  -- `ae` of the normalised measure equals `ae` of the raw measure (both inclusions via smul-le).
  have hae : ae (I⁻¹ • ν) = ae ν := by
    refine le_antisymm (Measure.ae_smul_measure_le _) ?_
    conv_lhs => rw [← hcancel]
    exact Measure.ae_smul_measure_le I
  rw [suspensionMeasure, ← hI, ← hν, Filter.eventually_iff, hae, ← Filter.eventually_iff,
    hν, suspensionMeasure₀, ae_map_iff (measurable_suspensionMk T hτ).aemeasurable hQ]

include hτ in
/-- **Push-forward + normalisation transfer.** A measurable property `Q` of the suspension quotient
that holds `(μ × volume)|_𝓕`-a.e. after pulling back along `suspensionMk` holds `μ̂`-a.e. This is
the forward direction of `suspensionMeasure_ae_iff`, the genuine reusable bridge from box-a.e. to
suspension-measure-a.e. -/
theorem ae_suspensionMeasure_of_ae_restrict (hτ_pos : 0 < ∫ x, τ x ∂μ)
    {Q : SuspensionSpace T hτ → Prop} (hQ : MeasurableSet {q | Q q})
    (h : ∀ᵐ p ∂(μ.prod volume).restrict (suspensionDomain τ), Q (suspensionMk T hτ p)) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ, Q q :=
  (suspensionMeasure_ae_iff T hτ μ hτ_pos hQ).2 h

/-- **Fubini over the box: lifting a base-a.e. fact to the fundamental domain.** A base-`μ`-a.e.
property `P` of `x ∈ X` lifts to a `(μ × volume)|_𝓕`-a.e. property of `(x, s)`, where the lift only
reads the cross-section coordinate `p.1` and ignores the flow height `p.2`.

A base-a.e. fact spreads over the whole product `μ × volume` (`MeasureTheory.ae_prod_iff_ae_ae`,
since the inner `s`-quantifier is vacuous: `P p.1` does not depend on `s`); restricting to the box
`𝓕` only shrinks the measure (`MeasureTheory.ae_restrict_of_ae`). `SFinite μ` is needed for the
product-measure Fubini a.e. lemma. (This step needs neither the base map `T` nor the roof
measurability `hτ` — only the roof `τ` itself, to name the box `suspensionDomain τ`.) -/
theorem ae_restrict_suspensionDomain_of_ae_base [SFinite μ] {P : X → Prop}
    (hP : MeasurableSet {x | P x}) (h : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ p ∂(μ.prod volume).restrict (suspensionDomain τ), P p.1 := by
  have hmeas : MeasurableSet {p : X × ℝ | P p.1} := measurable_fst hP
  have hprod : ∀ᵐ p ∂μ.prod volume, P p.1 :=
    (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := volume) hmeas).2
      (h.mono fun x hx => ae_of_all _ fun _ => hx)
  exact ae_restrict_of_ae hprod

include hτ in
/-- **The composed disintegration transfer.** A base-`μ`-a.e. property of `x` that determines a
measurable property `Q` of the suspension quotient through the cross-section coordinate — i.e.
`Q (suspensionMk (x, s))` is implied by `P x` for every `s` — lifts to `μ̂`-a.e.-`Q` on
`SuspensionSpace`. This chains `ae_restrict_suspensionDomain_of_ae_base` (base-a.e. ⇒ box-a.e.)
with `ae_suspensionMeasure_of_ae_restrict` (box-a.e. ⇒ suspension-a.e.). -/
theorem ae_suspensionMeasure_of_ae_base [SFinite μ] (hτ_pos : 0 < ∫ x, τ x ∂μ) {P : X → Prop}
    {Q : SuspensionSpace T hτ → Prop} (hP : MeasurableSet {x | P x}) (hQ : MeasurableSet {q | Q q})
    (hPQ : ∀ p : X × ℝ, P p.1 → Q (suspensionMk T hτ p)) (h : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ, Q q := by
  refine ae_suspensionMeasure_of_ae_restrict T hτ μ hτ_pos hQ ?_
  have hbox := ae_restrict_suspensionDomain_of_ae_base (τ := τ) μ hP h
  exact hbox.mono fun p hp => hPQ p hp

end Transfer

section HeadlineTransfer

variable {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X ≃ᵐ X) {τ : X → ℝ}
  (hτ : Measurable τ) {c C : ℝ}

include hτ in
/-- **The bounded-roof cross-section exponent set lifts to a `μ̂`-a.e. set.** Specialising the
disintegration transfer `ae_suspensionMeasure_of_ae_base` to the bounded-roof headline
`coverCocycle_tendsto_exponent_of_bddRoof`: the base-`μ`-a.e. set of points carrying the
cover-cocycle log-norm growth rate `λ_base / ∫τ` lifts to a `μ̂`-a.e. set of orbit classes
`q ∈ SuspensionSpace`. For `μ̂`-a.e. `q`, *some* box representative `(x, s)` with
`q = suspensionMk (x, s)` has a first coordinate `x` carrying the section exponent
`Real.log ‖coverCocycle (x, 0) t‖ / t → λ_base / ∫τ`.

This is the `μ̂`-a.e. transfer of the underlying a.e. **set** toward the space-level headline of
Issue #5. The exponent *value* as a representative-free function on `SuspensionSpace` still needs
the flow-cocycle growth-rate descent (see the module header); this lemma supplies the measure
transfer of the set, the disintegration that `SuspensionMeasureTransfer` flagged as missing.

The lifted property is stated existentially over a representative `(x, s)` of the class so that
`hPQ` (a base-a.e. point is its own representative) is immediate; the caller supplies the
measurability `hPmeas` of the base exponent set and `hmeas` of its lifted image (the quotient image
of a measurable set is not measurable for free — that is exactly the disintegration data this lemma
consumes rather than re-derives). -/
theorem ae_suspensionMeasure_section_exponent_set (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hC : ∀ x, τ x ≤ C) {μ : Measure X} [SFinite μ] {lam : ℝ}
    (hPmeas : MeasurableSet
      {x : X | Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
        atTop (𝓝 (lam / ∫ y, τ y ∂μ))})
    (hmeas : MeasurableSet
      {q : SuspensionSpace T hτ | ∃ p : X × ℝ, suspensionMk T hτ p = q ∧
        Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (p.1, 0) t‖ / t)
          atTop (𝓝 (lam / ∫ y, τ y ∂μ))})
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ,
      ∃ p : X × ℝ, suspensionMk T hτ p = q ∧
        Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (p.1, 0) t‖ / t)
          atTop (𝓝 (lam / ∫ y, τ y ∂μ)) := by
  have hτne : (∫ y, τ y ∂μ) ≠ 0 := ne_of_gt hτ_pos
  have hbase : ∀ᵐ x ∂μ,
      Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
        atTop (𝓝 (lam / ∫ y, τ y ∂μ)) :=
    coverCocycle_tendsto_exponent_of_bddRoof A T hτ hc hcpos hC hgrow hroof hτne
  exact ae_suspensionMeasure_of_ae_base T hτ μ hτ_pos hPmeas hmeas (fun p hp => ⟨p, rfl, hp⟩) hbase

end HeadlineTransfer

end Oseledets
