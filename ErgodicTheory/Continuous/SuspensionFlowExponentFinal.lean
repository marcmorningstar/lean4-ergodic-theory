/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlowExponentValue
import ErgodicTheory.Continuous.SuspensionExponentSetMeasurable

/-!
# The fully unconditional space-level special-flow exponent

This module removes the *last* explicit measurability hypothesis, `hPmeas`, from the space-level
special-flow Lyapunov-exponent headline, making the result **fully unconditional** in its
measurability data: it is now driven only by `hA : Measurable A` (the measurability of the base
cocycle generator) together with the bounded-roof and a.e.-Birkhoff hypotheses.

The previous unconditional headline
`ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_unconditional`
(`ErgodicTheory.Continuous.SuspensionFlowExponentValue`) had already discharged the quotient-image
measurability `hmeas`, but still carried the *base* exponent-set measurability

`hPmeas : MeasurableSet {x | Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t → λ_base/∫τ}`

as an explicit input, because the cover cocycle has no in-library measurability-in-`x` lemma. That
hypothesis is now supplied internally by `measurableSet_coverCocycle_exponent`
(`ErgodicTheory.Continuous.SuspensionExponentSetMeasurable`), which proves the exponent
set measurable
by rewriting it — pointwise — as the discrete return-time exponent set (the between-returns squeeze)
and invoking `MeasureTheory.measurableSet_tendsto`. Threading `hA` through closes the gap.

This is the Lyapunov-exponent analogue of Abramov's entropy formula `h(flow) = h(base)/∫τ`
(L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875), in the
special-flow / flow-under-a-roof setting of Cornfeld–Fomin–Sinai, *Ergodic Theory* (Springer 1982),
Ch. 11 (special/suspension flows; Ambrose–Kakutani).

## Main results

* `ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_of_measurable`: the **fully unconditional**
  space-level headline. Same conclusion as
  `ae_suspensionMeasure_hasFlowExponent_unconditional` but with `hPmeas` replaced by
  `hA : Measurable A`; for `μ̂ = suspensionMeasure`-a.e. orbit class `q`,
  `HasFlowExponent q (λ_base / ∫τ)`.
* `ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_flowOrbit_of_measurable`: the **flow-tied**
  corollary, likewise with `hPmeas` replaced by `hA`. For `μ̂`-a.e. `q`, `q` lies on the
  `suspensionFlow`-orbit of a base cross-section point and carries the flow exponent
  `λ_base / ∫τ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}

section Final

variable {μ : Measure X} [SFinite μ] {lam : ℝ}

include hτ in
/-- **The fully unconditional space-level special-flow Lyapunov exponent.** (`HasFlowExponent` is
existential over representatives: for `μ̂`-a.e. class *some* representative realises `λ_base / ∫τ`;
cross-representative uniqueness needs base-cocycle invertibility.) This is
`ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_unconditional` with the explicit
base exponent-set
measurability hypothesis `hPmeas` replaced by `hA : Measurable A`. Under a bounded roof
`c ≤ τ ≤ C` (`0 < c`), positive integral `0 < ∫τ`, measurable base cocycle generator `A`, and the
base-a.e. Birkhoff limits — discrete base growth rate `→ λ_base` and roof average `→ ∫τ` — for
`μ̂ = suspensionMeasure`-almost every orbit class `q ∈ SuspensionSpace`, the flow exponent equals
`λ_base / ∫τ`: `∀ᵐ q ∂μ̂, HasFlowExponent q (λ_base / ∫τ)`.

The base exponent-set measurability is supplied internally by
`measurableSet_coverCocycle_exponent` (`ErgodicTheory.Continuous.SuspensionExponentSetMeasurable`):
the
full-time cover-cocycle exponent set is rewritten — pointwise — as the discrete return-time exponent
set (the between-returns squeeze) and is measurable by `MeasureTheory.measurableSet_tendsto`. So no
measurability datum beyond `Measurable A` need be assumed. -/
theorem ae_suspensionMeasure_hasFlowExponent_of_measurable (hA : Measurable A) (hc : ∀ x, c ≤ τ x)
    (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ,
      HasFlowExponent A T hτ hc hcpos q (lam / ∫ y, τ y ∂μ) :=
  ae_suspensionMeasure_hasFlowExponent_unconditional A T hτ hc hcpos hC
    (measurableSet_coverCocycle_exponent hA T hτ hc hcpos hC (lam / ∫ y, τ y ∂μ))
    hgrow hroof hτ_pos

include hτ in
/-- **The fully unconditional space-level exponent, tied to the genuine measure-preserving flow.**
This is `ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_flowOrbit` with the explicit base
exponent-set measurability hypothesis `hPmeas` replaced by `hA : Measurable A`. For `μ̂`-almost
every orbit class `q ∈ SuspensionSpace`, `q` lies on the `suspensionFlow`-orbit of a base
cross-section point and carries the flow exponent `λ_base / ∫τ`: there are `x : X` and a flow time
`s : ℝ` with

`q = suspensionFlow hT hc hcpos s (suspensionSection x)`  and  `HasFlowExponent q (λ_base / ∫τ)`.

The base exponent-set measurability is supplied internally by
`measurableSet_coverCocycle_exponent` as in
`ae_suspensionMeasure_hasFlowExponent_of_measurable`. -/
theorem ae_suspensionMeasure_hasFlowExponent_flowOrbit_of_measurable (hA : Measurable A)
    (hT : MeasurePreserving T μ μ) (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ, ∃ (x : X) (s : ℝ),
      q = suspensionFlow T hτ hT hc hcpos s (suspensionSection T hτ x) ∧
        HasFlowExponent A T hτ hc hcpos q (lam / ∫ y, τ y ∂μ) :=
  ae_suspensionMeasure_hasFlowExponent_flowOrbit A T hτ hT hc hcpos hC
    (measurableSet_coverCocycle_exponent hA T hτ hc hcpos hC (lam / ∫ y, τ y ∂μ))
    hgrow hroof hτ_pos

end Final

end ErgodicTheory
