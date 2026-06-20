/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionQuotientImage

/-!
# The unconditional space-level special-flow exponent, tied to the suspension flow

This module removes the explicit quotient-image measurability hypothesis `hmeas` from the
space-level special-flow Lyapunov-exponent headline
`Oseledets.ae_suspensionMeasure_hasFlowExponent`
(`Oseledets.Continuous.SuspensionSpaceExponentValue`) and ties the resulting `μ̂`-a.e. flow
exponent to the genuine measure-preserving flow `Oseledets.suspensionFlow`
(`Oseledets.Continuous.SuspensionFlowMP`).

The headline `ae_suspensionMeasure_hasFlowExponent` produced, for `μ̂ = suspensionMeasure`-almost
every orbit class `q ∈ SuspensionSpace T hτ`, the flow exponent value `HasFlowExponent q
(λ_base / ∫τ)` — the Lyapunov analogue of Abramov's entropy formula `h(flow) = h(base)/∫τ`
(L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875), in the
special-flow / flow-under-a-roof setting of Cornfeld–Fomin–Sinai, *Ergodic Theory* (Springer 1982),
Ch. 11 (special/suspension flows; Ambrose–Kakutani). That statement, however, still carried the
quotient-image measurability of the lifted exponent set, `hmeas`, as an explicit input.

`Oseledets.Continuous.SuspensionQuotientImage` discharges exactly that input unconditionally
(`measurableSet_suspensionMk_exponent_image`: the quotient image of the measurable base exponent
cylinder is measurable). Feeding it in removes `hmeas` from the signature.

## Tying to the genuine flow

`HasFlowExponent q L` asserts that *some* representative `(x, s)` of the orbit class `q` carries the
cover-cocycle growth rate `L`. Via the cross-section embedding `suspensionSection x = [x, 0]` and
the flow identity `ζ_t [x, 0] = [x, t]` (`suspensionFlowMap_section`), that representative is the
genuine flow image `q = ζ_s (suspensionSection x)` of a cross-section point under the
`MeasurePreservingFlow` `suspensionFlow`. The corollary
`ae_suspensionMeasure_hasFlowExponent_flowOrbit` records that, for `μ̂`-a.e. `q`, `q` lies on the
`suspensionFlow`-orbit of a base cross-section point *and* carries the flow exponent `λ_base / ∫τ`
— phrasing the a.e. exponent against the actual flow object.

## Main results

* `Oseledets.ae_suspensionMeasure_hasFlowExponent_unconditional`: the **unconditional** space-level
  headline. Same statement as `ae_suspensionMeasure_hasFlowExponent` but with the quotient-image
  measurability hypothesis `hmeas` discharged (via Module 1); for `μ̂`-a.e. `q ∈ SuspensionSpace`,
  `HasFlowExponent q (λ_base / ∫τ)`.
* `Oseledets.ae_suspensionMeasure_hasFlowExponent_flowOrbit`: the **flow-tied** corollary. For
  `μ̂`-a.e. `q`, there is a base point `x` and a flow time `s` with `q = suspensionFlow s
  (suspensionSection x)` (the genuine `MeasurePreservingFlow` orbit of a cross-section point) and
  `HasFlowExponent q (λ_base / ∫τ)`.

## gap

The unconditional headline still carries the **base** exponent-set measurability `hPmeas` (that
`{x | log ‖coverCocycle (x, 0) t‖ / t → λ_base/∫τ}` is measurable): the base cover-cocycle has no
in-library measurability-in-`x` lemma (`coverCocycle` is not yet packaged as a measurable function
of its base point — the open keystone noted in `SuspensionNlap`), so this datum cannot be discharged
here and is kept explicit. Only the *quotient-image* hypothesis `hmeas`, which Module 1 settles
unconditionally from the orbit-saturation structure, is removed. The flow-tied corollary expresses
the a.e. exponent as a property of `suspensionFlow`-orbit points but does not restate the exponent
as a `FlowCocycle` norm-growth over `SuspensionSpace`: the matrix cover cocycle does not descend to
the
quotient (only its scalar growth rate is orbit-invariant), so a `μ̂`-a.e. flow-cocycle statement
would need the absent measurable quotient cocycle; this is left to the `FlowCocycle` keystone.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}

section Unconditional

variable {μ : Measure X} [SFinite μ] {lam : ℝ}

include hτ in
/-- **The unconditional space-level special-flow Lyapunov exponent.** This is
`Oseledets.ae_suspensionMeasure_hasFlowExponent` with its quotient-image measurability hypothesis
`hmeas` removed: under a bounded roof `c ≤ τ ≤ C` (`0 < c`), positive integral `0 < ∫τ`, the
base exponent-set measurability `hPmeas`, and the base-a.e. Birkhoff limits — discrete base growth
rate `→ λ_base` and roof average `→ ∫τ` — for `μ̂ = suspensionMeasure`-almost every orbit class
`q ∈ SuspensionSpace`, the flow exponent equals `λ_base / ∫τ`:
`∀ᵐ q ∂μ̂, HasFlowExponent q (λ_base / ∫τ)`.

The discharged hypothesis is supplied by `measurableSet_suspensionMk_exponent_image`
(`Oseledets.Continuous.SuspensionQuotientImage`): the lifted exponent set on the quotient is the
`suspensionMk`-image of the measurable base cylinder `Prod.fst ⁻¹' P`, measurable by the
orbit-saturation structure of the quotient — so no quotient-image datum need be assumed. (`hPmeas`
remains: the base cover-cocycle carries no in-library measurability-in-`x` lemma; see the module
`## gap`.) -/
theorem ae_suspensionMeasure_hasFlowExponent_unconditional (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hC : ∀ x, τ x ≤ C)
    (hPmeas : MeasurableSet
      {x : X | Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
        atTop (𝓝 (lam / ∫ y, τ y ∂μ))})
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ,
      HasFlowExponent A T hτ hc hcpos q (lam / ∫ y, τ y ∂μ) :=
  ae_suspensionMeasure_hasFlowExponent A T hτ hc hcpos hC hPmeas
    (measurableSet_suspensionMk_exponent_image A T hτ μ hc hcpos hPmeas)
    hgrow hroof hτ_pos

include hτ in
/-- **The space-level exponent tied to the genuine measure-preserving flow.** For `μ̂`-almost every
orbit class `q ∈ SuspensionSpace`, `q` lies on the `suspensionFlow`-orbit of a base cross-section
point and carries the flow exponent `λ_base / ∫τ`: there are `x : X` and a flow time `s : ℝ` with

`q = suspensionFlow hT hc hcpos s (suspensionSection x)`  and  `HasFlowExponent q (λ_base / ∫τ)`.

The unconditional headline `ae_suspensionMeasure_hasFlowExponent_unconditional` hands back, for
`μ̂`-a.e. `q`, a representative `(x, s)` with `suspensionMk (x, s) = q`; the flow identity
`suspensionFlowMap_section` (`ζ_s [x, 0] = [x, s]`) rewrites this as
`q = ζ_s (suspensionSection x)`, the genuine flow image of the cross-section point
`suspensionSection x` under the
`MeasurePreservingFlow` `suspensionFlow`. This expresses the a.e. exponent against the actual flow
object rather than a bare representative. -/
theorem ae_suspensionMeasure_hasFlowExponent_flowOrbit (hT : MeasurePreserving T μ μ)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (hPmeas : MeasurableSet
      {x : X | Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
        atTop (𝓝 (lam / ∫ y, τ y ∂μ))})
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ, ∃ (x : X) (s : ℝ),
      q = suspensionFlow T hτ hT hc hcpos s (suspensionSection T hτ x) ∧
        HasFlowExponent A T hτ hc hcpos q (lam / ∫ y, τ y ∂μ) := by
  have hae := ae_suspensionMeasure_hasFlowExponent_unconditional A T hτ hc hcpos hC hPmeas
    hgrow hroof hτ_pos
  filter_upwards [hae] with q hq
  -- Unpack the `HasFlowExponent` witness `(x, s)` of `q` (keeping `hq` for the exponent field).
  obtain ⟨x, s, hmk, _⟩ := id hq
  refine ⟨x, s, ?_, hq⟩
  -- `suspensionFlow s (suspensionSection x) = ζ_s [x, 0] = [x, s] = q`.
  rw [show suspensionFlow T hτ hT hc hcpos s (suspensionSection T hτ x)
      = suspensionFlowMap T hτ s (suspensionSection T hτ x) from rfl,
    suspensionFlowMap_section T hτ s x, hmk]

end Unconditional

end Oseledets
