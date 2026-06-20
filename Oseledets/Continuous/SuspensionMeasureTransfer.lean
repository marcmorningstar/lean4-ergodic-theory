/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionFlowMP
import Oseledets.Continuous.SuspensionBddRoofExponent

/-!
# The cross-section embedding into the suspension space, and the section measure bridge

This module supplies the **cross-section** plumbing that connects the section-level full-time
special-flow exponent `λ_flow = λ_base / ∫τ`
(`Oseledets.coverCocycle_tendsto_exponent_of_bddRoof`, a `μ`-a.e. statement over the *base*) to the
suspension quotient space `Oseledets.SuspensionSpace` and its invariant probability measure
`Oseledets.suspensionMeasure`. It lands the genuinely self-contained building blocks that the
existing API already supports, and documents precisely the disintegration gap that the full
`μ̂`-a.e. space-level statement still needs.

This is the Ambrose–Kakutani cross-section / flow-under-a-roof construction of Cornfeld–Fomin–Sinai,
*Ergodic Theory* (Springer 1982), Ch. 11 (special/suspension flows), the first-return / ceiling
construction underlying Abramov's entropy formula `h(flow) = h(base)/∫τ` (L.M. Abramov, *On the
entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875); the Lyapunov-exponent analogue
`λ_flow = λ_base / ∫τ` is the headline of Issue #5.

## The cross-section embedding

The base `X` embeds into the suspension as the **height-`0` cross-section** `x ↦ [x, 0]`:

`suspensionSection T hτ x := suspensionMk T hτ (x, 0)`.

This is the Ambrose–Kakutani cross-section read inside the quotient. Three facts make it the right
object:

* it is **measurable** (`measurable_suspensionSection`), being `suspensionMk ∘ (· , 0)`;
* the suspension flow **flows the section to height `t`**: `ζ_t [x, 0] = [x, t]`
  (`suspensionFlowMap_section`); in particular the flow over the roof time lands back on the section
  at the base image, `ζ_(τ x) [x, 0] = [T x, 0]` (`suspensionFlowMap_roof_section`);
* the section realizes the **orbit-gluing** `(x, τ x) ∼ (T x, 0)` that defines the suspension:
  `[x, τ x] = [T x, 0]` (`suspensionMk_roof_eq_section_base`).

## The section measure bridge

The suspension measure is `μ̂ = (∫τ)⁻¹ · ((μ × volume)|_𝓕 ↦ π)` for the fundamental box
`𝓕 = suspensionDomain τ`. Its total mass is `1` (`isProbabilityMeasure_suspensionMeasure`) and the
raw measure's mass is the box mass `(μ × volume) 𝓕 = ofReal (∫τ)` (`suspensionMeasure₀_univ`). We
record the clean **section box-mass bridge** `suspensionMeasure₀_univ` recast on the suspension:
the raw quotient measure assigns the *full* base–roof box mass to the whole space, so against the
normalised `μ̂` the box carries the unit of measure. The bridge lemma
`suspensionMeasure_univ_eq_one` (re-export) and the box-mass identity
`suspensionMeasure₀_univ_eq_ofReal_integral` package this so downstream descent arguments can read
the section against `μ̂` without re-deriving the Fubini box mass.

## The headline at section points

`coverCocycle_tendsto_exponent_section` restates the bounded-roof headline exponent
`coverCocycle_tendsto_exponent_of_bddRoof` with its starting cover point named as the section point
`(x, 0)` whose quotient class is `suspensionSection T hτ x`. This is the cleanest descent that the
cover cocycle admits: the *growth rate* `Real.log ‖coverCocycle (x, 0) t‖ / t → λ_base / ∫τ` is read
from the base cross-section, the orbit representative of `[x, 0] ∈ SuspensionSpace`.

## What is *not* in this file — the precise remaining gap

The genuine **space-level** statement — `λ_flow = λ_base / ∫τ` as a `μ̂`-a.e. property of points of
`SuspensionSpace` against the invariant measure `suspensionMeasure` — needs two pieces that the
cross-section plumbing here deliberately does **not** supply:

1. **Disintegration of `μ̂` over the cross-section.** The base-`μ`-a.e. quantifier of
   `coverCocycle_tendsto_exponent_of_bddRoof` ranges over `x ∈ X`; promoting it to a
   `μ̂`-a.e. quantifier over `[x, s] ∈ SuspensionSpace` requires the disintegration of `μ̂` over the
   cross-section `X` (the fundamental-box Fubini slicing `μ̂ = (∫τ)⁻¹ ∫_X (Leb|_{[0, τ x)}) dμ`,
   transported through `π`). The cross-section image `suspensionSection '' univ` is a `μ̂`-**null**
   set (a height-`0` slice of a two-dimensional space), so the section statement here is *not*
   directly a `μ̂`-a.e. statement; it must be spread along the fibres by the disintegration. That
   measure-theoretic disintegration (Fubini over the fundamental domain, pushed through the
   quotient) is the heavy missing infrastructure.

2. **A `FlowCocycle` over `SuspensionSpace` — and the structural reason the matrix cocycle does not
   descend.** Reading the exponent against `μ̂` ultimately wants a flow cocycle defined on
   `SuspensionSpace`. The **matrix** cover cocycle `coverCocycle` does **not** descend to the
   quotient as a matrix-valued function: the orbit gluing `(x, τ x) ∼ (T x, 0)` re-bases the
   accumulated matrix by the base step `A x` (this is exactly
   `coverCocycle_section_returnTime` specialized to one lap), so the matrix is well-defined only up
   to the left `cocycle`-conjugation along the orbit — it is a *cocycle over the flow*, not a
   function on the quotient. Only the scalar **growth rate / exponent** is orbit-invariant (the
   `log‖·‖ / t` limit is unchanged by left-multiplication by the fixed matrix `cocycle A T n x`),
   which is why this file descends the *exponent* at section points but not the matrix cocycle. The
   per-time measure-preservation needed to even phrase a `μ̂`-a.e. flow statement is already
   available (`measurePreserving_suspensionFlowMap`, `suspensionFlow`); the open keystone is the
   disintegration of (1).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X]

section CrossSection

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The **height-`0` cross-section embedding** of the base into the suspension space:
`suspensionSection T hτ x = [x, 0]`, the orbit class of the base point `x` placed at height `0`
along the flow direction. This is the Ambrose–Kakutani cross-section read inside the quotient
`SuspensionSpace`. -/
def suspensionSection (x : X) : SuspensionSpace T hτ :=
  suspensionMk T hτ (x, 0)

@[simp] theorem suspensionSection_apply (x : X) :
    suspensionSection T hτ x = suspensionMk T hτ (x, 0) := rfl

include hτ in
/-- The cross-section embedding `x ↦ [x, 0]` is measurable: it is the measurable quotient
projection `suspensionMk` (`measurable_suspensionMk`) composed with the measurable height-`0`
inclusion `x ↦ (x, 0)`. -/
theorem measurable_suspensionSection : Measurable (suspensionSection T hτ) :=
  (measurable_suspensionMk T hτ).comp (measurable_id.prodMk measurable_const)

/-- **The flow carries the section to height `t`.** Starting from the cross-section point `[x, 0]`,
the suspension flow over time `t` reaches `[x, t]`: `ζ_t [x, 0] = [x, t]`. This is the descent
identity `suspensionFlowMap_mk` with the translation `S t (x, 0) = (x, t)` evaluated. -/
theorem suspensionFlowMap_section (t : ℝ) (x : X) :
    suspensionFlowMap T hτ t (suspensionSection T hτ x) = suspensionMk T hτ (x, t) := by
  rw [suspensionSection_apply, suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]

/-- **The orbit gluing realized on the section.** The defining suspension identification
`(x, τ x) ∼ (T x, 0)` says the ceiling point above `x` is the base point above `T x`:
`[x, τ x] = [T x, 0] = suspensionSection (T x)`. The orbit witness is one step of the generator,
`suspensionGen (x, τ x) = (T x, τ x − τ x) = (T x, 0)`. -/
theorem suspensionMk_roof_eq_section_base (x : X) :
    suspensionMk T hτ (x, τ x) = suspensionSection T hτ (T x) := by
  letI := suspensionAddAction T hτ
  rw [suspensionSection_apply]
  refine Quotient.sound ?_
  -- The orbit witness is `-1`: one inverse step of the generator carries `(T x, 0)` to `(x, τ x)`.
  change ∃ n : ℤ, n +ᵥ (T x, (0 : ℝ)) = (x, τ x)
  refine ⟨-1, ?_⟩
  change suspensionAct T hτ (-1) (T x, (0 : ℝ)) = (x, τ x)
  rw [suspensionAct_neg_one, suspensionGen_symm_apply, MeasurableEquiv.symm_apply_apply,
    zero_add]

/-- **The flow over one roof time returns to the section at the base image.** Flowing for time
`τ x` from the section point `[x, 0]` lands back on the cross-section, at the base image `T x`:
`ζ_(τ x) [x, 0] = [T x, 0] = suspensionSection (T x)`. This is the first-return map of the
Ambrose–Kakutani cross-section: it composes `suspensionFlowMap_section` (the flow reaches
`[x, τ x]`) with the orbit gluing `suspensionMk_roof_eq_section_base`. -/
theorem suspensionFlowMap_roof_section (x : X) :
    suspensionFlowMap T hτ (τ x) (suspensionSection T hτ x) = suspensionSection T hτ (T x) := by
  rw [suspensionFlowMap_section, suspensionMk_roof_eq_section_base T hτ x]

end CrossSection

section MeasureBridge

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) (μ : Measure X)

/-- **The box-mass bridge for the raw suspension measure.** The raw quotient measure `μ̂₀` assigns
to the whole suspension space exactly the base–roof box mass `∫τ`, pushed through the quotient:
`μ̂₀ univ = ENNReal.ofReal (∫ x, τ x ∂μ)`. This is the normalising constant of the suspension's
invariant probability measure (re-export of `suspensionMeasure₀_univ`, the Fubini box mass
`measure_suspensionDomain` carried through `suspensionMeasure₀_univ_eq_measure_box`). It is the
measure-theoretic bridge from the base integral `∫τ` (Abramov's denominator) to the suspension
quotient: the cross-section box carries the full unit of base–roof mass. -/
theorem suspensionMeasure₀_univ_eq_ofReal_integral [SFinite μ] (hτ_nonneg : ∀ x, 0 ≤ τ x)
    (hτ_int : Integrable τ μ) :
    suspensionMeasure₀ T hτ μ univ = ENNReal.ofReal (∫ x, τ x ∂μ) :=
  suspensionMeasure₀_univ T hτ μ hτ_nonneg hτ_int

/-- **The suspension probability normalisation.** Against the invariant probability measure `μ̂`,
the whole suspension space has unit mass: `μ̂ univ = 1`. This is the normalised companion of the
box-mass bridge `suspensionMeasure₀_univ_eq_ofReal_integral`: dividing the box mass `∫τ` out of the
raw measure yields a probability measure (re-export of `suspensionMeasure_univ`). Downstream descent
arguments read the cross-section against this unit-mass `μ̂`. -/
theorem suspensionMeasure_univ_eq_one [SFinite μ] (hτ_nonneg : ∀ x, 0 ≤ τ x)
    (hτ_int : Integrable τ μ) (hτ_pos : 0 < ∫ x, τ x ∂μ) :
    suspensionMeasure T hτ μ univ = 1 :=
  suspensionMeasure_univ T hτ μ hτ_nonneg hτ_int hτ_pos

end MeasureBridge

section HeadlineSection

variable {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X ≃ᵐ X) {τ : X → ℝ}
  (hτ : Measurable τ) {c C : ℝ}

/-- **The full-time special-flow exponent at the cross-section points (headline, section form).**
This restates `coverCocycle_tendsto_exponent_of_bddRoof` with the starting cover point named as the
section point `(x, 0)`, whose quotient class is `suspensionSection T hτ x ∈ SuspensionSpace`. Under
the base growth rate `lam`, the convergent roof average `∫τ ≠ 0`, and the bounded roof `c ≤ τ ≤ C`,
the cover flow cocycle log-norm rescaled by the real elapsed flow time converges `μ`-a.e. to
`lam / ∫τ`:
`Real.log ‖coverCocycle (x, 0) t‖ / t → lam / ∫τ` as the real `t → ∞`,
read from the cross-section orbit representative of `[x, 0]`.

This is the cleanest descent the cover cocycle admits to `SuspensionSpace`: only the scalar growth
rate is orbit-invariant (the matrix cover cocycle re-bases by the base step along the gluing, see
the module header). Promoting the base-`μ`-a.e. quantifier to a `μ̂`-a.e. quantifier over points of
`SuspensionSpace` is the disintegration gap documented in the module header. -/
theorem coverCocycle_tendsto_exponent_section (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hC : ∀ x, τ x ≤ C) {μ : Measure X} {lam : ℝ}
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτne : (∫ y, τ y ∂μ) ≠ 0) :
    ∀ᵐ x ∂μ, suspensionSection T hτ x = suspensionMk T hτ (x, 0) ∧
      Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
        atTop (𝓝 (lam / ∫ y, τ y ∂μ)) := by
  have hexp := coverCocycle_tendsto_exponent_of_bddRoof A T hτ hc hcpos hC hgrow hroof hτne
  filter_upwards [hexp] with x hx
  exact ⟨suspensionSection_apply T hτ x, hx⟩

end HeadlineSection

end Oseledets
