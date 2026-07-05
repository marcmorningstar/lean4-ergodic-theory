/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionSpaceExponent
import ErgodicTheory.Continuous.SuspensionDisintegration

/-!
# The space-level special-flow Lyapunov exponent value `λ_base / ∫τ`

This module assembles the **space-level headline of Issue #5**: for the suspension (mapping-torus)
space `SuspensionSpace T hτ` of the base map `T` under the roof `τ`, the flow Lyapunov exponent
`HasFlowExponent q (λ_base / ∫τ)` holds for `μ̂`-almost every orbit class `q`, where `μ̂` is the
invariant probability measure `suspensionMeasure` and `λ_base` is the top base Lyapunov exponent.
This is the Lyapunov-exponent analogue of **Abramov's entropy formula** `h(flow) = h(base)/∫τ`
(L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875), in the
special-flow / flow-under-a-roof setting of Cornfeld–Fomin–Sinai, *Ergodic Theory* (Springer 1982),
Ch. 11 (special/suspension flows; Ambrose–Kakutani); the exponent-transfer direction is the design
reference of Bessa–Varandas (suspension Lyapunov exponents).

The assembly combines three already-built pieces:

* the **bounded-roof cross-section exponent** `coverCocycle_tendsto_exponent_of_bddRoof`
  (`ErgodicTheory.Continuous.SuspensionBddRoofExponent`), giving for base-`μ`-a.e. `x` the section
  growth rate `Real.log ‖coverCocycle (x, 0) t‖ / t → λ_base / ∫τ` (read off the base section,
  height `s = 0`);
* the **disintegration / fundamental-domain transfer**
  `ae_suspensionMeasure_section_exponent_set` (`ErgodicTheory.Continuous.SuspensionDisintegration`),
  lifting that base-a.e. set of section exponents to a `μ̂`-a.e. set of orbit classes admitting a
  box representative `(x, s)` whose first coordinate carries the section exponent;
* the **`HasFlowExponent` predicate** (`ErgodicTheory.Continuous.SuspensionSpaceExponent`), the
  representative-free flow exponent on `SuspensionSpace`.

The one new ingredient is the **height-shift step** `tendsto_coverCocycle_exponent_of_section`: the
section growth rate at the base point `(x, 0)` equals the cover-cocycle growth rate at *every*
height `(x, s)`. This is immediate from `coverCocycle (x, s) t = coverCocycle (x, 0) (s + t)`
(unfolding `ErgodicTheory.coverCocycle = flowCocycleSection (p.2 + t) p.1`): the per-`t` ratio
`log ‖coverCocycle (x, s) t‖ / t` is the section ratio at total time `s + t` rescaled by
`(s + t) / t → 1`, so the two limits coincide. The base representative `(x, s)` — the *actual*
representative `q = [x, s]` the disintegration hands back — is then a `HasFlowExponent` witness for
its own class.

## Main results

* `ErgodicTheory.tendsto_coverCocycle_exponent_of_section`: the height-shift. If
  `Real.log ‖coverCocycle (x, 0) t‖ / t → L`, then `Real.log ‖coverCocycle (x, s) t‖ / t → L` for
  every height `s`.
* `ErgodicTheory.ae_suspensionMeasure_hasFlowExponent`: the **space-level exponent**. Under a
  bounded roof `c ≤ τ ≤ C` with `0 < c`, positive integral `0 < ∫τ`, and the base-a.e. Birkhoff
  growth / roof-average limits (top base exponent `λ_base`, mean roof `∫τ`), for `μ̂`-a.e. `q ∈
  SuspensionSpace`, `HasFlowExponent q (λ_base / ∫τ)`.

## gap

The headline is the `μ̂`-a.e. *existence of the flow exponent value* `λ_base / ∫τ` at almost every
class — the genuine space-level #5 exponent. It is the `μ̂`-a.e. instantiation of the existential
predicate `HasFlowExponent`; uniqueness of that value across the class (well-definedness of a single
`SuspensionSpace → ℝ` exponent function) is the *forward-step* content of
`ErgodicTheory.tendsto_exponent_iff_of_suspensionAct` (`SuspensionSpaceExponent`), whose closure
over the full signed-integer orbit connection is deferred there. The measurability witness `hmeas`
of the lifted exponent set on the quotient is consumed as an explicit hypothesis (the disintegration
data, exactly as in `ae_suspensionMeasure_section_exponent_set`: the quotient image of a measurable
base set is not measurable for free). No closed-form identification of `λ_base` with the integrated
top Lyapunov exponent is asserted here beyond its defining base-a.e. Birkhoff limit `hgrow`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}

section HeightShift

/-- **Height-shift of the cover-cocycle exponent.** The section growth rate read at the base point
`(x, 0)` propagates to every height `(x, s)`: if
`Real.log ‖coverCocycle (x, 0) t‖ / t → L`, then `Real.log ‖coverCocycle (x, s) t‖ / t → L`.

Since `coverCocycle (x, s) t = flowCocycleSection (s + t) x = coverCocycle (x, 0) (s + t)`, the
height-`s` ratio at flow time `t` equals the section ratio at total time `s + t` times the rescaling
`(s + t) / t`. As `t → ∞` the section ratio tends to `L` (composition with `t ↦ s + t → atTop`) and
`(s + t) / t = 1 + s / t → 1`, so the product tends to `L`. -/
theorem tendsto_coverCocycle_exponent_of_section (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (x : X)
    (s : ℝ) {L : ℝ}
    (hL : Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
      atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖ / t) atTop (𝓝 L) := by
  -- The section ratio at total time `s + t` tends to `L` (precompose with `t ↦ s + t → atTop`).
  have hshift : Tendsto
      (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) (s + t)‖ / (s + t))
      atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_add_const_left atTop s tendsto_id)
  -- The rescaling factor `(s + t) / t = 1 + s / t → 1`.
  have hzero : Tendsto (fun t : ℝ => s / t) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hrescale : Tendsto (fun t : ℝ => (s + t) / t) atTop (𝓝 1) := by
    have hsum : Tendsto (fun t : ℝ => s / t + 1) atTop (𝓝 (0 + 1)) :=
      hzero.add tendsto_const_nhds
    have hrw : (fun t : ℝ => (s + t) / t) =ᶠ[atTop] fun t : ℝ => s / t + 1 := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      field_simp
    rw [zero_add] at hsum
    exact hsum.congr' hrw.symm
  -- The product tends to `L · 1 = L`; identify it with the height-`s` ratio.
  have hprod : Tendsto
      (fun t : ℝ =>
        (Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) (s + t)‖ / (s + t)) * ((s + t) / t))
      atTop (𝓝 (L * 1)) :=
    hshift.mul hrescale
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ),
    (tendsto_atTop_add_const_left atTop s tendsto_id).eventually_ne_atTop (0 : ℝ)]
    with t ht hst
  -- `coverCocycle (x, s) t = coverCocycle (x, 0) (s + t)`, then cancel the `(s + t)` factor.
  have hcc : coverCocycle A T hτ hc hcpos (x, s) t
      = coverCocycle A T hτ hc hcpos (x, 0) (s + t) := by
    simp only [coverCocycle, zero_add]
  rw [id] at hst
  rw [hcc]
  field_simp

end HeightShift

section SpaceExponentValue

variable {μ : Measure X} [SFinite μ] {lam : ℝ}

include hτ in
/-- **The space-level special-flow Lyapunov exponent.** (`HasFlowExponent` is existential over
representatives: for `μ̂`-a.e. class *some* representative realises the value `λ_base / ∫τ`;
cross-representative uniqueness is separate and needs base-cocycle invertibility.) For the
suspension space `SuspensionSpace
T hτ` with its invariant probability measure `μ̂ = suspensionMeasure`, under a bounded roof
`c ≤ τ ≤ C` (`0 < c`), positive integral `0 < ∫τ`, and the base-a.e. Birkhoff limits — the discrete
base growth rate `→ λ_base` and the roof average `→ ∫τ` — the flow Lyapunov exponent equals
`λ_base / ∫τ` for `μ̂`-almost every orbit class:
`∀ᵐ q ∂μ̂, HasFlowExponent q (λ_base / ∫τ)`.

The base-a.e. section exponent `coverCocycle_tendsto_exponent_of_bddRoof` is transferred to a
`μ̂`-a.e. set of classes by the disintegration `ae_suspensionMeasure_section_exponent_set`,
handing back, for `μ̂`-a.e. `q`, a box representative `(x, s)` with `suspensionMk (x, s) = q` and
the section exponent at `(x, 0)`. The height-shift `tendsto_coverCocycle_exponent_of_section`
promotes that section exponent to the cover-cocycle exponent at the *actual* representative
`(x, s)`, which then witnesses `HasFlowExponent q (λ_base / ∫τ)`.

`hmeas` (measurability of the lifted exponent set on the quotient) is the disintegration datum
required by `ae_suspensionMeasure_section_exponent_set` — the quotient image of a measurable base
set is not measurable for free — and is carried through as an explicit hypothesis. -/
theorem ae_suspensionMeasure_hasFlowExponent (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hC : ∀ x, τ x ≤ C)
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
      HasFlowExponent A T hτ hc hcpos q (lam / ∫ y, τ y ∂μ) := by
  -- The disintegration: for `μ̂`-a.e. `q`, a box representative carries the section exponent.
  have hset := ae_suspensionMeasure_section_exponent_set A T hτ hc hcpos hC hPmeas hmeas
    hgrow hroof hτ_pos
  filter_upwards [hset] with q hq
  obtain ⟨p, hpq, hpexp⟩ := hq
  -- The representative `(p.1, p.2) = p` of `q` is a `HasFlowExponent` witness: height-shift the
  -- section exponent at `(p.1, 0)` up to the cover-cocycle exponent at `p = (p.1, p.2)`.
  refine ⟨p.1, p.2, ?_, ?_⟩
  · rw [Prod.mk.eta]; exact hpq
  · exact tendsto_coverCocycle_exponent_of_section A T hτ hc hcpos p.1 p.2 hpexp

end SpaceExponentValue

end ErgodicTheory
