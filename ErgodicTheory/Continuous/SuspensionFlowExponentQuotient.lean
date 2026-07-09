/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionSpaceExponent
import ErgodicTheory.Continuous.SuspensionFlowExponentFinal
import ErgodicTheory.Cocycle.FurstenbergKesten

/-!
# The representative-free flow exponent as a genuine `SuspensionSpace → ℝ` function

`ErgodicTheory.Continuous.SuspensionSpaceExponent` proved the growth rate
`lim (1/t) log ‖coverCocycle p t‖` of the cover cocycle to be orbit-invariant across a **forward**
orbit step `suspensionAct (n : ℤ)` with `n : ℕ`, but explicitly deferred the *signed*-integer
closure (`m < 0`, a backward step) and hence the actual `Quotient.lift` of the exponent to a
function on the orbit quotient `SuspensionSpace T hτ`. This module closes that gap.

## The signed-step closure

Orbit equivalence in `SuspensionSpace` unfolds to a *signed* `m : ℤ` with
`suspensionAct m (x₂, s₂) = (x₁, s₁)`. `tendsto_exponent_iff_of_orbitRel` handles both signs by
**confluence to the forward iff at a different base point**: for `0 ≤ m` it applies the forward
`tendsto_exponent_iff_of_suspensionAct` (`ErgodicTheory.Continuous.SuspensionSpaceExponent`) at base
`(x₂, s₂)`; for `m ≤ 0` it inverts the connection to `suspensionAct (-m) (x₁, s₁) = (x₂, s₂)` and
applies the *same* forward iff at base `(x₁, s₁)`. The global invertibility hypothesis
`∀ x, (A x).det ≠ 0` supplies the unit-determinant and eventual strict-positivity side conditions on
*both* representatives (`coverCocycle_norm_pos`), which is exactly what makes the lift **total** on
every orbit class.

## The descent

`flowExponentAt` is the `Quotient.lift` of `repExponent` (the growth-rate limit read off from a
representative, with a fixed junk value `0` when no limit exists — a plain `dite`/`Exists.choose`
rather than `limUnder`, whose junk is not constant across representatives). Well-definedness is the
signed-step iff above: the *existence* of the limit transfers across an orbit step, and where the
limit exists on both sides `tendsto_nhds_unique` forces the two values to agree.

## Main definitions

* `ErgodicTheory.repExponent`: the representative-level growth rate `p ↦ lim (1/t) log ‖coverCocycle
  p t‖` (junk `0` off the convergence locus).
* `ErgodicTheory.flowExponentAt`: the representative-free flow exponent
  `SuspensionSpace T hτ → ℝ`, the `Quotient.lift` of `repExponent`, well defined under global
  base-cocycle invertibility.

## Main results

* `ErgodicTheory.tendsto_exponent_iff_of_orbitRel`: signed-step cross-representative uniqueness.
  For any `m : ℤ` connecting two cover points, the two cover-cocycle growth-rate `Tendsto`
  statements are equivalent.
* `ErgodicTheory.flowExponentAt_eq_of_hasFlowExponent`: `flowExponentAt q = L` whenever
  `HasFlowExponent q L`.
* `ErgodicTheory.ae_flowExponentAt_eq_base_div_roof`: the representative-free a.e. headline — for
  `suspensionMeasure`-almost every orbit class `q`, `flowExponentAt q = λ_base / ∫τ`.

## References

This is the standard special-flow / flow-under-a-roof bookkeeping of Cornfeld–Fomin–Sinai,
*Ergodic Theory* (Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani); the descent
direction — the *exponent*, not the matrix, passes to the quotient — is the design reference of
Bessa–Varandas (suspension Lyapunov exponents). The headline analogue is Abramov's entropy formula
`h(flow) = h(base)/∫τ` (L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128**
(1959) 873–875).
-/

open Filter Topology MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace ErgodicTheory

section Quotient

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}

/-- **Strict positivity of the cover-cocycle norm under global invertibility.** For every cover
point `p` and flow time `t`, if the base generator `A` is everywhere invertible (`det ≠ 0`) then
`0 < ‖coverCocycle p t‖`: the cover cocycle reduces to a base cocycle iterate `cocycle A T
(lapCount …) p.1`, whose norm is strictly positive by `norm_cocycle_pos`. -/
theorem coverCocycle_norm_pos [NeZero d] (hA : ∀ x, (A x).det ≠ 0) (hc : ∀ x, c ≤ τ x)
    (hcpos : 0 < c) (p : X × ℝ) (t : ℝ) :
    0 < ‖coverCocycle A T hτ hc hcpos p t‖ := by
  have hrw : coverCocycle A T hτ hc hcpos p t
      = cocycle A (⇑T) (lapCount T hτ hc hcpos (p.2 + t) p.1) p.1 := by
    simp only [coverCocycle, flowCocycleSection, suspensionCocycleReturn_returnTime]
  rw [hrw]; exact norm_cocycle_pos hA _ _

/-- **Eventual dominance of a flow time over a fixed return time.** The `n`-th return time
`returnTime T hτ n x` is a constant in the flow time `t`, so it is eventually `≤ s + t` as
`t → ∞`. This packages the `hret` side condition of `tendsto_exponent_iff_of_suspensionAct`. -/
theorem eventually_returnTime_le (n : ℕ) (x : X) (s : ℝ) :
    ∀ᶠ t : ℝ in atTop, returnTime T hτ n x ≤ s + t := by
  filter_upwards [eventually_ge_atTop (returnTime T hτ n x - s)] with t ht
  linarith

set_option maxHeartbeats 400000 in
-- the two branches each thread the long `coverCocycle` terms through the forward iff; the default
-- heartbeat budget is exceeded, exactly as in `tendsto_exponent_iff_of_suspensionAct`
/-- **Signed-step cross-representative uniqueness of the flow exponent.** If two cover points are
connected by a *signed* orbit step `suspensionAct T hτ m (x₂, s₂) = (x₁, s₁)` for `m : ℤ`, and the
base cocycle is everywhere invertible, then the cover-cocycle growth rates at `(x₁, s₁)` and at
`(x₂, s₂)` converge to one and the same `L`: the two `Tendsto` statements are equivalent.

This closes the signed-integer gap deferred in
`ErgodicTheory.Continuous.SuspensionSpaceExponent`. Both signs reduce to the *forward*
`tendsto_exponent_iff_of_suspensionAct`: for `0 ≤ m` at base `(x₂, s₂)`; for `m ≤ 0` after inverting
the connection to `suspensionAct T hτ (-m) (x₁, s₁) = (x₂, s₂)`, at base `(x₁, s₁)`. Global
invertibility discharges the unit-determinant and eventual strict-positivity side conditions on
both representatives via `coverCocycle_norm_pos`. -/
theorem tendsto_exponent_iff_of_orbitRel [NeZero d] (hA : ∀ x, (A x).det ≠ 0)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (m : ℤ) (x₁ x₂ : X) (s₁ s₂ : ℝ)
    (hm : suspensionAct T hτ m (x₂, s₂) = (x₁, s₁)) {L : ℝ} :
    Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x₁, s₁) t‖ / t) atTop (𝓝 L)
      ↔ Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x₂, s₂) t‖ / t)
        atTop (𝓝 L) := by
  have hpos : ∀ (p : X × ℝ) (t : ℝ), 0 < ‖coverCocycle A T hτ hc hcpos p t‖ :=
    fun p t => coverCocycle_norm_pos A T hτ hA hc hcpos p t
  rcases le_total 0 m with hmpos | hmneg
  · -- `0 ≤ m`: apply the forward iff at base `(x₂, s₂)`.
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg hmpos⟩
    have hU : IsUnit (cocycle A (⇑T) n x₂).det := (det_cocycle_ne_zero hA n x₂).isUnit
    have hret : ∀ᶠ t : ℝ in atTop, returnTime T hτ n x₂ ≤ s₂ + t :=
      eventually_returnTime_le T hτ n x₂ s₂
    have hp : ∀ᶠ t : ℝ in atTop, 0 < ‖coverCocycle A T hτ hc hcpos (x₂, s₂) t‖ :=
      Eventually.of_forall (hpos (x₂, s₂))
    have hq : ∀ᶠ t : ℝ in atTop,
        0 < ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x₂, s₂)) t‖ :=
      Eventually.of_forall (hpos (suspensionAct T hτ (n : ℤ) (x₂, s₂)))
    have hiff :=
      tendsto_exponent_iff_of_suspensionAct A T hτ hc hcpos n x₂ s₂ hU hret hp hq (L := L)
    rw [hm] at hiff
    exact hiff.symm
  · -- `m ≤ 0`: invert the connection and apply the forward iff at base `(x₁, s₁)`.
    have hm2 : suspensionAct T hτ (-m) (x₁, s₁) = (x₂, s₂) := by
      rw [← hm, ← suspensionAct_add, neg_add_cancel, suspensionAct_zero]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -m := ⟨(-m).toNat, Int.toNat_of_nonneg (by linarith)⟩
    rw [← hn] at hm2
    have hU : IsUnit (cocycle A (⇑T) n x₁).det := (det_cocycle_ne_zero hA n x₁).isUnit
    have hret : ∀ᶠ t : ℝ in atTop, returnTime T hτ n x₁ ≤ s₁ + t :=
      eventually_returnTime_le T hτ n x₁ s₁
    have hp : ∀ᶠ t : ℝ in atTop, 0 < ‖coverCocycle A T hτ hc hcpos (x₁, s₁) t‖ :=
      Eventually.of_forall (hpos (x₁, s₁))
    have hq : ∀ᶠ t : ℝ in atTop,
        0 < ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x₁, s₁)) t‖ :=
      Eventually.of_forall (hpos (suspensionAct T hτ (n : ℤ) (x₁, s₁)))
    have hiff :=
      tendsto_exponent_iff_of_suspensionAct A T hτ hc hcpos n x₁ s₁ hU hret hp hq (L := L)
    rw [hm2] at hiff
    exact hiff

open Classical in
/-- **The representative-level flow exponent.** The growth-rate limit `lim (1/t) log ‖coverCocycle
p t‖` read off from a cover representative `p`, with the fixed junk value `0` off the convergence
locus. Unlike `limUnder`, whose junk value need not be constant across representatives, this fixed
`dite`/`Exists.choose` form is what descends to the quotient. -/
noncomputable def repExponent (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (p : X × ℝ) : ℝ :=
  if h : ∃ L, Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos p t‖ / t) atTop (𝓝 L)
  then h.choose else 0

set_option maxHeartbeats 400000 in
-- the well-definedness obligation elaborates the long `coverCocycle` growth-rate `Tendsto` terms on
-- both representatives through the signed-step iff, exceeding the default heartbeat budget
/-- **The representative-free flow exponent on the suspension quotient.** The `Quotient.lift` of
`repExponent` to a genuine function `SuspensionSpace T hτ → ℝ`. Well-definedness is the signed-step
uniqueness `tendsto_exponent_iff_of_orbitRel`: the *existence* of the growth-rate limit transfers
across any orbit step, and where it exists on both representatives `tendsto_nhds_unique` forces the
two limits to agree. The global invertibility hypothesis `∀ x, (A x).det ≠ 0` is what makes the lift
**total** — well defined on every orbit class. -/
noncomputable def flowExponentAt [NeZero d] (hA : ∀ x, (A x).det ≠ 0)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) : SuspensionSpace T hτ → ℝ :=
  letI := suspensionAddAction T hτ
  Quotient.lift (repExponent A T hτ hc hcpos) (fun a b hab => by
    obtain ⟨ax, as⟩ := a
    obtain ⟨bx, bs⟩ := b
    change (ax, as) ∈ AddAction.orbit ℤ (bx, bs) at hab
    rw [AddAction.mem_orbit_iff] at hab
    obtain ⟨m, hm⟩ := hab
    have hm' : suspensionAct T hτ m (bx, bs) = (ax, as) := hm
    have hiff : ∀ L : ℝ,
        Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (ax, as) t‖ / t)
            atTop (𝓝 L) ↔
          Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (bx, bs) t‖ / t)
            atTop (𝓝 L) :=
      fun L => tendsto_exponent_iff_of_orbitRel A T hτ hA hc hcpos m ax bx as bs hm' (L := L)
    by_cases h₁ : ∃ L, Tendsto
        (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (ax, as) t‖ / t) atTop (𝓝 L)
    · have h₂ : ∃ L, Tendsto
          (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (bx, bs) t‖ / t) atTop (𝓝 L) := by
        obtain ⟨L, hL⟩ := h₁; exact ⟨L, (hiff L).mp hL⟩
      simp only [repExponent, dif_pos h₁, dif_pos h₂]
      exact tendsto_nhds_unique ((hiff h₁.choose).mp h₁.choose_spec) h₂.choose_spec
    · have h₂ : ¬ ∃ L, Tendsto
          (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (bx, bs) t‖ / t) atTop (𝓝 L) := by
        rintro ⟨L, hL⟩; exact h₁ ⟨L, (hiff L).mpr hL⟩
      simp only [repExponent, dif_neg h₁, dif_neg h₂])

@[simp] theorem flowExponentAt_mk [NeZero d] (hA : ∀ x, (A x).det ≠ 0)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (p : X × ℝ) :
    flowExponentAt A T hτ hA hc hcpos (suspensionMk T hτ p) = repExponent A T hτ hc hcpos p :=
  rfl

/-- **Reading the flow exponent off a convergent representative.** If the cover-cocycle growth rate
at the representative `p` converges to `L`, then `flowExponentAt` of its orbit class is `L`. -/
theorem flowExponentAt_eq_of_tendsto [NeZero d] (hA : ∀ x, (A x).det ≠ 0)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (p : X × ℝ) {L : ℝ}
    (hL : Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos p t‖ / t) atTop (𝓝 L)) :
    flowExponentAt A T hτ hA hc hcpos (suspensionMk T hτ p) = L := by
  rw [flowExponentAt_mk]
  have hex : ∃ L', Tendsto
      (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos p t‖ / t) atTop (𝓝 L') := ⟨L, hL⟩
  simp only [repExponent, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec hL

/-- **`flowExponentAt` reads off `HasFlowExponent`.** If `q` carries the flow exponent `L` (some
representative has cover-cocycle growth rate `L`), then `flowExponentAt q = L`. -/
theorem flowExponentAt_eq_of_hasFlowExponent [NeZero d] (hA : ∀ x, (A x).det ≠ 0)
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {q : SuspensionSpace T hτ} {L : ℝ}
    (hq : HasFlowExponent A T hτ hc hcpos q L) :
    flowExponentAt A T hτ hA hc hcpos q = L := by
  obtain ⟨x, s, hmk, hL⟩ := hq
  rw [← hmk]
  exact flowExponentAt_eq_of_tendsto A T hτ hA hc hcpos (x, s) hL

section Final

variable {μ : Measure X} [SFinite μ] {lam : ℝ}

include hτ in
/-- **The representative-free flow-exponent a.e. headline.** Under a bounded roof `c ≤ τ ≤ C`
(`0 < c`), positive integral `0 < ∫τ`, measurable base generator `A`, global invertibility
`∀ x, (A x).det ≠ 0`, and the base-a.e. Birkhoff limits (discrete growth rate `→ λ_base`, roof
average `→ ∫τ`), for `suspensionMeasure`-almost every orbit class `q`, the (now genuinely
representative-free) flow exponent equals `λ_base / ∫τ`:
`∀ᵐ q ∂suspensionMeasure T hτ μ, flowExponentAt q = λ_base / ∫τ`.

The added global-invertibility hypothesis `hAdet` (over the existential-only
`ae_suspensionMeasure_hasFlowExponent_of_measurable`) is the documented honest cost of upgrading the
`HasFlowExponent` predicate to the actual `Quotient.lift` value. -/
theorem ae_flowExponentAt_eq_base_div_roof [NeZero d] (hAdet : ∀ x, (A x).det ≠ 0)
    (hA : Measurable A) (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτ_pos : 0 < ∫ y, τ y ∂μ) :
    ∀ᵐ q ∂suspensionMeasure T hτ μ,
      flowExponentAt A T hτ hAdet hc hcpos q = lam / ∫ y, τ y ∂μ := by
  filter_upwards [ae_suspensionMeasure_hasFlowExponent_of_measurable A T hτ hA hc hcpos hC
    hgrow hroof hτ_pos] with q hq
  exact flowExponentAt_eq_of_hasFlowExponent A T hτ hAdet hc hcpos hq

end Final

end Quotient

end ErgodicTheory
