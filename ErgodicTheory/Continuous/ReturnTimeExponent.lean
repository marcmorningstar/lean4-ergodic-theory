/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.Suspension
import ErgodicTheory.Ergodic.Birkhoff
import ErgodicTheory.Cocycle.Basic
import ErgodicTheory.Cocycle.Norm

/-!
# The return-time exponent of a suspension

This module isolates the mathematical core of the suspension exponent-transfer identity

`λ_flow = λ_base / ∫ τ`,

namely the *denominator* `∫ τ` and the rescaling of the base index `n` by the roof Birkhoff
sum `roofSum n` (the return time after `n` base steps). The full flow-cocycle and its
identification with the base cocycle along the cross-section are deferred to a follow-up
module; here we land the base-only statement, which already captures the limit
`n / roofSum n x → 1 / ∫ τ` and combines it with an arbitrary base exponent to produce the
rescaled exponent `λ_base / ∫ τ`.

## Main results

* `ErgodicTheory.tendsto_div_of_tendsto_div`: a pure real-analysis ratio lemma — if
  `n⁻¹ · a n → L` and `n⁻¹ · r n → R ≠ 0` then `a n / r n → L / R`.
* `ErgodicTheory.roofSum_natCast_eq_birkhoffSum`: the reconciliation of the integer-indexed
  `roofSum` (restricted to `ℕ`) with Mathlib's `Function.birkhoffSum` of the roof along the
  base map; the crux that turns the suspension roof cocycle into a Birkhoff sum.
* `ErgodicTheory.tendsto_roofAverage_ae`: under ergodicity and integrability of `τ`, the roof
  average `n⁻¹ · roofSum n x` converges `μ`-a.e. to `∫ τ` (the ergodic Birkhoff theorem
  applied to the roof).
* `ErgodicTheory.integral_roof_pos`: positivity of `∫ τ` from a uniform lower bound on `τ` and a
  probability measure.
* `ErgodicTheory.returnTime_tendsto_exponent`: the **return-time exponent**. Given any base
  log-norm growth rate `lam` (a hypothesis, so the lemma applies to the top exponent, a
  `k`-th exponent, etc.), the cocycle log-norm rescaled by the return time `roofSum n x`
  converges `μ`-a.e. to `lam / ∫ τ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace ErgodicTheory

/-! ### A pure real-analysis ratio lemma -/

/-- **Ratio lemma.** If `n⁻¹ · a n → L` and `n⁻¹ · r n → R` with `R ≠ 0`, then the ratio
`a n / r n → L / R`. The common factor `n⁻¹` cancels for `n ≥ 1`, so the ratio is eventually
the quotient of the two averages, and `Filter.Tendsto.div` finishes (the limit denominator is
`R ≠ 0`). -/
theorem tendsto_div_of_tendsto_div {a r : ℕ → ℝ} {L R : ℝ} (hR : R ≠ 0)
    (ha : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * a n) atTop (𝓝 L))
    (hr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * r n) atTop (𝓝 R)) :
    Tendsto (fun n => a n / r n) atTop (𝓝 (L / R)) := by
  have hdiv : Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹ * a n) / ((n : ℝ)⁻¹ * r n)) atTop (𝓝 (L / R)) :=
    Tendsto.div ha hr hR
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_div_mul_left _ _ (ne_of_gt (inv_pos.2 hnpos))]

/-! ### Reconciling `roofSum` with the Birkhoff sum of the roof -/

section Reconcile

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The base iterate `baseIter (n : ℤ) x`, at a natural index `n`, is the `n`-th iterate of the
base map `T` applied to `x`. Proved by induction from the one-step form of `suspensionAct`. -/
theorem baseIter_natCast (n : ℕ) (x : X) :
    baseIter T hτ (n : ℤ) x = (⇑T)^[n] x := by
  induction n with
  | zero => simp [baseIter]
  | succ k ih =>
    have hstep : baseIter T hτ ((k : ℤ) + 1) x = T (baseIter T hτ (k : ℤ) x) := by
      have h : suspensionAct T hτ ((k : ℤ) + 1) (x, (0 : ℝ))
          = suspensionGen T hτ (suspensionAct T hτ (k : ℤ) (x, (0 : ℝ))) := by
        rw [add_comm, suspensionAct_add, suspensionAct_one]
      simp only [baseIter, h, suspensionGen_apply]
    rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, hstep, ih,
      Function.iterate_succ_apply']

/-- **Reconciliation.** For a natural index `n`, the suspension roof sum `roofSum (n : ℤ) x`
equals Mathlib's Birkhoff sum `birkhoffSum (⇑T) τ n x = ∑_{k<n} τ ((⇑T)^[k] x)`. Both satisfy
`F 0 = 0` and `F (n+1) = F n + τ ((⇑T)^[n] x)` (via `roofSum_add_one` and `baseIter_natCast`),
so they agree by induction. -/
theorem roofSum_natCast_eq_birkhoffSum (n : ℕ) (x : X) :
    roofSum T hτ (n : ℤ) x = birkhoffSum (⇑T) τ n x := by
  induction n with
  | zero => simp [birkhoffSum_zero]
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring,
      roofSum_add_one, baseIter_natCast, ih, birkhoffSum_succ]

end Reconcile

/-! ### The roof average converges a.e. to `∫ τ` -/

/-- **Roof average.** When `T` is ergodic for a probability measure `μ` and the roof `τ` is
integrable, the roof average `n⁻¹ · roofSum n x` converges `μ`-a.e. to the space average
`∫ τ ∂μ`. This is the ergodic Birkhoff theorem `tendsto_birkhoffAverage_ae_integral` applied to
the roof, after reconciling `roofSum` with the Birkhoff sum and unfolding `birkhoffAverage`. -/
theorem tendsto_roofAverage_ae {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ}
    (hτ : Measurable τ) {μ : Measure X} [IsProbabilityMeasure μ] (hT : Ergodic (⇑T) μ)
    (hτint : Integrable τ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop
      (𝓝 (∫ y, τ y ∂μ)) := by
  filter_upwards [tendsto_birkhoffAverage_ae_integral hT hτint] with x hx
  refine hx.congr (fun n => ?_)
  rw [roofSum_natCast_eq_birkhoffSum, birkhoffAverage, smul_eq_mul]

/-! ### Positivity of the roof integral -/

/-- **Positivity of `∫ τ`.** A uniform lower bound `c ≤ τ` with `0 < c` on a probability
measure forces `0 < ∫ τ ∂μ`, since `∫ τ ≥ ∫ c = c · μ univ = c > 0`. -/
theorem integral_roof_pos {X : Type*} [MeasurableSpace X] {τ : X → ℝ} {μ : Measure X}
    [IsProbabilityMeasure μ] {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hτint : Integrable τ μ) :
    0 < ∫ y, τ y ∂μ := by
  have hle : ∫ _y, c ∂μ ≤ ∫ y, τ y ∂μ :=
    integral_mono (integrable_const c) hτint hc
  rw [integral_const, probReal_univ, one_smul] at hle
  linarith

/-! ### The return-time exponent -/

/-- **The return-time exponent.** Suppose the base cocycle `A` has a `μ`-a.e. log-norm growth
rate `lam`, i.e. `n⁻¹ · log ‖cocycle A T n x‖ → lam` a.e. (this is the headline output of the
discrete Oseledets/Furstenberg–Kesten theorem; it is taken as a hypothesis so the lemma applies
to the top exponent, a `k`-th exponent, or any other rate). Suppose moreover that the roof
average converges a.e. to `∫ τ` and that `∫ τ ≠ 0`. Then the cocycle log-norm rescaled by the
*return time* `roofSum n x` (the time spent in the suspension after `n` base steps) converges
`μ`-a.e. to the rescaled exponent `lam / ∫ τ`.

The proof combines the two a.e. statements pointwise and applies the ratio lemma
`tendsto_div_of_tendsto_div` with `a n = log ‖cocycle A T n x‖`, `r n = roofSum n x`, `L = lam`
and `R = ∫ τ`. -/
theorem returnTime_tendsto_exponent {X : Type*} [MeasurableSpace X] {d : ℕ}
    (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {μ : Measure X}
    {A : X → Matrix (Fin d) (Fin d) ℝ} {lam : ℝ}
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτne : (∫ y, τ y ∂μ) ≠ 0) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => Real.log ‖cocycle A (⇑T) n x‖ / roofSum T hτ (n : ℤ) x) atTop
      (𝓝 (lam / ∫ y, τ y ∂μ)) := by
  filter_upwards [hgrow, hroof] with x hgx hrx
  exact tendsto_div_of_tendsto_div hτne hgx hrx

end ErgodicTheory
