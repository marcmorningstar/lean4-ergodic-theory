/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFullTimeExponent

/-!
# The full-time special-flow exponent under a bounded roof

This module closes the **section-level** full-time special-flow Lyapunov exponent
`λ_flow = λ_base / ∫τ` (the headline of Issue #5) under the natural extra hypothesis that the roof
`τ` is **bounded above**, `τ ≤ C`. The reduction lemmas
`ErgodicTheory.coverCocycle_norm_eq_lapCount` and `ErgodicTheory.log_coverCocycle_div_eq_lapCount`
(of `ErgodicTheory.Continuous.SuspensionFullTimeExponent`) already factor the full-time
Birkhoff ratio
exactly as

`log‖coverCocycle (x,0) t‖ / t
   = (returnTime (lapCount t x) x / t) · (log‖cocycle A T (lapCount t x) x‖ / returnTime (lapCount
     t x) x)`,

a product of a **time-distortion factor** and a **return-time exponent ratio**. The
`SuspensionFullTimeExponent` header records the precise remaining analytic gap: with only a uniform
*lower* bound `c ≤ τ`, the time-distortion factor `returnTime (lapCount t x) x / t` cannot be
squeezed to `1` (the lap width `returnTime (n+1) x − returnTime n x = τ (Tⁿ x)` is unbounded). The
present file supplies exactly the missing analytic input: with a uniform *upper* bound `τ ≤ C` the
lap width is bounded by `C`, the first-passage sandwich tightens to

`returnTime (lapCount t x) x ≤ t < returnTime (lapCount t x) x + C`,

and the time-distortion factor is squeezed to `1`.

This is the special-flow / flow-under-a-roof construction of Cornfeld–Fomin–Sinai, *Ergodic
Theory* (Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani), the first-return /
ceiling construction underlying Abramov's entropy formula `h(flow) = h(base)/∫τ` (L.M. Abramov, *On
the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875); the Lyapunov-exponent
analogue is the design reference of Bessa–Varandas (suspension Lyapunov exponents).

## Main results

* `ErgodicTheory.returnTime_succ_eq`: the return-time step
  `returnTime (n + 1) x = returnTime n x + τ (baseIter T hτ n x)`.
* `ErgodicTheory.lapCount_returnTime_lt_add_C`: the **tightened upper sandwich** under `τ ≤ C`,
  `t < returnTime (lapCount t x) x + C` (the lap width is at most `C`).
* `ErgodicTheory.lapCount_returnTime_div_tendsto_one`: the **time-distortion factor tends to `1`**,
  `returnTime (lapCount t x) x / t → 1` as the real `t → ∞` (squeeze between `1 − C/t` and `1`).
* `ErgodicTheory.lapCount_tendsto_atTop`: the lap count diverges, `lapCount t x → ∞` as `t → ∞`.
* `ErgodicTheory.coverCocycle_tendsto_exponent_of_bddRoof`: the
  **headline full-time section exponent**.
  Under the base growth, roof-average, and bounded-roof hypotheses, the full-time flow log-norm
  rescaled by `t` converges `μ`-a.e. to `lam / ∫τ`,
  `Real.log ‖coverCocycle (x,0) t‖ / t → lam / ∫τ` as the real `t → ∞`.

## What is *not* in this file — the precise remaining gap

The convergence below is the section-level (cover) full-time exponent on the base cross-section:
`coverCocycle (x, 0) ·` is the suspension flow cocycle read from height `0`. Two pieces remain
toward the genuine space-level headline against the invariant suspension measure:

1. **Quotient descent to `SuspensionSpace`.** Reading the rate as a class-invariant measurable
   function on the orbit quotient `ErgodicTheory.SuspensionSpace T hτ` (the `(x, τ x) ∼ (T x, 0)`
   identification) is the open keystone, the genuine space-level `FlowCocycle` (cf. the quotient
   gap documented in `ErgodicTheory.Continuous.SuspensionCocycle`).
2. **`MeasurePreservingFlow` packaging.** Reading `λ_flow = λ_base / ∫τ` against the invariant
   suspension measure `μ̂` needs per-time measure-preservation of the suspension flow. The
   denominator `∫τ` is Abramov's; the numerator is the base Oseledets exponent.

Under the bounded-roof hypothesis the full real-time section exponent is now sorry-free; only the
quotient descent and the measure-preservation packaging remain.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section BddRoofExponent

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}

/-- **The return-time step.** Advancing one lap adds the roof value at the shifted base point:
`returnTime (n + 1) x = returnTime n x + τ (baseIter T hτ n x)`. This unfolds the return time as the
roof Birkhoff sum and applies the roof-cocycle step `roofSum_add_one`. -/
theorem returnTime_succ_eq (n : ℕ) (x : X) :
    returnTime T hτ (n + 1) x = returnTime T hτ n x + τ (baseIter T hτ (n : ℤ) x) := by
  simp only [returnTime]
  rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by norm_cast, roofSum_add_one]

/-- **Bounded lap width.** Under a roof bounded above by `C` (`τ ≤ C`), one lap takes at most flow
time `C`: `returnTime (n + 1) x ≤ returnTime n x + C`. Combined with the lower bound `c ≤ τ` this
pins each lap width into `[c, C]`. -/
theorem returnTime_succ_le_add_C (hC : ∀ x, τ x ≤ C) (n : ℕ) (x : X) :
    returnTime T hτ (n + 1) x ≤ returnTime T hτ n x + C := by
  have hstep := returnTime_succ_eq T hτ n x
  have hbd := hC (baseIter T hτ (n : ℤ) x)
  rw [hstep]; linarith

/-- **The tightened upper sandwich.** Under `τ ≤ C` the next return overshoots `t` by at most `C`:
`t < returnTime (lapCount t x) x + C`. This is the upper first-passage bound
`t < returnTime (lapCount t x + 1) x` (`lapCount_lt_returnTime_succ`) combined with the bounded lap
width `returnTime (lapCount t x + 1) x ≤ returnTime (lapCount t x) x + C`. Together with the lower
bound `returnTime (lapCount t x) x ≤ t` (`lapCount_returnTime_le`) it confines `t` to a window of
width `C` above the lap's return time — the input that squeezes the time-distortion factor. -/
theorem lapCount_returnTime_lt_add_C (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (x : X) :
    t < returnTime T hτ (lapCount T hτ hc hcpos t x) x + C := by
  have hhi := lapCount_lt_returnTime_succ T hτ hc hcpos ht x
  have hwidth := returnTime_succ_le_add_C T hτ hC (lapCount T hτ hc hcpos t x) x
  linarith

/-- **The lap count is at least `n` once `t` has reached the `n`-th return.** For `returnTime n x ≤
t` the flow has completed at least `n` laps: `n ≤ lapCount t x`. This is read off from the upper
first-passage bound `t < returnTime (lapCount t x + 1) x` through strict monotonicity of the return
times. It is the engine of `lapCount_tendsto_atTop`. -/
theorem le_lapCount_of_returnTime_le (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {n : ℕ} {t : ℝ}
    (x : X) (hnt : returnTime T hτ n x ≤ t) :
    n ≤ lapCount T hτ hc hcpos t x := by
  have hmono : StrictMono (fun k : ℕ => returnTime T hτ k x) :=
    returnTime_strictMono T hτ hc hcpos x
  have ht : 0 ≤ t := le_trans (returnTime_nonneg T hτ hc hcpos n x) hnt
  have hhi := lapCount_lt_returnTime_succ T hτ hc hcpos ht x
  have hchain : returnTime T hτ n x < returnTime T hτ (lapCount T hτ hc hcpos t x + 1) x := by
    linarith
  exact Nat.lt_succ_iff.mp (hmono.lt_iff_lt.mp hchain)

/-- **The lap count diverges.** As the real flow time `t → ∞` the number of completed laps tends to
`+∞`: `lapCount t x → ∞`. For each target `n` the return time `returnTime n x` is a witness: once
`t ≥ returnTime n x` the flow has completed at least `n` laps
(`le_lapCount_of_returnTime_le`). -/
theorem lapCount_tendsto_atTop (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (x : X) :
    Tendsto (fun t : ℝ => lapCount T hτ hc hcpos t x) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro n
  refine ⟨returnTime T hτ n x, fun t ht => ?_⟩
  exact le_lapCount_of_returnTime_le T hτ hc hcpos x ht

/-- **The time-distortion factor tends to `1`.** Under the bounded roof `τ ≤ C`, the ratio of the
lap's return time to the elapsed flow time converges to `1`:
`returnTime (lapCount t x) x / t → 1` as the real `t → ∞`. This is the missing analytic input of the
between-returns squeeze. The tightened sandwich `returnTime (lapCount t x) x ≤ t < returnTime
(lapCount t x) x + C` confines the factor to `1 − C/t < returnTime (lapCount t x) x / t ≤ 1`, and
`1 − C/t → 1`, so the squeeze closes. -/
theorem lapCount_returnTime_div_tendsto_one (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (x : X) :
    Tendsto (fun t : ℝ => returnTime T hτ (lapCount T hτ hc hcpos t x) x / t) atTop (𝓝 1) := by
  -- Lower envelope `1 − C·t⁻¹ → 1`.
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hClow : Tendsto (fun t : ℝ => C * t⁻¹) atTop (𝓝 0) := by
    have := Filter.Tendsto.const_mul C hinv
    simpa only [mul_zero] using this
  have hlow : Tendsto (fun t : ℝ => 1 - C * t⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_zero] using h1.sub hClow
  -- Squeeze the factor between the lower envelope and the constant `1`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · -- Lower bound, eventually for `t > 0`.
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t htpos
    have ht : 0 ≤ t := le_of_lt htpos
    have hupper := lapCount_returnTime_lt_add_C T hτ hc hcpos hC ht x
    have hnum : t - C ≤ returnTime T hτ (lapCount T hτ hc hcpos t x) x := by linarith
    have hdiv : (t - C) / t ≤ returnTime T hτ (lapCount T hτ hc hcpos t x) x / t :=
      div_le_div_of_nonneg_right hnum ht
    have htne : t ≠ 0 := ne_of_gt htpos
    have heq : (t - C) / t = 1 - C * t⁻¹ := by
      rw [sub_div, div_self htne, div_eq_mul_inv]
    rw [heq] at hdiv; exact hdiv
  · -- Upper bound, eventually for `t > 0`.
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t htpos
    have hlo := lapCount_returnTime_le T hτ hc hcpos (le_of_lt htpos) x
    exact (div_le_one htpos).mpr hlo

end BddRoofExponent

section Headline

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}

/-- **The full-time section special-flow exponent under a bounded roof (headline).** Suppose the
base cocycle `A` has a `μ`-a.e. log-norm growth rate `lam` (`n⁻¹·log‖cocycle A T n x‖ → lam` a.e.;
the discrete Oseledets/Furstenberg–Kesten output, taken as a hypothesis so the lemma applies to the
top exponent or any other rate), the roof average converges a.e. to `∫τ`, `∫τ ≠ 0`, and the roof is
bounded `c ≤ τ ≤ C`. Then the **cover flow cocycle** log-norm, read from the base section and
rescaled by the *real* elapsed flow time `t`, converges `μ`-a.e. to `lam / ∫τ` as `t → ∞`:
`Real.log ‖coverCocycle (x, 0) t‖ / t → lam / ∫τ`.

This is the full real-time upgrade of `coverCocycle_returnTime_tendsto_exponent` (which holds only
along the discrete return subsequence). The proof runs the between-returns squeeze: by
`log_coverCocycle_div_eq_lapCount` the ratio factors as the time-distortion factor times the
return-time exponent ratio. The time-distortion factor tends to `1`
via `lapCount_returnTime_div_tendsto_one` (the bounded-roof input). The exponent ratio is the
discrete return-time exponent sampled at the lap count, tending to `lam / ∫τ` by composing
`coverCocycle_returnTime_tendsto_exponent` with `lapCount_tendsto_atTop` and the norm bridge
`coverCocycle_returnTime_norm_eq`. The product of the two limits is `(lam / ∫τ)·1 = lam / ∫τ`. -/
theorem coverCocycle_tendsto_exponent_of_bddRoof (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hC : ∀ x, τ x ≤ C) {μ : Measure X} {lam : ℝ}
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτne : (∫ y, τ y ∂μ) ≠ 0) :
    ∀ᵐ x ∂μ, Tendsto
      (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
      atTop (𝓝 (lam / ∫ y, τ y ∂μ)) := by
  have hret := coverCocycle_returnTime_tendsto_exponent A T hτ hc hcpos hgrow hroof hτne
  filter_upwards [hret] with x hx
  -- Abbreviation for the integral mean (roof-average denominator).
  set I := ∫ y, τ y ∂μ with hI
  set N : ℝ → ℕ := fun t => lapCount T hτ hc hcpos t x with hN
  -- Factor 2: the return-time exponent ratio at the lap count, `→ lam / I`.
  -- `hx` is the discrete return-time exponent; compose with `N · → atTop` and rewrite the
  -- cover-cocycle norm to the base cocycle norm via `coverCocycle_returnTime_norm_eq`.
  have hNtop : Tendsto N atTop atTop := lapCount_tendsto_atTop T hτ hc hcpos x
  have hfac2base : Tendsto
      (fun n : ℕ => Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x)
      atTop (𝓝 (lam / I)) := by
    refine hx.congr (fun n => ?_)
    rw [coverCocycle_returnTime_norm_eq A T hτ hc hcpos n x]
  have hfac2 : Tendsto
      (fun t : ℝ => Real.log ‖cocycle A (⇑T) (N t) x‖ / returnTime T hτ (N t) x)
      atTop (𝓝 (lam / I)) := hfac2base.comp hNtop
  -- Factor 1: the time-distortion factor `→ 1`.
  have hfac1 : Tendsto (fun t : ℝ => returnTime T hτ (N t) x / t) atTop (𝓝 1) :=
    lapCount_returnTime_div_tendsto_one T hτ hc hcpos hC x
  -- The product of the two factors tends to `(lam / I)·1 = lam / I`.
  have hprod : Tendsto
      (fun t : ℝ => (returnTime T hτ (N t) x / t)
        * (Real.log ‖cocycle A (⇑T) (N t) x‖ / returnTime T hτ (N t) x))
      atTop (𝓝 (lam / I)) := by
    have := hfac1.mul hfac2
    simpa only [one_mul] using this
  -- Rewrite the cover-cocycle ratio as that product, eventually for `t > 0` with a positive lap
  -- return time (so that `log_coverCocycle_div_eq_lapCount` applies).
  refine hprod.congr' ?_
  filter_upwards [(hNtop.eventually_gt_atTop 0), eventually_gt_atTop (0 : ℝ)]
    with t hNt htpos
  have ht : 0 ≤ t := le_of_lt htpos
  have hrt : returnTime T hτ (N t) x ≠ 0 := by
    have hpos : 0 < returnTime T hτ (N t) x := by
      have hmono : StrictMono (fun k : ℕ => returnTime T hτ k x) :=
        returnTime_strictMono T hτ hc hcpos x
      have := hmono (Nat.pos_of_ne_zero (Nat.pos_iff_ne_zero.mp hNt))
      simpa only [returnTime_zero] using this
    exact ne_of_gt hpos
  exact (log_coverCocycle_div_eq_lapCount A T hτ hc hcpos ht x hrt).symm

end Headline

end ErgodicTheory
