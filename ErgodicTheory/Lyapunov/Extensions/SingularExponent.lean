/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.Singular

/-!
# The forward singular Lyapunov exponent `γ_k` (`EReal`-valued, invertibility-free)

For a **possibly-singular** matrix cocycle generator `A : X → Matrix (Fin d) (Fin d) ℝ` — no
`det A ≠ 0`, no inverse integrability, only the forward hypothesis `IntegrableLogNorm A μ`
(`log⁺‖A‖ ∈ L¹`) — this module packages the cumulative **forward singular exponent**

`γ_k(x) = limsup_n (1/n) log⁺ sprod_k(A⁽ⁿ⁾ x)`

as an honest `EReal`-valued, everywhere-defined, measurable function. Here `sprod_k` is the
top-`k` singular-value product (`ErgodicTheory.sprod`, the `k`-volume growth). The `limsup` is used
(rather than `limUnder`) so the definition is robustly measurable; on the `μ`-a.e. full set where
the normalized `log⁺ sprod_k` converges (`ErgodicTheory.tendsto_top_posLogSprod`) the `limsup` is the
genuine limit `Γ_k⁺`, so `γ_k = (Γ_k⁺ : EReal)` `μ`-a.e.

The `log⁺` (= `Real.posLog`) form is essential: it is the *convergent* one
(`tendsto_top_posLogSprod`), it is non-negative term-by-term, and it agrees with the genuine
`log` whenever the latter is `≥ 0` (the expanding regime). The genuine `log sprod_k` need not
converge for a singular cocycle (it can fall to `−∞`), which is exactly why `γ_k` is built from
`log⁺` and recorded only as the a.e.-constant *forward* value rather than as a two-sided exponent.

## Main definitions

* `ErgodicTheory.forwardSingularExponent` — the cumulative forward singular exponent `γ_k`, an
  `EReal`-valued `limsup`, defined for every `x` with no invertibility hypothesis.

## Main results

* `ErgodicTheory.measurable_forwardSingularExponent` — `γ_k` is measurable (from `measurable_sprod`
  through the `ℝ → EReal` coercion and `Measurable.limsup`).
* `ErgodicTheory.forwardSingularExponent_nonneg` — `0 ≤ γ_k(x)` for **every** `x` (deterministic:
  each `log⁺`-term is `≥ 0`).
* `ErgodicTheory.forwardSingularExponent_zero` — `γ_0 = 0` everywhere (the empty product is `1`).
* `ErgodicTheory.ae_forwardSingularExponent_eq_coe` — under ergodicity and forward integrability,
  `γ_k = (Γ_k⁺ : EReal)` `μ`-a.e. for a real constant `Γ_k⁺`.
* `ErgodicTheory.ae_forwardSingularExponent_lt_top`, `ErgodicTheory.ae_forwardSingularExponent_ne_bot` —
  `μ`-a.e. finiteness (`γ_k < ⊤` and `⊥ < γ_k`), since `γ_k` a.e. equals a real coercion.

## Implementation notes

* Everything here rests **only** on the `sprod` forward results of
  `ErgodicTheory/Lyapunov/Extensions/Singular.lean`, which need only forward integrability and
  ergodicity. No `det A ≠ 0`, no `log⁺‖A⁻¹‖ ∈ L¹`.
* `γ_k` is the **cumulative** exponent (sum of the top `k` individual exponents), so it is **not**
  antitone in `k`; no monotonicity-in-`k` lemma is stated (only the increments
  `Γ_k − Γ_{k−1}` would be antitone, and those are not built here).
* The genuine-`log` `limsup` is identified with `γ_k` only when `Γ_k⁺ > 0`
  (`ErgodicTheory.limsup_logSprod_eq_top_of_pos`); the contracting case `Γ_k⁺ = 0` breaks that
  equality, so it is not folded into this packaging.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ} {μ : Measure X}

/-- **The forward singular Lyapunov exponent `γ_k`** of a possibly-singular cocycle generator,
as an `EReal`-valued `limsup`:

`γ_k(x) = limsup_n ((1/n) log⁺ sprod_k(A⁽ⁿ⁾ x) : EReal)`,

where `sprod_k = ErgodicTheory.sprod A T k` is the top-`k` singular-value product. The `log⁺`
(`Real.posLog`) form makes the sequence non-negative and convergent `μ`-a.e.
(`tendsto_top_posLogSprod`), and the `limsup` makes `γ_k` everywhere-defined and measurable with
no invertibility hypothesis. On the a.e. full convergence set this `limsup` equals the genuine
forward value `Γ_k⁺` (`ae_forwardSingularExponent_eq_coe`). -/
noncomputable def forwardSingularExponent (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k : ℕ) (x : X) : EReal :=
  Filter.limsup
    (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal)) atTop

/-- **`γ_k` is measurable.** Each `x ↦ (1/n) log⁺ sprod_k(A⁽ⁿ⁾ x)` is measurable: `sprod` is
measurable (`measurable_sprod`, which carries `[NeZero d]`), `log⁺ = max 0 ∘ log` is measurable
(`measurable_const.max Real.measurable_log`), and the scalar multiply is too; its `ℝ → EReal`
coercion is measurable (`measurable_coe_real_ereal`), and the `ℕ`-`limsup` of measurable
`EReal`-valued functions is measurable (`Measurable.limsup`). -/
theorem measurable_forwardSingularExponent [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hAmeas : Measurable A) (hTmeas : Measurable T) (k : ℕ) :
    Measurable (forwardSingularExponent A T k) := by
  refine Measurable.limsup (fun n => ?_)
  refine measurable_coe_real_ereal.comp ?_
  have hposLogFun : Measurable Real.posLog := measurable_const.max Real.measurable_log
  have hposLog : Measurable fun x => Real.posLog (sprod A T k n x) :=
    hposLogFun.comp (measurable_sprod hAmeas hTmeas k n)
  exact measurable_const.mul hposLog

omit [MeasurableSpace X] in
/-- **`γ_k ≥ 0` for every `x`** (deterministic, no hypotheses). Each term
`(1/n) log⁺ sprod_k(A⁽ⁿ⁾ x)` is `≥ 0` (`Real.posLog_nonneg`, `(n:ℝ)⁻¹ ≥ 0`), so its `EReal`
coercion is `≥ 0`, and the `limsup` of an everywhere-`≥ 0` sequence is `≥ 0`
(`le_limsup_of_frequently_le'` on the complete lattice `EReal`). -/
theorem forwardSingularExponent_nonneg (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k : ℕ) (x : X) : 0 ≤ forwardSingularExponent A T k x := by
  refine le_limsup_of_frequently_le' (Frequently.of_forall fun n => ?_)
  exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) Real.posLog_nonneg)

omit [MeasurableSpace X] in
/-- **`γ_0 = 0` everywhere** (deterministic). The empty singular-value product is `1`
(`sprod A T 0 n x = ∏_{i < 0} … = 1`), `log⁺ 1 = 0`, so every term of the defining sequence is
`0` and the `limsup` of the constant-`0` sequence is `0` (`Filter.limsup_const`). -/
theorem forwardSingularExponent_zero (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    forwardSingularExponent A T 0 x = 0 := by
  have hterm : (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T 0 n x) : ℝ) : EReal))
      = fun _ : ℕ => (0 : EReal) := by
    funext n
    simp [sprod, Real.posLog_one]
  rw [forwardSingularExponent, hterm, Filter.limsup_const]

/-- **`γ_k` is `μ`-a.e. a real constant `Γ_k⁺`.** For an ergodic measure-preserving `T` and a
possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹`, there is a real `Γ_k⁺` such that
`γ_k(x) = (Γ_k⁺ : EReal)` for `μ`-a.e. `x`. On the a.e. set where the normalized `log⁺ sprod_k`
sequence converges to `Γ_k⁺` (`tendsto_top_posLogSprod`), its `EReal`-coercion converges to
`(Γ_k⁺ : EReal)` (`continuous_coe_real_ereal`), so the `limsup` defining `γ_k` equals
`(Γ_k⁺ : EReal)` (`Tendsto.limsup_eq`). -/
theorem ae_forwardSingularExponent_eq_coe [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∃ gam : ℝ, ∀ᵐ x ∂μ, forwardSingularExponent A T k x = (gam : EReal) := by
  obtain ⟨gam, hgam⟩ := tendsto_top_posLogSprod hT hAmeas hint k
  refine ⟨gam, ?_⟩
  filter_upwards [hgam] with x hx
  have hxE : Tendsto
      (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T k n x) : ℝ) : EReal)) atTop
      (𝓝 (gam : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hx
  exact hxE.limsup_eq

/-- **`γ_k < ⊤` `μ`-a.e.** Since `γ_k` `μ`-a.e. equals a real coercion
(`ae_forwardSingularExponent_eq_coe`), it is `μ`-a.e. strictly below `⊤`. -/
theorem ae_forwardSingularExponent_lt_top [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∀ᵐ x ∂μ, forwardSingularExponent A T k x < ⊤ := by
  obtain ⟨gam, hgam⟩ := ae_forwardSingularExponent_eq_coe hT hAmeas hint k
  filter_upwards [hgam] with x hx
  rw [hx]; exact EReal.coe_lt_top gam

/-- **`⊥ < γ_k` `μ`-a.e.** Since `γ_k` `μ`-a.e. equals a real coercion
(`ae_forwardSingularExponent_eq_coe`), it is `μ`-a.e. strictly above `⊥`. -/
theorem ae_forwardSingularExponent_ne_bot [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (k : ℕ) :
    ∀ᵐ x ∂μ, ⊥ < forwardSingularExponent A T k x := by
  obtain ⟨gam, hgam⟩ := ae_forwardSingularExponent_eq_coe hT hAmeas hint k
  filter_upwards [hgam] with x hx
  rw [hx]; exact EReal.bot_lt_coe gam

end ErgodicTheory
