/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionGrowthDescent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Growth-rate (Lyapunov-exponent) descent of the cover cocycle to the orbit quotient

This module turns the two-sided bounded operator-norm **bracket** of
`ErgodicTheory.Continuous.SuspensionGrowthDescent` (the orbit re-basing
`coverCocycle (x, s) t = coverCocycle (suspensionAct n (x, s)) t * cocycle A T n x` and its two
op-norm shadows) into the **limit transfer** that the special-flow / suspension Lyapunov-exponent
program of issue #5 needs: the growth rate `lim (1/t) log ‖coverCocycle p t‖` is the *same* for a
cover point `(x, s)` and its re-based orbit point `suspensionAct (n : ℤ) (x, s)`. This is the
mechanism by which the cover-cocycle growth rate — although the *matrix* cover cocycle does not
descend to the orbit quotient `SuspensionSpace T hτ` — passes to the quotient: a fixed
multiplicative matrix discrepancy `cocycle A T n x` per `n` orbit steps becomes a fixed *additive*
`log` shift, washed out by the `1/t` Birkhoff average.

This is the standard special-flow / flow-under-a-roof bookkeeping of Cornfeld–Fomin–Sinai,
*Ergodic Theory* (Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani), the
first-return / ceiling construction underlying Abramov's entropy formula `h(flow) = h(base)/∫τ`
(L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875), whose
Lyapunov-exponent analogue `λ_flow = λ_base / ∫τ` is the headline target; the descent direction —
the *exponent*, not the matrix, passes to the quotient — is the design reference of Bessa–Varandas
(suspension Lyapunov exponents).

## Main results

* `ErgodicTheory.norm_pos_of_isUnit_det`: an invertible matrix (`IsUnit M.det`) over a nonempty index
  type has strictly positive operator norm (it is nonzero, since the zero matrix has determinant
  `0`, which is not a unit). Provided in the `[NeZero d]` form used downstream.
* `ErgodicTheory.coverCocycle_suspensionAct_log_discrepancy`: the **`t`-independent additive
  `log`-discrepancy bound**. Under base-cocycle invertibility and strict positivity of the two
  cover-cocycle norms, for `returnTime n x ≤ s + t`,
  `|log ‖coverCocycle (suspensionAct n (x, s)) t‖ − log ‖coverCocycle (x, s) t‖|`
  `≤ |log ‖cocycle A T n x‖| + |log ‖(cocycle A T n x)⁻¹‖|`,
  a constant in `t` (absolute values keep the bound honest: an operator norm need not be `≥ 1`, so
  an individual `log`-norm can be negative). Obtained by taking `Real.log` of the two op-norm
  brackets
  (`coverCocycle_suspensionAct_opNorm_le` / `_opNorm_ge`) via `Real.log_le_log` and `Real.log_mul`.
* `ErgodicTheory.coverCocycle_suspensionAct_tendsto_exponent`: **the limit transfer** (headline). If the
  cover-cocycle growth rate `(1/t) log ‖coverCocycle (x, s) t‖` converges to `L` as `t → ∞`, and
  the base cocycle is invertible with both cover-cocycle norms eventually strictly positive, then
  `(1/t) log ‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖` converges to the *same* `L`. Proved
  by a `Filter.Tendsto` squeeze: the per-`t` average at the re-based point lies within
  `(constant)/t` of the average at `(x, s)`, and `(constant)/t → 0`.

## gap

The space-level statement on `SuspensionSpace T hτ` is assembled elsewhere
(`coverCocycle_tendsto_exponent_of_bddRoof` for the bounded-roof section exponent, and the
base-a.e.→μ̂-a.e. disintegration `ae_suspensionMeasure_*` of
`ErgodicTheory.Continuous.SuspensionDisintegration`); this file supplies only the representative-free
*re-basing invariance* of the growth rate. The strict-positivity hypotheses on the two
cover-cocycle norms are taken **explicitly** rather than derived here: positivity of
`‖coverCocycle p t‖` holds when the base matrices `A` are invertible (every `flowCocycleSection` is
then a product of invertible `A`-factors, hence nonzero with positive operator norm), but that
derivation lives with the `flowCocycleSection` invertibility infrastructure and is not re-proved
here. No `λ_flow = λ_base / ∫τ` quotient identity is claimed in this module.
-/

open Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section ExponentDescent

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **Positivity of the operator norm of an invertible matrix.** If `M.det` is a unit then `M` is
nonzero (the zero matrix has determinant `0` over a nonempty index type, which is not a unit), so
its L2 operator norm is strictly positive. Stated in the `[NeZero d]` form: `NeZero d` provides the
`Nonempty (Fin d)` needed for `Matrix.det_zero`. -/
theorem norm_pos_of_isUnit_det [NeZero d] {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : IsUnit M.det) : 0 < ‖M‖ := by
  have hne : M ≠ 0 := by
    rintro rfl
    rw [Matrix.det_zero (by exact ⟨0, by simp [NeZero.pos d]⟩)] at hM
    exact (not_isUnit_zero) hM
  rwa [norm_pos_iff]

/-- **The `t`-independent additive `log`-discrepancy bound.** Taking `Real.log` of the two op-norm
brackets `coverCocycle_suspensionAct_opNorm_le` and `coverCocycle_suspensionAct_opNorm_ge` (valid
once `returnTime n x ≤ s + t`), under invertibility of the base cocycle and strict positivity of
both cover-cocycle norms, the two `log`-norms differ by at most the **constant** (in `t`)
`log ‖cocycle A T n x‖ + log ‖(cocycle A T n x)⁻¹‖`:
`|log ‖coverCocycle (suspensionAct n (x, s)) t‖ − log ‖coverCocycle (x, s) t‖|`
`≤ log ‖cocycle A T n x‖ + log ‖(cocycle A T n x)⁻¹‖`.
This is the bounded multiplicative discrepancy of `SuspensionGrowthDescent` turned additive — the
shift the `1/t` Birkhoff average will wash out. -/
theorem coverCocycle_suspensionAct_log_discrepancy [NeZero d] (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (n : ℕ) (x : X) (s t : ℝ) (hst : returnTime T hτ n x ≤ s + t)
    (hU : IsUnit (cocycle A (⇑T) n x).det)
    (hp : 0 < ‖coverCocycle A T hτ hc hcpos (x, s) t‖)
    (hq : 0 < ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖) :
    |Real.log ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
        - Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖|
      ≤ |Real.log ‖cocycle A (⇑T) n x‖| + |Real.log ‖(cocycle A (⇑T) n x)⁻¹‖| := by
  -- Strict positivity of the two fixed factors, from invertibility.
  have hcocpos : 0 < ‖cocycle A (⇑T) n x‖ := norm_pos_of_isUnit_det hU
  have hcocinvpos : 0 < ‖(cocycle A (⇑T) n x)⁻¹‖ := by
    refine norm_pos_of_isUnit_det (M := (cocycle A (⇑T) n x)⁻¹) (Ne.isUnit ?_)
    intro h0
    have := Matrix.det_nonsing_inv_mul_det (cocycle A (⇑T) n x) hU
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  -- Upper bound on `log ‖q‖`: from `‖p‖ ≤ ‖q‖ * ‖cocycle‖` (opNorm_le).
  have hup : Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖
      ≤ Real.log ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
          + Real.log ‖cocycle A (⇑T) n x‖ := by
    have hle := coverCocycle_suspensionAct_opNorm_le A T hτ hc hcpos n x s t hst
    calc Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖
        ≤ Real.log (‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
            * ‖cocycle A (⇑T) n x‖) := Real.log_le_log hp hle
      _ = Real.log ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
            + Real.log ‖cocycle A (⇑T) n x‖ := Real.log_mul (ne_of_gt hq) (ne_of_gt hcocpos)
  -- Upper bound on `log ‖p‖` reversed: from `‖q‖ ≤ ‖p‖ * ‖cocycle⁻¹‖` (opNorm_ge).
  have hge : Real.log ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
      ≤ Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖
          + Real.log ‖(cocycle A (⇑T) n x)⁻¹‖ := by
    have hle := coverCocycle_suspensionAct_opNorm_ge A T hτ hc hcpos n x s t hst hU
    calc Real.log ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
        ≤ Real.log (‖coverCocycle A T hτ hc hcpos (x, s) t‖
            * ‖(cocycle A (⇑T) n x)⁻¹‖) := Real.log_le_log hq hle
      _ = Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖
            + Real.log ‖(cocycle A (⇑T) n x)⁻¹‖ :=
          Real.log_mul (ne_of_gt hp) (ne_of_gt hcocinvpos)
  -- Assemble the two-sided bound. `Q - P ≤ log‖inv‖ ≤ |log‖inv‖|` (from `hge`) gives the upper
  -- side; `P - Q ≤ log‖cocycle‖ ≤ |log‖cocycle‖|` (from `hup`) gives the lower side. Each `log`
  -- factor is bounded by its absolute value (`le_abs_self`, `neg_abs_le`), so the sum dominates.
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 : Real.log ‖cocycle A (⇑T) n x‖ ≤ |Real.log ‖cocycle A (⇑T) n x‖| := le_abs_self _
    have h2 : (0 : ℝ) ≤ |Real.log ‖(cocycle A (⇑T) n x)⁻¹‖| := abs_nonneg _
    linarith [hup]
  · have h1 : Real.log ‖(cocycle A (⇑T) n x)⁻¹‖ ≤ |Real.log ‖(cocycle A (⇑T) n x)⁻¹‖| :=
      le_abs_self _
    have h2 : (0 : ℝ) ≤ |Real.log ‖cocycle A (⇑T) n x‖| := abs_nonneg _
    linarith [hge]

set_option maxHeartbeats 400000 in -- the squeeze threads several `Tendsto` combinators plus a
-- per-`t` `abs_le`/`div` sandwich over the long `coverCocycle` terms; the default budget is exceeded
/-- **The Lyapunov-exponent limit transfer (headline).** If the cover-cocycle growth rate
`(1/t) log ‖coverCocycle (x, s) t‖` converges to `L` as `t → ∞`, the base cocycle `cocycle A T n x`
is invertible, and both cover-cocycle norms are eventually strictly positive (for all large `t`),
then the cover-cocycle growth rate at the **re-based orbit point** `suspensionAct (n : ℤ) (x, s)`
converges to the *same* `L`:
`Tendsto (fun t ↦ log ‖coverCocycle (x, s) t‖ / t) atTop (𝓝 L)`
`→ Tendsto (fun t ↦ log ‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖ / t) atTop (𝓝 L)`.

The per-`t` average at the re-based point lies within `(C)/t` of the average at `(x, s)`, where
`C = |log ‖cocycle A T n x‖| + |log ‖(cocycle A T n x)⁻¹‖|` is the `t`-independent additive
`log`-discrepancy of `coverCocycle_suspensionAct_log_discrepancy`; since `C / t → 0`, a
`Filter.Tendsto` squeeze transfers the limit. This is the representative-free invariance of the
growth rate under the orbit action — the mechanism of the special-flow exponent descent. -/
theorem coverCocycle_suspensionAct_tendsto_exponent [NeZero d] (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (n : ℕ) (x : X) (s : ℝ) (hU : IsUnit (cocycle A (⇑T) n x).det)
    (hret : ∀ᶠ t : ℝ in atTop, returnTime T hτ n x ≤ s + t)
    (hp : ∀ᶠ t : ℝ in atTop, 0 < ‖coverCocycle A T hτ hc hcpos (x, s) t‖)
    (hq : ∀ᶠ t : ℝ in atTop,
        0 < ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖)
    {L : ℝ}
    (hL : Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖ / t)
        atTop (𝓝 L)) :
    Tendsto (fun t : ℝ =>
        Real.log ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖ / t)
      atTop (𝓝 L) := by
  set C : ℝ := |Real.log ‖cocycle A (⇑T) n x‖| + |Real.log ‖(cocycle A (⇑T) n x)⁻¹‖| with hCdef
  -- Abbreviate the two `log`-norm functions.
  set P : ℝ → ℝ := fun t => Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖ with hPdef
  set Q : ℝ → ℝ := fun t =>
    Real.log ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖ with hQdef
  -- The two squeezing functions: `(P t - C)/t` and `(P t + C)/t`, both → `L`.
  have hConst : Tendsto (fun t : ℝ => C / t) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hLo : Tendsto (fun t : ℝ => P t / t - C / t) atTop (𝓝 L) := by
    have := hL.sub hConst
    simpa using this
  have hUp : Tendsto (fun t : ℝ => P t / t + C / t) atTop (𝓝 L) := by
    have := hL.add hConst
    simpa using this
  -- The eventual two-sided sandwich `(P t - C)/t ≤ Q t / t ≤ (P t + C)/t`.
  have hsand : ∀ᶠ t : ℝ in atTop,
      P t / t - C / t ≤ Q t / t ∧ Q t / t ≤ P t / t + C / t := by
    filter_upwards [hret, hp, hq, eventually_gt_atTop (0 : ℝ)]
      with t htret htp htq htpos
    have hdisc := coverCocycle_suspensionAct_log_discrepancy
      A T hτ hc hcpos n x s t htret hU htp htq
    rw [abs_le] at hdisc
    obtain ⟨hd1, hd2⟩ := hdisc
    -- `hd1 : -C ≤ Q t - P t`, `hd2 : Q t - P t ≤ C` (P, Q as set above).
    have hinv : 0 < t⁻¹ := inv_pos.2 htpos
    refine ⟨?_, ?_⟩
    · have : (P t - C) * t⁻¹ ≤ Q t * t⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith [hd1]) (le_of_lt hinv)
      rw [sub_mul] at this
      simpa only [div_eq_mul_inv] using this
    · have : Q t * t⁻¹ ≤ (P t + C) * t⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith [hd2]) (le_of_lt hinv)
      rw [add_mul] at this
      simpa only [div_eq_mul_inv] using this
  -- Split the conjunction into the two one-sided eventual bounds and squeeze.
  have hlow : ∀ᶠ t : ℝ in atTop, P t / t - C / t ≤ Q t / t := hsand.mono fun _ h => h.1
  have hupp : ∀ᶠ t : ℝ in atTop, Q t / t ≤ P t / t + C / t := hsand.mono fun _ h => h.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hUp hlow hupp

end ExponentDescent

end ErgodicTheory
