/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionDescent
import ErgodicTheory.Continuous.ReturnTimeExponent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Orbit re-basing of the cover cocycle and growth-rate descent

This module makes precise the **open keystone** in the special-flow (suspension) Lyapunov-exponent
program of issue #5: the cover flow cocycle `coverCocycle` of
`ErgodicTheory.Continuous.SuspensionCoverFlow` does **not** descend to a single matrix on the orbit
quotient `SuspensionSpace T hτ`, yet its *growth rate* does. The geometric content is the standard
special-flow / flow-under-a-roof bookkeeping of Cornfeld–Fomin–Sinai, *Ergodic Theory*
(Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani), the first-return / ceiling
construction underlying Abramov's entropy formula `h(flow) = h(base)/∫τ` (L. M. Abramov, *On the
entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875), whose Lyapunov-exponent analogue
`λ_flow = λ_base / ∫τ` is the headline target; the descent direction — the *exponent*, not the
matrix, passes to the quotient — is the design reference of Bessa–Varandas (suspension Lyapunov
exponents).

`ErgodicTheory.Continuous.SuspensionDescent` already handles the **base-section, single-lap** case
(`coverCocycle_one_lap`, on points `(x, 0)`). The present file generalizes to **arbitrary height
`s` and `n` laps under the full orbit action** `suspensionAct (n : ℤ)`, and converts the resulting
exact re-basing into the two-sided bounded operator-norm discrepancy that drives the growth-rate
descent.

## The orbit action and the re-basing

The suspension orbit action is `suspensionAct (n : ℤ) (x, s) = (baseIter n x, s − roofSum n x)`
(`suspensionAct_eq`), which at a natural index `n` reads `((⇑T)^[n] x, s − returnTime n x)`
(`baseIter_natCast`; `returnTime n x = roofSum (n : ℤ) x` by definition). For a flow time `t` large
enough that the residual `r = s + t − returnTime n x` is nonnegative, advancing the suspension flow
for time `t` from `(x, s)` equals advancing for time `t` from the re-based orbit point
`suspensionAct (n : ℤ) (x, s)`, **post-multiplied by the fixed base cocycle `cocycle A T n x`**.
That fixed left-over factor is exactly why the *matrix* cover cocycle fails to descend to the
quotient, while the *growth rate* (the `1/t`-Birkhoff average of `log ‖·‖`) is unchanged: the extra
`log ‖cocycle A T n x‖` is a bounded additive term washed out by the `1/t`.

## Main results

* `ErgodicTheory.coverCocycle_suspensionAct_rebasing`: the **orbit re-basing identity** (the genuine
  descent core; no invertibility needed). For `n : ℕ`, height `s`, flow time `t` with
  `returnTime n x ≤ s + t`,
  `coverCocycle (x, s) t = coverCocycle (suspensionAct (n : ℤ) (x, s)) t * cocycle A T n x`.
* `ErgodicTheory.coverCocycle_suspensionAct_opNorm_le`: the forward operator-norm shadow,
  `‖coverCocycle (x, s) t‖ ≤ ‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖ * ‖cocycle A T n x‖`.
* `ErgodicTheory.coverCocycle_suspensionAct_rebasing_inv`: under base-cocycle invertibility
  (`IsUnit (cocycle A T n x).det`), the **inverse** re-basing,
  `coverCocycle (suspensionAct (n : ℤ) (x, s)) t = coverCocycle (x, s) t * (cocycle A T n x)⁻¹`,
  obtained from the forward identity by cancelling the unit factor on the right.
* `ErgodicTheory.coverCocycle_suspensionAct_opNorm_ge`: the reverse operator-norm shadow under
  invertibility,
  `‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖
      ≤ ‖coverCocycle (x, s) t‖ * ‖(cocycle A T n x)⁻¹‖`.

Together the last two bounds bracket the two cover-cocycle norms by a **fixed multiplicative
constant** (independent of `t`): the matrix discrepancy under one orbit step is the bounded factor
`cocycle A T n x`. This is the inequality through which the Lyapunov exponent — the growth rate
`lim (1/t) log ‖coverCocycle p t‖` — descends to the orbit quotient: a fixed multiplicative factor
becomes a fixed *additive* `log` shift, killed by the `1/t` average.

## What is *not* in this file — the remaining gap toward the `SuspensionSpace` flow exponent

The two-sided bounds above bracket `‖coverCocycle (x, s) t‖` and
`‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖` by the fixed constants `‖cocycle A T n x‖` and
`‖(cocycle A T n x)⁻¹‖`. Converting this into the **two-sided limit transfer**

`Tendsto (fun t ↦ log ‖coverCocycle (x, s) t‖ / t) atTop (𝓝 L)`
  `→ Tendsto (fun t ↦ log ‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖ / t) atTop (𝓝 L)`

needs the bounded *multiplicative* discrepancy to become a bounded *additive* `log` discrepancy,
i.e. `|log ‖coverCocycle (suspensionAct n (x,s)) t‖ − log ‖coverCocycle (x, s) t‖| ≤ C`. Taking
`Real.log` of the two bracketing inequalities requires both cover-cocycle norms to be **strictly
positive** (otherwise `Real.log` of a possibly-zero norm collapses to `0` and breaks the additive
bound). Positivity of `‖coverCocycle p t‖` holds when the base matrices `A` are invertible (so that
every `flowCocycleSection`, a product of `A`-factors, is invertible and hence has positive operator
norm, via the `BetweenTimes` inverse bound `norm_pos_of_det_ne_zero`). That positivity hypothesis,
the additive `log`-discrepancy bound it unlocks, and the resulting `Filter.Tendsto` squeeze
(constant additive error `C` divided by `t → ∞` vanishes) are the remaining gap, deferred to the
`SuspensionSpace` flow-exponent descent. The present file lands the exact re-basing identity (the
genuine matrix-level descent core) and the two-sided bounded operator-norm discrepancy, all
sorry-free.
-/

open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section GrowthDescent

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **The orbit re-basing identity** (the genuine descent core; no invertibility needed).
Advancing the suspension flow for time `t` from a cover point `(x, s)` at arbitrary height `s`,
provided the elapsed time has cleared `n` laps (`returnTime n x ≤ s + t`), equals advancing for the
same time `t` from the re-based orbit point `suspensionAct (n : ℤ) (x, s) = ((⇑T)^[n] x,
s − returnTime n x)`, **post-multiplied by the fixed base cocycle `cocycle A T n x`**:
`coverCocycle (x, s) t = coverCocycle (suspensionAct (n : ℤ) (x, s)) t * cocycle A T n x`.

This is the matrix-level reflection of the suspension orbit action re-basing the accumulated matrix
by the *fixed* factor `cocycle A T n x` per `n` orbit steps — exactly why the matrix cover cocycle
does **not** descend to the orbit quotient. Proof: unfold both `coverCocycle`s to
`flowCocycleSection` of their total elapsed heights (`s + t` on the left; `(s − returnTime n x) + t`
on the right, the residual `r`, via `suspensionAct_eq`, `baseIter_natCast`, and
`returnTime = roofSum`), then apply the section return identity
`coverCocycle_section_returnTime` written with `s + t = returnTime n x + r`. -/
theorem coverCocycle_suspensionAct_rebasing (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X)
    (s t : ℝ) (hst : returnTime T hτ n x ≤ s + t) :
    coverCocycle A T hτ hc hcpos (x, s) t
      = coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t
          * cocycle A (⇑T) n x := by
  -- The residual flow time left after clearing the `n` laps.
  set r : ℝ := s + t - returnTime T hτ n x with hr_def
  have hr : 0 ≤ r := by rw [hr_def]; linarith
  -- Re-base the orbit point: `suspensionAct n (x, s) = ((⇑T)^[n] x, s − returnTime n x)`.
  have hact : suspensionAct T hτ (n : ℤ) (x, s)
      = ((⇑T)^[n] x, s - returnTime T hτ n x) := by
    rw [suspensionAct_eq, baseIter_natCast]
    simp only [returnTime]
  rw [hact]
  -- Both cover cocycles unfold to `flowCocycleSection` of their total elapsed heights:
  -- LHS height `s + t`; RHS height `(s − returnTime n x) + t`.
  simp only [coverCocycle]
  -- Rewrite the two elapsed heights as `returnTime n x + r` and `r` respectively.
  have hheightL : s + t = returnTime T hτ n x + r := by rw [hr_def]; ring
  have hheightR : s - returnTime T hτ n x + t = r := by rw [hr_def]; ring
  rw [hheightL, hheightR]
  -- This is the section return identity, in cover form.
  have hsec := coverCocycle_section_returnTime A T hτ hc hcpos n hr x
  simp only [coverCocycle, zero_add] at hsec
  exact hsec

/-- **Forward operator-norm shadow of the re-basing.** Taking the L2 operator norm of
`coverCocycle_suspensionAct_rebasing` and applying submultiplicativity (`Matrix.l2_opNorm_mul`)
bounds the norm at `(x, s)` by the norm at the re-based orbit point times the fixed factor
`‖cocycle A T n x‖`:
`‖coverCocycle (x, s) t‖ ≤ ‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖ * ‖cocycle A T n x‖`. -/
theorem coverCocycle_suspensionAct_opNorm_le (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X)
    (s t : ℝ) (hst : returnTime T hτ n x ≤ s + t) :
    ‖coverCocycle A T hτ hc hcpos (x, s) t‖
      ≤ ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
          * ‖cocycle A (⇑T) n x‖ := by
  rw [coverCocycle_suspensionAct_rebasing A T hτ hc hcpos n x s t hst]
  exact Matrix.l2_opNorm_mul _ _

/-- **Inverse orbit re-basing under invertibility.** When the base cocycle `cocycle A T n x` is
invertible (its determinant is a unit), the forward re-basing
`coverCocycle (x, s) t = coverCocycle (suspensionAct n (x, s)) t * cocycle A T n x` can be solved
for the re-based cover cocycle by cancelling the unit factor on the right:
`coverCocycle (suspensionAct (n : ℤ) (x, s)) t = coverCocycle (x, s) t * (cocycle A T n x)⁻¹`. -/
theorem coverCocycle_suspensionAct_rebasing_inv (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X)
    (s t : ℝ) (hst : returnTime T hτ n x ≤ s + t)
    (hU : IsUnit (cocycle A (⇑T) n x).det) :
    coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t
      = coverCocycle A T hτ hc hcpos (x, s) t * (cocycle A (⇑T) n x)⁻¹ := by
  rw [coverCocycle_suspensionAct_rebasing A T hτ hc hcpos n x s t hst,
    Matrix.mul_nonsing_inv_cancel_right _ _ hU]

/-- **Reverse operator-norm shadow under invertibility.** Taking the L2 operator norm of the inverse
re-basing `coverCocycle_suspensionAct_rebasing_inv` and applying submultiplicativity bounds the norm
at the re-based orbit point by the norm at `(x, s)` times the fixed inverse factor
`‖(cocycle A T n x)⁻¹‖`:
`‖coverCocycle (suspensionAct (n : ℤ) (x, s)) t‖ ≤ ‖coverCocycle (x, s) t‖ * ‖(cocycle A T n x)⁻¹‖`.

Together with `coverCocycle_suspensionAct_opNorm_le`, this brackets the two cover-cocycle norms by
the fixed multiplicative constants `‖cocycle A T n x‖` and `‖(cocycle A T n x)⁻¹‖`, independent of
the flow time `t`: the bounded multiplicative discrepancy through which the growth rate descends. -/
theorem coverCocycle_suspensionAct_opNorm_ge (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X)
    (s t : ℝ) (hst : returnTime T hτ n x ≤ s + t)
    (hU : IsUnit (cocycle A (⇑T) n x).det) :
    ‖coverCocycle A T hτ hc hcpos (suspensionAct T hτ (n : ℤ) (x, s)) t‖
      ≤ ‖coverCocycle A T hτ hc hcpos (x, s) t‖ * ‖(cocycle A (⇑T) n x)⁻¹‖ := by
  rw [coverCocycle_suspensionAct_rebasing_inv A T hτ hc hcpos n x s t hst hU]
  exact Matrix.l2_opNorm_mul _ _

end GrowthDescent

end ErgodicTheory
