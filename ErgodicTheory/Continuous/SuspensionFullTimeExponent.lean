/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionBetweenReturns
import ErgodicTheory.Continuous.SuspensionFlowExponent

/-!
# The full-time special-flow exponent: the between-returns squeeze reduction

This module lands the **clean real-time reduction** underlying the full-time special-flow Lyapunov
exponent `λ_flow = λ_base / ∫τ` (the headline of Issue #5). The return-time version is already
`ErgodicTheory.coverCocycle_returnTime_tendsto_exponent` (of
`ErgodicTheory.Continuous.SuspensionFlowExponent`), which establishes the limit *along the discrete
cross-section return subsequence* `t = returnTime n x`. Upgrading it to *arbitrary real* flow time
`t → ∞` is the between-returns squeeze: this file provides the two exact, sorry-free algebraic
ingredients of that squeeze.

The structural input is the between-returns constancy of
`ErgodicTheory.Continuous.SuspensionBetweenReturns`: on the whole `n`-th lap interval
the cover cocycle
norm is locked to the discrete base cocycle norm. Sampling that constancy at the *lap count*
`n = lapCount t x` (the first-passage index of `ErgodicTheory.Continuous.SuspensionLapCount`,
with its
defining sandwich `returnTime (lapCount t x) x ≤ t < returnTime (lapCount t x + 1) x`) turns the
moving real-time norm into the discrete base norm evaluated at the lap count, *for every* real
`t ≥ 0`:

* `coverCocycle_norm_eq_lapCount`: `‖coverCocycle (x,0) t‖ = ‖cocycle A T (lapCount t x) x‖`.

From there the full-time Birkhoff ratio factors *exactly* — with no sign casework — as a product of
a **time-distortion factor** `returnTime (lapCount t x) x / t` (which tends to `1`, see the gap note
below) and the **return-time exponent ratio** `log‖cocycle A T (lapCount t x) x‖ / returnTime
(lapCount t x) x` (which tends to `λ_base / ∫τ` along the lap subsequence by
`coverCocycle_returnTime_tendsto_exponent`):

* `log_coverCocycle_div_eq_lapCount`:
  `log‖coverCocycle (x,0) t‖ / t
     = (returnTime (lapCount t x) x / t) · (log‖cocycle A T (lapCount t x) x‖ / returnTime
       (lapCount t x) x)`.

This product factorization is the engine of the squeeze: it isolates the two convergent factors and
sidesteps the sign of the logarithm entirely. It is the genuine real-time building block toward the
full-time exponent.

This is the special-flow / flow-under-a-roof construction of Cornfeld–Fomin–Sinai, *Ergodic
Theory* (Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani), the first-return /
ceiling construction underlying Abramov's entropy formula `h(flow) = h(base)/∫τ` (L.M. Abramov, *On
the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875); the Lyapunov-exponent
analogue is the design reference of Bessa–Varandas (suspension Lyapunov exponents).

## Main results

* `ErgodicTheory.coverCocycle_norm_eq_lapCount`: for every `0 ≤ t`, the cover-cocycle norm from the
  base section equals the base cocycle norm at the lap count, `‖coverCocycle (x,0) t‖ =
  ‖cocycle A T (lapCount t x) x‖`. (Lemma A — the real-time norm reduction.)
* `ErgodicTheory.log_coverCocycle_div_eq_lapCount`: for `0 < returnTime (lapCount t x) x` (hence
  `t > 0`), the full-time log-norm ratio factors as the time-distortion factor times the
  return-time exponent ratio. (Lemma B — the squeeze factorization.)

## What is *not* in this file — the precise remaining gap toward the full-time tendsto

The full-time tendsto `(1/t)·log‖coverCocycle (x,0) t‖ → λ_base / ∫τ` as the real `t → ∞` is *not*
assembled here. With Lemma B the squeeze reduces to two convergences, and exactly one of them is
still open:

1. **The return-time exponent factor** — `log‖cocycle A T (lapCount t x) x‖ / returnTime (lapCount t
   x) x → λ_base / ∫τ` — would follow from `coverCocycle_returnTime_tendsto_exponent` *composed with
   the lap count*, using `lapCount t x → ∞` as `t → ∞` (provable from `lapCount_mono` plus
   `returnTime_tendsto_atTop`, but the `atTop`-along-real-`t` composition of an `ℕ`-indexed a.e.
   limit with `lapCount · x` is the genuine real-analysis step and is *not* assembled here).

2. **The time-distortion factor** — `returnTime (lapCount t x) x / t → 1` as `t → ∞` — is the
   *missing analytic input*. The first-passage sandwich gives `returnTime (lapCount t x) x ≤ t <
   returnTime (lapCount t x + 1) x`, so the factor lies in `(returnTime n x / returnTime (n+1) x,
   1]`; squeezing it to `1` needs `returnTime (n+1) x / returnTime n x → 1`, i.e. that the roof
   increment `τ (Tⁿ x)` is `o(returnTime n x)`. Under the present hypotheses there is only a uniform
   *lower* bound `c ≤ τ`; a uniform *upper* bound on `τ` (or `τ ∈ L¹` with a Birkhoff-ratio
   argument) is required and is **not** available here. This is the precise analytic gap.

Beyond these, the **quotient descent** of `coverCocycle` from the cover `X × ℝ` to the orbit
quotient `ErgodicTheory.SuspensionSpace T hτ` (the `(x, τ x) ∼ (T x, 0)` identification, the measure
`μ̂`, and the `MeasurePreservingFlow` packaging) remains the open keystone toward the genuine
space-level headline (cf. the quotient gap documented
in `ErgodicTheory.Continuous.SuspensionCocycle`).
The present file lands the two exact reduction lemmas — sorry-free real-time building blocks — and
documents the remaining tendsto + quotient-descent gap precisely.
-/

open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section FullTimeExponent

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **Real-time norm reduction at the lap count (Lemma A).** For *every* flow time `t ≥ 0`, the
operator norm of the cover cocycle starting on the base section at `x` equals the discrete base
cocycle norm evaluated at the lap count `lapCount t x`, `‖coverCocycle (x, 0) t‖ =
‖cocycle A T (lapCount t x) x‖`. This samples the between-returns constancy
(`coverCocycle_norm_const_between_returns`) at the unique lap interval containing `t`, whose
endpoints are the first-passage sandwich
`returnTime (lapCount t x) x ≤ t < returnTime (lapCount t x + 1) x`
(`lapCount_returnTime_le` / `lapCount_lt_returnTime_succ`). It converts the moving real-time
flow-cocycle norm into the discrete base norm at the lap count, the first step of the
between-returns squeeze toward the full-time exponent. -/
theorem coverCocycle_norm_eq_lapCount (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {t : ℝ} (ht : 0 ≤ t)
    (x : X) :
    ‖coverCocycle A T hτ hc hcpos (x, 0) t‖
      = ‖cocycle A (⇑T) (lapCount T hτ hc hcpos t x) x‖ := by
  have hlo := lapCount_returnTime_le T hτ hc hcpos ht x
  have hhi := lapCount_lt_returnTime_succ T hτ hc hcpos ht x
  exact coverCocycle_norm_const_between_returns A T hτ hc hcpos
    (lapCount T hτ hc hcpos t x) x ht hlo hhi

/-- **The squeeze factorization (Lemma B).** Whenever the lap count's return time is positive,
`0 < returnTime (lapCount t x) x` (which forces `t > 0`, since `returnTime (lapCount t x) x ≤ t`),
the full-time flow log-norm ratio factors *exactly* as the **time-distortion factor**
`returnTime (lapCount t x) x / t` times the **return-time exponent ratio**
`log‖cocycle A T (lapCount t x) x‖ / returnTime (lapCount t x) x`:
`log‖coverCocycle (x, 0) t‖ / t = (returnTime (lapCount t x) x / t) ·
(log‖cocycle A T (lapCount t x) x‖ / returnTime (lapCount t x) x)`.

The proof rewrites the cover-cocycle norm by the lap-count reduction
`coverCocycle_norm_eq_lapCount` and then cancels the common factor `returnTime (lapCount t x) x`
algebraically. This isolates the two convergent factors of the between-returns squeeze (time
distortion `→ 1`; exponent ratio `→
λ_base / ∫τ` along the lap subsequence) with no casework on the sign of the logarithm — the genuine
real-time engine toward the full-time special-flow exponent. -/
theorem log_coverCocycle_div_eq_lapCount (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {t : ℝ} (ht : 0 ≤ t)
    (x : X) (hrt : returnTime T hτ (lapCount T hτ hc hcpos t x) x ≠ 0) :
    Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t
      = (returnTime T hτ (lapCount T hτ hc hcpos t x) x / t)
        * (Real.log ‖cocycle A (⇑T) (lapCount T hτ hc hcpos t x) x‖
            / returnTime T hτ (lapCount T hτ hc hcpos t x) x) := by
  rw [coverCocycle_norm_eq_lapCount A T hτ hc hcpos ht x, div_mul_div_cancel₀' hrt]

end FullTimeExponent

end ErgodicTheory
