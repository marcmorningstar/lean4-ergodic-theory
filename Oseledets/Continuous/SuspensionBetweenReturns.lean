/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionCoverFlow

/-!
# The special-flow cocycle is constant between base returns

This module records the **between-returns constancy** of the special-flow (suspension) cocycle:
on the whole `n`-th lap interval `returnTime n x ≤ t < returnTime (n + 1) x`, the matrix
accumulated by the suspension flow starting on the base section at `x` is *constant*, equal to the
discrete base cocycle `cocycle A T n x`. Geometrically, the special (suspension) flow acts by the
identity *between* base returns and by the base matrix `A` only *at* each return, so the accumulated
linear action only jumps at the returns and is locked to `A^{(n)}(x)` throughout the open lap. This
is the structural fact that extends the Lyapunov exponent from the discrete return times to *all*
flow times — the between-returns interpolation underlying the special-flow / flow-under-a-roof
exponent transfer `λ_flow = λ_base / ∫τ` (Cornfeld–Fomin–Sinai, *Ergodic Theory*, Springer 1982,
Ch. 11, special/suspension flows; the first-return/ceiling construction underlying Abramov's entropy
formula `h(flow) = h(base)/∫τ`, L.M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR
**128** (1959) 873–875).

The proof rests on the cover-cocycle identity `coverCocycle_base` of
`Oseledets.Continuous.SuspensionCoverFlow` (which reduces `coverCocycle (x, 0) t` to the
cross-section flow cocycle `flowCocycleSection t x`), the definitional unfolding of
`flowCocycleSection` to `suspensionCocycleReturn A T (lapCount t x) x`, and the uniqueness of the
sandwiched lap index `lapCount_unique` of `Oseledets.Continuous.SuspensionCoverCocycle` (which pins
`lapCount t x = n` from the two return-time bounds), together with the return identity
`suspensionCocycleReturn_returnTime` of `Oseledets.Continuous.SuspensionCocycle`.

## Main results

* `Oseledets.coverCocycle_const_between_returns`: on the lap interval
  `returnTime n x ≤ t < returnTime (n + 1) x` (with `0 ≤ t`) the cover cocycle from the base section
  is constant, `coverCocycle (x, 0) t = cocycle A T n x`. The flow cocycle only jumps at the
  returns.
* `Oseledets.coverCocycle_norm_const_between_returns`: the norm specialization,
  `‖coverCocycle (x, 0) t‖ = ‖cocycle A T n x‖` on the same lap interval — the immediate corollary
  used by the between-returns squeeze of the full-time exponent.

## What is *not* in this file — the remaining gap toward the full-time exponent

The **full-time flow exponent** `(1/t) log ‖coverCocycle (x, 0) t‖ → λ_base / ∫τ` as the real time
`t → ∞` is *not* assembled here. The return-time version is already
`Oseledets.coverCocycle_returnTime_tendsto_exponent` (in
`Oseledets.Continuous.SuspensionFlowExponent`); upgrading it to arbitrary real time is a
real-analysis squeeze that combines the present constancy (which replaces `‖coverCocycle (x,0) t‖`
by `‖cocycle A T (lapCount t x) x‖` on each lap) with three asymptotics — `lapCount t x → ∞`,
`returnTime (lapCount t x) x / t → 1`, and the return-time exponent along the lap subsequence — and
then a sandwich `returnTime (N t x) x ≤ t < returnTime (N t x + 1) x` pushed through the logarithm.
That interpolation, together with the descent of `coverCocycle` from the cover `X × ℝ` to the orbit
quotient `Oseledets.SuspensionSpace T hτ` (the `(x, τ x) ∼ (T x, 0)` identification, with the
measure `μ̂` and the `MeasurePreservingFlow` packaging of the suspension flow), is the remaining gap
toward the genuine space-level headline theorem, and is deferred (cf. the quotient gap documented in
`Oseledets.Continuous.SuspensionCocycle`). The present file lands the constancy itself — a
sorry-free structural milestone — and its norm corollary.
-/

open scoped Matrix.Norms.L2Operator

namespace Oseledets

section BetweenReturns

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **The special-flow cocycle is constant between base returns.** Starting on the base section at
`x`, for any flow time `t` in the `n`-th lap interval `returnTime n x ≤ t < returnTime (n + 1) x`
(with `0 ≤ t`), the cover cocycle equals the discrete base cocycle of the `n` completed laps,
`coverCocycle (x, 0) t = cocycle A T n x`, independently of where `t` sits inside the lap. The
special (suspension) flow acts by the identity between returns and by `A` only at the returns, so
the accumulated matrix is locked to `A^{(n)}(x)` across the whole open lap and only jumps at the
next return. This is the between-returns constancy underlying the special-flow exponent transfer
(Cornfeld–Fomin–Sinai, Ch. 11; Abramov). It is proved by reducing the cover cocycle to the section
cocycle (`coverCocycle_base`), unfolding `flowCocycleSection` to the return cocycle at the lap
count, pinning `lapCount t x = n` via the sandwich uniqueness `lapCount_unique`, and reading the
identity `suspensionCocycleReturn_returnTime`. -/
theorem coverCocycle_const_between_returns (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X)
    {t : ℝ} (ht : 0 ≤ t) (hlo : returnTime T hτ n x ≤ t)
    (hhi : t < returnTime T hτ (n + 1) x) :
    coverCocycle A T hτ hc hcpos (x, 0) t = cocycle A (⇑T) n x := by
  rw [coverCocycle_base]
  -- The section flow cocycle is the return cocycle at the lap count; pin the lap count to `n`.
  simp only [flowCocycleSection, lapCount_unique T hτ hc hcpos ht x hlo hhi,
    suspensionCocycleReturn_returnTime]

/-- **Norm constancy between base returns.** The immediate norm corollary of
`coverCocycle_const_between_returns`: on the `n`-th lap interval
`returnTime n x ≤ t < returnTime (n + 1) x` (with `0 ≤ t`), the operator norm of the cover cocycle
from the base section is constant and equal to the norm of the base cocycle of the completed laps,
`‖coverCocycle (x, 0) t‖ = ‖cocycle A T n x‖`. This is the form consumed by the between-returns
squeeze of the full-time exponent: it replaces the moving flow-cocycle norm by the discrete base
cocycle norm sampled at the lap count, whose growth rate is governed by the return-time exponent. -/
theorem coverCocycle_norm_const_between_returns (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X)
    {t : ℝ} (ht : 0 ≤ t) (hlo : returnTime T hτ n x ≤ t)
    (hhi : t < returnTime T hτ (n + 1) x) :
    ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ = ‖cocycle A (⇑T) n x‖ := by
  rw [coverCocycle_const_between_returns A T hτ hc hcpos n x ht hlo hhi]

end BetweenReturns

end Oseledets
