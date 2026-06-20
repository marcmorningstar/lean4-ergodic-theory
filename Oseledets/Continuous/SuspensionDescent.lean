/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionCoverFlow
import Oseledets.Cocycle.Norm

/-!
# The one-lap descent identity of the cover cocycle

This module lands the **one-lap height-reduction (descent) identity** of the cover flow cocycle
`coverCocycle` of `Oseledets.Continuous.SuspensionCoverFlow`, the matrix-level reflection of the
orbit identification

`(x, τ x) ∼ (T x, 0)`

that defines the suspension space `SuspensionSpace T hτ` (the quotient of `X × ℝ` by the suspension
`ℤ`-action `G (x, s) = (T x, s − τ x)` of `Oseledets.Continuous.Suspension` /
`Oseledets.Continuous.SuspensionSpace`). It is the increment one step before a genuine
quotient-well-defined `FlowCocycle` over `SuspensionSpace`.

The geometric content is the standard special-flow / flow-under-a-roof bookkeeping of
Cornfeld–Fomin–Sinai, *Ergodic Theory* (Springer 1982), Ch. 11 (special/suspension flows;
Ambrose–Kakutani), the first-return / ceiling construction underlying Abramov's entropy formula
`h(flow) = h(base)/∫τ`, whose Lyapunov-exponent analogue `λ_flow = λ_base / ∫τ` is the headline
target (Issue #5). The descent direction — the *exponent*, not the matrix, passes to the quotient —
is the design reference of Bessa–Varandas (suspension Lyapunov exponents).

## The descent picture

A cover point `(x, h)` with `h ≥ τ x` is identified, under the suspension generator, with its
re-based representative `(T x, h − τ x)`: the orbit relation glues the top of the roof over `x` to
the base section over `T x`. The cover cocycle does **not** descend to a single matrix on the
quotient class — the two representatives `(x, τ x)` and `(T x, 0)` of the *same* suspension point
carry accumulated matrices that differ by exactly one base factor `A x`. That discrepancy is a
*bounded* (single-step) factor, which is why the matrix itself does not descend but the **growth
rate** (Lyapunov exponent `lim (1/t) log ‖·‖`) does: the extra `log ‖A x‖` is washed out in the
`1/t` Birkhoff average. The two results below make this precise:

* the exact one-lap descent identity (matrices differ by the single base factor `A x`);
* its operator-norm submultiplicative shadow (the norm at the re-based representative controls the
  norm at the original up to the bounded factor `‖A x‖`).

## Main results

* `Oseledets.returnTime_one`: the first return time is the roof value, `returnTime T hτ 1 x = τ x`.
* `Oseledets.coverCocycle_one_lap`: the **one-lap descent identity** — advancing from the base
  section at `x` past one full lap `τ x` then a residual `r ≥ 0` equals advancing from the next base
  point `T x` by `r`, post-multiplied by the single base step `A x`:
  `coverCocycle (x, 0) (τ x + r) = coverCocycle (T x, 0) r * A x`.
* `Oseledets.coverCocycle_one_lap_opNorm_le`: the operator-norm submultiplicative form of the
  descent identity, `‖coverCocycle (x, 0) (τ x + r)‖ ≤ ‖coverCocycle (T x, 0) r‖ * ‖A x‖`, the
  inequality through which the *Lyapunov exponent* (not the matrix) descends to the quotient.

## What is *not* in this file — the remaining gap toward the `SuspensionSpace` `FlowCocycle`

This module lands the *matrix-level* descent at a single lap (and its norm shadow), but a genuine
quotient-well-defined `Oseledets.FlowCocycle` over `SuspensionSpace T hτ` and the suspension flow
needs three further pieces, all deferred:

1. **Quotient-class constancy.** `coverCocycle` is *not* constant on orbit classes (it changes by
   the factor `A x` per lap, exactly `coverCocycle_one_lap`); a descended object must therefore be
   the class-invariant *growth rate* `λ(p) = lim (1/t) log ‖coverCocycle p t‖`, whose invariance
   under the lap re-basing is the `1/t`-washout of the bounded `log ‖A x‖` discrepancy supplied
   here, *not* a literal matrix-valued descent. Packaging that limit as a measurable quotient
   function is the open keystone.
2. **The full additive flow law.** `coverCocycle p (s + t) = coverCocycle (flow s p) t *
   coverCocycle p s` for *arbitrary* (non-return) real times `s, t` — the present file only handles
   the lap-boundary split via `coverCocycle_section_returnTime`; the between-returns additive law in
   the height coordinate is not yet available.
3. **The `MeasurePreservingFlow` exponent.** The exponent-transfer `λ_flow = λ_base / ∫ τ` finally
   requires the per-time measure-preservation of the suspension flow on `(SuspensionSpace,
   suspensionMeasure)` (the descent of the `ℝ`-translation through the fundamental domain, deferred
   in `Oseledets.Continuous.SuspensionSpace`) so that the return-time Birkhoff average
   `(returnTime_tendsto_exponent`/`tendsto_roofAverage_ae`) can be read against the invariant
   measure. The denominator `∫ τ` is Abramov's; the numerator is the base Oseledets exponent.

The present file is self-contained and sorry-free.
-/

open scoped Matrix.Norms.L2Operator

namespace Oseledets

section Descent

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **The first return time is the roof value.** One lap from the cross-section point `x` takes flow
time `τ x`: `returnTime T hτ 1 x = τ x`. It is the one-term roof Birkhoff sum, via
`returnTime_eq_birkhoffSum` and `birkhoffSum_one`. -/
theorem returnTime_one (x : X) : returnTime T hτ 1 x = τ x := by
  rw [returnTime_eq_birkhoffSum, birkhoffSum_one]

/-- **The one-lap descent identity.** Starting on the base section at `x`, advancing the suspension
flow past one full lap `τ x` and then a residual time `r ≥ 0` equals advancing from the *next* base
section point `T x` by `r`, post-multiplied by the single base step `A x`:
`coverCocycle (x, 0) (τ x + r) = coverCocycle (T x, 0) r * A x`.

This is the matrix-level reflection of the suspension orbit identification `(x, τ x) ∼ (T x, 0)`:
the two representatives of the same suspension point carry accumulated matrices that differ by
exactly one base factor `A x`. It is `coverCocycle_section_returnTime` at `n = 1`, with the first
return time rewritten to `τ x` (`returnTime_one`), the iterate `(⇑T)^[1] x` collapsed to `T x`, and
the single-lap base cocycle `cocycle A T 1 x` collapsed to `A x` (`cocycle_one`). -/
theorem coverCocycle_one_lap (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {r : ℝ} (hr : 0 ≤ r) (x : X) :
    coverCocycle A T hτ hc hcpos (x, 0) (τ x + r)
      = coverCocycle A T hτ hc hcpos (T x, 0) r * A x := by
  have h := coverCocycle_section_returnTime A T hτ hc hcpos 1 hr x
  rw [returnTime_one T hτ x] at h
  rw [h, Function.iterate_one, cocycle_one]

/-- **The operator-norm form of the one-lap descent.** Taking the L2 operator norm of the one-lap
descent identity `coverCocycle_one_lap` and applying submultiplicativity (`Matrix.l2_opNorm_mul`)
bounds the norm of the matrix accumulated past one lap by the norm at the re-based representative
times the single bounded base factor `‖A x‖`:
`‖coverCocycle (x, 0) (τ x + r)‖ ≤ ‖coverCocycle (T x, 0) r‖ * ‖A x‖`.

This is the inequality through which the **Lyapunov exponent** descends to the quotient: in the
growth rate `lim (1/t) log ‖coverCocycle p t‖` the extra `log ‖A x‖` from one lap is a bounded
additive term killed by the `1/t` Birkhoff average, so the per-class growth rate is unchanged by the
lap re-basing even though the matrix is not. -/
theorem coverCocycle_one_lap_opNorm_le (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {r : ℝ} (hr : 0 ≤ r)
    (x : X) :
    ‖coverCocycle A T hτ hc hcpos (x, 0) (τ x + r)‖
      ≤ ‖coverCocycle A T hτ hc hcpos (T x, 0) r‖ * ‖A x‖ := by
  rw [coverCocycle_one_lap A T hτ hc hcpos hr x]
  exact Matrix.l2_opNorm_mul _ _

end Descent

end Oseledets
