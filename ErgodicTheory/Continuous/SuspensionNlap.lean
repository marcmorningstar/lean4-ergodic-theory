/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionDescent

/-!
# The `n`-lap operator-norm control of the cover cocycle at the section

This module lands the **`n`-lap (quantitative) operator-norm control** of the cover flow cocycle
`coverCocycle` of `ErgodicTheory.Continuous.SuspensionCoverFlow` *at the base section*. Where
`ErgodicTheory.Continuous.SuspensionDescent` recorded the single-lap descent identity and its norm
shadow, this file iterates it across `n` completed return laps: it ties the cover-cocycle norm at
the `n`-th return time exactly to the discrete base cocycle norm `‖cocycle A T n x‖`.

This is the quantitative input to the exponent-descent half of the special-flow exponent transfer
`λ_flow = λ_base / ∫τ` (Issue #5). The geometric bookkeeping is the standard special-flow /
flow-under-a-roof construction of Cornfeld–Fomin–Sinai, *Ergodic Theory* (Springer 1982), Ch. 11
(special/suspension flows; Ambrose–Kakutani), the first-return / ceiling construction underlying
Abramov's entropy formula `h(flow) = h(base)/∫τ`; the Lyapunov-exponent analogue is the design
reference of Bessa–Varandas (suspension Lyapunov exponents). The point of the exact identity below
is that, *at the section sampled along return times*, there is no bounded discrepancy to wash out:
the cover cocycle norm at `returnTime n x` equals the base cocycle norm on the nose, so the
return-time Birkhoff average `(1/returnTime n x)·log‖coverCocycle (x,0) (returnTime n x)‖` is
literally the rescaled base growth `(n/returnTime n x)·(1/n)·log‖cocycle A T n x‖`.

## Main results

* `ErgodicTheory.coverCocycle_returnTime_opNorm_le`: the **`n`-lap submultiplicative bound** with a
  residual `r ≥ 0`,
  `‖coverCocycle (x,0) (returnTime n x + r)‖ ≤ ‖coverCocycle (Tⁿ x, 0) r‖ * ‖cocycle A T n x‖`,
  directly from `coverCocycle_section_returnTime` and L2-norm submultiplicativity
  (`Matrix.l2_opNorm_mul`).
* `ErgodicTheory.coverCocycle_returnTime_eq`: at the residual `r = 0` the cover cocycle at
  the `n`-th
  return time **is** the base cocycle, `coverCocycle (x,0) (returnTime n x) = cocycle A T n x`.
* `ErgodicTheory.coverCocycle_returnTime_norm_eq`: the operator-norm bridge,
  `‖coverCocycle (x,0) (returnTime n x)‖ = ‖cocycle A T n x‖`, tying the cover-cocycle norm at
  return times exactly to the base cocycle norm.

## What is *not* in this file — the remaining gap toward the `MeasurePreservingFlow` exponent

The norm bridge `coverCocycle_returnTime_norm_eq` is the *quantitative* half of the exponent
descent: combined with the return-time exponent `ErgodicTheory.returnTime_tendsto_exponent` (and the
roof Birkhoff average `ErgodicTheory.tendsto_roofAverage_ae`) it yields
`(1/returnTime n x)·log‖coverCocycle (x,0)(returnTime n x)‖ → λ_base / ∫τ` along the return
subsequence. Three pieces remain, all deferred (as in `SuspensionDescent` /
`SuspensionCoverFlow`):

1. **The between-returns interpolation.** The limit above is along the discrete return times
   `returnTime n x`; upgrading it to the full continuous-time limit `(1/t)·log‖coverCocycle p t‖`
   over arbitrary real `t → ∞` needs the residual control `coverCocycle_returnTime_opNorm_le`
   sandwiched between consecutive returns (the bounded-residual squeeze) plus the additive flow law
   in the height coordinate, neither assembled here.
2. **Quotient descent to `SuspensionSpace`.** The growth rate must be read as a class-invariant
   function on the orbit quotient (the `1/t`-washout of the per-lap `log‖A x‖` discrepancy of
   `coverCocycle_one_lap`); packaging it as a measurable quotient function is the open keystone.
3. **The `MeasurePreservingFlow` exponent.** Reading `λ_flow = λ_base / ∫τ` against the invariant
   suspension measure needs the per-time measure-preservation of the suspension flow on
   `(SuspensionSpace, suspensionMeasure)`. The denominator `∫τ` is Abramov's; the numerator is the
   base Oseledets exponent.

The present file is self-contained and sorry-free.
-/

open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section Nlap

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **The `n`-lap operator-norm control at the section.** Taking the L2 operator norm of the
section return-boundary identity `coverCocycle_section_returnTime` and applying submultiplicativity
(`Matrix.l2_opNorm_mul`) bounds the cover-cocycle norm accumulated past `n` completed laps and a
residual `r ≥ 0` by the norm at the re-based residual representative `Tⁿ x` times the discrete base
cocycle norm:
`‖coverCocycle (x,0) (returnTime n x + r)‖ ≤ ‖coverCocycle (Tⁿ x, 0) r‖ * ‖cocycle A T n x‖`.
This is the quantitative input to the exponent descent (the `n`-lap operator-norm form of the
single-lap descent identity `coverCocycle_one_lap`). -/
theorem coverCocycle_returnTime_opNorm_le (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (x : X) :
    ‖coverCocycle A T hτ hc hcpos (x, 0) (returnTime T hτ n x + r)‖
      ≤ ‖coverCocycle A T hτ hc hcpos ((⇑T)^[n] x, 0) r‖ * ‖cocycle A (⇑T) n x‖ := by
  rw [coverCocycle_section_returnTime A T hτ hc hcpos n hr x]
  exact Matrix.l2_opNorm_mul _ _

/-- **The cover cocycle at the `n`-th return time is the base cocycle.** Sampling the cover cocycle
on the base section exactly at the `n`-th return time (residual `r = 0`) recovers the discrete base
cocycle:
`coverCocycle (x,0) (returnTime n x) = cocycle A T n x`.
The cover cocycle on the section reduces to the cross-section flow cocycle (`coverCocycle_base`),
and the section flow cocycle at an integer lap time is the base cocycle
(`flowCocycleSection_returnTime`: there `lapCount (returnTime n x) x = n` and the return cocycle at
`n` is `cocycle`). -/
theorem coverCocycle_returnTime_eq (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X) :
    coverCocycle A T hτ hc hcpos (x, 0) (returnTime T hτ n x) = cocycle A (⇑T) n x := by
  rw [coverCocycle_base, flowCocycleSection_returnTime]

/-- **The cover-cocycle norm bridge at return times.** Taking norms in `coverCocycle_returnTime_eq`,
the cover-cocycle operator norm at the `n`-th return time equals the discrete base cocycle norm on
the nose: `‖coverCocycle (x,0) (returnTime n x)‖ = ‖cocycle A T n x‖`. This is the bridge from which
the rescaled growth `(1/returnTime n x)·log‖coverCocycle‖ → λ_base / ∫τ` follows along the return
subsequence by `returnTime_tendsto_exponent` (the between-returns/quotient/measure pieces remain;
see the module header). -/
theorem coverCocycle_returnTime_norm_eq (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X) :
    ‖coverCocycle A T hτ hc hcpos (x, 0) (returnTime T hτ n x)‖ = ‖cocycle A (⇑T) n x‖ := by
  rw [coverCocycle_returnTime_eq A T hτ hc hcpos n x]

end Nlap

end ErgodicTheory
