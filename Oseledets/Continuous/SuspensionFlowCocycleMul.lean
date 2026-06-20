/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionFlowCocycle

/-!
# Multiplicativity of the section flow cocycle at return times

This module records the **cocycle multiplicativity of the special-flow cross-section cocycle**,
read off at the base return times. On the suspension (mapping torus) of a base map `T` under a
strictly positive roof `τ`, sampling the section flow cocycle `flowCocycleSection` at the integer
lap time `t = returnTime n x` recovers the discrete base cocycle `cocycle A T n x`
(`flowCocycleSection_returnTime`). Composing two such samples therefore inherits the base cocycle
identity `cocycle_add`, with the characteristic shift of the base point by `T^[n]` for the later
block. This is exactly the continuous-time `FlowCocycle` cocycle identity sampled at the return
times — the base-cocycle multiplicativity that the space-level `SuspensionSpace` `FlowCocycle`
descends from (Cornfeld–Fomin–Sinai, *Ergodic Theory*, Springer 1982, Ch. 11, special/suspension
flows; the first-return/ceiling construction underlying Abramov's entropy formula).

The construction sits on top of `Oseledets.Continuous.SuspensionFlowCocycle`
(`flowCocycleSection`, `flowCocycleSection_returnTime`) and the base cocycle identity of
`Oseledets.Cocycle.Basic` (`cocycle_add`, `cocycle_one`).

## Main results

* `Oseledets.flowCocycleSection_returnTime_add`: sampling the section flow cocycle at the
  `(n + m)`-th return time factors as the base cocycle over the last `m` returns (started from the
  shifted point `T^[n] x`) times the base cocycle over the first `n` returns.
* `Oseledets.flowCocycleSection_returnTime_succ`: the one-return step — sampling at the
  `(n + 1)`-th return time left-multiplies the `n`-th sample by the generator `A` at `T^[n] x`.
-/

namespace Oseledets

section FlowCocycleSectionMul

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **Multiplicativity of the section flow cocycle at return times.** Sampling the special-flow
cross-section cocycle at the `(n + m)`-th return time factors as the discrete base cocycle over the
last `m` returns — started from the shifted cross-section point `T^[n] x` — times the base cocycle
over the first `n` returns. This is the `FlowCocycle` cocycle identity sampled at the return times:
by `flowCocycleSection_returnTime` the sample at the `(n + m)`-th return is `cocycle A T (n + m) x`,
and the base identity `cocycle_add` splits it with the `T^[n]` base-point shift. -/
theorem flowCocycleSection_returnTime_add (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n m : ℕ) (x : X) :
    flowCocycleSection A T hτ hc hcpos (returnTime T hτ (n + m) x) x
      = cocycle A (⇑T) m ((⇑T)^[n] x) * cocycle A (⇑T) n x := by
  rw [flowCocycleSection_returnTime A T hτ hc hcpos (n + m) x, Nat.add_comm n m,
    cocycle_add A (⇑T) m n x]

/-- **One-return step of the section flow cocycle.** Advancing the sample from the `n`-th to the
`(n + 1)`-th return time left-multiplies by the generator `A` evaluated at the shifted cross-section
point `T^[n] x`. This is the single-step case of `flowCocycleSection_returnTime_add` (with `m = 1`),
collapsed through `cocycle_one`. -/
theorem flowCocycleSection_returnTime_succ (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X) :
    flowCocycleSection A T hτ hc hcpos (returnTime T hτ (n + 1) x) x
      = A ((⇑T)^[n] x) * cocycle A (⇑T) n x := by
  rw [flowCocycleSection_returnTime_add A T hτ hc hcpos n 1 x, cocycle_one A (⇑T)]

end FlowCocycleSectionMul

end Oseledets
