/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionLapCount

/-!
# The special-flow cocycle on the base section

This module assembles the **flow cocycle on the cross-section** of a special (suspension) flow.
On the suspension (mapping torus) of a base map `T` under a strictly positive roof `τ`, the natural
flow advances the time coordinate and acts linearly by the base matrix `A` once per completed lap
(base return), and by the identity between laps. Reading the lap counter
`lapCount T hτ hc hcpos t x` (Cornfeld–Fomin–Sinai, *Ergodic Theory*, Springer 1982, Ch. 11,
special/suspension flows; the first-return/ceiling construction underlying Abramov's entropy
formula), the matrix accumulated by flow time `t` starting on the base section at `x` is the
return cocycle evaluated at the number of completed laps.

The construction sits on top of the lap-counter first-passage API of
`Oseledets.Continuous.SuspensionLapCount` (`lapCount_returnTime_le`, `lapCount_lt_returnTime_succ`,
`returnTime_strictMono`) and the return cocycle of `Oseledets.Continuous.SuspensionCocycle`
(`suspensionCocycleReturn`, `cocycle_add`).

## Main definitions

* `Oseledets.flowCocycleSection`: `flowCocycleSection A T hτ hc hcpos t x` is the matrix accumulated
  by flow time `t` starting on the base section at `x`, namely the return cocycle at `lapCount t x`.

## Main results

* `Oseledets.lapCount_returnTime_eq`: the lap count at exactly the `n`-th return time is `n`, pinned
  by the first-passage sandwich and the strict monotonicity of the return times.
* `Oseledets.flowCocycleSection_returnTime`: at an integer lap time `t = returnTime n x` the flow
  cocycle on the section equals the discrete base cocycle `cocycle A T n x`.
* `Oseledets.flowCocycleSection_zero`: at flow time `0` the flow cocycle on the section is the
  identity matrix.

Measurability in `x` at fixed flow time `t` is *not* assembled here: `lapCount t x` is
`Nat.findGreatest` of an `x`-dependent predicate whose latch bound also varies with `x`, so the
section cocycle is a measurable selection over the (non-constant) lap value, which the present
`Nat.findGreatest`-measurability infrastructure does not close cleanly. It is therefore omitted.
-/

namespace Oseledets

section FlowCocycleSection

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **The special-flow cocycle on the base section.** The matrix accumulated by the suspension flow
over flow time `t`, starting from the cross-section point `x`: the flow acts by the base matrix `A`
once per completed lap and by the identity between laps, so the accumulated action is the return
cocycle `suspensionCocycleReturn A T n x` evaluated at the number `n = lapCount t x` of completed
laps. This is the cross-section flow cocycle of the special (suspension) flow (Cornfeld–Fomin–Sinai,
*Ergodic Theory*, Springer 1982, Ch. 11, special flows). -/
noncomputable def flowCocycleSection (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) (x : X) :
    Matrix (Fin d) (Fin d) ℝ :=
  suspensionCocycleReturn A (⇑T) (lapCount T hτ hc hcpos t x) x

/-- **The lap count at the `n`-th return time is `n`.** At exactly the flow time `returnTime n x`,
the number of completed laps is `n`. The lower-bound half of the first-passage sandwich gives
`returnTime (lapCount …) x ≤ returnTime n x`, hence `lapCount … ≤ n` by strict monotonicity; the
upper-bound half gives `returnTime n x < returnTime (lapCount … + 1) x`, hence `n ≤ lapCount …`. -/
theorem lapCount_returnTime_eq (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X) :
    lapCount T hτ hc hcpos (returnTime T hτ n x) x = n := by
  have hmono : StrictMono (fun m : ℕ => returnTime T hτ m x) :=
    returnTime_strictMono T hτ hc hcpos x
  have ht : 0 ≤ returnTime T hτ n x := by
    have := hmono.monotone (Nat.zero_le n)
    simpa only [returnTime_zero] using this
  -- Lower-bound half: `returnTime (lapCount …) x ≤ returnTime n x`, so `lapCount … ≤ n`.
  have hle : lapCount T hτ hc hcpos (returnTime T hτ n x) x ≤ n := by
    have hsand := lapCount_returnTime_le T hτ hc hcpos ht x
    exact hmono.le_iff_le.mp hsand
  -- Upper-bound half: `returnTime n x < returnTime (lapCount … + 1) x`, so `n < lapCount … + 1`.
  have hge : n ≤ lapCount T hτ hc hcpos (returnTime T hτ n x) x := by
    have hsand := lapCount_lt_returnTime_succ T hτ hc hcpos ht x
    have : n < lapCount T hτ hc hcpos (returnTime T hτ n x) x + 1 := hmono.lt_iff_lt.mp hsand
    exact Nat.lt_succ_iff.mp this
  exact le_antisymm hle hge

/-- **The flow cocycle on the section at a return time.** Sampling the section flow cocycle at the
integer lap time `t = returnTime n x` recovers the discrete base cocycle `cocycle A T n x`: by
`lapCount_returnTime_eq` the lap count there is `n`, and the return cocycle at `n` is `cocycle`. -/
theorem flowCocycleSection_returnTime (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X) :
    flowCocycleSection A T hτ hc hcpos (returnTime T hτ n x) x = cocycle A (⇑T) n x := by
  simp only [flowCocycleSection, lapCount_returnTime_eq T hτ hc hcpos n x,
    suspensionCocycleReturn_returnTime]

/-- **The flow cocycle on the section at time `0` is the identity.** At flow time `0` no lap has
completed (`lapCount 0 x = 0`, since `returnTime 0 x = 0 ≤ 0`), and the return cocycle at `0` is the
identity matrix. -/
theorem flowCocycleSection_zero (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (x : X) :
    flowCocycleSection A T hτ hc hcpos 0 x = 1 := by
  have h0 : lapCount T hτ hc hcpos (returnTime T hτ 0 x) x = 0 :=
    lapCount_returnTime_eq T hτ hc hcpos 0 x
  rw [returnTime_zero] at h0
  simp only [flowCocycleSection, h0, suspensionCocycleReturn_zero]

end FlowCocycleSection

end Oseledets
