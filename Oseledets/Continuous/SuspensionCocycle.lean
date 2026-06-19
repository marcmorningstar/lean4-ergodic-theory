/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.ReturnTimeExponent

/-!
# The suspension return cocycle

This module builds the **return-indexed linear cocycle** of a suspension: the value the
suspension flow cocycle takes when the flow crosses base-return times. On the suspension
(mapping-torus) of a base map `T` under a roof function `τ`, the natural flow `ζ_t` advances the
time coordinate, and the linear action is the identity *between* base returns and the base matrix
`A` *at* each return. After `n` returns starting from a base point `x` on the cross-section, the
accumulated linear action is therefore exactly the discrete iterated cocycle `cocycle A T n x`.

This is the cross-section reduction of the (continuous-time) suspension flow cocycle to the
discrete base cocycle. The flow time elapsed over the first `n` returns from `x` is the roof
Birkhoff sum `roofSum T hτ n x` (`returnTime`), so the pair
`(returnTime n x, suspensionCocycleReturn A T n x)` records the *time–matrix* schedule of the lift
along the cross-section orbit of `x`.

## Main definitions

* `Oseledets.suspensionCocycleReturn`: the return cocycle `n ↦ cocycle A T n x`, the linear action
  accumulated over `n` base returns from the cross-section point `x`.
* `Oseledets.returnTime`: the flow time `roofSum T hτ n x` elapsed over `n` returns from `x`.

## Main results

* `Oseledets.suspensionCocycleReturn_add`: the return-cocycle multiplicativity, read off from the
  base cocycle identity `cocycle_add`:
  `suspensionCocycleReturn A T (m + n) x = suspensionCocycleReturn A T m (T^[n] x)
  * suspensionCocycleReturn A T n x`.
* `Oseledets.returnTime_add`: the additivity of the return time along the cross-section orbit,
  `returnTime (m + n) x = returnTime m (T^[n] x) + returnTime n x`, the time-coordinate companion
  of the matrix multiplicativity (read off from `roofSum_natCast_eq_birkhoffSum` and the Birkhoff
  cocycle property).
* `Oseledets.measurable_suspensionCocycleReturn`: each return level is measurable.
* `Oseledets.suspensionCocycleReturn_returnTime`: the **return identity** in cross-section form —
  at the `n`-th return (flow time `returnTime n x`) the accumulated linear action is the base
  iterated cocycle `cocycle A T n x`. Stated as the definitional equality that ties the
  time-indexed schedule to the base cocycle.

## What is *not* in this file — the remaining gap toward the full flow cocycle

A genuine `Oseledets.FlowCocycle` instance over the suspension *space*
`Oseledets.SuspensionSpace T hτ` and the flow `Oseledets.suspensionFlowMap` is **not** built here.
`FlowCocycle φ d` (`Oseledets.Continuous.Flow`) requires a map `Ψ : ℝ → SuspensionSpace → Matrix`
satisfying the continuous cocycle identity `Ψ (t + s) [p] = Ψ t (ζ s [p]) * Ψ s [p]` for *all*
real `t, s`. Defining `Ψ t [x, s]` requires counting how many base returns the flow of duration `t`
crosses starting from the representative `(x, s)` — i.e. evaluating the integer return-count
function `n ↦ (unique k with suspensionAct k (x, s + t) ∈ box) − (unique k with
suspensionAct k (x, s) ∈ box)` on the quotient. That return-count is the descent of the
Ambrose–Kakutani first-return structure through the orbit quotient, and its well-definedness and
measurability are exactly the cross-section infrastructure (`suspension_exists_unique_act_mem`
descended to `SuspensionSpace`) that is not yet available. This module therefore lands the
cross-section building block — the return cocycle and its multiplicativity, which is `FlowCocycle`'s
content sampled at the return times — and defers the full space-level `FlowCocycle` lift.
-/

open MeasureTheory

namespace Oseledets

variable {X : Type*} {d : ℕ}

section ReturnCocycle

/-- The **suspension return cocycle**: the linear action accumulated over `n` base returns of the
suspension flow, starting from the cross-section point `x`. Because the suspension flow cocycle is
the identity between returns and the base matrix `A` at each return, after `n` returns it is exactly
the discrete iterated cocycle `cocycle A T n x`. This is the cross-section sampling of the
(continuous-time) suspension flow cocycle at the return times. -/
noncomputable def suspensionCocycleReturn (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) : Matrix (Fin d) (Fin d) ℝ :=
  cocycle A T n x

@[simp] theorem suspensionCocycleReturn_zero (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) : suspensionCocycleReturn A T 0 x = 1 := rfl

@[simp] theorem suspensionCocycleReturn_one (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) : suspensionCocycleReturn A T 1 x = A x := cocycle_one A T x

/-- **Return-cocycle multiplicativity.** Over `m + n` base returns the accumulated linear action
factors as the action over the last `m` returns (started from the shifted cross-section point
`T^[n] x`) times the action over the first `n` returns. This is the suspension flow cocycle
identity sampled at return times; it is read off directly from the base cocycle identity
`cocycle_add`. -/
theorem suspensionCocycleReturn_add (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (m n : ℕ) (x : X) :
    suspensionCocycleReturn A T (m + n) x
      = suspensionCocycleReturn A T m (T^[n] x) * suspensionCocycleReturn A T n x :=
  cocycle_add A T m n x

/-- Each return level of the suspension return cocycle is measurable, given a measurable generator
`A` and measurable base dynamics `T`. -/
theorem measurable_suspensionCocycleReturn [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T)
    (n : ℕ) : Measurable (fun x => suspensionCocycleReturn A T n x) :=
  measurable_cocycle hA hT n

end ReturnCocycle

section ReturnTime

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The **return time** of the suspension flow after `n` base returns from the cross-section point
`x`: the roof Birkhoff sum `roofSum T hτ n x = τ x + τ (T x) + ⋯ + τ (T^[n-1] x)`. This is the flow
duration elapsed between the start `[x, 0]` and its `n`-th return to the cross-section; it is the
time-coordinate companion of `suspensionCocycleReturn`. -/
noncomputable def returnTime (n : ℕ) (x : X) : ℝ := roofSum T hτ (n : ℤ) x

@[simp] theorem returnTime_zero (x : X) : returnTime T hτ 0 x = 0 := by
  simp [returnTime, roofSum_zero]

/-- The return time as a Birkhoff sum of the roof along the base map. -/
theorem returnTime_eq_birkhoffSum (n : ℕ) (x : X) :
    returnTime T hτ n x = birkhoffSum (⇑T) τ n x :=
  roofSum_natCast_eq_birkhoffSum T hτ n x

/-- **Return-time additivity.** The flow time over `m + n` returns is the time over the last `m`
returns (from the shifted cross-section point `T^[n] x`) plus the time over the first `n` returns.
This is the time-coordinate companion of `suspensionCocycleReturn_add`, obtained from the Birkhoff
cocycle property of the roof sum. -/
theorem returnTime_add (m n : ℕ) (x : X) :
    returnTime T hτ (m + n) x
      = returnTime T hτ m ((⇑T)^[n] x) + returnTime T hτ n x := by
  simp only [returnTime_eq_birkhoffSum]
  rw [add_comm m n, birkhoffSum_add]
  ring

end ReturnTime

section ReturnIdentity

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- **The cross-section return identity.** Sampling the suspension flow cocycle along the
cross-section orbit of `x` yields, at flow time `returnTime T hτ n x` (the `n`-th return), the base
iterated cocycle `cocycle A T n x`. This states explicitly that the return cocycle scheduled at the
return times *is* the base cocycle — the cross-section reduction of the continuous-time suspension
flow cocycle to the discrete Oseledets cocycle. -/
theorem suspensionCocycleReturn_returnTime (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) :
    suspensionCocycleReturn A (⇑T) n x = cocycle A (⇑T) n x :=
  rfl

end ReturnIdentity

end Oseledets
