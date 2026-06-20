/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionCoverCocycle

/-!
# The cover flow cocycle on `X × ℝ`

This module lifts the cross-section flow cocycle `flowCocycleSection` of
`Oseledets.Continuous.SuspensionFlowCocycle` to the **cover** `X × ℝ` of the suspension (mapping
torus), one step before the quotient descent to the genuine space-level `FlowCocycle` over
`SuspensionSpace`. A cover point `p = (x, h)` is a base point `x` carrying a height coordinate `h`
along the flow direction; advancing the special (suspension) flow for time `t` from `p` is the same
as advancing the cross-section flow from `x` for the *total* elapsed time `h + t`. This is the
standard special-flow / flow-under-a-roof bookkeeping (Cornfeld–Fomin–Sinai, *Ergodic Theory*,
Springer 1982, Ch. 11, special/suspension flows; Ambrose–Kakutani), the first-return / ceiling
construction also underlying Abramov's entropy formula `h(flow) = h(base)/∫τ`, whose
Lyapunov-exponent analogue `λ_flow = λ_base / ∫τ` is the headline target.

## Main definitions

* `Oseledets.coverCocycle`: `coverCocycle A T hτ hc hcpos p t` is the matrix accumulated by the
  suspension flow over flow time `t` from the cover point `p = (x, h)`, namely the cross-section
  flow cocycle `flowCocycleSection` read at the total elapsed time `h + t` from the base point `x`.

## Main results

* `Oseledets.coverCocycle_base`: on the base section (`h = 0`) the cover cocycle agrees with the
  cross-section flow cocycle, `coverCocycle (x, 0) t = flowCocycleSection t x`.
* `Oseledets.coverCocycle_section_returnTime`: the **flow-cocycle multiplicativity along the
  section** at a return boundary,
  `coverCocycle (x, 0) (returnTime n x + r) = coverCocycle (Tⁿ x, 0) r * cocycle A T n x`,
  for `0 ≤ r`. The residual flow over time `r` started from the shifted base point `Tⁿ x` composes
  on the left of the `n` completed base laps. Proved from the additive split of the lap counter at a
  return boundary (`lapCount_returnTime_add`) pushed through return-cocycle multiplicativity
  (`suspensionCocycleReturn_add`) and the return identity (`suspensionCocycleReturn_returnTime`).

## What is *not* in this file — the remaining gap toward the `SuspensionSpace` `FlowCocycle`

The cover cocycle here lives on `X × ℝ` *before* the orbit-quotient identification
`(x, τ x) ∼ (T x, 0)` that defines `SuspensionSpace`. The genuine space-level `FlowCocycle` is the
descent of `coverCocycle` to that quotient: it requires checking that `coverCocycle` is constant on
the equivalence classes of the suspension relation (i.e. that the height-coordinate reduction
`(x, h)` with `h ≥ τ x` re-based to `(T x, h − τ x)` leaves the accumulated matrix unchanged, which
is exactly `coverCocycle_section_returnTime` specialized to one lap together with the `flowAct`
height reduction) and an additive flow-cocycle law `coverCocycle p (s + t) = coverCocycle (flow s p)
t * coverCocycle p s` in the height coordinate. Those two facts — the well-definedness on classes
and the full additive law over arbitrary (non-return) times — are the remaining gap, and are
deferred to the `SuspensionSpace` descent (cf. the quotient gap documented in
`Oseledets.Continuous.SuspensionCocycle`). The present file lands the cover *definition*, its
agreement with the section, and the section-level multiplicativity at return boundaries, all
sorry-free.
-/

namespace Oseledets

section CoverFlow

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **The cover flow cocycle on `X × ℝ`.** For a cover point `p = (x, h)` (base point `x` at
height `h` along the flow direction) the matrix accumulated by the suspension flow over flow time
`t` is the cross-section flow cocycle `flowCocycleSection` read at the *total* elapsed time `h + t`
from the base point `x`. This is the cover-level form of the special-flow cocycle of
Cornfeld–Fomin–Sinai, Ch. 11, before the orbit-quotient descent to the `SuspensionSpace`
`FlowCocycle`. -/
noncomputable def coverCocycle (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (p : X × ℝ) (t : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  flowCocycleSection A T hτ hc hcpos (p.2 + t) p.1

/-- **Agreement with the section on the base section.** At height `0` the cover cocycle is exactly
the cross-section flow cocycle: `coverCocycle (x, 0) t = flowCocycleSection t x`, since the total
elapsed time `0 + t` collapses to `t`. -/
theorem coverCocycle_base (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) (x : X) :
    coverCocycle A T hτ hc hcpos (x, 0) t = flowCocycleSection A T hτ hc hcpos t x := by
  simp only [coverCocycle, zero_add]

/-- **Flow-cocycle multiplicativity along the section at a return boundary.** Starting on the base
section at `x`, the cover cocycle over flow time `returnTime n x + r` (for `0 ≤ r`) factors as the
residual flow over time `r` started from the shifted base point `Tⁿ x`, composed on the left of the
discrete base cocycle `cocycle A T n x` for the `n` completed laps:
`coverCocycle (x, 0) (returnTime n x + r) = coverCocycle (Tⁿ x, 0) r * cocycle A T n x`.
The accumulated matrix splits at the return boundary because the lap counter does
(`lapCount_returnTime_add`), and the return cocycle is multiplicative across that split
(`suspensionCocycleReturn_add`), with the first `n` laps giving `cocycle A T n x` via the return
identity (`suspensionCocycleReturn_returnTime`). This is the section-level shadow of the
`SuspensionSpace` `FlowCocycle` identity. -/
theorem coverCocycle_section_returnTime (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (x : X) :
    coverCocycle A T hτ hc hcpos (x, 0) (returnTime T hτ n x + r)
      = coverCocycle A T hτ hc hcpos ((⇑T)^[n] x, 0) r * cocycle A (⇑T) n x := by
  -- Reduce both cover cocycles to the cross-section flow cocycle (heights are `0`).
  rw [coverCocycle_base, coverCocycle_base]
  -- Unfold the section cocycle and split the lap counter at the return boundary.
  simp only [flowCocycleSection,
    lapCount_returnTime_add T hτ hc hcpos n hr x]
  -- The return cocycle is multiplicative across `n + (lapCount r (Tⁿ x))` laps; reorder so that the
  -- first `n` laps sit on the right and the residual laps on the left.
  rw [Nat.add_comm n (lapCount T hτ hc hcpos r ((⇑T)^[n] x)),
    suspensionCocycleReturn_add A (⇑T) (lapCount T hτ hc hcpos r ((⇑T)^[n] x)) n x,
    suspensionCocycleReturn_returnTime T A n x]

end CoverFlow

end Oseledets
