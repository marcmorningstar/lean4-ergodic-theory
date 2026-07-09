/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Livšic flow tier: the flow coboundary and its periodic-orbit obstruction

This module opens the **flow** version of the Livšic (Livshits) cohomological rigidity theory
(issue #36) with a regularity-free definition mirroring the discrete `ErgodicTheory.IsCoboundary`.

For a one-parameter flow `Φ : ℝ → Q → Q` and an observable `F : Q → ℝ`, we say `F` is a
**flow coboundary** if it is the time-derivative (along the flow) of a *transfer function*
`u : Q → ℝ`, read integrally:

`u (Φ t q) − u q = ∫₀ᵗ F (Φ s q) ds`   for all `q` and `t`.

No integrability or regularity is assumed — the interval integral is taken as an opaque real, so the
definition is a bare cohomological one. This is the flow analogue of `IsCoboundary Φ F` and gives
the downstream *no continuous section* obstruction in the flow setting.

The **trivial direction** of the flow Livšic theorem is recorded here in full generality: a single
periodic orbit whose integral of `F` around the period does not vanish defeats *every* transfer
function. This is the fundamental-theorem-of-calculus telescoping around a closed orbit and needs
only a bare flow `Φ : ℝ → Q → Q`.

## Main definitions

* `ErgodicTheory.IsFlowCoboundary` — `F` has a transfer function `u` along `Φ`.

## Main results

* `ErgodicTheory.isFlowCoboundary_zero` — the zero observable is a flow coboundary of every flow
  (the trivial inhabitant, with `u = 0`).
* `ErgodicTheory.not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero` — the periodic-orbit
  obstruction: a nonzero orbit integral over a closed orbit forbids `F` from being a flow
  coboundary.

Reference: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §19.2
(the flow version of the Livšic obstruction).
-/

open MeasureTheory

namespace ErgodicTheory

/-- `F` is a **flow coboundary** for the flow `Φ : ℝ → Q → Q` if it is the flow-time derivative
(read integrally) of some transfer function `u : Q → ℝ`:
`u (Φ t q) − u q = ∫₀ᵗ F (Φ s q) ds` for all `q` and `t`. This mirrors `IsCoboundary`; the integral
is read as an opaque real (no integrability assumed).

By Mathlib's convention the interval integral of a non-integrable integrand is `0`, so for an `F`
that is non-integrable along all of its orbits the predicate holds trivially with `u = 0`, and the
periodic-orbit obstruction below is silent in that regime — it fires exactly when the closed-orbit
integral is a genuine nonzero real. -/
def IsFlowCoboundary {Q : Type*} (Φ : ℝ → Q → Q) (F : Q → ℝ) : Prop :=
  ∃ u : Q → ℝ, ∀ (q : Q) (t : ℝ), u (Φ t q) - u q = ∫ s in (0 : ℝ)..t, F (Φ s q)

/-- The **zero observable is a flow coboundary** of every flow, with the constant-`0` transfer
function: `u (Φ t q) − u q = 0 = ∫₀ᵗ 0 ds` (`intervalIntegral.integral_zero`). This is the trivial
inhabitant of `IsFlowCoboundary` — the flow analogue of `IsCoboundary`'s zero coboundary. -/
theorem isFlowCoboundary_zero {Q : Type*} (Φ : ℝ → Q → Q) :
    IsFlowCoboundary Φ (fun _ => (0 : ℝ)) :=
  ⟨fun _ => 0, fun _ _ => by simp [intervalIntegral.integral_zero]⟩

/-- **Periodic-orbit obstruction (flow Livšic, trivial direction).** If `q` is a periodic point of
period `P` (`Φ P q = q`) and the integral of `F` around that closed orbit does not vanish, then `F`
is not a flow coboundary of any transfer function. This is the fundamental-theorem-of-calculus
telescoping around a periodic orbit: a transfer function would force the orbit integral to equal
`u (Φ P q) − u q = u q − u q = 0`. It needs nothing but a bare flow `Φ : ℝ → Q → Q`. -/
theorem not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero {Q : Type*}
    {Φ : ℝ → Q → Q} {F : Q → ℝ} {q : Q} {P : ℝ}
    (hper : Φ P q = q) (hI : (∫ s in (0 : ℝ)..P, F (Φ s q)) ≠ 0) :
    ¬ IsFlowCoboundary Φ F := by
  rintro ⟨u, hu⟩
  exact hI (by rw [← hu q P, hper, sub_self])

end ErgodicTheory
