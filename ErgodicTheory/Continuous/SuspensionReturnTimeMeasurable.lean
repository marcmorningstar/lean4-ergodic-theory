/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlowMP
import ErgodicTheory.Continuous.SuspensionCocycle
import ErgodicTheory.Cocycle.FurstenbergKesten

/-!
# Measurability of the return time and the return-time exponent ratio

This module records two measurability facts about the suspension cross-section schedule that are
needed to make the special-flow Lyapunov exponent set *measurable* in the base point. Both are
read off mechanically from existing measurability infrastructure.

The first is that, for each lap index `n`, the return time `returnTime T hτ n x` (the flow time
elapsed over `n` base returns) is a measurable function of the base point `x`. By definition
`returnTime T hτ n x = roofSum T hτ (n : ℤ) x = -(suspensionAct T hτ (n : ℤ) (x, 0)).2`, so this
follows from the measurability of the integer iterates of the suspension action
(`measurable_suspensionAct`, of `ErgodicTheory.Continuous.SuspensionFlowMP`).

The second is that the return-time exponent ratio
`x ↦ Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x` is measurable, combining the
measurability of the discrete log-norm cocycle (`measurable_logNorm_cocycle`, of
`ErgodicTheory.Cocycle.FurstenbergKesten`) with the measurability of the return time. This is the
per-index input to `MeasureTheory.measurableSet_tendsto`, which downstream turns the discrete
return-time exponent convergence set into a measurable set.

## Main results

* `ErgodicTheory.measurable_returnTime`: the return time `x ↦ returnTime T hτ n x` is measurable.
* `ErgodicTheory.measurable_logNorm_div_returnTime`: the return-time exponent ratio
  `x ↦ Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x` is measurable.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

/-- **Measurability of the return time.** For each lap index `n`, the flow time `returnTime T hτ n
x` elapsed over `n` base returns is a measurable function of the base point `x`. It is the negated
`ℝ`-coordinate of the `n`-th integer iterate of the suspension action started at height `0`
(`returnTime T hτ n x = -(suspensionAct T hτ (n : ℤ) (x, 0)).2`), so it is measurable by
`measurable_suspensionAct`. -/
theorem measurable_returnTime (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) (n : ℕ) :
    Measurable (fun x => returnTime T hτ n x) := by
  have hact : Measurable (fun x : X => suspensionAct T hτ (n : ℤ) (x, (0 : ℝ))) :=
    (measurable_suspensionAct T hτ (n : ℤ)).comp (measurable_id.prodMk measurable_const)
  have : (fun x => returnTime T hτ n x)
      = fun x => -(suspensionAct T hτ (n : ℤ) (x, (0 : ℝ))).2 := by
    funext x; rfl
  rw [this]
  exact (hact.snd).neg

/-- **Measurability of the return-time exponent ratio.** For each lap index `n`, the rescaled
log-norm `x ↦ Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x` is a measurable function of the
base point `x`. It is the quotient of the measurable discrete log-norm cocycle
(`measurable_logNorm_cocycle`) and the measurable return time (`measurable_returnTime`). This is the
per-index input to `MeasureTheory.measurableSet_tendsto`. -/
theorem measurable_logNorm_div_returnTime {d : ℕ} {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : Measurable A) (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) (n : ℕ) :
    Measurable (fun x => Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x) :=
  (measurable_logNorm_cocycle (T := (⇑T)) hA T.measurable n).div
    (measurable_returnTime T hτ n)

end ErgodicTheory
