/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionExponentSetEquiv
import ErgodicTheory.Continuous.SuspensionReturnTimeMeasurable

/-!
# Measurability of the full-time special-flow exponent set

This module discharges the last explicit measurability hypothesis of the unconditional space-level
special-flow exponent (`hPmeas`): for a fixed value `L`, under a bounded roof `c ≤ τ ≤ C`, the set
of base points carrying the full-time cover-cocycle growth rate `L`,

`{x | Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t → L  as t → ∞}`,

is measurable. The cover cocycle has no in-library measurability-in-`x` lemma, so this cannot be
attacked directly. Instead the set is first rewritten — *pointwise in `x`* — as the discrete
return-time exponent set (`coverCocycle_exponent_set_eq`, the between-returns squeeze of
`ErgodicTheory.Continuous.SuspensionExponentSetEquiv`), whose convergence is of an `ℕ`-indexed sequence
of measurable functions and hence measurable by `MeasureTheory.measurableSet_tendsto`, with the
per-index measurability supplied by `measurable_logNorm_div_returnTime`
(`ErgodicTheory.Continuous.SuspensionReturnTimeMeasurable`).

## Main results

* `ErgodicTheory.measurableSet_coverCocycle_exponent`: the full-time cover-cocycle exponent set
  `{x | log ‖coverCocycle (x, 0) t‖ / t → L}` is measurable (under `Measurable A`, measurable roof
  `τ`, and a bounded roof `c ≤ τ ≤ C`).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section ExponentSetMeasurable

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- **Measurability of the full-time cover-cocycle exponent set.** For a fixed value `L`, the set of
base points `x` whose full-time cover-cocycle log-norm rescaled by `t` tends to `L` as the real
`t → ∞` is measurable. The cover cocycle carries no direct measurability-in-`x` lemma; instead the
set is rewritten as the discrete return-time exponent set (`coverCocycle_exponent_set_eq`, the
between-returns squeeze) and that set is measurable by `MeasureTheory.measurableSet_tendsto` applied
to the `ℕ`-indexed sequence of measurable functions
`x ↦ Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x` (`measurable_logNorm_div_returnTime`). -/
theorem measurableSet_coverCocycle_exponent {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : Measurable A) (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}
    (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C) (L : ℝ) :
    MeasurableSet {x : X |
      Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
        atTop (𝓝 L)} := by
  rw [coverCocycle_exponent_set_eq A T hτ hc hcpos hC L]
  exact measurableSet_tendsto (𝓝 L)
    (fun n => measurable_logNorm_div_returnTime hA T hτ n)

end ExponentSetMeasurable

end ErgodicTheory
