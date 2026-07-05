/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionBddRoofExponent

/-!
# The full-time exponent set equals the discrete return-time exponent set

This module proves the **set equality** that lets the full-time special-flow Lyapunov-exponent set
be recognised as measurable. For a fixed value `L : ℝ`, the set of base points carrying the
full-time cover-cocycle growth rate `L`,

`{x | Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t → L  as t → ∞}`,

coincides — *pointwise in `x`*, under a bounded roof `c ≤ τ ≤ C` — with the set of base points
carrying the discrete return-time growth rate `L`,

`{x | Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x → L  as n → ∞}`.

The two inclusions are the two halves of the between-returns squeeze, run *per point* rather than
`μ`-a.e.:

* **Full ⟹ discrete** (`tendsto_returnTimeExp_of_coverCocycle`). Sample the full-time limit along
  the return-time subsequence `t = returnTime T hτ n x`, which tends to `+∞`
  (`returnTime_tendsto_atTop`); the cover-cocycle norm at a return time equals the base cocycle norm
  (`coverCocycle_returnTime_norm_eq`), so the sampled full-time ratio is exactly the discrete
  return-time ratio. This direction needs only the positive *lower* roof bound.

* **Discrete ⟹ full** (`tendsto_coverCocycle_of_returnTimeExp`). This is the per-point core of
  `coverCocycle_tendsto_exponent_of_bddRoof`: factor the full-time ratio as the time-distortion
  factor `returnTime (lapCount t x) x / t` (which `→ 1` by `lapCount_returnTime_div_tendsto_one`,
  the bounded-roof input) times the discrete exponent ratio evaluated at the lap count (which `→ L`
  by composing the discrete hypothesis with `lapCount_tendsto_atTop`). The product factorization is
  `log_coverCocycle_div_eq_lapCount`. This direction genuinely needs the uniform *upper* roof bound
  `τ ≤ C`.

The normal form of the discrete set is fixed exactly as
`Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x` so that the downstream measurability rewrite
(`ErgodicTheory.Continuous.SuspensionExponentSetMeasurable`) lands on a
`MeasureTheory.measurableSet_tendsto` shape with the per-index measurability supplied by
`measurable_logNorm_div_returnTime`.

This is the special-flow / flow-under-a-roof construction of Cornfeld–Fomin–Sinai, *Ergodic Theory*
(Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani); the Lyapunov-exponent
analogue of Abramov's entropy formula `h(flow) = h(base)/∫τ`.

## Main results

* `ErgodicTheory.tendsto_returnTimeExp_of_coverCocycle`: full-time exponent ⟹ discrete return-time
  exponent (sampling along the returns).
* `ErgodicTheory.tendsto_coverCocycle_of_returnTimeExp`: discrete return-time exponent ⟹ full-time
  exponent (the bounded-roof between-returns squeeze, per point).
* `ErgodicTheory.coverCocycle_exponent_set_eq`: the two exponent sets coincide, for every value `L`.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section ExponentSetEquiv

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c C : ℝ}

/-- **Full-time exponent ⟹ discrete return-time exponent.** If the cover-cocycle log-norm rescaled
by the elapsed flow time `t` tends to `L` as the real `t → ∞`, then the discrete return-time ratio
`Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x` tends to `L` as `n → ∞`. The discrete ratio is
the full-time ratio sampled along the return-time subsequence `t = returnTime T hτ n x` (which tends
to `+∞`, `returnTime_tendsto_atTop`), and the cover-cocycle norm at a return time equals the base
cocycle norm (`coverCocycle_returnTime_norm_eq`). Needs only the lower roof bound `0 < c ≤ τ`. -/
theorem tendsto_returnTimeExp_of_coverCocycle (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (x : X) {L : ℝ}
    (hfull : Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t)
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x) atTop (𝓝 L) := by
  -- Sample the full-time limit along the return-time subsequence `t = returnTime n x → ∞`.
  have hrt : Tendsto (fun n : ℕ => returnTime T hτ n x) atTop atTop :=
    returnTime_tendsto_atTop T hτ hc hcpos x
  have hcomp := hfull.comp hrt
  -- Rewrite the sampled ratio: the cover-cocycle norm at the return time is the base cocycle norm.
  refine hcomp.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [coverCocycle_returnTime_norm_eq A T hτ hc hcpos n x]

/-- **Discrete return-time exponent ⟹ full-time exponent.** If the discrete return-time ratio
`Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x` tends to `L` as `n → ∞`, then under a bounded
roof `c ≤ τ ≤ C` the full-time cover-cocycle log-norm rescaled by `t` tends to `L` as the real
`t → ∞`. This is the per-point core of `coverCocycle_tendsto_exponent_of_bddRoof`: the full-time
ratio factors (`log_coverCocycle_div_eq_lapCount`) as the time-distortion factor
`returnTime (lapCount t x) x / t` (`→ 1` by `lapCount_returnTime_div_tendsto_one`) times the
discrete exponent ratio sampled at the lap count (`→ L` by composing the hypothesis with
`lapCount_tendsto_atTop`). The product of the two limits is `L · 1 = L`. Needs the upper roof bound
`τ ≤ C`. -/
theorem tendsto_coverCocycle_of_returnTimeExp (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (hC : ∀ x, τ x ≤ C) (x : X) {L : ℝ}
    (hdisc : Tendsto (fun n : ℕ => Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x)
      atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t) atTop (𝓝 L) := by
  set N : ℝ → ℕ := fun t => lapCount T hτ hc hcpos t x with hN
  -- The lap count diverges as the flow time grows.
  have hNtop : Tendsto N atTop atTop := lapCount_tendsto_atTop T hτ hc hcpos x
  -- Factor 2: the discrete exponent ratio sampled at the lap count, `→ L`.
  have hfac2 : Tendsto
      (fun t : ℝ => Real.log ‖cocycle A (⇑T) (N t) x‖ / returnTime T hτ (N t) x)
      atTop (𝓝 L) := hdisc.comp hNtop
  -- Factor 1: the time-distortion factor `→ 1`.
  have hfac1 : Tendsto (fun t : ℝ => returnTime T hτ (N t) x / t) atTop (𝓝 1) :=
    lapCount_returnTime_div_tendsto_one T hτ hc hcpos hC x
  -- The product of the two factors tends to `1 · L = L`.
  have hprod : Tendsto
      (fun t : ℝ => (returnTime T hτ (N t) x / t)
        * (Real.log ‖cocycle A (⇑T) (N t) x‖ / returnTime T hτ (N t) x))
      atTop (𝓝 L) := by
    have := hfac1.mul hfac2
    simpa only [one_mul] using this
  -- Rewrite the cover-cocycle ratio as that product, eventually for `t > 0` with a positive lap
  -- return time (so that `log_coverCocycle_div_eq_lapCount` applies).
  refine hprod.congr' ?_
  filter_upwards [(hNtop.eventually_gt_atTop 0), eventually_gt_atTop (0 : ℝ)]
    with t hNt htpos
  have ht : 0 ≤ t := le_of_lt htpos
  have hrt : returnTime T hτ (N t) x ≠ 0 := by
    have hpos : 0 < returnTime T hτ (N t) x := by
      have hmono : StrictMono (fun k : ℕ => returnTime T hτ k x) :=
        returnTime_strictMono T hτ hc hcpos x
      have := hmono (Nat.pos_of_ne_zero (Nat.pos_iff_ne_zero.mp hNt))
      simpa only [returnTime_zero] using this
    exact ne_of_gt hpos
  exact (log_coverCocycle_div_eq_lapCount A T hτ hc hcpos ht x hrt).symm

/-- **The full-time exponent set equals the discrete return-time exponent set.** For a fixed value
`L`, under a bounded roof `c ≤ τ ≤ C`, the set of base points whose full-time cover-cocycle growth
rate is `L` coincides with the set of base points whose discrete return-time growth rate is `L`:

`{x | log ‖coverCocycle (x, 0) t‖ / t → L} = {x | log ‖cocycle A (⇑T) n x‖ / returnTime n x → L}`.

This is the two-sided between-returns squeeze, run per point. The forward inclusion samples along
the returns (`tendsto_returnTimeExp_of_coverCocycle`), the reverse runs the bounded-roof squeeze
(`tendsto_coverCocycle_of_returnTimeExp`). -/
theorem coverCocycle_exponent_set_eq (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (hC : ∀ x, τ x ≤ C)
    (L : ℝ) :
    {x | Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) t‖ / t) atTop (𝓝 L)}
      = {x | Tendsto (fun n : ℕ => Real.log ‖cocycle A (⇑T) n x‖ / returnTime T hτ n x)
          atTop (𝓝 L)} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · exact tendsto_returnTimeExp_of_coverCocycle A T hτ hc hcpos x
  · exact tendsto_coverCocycle_of_returnTimeExp A T hτ hc hcpos hC x

end ExponentSetEquiv

end ErgodicTheory
