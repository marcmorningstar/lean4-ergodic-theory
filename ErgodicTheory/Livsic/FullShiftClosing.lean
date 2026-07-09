/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.ShiftMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The exponential closing property for the one-sided full shift

This file establishes the concrete instance of the abstracted `ExpClosing` property
(`ErgodicTheory.Livsic.Defs`) for the **one-sided full shift** `shiftMap` on `Shift α₀`, the
simplest mixing subshift of finite type. It is the geometric input that feeds the substantive
Livšic direction (issue #29): every almost-periodic point is `α`-Hölder shadowed by a genuine
periodic point, with a summed shadowing cost geometrically controlled by the return gap.

## The closing construction (Parry–Pollicott, *Zeta functions and the periodic orbit structure
of hyperbolic dynamics*, Astérisque 187–188, Ch. 3)

Because the full shift has **no admissibility bookkeeping** — every finite word is legal — the
periodic shadow of a point `x` that almost `n`-returns is produced by pure *periodization*:
`p i := x (i % n)` is the `n`-periodic sequence that repeats the first `n` symbols of `x`. If `x`
and `σ^n x` first differ at index `N` (so `dist x (σ^n x) = (1/2)^N`), then `x` is genuinely
`n`-periodic on its first `n + N` coordinates, hence `p` agrees with `x` there; the per-step
shadowing distances therefore decay like `(1/2)^(n+N-i)` and their `α`-th powers sum to a finite
geometric series bounded by `(1/2)^(Nα) · (1/2)^α / (1 - (1/2)^α)`.

## Main results

* `expClosing_shiftMap` — the full shift satisfies `ExpClosing shiftMap α 1 K` with the explicit
  constant `K = (1/2)^α / (1 - (1/2)^α)`, for every Hölder exponent `α > 0`. The exponent `α`
  is a *free variable*, so this instance transports against a Hölder observable of **any**
  exponent `r > 0` with no further work.
-/

open Function Filter Topology
open scoped NNReal

namespace ErgodicTheory.Livsic

open ErgodicTheory.Multifractal

variable {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]

attribute [local instance] PiNat.metricSpace

/-- **Exponential closing for the full shift** (Parry–Pollicott, Ch. 3). For every Hölder exponent
`α > 0`, the one-sided full shift `shiftMap` on `Shift α₀` satisfies the summed-cost closing
property `ExpClosing shiftMap α 1 K` with the explicit constant
`K = (1/2)^α / (1 - (1/2)^α) ≥ 0`.

The closing radius `δ = 1` is vacuous (all distances `≤ 1`, `PiNat.dist_le_one`); the shadow of a
point `x` that almost `n`-returns is the periodization `p i := x (i % n)`, which needs no
admissibility bookkeeping because the full shift is the simplest mixing SFT. -/
theorem expClosing_shiftMap {α : ℝ} (hα : 0 < α) :
    ExpClosing (shiftMap (α₀ := α₀)) α 1 ((1 / 2) ^ α / (1 - (1 / 2) ^ α)) := by
  intro n x _hx
  rcases eq_or_ne x (shiftMap^[n] x) with hxeq | hne_x
  · -- `x` is already `n`-periodic: it shadows itself with zero cost.
    refine ⟨x, hxeq.symm, ?_⟩
    have hz : ∀ i ∈ Finset.range n,
        dist (shiftMap^[i] x) (shiftMap^[i] x) ^ α = 0 :=
      fun i _ => by rw [dist_self, Real.zero_rpow (ne_of_gt hα)]
    refine le_of_eq ?_
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, ← hxeq, dist_self,
      Real.zero_rpow (ne_of_gt hα), mul_zero]
  · -- Main case `x ≠ σ^n x` (`n ≥ 1`): the periodic shadow is the periodization `p i := x (i%n)`.
    have hn : 0 < n :=
      Nat.pos_of_ne_zero (by rintro rfl; exact hne_x (Function.iterate_zero_apply _ _).symm)
    -- The periodic shadow: repeat the first `n` symbols of `x`.
    set p : Shift α₀ := fun i => x (i % n) with hp
    -- `p` is genuinely `n`-periodic.
    have hper_p : shiftMap^[n] p = p := by
      funext i
      rw [shiftMap_iterate_apply]
      simp only [hp, Nat.add_mod_right]
    -- The shadow bound is exactly the ambient periodization estimate `sum_shadow_le`.
    refine ⟨p, hper_p, ?_⟩
    rw [hp]
    exact sum_shadow_le hα n hn x hne_x

end ErgodicTheory.Livsic
