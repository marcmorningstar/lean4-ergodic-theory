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
  · -- Main case: `x ≠ σ^n x`, so `n ≥ 1` and the first-difference index `N` is well defined.
    set N := PiNat.firstDiff x (shiftMap^[n] x) with hN
    have hn : 0 < n :=
      Nat.pos_of_ne_zero (by rintro rfl; exact hne_x (Function.iterate_zero_apply _ _).symm)
    have hdist : dist x (shiftMap^[n] x) = (1 / 2 : ℝ) ^ N := PiNat.dist_eq_of_ne hne_x
    set θ := (1 / 2 : ℝ) ^ α with hθdef
    have hθ0 : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos (by norm_num) α
    have hθ1 : θ < 1 := by rw [hθdef]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hα
    -- `((1/2)^m)^α = θ^m`: the npow/rpow interchange, used both ways (shared `half_pow_rpow`).
    have hpow : ∀ m : ℕ, ((1 / 2 : ℝ) ^ m) ^ α = θ ^ m := fun m => by
      rw [hθdef]; exact half_pow_rpow α m
    have hgeom : ∑ i ∈ Finset.range n, θ ^ i ≤ (1 - θ)⁻¹ :=
      geomSum_range_le_inv_one_sub hθ0.le hθ1 n
    -- The periodic shadow: repeat the first `n` symbols of `x`.
    set p : Shift α₀ := fun i => x (i % n) with hp
    -- `x` is `n`-periodic below index `N` because `x` and `σ^n x` agree there.
    have hper : ∀ j, j < N → x j = x (j + n) := by
      intro j hj
      have hjfd : j < PiNat.firstDiff x (shiftMap^[n] x) := by rw [← hN]; exact hj
      have h1 : x j = (shiftMap^[n] x) j := PiNat.apply_eq_of_lt_firstDiff hjfd
      rwa [shiftMap_iterate_apply] at h1
    -- `p` is genuinely `n`-periodic.
    have hper_p : shiftMap^[n] p = p := by
      funext i
      rw [shiftMap_iterate_apply]
      simp only [hp, Nat.add_mod_right]
    -- `p` agrees with `x` on the first `n + N` coordinates.
    have hagree : ∀ i, i < n + N → p i = x i := by
      intro i
      induction i using Nat.strongRecOn with
      | ind i ih =>
        intro hi
        rcases lt_or_ge i n with hlt | hge
        · simp only [hp, Nat.mod_eq_of_lt hlt]
        · simp only [hp]
          rw [Nat.mod_eq_sub_mod hge]
          have hind : p (i - n) = x (i - n) := ih (i - n) (by omega) (by omega)
          simp only [hp] at hind
          rw [hind, hper (i - n) (by omega)]
          congr 1
          omega
    -- Per-step shadowing bound `dist (σ^i x) (σ^i p) ≤ (1/2)^(n+N-i)`.
    have hle_i : ∀ i ∈ Finset.range n,
        dist (shiftMap^[i] x) (shiftMap^[i] p) ≤ (1 / 2 : ℝ) ^ (n + N - i) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [← agree_iff_dist_le]
      intro j hj
      simp only [shiftMap_iterate_apply]
      exact (hagree (j + i) (by omega)).symm
    -- The `α`-th power of each shadowing distance is `≤ θ^(n+N-i)`.
    have hterm : ∀ i ∈ Finset.range n,
        dist (shiftMap^[i] x) (shiftMap^[i] p) ^ α ≤ θ ^ (n + N - i) := by
      intro i hi
      calc dist (shiftMap^[i] x) (shiftMap^[i] p) ^ α
          ≤ ((1 / 2 : ℝ) ^ (n + N - i)) ^ α :=
            Real.rpow_le_rpow dist_nonneg (hle_i i hi) hα.le
        _ = θ ^ (n + N - i) := hpow (n + N - i)
    have hsum1 : ∑ i ∈ Finset.range n, dist (shiftMap^[i] x) (shiftMap^[i] p) ^ α
        ≤ ∑ i ∈ Finset.range n, θ ^ (n + N - i) := Finset.sum_le_sum hterm
    -- Reindex `i ↦ n-1-i` to expose the geometric series `θ^(N+1) · ∑ θ^i`.
    have hreflect : ∑ i ∈ Finset.range n, θ ^ (n + N - i)
        = θ ^ (N + 1) * ∑ i ∈ Finset.range n, θ ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun i => θ ^ (n + N - i)) n]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      change θ ^ (n + N - (n - 1 - i)) = θ ^ (N + 1) * θ ^ i
      rw [← pow_add]
      congr 1
      omega
    have hsum2 : ∑ i ∈ Finset.range n, θ ^ (n + N - i) ≤ θ ^ (N + 1) * (1 - θ)⁻¹ := by
      rw [hreflect]
      exact mul_le_mul_of_nonneg_left hgeom (pow_nonneg hθ0.le (N + 1))
    have hfin : θ ^ (N + 1) * (1 - θ)⁻¹
        = θ / (1 - θ) * dist x (shiftMap^[n] x) ^ α := by
      rw [hdist, hpow N, pow_succ]
      ring
    refine ⟨p, hper_p, ?_⟩
    calc ∑ i ∈ Finset.range n, dist (shiftMap^[i] x) (shiftMap^[i] p) ^ α
        ≤ ∑ i ∈ Finset.range n, θ ^ (n + N - i) := hsum1
      _ ≤ θ ^ (N + 1) * (1 - θ)⁻¹ := hsum2
      _ = θ / (1 - θ) * dist x (shiftMap^[n] x) ^ α := hfin

end ErgodicTheory.Livsic
