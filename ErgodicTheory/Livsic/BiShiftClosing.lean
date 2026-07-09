/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.BiShiftMetric
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.ShiftMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exponential closing property for the two-sided full shift

This file establishes the concrete instance of the abstracted `ExpClosing` property
(`ErgodicTheory.Livsic.Defs`) for the **two-sided full shift** `biShiftMap` on `BiShift α₀`, the
bi-infinite analogue of the one-sided closing recorded in `ErgodicTheory.Livsic.FullShiftClosing`.
It is the geometric input feeding the two-sided Livšic instance (GitHub issue #32, tier 1).

## The two-sided closing construction (Katok–Hasselblatt, *Introduction to the Modern Theory of
Dynamical Systems*, §6.4 Anosov closing / §19.2 Livšic)

Because the full shift has **no admissibility bookkeeping** — every bi-infinite word is legal — the
periodic shadow of a point `x` that almost `n`-returns is the **central-block periodization**
`p j := x (j % n)` (with `Int.emod`, so `j % n ∈ [0, n)`): the `n`-periodic sequence repeating the
central block `x 0, …, x (n-1)`. If `x` and `σ^n x` first differ at `|·| = N` (so
`dist x (σ^n x) = (1/2)^N`), then `x` is genuinely `n`-periodic on the whole window `-N < j < n+N`,
hence `p` agrees with `x` there. The two-sided geometry makes the per-step shadowing distance decay
like the **two-sided profile** `θ^min(i, n-i)` (small near both ends of the block, `θ = (1/2)^α`),
whose reflected geometric sum is bounded by `2·(1-θ)⁻¹` — *twice* the one-sided constant.

## Main results

* `min_regime_sum_le` — the two-sided geometric bound
  `∑_{i<n} θ^min(i,n-i) ≤ 2·(1-θ)⁻¹` for `0 ≤ θ < 1`.
* `periodize_agree` — the central periodization agrees with `x` throughout the periodicity window.
* `biShiftMap_iterate_periodize` — the periodization is genuinely `n`-periodic.
* `expClosing_biShiftMap` — the two-sided full shift satisfies `ExpClosing biShiftMap α 1 K` with
  explicit constant `K = 2/(1 - (1/2)^α)`, for every Hölder exponent `α > 0`. As on the one-sided
  side, `α` is a *free variable*, so the instance transports against a Hölder observable of any
  exponent with no further work.
-/

open Function
open scoped NNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

variable {α₀ : Type*}

/-! ### The two-sided geometric bound -/

/-- **Two-sided regime geometric bound.** For `0 ≤ θ < 1`,
`∑_{i<n} θ^min(i, n-i) ≤ 2·(1-θ)⁻¹`. The two-sided profile `θ^min(i,n-i)` is dominated termwise by
`θ^i + θ^(n-i)`; the first arm is a geometric partial sum, and the second reflects (via
`Finset.sum_range_reflect`) to another one — hence *twice* the one-sided bound `(1-θ)⁻¹`. -/
theorem min_regime_sum_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, θ ^ min i (n - i) ≤ 2 * (1 - θ)⁻¹ := by
  have hbound : ∀ i, θ ^ min i (n - i) ≤ θ ^ i + θ ^ (n - i) := by
    intro i
    rcases le_total i (n - i) with h | h
    · rw [min_eq_left h]; linarith [pow_nonneg h0 (n - i)]
    · rw [min_eq_right h]; linarith [pow_nonneg h0 i]
  have h1st : ∑ i ∈ Finset.range n, θ ^ i ≤ (1 - θ)⁻¹ := geomSum_range_le_inv_one_sub h0 h1 n
  have hrefl : ∑ i ∈ Finset.range n, θ ^ (n - i) = ∑ i ∈ Finset.range n, θ ^ (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => θ ^ (n - i)) n]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    change θ ^ (n - (n - 1 - i)) = θ ^ (i + 1)
    congr 1
    omega
  have h2nd : ∑ i ∈ Finset.range n, θ ^ (n - i) ≤ (1 - θ)⁻¹ := by
    rw [hrefl]
    calc ∑ i ∈ Finset.range n, θ ^ (i + 1)
        ≤ ∑ i ∈ Finset.range n, θ ^ i :=
          Finset.sum_le_sum fun i _ => pow_le_pow_of_le_one h0 h1.le (Nat.le_succ i)
      _ ≤ (1 - θ)⁻¹ := h1st
  calc ∑ i ∈ Finset.range n, θ ^ min i (n - i)
      ≤ ∑ i ∈ Finset.range n, (θ ^ i + θ ^ (n - i)) := Finset.sum_le_sum fun i _ => hbound i
    _ = (∑ i ∈ Finset.range n, θ ^ i) + ∑ i ∈ Finset.range n, θ ^ (n - i) := Finset.sum_add_distrib
    _ ≤ (1 - θ)⁻¹ + (1 - θ)⁻¹ := by linarith [h1st, h2nd]
    _ = 2 * (1 - θ)⁻¹ := by ring

/-! ### The shift iterate on integer coordinates -/

/-- The `k`-th iterate of the two-sided shift advances every (integer) index by `k`:
`biShiftMap^[k] x m = x (m + k)`. (A local copy of the identity, to keep this module's imports to
the metric layer.) -/
theorem biShiftMap_iterate_apply (k : ℕ) (x : BiShift α₀) (m : ℤ) :
    (biShiftMap^[k] x) m = x (m + k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', biShiftMap, ih]
    push_cast
    ring_nf

/-! ### The central periodization -/

/-- **Periodicity window agreement.** Suppose `x` is `n`-periodic on the reach `|j| < N`, i.e.
`x j = x (j + n)` whenever `|j| < N`. Then the central periodization `j ↦ x (j % n)` (with
`Int.emod`, values in `[0, n)`) agrees with `x` on the *whole* window `-N < j < n + N`.

The proof is a walk along the `n`-periods, organized by strong induction on the quotient magnitude
`|j / n|`: from an index `j ≥ n` step down by `n` (its predecessor `j - n` still lies in the window,
one period closer to `[0, n)`), from `j < 0` step up by `n`, each single step licensed by `hagree`
because the base index stays within reach. -/
theorem periodize_agree {x : BiShift α₀} {n : ℕ} (hn : 0 < n) {N : ℕ}
    (hagree : ∀ j : ℤ, j.natAbs < N → x j = x (j + n)) (j : ℤ)
    (hlo : -(N : ℤ) < j) (hhi : j < (n : ℤ) + N) : x (j % n) = x j := by
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hn' : (n : ℤ) ≠ 0 := ne_of_gt hn0
  suffices H : ∀ m : ℕ, ∀ k : ℤ, (k / (n : ℤ)).natAbs = m →
      -(N : ℤ) < k → k < (n : ℤ) + N → x (k % n) = x k by
    exact H (j / (n : ℤ)).natAbs j rfl hlo hhi
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k hkm hlo' hhi'
    rcases lt_trichotomy k 0 with hkneg | hkzero | hkpos
    · -- `k < 0`: step up one period to `k + n`.
      have hqneg : k / (n : ℤ) ≤ -1 := by
        by_contra h
        rw [not_le] at h
        have h0 : (0 : ℤ) ≤ k / n := by omega
        have hk0 : (0 : ℤ) ≤ k := by
          have := (Int.le_ediv_iff_mul_le hn0).mp h0
          simpa using this
        omega
      have hshift : (k + n) / (n : ℤ) = k / n + 1 := by
        have hrw : k + (n : ℤ) = k + 1 * n := by ring
        rw [hrw, Int.add_mul_ediv_right k 1 hn']
      have hdec : ((k + n) / (n : ℤ)).natAbs < m := by rw [hshift]; omega
      have hrec : x ((k + n) % n) = x (k + n) :=
        ih _ hdec (k + n) rfl (by omega) (by omega)
      have hemod : (k + n) % (n : ℤ) = k % n := by
        have hrw : k + (n : ℤ) = k + n * 1 := by ring
        rw [hrw, Int.add_mul_emod_self_left]
      have hstep : x k = x (k + n) := hagree k (by omega)
      rw [← hemod, hrec, hstep]
    · -- `k = 0`: base case.
      subst hkzero
      rw [Int.zero_emod]
    · -- `k > 0`.
      by_cases hkge : (n : ℤ) ≤ k
      · -- `k ≥ n`: step down one period to `k - n`.
        have hshift : (k - n) / (n : ℤ) = k / n - 1 := by
          have hrw : k - (n : ℤ) = k + (-1) * n := by ring
          rw [hrw, Int.add_mul_ediv_right k (-1) hn']
          ring
        have hdec : ((k - n) / (n : ℤ)).natAbs < m := by
          rw [hshift]
          have h1 : (1 : ℤ) ≤ k / n := (Int.le_ediv_iff_mul_le hn0).mpr (by omega)
          omega
        have hrec : x ((k - n) % n) = x (k - n) :=
          ih _ hdec (k - n) rfl (by omega) (by omega)
        have hemod : (k - n) % (n : ℤ) = k % n := by
          have hrw : k - (n : ℤ) = k + n * (-1) := by ring
          rw [hrw, Int.add_mul_emod_self_left]
        have hstep : x (k - n) = x k := by
          have h := hagree (k - n) (by omega)
          simpa using h
        rw [← hemod, hrec, hstep]
      · -- `0 < k < n`: base case.
        have hklt : k < (n : ℤ) := not_le.mp hkge
        rw [Int.emod_eq_of_lt (le_of_lt hkpos) hklt]

/-- The central periodization `j ↦ x (j % n)` is genuinely `n`-periodic: applying the `n`-th shift
returns it unchanged. -/
theorem biShiftMap_iterate_periodize (x : BiShift α₀) (n : ℕ) :
    biShiftMap^[n] (fun j => x (j % (n : ℤ))) = (fun j => x (j % (n : ℤ))) := by
  funext j
  rw [biShiftMap_iterate_apply]
  show x ((j + (n : ℤ)) % n) = x (j % n)
  congr 1
  have hrw : j + (n : ℤ) = j + n * 1 := by ring
  rw [hrw, Int.add_mul_emod_self_left]

/-! ### The exponential closing property -/

section Metric

variable [TopologicalSpace α₀] [DiscreteTopology α₀]

attribute [local instance] biShiftMetricSpace

/-- **Exponential closing for the two-sided full shift** (Katok–Hasselblatt §6.4/§19.2). For every
Hölder exponent `α > 0`, the two-sided full shift `biShiftMap` on `BiShift α₀` satisfies the
summed-cost closing property `ExpClosing biShiftMap α 1 K` with the explicit constant
`K = 2/(1 - (1/2)^α) ≥ 0` — *twice* the one-sided constant of `expClosing_shiftMap`, reflecting the
bilateral shadowing profile `θ^min(i, n-i)`.

The closing radius `δ = 1` is vacuous (all distances `≤ 1`); the shadow of a point `x` that almost
`n`-returns is the central periodization `p j := x (j % n)`, which needs no admissibility
bookkeeping because the full shift is the simplest mixing SFT. -/
theorem expClosing_biShiftMap {α : ℝ} (hα : 0 < α) :
    ExpClosing (biShiftMap (α₀ := α₀)) α 1 (2 / (1 - (1 / 2) ^ α)) := by
  intro n x _hx
  rcases eq_or_ne x (biShiftMap^[n] x) with hxeq | hne_x
  · -- `x` is already `n`-periodic: it shadows itself with zero cost.
    refine ⟨x, hxeq.symm, ?_⟩
    have hz : ∀ i ∈ Finset.range n,
        dist (biShiftMap^[i] x) (biShiftMap^[i] x) ^ α = 0 :=
      fun i _ => by rw [dist_self, Real.zero_rpow (ne_of_gt hα)]
    refine le_of_eq ?_
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, ← hxeq, dist_self,
      Real.zero_rpow (ne_of_gt hα), mul_zero]
  · -- Main case: `x ≠ σ^n x`, so `n ≥ 1` and the first-difference index `N` is well defined.
    set N := firstDiffZ x (biShiftMap^[n] x) with hN
    have hn : 0 < n :=
      Nat.pos_of_ne_zero (by rintro rfl; exact hne_x (Function.iterate_zero_apply _ _).symm)
    have hdist : dist x (biShiftMap^[n] x) = (1 / 2 : ℝ) ^ N := by
      rw [dist_eq_distZ]; exact distZ_of_ne hne_x
    set θ := (1 / 2 : ℝ) ^ α with hθdef
    have hθ0 : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos (by norm_num) α
    have hθ1 : θ < 1 := by rw [hθdef]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hα
    have hpow : ∀ m : ℕ, ((1 / 2 : ℝ) ^ m) ^ α = θ ^ m := fun m => by
      rw [hθdef]; exact half_pow_rpow α m
    have hmin_sum : ∑ i ∈ Finset.range n, θ ^ min i (n - i) ≤ 2 * (1 - θ)⁻¹ :=
      min_regime_sum_le hθ0.le hθ1 n
    -- `x` is `n`-periodic on the reach `|j| < N` because `x` and `σ^n x` agree there.
    have hagree : ∀ j : ℤ, j.natAbs < N → x j = x (j + n) := by
      intro j hj
      have hjfd : j.natAbs < firstDiffZ x (biShiftMap^[n] x) := by rw [← hN]; exact hj
      have h1 : x j = (biShiftMap^[n] x) j := apply_eq_of_natAbs_lt_firstDiffZ hjfd
      rwa [biShiftMap_iterate_apply] at h1
    -- The central periodic shadow.
    set p : BiShift α₀ := fun j => x (j % (n : ℤ)) with hp
    have hper_p : biShiftMap^[n] p = p := biShiftMap_iterate_periodize x n
    -- Per-step shadowing bound with the two-sided profile `(1/2)^min(N+i, N+n-i)`.
    have hshadow : ∀ i, i < n →
        dist (biShiftMap^[i] x) (biShiftMap^[i] p)
          ≤ (1 / 2 : ℝ) ^ min (N + i) (N + n - i) := by
      intro i hi
      rw [dist_eq_distZ, ← mem_symCyl_iff_distZ_le]
      intro j hj
      rw [biShiftMap_iterate_apply, biShiftMap_iterate_apply]
      simp only [hp]
      exact (periodize_agree hn hagree (j + i) (by omega) (by omega)).symm
    -- The `α`-th power of each shadowing distance is `≤ θ^min(N+i, N+n-i)`.
    have hterm : ∀ i ∈ Finset.range n,
        dist (biShiftMap^[i] x) (biShiftMap^[i] p) ^ α
          ≤ θ ^ min (N + i) (N + n - i) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      calc dist (biShiftMap^[i] x) (biShiftMap^[i] p) ^ α
          ≤ ((1 / 2 : ℝ) ^ min (N + i) (N + n - i)) ^ α :=
            Real.rpow_le_rpow dist_nonneg (hshadow i hi) hα.le
        _ = θ ^ min (N + i) (N + n - i) := hpow _
    have hsum1 : ∑ i ∈ Finset.range n, dist (biShiftMap^[i] x) (biShiftMap^[i] p) ^ α
        ≤ ∑ i ∈ Finset.range n, θ ^ min (N + i) (N + n - i) := Finset.sum_le_sum hterm
    -- Factor the shift `N` out of the two-sided profile: `min(N+i,N+n-i) = N + min(i,n-i)`.
    have hmineq : ∀ i ∈ Finset.range n,
        θ ^ min (N + i) (N + n - i) = θ ^ N * θ ^ min i (n - i) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [show min (N + i) (N + n - i) = N + min i (n - i) from by omega, pow_add]
    have hsum2 : ∑ i ∈ Finset.range n, θ ^ min (N + i) (N + n - i)
        = θ ^ N * ∑ i ∈ Finset.range n, θ ^ min i (n - i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hmineq
    have hsum3 : ∑ i ∈ Finset.range n, θ ^ min (N + i) (N + n - i)
        ≤ θ ^ N * (2 * (1 - θ)⁻¹) := by
      rw [hsum2]
      exact mul_le_mul_of_nonneg_left hmin_sum (pow_nonneg hθ0.le N)
    have hK : θ ^ N * (2 * (1 - θ)⁻¹)
        = 2 / (1 - θ) * dist x (biShiftMap^[n] x) ^ α := by
      rw [hdist, hpow N, div_eq_mul_inv]
      ring
    refine ⟨p, hper_p, ?_⟩
    calc ∑ i ∈ Finset.range n, dist (biShiftMap^[i] x) (biShiftMap^[i] p) ^ α
        ≤ ∑ i ∈ Finset.range n, θ ^ min (N + i) (N + n - i) := hsum1
      _ ≤ θ ^ N * (2 * (1 - θ)⁻¹) := hsum3
      _ = 2 / (1 - θ) * dist x (biShiftMap^[n] x) ^ α := hK

end Metric

end ErgodicTheory
