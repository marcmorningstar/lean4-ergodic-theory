/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Examples.Elementary
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# The exponential closing property for the doubling map

This file establishes the concrete instance of the abstracted `ExpClosing` property
(`ErgodicTheory.Livsic.Defs`) for the **doubling map** `doublingMap : y ↦ 2 • y` on the unit
circle `UnitAddCircle`, the natural smooth expanding instance of the Livšic cohomological rigidity
theorem (issue #33). It is the geometric input that feeds the substantive Livšic direction: every
almost-periodic point is `α`-Hölder shadowed by a genuine periodic point, with a summed shadowing
cost geometrically controlled by the return gap.

## The closing construction

Because `doublingMap^[n] = (2 ^ n) • ·` is a group endomorphism, a point `x = ↑a` almost `n`-returns
exactly when `2 ^ n a` is close to `a` mod `1`. The periodic shadow is obtained by *rounding*: with
`M := 2 ^ n - 1` and `k := round (M a)`, the point `p := ↑a − ↑((M a − k) / M)` is a genuine
`n`-periodic point (`M • p = 0`, so `2 ^ n • p = p`) lying within `‖x − 2 ^ n • x‖ / M` of `x`.
The `i`-th orbit points then satisfy `dist (2 ^ i • x) (2 ^ i • p) ≤ 2 ^ i ‖x − p‖`, and the
`α`-th powers of these distances sum to a geometric series bounded by
`(2 ^ α / (2 ^ α − 1)) · ‖x − 2 ^ n • x‖ ^ α`, using `2 ^ n / (2 ^ n − 1) ≤ 2` (maximised at
`n = 1`).

## Main results

* `ErgodicTheory.doublingMap_iterate` — the `n`-th iterate is scalar multiplication by `2 ^ n`.
* `ErgodicTheory.exists_doubling_periodic_shadow` — the rounding construction of a periodic shadow
  with the quantitative return-gap bound.
* `ErgodicTheory.expClosing_doublingMap` — the doubling map satisfies `ExpClosing doublingMap r 1 K`
  with the explicit constant `K = 2 ^ r / (2 ^ r − 1)`, for every Hölder exponent `r > 0`.

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.1 (Livšic) and Ch. 19 (expanding maps and the closing lemma).
-/

open Function
open scoped NNReal

namespace ErgodicTheory

/-- `n • (↑r) = ↑(n * r)` on the unit circle: the coercion `ℝ → UnitAddCircle` is additive, so it
intertwines the natural `ℕ`-action with real multiplication. -/
theorem coe_nsmul' (m : ℕ) (r : ℝ) :
    m • ((r : UnitAddCircle)) = (((m : ℝ) * r : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]

/-- **The `n`-th iterate of the doubling map is multiplication by `2 ^ n`.** -/
theorem doublingMap_iterate (n : ℕ) (x : UnitAddCircle) :
    doublingMap^[n] x = (2 ^ n : ℕ) • x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [doublingMap]
    rw [smul_smul, ← pow_succ']

/-- **The rounding shadow lemma for the doubling map.** For `n ≥ 1` and any `x : UnitAddCircle`
there is a genuine `2 ^ n`-periodic point `p` whose distance to `x` is controlled by the return gap:
`‖x − p‖ ≤ ‖x − 2 ^ n • x‖ / (2 ^ n − 1)`.

Construction: writing `x = ↑a`, set `M := 2 ^ n − 1`, `k := round (M a)` and
`p := ↑a − ↑((M a − k) / M)`. Then `M • p = ↑k = 0`, so `2 ^ n • p = (M + 1) • p = p`, and the
displacement `‖x − p‖ = ‖↑((M a − k) / M)‖ ≤ |M a − k| / M = ‖x − 2 ^ n • x‖ / M`. -/
theorem exists_doubling_periodic_shadow (n : ℕ) (hn : 1 ≤ n) (x : UnitAddCircle) :
    ∃ p, (2 ^ n : ℕ) • p = p ∧
      ‖x - p‖ ≤ ‖x - (2 ^ n : ℕ) • x‖ / ((2 ^ n - 1 : ℕ) : ℝ) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  set M : ℕ := 2 ^ n - 1 with hMdef
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have h2n2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hMpos : 1 ≤ M := by omega
  have hMposℝ : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMposℝ
  have hMcast : (M : ℝ) = (2 : ℝ) ^ n - 1 := by rw [hMdef, Nat.cast_sub h2n]; push_cast; ring
  set k : ℤ := round ((M : ℝ) * a) with hkdef
  set w : UnitAddCircle := ((((M : ℝ) * a - (k : ℝ)) / (M : ℝ) : ℝ) : UnitAddCircle) with hwdef
  set p : UnitAddCircle := (↑a : UnitAddCircle) - w with hpdef
  refine ⟨p, ?_, ?_⟩
  · -- Fixed point: `2 ^ n • p = p`, reducing to `M • p = 0`.
    have hE : (M : ℝ) * a - (M : ℝ) * (((M : ℝ) * a - (k : ℝ)) / (M : ℝ)) = (k : ℝ) := by
      field_simp
      ring
    have hMp0 : (M : ℕ) • p = 0 := by
      rw [hpdef, hwdef, smul_sub, coe_nsmul', coe_nsmul', ← AddCircle.coe_sub, hE,
        AddCircle.coe_eq_zero_iff]
      exact ⟨k, by simp⟩
    have h2nM : (2 : ℕ) ^ n = M + 1 := by omega
    rw [h2nM, succ_nsmul, hMp0, zero_add]
  · -- Norm bound.
    have hxp : (↑a : UnitAddCircle) - p = w := by rw [hpdef]; abel
    have hgap : ‖(↑a : UnitAddCircle) - (2 ^ n : ℕ) • (↑a : UnitAddCircle)‖
        = |(M : ℝ) * a - (k : ℝ)| := by
      rw [coe_nsmul', ← AddCircle.coe_sub]
      have heq : a - ((2 ^ n : ℕ) : ℝ) * a = -((M : ℝ) * a) := by
        rw [hMcast]; push_cast; ring
      rw [heq, AddCircle.coe_neg, norm_neg, UnitAddCircle.norm_eq, ← hkdef]
    rw [hxp, hgap, hwdef]
    calc ‖(((M : ℝ) * a - (k : ℝ)) / (M : ℝ) : UnitAddCircle)‖
        ≤ ‖(((M : ℝ) * a - (k : ℝ)) / (M : ℝ) : ℝ)‖ := QuotientAddGroup.norm_mk_le_norm
      _ = |(M : ℝ) * a - (k : ℝ)| / (M : ℝ) := by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hMposℝ]

/-- **Exponential closing for the doubling map.** For every Hölder exponent `r > 0`, the doubling
map `doublingMap` on `UnitAddCircle` satisfies the summed-cost closing property
`ExpClosing doublingMap r 1 (2 ^ r / (2 ^ r − 1))`.

The closing radius `δ = 1` is unused (the construction is unconditional): the shadow of a point `x`
that almost `n`-returns is the rounding point `p` of `exists_doubling_periodic_shadow`, whose orbit
`α`-Hölder-shadows that of `x` with summed cost `≤ (2 ^ r / (2 ^ r − 1)) · dist x (T^[n] x) ^ r`. -/
theorem expClosing_doublingMap {r : ℝ} (hr : 0 < r) :
    ExpClosing doublingMap r 1 (2 ^ r / (2 ^ r - 1)) := by
  intro n x _hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `p := x`, empty sum.
    refine ⟨x, by simp, ?_⟩
    simp [Real.zero_rpow (ne_of_gt hr)]
  · -- Main case `n ≥ 1`.
    set s : ℝ := (2 : ℝ) ^ r with hs
    have hs0 : (0 : ℝ) < s := Real.rpow_pos_of_pos (by norm_num) _
    have hs1 : (1 : ℝ) < s := Real.one_lt_rpow (by norm_num) hr
    have hsm1 : (0 : ℝ) < s - 1 := by linarith
    have hpow_swap : ∀ i : ℕ, ((2 : ℝ) ^ i) ^ r = s ^ i := by
      intro i
      rw [hs, ← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    obtain ⟨p, hpfix, hpbound⟩ := exists_doubling_periodic_shadow n hn x
    set Mn : ℝ := ((2 ^ n - 1 : ℕ) : ℝ) with hMndef
    have hpfix' : doublingMap^[n] p = p := by rw [doublingMap_iterate]; exact hpfix
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    have h2n2 : 2 ≤ 2 ^ n := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hMnpos : (0 : ℝ) < Mn := by rw [hMndef]; exact_mod_cast Nat.sub_pos_of_lt (by omega)
    have hMn_eq : Mn = (2 : ℝ) ^ n - 1 := by rw [hMndef, Nat.cast_sub h2n]; push_cast; ring
    have hMn_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ n - 1 := by rw [← hMn_eq]; exact hMnpos.le
    have hgap_eq : dist x (doublingMap^[n] x) = ‖x - (2 ^ n : ℕ) • x‖ := by
      rw [dist_eq_norm, doublingMap_iterate]
    -- Per-term shadowing bound.
    have hterm : ∀ i ∈ Finset.range n,
        dist (doublingMap^[i] x) (doublingMap^[i] p) ^ r ≤ s ^ i * ‖x - p‖ ^ r := by
      intro i _
      have hdi : dist (doublingMap^[i] x) (doublingMap^[i] p) ≤ (2 : ℝ) ^ i * ‖x - p‖ := by
        rw [dist_eq_norm, doublingMap_iterate, doublingMap_iterate, ← smul_sub]
        calc ‖(2 ^ i : ℕ) • (x - p)‖ ≤ ((2 ^ i : ℕ) : ℝ) * ‖x - p‖ := norm_nsmul_le
          _ = (2 : ℝ) ^ i * ‖x - p‖ := by push_cast; ring
      calc dist (doublingMap^[i] x) (doublingMap^[i] p) ^ r
          ≤ ((2 : ℝ) ^ i * ‖x - p‖) ^ r := Real.rpow_le_rpow dist_nonneg hdi hr.le
        _ = ((2 : ℝ) ^ i) ^ r * ‖x - p‖ ^ r := Real.mul_rpow (by positivity) (norm_nonneg _)
        _ = s ^ i * ‖x - p‖ ^ r := by rw [hpow_swap i]
    -- Sum bound.
    have hsum : ∑ i ∈ Finset.range n, dist (doublingMap^[i] x) (doublingMap^[i] p) ^ r
        ≤ ‖x - p‖ ^ r * ((s ^ n - 1) / (s - 1)) := by
      calc ∑ i ∈ Finset.range n, dist (doublingMap^[i] x) (doublingMap^[i] p) ^ r
          ≤ ∑ i ∈ Finset.range n, s ^ i * ‖x - p‖ ^ r := Finset.sum_le_sum hterm
        _ = ‖x - p‖ ^ r * ∑ i ∈ Finset.range n, s ^ i := by rw [← Finset.sum_mul, mul_comm]
        _ = ‖x - p‖ ^ r * ((s ^ n - 1) / (s - 1)) := by rw [geom_sum_eq hs1.ne']
    -- The key polynomial inequality (denominators cleared).
    have hMle : ‖x - p‖ * Mn ≤ ‖x - (2 ^ n : ℕ) • x‖ := (le_div_iff₀ hMnpos).1 hpbound
    have hkey1 : ‖x - p‖ ^ r * Mn ^ r ≤ ‖x - (2 ^ n : ℕ) • x‖ ^ r := by
      rw [← Real.mul_rpow (norm_nonneg _) hMnpos.le]
      exact Real.rpow_le_rpow (by positivity) hMle hr.le
    have hcast2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast h2n2
    have hge : (2 : ℝ) ^ n ≤ 2 * ((2 : ℝ) ^ n - 1) := by linarith
    have hsn_eq : s ^ n = ((2 : ℝ) ^ n) ^ r := (hpow_swap n).symm
    have hprod : s * Mn ^ r = (2 * ((2 : ℝ) ^ n - 1)) ^ r := by
      rw [hs, hMn_eq, ← Real.mul_rpow (by norm_num) hMn_nonneg]
    have hkey2 : s ^ n - 1 ≤ s * Mn ^ r := by
      have hstep : s ^ n ≤ s * Mn ^ r := by
        rw [hsn_eq, hprod]
        exact Real.rpow_le_rpow (by positivity) hge hr.le
      linarith
    have key : ‖x - p‖ ^ r * (s ^ n - 1) ≤ s * ‖x - (2 ^ n : ℕ) • x‖ ^ r := by
      calc ‖x - p‖ ^ r * (s ^ n - 1)
          ≤ ‖x - p‖ ^ r * (s * Mn ^ r) :=
            mul_le_mul_of_nonneg_left hkey2 (Real.rpow_nonneg (norm_nonneg _) _)
        _ = s * (‖x - p‖ ^ r * Mn ^ r) := by ring
        _ ≤ s * ‖x - (2 ^ n : ℕ) • x‖ ^ r := mul_le_mul_of_nonneg_left hkey1 hs0.le
    -- Assemble.
    refine ⟨p, hpfix', ?_⟩
    rw [hgap_eq]
    refine le_trans hsum ?_
    rw [← mul_div_assoc, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hsm1]
    exact key

end ErgodicTheory
