/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.SymbolicDimension
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The `PiNat` metric substrate for the full-shift Livšic instance

This file records the metric facts about the one-sided full shift `Shift α₀ := ∀ _ : ℕ, α₀`, under
Mathlib's `PiNat` ultrametric `dist x y = (1/2) ^ firstDiff x y`, that the full-shift Livšic
instance (`ErgodicTheory.Livsic.FullShift`) consumes. It reuses the exact local-`PiNat` idiom of
`ErgodicTheory.Multifractal.SymbolicDimension` (sharing `Shift`/`shiftMap`), so no wrapper metric is
introduced: `PiNat.metricSpace` needs a discrete topology on the alphabet and is registered only as
a `local instance`, never a global Mathlib instance.

## Main results

* `lipschitzWith_two_shiftMap` — the left shift is `2`-Lipschitz for the `PiNat` ultrametric (and
  the constant `2` is tight), hence continuous.
* `agree_iff_dist_le` — the coordinate-agreement ↔ distance dictionary: `x, y` agree on their first
  `n` coordinates iff `dist x y ≤ (1/2) ^ n`.
* `instIsUltrametricDist_shift` — the `PiNat` metric on the shift is an ultrametric (a `local`
  instance mirroring the `local` metric).
* `half_pow_rpow` — the npow/rpow interchange `((1/2)^k)^s = ((1/2)^s)^k`, shared by the two
  closing/​shadowing modules to turn a per-step dyadic bound into a term of a geometric series.
* `geomSum_range_le_inv_one_sub` — the geometric partial-sum bound `∑_{i<n} θ^i ≤ (1-θ)⁻¹` for
  `0 ≤ θ < 1`, likewise shared by both consumers.
* `sum_shadow_le` — the ambient periodization shadow estimate: `fun j => y (j % n)` `α`-Hölder
  shadows the orbit of `y` with geometrically summable cost. It is the bookkeeping-free `n ≥ 1` core
  of both the full-shift (`FullShiftClosing`) and the subshift-of-finite-type (`SubshiftFiniteType`)
  closing properties.

Compactness of `Shift α₀` for a compact (e.g. `Finite`) discrete alphabet is not stated separately:
it is `inferInstance` (Tychonoff, `Pi.compactSpace`) under the local metric, and the downstream
instance simply invokes it.
-/

open Topology Function Set
open scoped ENNReal NNReal

namespace ErgodicTheory.Livsic

open ErgodicTheory.Multifractal

/-! ### Shared geometric bookkeeping for the closing/shadowing series

These two alphabet-independent real-analysis facts are consumed *identically* by both the
closing-property module (`FullShiftClosing`) and the bounded-tier shadowing module
(`BoundedRigidity`); they live here (the common metric substrate both already import) so neither
copy is duplicated. -/

/-- The npow/rpow interchange `((1/2)^k)^s = ((1/2)^s)^k`: the `k`-fold `ℕ`-power commutes with the
real exponent `s` through the common `rpow` `(1/2)^(k·s)`. Used to turn a per-step dyadic bound
`((1/2)^m)^r` into a term `θ^m` of a genuine geometric series with ratio `θ = (1/2)^r`. -/
theorem half_pow_rpow (s : ℝ) (k : ℕ) :
    ((1 / 2 : ℝ) ^ k) ^ s = ((1 / 2 : ℝ) ^ s) ^ k := by
  rw [← Real.rpow_natCast (1 / 2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.rpow_natCast ((1 / 2 : ℝ) ^ s) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_comm]

/-- The geometric partial-sum bound `∑_{i<n} θ^i ≤ (1-θ)⁻¹` for `0 ≤ θ < 1`: the finite partial sum
is dominated by the full convergent geometric series `∑' i, θ^i = (1-θ)⁻¹`. -/
theorem geomSum_range_le_inv_one_sub {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, θ ^ i ≤ (1 - θ)⁻¹ := by
  have hsum := summable_geometric_of_lt_one h0 h1
  have hle := Summable.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg h0 i) hsum
  rwa [tsum_geometric_of_lt_one h0 h1] at hle

variable {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]

attribute [local instance] PiNat.metricSpace

/-! ### `shiftMap` is `2`-Lipschitz (and `2` is tight) -/

/-- The left shift is `2`-Lipschitz for the `PiNat` ultrametric. If `x, y` first differ at index
`k` then `shiftMap x, shiftMap y` first differ at index `≥ k - 1`, so their distance grows by at
most the factor `2`. The constant `2` is *tight*: with `x = (0,1,0,0,…)`, `y = (0,0,0,0,…)` one has
`dist x y = 1/2` but `dist (shiftMap x) (shiftMap y) = 1`. -/
theorem lipschitzWith_two_shiftMap : LipschitzWith 2 (shiftMap (α₀ := α₀)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases eq_or_ne (shiftMap x) (shiftMap y) with hsxy | hsxy
  · rw [hsxy, dist_self]; positivity
  · have hxy : x ≠ y := fun h => hsxy (by rw [h])
    rw [PiNat.dist_eq_of_ne hsxy, PiNat.dist_eq_of_ne hxy]
    set j := PiNat.firstDiff (shiftMap x) (shiftMap y) with hj
    set k := PiNat.firstDiff x y with hk
    -- key inequality `k ≤ j + 1`: the shifts differ at `j`, i.e. `x (j+1) ≠ y (j+1)`.
    have hne : x (j + 1) ≠ y (j + 1) := by
      have h := PiNat.apply_firstDiff_ne hsxy
      simpa only [shiftMap, ← hj] using h
    have hkey : k ≤ j + 1 := by
      by_contra hlt
      rw [not_le] at hlt
      exact hne (PiNat.apply_eq_of_lt_firstDiff (by rw [← hk]; exact hlt))
    -- `(1/2)^j = 2·(1/2)^(j+1) ≤ 2·(1/2)^k`, and `↑(2 : ℝ≥0) = 2`.
    have hstep : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkey
    have hhalf : (1 / 2 : ℝ) ^ j = 2 * (1 / 2 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring
    have : (1 / 2 : ℝ) ^ j ≤ 2 * (1 / 2 : ℝ) ^ k := by
      rw [hhalf]; exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    calc (1 / 2 : ℝ) ^ j ≤ 2 * (1 / 2 : ℝ) ^ k := this
      _ = (2 : ℝ≥0) * (1 / 2 : ℝ) ^ k := by push_cast; ring

/-! ### The distance ↔ coordinate-agreement dictionary

The Livšic core translates "agree on first `n` coordinates" ⇔ "within dyadic distance". All of it
is pre-existing `PiNat` API; we only re-package the exact composed statements the core cites. -/

/-- **`≤` dictionary (iff).** `x, y` agree on the first `n` coordinates iff `dist x y ≤ (1/2)^n`.
This is `mem_cylinder_iff` composed with `mem_cylinder_iff_dist_le` (plus `dist_comm`). -/
theorem agree_iff_dist_le (n : ℕ) (x y : Shift α₀) :
    (∀ i < n, x i = y i) ↔ dist x y ≤ (1 / 2 : ℝ) ^ n := by
  rw [dist_comm, ← PiNat.mem_cylinder_iff_dist_le, PiNat.mem_cylinder_iff]
  exact ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩

/-! ### The periodization shadow estimate

The geometric heart of the closing property is the *periodization shadow estimate*, which lives
entirely on the ambient full shift and is independent of any admissibility bookkeeping. It is the
`n ≥ 1` core of both `ErgodicTheory.Livsic.expClosing_shiftMap` (the full shift) and
`ErgodicTheory.expClosing_sftShiftMap` (a subshift of finite type), so it is shared here (the common
metric substrate both import). It returns the bound for the **explicit** periodization
`fun j => y (j % n)` (rather than an existential witness), so the SFT instance can reuse it after
checking that this periodization lands in the SFT. -/

/-- **Periodization shadow estimate on the full shift.** If `y ≠ σ^n y` (`n ≥ 1`), the periodization
`p i := y (i % n)` `α`-Hölder-shadows the orbit of `y` with total cost geometrically controlled by
the return gap: `∑_{i<n} dist (σ^i y) (σ^i p)^α ≤ (1/2)^α / (1 - (1/2)^α) · dist y (σ^n y)^α`.

This is the ambient (bookkeeping-free) core of the closing property; the full-shift and SFT closing
lemmas reuse it verbatim once they have checked that the periodization is admissible. -/
theorem sum_shadow_le {α : ℝ} (hα : 0 < α) (n : ℕ) (_hn : 0 < n)
    (y : Shift α₀) (hne : y ≠ shiftMap^[n] y) :
    ∑ i ∈ Finset.range n,
        dist (shiftMap^[i] y) (shiftMap^[i] (fun j => y (j % n))) ^ α
      ≤ (1 / 2) ^ α / (1 - (1 / 2) ^ α) * dist y (shiftMap^[n] y) ^ α := by
  set N := PiNat.firstDiff y (shiftMap^[n] y) with hN
  have hdist : dist y (shiftMap^[n] y) = (1 / 2 : ℝ) ^ N := PiNat.dist_eq_of_ne hne
  set θ := (1 / 2 : ℝ) ^ α with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos (by norm_num) α
  have hθ1 : θ < 1 := by rw [hθdef]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hpow : ∀ m : ℕ, ((1 / 2 : ℝ) ^ m) ^ α = θ ^ m := fun m => by
    rw [hθdef]; exact half_pow_rpow α m
  have hgeom : ∑ i ∈ Finset.range n, θ ^ i ≤ (1 - θ)⁻¹ :=
    geomSum_range_le_inv_one_sub hθ0.le hθ1 n
  set p : Shift α₀ := fun i => y (i % n) with hp
  have hper : ∀ j, j < N → y j = y (j + n) := by
    intro j hj
    have hjfd : j < PiNat.firstDiff y (shiftMap^[n] y) := by rw [← hN]; exact hj
    have h1 : y j = (shiftMap^[n] y) j := PiNat.apply_eq_of_lt_firstDiff hjfd
    rwa [shiftMap_iterate_apply] at h1
  have hagree : ∀ i, i < n + N → p i = y i := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro hi
      rcases lt_or_ge i n with hlt | hge
      · simp only [hp, Nat.mod_eq_of_lt hlt]
      · simp only [hp]
        rw [Nat.mod_eq_sub_mod hge]
        have hind : p (i - n) = y (i - n) := ih (i - n) (by omega) (by omega)
        simp only [hp] at hind
        rw [hind, hper (i - n) (by omega)]
        congr 1
        omega
  have hle_i : ∀ i ∈ Finset.range n,
      dist (shiftMap^[i] y) (shiftMap^[i] p) ≤ (1 / 2 : ℝ) ^ (n + N - i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [← agree_iff_dist_le]
    intro j hj
    simp only [shiftMap_iterate_apply]
    exact (hagree (j + i) (by omega)).symm
  have hterm : ∀ i ∈ Finset.range n,
      dist (shiftMap^[i] y) (shiftMap^[i] p) ^ α ≤ θ ^ (n + N - i) := by
    intro i hi
    calc dist (shiftMap^[i] y) (shiftMap^[i] p) ^ α
        ≤ ((1 / 2 : ℝ) ^ (n + N - i)) ^ α :=
          Real.rpow_le_rpow dist_nonneg (hle_i i hi) hα.le
      _ = θ ^ (n + N - i) := hpow (n + N - i)
  have hsum1 : ∑ i ∈ Finset.range n, dist (shiftMap^[i] y) (shiftMap^[i] p) ^ α
      ≤ ∑ i ∈ Finset.range n, θ ^ (n + N - i) := Finset.sum_le_sum hterm
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
      = θ / (1 - θ) * dist y (shiftMap^[n] y) ^ α := by
    rw [hdist, hpow N, pow_succ]
    ring
  calc ∑ i ∈ Finset.range n, dist (shiftMap^[i] y) (shiftMap^[i] p) ^ α
      ≤ ∑ i ∈ Finset.range n, θ ^ (n + N - i) := hsum1
    _ ≤ θ ^ (N + 1) * (1 - θ)⁻¹ := hsum2
    _ = θ / (1 - θ) * dist y (shiftMap^[n] y) ^ α := hfin

/-! ### Ultrametric availability

Mathlib does **not** register a global `IsUltrametricDist` for the `PiNat` metric (the metric itself
is deliberately non-global), but the non-archimedean triangle inequality `dist_triangle_nonarch` is
available, so the instance is a one-liner. It is provided as a *local* instance to mirror the
metric. -/

/-- The `PiNat` metric on the shift is an ultrametric. -/
instance instIsUltrametricDist_shift : IsUltrametricDist (Shift α₀) :=
  ⟨fun x y z => PiNat.dist_triangle_nonarch x y z⟩

end ErgodicTheory.Livsic
