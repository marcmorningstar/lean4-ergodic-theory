/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.BernoulliTwoSided
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Lattice

/-!
# The ℤ-indexed θ-ultrametric on the two-sided full shift

This file builds the bi-infinite θ-ultrametric on the two-sided full shift
`BiShift α₀ = ∀ _ : ℤ, α₀`, the two-sided analogue of the one-sided `PiNat` substrate recorded in
`ErgodicTheory.Livsic.ShiftMetric`. It is the metric layer for the two-sided Livšic instance
(GitHub issue #32, tier 1).

Rather than transport Mathlib's `PiNat` metric through a `ℤ ≃ ℕ` reindexing (which would scramble
the cylinder/​ball dictionary) or use `PiCountable.metricSpace` (whose `tsum` distance is *not* an
ultrametric), the metric is built **directly**. The first-difference index is measured by absolute
value of the (integer) coordinate:

* `firstDiffZ x y = sInf {n : ℕ | ∃ j : ℤ, j.natAbs = n ∧ x j ≠ y j}` — the least `|j|` at which
  `x` and `y` disagree (and `0` when `x = y`, by the `sInf ∅ = 0` convention).
* `distZ x y = if x = y then 0 else (1/2) ^ firstDiffZ x y` — the θ-ultrametric with `θ = 1/2`.
* `symCyl x N = {y | ∀ j, |j| < N → y j = x j}` — the symmetric cylinder of radius `N`.

## Main results

* `distZ_triangle_nonarch` — the non-archimedean (ultrametric) triangle inequality.
* `mem_symCyl_iff_distZ_le` — the cylinder ↔ ball dictionary `y ∈ symCyl x N ↔ distZ y x ≤ (1/2)^N`.
* `biShiftMetricSpace` — the metric space, built with `MetricSpace.ofDistTopology` against the
  **pre-existing product topology**, so `CompactSpace`/`BorelSpace` are inherited with no diamond
  (certified by the `Sanity` examples over `Fin 2`).
* `instIsUltrametricDist_biShift` — the metric is an ultrametric (a `local` instance mirroring the
  `local` metric).
* `lipschitzWith_two_biShiftMap` — the two-sided left shift is `2`-Lipschitz.
-/

open scoped NNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal

variable {α₀ : Type*}

/-! ### The first-difference index -/

/-- The **first-difference index** of two bi-infinite sequences: the least `|j|` (with `j : ℤ`) at
which `x` and `y` disagree. When `x = y` the underlying set is empty and `sInf ∅ = 0`. -/
noncomputable def firstDiffZ (x y : BiShift α₀) : ℕ :=
  sInf {n : ℕ | ∃ j : ℤ, j.natAbs = n ∧ x j ≠ y j}

/-- The first-difference index is symmetric. -/
theorem firstDiffZ_comm (x y : BiShift α₀) : firstDiffZ x y = firstDiffZ y x := by
  have hset : {n : ℕ | ∃ j : ℤ, j.natAbs = n ∧ x j ≠ y j}
      = {n : ℕ | ∃ j : ℤ, j.natAbs = n ∧ y j ≠ x j} := by
    ext n
    simp only [Set.mem_setOf_eq]
    exact ⟨fun ⟨j, hj, hne⟩ => ⟨j, hj, hne.symm⟩, fun ⟨j, hj, hne⟩ => ⟨j, hj, hne.symm⟩⟩
  unfold firstDiffZ
  rw [hset]

/-- Below the first-difference index the two sequences agree: if `|j| < firstDiffZ x y` then
`x j = y j`. (When `x = y` the index is `0`, so the hypothesis is vacuous.) -/
theorem apply_eq_of_natAbs_lt_firstDiffZ {x y : BiShift α₀} {j : ℤ}
    (hj : j.natAbs < firstDiffZ x y) : x j = y j := by
  by_contra hne
  have hmem : j.natAbs ∈ {n : ℕ | ∃ j' : ℤ, j'.natAbs = n ∧ x j' ≠ y j'} := ⟨j, rfl, hne⟩
  have hle : firstDiffZ x y ≤ j.natAbs := Nat.sInf_le hmem
  omega

/-- When `x ≠ y`, the first-difference index is attained: there is an index `j` with
`|j| = firstDiffZ x y` and `x j ≠ y j`. -/
theorem firstDiffZ_le_of_ne {x y : BiShift α₀} (h : x ≠ y) :
    ∃ j : ℤ, j.natAbs = firstDiffZ x y ∧ x j ≠ y j := by
  have hne : {n : ℕ | ∃ j : ℤ, j.natAbs = n ∧ x j ≠ y j}.Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact ⟨j.natAbs, j, rfl, hj⟩
  exact Nat.sInf_mem hne

/-- The ultrametric core for the first-difference index: `min (firstDiffZ x y) (firstDiffZ y z)`
does not exceed `firstDiffZ x z` (whenever `x ≠ z`, so the right side is genuinely attained). -/
theorem min_firstDiffZ_le {x y z : BiShift α₀} (h : x ≠ z) :
    min (firstDiffZ x y) (firstDiffZ y z) ≤ firstDiffZ x z := by
  obtain ⟨j, hj, hne⟩ := firstDiffZ_le_of_ne h
  by_contra hlt
  rw [not_le] at hlt
  have h1 : j.natAbs < firstDiffZ x y :=
    calc j.natAbs = firstDiffZ x z := hj
      _ < min (firstDiffZ x y) (firstDiffZ y z) := hlt
      _ ≤ firstDiffZ x y := min_le_left _ _
  have h2 : j.natAbs < firstDiffZ y z :=
    calc j.natAbs = firstDiffZ x z := hj
      _ < min (firstDiffZ x y) (firstDiffZ y z) := hlt
      _ ≤ firstDiffZ y z := min_le_right _ _
  exact hne ((apply_eq_of_natAbs_lt_firstDiffZ h1).trans (apply_eq_of_natAbs_lt_firstDiffZ h2))

/-! ### The θ-ultrametric distance -/

open scoped Classical in
/-- The **θ-ultrametric** on the two-sided full shift, with `θ = 1/2`: two distinct sequences are at
distance `(1/2) ^ firstDiffZ x y`, and equal sequences at distance `0`. -/
noncomputable def distZ (x y : BiShift α₀) : ℝ :=
  if x = y then 0 else (1 / 2 : ℝ) ^ firstDiffZ x y

/-- The distance of distinct sequences is the dyadic value at the first-difference index. -/
theorem distZ_of_ne {x y : BiShift α₀} (h : x ≠ y) :
    distZ x y = (1 / 2 : ℝ) ^ firstDiffZ x y := if_neg h

/-- Distance to self is zero. -/
theorem distZ_self (x : BiShift α₀) : distZ x x = 0 := if_pos rfl

/-- The distance is symmetric. -/
theorem distZ_comm (x y : BiShift α₀) : distZ x y = distZ y x := by
  by_cases h : x = y
  · rw [h]
  · unfold distZ
    rw [if_neg h, if_neg (Ne.symm h), firstDiffZ_comm]

/-- The distance is nonnegative. -/
theorem distZ_nonneg (x y : BiShift α₀) : 0 ≤ distZ x y := by
  unfold distZ
  split
  · exact le_refl 0
  · positivity

/-- The distance is bounded by `1`. -/
theorem distZ_le_one (x y : BiShift α₀) : distZ x y ≤ 1 := by
  unfold distZ
  split
  · norm_num
  · exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The distance vanishes exactly on the diagonal. -/
theorem distZ_eq_zero_iff (x y : BiShift α₀) : distZ x y = 0 ↔ x = y := by
  unfold distZ
  split
  · rename_i h
    simp [h]
  · rename_i h
    refine ⟨fun hz => absurd hz ?_, fun hxy => absurd hxy h⟩
    positivity

/-- **Non-archimedean triangle inequality.** The distance is an ultrametric:
`distZ x z ≤ max (distZ x y) (distZ y z)`. The equality cases (`x = z`, `x = y`, `y = z`) are
handled directly; when all three are distinct the inequality descends from `min_firstDiffZ_le`,
turning the min of exponents into the max of dyadic values. -/
theorem distZ_triangle_nonarch (x y z : BiShift α₀) :
    distZ x z ≤ max (distZ x y) (distZ y z) := by
  by_cases hxz : x = z
  · rw [hxz, distZ_self]
    exact le_max_of_le_left (distZ_nonneg z y)
  by_cases hxy : x = y
  · rw [hxy]
    exact le_max_right _ _
  by_cases hyz : y = z
  · rw [hyz]
    exact le_max_left _ _
  rw [distZ_of_ne hxz, distZ_of_ne hxy, distZ_of_ne hyz]
  have hmin : min (firstDiffZ x y) (firstDiffZ y z) ≤ firstDiffZ x z := min_firstDiffZ_le hxz
  have hpow : (1 / 2 : ℝ) ^ firstDiffZ x z
      ≤ (1 / 2 : ℝ) ^ min (firstDiffZ x y) (firstDiffZ y z) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmin
  have hmax : (1 / 2 : ℝ) ^ min (firstDiffZ x y) (firstDiffZ y z)
      = max ((1 / 2 : ℝ) ^ firstDiffZ x y) ((1 / 2 : ℝ) ^ firstDiffZ y z) := by
    rcases le_total (firstDiffZ x y) (firstDiffZ y z) with hle | hle
    · rw [min_eq_left hle, max_eq_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hle)]
    · rw [min_eq_right hle, max_eq_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hle)]
  rw [hmax] at hpow
  exact hpow

/-- The ordinary triangle inequality, extracted from the non-archimedean one (as
`MetricSpace.ofDistTopology` requires it). -/
theorem distZ_triangle (x y z : BiShift α₀) : distZ x z ≤ distZ x y + distZ y z :=
  le_trans (distZ_triangle_nonarch x y z)
    (max_le (le_add_of_nonneg_right (distZ_nonneg y z))
      (le_add_of_nonneg_left (distZ_nonneg x y)))

/-! ### Symmetric cylinders and the cylinder ↔ ball dictionary -/

/-- The **symmetric cylinder** of radius `N` around `x`: the sequences agreeing with `x` on every
coordinate `j` with `|j| < N`. -/
def symCyl (x : BiShift α₀) (N : ℕ) : Set (BiShift α₀) :=
  {y | ∀ j : ℤ, j.natAbs < N → y j = x j}

/-- A sequence lies in its own symmetric cylinders. -/
theorem self_mem_symCyl (x : BiShift α₀) (N : ℕ) : x ∈ symCyl x N := by
  intro j _
  rfl

/-- **Cylinder ↔ ball dictionary.** `y` lies in the symmetric cylinder of radius `N` around `x`
iff `distZ y x ≤ (1/2)^N`. -/
theorem mem_symCyl_iff_distZ_le (y x : BiShift α₀) (N : ℕ) :
    y ∈ symCyl x N ↔ distZ y x ≤ (1 / 2 : ℝ) ^ N := by
  by_cases hyx : y = x
  · rw [hyx]
    exact iff_of_true (self_mem_symCyl x N) (by rw [distZ_self]; positivity)
  · rw [distZ_of_ne hyx, pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)]
    simp only [symCyl, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨j, hj, hne⟩ := firstDiffZ_le_of_ne hyx
      exact hne (h j (by omega))
    · intro h j hj
      exact apply_eq_of_natAbs_lt_firstDiffZ (lt_of_lt_of_le hj h)

/-! ### Compatibility with the product topology -/

variable [TopologicalSpace α₀] [DiscreteTopology α₀]

/-- Every symmetric cylinder is open: it is a finite-coordinate box `Set.pi (Ioo (-N) N)` of
open singletons (the alphabet being discrete). -/
theorem isOpen_symCyl (x : BiShift α₀) (N : ℕ) : IsOpen (symCyl x N) := by
  have heq : symCyl x N
      = Set.pi (Set.Ioo (-(N : ℤ)) (N : ℤ)) (fun j => {x j}) := by
    ext y
    simp only [symCyl, Set.mem_setOf_eq, Set.mem_pi, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · intro h j hj
      exact h j (by omega)
    · intro h j hj
      exact h j (by omega)
  rw [heq]
  exact isOpen_set_pi (Set.finite_Ioo _ _) (fun _ _ => isOpen_discrete _)

/-- **Topological compatibility.** The `distZ`-openness criterion agrees with the pre-existing
product topology, in the exact shape consumed by `MetricSpace.ofDistTopology`. Forward: a
product-open set unpacks via `isOpen_pi_iff` into a finite box, which a symmetric cylinder of large
radius refines. Backward: a `distZ`-ball around each point is a symmetric cylinder, which is open by
`isOpen_symCyl`. -/
theorem isOpen_iff_distZ (s : Set (BiShift α₀)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, distZ x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    rw [isOpen_pi_iff] at hs
    obtain ⟨I, u, hu, hsub⟩ := hs x hx
    refine ⟨(1 / 2 : ℝ) ^ (I.sup (fun i => i.natAbs) + 1), by positivity, fun y hy => ?_⟩
    apply hsub
    intro i hi
    have hiI : i ∈ I := Finset.mem_coe.mp hi
    have hyx : y i = x i := by
      have hle : distZ y x ≤ (1 / 2 : ℝ) ^ (I.sup (fun i => i.natAbs) + 1) := by
        rw [distZ_comm]; exact le_of_lt hy
      have hmem : y ∈ symCyl x (I.sup (fun i => i.natAbs) + 1) :=
        (mem_symCyl_iff_distZ_le y x _).mpr hle
      exact hmem i (Nat.lt_succ_of_le (Finset.le_sup hiI))
    rw [hyx]
    exact (hu i hiI).2
  · intro h
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨ε, hε, hball⟩ := h x hx
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨symCyl x N, ?_, isOpen_symCyl x N, self_mem_symCyl x N⟩
    intro y hy
    rw [mem_symCyl_iff_distZ_le] at hy
    apply hball
    calc distZ x y = distZ y x := distZ_comm x y
      _ ≤ (1 / 2 : ℝ) ^ N := hy
      _ < ε := hN

/-- **The two-sided θ-ultrametric metric space.** Built with `MetricSpace.ofDistTopology` against
the pre-existing product topology, so the metric topology is *definitionally* the product topology
and inherited structure (`CompactSpace`, `BorelSpace`, …) carries over with no diamond. The
`@[implicit_reducible]` attribute is required for a metric-space `def`. -/
@[implicit_reducible]
noncomputable def biShiftMetricSpace : MetricSpace (BiShift α₀) :=
  MetricSpace.ofDistTopology distZ distZ_self distZ_comm distZ_triangle isOpen_iff_distZ
    fun x y => (distZ_eq_zero_iff x y).mp

/-! ### The metric layer under the local instance -/

section Sanity

attribute [local instance] biShiftMetricSpace

/-- Under the metric instance, `dist` is definitionally `distZ`. -/
theorem dist_eq_distZ (x y : BiShift α₀) : dist x y = distZ x y := rfl

/-- The two-sided θ-metric is an ultrametric (a `local` instance mirroring the `local` metric). -/
instance instIsUltrametricDist_biShift : IsUltrametricDist (BiShift α₀) :=
  ⟨fun x y z => distZ_triangle_nonarch x y z⟩

/-- **The two-sided left shift is `2`-Lipschitz** for the θ-ultrametric. If `biShiftMap x` and
`biShiftMap y` first differ at index `j`, then `x, y` differ at `j + 1`, and
`|j + 1| ≤ |j| + 1`, so the first-difference index grows by at most one and the distance by at most
the factor `2`. -/
theorem lipschitzWith_two_biShiftMap : LipschitzWith 2 (biShiftMap (α₀ := α₀)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases eq_or_ne (biShiftMap x) (biShiftMap y) with hs | hs
  · rw [hs, dist_self]
    exact mul_nonneg (by positivity) dist_nonneg
  · have hxy : x ≠ y := fun h => hs (by rw [h])
    simp only [dist_eq_distZ]
    rw [distZ_of_ne hs, distZ_of_ne hxy]
    obtain ⟨j, hj, hne⟩ := firstDiffZ_le_of_ne hs
    have hne' : x (j + 1) ≠ y (j + 1) := hne
    have hmem : (j + 1).natAbs ∈ {n : ℕ | ∃ i : ℤ, i.natAbs = n ∧ x i ≠ y i} :=
      ⟨j + 1, rfl, hne'⟩
    have hKle : firstDiffZ x y ≤ (j + 1).natAbs := Nat.sInf_le hmem
    have hkey : firstDiffZ x y ≤ firstDiffZ (biShiftMap x) (biShiftMap y) + 1 := by
      have hb : (j + 1).natAbs ≤ j.natAbs + 1 := by omega
      omega
    have hstep : (1 / 2 : ℝ) ^ (firstDiffZ (biShiftMap x) (biShiftMap y) + 1)
        ≤ (1 / 2 : ℝ) ^ firstDiffZ x y :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkey
    have hfin : (1 / 2 : ℝ) ^ firstDiffZ (biShiftMap x) (biShiftMap y)
        ≤ 2 * (1 / 2 : ℝ) ^ firstDiffZ x y := by
      have hhalf : (1 / 2 : ℝ) ^ firstDiffZ (biShiftMap x) (biShiftMap y)
          = 2 * (1 / 2 : ℝ) ^ (firstDiffZ (biShiftMap x) (biShiftMap y) + 1) := by
        rw [pow_succ]; ring
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    have h2 : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
    rw [h2]
    exact hfin

/-! ### No-diamond certificates over `Fin 2`

The pre-existing product-topology structure is inherited through the metric instance with no
diamond: compactness (Tychonoff) and the Borel structure are found by `inferInstance`. -/

example : CompactSpace (BiShift (Fin 2)) := inferInstance

example : BorelSpace (BiShift (Fin 2)) := inferInstance

end Sanity

end ErgodicTheory
