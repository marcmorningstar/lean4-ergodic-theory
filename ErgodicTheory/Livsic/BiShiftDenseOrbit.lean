/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.BiShiftMetric
import ErgodicTheory.Livsic.DenseOrbit

/-!
# A dense forward orbit on the two-sided full shift

This file is the bilateral analogue of `ErgodicTheory.Livsic.DenseOrbit`. Over any **nonempty,
encodable** alphabet `α₀` it exhibits a two-sided sequence whose forward `biShiftMap`-orbit is
dense for the `ℤ`-indexed θ-ultrametric of `ErgodicTheory.Livsic.BiShiftMetric`. It supplies the
two-sided dense-orbit ingredient for the Livšic instance (GitHub issue #32, tier 1).

## Construction

The witness `richPointZ` puts the fixed dummy symbol on every negative position and, on the
nonnegative positions, copies the one-sided `richPoint α₀`, i.e. the concatenation of *all* finite
words (`richPointZ j = if 0 ≤ j then richPoint α₀ j.toNat else dummy α₀`). Every finite window of a
target sequence `z` — the word on indices `-(N-1) … (N-1)` — appears as a block somewhere to the
right of `richPointZ` (it is *some* decoded word, so `richPoint`'s block-appearance lemma applies).
Centering that block by a forward shift of the right length places `richPointZ`'s orbit inside the
symmetric cylinder `symCyl z N`; the cylinder ↔ ball dictionary then upgrades cylinder-visiting to
metric density.

## Main results

* `ErgodicTheory.exists_orbit_mem_symCyl` — every symmetric cylinder is visited by the forward
  orbit of `richPointZ`.
* `ErgodicTheory.exists_denseRange_biShiftMap_orbit` — the forward `biShiftMap`-orbit of
  `richPointZ` is dense.

## References

* A. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972).
-/

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

noncomputable section

variable {α₀ : Type*} [Nonempty α₀] [Encodable α₀]

/-! ### The shift-iterate reads a forward coordinate -/

omit [Nonempty α₀] [Encodable α₀] in
/-- The `k`-th iterate of the two-sided shift advances every (integer) index by `k`:
`biShiftMap^[k] x n = x (n + k)`. (Restated locally to avoid importing the measure-theoretic
two-sided Bernoulli development.)

Kept `private` here: the identical public statement is exported by
`ErgodicTheory.Livsic.BiShiftClosing` (`ErgodicTheory.biShiftMap_iterate_apply`), and both modules
feed the same downstream two-sided Livšic assembly, so exactly one public copy is retained. -/
private theorem biShiftMap_iterate_apply (k : ℕ) (x : BiShift α₀) (n : ℤ) :
    (biShiftMap^[k] x) n = x (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', biShiftMap, ih]
    push_cast
    ring_nf

/-! ### The two-sided rich point -/

/-- The base point of the dense two-sided orbit: the fixed dummy symbol on the negative axis and
the one-sided `richPoint α₀` (the concatenation of all finite words) on the nonnegative axis. -/
def richPointZ : BiShift α₀ := fun j => if 0 ≤ j then richPoint α₀ j.toNat else dummy α₀

/-- On a nonnegative coordinate, `richPointZ` reads the one-sided rich point. -/
theorem richPointZ_of_nonneg {j : ℤ} (hj : 0 ≤ j) :
    richPointZ (α₀ := α₀) j = richPoint α₀ j.toNat := by
  simp only [richPointZ]
  rw [if_pos hj]

/-- Reading `richPointZ` at a natural-number coordinate returns the one-sided rich point there. -/
theorem richPointZ_natCast (n : ℕ) : richPointZ (α₀ := α₀) (n : ℤ) = richPoint α₀ n := by
  rw [richPointZ_of_nonneg (Int.natCast_nonneg n), Int.toNat_natCast]

/-- Iterate-apply for the two-sided rich point: `biShiftMap^[k] richPointZ` reads `richPointZ`
shifted forward by `k`. -/
theorem biShiftMap_iterate_richPointZ_apply (k : ℕ) (j : ℤ) :
    (biShiftMap^[k] (richPointZ (α₀ := α₀))) j = richPointZ (j + k) :=
  biShiftMap_iterate_apply k (richPointZ (α₀ := α₀)) j

/-! ### Cylinder visiting -/

/-- **Symmetric-cylinder visiting.** For every target sequence `z` and radius `N`, some forward
iterate of `richPointZ` lies in the symmetric cylinder `symCyl z N`. The window of `z` on indices
`-(N-1) … (N-1)` is *some* decoded word, hence appears as a block of `richPointZ`; shifting that
block to the origin centers it inside the cylinder. -/
theorem exists_orbit_mem_symCyl (z : BiShift α₀) (N : ℕ) :
    ∃ k : ℕ, biShiftMap^[k] (richPointZ (α₀ := α₀)) ∈ symCyl z N := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · refine ⟨0, ?_⟩
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  -- `N ≥ 1`: build the length-`2N-1` window word on indices `-(N-1) … (N-1)`.
  set w := List.ofFn (fun m : Fin (2 * N - 1) => z ((m : ℤ) - ((N : ℤ) - 1))) with hw
  have hwlen : w.length = 2 * N - 1 := by rw [hw]; simp
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, (Encodable.decode (α := List α₀) k₀).getD [] = w :=
    ⟨Encodable.encode w, by rw [Encodable.encodek]; rfl⟩
  refine ⟨(prefixList α₀ k₀).length + (N - 1), ?_⟩
  intro j hj
  -- `i` is the block offset corresponding to the target index `j`.
  set i := (j + ((N : ℤ) - 1)).toNat with hi_def
  have hi_lt : i < 2 * N - 1 := by omega
  have hi_word : i < (word α₀ k₀).length := by
    simp only [word, hk₀, List.length_append, hwlen, List.length_singleton]; omega
  have hindex : j + (↑((prefixList α₀ k₀).length + (N - 1)) : ℤ)
      = (↑((prefixList α₀ k₀).length + i) : ℤ) := by omega
  rw [biShiftMap_iterate_richPointZ_apply, hindex, richPointZ_natCast,
    richPoint_block α₀ k₀ i hi_word]
  simp only [word, hk₀]
  have hiw : i < w.length := by rw [hwlen]; exact hi_lt
  rw [List.getD_append _ _ _ _ hiw, List.getD_eq_getElem _ _ hiw]
  simp only [hw, List.getElem_ofFn]
  congr 1
  omega

/-! ### Density of the forward orbit -/

variable [TopologicalSpace α₀] [DiscreteTopology α₀]

attribute [local instance] biShiftMetricSpace

/-- **Dense forward orbit.** Over any nonempty encodable alphabet the two-sided full shift has a
point whose forward `biShiftMap`-orbit is dense for the θ-ultrametric. Cylinder-visiting
(`exists_orbit_mem_symCyl`) is turned into metric density through the cylinder ↔ ball dictionary
`mem_symCyl_iff_distZ_le`. -/
theorem exists_denseRange_biShiftMap_orbit :
    ∃ x₀ : BiShift α₀, DenseRange fun n : ℕ => biShiftMap^[n] x₀ := by
  refine ⟨richPointZ (α₀ := α₀), ?_⟩
  rw [Metric.denseRange_iff]
  intro z r hr
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < r := exists_pow_lt_of_lt_one hr (by norm_num)
  obtain ⟨k, hk⟩ := exists_orbit_mem_symCyl z N
  refine ⟨k, ?_⟩
  rw [dist_eq_distZ, distZ_comm]
  exact lt_of_le_of_lt ((mem_symCyl_iff_distZ_le _ z N).mp hk) hN

end

end ErgodicTheory
