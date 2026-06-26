/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.SymbolicDimensionBernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Bernoulli entropy identity (N4a)

For the i.i.d. (Bernoulli) measure `bern ν` on the one-sided full shift `Shift α₀` over a finite
alphabet, the Kolmogorov–Sinai entropy of the coordinate partition equals the single-symbol
Shannon entropy `Hnu ν = ∑ i, negMulLog (ν {i}).toReal`.

The argument is the classical computation that the entropy of an i.i.d. process is additive over
coordinates:

* **N4a.1 (cell mass).** The depth-`n` join cell of the coordinate partition at an index
  `f : Fin n → α₀` is the length-`n` cylinder `{x | ∀ k : Fin n, x k = f k}`, whose `bern ν`-mass
  is the product `∏ k, (ν {f k}).toReal` of single-symbol masses (`Measure.infinitePi_pi`).
* **N4a.2 (per-`n` entropy).** Hence `ksEntropySeq n = ∑ f, negMulLog (∏ k, p (f k))` with
  `p a := (ν {a}).toReal`. The per-coordinate factorization
  `negMulLog (∏ k, p (f k)) = ∑ k, (∏ j, p (f j)) * (-log (p (f k)))` followed by the
  sum/product swap `Finset.sum_prod_piFinset` (and `∑ a, p a = 1`) collapses this to `n * Hnu ν`.
* **N4a.3 (Fekete limit).** Since `ksEntropySeq n = n * Hnu ν`, the averaged sequence
  `ksEntropySeq n / n` is eventually the constant `Hnu ν`; by uniqueness of the Fekete limit
  (`tendsto_ksEntropySeq`), the partition entropy is `Hnu ν`.

The system entropy identity `(ksEntropy).toReal = Hnu ν` then follows from the generator reduction
already proved on `main` (`ksEntropy_eq_ksEntropyPartition_of_generating` via
`coordPartition_isGenerating`), taking the ergodicity of the shift as a hypothesis (it is a
sibling node).

## Main results

* `Oseledets.Multifractal.ksEntropyPartition_coordPartition_bern_eq`
* `Oseledets.Multifractal.ksEntropy_bern_eq`
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

namespace Oseledets.Multifractal

open Oseledets.Entropy

variable {α₀ : Type*} [Fintype α₀] [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

attribute [local instance] PiNat.metricSpace

/-! ### N4a.0 — a real-analytic per-`f` factorization -/

/-- **Per-coordinate factorization of `negMulLog` of a product.** For any finite family
`p : Fin n → ℝ` of nonnegative reals,
`negMulLog (∏ k, p k) = ∑ k, (∏ j, p j) * (-log (p k))`. When every `p k` is nonzero this is the
distributivity of `log` over the product; when some `p k = 0` both sides vanish (the product is
`0`, and on the right each summand carries the vanishing product factor; the convention
`Real.log 0 = 0` keeps the `k`-summand `0 * 0 = 0`). -/
theorem negMulLog_prod_eq_sum {n : ℕ} (p : Fin n → ℝ) :
    Real.negMulLog (∏ k, p k) = ∑ k, (∏ j, p j) * (-Real.log (p k)) := by
  by_cases hzero : ∃ k, p k = 0
  · obtain ⟨k₀, hk₀⟩ := hzero
    have hprod : ∏ j, p j = 0 := Finset.prod_eq_zero (Finset.mem_univ k₀) hk₀
    rw [hprod, Real.negMulLog_zero]
    refine (Finset.sum_eq_zero ?_).symm
    intro k _
    rw [zero_mul]
  · have hne : ∀ k, p k ≠ 0 := fun k hk => hzero ⟨k, hk⟩
    have hlog : Real.log (∏ k, p k) = ∑ k, Real.log (p k) :=
      Real.log_prod (fun x _ => hne x)
    change -(∏ k, p k) * Real.log (∏ k, p k) = ∑ k, (∏ j, p j) * -Real.log (p k)
    rw [hlog, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ### N4a.1 — the depth-`n` join cell mass -/

variable (ν : Measure α₀) [IsProbabilityMeasure ν]

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [IsProbabilityMeasure ν] in
/-- The depth-`n` join cell of the coordinate partition at `f : Fin n → α₀` is the cylinder
`{x | ∀ k : Fin n, x ↑k = f k}`: the cell at coordinate `k` pulled back along `shiftMap^[k]` is
`{x | x ↑k = f k}` (because `(shiftMap^[k] x) 0 = x k`). -/
theorem ksJoinCells_coordPartition_eq (n : ℕ) (f : Fin n → α₀) :
    ksJoinCells (coordPartition (bern ν)).cells (shiftMap (α₀ := α₀)) n f
      = {x : Shift α₀ | ∀ k : Fin n, x (k : ℕ) = f k} := by
  rw [ksJoinCells_apply]
  ext x
  simp only [Set.mem_iInter, Set.mem_preimage, coordPartition, Set.mem_setOf_eq]
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · have := h k
    rwa [shiftMap_iterate_apply, Nat.zero_add] at this
  · rw [shiftMap_iterate_apply, Nat.zero_add]
    exact h k

omit [Fintype α₀] [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [MeasurableSpace α₀]
  [MeasurableSingletonClass α₀] in
/-- The cylinder `{x | ∀ k : Fin n, x ↑k = f k}` is the measurable box `Set.pi ↑(Finset.range n) t`
with `t i = {f ⟨i, hi⟩}` for `i < n` (and `Set.univ` otherwise). -/
theorem cylinder_eq_pi (n : ℕ) (f : Fin n → α₀) :
    {x : Shift α₀ | ∀ k : Fin n, x (k : ℕ) = f k}
      = Set.pi (↑(Finset.range n))
          (fun i => if hi : i < n then {f ⟨i, hi⟩} else Set.univ) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
  refine ⟨fun h i hi => ?_, fun h k => ?_⟩
  · rw [dif_pos hi]
    exact h ⟨i, hi⟩
  · have := h (k : ℕ) k.2
    rw [dif_pos k.2] at this
    simpa using this

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] in
/-- **N4a.1 (cell mass).** The `bern ν`-mass of the depth-`n` join cell at `f : Fin n → α₀` is the
product `∏ k, ν {f k}` of single-symbol masses (`Measure.infinitePi_pi` on the cylinder box). -/
theorem bern_ksJoinCells_eq (n : ℕ) (f : Fin n → α₀) :
    bern ν (ksJoinCells (coordPartition (bern ν)).cells (shiftMap (α₀ := α₀)) n f)
      = ∏ k : Fin n, ν {f k} := by
  rw [ksJoinCells_coordPartition_eq, cylinder_eq_pi, bern,
    Measure.infinitePi_pi (μ := fun _ : ℕ => ν) ?_]
  · -- The product over `Finset.range n` of `ν (box i)` equals `∏ k : Fin n, ν {f k}`.
    rw [Finset.prod_range fun i => ν (if hi : i < n then {f ⟨i, hi⟩} else Set.univ)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [dif_pos k.2]
  · -- Measurability of the box sets.
    intro i _
    by_cases hi : i < n
    · rw [dif_pos hi]; exact measurableSet_singleton _
    · rw [dif_neg hi]; exact MeasurableSet.univ

/-! ### N4a.2 — the per-`n` entropy is `n * Hnu ν` -/

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] in
/-- The single-symbol masses sum to `1`: `∑ a, (ν {a}).toReal = 1`. -/
theorem sum_measureReal_singleton_eq_one :
    ∑ a : α₀, (ν {a}).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top ν {a})]
  rw [MeasureTheory.sum_measure_singleton]
  simp

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] in
/-- **N4a.2 (per-`n` entropy).** The iterated-join entropy of the coordinate partition at depth `n`
is `n * Hnu ν`. -/
theorem ksEntropySeq_coordPartition_bern_eq (n : ℕ) :
    ksEntropySeq (measurePreserving_shiftMap_bern ν) (coordPartition (bern ν)) n
      = (n : ℝ) * Hnu ν := by
  set p : α₀ → ℝ := fun a => (ν {a}).toReal with hp
  -- Unfold to `∑ f, negMulLog (∏ k, p (f k))`.
  rw [ksEntropySeq, ksJoin_cells, entropy_def]
  have hcell : ∀ f : Fin n → α₀,
      Real.negMulLog
        ((bern ν (ksJoinCells (coordPartition (bern ν)).cells (shiftMap (α₀ := α₀)) n f)).toReal)
        = Real.negMulLog (∏ k, p (f k)) := by
    intro f
    rw [bern_ksJoinCells_eq, ENNReal.toReal_prod]
  simp_rw [hcell]
  -- Factorize each `negMulLog` term across coordinates.
  simp_rw [negMulLog_prod_eq_sum]
  -- Swap the order: sum over `f` then `k`  →  sum over `k` then `f`.
  rw [Finset.sum_comm]
  -- For each fixed `k`, the inner sum over `f` is `Hnu ν`.
  have hinner : ∀ k : Fin n,
      ∑ f : Fin n → α₀, (∏ j, p (f j)) * (-Real.log (p (f k))) = Hnu ν := by
    intro k
    classical
    -- The per-coordinate factor: `g k = negMulLog ∘ p`, `g j = p` for `j ≠ k`.
    set g : Fin n → α₀ → ℝ :=
      fun j a => if j = k then Real.negMulLog (p a) else p a with hg
    -- Rewrite each summand as a product `∏ j, g j (f j)`.
    have hrw : ∀ f : Fin n → α₀,
        (∏ j, p (f j)) * (-Real.log (p (f k))) = ∏ j, g j (f j) := by
      intro f
      -- Split the `k`-factor off both products.
      rw [← Finset.mul_prod_erase Finset.univ (fun j => g j (f j)) (Finset.mem_univ k),
        ← Finset.mul_prod_erase Finset.univ (fun j => p (f j)) (Finset.mem_univ k)]
      have hgk : g k (f k) = Real.negMulLog (p (f k)) := by rw [hg]; simp
      have hgerase : ∏ j ∈ Finset.univ.erase k, g j (f j)
          = ∏ j ∈ Finset.univ.erase k, p (f j) := by
        refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [hg]; simp [Finset.ne_of_mem_erase hj]
      rw [hgk, hgerase, Real.negMulLog_eq_neg]
      ring
    simp_rw [hrw]
    -- Swap sum over `f : Fin n → α₀` and product over coordinates:
    -- `∑ f, ∏ j, g j (f j) = ∏ j, ∑ a, g j a`.
    have hswap : ∑ f : Fin n → α₀, ∏ j, g j (f j) = ∏ j, ∑ a, g j a := by
      rw [← Fintype.piFinset_univ (α := Fin n) (β := fun _ => α₀)]
      exact Finset.sum_prod_piFinset Finset.univ g
    rw [hswap]
    -- `∏ j, ∑ a, g j a = ∏ j, (if j = k then Hnu ν else 1) = Hnu ν`.
    have hsumg : ∀ j : Fin n, ∑ a, g j a = if j = k then Hnu ν else 1 := by
      intro j
      rw [hg]
      by_cases hjk : j = k
      · simp only [hjk, if_true]
        rw [Hnu]
      · simp only [hjk, if_false]
        exact sum_measureReal_singleton_eq_one ν
    rw [Finset.prod_congr rfl (fun j _ => hsumg j), Finset.prod_ite_eq' Finset.univ k]
    simp
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### N4a — the headline partition identity -/

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] in
/-- **N4a (partition entropy).** The Kolmogorov–Sinai entropy of the coordinate partition for the
Bernoulli measure `bern ν` equals the single-symbol Shannon entropy `Hnu ν`. -/
theorem ksEntropyPartition_coordPartition_bern_eq :
    ksEntropyPartition (measurePreserving_shiftMap_bern ν) (coordPartition (bern ν)) = Hnu ν := by
  -- The averaged sequence is eventually constant `Hnu ν`; the Fekete limit is `Hnu ν`.
  have hconst : Tendsto
      (fun n => ksEntropySeq (measurePreserving_shiftMap_bern ν) (coordPartition (bern ν)) n / n)
      atTop (𝓝 (Hnu ν)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [ksEntropySeq_coordPartition_bern_eq, mul_comm, mul_div_assoc, div_self hn0, mul_one]
  exact tendsto_nhds_unique (tendsto_ksEntropySeq _ _) hconst

/-! ### N4a — the system entropy identity -/

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] in
/-- **N4a (system entropy).** For the Bernoulli shift, the Kolmogorov–Sinai entropy of the system
equals the single-symbol Shannon entropy `Hnu ν`.

The coordinate partition is a generator (`coordPartition_isGenerating`), so the Kolmogorov–Sinai
generator theorem (`ksEntropy_eq_ksEntropyPartition_of_generating`, on the `Fin`-reindexed
partition) identifies `ksEntropy` with the coordinate-partition entropy, which the partition
identity ties to `Hnu ν`. No ergodicity is needed: the generator reduction is unconditional (it
consumes only the generating property and the standard-Borel structure). -/
theorem ksEntropy_bern_eq :
    (Oseledets.Entropy.ksEntropy (measurePreserving_shiftMap_bern ν)).toReal = Hnu ν := by
  -- The generator theorem on the `Fin`-reindexed coordinate partition.
  have hgenFin : IsGenerating (bern ν) (shiftMap (α₀ := α₀)) (coordPartitionFin (bern ν)) := by
    unfold IsGenerating
    rw [generatedSigmaAlgebra_coordPartitionFin_eq]
    exact coordPartition_isGenerating (measurePreserving_shiftMap_bern ν)
  have hred := ksEntropy_eq_ksEntropyPartition_of_generating (measurePreserving_shiftMap_bern ν)
    (coordPartitionFin (bern ν)) hgenFin
  rw [hred, EReal.toReal_coe,
    ksEntropyPartition_coordPartitionFin_eq (measurePreserving_shiftMap_bern ν),
    ksEntropyPartition_coordPartition_bern_eq]

end Oseledets.Multifractal
