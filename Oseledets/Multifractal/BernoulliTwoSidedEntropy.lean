/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.BernoulliTwoSided
import Oseledets.Multifractal.BernoulliEntropy

/-!
# The two-sided Bernoulli entropy identity (the `hbase` for the W3 flow descent)

This file lifts the one-sided Bernoulli entropy identity
(`Oseledets/Multifractal/BernoulliEntropy.lean`) to the **two-sided (invertible) full shift**
`BiShift α₀ := ℤ → α₀` equipped with the two-sided i.i.d. measure `bernZ ν`
(`Oseledets/Multifractal/BernoulliTwoSided.lean`). The result is the base entropy datum that the
W3 flow-entropy descent consumes.

The combinatorial core is **identical** to the one-sided case: the depth-`n` forward join of the
time-`0` coordinate partition `coordPartitionZ` reads the coordinates `0, 1, …, n-1` (because
`biShiftMap^[k] x` reads coordinate `k`), so its `bernZ ν`-mass factorizes as a product of
single-symbol masses (`bernZ_pi_eq_prod`); the real-analytic identity
`negMulLog_prod_eq_sum` and the sum/product swap `Finset.sum_prod_piFinset` (both reused verbatim
from the one-sided file) collapse the per-`n` join entropy to `n · Hnu ν`, and Fekete's limit
uniqueness gives the partition entropy `Hnu ν`.

The one and only structural difference is that the index type is `ℤ` rather than `ℕ`: the
coordinate-support of the join cell is `{0, 1, …, n-1} ⊆ ℤ`, packaged as
`(Finset.range n).map intOfNatEmb`.

There is deliberately **no generator-theorem step** here: `coordPartitionZ` is *not* one-sided
generating for an invertible shift (it sees only the forward future), so the system-entropy
reduction from the one-sided file does not port. Only the partition-relative identity is established
(that is all the W3 descent needs).

## Main results

* `Oseledets.Multifractal.coordPartitionZFin`
* `Oseledets.Multifractal.ksEntropyPartition_coordPartitionZ_bernZ_eq`
* `Oseledets.Multifractal.ksEntropyPartition_coordPartitionZFin_bernZ_eq`  — the headline `hbase`
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

namespace Oseledets.Multifractal

open Oseledets.Entropy

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-! ### The shift-iterate reads a forward coordinate -/

omit [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀] in
/-- The `k`-th iterate of the two-sided shift advances every (integer) index by `k`:
`biShiftMap^[k] x n = x (n + k)`. -/
theorem biShiftMap_iterate_apply (k : ℕ) (x : BiShift α₀) (n : ℤ) :
    (biShiftMap^[k] x) n = x (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', biShiftMap, ih]
    push_cast
    ring_nf

/-! ### The integer-coordinate support `{0, 1, …, n-1}` -/

/-- The order-embedding `ℕ ↪ ℤ` of nonnegative integers, used to package the coordinate support
`{0, 1, …, n-1} ⊆ ℤ` of a depth-`n` forward join cell as `(Finset.range n).map intOfNatEmb`. -/
def intOfNatEmb : ℕ ↪ ℤ := ⟨fun k => (k : ℤ), fun _ _ h => Int.natCast_inj.mp h⟩

@[simp]
theorem intOfNatEmb_apply (k : ℕ) : intOfNatEmb k = (k : ℤ) := rfl

/-! ### The depth-`n` forward join cell is the integer-coordinate cylinder -/

variable (ν : Measure α₀) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- The depth-`n` forward join cell of `coordPartitionZ` at `f : Fin n → α₀` is the cylinder
`{x | ∀ k : Fin n, x ↑k = f k}` on the (integer) coordinates `0, …, n-1`: the cell at coordinate
`k` pulled back along `biShiftMap^[k]` is `{x | x ↑k = f k}` (because `(biShiftMap^[k] x) 0 = x k`).
-/
theorem ksJoinCells_coordPartitionZ_eq (n : ℕ) (f : Fin n → α₀) :
    ksJoinCells (coordPartitionZ (bernZ ν)).cells (biShiftMap (α₀ := α₀)) n f
      = {x : BiShift α₀ | ∀ k : Fin n, x (k : ℤ) = f k} := by
  rw [ksJoinCells_apply]
  ext x
  simp only [Set.mem_iInter, Set.mem_preimage, coordPartitionZ, Set.mem_setOf_eq]
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · have := h k
    rwa [biShiftMap_iterate_apply, zero_add] at this
  · rw [biShiftMap_iterate_apply, zero_add]
    exact h k

omit [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀] [IsProbabilityMeasure ν] in
/-- The cylinder `{x | ∀ k : Fin n, x ↑k = f k}` is the measurable box
`Set.pi ↑((Finset.range n).map intOfNatEmb) t` with `t i = {f ⟨i.toNat, _⟩}` on the support and
`Set.univ` elsewhere. -/
theorem coordCylinderZ_eq_pi (n : ℕ) (f : Fin n → α₀) :
    {x : BiShift α₀ | ∀ k : Fin n, x (k : ℤ) = f k}
      = Set.pi (↑((Finset.range n).map intOfNatEmb))
          (fun i => if hi : i.toNat < n ∧ 0 ≤ i then {f ⟨i.toNat, hi.1⟩} else Set.univ) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_map, Set.mem_image, Finset.mem_coe,
    Finset.mem_range, intOfNatEmb, Function.Embedding.coeFn_mk]
  refine ⟨fun h i hi => ?_, fun h k => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := hi
    have htoNat : (k : ℤ).toNat = k := Int.toNat_natCast k
    have hcond : (k : ℤ).toNat < n ∧ 0 ≤ (k : ℤ) := ⟨by rw [htoNat]; exact hk, by positivity⟩
    rw [dif_pos hcond]
    have hkeq : (⟨(k : ℤ).toNat, hcond.1⟩ : Fin n) = ⟨k, hk⟩ := by
      ext; exact htoNat
    rw [Set.mem_singleton_iff, hkeq]
    exact h ⟨k, hk⟩
  · have hmem : ∃ a : ℕ, a < n ∧ (a : ℤ) = (k : ℤ) := ⟨(k : ℕ), k.2, rfl⟩
    have hk' := h (k : ℤ) hmem
    have htoNat : ((k : ℕ) : ℤ).toNat = (k : ℕ) := Int.toNat_natCast _
    have hcond : ((k : ℕ) : ℤ).toNat < n ∧ 0 ≤ ((k : ℕ) : ℤ) :=
      ⟨by rw [htoNat]; exact k.2, by positivity⟩
    rw [dif_pos hcond, Set.mem_singleton_iff] at hk'
    rw [hk']
    exact congrArg f (Fin.ext htoNat)

/-! ### N4a.1 — the depth-`n` forward join cell mass -/

/-- **N4a.1 (cell mass).** The `bernZ ν`-mass of the depth-`n` forward join cell at `f : Fin n → α₀`
is the product `∏ k, ν {f k}` of single-symbol masses (`bernZ_pi_eq_prod` on the cylinder box). -/
theorem bernZ_ksJoinCells_eq (n : ℕ) (f : Fin n → α₀) :
    bernZ ν (ksJoinCells (coordPartitionZ (bernZ ν)).cells (biShiftMap (α₀ := α₀)) n f)
      = ∏ k : Fin n, ν {f k} := by
  have hmeas : ∀ i : ℤ, MeasurableSet
      (if hi : i.toNat < n ∧ 0 ≤ i then ({f ⟨i.toNat, hi.1⟩} : Set α₀) else Set.univ) := by
    intro i
    by_cases hi : i.toNat < n ∧ 0 ≤ i
    · rw [dif_pos hi]; exact measurableSet_singleton _
    · rw [dif_neg hi]; exact MeasurableSet.univ
  rw [ksJoinCells_coordPartitionZ_eq, coordCylinderZ_eq_pi, bernZ_pi_eq_prod ν _ _ hmeas,
    Finset.prod_map,
    Finset.prod_range fun i => ν (if hi : (intOfNatEmb i).toNat < n ∧ 0 ≤ intOfNatEmb i
      then ({f ⟨(intOfNatEmb i).toNat, hi.1⟩} : Set α₀) else Set.univ)]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp only [intOfNatEmb, Function.Embedding.coeFn_mk]
  have htoNat : ((k : ℕ) : ℤ).toNat = (k : ℕ) := Int.toNat_natCast _
  have hcond : ((k : ℕ) : ℤ).toNat < n ∧ 0 ≤ ((k : ℕ) : ℤ) :=
    ⟨by rw [htoNat]; exact k.2, by positivity⟩
  rw [dif_pos hcond]
  have hkeq : (⟨((k : ℕ) : ℤ).toNat, hcond.1⟩ : Fin n) = k := Fin.ext htoNat
  rw [hkeq]

/-! ### N4a.2 — the per-`n` entropy is `n * Hnu ν` -/

/-- **N4a.2 (per-`n` entropy).** The iterated-join entropy of the coordinate partition at depth `n`
is `n * Hnu ν`. The combinatorial core is reused verbatim from the one-sided file via
`negMulLog_prod_eq_sum`, `Finset.sum_prod_piFinset`, and `sum_measureReal_singleton_eq_one`. -/
theorem ksEntropySeq_coordPartitionZ_bernZ_eq (n : ℕ) :
    ksEntropySeq (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZ (bernZ ν)) n
      = (n : ℝ) * Hnu ν := by
  set p : α₀ → ℝ := fun a => (ν {a}).toReal with hp
  -- Unfold to `∑ f, negMulLog (∏ k, p (f k))`.
  rw [ksEntropySeq, ksJoin_cells, entropy_def]
  simp only [coe_biShiftEquiv]
  have hcell : ∀ f : Fin n → α₀,
      Real.negMulLog
        ((bernZ ν (ksJoinCells (coordPartitionZ (bernZ ν)).cells
          (biShiftMap (α₀ := α₀)) n f)).toReal)
        = Real.negMulLog (∏ k, p (f k)) := by
    intro f
    rw [bernZ_ksJoinCells_eq, ENNReal.toReal_prod]
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

/-- **N4a (partition entropy, two-sided).** The Kolmogorov–Sinai entropy of the time-`0` coordinate
partition `coordPartitionZ` for the two-sided Bernoulli measure `bernZ ν` equals the single-symbol
Shannon entropy `Hnu ν`. Ported verbatim from the one-sided
`ksEntropyPartition_coordPartition_bern_eq`: the averaged join-entropy sequence is eventually
constant `Hnu ν`, so the Fekete limit is `Hnu ν`. -/
theorem ksEntropyPartition_coordPartitionZ_bernZ_eq :
    ksEntropyPartition (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZ (bernZ ν))
      = Hnu ν := by
  -- The averaged sequence is eventually constant `Hnu ν`; the Fekete limit is `Hnu ν`.
  have hconst : Tendsto
      (fun n => ksEntropySeq (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZ (bernZ ν)) n
        / n) atTop (𝓝 (Hnu ν)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [ksEntropySeq_coordPartitionZ_bernZ_eq, mul_comm, mul_div_assoc, div_self hn0, mul_one]
  exact tendsto_nhds_unique (tendsto_ksEntropySeq _ _) hconst

/-! ### The `Fin`-reindexed coordinate partition and its entropy -/

/-- The two-sided coordinate partition reindexed onto `Fin (card α₀)` via
`(Fintype.equivFin α₀).symm`, mirroring `coordPartitionFin` for the one-sided shift. This is the
canonical `Fin`-indexed presentation consumed by the W3 descent. -/
def coordPartitionZFin (ν : Measure (BiShift α₀)) :
    MeasurePartition ν (Fin (Fintype.card α₀)) where
  cells := fun j => (coordPartitionZ ν).cells ((Fintype.equivFin α₀).symm j)
  measurable := fun j => (coordPartitionZ ν).measurable _
  aedisjoint := fun j k hjk =>
    (coordPartitionZ ν).aedisjoint (fun he => hjk ((Fintype.equivFin α₀).symm.injective he))
  cover := by
    rw [← (coordPartitionZ ν).cover]
    exact (Fintype.equivFin α₀).symm.surjective.iUnion_comp (coordPartitionZ ν).cells

/-- **Reindexing invariance of the two-sided partition-relative entropy.** The reindexed coordinate
partition has the same Kolmogorov–Sinai entropy as the original. Ported from
`ksEntropyPartition_coordPartitionFin_eq`: the iterated-join entropy sequences agree (the cells
coincide up to the index reindexing `Equiv.piCongrRight`), and the Fekete limit is determined by
that sequence. -/
theorem ksEntropyPartition_coordPartitionZFin_eq :
    ksEntropyPartition (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZFin (bernZ ν))
      = ksEntropyPartition (measurePreserving_biShiftEquiv_bernZ ν)
          (coordPartitionZ (bernZ ν)) := by
  -- The two iterated-join entropy sequences coincide.
  have hseq : ksEntropySeq (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZFin (bernZ ν))
      = ksEntropySeq (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZ (bernZ ν)) := by
    funext n
    rw [ksEntropySeq, ksEntropySeq, ksJoin_cells, ksJoin_cells]
    rw [← entropy_reindex (bernZ ν)
      (Equiv.piCongrRight (fun _ : Fin n => (Fintype.equivFin α₀).symm))
      (ksJoinCells (coordPartitionZ (bernZ ν)).cells (⇑(biShiftEquiv (α₀ := α₀))) n)]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    have hcell : ksJoinCells (coordPartitionZFin (bernZ ν)).cells (⇑(biShiftEquiv (α₀ := α₀))) n f
        = ksJoinCells (coordPartitionZ (bernZ ν)).cells (⇑(biShiftEquiv (α₀ := α₀))) n
            (Equiv.piCongrRight (fun _ : Fin n => (Fintype.equivFin α₀).symm) f) := by
      rw [ksJoinCells_apply, ksJoinCells_apply]
      refine Set.iInter_congr (fun k => ?_)
      simp only [Equiv.piCongrRight_apply, Pi.map_apply]
      rfl
    rw [hcell]
  -- The Fekete limit is determined by the entropy sequence (uniqueness of limits).
  have h1 := tendsto_ksEntropySeq (measurePreserving_biShiftEquiv_bernZ ν)
    (coordPartitionZFin (bernZ ν))
  rw [hseq] at h1
  exact tendsto_nhds_unique h1
    (tendsto_ksEntropySeq (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZ (bernZ ν)))

/-- **The headline `hbase`.** The Kolmogorov–Sinai entropy of the `Fin`-reindexed time-`0`
coordinate partition `coordPartitionZFin` for the two-sided Bernoulli measure `bernZ ν` equals the
single-symbol Shannon entropy `Hnu ν`. This is the base entropy datum consumed by the W3
flow-entropy descent. -/
theorem ksEntropyPartition_coordPartitionZFin_bernZ_eq :
    ksEntropyPartition (measurePreserving_biShiftEquiv_bernZ ν) (coordPartitionZFin (bernZ ν))
      = Hnu ν := by
  rw [ksEntropyPartition_coordPartitionZFin_eq ν, ksEntropyPartition_coordPartitionZ_bernZ_eq ν]

end Oseledets.Multifractal
