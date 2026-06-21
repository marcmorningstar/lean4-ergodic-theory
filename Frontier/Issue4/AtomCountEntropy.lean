/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.KSEntropyBounds

/-!
# Partition entropy bounded by the growth rate of the non-empty atom count

This file bounds the dynamical (Kolmogorov–Sinai) partition entropy `h(α, T)` of a
measure-preserving transformation `T` relative to a finite measurable partition `α = P` by the
**exponential growth rate of the number of non-empty atoms** of the refined partition
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`. Concretely,

`h(α, T) ≤ limsupₙ (1 / n) · log (#{non-empty atoms of ⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P}).`

This is the *entropy-bookkeeping half* of the Margulis–Ruelle inequality (Le Maître's notes, the
Mañé proof in Contractor's REU notes): the geometric content of that inequality is to count how
many atoms of a small partition survive under `T^[n]`, and this file packages the abstract step
that turns such an atom count into a bound on `h(α, T)`. It uses only the present entropy API:

* the Jensen bound `entropy_le_log_card` (`Oseledets.Entropy.Partition`), which gives
  `H(α) ≤ log #α`, here strengthened to count only the non-empty cells (the empty ones, of measure
  zero, contribute `negMulLog 0 = 0` to the entropy), and
* the Fekete limit `ksEntropyPartition = limₙ (1 / n) · H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P)`
  (`Oseledets.Entropy.KSEntropy`).

Combining `H(⋁ₖ₌₀ⁿ⁻¹) ≤ log (#non-empty atoms)` with the convergence of the averaged sequence and
passing to the `limsup` gives the displayed bound.

## Main definitions

* `Oseledets.Entropy.atomCount`: the number of non-empty atoms of the flat `n`-fold join
  `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`, as a `ℕ` (the cardinality of the `Finset` of indices `f : Fin n → ι` whose
  cell is non-empty).

## Main results

* `Oseledets.Entropy.entropy_le_log_card_filter`: a Jensen entropy bound counting only the cells
  outside of which the family is `μ`-null.
* `Oseledets.Entropy.entropy_le_log_atomCount`: the single-`n` bound
  `H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P) ≤ log (atomCount …)`.
* `Oseledets.Entropy.ksEntropyPartition_le_limsup_log_atomCount`: the dynamical bound
  `h(α, T) ≤ limsupₙ (1 / n) · log (atomCount …)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
-/

open MeasureTheory Function Filter Topology
open scoped Classical

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- **Jensen entropy bound counting only the supported cells.** If the cell measures of a finite
family `s : ι → Set α` sum to `1` and `s i` is `μ`-null for every index outside a non-empty
`Finset S`, then the Shannon entropy is bounded by `log #S`. This sharpens `entropy_le_log_card`:
cells of measure zero contribute `negMulLog 0 = 0` to the entropy, so only the supported cells
count. The proof is Jensen's inequality for the concave `negMulLog` with equal weights `(#S)⁻¹`
over `S`. -/
lemma entropy_le_log_card_filter [Fintype ι] (μ : Measure α) (s : ι → Set α) (S : Finset ι)
    (hS : S.Nonempty) (hnull : ∀ i ∉ S, μ (s i) = 0)
    (hsum : ∑ i, (μ (s i)).toReal = 1) :
    entropy μ s ≤ Real.log S.card := by
  -- Cells outside `S` are null, hence their `toReal`-measure is `0`.
  have hp_zero : ∀ i ∉ S, (μ (s i)).toReal = 0 := fun i hi => by
    rw [hnull i hi, ENNReal.toReal_zero]
  -- The entropy and the cell-measure sum localize to `S`: the omitted terms are `negMulLog 0 = 0`
  -- and `0` respectively.
  have hH : entropy μ s = ∑ i ∈ S, Real.negMulLog (μ (s i)).toReal := by
    rw [entropy_def]
    refine (Finset.sum_subset S.subset_univ fun i _ hi => ?_).symm
    rw [hp_zero i hi, Real.negMulLog_zero]
  have hsumS : ∑ i ∈ S, (μ (s i)).toReal = 1 := by
    rw [← hsum]
    exact Finset.sum_subset S.subset_univ fun i _ hi => hp_zero i hi
  -- Cardinality data for the Jensen weights.
  set k : ℝ := (S.card : ℝ) with hk
  have hk_pos : 0 < k := by rw [hk]; exact_mod_cast Finset.card_pos.mpr hS
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  -- Jensen for the concave `negMulLog` over `Set.Ici 0` with equal weights `k⁻¹`.
  have hjensen :
      (∑ i ∈ S, k⁻¹ • Real.negMulLog (μ (s i)).toReal)
        ≤ Real.negMulLog (∑ i ∈ S, k⁻¹ • (μ (s i)).toReal) := by
    refine Real.concaveOn_negMulLog.le_map_sum (fun i _ => le_of_lt (inv_pos.mpr hk_pos)) ?_
      (fun i _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg)
    rw [Finset.sum_const, nsmul_eq_mul, ← hk, mul_inv_cancel₀ hk_ne]
  -- Simplify both sides of the Jensen inequality.
  have hLHS : (∑ i ∈ S, k⁻¹ • Real.negMulLog (μ (s i)).toReal) = k⁻¹ * entropy μ s := by
    rw [hH, Finset.mul_sum]; simp only [smul_eq_mul]
  have harg : (∑ i ∈ S, k⁻¹ • (μ (s i)).toReal) = k⁻¹ := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsumS, mul_one]
  have hRHS : Real.negMulLog (∑ i ∈ S, k⁻¹ • (μ (s i)).toReal) = k⁻¹ * Real.log k := by
    rw [harg, Real.negMulLog, Real.log_inv]; ring
  rw [hLHS, hRHS] at hjensen
  -- Cancel the positive factor `k⁻¹`.
  have hcancel := le_of_mul_le_mul_left hjensen (inv_pos.mpr hk_pos)
  rwa [hk] at hcancel

/-- The **non-empty atom count** of the flat `n`-fold join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`: the number of indices
`f : Fin n → ι` whose atom `⋂ₖ T⁻ᵏ (P_{f k})` is non-empty, as a natural number. This is the
combinatorial quantity whose exponential growth rate bounds the dynamical partition entropy. -/
noncomputable def atomCount [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin n → ι => ((ksJoin hT P n).cells f).Nonempty).card

/-- The non-empty atom count is positive: the cells cover the whole (probability) space, so at
least one of them is non-empty. -/
lemma atomCount_pos [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    0 < atomCount hT P n := by
  rw [atomCount, Finset.card_pos, Finset.filter_nonempty_iff]
  -- The whole space is non-empty (its measure is `1 ≠ 0`) and is covered by the cells, so the cell
  -- containing any point is a non-empty atom.
  have huniv_ne : μ (Set.univ : Set α) ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  obtain ⟨x, -⟩ : (Set.univ : Set α).Nonempty := nonempty_of_measure_ne_zero huniv_ne
  have hx : x ∈ ⋃ f, (ksJoin hT P n).cells f := (ksJoin hT P n).cover ▸ Set.mem_univ x
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
  exact ⟨f, Finset.mem_univ f, ⟨x, hf⟩⟩

/-- **Single-`n` atom-count bound.** The Shannon entropy of the flat `n`-fold join
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is at most the logarithm of its non-empty atom count. The empty atoms have measure
zero, so `entropy_le_log_card_filter` (counting only the non-empty cells) applies, with the cell
measures summing to `1` because `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is a partition of a probability space. -/
lemma entropy_le_log_atomCount [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P n ≤ Real.log (atomCount hT P n) := by
  rw [ksEntropySeq, atomCount]
  refine entropy_le_log_card_filter μ (ksJoin hT P n).cells _ ?_ ?_
    (ksJoin hT P n).sum_toReal_measure_eq_one
  · -- The filter is non-empty: some atom is non-empty (probability mass `1` is somewhere).
    have := atomCount_pos hT P n
    rwa [atomCount, Finset.card_pos] at this
  · -- An atom outside the filter is empty, hence null.
    intro f hf
    rw [Finset.mem_filter, not_and] at hf
    have hempty : ¬ ((ksJoin hT P n).cells f).Nonempty := hf (Finset.mem_univ f)
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, measure_empty]

/-- **Dynamical atom-count entropy bound.** The Kolmogorov–Sinai partition entropy `h(α, T)` is
bounded by the exponential growth rate of the number of non-empty atoms of the refined partition
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`:

`h(α, T) ≤ limsupₙ (1 / n) · log (atomCount …).`

The averaged iterated-join entropies `(1 / n) · H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P)` converge to `h(α, T)`
(`tendsto_ksEntropySeq`), so `h(α, T)` is their `limsup`; the per-`n` bound
`H(⋁ₖ₌₀ⁿ⁻¹) ≤ log (atomCount …)` (`entropy_le_log_atomCount`) divides through by `n` and is then
compared `limsup`-to-`limsup`. The required boundedness is supplied by the convergence of the
averaged entropies (giving coboundedness of the left side) and by the uniform bound
`(1 / n) · log (atomCount …) ≤ log #ι` — the atom count never exceeds the total number of indices
`#(Fin n → ι) = (#ι)ⁿ`. -/
theorem ksEntropyPartition_le_limsup_log_atomCount [Fintype ι] [Nonempty ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) :
    ksEntropyPartition hT P
      ≤ limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (atomCount hT P n)) atTop := by
  -- The averaged entropy sequence and the averaged log-atom-count.
  set u : ℕ → ℝ := fun n => ksEntropySeq hT P n / n with hu
  set v : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (atomCount hT P n) with hv
  -- `h(α, T)` is the limit, hence the `limsup`, of `u`.
  have htends : Tendsto u atTop (𝓝 (ksEntropyPartition hT P)) := tendsto_ksEntropySeq hT P
  -- Eventually `u n ≤ v n`: divide the single-`n` bound by `n ≥ 1`.
  have hle : u ≤ᶠ[atTop] v := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hu, hv, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (entropy_le_log_atomCount hT P n) (le_of_lt (inv_pos.mpr hn0))
  -- `v` is bounded above by `log #ι`, uniformly in `n` (so its `limsup` is genuine).
  have hv_bdd : IsBoundedUnder (· ≤ ·) atTop v := by
    refine isBoundedUnder_of_eventually_le (a := Real.log (Fintype.card ι)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    -- `atomCount ≤ #(Fin n → ι) = (#ι)ⁿ`, so `log (atomCount) ≤ n · log #ι`.
    have hcard_le : atomCount hT P n ≤ Fintype.card (Fin n → ι) := by
      rw [atomCount]
      exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])
    have hac_pos : 0 < atomCount hT P n := atomCount_pos hT P n
    have hlog_le : Real.log (atomCount hT P n) ≤ Real.log (Fintype.card (Fin n → ι)) :=
      Real.log_le_log (by exact_mod_cast hac_pos) (by exact_mod_cast hcard_le)
    have hcard_eq : (Fintype.card (Fin n → ι) : ℝ) = (Fintype.card ι : ℝ) ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hlogpow : Real.log (Fintype.card (Fin n → ι)) = n * Real.log (Fintype.card ι) := by
      rw [hcard_eq, Real.log_pow]
    simp only [hv]
    calc (n : ℝ)⁻¹ * Real.log (atomCount hT P n)
        ≤ (n : ℝ)⁻¹ * (n * Real.log (Fintype.card ι)) := by
          rw [← hlogpow]
          exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt (inv_pos.mpr hn0))
      _ = Real.log (Fintype.card ι) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn0), one_mul]
  -- Compare the two `limsup`s and identify the left one with `h(α, T)`.
  calc ksEntropyPartition hT P = limsup u atTop := htends.limsup_eq.symm
    _ ≤ limsup v atTop := limsup_le_limsup hle htends.isCoboundedUnder_le hv_bdd

end Oseledets.Entropy
