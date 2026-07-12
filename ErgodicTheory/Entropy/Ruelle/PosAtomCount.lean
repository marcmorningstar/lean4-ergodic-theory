/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Ruelle.AtomCount
import ErgodicTheory.Entropy.Ruelle.Crude

/-!
# Partition entropy bounded by the growth rate of the positive-measure atom count

This file is the **positive-measure twin** of `ErgodicTheory.Entropy.Ruelle.AtomCount` /
`ErgodicTheory.Entropy.Ruelle.Crude`. It replaces the *set-nonempty* atom count of the refined
partition `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` by the **positive-measure atom count** — the number of index families
`f : Fin n → ι` whose cell has `μ`-mass `≠ 0`. Since the entropy-side Jensen bound
`entropy_le_log_card_filter` already discards cells on which `μ` vanishes (they contribute
`negMulLog 0 = 0`), the entire backbone goes through verbatim with the sharper filter predicate:
`μ (cell) ≠ 0` in place of `(cell).Nonempty`.

The point of this refinement is robustness under measure-zero junk: a partition may carry a null
"junk" cell, and every itinerary that visits it has a null atom, so it is *not* counted here. The
positive-measure count is therefore `≤` the nonempty count (`posAtomCount_le_atomCount`), yet still
bounds the entropy, giving a strictly sharper crude Ruelle backbone.

## Main definitions

* `ErgodicTheory.Entropy.posAtomCount`: the number of positive-measure atoms of the flat `n`-fold
  join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` (the cardinality of the `Finset` of indices whose cell has `μ`-mass `≠ 0`).

## Main results

* `ErgodicTheory.Entropy.posAtomCount_le_atomCount`: positive measure implies non-empty.
* `ErgodicTheory.Entropy.entropy_le_log_posAtomCount`: the single-`n` bound
  `H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P) ≤ log (posAtomCount …)`.
* `ErgodicTheory.Entropy.ksEntropyPartition_le_limsup_log_posAtomCount`: the dynamical bound
  `h(α, T) ≤ limsupₙ (1 / n) · log (posAtomCount …)`.
* `ErgodicTheory.Entropy.ksEntropyPartition_le_of_posAtomCount_growth`: the arithmetic backbone,
  `posAtomCount ≤ C · exp(n R)` ⇒ `h(P, T) ≤ R`.
* `ErgodicTheory.Entropy.ksEntropyPartition_le_of_posAtomCount_growth_poly`: the `ε`-rate form,
  absorbing polynomial factors, `∀ ε>0, posAtomCount ≤ exp(n(R+ε))` ⇒ `h(P, T) ≤ R`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

variable {α : Type*} [MeasurableSpace α]

open Classical in
/-- The **positive-measure atom count** of the flat `n`-fold join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`: the number of
index families `f : Fin n → ι` whose atom `⋂ₖ T⁻ᵏ (P_{f k})` has `μ`-mass `≠ 0`, as a natural
number. Cells of measure zero (including a possible junk cell) are not counted; this sharpens
`atomCount`, which counts merely non-empty cells. -/
noncomputable def posAtomCount {ι : Type*} [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin n → ι => μ ((ksJoin hT P n).cells f) ≠ 0).card

/-- The positive-measure atom count is at most the non-empty atom count: a cell of positive measure
is non-empty (the empty set is null), so the positive-measure filter is contained in the non-empty
filter. -/
lemma posAtomCount_le_atomCount {ι : Type*} [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    posAtomCount hT P n ≤ atomCount hT P n := by
  classical
  rw [posAtomCount, atomCount]
  refine Finset.card_le_card fun f hf => ?_
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨hf.1, nonempty_of_measure_ne_zero hf.2⟩

/-- The positive-measure atom count is positive: the cell measures sum to `1`, so they cannot all
vanish, and at least one cell has `μ`-mass `≠ 0`. -/
lemma posAtomCount_pos {ι : Type*} [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    0 < posAtomCount hT P n := by
  classical
  rw [posAtomCount, Finset.card_pos, Finset.filter_nonempty_iff]
  by_contra hc
  have hc' : ∀ a, μ ((ksJoin hT P n).cells a) = 0 :=
    fun a => not_not.mp fun h => hc ⟨a, Finset.mem_univ a, h⟩
  have hsum := (ksJoin hT P n).sum_toReal_measure_eq_one
  rw [Finset.sum_eq_zero fun f _ => by rw [hc' f, ENNReal.toReal_zero]] at hsum
  exact one_ne_zero hsum.symm

/-- **Single-`n` positive-measure atom-count bound.** The Shannon entropy of the flat `n`-fold join
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is at most the logarithm of its positive-measure atom count. The remaining cells
have measure zero, so `entropy_le_log_card_filter` — whose filter predicate is exactly `μ ≠ 0` —
applies directly, the cell measures summing to `1` over a probability space. -/
lemma entropy_le_log_posAtomCount {ι : Type*} [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P n ≤ Real.log (posAtomCount hT P n) := by
  classical
  rw [ksEntropySeq, posAtomCount]
  refine entropy_le_log_card_filter μ (ksJoin hT P n).cells _ ?_ ?_
    (ksJoin hT P n).sum_toReal_measure_eq_one
  · have := posAtomCount_pos hT P n
    rwa [posAtomCount, Finset.card_pos] at this
  · intro f hf
    rw [Finset.mem_filter, not_and] at hf
    exact not_not.mp (hf (Finset.mem_univ f))

/-- **Dynamical positive-measure atom-count entropy bound.** The Kolmogorov–Sinai partition entropy
`h(α, T)` is bounded by the exponential growth rate of the number of positive-measure atoms of the
refined partition `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`:

`h(α, T) ≤ limsupₙ (1 / n) · log (posAtomCount …).`

The proof mirrors `ksEntropyPartition_le_limsup_log_atomCount`: the averaged join entropies converge
to `h(α, T)`, the per-`n` bound `entropy_le_log_posAtomCount` divides through by `n`, and the count
is bounded by `#(Fin n → ι) = (#ι)ⁿ` to supply the boundedness needed for the `limsup`
comparison. -/
theorem ksEntropyPartition_le_limsup_log_posAtomCount {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) :
    ksEntropyPartition hT P
      ≤ limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (posAtomCount hT P n)) atTop := by
  classical
  set u : ℕ → ℝ := fun n => ksEntropySeq hT P n / n with hu
  set v : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (posAtomCount hT P n) with hv
  have htends : Tendsto u atTop (𝓝 (ksEntropyPartition hT P)) := tendsto_ksEntropySeq hT P
  have hle : u ≤ᶠ[atTop] v := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hu, hv, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (entropy_le_log_posAtomCount hT P n)
      (le_of_lt (inv_pos.mpr hn0))
  have hv_bdd : IsBoundedUnder (· ≤ ·) atTop v := by
    refine isBoundedUnder_of_eventually_le (a := Real.log (Fintype.card ι)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hcard_le : posAtomCount hT P n ≤ Fintype.card (Fin n → ι) := by
      rw [posAtomCount]
      exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])
    have hac_pos : 0 < posAtomCount hT P n := posAtomCount_pos hT P n
    have hlog_le : Real.log (posAtomCount hT P n) ≤ Real.log (Fintype.card (Fin n → ι)) :=
      Real.log_le_log (by exact_mod_cast hac_pos) (by exact_mod_cast hcard_le)
    have hcard_eq : (Fintype.card (Fin n → ι) : ℝ) = (Fintype.card ι : ℝ) ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hlogpow : Real.log (Fintype.card (Fin n → ι)) = n * Real.log (Fintype.card ι) := by
      rw [hcard_eq, Real.log_pow]
    simp only [hv]
    calc (n : ℝ)⁻¹ * Real.log (posAtomCount hT P n)
        ≤ (n : ℝ)⁻¹ * (n * Real.log (Fintype.card ι)) := by
          rw [← hlogpow]
          exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt (inv_pos.mpr hn0))
      _ = Real.log (Fintype.card ι) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn0), one_mul]
  calc ksEntropyPartition hT P = limsup u atTop := htends.limsup_eq.symm
    _ ≤ limsup v atTop := limsup_le_limsup hle htends.isCoboundedUnder_le hv_bdd

/-- **Arithmetic backbone of the crude Ruelle bound (positive-measure twin).**

If the number of positive-measure atoms of the refined partition `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is eventually
bounded by `C · exp(n · R)` for some `C ≥ 1` and rate `R`, then the Kolmogorov–Sinai partition
entropy is bounded by the rate:

`h(P, T) ≤ R`.

This is the positive-measure analogue of `ksEntropyPartition_le_of_atomCount_growth`, obtained by
feeding `ksEntropyPartition_le_limsup_log_posAtomCount` into the same
`(1/n) · log (C · exp(n R)) = (log C)/n + R → R` comparison. -/
theorem ksEntropyPartition_le_of_posAtomCount_growth {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {C R : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ᶠ n : ℕ in atTop, (posAtomCount hT P n : ℝ) ≤ C * Real.exp (n * R)) :
    ksEntropyPartition hT P ≤ R := by
  set v : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (posAtomCount hT P n) with hv
  set w : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log C + R with hw
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hvw : v ≤ᶠ[atTop] w := by
    filter_upwards [hgrow, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hac_pos : 0 < posAtomCount hT P n := posAtomCount_pos hT P n
    have hac0 : (0 : ℝ) < posAtomCount hT P n := by exact_mod_cast hac_pos
    have hlog_le : Real.log (posAtomCount hT P n) ≤ Real.log C + n * R := by
      calc Real.log (posAtomCount hT P n)
          ≤ Real.log (C * Real.exp (n * R)) := Real.log_le_log hac0 hn
        _ = Real.log C + n * R := by
            rw [Real.log_mul hC0.ne' (Real.exp_ne_zero _), Real.log_exp]
    have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt (inv_pos.mpr hn0))
    have hsimp : (n : ℝ)⁻¹ * (Real.log C + n * R) = (n : ℝ)⁻¹ * Real.log C + R := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hn0.ne', one_mul]
    simp only [hv, hw]
    rw [hsimp] at hmul
    exact hmul
  have hw_tendsto : Tendsto w atTop (𝓝 R) := by
    have h0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log C) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := Real.log C)).div_atTop tendsto_natCast_atTop_atTop
      simpa only [div_eq_inv_mul] using this.congr fun n => by ring
    simpa only [hw, zero_add] using h0.add_const R
  have hvcob : IsCoboundedUnder (· ≤ ·) atTop v :=
    isCoboundedUnder_le_of_le atTop fun n => by
      simp only [hv]
      exact mul_nonneg (by positivity)
        (Real.log_nonneg (by exact_mod_cast (posAtomCount_pos hT P n)))
  calc ksEntropyPartition hT P
      ≤ limsup v atTop := ksEntropyPartition_le_limsup_log_posAtomCount hT P
    _ ≤ limsup w atTop := limsup_le_limsup hvw hvcob hw_tendsto.isBoundedUnder_le
    _ = R := hw_tendsto.limsup_eq

/-- **`ε`-rate positive-measure atom-count entropy bound.**

If for every `ε > 0` the positive-measure atom count of `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is eventually bounded by
`exp(n · (R + ε))`, then the Kolmogorov–Sinai partition entropy is bounded by `R`:

`h(P, T) ≤ R`.

Since `exp(n·(R+ε))` absorbs any polynomial factor `poly(n) · exp(nR)` eventually, this is the form
that consumes a bare sub-exponential growth rate. It applies the backbone
`ksEntropyPartition_le_of_posAtomCount_growth` at rate `R + ε` (with `C = 1`) to get
`h ≤ R + ε` for all `ε > 0`, then lets `ε → 0`. -/
theorem ksEntropyPartition_le_of_posAtomCount_growth_poly {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {R : ℝ}
    (hgrow : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (posAtomCount hT P n : ℝ) ≤ Real.exp (n * (R + ε))) :
    ksEntropyPartition hT P ≤ R := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine ksEntropyPartition_le_of_posAtomCount_growth hT P (C := 1) le_rfl ?_
  filter_upwards [hgrow ε hε] with n hn
  rwa [one_mul]

end ErgodicTheory.Entropy
