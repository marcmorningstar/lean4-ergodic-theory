/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Join

/-!
# Subadditivity of Shannon entropy under joins

This file continues the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`ErgodicTheory.Entropy.Partition` and `ErgodicTheory.Entropy.Join`. It establishes the **subadditivity**
of Shannon entropy under the join of two finite measurable partitions,
`H(α ∨ β) ≤ H(α) + H(β)`, the analytic heart of the Fekete argument that turns the sequence
`n ↦ H(⋁ₖ₌₀ⁿ⁻¹ Tᵏα)` into the well-defined Kolmogorov–Sinai entropy `h(T, α)`.

Following the Le Maître notes on the Kolmogorov–Sinai theorem, the proof rests on the **discrete
Gibbs inequality** (relative entropy is nonnegative): for a probability vector `p` and a
sub-probability vector `q` with `q i ≠ 0` wherever `p i ≠ 0`,
`∑ᵢ negMulLog (p i) ≤ - ∑ᵢ p i · log (q i)`. Applying this with `p (i,j) = μ(Aᵢ ∩ Bⱼ)` and the
product `q (i,j) = μ(Aᵢ) · μ(Bⱼ)` and using the marginal identities `μ(Aᵢ) = ∑ⱼ μ(Aᵢ ∩ Bⱼ)` and
`μ(Bⱼ) = ∑ᵢ μ(Aᵢ ∩ Bⱼ)` reorganizes the right-hand side into `H(α) + H(β)`.

The scalar Gibbs inequality itself is proved term by term from `Real.log_le_sub_one_of_pos`,
`log x ≤ x - 1`: where `p i > 0` we have `q i > 0` and
`p i · (log (q i) - log (p i)) = p i · log (q i / p i) ≤ q i - p i`, and summing the bound over
`i` gives `∑ q - ∑ p ≤ 1 - 1 = 0`.

## Main results

* `ErgodicTheory.Entropy.MeasurePartition.measure_eq_sum_inter`: the marginal identity
  `μ A = ∑ j, μ (A ∩ Q.cells j)` of a measurable set against a partition.
* `ErgodicTheory.Entropy.sum_negMulLog_le`: the discrete Gibbs inequality for finite probability and
  sub-probability vectors that are mutually absolutely continuous on the support of `p`.
* `ErgodicTheory.Entropy.entropy_join_le`: subadditivity of Shannon entropy,
  `H(α ∨ β) ≤ H(α) + H(β)`, for two finite measurable partitions of a probability space.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

/-- **Marginal identity.** For a measurable set `A` and a finite measurable partition `Q` of a
measure space, the measure of `A` is the sum of the measures of its intersections with the cells
of `Q`. The sets `A ∩ Q.cells j` cover `A` (since the cells cover the space), are pairwise
almost-everywhere disjoint (each is contained in the corresponding cell), and are null-measurable,
so finite additivity of `μ` applies. -/
lemma MeasurePartition.measure_eq_sum_inter [Fintype κ] {μ : Measure α}
    (Q : MeasurePartition μ κ) {A : Set α} (hA : MeasurableSet A) :
    μ A = ∑ j, μ (A ∩ Q.cells j) := by
  have hcover : A = ⋃ j ∈ (Finset.univ : Finset κ), A ∩ Q.cells j := by
    simp only [Finset.mem_univ, Set.iUnion_true, ← Set.inter_iUnion, Q.cover, Set.inter_univ]
  have hadd : μ (⋃ j ∈ (Finset.univ : Finset κ), A ∩ Q.cells j) = ∑ j, μ (A ∩ Q.cells j) :=
    measure_biUnion_finset₀
      (fun i _ j _ hij =>
        AEDisjoint.mono (Q.aedisjoint hij) Set.inter_subset_right Set.inter_subset_right)
      (fun j _ => (hA.inter (Q.measurable j)).nullMeasurableSet)
  rw [← hadd, ← hcover]

/-- **Discrete Gibbs inequality** (nonnegativity of relative entropy). Let `p` be a probability
vector and `q` a sub-probability vector on a finite index type, with `q i ≠ 0` wherever
`p i ≠ 0`. Then `∑ᵢ negMulLog (p i) ≤ - ∑ᵢ p i · log (q i)`. Equivalently
`∑ᵢ p i · log (p i / q i) ≥ 0`. The proof bounds each term using `log x ≤ x - 1`: where
`p i > 0`, `p i · (log (q i) - log (p i)) ≤ q i - p i`; summing gives `∑ q - ∑ p ≤ 0`. -/
lemma sum_negMulLog_le {ω : Type*} [Fintype ω] (p q : ω → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i ≤ 1)
    (hac : ∀ i, p i ≠ 0 → q i ≠ 0) :
    ∑ i, Real.negMulLog (p i) ≤ - ∑ i, p i * Real.log (q i) := by
  -- It suffices to bound `∑ (negMulLog (p i) + p i · log (q i))` by `0`.
  have hkey : ∀ i, Real.negMulLog (p i) + p i * Real.log (q i) ≤ q i - p i := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · -- `p i = 0`: the left-hand side vanishes and `q i - 0 ≥ 0`.
      simp only [← hpi, Real.negMulLog_zero, zero_mul, add_zero, sub_zero]
      exact hq i
    · -- `p i > 0`, hence `q i > 0`; use `log (q i / p i) ≤ q i / p i - 1`.
      have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm (hac i (ne_of_gt hpi)))
      have hdiv : 0 < q i / p i := div_pos hqi hpi
      have hlog := Real.log_le_sub_one_of_pos hdiv
      rw [Real.log_div (ne_of_gt hqi) (ne_of_gt hpi)] at hlog
      have hmul : p i * (Real.log (q i) - Real.log (p i)) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hpi)
      have hcancel : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      rw [hcancel] at hmul
      simp only [Real.negMulLog, neg_mul]
      nlinarith [hmul]
  have hsum : ∑ i, (Real.negMulLog (p i) + p i * Real.log (q i)) ≤ ∑ i, (q i - p i) :=
    Finset.sum_le_sum (fun i _ => hkey i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hpsum] at hsum
  linarith [hsum]

/-- **Subadditivity of Shannon entropy under joins.** For two finite measurable partitions `P`
(`= α`) and `Q` (`= β`) of a probability space, the entropy of the join is at most the sum of the
entropies: `H(α ∨ β) ≤ H(α) + H(β)`.

This is the discrete Gibbs inequality `sum_negMulLog_le` applied to the joint distribution
`p (i,j) = μ(Aᵢ ∩ Bⱼ)` and the product distribution `q (i,j) = μ(Aᵢ) · μ(Bⱼ)`. The marginal
identities `measure_eq_sum_inter` show `∑ⱼ p (i,j) = μ(Aᵢ)` and `∑ᵢ p (i,j) = μ(Bⱼ)`, which make
`∑ p = 1` and `∑ q = 1`, and turn `- ∑ p (i,j) · log (μ(Aᵢ) · μ(Bⱼ))` into exactly
`H(α) + H(β)`. -/
lemma entropy_join_le [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    entropy μ (joinCells P.cells Q.cells) ≤ entropy μ P.cells + entropy μ Q.cells := by
  -- Real-valued cell measures, written out explicitly to keep rewriting transparent.
  let a : ι → ℝ := fun i => (μ (P.cells i)).toReal
  let b : κ → ℝ := fun j => (μ (Q.cells j)).toReal
  let p : ι × κ → ℝ := fun x => (μ (P.cells x.1 ∩ Q.cells x.2)).toReal
  let q : ι × κ → ℝ := fun x => a x.1 * b x.2
  -- Marginals: row sums of `p` give `a`, column sums give `b`.
  have hrow : ∀ i, ∑ j, p (i, j) = a i := fun i => by
    change ∑ j, (μ (P.cells i ∩ Q.cells j)).toReal = (μ (P.cells i)).toReal
    rw [Q.measure_eq_sum_inter (P.measurable i),
      ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
  have hcol : ∀ j, ∑ i, p (i, j) = b j := fun j => by
    change ∑ i, (μ (P.cells i ∩ Q.cells j)).toReal = (μ (Q.cells j)).toReal
    rw [P.measure_eq_sum_inter (Q.measurable j),
      ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]
    exact Finset.sum_congr rfl fun i _ => by rw [Set.inter_comm]
  -- The cell measures sum to one.
  have hasum : ∑ i, a i = 1 := P.sum_toReal_measure_eq_one
  have hbsum : ∑ j, b j = 1 := Q.sum_toReal_measure_eq_one
  -- `p` is a probability vector.
  have hpsum : ∑ x, p x = 1 := by
    rw [Fintype.sum_prod_type]; simp_rw [hrow]; exact hasum
  -- `q` is a probability vector (and in particular a sub-probability vector).
  have hqsum : ∑ x, q x = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [show ∀ i j, q (i, j) = a i * b j from fun _ _ => rfl, ← Finset.mul_sum, hbsum,
      mul_one, hasum]
  -- Nonnegativity.
  have hpnn : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  have hann : ∀ i, 0 ≤ a i := fun _ => ENNReal.toReal_nonneg
  have hbnn : ∀ j, 0 ≤ b j := fun _ => ENNReal.toReal_nonneg
  have hqnn : ∀ x, 0 ≤ q x := fun x => mul_nonneg (hann x.1) (hbnn x.2)
  -- Absolute continuity: a positive joint cell forces both marginals positive.
  have hac : ∀ x, p x ≠ 0 → q x ≠ 0 := by
    rintro ⟨i, j⟩ hpx
    have hμ : μ (P.cells i ∩ Q.cells j) ≠ 0 := (ENNReal.toReal_ne_zero.mp hpx).1
    have hpos : 0 < μ (P.cells i ∩ Q.cells j) := pos_iff_ne_zero.mpr hμ
    have ha_pos : 0 < a i :=
      ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le hpos (measure_mono Set.inter_subset_left))) (measure_ne_top μ _)
    have hb_pos : 0 < b j :=
      ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le hpos (measure_mono Set.inter_subset_right))) (measure_ne_top μ _)
    exact ne_of_gt (mul_pos ha_pos hb_pos)
  -- Apply the discrete Gibbs inequality.
  have hgibbs := sum_negMulLog_le p q hpnn hqnn hpsum (le_of_eq hqsum) hac
  -- Identify the left-hand side with the joint entropy.
  have hLHS : ∑ x, Real.negMulLog (p x) = entropy μ (joinCells P.cells Q.cells) := by
    rw [entropy_def]; exact Finset.sum_congr rfl fun x _ => by rw [joinCells_apply]
  -- Expand the right-hand side into `H(α) + H(β)` using `log (a·b) = log a + log b`.
  have hexpand : ∀ x : ι × κ, p x * Real.log (q x)
      = p x * Real.log (a x.1) + p x * Real.log (b x.2) := by
    rintro ⟨i, j⟩
    rcases eq_or_lt_of_le (hpnn (i, j)) with hpi | hpi
    · simp only [← hpi, zero_mul, add_zero]
    · obtain ⟨ha0, hb0⟩ := mul_ne_zero_iff.mp (hac (i, j) (ne_of_gt hpi))
      change p (i, j) * Real.log (a i * b j) = _
      rw [Real.log_mul ha0 hb0, mul_add]
  -- The `a`-marginal of the cross term recovers `H(α)`.
  have hA : ∑ x, p x * Real.log (a x.1) = - entropy μ P.cells := by
    rw [Fintype.sum_prod_type, entropy_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, p (i, j) * Real.log (a i) = (∑ j, p (i, j)) * Real.log (a i) :=
      (Finset.sum_mul ..).symm
    rw [this, hrow, Real.negMulLog]
    change (μ (P.cells i)).toReal * Real.log (μ (P.cells i)).toReal = _
    ring
  -- The `b`-marginal of the cross term recovers `H(β)`.
  have hB : ∑ x, p x * Real.log (b x.2) = - entropy μ Q.cells := by
    rw [Fintype.sum_prod_type_right, entropy_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∑ i, p (i, j) * Real.log (b j) = (∑ i, p (i, j)) * Real.log (b j) :=
      (Finset.sum_mul ..).symm
    rw [this, hcol, Real.negMulLog]
    change (μ (Q.cells j)).toReal * Real.log (μ (Q.cells j)).toReal = _
    ring
  have hRHS : - ∑ x, p x * Real.log (q x) = entropy μ P.cells + entropy μ Q.cells := by
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, hA, hB]; ring
  rw [hLHS, hRHS] at hgibbs
  exact hgibbs

end ErgodicTheory.Entropy
