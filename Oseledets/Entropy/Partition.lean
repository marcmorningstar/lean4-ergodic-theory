/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Shannon entropy of a finite measurable partition

This file lays the measure-theoretic foundation for Kolmogorov–Sinai entropy by defining the
**Shannon entropy** of a finite family of measurable cells with respect to a probability measure
`μ`, and proving its two elementary bounds. Following the Le Maître notes on the
Kolmogorov–Sinai theorem, the entropy of a partition `α = (Aᵢ)` is
`H(α) = - ∑ᵢ μ(Aᵢ) log μ(Aᵢ) = ∑ᵢ negMulLog (μ Aᵢ).toReal`, the average information gained by
learning which cell a `μ`-random point lies in.

The entropy is defined on *loose data* — a `Fintype`-indexed family of sets — so that it can be
reused both for a genuine partition and for intermediate non-partition families. The
companion `MeasurePartition` structure bundles the partition hypotheses (almost-everywhere
disjoint cells covering the space) for later use.

## Main definitions

* `Oseledets.Entropy.entropy`: the Shannon entropy `∑ i, negMulLog (μ (s i)).toReal` of a finite
  family of cells `s : ι → Set α`.
* `Oseledets.Entropy.MeasurePartition`: a finite measurable partition of a measure space, i.e. a
  family of measurable, almost-everywhere disjoint cells covering the whole space.

## Main results

* `Oseledets.Entropy.entropy_nonneg`: entropy is nonnegative for a probability measure.
* `Oseledets.Entropy.entropy_le_log_card`: a partition into `k` cells has entropy at most
  `log k` (Proposition 1 of the notes), proved by Jensen's inequality for the concave function
  `negMulLog`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- The Shannon entropy `∑ i, negMulLog (μ (s i)).toReal` of a finite family of cells
`s : ι → Set α` with respect to a measure `μ`. For a genuine partition this is
`- ∑ᵢ μ(sᵢ) log μ(sᵢ)`, the average information gained by learning which cell a random point
lies in. -/
noncomputable def entropy [Fintype ι] (μ : Measure α) (s : ι → Set α) : ℝ :=
  ∑ i, Real.negMulLog (μ (s i)).toReal

@[simp]
lemma entropy_def [Fintype ι] (μ : Measure α) (s : ι → Set α) :
    entropy μ s = ∑ i, Real.negMulLog (μ (s i)).toReal := rfl

/-- A finite measurable partition of a measure space `(α, μ)`: a `Fintype`-indexed family of
measurable cells that are pairwise almost-everywhere disjoint and cover the whole space. -/
structure MeasurePartition (μ : Measure α) (ι : Type*) [Fintype ι] where
  /-- The cells of the partition. -/
  cells : ι → Set α
  /-- Each cell is measurable. -/
  measurable : ∀ i, MeasurableSet (cells i)
  /-- The cells are pairwise almost-everywhere disjoint. -/
  aedisjoint : Pairwise (AEDisjoint μ on cells)
  /-- The cells cover the whole space. -/
  cover : ⋃ i, cells i = Set.univ

/-- Shannon entropy of a finite family of cells is nonnegative for a probability measure, since
each cell has measure in `[0, 1]` and `negMulLog` is nonnegative there. -/
lemma entropy_nonneg [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ] (s : ι → Set α) :
    0 ≤ entropy μ s := by
  rw [entropy_def]
  refine Finset.sum_nonneg fun i _ => ?_
  refine Real.negMulLog_nonneg ENNReal.toReal_nonneg ?_
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := s i))
  rwa [ENNReal.toReal_one] at h

/-- **Proposition 1 (Le Maître).** A finite family of `k` cells whose `μ`-measures sum to `1`
(in particular, a partition of a probability space) has Shannon entropy at most `log k`.

This is Jensen's inequality applied to the concave function `negMulLog` with equal weights
`1 / k`: writing `pᵢ = (μ (s i)).toReal`,
`k⁻¹ * H = ∑ᵢ k⁻¹ • negMulLog pᵢ ≤ negMulLog (∑ᵢ k⁻¹ • pᵢ) = negMulLog k⁻¹ = k⁻¹ * log k`. -/
lemma entropy_le_log_card [Fintype ι] [Nonempty ι] (μ : Measure α) (s : ι → Set α)
    (hsum : ∑ i, (μ (s i)).toReal = 1) :
    entropy μ s ≤ Real.log (Fintype.card ι) := by
  set k : ℝ := (Fintype.card ι : ℝ) with hk
  have hk_pos : 0 < k := by
    rw [hk]; exact_mod_cast Fintype.card_pos
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  -- Jensen for the concave `negMulLog` over `Set.Ici 0` with equal weights `k⁻¹`.
  have hjensen :
      (∑ i, k⁻¹ • Real.negMulLog (μ (s i)).toReal) ≤
        Real.negMulLog (∑ i, k⁻¹ • (μ (s i)).toReal) := by
    refine Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (fun i _ => le_of_lt (inv_pos.mpr hk_pos)) ?_
      (fun i _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk, mul_inv_cancel₀ hk_ne]
  -- Simplify both sides of the Jensen inequality.
  have hLHS : (∑ i, k⁻¹ • Real.negMulLog (μ (s i)).toReal) = k⁻¹ * entropy μ s := by
    rw [entropy_def, Finset.mul_sum]; simp only [smul_eq_mul]
  have harg : (∑ i, k⁻¹ • (μ (s i)).toReal) = k⁻¹ := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
  have hRHS : Real.negMulLog (∑ i, k⁻¹ • (μ (s i)).toReal) = k⁻¹ * Real.log k := by
    rw [harg, Real.negMulLog, Real.log_inv]; ring
  rw [hLHS, hRHS] at hjensen
  -- Cancel the positive factor `k⁻¹`.
  have hcancel := le_of_mul_le_mul_left hjensen (inv_pos.mpr hk_pos)
  rwa [hk] at hcancel

end Oseledets.Entropy
