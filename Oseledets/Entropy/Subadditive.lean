/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.Join
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Invariance of Shannon entropy under a measure-preserving map

This file continues the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`Oseledets.Entropy.Partition` and `Oseledets.Entropy.Join`. It records the **`T`-invariance** of
the Shannon entropy of a finite family of cells: pulling each cell back along a measure-preserving
transformation `T` leaves the entropy unchanged.

Following the Le Maître notes on the Kolmogorov–Sinai theorem, this is the elementary but
indispensable ingredient making the sequence `n ↦ H(⋁ₖ₌₀ⁿ⁻¹ Tᵏα)` *subadditive*, which is what
licenses the Fekete limit defining the entropy `h(T, α)` of `T` relative to a partition `α`. The
entropy of the pulled-back partition `T⁻¹α = (T⁻¹Aᵢ)` equals that of `α` simply because `T`
preserves the measure of each cell, `μ (T⁻¹ Aᵢ) = μ Aᵢ`, so the corresponding `negMulLog` terms
agree.

## Main results

* `Oseledets.Entropy.entropy_comp_preimage`: for a measure-preserving `T : α → α` and a finite
  family of null-measurable cells `s`, the entropy of the pulled-back family `fun i => T ⁻¹' s i`
  equals that of `s`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- **`T`-invariance of Shannon entropy.** If `T : α → α` preserves the measure `μ` and each cell
`s i` is null-measurable, then the entropy of the pulled-back family `fun i => T ⁻¹' s i` equals
the entropy of `s`. Indeed each term `negMulLog (μ (T ⁻¹' s i)).toReal` equals
`negMulLog (μ (s i)).toReal`, since `μ (T ⁻¹' s i) = μ (s i)` by measure-preservation. This is the
invariance making the joined-partition entropy sequence subadditive, hence the Fekete limit
defining Kolmogorov–Sinai entropy well defined. -/
lemma entropy_comp_preimage [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (s : ι → Set α) (hs : ∀ i, NullMeasurableSet (s i) μ) :
    entropy μ (fun i => T ⁻¹' s i) = entropy μ s := by
  rw [entropy_def, entropy_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hT.measure_preimage (hs i)]

end Oseledets.Entropy
