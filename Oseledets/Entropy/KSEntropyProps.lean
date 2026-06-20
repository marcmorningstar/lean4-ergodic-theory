/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.KSEntropyBounds

/-!
# The infimum characterization of the Kolmogorov–Sinai entropy

For a measure-preserving transformation `T` and a finite measurable partition `α`, the
Kolmogorov–Sinai entropy `h(α, T) = ksEntropyPartition hT P` is the Fekete limit of the
averaged iterated-join entropies `ksEntropySeq hT P n / n`. A *subadditive* sequence's
averages converge **down** to their infimum, so the limit is a lower bound for *every*
averaged term. This file records that standard property:

* `ksEntropyPartition_le_ksEntropySeq_div`: `h(α, T) ≤ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α) / n` for `n ≥ 1`,
  i.e. `h(α, T) = infₙ ksEntropySeq n / n`.

This is the genuine tightening behind the cruder bound `h(α, T) ≤ H(α)`
(`ksEntropyPartition_le_entropy`), which it recovers as the `n = 1` case via
`ksEntropySeq_one`. The proof is a direct application of Fekete's lemma in the sharp
`lim ≤ u n / n` form (`Subadditive.lim_le_div` in `Mathlib.Analysis.Subadditive`); the
required bounded-below hypothesis is the same one discharged from entropy nonnegativity in
`tendsto_ksEntropySeq`.

The property is standard in the Kolmogorov–Sinai theory; see Le Maître, *Notes on the
Kolmogorov–Sinai theorem* (2017), §1, where `h(α, T)` is introduced precisely as the
infimum `infₙ (1/n) H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)` of the subadditive averaged entropies.

## Main results

* `Oseledets.Entropy.ksEntropyPartition_le_ksEntropySeq_div`:
  `ksEntropyPartition hT P ≤ ksEntropySeq hT P n / n` for `n ≥ 1`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter Topology

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- The averaged iterated-join entropies are **bounded below** (by `0`): each
`ksEntropySeq hT P n / n` is a quotient of nonnegative numbers. This is the boundedness
hypothesis of Fekete's lemma, packaged for reuse. -/
lemma bddBelow_ksEntropySeq_div [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    BddBelow (Set.range fun n => ksEntropySeq hT P n / n) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (ksEntropySeq_nonneg hT P n) (Nat.cast_nonneg n)

/-- **Infimum characterization of the Kolmogorov–Sinai entropy:** for every `n ≥ 1`,
`h(α, T) ≤ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α) / n`. Equivalently, the averaged iterated-join entropies
converge *down* to their infimum, `h(α, T) = infₙ ksEntropySeq n / n`, so `h(α, T)` is a
lower bound for each averaged term. This is the sharp form of the bound
`h(α, T) ≤ H(α)` (`ksEntropyPartition_le_entropy`), recovered from it at `n = 1` via
`ksEntropySeq_one`. The proof applies Fekete's lemma in its `lim ≤ u n / n` form
(`Subadditive.lim_le_div`) to the subadditive sequence `ksSubadditive hT P`, with the
bounded-below hypothesis supplied by `bddBelow_ksEntropySeq_div`. -/
lemma ksEntropyPartition_le_ksEntropySeq_div [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {n : ℕ} (hn : 1 ≤ n) :
    ksEntropyPartition hT P ≤ ksEntropySeq hT P n / n :=
  (ksSubadditive hT P).lim_le_div (bddBelow_ksEntropySeq_div hT P) (Nat.one_le_iff_ne_zero.mp hn)

end Oseledets.Entropy
