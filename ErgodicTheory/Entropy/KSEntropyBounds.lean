/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropy

/-!
# Characterizing bounds of the Kolmogorov–Sinai entropy

This file proves the two elementary bounds that pin down the Kolmogorov–Sinai entropy
`h(α, T) = ksEntropyPartition hT P` between `0` and the Shannon entropy `H(α)` of the
generating partition:

* `0 ≤ h(α, T)` (`ksEntropyPartition_nonneg`), and
* `h(α, T) ≤ H(α)` (`ksEntropyPartition_le_entropy`).

The first is immediate from the nonnegativity of each averaged iterated-join entropy together
with `tendsto_ksEntropySeq`. The second rests on the linear upper bound
`ksEntropySeq n ≤ n • H(α)` (`ksEntropySeq_le_nsmul`), obtained by induction from the
subadditivity `ksEntropySeq_subadditive` and the single-step identity
`ksEntropySeq 1 = H(α)` (`ksEntropySeq_one`); dividing by `n ≥ 1` and passing to the Fekete
limit yields `h(α, T) ≤ H(α)`.

## Main results

* `ErgodicTheory.Entropy.ksEntropySeq_one`: `ksEntropySeq hT P 1 = entropy μ P.cells`.
* `ErgodicTheory.Entropy.ksEntropySeq_le_nsmul`: `ksEntropySeq hT P n ≤ n • entropy μ P.cells`.
* `ErgodicTheory.Entropy.ksEntropyPartition_nonneg`: `0 ≤ ksEntropyPartition hT P`.
* `ErgodicTheory.Entropy.ksEntropyPartition_le_entropy`: `ksEntropyPartition hT P ≤ entropy μ P.cells`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- The single-step iterated-join entropy equals the Shannon entropy of the partition itself:
`ksEntropySeq hT P 1 = H(α)`. The `1`-fold join `⋁ₖ₌₀⁰ T⁻ᵏ α` has cell at `f : Fin 1 → ι` the
single intersection `⋂ₖ T⁻ᵏ (α_{f k}) = T⁰⁻¹(α_{f 0}) = α_{f 0}`, so it is `α` reindexed by the
equivalence `(Fin 1 → ι) ≃ ι`; entropy is invariant under this reindexing. -/
@[simp]
lemma ksEntropySeq_one [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    ksEntropySeq hT P 1 = entropy μ P.cells := by
  rw [ksEntropySeq, ksJoin_cells]
  have hcell : ∀ i : ι,
      ksJoinCells P.cells T 1 ((Equiv.funUnique (Fin 1) ι).symm i) = P.cells i := by
    intro i
    rw [ksJoinCells_apply]
    have hstep : ∀ k : Fin 1,
        (T^[(k : ℕ)]) ⁻¹' P.cells ((Equiv.funUnique (Fin 1) ι).symm i k) = P.cells i := by
      intro k
      rw [Equiv.funUnique_symm_apply, uniqueElim_const,
        show (k : ℕ) = 0 by omega, Function.iterate_zero, Set.preimage_id]
    rw [Set.iInter_congr hstep, Set.iInter_const]
  rw [← entropy_reindex μ (Equiv.funUnique (Fin 1) ι).symm (ksJoinCells P.cells T 1)]
  exact congrArg (entropy μ) (funext hcell)

/-- The iterated-join entropy grows at most linearly: `ksEntropySeq hT P n ≤ n • H(α)`. This is the
subadditive estimate `u n ≤ n • u 1`, proved by induction from `ksEntropySeq_subadditive`, with the
single step `ksEntropySeq 1 = H(α)` substituted via `ksEntropySeq_one`. -/
lemma ksEntropySeq_le_nsmul [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P n ≤ n • entropy μ P.cells := by
  induction n with
  | zero => simp
  | succ k IH =>
    calc ksEntropySeq hT P (k + 1)
        ≤ ksEntropySeq hT P k + ksEntropySeq hT P 1 := ksEntropySeq_subadditive hT P k 1
      _ ≤ k • entropy μ P.cells + entropy μ P.cells := by
          rw [ksEntropySeq_one]; gcongr
      _ = (k + 1) • entropy μ P.cells := by rw [succ_nsmul]

/-- **Nonnegativity of the Kolmogorov–Sinai entropy:** `0 ≤ h(α, T)`. Each averaged iterated-join
entropy `ksEntropySeq n / n` is nonnegative, and the bound passes to the Fekete limit. -/
lemma ksEntropyPartition_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    0 ≤ ksEntropyPartition hT P := by
  refine ge_of_tendsto (tendsto_ksEntropySeq hT P) ?_
  filter_upwards with n
  exact div_nonneg (ksEntropySeq_nonneg hT P n) (Nat.cast_nonneg n)

/-- **Upper bound of the Kolmogorov–Sinai entropy by the partition entropy:** `h(α, T) ≤ H(α)`.
From the linear bound `ksEntropySeq n ≤ n • H(α)` (`ksEntropySeq_le_nsmul`), dividing by `n ≥ 1`
gives `ksEntropySeq n / n ≤ H(α)` eventually; this passes to the Fekete limit. -/
lemma ksEntropyPartition_le_entropy [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    ksEntropyPartition hT P ≤ entropy μ P.cells := by
  refine le_of_tendsto (tendsto_ksEntropySeq hT P) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn0]
  calc ksEntropySeq hT P n ≤ n • entropy μ P.cells := ksEntropySeq_le_nsmul hT P n
    _ = entropy μ P.cells * (n : ℝ) := by rw [nsmul_eq_mul, mul_comm]

end ErgodicTheory.Entropy
