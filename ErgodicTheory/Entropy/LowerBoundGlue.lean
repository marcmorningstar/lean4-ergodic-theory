/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropySystem
import ErgodicTheory.Entropy.KSEntropyPow
import ErgodicTheory.Entropy.Join

/-!
# A lower-bound glue for Kolmogorov–Sinai entropy from atom-measure decay

This module packages the elementary lower-bound machinery for the Kolmogorov–Sinai entropy of a
measure-preserving system, tailored to the situation where every atom (cell of the iterated join)
of a fixed generating-style partition has measure decaying geometrically, `μ(atom) ≤ C · θⁿ` with
`0 < θ`. The three ingredients are:

* `entropy_ge_neg_log_of_forall_le`: a Shannon-entropy lower bound `H(P) ≥ -log ε` whenever every
  cell has measure at most `ε`.
* `ksEntropyPartition_ge_of_seq_bound`: a Fekete-limit lower bound from a per-`n` affine bound on
  the iterated-join entropy sequence.
* `coe_le_ksEntropy_of_partition_ge`: lifting a partition-relative lower bound to the entropy of
  the system.

Combining them yields `ksEntropy_ge_of_atom_measure_le`: a geometric atom-measure bound
`μ(atom) ≤ C · θⁿ` forces `-log θ ≤ h(T)`.

## Main results

* `ErgodicTheory.Entropy.entropy_ge_neg_log_of_forall_le`
* `ErgodicTheory.Entropy.ksEntropyPartition_ge_of_seq_bound`
* `ErgodicTheory.Entropy.coe_le_ksEntropy_of_partition_ge`
* `ErgodicTheory.Entropy.ksEntropy_ge_of_atom_measure_le`
-/

open MeasureTheory Function Filter Topology
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {α : Type*} [MeasurableSpace α]

/-- **Shannon-entropy lower bound from a uniform cell-measure bound.** If every cell of a finite
measurable partition of a probability space has measure at most `ε > 0`, then the entropy is at
least `-log ε`. Term by term `negMulLog (pᵢ) ≥ pᵢ · (-log ε)` (trivially when `pᵢ = 0`, and by
`log pᵢ ≤ log ε` otherwise); summing and using `∑ pᵢ = 1` gives the claim. -/
theorem entropy_ge_neg_log_of_forall_le {ι : Type*} [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] (P : MeasurePartition μ ι) {ε : ℝ}
    (hle : ∀ i, (μ (P.cells i)).toReal ≤ ε) :
    entropy μ P.cells ≥ -Real.log ε := by
  set p : ι → ℝ := fun i => (μ (P.cells i)).toReal with hp
  have hsum : ∑ i, p i = 1 := P.sum_toReal_measure_eq_one
  have key : ∀ i, p i * (-Real.log ε) ≤ Real.negMulLog (p i) := by
    intro i
    have hnn : (0 : ℝ) ≤ p i := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · rw [← h0]; simp [Real.negMulLog]
    · have hlog : Real.log (p i) ≤ Real.log ε := Real.log_le_log hpos (hle i)
      rw [Real.negMulLog]
      nlinarith [hlog, hpos.le]
  calc -Real.log ε
      = (∑ i, p i) * (-Real.log ε) := by rw [hsum, one_mul]
    _ = ∑ i, p i * (-Real.log ε) := by rw [Finset.sum_mul]
    _ ≤ ∑ i, Real.negMulLog (p i) := Finset.sum_le_sum (fun i _ => key i)
    _ = entropy μ P.cells := by rw [entropy_def]

/-- **Fekete lower bound from a per-`n` affine bound.** If `(n : ℝ) · L - c ≤ ksEntropySeq n` for
every `n`, then `L ≤ ksEntropyPartition`. The averaged sequence tends to `ksEntropyPartition`,
while `L - c / n → L`; the per-`n` bound compares them. -/
theorem ksEntropyPartition_ge_of_seq_bound {ι : Type*} [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {L c : ℝ}
    (hbound : ∀ n : ℕ, (n : ℝ) * L - c ≤ ksEntropySeq hT P n) :
    L ≤ ksEntropyPartition hT P := by
  have h1 : Tendsto (fun n : ℕ => ksEntropySeq hT P n / n) atTop
      (𝓝 (ksEntropyPartition hT P)) := tendsto_ksEntropySeq hT P
  have hcdiv : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have h2 : Tendsto (fun n : ℕ => L - c / (n : ℝ)) atTop (𝓝 L) := by
    have := (tendsto_const_nhds (x := L) (f := atTop)).sub hcdiv
    simpa using this
  refine le_of_tendsto_of_tendsto h2 h1 ?_
  refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  have hexpand : (L - c / (n : ℝ)) * n = (n : ℝ) * L - c := by
    field_simp
  rw [hexpand]; exact hbound n

/-- **Lifting a partition lower bound to the entropy of the system.** A real lower bound
`L ≤ ksEntropyPartition hT P` for an arbitrary-`Fintype`-indexed partition `P` coerces to
`(L : EReal) ≤ ksEntropy hT`, since `ksEntropyPartition_coe_le_ksEntropy` already reindexes to a
`Fin`-indexed partition internally. -/
theorem coe_le_ksEntropy_of_partition_ge {ι : Type*} [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {L : ℝ} (h : L ≤ ksEntropyPartition hT P) :
    ((L : ℝ) : EReal) ≤ ksEntropy hT :=
  (EReal.coe_le_coe h).trans (ksEntropyPartition_coe_le_ksEntropy hT P)

/-- **Entropy lower bound from geometric atom-measure decay.** If every atom
`⋂ₖ T⁻ᵏ (P_{f k})` of the `n`-fold iterated join of a finite measurable partition `P` has measure
at most `C · θⁿ` (with `0 < θ`, `0 < C`), then `-log θ ≤ h(T)`. Per `n`, the uniform cell bound
gives `ksEntropySeq n ≥ -log (C · θⁿ) = n · (-log θ) - log C`; the Fekete bound then yields
`-log θ ≤ ksEntropyPartition`, which lifts to the system. -/
theorem ksEntropy_ge_of_atom_measure_le {ι : Type*} [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hatom : ∀ n (f : Fin n → ι),
      μ (ksJoinCells P.cells T n f) ≤ ENNReal.ofReal (C * θ ^ n)) :
    ((-Real.log θ : ℝ) : EReal) ≤ ksEntropy hT := by
  refine coe_le_ksEntropy_of_partition_ge hT P
    (ksEntropyPartition_ge_of_seq_bound hT P (L := -Real.log θ) (c := Real.log C) ?_)
  intro n
  have hθn : (0 : ℝ) < θ ^ n := pow_pos hθ n
  have hε : (0 : ℝ) < C * θ ^ n := mul_pos hC hθn
  -- Each atom's real measure is at most `C · θⁿ`.
  have hle : ∀ f : Fin n → ι, (μ ((ksJoin hT P n).cells f)).toReal ≤ C * θ ^ n := by
    intro f
    exact ENNReal.toReal_le_of_le_ofReal hε.le (hatom n f)
  -- Shannon lower bound for the join partition, then rewrite the log.
  have hlb : ksEntropySeq hT P n ≥ -Real.log (C * θ ^ n) :=
    entropy_ge_neg_log_of_forall_le (ksJoin hT P n) hle
  have hlog : Real.log (C * θ ^ n) = Real.log C + n * Real.log θ := by
    rw [Real.log_mul hC.ne' hθn.ne', Real.log_pow]
  have hrw : -Real.log (C * θ ^ n) = (n : ℝ) * -Real.log θ - Real.log C := by
    rw [hlog]; ring
  rw [hrw] at hlb
  exact hlb

end ErgodicTheory.Entropy
