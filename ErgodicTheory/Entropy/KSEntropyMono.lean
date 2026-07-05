/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropyJoin
import ErgodicTheory.Entropy.KSEntropyProps

/-!
# Monotonicity of the Kolmogorov–Sinai entropy under refinement by a join

For a measure-preserving transformation `T` and two finite measurable partitions `α` and `β`, the
join `α ∨ β` *refines* `α` (every `α`-cell is a union of `(α ∨ β)`-cells). This file proves that
the partition-relative Kolmogorov–Sinai entropy is **monotone under this refinement**:
`h(α, T) ≤ h(α ∨ β, T)`.

This is the entropy-increases-under-refinement half of the variational picture, complementing the
subadditivity `h(α ∨ β, T) ≤ h(α, T) + h(β, T)` (`ksEntropyPartition_join_le`): together they
sandwich the join entropy between `max (h(α, T), h(β, T))` and `h(α, T) + h(β, T)`.

The dynamical statement reduces, cell by cell, to a *static* refinement bound
`H(α) ≤ H(α ∨ β)` (`entropy_le_entropy_join`). At the scalar level this is the **superadditivity
of `negMulLog` over a finite sum**: for nonnegative reals `x` with sum `s`,
`negMulLog s ≤ ∑ⱼ negMulLog (x j)` (`negMulLog_sum_le_sum_negMulLog`), because each term obeys
`x j · log (x j) ≤ x j · log s` by monotonicity of `log` on `0 < x j ≤ s` (the `x j = 0` terms
contribute `0`), so `∑ⱼ x j · log (x j) ≤ s · log s`; negating gives the claim. Applying it to
each `α`-row of the joint cell measures `μ(Aᵢ ∩ Bⱼ)`, whose `β`-marginal is `μ(Aᵢ)`
(`MeasurePartition.measure_eq_sum_inter`), yields `H(α) ≤ H(α ∨ β)`.

The dynamical step then mirrors `ksEntropySeq_join_le`: reindexing the `n`-fold join of `α ∨ β`
by `Equiv.arrowProdEquivProdArrow` exhibits its entropy as the static join entropy of the two
`n`-fold joins (`ksJoinCells_joinCells`), so the static refinement bound gives the per-`n`
inequality `ksEntropySeq α n ≤ ksEntropySeq (α ∨ β) n`; dividing by `n` and passing both Fekete
limits (`tendsto_ksEntropySeq`, `le_of_tendsto_of_tendsto'`) gives the dynamical statement.

## Main results

* `ErgodicTheory.Entropy.negMulLog_sum_le_sum_negMulLog`: `negMulLog (∑ⱼ x j) ≤ ∑ⱼ negMulLog (x j)`
  for a nonnegative family.
* `ErgodicTheory.Entropy.entropy_le_entropy_join`: the static refinement bound `H(α) ≤ H(α ∨ β)`.
* `ErgodicTheory.Entropy.ksEntropySeq_le_join`: the per-`n` bound `ksEntropySeq α n ≤
  ksEntropySeq (α ∨ β) n`.
* `ErgodicTheory.Entropy.ksEntropyPartition_le_join`: `h(α, T) ≤ h(α ∨ β, T)`, monotonicity of the
  Kolmogorov–Sinai entropy under refinement by a join.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

/-- **Superadditivity of `negMulLog` over a finite sum.** For a nonnegative family `x : ω → ℝ`
with total `s = ∑ⱼ x j`, the value of `negMulLog` at the sum is at most the sum of the values:
`negMulLog (∑ⱼ x j) ≤ ∑ⱼ negMulLog (x j)`. Equivalently `s · log s ≤ ∑ⱼ x j · log (x j)`: each
term obeys `x j · log (x j) ≤ x j · log s` by monotonicity of `log` on `0 < x j ≤ s`, with the
`x j = 0` terms contributing `0` on both sides. -/
lemma negMulLog_sum_le_sum_negMulLog {ω : Type*} [Fintype ω] (x : ω → ℝ)
    (hx : ∀ j, 0 ≤ x j) :
    Real.negMulLog (∑ j, x j) ≤ ∑ j, Real.negMulLog (x j) := by
  -- It suffices to show `(∑ⱼ x j) · log (∑ⱼ x j) ≤ ∑ⱼ x j · log (x j)`, then negate.
  have hterm : ∀ j, x j * Real.log (x j) ≤ x j * Real.log (∑ i, x i) := by
    intro j
    rcases eq_or_lt_of_le (hx j) with hxj | hxj
    · simp [← hxj]
    · have hle : x j ≤ ∑ i, x i := Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ j)
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hxj hle) (hx j)
  have hsum : ∑ j, x j * Real.log (x j) ≤ ∑ j, x j * Real.log (∑ i, x i) :=
    Finset.sum_le_sum fun j _ => hterm j
  rw [← Finset.sum_mul] at hsum
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith [hsum]

/-- **Static refinement bound: entropy increases under joins.** For two finite measurable
partitions `P` (`= α`) and `Q` (`= β`) of a probability space, the entropy of the join dominates
the entropy of either factor: `H(α) ≤ H(α ∨ β)`.

Each `α`-cell measure splits along `β` as `μ(Aᵢ) = ∑ⱼ μ(Aᵢ ∩ Bⱼ)`
(`MeasurePartition.measure_eq_sum_inter`); the scalar superadditivity
`negMulLog_sum_le_sum_negMulLog` applied to the `i`-th row of the joint cell measures bounds
`negMulLog (μ(Aᵢ).toReal)` by `∑ⱼ negMulLog (μ(Aᵢ ∩ Bⱼ).toReal)`, and summing over `i` (regrouping
the product index `ι × κ` by `Fintype.sum_prod_type`) gives the claim. -/
lemma entropy_le_entropy_join [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    entropy μ P.cells ≤ entropy μ (joinCells P.cells Q.cells) := by
  -- Real-valued joint cell measures.
  set p : ι × κ → ℝ := fun x => (μ (P.cells x.1 ∩ Q.cells x.2)).toReal with hp
  have hpnn : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  -- Row marginal: the `β`-sum of the `i`-th row recovers `μ(Aᵢ).toReal`.
  have hrow : ∀ i, ∑ j, p (i, j) = (μ (P.cells i)).toReal := by
    intro i
    rw [Q.measure_eq_sum_inter (P.measurable i),
      ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
  -- Rewrite both entropies as sums over the product index and bound row by row.
  rw [entropy_def, entropy_def, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← hrow i]
  exact negMulLog_sum_le_sum_negMulLog (fun j => p (i, j)) (fun j => hpnn (i, j))

/-- **Per-`n` refinement bound.** The `n`-fold dynamical-join entropy of `α` is at most that of the
join `α ∨ β`: `H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α) ≤ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ(α ∨ β))`.

Reindexing the product index `Fin n → ι × κ` by `Equiv.arrowProdEquivProdArrow` and using the cell
identity `ksJoinCells_joinCells`, the `(α ∨ β)`-join entropy equals the *static* join entropy of
the two `n`-fold joins; the static refinement bound `entropy_le_entropy_join` then dominates the
`n`-fold join entropy of `α`. -/
lemma ksEntropySeq_le_join [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (Q : MeasurePartition μ κ) (n : ℕ) :
    ksEntropySeq hT P n ≤ ksEntropySeq hT (joinPartition P Q) n := by
  -- The `n`-fold joins of `α` and `β`, as the two factors of a static join.
  set A : MeasurePartition μ (Fin n → ι) := ksJoin hT P n with hA
  set B : MeasurePartition μ (Fin n → κ) := ksJoin hT Q n with hB
  -- Rewrite the `(α ∨ β)`-join entropy as the static join entropy via the product reindexing.
  have hreindex : ksEntropySeq hT (joinPartition P Q) n
      = entropy μ (joinCells A.cells B.cells) := by
    rw [ksEntropySeq, ksJoin_cells, joinPartition_cells,
      ← entropy_reindex μ (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ)).symm,
      entropy_def, entropy_def]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨g, h⟩ := q
    rw [hA, hB, ksJoin_cells, ksJoin_cells, joinCells_apply]
    have hcell : ksJoinCells (joinCells P.cells Q.cells) T n
        ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ)).symm (g, h))
          = ksJoinCells P.cells T n g ∩ ksJoinCells Q.cells T n h :=
      ksJoinCells_joinCells P.cells Q.cells T n _
    rw [hcell]
  rw [hreindex, ksEntropySeq, ← hA]
  exact entropy_le_entropy_join A B

/-- **Monotonicity of the Kolmogorov–Sinai entropy under refinement by a join:**
`h(α, T) ≤ h(α ∨ β, T)`.

The join `α ∨ β` refines `α`, so its long-run entropy rate dominates. The per-`n` bound
`ksEntropySeq_le_join` divided by `n` reads `ksEntropySeq α n / n ≤ ksEntropySeq (α ∨ β) n / n`.
Each averaged sequence converges to its Kolmogorov–Sinai entropy by `tendsto_ksEntropySeq`, so
passing the pointwise inequality to the two Fekete limits (`le_of_tendsto_of_tendsto'`) gives the
claim. -/
lemma ksEntropyPartition_le_join [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (Q : MeasurePartition μ κ) :
    ksEntropyPartition hT P ≤ ksEntropyPartition hT (joinPartition P Q) := by
  refine le_of_tendsto_of_tendsto' (tendsto_ksEntropySeq hT P)
    (tendsto_ksEntropySeq hT (joinPartition P Q)) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right (ksEntropySeq_le_join hT P Q n) hn0.le

end ErgodicTheory.Entropy
