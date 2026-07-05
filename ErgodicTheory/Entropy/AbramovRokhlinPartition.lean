/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondChainRule
import ErgodicTheory.Entropy.CondKSEntropy
import ErgodicTheory.Entropy.FactorEntropy

/-!
# The partition-level Abramov–Rokhlin identity (B6a, issue #13)

This file develops the **finite-`n` foundations** of the partition-level Abramov–Rokhlin identity
(B6a) sorry-free, isolating the one genuinely analytic residual (a Cesàro/martingale
σ-convergence) as a single named hypothesis.

The target identity, for a factor map `π : (α, T, μ) → (β, S, ν)` with `𝒜 = comap π 𝓑_Y` and a
generating partition `P` refining the pulled-back partition `R.pulledBack`, is
`h(P, T) = h(π⁻¹R, T) + h(P, T | 𝒜)`.

## Roadmap and what is proved here

Write `A_n = ⋁_{k<n} T⁻ᵏ P` and `B_n = ⋁_{k<n} T⁻ᵏ(π⁻¹R)`. The finite-`n` decomposition is

1. **W1 (refinement collapse)** `entropy_joinCells_of_refines`: when each cell of the finer family
   `t` is `μ`-a.e. contained in a single cell of the coarser *partition* `s`, the join entropy
   collapses, `H(s ∨ t) = H(t)`.
2. The **absolute chain rule** `entropy_join_eq_add_condEntropyGivenPartition` (proved in
   `CondChainRule`): `H(B_n ∨ A_n) = H(B_n) + condEntropyGivenPartition μ B_n A_n`.
3. Combining (1) and (2) gives the **per-`n` identity** `H(A_n) = H(B_n) + cond(B_n, A_n)`.

All three are proved here sorry-free.

## Main results

* `ErgodicTheory.Entropy.entropy_joinCells_of_refines` (W1): the refinement collapse of join entropy.
* `ErgodicTheory.Entropy.entropy_join_eq_of_refines`: the per-`n` identity
  `H(A_n) = H(B_n) + condEntropyGivenPartition μ B_n A_n` for a coarsening `B_n` of `A_n`.

## References

* L. M. Abramov, V. A. Rokhlin, *The entropy of a skew product of measure-preserving
  transformations*, Vestnik Leningrad Univ. **17** (1962).
* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Ch. 4.
-/

open MeasureTheory Function Filter Topology
open scoped ENNReal

namespace ErgodicTheory.Entropy

-- NOTE: the variable ORDER `{𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]` (mirroring
-- `CondKSEntropy`/`CondChainRule`) is load-bearing: `mα` is declared AFTER `𝒜`, so it has higher
-- instance priority and `Measure α` / `StandardBorelSpace α` resolve to the ambient `mα`, not the
-- conditioning sub-σ-algebra `𝒜`. The W1 / per-`n` lemmas do not reference `𝒜` (it is dropped from
-- their signatures); only the step-4 limit assembly consumes it.
variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]

/-! ## W1: the refinement collapse of join entropy.

When the finer family `t` refines the coarser *partition* `s` — meaning each cell `t j` is
`μ`-almost contained in a single cell `s (g j)` of `s` — the join `s ∨ t` has the same entropy as
`t` alone, because for each `j` the only nonnull intersection `s i ∩ t j` is the one at `i = g j`,
which equals `t j` up to null sets.
-/

/-- **Refinement collapse of join entropy (W1).** Let `s : ι → Set α` be a finite measurable
*partition* of a measure space `(α, μ)` (its cells are measurable, pairwise a.e. disjoint, covering
the space) and `t : κ → Set α` a finite measurable family. Suppose `t` refines `s` in the sense
that there is an assignment `g : κ → ι` with each cell `t j` `μ`-a.e. contained in the cell
`s (g j)`. Then the entropy of the join collapses to that of the finer family:
`H(s ∨ t) = H(t)`.

For each `j`, of the `ι` intersections `s i ∩ t j` only the one at `i = g j` is nonnull: it equals
`t j` up to a null set (since `t j ⊆ᵐ s (g j)`), and every other `s i ∩ t j` (for `i ≠ g j`) is null
(it lies inside `s i ∩ s (g j)`, an a.e.-disjoint pair of partition cells). Summing `negMulLog` over
the grid `ι × κ` therefore leaves exactly `∑ⱼ negMulLog (μ (t j))`. -/
theorem entropy_joinCells_of_refines [Fintype ι] [Fintype κ] {μ : Measure α}
    (s : ι → Set α) (hs_meas : ∀ i, MeasurableSet (s i))
    (hs_disj : Pairwise (AEDisjoint μ on s)) (t : κ → Set α)
    (g : κ → ι) (hrefine : ∀ j, t j ≤ᵐ[μ] s (g j)) :
    entropy μ (joinCells s t) = entropy μ t := by
  rw [entropy_def, entropy_def]
  -- Group the join sum over `ι × κ` by the `κ`-coordinate.
  rw [show (∑ x, Real.negMulLog (μ (joinCells s t x)).toReal)
      = ∑ j, ∑ i, Real.negMulLog (μ (s i ∩ t j)).toReal from by
        rw [Fintype.sum_prod_type_right]; rfl]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- For this `j`: the diagonal term `i = g j` survives, all others vanish.
  -- The a.e.-containment `t j ⊆ᵐ s (g j)`, as a measure-zero statement on `t j \ s (g j)`.
  have hdiff : μ (t j \ s (g j)) = 0 := by
    have := (hrefine j)
    rwa [ae_le_set] at this
  have hdiag : μ (s (g j) ∩ t j) = μ (t j) := by
    -- `μ (t j ∩ s (g j)) + μ (t j \ s (g j)) = μ (t j)`, with the second piece null.
    have hsplit := measure_inter_add_diff (μ := μ) (t j) (hs_meas (g j))
    rw [hdiff, add_zero] at hsplit
    rw [Set.inter_comm]; exact hsplit
  have hoff : ∀ i, i ≠ g j → μ (s i ∩ t j) = 0 := by
    intro i hi
    -- `s i ∩ t j ⊆ᵐ s i ∩ s (g j)`, which is null since `s i, s (g j)` are a.e. disjoint.
    have hnull : μ (s i ∩ s (g j)) = 0 := hs_disj hi
    -- `s i ∩ t j ⊆ (s i ∩ s (g j)) ∪ (t j \ s (g j))`, both pieces null.
    have hsub : (s i ∩ t j : Set α) ⊆ (s i ∩ s (g j)) ∪ (t j \ s (g j)) := by
      intro x hx
      by_cases hmem : x ∈ s (g j)
      · exact Or.inl ⟨hx.1, hmem⟩
      · exact Or.inr ⟨hx.2, hmem⟩
    exact measure_mono_null hsub (measure_union_null hnull hdiff)
  -- Collapse the inner sum to the single diagonal term.
  rw [show (∑ i, Real.negMulLog (μ (s i ∩ t j)).toReal)
      = Real.negMulLog (μ (s (g j) ∩ t j)).toReal from ?_]
  · rw [hdiag]
  · rw [Finset.sum_eq_single (g j)]
    · intro i _ hi; rw [hoff i hi]; simp
    · intro h; exact absurd (Finset.mem_univ (g j)) h

/-! ## The per-`n` identity: chain rule + W1.

Combining the absolute chain rule `entropy_join_eq_add_condEntropyGivenPartition` with the
refinement collapse W1 yields, for any coarsening `B` of a partition `A`, the per-`n` decomposition
`H(A) = H(B) + condEntropyGivenPartition μ B A`. This is the finite stage of the Abramov–Rokhlin
identity (before dividing by `n` and taking the limit).
-/

/-- **The per-`n` Abramov–Rokhlin identity.** Let `A` and `B` be finite measurable *partitions* of a
probability space with `A` a refinement of `B` (each cell `A_f` is `μ`-a.e. contained in a single
cell `B (g f)`). Then the entropy of `A` splits as the entropy of the coarser `B` plus the
conditional entropy of `A` given `B`:
`H(A) = H(B) + condEntropyGivenPartition μ B.cells A.cells`.

The absolute chain rule `entropy_join_eq_add_condEntropyGivenPartition` gives
`H(B ∨ A) = H(B) + condEntropyGivenPartition μ B.cells A.cells`, and the refinement collapse W1
(`entropy_joinCells_of_refines`, applicable because `B` is a partition and `A` refines it) rewrites
`H(B ∨ A) = H(A)`. -/
theorem entropy_join_eq_of_refines [Fintype ι] [Fintype κ] {μ : Measure α}
    [IsProbabilityMeasure μ] (B : MeasurePartition μ ι) (A : MeasurePartition μ κ)
    (g : κ → ι) (hrefine : ∀ f, A.cells f ≤ᵐ[μ] B.cells (g f)) :
    entropy μ A.cells
      = entropy μ B.cells + condEntropyGivenPartition μ B.cells A.cells := by
  rw [← entropy_join_eq_add_condEntropyGivenPartition B A,
    entropy_joinCells_of_refines B.cells B.measurable B.aedisjoint A.cells g hrefine]

/-! ## Step 4: divide by `n` and pass to the limit.

The per-`n` identity divided by `n` is `(1/n) H(A_n) = (1/n) H(B_n) + (1/n) cond(B_n, A_n)`. The two
absolute terms converge to `ksEntropyPartition` (Fekete, `tendsto_ksEntropySeq`), so the
conditional cell-form term `(1/n) condEntropyGivenPartition μ B_n A_n` converges to the difference.
Assembling the limit identity is then pure `Tendsto` algebra and uniqueness of limits. The result is
stated against a *named hypothesis* `hW3` identifying that limit with the relative entropy
`condKsEntropyPartition` — exactly the residual W3 σ-convergence step (Lévy upward / Cesàro), which
is the one analytic input not discharged here. -/

variable {μ : Measure α} [IsProbabilityMeasure μ] [StandardBorelSpace α]
variable {T : α → α}

/-- The **conditional cell-form sequence** `n ↦ condEntropyGivenPartition μ B_n A_n`, the additive-
over-cells conditional entropy of the `n`-fold join `A_n = ⋁_{k<n}T⁻ᵏP` given the coarser join
`B_n = ⋁_{k<n}T⁻ᵏQ`. This is the term whose Cesàro limit is, by the per-`n` identity, the
difference `h(P, T) − h(Q, T)`. -/
noncomputable def condCellSeq [Fintype ι] [Fintype κ]
    (hT : MeasurePreserving T μ μ) (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι) (n : ℕ) :
    ℝ :=
  condEntropyGivenPartition μ (ksJoin hT Q n).cells (ksJoin hT P n).cells

/-- **The Abramov–Rokhlin partition identity, modulo the W3 limit-identity hypothesis.** Given the
per-`n` refinement of `A_n` over `B_n` (each cell of the `P`-join is `μ`-a.e. inside a single cell
of the `Q`-join, witnessed by `g n`) and the W3 σ-convergence hypothesis `hW3` identifying the
Cesàro limit of the conditional cell-form sequence with the relative entropy
`condKsEntropyPartition`, the partition-level Abramov–Rokhlin identity holds:
`h(P, T) = h(Q, T) + h(P, T | 𝒜)`.

Everything except `hW3` is discharged sorry-free: the per-`n` identity `entropy_join_eq_of_refines`
divided by `n`, the two Fekete convergences `tendsto_ksEntropySeq` for `A_n` and `B_n`, and limit
uniqueness. `hW3` is the genuine analytic residual (the increasing σ-algebras `σ(B_n)` catching up
to the fixed factor σ-algebra `𝒜`, a martingale/Cesàro step). -/
theorem abramovRokhlin_partition_of_W3 [Fintype ι] [Fintype κ]
    (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (g : ∀ n, (Fin n → ι) → (Fin n → κ))
    (hrefine : ∀ n f, (ksJoin hT P n).cells f ≤ᵐ[μ] (ksJoin hT Q n).cells (g n f))
    (hW3 : Tendsto (fun n => condCellSeq hT Q P n / n) atTop
        (𝓝 (condKsEntropyPartition hm hT hinv P))) :
    ksEntropyPartition hT P
      = ksEntropyPartition hT Q + condKsEntropyPartition hm hT hinv P := by
  -- Per-`n`: `H(A_n) = H(B_n) + condCellSeq n`, hence `(1/n)H(A_n) = (1/n)H(B_n) + (1/n)cellSeq`.
  have hpern : ∀ n, ksEntropySeq hT P n = ksEntropySeq hT Q n + condCellSeq hT Q P n := fun n =>
    entropy_join_eq_of_refines (ksJoin hT Q n) (ksJoin hT P n) (g n) (hrefine n)
  -- Divide each per-`n` identity by `n`.
  have hdiv : (fun n => ksEntropySeq hT P n / n)
      = fun n => ksEntropySeq hT Q n / n + condCellSeq hT Q P n / n := by
    funext n; rw [hpern n, add_div]
  -- The averaged `A_n`-sequence converges to `h(P, T)`.
  have hA : Tendsto (fun n => ksEntropySeq hT P n / n) atTop (𝓝 (ksEntropyPartition hT P)) :=
    tendsto_ksEntropySeq hT P
  -- The RHS converges to `h(Q, T) + h(P, T | 𝒜)`.
  have hRHS : Tendsto (fun n => ksEntropySeq hT Q n / n + condCellSeq hT Q P n / n) atTop
      (𝓝 (ksEntropyPartition hT Q + condKsEntropyPartition hm hT hinv P)) :=
    (tendsto_ksEntropySeq hT Q).add hW3
  -- Both sides are limits of the same sequence; uniqueness pins the equality.
  exact tendsto_nhds_unique (hdiv ▸ hA) hRHS

end ErgodicTheory.Entropy
