/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.CondPartition
import Oseledets.Entropy.Subadditive2

/-!
# Subadditivity and invariance of conditional entropy

This file is the next layer of the conditional-entropy milestone (GitHub issue #13). It continues
`Oseledets.Entropy.CondPartition` (which defines `condEntropy μ 𝒜 s`, the `μ`-average of the
pointwise entropy against the regular conditional probability `condExpKernel μ 𝒜 ω`).

The structural fact established here is **subadditivity under joins** (`condEntropy_join_le`): for
partitions `P` and `Q`, `H(P ∨ Q | 𝒜) ≤ H(P | 𝒜) + H(Q | 𝒜)`. This is proved by running the
absolute argument (`entropy_join_le`) *pointwise inside the integral* against the Markov-kernel
measure `condExpKernel μ 𝒜 ω`, which for `μ`-a.e. `ω` is a probability measure for which `P` and `Q`
are still genuine measurable partitions; the resulting pointwise bound integrates termwise.

Invariance of conditional entropy under a factor is provided instead by
`Oseledets.Entropy.condEntropy_comap_pullback` (`Oseledets.Entropy.CondJointPullback`), which
conditions on the *pulled-back* σ-algebra `comap S 𝒜` and so needs only the one-sided hypothesis; it
superseded an earlier fixed-`𝒜` pull-back that required the two-sided invariance hypotheses.

## Main results

* `Oseledets.Entropy.condEntropy_join_le`: subadditivity of conditional entropy under joins.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Entropy

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

/-- For a finite measurable partition `P` of the probability space, the cells are
`condExpKernel μ 𝒜 ω`-a.e. pairwise disjoint for `μ`-almost every `ω`. This is the partition
hypothesis of `MeasurePartition` transferred from `μ` to the conditional kernel through the
disintegration `condExpKernel μ 𝒜 ∘ₘ μ.trim h𝒜 = μ`. -/
lemma condExpKernel_pairwise_aedisjoint [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    ∀ᵐ ω ∂μ, Pairwise (AEDisjoint (@condExpKernel α mα _ μ _ 𝒜 ω) on P.cells) := by
  have hdisj : ∀ᵐ ω ∂μ, ∀ i j, i ≠ j →
      @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i ∩ P.cells j) = 0 := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    refine eventually_imp_distrib_left.2 fun hij => ?_
    have hμ0 : μ (P.cells i ∩ P.cells j) = 0 := P.aedisjoint hij
    have hμ : ∀ᵐ ω ∂μ, ω ∉ P.cells i ∩ P.cells j := by
      rw [ae_iff]; simpa using hμ0
    have hμ2 : ∀ᵐ ω ∂(@condExpKernel α mα _ μ _ 𝒜 ∘ₘ μ.trim h𝒜),
        ω ∉ P.cells i ∩ P.cells j := by
      rw [condExpKernel_comp_trim h𝒜]; exact hμ
    have hae := Measure.ae_ae_of_ae_comp hμ2
    refine ae_of_ae_trim h𝒜 ?_
    filter_upwards [hae] with ω hω
    simpa using ae_iff.mp hω
  filter_upwards [hdisj] with ω hω i j hij
  exact hω i j hij

/-- The pointwise `condEntropy` integrand of a family `s` equals the Shannon `entropy` of `s`
computed against the conditional-kernel probability measure `condExpKernel μ 𝒜 ω`. -/
lemma condEntropy_integrand_eq_entropy [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ]
    (s : ι → Set α) (ω : α) :
    (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (s i)).toReal)
      = entropy (@condExpKernel α mα _ μ _ 𝒜 ω) s := by
  rw [entropy_def]

/-- **Subadditivity of conditional entropy under joins.** For two finite measurable partitions `P`
and `Q` of a probability space, the conditional entropy of the join is at most the sum of the
conditional entropies: `H(P ∨ Q | 𝒜) ≤ H(P | 𝒜) + H(Q | 𝒜)`.

The bound is the absolute subadditivity `entropy_join_le` run *pointwise inside the integral*: for
`μ`-almost every `ω` the conditional kernel `condExpKernel μ 𝒜 ω` is a probability measure for which
both `P` and `Q` are still genuine measurable partitions (their cells are kernel-a.e. disjoint by
`condExpKernel_pairwise_aedisjoint` and still cover the space), so the discrete Gibbs argument
bounds the pointwise integrand `entropy (κ ω) (P ∨ Q)` by `entropy (κ ω) P + entropy (κ ω) Q`.
Integrating this a.e. inequality over `μ` (all three integrands are integrable by the `log card`
bound) gives the claim. -/
lemma condEntropy_join_le [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    condEntropy μ 𝒜 (joinCells P.cells Q.cells)
      ≤ condEntropy μ 𝒜 P.cells + condEntropy μ 𝒜 Q.cells := by
  rw [condEntropy_def, condEntropy_def, condEntropy_def,
    ← integral_add (integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i))
      (integrable_condEntropy_integrand h𝒜 Q.cells (fun j => Q.measurable j))]
  -- Pointwise bound on the integrand for `μ`-a.e. `ω`, via the kernel-level partitions.
  have hbound : ∀ᵐ ω ∂μ,
      (∑ x, Real.negMulLog
          (@condExpKernel α mα _ μ _ 𝒜 ω ((joinCells P.cells Q.cells) x)).toReal)
        ≤ (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal)
          + ∑ j, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (Q.cells j)).toReal := by
    filter_upwards [condExpKernel_pairwise_aedisjoint h𝒜 P,
      condExpKernel_pairwise_aedisjoint h𝒜 Q] with ω hPd hQd
    -- The kernel is a probability measure, and `P`, `Q` are partitions for it.
    have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
      IsMarkovKernel.isProbabilityMeasure ω
    let Pω : MeasurePartition (@condExpKernel α mα _ μ _ 𝒜 ω) ι :=
      { cells := P.cells, measurable := P.measurable, aedisjoint := hPd, cover := P.cover }
    let Qω : MeasurePartition (@condExpKernel α mα _ μ _ 𝒜 ω) κ :=
      { cells := Q.cells, measurable := Q.measurable, aedisjoint := hQd, cover := Q.cover }
    have hjoin := entropy_join_le Pω Qω
    rw [entropy_def, entropy_def, entropy_def] at hjoin
    exact hjoin
  -- Integrate the pointwise inequality.
  exact integral_mono_ae
    (integrable_condEntropy_integrand h𝒜 (joinCells P.cells Q.cells)
      (fun x => (P.measurable x.1).inter (Q.measurable x.2)))
    ((integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i)).add
      (integrable_condEntropy_integrand h𝒜 Q.cells (fun j => Q.measurable j)))
    hbound

end Oseledets.Entropy
