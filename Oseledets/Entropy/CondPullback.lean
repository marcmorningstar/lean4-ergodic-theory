/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.CondPartition
import Oseledets.Entropy.CondExpEquivariant
import Oseledets.Entropy.Subadditive2

/-!
# Subadditivity and invariance of conditional entropy

This file is the next layer of the conditional-entropy milestone (GitHub issue #13). It continues
`Oseledets.Entropy.CondPartition` (which defines `condEntropy μ 𝒜 s`, the `μ`-average of the
pointwise entropy against the regular conditional probability `condExpKernel μ 𝒜 ω`) and
`Oseledets.Entropy.CondExpEquivariant` (the two-sided conditional-expectation equivariance `(★)`).

Two structural facts about conditional entropy are established:

* **Subadditivity under joins** (`condEntropy_join_le`): for partitions `P` and `Q`,
  `H(P ∨ Q | 𝒜) ≤ H(P | 𝒜) + H(Q | 𝒜)`. This is proved by running the absolute argument
  (`entropy_join_le`) *pointwise inside the integral* against the Markov-kernel measure
  `condExpKernel μ 𝒜 ω`, which for `μ`-a.e. `ω` is a probability measure for which `P` and `Q` are
  still genuine measurable partitions; the resulting pointwise bound integrates termwise.

* **Invariance under a measure-preserving factor** (`condEntropy_pullback` and its iterate):
  for a measure-preserving `T : α → α` satisfying the *two-sided* invariance hypotheses (`T` is
  `𝒜/𝒜`-measurable and every `𝒜`-set is `μ`-a.e. a `T`-preimage of an `𝒜`-set),
  `H(T⁻¹P | 𝒜) = H(P | 𝒜)`, and the iterated version `H(T⁻ⁿP | 𝒜) = H(P | 𝒜)`. The proof bridges
  the conditional kernel to the conditional expectation (`condExpKernel_ae_eq_condExp`), invokes the
  equivariance `(★)` (`condExp_indicator_preimage_comp`), and finishes with the measure-preserving
  change of variables `integral_comp_self`.

The two-sided hypotheses are necessary: a prior analysis exhibited an explicit non-invertible Markov
factor for which the one-sided hypothesis `comap T 𝒜 ≤ 𝒜` makes `condEntropy_pullback` false.

## Main results

* `Oseledets.Entropy.condEntropy_sum_eq_one`: a.e. normalization of the conditional cell
  probabilities of a partition.
* `Oseledets.Entropy.condExpKernel_sum_inter_toReal`: the conditional marginal identity
  `∑ⱼ (κ(ω, Pᵢ ∩ Qⱼ)).toReal = (κ(ω, Pᵢ)).toReal` (a.e.).
* `Oseledets.Entropy.condEntropy_join_le`: subadditivity of conditional entropy under joins.
* `Oseledets.Entropy.condEntropy_pullback`: invariance of conditional entropy under a two-sided
  measure-preserving factor.
* `Oseledets.Entropy.condEntropy_pullback_iterate`: the iterated invariance
  `H(T⁻ⁿP | 𝒜) = H(P | 𝒜)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Entropy

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

/-- For a finite measurable partition `P` of the probability space and `μ`-almost every `ω`, the
conditional cell probabilities under `condExpKernel μ 𝒜 ω` sum to `1`. This is a re-export of
`condExpKernel_sum_toReal_measure_eq_one`. -/
lemma condEntropy_sum_eq_one [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    (P : MeasurePartition μ ι) :
    ∀ᵐ ω ∂μ, ∑ i, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal = 1 :=
  condExpKernel_sum_toReal_measure_eq_one h𝒜 P

/-- **Conditional marginal identity.** For partitions `P` (indexed by `ι`) and `Q` (indexed by `κ`)
of the probability space, the conditional kernel measures of the join cells `Pᵢ ∩ Qⱼ` sum, over the
column index `j`, to the conditional kernel measure of `Pᵢ`, for `μ`-almost every `ω`.

This is the conditional (kernel-level) analogue of `MeasurePartition.measure_eq_sum_inter`. It
follows from finite additivity of the probability measure `condExpKernel μ 𝒜 ω` over the family
`(Pᵢ ∩ Qⱼ)ⱼ`, whose union is `Pᵢ` (since the cells of `Q` cover the space) and whose members are
`condExpKernel μ 𝒜 ω`-a.e. disjoint; the a.e.-disjointness is transferred from `μ` through the
disintegration `condExpKernel μ 𝒜 ∘ₘ μ.trim h𝒜 = μ`. -/
lemma condExpKernel_sum_inter_toReal [Fintype ι] [Fintype κ] {μ : Measure α}
    [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    ∀ᵐ ω ∂μ, ∀ i, ∑ j, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i ∩ Q.cells j)).toReal
      = (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal := by
  -- Kernel-level a.e.-disjointness of `Pᵢ ∩ Qⱼ` and `Pᵢ ∩ Qⱼ'` (for `j ≠ j'`), transferred from
  -- `μ` via the disintegration `condExpKernel μ 𝒜 ∘ₘ μ.trim h𝒜 = μ`.
  have hdisj : ∀ᵐ ω ∂μ, ∀ i j j', j ≠ j' →
      @condExpKernel α mα _ μ _ 𝒜 ω ((P.cells i ∩ Q.cells j) ∩ (P.cells i ∩ Q.cells j')) = 0 := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro j'
    refine eventually_imp_distrib_left.2 fun hjj' => ?_
    have hsub : (P.cells i ∩ Q.cells j) ∩ (P.cells i ∩ Q.cells j') ⊆ Q.cells j ∩ Q.cells j' :=
      fun x hx => ⟨hx.1.2, hx.2.2⟩
    have hμ0 : μ ((P.cells i ∩ Q.cells j) ∩ (P.cells i ∩ Q.cells j')) = 0 :=
      measure_mono_null hsub (Q.aedisjoint hjj')
    have hμ : ∀ᵐ ω ∂μ, ω ∉ (P.cells i ∩ Q.cells j) ∩ (P.cells i ∩ Q.cells j') := by
      rw [ae_iff]; simpa using hμ0
    have hμ2 : ∀ᵐ ω ∂(@condExpKernel α mα _ μ _ 𝒜 ∘ₘ μ.trim h𝒜),
        ω ∉ (P.cells i ∩ Q.cells j) ∩ (P.cells i ∩ Q.cells j') := by
      rw [condExpKernel_comp_trim h𝒜]; exact hμ
    have hae := Measure.ae_ae_of_ae_comp hμ2
    refine ae_of_ae_trim h𝒜 ?_
    filter_upwards [hae] with ω hω
    simpa using ae_iff.mp hω
  filter_upwards [hdisj] with ω hω i
  -- For this `ω` and `i`, sum the kernel measures over the a.e.-disjoint cover of `Pᵢ`.
  have hcover : P.cells i = ⋃ j ∈ (Finset.univ : Finset κ), P.cells i ∩ Q.cells j := by
    simp only [Finset.mem_univ, Set.iUnion_true, ← Set.inter_iUnion, Q.cover, Set.inter_univ]
  have hadd : @condExpKernel α mα _ μ _ 𝒜 ω (⋃ j ∈ (Finset.univ : Finset κ), P.cells i ∩ Q.cells j)
      = ∑ j, @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i ∩ Q.cells j) :=
    measure_biUnion_finset₀
      (fun j _ j' _ hjj' => hω i j j' hjj')
      (fun j _ => ((P.measurable i).inter (Q.measurable j)).nullMeasurableSet)
  rw [← hcover] at hadd
  have hfin : ∀ j, @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i ∩ Q.cells j) ≠ ⊤ :=
    fun j => measure_ne_top _ _
  rw [← ENNReal.toReal_sum (fun j _ => hfin j), ← hadd]

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

section Pullback

variable {T : α → α}

/-- **Kernel equivariance.** Under the two-sided invariance hypotheses, for a measurable set `B` the
conditional kernel probability of the `T`-preimage `T⁻¹B` is `μ`-a.e. the conditional kernel
probability of `B` evaluated at `T ω`:
`(κ(ω, T⁻¹B)).toReal =ᵐ[μ] (κ(Tω, B)).toReal`.

The proof bridges the kernel to the conditional expectation via `condExpKernel_ae_eq_condExp`,
applies the conditional-expectation equivariance `(★)` (`condExp_indicator_preimage_comp`), and
transports the kernel-side identity for `B` through the measure-preserving change of variables with
`Measure.QuasiMeasurePreserving.ae_eq_comp`. -/
lemma condExpKernel_preimage_toReal_ae_eq {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ) (hTA : @Measurable α α 𝒜 𝒜 T)
    (hpull : ∀ A : Set α, MeasurableSet[𝒜] A →
      ∃ A' : Set α, MeasurableSet[𝒜] A' ∧ A =ᵐ[μ] T ⁻¹' A')
    {B : Set α} (hB : @MeasurableSet α mα B) :
    (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (T ⁻¹' B)).toReal)
      =ᵐ[μ] fun ω => (@condExpKernel α mα _ μ _ 𝒜 (T ω) B).toReal := by
  have hTB : @MeasurableSet α mα (T ⁻¹' B) :=
    measurableSet_preimage_of_measurePreserving (mΩ := mα) hT hB
  -- κ(·, T⁻¹B).toReal =ᵐ μ⟦T⁻¹B | 𝒜⟧
  have h1 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (T ⁻¹' B)).toReal)
      =ᵐ[μ] μ⟦T ⁻¹' B | 𝒜⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp h𝒜 hTB
  -- μ⟦T⁻¹B | 𝒜⟧ =ᵐ (μ⟦B | 𝒜⟧) ∘ T   (the (★) equivariance)
  have h2 : (μ⟦T ⁻¹' B | 𝒜⟧) =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) :=
    condExp_indicator_preimage_comp h𝒜 hT hTA hpull hB
  -- κ(·, B).toReal =ᵐ μ⟦B | 𝒜⟧, transported through `T`.
  have h3 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω B).toReal) =ᵐ[μ] μ⟦B | 𝒜⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp h𝒜 hB
  have h4 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 (T ω) B).toReal)
      =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) :=
    hT.quasiMeasurePreserving.ae_eq_comp h3
  exact (h1.trans h2).trans h4.symm

omit [StandardBorelSpace α] in
/-- Iterating the two-sided pull-back hypothesis. If every `𝒜`-set is `μ`-a.e. a `T`-preimage of an
`𝒜`-set, then every `𝒜`-set is `μ`-a.e. a `T^[n]`-preimage of an `𝒜`-set, for every `n`. The
inductive step composes the `n`-fold preimage of the chosen `𝒜`-witness with one more application of
the hypothesis, transported through the measure-preserving `T`. -/
lemma hpull_iterate {μ : Measure α} (hT : @MeasurePreserving α α mα mα T μ μ)
    (hpull : ∀ A : Set α, MeasurableSet[𝒜] A →
      ∃ A' : Set α, MeasurableSet[𝒜] A' ∧ A =ᵐ[μ] T ⁻¹' A') :
    ∀ n, ∀ A : Set α, MeasurableSet[𝒜] A →
      ∃ A' : Set α, MeasurableSet[𝒜] A' ∧ A =ᵐ[μ] (T^[n]) ⁻¹' A' := by
  intro n
  induction n with
  | zero => intro A hA; exact ⟨A, hA, by simp⟩
  | succ n ih =>
    intro A hA
    obtain ⟨A₁, hA₁mem, hA₁eq⟩ := hpull A hA
    obtain ⟨A₂, hA₂mem, hA₂eq⟩ := ih A₁ hA₁mem
    refine ⟨A₂, hA₂mem, ?_⟩
    -- A =ᵐ T⁻¹A₁ =ᵐ T⁻¹((T^[n])⁻¹A₂) = (T^[n+1])⁻¹A₂
    have hstep : (T ⁻¹' A₁ : Set α) =ᵐ[μ] T ⁻¹' ((T^[n]) ⁻¹' A₂) :=
      hT.quasiMeasurePreserving.preimage_ae_eq hA₂eq
    refine hA₁eq.trans (hstep.trans ?_)
    rw [← Set.preimage_comp, ← Function.iterate_succ]

/-- **Invariance of conditional entropy under a two-sided measure-preserving factor.** For a
measure-preserving `T : α → α` that is `𝒜/𝒜`-measurable and satisfies the two-sided pull-back
hypothesis (every `𝒜`-set is `μ`-a.e. a `T`-preimage of an `𝒜`-set), the conditional entropy of the
pulled-back partition `T⁻¹P` equals that of `P`:
`H(T⁻¹P | 𝒜) = H(P | 𝒜)`.

The `condEntropy` integrand at `T⁻¹P` is, by the kernel equivariance
`condExpKernel_preimage_toReal_ae_eq` applied to each (measurable) cell, `μ`-a.e. equal to the
integrand at `P` precomposed with `T`; the measure-preserving change of variables
`integral_comp_self` then leaves the integral unchanged. -/
theorem condEntropy_pullback [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ) (hTA : @Measurable α α 𝒜 𝒜 T)
    (hpull : ∀ A : Set α, MeasurableSet[𝒜] A →
      ∃ A' : Set α, MeasurableSet[𝒜] A' ∧ A =ᵐ[μ] T ⁻¹' A')
    (P : MeasurePartition μ ι) :
    condEntropy μ 𝒜 (fun i => T ⁻¹' P.cells i) = condEntropy μ 𝒜 P.cells := by
  rw [condEntropy_def, condEntropy_def]
  -- The pulled-back integrand is a.e. the original integrand precomposed with `T`.
  have hae : (fun ω => ∑ i, Real.negMulLog
        (@condExpKernel α mα _ μ _ 𝒜 ω (T ⁻¹' P.cells i)).toReal)
      =ᵐ[μ] fun ω => (fun ω' => ∑ i, Real.negMulLog
        (@condExpKernel α mα _ μ _ 𝒜 ω' (P.cells i)).toReal) (T ω) := by
    have hcell : ∀ i, (fun ω => Real.negMulLog
          (@condExpKernel α mα _ μ _ 𝒜 ω (T ⁻¹' P.cells i)).toReal)
        =ᵐ[μ] fun ω => Real.negMulLog
          (@condExpKernel α mα _ μ _ 𝒜 (T ω) (P.cells i)).toReal := by
      intro i
      filter_upwards [condExpKernel_preimage_toReal_ae_eq h𝒜 hT hTA hpull (P.measurable i)]
        with ω hω
      rw [hω]
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    exact Finset.sum_congr rfl fun i _ => hω i
  rw [integral_congr_ae hae]
  -- Change of variables: `∫ g(T ω) dμ = ∫ g dμ`.
  exact integral_comp_self (mΩ := mα) hT
    (integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i)).aestronglyMeasurable

/-- **Iterated invariance of conditional entropy.** For a measure-preserving `T` satisfying the
two-sided invariance hypotheses, the conditional entropy of the `n`-fold pulled-back partition
`T^[n]⁻¹P` equals that of `P`:
`H(T⁻ⁿP | 𝒜) = H(P | 𝒜)`.

The hypotheses are iteration-stable: `T^[n]` is again measure-preserving
(`MeasurePreserving.iterate`) and `𝒜/𝒜`-measurable (`Measurable.iterate`), and `hpull_iterate` lifts
the pull-back hypothesis to `T^[n]`. The claim is then `condEntropy_pullback` applied to `T^[n]`. -/
theorem condEntropy_pullback_iterate [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ) (hTA : @Measurable α α 𝒜 𝒜 T)
    (hpull : ∀ A : Set α, MeasurableSet[𝒜] A →
      ∃ A' : Set α, MeasurableSet[𝒜] A' ∧ A =ᵐ[μ] T ⁻¹' A')
    (n : ℕ) (P : MeasurePartition μ ι) :
    condEntropy μ 𝒜 (fun i => (T^[n]) ⁻¹' P.cells i) = condEntropy μ 𝒜 P.cells :=
  condEntropy_pullback h𝒜 (hT.iterate n) (hTA.iterate n) (hpull_iterate hT hpull n) P

end Pullback

end Oseledets.Entropy
