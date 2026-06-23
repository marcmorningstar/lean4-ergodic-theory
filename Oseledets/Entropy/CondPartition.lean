/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Analysis.Convex.Integral
import Oseledets.Entropy.Partition

/-!
# Conditional Shannon entropy of a finite measurable partition

This file extends the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`Oseledets.Entropy.Partition` to the **conditional** setting. Given a probability space `(α, μ)`
that is standard Borel, a sub-σ-algebra `𝒜 ≤ mα`, and a finite family of cells `s : ι → Set α`,
the conditional Shannon entropy is the `μ`-average of the pointwise entropy computed with respect
to the regular conditional probability `κ = condExpKernel μ 𝒜`:
`H(s | 𝒜) = ∫ ω, ∑ᵢ negMulLog (κ(ω) (s i)).toReal ∂μ`.

This is the information about the partition that remains after conditioning on the information in
`𝒜`. We record its three basic properties — nonnegativity, the `log k` upper bound for a genuine
partition, and the reduction to ordinary entropy when `𝒜 = ⊥` — together with the fundamental
fact that **conditioning does not increase entropy** (`condEntropy_le`), which is Jensen's
inequality for the concave function `negMulLog` applied to the disintegration of `μ`.

## Main definitions

* `Oseledets.Entropy.condEntropy`: the conditional Shannon entropy
  `∫ ω, ∑ i, negMulLog (condExpKernel μ 𝒜 ω (s i)).toReal ∂μ` of a finite family of cells.

## Main results

* `Oseledets.Entropy.condEntropy_nonneg`: conditional entropy is nonnegative.
* `Oseledets.Entropy.condEntropy_le_log_card`: a partition into `k` cells has conditional entropy
  at most `log k`.
* `Oseledets.Entropy.condEntropy_bot`: conditioning on the trivial σ-algebra `⊥` recovers the
  ordinary entropy.
* `Oseledets.Entropy.condEntropy_le`: conditioning does not increase entropy.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM 79, Chapter 4.
-/

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

/-- The conditional Shannon entropy
`∫ ω, ∑ i, negMulLog (condExpKernel μ 𝒜 ω (s i)).toReal ∂μ` of a finite family of cells
`s : ι → Set α` given a sub-σ-algebra `𝒜`. It is the `μ`-average of the pointwise entropy of `s`
computed against the regular conditional probability `condExpKernel μ 𝒜 ω`, i.e. the information
about the partition remaining after conditioning on `𝒜`. -/
noncomputable def condEntropy {mΩ : MeasurableSpace α} [Fintype ι] [StandardBorelSpace α]
    (μ : @Measure α mΩ) [IsFiniteMeasure μ] (𝒜 : MeasurableSpace α) (s : ι → Set α) : ℝ :=
  ∫ ω, (∑ i, Real.negMulLog (@condExpKernel α mΩ _ μ _ 𝒜 ω (s i)).toReal) ∂μ

omit mα [StandardBorelSpace α] in
@[simp]
lemma condEntropy_def {mΩ : MeasurableSpace α} [Fintype ι] [StandardBorelSpace α]
    (μ : @Measure α mΩ) [IsFiniteMeasure μ] (𝒜 : MeasurableSpace α) (s : ι → Set α) :
    condEntropy μ 𝒜 s
      = ∫ ω, (∑ i, Real.negMulLog (@condExpKernel α mΩ _ μ _ 𝒜 ω (s i)).toReal) ∂μ := rfl

/-- For every `ω`, the conditional probability `condExpKernel μ 𝒜 ω A` of a set `A` has real value
in `[0, 1]`, because `condExpKernel μ 𝒜 ω` is a probability measure. -/
lemma toReal_condExpKernel_le_one {μ : Measure α} [IsFiniteMeasure μ] (A : Set α) (ω : α) :
    (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal ≤ 1 := by
  have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
    IsMarkovKernel.isProbabilityMeasure ω
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := @condExpKernel α mα _ μ _ 𝒜 ω) (s := A))
  rwa [ENNReal.toReal_one] at h

/-- The pointwise integrand of `condEntropy` is nonnegative: for every `ω` each cell has
conditional probability in `[0, 1]` (the kernel is Markov), where `negMulLog` is nonnegative. -/
lemma negMulLog_condExpKernel_sum_nonneg [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ]
    (s : ι → Set α) (ω : α) :
    0 ≤ ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (s i)).toReal :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg ENNReal.toReal_nonneg (toReal_condExpKernel_le_one (s i) ω)

/-- Conditional Shannon entropy is nonnegative: the integrand is pointwise nonnegative because each
conditional cell probability lies in `[0, 1]`. -/
lemma condEntropy_nonneg [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ] {s : ι → Set α} :
    0 ≤ condEntropy μ 𝒜 s := by
  rw [condEntropy_def]
  exact integral_nonneg fun ω => negMulLog_condExpKernel_sum_nonneg s ω

/-- Integrability of the single term `ω ↦ negMulLog (condExpKernel μ 𝒜 ω A).toReal`: the function
is measurable (composition of the continuous `negMulLog` with the measurable conditional
probability) and bounded by `1`, hence integrable on the finite measure `μ`. -/
lemma integrable_negMulLog_condExpKernel {μ : Measure α} [IsFiniteMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    {A : Set α} (hA : MeasurableSet A) :
    Integrable (fun ω => Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal) μ := by
  have hmeas : AEStronglyMeasurable
      (fun ω => Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal) μ := by
    have h1 : Measurable[mα] fun ω => @condExpKernel α mα _ μ _ 𝒜 ω A :=
      (measurable_condExpKernel hA).mono h𝒜 le_rfl
    exact Real.continuous_negMulLog.comp_aestronglyMeasurable
      h1.ennreal_toReal.aestronglyMeasurable
  refine Integrable.of_bound hmeas 1 (Eventually.of_forall fun ω => ?_)
  have h01 : (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal ≤ 1 := toReal_condExpKernel_le_one A ω
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.negMulLog_nonneg ENNReal.toReal_nonneg h01)]
  calc Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal
      ≤ 1 - (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal :=
        Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg
    _ ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := @condExpKernel α mα _ μ _ 𝒜 ω A)]

/-- The integrand `ω ↦ ∑ i, negMulLog (condExpKernel μ 𝒜 ω (s i)).toReal` of `condEntropy` is
`μ`-integrable, as a finite sum of integrable single terms. -/
lemma integrable_condEntropy_integrand [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    Integrable (fun ω => ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (s i)).toReal) μ :=
  integrable_finsetSum _ fun i _ => integrable_negMulLog_condExpKernel h𝒜 (hs i)

/-- For a finite measurable partition `P` of the probability space and `μ`-almost every `ω`, the
conditional probabilities of the cells under `condExpKernel μ 𝒜 ω` sum to `1`.

The cells are measurable, cover the whole space, and are `μ`-a.e. disjoint; the last fact transfers
to the conditional kernel via the disintegration `condExpKernel μ 𝒜 ∘ₘ μ.trim h𝒜 = μ`, so for a.e.
`ω` the cells are `condExpKernel μ 𝒜 ω`-a.e. disjoint and the kernel — being Markov — distributes
its total mass `1` over them. -/
lemma condExpKernel_sum_toReal_measure_eq_one [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    ∀ᵐ ω ∂μ, ∑ i, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal = 1 := by
  -- Kernel-level a.e.-disjointness of every pair of cells, transferred from `μ` via the
  -- disintegration `condExpKernel μ 𝒜 ∘ₘ μ.trim h𝒜 = μ`.
  have hdisj : ∀ᵐ ω ∂μ, ∀ i j, i ≠ j →
      @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i ∩ P.cells j) = 0 := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    refine eventually_imp_distrib_left.2 fun hij => ?_
    -- `μ (Pᵢ ∩ Pⱼ) = 0`, i.e. a.e. `ω` avoids `Pᵢ ∩ Pⱼ`; push through the kernel composition.
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
  filter_upwards [hdisj] with ω hω
  -- For this `ω`, sum the kernel measures of the cells over the (a.e.-disjoint, covering) family.
  have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
    IsMarkovKernel.isProbabilityMeasure ω
  have hadd : @condExpKernel α mα _ μ _ 𝒜 ω (⋃ i ∈ (Finset.univ : Finset ι), P.cells i)
      = ∑ i, @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i) :=
    measure_biUnion_finset₀
      (fun i _ j _ hij => hω i j hij)
      (fun i _ => (P.measurable i).nullMeasurableSet)
  simp only [Finset.mem_univ, Set.iUnion_true] at hadd
  rw [P.cover, measure_univ] at hadd
  have hfin : ∀ i, @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i) ≠ ⊤ :=
    fun i => measure_ne_top _ (P.cells i)
  rw [← ENNReal.toReal_sum (fun i _ => hfin i), ← hadd, ENNReal.toReal_one]

/-- **Conditional version of Proposition 1 (Le Maître).** A finite measurable partition of a
probability space into `k` cells has conditional Shannon entropy at most `log k`.

For `μ`-almost every `ω` the cell probabilities under `condExpKernel μ 𝒜 ω` sum to `1`, so the
pointwise entropy is bounded by `log k` via the existing Jensen bound `entropy_le_log_card`;
integrating this constant bound over the probability measure `μ` yields the claim. -/
lemma condEntropy_le_log_card [Fintype ι] [Nonempty ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    condEntropy μ 𝒜 P.cells ≤ Real.log (Fintype.card ι) := by
  rw [condEntropy_def]
  have hbound : ∀ᵐ ω ∂μ,
      (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal)
        ≤ Real.log (Fintype.card ι) := by
    filter_upwards [condExpKernel_sum_toReal_measure_eq_one h𝒜 P] with ω hω
    have := entropy_le_log_card (μ := @condExpKernel α mα _ μ _ 𝒜 ω) P.cells hω
    rwa [entropy_def] at this
  calc
    ∫ ω, (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal) ∂μ
        ≤ ∫ _ω, Real.log (Fintype.card ι) ∂μ :=
          integral_mono_ae
            (integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i))
            (integrable_const _) hbound
    _ = Real.log (Fintype.card ι) := by
          rw [integral_const, probReal_univ, one_smul]

/-- Conditioning on the trivial σ-algebra `⊥` recovers the ordinary Shannon entropy: the
conditional probability `condExpKernel μ ⊥ ω (s i)` equals the unconditional probability `μ (s i)`
for `μ`-almost every `ω`, so the integrand is a.e. the constant `entropy μ s`. -/
lemma condEntropy_bot [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {s : ι → Set α}
    (hs : ∀ i, MeasurableSet (s i)) :
    condEntropy μ ⊥ s = entropy μ s := by
  rw [condEntropy_def, entropy_def]
  -- For each `i`, the conditional cell probability is a.e. the unconditional one.
  have hcell : ∀ i, (fun ω => (@condExpKernel α mα _ μ _ ⊥ ω (s i)).toReal)
      =ᵐ[μ] fun _ => (μ (s i)).toReal := by
    intro i
    have h1 := condExpKernel_ae_eq_condExp (μ := μ) (m := ⊥) bot_le (hs i)
    have h2 : μ⟦s i | ⊥⟧ = fun _ => ∫ x, (s i).indicator (fun _ => (1 : ℝ)) x ∂μ :=
      condExp_bot _
    filter_upwards [h1] with ω hω
    rw [measureReal_def] at hω
    rw [hω, h2, integral_indicator (hs i), setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  -- Hence the whole integrand is a.e. the constant `entropy μ s`.
  have hsum : (fun ω => ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ ⊥ ω (s i)).toReal)
      =ᵐ[μ] fun _ => ∑ i, Real.negMulLog (μ (s i)).toReal := by
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    exact Finset.sum_congr rfl fun i _ => by rw [hω i]
  rw [integral_congr_ae hsum, integral_const, probReal_univ, one_smul]

/-- The disintegration identity `∫ ω, (condExpKernel μ 𝒜 ω A).toReal ∂μ = (μ A).toReal`:
the `μ`-average of the conditional probability of a measurable set recovers its unconditional
probability, by the law of total probability (`condExpKernel_ae_eq_condExp` and `integral_condExp`
applied to the indicator of the set). -/
lemma integral_condExpKernel_toReal {μ : Measure α} [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    {A : Set α} (hA : MeasurableSet A) :
    ∫ ω, (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal ∂μ = (μ A).toReal := by
  have hae : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal) =ᵐ[μ] μ⟦A | 𝒜⟧ := by
    have h := condExpKernel_ae_eq_condExp (μ := μ) (m := 𝒜) h𝒜 hA
    simpa only [measureReal_def] using h
  rw [integral_congr_ae hae, integral_condExp h𝒜, integral_indicator hA, setIntegral_const,
    smul_eq_mul, mul_one, measureReal_def]

/-- **Conditioning does not increase entropy.** For any finite measurable partition `P` of the
probability space and any sub-σ-algebra `𝒜`, the conditional entropy is at most the unconditional
entropy.

This is Jensen's inequality (`ConcaveOn.le_map_integral`) for the concave function `negMulLog`,
applied term by term: for each cell `Pᵢ`, the average of `negMulLog (κ(ω) Pᵢ).toReal` is at most
`negMulLog` of the average `∫ ω, (κ(ω) Pᵢ).toReal ∂μ`, which equals `negMulLog (μ Pᵢ).toReal` by the
disintegration `integral_condExpKernel_toReal`. Summing over `i` gives the bound. -/
lemma condEntropy_le [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    (P : MeasurePartition μ ι) :
    condEntropy μ 𝒜 P.cells ≤ entropy μ P.cells := by
  rw [condEntropy_def, entropy_def]
  -- Move the integral inside the finite sum.
  rw [integral_finsetSum _
    (fun i _ => integrable_negMulLog_condExpKernel h𝒜 (P.measurable i))]
  refine Finset.sum_le_sum fun i _ => ?_
  -- Jensen for the concave `negMulLog` over `Set.Ici 0` against the probability measure `μ`.
  have hfi : Integrable (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal) μ :=
    integrable_toReal_condExpKernel (P.measurable i)
  have hgi : Integrable
      (fun ω => Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal) μ :=
    integrable_negMulLog_condExpKernel h𝒜 (P.measurable i)
  have hfs : ∀ᵐ ω ∂μ, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal ∈ Set.Ici (0 : ℝ) :=
    Eventually.of_forall fun ω => Set.mem_Ici.mpr ENNReal.toReal_nonneg
  have hjensen :
      (∫ ω, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal ∂μ)
        ≤ Real.negMulLog (∫ ω, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal ∂μ) :=
    Real.concaveOn_negMulLog.le_map_integral
      Real.continuous_negMulLog.continuousOn isClosed_Ici hfs hfi hgi
  rwa [integral_condExpKernel_toReal h𝒜 (P.measurable i)] at hjensen

end Oseledets.Entropy
