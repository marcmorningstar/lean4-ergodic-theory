/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.CondPartition
import Oseledets.Entropy.CondExpEquivariant
import Oseledets.Entropy.CondPullback

/-!
# Joint pull-back of conditional entropy (issue #13, lemma B4)

This file proves the **joint change of variables** for conditional entropy: for a
measure-preserving map `S` (in the application `S = T^[n]`), pulling back BOTH the partition
`P` AND the conditioning σ-algebra `𝒜` by the *same* map leaves the conditional entropy
unchanged:
```
H(S⁻¹P | S⁻¹𝒜) = H(P | 𝒜),
```
where `S⁻¹𝒜` is the comap σ-algebra `MeasurableSpace.comap S 𝒜`.

This is distinct from `condEntropy_pullback` (`Oseledets.Entropy.CondPullback`), which fixes the
conditioning σ-algebra `𝒜` and therefore needs the *two-sided* invariance hypotheses
(`𝒜/𝒜`-measurability of `T` and the pull-back surjectivity). Here, conditioning on the *pulled
back* σ-algebra `comap S 𝒜` makes every hypothesis automatic: a `comap S 𝒜`-set is *literally*
`S ⁻¹' A'` for an `𝒜`-set `A'` (`MeasurableSpace.measurableSet_comap`), and `S` is automatically
`comap S 𝒜 / 𝒜`-measurable. No two-sided assumption is required.

## Main results

* `Oseledets.Entropy.condExp_indicator_preimage_comap`: conditional-expectation equivariance for the
  comap σ-algebra, `μ⟦S⁻¹B | comap S 𝒜⟧ =ᵐ[μ] (μ⟦B | 𝒜⟧) ∘ S`, with NO two-sided hypothesis.
* `Oseledets.Entropy.condExpKernel_preimage_comap_toReal_ae_eq`: the kernel-level form
  `(κ_{comap S 𝒜}(ω, S⁻¹B)).toReal =ᵐ[μ] (κ_𝒜(S ω, B)).toReal`.
* `Oseledets.Entropy.condEntropy_comap_preimage`: the single-map joint pull-back
  `H(S⁻¹P | comap S 𝒜) = H(P | 𝒜)`.
* `Oseledets.Entropy.condEntropy_comap_pullback`: the iterated form for `S = T^[n]`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

section JointPullback

variable {T : α → α}

omit [StandardBorelSpace α] in
/-- **(★) Conditional-expectation equivariance for the comap σ-algebra.** For a measure-preserving
`S : α → α`, a sub-σ-algebra `𝒜 ≤ mα`, and a measurable set `B`,
```
μ⟦S ⁻¹' B | comap S 𝒜⟧  =ᵐ[μ]  (μ⟦B | 𝒜⟧) ∘ S.
```

Unlike `condExp_indicator_preimage_comp`, this needs NO two-sided invariance hypothesis: a
`comap S 𝒜`-set is *literally* `S ⁻¹' A'` for an `𝒜`-set `A'`
(`MeasurableSpace.measurableSet_comap`), so the set-integral identity that characterises the
conditional expectation holds by the measure-preserving change of variables alone. The candidate
`g := (μ⟦B | 𝒜⟧) ∘ S` is `comap S 𝒜`-strongly-measurable because `S` is automatically
`comap S 𝒜 / 𝒜`-measurable. -/
theorem condExp_indicator_preimage_comap {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hS : @MeasurePreserving α α mα mα T μ μ)
    {B : Set α} (hB : @MeasurableSet α mα B) :
    (μ⟦T ⁻¹' B | MeasurableSpace.comap T 𝒜⟧) =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) := by
  classical
  -- The comap σ-algebra is dominated by the ambient one (`S` is measurable).
  have hcm : MeasurableSpace.comap T 𝒜 ≤ mα := fun s ⟨A', hA', hA'eq⟩ =>
    hA'eq ▸ hS.measurable (hm A' hA')
  -- `S` is `comap S 𝒜 / 𝒜`-measurable: every `𝒜`-set pulls back into `comap S 𝒜`.
  have hSA : @Measurable α α (MeasurableSpace.comap T 𝒜) 𝒜 T :=
    fun A' hA' => ⟨A', hA', rfl⟩
  have hTB : @MeasurableSet α mα (T ⁻¹' B) :=
    measurableSet_preimage_of_measurePreserving (mΩ := mα) hS hB
  -- `𝟙_{S⁻¹B} = 𝟙_B ∘ S`
  have hind : Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ))
      = fun ω => Set.indicator B (fun _ => (1 : ℝ)) (T ω) := by
    funext ω
    by_cases hω : T ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  have hfintB : Integrable (Set.indicator B (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hfintTB : Integrable (Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hTB
  -- `g := (μ⟦B | 𝒜⟧) ∘ S` is the candidate.
  set g : α → ℝ := fun ω => (μ⟦B | 𝒜⟧) (T ω) with hg
  have hgSM : StronglyMeasurable[MeasurableSpace.comap T 𝒜] g :=
    (stronglyMeasurable_condExp).comp_measurable hSA
  have hgint : Integrable g μ := integrable_comp_self (mΩ := mα) hS integrable_condExp
  have : SigmaFinite (μ.trim hcm) := inferInstance
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hcm hfintTB
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => ?_) hgSM.aestronglyMeasurable
  -- A `comap S 𝒜`-set `s` is literally `S ⁻¹' A'` for an `𝒜`-set `A'`.
  obtain ⟨A', hA'mem, hA'eq⟩ := hs
  have hA'meas : @MeasurableSet α mα A' := hm A' hA'mem
  -- LHS: ∫_{S⁻¹A'} g = ∫_{A'} μ⟦B|𝒜⟧  (change of variables on the preimage).
  have hL : ∫ ω in s, g ω ∂μ = ∫ ω in A', (μ⟦B | 𝒜⟧) ω ∂μ := by
    rw [← hA'eq, hg]
    exact setIntegral_comp_preimage (mΩ := mα) hS
      integrable_condExp.aestronglyMeasurable hA'meas
  -- ∫_{A'} μ⟦B|𝒜⟧ = ∫_{A'} 𝟙_B   (defining property of condExp on 𝒜-sets).
  have hcond : ∫ ω in A', (μ⟦B | 𝒜⟧) ω ∂μ
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂μ :=
    setIntegral_condExp hm hfintB hA'mem
  -- RHS: ∫_{S⁻¹A'} 𝟙_{S⁻¹B} = ∫_{S⁻¹A'} (𝟙_B ∘ S) = ∫_{A'} 𝟙_B.
  have hR : ∫ ω in s, Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ)) ω ∂μ
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [← hA'eq, hind]
    exact setIntegral_comp_preimage (mΩ := mα) hS hfintB.aestronglyMeasurable hA'meas
  rw [hL, hcond, hR]

/-- **Kernel equivariance for the comap σ-algebra.** For a measure-preserving `S : α → α`, a
sub-σ-algebra `𝒜 ≤ mα`, and a measurable set `B`,
```
(κ_{comap S 𝒜}(ω, S⁻¹B)).toReal  =ᵐ[μ]  (κ_𝒜(S ω, B)).toReal,
```
where `κ_𝒜 = condExpKernel μ 𝒜`. The proof bridges each kernel to a conditional expectation via
`condExpKernel_ae_eq_condExp`, applies the comap equivariance `condExp_indicator_preimage_comap`,
and transports the `B`-side identity through the measure-preserving change of variables with
`Measure.QuasiMeasurePreserving.ae_eq_comp`. -/
theorem condExpKernel_preimage_comap_toReal_ae_eq {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hS : @MeasurePreserving α α mα mα T μ μ)
    {B : Set α} (hB : @MeasurableSet α mα B) :
    (fun ω => (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' B)).toReal)
      =ᵐ[μ] fun ω => (@condExpKernel α mα _ μ _ 𝒜 (T ω) B).toReal := by
  have hcm : MeasurableSpace.comap T 𝒜 ≤ mα := fun s ⟨A', hA', hA'eq⟩ =>
    hA'eq ▸ hS.measurable (hm A' hA')
  have hTB : @MeasurableSet α mα (T ⁻¹' B) :=
    measurableSet_preimage_of_measurePreserving (mΩ := mα) hS hB
  -- κ_{comap S 𝒜}(·, S⁻¹B).toReal =ᵐ μ⟦S⁻¹B | comap S 𝒜⟧
  have h1 : (fun ω => (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' B)).toReal)
      =ᵐ[μ] μ⟦T ⁻¹' B | MeasurableSpace.comap T 𝒜⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp hcm hTB
  -- μ⟦S⁻¹B | comap S 𝒜⟧ =ᵐ (μ⟦B | 𝒜⟧) ∘ S   (the comap equivariance)
  have h2 : (μ⟦T ⁻¹' B | MeasurableSpace.comap T 𝒜⟧) =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) :=
    condExp_indicator_preimage_comap hm hS hB
  -- κ_𝒜(·, B).toReal =ᵐ μ⟦B | 𝒜⟧, transported through `S`.
  have h3 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω B).toReal) =ᵐ[μ] μ⟦B | 𝒜⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp hm hB
  have h4 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 (T ω) B).toReal)
      =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) :=
    hS.quasiMeasurePreserving.ae_eq_comp h3
  exact (h1.trans h2).trans h4.symm

/-- **Joint pull-back of conditional entropy (single map).** For a measure-preserving `S : α → α`
and a sub-σ-algebra `𝒜 ≤ mα`, pulling back BOTH the finite partition `P` and the conditioning
σ-algebra `𝒜` by the *same* map `S` leaves the conditional entropy unchanged:
```
H(S⁻¹P | comap S 𝒜) = H(P | 𝒜).
```

The `condEntropy` integrand at `(S⁻¹P, comap S 𝒜)` is, by the comap kernel equivariance
`condExpKernel_preimage_comap_toReal_ae_eq` applied to each cell, `μ`-a.e. equal to the integrand
at `(P, 𝒜)` precomposed with `S`; the measure-preserving change of variables `integral_comp_self`
then leaves the integral unchanged. No two-sided invariance hypothesis is needed. -/
theorem condEntropy_comap_preimage [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hS : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) :
    condEntropy μ (MeasurableSpace.comap T 𝒜) (fun i => T ⁻¹' P.cells i)
      = condEntropy μ 𝒜 P.cells := by
  rw [condEntropy_def, condEntropy_def]
  -- The pulled-back integrand is a.e. the original integrand precomposed with `S`.
  have hae : (fun ω => ∑ i, Real.negMulLog
        (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' P.cells i)).toReal)
      =ᵐ[μ] fun ω => (fun ω' => ∑ i, Real.negMulLog
        (@condExpKernel α mα _ μ _ 𝒜 ω' (P.cells i)).toReal) (T ω) := by
    have hcell : ∀ i, (fun ω => Real.negMulLog
          (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' P.cells i)).toReal)
        =ᵐ[μ] fun ω => Real.negMulLog
          (@condExpKernel α mα _ μ _ 𝒜 (T ω) (P.cells i)).toReal := by
      intro i
      filter_upwards [condExpKernel_preimage_comap_toReal_ae_eq hm hS (P.measurable i)]
        with ω hω
      rw [hω]
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    exact Finset.sum_congr rfl fun i _ => hω i
  rw [integral_congr_ae hae]
  -- Change of variables: `∫ g(S ω) dμ = ∫ g dμ`.
  exact integral_comp_self (mΩ := mα) hS
    (integrable_condEntropy_integrand hm P.cells (fun i => P.measurable i)).aestronglyMeasurable

/-- **Joint pull-back of conditional entropy (iterated form).** For a measure-preserving
`T : α → α`, a sub-σ-algebra `𝒜 ≤ mα`, and `n : ℕ`, pulling back BOTH the finite partition `P`
and the conditioning σ-algebra `𝒜` by `T^[n]` leaves the conditional entropy unchanged:
```
H(T⁻ⁿP | comap (T^[n]) 𝒜) = H(P | 𝒜).
```

This is `condEntropy_comap_preimage` applied to the measure-preserving iterate `T^[n]`
(`MeasurePreserving.iterate`). Unlike `condEntropy_pullback_iterate`, no two-sided invariance
hypothesis (`𝒜/𝒜`-measurability or pull-back surjectivity of `T`) is required, because the
conditioning σ-algebra is itself pulled back along `T^[n]`. -/
theorem condEntropy_comap_pullback [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ) (n : ℕ)
    (P : MeasurePartition μ ι) :
    condEntropy μ (MeasurableSpace.comap (T^[n]) 𝒜) (fun i => (T^[n]) ⁻¹' P.cells i)
      = condEntropy μ 𝒜 P.cells :=
  condEntropy_comap_preimage hm (hT.iterate n) P

end JointPullback

end Oseledets.Entropy
