/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.CondKSEntropySystem
import Oseledets.Entropy.FactorEntropy

/-!
# Conditional Kolmogorov–Sinai entropy across a measure-preserving conjugacy

This file transports the **relative** (conditional) Kolmogorov–Sinai entropy of a
measure-preserving system across a measurable conjugacy, with the two conditioning σ-algebras
matched by pull-back. It is the conditional companion of `Oseledets.Entropy.FactorEntropy`
(`factor_relative_eq`) and `Oseledets.Entropy.KSEntropyConjugacy`
(`ksEntropy_congr_of_conjugacy`), needed for the conditional-fibre vanishing of issue #21.

The crux is the **cross-space joint pull-back** of conditional entropy: for a measure-preserving
`e : α → β`, pulling back BOTH a finite partition `R` of `β` and a conditioning σ-algebra
`𝒜β ≤ mβ` along `e` leaves the conditional entropy unchanged,
```
H(e⁻¹R | comap e 𝒜β) = H(R | 𝒜β).
```
This is the two-space generalisation of `condEntropy_comap_preimage`
(`Oseledets.Entropy.CondJointPullback`); a `comap e 𝒜β`-set is *literally* `e ⁻¹' A'` for an
`𝒜β`-set `A'`, so the kernel-level change of variables needs no extra hypothesis.

## Main results

* `Oseledets.Entropy.condEntropy_comap_preimage_cross`: the cross-space joint pull-back of
  conditional Shannon entropy.
* `Oseledets.Entropy.condKsEntropyPartition_pulledBack_eq`: the conditional factor-relative entropy
  invariance, `h(e⁻¹R, T | comap e 𝒜β) = h(R, S | 𝒜β)`.
* `Oseledets.Entropy.condKsEntropy_congr_of_conjugacy`: measurable conjugacy with matched
  conditioning σ-algebras ⇒ equal relative entropy, `h(T | comap e 𝒜β) = h(S | 𝒜β)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Ch. 4.
-/

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Entropy

/-! ## Cross-space change-of-variables helpers.
These mirror `integral_comp_self`/`setIntegral_comp_preimage`
(`Oseledets.Entropy.CondExpEquivariant`), generalised from a self-map to a measure-preserving
`e : α → β` between two spaces. -/

section CrossChangeOfVariables

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {e : α → β}

/-- Cross-space change of variables: `∫ f(e ω) ∂μ = ∫ f ∂ν` for measure-preserving `e`. -/
theorem integral_comp_cross (he : MeasurePreserving e μ ν) {f : β → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    ∫ ω, f (e ω) ∂μ = ∫ ω, f ω ∂ν := by
  have hf' : AEStronglyMeasurable f (Measure.map e μ) := by rw [he.map_eq]; exact hf
  rw [← integral_map he.measurable.aemeasurable hf', he.map_eq]

/-- Cross-space change of variables on `e`-preimages of measurable sets:
`∫_{e⁻¹A'} f(e ω) ∂μ = ∫_{A'} f ∂ν`. -/
theorem setIntegral_comp_preimage_cross (he : MeasurePreserving e μ ν) {f : β → ℝ}
    (hf : AEStronglyMeasurable f ν) {A' : Set β} (hA' : MeasurableSet A') :
    ∫ ω in e ⁻¹' A', f (e ω) ∂μ = ∫ ω in A', f ω ∂ν := by
  rw [← integral_indicator (he.measurable hA'), ← integral_indicator hA']
  have hcomp : (e ⁻¹' A').indicator (fun ω => f (e ω)) = fun ω => (A'.indicator f) (e ω) := by
    funext ω
    by_cases hω : e ω ∈ A'
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  rw [hcomp]
  exact integral_comp_cross he (hf.indicator hA')

end CrossChangeOfVariables

/-! ## Conditional conjugacy transport.

The conditioning σ-algebra `𝒜β` on the target is declared BEFORE the ambient `[mα]`/`[mβ]`, so the
ambient instances keep higher resolution priority (the CLAUDE Cond*-trap, here for two spaces). -/

section CondConjugacy

variable {α β : Type*} {ιE : Type*} {𝒜β : MeasurableSpace β}
  [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [StandardBorelSpace α] [StandardBorelSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {T : α → α} {S : β → β}

omit [StandardBorelSpace α] [StandardBorelSpace β] in
/-- **Cross-space conditional-expectation equivariance.** For a measure-preserving `e : α → β`, a
sub-σ-algebra `𝒜β ≤ mβ`, and a measurable set `B`,
```
μ⟦e ⁻¹' B | comap e 𝒜β⟧  =ᵐ[μ]  (ν⟦B | 𝒜β⟧) ∘ e.
```
A `comap e 𝒜β`-set is *literally* `e ⁻¹' A'` for an `𝒜β`-set `A'`, so the set-integral identity
characterising the conditional expectation holds by the measure-preserving change of variables
`setIntegral_comp_preimage_cross` alone. Cross-space analog of `condExp_indicator_preimage_comap`
(`Oseledets.Entropy.CondJointPullback`). -/
theorem condExp_indicator_preimage_comap_cross {e : α → β}
    (hm : 𝒜β ≤ mβ) (he : MeasurePreserving e μ ν) {B : Set β} (hB : @MeasurableSet β mβ B) :
    (μ⟦e ⁻¹' B | MeasurableSpace.comap e 𝒜β⟧) =ᵐ[μ] fun ω => (ν⟦B | 𝒜β⟧) (e ω) := by
  classical
  have hcm : MeasurableSpace.comap e 𝒜β ≤ mα := fun s ⟨A', hA', hA'eq⟩ =>
    hA'eq ▸ he.measurable (hm A' hA')
  have heA : @Measurable α β (MeasurableSpace.comap e 𝒜β) 𝒜β e := fun A' hA' => ⟨A', hA', rfl⟩
  have heB : @MeasurableSet α mα (e ⁻¹' B) := he.measurable hB
  have hind : Set.indicator (e ⁻¹' B) (fun _ => (1 : ℝ))
      = fun ω => Set.indicator B (fun _ => (1 : ℝ)) (e ω) := by
    funext ω
    by_cases hω : e ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  have hfintB : Integrable (Set.indicator B (fun _ => (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator hB
  have hfinteB : Integrable (Set.indicator (e ⁻¹' B) (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator heB
  set g : α → ℝ := fun ω => (ν⟦B | 𝒜β⟧) (e ω) with hg
  have hgSM : StronglyMeasurable[MeasurableSpace.comap e 𝒜β] g :=
    (stronglyMeasurable_condExp).comp_measurable heA
  have hgint : Integrable g μ := he.integrable_comp_of_integrable integrable_condExp
  have hsfμ : SigmaFinite (μ.trim hcm) := inferInstance
  have hsfν : SigmaFinite (ν.trim hm) := inferInstance
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hcm hfinteB
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => ?_) hgSM.aestronglyMeasurable
  obtain ⟨A', hA'mem, hA'eq⟩ := hs
  have hA'meas : @MeasurableSet β mβ A' := hm A' hA'mem
  have hL : ∫ ω in s, g ω ∂μ = ∫ ω in A', (ν⟦B | 𝒜β⟧) ω ∂ν := by
    rw [← hA'eq, hg]
    exact setIntegral_comp_preimage_cross he integrable_condExp.aestronglyMeasurable hA'meas
  have hcond : ∫ ω in A', (ν⟦B | 𝒜β⟧) ω ∂ν
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂ν :=
    setIntegral_condExp hm hfintB hA'mem
  have hR : ∫ ω in s, Set.indicator (e ⁻¹' B) (fun _ => (1 : ℝ)) ω ∂μ
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂ν := by
    rw [← hA'eq, hind]
    exact setIntegral_comp_preimage_cross he hfintB.aestronglyMeasurable hA'meas
  rw [hL, hcond, hR]

/-- **Cross-space kernel equivariance for the comap σ-algebra.** For a measure-preserving
`e : α → β`, a sub-σ-algebra `𝒜β ≤ mβ`, and a measurable set `B`,
```
(condExpKernel μ (comap e 𝒜β) ω (e ⁻¹' B)).toReal  =ᵐ[μ]  (condExpKernel ν 𝒜β (e ω) B).toReal.
```
Bridges each kernel to a conditional expectation via `condExpKernel_ae_eq_condExp`, applies the
cross equivariance `condExp_indicator_preimage_comap_cross`, and transports the `B`-side identity
through the measure-preserving change of variables. -/
theorem condExpKernel_preimage_comap_toReal_ae_eq_cross {e : α → β}
    (hm : 𝒜β ≤ mβ) (he : MeasurePreserving e μ ν) {B : Set β} (hB : @MeasurableSet β mβ B) :
    (fun ω => (@condExpKernel α mα _ μ _ (MeasurableSpace.comap e 𝒜β) ω (e ⁻¹' B)).toReal)
      =ᵐ[μ] fun ω => (@condExpKernel β mβ _ ν _ 𝒜β (e ω) B).toReal := by
  have hcm : MeasurableSpace.comap e 𝒜β ≤ mα := fun s ⟨A', hA', hA'eq⟩ =>
    hA'eq ▸ he.measurable (hm A' hA')
  have heB : @MeasurableSet α mα (e ⁻¹' B) := he.measurable hB
  have h1 : (fun ω => (@condExpKernel α mα _ μ _ (MeasurableSpace.comap e 𝒜β) ω (e ⁻¹' B)).toReal)
      =ᵐ[μ] μ⟦e ⁻¹' B | MeasurableSpace.comap e 𝒜β⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp hcm heB
  have h2 : (μ⟦e ⁻¹' B | MeasurableSpace.comap e 𝒜β⟧) =ᵐ[μ] fun ω => (ν⟦B | 𝒜β⟧) (e ω) :=
    condExp_indicator_preimage_comap_cross hm he hB
  have h3 : (fun ω => (@condExpKernel β mβ _ ν _ 𝒜β ω B).toReal) =ᵐ[ν] ν⟦B | 𝒜β⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp hm hB
  have h4 : (fun ω => (@condExpKernel β mβ _ ν _ 𝒜β (e ω) B).toReal)
      =ᵐ[μ] fun ω => (ν⟦B | 𝒜β⟧) (e ω) :=
    he.quasiMeasurePreserving.ae_eq_comp h3
  exact (h1.trans h2).trans h4.symm

/-- **E0 — cross-space joint pull-back of conditional entropy.** For a measure-preserving
`e : α → β` and a sub-σ-algebra `𝒜β ≤ mβ`, pulling back BOTH the finite partition `R` of `β` and
the conditioning σ-algebra `𝒜β` along `e` leaves the conditional entropy unchanged:
```
H(e⁻¹R | comap e 𝒜β) = H(R | 𝒜β).
```
The `condEntropy` integrand at `(e⁻¹R, comap e 𝒜β)` is, by the cross kernel equivariance
`condExpKernel_preimage_comap_toReal_ae_eq_cross` applied to each cell, `μ`-a.e. equal to the
integrand at `(R, 𝒜β)` precomposed with `e`; the change of variables `integral_comp_cross` then
leaves the integral unchanged. Cross-space analog of `condEntropy_comap_preimage`. -/
theorem condEntropy_comap_preimage_cross [Fintype ιE]
    {e : α → β} (he : MeasurePreserving e μ ν) (hm : 𝒜β ≤ mβ)
    (R : MeasurePartition ν ιE) :
    condEntropy μ (MeasurableSpace.comap e 𝒜β) (fun i => e ⁻¹' R.cells i)
      = condEntropy ν 𝒜β R.cells := by
  rw [condEntropy_def, condEntropy_def]
  have hae : (fun ω => ∑ i, Real.negMulLog
        (@condExpKernel α mα _ μ _ (MeasurableSpace.comap e 𝒜β) ω (e ⁻¹' R.cells i)).toReal)
      =ᵐ[μ] fun ω => (fun ω' => ∑ i, Real.negMulLog
        (@condExpKernel β mβ _ ν _ 𝒜β ω' (R.cells i)).toReal) (e ω) := by
    have hcell : ∀ i, (fun ω => Real.negMulLog
          (@condExpKernel α mα _ μ _ (MeasurableSpace.comap e 𝒜β) ω (e ⁻¹' R.cells i)).toReal)
        =ᵐ[μ] fun ω => Real.negMulLog
          (@condExpKernel β mβ _ ν _ 𝒜β (e ω) (R.cells i)).toReal := by
      intro i
      filter_upwards [condExpKernel_preimage_comap_toReal_ae_eq_cross hm he (R.measurable i)]
        with ω hω
      rw [hω]
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    exact Finset.sum_congr rfl fun i _ => hω i
  rw [integral_congr_ae hae]
  have hint : Integrable (fun ω' => ∑ i, Real.negMulLog
      (@condExpKernel β mβ _ ν _ 𝒜β ω' (R.cells i)).toReal) ν :=
    integrable_condEntropy_integrand (μ := ν) hm R.cells (fun i => R.measurable i)
  exact integral_comp_cross he hint.aestronglyMeasurable

/-- **E1 — conditional factor-relative entropy invariance.** A conjugacy `e : α → β`
(measure-preserving, intertwining `e ∘ T = S ∘ e`) transports the partition-relative conditional
entropy of the `e`-pulled-back partition with the `e`-pulled-back conditioning σ-algebra:
```
h(e⁻¹R, T | comap e 𝒜β) = h(R, S | 𝒜β).
```
For each `n` the cells of the iterated join of `e⁻¹R` are the `e`-preimages of those of the
iterated join of `R` (`ksJoinCells_pulledBack`), so the conditional iterated-join entropy sequences
coincide via E0 (`condEntropy_comap_preimage_cross`); the subadditive sequences are equal, hence so
are their Fekete limits. Conditional mirror of `factor_relative_eq`. -/
theorem condKsEntropyPartition_pulledBack_eq [Fintype ιE]
    {e : α → β} (he : MeasurePreserving e μ ν) (hconj : e ∘ T = S ∘ e)
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (hmβ : 𝒜β ≤ mβ) (hinvβ : MeasurableSpace.comap S 𝒜β ≤ 𝒜β)
    (hmα : MeasurableSpace.comap e 𝒜β ≤ mα)
    (hinvα : MeasurableSpace.comap T (MeasurableSpace.comap e 𝒜β) ≤ MeasurableSpace.comap e 𝒜β)
    (R : MeasurePartition ν ιE) :
    condKsEntropyPartition hmα hT hinvα (R.pulledBack he)
      = condKsEntropyPartition hmβ hS hinvβ R := by
  rw [condKsEntropyPartition, condKsEntropyPartition]
  refine Subadditive.lim_eq_of_eq _ _ (funext fun n => ?_)
  rw [condKsEntropySeq, condKsEntropySeq]
  have hcells : (ksJoin hT (R.pulledBack he) n).cells
      = fun f => e ⁻¹' (ksJoin hS R n).cells f := by
    funext f
    rw [ksJoin_cells, ksJoin_cells, MeasurePartition.pulledBack_cells,
      ksJoinCells_pulledBack hconj R.cells n f]
  rw [hcells]
  exact condEntropy_comap_preimage_cross he hmβ (ksJoin hS R n)

/-- **E2 — measurable-conjugacy invariance of the relative entropy.** If a measurable isomorphism
`e : α ≃ᵐ β` is measure-preserving and intertwines the two dynamics (`e ∘ T = S ∘ e`), then the
relative Kolmogorov–Sinai entropies of the systems with matched conditioning σ-algebras agree:
```
h(T | comap e 𝒜β) = h(S | 𝒜β).
```
For `h(S | 𝒜β) ≤ h(T | comap e 𝒜β)`, pull each `β`-partition `R` back through `e` and apply E1.
For the reverse, every `α`-partition `P` is, up to its cells, the `e`-pullback of `e.symm⁻¹P`
(`e.symm ∘ e = id`), so E1 transports it to the `β`-side. Conditional mirror of
`ksEntropy_congr_of_conjugacy`. -/
theorem condKsEntropy_congr_of_conjugacy
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (hconj : ⇑e ∘ T = S ∘ ⇑e)
    (hmβ : 𝒜β ≤ mβ) (hinvβ : MeasurableSpace.comap S 𝒜β ≤ 𝒜β)
    (hmα : MeasurableSpace.comap (⇑e) 𝒜β ≤ mα)
    (hinvα : MeasurableSpace.comap T (MeasurableSpace.comap (⇑e) 𝒜β)
      ≤ MeasurableSpace.comap (⇑e) 𝒜β) :
    condKsEntropy hmα hT hinvα = condKsEntropy hmβ hS hinvβ := by
  have he' : MeasurePreserving (⇑e.symm) ν μ := MeasurePreserving.symm e he
  refine le_antisymm ?_ ?_
  · -- `h(T | comap e 𝒜β) ≤ h(S | 𝒜β)`: realise each `α`-partition `P` as the `e`-pullback of
    -- `e.symm⁻¹P` and transport it to `β` via E1.
    refine iSup_le fun n => iSup_le fun P => ?_
    have hcells0 : ((P.pulledBack he').pulledBack he).cells = P.cells := by
      funext i
      simp only [MeasurePartition.pulledBack_cells]
      ext x
      simp only [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    have hPR : condKsEntropyPartition hmα hT hinvα P
        = condKsEntropyPartition hmβ hS hinvβ (P.pulledBack he') := by
      rw [← condKsEntropyPartition_pulledBack_eq he hconj hT hS hmβ hinvβ hmα hinvα
        (P.pulledBack he')]
      rw [condKsEntropyPartition, condKsEntropyPartition]
      refine Subadditive.lim_eq_of_eq _ _ (funext fun n => ?_)
      rw [condKsEntropySeq, condKsEntropySeq, ksJoin_cells, ksJoin_cells, hcells0]
    rw [hPR]
    exact le_condKsEntropy hmβ hS hinvβ (P.pulledBack he')
  · -- `h(S | 𝒜β) ≤ h(T | comap e 𝒜β)`: pull each `β`-partition `R` back through `e` (E1).
    refine iSup_le fun n => iSup_le fun R => ?_
    rw [← condKsEntropyPartition_pulledBack_eq he hconj hT hS hmβ hinvβ hmα hinvα R]
    exact le_condKsEntropy hmα hT hinvα (R.pulledBack he)

end CondConjugacy

end Oseledets.Entropy
