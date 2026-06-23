/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Probability.Kernel.Condexp

/-!
# (★) Conditional-expectation equivariance under a measure-preserving map (TWO-SIDED)

This scratch module settles the architectural crux of GitHub issue #13.

For a measure-preserving `T : Ω → Ω` and a sub-σ-algebra `𝒜`, the **conditional-expectation
equivariance**
```
μ⟦T⁻¹' B | 𝒜⟧  =ᵐ[μ]  (μ⟦B | 𝒜⟧) ∘ T          (★)
```
holds *under the TWO-SIDED invariance hypothesis* `T⁻¹𝒜 =ᵐ[μ] 𝒜`, encoded here as: every
`𝒜`-set `A` is `μ`-a.e. equal to `T⁻¹' A'` for some `𝒜`-set `A'` (the "pull-back surjectivity"
direction), together with `T` being `𝒜/𝒜`-measurable (the easy one-sided direction
`comap T 𝒜 ≤ 𝒜`, giving `g := μ⟦B|𝒜⟧ ∘ T` its `𝒜`-measurability).

Here `μ⟦s | m⟧` is Mathlib's `condExp m μ (Set.indicator s (fun _ ↦ (1 : ℝ)))`.

**This is the correct M2 lemma.** The one-sided hypothesis `comap T 𝒜 ≤ 𝒜` alone is NOT enough:
for a genuine NON-invertible factor map there is an explicit Markov counterexample where (★) — and
even `condEntropy_pullback` itself — fails (see the report accompanying this module).

The proof is the uniqueness characterisation `ae_eq_condExp_of_forall_setIntegral_eq`: we exhibit
`g := μ⟦B|𝒜⟧ ∘ T` as a candidate for `μ⟦T⁻¹'B | 𝒜⟧` and check the three hypotheses, the last of
which (the set-integral identity over all `A ∈ 𝒜`) is exactly where two-sided invariance is used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Oseledets.Entropy

section Helpers
-- These helpers involve ONLY the ambient `mΩ`: no sub-σ-algebra is in scope, so the measurable
-- space is unambiguous for instance synthesis (`integral_map`, `MeasurableSet`, …).
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-- `T⁻¹' B` is measurable when `T` is measure-preserving and `B` is measurable. -/
theorem measurableSet_preimage_of_measurePreserving
    (hT : MeasurePreserving T μ μ) {B : Set Ω} (hB : MeasurableSet B) :
    MeasurableSet (T ⁻¹' B) :=
  hT.measurable hB

/-- Integrability is preserved under precomposition with a measure-preserving self-map. -/
theorem integrable_comp_self
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω => f (T ω)) μ :=
  Integrable.comp_measurable (by rwa [hT.map_eq]) hT.measurable

/-- Change of variables for a measure-preserving self-map: `∫ f(T ω) dμ = ∫ f dμ`. -/
theorem integral_comp_self
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∫ ω, f (T ω) ∂μ = ∫ ω, f ω ∂μ := by
  rw [← integral_map (φ := T) hT.measurable.aemeasurable (hf.mono_ac (by rw [hT.map_eq])),
    hT.map_eq]

/-- The change-of-variables building block on `T`-preimages of measurable sets:
`∫_{T⁻¹A'} f(T ω) dμ = ∫_{A'} f dμ`. -/
theorem setIntegral_comp_preimage
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {A' : Set Ω} (hA' : MeasurableSet A') :
    ∫ ω in T ⁻¹' A', f (T ω) ∂μ = ∫ ω in A', f ω ∂μ := by
  rw [← integral_indicator (hT.measurable hA'), ← integral_indicator hA']
  have hcomp : (T ⁻¹' A').indicator (fun ω => f (T ω))
      = fun ω => (A'.indicator f) (T ω) := by
    funext ω
    by_cases hω : T ω ∈ A'
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  rw [hcomp]
  exact integral_comp_self hT (hf.indicator hA')

end Helpers

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {𝒜 : MeasurableSpace Ω}
  {T : Ω → Ω}

/-- **(★) conditional-expectation equivariance under a measure-preserving map, two-sided.**

If `T` is `μ`-preserving, `𝒜 ≤ mΩ`, `T` is `𝒜/𝒜`-measurable (one-sided `comap T 𝒜 ≤ 𝒜`), and
every `𝒜`-set is `μ`-a.e. a `T`-preimage of an `𝒜`-set (the surjective/two-sided direction
`T⁻¹𝒜 =ᵐ 𝒜`), then for every measurable `B`
```
μ⟦T⁻¹' B | 𝒜⟧  =ᵐ[μ]  (μ⟦B | 𝒜⟧) ∘ T.
```
-/
theorem condExp_indicator_preimage_comp
    [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mΩ) (hT : @MeasurePreserving Ω Ω mΩ mΩ T μ μ)
    (hTA : @Measurable Ω Ω 𝒜 𝒜 T)
    (hpull : ∀ A : Set Ω, MeasurableSet[𝒜] A →
      ∃ A' : Set Ω, MeasurableSet[𝒜] A' ∧ A =ᵐ[μ] T ⁻¹' A')
    {B : Set Ω} (hB : @MeasurableSet Ω mΩ B) :
    (μ⟦T ⁻¹' B | 𝒜⟧) =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) := by
  classical
  have hTB : @MeasurableSet Ω mΩ (T ⁻¹' B) :=
    measurableSet_preimage_of_measurePreserving (mΩ := mΩ) hT hB
  -- `𝟙_{T⁻¹B} = 𝟙_B ∘ T`
  have hind : Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ))
      = fun ω => Set.indicator B (fun _ => (1 : ℝ)) (T ω) := by
    funext ω
    by_cases hω : T ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  -- integrability of the indicator of `T⁻¹B`
  have hfintB : Integrable (Set.indicator B (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hfintTB : Integrable (Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hTB
  -- `g := (μ⟦B | 𝒜⟧) ∘ T` is the candidate.
  set g : Ω → ℝ := fun ω => (μ⟦B | 𝒜⟧) (T ω) with hg
  -- `g` is `𝒜`-strongly-measurable: `𝒜`-strongly-meas condExp composed with `𝒜/𝒜`-meas `T`.
  have hgSM : StronglyMeasurable[𝒜] g :=
    (stronglyMeasurable_condExp).comp_measurable hTA
  -- `g` is globally integrable: `μ⟦B|𝒜⟧` is integrable, and integrability is `T`-stable.
  have hgint : Integrable g μ := integrable_comp_self (mΩ := mΩ) hT integrable_condExp
  -- Sigma-finiteness of `μ.trim hm` is free from `IsProbabilityMeasure`
  -- (`isFiniteMeasure_trim` + `IsFiniteMeasure.toSigmaFinite` are both instances).
  have : SigmaFinite (μ.trim hm) := inferInstance
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfintTB
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => ?_) hgSM.aestronglyMeasurable
  -- set-integral identity ∫_s g = ∫_s 𝟙_{T⁻¹B}, for s ∈ 𝒜, via two-sided invariance.
  obtain ⟨A', hA'mem, hA'eq⟩ := hpull s hs
  have hA'meas : @MeasurableSet Ω mΩ A' := hm A' hA'mem
  have hsT : s =ᵐ[μ] T ⁻¹' A' := hA'eq
  -- LHS: ∫_s g = ∫_{T⁻¹A'} g = ∫_{A'} μ⟦B|𝒜⟧  (set congr + change of variables)
  have hL : ∫ ω in s, g ω ∂μ = ∫ ω in A', (μ⟦B | 𝒜⟧) ω ∂μ := by
    rw [setIntegral_congr_set hsT, hg]
    exact setIntegral_comp_preimage (mΩ := mΩ) hT integrable_condExp.aestronglyMeasurable hA'meas
  -- ∫_{A'} μ⟦B|𝒜⟧ = ∫_{A'} 𝟙_B   (defining property of condExp on 𝒜-sets)
  have hcond : ∫ ω in A', (μ⟦B | 𝒜⟧) ω ∂μ
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂μ :=
    setIntegral_condExp hm hfintB hA'mem
  -- RHS: ∫_s 𝟙_{T⁻¹B} = ∫_{T⁻¹A'} 𝟙_{T⁻¹B} = ∫_{T⁻¹A'} (𝟙_B ∘ T) = ∫_{A'} 𝟙_B
  have hR : ∫ ω in s, Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ)) ω ∂μ
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [setIntegral_congr_set hsT, hind]
    exact setIntegral_comp_preimage (mΩ := mΩ) hT hfintB.aestronglyMeasurable hA'meas
  rw [hL, hcond, hR]

end Oseledets.Entropy
