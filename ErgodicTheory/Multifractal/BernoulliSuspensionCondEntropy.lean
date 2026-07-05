/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondProductIdEntropy
import ErgodicTheory.Entropy.CondKSEntropyConjugacy
import ErgodicTheory.Multifractal.BernoulliSuspensionEntropy
import ErgodicTheory.Multifractal.BernoulliSuspensionFlow

/-!
# The conditional-fibre entropy of the constant-roof Bernoulli suspension vanishes

This is the final headline of issue #21: the **literal conditional-fibre Kolmogorov–Sinai entropy**
of the constant-roof (`τ ≡ 1`) Bernoulli suspension's time-`1` map, conditioned on the base factor
`comap suspensionBaseProj mβ`, is `0`:

`condKsEntropy hm ((bernSuspensionFlow ν).measurePreserving 1) hinv = 0`
(`ErgodicTheory.Multifractal.condKsEntropy_bernSuspensionFlow_one_baseProj_eq_zero`).

The proof transports the conditional frozen-product vanishing
`ErgodicTheory.Entropy.condKsEntropy_prod_id_eq_zero` (`h(T × id | comap fst) = 0`) across the
fundamental-domain measurable conjugacy `suspensionUnitMeasurableEquiv`, using the conditional
conjugacy-invariance `ErgodicTheory.Entropy.condKsEntropy_congr_of_conjugacy`. The two conditioning
σ-algebras match: `comap suspensionBaseProj mβ = comap e (comap fst mβ)`, since the base projection
factors as `suspensionBaseProj = fst ∘ e` (the equivalence sends `[x, s] ↦ (baseIter ⌊s⌋ x, …)`).

## Main results

* `ErgodicTheory.Multifractal.suspensionBaseProj_eq_fst_comp_unitEquiv`: the base projection is the
  first coordinate of the fundamental-domain equivalence (F-prep).
* `ErgodicTheory.Multifractal.condKsEntropy_bernSuspensionFlow_one_baseProj_eq_zero`: the conditional
  fibre entropy vanishes (the literal target of issue #21).

## References

* L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959), 873–875.
* P. Walters, *An Introduction to Ergodic Theory*, GTM 79, Springer (1982), Theorem 4.23.
-/

open MeasureTheory Set Function

namespace ErgodicTheory.Entropy

-- The two conditioning σ-algebras `𝒜₁`/`𝒜₂` are declared BEFORE the ambient `[mα]`, so the ambient
-- instance keeps higher resolution priority (the CLAUDE Cond*-trap).
variable {α : Type*} {𝒜₁ 𝒜₂ : MeasurableSpace α} [mα : MeasurableSpace α] [StandardBorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

/-- **Congruence of the relative Kolmogorov–Sinai entropy under equality of the conditioning
σ-algebra.** If two sub-σ-algebras `𝒜₁ = 𝒜₂` coincide, the relative entropies agree for any choice
of the (proof-irrelevant) measurability and forward-invariance witnesses. -/
theorem condKsEntropy_congr_sigma (hσ : 𝒜₁ = 𝒜₂)
    (hT : MeasurePreserving T μ μ) (hm₁ : 𝒜₁ ≤ mα) (hinv₁ : MeasurableSpace.comap T 𝒜₁ ≤ 𝒜₁)
    (hm₂ : 𝒜₂ ≤ mα) (hinv₂ : MeasurableSpace.comap T 𝒜₂ ≤ 𝒜₂) :
    condKsEntropy hm₁ hT hinv₁ = condKsEntropy hm₂ hT hinv₂ := by
  subst hσ
  rfl

end ErgodicTheory.Entropy

namespace ErgodicTheory.Multifractal

open ErgodicTheory.Entropy

noncomputable section

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **F-prep.** The base projection of the constant-roof Bernoulli suspension is the first
coordinate of the fundamental-domain equivalence: `suspensionBaseProj = fst ∘ suspensionUnitEquiv`.
On a representative `[x, s]` both sides send it to `baseIter ⌊s⌋ x`. -/
theorem suspensionBaseProj_eq_fst_comp_unitEquiv (ν : Measure α₀) [IsProbabilityMeasure ν] :
    (suspensionBaseProj (α₀ := α₀))
      = Prod.fst ∘ ⇑(suspensionUnitMeasurableEquiv biShiftEquiv measurable_oneRoof rfl) := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspensionBaseProj (suspensionMk biShiftEquiv measurable_oneRoof (x, s))
    = Prod.fst (suspensionUnitFwd biShiftEquiv measurable_oneRoof rfl
        (suspensionMk biShiftEquiv measurable_oneRoof (x, s)))
  rw [suspensionBaseProj_mk, suspensionUnitFwd_mk]
  rfl

set_option linter.unusedFintypeInType false in
/-- **F (literal target of issue #21).** The conditional-fibre Kolmogorov–Sinai entropy of the
constant-roof Bernoulli suspension's time-`1` map, conditioned on the base factor
`comap suspensionBaseProj mβ`, is `0`. Transport the conditional frozen-product vanishing
`condKsEntropy_prod_id_eq_zero` across the fundamental-domain conjugacy via
`condKsEntropy_congr_of_conjugacy`; the conditioning σ-algebras match because
`suspensionBaseProj = fst ∘ suspensionUnitEquiv`. -/
theorem condKsEntropy_bernSuspensionFlow_one_baseProj_eq_zero (ν : Measure α₀)
    [IsProbabilityMeasure ν]
    (hm : MeasurableSpace.comap (suspensionBaseProj (α₀ := α₀))
            (inferInstance : MeasurableSpace (BiShift α₀))
          ≤ (inferInstance : MeasurableSpace (SuspensionSpace biShiftEquiv measurable_oneRoof)))
    (hinv : MeasurableSpace.comap ((bernSuspensionFlow ν) 1)
              (MeasurableSpace.comap (suspensionBaseProj (α₀ := α₀))
                (inferInstance : MeasurableSpace (BiShift α₀)))
            ≤ MeasurableSpace.comap (suspensionBaseProj (α₀ := α₀))
                (inferInstance : MeasurableSpace (BiShift α₀))) :
    condKsEntropy hm ((bernSuspensionFlow ν).measurePreserving 1) hinv = 0 := by
  haveI : StandardBorelSpace ↥(Set.Ico (0 : ℝ) 1) := measurableSet_Ico.standardBorel
  set e := suspensionUnitMeasurableEquiv (biShiftEquiv (α₀ := α₀)) measurable_oneRoof rfl
  -- `suspensionBaseProj = fst ∘ e`, phrased with the abbreviation `e`.
  have hsb : suspensionBaseProj (α₀ := α₀) = Prod.fst ∘ ⇑e :=
    suspensionBaseProj_eq_fst_comp_unitEquiv ν
  -- The two conditioning σ-algebras coincide: `comap π mβ = comap e (comap fst mβ)`.
  have key : MeasurableSpace.comap (suspensionBaseProj (α₀ := α₀))
        (inferInstance : MeasurableSpace (BiShift α₀))
      = MeasurableSpace.comap (⇑e)
          (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1))) := by
    have hbf : (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1)))
        = MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (BiShift α₀)) := rfl
    rw [hsb, hbf, MeasurableSpace.comap_comp]
  -- The product-side conditioning witnesses (over `comap e baseFactor`).
  have hm_e : MeasurableSpace.comap (⇑e)
        (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1)))
      ≤ (inferInstance : MeasurableSpace (SuspensionSpace biShiftEquiv measurable_oneRoof)) := by
    rw [← key]; exact hm
  have hinv_e : MeasurableSpace.comap ((bernSuspensionFlow ν) 1)
        (MeasurableSpace.comap (⇑e)
          (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1))))
      ≤ MeasurableSpace.comap (⇑e)
          (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1))) := by
    rw [← key]; exact hinv
  -- The D-side conditioning witnesses (over `baseFactor` on the product).
  have hm_D : (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1)))
      ≤ (inferInstance : MeasurableSpace (BiShift α₀ × ↥(Set.Ico (0 : ℝ) 1))) :=
    measurable_iff_comap_le.mp measurable_fst
  have hinv_D : MeasurableSpace.comap
        (Prod.map (⇑(biShiftEquiv (α₀ := α₀)))
          (id : ↥(Set.Ico (0 : ℝ) 1) → ↥(Set.Ico (0 : ℝ) 1)))
        (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1)))
      ≤ (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1))) := by
    have hbf : (baseFactor (X := BiShift α₀) (Y := ↥(Set.Ico (0 : ℝ) 1)))
        = MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (BiShift α₀)) := rfl
    rw [hbf, MeasurableSpace.comap_comp]
    have hfun : Prod.fst ∘ Prod.map (⇑(biShiftEquiv (α₀ := α₀)))
          (id : ↥(Set.Ico (0 : ℝ) 1) → ↥(Set.Ico (0 : ℝ) 1))
        = (⇑(biShiftEquiv (α₀ := α₀))) ∘ Prod.fst := by
      funext p; rfl
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (measurable_iff_comap_le.mp (biShiftEquiv (α₀ := α₀)).measurable)
  -- Transport the conditioning σ-algebra, then apply the conjugacy invariance and the D-side
  -- frozen-product vanishing.
  rw [condKsEntropy_congr_sigma key ((bernSuspensionFlow ν).measurePreserving 1)
        hm hinv hm_e hinv_e,
    condKsEntropy_congr_of_conjugacy ((bernSuspensionFlow ν).measurePreserving 1)
        ((measurePreserving_biShiftEquiv_bernZ ν).prod (MeasurePreserving.id fibreMeasure))
        (suspensionUnitMeasurableEquiv biShiftEquiv measurable_oneRoof rfl)
        (measurePreserving_suspensionUnitEquiv ν) (suspensionUnitEquiv_comp_flow ν)
        hm_D hinv_D hm_e hinv_e]
  exact condKsEntropy_prod_id_eq_zero (measurePreserving_biShiftEquiv_bernZ ν) hm_D hinv_D

end

end ErgodicTheory.Multifractal
