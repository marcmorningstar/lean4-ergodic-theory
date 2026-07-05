/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Multifractal.BernoulliTwoSidedSystemEntropy
import ErgodicTheory.Entropy.ProductIdEntropy
import ErgodicTheory.Entropy.KSEntropyConjugacy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The constant-roof Bernoulli suspension's time-`1` map has entropy `Hnu ν`

This is the final fibre theorem of issue #20: the **time-`1` map of the constant-roof (`τ ≡ 1`)
Bernoulli suspension flow** has Kolmogorov–Sinai entropy exactly the per-symbol Shannon entropy
`Hnu ν`:

`ksEntropy ((bernSuspensionFlow ν).measurePreserving 1) = Hnu ν`
(`ErgodicTheory.Multifractal.ksEntropy_bernSuspensionFlow_one_eq_Hnu`).

This is the Abramov-type identity for the constant roof, where the time-`1` map of the suspension is
*measurably conjugate* to the product of the base shift with the identity on the unit fibre. It
upgrades the positivity result `suspensionFlow_bernZ_ksEntropy_pos` (issue #19) to the exact value.

## Construction

For the constant roof the suspension space is measurably equivalent to the fundamental domain
`BiShift α₀ × ↥(Set.Ico (0 : ℝ) 1)` via `suspensionUnitMeasurableEquiv`, with forward coordinate
`[x, s] ↦ (T^{⌊s⌋} x, Int.fract s)`. Under this equivalence:

* the **time-`1` map** `ζ_1 [x, s] = [x, s + 1]` becomes the *frozen product* `T × id`
  (`suspensionUnitEquiv_comp_flow`), because `⌊s + 1⌋ = ⌊s⌋ + 1`, `Int.fract (s + 1) = Int.fract s`
  and `baseIter (⌊s⌋ + 1) x = T (baseIter ⌊s⌋ x)`;
* the **suspension probability measure** becomes the product `bernZ ν × fibreMeasure`, where
  `fibreMeasure` is Lebesgue measure on the unit fibre (a probability measure)
  (`measurePreserving_suspensionUnitEquiv`). This is proved through the inverse embedding
  `(x, t) ↦ [x, t]` of the box `BiShift α₀ × [0, 1)`: pushing `bernZ ν × fibreMeasure` through it
  lands on `(bernZ ν × volume)|_box`, which is exactly the raw suspension measure (for `τ ≡ 1` the
  normalisation is `1`).

The entropy is then a clean three-step chain:

1. **conjugacy invariance** (`ksEntropy_congr_of_conjugacy`): `h(ζ_1) = h(T × id)`;
2. **frozen-factor product entropy** (`ksEntropy_prod_id_eq`): `h(T × id) = h(T)`;
3. **two-sided Bernoulli system entropy** (`ksEntropy_biShiftEquiv_bernZ_eq`): `h(T) = Hnu ν`.

## Main results

* `ErgodicTheory.Multifractal.fibreMeasure`: Lebesgue measure on `↥(Set.Ico (0 : ℝ) 1)`
  (a probability measure).
* `ErgodicTheory.Multifractal.measurePreserving_suspensionUnitEquiv`: the fundamental-domain
  equivalence sends the suspension measure to `bernZ ν × fibreMeasure`.
* `ErgodicTheory.Multifractal.suspensionUnitEquiv_comp_flow`: the equivalence conjugates the time-`1`
  map to the frozen product `T × id`.
* `ErgodicTheory.Multifractal.ksEntropy_bernSuspensionFlow_one_eq_Hnu`: the headline identity.
* `ErgodicTheory.Multifractal.bernSuspensionFlow_ksEntropy_eq_Hnu`: the flow-metric-entropy restatement.

## References

* L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959), 873–875.
* P. Walters, *An Introduction to Ergodic Theory*, GTM 79, Springer (1982), Theorem 4.23.
-/

open MeasureTheory Set
open ErgodicTheory.Entropy

namespace ErgodicTheory.Multifractal

noncomputable section

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- **Lebesgue measure on the unit fibre** `↥(Set.Ico (0 : ℝ) 1)`, as the comap of `volume` along
the subtype inclusion. Since `volume (Ico 0 1) = 1` this is a probability measure. -/
noncomputable def fibreMeasure : Measure ↥(Set.Ico (0 : ℝ) 1) :=
  Measure.comap Subtype.val volume

/-- The unit-fibre measure is a probability measure (`fibreMeasure univ = volume (Ico 0 1) = 1`). -/
instance instIsProbabilityMeasureFibreMeasure : IsProbabilityMeasure (fibreMeasure) := by
  constructor
  unfold fibreMeasure
  rw [comap_subtype_coe_apply measurableSet_Ico, Subtype.coe_image_univ, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one]

/-! ### Measure preservation of the fundamental-domain equivalence -/

-- Finite-alphabet typeclasses unused here: `SFinite (bernZ ν)` needs only `[MeasurableSpace α₀]`.
omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The inverse embedding `(x, t) ↦ [x, t]` of the box pushes `bernZ ν × fibreMeasure` to the
suspension probability measure. Concretely `suspensionUnitInv = suspensionMk ∘ (id × Subtype.val)`,
so the pushforward factors as
`map suspensionMk ((bernZ ν) × (volume|_(Ico 0 1)))
  = map suspensionMk ((bernZ ν × volume)|_box) = suspensionMeasure₀ = suspensionMeasure`
(the last step uses that for `τ ≡ 1` the normalisation is `1`). -/
theorem map_suspensionUnitInv_eq (ν : Measure α₀) [IsProbabilityMeasure ν] :
    Measure.map (suspensionUnitInv (biShiftEquiv (α₀ := α₀)) measurable_oneRoof)
        ((bernZ ν).prod fibreMeasure)
      = suspensionMeasure biShiftEquiv measurable_oneRoof (bernZ ν) := by
  have hinv_eq : suspensionUnitInv (biShiftEquiv (α₀ := α₀)) measurable_oneRoof
      = suspensionMk biShiftEquiv measurable_oneRoof ∘ Prod.map id Subtype.val := by
    funext y
    rfl
  have hmk : Measurable (suspensionMk (biShiftEquiv (α₀ := α₀)) measurable_oneRoof) :=
    measurable_suspensionMk _ _
  have hincl : Measurable (Prod.map (id : BiShift α₀ → BiShift α₀)
      (Subtype.val : ↥(Set.Ico (0 : ℝ) 1) → ℝ)) :=
    measurable_id.prodMap measurable_subtype_coe
  rw [hinv_eq, ← Measure.map_map hmk hincl,
    ← Measure.map_prod_map (bernZ ν) fibreMeasure measurable_id measurable_subtype_coe,
    Measure.map_id]
  unfold fibreMeasure
  rw [map_comap_subtype_coe measurableSet_Ico]
  have hpr : (bernZ ν).prod ((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1))
      = ((bernZ ν).prod volume).restrict (Set.univ ×ˢ Set.Ico (0 : ℝ) 1) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hdom : (Set.univ : Set (BiShift α₀)) ×ˢ Set.Ico (0 : ℝ) 1
      = suspensionDomain (oneRoof (α₀ := α₀)) := by
    ext p
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ico, suspensionDomain, oneRoof,
      Set.mem_setOf_eq, true_and]
  rw [hpr, hdom, suspensionMeasure_oneRoof_eq ν]
  rfl

-- Finite-alphabet typeclasses unused here (the proof only flips `map_suspensionUnitInv_eq`).
omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **The fundamental-domain equivalence is measure-preserving**, sending the suspension probability
measure to `bernZ ν × fibreMeasure`. Obtained by flipping the inverse-direction statement
`map_suspensionUnitInv_eq` (a `MeasurableEquiv` is measure-preserving iff its inverse is). -/
theorem measurePreserving_suspensionUnitEquiv (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving
      ⇑(suspensionUnitMeasurableEquiv (biShiftEquiv (α₀ := α₀)) measurable_oneRoof rfl)
      (suspensionMeasure biShiftEquiv measurable_oneRoof (bernZ ν))
      ((bernZ ν).prod fibreMeasure) := by
  have h : MeasurePreserving
      ⇑(suspensionUnitMeasurableEquiv (biShiftEquiv (α₀ := α₀)) measurable_oneRoof rfl).symm
      ((bernZ ν).prod fibreMeasure)
      (suspensionMeasure biShiftEquiv measurable_oneRoof (bernZ ν)) :=
    ⟨(suspensionUnitMeasurableEquiv biShiftEquiv measurable_oneRoof rfl).symm.measurable,
      map_suspensionUnitInv_eq ν⟩
  exact MeasurePreserving.symm
    (suspensionUnitMeasurableEquiv biShiftEquiv measurable_oneRoof rfl).symm h

/-! ### The equivalence conjugates the time-`1` map to the frozen product -/

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **The fundamental-domain equivalence conjugates the time-`1` map to the frozen product
`T × id`.** For `τ ≡ 1`, `ζ_1 [x, s] = [x, s + 1]`, and the equivalence maps `[x, s]` to
`(baseIter ⌊s⌋ x, Int.fract s)`; both sides of the conjugacy equation give
`(T (baseIter ⌊s⌋ x), Int.fract s)` since `⌊s + 1⌋ = ⌊s⌋ + 1`, `Int.fract (s + 1) = Int.fract s`
and `baseIter (⌊s⌋ + 1) x = T (baseIter ⌊s⌋ x)`. -/
theorem suspensionUnitEquiv_comp_flow (ν : Measure α₀) [IsProbabilityMeasure ν] :
    ⇑(suspensionUnitMeasurableEquiv (biShiftEquiv (α₀ := α₀)) measurable_oneRoof rfl)
        ∘ (bernSuspensionFlow ν) 1
      = Prod.map ⇑(biShiftEquiv (α₀ := α₀)) id
          ∘ ⇑(suspensionUnitMeasurableEquiv biShiftEquiv measurable_oneRoof rfl) := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspensionUnitFwd biShiftEquiv measurable_oneRoof rfl
      ((bernSuspensionFlow ν) 1 (suspensionMk biShiftEquiv measurable_oneRoof (x, s)))
    = Prod.map ⇑biShiftEquiv id
        (suspensionUnitFwd biShiftEquiv measurable_oneRoof rfl
          (suspensionMk biShiftEquiv measurable_oneRoof (x, s)))
  rw [bernSuspensionFlow_apply, suspensionFlowMap_mk, suspensionTranslate_apply,
    suspensionUnitFwd_mk, suspensionUnitFwd_mk]
  refine Prod.ext ?_ ?_
  · change suspensionBaseProjRaw biShiftEquiv measurable_oneRoof ((x, s).1, (x, s).2 + 1)
        = ⇑biShiftEquiv (suspensionBaseProjRaw biShiftEquiv measurable_oneRoof (x, s))
    rw [suspensionBaseProjRaw_apply, suspensionBaseProjRaw_apply, Int.floor_add_one, baseIter_succ']
  · apply Subtype.ext
    change Int.fract ((x, s).2 + 1) = Int.fract (x, s).2
    rw [Int.fract_add_one]

/-! ### The headline entropy identity -/

/-- **The constant-roof Bernoulli suspension's time-`1` map has Kolmogorov–Sinai entropy `Hnu ν`.**

The fundamental-domain equivalence `suspensionUnitMeasurableEquiv` conjugates the time-`1` map to
the frozen product `biShiftEquiv × id` on `BiShift α₀ × ↥(Set.Ico 0 1)`, and maps the suspension
measure to `bernZ ν × fibreMeasure`; hence by conjugacy invariance, the frozen-factor product
identity `h(T × id) = h(T)`, and the two-sided Bernoulli system entropy `h(T) = Hnu ν`, the time-`1`
map has entropy `Hnu ν`. -/
theorem ksEntropy_bernSuspensionFlow_one_eq_Hnu (ν : Measure α₀) [IsProbabilityMeasure ν] :
    ksEntropy ((bernSuspensionFlow ν).measurePreserving 1) = ((Hnu ν : ℝ) : EReal) := by
  haveI : StandardBorelSpace ↥(Set.Ico (0 : ℝ) 1) := measurableSet_Ico.standardBorel
  rw [ksEntropy_congr_of_conjugacy ((bernSuspensionFlow ν).measurePreserving 1)
        ((measurePreserving_biShiftEquiv_bernZ ν).prod (MeasurePreserving.id fibreMeasure))
        (suspensionUnitMeasurableEquiv biShiftEquiv measurable_oneRoof rfl)
        (measurePreserving_suspensionUnitEquiv ν) (suspensionUnitEquiv_comp_flow ν),
    ksEntropy_prod_id_eq (measurePreserving_biShiftEquiv_bernZ ν),
    ksEntropy_biShiftEquiv_bernZ_eq ν]

/-- **The constant-roof Bernoulli suspension flow has metric entropy `Hnu ν`.** Restatement of
`ksEntropy_bernSuspensionFlow_one_eq_Hnu` in terms of the flow's metric entropy
(`MeasurePreservingFlow.ksEntropy`, the entropy of the time-`1` map). -/
theorem bernSuspensionFlow_ksEntropy_eq_Hnu (ν : Measure α₀) [IsProbabilityMeasure ν] :
    (bernSuspensionFlow ν).ksEntropy = ((Hnu ν : ℝ) : EReal) :=
  ksEntropy_bernSuspensionFlow_one_eq_Hnu ν

end

end ErgodicTheory.Multifractal
