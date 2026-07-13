/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlow
import ErgodicTheory.Entropy.FactorMap

/-!
# Functoriality of the unit-roof suspension on factor maps

For measurable automorphisms `T : X ≃ᵐ X`, `S : Y ≃ᵐ Y` with **unit roofs** `τ ≡ 1`, `σ ≡ 1`, a
base factor map `π : X → Y` (measurable, `π ∘ T = S ∘ π`) lifts to a factor map of the two
suspension (mapping-torus) flows. On `X × ℝ` the lift is the fibrewise map
`(x, s) ↦ (π x, s)`; descending through the two orbit quotients gives

`suspensionFactorMap : SuspensionSpace T hτ → SuspensionSpace S hσ`, `[x, s] ↦ [π x, s]`,

which intertwines the two suspension flows and transports the invariant
measure (`suspensionFactorMap_* μ̂ =` the suspension measure of `π_* μ`). Packaged as an
`Entropy.IsFactorMap` of the time-`1` flow maps, this is the ingredient for the flow entropy
tower of issue #58. When `π` is injective, so is `suspensionFactorMap` (conjugacy stage).

This is the constant-roof (`τ ≡ σ ≡ 1`) case of the **Ambrose–Kakutani** functoriality of the
suspension construction: the suspension is a functor on unit-roof factor maps.

## Main definitions

* `ErgodicTheory.suspensionFactorRaw`: the fibre map `(x, s) ↦ (π x, s)` on `X × ℝ`.
* `ErgodicTheory.suspensionFactorMap`: the descended factor map between the two suspension spaces.

## Main results

* `ErgodicTheory.suspensionFactorRaw_act`: the `ℤ`-action intertwining (well-definedness core).
* `ErgodicTheory.suspensionFactorMap_comp_flow`: the flow intertwining.
* `ErgodicTheory.map_suspensionFactorMap_suspensionMeasure`: the measure transport.
* `ErgodicTheory.measurePreserving_suspensionFactorMap`: it is measure preserving.
* `ErgodicTheory.isFactorMap_suspensionFactorMap`: the time-`1` `Entropy.IsFactorMap` package.
* `ErgodicTheory.injective_suspensionFactorMap`: injectivity transport from `π`.

## References

* W. Ambrose and S. Kakutani, *Structure and continuity of measurable flows*, Duke Math. J. **9**
  (1942), 25–42.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ErgodicTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

section Raw

variable (T : X ≃ᵐ X) (S : Y ≃ᵐ Y) {τ : X → ℝ} {σ : Y → ℝ}
  (hτ : Measurable τ) (hσ : Measurable σ)
  (hτ1 : τ = fun _ => (1 : ℝ)) (hσ1 : σ = fun _ => (1 : ℝ))
  (π : X → Y) (hπ : Measurable π) (hsemiconj : ∀ x, π (T x) = S (π x))

/-- The **raw fibre factor map** `(x, s) ↦ (π x, s)` on `X × ℝ` (act by `π` on the base, leave the
time coordinate fixed). Its descent through the two orbit quotients is `suspensionFactorMap`. -/
def suspensionFactorRaw (p : X × ℝ) : Y × ℝ := (π p.1, p.2)

omit [MeasurableSpace X] [MeasurableSpace Y] in
@[simp] theorem suspensionFactorRaw_apply (p : X × ℝ) :
    suspensionFactorRaw π p = (π p.1, p.2) := rfl

theorem measurable_suspensionFactorRaw (hπ : Measurable π) :
    Measurable (suspensionFactorRaw π) :=
  (hπ.comp measurable_fst).prodMk measurable_snd

include hsemiconj in
/-- The base semiconjugacy transports through the inverses: `π ∘ T⁻¹ = S⁻¹ ∘ π`. Derived from
`π ∘ T = S ∘ π` using that `S` (a `MeasurableEquiv`) is injective. -/
theorem semiconj_symm (x : X) : π (T.symm x) = S.symm (π x) := by
  have h := hsemiconj (T.symm x)
  rw [T.apply_symm_apply] at h
  rw [h, S.symm_apply_apply]

include hτ1 hσ1 hsemiconj in
/-- The raw factor map conjugates the source generator to the target generator:
`π̃ (G_T p) = G_S (π̃ p)`. Uses the base semiconjugacy `π (T x) = S (π x)` on the first coordinate
and the unit-roof equalities `τ x = 1 = σ (π x)` on the second. -/
theorem suspensionFactorRaw_gen (p : X × ℝ) :
    suspensionFactorRaw π (suspensionGen T hτ p)
      = suspensionGen S hσ (suspensionFactorRaw π p) := by
  obtain ⟨x, s⟩ := p
  simp only [suspensionGen_apply, suspensionFactorRaw_apply, hτ1, hσ1]
  rw [hsemiconj]

include hτ1 hσ1 hsemiconj in
/-- The inverse-generator version of `suspensionFactorRaw_gen`. -/
theorem suspensionFactorRaw_gen_symm (p : X × ℝ) :
    suspensionFactorRaw π ((suspensionGen T hτ).symm p)
      = (suspensionGen S hσ).symm (suspensionFactorRaw π p) := by
  obtain ⟨x, s⟩ := p
  simp only [suspensionGen_symm_apply, suspensionFactorRaw_apply, hτ1, hσ1]
  rw [semiconj_symm T S π hsemiconj]

include hτ1 hσ1 hsemiconj in
/-- **The `ℤ`-action intertwining.** The raw factor map conjugates the whole source suspension
action to the target one: `π̃ ∘ suspensionAct^T n = suspensionAct^S n ∘ π̃`. This is the
well-definedness core from which the descended factor map is built. -/
theorem suspensionFactorRaw_act (n : ℤ) (p : X × ℝ) :
    suspensionFactorRaw π (suspensionAct T hτ n p)
      = suspensionAct S hσ n (suspensionFactorRaw π p) := by
  induction n using Int.induction_on with
  | zero => simp only [suspensionAct_zero]
  | succ k ih =>
    have e1 : suspensionAct T hτ ((k : ℤ) + 1) p
        = suspensionGen T hτ (suspensionAct T hτ (k : ℤ) p) := by
      rw [add_comm (k : ℤ) 1, suspensionAct_add, suspensionAct_one]
    have e2 : suspensionAct S hσ ((k : ℤ) + 1) (suspensionFactorRaw π p)
        = suspensionGen S hσ (suspensionAct S hσ (k : ℤ) (suspensionFactorRaw π p)) := by
      rw [add_comm (k : ℤ) 1, suspensionAct_add, suspensionAct_one]
    rw [e1, e2, suspensionFactorRaw_gen T S hτ hσ hτ1 hσ1 π hsemiconj, ih]
  | pred k ih =>
    have e1 : suspensionAct T hτ (-(k : ℤ) - 1) p
        = (suspensionGen T hτ).symm (suspensionAct T hτ (-(k : ℤ)) p) := by
      rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one]
    have e2 : suspensionAct S hσ (-(k : ℤ) - 1) (suspensionFactorRaw π p)
        = (suspensionGen S hσ).symm
            (suspensionAct S hσ (-(k : ℤ)) (suspensionFactorRaw π p)) := by
      rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one]
    rw [e1, e2, suspensionFactorRaw_gen_symm T S hτ hσ hτ1 hσ1 π hsemiconj, ih]

end Raw

/-! ### The descended factor map -/

section FactorMap

variable (T : X ≃ᵐ X) (S : Y ≃ᵐ Y) {τ : X → ℝ} {σ : Y → ℝ}
  (hτ : Measurable τ) (hσ : Measurable σ)
  (hτ1 : τ = fun _ => (1 : ℝ)) (hσ1 : σ = fun _ => (1 : ℝ))
  (π : X → Y) (hπ : Measurable π) (hsemiconj : ∀ x, π (T x) = S (π x))

include hτ1 hσ1 hsemiconj in
/-- **The suspension factor map** `[x, s] ↦ [π x, s]`, the descent of the raw fibre map
`suspensionFactorRaw` through the two suspension orbit quotients (unit roofs). It is well-defined by
the `ℤ`-action intertwining `suspensionFactorRaw_act`. -/
def suspensionFactorMap : SuspensionSpace T hτ → SuspensionSpace S hσ :=
  letI := suspensionAddAction T hτ
  Quotient.lift (fun p => suspensionMk S hσ (suspensionFactorRaw π p))
    (fun p q h => by
      obtain ⟨n, hn⟩ := h
      have hn' : suspensionAct T hτ n q = p := hn
      change suspensionMk S hσ (suspensionFactorRaw π p)
        = suspensionMk S hσ (suspensionFactorRaw π q)
      rw [← hn', suspensionFactorRaw_act T S hτ hσ hτ1 hσ1 π hsemiconj]
      letI := suspensionAddAction S hσ
      exact Quotient.sound
        ⟨n, suspension_vadd_eq_act S hσ n (suspensionFactorRaw π q)⟩)

/-- The descent identity: `suspensionFactorMap [p] = [π̃ p]`. -/
@[simp] theorem suspensionFactorMap_mk (p : X × ℝ) :
    suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj (suspensionMk T hτ p)
      = suspensionMk S hσ (suspensionFactorRaw π p) := rfl

include hπ in
/-- The suspension factor map is measurable: it is the descent of the measurable raw fibre map, and
measurability out of a quotient is measurability of the composite with the quotient map. -/
theorem measurable_suspensionFactorMap :
    Measurable (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj) := by
  letI := suspensionAddAction T hτ
  refine measurable_from_quotient.2 ?_
  exact (measurable_suspensionMk S hσ).comp (measurable_suspensionFactorRaw π hπ)

/-- The descent commutation `suspensionFactorMap ∘ π_T = π_S ∘ suspensionFactorRaw`. -/
theorem suspensionFactorMap_comp_mk :
    (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj) ∘ (suspensionMk T hτ)
      = (suspensionMk S hσ) ∘ (suspensionFactorRaw π) := by
  funext p; exact suspensionFactorMap_mk T S hτ hσ hτ1 hσ1 π hsemiconj p

/-- **The flow intertwining.** The suspension factor map conjugates the source suspension flow to
the target one: `suspensionFactorMap ∘ ζ^T_t = ζ^S_t ∘ suspensionFactorMap`. On representatives
both send `[x, s]` to `[π x, s + t]`. -/
theorem suspensionFactorMap_comp_flow (t : ℝ) :
    (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj) ∘ (suspensionFlowMap T hτ t)
      = (suspensionFlowMap S hσ t) ∘ (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj) := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj
      (suspensionFlowMap T hτ t (suspensionMk T hτ (x, s)))
    = suspensionFlowMap S hσ t
        (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj (suspensionMk T hτ (x, s)))
  simp only [suspensionFlowMap_mk, suspensionFactorMap_mk, suspensionTranslate_apply,
    suspensionFactorRaw_apply]

end FactorMap

/-! ### The invariant-measure transport -/

section MeasureTransport

variable (T : X ≃ᵐ X) (S : Y ≃ᵐ Y) {τ : X → ℝ} {σ : Y → ℝ}
  (hτ : Measurable τ) (hσ : Measurable σ)
  (hτ1 : τ = fun _ => (1 : ℝ)) (hσ1 : σ = fun _ => (1 : ℝ))
  (π : X → Y) (hπ : Measurable π) (hsemiconj : ∀ x, π (T x) = S (π x))

include hτ1 hσ1 hπ in
/-- **The box measure transport.** The push-forward of `(μ × volume)` restricted to the unit box
`X × [0, 1)` along the raw fibre factor map equals `(π_* μ × volume)` restricted to the unit box
`Y × [0, 1)`. The base component pushes `μ` to `π_* μ`; the fibre component is the identity. -/
theorem map_suspensionFactorRaw_prodVolume_restrict {μ : Measure X} [SFinite μ] :
    Measure.map (suspensionFactorRaw π)
        ((μ.prod volume).restrict (suspensionDomain τ))
      = ((Measure.map π μ).prod volume).restrict (suspensionDomain σ) := by
  have hdomτ : suspensionDomain τ = Set.univ ×ˢ Set.Ico (0 : ℝ) 1 := by
    rw [hτ1]; ext p
    simp only [suspensionDomain, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ico]
  have hdomσ : suspensionDomain σ = Set.univ ×ˢ Set.Ico (0 : ℝ) 1 := by
    rw [hσ1]; ext p
    simp only [suspensionDomain, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ico]
  have hraw_eq : (suspensionFactorRaw π : X × ℝ → Y × ℝ)
      = Prod.map π (id : ℝ → ℝ) := rfl
  rw [hdomτ, hdomσ]
  calc Measure.map (suspensionFactorRaw π)
          ((μ.prod volume).restrict (Set.univ ×ˢ Set.Ico (0 : ℝ) 1))
      = Measure.map (Prod.map π (id : ℝ → ℝ))
          (μ.prod (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
        rw [hraw_eq, ← Measure.prod_restrict, Measure.restrict_univ]
    _ = (Measure.map π μ).prod
          (Measure.map (id : ℝ → ℝ) (volume.restrict (Set.Ico (0 : ℝ) 1))) :=
        (Measure.map_prod_map μ (volume.restrict (Set.Ico (0 : ℝ) 1)) hπ measurable_id).symm
    _ = (Measure.map π μ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
        rw [Measure.map_id]
    _ = ((Measure.map π μ).prod volume).restrict (Set.univ ×ˢ Set.Ico (0 : ℝ) 1) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]

include hπ in
/-- **The raw invariant-measure transport.** The suspension factor map sends the raw suspension
measure `μ̂₀` to the raw suspension measure `(π_* μ)^₀` of the pushed-forward base measure. -/
theorem map_suspensionFactorMap_suspensionMeasure₀ {μ : Measure X} [SFinite μ] :
    Measure.map (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj)
        (suspensionMeasure₀ T hτ μ)
      = suspensionMeasure₀ S hσ (Measure.map π μ) := by
  have hf : Measurable (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj) :=
    measurable_suspensionFactorMap T S hτ hσ hτ1 hσ1 π hπ hsemiconj
  have hmkT : Measurable (suspensionMk T hτ) := measurable_suspensionMk T hτ
  have hmkS : Measurable (suspensionMk S hσ) := measurable_suspensionMk S hσ
  unfold suspensionMeasure₀
  rw [Measure.map_map hf hmkT, suspensionFactorMap_comp_mk,
    ← Measure.map_map hmkS (measurable_suspensionFactorRaw π hπ),
    map_suspensionFactorRaw_prodVolume_restrict hτ1 hσ1 π hπ]

include hτ1 in
/-- For a probability base measure and unit roof, the normalised suspension measure coincides with
the raw box push-forward (the `(∫ τ) = 1` normalisation is trivial). -/
theorem suspensionMeasure_eq_of_unitRoof {μ : Measure X} [IsProbabilityMeasure μ] :
    suspensionMeasure T hτ μ = suspensionMeasure₀ T hτ μ := by
  have hint : ∫ x, τ x ∂μ = 1 := by rw [hτ1]; simp
  simp only [suspensionMeasure]
  rw [hint, ENNReal.ofReal_one, inv_one, one_smul]

include hπ in
/-- **The invariant-measure transport.** The suspension factor map sends the invariant probability
measure of the source suspension to that of the target suspension over the pushed-forward base
measure `π_* μ`. For unit roofs and a probability base measure the normalisations are trivial, so
this reduces to the raw transport `map_suspensionFactorMap_suspensionMeasure₀`. -/
theorem map_suspensionFactorMap_suspensionMeasure {μ : Measure X} [IsProbabilityMeasure μ] :
    Measure.map (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj)
        (suspensionMeasure T hτ μ)
      = suspensionMeasure S hσ (Measure.map π μ) := by
  haveI : IsProbabilityMeasure (Measure.map π μ) :=
    Measure.isProbabilityMeasure_map hπ.aemeasurable
  rw [suspensionMeasure_eq_of_unitRoof T hτ hτ1, suspensionMeasure_eq_of_unitRoof S hσ hσ1,
    map_suspensionFactorMap_suspensionMeasure₀ T S hτ hσ hτ1 hσ1 π hπ hsemiconj]

include hπ in
/-- **The suspension factor map is measure preserving** from the source suspension probability space
to the target suspension probability space over `π_* μ`. -/
theorem measurePreserving_suspensionFactorMap {μ : Measure X} [IsProbabilityMeasure μ] :
    MeasurePreserving (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj)
      (suspensionMeasure T hτ μ) (suspensionMeasure S hσ (Measure.map π μ)) where
  measurable := measurable_suspensionFactorMap T S hτ hσ hτ1 hσ1 π hπ hsemiconj
  map_eq := map_suspensionFactorMap_suspensionMeasure T S hτ hσ hτ1 hσ1 π hπ hsemiconj

include hπ in
/-- **The time-`1` factor-map package.** The suspension factor map is an `Entropy.IsFactorMap` from
the time-`1` map of the source suspension flow onto the time-`1` map of the target suspension flow
(over the pushed-forward base measure `π_* μ`): it is measure preserving, the target flow map is
measurable, and it intertwines the two time-`1` maps. This is the ingredient a downstream flow
entropy tower chains with the base factor. -/
theorem isFactorMap_suspensionFactorMap {μ : Measure X} [IsProbabilityMeasure μ] :
    Entropy.IsFactorMap (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj)
      (suspensionFlowMap T hτ 1) (suspensionFlowMap S hσ 1)
      (suspensionMeasure T hτ μ) (suspensionMeasure S hσ (Measure.map π μ)) :=
  ⟨measurePreserving_suspensionFactorMap T S hτ hσ hτ1 hσ1 π hπ hsemiconj,
    measurable_suspensionFlowMap S hσ 1,
    suspensionFactorMap_comp_flow T S hτ hσ hτ1 hσ1 π hsemiconj 1⟩

end MeasureTransport

/-! ### Injectivity transport -/

section Injective

variable (T : X ≃ᵐ X) (S : Y ≃ᵐ Y) {τ : X → ℝ} {σ : Y → ℝ}
  (hτ : Measurable τ) (hσ : Measurable σ)
  (hτ1 : τ = fun _ => (1 : ℝ)) (hσ1 : σ = fun _ => (1 : ℝ))
  (π : X → Y) (hsemiconj : ∀ x, π (T x) = S (π x))

include hsemiconj in
/-- **Injectivity transport.** If the base factor map `π` is injective then so is the descended
suspension factor map. If `[π x, s]` and `[π y, t]` land in the same target orbit, the witnessing
integer `n` gives `S^n (π y) = π x`, i.e. `π (T^n y) = π x` by the action intertwining; injectivity
of `π` upgrades this to `T^n y = x`, exhibiting `[x, s]` and `[y, t]` in the same source orbit. -/
theorem injective_suspensionFactorMap (hπinj : Function.Injective π) :
    Function.Injective (suspensionFactorMap T S hτ hσ hτ1 hσ1 π hsemiconj) := by
  letI := suspensionAddAction T hτ
  letI := suspensionAddAction S hσ
  refine fun a b => Quotient.inductionOn₂ a b (fun p q hab => ?_)
  have heq : suspensionMk S hσ (suspensionFactorRaw π p)
      = suspensionMk S hσ (suspensionFactorRaw π q) := hab
  obtain ⟨n, hn⟩ := Quotient.exact heq
  have hn' : suspensionAct S hσ n (suspensionFactorRaw π q) = suspensionFactorRaw π p := hn
  rw [← suspensionFactorRaw_act T S hτ hσ hτ1 hσ1 π hsemiconj] at hn'
  simp only [suspensionFactorRaw_apply, Prod.mk.injEq] at hn'
  obtain ⟨hfst, hsnd⟩ := hn'
  have hpair : suspensionAct T hτ n q = p := Prod.ext (hπinj hfst) hsnd
  exact Quotient.sound ⟨n, (suspension_vadd_eq_act T hτ n q).trans hpair⟩

end Injective

end ErgodicTheory
