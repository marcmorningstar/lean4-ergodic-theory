/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlowMP
import ErgodicTheory.Entropy.KSEntropyConjugacy
import ErgodicTheory.Multifractal.BernoulliSuspensionEntropy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Fibre time-rescaling of constant-roof suspensions (Abramov time-change, constant case)

For a measurable automorphism `T : X ≃ᵐ X` and a scale `r > 0`, the fibre-rescaling map
`(x, s) ↦ (x, s / r)` on `X × ℝ` conjugates the suspension `ℤ`-action of the **constant roof**
`τ ≡ r` to that of the **unit roof** `τ ≡ 1`: the generator `G_r (x, s) = (T x, s − r)` is sent
to `G_1 (x, s) = (T x, s − 1)` because `(s − r) / r = s / r − 1`. Descending through the orbit
quotients gives a measurable equivalence

`suspensionRescale : SuspensionSpace T (τ ≡ r) ≃ᵐ SuspensionSpace T (τ ≡ 1)`

which intertwines the two suspension flows by a time-rescale (`ζ^{(r)}_t` becomes `ζ^{(1)}_{t/r}`)
and transports the invariant probability measure of the `r`-suspension to that of the unit
suspension — the box `X × [0, r)` maps to `X × [0, 1)`, scaling the fibre Lebesgue measure by `r`,
exactly cancelling the `r⁻¹` vs `1⁻¹` normalisation factors.

This is the constant-roof special case of the Ambrose–Kakutani / Abramov time-change for
suspension (mapping-torus) flows. Its payoff is the **time-`r` entropy seal**: the time-`t` map of
the `r`-suspension flow has the same Kolmogorov–Sinai entropy as the time-`t/r` map of the unit
suspension flow (`ksEntropy_suspensionFlowMap_const_eq_unit`); specialised to the constant-roof
Bernoulli suspension it computes the entropy of the time-`r` map as the per-symbol Shannon entropy
`Hnu ν` (`ksEntropy_bernConstSuspension_time_r`). Consumed by issue #38's entropy descent.

## Main definitions

* `ErgodicTheory.rescaleRaw` / `ErgodicTheory.rescaleInvRaw`: the fibre maps `(x, s) ↦ (x, s / r)`
  and `(x, s) ↦ (x, s · r)` on `X × ℝ`.
* `ErgodicTheory.suspensionRescale`: the descended measurable equivalence between the constant-roof
  (`τ ≡ r`) and unit-roof (`τ ≡ 1`) suspension spaces.

## Main results

* `ErgodicTheory.rescaleRaw_act`: the `ℤ`-action intertwining
  `ρ ∘ suspensionAct^{(r)} n = suspensionAct^{(1)} n ∘ ρ` (the well-definedness core).
* `ErgodicTheory.suspensionRescale_comp_suspensionFlowMap`: the flow intertwining
  `ρ ∘ ζ^{(r)}_t = ζ^{(1)}_{t/r} ∘ ρ`.
* `ErgodicTheory.map_suspensionRescale_suspensionMeasure`: the invariant-measure transport.
* `ErgodicTheory.ksEntropy_suspensionFlowMap_const_eq_unit`: the time-`r` entropy conjugacy.
* `ErgodicTheory.ksEntropy_bernConstSuspension_time_r`: the entropy of the time-`r` map of the
  constant-roof Bernoulli suspension equals `Hnu ν`.

## References

* W. Ambrose and S. Kakutani, *Structure and continuity of measurable flows*, Duke Math. J. **9**
  (1942), 25–42.
* L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959), 873–875.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

/-- Measurability of the constant roof `τ ≡ r`. Pinned as a named lemma so the two roof
measurability proofs (`r` and `1`) are spelled identically across all statements. -/
theorem measurable_constFun (r : ℝ) : Measurable (fun _ : X => r) := measurable_const

/-! ### The raw fibre-rescaling maps on `X × ℝ` -/

/-- The **fibre-rescaling map** `(x, s) ↦ (x, s / r)` on `X × ℝ`. -/
noncomputable def rescaleRaw (r : ℝ) (p : X × ℝ) : X × ℝ := (p.1, p.2 / r)

omit [MeasurableSpace X] in
@[simp] theorem rescaleRaw_apply (r : ℝ) (p : X × ℝ) : rescaleRaw r p = (p.1, p.2 / r) := rfl

/-- The **inverse fibre-rescaling map** `(x, s) ↦ (x, s · r)` on `X × ℝ`. -/
noncomputable def rescaleInvRaw (r : ℝ) (p : X × ℝ) : X × ℝ := (p.1, p.2 * r)

omit [MeasurableSpace X] in
@[simp] theorem rescaleInvRaw_apply (r : ℝ) (p : X × ℝ) :
    rescaleInvRaw r p = (p.1, p.2 * r) := rfl

theorem measurable_rescaleRaw (r : ℝ) : Measurable (rescaleRaw r : X × ℝ → X × ℝ) :=
  measurable_fst.prodMk (measurable_snd.div_const r)

theorem measurable_rescaleInvRaw (r : ℝ) : Measurable (rescaleInvRaw r : X × ℝ → X × ℝ) :=
  measurable_fst.prodMk (measurable_snd.mul_const r)

omit [MeasurableSpace X] in
theorem rescaleInvRaw_rescaleRaw {r : ℝ} (hr : 0 < r) (p : X × ℝ) :
    rescaleInvRaw r (rescaleRaw r p) = p := by
  obtain ⟨x, s⟩ := p
  simp only [rescaleRaw_apply, rescaleInvRaw_apply]
  rw [div_mul_cancel₀ s hr.ne']

omit [MeasurableSpace X] in
theorem rescaleRaw_rescaleInvRaw {r : ℝ} (hr : 0 < r) (p : X × ℝ) :
    rescaleRaw r (rescaleInvRaw r p) = p := by
  obtain ⟨x, s⟩ := p
  simp only [rescaleRaw_apply, rescaleInvRaw_apply]
  rw [mul_div_cancel_right₀ s hr.ne']

/-! ### Intertwining the two suspension actions -/

section Intertwine

variable (T : X ≃ᵐ X)

/-- The rescale map conjugates the constant-`r` generator to the unit generator:
`ρ (G_r p) = G_1 (ρ p)`, since `(s − r) / r = s / r − 1`. -/
theorem rescaleRaw_gen {r : ℝ} (hr : 0 < r) (p : X × ℝ) :
    rescaleRaw r (suspensionGen T (measurable_constFun r) p)
      = suspensionGen T (measurable_constFun (1 : ℝ)) (rescaleRaw r p) := by
  obtain ⟨x, s⟩ := p
  simp only [suspensionGen_apply, rescaleRaw_apply]
  congr 1
  rw [sub_div, div_self hr.ne']

/-- The inverse-generator version of `rescaleRaw_gen`. -/
theorem rescaleRaw_gen_symm {r : ℝ} (hr : 0 < r) (p : X × ℝ) :
    rescaleRaw r ((suspensionGen T (measurable_constFun r)).symm p)
      = (suspensionGen T (measurable_constFun (1 : ℝ))).symm (rescaleRaw r p) := by
  obtain ⟨x, s⟩ := p
  simp only [suspensionGen_symm_apply, rescaleRaw_apply]
  congr 1
  rw [add_div, div_self hr.ne']

/-- **The `ℤ`-action intertwining.** The rescale map conjugates the whole constant-`r` suspension
action to the unit one: `ρ ∘ suspensionAct^{(r)} n = suspensionAct^{(1)} n ∘ ρ`. This is the
well-definedness core from which the descended equivalence is built. -/
theorem rescaleRaw_act {r : ℝ} (hr : 0 < r) (n : ℤ) (p : X × ℝ) :
    rescaleRaw r (suspensionAct T (measurable_constFun r) n p)
      = suspensionAct T (measurable_constFun (1 : ℝ)) n (rescaleRaw r p) := by
  induction n using Int.induction_on with
  | zero => simp only [suspensionAct_zero]
  | succ k ih =>
    have e1 : suspensionAct T (measurable_constFun r) ((k : ℤ) + 1) p
        = suspensionGen T (measurable_constFun r)
            (suspensionAct T (measurable_constFun r) (k : ℤ) p) := by
      rw [add_comm (k : ℤ) 1, suspensionAct_add, suspensionAct_one]
    have e2 : suspensionAct T (measurable_constFun (1 : ℝ)) ((k : ℤ) + 1) (rescaleRaw r p)
        = suspensionGen T (measurable_constFun (1 : ℝ))
            (suspensionAct T (measurable_constFun (1 : ℝ)) (k : ℤ) (rescaleRaw r p)) := by
      rw [add_comm (k : ℤ) 1, suspensionAct_add, suspensionAct_one]
    rw [e1, e2, rescaleRaw_gen T hr, ih]
  | pred k ih =>
    have e1 : suspensionAct T (measurable_constFun r) (-(k : ℤ) - 1) p
        = (suspensionGen T (measurable_constFun r)).symm
            (suspensionAct T (measurable_constFun r) (-(k : ℤ)) p) := by
      rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one]
    have e2 : suspensionAct T (measurable_constFun (1 : ℝ)) (-(k : ℤ) - 1) (rescaleRaw r p)
        = (suspensionGen T (measurable_constFun (1 : ℝ))).symm
            (suspensionAct T (measurable_constFun (1 : ℝ)) (-(k : ℤ)) (rescaleRaw r p)) := by
      rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one]
    rw [e1, e2, rescaleRaw_gen_symm T hr, ih]

/-- The inverse `ℤ`-action intertwining, derived from `rescaleRaw_act` by cancelling the
rescale. -/
theorem rescaleInvRaw_act {r : ℝ} (hr : 0 < r) (n : ℤ) (q : X × ℝ) :
    rescaleInvRaw r (suspensionAct T (measurable_constFun (1 : ℝ)) n q)
      = suspensionAct T (measurable_constFun r) n (rescaleInvRaw r q) := by
  have key := rescaleRaw_act T hr n (rescaleInvRaw r q)
  rw [rescaleRaw_rescaleInvRaw hr] at key
  calc rescaleInvRaw r (suspensionAct T (measurable_constFun (1 : ℝ)) n q)
      = rescaleInvRaw r
          (rescaleRaw r (suspensionAct T (measurable_constFun r) n (rescaleInvRaw r q))) := by
        rw [key]
    _ = suspensionAct T (measurable_constFun r) n (rescaleInvRaw r q) :=
        rescaleInvRaw_rescaleRaw hr _

end Intertwine

/-! ### The descended measurable equivalence -/

noncomputable section Equiv

variable (T : X ≃ᵐ X)

/-- The forward descended map `[x, s] ↦ [x, s / r]`, the lift of the rescale to the quotients. -/
def rescaleFwd {r : ℝ} (hr : 0 < r) :
    SuspensionSpace T (measurable_constFun r) →
      SuspensionSpace T (measurable_constFun (1 : ℝ)) :=
  letI := suspensionAddAction T (measurable_constFun r)
  Quotient.lift (fun p => suspensionMk T (measurable_constFun (1 : ℝ)) (rescaleRaw r p))
    (fun p q h => by
      obtain ⟨n, hn⟩ := h
      have hn' : suspensionAct T (measurable_constFun r) n q = p := hn
      change suspensionMk T (measurable_constFun (1 : ℝ)) (rescaleRaw r p)
        = suspensionMk T (measurable_constFun (1 : ℝ)) (rescaleRaw r q)
      rw [← hn', rescaleRaw_act T hr]
      exact suspensionMk_act T (measurable_constFun (1 : ℝ)) n (rescaleRaw r q))

/-- The inverse descended map `[x, s] ↦ [x, s · r]`. -/
def rescaleInv {r : ℝ} (hr : 0 < r) :
    SuspensionSpace T (measurable_constFun (1 : ℝ)) →
      SuspensionSpace T (measurable_constFun r) :=
  letI := suspensionAddAction T (measurable_constFun (1 : ℝ))
  Quotient.lift (fun p => suspensionMk T (measurable_constFun r) (rescaleInvRaw r p))
    (fun p q h => by
      obtain ⟨n, hn⟩ := h
      have hn' : suspensionAct T (measurable_constFun (1 : ℝ)) n q = p := hn
      change suspensionMk T (measurable_constFun r) (rescaleInvRaw r p)
        = suspensionMk T (measurable_constFun r) (rescaleInvRaw r q)
      rw [← hn', rescaleInvRaw_act T hr]
      exact suspensionMk_act T (measurable_constFun r) n (rescaleInvRaw r q))

@[simp] theorem rescaleFwd_mk {r : ℝ} (hr : 0 < r) (p : X × ℝ) :
    rescaleFwd T hr (suspensionMk T (measurable_constFun r) p)
      = suspensionMk T (measurable_constFun (1 : ℝ)) (rescaleRaw r p) := rfl

@[simp] theorem rescaleInv_mk {r : ℝ} (hr : 0 < r) (p : X × ℝ) :
    rescaleInv T hr (suspensionMk T (measurable_constFun (1 : ℝ)) p)
      = suspensionMk T (measurable_constFun r) (rescaleInvRaw r p) := rfl

theorem measurable_rescaleFwd {r : ℝ} (hr : 0 < r) : Measurable (rescaleFwd T hr) := by
  letI := suspensionAddAction T (measurable_constFun r)
  refine measurable_from_quotient.2 ?_
  exact (measurable_suspensionMk T (measurable_constFun (1 : ℝ))).comp (measurable_rescaleRaw r)

theorem measurable_rescaleInv {r : ℝ} (hr : 0 < r) : Measurable (rescaleInv T hr) := by
  letI := suspensionAddAction T (measurable_constFun (1 : ℝ))
  refine measurable_from_quotient.2 ?_
  exact (measurable_suspensionMk T (measurable_constFun r)).comp (measurable_rescaleInvRaw r)

/-- **The fibre-rescaling measurable equivalence** between the constant-roof (`τ ≡ r`) and
unit-roof (`τ ≡ 1`) suspension spaces, with forward map `[x, s] ↦ [x, s / r]` and inverse
`[x, s] ↦ [x, s·r]`. Constant-roof case of the Ambrose–Kakutani/Abramov time-change. -/
noncomputable def suspensionRescale {r : ℝ} (hr : 0 < r) :
    SuspensionSpace T (measurable_constFun r) ≃ᵐ
      SuspensionSpace T (measurable_constFun (1 : ℝ)) where
  toFun := rescaleFwd T hr
  invFun := rescaleInv T hr
  left_inv := by
    refine fun y => Quotient.inductionOn y (fun p => ?_)
    change suspensionMk T (measurable_constFun r) (rescaleInvRaw r (rescaleRaw r p))
      = suspensionMk T (measurable_constFun r) p
    rw [rescaleInvRaw_rescaleRaw hr]
  right_inv := by
    refine fun y => Quotient.inductionOn y (fun p => ?_)
    change suspensionMk T (measurable_constFun (1 : ℝ)) (rescaleRaw r (rescaleInvRaw r p))
      = suspensionMk T (measurable_constFun (1 : ℝ)) p
    rw [rescaleRaw_rescaleInvRaw hr]
  measurable_toFun := measurable_rescaleFwd T hr
  measurable_invFun := measurable_rescaleInv T hr

@[simp] theorem suspensionRescale_mk {r : ℝ} (hr : 0 < r) (p : X × ℝ) :
    suspensionRescale T hr (suspensionMk T (measurable_constFun r) p)
      = suspensionMk T (measurable_constFun (1 : ℝ)) (rescaleRaw r p) := rfl

/-- The descent commutation `ρ ∘ π_r = π_1 ∘ rescaleRaw`. -/
theorem suspensionRescale_comp_mk {r : ℝ} (hr : 0 < r) :
    (⇑(suspensionRescale T hr)) ∘ (suspensionMk T (measurable_constFun r))
      = (suspensionMk T (measurable_constFun (1 : ℝ))) ∘ (rescaleRaw r) := by
  funext p; exact suspensionRescale_mk T hr p

/-! ### The flow intertwining -/

/-- **The flow intertwining.** The rescale equivalence conjugates the time-`t` map of the `r`-roof
suspension flow to the time-`t/r` map of the unit-roof flow:
`ρ ∘ ζ^{(r)}_t = ζ^{(1)}_{t/r} ∘ ρ`. On representatives, `(x, (s+t)/r) = (x, s/r + t/r)`. -/
theorem suspensionRescale_comp_suspensionFlowMap {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (⇑(suspensionRescale T hr)) ∘ (suspensionFlowMap T (measurable_constFun r) t)
      = (suspensionFlowMap T (measurable_constFun (1 : ℝ)) (t / r))
          ∘ (suspensionRescale T hr) := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspensionRescale T hr (suspensionFlowMap T (measurable_constFun r) t
      (suspensionMk T (measurable_constFun r) (x, s)))
    = suspensionFlowMap T (measurable_constFun (1 : ℝ)) (t / r)
        (suspensionRescale T hr (suspensionMk T (measurable_constFun r) (x, s)))
  simp only [suspensionFlowMap_mk, suspensionRescale_mk, suspensionTranslate_apply,
    rescaleRaw_apply]
  rw [add_div]

end Equiv

/-! ### The invariant-measure transport -/

/-- The integral of the constant function `r` against a probability measure is `r`. -/
theorem integral_constFun (r : ℝ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∫ _x, (r : ℝ) ∂μ = r := by
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]

/-- **The 1-D fibre scaling.** Pushing Lebesgue measure on `[0, r)` forward along `s ↦ s / r`
gives `r`-scaled Lebesgue measure on `[0, 1)`. -/
theorem map_div_volume_restrict {r : ℝ} (hr : 0 < r) :
    Measure.map (fun s : ℝ => s / r) (volume.restrict (Set.Ico (0 : ℝ) r))
      = ENNReal.ofReal r • volume.restrict (Set.Ico (0 : ℝ) 1) := by
  have hdivmeas : Measurable (fun s : ℝ => s / r) := by fun_prop
  have hpre : (fun s : ℝ => s / r) ⁻¹' Set.Ico (0 : ℝ) 1 = Set.Ico (0 : ℝ) r := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ico]
    rw [le_div_iff₀ hr, zero_mul, div_lt_one hr]
  have hmapvol : Measure.map (fun s : ℝ => s / r) volume = ENNReal.ofReal r • volume := by
    have hfun : (fun s : ℝ => s / r) = (fun s : ℝ => s * r⁻¹) := by
      funext s; rw [div_eq_mul_inv]
    rw [hfun, Real.map_volume_mul_right (inv_ne_zero hr.ne'), inv_inv, abs_of_pos hr]
  calc Measure.map (fun s : ℝ => s / r) (volume.restrict (Set.Ico (0 : ℝ) r))
      = Measure.map (fun s : ℝ => s / r)
          (volume.restrict ((fun s : ℝ => s / r) ⁻¹' Set.Ico (0 : ℝ) 1)) := by rw [hpre]
    _ = (Measure.map (fun s : ℝ => s / r) volume).restrict (Set.Ico (0 : ℝ) 1) :=
        (Measure.restrict_map hdivmeas measurableSet_Ico).symm
    _ = (ENNReal.ofReal r • volume).restrict (Set.Ico (0 : ℝ) 1) := by rw [hmapvol]
    _ = ENNReal.ofReal r • volume.restrict (Set.Ico (0 : ℝ) 1) := Measure.restrict_smul _ _ _

/-- **The box measure transport.** The push-forward of `(μ × volume)` restricted to the `r`-box
`X × [0, r)` along the fibre rescale equals `r` times the same restricted to the unit box
`X × [0, 1)`. -/
theorem map_rescaleRaw_prodVolume_restrict {r : ℝ} (hr : 0 < r) {μ : Measure X} [SFinite μ] :
    Measure.map (rescaleRaw r) ((μ.prod volume).restrict (suspensionDomain (fun _ : X => r)))
      = ENNReal.ofReal r •
          ((μ.prod volume).restrict (suspensionDomain (fun _ : X => (1 : ℝ)))) := by
  have hdomr : suspensionDomain (fun _ : X => r) = Set.univ ×ˢ Set.Ico (0 : ℝ) r := by
    ext p
    simp only [suspensionDomain, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ico]
  have hdom1 : suspensionDomain (fun _ : X => (1 : ℝ)) = Set.univ ×ˢ Set.Ico (0 : ℝ) 1 := by
    ext p
    simp only [suspensionDomain, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ico]
  have hdivmeas : Measurable (fun s : ℝ => s / r) := by fun_prop
  have hrescale_eq :
      (rescaleRaw r : X × ℝ → X × ℝ) = Prod.map (id : X → X) (fun s : ℝ => s / r) := rfl
  rw [hdomr, hdom1]
  calc Measure.map (rescaleRaw r) ((μ.prod volume).restrict (Set.univ ×ˢ Set.Ico (0 : ℝ) r))
      = Measure.map (Prod.map (id : X → X) (fun s : ℝ => s / r))
          (μ.prod (volume.restrict (Set.Ico (0 : ℝ) r))) := by
        rw [hrescale_eq, ← Measure.prod_restrict, Measure.restrict_univ]
    _ = (Measure.map id μ).prod
          (Measure.map (fun s : ℝ => s / r) (volume.restrict (Set.Ico (0 : ℝ) r))) :=
        (Measure.map_prod_map μ (volume.restrict (Set.Ico (0 : ℝ) r)) measurable_id
          hdivmeas).symm
    _ = μ.prod (ENNReal.ofReal r • volume.restrict (Set.Ico (0 : ℝ) 1)) := by
        rw [Measure.map_id, map_div_volume_restrict hr]
    _ = ENNReal.ofReal r • μ.prod (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
        Measure.prod_smul_right _
    _ = ENNReal.ofReal r • ((μ.prod volume).restrict (Set.univ ×ˢ Set.Ico (0 : ℝ) 1)) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]

section MeasureTransport

variable (T : X ≃ᵐ X)

/-- The constant-`r` suspension probability measure is `(ENNReal.ofReal r)⁻¹` times the raw
box push-forward. -/
theorem suspensionMeasure_constFun_eq {r : ℝ} (μ : Measure X) [IsProbabilityMeasure μ] :
    suspensionMeasure T (measurable_constFun r) μ
      = (ENNReal.ofReal r)⁻¹ • suspensionMeasure₀ T (measurable_constFun r) μ := by
  simp only [suspensionMeasure]
  rw [integral_constFun]

/-- The unit-roof normalisation is `1`, so the unit suspension probability measure coincides with
the raw box push-forward. -/
theorem suspensionMeasure_constFun_one_eq (μ : Measure X) [IsProbabilityMeasure μ] :
    suspensionMeasure T (measurable_constFun (1 : ℝ)) μ
      = suspensionMeasure₀ T (measurable_constFun (1 : ℝ)) μ := by
  simp only [suspensionMeasure]
  rw [integral_constFun, ENNReal.ofReal_one, inv_one, one_smul]

/-- **The invariant-measure transport.** The rescale equivalence sends the constant-`r` suspension
probability measure to the unit-roof one. The box push-forward scales by `r`
(`map_rescaleRaw_prodVolume_restrict`), and the `r⁻¹` vs `1⁻¹` normalisations cancel it exactly. -/
theorem map_suspensionRescale_suspensionMeasure {r : ℝ} (hr : 0 < r) {μ : Measure X}
    [IsProbabilityMeasure μ] :
    Measure.map (suspensionRescale T hr) (suspensionMeasure T (measurable_constFun r) μ)
      = suspensionMeasure T (measurable_constFun (1 : ℝ)) μ := by
  have hresc : Measurable (suspensionRescale T hr) := (suspensionRescale T hr).measurable
  have hmk_r : Measurable (suspensionMk T (measurable_constFun r)) := measurable_suspensionMk _ _
  have hmk_1 : Measurable (suspensionMk T (measurable_constFun (1 : ℝ))) :=
    measurable_suspensionMk _ _
  have hraw :
      Measure.map (suspensionRescale T hr) (suspensionMeasure₀ T (measurable_constFun r) μ)
        = ENNReal.ofReal r • suspensionMeasure₀ T (measurable_constFun (1 : ℝ)) μ := by
    unfold suspensionMeasure₀
    rw [Measure.map_map hresc hmk_r, suspensionRescale_comp_mk,
      ← Measure.map_map hmk_1 (measurable_rescaleRaw r),
      map_rescaleRaw_prodVolume_restrict hr, Measure.map_smul]
  rw [suspensionMeasure_constFun_eq T μ, suspensionMeasure_constFun_one_eq T μ,
    Measure.map_smul, hraw, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top, one_smul]

end MeasureTransport

/-! ### Probability-measure instances for constant-roof suspensions -/

/-- The unit-roof suspension measure is a probability measure. -/
instance isProbabilityMeasure_suspensionMeasure_constFun_one (T : X ≃ᵐ X) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (suspensionMeasure T (measurable_constFun (1 : ℝ)) μ) :=
  isProbabilityMeasure_suspensionMeasure T (measurable_constFun (1 : ℝ)) μ
    (fun _ => zero_le_one) (integrable_const 1) (by rw [integral_constFun]; exact one_pos)

/-- The constant-`r` suspension measure is a probability measure (for `0 < r`, supplied as a
`Fact` so instance resolution can fire when stating `ksEntropy` of a time-`t` map). -/
instance isProbabilityMeasure_suspensionMeasure_constFun (T : X ≃ᵐ X) (r : ℝ)
    [hr : Fact (0 < r)] (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (suspensionMeasure T (measurable_constFun r) μ) :=
  isProbabilityMeasure_suspensionMeasure T (measurable_constFun r) μ
    (fun _ => hr.out.le) (integrable_const r) (by rw [integral_constFun]; exact hr.out)

/-! ### The time-`r` entropy seal -/

/-- **The time-`r` entropy conjugacy.** The time-`t` map of the constant-`r` suspension flow has
the same Kolmogorov–Sinai entropy as the time-`t/r` map of the unit-roof suspension flow. Proved
by the measurable-conjugacy invariance of entropy (`ksEntropy_congr_of_conjugacy`) applied to the
rescale equivalence, using the flow intertwining and the invariant-measure transport. -/
theorem ksEntropy_suspensionFlowMap_const_eq_unit (T : X ≃ᵐ X) (r : ℝ) [hr : Fact (0 < r)]
    (t : ℝ) {μ : Measure X} [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ) :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap T (measurable_constFun r) hT
        (fun _ => le_refl r) hr.out t)
      = Entropy.ksEntropy (measurePreserving_suspensionFlowMap T (measurable_constFun (1 : ℝ)) hT
        (fun _ => le_refl (1 : ℝ)) one_pos (t / r)) :=
  Entropy.ksEntropy_congr_of_conjugacy
    (measurePreserving_suspensionFlowMap T (measurable_constFun r) hT (fun _ => le_refl r)
      hr.out t)
    (measurePreserving_suspensionFlowMap T (measurable_constFun (1 : ℝ)) hT
      (fun _ => le_refl (1 : ℝ)) one_pos (t / r))
    (suspensionRescale T hr.out)
    ⟨(suspensionRescale T hr.out).measurable,
      map_suspensionRescale_suspensionMeasure T hr.out⟩
    (suspensionRescale_comp_suspensionFlowMap T hr.out t)

/-! ### The time-`r` entropy seal on the constant-roof Bernoulli suspension -/

open Multifractal in
/-- **The time-`r` entropy seal.** For the constant-roof (`τ ≡ r`) suspension of the two-sided
Bernoulli shift, the time-`r` map has Kolmogorov–Sinai entropy exactly the per-symbol Shannon
entropy `Hnu ν`. This is `ksEntropy_suspensionFlowMap_const_eq_unit` at `t = r` (so `t / r = 1`)
composed with the unit-roof value `ksEntropy_bernSuspensionFlow_one_eq_Hnu`. -/
theorem ksEntropy_bernConstSuspension_time_r {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀]
    [MeasurableSingletonClass α₀] (ν : Measure α₀) [IsProbabilityMeasure ν] (r : ℝ)
    [hr : Fact (0 < r)] :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
        (measurable_constFun r) (measurePreserving_biShiftEquiv_bernZ ν)
        (fun _ => le_refl r) hr.out r)
      = ((Hnu ν : ℝ) : EReal) := by
  rw [ksEntropy_suspensionFlowMap_const_eq_unit biShiftEquiv r r
      (measurePreserving_biShiftEquiv_bernZ ν), div_self hr.out.ne']
  exact ksEntropy_bernSuspensionFlow_one_eq_Hnu ν

end ErgodicTheory
