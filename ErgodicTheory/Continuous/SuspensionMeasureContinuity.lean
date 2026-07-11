/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionRescale
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Measure-continuity of the constant-roof suspension flow at time zero

For a measurable-equivalence base map `T : X ≃ᵐ X` and a probability measure `μ` on `X`, the
unit-roof suspension flow `ζ_t` on the suspension probability space is **continuous in measure at
`t = 0`**: for every measurable set `A` of the suspension space,

`μ̂ (ζ_t ⁻¹' A ∆ A) → 0`  as  `t → 0`,

where `μ̂ = suspensionMeasure T (τ ≡ 1) μ` and `∆` is the symmetric difference. This is the
first-order continuity input for the ergodic theory of the flow (issue #48).

## Proof strategy

The suspension measure is the push-forward of `μ × volume` restricted to the fundamental box
`𝓕 = X × [0, 1)` along the quotient projection `π = suspensionMk`. Writing `Ũ = π ⁻¹' A` for the
saturated (`ℤ`-periodic) preimage and `S t (x, s) = (x, s + t)` for the raw vertical translation,
the descent commutation `ζ_t ∘ π = π ∘ S t` gives

`μ̂ (ζ_t ⁻¹' A ∆ A) = (μ × volume) ((S t ⁻¹' Ũ ∆ Ũ) ∩ 𝓕)`.

For `|t| < 1` the periodic set `S t ⁻¹' Ũ ∆ Ũ` agrees on `𝓕` with `S t ⁻¹' W ∆ W`, where
`W = Ũ ∩ (X × [-1, 2))` is a single finite-measure window: on the slab `[0, 1)` a shift by `|t| < 1`
stays inside `(-1, 2)`, so clipping to the window changes nothing. Hence

`μ̂ (ζ_t ⁻¹' A ∆ A) ≤ (μ × volume) (S t ⁻¹' W ∆ W)`,

and the right-hand side tends to `0` by continuity of translation in measure. That continuity is
proved fibrewise: `(μ × volume) (S t ⁻¹' W ∆ W) = ∫ x, volume ((· + t) ⁻¹' W_x ∆ W_x) dμ` by Fubini,
each fibre integrand tends to `0` by the one-dimensional translation-continuity lemma
`MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero` on `ℝ`, and the passage to the limit is
dominated convergence (the fibres are uniformly bounded by `volume [-1, 2) = 3`).

## Main results

* `ErgodicTheory.tendsto_volume_translate_symmDiff`: 1-D Lebesgue translation continuity of the
  symmetric difference of a finite-measure set.
* `ErgodicTheory.tendsto_prod_measure_translate_symmDiff`: continuity of vertical translation in
  measure on `X × ℝ` for a window with uniformly bounded fibres.
* `ErgodicTheory.tendsto_measure_symmDiff_suspensionFlowMap`: the `ℝ≥0∞`-valued time-zero
  measure-continuity of the unit-roof suspension flow.
* `ErgodicTheory.tendsto_measureReal_symmDiff_suspensionFlowMap`: the real-valued version (the
  deliverable).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology symmDiff

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

/-- **One-dimensional translation continuity.** For a measurable set `A ⊆ ℝ` of finite Lebesgue
measure, the measure of the symmetric difference of `A` with its translate `(· + t) ⁻¹' A` tends to
zero as `t → 0`. This is `MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero` applied to the
continuous family of translations on `ℝ`, transported through `ContinuousMap.curry`. -/
theorem tendsto_volume_translate_symmDiff {A : Set ℝ} (hA : MeasurableSet A)
    (hAf : volume A ≠ ∞) :
    Tendsto (fun t : ℝ => volume (((fun s => s + t) ⁻¹' A) ∆ A)) (𝓝 0) (𝓝 0) := by
  set G : C(ℝ × ℝ, ℝ) := ⟨fun p => p.2 + p.1, by fun_prop⟩ with hG
  have hcurry : ∀ t : ℝ, (⇑(G.curry t)) = (fun s => s + t) := by
    intro t; ext s; simp [hG, ContinuousMap.curry_apply]
  have hcurry0 : G.curry 0 = ContinuousMap.id ℝ := by
    ext s; simp [hG, ContinuousMap.curry_apply]
  have hfg : Tendsto (fun t : ℝ => G.curry t) (𝓝 0) (𝓝 (ContinuousMap.id ℝ)) := by
    rw [← hcurry0]; exact G.curry.continuous.tendsto 0
  have hf : ∀ᶠ t in 𝓝 (0 : ℝ), MeasurePreserving (⇑(G.curry t)) volume volume := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [hcurry t]; exact measurePreserving_add_right volume t
  have hg : MeasurePreserving (⇑(ContinuousMap.id ℝ)) volume volume := by
    have : (⇑(ContinuousMap.id ℝ) : ℝ → ℝ) = id := rfl
    rw [this]; exact MeasurePreserving.id volume
  have key := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume)
    hfg hf hg hA.nullMeasurableSet hAf
  refine key.congr (fun t => ?_)
  simp only [hcurry t, ContinuousMap.coe_id, preimage_id]

/-- **Continuity of vertical translation in measure on `X × ℝ`.** If `W ⊆ X × ℝ` is measurable and
each fibre `W_x = {s | (x, s) ∈ W}` has Lebesgue measure at most `C` (`0 ≤ C`), then the measure of
the symmetric difference `S t ⁻¹' W ∆ W` (for the vertical translation `S t (x, s) = (x, s + t)`)
tends to zero as `t → 0`. Proved fibrewise by Fubini and dominated convergence, using the
one-dimensional lemma `tendsto_volume_translate_symmDiff` on each fibre. -/
theorem tendsto_prod_measure_translate_symmDiff (μ : Measure X) [IsProbabilityMeasure μ]
    {W : Set (X × ℝ)} (hW : MeasurableSet W) {C : ℝ} (hC : 0 ≤ C)
    (hWC : ∀ x, volume (Prod.mk x ⁻¹' W) ≤ ENNReal.ofReal C) :
    Tendsto (fun t : ℝ => (μ.prod volume) ((suspensionTranslate t ⁻¹' W) ∆ W)) (𝓝 0) (𝓝 0) := by
  -- Measurability of the symmetric-difference set for each `t`.
  have hEmeas : ∀ t : ℝ, MeasurableSet ((suspensionTranslate t ⁻¹' W) ∆ W) := fun t =>
    (hW.preimage (measurable_suspensionTranslate t)).symmDiff hW
  -- Measurability of each fibre.
  have hAx : ∀ x : X, MeasurableSet (Prod.mk x ⁻¹' W) := fun x => hW.preimage measurable_prodMk_left
  -- Finiteness of each fibre.
  have hAfin : ∀ x : X, volume (Prod.mk x ⁻¹' W) ≠ ∞ := fun x =>
    ((hWC x).trans_lt ENNReal.ofReal_lt_top).ne
  -- Slice identity: the fibre of `S t ⁻¹' W ∆ W` over `x` is the 1-D translated symmetric
  -- difference of the fibre `W_x` (both symmetric-difference arguments agree definitionally).
  have hslice : ∀ (t : ℝ) (x : X),
      Prod.mk x ⁻¹' ((suspensionTranslate t ⁻¹' W) ∆ W)
        = ((fun s => s + t) ⁻¹' (Prod.mk x ⁻¹' W)) ∆ (Prod.mk x ⁻¹' W) := by
    intro t x
    rw [preimage_symmDiff]
    congr 1
  -- Finiteness of each fibre symmetric difference.
  have hslicefin : ∀ (t : ℝ) (x : X),
      volume (Prod.mk x ⁻¹' ((suspensionTranslate t ⁻¹' W) ∆ W)) ≠ ∞ := by
    intro t x
    rw [hslice t x]
    refine ((measure_mono symmDiff_subset_union).trans (measure_union_le _ _)).trans_lt ?_ |>.ne
    rw [(measurePreserving_add_right volume t).measure_preimage (hAx x).nullMeasurableSet]
    exact ENNReal.add_lt_top.mpr ⟨(hAfin x).lt_top, (hAfin x).lt_top⟩
  -- Fubini turns the target `(μ × vol)`-measure into an `∫ ... dμ`.
  have hFubini : ∀ t : ℝ,
      ((μ.prod volume) ((suspensionTranslate t ⁻¹' W) ∆ W)).toReal
        = ∫ x, (volume (Prod.mk x ⁻¹' ((suspensionTranslate t ⁻¹' W) ∆ W))).toReal ∂μ := by
    intro t
    rw [Measure.prod_apply (hEmeas t)]
    refine (integral_toReal ?_ ?_).symm
    · exact (measurable_measure_prodMk_left (hEmeas t)).aemeasurable
    · exact Filter.Eventually.of_forall (fun x => (hslicefin t x).lt_top)
  -- Uniform bound `2 * C` on the fibre integrand.
  have hbound : ∀ (t : ℝ) (x : X),
      ‖(volume (Prod.mk x ⁻¹' ((suspensionTranslate t ⁻¹' W) ∆ W))).toReal‖ ≤ 2 * C := by
    intro t x
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, hslice t x]
    have hle : volume (((fun s => s + t) ⁻¹' (Prod.mk x ⁻¹' W)) ∆ (Prod.mk x ⁻¹' W))
        ≤ ENNReal.ofReal (2 * C) := by
      refine (measure_mono symmDiff_subset_union).trans ((measure_union_le _ _).trans ?_)
      rw [(measurePreserving_add_right volume t).measure_preimage (hAx x).nullMeasurableSet]
      calc volume (Prod.mk x ⁻¹' W) + volume (Prod.mk x ⁻¹' W)
          ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add (hWC x) (hWC x)
        _ = ENNReal.ofReal (2 * C) := by
            rw [← ENNReal.ofReal_add hC hC]; ring_nf
    calc (volume (((fun s => s + t) ⁻¹' (Prod.mk x ⁻¹' W)) ∆ (Prod.mk x ⁻¹' W))).toReal
        ≤ (ENNReal.ofReal (2 * C)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = 2 * C := ENNReal.toReal_ofReal (by positivity)
  -- Dominated convergence: pass the fibre limit `→ 0` through the `μ`-integral.
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun t => (volume (Prod.mk x ⁻¹' ((suspensionTranslate t ⁻¹' W) ∆ W))).toReal)
      (𝓝 0) (𝓝 0) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1d := tendsto_volume_translate_symmDiff (hAx x) (hAfin x)
    have hcomp := ((ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto).comp h1d
    simp only [ENNReal.toReal_zero] at hcomp
    refine hcomp.congr (fun t => ?_)
    rw [Function.comp_apply, ← hslice t x]
  have hmeas : ∀ t : ℝ,
      AEStronglyMeasurable
        (fun x => (volume (Prod.mk x ⁻¹' ((suspensionTranslate t ⁻¹' W) ∆ W))).toReal) μ :=
    fun t => ((measurable_measure_prodMk_left (hEmeas t)).ennreal_toReal).aestronglyMeasurable
  have hInt := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 (0 : ℝ))
    (F := fun t x => (volume (Prod.mk x ⁻¹' ((suspensionTranslate t ⁻¹' W) ∆ W))).toReal)
    (f := fun _ : X => (0 : ℝ)) (bound := fun _ : X => 2 * C)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (hbound t)))
    (integrable_const _) hlim
  simp only [integral_zero] at hInt
  -- Reassemble: `∫ (fibre integrand) = ((μ × vol) (S t ⁻¹' W ∆ W)).toReal`; lift `toReal → ℝ≥0∞`.
  have hReal : Tendsto
      (fun t : ℝ => ((μ.prod volume) ((suspensionTranslate t ⁻¹' W) ∆ W)).toReal) (𝓝 0) (𝓝 0) :=
    hInt.congr (fun t => (hFubini t).symm)
  -- Each such measure is finite, so `ofReal ∘ toReal` is the identity, and `ofReal` is continuous.
  have hEfin : ∀ t : ℝ, (μ.prod volume) ((suspensionTranslate t ⁻¹' W) ∆ W) ≠ ∞ := by
    intro t
    have hWfin : (μ.prod volume) W ≠ ∞ := by
      rw [Measure.prod_apply hW]
      refine ((lintegral_mono hWC).trans_lt ?_).ne
      rw [lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_lt_top
    have hle : (μ.prod volume) ((suspensionTranslate t ⁻¹' W) ∆ W)
        ≤ (μ.prod volume) (suspensionTranslate t ⁻¹' W) + (μ.prod volume) W :=
      (measure_mono symmDiff_subset_union).trans (measure_union_le _ _)
    rw [(measurePreserving_translate μ t).measure_preimage hW.nullMeasurableSet] at hle
    exact (hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hWfin.lt_top, hWfin.lt_top⟩)).ne
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hReal
  simp only [ENNReal.ofReal_zero] at hofReal
  refine hofReal.congr (fun t => ?_)
  rw [Function.comp_apply, ENNReal.ofReal_toReal (hEfin t)]

section MainTheorem

variable (T : X ≃ᵐ X)

/-- **Time-zero measure-continuity of the unit-roof suspension flow (`ℝ≥0∞` version).** For a
probability measure `μ` and any measurable set `A` of the suspension space, the suspension measure
of `ζ_t ⁻¹' A ∆ A` tends to `0` as `t → 0`. -/
theorem tendsto_measure_symmDiff_suspensionFlowMap {μ : Measure X} [IsProbabilityMeasure μ]
    {A : Set (SuspensionSpace T (measurable_constFun (1 : ℝ)))} (hA : MeasurableSet A) :
    Tendsto (fun t : ℝ => (suspensionMeasure T (measurable_constFun (1 : ℝ)) μ)
        (((suspensionFlowMap T (measurable_constFun (1 : ℝ)) t) ⁻¹' A) ∆ A)) (𝓝 0) (𝓝 0) := by
  have hmπ : Measurable (suspensionMk T (measurable_constFun (1 : ℝ))) :=
    measurable_suspensionMk T (measurable_constFun (1 : ℝ))
  -- The saturated preimage and the finite window.
  set U : Set (X × ℝ) := suspensionMk T (measurable_constFun (1 : ℝ)) ⁻¹' A with hU
  have hUmeas : MeasurableSet U := hA.preimage hmπ
  set W : Set (X × ℝ) := U ∩ (univ ×ˢ Ico (-1 : ℝ) 2) with hW
  have hWmeas : MeasurableSet W :=
    hUmeas.inter (MeasurableSet.univ.prod measurableSet_Ico)
  -- The fundamental box `X × [0, 1)`.
  have hdom1 : suspensionDomain (fun _ : X => (1 : ℝ)) = univ ×ˢ Ico (0 : ℝ) 1 := by
    ext p
    simp only [suspensionDomain, mem_setOf_eq, mem_prod, mem_univ, true_and, mem_Ico]
  -- Fibre bound for the window: each fibre sits inside `[-1, 2)`, so has measure `≤ 3`.
  have hWC : ∀ x : X, volume (Prod.mk x ⁻¹' W) ≤ ENNReal.ofReal 3 := by
    intro x
    have hsub : Prod.mk x ⁻¹' W ⊆ Ico (-1 : ℝ) 2 := by
      intro s hs
      simp only [mem_preimage, hW, mem_inter_iff, mem_prod, mem_univ, true_and] at hs
      exact hs.2
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Ico]
    norm_num
  -- The translation-continuity upper bound.
  have hDCT : Tendsto (fun t : ℝ => (μ.prod volume) ((suspensionTranslate t ⁻¹' W) ∆ W))
      (𝓝 0) (𝓝 0) :=
    tendsto_prod_measure_translate_symmDiff μ hWmeas (by norm_num) hWC
  -- The bridge: `μ̂ V = (μ × vol) (π ⁻¹' V ∩ 𝓕)`.
  have hbridge : ∀ {V : Set (SuspensionSpace T (measurable_constFun (1 : ℝ)))}, MeasurableSet V →
      suspensionMeasure T (measurable_constFun (1 : ℝ)) μ V
        = (μ.prod volume)
            ((suspensionMk T (measurable_constFun (1 : ℝ)) ⁻¹' V) ∩ (univ ×ˢ Ico (0 : ℝ) 1)) := by
    intro V hVmeas
    rw [suspensionMeasure_constFun_one_eq T μ]
    unfold suspensionMeasure₀
    rw [hdom1, Measure.map_apply hmπ hVmeas, Measure.restrict_apply (hVmeas.preimage hmπ)]
  -- The eventual upper bound `μ̂ (ζ_t ⁻¹' A ∆ A) ≤ (μ × vol) (S t ⁻¹' W ∆ W)` for `|t| < 1`.
  have hub : ∀ᶠ t in 𝓝 (0 : ℝ),
      (suspensionMeasure T (measurable_constFun (1 : ℝ)) μ)
          (((suspensionFlowMap T (measurable_constFun (1 : ℝ)) t) ⁻¹' A) ∆ A)
        ≤ (μ.prod volume) ((suspensionTranslate t ⁻¹' W) ∆ W) := by
    have habs : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 :=
      (isOpen_lt continuous_abs continuous_const).eventually_mem
        (show (0 : ℝ) ∈ {t : ℝ | |t| < 1} by simp)
    filter_upwards [habs] with t ht
    -- Preimage of the flow symmetric difference is `S t ⁻¹' U ∆ U`.
    have hUmeasFlow :
        MeasurableSet (((suspensionFlowMap T (measurable_constFun (1 : ℝ)) t) ⁻¹' A) ∆ A) :=
      (hA.preimage (measurable_suspensionFlowMap T (measurable_constFun (1 : ℝ)) t)).symmDiff hA
    have hcomm : suspensionMk T (measurable_constFun (1 : ℝ))
          ⁻¹' ((suspensionFlowMap T (measurable_constFun (1 : ℝ)) t) ⁻¹' A)
        = suspensionTranslate t ⁻¹' U := by
      rw [hU, ← preimage_comp, ← preimage_comp,
        suspensionFlowMap_comp_mk T (measurable_constFun (1 : ℝ)) t]
    have hpre : suspensionMk T (measurable_constFun (1 : ℝ))
          ⁻¹' (((suspensionFlowMap T (measurable_constFun (1 : ℝ)) t) ⁻¹' A) ∆ A)
        = (suspensionTranslate t ⁻¹' U) ∆ U := by
      rw [preimage_symmDiff, hcomm, ← hU]
    rw [hbridge hUmeasFlow, hpre]
    -- On the box `𝓕 = X × [0, 1)`, clipping `U` to the window `W` changes nothing (`|t| < 1`).
    have hset : ((suspensionTranslate t ⁻¹' U) ∆ U) ∩ (univ ×ˢ Ico (0 : ℝ) 1)
        = ((suspensionTranslate t ⁻¹' W) ∆ W) ∩ (univ ×ˢ Ico (0 : ℝ) 1) := by
      obtain ⟨htlo, hthi⟩ : (-1 : ℝ) < t ∧ t < 1 := abs_lt.mp ht
      ext p
      obtain ⟨x, s⟩ := p
      simp only [mem_inter_iff, mem_prod, mem_univ, true_and, mem_Ico, mem_symmDiff,
        mem_preimage, suspensionTranslate_apply, hW]
      constructor
      · rintro ⟨hUU, hs0, hs1⟩
        refine ⟨?_, hs0, hs1⟩
        rcases hUU with h | h
        · left
          exact ⟨⟨h.1, by linarith, by linarith⟩, fun hc => h.2 hc.1⟩
        · right
          exact ⟨⟨h.1, by linarith, by linarith⟩, fun hc => h.2 hc.1⟩
      · rintro ⟨hWW, hs0, hs1⟩
        refine ⟨?_, hs0, hs1⟩
        rcases hWW with h | h
        · left
          exact ⟨h.1.1, fun hc => h.2 ⟨hc, by constructor <;> linarith⟩⟩
        · right
          exact ⟨h.1.1, fun hc => h.2 ⟨hc, by constructor <;> linarith⟩⟩
    rw [hset]
    exact measure_mono inter_subset_left
  -- Squeeze `0 ≤ μ̂(...) ≤ (μ × vol)(S t ⁻¹' W ∆ W) → 0`.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hDCT
    (Filter.Eventually.of_forall (fun _ => zero_le')) hub

set_option linter.unusedVariables false in
/-- **Time-zero measure-continuity of the unit-roof suspension flow (real-valued version).** For a
probability measure `μ` and any measurable set `A` of the suspension space, the real suspension
measure of `ζ_t ⁻¹' A ∆ A` tends to `0` as `t → 0`. This is the deliverable form: continuity in
measure of the suspension flow at time zero. (The measure-preserving hypothesis `hT` is not needed
for continuity in measure; it is retained to match the downstream flow-ergodicity interface.) -/
theorem tendsto_measureReal_symmDiff_suspensionFlowMap {μ : Measure X} [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ)
    {A : Set (SuspensionSpace T (measurable_constFun (1 : ℝ)))} (hA : MeasurableSet A) :
    Tendsto (fun t : ℝ => (suspensionMeasure T (measurable_constFun (1 : ℝ)) μ).real
        (((suspensionFlowMap T (measurable_constFun (1 : ℝ)) t) ⁻¹' A) ∆ A)) (𝓝 0) (𝓝 0) := by
  have hEN := tendsto_measure_symmDiff_suspensionFlowMap T (μ := μ) hA
  have hcomp := ((ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto).comp hEN
  simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_apply] using hcomp

end MainTheorem

end ErgodicTheory
