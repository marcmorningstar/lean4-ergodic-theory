/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.LocalDimension
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The local-dimension → Hausdorff-dimension bridge

This file connects the pointwise *local dimension* `d_μ(x)` of an absolutely-continuous probability
measure (formalized in `ErgodicTheory/Multifractal/LocalDimension.lean`) to the **Hausdorff dimension**
`dimH s` of a full-measure carrier set `s`.

The headline result is:

* `ErgodicTheory.Multifractal.dimH_eq_finrank_of_ae_full_of_absolutelyContinuous` — if `μ` is a
  probability measure on a finite-dimensional real inner-product space `E`, absolutely continuous
  w.r.t. a Haar measure, then **every** set `s` of full `μ`-measure has Hausdorff dimension equal to
  the ambient dimension `finrank ℝ E`.

The Frostman lower-bound machinery and the Billingsley upper bound are formulated over a bare
metric space (`MetricSpace` + Borel + second-countable), so the general bridge
`dimH_eq_of_localDimension_eq` applies to non-Euclidean ambient spaces — e.g. a symbolic shift.

## Proof outline

* **Upper bound** `dimH s ≤ finrank ℝ E`. Immediate from `s ⊆ univ`, monotonicity `dimH_mono`, and
  the Mathlib computation `Real.dimH_univ_eq_finrank`.
* **Lower bound** `finrank ℝ E ≤ dimH s`. This is the **mass-distribution / Frostman** direction. We
  package a self-contained mass-distribution principle (`le_dimH_of_uniform_ball_bound`): if on a
  set `A` the measure satisfies a uniform ball bound `μ.real (closedBall x r) ≤ r ^ a` for all
  `x ∈ A` and all small `r > 0`, and `μ A > 0`, then `a ≤ dimH A`. The uniform sets `A` come from
  the a.e. local-dimension statement `ae_tendsto_localDimension_of_absolutelyContinuous`: for
  `a < finrank`, the limit `log μ.real(B(x,r)) / log r → finrank` forces, `μ`-a.e., a radius below
  which `μ.real(B(x,r)) ≤ r ^ a`. A countable exhaustion of `s` by such uniform sets then has
  positive measure on at least one piece, giving `a ≤ dimH s`; finally we let `a → finrank`.
-/

open MeasureTheory Filter Topology Metric Set Module
open scoped ENNReal NNReal MeasureTheory

namespace ErgodicTheory.Multifractal

/-! ## Metric-space machinery

The Frostman lower bound, the Billingsley upper bound and the general bridge only ever use generic
metric-space facts (`dist`, `Metric.closedBall`, `ediam`, the Vitali enlargement covering, and the
Hausdorff-measure/`dimH` API). We therefore prove them over a genuine metric space with a Borel
second-countable structure, so they are usable on non-inner-product ambient spaces. -/

section Metric

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [SecondCountableTopology E] in
/-- **Mass-distribution / Frostman principle (single uniform bound).** Let `μ` be a finite measure
on `E`, `0 < a`, and `A` a set on which a *uniform* ball bound holds: there is a radius `δ > 0` such
that `μ.real (closedBall x r) ≤ r ^ a` for every `x ∈ A` and every `0 < r ≤ δ`. If `0 < μ A`, then
`a ≤ dimH A`.

The proof is the classical mass-distribution argument: the restricted measure `μ.restrict A` is
dominated by the `a`-dimensional Hausdorff measure (any small-diameter set either misses `A` — then
carries no restricted mass — or contains a point of `A`, in which case it lies inside a small ball
and the uniform bound applies). Evaluating that domination on `A` itself shows `μH[a] A ≥ μ A > 0`,
hence `dimH A ≥ a`. -/
theorem le_dimH_of_uniform_ball_bound {μ : Measure E} [IsFiniteMeasure μ] {a : ℝ≥0} (ha : 0 < a)
    {A : Set E} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ x ∈ A, ∀ r : ℝ, 0 < r → r ≤ δ → μ.real (closedBall x r) ≤ r ^ (a : ℝ))
    {t : Set E} (hts : t ⊆ A) (hpos : 0 < μ t) : (a : ℝ≥0∞) ≤ dimH t := by
  -- Single points of `A` are null: `μ {x} ≤ μ (closedBall x r) ≤ ofReal (r^a) → 0`.
  have hatom : ∀ x ∈ A, μ {x} = 0 := by
    intro x hxA
    have hle : ∀ r : ℝ, 0 < r → r ≤ δ → μ {x} ≤ ENNReal.ofReal (r ^ (a : ℝ)) := by
      intro r hr0 hrδ
      calc μ {x} ≤ μ (closedBall x r) :=
            measure_mono (singleton_subset_iff.mpr (mem_closedBall_self hr0.le))
        _ = ENNReal.ofReal (μ.real (closedBall x r)) := (ofReal_measureReal (by finiteness)).symm
        _ ≤ ENNReal.ofReal (r ^ (a : ℝ)) := ENNReal.ofReal_le_ofReal (hbound x hxA r hr0 hrδ)
    -- Let `r → 0⁺`; `ofReal (r^a) → 0` since `a > 0`.
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have htend : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (a : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => r ^ (a : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc := (Real.continuousAt_rpow_const 0 (a : ℝ) (Or.inr ha0.le)).tendsto
        rw [Real.zero_rpow ha0.ne'] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      have : Tendsto (fun y : ℝ => ENNReal.ofReal y) (𝓝 0) (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal).tendsto 0
      rw [ENNReal.ofReal_zero] at this
      exact this.comp h1
    refine le_antisymm (ge_of_tendsto htend ?_) (zero_le')
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr using hle r hr.1 hr.2.le
  -- The mass-distribution domination: `μ.restrict A ≤ μH[a]`.
  have hdom : μ.restrict A ≤ μH[(a : ℝ)] := by
    refine Measure.le_hausdorffMeasure (a : ℝ) _ (ENNReal.ofReal δ) (by positivity) (fun s hs => ?_)
    by_cases hsA : (s ∩ A).Nonempty
    · obtain ⟨x, hxs, hxA⟩ := hsA
      -- `s` lies in a small closed ball around `x ∈ A`; bound its `μ`-mass.
      set δ' : ℝ := (ediam s).toReal with hδ'_def
      have hdiam_ne : ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
      have hsub : s ⊆ closedBall x δ' := by
        intro y hys
        rw [mem_closedBall, dist_comm, dist_edist]
        calc (edist x y).toReal ≤ (ediam s).toReal :=
              ENNReal.toReal_mono hdiam_ne (edist_le_ediam_of_mem hxs hys)
          _ = δ' := rfl
      have hδ'_nonneg : 0 ≤ δ' := ENNReal.toReal_nonneg
      have hδ'_le : δ' ≤ δ := by
        rw [hδ'_def, ← ENNReal.toReal_ofReal hδ.le]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
      -- `μ.restrict A s ≤ μ (closedBall x δ') ≤ ofReal (δ'^a) = ediam s ^ a`.
      have hmass : μ.restrict A s ≤ ENNReal.ofReal (δ' ^ (a : ℝ)) := by
        rcases eq_or_lt_of_le hδ'_nonneg with hδ'0 | hδ'0
        · -- `ediam s = 0`: `s` is a subsingleton inside `{x}`, hence `μ`-null.
          have hsing : s ⊆ {x} := by
            intro y hys
            have hz : ediam s = 0 := by
              rw [← ENNReal.ofReal_toReal hdiam_ne, ← hδ'_def, ← hδ'0, ENNReal.ofReal_zero]
            have hsub' := ediam_eq_zero_iff.mp hz
            exact hsub' hys hxs
          calc μ.restrict A s ≤ μ s := Measure.restrict_apply_le _ _
            _ ≤ μ {x} := measure_mono hsing
            _ = 0 := hatom x hxA
            _ ≤ _ := zero_le'
        · calc μ.restrict A s ≤ μ s := Measure.restrict_apply_le _ _
            _ ≤ μ (closedBall x δ') := measure_mono hsub
            _ = ENNReal.ofReal (μ.real (closedBall x δ')) :=
              (ofReal_measureReal (by finiteness)).symm
            _ ≤ ENNReal.ofReal (δ' ^ (a : ℝ)) :=
              ENNReal.ofReal_le_ofReal (hbound x hxA δ' hδ'0 hδ'_le)
      -- Convert the real `ofReal (δ'^a)` to the `ℝ≥0∞`-rpow `ediam s ^ a`.
      calc μ.restrict A s ≤ ENNReal.ofReal (δ' ^ (a : ℝ)) := hmass
        _ = (ENNReal.ofReal δ') ^ (a : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg hδ'_nonneg a.coe_nonneg).symm
        _ = ediam s ^ (a : ℝ) := by rw [ENNReal.ofReal_toReal hdiam_ne]
    · -- `s` misses `A`: the restricted measure assigns it zero.
      rw [not_nonempty_iff_eq_empty] at hsA
      have : μ.restrict A s = 0 := by
        rw [Measure.restrict_apply' hA, hsA, measure_empty]
      rw [this]; exact zero_le'
  -- Evaluate the domination at `t ⊆ A`: `μ t ≤ μH[a] t`, so `μH[a] t ≠ 0`, hence `a ≤ dimH t`.
  have hHt : 0 < μH[(a : ℝ)] t := by
    have hμt : μ.restrict A t = μ t := by
      rw [Measure.restrict_apply' hA, inter_eq_self_of_subset_left hts]
    calc (0 : ℝ≥0∞) < μ t := hpos
      _ = μ.restrict A t := hμt.symm
      _ ≤ μH[(a : ℝ)] t := hdom t
  have := le_dimH_of_hausdorffMeasure_ne_zero (s := t) (d := a) hHt.ne'
  simpa using this

omit [BorelSpace E] [SecondCountableTopology E] in
/-- **From the local-dimension limit to a uniform ball bound near a point.** If at `x` the
local-dimension quotient `log μ.real(B(x,r)) / log r` tends to `d` and `a < d`, then there is a
radius `δ > 0` below which `μ.real (closedBall x r) ≤ r ^ a`. -/
theorem exists_uniform_ball_bound_of_tendsto {μ : Measure E} {x : E} {a d : ℝ} (had : a < d)
    (hx : Tendsto (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r ≤ δ → μ.real (closedBall x r) ≤ r ^ a := by
  -- Eventually the quotient exceeds `a` and `r < 1`.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      a < Real.log (μ.real (closedBall x r)) / Real.log r ∧ r < 1 :=
    (hx.eventually (eventually_gt_nhds had)).and (eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds one_pos))
  -- Extract a radius `δ` with `Ioo 0 δ` inside the good set.
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ0, hδ⟩ := hev
  refine ⟨δ / 2, by positivity, fun r hr0 hrδ => ?_⟩
  have hrδ' : r < δ := by
    have : δ / 2 < δ := by linarith
    linarith
  have hgood := hδ (by rw [Real.dist_eq, sub_zero, abs_of_pos hr0]; linarith) hr0
  obtain ⟨hquot, hr1⟩ := hgood
  -- Translate the quotient bound into the ball bound.
  set m : ℝ := μ.real (closedBall x r) with hm_def
  have hm_nonneg : 0 ≤ m := measureReal_nonneg
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  rcases eq_or_lt_of_le hm_nonneg with hm0 | hm0
  · -- `μ.real(B) = 0`: bound is immediate since `r ^ a > 0`.
    rw [← hm0]
    positivity
  · -- `μ.real(B) > 0`: pass through `log`/`exp`.
    have hlogm : Real.log m < a * Real.log r := (lt_div_iff_of_neg hlogr).mp hquot
    have hrpow : r ^ a = Real.exp (a * Real.log r) := by
      rw [Real.rpow_def_of_pos hr0, mul_comm]
    rw [hrpow, ← Real.exp_log hm0]
    exact (Real.exp_lt_exp.mpr hlogm).le

variable (E) in
/-- **Measurability of the ball-mass function.** For a finite measure `μ` and a fixed radius `r`,
the map `x ↦ μ (closedBall x r)` is measurable. -/
theorem measurable_measure_closedBall {μ : Measure E} [IsFiniteMeasure μ] (r : ℝ) :
    Measurable fun x => μ (closedBall x r) := by
  set C : Set (E × E) := {p : E × E | dist p.1 p.2 ≤ r} with hC_def
  have hC : MeasurableSet C := (isClosed_le continuous_dist continuous_const).measurableSet
  have hmeas := measurable_measure_prodMk_left_finite (ν := μ) hC
  have heq : (fun x => μ (closedBall x r)) = fun x => μ (Prod.mk x ⁻¹' C) := by
    funext x
    congr 1
    ext y
    simp only [hC_def, mem_preimage, mem_setOf_eq, mem_closedBall, dist_comm y x]
  rw [heq]
  exact hmeas

/-- **Lower bound from an a.e. local-dimension limit (Frostman direction).** If `μ` is a
probability measure and, `μ`-a.e., the local-dimension quotient `log μ.real(B(x,r)) / log r` tends
to a real value `d`, then every set `s` of full `μ`-measure has Hausdorff dimension at least `d`
(more precisely `ENNReal.ofReal d ≤ dimH s`).

This packages the mass-distribution argument: for each `a < d` the a.e. limit yields, on a
positive-measure measurable piece of `s`, a uniform upper ball bound `μ.real(B(x,r)) ≤ r ^ a`, and
`le_dimH_of_uniform_ball_bound` upgrades it to `a ≤ dimH s`; letting `a → d` finishes. -/
theorem le_dimH_of_ae_tendsto_quotient {μ : Measure E} [IsProbabilityMeasure μ] {d : ℝ}
    {s : Set E} (hs : μ sᶜ = 0)
    (hae : ∀ᵐ x ∂μ, Tendsto
      (fun r => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    ENNReal.ofReal d ≤ dimH s := by
  -- Reduce to `↑a ≤ dimH s` for every `a : ℝ≥0` with `↑a < ofReal d`.
  refine ENNReal.le_of_forall_nnreal_lt (fun a ha => ?_)
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  have hapos : 0 < a := pos_iff_ne_zero.mpr ha0
  -- `↑a < ofReal d` ⇒ `(a : ℝ) < d` (as `a ≥ 0`).
  have had : (a : ℝ) < d := by
    rw [← ENNReal.ofReal_coe_nnreal] at ha
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg a.coe_nonneg).mp ha
  -- The measurable uniform sets, indexed by `n` (radius `≤ 1/(n+1)`), via rational radii.
  set Bset : ℕ → Set E := fun n => ⋂ (q : ℚ) (_ : 0 < (q : ℝ)) (_ : (q : ℝ) ≤ 1 / ((n : ℝ) + 1)),
    {x : E | μ (closedBall x q) ≤ ENNReal.ofReal ((q : ℝ) ^ (a : ℝ))} with hBset_def
  -- Each `Bset n` is measurable.
  have hBmeas : ∀ n, MeasurableSet (Bset n) := by
    intro n
    refine MeasurableSet.iInter (fun q => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => ?_)))
    exact measurable_measure_closedBall E (q : ℝ) measurableSet_Iic
  -- On `Bset n`, the rational bound upgrades to the real bound for all `r ≤ 1/(n+2)` (with a small
  -- margin to `1/(n+1)`, the radius covered by the rational intersection, so the limit `ε ↓ r` can
  -- approach `r` from above while staying within range).
  have hBbound : ∀ n, ∀ x ∈ Bset n, ∀ r : ℝ, 0 < r → r ≤ 1 / ((n : ℝ) + 2) →
      μ.real (closedBall x r) ≤ r ^ (a : ℝ) := by
    intro n x hx r hr0 hr
    have hr' : r < 1 / ((n : ℝ) + 1) := by
      have h1 : (1 : ℝ) / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      linarith
    -- Bound at any rational `q ∈ (r, 1/(n+1)]` and let `q → r⁺`.
    have hmono : ∀ q : ℚ, r ≤ (q : ℝ) → (q : ℝ) ≤ 1 / ((n : ℝ) + 1) →
        μ.real (closedBall x r) ≤ (q : ℝ) ^ (a : ℝ) := by
      intro q hrq hq1
      have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le hr0 hrq
      have hmem : x ∈ {x : E | μ (closedBall x q) ≤ ENNReal.ofReal ((q : ℝ) ^ (a : ℝ))} := by
        simp only [hBset_def, mem_iInter] at hx
        exact hx q hq0 hq1
      have hball : μ.real (closedBall x r) ≤ μ.real (closedBall x q) :=
        measureReal_mono (closedBall_subset_closedBall hrq) (measure_ne_top μ _)
      have : μ.real (closedBall x q) ≤ (q : ℝ) ^ (a : ℝ) := by
        have := hmem
        simp only [mem_setOf_eq] at this
        calc μ.real (closedBall x q) = (μ (closedBall x q)).toReal := rfl
          _ ≤ (ENNReal.ofReal ((q : ℝ) ^ (a : ℝ))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top this
          _ = (q : ℝ) ^ (a : ℝ) := ENNReal.toReal_ofReal (by positivity)
      linarith
    -- For every real `ε ∈ (r, 1/(n+1)]` the bound `μ.real(B(x,r)) ≤ ε^a` holds (via a rational
    -- `q ∈ (r, ε)`), then let `ε ↓ r`.
    have hreal : ∀ ε : ℝ, r < ε → ε ≤ 1 / ((n : ℝ) + 1) →
        μ.real (closedBall x r) ≤ ε ^ (a : ℝ) := by
      intro ε hrε hε1
      obtain ⟨q, hrq, hqε⟩ := exists_rat_btwn hrε
      calc μ.real (closedBall x r) ≤ (q : ℝ) ^ (a : ℝ) :=
            hmono q hrq.le (hqε.le.trans hε1)
        _ ≤ ε ^ (a : ℝ) :=
            Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le hr0 hrq.le)) hqε.le a.coe_nonneg
    -- Limit `ε ↓ r`: `ε ^ a → r ^ a`.
    have htend : Tendsto (fun ε : ℝ => ε ^ (a : ℝ)) (𝓝[>] r) (𝓝 (r ^ (a : ℝ))) :=
      (Real.continuousAt_rpow_const r (a : ℝ) (Or.inl hr0.ne')).tendsto.mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT hr'] with ε hε using hreal ε hε.1 hε.2.le
  -- Pointwise: a.e. `x` lies in some `Bset n` (where the eventual bound kicks in).
  have hmem_ae : ∀ᵐ x ∂μ, ∃ n, x ∈ Bset n := by
    filter_upwards [hae] with x hx
    obtain ⟨δ, hδ0, hδ⟩ := exists_uniform_ball_bound_of_tendsto had hx
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
    refine ⟨n, ?_⟩
    have hn1 : 1 / ((n : ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ0] at hn
      nlinarith [hn, hδ0]
    simp only [hBset_def, mem_iInter, mem_setOf_eq]
    intro q hq0 hq1
    have hq1δ : (q : ℝ) ≤ δ := hq1.trans hn1
    have := hδ (q : ℝ) hq0 hq1δ
    calc μ (closedBall x q) = ENNReal.ofReal (μ.real (closedBall x q)) :=
          (ofReal_measureReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal ((q : ℝ) ^ (a : ℝ)) := ENNReal.ofReal_le_ofReal this
  -- The union `⋃ n, Bset n` is `μ`-conull (every a.e. point lies in some `Bset n`).
  have hUnull : μ ((⋃ n, Bset n)ᶜ) = 0 := by
    have hz : μ {x | ¬ ∃ n, x ∈ Bset n} = 0 := ae_iff.mp hmem_ae
    rwa [show {x | ¬ ∃ n, x ∈ Bset n} = (⋃ n, Bset n)ᶜ by
      ext x; simp only [mem_compl_iff, mem_iUnion, mem_setOf_eq]] at hz
  -- Combine with `s` conull: `T = (⋃ Bset n) ∩ s` has `μ T ≥ 1 > 0`.
  set T : Set E := (⋃ n, Bset n) ∩ s with hT_def
  have hpos_union : 0 < μ (⋃ n, Bset n ∩ s) := by
    have hTc : μ Tᶜ = 0 := by
      rw [hT_def, Set.compl_inter]
      refine le_antisymm ?_ (zero_le')
      calc μ ((⋃ n, Bset n)ᶜ ∪ sᶜ) ≤ μ ((⋃ n, Bset n)ᶜ) + μ sᶜ := measure_union_le _ _
        _ = 0 := by rw [hUnull, hs, add_zero]
    have hT1 : (1 : ℝ≥0∞) ≤ μ T := by
      calc (1 : ℝ≥0∞) = μ (Set.univ : Set E) := (measure_univ).symm
        _ = μ (T ∪ Tᶜ) := by rw [Set.union_compl_self]
        _ ≤ μ T + μ Tᶜ := measure_union_le _ _
        _ = μ T := by rw [hTc, add_zero]
    rw [show (⋃ n, Bset n ∩ s) = T by rw [hT_def, iUnion_inter]]
    exact lt_of_lt_of_le one_pos hT1
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hpos_union.ne'
  -- Apply the Frostman principle on `A = Bset n`, target `t = Bset n ∩ s ⊆ Bset n`.
  have hδn : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  refine le_dimH_of_uniform_ball_bound hapos (hBmeas n) hδn (hBbound n) inter_subset_left hn
    |>.trans (dimH_mono inter_subset_right)

/-! ### The Billingsley upper bound

The companion to the Frostman lower bound `le_dimH_of_uniform_ball_bound`. Where Frostman gives
`a ≤ dimH` from an *upper* ball bound `μ(B(x,r)) ≤ r ^ a`, the **Billingsley** principle gives
`dimH ≤ a` from a *lower* ball bound `μ(B(x,r)) ≥ r ^ a` available at arbitrarily small radii (a
fine cover). The proof is a Vitali `τ`-enlargement covering argument: a disjoint subfamily of such
balls whose enlargements cover `A` controls the `a`-dimensional Hausdorff pre-measure by a fixed
multiple of `μ (univ)`, which is finite; feeding coverings of vanishing diameter into
`hausdorffMeasure_le_liminf_tsum` shows `μH[a] A < ∞`, whence `dimH A ≤ a`.  -/

/-- **Billingsley upper bound on the Hausdorff dimension (fine-cover form).** Let `μ` be a finite
measure on `E`, `0 ≤ a`, and `A` a set on which a *lower* ball bound holds at arbitrarily small
scales: for every `x ∈ A` and every `ε > 0` there is a radius `r ∈ (0, ε]` with
`ENNReal.ofReal (r ^ a) ≤ μ (closedBall x r)`. Then `dimH A ≤ a`.

This is the classical mass-distribution argument run "in reverse": a Vitali `τ`-enlargement of a
disjoint subfamily of such balls covers `A` while `∑ diam ^ a ≤ (2 τ) ^ a · μ (univ) < ∞`. -/
theorem dimH_le_of_fine_cover_mass_lower {μ : Measure E} [IsFiniteMeasure μ] {a : ℝ} (ha : 0 ≤ a)
    {A : Set E}
    (hfine : ∀ x ∈ A, ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ ENNReal.ofReal (r ^ a) ≤ μ (closedBall x r)) :
    dimH A ≤ ENNReal.ofReal a := by
  -- Reduce to `μH[a] A < ∞`, working with the `ℝ≥0`-valued exponent `a.toNNReal`.
  rw [show ENNReal.ofReal a = ((a.toNNReal : ℝ≥0) : ℝ≥0∞) from rfl]
  refine dimH_le_of_hausdorffMeasure_ne_top (d := a.toNNReal) ?_
  rw [Real.coe_toNNReal a ha]
  -- The constant multiplier `K = (2 * τ) ^ a` for the chosen enlargement factor `τ = 4`.
  set τ : ℝ := 4 with hτ_def
  have hτ3 : (3 : ℝ) < τ := by norm_num [hτ_def]
  have hτ0 : (0 : ℝ) < τ := by norm_num [hτ_def]
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * τ) ^ a) with hK_def
  have hK_lt_top : K ≠ ∞ := by rw [hK_def]; exact ENNReal.ofReal_ne_top
  -- Each scale `n` produces a countable Vitali subfamily covering `A`.
  -- We package, for each `n : ℕ`, a covering of `A` by enlarged balls of diameter `≤ 2 τ /(n+1)`.
  -- Abbreviation: at scale `n` the requested fineness is `ε = 1 / (n+1)`.
  -- For each `x ∈ A` choose such a radius and ball.
  -- We build the indexed family via the Vitali enlargement theorem, applied to the fine family.
  -- Define, for a scale parameter `δ > 0`, the cover.
  have key : ∀ δ : ℝ, 0 < δ → ∃ (ι : Type _) (_ : Countable ι) (c : ι → E) (ρ : ι → ℝ),
      (A ⊆ ⋃ i, closedBall (c i) (τ * ρ i)) ∧ (∀ i, ρ i ≤ δ) ∧ (∀ i, 0 ≤ ρ i) ∧
      ∑' i, ediam (closedBall (c i) (τ * ρ i)) ^ a ≤ K * μ (univ : Set E) := by
    intro δ hδ
    -- The fine family of admissible (center, radius) pairs at scales `≤ δ`.
    classical
    -- Index set: points `x ∈ A`, each with a chosen good radius `≤ δ`.
    -- Use the choice function from `hfine`.
    have hchoice : ∀ x : A, ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
        ENNReal.ofReal (r ^ a) ≤ μ (closedBall (x : E) r) := by
      intro x
      obtain ⟨r, hr0, hrδ, hrμ⟩ := hfine (x : E) x.2 δ hδ
      exact ⟨r, hr0, hrδ, hrμ⟩
    choose rad hrad0 hradδ hradμ using hchoice
    -- Vitali enlargement on the index `A`.
    obtain ⟨u, hu_sub, hu_disj, hu_cov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (ι := A) (Set.univ)
        (fun x => (x : E)) rad δ (fun x _ => hradδ x) τ hτ3
    -- `u : Set A` countable (disjoint balls of positive measure in a finite measure space).
    have hu_count : u.Countable := by
      -- A pairwise-disjoint family of open balls (with positive radius) is countable in a
      -- separable space.
      have hopen : u.PairwiseDisjoint (fun x : A => ball ((x : E)) (rad x)) :=
        hu_disj.mono (fun x => ball_subset_closedBall)
      exact hopen.countable_of_isOpen (fun x _ => isOpen_ball)
        (fun x _ => ⟨(x : E), mem_ball_self (hrad0 x)⟩)
    refine ⟨u, hu_count.to_subtype, fun i => ((i : A) : E), fun i => rad (i : A), ?_, ?_, ?_, ?_⟩
    · -- `A ⊆ ⋃ enlarged balls`.
      intro y hy
      have hyA : (⟨y, hy⟩ : A) ∈ (Set.univ : Set A) := mem_univ _
      obtain ⟨b, hbu, hb_sub⟩ := hu_cov ⟨y, hy⟩ hyA
      rw [mem_iUnion]
      exact ⟨⟨b, hbu⟩, hb_sub (mem_closedBall_self (hrad0 _).le)⟩
    · exact fun i => hradδ (i : A)
    · exact fun i => (hrad0 (i : A)).le
    · -- The Hausdorff sum bound.
      -- Bound each term by `K * μ (closedBall (c i) (rad i))`.
      have hterm : ∀ i : u, ediam (closedBall ((i : A) : E) (τ * rad (i : A))) ^ a ≤
          K * μ (closedBall ((i : A) : E) (rad (i : A))) := by
        rintro ⟨x, hx⟩
        have hr0 : 0 < rad x := hrad0 x
        -- `ediam (closedBall c (τ r)) ≤ ofReal (2 τ r)`.
        have hediam : ediam (closedBall ((x : E)) (τ * rad x)) ≤
            ENNReal.ofReal (2 * (τ * rad x)) := by
          refine ediam_le_of_forall_dist_le (fun p hp q hq => ?_)
          calc dist p q ≤ dist p (x : E) + dist (x : E) q := dist_triangle _ _ _
            _ ≤ (τ * rad x) + (τ * rad x) := by
                exact add_le_add (mem_closedBall.mp hp) (mem_closedBall'.mp hq)
            _ = 2 * (τ * rad x) := by ring
        -- Raise to power `a`.
        have hpow : ediam (closedBall ((x : E)) (τ * rad x)) ^ a ≤
            ENNReal.ofReal (2 * (τ * rad x)) ^ a :=
          ENNReal.rpow_le_rpow hediam ha
        -- `ofReal(2 τ r)^a = ofReal((2τ)^a) * ofReal(r^a) = K * ofReal(r^a)`.
        have hsplit : ENNReal.ofReal (2 * (τ * rad x)) ^ a = K * ENNReal.ofReal (rad x ^ a) := by
          rw [hK_def, ← ENNReal.ofReal_mul (by positivity)]
          rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
          congr 1
          rw [show 2 * (τ * rad x) = (2 * τ) * rad x by ring,
            Real.mul_rpow (by positivity) (by positivity)]
        -- `ofReal(r^a) ≤ μ (closedBall c r)`.
        calc ediam (closedBall ((x : E)) (τ * rad x)) ^ a
            ≤ ENNReal.ofReal (2 * (τ * rad x)) ^ a := hpow
          _ = K * ENNReal.ofReal (rad x ^ a) := hsplit
          _ ≤ K * μ (closedBall ((x : E)) (rad x)) := by
              gcongr
              exact hradμ x
      -- Sum and use disjointness: `∑ μ(B_i) ≤ μ (univ)`.
      calc ∑' i : u, ediam (closedBall ((i : A) : E) (τ * rad (i : A))) ^ a
          ≤ ∑' i : u, K * μ (closedBall ((i : A) : E) (rad (i : A))) :=
            ENNReal.tsum_le_tsum hterm
        _ = K * ∑' i : u, μ (closedBall ((i : A) : E) (rad (i : A))) := ENNReal.tsum_mul_left
        _ ≤ K * μ (univ : Set E) := by
            gcongr
            refine tsum_measure_le_measure_univ
              (fun i => (measurableSet_closedBall).nullMeasurableSet) ?_
            -- Pairwise disjoint balls.
            intro i j hij
            have hne : (i : ↥A) ≠ (j : ↥A) := fun h => hij (Subtype.ext h)
            exact (hu_disj i.2 j.2 hne).aedisjoint
  -- Feed the family into `hausdorffMeasure_le_liminf_tsum` along `δ = 1/(n+1) → 0`.
  -- `key` produces a different `ι` at each `n`; choose a sequence `n ↦ (ι n, c n, ρ n)` and feed
  -- the resulting per-scale coverings into the liminf Hausdorff bound.
  classical
  -- Choose, for each `n`, the cover at scale `1/(n+1)`.
  have hkey : ∀ n : ℕ, ∃ (ι : Type _) (_ : Countable ι) (c : ι → E) (ρ : ι → ℝ),
      (A ⊆ ⋃ i, closedBall (c i) (τ * ρ i)) ∧ (∀ i, ρ i ≤ 1 / ((n : ℝ) + 1)) ∧ (∀ i, 0 ≤ ρ i) ∧
      ∑' i, ediam (closedBall (c i) (τ * ρ i)) ^ a ≤ K * μ (univ : Set E) :=
    fun n => key (1 / ((n : ℝ) + 1)) (by positivity)
  choose ι hιcount cen ρ hcov hρδ hρ0 hsum using hkey
  -- The covering sets `t n i = closedBall (cen n i) (τ * ρ n i)`.
  set t : ∀ n : ℕ, ι n → Set E := fun n i => closedBall (cen n i) (τ * ρ n i) with ht_def
  -- The diameter bound `r n = ofReal (2 τ /(n+1)) → 0`.
  set rseq : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 * τ / ((n : ℝ) + 1)) with hrseq_def
  have hr_tendsto : Tendsto rseq atTop (𝓝 0) := by
    rw [hrseq_def]
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have : Tendsto (fun n : ℕ => 2 * τ * (1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * τ * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero] at this
    refine this.congr (fun n => by ring)
  -- Each covering set has `ediam ≤ rseq n`.
  have ht_diam : ∀ n, ∀ i, ediam (t n i) ≤ rseq n := by
    intro n i
    rw [ht_def, hrseq_def]
    have hρle : ρ n i ≤ 1 / ((n : ℝ) + 1) := hρδ n i
    refine (ediam_le_of_forall_dist_le (C := 2 * τ * ρ n i) (fun p hp q hq => ?_)).trans ?_
    · calc dist p q ≤ dist p (cen n i) + dist (cen n i) q := dist_triangle _ _ _
        _ ≤ (τ * ρ n i) + (τ * ρ n i) :=
            add_le_add (mem_closedBall.mp hp) (mem_closedBall'.mp hq)
        _ = 2 * τ * ρ n i := by ring
    · refine ENNReal.ofReal_le_ofReal ?_
      have : ρ n i ≤ 1 / ((n : ℝ) + 1) := hρle
      have hτ0' : 0 ≤ 2 * τ := by positivity
      calc 2 * τ * ρ n i ≤ 2 * τ * (1 / ((n : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_left this hτ0'
        _ = 2 * τ / ((n : ℝ) + 1) := by ring
  -- `A ⊆ ⋃ i, t n i` for every `n`.
  have ht_cov : ∀ n, A ⊆ ⋃ i, t n i := fun n => hcov n
  -- Apply the liminf Hausdorff bound.
  have hmeasure_le : μH[a] A ≤ liminf (fun n => ∑' i, ediam (t n i) ^ a) atTop :=
    Measure.hausdorffMeasure_le_liminf_tsum a A rseq hr_tendsto t
      (Eventually.of_forall (fun n i => ht_diam n i))
      (Eventually.of_forall ht_cov)
  -- The liminf is bounded by the fixed finite constant `K * μ univ`.
  have hliminf_le : liminf (fun n => ∑' i, ediam (t n i) ^ a) atTop ≤ K * μ (univ : Set E) := by
    refine liminf_le_of_frequently_le' ?_
    refine Frequently.of_forall (fun n => ?_)
    simpa only [ht_def] using hsum n
  refine ne_top_of_le_ne_top ?_ (hmeasure_le.trans hliminf_le)
  exact ENNReal.mul_ne_top hK_lt_top (measure_ne_top μ _)

omit [BorelSpace E] [SecondCountableTopology E] in
/-- **From the local-dimension limit to a fine lower ball bound near a point.** If at `x` every
closed ball of positive radius has positive `μ`-mass (i.e. `x` is in the support of `μ`) and the
local-dimension quotient `log μ.real(B(x,r)) / log r` tends to `d` with `d < a`, then for every
`ε > 0` there is a radius `r ∈ (0, ε]` with `ENNReal.ofReal (r ^ a) ≤ μ (closedBall x r)`.

This is the "reverse" of `exists_uniform_ball_bound_of_tendsto`, feeding the Billingsley upper
bound. Because the genuine limit is `< a`, the quotient is eventually `< a`, which (as `log r < 0`
and the ball mass is positive) becomes a *lower* bound `μ.real(B(x,r)) ≥ r ^ a` for all small `r`.
The support hypothesis rules out the degenerate `μ(B(x,r)) = 0` case (where `log 0 = 0` makes the
quotient vanish and no positive lower bound can hold). -/
theorem exists_fine_ball_lower_of_tendsto {μ : Measure E} [IsFiniteMeasure μ] {x : E} {a d : ℝ}
    (had : d < a) (hxsupp : ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r))
    (hx : Tendsto (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ ENNReal.ofReal (r ^ a) ≤ μ (closedBall x r) := by
  -- Eventually the quotient is below `a`, and `r < 1`.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Real.log (μ.real (closedBall x r)) / Real.log r < a ∧ r < 1 :=
    (hx.eventually (eventually_lt_nhds had)).and (eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds one_pos))
  intro ε hε
  -- Pick a radius `r ∈ (0, ε]` in the eventual good set.
  obtain ⟨r, hgood, hr0, hrε⟩ :
      ∃ r, (Real.log (μ.real (closedBall x r)) / Real.log r < a ∧ r < 1) ∧ 0 < r ∧ r ≤ ε := by
    have hmem : {r : ℝ | (Real.log (μ.real (closedBall x r)) / Real.log r < a ∧ r < 1)
        ∧ 0 < r ∧ r ≤ ε} ∈ 𝓝[>] (0 : ℝ) := by
      filter_upwards [hev, self_mem_nhdsWithin, Ioc_mem_nhdsGT hε] with r hr hr0 hrε
      exact ⟨hr, hr0, hrε.2⟩
    obtain ⟨r, hr⟩ := Filter.nonempty_of_mem hmem
    exact ⟨r, hr⟩
  obtain ⟨hquot, hr1⟩ := hgood
  refine ⟨r, hr0, hrε, ?_⟩
  -- Translate the quotient bound into the lower ball bound: `r ^ a ≤ μ.real (B(x,r))`.
  set m : ℝ := μ.real (closedBall x r) with hm_def
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  -- `m > 0` because `x` is in the support.
  have hm0 : 0 < m := by
    rw [hm_def, measureReal_def]
    exact ENNReal.toReal_pos (hxsupp r hr0).ne' (measure_ne_top μ _)
  have hreal : r ^ a ≤ m := by
    have hlogm : a * Real.log r < Real.log m := (div_lt_iff_of_neg hlogr).mp hquot
    have hrpow : r ^ a = Real.exp (a * Real.log r) := by
      rw [Real.rpow_def_of_pos hr0, mul_comm]
    rw [hrpow, ← Real.exp_log hm0]
    exact (Real.exp_lt_exp.mpr hlogm).le
  calc ENNReal.ofReal (r ^ a) ≤ ENNReal.ofReal m := ENNReal.ofReal_le_ofReal hreal
    _ = μ (closedBall x r) := ofReal_measureReal (measure_ne_top μ _)

omit [BorelSpace E] [SecondCountableTopology E] in
/-- **A positive local-dimension limit forces positive ball masses.** If the local-dimension
quotient `log μ.real(B(x,r)) / log r` tends to a *positive* value `d`, then every closed ball
around `x` of positive radius has positive `μ`-mass. Otherwise some ball would be `μ`-null, and by
monotonicity all smaller balls too, making the quotient identically `0` near `0` (as `log 0 = 0`),
contradicting `d > 0`. -/
theorem ball_mass_pos_of_tendsto_pos {μ : Measure E} {x : E} {d : ℝ} (hd : 0 < d)
    (hx : Tendsto (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r) := by
  intro r hr
  by_contra hcon
  rw [not_lt, nonpos_iff_eq_zero] at hcon
  -- The quotient is `0` on `(0, r]`, so its limit is `0`.
  have hq0 : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.log (μ.real (closedBall x s)) / Real.log s = 0 := by
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hr] with s _ hsr
    have hsub : closedBall x s ⊆ closedBall x r := closedBall_subset_closedBall hsr.2
    have hs0 : μ (closedBall x s) = 0 := le_antisymm (hcon ▸ measure_mono hsub) bot_le
    simp only [measureReal_def, hs0, ENNReal.toReal_zero, Real.log_zero, zero_div]
  have hlim0 : Tendsto (fun s => Real.log (μ.real (closedBall x s)) / Real.log s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hq0.mono fun s hsq => hsq.symm)
  exact hd.ne' (tendsto_nhds_unique hx hlim0)

/-- **The local-dimension → Hausdorff-dimension bridge (general form).** Let `μ` be a probability
measure on a metric space `E`, `0 < α`, and `s` a set of full `μ`-measure on which the
local-dimension quotient `log μ.real(B(x,r)) / log r` tends, as `r → 0⁺`, to the constant `α` *for
every* `x ∈ s`. Then `dimH s = α`.

Both inequalities use a single hypothesis. The **lower** bound `α ≤ dimH s` is the Frostman
direction `le_dimH_of_ae_tendsto_quotient`, fed by the limit holding `μ`-a.e. (it holds everywhere
on the conull `s`). The **upper** bound `dimH s ≤ α` is the Billingsley direction
`dimH_le_of_fine_cover_mass_lower`: for any `a > α` the pointwise limit produces, at arbitrarily
small radii, a lower ball bound `μ(B(x,r)) ≥ r ^ a` (the positive limit `α` guarantees the balls
have positive mass), so `dimH s ≤ a`; letting `a ↓ α` finishes.

The pointwise (not merely a.e.) limit on `s` is essential for the upper bound: a `μ`-null subset of
`s` can carry Hausdorff dimension larger than `α`, so an a.e.-only hypothesis cannot bound
`dimH s` from above. The positivity `0 < α` is needed both for Frostman (`le_dimH_of_uniform_…`
requires a positive exponent) and to force the ball masses positive. -/
theorem dimH_eq_of_localDimension_eq {μ : Measure E} [IsProbabilityMeasure μ] {α : ℝ≥0}
    (hα : 0 < α) {s : Set E} (hs : μ sᶜ = 0)
    (h : ∀ x ∈ s, Tendsto (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 (α : ℝ))) :
    dimH s = (α : ℝ≥0∞) := by
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  -- Ball masses are positive at every `x ∈ s` (from the positive limit `α`).
  have hsupp : ∀ x ∈ s, ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r) :=
    fun x hxs => ball_mass_pos_of_tendsto_pos hαR (h x hxs)
  refine le_antisymm ?_ ?_
  · -- Upper (Billingsley): `dimH s ≤ ofReal a` for every real `a > α`, then `a ↓ α`.
    have H : ∀ a : ℝ, (α : ℝ) < a → dimH s ≤ ENNReal.ofReal a := by
      intro a haα
      have ha0 : 0 ≤ a := le_of_lt (lt_trans hαR haα)
      refine dimH_le_of_fine_cover_mass_lower (μ := μ) ha0 (fun x hxs => ?_)
      exact exists_fine_ball_lower_of_tendsto haα (hsupp x hxs) (h x hxs)
    -- Take the infimum over `a > α`: `dimH s ≤ ofReal α = α`.
    refine le_of_forall_gt_imp_ge_of_dense (fun b hb => ?_)
    rcases eq_or_ne b ∞ with rfl | hbtop
    · exact le_top
    · have hbR : (α : ℝ) < b.toReal := by
        rw [← ENNReal.ofReal_coe_nnreal] at hb
        exact (ENNReal.ofReal_lt_iff_lt_toReal α.coe_nonneg hbtop).mp hb
      calc dimH s ≤ ENNReal.ofReal b.toReal := H b.toReal hbR
        _ = b := ENNReal.ofReal_toReal hbtop
  · -- Lower (Frostman): the limit holds `μ`-a.e. on `s` (it holds everywhere on the conull `s`).
    have hae : ∀ᵐ x ∂μ, Tendsto
        (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
        (𝓝[>] (0 : ℝ)) (𝓝 (α : ℝ)) := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hs
      exact fun hxs => hx (h x hxs)
    have hlow := le_dimH_of_ae_tendsto_quotient (d := (α : ℝ)) hs hae
    rwa [ENNReal.ofReal_coe_nnreal] at hlow

end Metric

/-! ## The Euclidean (finite-dimensional inner-product) specializations

These results genuinely need the inner-product / finite-dimensional structure: they speak of the
ambient dimension `finrank ℝ E`, of Haar measures, and of the absolutely-continuous local-dimension
computation `ae_tendsto_localDimension_of_absolutelyContinuous`. They reuse the metric machinery
above (a finite-dimensional inner-product space is a Borel, second-countable metric space). -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Upper bound on the Hausdorff dimension of any set.** In a finite-dimensional real
inner-product space the Hausdorff dimension of any set is bounded by the ambient dimension. -/
theorem dimH_le_finrank (s : Set E) : dimH s ≤ (finrank ℝ E : ℝ≥0∞) := by
  calc dimH s ≤ dimH (Set.univ : Set E) := dimH_mono (subset_univ s)
    _ = (finrank ℝ E : ℝ≥0∞) := Real.dimH_univ_eq_finrank E

/-- **The local-dimension → Hausdorff-dimension bridge (headline).** Let `μ` be a probability
measure on a finite-dimensional real inner-product space `E`, absolutely continuous with respect to
a Haar measure `ν`. Then every set `s` of full `μ`-measure has Hausdorff dimension equal to the
ambient dimension `finrank ℝ E`.

The upper bound is the trivial `dimH s ≤ dimH univ = finrank`. The lower bound is the
mass-distribution argument packaged in `le_dimH_of_ae_tendsto_quotient`, fed by the a.e.
local-dimension limit `ae_tendsto_localDimension_of_absolutelyContinuous`. -/
theorem dimH_eq_finrank_of_ae_full_of_absolutelyContinuous {μ ν : Measure E}
    [IsProbabilityMeasure μ] [ν.IsAddHaarMeasure] (hμν : μ ≪ ν) {s : Set E} (hs : μ sᶜ = 0) :
    dimH s = (finrank ℝ E : ℝ≥0∞) := by
  refine le_antisymm (dimH_le_finrank s) ?_
  have hle := le_dimH_of_ae_tendsto_quotient (d := (finrank ℝ E : ℝ)) hs
    (ae_tendsto_localDimension_of_absolutelyContinuous hμν)
  rwa [ENNReal.ofReal_natCast] at hle

/-- **Tie-back: the absolutely-continuous case via the general bridge.** When the ambient dimension
is positive, the headline a.c. result is recovered through `dimH_eq_of_localDimension_eq` on the
*specific* conull carrier `s₀ = {x | log μ.real(B(x,r))/log r → finrank}`, on which the local
dimension equals `finrank` *for every* point (so the pointwise Billingsley hypothesis is met). This
is a sanity check that the general bridge subsumes the a.c. computation. -/
theorem dimH_eq_finrank_carrier_of_absolutelyContinuous {μ ν : Measure E} [IsProbabilityMeasure μ]
    [ν.IsAddHaarMeasure] (hμν : μ ≪ ν) (hpos : 0 < finrank ℝ E) :
    dimH {x : E | Tendsto (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 (finrank ℝ E : ℝ))} = (finrank ℝ E : ℝ≥0∞) := by
  set s₀ : Set E := {x : E | Tendsto (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
    (𝓝[>] (0 : ℝ)) (𝓝 (finrank ℝ E : ℝ))} with hs₀_def
  -- `s₀` is conull: the a.e. limit lands exactly in `s₀`.
  have hs₀ : μ s₀ᶜ = 0 := by
    have hae := ae_tendsto_localDimension_of_absolutelyContinuous hμν
    rw [ae_iff] at hae
    rwa [show s₀ᶜ = {x : E | ¬ Tendsto
        (fun r => Real.log (μ.real (closedBall x r)) / Real.log r)
        (𝓝[>] (0 : ℝ)) (𝓝 (finrank ℝ E : ℝ))} from rfl]
  -- Apply the general bridge with `α = finrank` (a positive `ℝ≥0`).
  have hαpos : (0 : ℝ≥0) < (finrank ℝ E : ℝ≥0) := by exact_mod_cast hpos
  have hbridge := dimH_eq_of_localDimension_eq (μ := μ) (α := (finrank ℝ E : ℝ≥0)) hαpos hs₀
    (fun x hx => by
      simp only [hs₀_def, mem_setOf_eq, NNReal.coe_natCast] at hx ⊢
      exact hx)
  rw [hbridge]
  exact_mod_cast (ENNReal.coe_natCast (finrank ℝ E))

end Euclidean

end ErgodicTheory.Multifractal
