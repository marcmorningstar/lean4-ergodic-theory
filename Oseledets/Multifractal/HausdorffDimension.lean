/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.LocalDimension
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The local-dimension → Hausdorff-dimension bridge

This file connects the pointwise *local dimension* `d_μ(x)` of an absolutely-continuous probability
measure (formalized in `Oseledets/Multifractal/LocalDimension.lean`) to the **Hausdorff dimension**
`dimH s` of a full-measure carrier set `s`.

The headline result is:

* `Oseledets.Multifractal.dimH_eq_finrank_of_ae_full_of_absolutelyContinuous` — if `μ` is a
  probability measure on a finite-dimensional real inner-product space `E`, absolutely continuous
  w.r.t. a Haar measure, then **every** set `s` of full `μ`-measure has Hausdorff dimension equal to
  the ambient dimension `finrank ℝ E`.

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

namespace Oseledets.Multifractal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Upper bound on the Hausdorff dimension of any set.** In a finite-dimensional real
inner-product space the Hausdorff dimension of any set is bounded by the ambient dimension. -/
theorem dimH_le_finrank (s : Set E) : dimH s ≤ (finrank ℝ E : ℝ≥0∞) := by
  calc dimH s ≤ dimH (Set.univ : Set E) := dimH_mono (subset_univ s)
    _ = (finrank ℝ E : ℝ≥0∞) := Real.dimH_univ_eq_finrank E

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
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

/-- **The local-dimension → Hausdorff-dimension bridge (headline).** Let `μ` be a probability
measure on a finite-dimensional real inner-product space `E`, absolutely continuous with respect to
a Haar measure `ν`. Then every set `s` of full `μ`-measure has Hausdorff dimension equal to the
ambient dimension `finrank ℝ E`.

The upper bound is the trivial `dimH s ≤ dimH univ = finrank`. The lower bound is the
mass-distribution argument: from `ae_tendsto_localDimension_of_absolutelyContinuous` the local
dimension equals `finrank` `μ`-a.e., which yields, for each `a < finrank`, a measurable set of
positive `μ`-mass carrying a uniform ball bound `μ.real(B(x,r)) ≤ r ^ a`; the Frostman principle
`le_dimH_of_uniform_ball_bound` then gives `a ≤ dimH s`, and we let `a → finrank`. -/
theorem dimH_eq_finrank_of_ae_full_of_absolutelyContinuous {μ ν : Measure E}
    [IsProbabilityMeasure μ] [ν.IsAddHaarMeasure] (hμν : μ ≪ ν) {s : Set E} (hs : μ sᶜ = 0) :
    dimH s = (finrank ℝ E : ℝ≥0∞) := by
  refine le_antisymm (dimH_le_finrank s) ?_
  set d : ℕ := finrank ℝ E with hd_def
  -- a.e.-pointwise local dimension equals `d`.
  have hae : ∀ᵐ x ∂μ, Tendsto
      (fun r => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ)) :=
    ae_tendsto_localDimension_of_absolutelyContinuous hμν
  -- Reduce to `↑a ≤ dimH s` for every `a : ℝ≥0` with `↑a < ↑d` in `ℝ≥0∞`.
  refine ENNReal.le_of_forall_nnreal_lt (fun a ha => ?_)
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  have hapos : 0 < a := pos_iff_ne_zero.mpr ha0
  have had : (a : ℝ) < (d : ℝ) := by exact_mod_cast ha
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

end Oseledets.Multifractal
