/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Pointwise local dimension: the absolutely-continuous case

This file delivers the **absolutely-continuous (a.c.) special case** of issue #16, item 5: for a
probability measure `μ` on a finite-dimensional real normed space that is absolutely continuous with
respect to the Haar (= Lebesgue) measure, the pointwise *local dimension*
`d_μ(x) = lim_{r→0⁺} log μ(B(x,r)) / log r` exists and equals the **ambient dimension**
`finrank ℝ E`, for `μ`-almost every `x`.

This is the standard **Lebesgue-density / measure-differentiation** result and uses no dynamics:
the proof assembles

* the **Besicovitch differentiation theorem**
  `Besicovitch.ae_tendsto_rnDeriv` — `μ(closedBall x r) / ν(closedBall x r) → (dμ/dν)(x)` as
  `r → 0⁺`, `ν`-a.e.;
* the **Radon–Nikodym density is finite and positive** `μ`-a.e.
  (`Measure.rnDeriv_lt_top`, `Measure.rnDeriv_pos`) when `μ ≪ ν`;
* the **Haar ball-volume scaling** `Measure.addHaar_real_closedBall'` —
  `ν(closedBall x r) = r ^ (finrank ℝ E) · ν(closedBall 0 1)`;
* a real-analytic **logarithm limit** (proved here as `logBall_div_log_tendsto`): if
  `μ.real(B(x,r)) = ratio(r) · r^d · C` with `ratio(r) → L > 0` and `C > 0`, then
  `log μ.real(B(x,r)) / log r = (log ratio(r) + log C) / log r + d → d`, because
  `log r → -∞` kills the bounded numerator `log ratio(r) + log C` while `d · log r / log r = d`.

## Main results

* `ErgodicTheory.Multifractal.localDimension` — the upper local/pointwise dimension `d̄_μ(x)`,
  defined as the `limsup` of `log μ.real(B(x,r)) / log r` as `r → 0⁺`. In the a.c. case below the
  genuine limit exists, so this `limsup` is the honest local dimension.
* `ErgodicTheory.Multifractal.ae_tendsto_localDimension_of_absolutelyContinuous` — the headline
  a.e.-convergence of the local-dimension quotient to `finrank ℝ E`.
* `ErgodicTheory.Multifractal.ae_localDimension_eq_finrank` — the corollary
  `localDimension μ x = finrank ℝ E` for `μ`-a.e. `x`.

## Scope (what is, and is NOT, formalized here)

This is **only the absolutely-continuous case**, a pure measure-differentiation statement with no
dynamics. The general **singular / SRB exact-dimensionality** theory — the
Ledrappier–Young formula and the absolute continuity of the conditional measures on unstable
manifolds — is the deep research frontier shared with issue #10's Pesin SRB measures and is
deliberately *not* formalized here.
-/

open MeasureTheory Filter Topology Metric Set Module
open scoped ENNReal NNReal

namespace ErgodicTheory.Multifractal

/-- The **upper local (pointwise) dimension** `d̄_μ(x)` of a measure `μ` at a point `x`: the
`limsup` as `r → 0⁺` of `log μ.real(closedBall x r) / log r` (where `μ.real s = (μ s).toReal`). For
the absolutely-continuous case treated in this file the genuine limit exists, so this `limsup`
coincides with the honest local dimension `lim_{r→0⁺} log μ(B(x,r)) / log r`. -/
noncomputable def localDimension {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (μ : Measure E) (x : E) : ℝ :=
  Filter.limsup (fun r => Real.log (μ.real (Metric.closedBall x r)) / Real.log r) (𝓝[>] (0 : ℝ))

/-- **The logarithm limit.** Suppose `value : ℝ → ℝ` factors, for `r` near `0⁺`, as
`value r = ratio r · (r ^ d · C)` with `ratio r → L`, `0 < L`, and `0 < C`. Then
`log (value r) / log r → d` as `r → 0⁺`. Indeed `log (value r) = log (ratio r) + d · log r + log C`,
so the quotient is `(log (ratio r) + log C) / log r + d`; as `r → 0⁺` the factor `(log r)⁻¹ → 0`
kills the convergent numerator while the `d` term survives. -/
theorem logBall_div_log_tendsto {d : ℕ} {value ratio : ℝ → ℝ} {L C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (hratio : Tendsto ratio (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hval : ∀ᶠ r in 𝓝[>] (0 : ℝ), value r = ratio r * (r ^ d * C)) :
    Tendsto (fun r => Real.log (value r) / Real.log r) (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ)) := by
  -- `(log r)⁻¹ → 0` because `log r → -∞` on `𝓝[>] 0`.
  have hinv : Tendsto (fun r => (Real.log r)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot
  -- The numerator `log (ratio r) + log C → log L + log C` is convergent (hence bounded).
  have hnum : Tendsto (fun r => Real.log (ratio r) + Real.log C) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log L + Real.log C)) :=
    ((Real.continuousAt_log hL.ne').tendsto.comp hratio).add tendsto_const_nhds
  -- Hence `(log (ratio r) + log C) · (log r)⁻¹ → 0`.
  have hprod : Tendsto (fun r => (Real.log (ratio r) + Real.log C) * (Real.log r)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have := hnum.mul hinv
    simpa using this
  -- Add the constant `d` and rewrite the quotient on the eventual factorization region.
  have hgoal : Tendsto (fun r => (Real.log (ratio r) + Real.log C) * (Real.log r)⁻¹ + (d : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ)) := by
    simpa using hprod.add (tendsto_const_nhds (x := (d : ℝ)))
  refine hgoal.congr' ?_
  -- Eventually `r ∈ (0,1)`, so `log r ≠ 0` and the factorization holds.
  have hsmall : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hval, hsmall, hratio.eventually (eventually_gt_nhds hL)] with r hr hr01 hratiopos
  rw [hr]
  have hr0 : (0 : ℝ) < r := hr01.1
  have hr1 : r < 1 := hr01.2
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hlogr_ne : Real.log r ≠ 0 := ne_of_lt hlogr
  have hrd : (0 : ℝ) < r ^ d := pow_pos hr0 d
  -- `log (ratio r * (r^d * C)) = log (ratio r) + d * log r + log C`.
  rw [Real.log_mul hratiopos.ne' (by positivity), Real.log_mul hrd.ne' hC.ne',
    Real.log_pow]
  field_simp
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Local dimension of an absolutely-continuous probability measure (a.e. convergence).** Let `μ`
be a probability measure on a finite-dimensional real inner-product space `E`, absolutely continuous
with respect to a Haar measure `ν` (e.g. `ν = volume`). Then for `μ`-almost every `x` the
local-dimension quotient `log μ.real(B(x,r)) / log r` converges, as `r → 0⁺`, to the ambient
dimension `finrank ℝ E`.

This is the standard Lebesgue-density / measure-differentiation result: Besicovitch differentiation
gives `μ(B(x,r))/ν(B(x,r)) → (dμ/dν)(x) ∈ (0,∞)` `μ`-a.e.; the Haar ball-volume scaling
`ν(B(x,r)) = r^(finrank) · ν(B(0,1))` then turns the logarithm of `μ.real(B(x,r))` into
`log((dμ/dν)(x)) + finrank · log r + log ν.real(B(0,1)) + o(1)`, whose ratio to `log r → -∞` is
`finrank`. -/
theorem ae_tendsto_localDimension_of_absolutelyContinuous
    {μ ν : Measure E} [IsProbabilityMeasure μ] [ν.IsAddHaarMeasure] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun r => Real.log (μ.real (Metric.closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 (Module.finrank ℝ E : ℝ)) := by
  set d := Module.finrank ℝ E with hd
  -- Ball-volume scaling constant `C = ν.real (closedBall 0 1) > 0`.
  set C : ℝ := ν.real (closedBall (0 : E) 1) with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def, measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos ν 0 one_pos).ne' measure_closedBall_lt_top.ne
  -- Besicovitch differentiation: `ν`-a.e. closed-ball density limit (in `ℝ≥0∞`).
  have hbes : ∀ᵐ x ∂ν, Tendsto
      (fun r => μ (closedBall x r) / ν (closedBall x r)) (𝓝[>] (0 : ℝ))
      (𝓝 (μ.rnDeriv ν x)) := Besicovitch.ae_tendsto_rnDeriv μ ν
  -- Transfer the `ν`-a.e. density limit to `μ`-a.e. via `μ ≪ ν`; the density is finite `ν`-a.e.
  have hbes_mu : ∀ᵐ x ∂μ, Tendsto
      (fun r => μ (closedBall x r) / ν (closedBall x r)) (𝓝[>] (0 : ℝ))
      (𝓝 (μ.rnDeriv ν x)) := hμν.ae_le hbes
  have hfin : ∀ᵐ x ∂μ, μ.rnDeriv ν x < ∞ := hμν.ae_le (Measure.rnDeriv_lt_top μ ν)
  have hpos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := Measure.rnDeriv_pos hμν
  filter_upwards [hbes_mu, hfin, hpos] with x hx hxfin hxpos
  -- Real-valued density limit `L = (dμ/dν)(x).toReal ∈ (0,∞)`.
  set L : ℝ := (μ.rnDeriv ν x).toReal with hL_def
  have hL_pos : 0 < L := by
    rw [hL_def, ENNReal.toReal_pos_iff]
    exact ⟨hxpos, hxfin⟩
  -- Push the `ℝ≥0∞` density limit through `.toReal` (limit is finite).
  have hxreal : Tendsto
      (fun r => (μ (closedBall x r) / ν (closedBall x r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    (ENNReal.tendsto_toReal hxfin.ne).comp hx
  -- The `.toReal` of the ENNReal ratio is the ratio of `Measure.real`s on small balls.
  set ratio : ℝ → ℝ := fun r => μ.real (closedBall x r) / ν.real (closedBall x r) with hratio_def
  have hxreal' : Tendsto ratio (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    refine hxreal.congr' ?_
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), (0 : ℝ) < r := self_mem_nhdsWithin
    filter_upwards [hsmall] with r _
    simp only [hratio_def, measureReal_def, ENNReal.toReal_div]
  -- The factorization `μ.real(B(x,r)) = ratio r · (r^d · C)` on the eventual region `r > 0`.
  have hval : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ.real (closedBall x r) = ratio r * (r ^ d * C) := by
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), (0 : ℝ) < r := self_mem_nhdsWithin
    filter_upwards [hsmall] with r hr0
    have hvol : ν.real (closedBall x r) = r ^ d * C :=
      Measure.addHaar_real_closedBall' ν x hr0.le
    have hvol_pos : 0 < ν.real (closedBall x r) := by
      rw [hvol]; positivity
    simp only [hratio_def]
    rw [hvol]
    field_simp
  -- Assemble via the logarithm-limit lemma.
  exact logBall_div_log_tendsto hL_pos hC_pos hxreal' hval

/-- **Local dimension of an absolutely-continuous probability measure (value).** For `μ`-almost
every `x`, the upper local dimension `localDimension μ x` equals the ambient dimension
`finrank ℝ E`. This is the corollary of
`ae_tendsto_localDimension_of_absolutelyContinuous`: where the genuine limit exists, the `limsup`
defining `localDimension` returns that limit. -/
theorem ae_localDimension_eq_finrank
    {μ ν : Measure E} [IsProbabilityMeasure μ] [ν.IsAddHaarMeasure] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, localDimension μ x = (Module.finrank ℝ E : ℝ) := by
  filter_upwards [ae_tendsto_localDimension_of_absolutelyContinuous hμν] with x hx
  rw [localDimension]
  exact hx.limsup_eq

end ErgodicTheory.Multifractal
