/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.Flow
import Oseledets.Ergodic.Birkhoff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Between integer times: continuous growth equals integer-time growth

This file is the analysis core of the **continuous-flow** Oseledets multiplicative ergodic
theorem (MET). It shows that the continuous-parameter exponential growth rate of a flow
cocycle along a fixed direction agrees with the integer-time growth rate.

Concretely, fix a measure-preserving flow `φ`, a continuous-time linear cocycle `A` over `φ`,
a point `x`, and a nonzero vector `v`. The integer-time growth
`n⁻¹ · log ‖A (n:ℝ) x · v‖` is governed by the discrete MET. The cocycle identity
`A t x = A r (φ (n:ℝ) x) · A (n:ℝ) x` for `t = r + n` with `n = ⌊t⌋₊` and `r ∈ [0,1)`
together with two integrable controls of the one-step log-norm fluctuation (forward and
inverse) lets one sandwich the continuous-time average between the integer-time average
shifted by a vanishing error. A squeeze along the floor then transfers the integer-time
limit `L` to the continuous-time limit.

## Main results

* `Oseledets.ae_tendsto_flowError_zero`: the one-step fluctuation control evaluated along the
  integer orbit, `n⁻¹ · (g (φ (n:ℝ) x) + g' (φ (n:ℝ) x))`, tends to `0` almost everywhere.
* `Oseledets.tendsto_log_norm_atTop_of_discrete`: if the integer-time average
  `n⁻¹ · log ‖A (n:ℝ) x v‖` converges to `L` and the fluctuation error vanishes, then the
  continuous-time average `t⁻¹ · log ‖A t x v‖` converges to `L` as `t → ∞`.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} {μ : Measure X}

/-! ### Operator-norm bounds for `toEuclideanCLM` of a matrix -/

/-- The continuous linear map `toEuclideanCLM M` is bounded by the (L2 operator) norm of `M`. -/
private theorem norm_toEuclideanCLM_le (M : Matrix (Fin d) (Fin d) ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ ≤ ‖M‖ * ‖v‖ := by
  calc ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * ‖v‖ :=
        (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm v
    _ = ‖M‖ * ‖v‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]

/-- A lower bound on a vector via the inverse matrix: for invertible `M`,
`‖v‖ ≤ ‖M⁻¹‖ · ‖toEuclideanCLM M v‖`. -/
private theorem norm_le_norm_inv_mul (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ ‖M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
  have hinv : (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.nonsing_inv_mul M (Ne.isUnit hM),
        map_one, ContinuousLinearMap.one_apply]
  calc ‖v‖ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) v)‖ := by
            rw [hinv]
    _ ≤ ‖M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
        calc ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) v)‖
            ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ :=
              (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹).le_opNorm _
          _ = ‖M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
              rw [Matrix.l2_opNorm_toEuclideanCLM]

/-- For an invertible matrix `M` and nonzero vector `v`, the image `toEuclideanCLM M v` has
positive norm. -/
private theorem norm_toEuclideanCLM_pos (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    0 < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
  have hvpos : 0 < ‖v‖ := by rwa [norm_pos_iff]
  have hle := norm_le_norm_inv_mul M hM v
  -- `0 < ‖v‖ ≤ ‖M⁻¹‖ * ‖toEuclideanCLM M v‖`, so the second factor must be positive.
  by_contra hcon
  rw [not_lt] at hcon
  have hzero : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ = 0 :=
    le_antisymm hcon (norm_nonneg _)
  rw [hzero, mul_zero] at hle
  linarith

/-- For an invertible matrix `M` and nonzero vector `v`, the (L2 operator) norm of `M` is
positive (it dominates `‖toEuclideanCLM M v‖ / ‖v‖ > 0`). -/
private theorem norm_pos_of_det_ne_zero (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    0 < ‖M‖ := by
  have hvpos : 0 < ‖v‖ := by rwa [norm_pos_iff]
  have hpos := norm_toEuclideanCLM_pos M hM hv
  have hle := norm_toEuclideanCLM_le M v
  by_contra hcon
  rw [not_lt] at hcon
  have hM0 : ‖M‖ = 0 := le_antisymm hcon (norm_nonneg _)
  rw [hM0, zero_mul] at hle
  linarith

/-! ### Deliverable 1: error sublinearity along the integer orbit -/

/-- **Error sublinearity, almost everywhere.** For integrable controls `g, g'`, the combined
one-step fluctuation `n⁻¹ · (g (φ (n:ℝ) x) + g' (φ (n:ℝ) x))` evaluated along the integer
orbit of the flow tends to `0` for almost every `x`.

This is the orbital-tail estimate `ae_tendsto_orbit_div_atTop_zero` for the time-`1` map of
the flow, with the integer-time orbit `(φ 1)^[n] x` rewritten as `φ (n:ℝ) x`. -/
theorem ae_tendsto_flowError_zero (φ : MeasurePreservingFlow μ)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (g (φ (n : ℝ) x) + g' (φ (n : ℝ) x)))
      atTop (𝓝 0) := by
  have h := ae_tendsto_orbit_div_atTop_zero (φ.measurePreserving 1) (hg.add hg')
  filter_upwards [h] with x hx
  refine hx.congr (fun n => ?_)
  simp only [Pi.add_apply, ← congrFun (φ.natCast_eq_iterate n) x]

/-! ### Deliverable 2: discrete limit implies continuous limit -/

set_option maxHeartbeats 800000 in
-- The sandwich combines several `calc` blocks over `toEuclideanCLM` norms and a triple
-- floor-squeeze, so the default heartbeat budget is exceeded; raise it for this command only.
/-- **Crux: continuous growth equals integer-time growth.** Fix a flow `φ`, a flow cocycle
`A`, a point `x`, and a nonzero vector `v`. Suppose:

* `g` controls the forward one-step log-norm on `[0,1]` (`Real.posLog ‖A s y‖ ≤ g y`),
* `g'` controls the inverse one-step log-norm on `[0,1]` (`Real.posLog ‖(A s y)⁻¹‖ ≤ g' y`),
* the combined fluctuation error along the integer orbit vanishes (`herr`),
* the integer-time average `n⁻¹ · log ‖A (n:ℝ) x v‖` converges to `L` (`hdisc`).

Then the continuous-time average `t⁻¹ · log ‖A t x v‖` converges to `L` as `t → ∞`.

The proof writes `t = r + n` with `n = ⌊t⌋₊ ≥ 1` and `r ∈ [0,1)`, splits the cocycle via
`A t x = A r (φ (n:ℝ) x) · A (n:ℝ) x`, and sandwiches `log ‖A t x v‖` between
`a n ± (one-step control at φ (n:ℝ) x)`; dividing by `t` and squeezing along the floor
delivers the limit. -/
theorem tendsto_log_norm_atTop_of_discrete (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ}
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y)
    {x : X} {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) {L : ℝ}
    (herr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (g (φ (n : ℝ) x) + g' (φ (n : ℝ) x)))
        atTop (𝓝 0))
    (hdisc : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A (n : ℝ) x)) v‖) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => t⁻¹ *
        Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖) atTop (𝓝 L) := by
  classical
  -- Abbreviations.
  set F : ℝ → ℝ := fun t => Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖ with hFdef
  set a : ℕ → ℝ := fun n => F (n : ℝ) with hadef
  set e : ℕ → ℝ := fun n => g (φ (n : ℝ) x) + g' (φ (n : ℝ) x) with hedef
  -- (A) Pointwise nonnegativity of the controls.
  have hgnn : ∀ y, 0 ≤ g y := fun y =>
    (Real.posLog_nonneg).trans (hgb 0 (by norm_num [Set.mem_Icc]) y)
  have hg'nn : ∀ y, 0 ≤ g' y := fun y =>
    (Real.posLog_nonneg).trans (hg'b 0 (by norm_num [Set.mem_Icc]) y)
  have henn : ∀ n : ℕ, 0 ≤ e n := fun n => by
    simp only [hedef]; exact add_nonneg (hgnn _) (hg'nn _)
  -- (B) The per-`t` sandwich for `1 ≤ t`.
  have hsandwich : ∀ t : ℝ, 1 ≤ t →
      a ⌊t⌋₊ - e ⌊t⌋₊ ≤ F t ∧ F t ≤ a ⌊t⌋₊ + e ⌊t⌋₊ := by
    intro t ht
    set n : ℕ := ⌊t⌋₊ with hndef
    set r : ℝ := t - (n : ℝ) with hrdef
    have hn1 : 1 ≤ n := (Nat.one_le_floor_iff t).2 ht
    have hnt : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
    have hr0 : 0 ≤ r := by simp only [hrdef]; linarith
    have hr1 : r < 1 := by
      have hlt := Nat.lt_floor_add_one t
      simp only [hrdef]; rw [← hndef] at hlt; linarith
    have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr0, le_of_lt hr1⟩
    have htrn : t = r + (n : ℝ) := by simp only [hrdef]; ring
    -- The cocycle split at `t = r + n`.
    have hsplit : A t x = A r (φ (n : ℝ) x) * A (n : ℝ) x := by
      have hc := A.cocycle_apply (n : ℝ) r x
      rwa [← htrn] at hc
    -- Operator split applied to `v`.
    set w : EuclideanSpace ℝ (Fin d) := (Matrix.toEuclideanCLM (𝕜 := ℝ) (A (n : ℝ) x)) v
      with hwdef
    have hopsplit : (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) (A r (φ (n : ℝ) x))) w := by
      rw [hsplit, map_mul, ContinuousLinearMap.mul_apply]
    -- Positivity facts.
    have hwpos : 0 < ‖w‖ := norm_toEuclideanCLM_pos (A (n : ℝ) x) (A.det_ne_zero _ _) hv
    have hFtpos : 0 < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖ :=
      norm_toEuclideanCLM_pos (A t x) (A.det_ne_zero _ _) hv
    have hwne : w ≠ 0 := by rw [← norm_pos_iff]; exact hwpos
    have hArpos : 0 < ‖A r (φ (n : ℝ) x)‖ :=
      norm_pos_of_det_ne_zero (A r (φ (n : ℝ) x)) (A.det_ne_zero _ _) hwne
    -- `a n = log ‖w‖`.
    have han : a n = Real.log ‖w‖ := rfl
    constructor
    · -- Lower bound: `a n - e n ≤ F t`.
      -- `‖w‖ ≤ ‖(A r (φₙx))⁻¹‖ * ‖toEuclideanCLM (A t x) v‖`.
      have hlow : ‖w‖ ≤ ‖(A r (φ (n : ℝ) x))⁻¹‖
          * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖ := by
        have := norm_le_norm_inv_mul (A r (φ (n : ℝ) x)) (A.det_ne_zero _ _) w
        rwa [← hopsplit] at this
      have hinvpos : 0 < ‖(A r (φ (n : ℝ) x))⁻¹‖ := by
        rcases lt_or_eq_of_le (norm_nonneg ((A r (φ (n : ℝ) x))⁻¹)) with h | h
        · exact h
        · exfalso; rw [← h, zero_mul] at hlow; linarith
      -- Take logs.
      have hloglow : Real.log ‖w‖ ≤ Real.log ‖(A r (φ (n : ℝ) x))⁻¹‖
          + Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖ := by
        calc Real.log ‖w‖
            ≤ Real.log (‖(A r (φ (n : ℝ) x))⁻¹‖
                * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖) := Real.log_le_log hwpos hlow
          _ = Real.log ‖(A r (φ (n : ℝ) x))⁻¹‖
                + Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖ :=
              Real.log_mul (ne_of_gt hinvpos) (ne_of_gt hFtpos)
      -- Bound the inverse log by `g' (φₙx) ≤ e n`.
      have hbound : Real.log ‖(A r (φ (n : ℝ) x))⁻¹‖ ≤ e n := by
        have h1 : Real.log ‖(A r (φ (n : ℝ) x))⁻¹‖ ≤ Real.posLog ‖(A r (φ (n : ℝ) x))⁻¹‖ := by
          rw [Real.posLog_def]; exact le_max_right _ _
        have h2 : Real.posLog ‖(A r (φ (n : ℝ) x))⁻¹‖ ≤ g' (φ (n : ℝ) x) :=
          hg'b r hrIcc (φ (n : ℝ) x)
        calc Real.log ‖(A r (φ (n : ℝ) x))⁻¹‖ ≤ g' (φ (n : ℝ) x) := h1.trans h2
          _ ≤ e n := by simp only [hedef]; linarith [hgnn (φ (n : ℝ) x)]
      -- Assemble.
      have : a n - e n ≤ F t := by
        rw [han, hFdef]
        have : Real.log ‖w‖ - e n
            ≤ Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖ := by linarith [hloglow, hbound]
        simpa using this
      exact this
    · -- Upper bound: `F t ≤ a n + e n`.
      -- `‖toEuclideanCLM (A t x) v‖ = ‖toEuclideanCLM (A r (φₙx)) w‖ ≤ ‖A r (φₙx)‖ * ‖w‖`.
      have hup : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖
          ≤ ‖A r (φ (n : ℝ) x)‖ * ‖w‖ := by
        rw [hopsplit]
        exact norm_toEuclideanCLM_le (A r (φ (n : ℝ) x)) w
      have hlogup : Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖
          ≤ Real.log ‖A r (φ (n : ℝ) x)‖ + Real.log ‖w‖ := by
        calc Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖
            ≤ Real.log (‖A r (φ (n : ℝ) x)‖ * ‖w‖) := Real.log_le_log hFtpos hup
          _ = Real.log ‖A r (φ (n : ℝ) x)‖ + Real.log ‖w‖ :=
              Real.log_mul (ne_of_gt hArpos) (ne_of_gt hwpos)
      -- Bound the forward log by `g (φₙx) ≤ e n`.
      have hbound : Real.log ‖A r (φ (n : ℝ) x)‖ ≤ e n := by
        have h1 : Real.log ‖A r (φ (n : ℝ) x)‖ ≤ Real.posLog ‖A r (φ (n : ℝ) x)‖ := by
          rw [Real.posLog_def]; exact le_max_right _ _
        have h2 : Real.posLog ‖A r (φ (n : ℝ) x)‖ ≤ g (φ (n : ℝ) x) := hgb r hrIcc (φ (n : ℝ) x)
        calc Real.log ‖A r (φ (n : ℝ) x)‖ ≤ g (φ (n : ℝ) x) := h1.trans h2
          _ ≤ e n := by simp only [hedef]; linarith [hg'nn (φ (n : ℝ) x)]
      -- Assemble.
      rw [hFdef, han]
      have : Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)) v‖
          ≤ e n + Real.log ‖w‖ := by linarith [hlogup, hbound]
      linarith [this]
  -- (C) Divide by `t`: the per-`t` sandwich on the averages.
  set Up : ℝ → ℝ := fun t => (a ⌊t⌋₊ + e ⌊t⌋₊) / t with hUpdef
  set Lo : ℝ → ℝ := fun t => (a ⌊t⌋₊ - e ⌊t⌋₊) / t with hLodef
  have hLoF : ∀ᶠ t : ℝ in atTop, Lo t ≤ t⁻¹ * F t := by
    refine eventually_atTop.2 ⟨1, fun t ht => ?_⟩
    have htpos : 0 < t := by linarith
    obtain ⟨hlo, _⟩ := hsandwich t ht
    simp only [hLodef, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hlo (by positivity)
  -- (D) The limits of `Up` and `Lo`.
  -- `(⌊t⌋₊:ℝ)⁻¹ * a ⌊t⌋₊ → L` and `(⌊t⌋₊:ℝ)⁻¹ * e ⌊t⌋₊ → 0`.
  have hflA : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ))⁻¹ * a ⌊t⌋₊) atTop (𝓝 L) :=
    hdisc.comp tendsto_nat_floor_atTop
  have hflE : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ))⁻¹ * e ⌊t⌋₊) atTop (𝓝 0) :=
    herr.comp tendsto_nat_floor_atTop
  have hfldiv : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ)) / t) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop
  -- `Up → L`.
  have hUp : Tendsto Up atTop (𝓝 L) := by
    have hprodA : Tendsto (fun t : ℝ => (((⌊t⌋₊ : ℝ))⁻¹ * a ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t))
        atTop (𝓝 (L * 1)) := hflA.mul hfldiv
    have hprodE : Tendsto (fun t : ℝ => (((⌊t⌋₊ : ℝ))⁻¹ * e ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t))
        atTop (𝓝 (0 * 1)) := hflE.mul hfldiv
    have hsum := hprodA.add hprodE
    have hUp' : Tendsto (fun t : ℝ => (((⌊t⌋₊ : ℝ))⁻¹ * a ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t)
        + (((⌊t⌋₊ : ℝ))⁻¹ * e ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t)) atTop (𝓝 L) := by
      simpa using hsum
    refine hUp'.congr' ?_
    refine eventually_atTop.2 ⟨1, fun t ht => ?_⟩
    have htpos : 0 < t := by linarith
    have hn1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).2 ht
    have hne : (⌊t⌋₊ : ℝ) ≠ 0 := by positivity
    simp only [hUpdef]
    field_simp
  -- `Lo → L`.
  have hLo : Tendsto Lo atTop (𝓝 L) := by
    have hprodA : Tendsto (fun t : ℝ => (((⌊t⌋₊ : ℝ))⁻¹ * a ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t))
        atTop (𝓝 (L * 1)) := hflA.mul hfldiv
    have hprodE : Tendsto (fun t : ℝ => (((⌊t⌋₊ : ℝ))⁻¹ * e ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t))
        atTop (𝓝 (0 * 1)) := hflE.mul hfldiv
    have hsub := hprodA.sub hprodE
    have hLo' : Tendsto (fun t : ℝ => (((⌊t⌋₊ : ℝ))⁻¹ * a ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t)
        - (((⌊t⌋₊ : ℝ))⁻¹ * e ⌊t⌋₊) * (((⌊t⌋₊ : ℝ)) / t)) atTop (𝓝 L) := by
      simpa using hsub
    refine hLo'.congr' ?_
    refine eventually_atTop.2 ⟨1, fun t ht => ?_⟩
    have htpos : 0 < t := by linarith
    have hn1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).2 ht
    have hne : (⌊t⌋₊ : ℝ) ≠ 0 := by positivity
    simp only [hLodef]
    field_simp
  -- Upper eventual bound.
  have hFUp : ∀ᶠ t : ℝ in atTop, t⁻¹ * F t ≤ Up t := by
    refine eventually_atTop.2 ⟨1, fun t ht => ?_⟩
    have htpos : 0 < t := by linarith
    obtain ⟨_, hup⟩ := hsandwich t ht
    simp only [hUpdef, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hup (by positivity)
  -- (E) Squeeze.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hUp hLoF hFUp

end Oseledets
