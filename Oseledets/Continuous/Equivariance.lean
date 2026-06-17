/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.Flow
import Oseledets.Continuous.Reduction
import Oseledets.Ergodic.Birkhoff
import Oseledets.Lyapunov.Extensions.Corollaries
import Oseledets.Cocycle.FurstenbergKesten

/-!
# Equivariance of the continuous-flow Oseledets filtration at every real time

The discrete Oseledets multiplicative ergodic theorem produces, for the time-`1` generator
`A 1` over the time-`1` dynamics `φ 1`, a filtration `V` that is equivariant under the cocycle
*one integer step at a time*. This file upgrades that to equivariance under the flow at **every
real time** `t₀ : ℝ`: almost everywhere,
`Submodule.map (toEuclideanCLM (A t₀ x)) (V i x) = V i (φ t₀ x)`.

The route is purely analytic and follows the canonical growth characterization
`Oseledets.IsOseledetsFiltration.ae_mem_iff_limsup_le`: a vector lies in the level `V i` iff it
is zero or its discrete-time Lyapunov growth rate is `≤ lam i`. The fixed-time matrix `A t₀ x`
is a *bounded* (operator-norm-comparable to a constant in `n`) bijection, so applying it to a
vector changes the discrete-time `limsup` growth rate by `o(1)`, hence not at all. Membership in
the growth sublevel set is therefore preserved, which is exactly equivariance.

## Main results

* `Oseledets.norm_clm_pos`: for invertible `M` and nonzero `v`, `0 < ‖toEuclideanCLM M v‖`.
* `Oseledets.ae_tendsto_logNorm_fixedTime_zero`: almost everywhere, the fixed-time log-norms
  `n⁻¹ · log ‖A t₀ (φ (n:ℝ) x)‖` and `n⁻¹ · log ‖(A t₀ (φ (n:ℝ) x))⁻¹‖` tend to `0`.
* `Oseledets.glim_shift`: almost everywhere, the discrete-time growth `limsup` is unchanged by
  applying `toEuclideanCLM (A t₀ x)` to the test vector.
* `Oseledets.ae_flow_equivariant`: almost everywhere, the Oseledets filtration is equivariant
  under the flow at the real time `t₀`.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} {μ : Measure X}

/-! ### S0: local positivity of the image norm -/

/-- **Local positivity.** For an invertible matrix `M` and a nonzero vector `v`, the image
`toEuclideanCLM M v` is nonzero, hence has positive norm. The continuous linear map
`toEuclideanCLM M` has the two-sided inverse `toEuclideanCLM M⁻¹`, so it is injective. -/
theorem norm_clm_pos (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    0 < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
  rw [norm_pos_iff]
  intro hzero
  -- `toEuclideanCLM M⁻¹` undoes `toEuclideanCLM M`, so `v = 0`, a contradiction.
  have hinv : (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹)
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul,
      Matrix.nonsing_inv_mul M (Ne.isUnit hM), map_one, ContinuousLinearMap.one_apply]
  rw [hzero, map_zero] at hinv
  exact hv hinv.symm

/-! ### S1: the fixed-time log-norm is sublinear, almost everywhere

The core difficulty is integrability of a dominator for `|log ‖A t₀ y‖|`. We build, for every
real time, an integrable function dominating *both* `log⁺ ‖A t₀ y‖` and `log⁺ ‖(A t₀ y)⁻¹‖`; the
two-sided log-norm bound `abs_log_norm_le` then turns this into an integrable dominator for the
absolute log-norm, and the orbital tail estimate finishes the squeeze. -/

/-- The product of the norm of an invertible matrix and the norm of its inverse has nonnegative
log: `0 ≤ log ‖M‖ + log ‖M⁻¹‖`. For `d = 0` both norms vanish and both logs are `0`; for
`d ≥ 1` a fixed nonzero vector gives `1 ≤ ‖M‖ · ‖M⁻¹‖`, whence the log is nonnegative. -/
private theorem zero_le_log_norm_add_log_norm_inv (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.det ≠ 0) :
    0 ≤ Real.log ‖M‖ + Real.log ‖M⁻¹‖ := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: the matrix space is trivial, so both norms are `0`.
    subst hd
    have h0 : ‖M‖ = 0 := by
      have : M = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]
    have h0' : ‖M⁻¹‖ = 0 := by
      have : M⁻¹ = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]
    rw [h0, h0', Real.log_zero, add_zero]
  · -- `d ≥ 1`: use the fixed unit vector `e₀`.
    set v : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1 with hvdef
    have hv : v ≠ 0 := by
      rw [hvdef, ne_eq, PiLp.single_eq_zero_iff]; exact one_ne_zero
    -- `‖v‖ ≤ ‖M⁻¹‖ · ‖toEuclideanCLM M v‖ ≤ ‖M⁻¹‖ · (‖M‖ · ‖v‖)`.
    have hvpos : 0 < ‖v‖ := by rwa [norm_pos_iff]
    have hlow : ‖v‖ ≤ ‖M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
      have hinv : (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹)
          ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) v) = v := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul,
          Matrix.nonsing_inv_mul M (Ne.isUnit hM), map_one, ContinuousLinearMap.one_apply]
      calc ‖v‖
          = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹)
              ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) v)‖ := by rw [hinv]
        _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ :=
            (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹).le_opNorm _
        _ = ‖M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
            rw [Matrix.l2_opNorm_toEuclideanCLM]
    have hup : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ ≤ ‖M‖ * ‖v‖ := by
      calc ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖
          ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * ‖v‖ :=
            (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm v
        _ = ‖M‖ * ‖v‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]
    have hMpos : 0 < ‖M‖ := by
      rcases lt_or_eq_of_le (norm_nonneg M) with h | h
      · exact h
      · exfalso
        have hclmpos := norm_clm_pos M hM hv
        rw [← h, zero_mul] at hup
        linarith
    have hMinvpos : 0 < ‖M⁻¹‖ := by
      rcases lt_or_eq_of_le (norm_nonneg M⁻¹) with h | h
      · exact h
      · exfalso; rw [← h, zero_mul] at hlow; linarith
    -- `1 ≤ ‖M⁻¹‖ · ‖M‖`.
    have hone : 1 ≤ ‖M⁻¹‖ * ‖M‖ := by
      have hchain : ‖v‖ ≤ (‖M⁻¹‖ * ‖M‖) * ‖v‖ := by
        calc ‖v‖ ≤ ‖M⁻¹‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) v‖ := hlow
          _ ≤ ‖M⁻¹‖ * (‖M‖ * ‖v‖) :=
              mul_le_mul_of_nonneg_left hup (le_of_lt hMinvpos)
          _ = (‖M⁻¹‖ * ‖M‖) * ‖v‖ := by ring
      nlinarith [hchain, hvpos]
    -- Take logs: `log ‖M‖ + log ‖M⁻¹‖ = log (‖M‖ · ‖M⁻¹‖) ≥ log 1 = 0`.
    rw [← Real.log_mul (ne_of_gt hMpos) (ne_of_gt hMinvpos)]
    have : (1 : ℝ) ≤ ‖M‖ * ‖M⁻¹‖ := by rw [mul_comm]; exact hone
    calc (0 : ℝ) = Real.log 1 := Real.log_one.symm
      _ ≤ Real.log (‖M‖ * ‖M⁻¹‖) := Real.log_le_log one_pos this

/-- **Two-sided log-norm bound.** For an invertible matrix `M`,
`|log ‖M‖| ≤ log⁺ ‖M‖ + log⁺ ‖M⁻¹‖`. -/
private theorem abs_log_norm_le (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0) :
    |Real.log ‖M‖| ≤ Real.posLog ‖M‖ + Real.posLog ‖M⁻¹‖ := by
  have hposM : Real.log ‖M‖ ≤ Real.posLog ‖M‖ := by
    rw [Real.posLog_def]; exact le_max_right _ _
  have hposMinv : Real.log ‖M⁻¹‖ ≤ Real.posLog ‖M⁻¹‖ := by
    rw [Real.posLog_def]; exact le_max_right _ _
  have hsum := zero_le_log_norm_add_log_norm_inv M hM
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `-(log⁺‖M‖ + log⁺‖M⁻¹‖) ≤ log ‖M‖`, i.e. `-log ‖M‖ ≤ log⁺‖M‖ + log⁺‖M⁻¹‖`.
    have h := Real.posLog_nonneg (x := ‖M‖)
    linarith [hposMinv, hsum]
  · -- `log ‖M‖ ≤ log⁺‖M‖ + log⁺‖M⁻¹‖`.
    have h := Real.posLog_nonneg (x := ‖M⁻¹‖)
    linarith [hposM]

/-- **Integrable dominator for nonnegative fixed times.** For each `n : ℕ` and each
`ρ ∈ [0,1]`, there is an integrable function `H` with `log⁺ ‖A (ρ + n) y‖ ≤ H y` and
`log⁺ ‖(A (ρ + n) y)⁻¹‖ ≤ H y` for every `y`.

The proof is by induction on `n`, splitting `A ((ρ + n) + 1) y = A (ρ + n) (φ 1 y) · A 1 y`
(and dually for the inverse via `mul_inv_rev`) and bounding `log⁺` of a product by the sum of
`log⁺`s; the inductive dominator at the shifted point `φ 1 y` stays integrable because `φ 1` is
measure-preserving. -/
private theorem exists_integrable_dom_nonneg (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y)
    (n : ℕ) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ H : X → ℝ, Integrable H μ ∧
      (∀ y, Real.posLog ‖A (ρ + n) y‖ ≤ H y) ∧
      (∀ y, Real.posLog ‖(A (ρ + n) y)⁻¹‖ ≤ H y) := by
  induction n with
  | zero =>
    refine ⟨fun y => g y + g' y, hg.add hg', ?_, ?_⟩
    · intro y
      have := hgb ρ hρ y
      simpa using le_add_of_le_of_nonneg (by simpa using this) (hg'nn y)
    · intro y
      have := hg'b ρ hρ y
      simpa using le_add_of_nonneg_of_le (hgnn y) (by simpa using this)
  | succ n ih =>
    obtain ⟨H, hHint, hHfwd, hHinv⟩ := ih
    -- The dominator at the shifted point, plus the one-step controls.
    refine ⟨fun y => H (φ 1 y) + (g y + g' y),
      ((φ.measurePreserving 1).integrable_comp_of_integrable hHint).add (hg.add hg'), ?_, ?_⟩
    · intro y
      -- `A ((ρ + n) + 1) y = A (ρ + n) (φ 1 y) · A 1 y`.
      have hsplit : A (ρ + (n + 1 : ℕ)) y = A (ρ + n) (φ 1 y) * A 1 y := by
        have hc := A.cocycle_apply 1 (ρ + n) y
        have hcast : (ρ + n) + 1 = ρ + ((n : ℝ) + 1) := by ring
        rw [hcast] at hc
        push_cast
        rw [hc]
      rw [hsplit]
      calc Real.posLog ‖A (ρ + n) (φ 1 y) * A 1 y‖
          ≤ Real.posLog (‖A (ρ + n) (φ 1 y)‖ * ‖A 1 y‖) :=
            Real.posLog_le_posLog (norm_nonneg _) (norm_mul_le _ _)
        _ ≤ Real.posLog ‖A (ρ + n) (φ 1 y)‖ + Real.posLog ‖A 1 y‖ := Real.posLog_mul
        _ ≤ H (φ 1 y) + (g y + g' y) := by
            have h1 := hHfwd (φ 1 y)
            have h2 : Real.posLog ‖A 1 y‖ ≤ g y := hgb 1 (by norm_num [Set.mem_Icc]) y
            have h3 := hg'nn y
            linarith
    · intro y
      have hsplit : A (ρ + (n + 1 : ℕ)) y = A (ρ + n) (φ 1 y) * A 1 y := by
        have hc := A.cocycle_apply 1 (ρ + n) y
        have hcast : (ρ + n) + 1 = ρ + ((n : ℝ) + 1) := by ring
        rw [hcast] at hc
        push_cast
        rw [hc]
      rw [hsplit, Matrix.mul_inv_rev]
      calc Real.posLog ‖(A 1 y)⁻¹ * (A (ρ + n) (φ 1 y))⁻¹‖
          ≤ Real.posLog (‖(A 1 y)⁻¹‖ * ‖(A (ρ + n) (φ 1 y))⁻¹‖) :=
            Real.posLog_le_posLog (norm_nonneg _) (norm_mul_le _ _)
        _ ≤ Real.posLog ‖(A 1 y)⁻¹‖ + Real.posLog ‖(A (ρ + n) (φ 1 y))⁻¹‖ := Real.posLog_mul
        _ ≤ H (φ 1 y) + (g y + g' y) := by
            have h1 := hHinv (φ 1 y)
            have h2 : Real.posLog ‖(A 1 y)⁻¹‖ ≤ g' y := hg'b 1 (by norm_num [Set.mem_Icc]) y
            have h3 := hgnn y
            linarith
where
  hgnn : ∀ y, 0 ≤ g y := fun y =>
    (Real.posLog_nonneg).trans (hgb 0 (by norm_num [Set.mem_Icc]) y)
  hg'nn : ∀ y, 0 ≤ g' y := fun y =>
    (Real.posLog_nonneg).trans (hg'b 0 (by norm_num [Set.mem_Icc]) y)

/-- **Integrable dominator for nonnegative real times.** For any real `t₀ ≥ 0` there is an
integrable `H` dominating both `log⁺ ‖A t₀ y‖` and `log⁺ ‖(A t₀ y)⁻¹‖`. Writing
`t₀ = (t₀ - ⌊t₀⌋₊) + ⌊t₀⌋₊` reduces this to `exists_integrable_dom_nonneg`. -/
private theorem exists_integrable_dom_of_nonneg (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    ∃ H : X → ℝ, Integrable H μ ∧
      (∀ y, Real.posLog ‖A t₀ y‖ ≤ H y) ∧
      (∀ y, Real.posLog ‖(A t₀ y)⁻¹‖ ≤ H y) := by
  set m : ℕ := ⌊t₀⌋₊ with hmdef
  set ρ : ℝ := t₀ - (m : ℝ) with hρdef
  have hmle : (m : ℝ) ≤ t₀ := Nat.floor_le ht₀
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; linarith
  have hρ1 : ρ ≤ 1 := by
    have hlt : t₀ < (m : ℝ) + 1 := by rw [hmdef]; exact Nat.lt_floor_add_one t₀
    rw [hρdef]; linarith
  have hsum : ρ + (m : ℝ) = t₀ := by rw [hρdef]; ring
  obtain ⟨H, hHint, hHfwd, hHinv⟩ :=
    exists_integrable_dom_nonneg φ A hg hg' hgb hg'b m ⟨hρ0, hρ1⟩
  refine ⟨H, hHint, ?_, ?_⟩
  · intro y; rw [← hsum]; exact hHfwd y
  · intro y; rw [← hsum]; exact hHinv y

/-- **Integrable dominator at every real time.** For any real `t₀` there is an integrable `H`
dominating both `log⁺ ‖A t₀ y‖` and `log⁺ ‖(A t₀ y)⁻¹‖`. For `t₀ < 0` the cocycle identity gives
`A t₀ y = (A (-t₀) (φ t₀ y))⁻¹`, transferring the nonnegative-time dominator at `-t₀` along the
measure-preserving map `φ t₀`. -/
private theorem exists_integrable_dom (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y)
    (t₀ : ℝ) :
    ∃ H : X → ℝ, Integrable H μ ∧
      (∀ y, Real.posLog ‖A t₀ y‖ ≤ H y) ∧
      (∀ y, Real.posLog ‖(A t₀ y)⁻¹‖ ≤ H y) := by
  rcases le_or_gt 0 t₀ with ht₀ | ht₀
  · exact exists_integrable_dom_of_nonneg φ A hg hg' hgb hg'b ht₀
  · -- `t₀ < 0`: set `u := -t₀ > 0`.
    obtain ⟨H, hHint, hHfwd, hHinv⟩ :=
      exists_integrable_dom_of_nonneg φ A hg hg' hgb hg'b (le_of_lt (neg_pos.mpr ht₀))
    -- The key identity: `A t₀ y = (A (-t₀) (φ t₀ y))⁻¹`.
    have hkey : ∀ y, A t₀ y = (A (-t₀) (φ t₀ y))⁻¹ := by
      intro y
      -- `A 0 y = A (-t₀) (φ t₀ y) · A t₀ y = 1`, so `(A t₀ y)⁻¹ = A (-t₀) (φ t₀ y)`.
      have hc := A.cocycle_apply t₀ (-t₀) y
      rw [show -t₀ + t₀ = (0 : ℝ) by ring, A.map_zero] at hc
      -- `hc : 1 = A (-t₀) (φ t₀ y) * A t₀ y`.
      have hinv : (A t₀ y)⁻¹ = A (-t₀) (φ t₀ y) := Matrix.inv_eq_left_inv hc.symm
      rw [← hinv, Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit (A.det_ne_zero t₀ y))]
    refine ⟨fun y => H (φ t₀ y),
      (φ.measurePreserving t₀).integrable_comp_of_integrable hHint, ?_, ?_⟩
    · intro y
      rw [hkey y]
      exact hHinv (φ t₀ y)
    · intro y
      rw [hkey y, Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit (A.det_ne_zero (-t₀) (φ t₀ y)))]
      exact hHfwd (φ t₀ y)

/-- **S1: the fixed-time log-norm is sublinear, almost everywhere.** For any real time `t₀`,
almost every `x` satisfies that both `n⁻¹ · log ‖A t₀ (φ (n:ℝ) x)‖` and
`n⁻¹ · log ‖(A t₀ (φ (n:ℝ) x))⁻¹‖` tend to `0`.

We dominate both absolute log-norms by an integrable function `G` (built from the two-sided
log-norm bound and the integrable dominator `exists_integrable_dom`), apply the orbital tail
estimate to `G` along the integer orbit of `φ 1`, and squeeze. -/
theorem ae_tendsto_logNorm_fixedTime_zero (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y)
    (t₀ : ℝ) :
    ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖A t₀ (φ (n : ℝ) x)‖) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖(A t₀ (φ (n : ℝ) x))⁻¹‖) atTop (𝓝 0) := by
  obtain ⟨H, hHint, hHfwd, hHinv⟩ := exists_integrable_dom φ A hg hg' hgb hg'b t₀
  -- The two-sided dominator `G = H + H`.
  set G : X → ℝ := fun y => H y + H y with hGdef
  have hGint : Integrable G μ := hHint.add hHint
  -- `|log ‖A t₀ y‖| ≤ G y` and `|log ‖(A t₀ y)⁻¹‖| ≤ G y` for every `y`.
  have hGfwd : ∀ y, |Real.log ‖A t₀ y‖| ≤ G y := by
    intro y
    calc |Real.log ‖A t₀ y‖|
        ≤ Real.posLog ‖A t₀ y‖ + Real.posLog ‖(A t₀ y)⁻¹‖ :=
          abs_log_norm_le (A t₀ y) (A.det_ne_zero t₀ y)
      _ ≤ G y := by rw [hGdef]; exact add_le_add (hHfwd y) (hHinv y)
  have hGinv : ∀ y, |Real.log ‖(A t₀ y)⁻¹‖| ≤ G y := by
    intro y
    have hdet : ((A t₀ y)⁻¹).det ≠ 0 := by
      have : IsUnit ((A t₀ y)⁻¹).det :=
        Matrix.isUnit_nonsing_inv_det (A := A t₀ y) (Ne.isUnit (A.det_ne_zero t₀ y))
      exact this.ne_zero
    calc |Real.log ‖(A t₀ y)⁻¹‖|
        ≤ Real.posLog ‖(A t₀ y)⁻¹‖ + Real.posLog ‖((A t₀ y)⁻¹)⁻¹‖ :=
          abs_log_norm_le ((A t₀ y)⁻¹) hdet
      _ = Real.posLog ‖(A t₀ y)⁻¹‖ + Real.posLog ‖A t₀ y‖ := by
          rw [Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit (A.det_ne_zero t₀ y))]
      _ ≤ G y := by rw [hGdef]; exact add_le_add (hHinv y) (hHfwd y)
  -- The orbital tail of `G` along the integer orbit tends to `0`.
  have htail := ae_tendsto_orbit_div_atTop_zero (φ.measurePreserving 1) hGint
  filter_upwards [htail] with x hx
  -- Rewrite `(φ 1)^[n] x = φ (n:ℝ) x`.
  have hxφ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * G (φ (n : ℝ) x)) atTop (𝓝 0) := by
    refine hx.congr (fun n => ?_)
    rw [← congrFun (φ.natCast_eq_iterate n) x]
  -- Squeeze both log-norms.
  have hbound : ∀ (B : X → ℝ), (∀ y, |Real.log (B y)| ≤ G y) →
      ∀ n : ℕ, |(n : ℝ)⁻¹ * Real.log (B (φ (n : ℝ) x))| ≤ (n : ℝ)⁻¹ * G (φ (n : ℝ) x) := by
    intro B hB n
    calc |(n : ℝ)⁻¹ * Real.log (B (φ (n : ℝ) x))|
        = (n : ℝ)⁻¹ * |Real.log (B (φ (n : ℝ) x))| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      _ ≤ (n : ℝ)⁻¹ * G (φ (n : ℝ) x) :=
          mul_le_mul_of_nonneg_left (hB _) (by positivity)
  refine ⟨?_, ?_⟩
  · refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    exact squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall (hbound (fun y => ‖A t₀ y‖) hGfwd)) hxφ
  · refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    exact squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall (hbound (fun y => ‖(A t₀ y)⁻¹‖) hGinv)) hxφ

/-! ### S2: the discrete growth `limsup` is shift-invariant under `A t₀ x`

The discrete-time growth rate `n⁻¹ · log ‖cocycle … n x · u‖` is unchanged when the test vector
is pushed through the fixed bijection `toEuclideanCLM (A t₀ x)`. We first establish a.e.
two-sided boundedness of this growth average (via the Furstenberg–Kesten Fekete bounds and the
Birkhoff ergodic theorem), then conclude with the perturbation lemma
`limsup_eq_of_sub_tendsto_zero`. -/

/-- **Boundedness of the discrete growth average.** For almost every `x`, for every nonzero
test vector `u`, the discrete-time growth average `n⁻¹ · log ‖cocycle (A 1 ·) (φ 1) n x · u‖`
has bounded range (both above and below). The upper bound comes from the Furstenberg–Kesten
Fekete bound `log ‖cocycle‖ ≤ birkhoffSum (log⁺ ‖A 1‖)`, whose Birkhoff average converges; the
lower bound is symmetric using the inverse cocycle. -/
private theorem ae_bddRange_discreteGrowth [IsFiniteMeasure μ] [NeZero d]
    (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y) :
    ∀ᵐ x ∂μ, ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 →
      BddAbove (Set.range (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n x)) u‖)) ∧
      BddBelow (Set.range (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n x)) u‖)) := by
  -- Abbreviate the generator and its pointwise log⁺ controls.
  set A₁ : X → Matrix (Fin d) (Fin d) ℝ := fun y => A 1 y with hA₁def
  have hA₁det : ∀ y, (A₁ y).det ≠ 0 := fun y => A.det_ne_zero 1 y
  have hgb₁ : ∀ y, Real.posLog ‖A₁ y‖ ≤ g y := fun y => hgb 1 (by norm_num [Set.mem_Icc]) y
  have hg'b₁ : ∀ y, Real.posLog ‖(A₁ y)⁻¹‖ ≤ g' y := fun y => hg'b 1 (by norm_num [Set.mem_Icc]) y
  -- The Birkhoff averages of `g` and `g'` converge a.e.
  have hbaG := tendsto_birkhoffAverage_ae (φ.measurePreserving 1) hg
  have hbaG' := tendsto_birkhoffAverage_ae (φ.measurePreserving 1) hg'
  filter_upwards [hbaG, hbaG'] with x hxG hxG' u hu
  -- The two convergent (hence bounded-range) sequences.
  set U : ℕ → ℝ := fun n => birkhoffAverage ℝ (φ 1) g n x +
    (n : ℝ)⁻¹ * Real.log ‖u‖ with hUdef
  set L : ℕ → ℝ := fun n => -birkhoffAverage ℝ (φ 1) g' n x +
    (n : ℝ)⁻¹ * Real.log ‖u‖ with hLdef
  have hUtend : Tendsto U atTop (𝓝 ((μ[g | MeasurableSpace.invariants (φ 1)]) x + 0)) := by
    refine hxG.add ?_
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (Real.log ‖u‖)
  have hLtend : Tendsto L atTop (𝓝 (-(μ[g' | MeasurableSpace.invariants (φ 1)]) x + 0)) := by
    refine (hxG'.neg).add ?_
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (Real.log ‖u‖)
  have hUbdd : BddAbove (Set.range U) := hUtend.bddAbove_range
  have hLbdd : BddBelow (Set.range L) := hLtend.bddBelow_range
  -- The pointwise upper bound `b' n ≤ U n` and lower bound `L n ≤ b' n`.
  set b' : ℕ → ℝ := fun n => (n : ℝ)⁻¹ *
    Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ with hb'def
  have hupper : ∀ n, b' n ≤ U n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hb'def, hUdef, hn]
    · have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      have hcocy : 0 < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ :=
        norm_clm_pos _ (det_cocycle_ne_zero hA₁det n x) hu
      have hupos : 0 < ‖u‖ := by rwa [norm_pos_iff]
      -- `log ‖cocycle · u‖ ≤ log ‖cocycle‖ + log ‖u‖`.
      have hlogle : Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖
          ≤ Real.log ‖cocycle A₁ (φ 1) n x‖ + Real.log ‖u‖ := by
        have hnorm : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖
            ≤ ‖cocycle A₁ (φ 1) n x‖ * ‖u‖ := by
          calc ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖
              ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)‖ * ‖u‖ :=
                (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)).le_opNorm u
            _ = ‖cocycle A₁ (φ 1) n x‖ * ‖u‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]
        have hcpos : 0 < ‖cocycle A₁ (φ 1) n x‖ := norm_cocycle_pos hA₁det n x
        calc Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖
            ≤ Real.log (‖cocycle A₁ (φ 1) n x‖ * ‖u‖) := Real.log_le_log hcocy hnorm
          _ = Real.log ‖cocycle A₁ (φ 1) n x‖ + Real.log ‖u‖ :=
              Real.log_mul (ne_of_gt hcpos) (ne_of_gt hupos)
      -- `log ‖cocycle‖ ≤ birkhoffSum (log⁺‖A₁‖) ≤ birkhoffSum g`.
      have hfekete : Real.log ‖cocycle A₁ (φ 1) n x‖
          ≤ birkhoffSum (φ 1) g n x := by
        refine (logNorm_cocycle_le_birkhoffSum hA₁det n x).trans ?_
        exact Finset.sum_le_sum fun k _ => hgb₁ _
      -- Multiply by `n⁻¹ ≥ 0`.
      have hb'le : b' n ≤ (n : ℝ)⁻¹ * (birkhoffSum (φ 1) g n x + Real.log ‖u‖) := by
        rw [hb'def]
        exact mul_le_mul_of_nonneg_left (by linarith [hlogle, hfekete]) hninv
      calc b' n ≤ (n : ℝ)⁻¹ * (birkhoffSum (φ 1) g n x + Real.log ‖u‖) := hb'le
        _ = U n := by simp only [hUdef, birkhoffAverage, smul_eq_mul]; ring
  have hlower : ∀ n, L n ≤ b' n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hb'def, hLdef, hn]
    · have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      have hcocy : 0 < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ :=
        norm_clm_pos _ (det_cocycle_ne_zero hA₁det n x) hu
      have hupos : 0 < ‖u‖ := by rwa [norm_pos_iff]
      have hinvpos : 0 < ‖(cocycle A₁ (φ 1) n x)⁻¹‖ := norm_inv_cocycle_pos hA₁det n x
      -- `log ‖u‖ ≤ log ‖(cocycle)⁻¹‖ + log ‖cocycle · u‖`.
      have hloge : Real.log ‖u‖ ≤ Real.log ‖(cocycle A₁ (φ 1) n x)⁻¹‖
          + Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ := by
        have hnorm : ‖u‖ ≤ ‖(cocycle A₁ (φ 1) n x)⁻¹‖
            * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ := by
          have hid : (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)⁻¹)
              ((Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u) = u := by
            rw [← ContinuousLinearMap.mul_apply, ← map_mul,
              Matrix.nonsing_inv_mul _ (Ne.isUnit (det_cocycle_ne_zero hA₁det n x)),
              map_one, ContinuousLinearMap.one_apply]
          calc ‖u‖
              = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)⁻¹)
                  ((Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u)‖ := by rw [hid]
            _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)⁻¹‖
                  * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ :=
                (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)⁻¹).le_opNorm _
            _ = ‖(cocycle A₁ (φ 1) n x)⁻¹‖
                  * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ := by
                rw [Matrix.l2_opNorm_toEuclideanCLM]
        calc Real.log ‖u‖
            ≤ Real.log (‖(cocycle A₁ (φ 1) n x)⁻¹‖
                * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖) :=
              Real.log_le_log hupos hnorm
          _ = Real.log ‖(cocycle A₁ (φ 1) n x)⁻¹‖
                + Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A₁ (φ 1) n x)) u‖ :=
              Real.log_mul (ne_of_gt hinvpos) (ne_of_gt hcocy)
      -- `log ‖(cocycle)⁻¹‖ ≤ birkhoffSum (log⁺‖A₁⁻¹‖) ≤ birkhoffSum g'`.
      have hfekete : Real.log ‖(cocycle A₁ (φ 1) n x)⁻¹‖
          ≤ birkhoffSum (φ 1) g' n x := by
        refine (logNorm_inv_cocycle_le_birkhoffSum hA₁det n x).trans ?_
        exact Finset.sum_le_sum fun k _ => hg'b₁ _
      -- So `log ‖cocycle · u‖ ≥ log ‖u‖ - birkhoffSum g'`. Multiply by `n⁻¹ ≥ 0`.
      have hge : (n : ℝ)⁻¹ * (-birkhoffSum (φ 1) g' n x + Real.log ‖u‖) ≤ b' n := by
        rw [hb'def]
        exact mul_le_mul_of_nonneg_left (by linarith [hloge, hfekete]) hninv
      calc L n = (n : ℝ)⁻¹ * (-birkhoffSum (φ 1) g' n x + Real.log ‖u‖) := by
            simp only [hLdef, birkhoffAverage, smul_eq_mul]; ring
        _ ≤ b' n := hge
  -- Transfer boundedness of `U`, `L` to `b'`.
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC⟩ := hUbdd
    exact ⟨C, by rintro _ ⟨n, rfl⟩; exact (hupper n).trans (hC ⟨n, rfl⟩)⟩
  · obtain ⟨c, hc⟩ := hLbdd
    exact ⟨c, by rintro _ ⟨n, rfl⟩; exact (hc ⟨n, rfl⟩).trans (hlower n)⟩

/-- **S2: the discrete growth `limsup` is shift-invariant under `A t₀ x`.** Almost everywhere,
for every test vector `u`, the discrete-time growth `limsup` of `cocycle … n x` applied to `u`
equals that of `cocycle … n (φ t₀ x)` applied to the pushed-forward vector
`toEuclideanCLM (A t₀ x) u`. The fixed bijection `A t₀ x` perturbs the per-step log-norm only by
`o(n)`, by the fixed-time sublinearity `ae_tendsto_logNorm_fixedTime_zero`. -/
theorem glim_shift [IsFiniteMeasure μ]
    (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y)
    (t₀ : ℝ) :
    ∀ᵐ x ∂μ, ∀ (u : EuclideanSpace ℝ (Fin d)),
      limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x))
              ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)) u)‖) atTop
        = limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n x) u‖) atTop := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: every vector is zero, both `limsup`s are of `log ‖0‖ = 0`.
    filter_upwards with x u
    have hu0 : u = 0 := by subst hd; exact Subsingleton.elim _ _
    subst hu0
    simp
  · haveI : NeZero d := ⟨hd.ne'⟩
    filter_upwards [ae_tendsto_logNorm_fixedTime_zero φ A hg hg' hgb hg'b t₀,
      ae_bddRange_discreteGrowth φ A hg hg' hgb hg'b] with x hxS1 hxbdd u
    obtain ⟨hxfwd, hxinv⟩ := hxS1
    -- Abbreviations.
    set b' : ℕ → ℝ := fun n => (n : ℝ)⁻¹ *
      Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n x)) u‖
      with hb'def
    set c : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x))
            ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)) u)‖ with hcdef
    rcases eq_or_ne u 0 with rfl | hu
    · -- `u = 0`: both sequences are identically `0`.
      have hc0 : c = fun _ => 0 := by
        funext n; simp [hcdef, map_zero]
      have hb'0 : b' = fun _ => 0 := by
        funext n; simp [hb'def, map_zero]
      rw [hc0, hb'0]
    · -- `u ≠ 0`: the substantive case.
      obtain ⟨hbddA, hbddB⟩ := hxbdd u hu
      -- The shift identity: `c n` is the log-norm of `A t₀ (φ_n x)` applied to `w n`.
      set w : ℕ → EuclideanSpace ℝ (Fin d) := fun n =>
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n x)) u with hwdef
      have hwne : ∀ n, w n ≠ 0 := by
        intro n
        simp only [hwdef, ne_eq, ← norm_pos_iff]
        exact norm_clm_pos _ (det_cocycle_ne_zero (fun y => A.det_ne_zero 1 y) n x) hu
      have hshift : ∀ n : ℕ,
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x)))
              ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)) u)
            = (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n) := by
        intro n
        have hmat : cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x) * A t₀ x
            = A t₀ (φ (n : ℝ) x) * cocycle (fun y => A 1 y) (φ 1) n x := by
          rw [← A.toCocycle_eq n (φ t₀ x), ← A.toCocycle_eq n x,
            ← A.cocycle_apply t₀ (n : ℝ) x, ← A.cocycle_apply (n : ℝ) t₀ x, add_comm]
        calc (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x)))
                ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)) u)
            = (Matrix.toEuclideanCLM (𝕜 := ℝ)
                (cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x) * A t₀ x)) u := by
              rw [map_mul, ContinuousLinearMap.mul_apply]
          _ = (Matrix.toEuclideanCLM (𝕜 := ℝ)
                (A t₀ (φ (n : ℝ) x) * cocycle (fun y => A 1 y) (φ 1) n x)) u := by rw [hmat]
          _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n) := by
              rw [hwdef, map_mul, ContinuousLinearMap.mul_apply]
      -- The two correction sequences tend to `0`.
      have hcdiff : Tendsto (fun n => c n - b' n) atTop (𝓝 0) := by
        -- Squeeze `c n - b' n` between `-n⁻¹ log‖(A t₀(φ_n x))⁻¹‖` and `n⁻¹ log‖A t₀(φ_n x)‖`.
        have hlow : ∀ n : ℕ, -((n : ℝ)⁻¹ * Real.log ‖(A t₀ (φ (n : ℝ) x))⁻¹‖) ≤ c n - b' n := by
          intro n
          rcases Nat.eq_zero_or_pos n with hn | hn
          · simp [hcdef, hb'def, hn]
          · have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
            have hwpos : 0 < ‖w n‖ := by rw [norm_pos_iff]; exact hwne n
            have hcpos : 0 < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ :=
              norm_clm_pos _ (A.det_ne_zero t₀ _) (hwne n)
            have hinvpos : 0 < ‖(A t₀ (φ (n : ℝ) x))⁻¹‖ := by
              rcases lt_or_eq_of_le (norm_nonneg ((A t₀ (φ (n : ℝ) x))⁻¹)) with h | h
              · exact h
              · exfalso
                have hbnd : ‖w n‖ ≤ ‖(A t₀ (φ (n : ℝ) x))⁻¹‖
                    * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ := by
                  have hid : (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹)
                      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)) = w n := by
                    rw [← ContinuousLinearMap.mul_apply, ← map_mul,
                      Matrix.nonsing_inv_mul _ (Ne.isUnit (A.det_ne_zero t₀ _)),
                      map_one, ContinuousLinearMap.one_apply]
                  calc ‖w n‖
                      = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹)
                          ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n))‖ := by
                        rw [hid]
                    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹‖
                          * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ :=
                        (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹).le_opNorm _
                    _ = ‖(A t₀ (φ (n : ℝ) x))⁻¹‖
                          * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ := by
                        rw [Matrix.l2_opNorm_toEuclideanCLM]
                rw [← h, zero_mul] at hbnd; linarith
            -- `b n ≤ log‖(A t₀(φ_n x))⁻¹‖ + LHSlog n`.
            have hnorm : ‖w n‖ ≤ ‖(A t₀ (φ (n : ℝ) x))⁻¹‖
                * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ := by
              have hid : (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹)
                  ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)) = w n := by
                rw [← ContinuousLinearMap.mul_apply, ← map_mul,
                  Matrix.nonsing_inv_mul _ (Ne.isUnit (A.det_ne_zero t₀ _)),
                  map_one, ContinuousLinearMap.one_apply]
              calc ‖w n‖
                  = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹)
                      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n))‖ := by rw [hid]
                _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹‖
                      * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ :=
                    (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))⁻¹).le_opNorm _
                _ = ‖(A t₀ (φ (n : ℝ) x))⁻¹‖
                      * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ := by
                    rw [Matrix.l2_opNorm_toEuclideanCLM]
            have hlogb : Real.log ‖w n‖ ≤ Real.log ‖(A t₀ (φ (n : ℝ) x))⁻¹‖
                + Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ := by
              calc Real.log ‖w n‖
                  ≤ Real.log (‖(A t₀ (φ (n : ℝ) x))⁻¹‖
                      * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖) :=
                    Real.log_le_log hwpos hnorm
                _ = Real.log ‖(A t₀ (φ (n : ℝ) x))⁻¹‖
                      + Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ :=
                    Real.log_mul (ne_of_gt hinvpos) (ne_of_gt hcpos)
            -- Conclude the lower bound on `c n - b' n`.
            have hdiff : c n - b' n
                = (n : ℝ)⁻¹ *
                    (Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖
                      - Real.log ‖w n‖) := by
              simp only [hcdef, hb'def]; rw [hshift n]; simp only [hwdef]; ring
            rw [hdiff, neg_eq_neg_one_mul, ← mul_assoc, mul_comm (-1 : ℝ), mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ hninv
            rw [neg_one_mul]; linarith [hlogb]
        have hhigh : ∀ n, c n - b' n ≤ (n : ℝ)⁻¹ * Real.log ‖A t₀ (φ (n : ℝ) x)‖ := by
          intro n
          rcases Nat.eq_zero_or_pos n with hn | hn
          · simp [hcdef, hb'def, hn]
          · have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
            have hwpos : 0 < ‖w n‖ := by rw [norm_pos_iff]; exact hwne n
            have hcpos : 0 < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖ :=
              norm_clm_pos _ (A.det_ne_zero t₀ _) (hwne n)
            have hnorm : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖
                ≤ ‖A t₀ (φ (n : ℝ) x)‖ * ‖w n‖ := by
              calc ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖
                  ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))‖ * ‖w n‖ :=
                    (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))).le_opNorm _
                _ = ‖A t₀ (φ (n : ℝ) x)‖ * ‖w n‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]
            have hApos : 0 < ‖A t₀ (φ (n : ℝ) x)‖ := by
              rcases lt_or_eq_of_le (norm_nonneg (A t₀ (φ (n : ℝ) x))) with h | h
              · exact h
              · exfalso; rw [← h, zero_mul] at hnorm; linarith [hcpos]
            have hlogc : Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖
                ≤ Real.log ‖A t₀ (φ (n : ℝ) x)‖ + Real.log ‖w n‖ := by
              calc Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖
                  ≤ Real.log (‖A t₀ (φ (n : ℝ) x)‖ * ‖w n‖) := Real.log_le_log hcpos hnorm
                _ = Real.log ‖A t₀ (φ (n : ℝ) x)‖ + Real.log ‖w n‖ :=
                    Real.log_mul (ne_of_gt hApos) (ne_of_gt hwpos)
            have hdiff : c n - b' n
                = (n : ℝ)⁻¹ *
                    (Real.log ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ (φ (n : ℝ) x))) (w n)‖
                      - Real.log ‖w n‖) := by
              simp only [hcdef, hb'def]; rw [hshift n]; simp only [hwdef]; ring
            rw [hdiff]
            refine mul_le_mul_of_nonneg_left ?_ hninv
            linarith [hlogc]
        -- Squeeze: both bounding sequences tend to `0`.
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
          (by simpa using hxinv.neg) hxfwd
          (Eventually.of_forall hlow) (Eventually.of_forall hhigh)
      -- Boundedness of `c` from boundedness of `b'` plus the convergent difference.
      have hrA : BddAbove (Set.range (fun n => c n - b' n)) :=
        (hcdiff.bddAbove_range)
      have hrB : BddBelow (Set.range (fun n => c n - b' n)) :=
        (hcdiff.bddBelow_range)
      have hcA : BddAbove (Set.range c) := by
        obtain ⟨P, hP⟩ := hbddA
        obtain ⟨Q, hQ⟩ := hrA
        refine ⟨P + Q, ?_⟩
        rintro _ ⟨n, rfl⟩
        have h1 : b' n ≤ P := hP ⟨n, rfl⟩
        have h2 : c n - b' n ≤ Q := hQ ⟨n, rfl⟩
        linarith
      have hcB : BddBelow (Set.range c) := by
        obtain ⟨P, hP⟩ := hbddB
        obtain ⟨Q, hQ⟩ := hrB
        refine ⟨P + Q, ?_⟩
        rintro _ ⟨n, rfl⟩
        have h1 : P ≤ b' n := hP ⟨n, rfl⟩
        have h2 : Q ≤ c n - b' n := hQ ⟨n, rfl⟩
        linarith
      exact limsup_eq_of_sub_tendsto_zero hcA hcB hbddA hbddB hcdiff

/-! ### S3: per-time equivariance of the Oseledets filtration -/

/-- **Equivariance of the Oseledets filtration at every real time.** Let `V` be the Oseledets
filtration produced by the discrete theorem for the time-`1` generator `A 1` over the time-`1`
dynamics `φ 1`. Then for every real time `t₀`, almost everywhere the filtration is equivariant
under the flow: `Submodule.map (toEuclideanCLM (A t₀ x)) (V i x) = V i (φ t₀ x)`.

The proof combines the canonical growth characterization
`IsOseledetsFiltration.ae_mem_iff_limsup_le` at `x` and (pulled back) at `φ t₀ x`, the
shift-invariance of the growth `limsup` under `A t₀ x` (`glim_shift`), and the fact that
`toEuclideanCLM (A t₀ x)` is a bijection. The bottom level `V (Fin.last k)` is `⊥`, which maps
to `⊥`; each other level is handled by `le_antisymm` of the two membership characterizations. -/
theorem ae_flow_equivariant [IsProbabilityMeasure μ]
    (φ : MeasurePreservingFlow μ) (A : FlowCocycle φ d)
    {g g' : X → ℝ} (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖A s y‖ ≤ g y)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, Real.posLog ‖(A s y)⁻¹‖ ≤ g' y)
    {k : ℕ} {lam : Fin k → ℝ}
    {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (hV : IsOseledetsFiltration μ (φ 1) (fun x => A 1 x) k lam V) (t₀ : ℝ) :
    ∀ᵐ x ∂μ, ∀ i : Fin (k + 1),
      Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)).toLinearMap (V i x)
        = V i (φ t₀ x) := by
  have hchar := hV.ae_mem_iff_limsup_le
  have hcharφ := (φ.measurePreserving t₀).quasiMeasurePreserving.ae hchar
  have hbotφ := (φ.measurePreserving t₀).quasiMeasurePreserving.ae hV.2.2
  filter_upwards [hchar, hcharφ, hV.2.2, hbotφ, glim_shift φ A hg hg' hgb hg'b t₀]
    with x hx hxφ hxblk hxblkφ hglim
  -- Bottom level facts.
  obtain ⟨-, hbot_x, -, -, -⟩ := hxblk
  obtain ⟨-, hbot_φ, -, -, -⟩ := hxblkφ
  intro i
  -- The bijection `P = toEuclideanCLM (A t₀ x)` and its inverse.
  set P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x) with hPdef
  set Pinv : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)⁻¹ with hPinvdef
  have hPinvP : ∀ w, Pinv (P w) = w := by
    intro w
    rw [hPdef, hPinvdef, ← ContinuousLinearMap.mul_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ (Ne.isUnit (A.det_ne_zero t₀ x)), map_one,
      ContinuousLinearMap.one_apply]
  have hPPinv : ∀ w, P (Pinv w) = w := by
    intro w
    rw [hPdef, hPinvdef, ← ContinuousLinearMap.mul_apply, ← map_mul,
      Matrix.mul_nonsing_inv _ (Ne.isUnit (A.det_ne_zero t₀ x)), map_one,
      ContinuousLinearMap.one_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · -- A non-bottom level: prove by antisymmetry of the membership characterizations.
    apply le_antisymm
    · -- `map P (V i'.castSucc x) ≤ V i'.castSucc (φ t₀ x)`.
      rintro v hv
      rw [Submodule.mem_map] at hv
      obtain ⟨w, hwmem, rfl⟩ := hv
      simp only [ContinuousLinearMap.coe_coe]
      rw [hxφ i' (P w)]
      rcases (hx i' w).mp hwmem with hw0 | hwle
      · exact Or.inl (by rw [hw0, map_zero])
      · refine Or.inr ?_
        -- Rewrite the growth `limsup` at `φ t₀ x` via `glim_shift`.
        rw [hPdef, hglim w]
        exact hwle
    · -- `V i'.castSucc (φ t₀ x) ≤ map P (V i'.castSucc x)`.
      rintro v hv
      rw [Submodule.mem_map]
      refine ⟨Pinv v, ?_, ?_⟩
      · -- `Pinv v ∈ V i'.castSucc x`.
        rw [hx i' (Pinv v)]
        rcases (hxφ i' v).mp hv with hv0 | hvle
        · exact Or.inl (by rw [hv0, map_zero])
        · refine Or.inr ?_
          -- `limsup (growth of Pinv v at x) = limsup (growth of P (Pinv v) = v at φ t₀ x)`.
          calc limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
                  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (fun y => A 1 y) (φ 1) n x)
                      (Pinv v)‖) atTop
              = limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
                  ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                      (cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x))
                      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)) (Pinv v))‖) atTop :=
                (hglim (Pinv v)).symm
            _ = limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
                  ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                      (cocycle (fun y => A 1 y) (φ 1) n (φ t₀ x)) v‖) atTop := by
                rw [show (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t₀ x)) (Pinv v) = v from hPPinv v]
            _ ≤ lam i' := hvle
      · simp only [ContinuousLinearMap.coe_coe]
        exact hPPinv v
  · -- Bottom level `Fin.last k`: both sides are `⊥`.
    rw [hbot_φ, hbot_x, Submodule.map_bot]

end Oseledets
