/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue4.CoveringFromVolume
import Frontier.Issue4.VolumeDistortion
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# The one-step local covering count (geometric heart of the sharp Margulis–Ruelle bound)

This module bounds the **covering number of the image of a small ball** under a continuous linear
map on Euclidean space.  It is the geometric heart of the *sharp* Margulis–Ruelle inequality
(Liao–Qiu, *Margulis–Ruelle inequality for general manifolds*, §3, Lemmas 3.2–3.3): the entropy
contribution of one dynamical step is controlled by how many balls of radius `~ε` are needed to
cover `g '' B(x, ε)`, and Liao–Qiu's Lemma 3.3 shows this count is `≲ ‖(D_x g)^∧‖`, i.e. the
**positive-part singular-value product** `∏ᵢ max(1, σᵢ(D_x g))`.

## The route taken here

We use the *volume → covering* route named in the design:

* `Frontier.Issue4.CoveringFromVolume` turns a bound on the volume of the **closed thickening** of a
  set into a bound on its covering number:
  `coveringNumber ε S ≤ V / ((ε/2) ^ d * μ (ball 0 1))` once `μ (cthickening (ε/2) S) ≤ V`.
* The image `L '' closedBall x ε` of a ball under a continuous linear map `L` lies in the ball
  `closedBall (L x) (‖L‖ * ε)` (operator-norm bound), so its `ε/2`-thickening is exactly
  `closedBall (L x) (ε/2 + ‖L‖ ε)` (`Metric.cthickening_closedBall`), of Haar volume
  `(ε/2 + ‖L‖ ε) ^ d · μ (ball 0 1)`.

Dividing, the dimensional constant `μ (ball 0 1)` cancels and one obtains the clean **isotropic**
covering count
`coveringNumber ε (L '' closedBall x ε) ≤ (2 ‖L‖ + 1) ^ d`,
with **no smallness hypothesis on `ε`** beyond positivity and **no `C¹` linearisation error**, since
`L` is genuinely linear.  This is the `k = d` (top) truncation of the positive-part product
`∏ᵢ max(1, σᵢ) = ⨆_{k≤d} ∏_{i<k} σᵢ` (`Frontier.Issue4.VolumeDistortion`): writing `σ₀ = ‖L‖`,
`∏ᵢ max(1, σᵢ) ≤ (1 + σ₀) ^ d`, so the isotropic bound is a *valid but non-sharp* upper bound for
the positive-part product (`Oseledets.prod_max_one_singularValues_le_one_add_opNorm_pow`).

## What is sharp and what is not (a recorded obstruction)

The genuinely **sharp** count `≲ ∏ᵢ max(1, σᵢ(L))` (anisotropic: a thin pancake needs *few* balls
along its thin directions) cannot be reached by the *isotropic* volume bound above, which only sees
`‖L‖ = σ₀`.  The sharp count requires either

* a **constructive SVD diagonalisation** `L = U Σ Vᵀ` with `U, V` orthogonal (so that covering
  `L '' ball = U (Σ '' ball)` reduces, by isometry-invariance of covering numbers
  `Isometry.coveringNumber_image`, to covering the *axis-aligned* ellipsoid `Σ '' ball`, an explicit
  product box of sides `σᵢ ε` covered by `∏ᵢ ⌈…⌉ ≲ ∏ᵢ max(1, σᵢ)` boxes — Mañé's Lemma 12.5); **or**
* a **Minkowski-sum / Steiner-formula volume bound** for `vol((L '' ball) ⊕ ball)`, giving the
  anisotropic `∏ᵢ (σᵢ ε + ε/2)` directly.

As of the pinned Mathlib (`v4.30.0-rc2`) **neither is available**: `singularValues` exposes the
values, antitonicity and `∏ σᵢ = ‖Cₖ‖` (used in `VolumeDistortion`), but **no orthonormal-basis SVD
factorisation**; and there is no Minkowski-sum volume inequality / Steiner formula.  Hence the sharp
anisotropic covering count is *infrastructure-blocked*, and this module delivers the fully honest
isotropic specialisation together with the explicit `∏ᵢ max(1, σᵢ) ≤ (1 + ‖L‖) ^ d` comparison that
locates it as the `k = d` extreme of the positive-part product.

## Main results

* `Metric.cthickening_image_closedBall_subset` — the thickened linear image lies in a single ball:
  `cthickening δ (L '' closedBall x ε) ⊆ closedBall (L x) (δ + ‖L‖ * ε)`.
* `MeasureTheory.addHaar_cthickening_image_closedBall_le` — its Haar volume bound.
* `Metric.coveringCount_image_ball_linear_le` — the **isotropic one-step covering count**:
  `coveringNumber ε (L '' closedBall x ε) ≤ ENNReal.ofReal ((2 * ‖L‖ + 1) ^ d)`.
* `Oseledets.prod_max_one_singularValues_le_one_add_opNorm_pow` — the comparison
  `∏ᵢ max(1, σᵢ(L)) ≤ (1 + ‖L‖) ^ d`, placing the sharp positive-part product below the
  isotropic count.
-/

open Metric MeasureTheory Set
open scoped ENNReal NNReal

namespace Metric

variable {d : ℕ}

/-- The image of a closed ball under a continuous linear map lies in a single closed ball of radius
scaled by the operator norm: `L '' closedBall x ε ⊆ closedBall (L x) (‖L‖ * ε)`. -/
theorem image_closedBall_subset_closedBall_opNorm
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    L '' closedBall x ε ⊆ closedBall (L x) (‖L‖ * ε) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_closedBall] at hy ⊢
  calc dist (L y) (L x) = ‖L (y - x)‖ := by rw [dist_eq_norm, ← map_sub]
    _ ≤ ‖L‖ * ‖y - x‖ := L.le_opNorm _
    _ = ‖L‖ * dist y x := by rw [dist_eq_norm]
    _ ≤ ‖L‖ * ε := by gcongr

/-- **The thickened linear image lies in a single ball.**  The closed `δ`-thickening of the image
of `closedBall x ε` under a continuous linear map `L` is contained in `closedBall (L x)
(δ + ‖L‖ * ε)`: the operator-norm bound puts the image inside `closedBall (L x) (‖L‖ ε)`, and
`Metric.cthickening_closedBall` enlarges the radius by exactly `δ`. -/
theorem cthickening_image_closedBall_subset
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    cthickening δ (L '' closedBall x ε) ⊆ closedBall (L x) (δ + ‖L‖ * ε) := by
  refine (cthickening_subset_of_subset δ
    (image_closedBall_subset_closedBall_opNorm L x ε)).trans ?_
  rw [cthickening_closedBall hδ (by positivity) (L x)]

end Metric

namespace MeasureTheory

variable {d : ℕ}

/-- **Haar volume of the thickened linear image.**  The Haar measure of the closed `δ`-thickening of
`L '' closedBall x ε` is bounded by `(δ + ‖L‖ ε) ^ d · μ (ball 0 1)` — the volume of the enclosing
ball `closedBall (L x) (δ + ‖L‖ ε)` from `Metric.cthickening_image_closedBall_subset`. -/
theorem addHaar_cthickening_image_closedBall_le
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [μ.IsAddHaarMeasure]
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    μ (cthickening δ (L '' closedBall x ε))
      ≤ ENNReal.ofReal ((δ + ‖L‖ * ε) ^ d) * μ (ball 0 1) := by
  calc μ (cthickening δ (L '' closedBall x ε))
      ≤ μ (closedBall (L x) (δ + ‖L‖ * ε)) :=
        measure_mono (Metric.cthickening_image_closedBall_subset L x hε hδ)
    _ = ENNReal.ofReal ((δ + ‖L‖ * ε) ^ d) * μ (ball 0 1) := by
        rw [Measure.addHaar_closedBall μ _ (by positivity), finrank_euclideanSpace_fin]

end MeasureTheory

namespace Metric

open MeasureTheory

variable {d : ℕ}

/-- **The isotropic one-step covering count (linear version).**  For a continuous linear map `L` on
`EuclideanSpace ℝ (Fin d)` and `ε > 0`, the `ε`-covering number of the image `L '' closedBall x ε`
is bounded by `(2 ‖L‖ + 1) ^ d`.

This is the linear instance of Liao–Qiu's one-step covering count (§3, Lemma 3.3) obtained by the
*volume → covering* route: the `ε/2`-thickening of the image fits inside
`closedBall (L x) (ε/2 + ‖L‖ ε)` (`cthickening_image_closedBall_subset`), of Haar volume
`(ε/2 + ‖L‖ ε) ^ d · μ (ball 0 1)`, and `coveringNumber_le_addHaar_div_of_addHaar_le` divides by
`(ε/2) ^ d · μ (ball 0 1)`.  The dimensional constant `μ (ball 0 1)` cancels and
`(ε/2 + ‖L‖ ε) / (ε/2) = 2 ‖L‖ + 1`.

It is the `k = d` (isotropic, top) truncation of the sharp positive-part product
`∏ᵢ max(1, σᵢ(L))`; see `Oseledets.prod_max_one_singularValues_le_one_add_opNorm_pow` for the
comparison `∏ᵢ max(1, σᵢ) ≤ (1 + ‖L‖) ^ d ≤ (2 ‖L‖ + 1) ^ d`. -/
theorem coveringCount_image_ball_linear_le
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [μ.IsAddHaarMeasure]
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) {ε : ℝ≥0} (hε : 0 < ε) :
    coveringNumber ε (L '' closedBall x (ε : ℝ))
      ≤ ENNReal.ofReal ((2 * ‖L‖ + 1) ^ d) := by
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hε0 : (0 : ℝ) ≤ (ε : ℝ) := hεr.le
  set V : ℝ≥0∞ := ENNReal.ofReal (((ε : ℝ) / 2 + ‖L‖ * ε) ^ d) * μ (ball 0 1) with hV
  -- Volume of the (ε/2)-thickening of the image.
  have hVbound : μ (cthickening ((ε : ℝ) / 2) (L '' closedBall x (ε : ℝ))) ≤ V :=
    addHaar_cthickening_image_closedBall_le μ L x hε0 (by positivity)
  -- Apply the volume → covering bound.
  have hcov := coveringNumber_le_addHaar_div_of_addHaar_le (S := L '' closedBall x (ε : ℝ))
    μ hε hVbound
  refine hcov.trans (le_of_eq ?_)
  -- Now compute the division: V / ((ε/2)^d * μ(ball 1)) = (2‖L‖ + 1)^d.
  have hμpos : 0 < μ (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    measure_ball_pos μ 0 (by norm_num)
  have hμtop : μ (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hpow : (0 : ℝ) < ((ε : ℝ) / 2) ^ d := pow_pos (by positivity) d
  -- Cancel `μ (ball 0 1)` in numerator and denominator, then divide the `ofReal`s.
  rw [hV, ENNReal.mul_div_mul_right _ _ hμpos.ne' hμtop, ← ENNReal.ofReal_div_of_pos hpow]
  congr 1
  -- `(ε/2 + ‖L‖ ε)^d / (ε/2)^d = (2‖L‖ + 1)^d`.
  rw [← div_pow]
  congr 1
  field_simp
  ring

end Metric

namespace Oseledets

open Finset

/-- **The positive-part product is dominated by the isotropic count (abstract).**  For an antitone,
nonnegative sequence `σ` (the singular values are such), every term satisfies `σᵢ ≤ σ₀`, hence
`max(1, σᵢ) ≤ 1 + σ₀`, so the positive-part product over `range d` is at most `(1 + σ 0) ^ d`.

Applied to the singular values of a continuous linear map `L` with `σ₀ = ‖L‖`, this locates the
sharp anisotropic count `∏ᵢ max(1, σᵢ)` (Liao–Qiu Lemma 3.3) *below* the isotropic count
`(2 ‖L‖ + 1) ^ d` of `Metric.coveringCount_image_ball_linear_le`:
`∏ᵢ max(1, σᵢ) ≤ (1 + σ₀) ^ d ≤ (2 σ₀ + 1) ^ d`.  This is the abstract antitone-sequence form, so it
needs no operator-norm/singular-value bridge (`σ₀ = ‖L‖`) and keeps the import footprint light. -/
theorem prod_max_one_le_one_add_top_pow {σ : ℕ → ℝ} (hanti : Antitone σ) (hpos : ∀ i, 0 ≤ σ i)
    (d : ℕ) :
    ∏ i ∈ range d, max 1 (σ i) ≤ (1 + σ 0) ^ d := by
  have hbound : ∀ i, max 1 (σ i) ≤ 1 + σ 0 := by
    intro i
    rw [max_le_iff]
    exact ⟨by linarith [hpos 0], by linarith [hanti (Nat.zero_le i)]⟩
  calc ∏ i ∈ range d, max 1 (σ i)
      ≤ ∏ _i ∈ range d, (1 + σ 0) :=
        Finset.prod_le_prod (fun i _ => le_trans zero_le_one (le_max_left _ _))
          (fun i _ => hbound i)
    _ = (1 + σ 0) ^ d := by rw [Finset.prod_const, card_range]

end Oseledets
