/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MeasureTheory.CoveringFromVolume
import ErgodicTheory.Entropy.Ruelle.VolumeDistortion
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Volume-geometry building blocks for the sharp Margulis–Ruelle covering count

This module records the elementary volume-geometry facts about the **image of a small ball** under a
continuous linear map on Euclidean space, together with an abstract positive-part comparison.  They
are the building blocks of the *volume → covering* route to the Margulis–Ruelle one-step covering
count (Liao–Qiu, *Margulis–Ruelle inequality for general manifolds*, §3, Lemmas 3.2–3.3): the
entropy contribution of one dynamical step is controlled by how many balls of radius `~ε` are needed
to cover `g '' B(x, ε)`, which Liao–Qiu bound by the **positive-part singular-value product**
`∏ᵢ max(1, σᵢ(D_x g))`.

## Contents

* The image `L '' closedBall x ε` of a ball under a continuous linear map `L` lies in the ball
  `closedBall (L x) (‖L‖ * ε)` (operator-norm bound), so its `δ`-thickening lies in
  `closedBall (L x) (δ + ‖L‖ ε)` (`cthickening_image_closedBall_subset`), of Haar volume
  `(δ + ‖L‖ ε) ^ d · μ (ball 0 1)` (`addHaar_cthickening_image_closedBall_le`).  Fed into
  `ErgodicTheory.MeasureTheory.CoveringFromVolume` these give the *isotropic* covering count
  `≲ (2 ‖L‖ + 1) ^ d`, the `k = d` (top) truncation of the positive-part product that sees only
  `σ₀ = ‖L‖`.
* `ErgodicTheory.prod_max_one_le_one_add_top_pow` records the abstract comparison
  `∏ᵢ max(1, σᵢ) ≤ (1 + σ₀) ^ d`, placing the positive-part product below the isotropic count.

The genuinely **sharp anisotropic** count `≲ ∏ᵢ max(1, σᵢ(L))` (a thin pancake needs *few* balls
along its thin directions) is proved in the sibling module
`ErgodicTheory.Entropy.Ruelle.SharpCovering` (`ErgodicTheory.coveringCount_image_ball_le_volProd`,
via the
constructive `ErgodicTheory.svd_exists` + an ellipsoid-domination volume bound, with dimensional
constant `6^d`), which is the count the sharp Margulis–Ruelle track uses.

## Main results

* `Metric.cthickening_image_closedBall_subset` — the thickened linear image lies in a single ball:
  `cthickening δ (L '' closedBall x ε) ⊆ closedBall (L x) (δ + ‖L‖ * ε)`.
* `MeasureTheory.addHaar_cthickening_image_closedBall_le` — its Haar volume bound.
* `ErgodicTheory.prod_max_one_le_one_add_top_pow` — the comparison
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

namespace ErgodicTheory

open Finset

/-- **The positive-part product is dominated by the isotropic count (abstract).**  For an antitone,
nonnegative sequence `σ` (the singular values are such), every term satisfies `σᵢ ≤ σ₀`, hence
`max(1, σᵢ) ≤ 1 + σ₀`, so the positive-part product over `range d` is at most `(1 + σ 0) ^ d`.

Applied to the singular values of a continuous linear map `L` with `σ₀ = ‖L‖`, this locates the
sharp anisotropic count `∏ᵢ max(1, σᵢ)` (Liao–Qiu Lemma 3.3) *below* the isotropic count
`(2 ‖L‖ + 1) ^ d`:
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

end ErgodicTheory
