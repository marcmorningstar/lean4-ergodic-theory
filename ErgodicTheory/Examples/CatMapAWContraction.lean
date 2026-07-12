/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapAdlerWeiss

/-!
# The Adler–Weiss two-sided contraction estimate for the Arnold cat map

This module supplies the **partition-independent metric core** of the two-sided-generator argument
for the Adler–Weiss Markov partition of the Arnold cat map `catTorus` on the sup-metric torus
`T2 = Fin 2 → UnitAddCircle`.

The geometric content is: two lifts whose eigen-coordinates are controlled after `m` steps of the
dynamics (unstable coordinate small at the forward end, stable coordinate small at the backward end)
are `O(μ^m)`-close, where `μ = φ⁻²` is the contraction rate.  Concretely, if `d` is a real lift of
`x − y` whose unstable coordinate `pC (catℝ^m *ᵥ d)` is smaller than `φ` and whose stable coordinate
comes from a backward lift `dq` with `catℝ^m *ᵥ dq = d` and `|qC dq| < φ`, then
`dist x y ≤ 2·φ·μ^m` (`dist_le_of_coordDiff`).

Together with the affine-step lemma `awRep_step` (which pins down the unique branch representative
after one step of the dynamics, using injectivity of the covering projection on each golden
rectangle, `catProj_injOn_awBox`), this is exactly the quantitative input a gluing step combines
with the Adler–Weiss `MeasurePartition` and the separating-⇒-generating bridge to conclude that the
Adler–Weiss partition is two-sided generating.

## Main results

* `ErgodicTheory.CatMapToral.pC_pow_mulVec`, `qC_pow_mulVec` — iterated eigen-scaling
  `pC (catℝ^k *ᵥ v) = λ^k · pC v`, `qC (catℝ^k *ᵥ v) = μ^k · qC v`.
* `ErgodicTheory.CatMapToral.norm_le_of_coords` — the sup norm is bounded by the sum of the
  absolute eigen-coordinates, `‖v‖ ≤ |pC v| + |qC v|`.
* `ErgodicTheory.CatMapToral.catProj_injOn_awBox` — the covering projection is injective on each
  golden rectangle `awBox b` (a restriction of `catProj_injOn_awUnion`).
* `ErgodicTheory.CatMapToral.awRep_step` — the one-step affine identity for branch representatives
  along an admissible transition.
* `ErgodicTheory.CatMapToral.dist_le_of_coordDiff` — the two-sided `μ^m`-contraction estimate.
-/

open Matrix

noncomputable section

namespace ErgodicTheory.CatMapToral

/-! ## Iterated eigen-scaling -/

/-- **Iterated unstable scaling:** `pC (catℝ^k *ᵥ v) = λ^k · pC v`. -/
lemma pC_pow_mulVec (k : ℕ) (v : Fin 2 → ℝ) : pC ((catℝ ^ k) *ᵥ v) = lam ^ k * pC v := by
  induction k with
  | zero => simp
  | succ j ih => rw [pow_succ', ← Matrix.mulVec_mulVec, pC_mulVec, ih]; ring

/-- **Iterated stable scaling:** `qC (catℝ^k *ᵥ v) = μ^k · qC v`. -/
lemma qC_pow_mulVec (k : ℕ) (v : Fin 2 → ℝ) : qC ((catℝ ^ k) *ᵥ v) = mu ^ k * qC v := by
  induction k with
  | zero => simp
  | succ j ih => rw [pow_succ', ← Matrix.mulVec_mulVec, qC_mulVec, ih]; ring

/-! ## The sup norm from the eigen-coordinates -/

/-- **The sup norm is controlled by the eigen-coordinates:** `‖v‖ ≤ |pC v| + |qC v|`.  Inverting the
`(pC, qC)`-change of coordinates, each Cartesian coordinate is a golden-field combination of `pC`
and `qC` with coefficients below `1`, so its absolute value is at most `|pC v| + |qC v|`. -/
lemma norm_le_of_coords (v : Fin 2 → ℝ) : ‖v‖ ≤ |pC v| + |qC v| := by
  have hpos := phiAW_pos
  have hsq := phiAW_sq
  have hden : (0 : ℝ) < phiAW ^ 2 + 1 := by positivity
  have hv0 : (phiAW ^ 2 + 1) * v 0 = phiAW * pC v + qC v := by simp only [pC, qC]; ring
  have hv1 : (phiAW ^ 2 + 1) * v 1 = pC v - phiAW * qC v := by simp only [pC, qC]; ring
  have hpc1 := le_abs_self (pC v)
  have hpc2 := neg_abs_le (pC v)
  have hqc1 := le_abs_self (qC v)
  have hqc2 := neg_abs_le (qC v)
  have hpn := abs_nonneg (pC v)
  have hqn := abs_nonneg (qC v)
  have hp1 := mul_le_mul_of_nonneg_left hpc1 hpos.le
  have hp2 := mul_le_mul_of_nonneg_left hpc2 hpos.le
  have hq1 := mul_le_mul_of_nonneg_left hqc1 hpos.le
  have hq2 := mul_le_mul_of_nonneg_left hqc2 hpos.le
  have h0 : |v 0| ≤ |pC v| + |qC v| := by
    rw [abs_le]
    constructor <;> nlinarith [hv0, hpc1, hpc2, hqc1, hqc2, hpn, hqn, hpos, hden, hsq,
      hp1, hp2, hq1, hq2]
  have h1 : |v 1| ≤ |pC v| + |qC v| := by
    rw [abs_le]
    constructor <;> nlinarith [hv1, hpc1, hpc2, hqc1, hqc2, hpn, hqn, hpos, hden, hsq,
      hp1, hp2, hq1, hq2]
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact h0
  · exact h1

/-! ## Injectivity of the covering projection on each golden rectangle -/

/-- **Injectivity on the golden rectangles.**  The covering projection `catProj` is injective on
each Adler–Weiss rectangle `awBox b`.  Each rectangle is one of the two pieces of the fundamental
domain `R₁ ∪ R₂`, so injectivity restricts from `catProj_injOn_awUnion`. -/
theorem catProj_injOn_awBox (b : Fin 2) : Set.InjOn catProj (awBox b) :=
  catProj_injOn_awUnion.mono (awBox_subset_awUnion b)

/-! ## The one-step affine identity for branch representatives -/

/-- **Affine step for branch representatives.**  Suppose `r` is a lift in the `e`-th branch of a
toral point `catProj r`, and `r'` a lift in the `e'`-th branch of its image `catTorus (catProj r)`
along an **admissible** transition `tgt e = src e'`.  Then `r'` is exactly the affine image
`catℝ *ᵥ r − off e`.  Both candidates lie in the single rectangle `awBox (tgt e)` and project to the
same toral point, so injectivity of `catProj` there identifies them. -/
theorem awRep_step {e e' : Fin 5} (hadm : tgt e = src e') {r r' : Fin 2 → ℝ}
    (hr : r ∈ branchBox e) (hr' : r' ∈ branchBox e')
    (hrr' : catProj r' = catTorus (catProj r)) :
    r' = catℝ *ᵥ r - off e := by
  have h1 : catℝ *ᵥ r - off e ∈ awBox (tgt e) := branch_step e hr
  have h2 : catProj (catℝ *ᵥ r - off e) = catTorus (catProj r) := by
    rw [catProj_sub, catProj_off, sub_zero, catProj_mulVec]
  have hr'box : r' ∈ awBox (tgt e) := by
    rw [hadm]; exact branchBox_subset_awBox_src e' hr'
  exact catProj_injOn_awBox (tgt e) hr'box h1 (by rw [hrr', h2])

/-! ## The two-sided contraction estimate -/

/-- **Two-sided `μ^m`-contraction.**  Let `d` be a real lift of `x − y` (`catProj d = x − y`) whose
unstable coordinate is controlled at the forward end of an `m`-step window
(`|pC (catℝ^m *ᵥ d)| < φ`), and let `dq` be a backward lift with `catℝ^m *ᵥ dq = d` and controlled
stable coordinate `|qC dq| < φ`.  Then `x` and `y` are `2·φ·μ^m`-close.

This is the metric heart of the two-sided generator argument: matching Adler–Weiss itineraries over
`[−m, m]` produce exactly such lifts (the unstable coordinate contracts by `μ^m` forward, the stable
coordinate by `μ^m` backward), so points with the same bi-infinite itinerary coincide. -/
theorem dist_le_of_coordDiff (x y : T2) (m : ℕ) (d : Fin 2 → ℝ) (hxy : catProj d = x - y)
    (hpm : |pC ((catℝ ^ m) *ᵥ d)| < phiAW) (dq : Fin 2 → ℝ) (hdq : (catℝ ^ m) *ᵥ dq = d)
    (hqm : |qC dq| < phiAW) :
    dist x y ≤ 2 * phiAW * mu ^ m := by
  have hmupos : (0 : ℝ) ≤ mu ^ m := pow_nonneg mu_pos.le m
  have hlm : mu ^ m * lam ^ m = 1 := by rw [← mul_pow, mul_comm, lam_mul_mu, one_pow]
  -- Unstable coordinate at time 0: `pC d = μ^m · pC (catℝ^m *ᵥ d)`, hence `|pC d| ≤ φ · μ^m`.
  have hpd0 : pC d = mu ^ m * pC ((catℝ ^ m) *ᵥ d) := by
    rw [pC_pow_mulVec, ← mul_assoc, hlm, one_mul]
  have hpd : |pC d| ≤ phiAW * mu ^ m := by
    rw [hpd0, abs_mul, abs_of_nonneg hmupos]
    nlinarith [hpm, hmupos, phiAW_pos, abs_nonneg (pC ((catℝ ^ m) *ᵥ d))]
  -- Stable coordinate at time 0: `qC d = μ^m · qC dq`, hence `|qC d| ≤ φ · μ^m`.
  have hqd0 : qC d = mu ^ m * qC dq := by rw [← hdq, qC_pow_mulVec]
  have hqd : |qC d| ≤ phiAW * mu ^ m := by
    rw [hqd0, abs_mul, abs_of_nonneg hmupos]
    nlinarith [hqm, hmupos, phiAW_pos, abs_nonneg (qC dq)]
  -- `dist x y ≤ ‖d‖`, because `catProj` is nonexpanding and `catProj d = x − y`.
  have hcp0 : catProj (0 : Fin 2 → ℝ) = 0 := by funext i; simp [catProj]
  have hdist : dist x y ≤ ‖d‖ := by
    calc dist x y = ‖x - y‖ := dist_eq_norm x y
      _ = ‖catProj d‖ := by rw [hxy]
      _ = dist (catProj d) 0 := by rw [dist_eq_norm, sub_zero]
      _ ≤ ‖d‖ := by have h := dist_catProj_le d 0; rwa [hcp0, sub_zero] at h
  -- Combine: `‖d‖ ≤ |pC d| + |qC d| ≤ 2·φ·μ^m`.
  have hsum : 2 * phiAW * mu ^ m = phiAW * mu ^ m + phiAW * mu ^ m := by ring
  calc dist x y ≤ ‖d‖ := hdist
    _ ≤ |pC d| + |qC d| := norm_le_of_coords d
    _ ≤ 2 * phiAW * mu ^ m := by rw [hsum]; linarith [hpd, hqd]

end ErgodicTheory.CatMapToral

end
