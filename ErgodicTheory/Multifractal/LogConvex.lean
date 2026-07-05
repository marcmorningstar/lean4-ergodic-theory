/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Mul
import ErgodicTheory.Multifractal.Defs

/-!
# Coarse-grained multifractal analysis: log-convexity of the partition function

This file proves the mathematical heart of the coarse-grained multifractal theory: the
**log-convexity of the generalized partition function** `Z_q = ∑_{p i > 0} (p i) ^ q` of a finite
weight family `p : ι → ℝ` as a function of the parameter `q`, and the corresponding **concavity of
the mass exponent** `τ(q) = log Z_q / log ε` (for `0 < ε < 1`).

The proof is the classical Hölder / cumulant-convexity argument, with **no derivatives**. The
midpoint convexity inequality `Z_{a q₁ + b q₂} ≤ (Z q₁) ^ a · (Z q₂) ^ b` (for nonnegative weights
`a, b` with `a + b = 1`) is exactly the two-term Hölder inequality with conjugate exponents
`1/a, 1/b`; taking logarithms and using monotonicity of `log` turns it into the convexity
inequality for `log ∘ Z`.

## Main results

* `ErgodicTheory.Multifractal.partitionFunction_holder`: the multiplicative Hölder inequality
  `Z_{a q₁ + b q₂} ≤ (Z q₁) ^ a · (Z q₂) ^ b`.
* `ErgodicTheory.Multifractal.logPartitionFunction_convexOn`: `q ↦ log Z_q` is convex on `ℝ`.
* `ErgodicTheory.Multifractal.massExponent_concaveOn`: for `0 < ε < 1`, the mass exponent
  `q ↦ τ(q) = log Z_q / log ε` is concave on `ℝ` (the negative factor `1 / log ε` flips
  convex to concave).
-/

open Real

namespace ErgodicTheory.Multifractal

variable {ι : Type*} [Fintype ι]

/-- **Multiplicative Hölder inequality** for the partition function. For nonnegative weights
`a, b` with `a + b = 1` and any exponents `q₁, q₂`, the partition function at the convex
combination `a q₁ + b q₂` is bounded by the weighted geometric mean of the partition functions at
`q₁` and `q₂`:
`Z_{a q₁ + b q₂} ≤ (Z q₁) ^ a · (Z q₂) ^ b`.
This is the two-term Hölder inequality with conjugate exponents `1/a, 1/b` applied on the support
`{i : 0 < p i}`. -/
lemma partitionFunction_holder {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) {a b q₁ q₂ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    partitionFunction p (a * q₁ + b * q₂) ≤
      (partitionFunction p q₁) ^ a * (partitionFunction p q₂) ^ b := by
  -- The guarded summands for `q₁` and `q₂`.
  set u : ι → ℝ := fun i => if 0 < p i then (p i) ^ q₁ else 0 with hu
  set v : ι → ℝ := fun i => if 0 < p i then (p i) ^ q₂ else 0 with hv
  have hu0 : ∀ i, 0 ≤ u i := by
    intro i; simp only [hu]; split
    · exact rpow_nonneg (hp i) q₁
    · exact le_refl 0
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i; simp only [hv]; split
    · exact rpow_nonneg (hp i) q₂
    · exact le_refl 0
  -- Hölder's inequality with `f i = (u i) ^ a`, `g i = (v i) ^ b` and exponents `1/a, 1/b`.
  have hconj : (1 / a).HolderConjugate (1 / b) := Real.holderConjugate_one_div ha hb hab
  have hf0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (u i) ^ a := fun i _ => rpow_nonneg (hu0 i) a
  have hg0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (v i) ^ b := fun i _ => rpow_nonneg (hv0 i) b
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hconj hf0 hg0
  -- `((u i) ^ a) ^ (1/a) = u i` since `u i ≥ 0` and `a * (1/a) = 1`.
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hpow1 : ∀ i, ((u i) ^ a) ^ (1 / a) = u i := by
    intro i
    rw [← rpow_mul (hu0 i), mul_one_div, div_self ha', rpow_one]
  have hpow2 : ∀ i, ((v i) ^ b) ^ (1 / b) = v i := by
    intro i
    rw [← rpow_mul (hv0 i), mul_one_div, div_self hb', rpow_one]
  -- The product term `(u i)^a * (v i)^b` equals the guarded summand of `Z` at `a q₁ + b q₂`.
  have hprod : ∀ i, (u i) ^ a * (v i) ^ b =
      (if 0 < p i then (p i) ^ (a * q₁ + b * q₂) else 0) := by
    intro i
    by_cases hi : 0 < p i
    · simp only [hu, hv, if_pos hi]
      rw [← rpow_mul (le_of_lt hi), ← rpow_mul (le_of_lt hi),
        ← rpow_add hi, mul_comm q₁ a, mul_comm q₂ b]
    · simp only [hu, hv, if_neg hi, zero_rpow ha', zero_rpow hb', mul_zero]
  -- Assemble: rewrite all three sums and conclude.
  calc partitionFunction p (a * q₁ + b * q₂)
      = ∑ i, (u i) ^ a * (v i) ^ b := by
        rw [partitionFunction]; exact (Finset.sum_congr rfl fun i _ => (hprod i).symm)
    _ ≤ (∑ i, ((u i) ^ a) ^ (1 / a)) ^ (1 / (1 / a)) *
          (∑ i, ((v i) ^ b) ^ (1 / b)) ^ (1 / (1 / b)) := hholder
    _ = (partitionFunction p q₁) ^ a * (partitionFunction p q₂) ^ b := by
        simp_rw [hpow1, hpow2, one_div_one_div]
        rw [partitionFunction, partitionFunction]

/-- The logarithm of the partition function, `q ↦ log Z_q`, is **convex** on all of `ℝ`. This is
the cumulant-convexity / Hölder property and is the mathematical core of the multifractal theory.
The hypothesis `∃ i, 0 < p i` guarantees `Z_q > 0` so the logarithm is well behaved. -/
lemma logPartitionFunction_convexOn {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hpos : ∃ i, 0 < p i) :
    ConvexOn ℝ Set.univ (fun q => Real.log (partitionFunction p q)) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_univ, fun q₁ _ q₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  -- Take logs of the multiplicative Hölder inequality.
  have hZ1 : 0 < partitionFunction p q₁ := partitionFunction_pos hpos q₁
  have hZ2 : 0 < partitionFunction p q₂ := partitionFunction_pos hpos q₂
  have hZc : 0 < partitionFunction p (a * q₁ + b * q₂) :=
    partitionFunction_pos hpos (a * q₁ + b * q₂)
  have hholder := partitionFunction_holder hp ha hb hab (q₁ := q₁) (q₂ := q₂)
  have hlog := Real.log_le_log hZc hholder
  rw [Real.log_mul (ne_of_gt (rpow_pos_of_pos hZ1 a)) (ne_of_gt (rpow_pos_of_pos hZ2 b)),
    Real.log_rpow hZ1, Real.log_rpow hZ2] at hlog
  exact hlog

/-- For a scale `0 < ε < 1` the mass exponent `q ↦ τ(q) = log Z_q / log ε` is **concave** on `ℝ`.
Since `log ε < 0`, dividing the convex `log Z_q` by `log ε` flips convexity to concavity. -/
lemma massExponent_concaveOn {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hpos : ∃ i, 0 < p i)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ConcaveOn ℝ Set.univ (fun q => massExponent p ε q) := by
  have hlogε : Real.log ε < 0 := Real.log_neg hε0 hε1
  set c : ℝ := -(Real.log ε)⁻¹ with hc
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg, inv_nonpos]; exact le_of_lt hlogε
  -- `c • log Z` is convex, so its negation `massExponent` is concave.
  have hconv := (logPartitionFunction_convexOn hp hpos).smul hc0
  have hconc := hconv.neg
  refine hconc.congr (fun q _ => ?_)
  simp only [Pi.neg_apply, smul_eq_mul, hc, massExponent]
  rw [neg_mul, neg_neg, div_eq_mul_inv, mul_comm]

end ErgodicTheory.Multifractal
