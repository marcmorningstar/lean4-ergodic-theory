/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Oseledets.Multifractal.LogConvex

/-!
# Coarse-grained multifractal analysis: monotonicity of the Rényi dimension

This file proves that the Rényi (generalized) dimension `D_q` of a finite probability weight family
`p : ι → ℝ` at a scale `0 < ε < 1` is **non-increasing in `q`** (issue item 4b).

The argument is the classical secant-slope argument. Let `h q = log Z_q` be the logarithm of the
partition function; by `logPartitionFunction_convexOn` (file `LogConvex.lean`) it is convex on `ℝ`,
and `h 1 = 0` for a probability family. The **secant slope anchored at `1`**,
`g q = (h q - h 1) / (q - 1) = h q / (q - 1)`, is therefore non-decreasing in `q` away from the
anchor (`ConvexOn.secant_mono`). For `q ≠ 1` the Rényi dimension is `D_q = g q / log ε`, and since
`log ε < 0` the division flips the monotone `g` to the antitone `D`.

The genuinely subtle point is the **information-dimension singularity `q = 1`**, where `D_1` is
defined directly as `(∑ i, p i log p i) / log ε` (the secant slope `g` itself takes a junk `0/0 = 0`
value at the anchor, so one cannot route through it). The numerator `∑ i, p i log p i` is exactly
the derivative `h'(1)` of the convex function `h`, and the convex supporting-line inequalities
`ConvexOn.le_slope_of_hasDerivAt` / `ConvexOn.slope_le_of_hasDerivAt` give `g q ≤ h'(1) ≤ g q'` for
`q < 1 < q'`. Dividing by `log ε < 0` glues `D_1` into the monotone family, so antitonicity holds
across `q = 1` as well — i.e. the *full* `Antitone` over all of `ℝ`.

## Main results

* `Oseledets.Multifractal.logPartitionFunction_secantSlope_monotoneOn`: the reusable core, the
  secant slope `q ↦ log Z_q / (q - 1)` of the (convex) `log Z` anchored at the probability point
  `q = 1` is monotone on `{q | q ≠ 1}`.
* `Oseledets.Multifractal.hasDerivAt_logPartitionFunction_one`: the derivative of `q ↦ log Z_q` at
  `q = 1` is `∑ i, p i * log (p i)` (the information-dimension numerator).
* `Oseledets.Multifractal.renyiDim_antitone`: the headline — `q ↦ D_q` is antitone on `ℝ`.
-/

open Real

namespace Oseledets.Multifractal

variable {ι : Type*} [Fintype ι]

/-- The secant slope of `q ↦ log Z_q`, anchored at the probability point `q = 1` (where
`log Z_1 = 0`), is **monotone** (non-decreasing) on `{q | q ≠ 1}`. This is the reusable core of the
monotonicity of the Rényi dimension: for `q ≠ 1`, `D_q = (this slope) / log ε`, and `log ε < 0`
flips it to antitone.

Concretely `q ↦ log Z_q / (q - 1)` is non-decreasing as `q` ranges over `{q | q ≠ 1}` (away from the
anchor, where the expression is the junk `0 / 0`). -/
lemma logPartitionFunction_secantSlope_monotoneOn {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hpos : ∃ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    MonotoneOn (fun q => Real.log (partitionFunction p q) / (q - 1)) {q : ℝ | q ≠ 1} := by
  have hconv : ConvexOn ℝ Set.univ (fun q => Real.log (partitionFunction p q)) :=
    logPartitionFunction_convexOn hp hpos
  have hone : Real.log (partitionFunction p 1) = 0 := by
    rw [partitionFunction_one_eq_one hp hsum, Real.log_one]
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  -- The secant slope anchored at `1` is monotone for `a, b ≠ 1` with `a ≤ b`.
  have key := hconv.secant_mono (a := 1) (x := a) (y := b) (Set.mem_univ _) (Set.mem_univ _)
    (Set.mem_univ _) ha hb hab
  -- Rewrite the secant slopes using `log Z_1 = 0`, turning them into `log Z_q / (q - 1)`.
  simpa only [hone, sub_zero] using key

/-- The derivative of the partition function `q ↦ Z_q = ∑_{p i > 0} (p i) ^ q` at any point `q` is
`∑_{p i > 0} (p i) ^ q * log (p i)`: each surviving summand `q ↦ (p i) ^ q` (for `p i > 0`) is a
real exponential whose derivative is `(p i) ^ q * log (p i)`, and the empty cells are constants. -/
lemma hasDerivAt_partitionFunction {p : ι → ℝ} (q : ℝ) :
    HasDerivAt (fun q => partitionFunction p q)
      (∑ i, if 0 < p i then (p i) ^ q * Real.log (p i) else 0) q := by
  unfold partitionFunction
  apply HasDerivAt.fun_sum
  intro i _
  by_cases hi : 0 < p i
  · simp only [if_pos hi]
    exact hasStrictDerivAt_const_rpow hi q |>.hasDerivAt
  · simp only [if_neg hi]
    exact hasDerivAt_const q 0

/-- The derivative of `q ↦ log Z_q` at the probability point `q = 1` is the information-dimension
numerator `∑ i, p i * log (p i)`. (At `q = 1` the surviving summands give `p i * log (p i)`, and the
empty cells `p i = 0` contribute `0 = 0 * log 0` automatically, by `Real.log 0 = 0`.) -/
lemma hasDerivAt_logPartitionFunction_one {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    HasDerivAt (fun q => Real.log (partitionFunction p q)) (∑ i, p i * Real.log (p i)) 1 := by
  have hZ : HasDerivAt (fun q => partitionFunction p q)
      (∑ i, if 0 < p i then (p i) ^ (1 : ℝ) * Real.log (p i) else 0) 1 :=
    hasDerivAt_partitionFunction 1
  have hne : partitionFunction p 1 ≠ 0 := by
    rw [partitionFunction_one_eq_one hp hsum]; exact one_ne_zero
  have hlog := hZ.log hne
  -- Simplify `Z'(1) / Z(1)` to `Z'(1)`, then the summands to `p i * log (p i)`.
  rw [partitionFunction_one_eq_one hp hsum, div_one] at hlog
  refine hlog.congr_deriv ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : 0 < p i
  · rw [if_pos hi, Real.rpow_one]
  · rw [if_neg hi]
    have hpi : p i = 0 := le_antisymm (not_lt.1 hi) (hp i)
    rw [hpi, zero_mul]

/-- **Antitonicity of the Rényi (generalized) dimension.** For a probability weight family
`p : ι → ℝ` (`0 ≤ p i`, `∑ i, p i = 1`, with at least one positive weight) at a scale `0 < ε < 1`,
the Rényi dimension `q ↦ D_q` is **non-increasing** in `q`. This is the secant-slope argument: the
slope `g q = log Z_q / (q - 1)` of the convex `log Z` (anchored at `q = 1`) is non-decreasing, and
`D_q = g q / log ε` with `log ε < 0` flips it to antitone; the information-dimension point `q = 1`
is glued in by the convex supporting-line inequality (numerator `h'(1) = ∑ i, p i log p i`). -/
theorem renyiDim_antitone {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hpos : ∃ i, 0 < p i)
    (hsum : ∑ i, p i = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Antitone (fun q => renyiDim p ε q) := by
  have hlogε : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hconv : ConvexOn ℝ Set.univ (fun q => Real.log (partitionFunction p q)) :=
    logPartitionFunction_convexOn hp hpos
  have hone : Real.log (partitionFunction p 1) = 0 := by
    rw [partitionFunction_one_eq_one hp hsum, Real.log_one]
  have hmono := logPartitionFunction_secantSlope_monotoneOn hp hpos hsum
  have hderiv := hasDerivAt_logPartitionFunction_one hp hsum
  -- The Rényi dimension as `g q / log ε` for `q ≠ 1`; the secant slope `g q = log Z_q / (q - 1)`.
  set g : ℝ → ℝ := fun q => Real.log (partitionFunction p q) / (q - 1) with hg
  set G : ℝ := ∑ i, p i * Real.log (p i) with hG
  have hren_ne : ∀ {q : ℝ}, q ≠ 1 → renyiDim p ε q = g q / Real.log ε := by
    intro q hq
    rw [renyiDim, if_neg hq, massExponent, hg, div_div, div_div, mul_comm]
  have hren_one : renyiDim p ε 1 = G / Real.log ε := by
    rw [renyiDim, if_pos rfl, hG]
  -- Dividing by `log ε < 0` is antitone: `x ≤ y → y / log ε ≤ x / log ε`.
  have hdiv : ∀ {x y : ℝ}, x ≤ y → y / Real.log ε ≤ x / Real.log ε := by
    intro x y hxy
    exact (div_le_div_right_of_neg hlogε).mpr hxy
  intro a b hab
  simp only []
  by_cases ha1 : a = 1
  · by_cases hb1 : b = 1
    · rw [ha1, hb1]
    · -- a = 1 < b: need `D_b ≤ D_1`, i.e. `g b / log ε ≤ G / log ε`, i.e. `G ≤ g b`.
      rw [ha1, hren_one, hren_ne hb1]
      refine hdiv ?_
      have h1b : (1 : ℝ) < b := lt_of_le_of_ne (ha1 ▸ hab) (Ne.symm hb1)
      have hsl := hconv.le_slope_of_hasDerivAt (Set.mem_univ 1) (Set.mem_univ b) h1b hderiv
      rw [slope_def_field, hone, sub_zero] at hsl
      simpa only [hg] using hsl
  · by_cases hb1 : b = 1
    · -- a < 1 = b: need `D_1 ≤ D_a`, i.e. `G / log ε ≤ g a / log ε`, i.e. `g a ≤ G`.
      rw [hb1, hren_one, hren_ne ha1]
      refine hdiv ?_
      have ha1' : a < (1 : ℝ) := lt_of_le_of_ne (hb1 ▸ hab) ha1
      have hsl := hconv.slope_le_of_hasDerivAt (Set.mem_univ a) (Set.mem_univ 1) ha1' hderiv
      rw [slope_def_field, hone, zero_sub] at hsl
      -- `slope h a 1 = -log(Z a)/(1 - a) = log(Z a)/(a - 1) = g a`, so `g a ≤ G`.
      have heq : -Real.log (partitionFunction p a) / (1 - a) =
          Real.log (partitionFunction p a) / (a - 1) := by
        rw [neg_div, ← div_neg, neg_sub]
      rw [heq] at hsl
      simpa only [hg] using hsl
    · -- a ≠ 1, b ≠ 1: pure secant monotonicity, divided by `log ε < 0`.
      rw [hren_ne ha1, hren_ne hb1]
      refine hdiv ?_
      exact hmono ha1 hb1 hab

end Oseledets.Multifractal
