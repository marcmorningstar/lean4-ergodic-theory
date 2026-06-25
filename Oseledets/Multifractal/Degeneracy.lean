/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.Defs

/-!
# Coarse-grained multifractal analysis: equal-measure degeneracy

This file records the **equal-measure (uniform) degeneracy** of the multifractal formalism: when
every cell carries the same weight `p i = N⁻¹` (with `N = Fintype.card ι`), the generalized
dimension `D_q` collapses to a single, `q`-independent value, namely `log N / (-log ε)`. This is
the standard sanity check (issue #16, item 4c): a uniform measure is *monofractal*, so its whole
Rényi spectrum is a single point, equal to the box-counting dimension `log N / log (1/ε)`.

## Main results

* `Oseledets.Multifractal.partitionFunction_equalMeasure`: for the uniform family,
  `Z_q = N ^ (1 - q)`.
* `Oseledets.Multifractal.renyiDim_equalMeasure`: for the uniform family and `0 < ε < 1`,
  `D_q = log N / (-log ε)` for *every* `q` — both the `q = 1` information-dimension branch and the
  general `q ≠ 1` branch are shown to agree on this common value.
-/

open Real

namespace Oseledets.Multifractal

variable {ι : Type*} [Fintype ι]

/-- For the **uniform (equal-measure)** family `p i = (Fintype.card ι)⁻¹`, the generalized
partition function is `Z_q = N ^ (1 - q)` with `N = Fintype.card ι`. Each of the `N` cells is
occupied (`N⁻¹ > 0`), contributing `(N⁻¹) ^ q`, so `Z_q = N • (N⁻¹) ^ q = N ^ (1 - q)`. -/
lemma partitionFunction_equalMeasure [Nonempty ι] {p : ι → ℝ}
    (hp : ∀ i, p i = (Fintype.card ι : ℝ)⁻¹) (q : ℝ) :
    partitionFunction p q = (Fintype.card ι : ℝ) ^ (1 - q) := by
  have hNpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hNinv_pos : 0 < (Fintype.card ι : ℝ)⁻¹ := inv_pos.2 hNpos
  -- every guard `0 < p i` holds, so the partition function is a constant sum
  have hterm : ∀ i, (if 0 < p i then (p i) ^ q else 0) = ((Fintype.card ι : ℝ)⁻¹) ^ q := by
    intro i
    rw [hp i, if_pos hNinv_pos]
  rw [partitionFunction]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- now: N * (N⁻¹) ^ q = N ^ (1 - q)
  rw [Real.rpow_sub hNpos, Real.rpow_one, Real.inv_rpow hNpos.le, div_eq_mul_inv]

/-- For the **uniform (equal-measure)** family `p i = (Fintype.card ι)⁻¹` and `0 < ε < 1`, the
Rényi (generalized) dimension is `q`-independent: `D_q = log N / (-log ε)` for every `q`. This is
the monofractal degeneracy of a uniform measure: the entire Rényi spectrum is the single point
`log N / log (1/ε)`. Both branches of `renyiDim` (the `q = 1` information dimension and the general
`q ≠ 1` formula) are shown to evaluate to this common value. -/
lemma renyiDim_equalMeasure [Nonempty ι] {p : ι → ℝ}
    (hp : ∀ i, p i = (Fintype.card ι : ℝ)⁻¹) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (q : ℝ) :
    renyiDim p ε q = Real.log (Fintype.card ι) / (- Real.log ε) := by
  have hNpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hlogε_neg : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hlogε_ne : Real.log ε ≠ 0 := ne_of_lt hlogε_neg
  rw [renyiDim]
  split
  · -- q = 1 branch: (∑ i, p i * log (p i)) / log ε
    rename_i hq1
    have hterm : ∀ i, p i * Real.log (p i)
        = (Fintype.card ι : ℝ)⁻¹ * Real.log ((Fintype.card ι : ℝ)⁻¹) := by
      intro i; rw [hp i]
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- N * (N⁻¹ * log (N⁻¹)) = log (N⁻¹) = - log N
    rw [Real.log_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul,
      neg_div, div_neg]
  · -- q ≠ 1 branch: massExponent p ε q / (q - 1)
    rename_i hq1
    have hq1' : q - 1 ≠ 0 := sub_ne_zero.2 hq1
    have hnegε_ne : -Real.log ε ≠ 0 := neg_ne_zero.2 hlogε_ne
    rw [massExponent, partitionFunction_equalMeasure hp q, Real.log_rpow hNpos]
    -- ((1 - q) * log N / log ε) / (q - 1) = log N / (- log ε)
    rw [div_div, div_eq_div_iff (mul_ne_zero hlogε_ne hq1') hnegε_ne]
    ring

end Oseledets.Multifractal
