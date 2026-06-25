/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Coarse-grained multifractal analysis: core definitions

This file lays the abstract, measure-free foundation for the coarse-grained multifractal analysis
of a finite weight family `p : ι → ℝ` (think `p i = μ(cell i)` for the cells of a partition at
scale `ε`). All quantities are defined on a bare family `p`; the hypotheses one needs for the
theory (`0 ≤ p i`, `∑ i, p i = 1`, `0 < ε < 1`) are carried on the *lemmas*, never baked
into the definitions, so the algebra stays clean and the same definitions specialize to any
measure.

The exponent `^` throughout is `Real.rpow` (real-base, real-exponent power), which is the right
notion for the continuous parameter `q : ℝ`.

## Main definitions

* `Oseledets.Multifractal.partitionFunction`: the generalized partition function
  `Z_q = ∑_{i : p i > 0} (p i) ^ q`. The guard `0 < p i` is load-bearing at `q = 0`: it forces
  empty cells to contribute `0` (so `Z_0` counts occupied cells) instead of `Real.rpow 0 0 = 1`.
* `Oseledets.Multifractal.massExponent`: the mass exponent `τ(q) = log Z_q / log ε`.
* `Oseledets.Multifractal.renyiDim`: the Rényi / generalized dimension `D_q = τ(q) / (q - 1)`,
  with the `q = 1` information-dimension branch `(∑ i, p i log p i) / log ε` supplied directly
  (the `L'Hôpital` limit), since the general formula is `0 / 0` there.
* `Oseledets.Multifractal.singularitySpectrum`: the singularity spectrum
  `f(α) = ⨅ q, q α - τ(q)`, the Legendre transform of `τ`. This is an **infimum**: because
  `τ` is concave, the supremum would be `+∞`.

## Main results

* `Oseledets.Multifractal.partitionFunction_nonneg`: `Z_q ≥ 0` when `0 ≤ p i`.
* `Oseledets.Multifractal.partitionFunction_eq_sum_rpow`: for `q ≠ 0` the guard is removable,
  `Z_q = ∑ i, (p i) ^ q`, since `Real.zero_rpow` makes empty cells vanish anyway.
* `Oseledets.Multifractal.partitionFunction_one_eq_one`: `Z_1 = 1` for a probability weight family.
* `Oseledets.Multifractal.massExponent_one_eq_zero`: `τ(1) = 0` for a probability weight family.
-/

open Real

namespace Oseledets.Multifractal

variable {ι : Type*} [Fintype ι]

/-- The generalized **partition function** `Z_q = ∑_{i : p i > 0} (p i) ^ q` of a finite weight
family `p : ι → ℝ`, with exponent `^` interpreted as `Real.rpow`. The guard `0 < p i` is
load-bearing at `q = 0`: it ensures empty cells (`p i = 0`) contribute `0` rather than
`Real.rpow 0 0 = 1`, so that `Z_0` counts the number of occupied cells. -/
noncomputable def partitionFunction (p : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ i, if 0 < p i then (p i) ^ q else 0

/-- The **mass exponent** `τ(q) = log Z_q / log ε` of a finite weight family `p` at scale `ε`.
This is defined for every `q` with no case split. -/
noncomputable def massExponent (p : ι → ℝ) (ε q : ℝ) : ℝ :=
  Real.log (partitionFunction p q) / Real.log ε

/-- The **Rényi (generalized) dimension** `D_q` of a finite weight family `p` at scale `ε`. For
`q ≠ 1` it is `τ(q) / (q - 1)`. At `q = 1` the general formula is the indeterminate `0 / 0`,
so the `L'Hôpital` value — the **information dimension** `(∑ i, p i log p i) / log ε` — is
supplied directly. (By the Mathlib convention `Real.log 0 = 0`, the `q = 1` numerator needs
no guard: empty cells contribute `0` automatically.) -/
noncomputable def renyiDim (p : ι → ℝ) (ε q : ℝ) : ℝ :=
  if q = 1 then (∑ i, p i * Real.log (p i)) / Real.log ε
  else massExponent p ε q / (q - 1)

/-- The **singularity spectrum** `f(α) = ⨅ q, q α - τ(q)` of a finite weight family `p` at
scale `ε`, the Legendre transform of the mass exponent `τ`. This is an **infimum**: since `τ`
is concave, the supremum of `q α - τ(q)` would be `+∞`. -/
noncomputable def singularitySpectrum (p : ι → ℝ) (ε α : ℝ) : ℝ :=
  ⨅ q : ℝ, q * α - massExponent p ε q

/-- The generalized partition function of a nonnegative weight family is nonnegative. -/
lemma partitionFunction_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (q : ℝ) :
    0 ≤ partitionFunction p q := by
  refine Finset.sum_nonneg fun i _ => ?_
  split
  · exact Real.rpow_nonneg (hp i) q
  · exact le_refl 0

/-- For `q ≠ 0` the positivity guard in the partition function is removable: empty cells
(`p i = 0`) contribute `Real.rpow 0 q = 0` anyway, so `Z_q = ∑ i, (p i) ^ q`. -/
lemma partitionFunction_eq_sum_rpow {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) {q : ℝ}
    (hq : q ≠ 0) : partitionFunction p q = ∑ i, (p i) ^ q := by
  refine Finset.sum_congr rfl fun i _ => ?_
  split
  · rfl
  · rename_i hi
    have hpi : p i = 0 := le_antisymm (not_lt.1 hi) (hp i)
    rw [hpi, Real.zero_rpow hq]

/-- For a probability weight family (`0 ≤ p i` and `∑ i, p i = 1`), the partition function at
`q = 1` is `1`. Occupied cells contribute `(p i) ^ 1 = p i`, empty cells contribute `0` either
way. -/
lemma partitionFunction_one_eq_one {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : partitionFunction p 1 = 1 := by
  rw [partitionFunction_eq_sum_rpow hp one_ne_zero]
  simp_rw [Real.rpow_one]
  exact hsum

/-- For a probability weight family, the mass exponent at `q = 1` vanishes, since `Z_1 = 1` and
`log 1 = 0`. -/
lemma massExponent_one_eq_zero {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ε : ℝ) : massExponent p ε 1 = 0 := by
  rw [massExponent, partitionFunction_one_eq_one hp hsum, Real.log_one, zero_div]

/-- If at least one weight is strictly positive, the partition function is strictly positive: the
contributing cell `i` adds `(p i) ^ q > 0` to a sum of nonnegative terms (each guarded summand is
either a positive `rpow` of a positive base, or `0`). -/
lemma partitionFunction_pos {p : ι → ℝ} (hpos : ∃ i, 0 < p i) (q : ℝ) :
    0 < partitionFunction p q := by
  obtain ⟨j, hj⟩ := hpos
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · split
    · rename_i hi
      exact le_of_lt (Real.rpow_pos_of_pos hi q)
    · exact le_refl 0
  · rw [if_pos hj]
    exact Real.rpow_pos_of_pos hj q

end Oseledets.Multifractal
