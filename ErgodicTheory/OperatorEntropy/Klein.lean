import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Klein's inequality (scalar / Peierls form)

The scalar Klein–Peierls bound `p - s ≤ p·log p - p·log s` (for `0 ≤ p`, `0 < s`), the termwise
core powering the subadditivity of the operator (von Neumann) entropy.
-/

open Real

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-- Scalar Peierls bound: for `0 ≤ p` and `0 < s`,
`p - s ≤ p * log p - p * log s`.  This is the termwise core of Klein's inequality.
(With the Mathlib convention `Real.log 0 = 0` this can fail when `s = 0` and `p > 0`,
which is why the hypothesis `0 < s` is required here.) -/
private lemma log_sub_bound {p s : ℝ} (hp : 0 ≤ p) (hs : 0 < s) :
    p - s ≤ p * Real.log p - p * Real.log s := by
  rcases hp.eq_or_lt with hp0 | hp0
  · subst hp0
    simp only [zero_mul, sub_zero]
    linarith
  · have hpne : p ≠ 0 := hp0.ne'
    have hkey : Real.log s - Real.log p ≤ s / p - 1 := by
      rw [← Real.log_div hs.ne' hpne]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hmul : p * (Real.log s - Real.log p) ≤ p * (s / p - 1) :=
      mul_le_mul_of_nonneg_left hkey hp0.le
    have hsp : p * (s / p - 1) = s - p := by field_simp
    have hexp : p * (Real.log s - Real.log p)
        = p * Real.log s - p * Real.log p := by ring
    linarith [hmul, hsp, hexp]

/-- **Scalar Klein / Peierls inequality.**  Let `D` be a doubly stochastic `K × M`
matrix (row sums `hrow` and column sums `hcol` equal `1`), `p ≥ 0` a probability-like
vector on `K` and `s ≥ 0` one on `M` with equal total mass (`hsum`).  Writing
`a m = ∑ k, D k m * p k` for the column marginal, the support hypothesis `hsupp`
(`s m = 0 ⟹ D k m * p k = 0`) handles the columns where `s m = 0` (there `a m = 0`).
Then `∑ m, a m * log (s m) ≤ ∑ k, p k * log (p k)`.

This is the finite, scalar analogue powering the matrix/operator Klein inequality
(Carlen, *Trace Inequalities and Quantum Entropy*, Thm 2.11 / Peierls Thm 2.9). -/
theorem klein_scalar {K M : Type*} [Fintype K] [Fintype M]
    (p : K → ℝ) (s : M → ℝ) (D : K → M → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : ∀ m, 0 ≤ s m) (hD : ∀ k m, 0 ≤ D k m)
    (hrow : ∀ k, ∑ m, D k m = 1) (hcol : ∀ m, ∑ k, D k m = 1)
    (hsum : ∑ k, p k = ∑ m, s m)
    (hsupp : ∀ m k, s m = 0 → D k m * p k = 0) :
    ∑ m, (∑ k, D k m * p k) * Real.log (s m) ≤ ∑ k, p k * Real.log (p k) := by
  -- Rewrite both sides as double sums over `k` then `m`.
  have hB : (∑ m, (∑ k, D k m * p k) * Real.log (s m))
      = ∑ k, ∑ m, D k m * (p k * Real.log (s m)) := by
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hA : (∑ k, p k * Real.log (p k))
      = ∑ k, ∑ m, D k m * (p k * Real.log (p k)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul, hrow k, one_mul]
  -- The mass-balance term telescopes to `0`.
  have e1 : (∑ k, ∑ m, D k m * p k) = ∑ k, p k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul, hrow k, one_mul]
  have e2 : (∑ k, ∑ m, D k m * s m) = ∑ m, s m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_mul, hcol m, one_mul]
  have hC : (∑ k, ∑ m, D k m * (p k - s m)) = 0 := by
    have expand : (∑ k, ∑ m, D k m * (p k - s m))
        = (∑ k, ∑ m, D k m * p k) - (∑ k, ∑ m, D k m * s m) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m _
      rw [mul_sub]
    rw [expand, e1, e2, hsum, sub_self]
  -- Termwise Peierls bound, summed.
  rw [hB, hA]
  have step : (∑ k, ∑ m, D k m * (p k * Real.log (s m)))
      ≤ ∑ k, ∑ m, (D k m * (p k * Real.log (p k)) - D k m * (p k - s m)) := by
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro m _
    rcases (hs m).eq_or_lt with hsm | hsm
    · -- column with `s m = 0`: both sides vanish via `hsupp`.
      have hsm0 : s m = 0 := hsm.symm
      have hDp : D k m * p k = 0 := hsupp m k hsm0
      have hL : D k m * (p k * Real.log (s m)) = 0 := by
        rw [hsm0, Real.log_zero, mul_zero, mul_zero]
      have hR : D k m * (p k * Real.log (p k)) - D k m * (p k - s m) = 0 := by
        rw [hsm0, sub_zero, ← mul_assoc, hDp, zero_mul, sub_zero]
      linarith [hL, hR]
    · -- column with `s m > 0`: scalar Peierls bound, scaled by `D k m ≥ 0`.
      have hb := log_sub_bound (hp k) hsm
      have hmul : D k m * (p k - s m)
          ≤ D k m * (p k * Real.log (p k) - p k * Real.log (s m)) :=
        mul_le_mul_of_nonneg_left hb (hD k m)
      have hexp : D k m * (p k * Real.log (p k) - p k * Real.log (s m))
          = D k m * (p k * Real.log (p k)) - D k m * (p k * Real.log (s m)) := by
        ring
      linarith [hmul, hexp]
  have hsplit : (∑ k, ∑ m, (D k m * (p k * Real.log (p k)) - D k m * (p k - s m)))
      = (∑ k, ∑ m, D k m * (p k * Real.log (p k)))
        - (∑ k, ∑ m, D k m * (p k - s m)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_sub_distrib]
  rw [hsplit, hC, sub_zero] at step
  exact step

end ErgodicTheory.OperatorEntropy
