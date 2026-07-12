/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapOrbit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A finite-sample rate for the cat-map top-Lyapunov-exponent estimator

The derivative cocycle of the Arnold cat map is the **constant** hyperbolic matrix
`catℝ = !![2,1;1,1]` (`ErgodicTheory.Examples.CatMapSuspensionFlow`), so the top-Lyapunov
estimator read off from a length-`n` orbit segment is the **deterministic** number
`(1/n) log ‖catℝ ⁿ‖`.  The companion file `CatMapSuspensionFlow` records the *limit*
`tendsto_catℝ_pow_log : (1/n) log ‖catℝ ⁿ‖ → log((3 + √5)/2)`.  This module supplies the
**finite-sample strengthening** requested by issue #62 (tier 3): a fully explicit *rate* for how
fast that estimator converges.

Because `catℝ` is a fixed hyperbolic matrix, the Gelfand growth `‖catℝ ⁿ‖` is squeezed between
two explicit constant multiples of `λⁿ`, `λ = (3 + √5)/2`:

* **lower bound** `λⁿ ≤ ‖catℝ ⁿ‖` — apply `catℝ ⁿ` to the `λ`-eigenvector and use the L2 operator
  bound `‖A x‖ ≤ ‖A‖ ‖x‖`;
* **upper bound** `‖catℝ ⁿ‖ ≤ C · λⁿ` with `C = (‖catℝ‖ + λ + 1)/√5` — Cayley–Hamilton gives the
  closed form `catℝ ⁿ = aₙ • catℝ + bₙ • 1` with `aₙ = (λⁿ - μⁿ)/√5`, `bₙ = (λμⁿ - μλⁿ)/√5`
  (`μ = (3 - √5)/2 ∈ (0,1)`), whose coefficients are bounded by explicit multiples of `λⁿ`
  (`μⁿ ≤ 1 ≤ λⁿ`), then the norm triangle inequality.

Taking logarithms (`Real.log_pow`, monotonicity) turns the two-sided norm bound into the headline

`|log ‖catℝ ⁿ‖ / n - log λ| ≤ C₀ / n`,  with `C₀ = |log C|`  (`catExponent_rate`),

the deterministic finite-sample guarantee for estimating the top Lyapunov exponent
`log((3 + √5)/2)` of the cat map from an orbit segment.  Letting `n → ∞` re-derives the limit as a
sanity corollary (`tendsto_catExponent_rate`), matching `tendsto_catℝ_pow_log`.

The matrix norm is the scoped **L2 operator norm** `Matrix.Norms.L2Operator`, the norm used
throughout the cocycle library and in `tendsto_catℝ_pow_log`.

## Main results

* `ErgodicTheory.CatMapToral.catℝ_pow_norm_lower` — `λⁿ ≤ ‖catℝ ⁿ‖`.
* `ErgodicTheory.CatMapToral.catℝ_pow_norm_upper` — `‖catℝ ⁿ‖ ≤ catNormBound · λⁿ`.
* `ErgodicTheory.CatMapToral.catExponent_rate` — `|log ‖catℝ ⁿ‖ / n - log λ| ≤ catRateConst / n`.
* `ErgodicTheory.CatMapToral.tendsto_catExponent_rate` — the limit `log ‖catℝ ⁿ‖ / n → log λ`,
  re-derived from the rate.

## References

* I. M. Gelfand, *Normierte Ringe*, Mat. Sb. **9** (1941), 3–24 (the spectral-radius growth law).
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory.CatMapToral

/-! ## The closed form `catℝ ⁿ = aₙ • catℝ + bₙ • 1` (Cayley–Hamilton)

The elementary scalar facts about `λ`, `μ`, `√5` used throughout this module (`lam_add_mu`,
`lam_mul_mu`, `lam_pos`, `mu_pos`, `mu_lt_one`, `mu_le_lam`, `sqrt5_pos`, `sqrt5_ne_zero`) are
proved once in `ErgodicTheory.Examples.CatMapOrbit`. -/

/-- Coefficient of `catℝ` in the closed form of `catℝ ⁿ`: `aₙ = (λⁿ - μⁿ)/√5`. -/
noncomputable def aCoeff (n : ℕ) : ℝ := (lam ^ n - mu ^ n) / Real.sqrt 5

/-- Coefficient of `1` in the closed form of `catℝ ⁿ`: `bₙ = (λ μⁿ - μ λⁿ)/√5`. -/
noncomputable def bCoeff (n : ℕ) : ℝ := (lam * mu ^ n - mu * lam ^ n) / Real.sqrt 5

/-- `a₀ = 0`. -/
lemma aCoeff_zero : aCoeff 0 = 0 := by simp [aCoeff]

/-- `b₀ = 1` (using `λ - μ = √5`). -/
lemma bCoeff_zero : bCoeff 0 = 1 := by
  simp only [bCoeff, pow_zero, mul_one]
  rw [lam_sub_mu, div_self sqrt5_ne_zero]

/-- Scalar recurrence for `aₙ`: `aₙ₊₁ = 3 aₙ + bₙ`. -/
lemma aCoeff_succ (n : ℕ) : aCoeff (n + 1) = 3 * aCoeff n + bCoeff n := by
  unfold aCoeff bCoeff
  rw [pow_succ, pow_succ, ← mul_div_assoc, ← add_div]
  congr 1
  linear_combination (lam ^ n - mu ^ n) * lam_add_mu

/-- Scalar recurrence for `bₙ`: `bₙ₊₁ = -aₙ`. -/
lemma bCoeff_succ (n : ℕ) : bCoeff (n + 1) = -aCoeff n := by
  unfold bCoeff aCoeff
  rw [pow_succ, pow_succ, ← neg_div]
  congr 1
  linear_combination (mu ^ n - lam ^ n) * lam_mul_mu

/-- **Cayley–Hamilton for `catℝ`.** `catℝ² = 3 • catℝ - 1` (char. poly `x² - 3x + 1`). -/
lemma catℝ_sq : catℝ ^ 2 = (3 : ℝ) • catℝ - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [catℝ, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply] <;> norm_num

/-- **The closed form of the matrix power.** `catℝ ⁿ = aₙ • catℝ + bₙ • 1`. -/
lemma catℝ_pow_eq (n : ℕ) :
    catℝ ^ n = aCoeff n • catℝ + bCoeff n • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  induction n with
  | zero => rw [pow_zero, aCoeff_zero, bCoeff_zero, zero_smul, one_smul, zero_add]
  | succ n ih =>
    rw [pow_succ, ih, aCoeff_succ, bCoeff_succ, add_mul, smul_mul_assoc, smul_mul_assoc,
      one_mul, ← pow_two, catℝ_sq]
    module

/-! ## Explicit bounds on the coefficients -/

/-- `0 ≤ aₙ`. -/
lemma aCoeff_nonneg (n : ℕ) : 0 ≤ aCoeff n := by
  apply div_nonneg _ sqrt5_pos.le
  have : mu ^ n ≤ lam ^ n := pow_le_pow_left₀ mu_pos.le mu_le_lam n
  linarith

/-- `|aₙ| ≤ λⁿ / √5`. -/
lemma aCoeff_abs_le (n : ℕ) : |aCoeff n| ≤ lam ^ n / Real.sqrt 5 := by
  rw [abs_of_nonneg (aCoeff_nonneg n)]
  unfold aCoeff
  have hmun : (0 : ℝ) ≤ mu ^ n := pow_nonneg mu_pos.le n
  gcongr
  linarith

/-- `|bₙ| ≤ (λ + 1) λⁿ / √5`. -/
lemma bCoeff_abs_le (n : ℕ) : |bCoeff n| ≤ (lam + 1) * lam ^ n / Real.sqrt 5 := by
  have hmun1 : mu ^ n ≤ 1 := pow_le_one₀ mu_pos.le mu_lt_one.le
  have hmun0 : 0 ≤ mu ^ n := pow_nonneg mu_pos.le n
  have hlamn1 : 1 ≤ lam ^ n := one_le_pow₀ one_lt_lam.le
  have hlamn0 : 0 ≤ lam ^ n := pow_nonneg lam_pos.le n
  have hlam0 : 0 ≤ lam := lam_pos.le
  have hnum : |lam * mu ^ n - mu * lam ^ n| ≤ (lam + 1) * lam ^ n := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [mul_nonneg hlam0 hmun0,
        mul_nonneg (show (0 : ℝ) ≤ lam + 1 - mu by linarith [mu_lt_one, one_lt_lam]) hlamn0]
    · nlinarith [mul_le_mul_of_nonneg_left hmun1 hlam0, mul_nonneg mu_pos.le hlamn0,
        mul_le_mul_of_nonneg_left hlamn1 (show (0 : ℝ) ≤ lam + 1 by linarith [lam_pos])]
  unfold bCoeff
  rw [abs_div, abs_of_pos sqrt5_pos]
  gcongr

/-! ## The two-sided explicit norm bounds on `catℝ ⁿ` -/

/-- The explicit upper constant `C = (‖catℝ‖ + λ + 1)/√5`. -/
noncomputable def catNormBound : ℝ := (‖catℝ‖ + lam + 1) / Real.sqrt 5

/-- `0 < catNormBound`. -/
lemma catNormBound_pos : 0 < catNormBound := by
  unfold catNormBound
  apply div_pos _ sqrt5_pos
  have := norm_nonneg catℝ
  have := lam_pos
  linarith

/-- The L2 operator norm of the identity `2×2` matrix is `1`. -/
lemma l2_opNorm_one : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact norm_one

/-- **Explicit upper bound.** `‖catℝ ⁿ‖ ≤ catNormBound · λⁿ` for every `n`. -/
theorem catℝ_pow_norm_upper (n : ℕ) : ‖catℝ ^ n‖ ≤ catNormBound * lam ^ n := by
  rw [catℝ_pow_eq n]
  have h1 : ‖aCoeff n • catℝ + bCoeff n • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      ≤ |aCoeff n| * ‖catℝ‖ + |bCoeff n| := by
    calc ‖aCoeff n • catℝ + bCoeff n • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖
        ≤ ‖aCoeff n • catℝ‖ + ‖bCoeff n • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := norm_add_le _ _
      _ = |aCoeff n| * ‖catℝ‖ + |bCoeff n| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = |aCoeff n| * ‖catℝ‖ + |bCoeff n| := by rw [l2_opNorm_one, mul_one]
  have hcat : (0 : ℝ) ≤ ‖catℝ‖ := norm_nonneg _
  calc ‖aCoeff n • catℝ + bCoeff n • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      ≤ |aCoeff n| * ‖catℝ‖ + |bCoeff n| := h1
    _ ≤ lam ^ n / Real.sqrt 5 * ‖catℝ‖ + (lam + 1) * lam ^ n / Real.sqrt 5 := by
        gcongr
        · exact aCoeff_abs_le n
        · exact bCoeff_abs_le n
    _ = catNormBound * lam ^ n := by
        unfold catNormBound
        field_simp
        ring

/-- **Explicit lower bound.** `λⁿ ≤ ‖catℝ ⁿ‖` for every `n` (apply `catℝ ⁿ` to the
`λ`-eigenvector and use `‖A x‖ ≤ ‖A‖ ‖x‖`). -/
theorem catℝ_pow_norm_lower (n : ℕ) : lam ^ n ≤ ‖catℝ ^ n‖ := by
  set v : Fin 2 → ℝ := ![1, lam - 2] with hv
  have hEigen : Matrix.toEuclideanCLM (𝕜 := ℝ) (catℝ ^ n) (WithLp.toLp 2 v)
      = lam ^ n • WithLp.toLp 2 v := by
    rw [Matrix.toEuclideanCLM_toLp, catℝ_pow_mulVec_eigen_lam, WithLp.toLp_smul]
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (catℝ ^ n) (WithLp.toLp 2 v)‖
      = lam ^ n * ‖WithLp.toLp 2 v‖ := by
    rw [hEigen, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg lam_pos.le n)]
  have hle : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (catℝ ^ n) (WithLp.toLp 2 v)‖
      ≤ ‖catℝ ^ n‖ * ‖WithLp.toLp 2 v‖ := by
    have := (Matrix.toEuclideanCLM (𝕜 := ℝ) (catℝ ^ n)).le_opNorm (WithLp.toLp 2 v)
    rwa [Matrix.l2_opNorm_toEuclideanCLM] at this
  have hxpos : 0 < ‖WithLp.toLp 2 v‖ := by
    rw [norm_pos_iff, Ne, WithLp.toLp_eq_zero]
    intro h
    have h0 : v 0 = 0 := by rw [h]; rfl
    simp [hv] at h0
  have hcomb : lam ^ n * ‖WithLp.toLp 2 v‖ ≤ ‖catℝ ^ n‖ * ‖WithLp.toLp 2 v‖ := by
    rw [← hnorm]; exact hle
  exact le_of_mul_le_mul_right hcomb hxpos

/-! ## The finite-sample rate (the headline) -/

/-- The explicit rate constant `C₀ = |log C| = |log catNormBound|`. -/
noncomputable def catRateConst : ℝ := |Real.log catNormBound|

/-- **The finite-sample rate for the cat-map top-exponent estimator.** For every `n ≥ 1`,

`|log ‖catℝ ⁿ‖ / n - log λ| ≤ catRateConst / n`,

a fully explicit `O(1/n)` deterministic guarantee for estimating the top Lyapunov exponent
`log λ = log((3 + √5)/2)` of the cat map from a length-`n` orbit segment.  The two-sided norm
bounds `λⁿ ≤ ‖catℝ ⁿ‖ ≤ catNormBound · λⁿ` become, after taking logarithms and dividing by `n`,
`0 ≤ log ‖catℝ ⁿ‖ / n - log λ ≤ log catNormBound / n`. -/
theorem catExponent_rate (n : ℕ) (hn : 1 ≤ n) :
    |Real.log ‖catℝ ^ n‖ / n - Real.log lam| ≤ catRateConst / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hlamn : 0 < lam ^ n := pow_pos lam_pos n
  have hlower := catℝ_pow_norm_lower n
  have hupper := catℝ_pow_norm_upper n
  have hnormpos : 0 < ‖catℝ ^ n‖ := lt_of_lt_of_le hlamn hlower
  have hCpos := catNormBound_pos
  have hlog_lower : (n : ℝ) * Real.log lam ≤ Real.log ‖catℝ ^ n‖ := by
    have := Real.log_le_log hlamn hlower
    rwa [Real.log_pow] at this
  have hlog_upper : Real.log ‖catℝ ^ n‖ ≤ Real.log catNormBound + (n : ℝ) * Real.log lam := by
    have := Real.log_le_log hnormpos hupper
    rwa [Real.log_mul hCpos.ne' hlamn.ne', Real.log_pow] at this
  have h0 : 0 ≤ Real.log ‖catℝ ^ n‖ - (n : ℝ) * Real.log lam := by linarith
  have hEq : Real.log ‖catℝ ^ n‖ / (n : ℝ) - Real.log lam
      = (Real.log ‖catℝ ^ n‖ - (n : ℝ) * Real.log lam) / (n : ℝ) := by
    field_simp
  rw [hEq, catRateConst, abs_of_nonneg (div_nonneg h0 hn0.le)]
  rw [div_le_div_iff_of_pos_right hn0]
  calc Real.log ‖catℝ ^ n‖ - (n : ℝ) * Real.log lam
      ≤ Real.log catNormBound := by linarith
    _ ≤ |Real.log catNormBound| := le_abs_self _

/-- **Sanity corollary: the limit, re-derived from the rate.** `log ‖catℝ ⁿ‖ / n → log λ`.  This
matches `tendsto_catℝ_pow_log` (there stated as `(1/n) log ‖catℝ ⁿ‖ → log((3 + √5)/2)`) and follows
by squeezing the `catExponent_rate` bound `catRateConst / n → 0`. -/
theorem tendsto_catExponent_rate :
    Tendsto (fun n : ℕ => Real.log ‖catℝ ^ n‖ / n) atTop (𝓝 (Real.log lam)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ n : ℕ in atTop,
      dist (Real.log ‖catℝ ^ n‖ / n) (Real.log lam) ≤ catRateConst / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.dist_eq]
    exact catExponent_rate n hn
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ dist (Real.log ‖catℝ ^ n‖ / n) (Real.log lam) :=
    Filter.Eventually.of_forall fun n => dist_nonneg
  have htend : Tendsto (fun n : ℕ => catRateConst / n) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul catRateConst
    simp only [mul_zero, mul_one_div] at h
    exact h
  exact squeeze_zero' hpos hbound htend

end ErgodicTheory.CatMapToral
