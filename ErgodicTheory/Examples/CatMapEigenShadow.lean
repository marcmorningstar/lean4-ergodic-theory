/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapOrbit
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Eigenbasis shadowing estimates for the Arnold cat map

Working entirely on the plain type `Fin 2 → ℝ` with the sup (`L∞`) `Pi` norm, this file assembles
the linear-algebra core of the Anosov **closing property** for the cat-map matrix
`catℝ = !![2,1;1,1]` (see `ErgodicTheory.Examples.CatMapOrbit` for the eigen-data:
`lam = (3+√5)/2 > 1`, `mu = (3-√5)/2 ∈ (0,1)`, and the eigenvectors `![1, lam-2]`, `![1, mu-2]`).

The hyperbolic splitting lets one solve the *cohomological* equation `(catℝⁿ - 1) w = e` explicitly
in the eigenbasis, and bound the whole forward orbit of the solution by a two-sided geometric decay
`θ^(n-i) + θ^i` with `θ = mu`.  Summing the `α`-th powers of those bounds produces exactly the
`ExpClosing`-shaped estimate consumed by the Livšic closing machinery.

## Main results

* `eig_decomp` — every `e : Fin 2 → ℝ` decomposes as `eigCoordU e • vU + eigCoordS e • vS`.
* `abs_eigCoordU_le`, `abs_eigCoordS_le` — the eigenbasis coordinates are sup-norm bounded by
  `Ccoord = 3/2` times `‖e‖`.
* `catShadowSol` / `sub_mulVec_catShadowSol` — the explicit solution `w` of `(catℝⁿ - 1) w = e`.
* `catPow_mulVec_catShadowSol` — the forward image `catℝⁱ ·ᵥ w` in closed eigenbasis form.
* `norm_catPow_catShadowSol_le` — the two-sided shadowing bound
  `‖catℝⁱ ·ᵥ w‖ ≤ Cshadow · ‖e‖ · (θ^(n-i) + θ^i)`.
* `sum_rpow_norm_catShadow_le` — the summed `ExpClosing`-shape bound
  `∑_{i<n} ‖catℝⁱ ·ᵥ w‖^α ≤ (2·Cshadow^α / (1 - θ^α)) · ‖e‖^α` for `0 < α ≤ 1`.
-/

open Matrix

namespace ErgodicTheory.CatMapToral

noncomputable section

/-! ## The coordinate constant

The eigenvalue facts `mu_pos`, `mu_lt_one`, `lam_mul_mu` used below are proved once in
`ErgodicTheory.Examples.CatMapOrbit`. -/

/-- The explicit sup-norm bound on the eigenbasis coordinates. -/
def Ccoord : ℝ := 3 / 2

lemma Ccoord_pos : 0 < Ccoord := by unfold Ccoord; norm_num

lemma Ccoord_nonneg : 0 ≤ Ccoord := Ccoord_pos.le

/-- The stable ratio `θ = μ ∈ (0,1)`. -/
def θ : ℝ := mu

lemma θ_pos : 0 < θ := by unfold θ; exact mu_pos

lemma θ_lt_one : θ < 1 := by unfold θ; exact mu_lt_one

/-- The explicit constant in the two-sided shadowing bound. -/
def Cshadow : ℝ := 2 * Ccoord / (1 - θ)

lemma Cshadow_pos : 0 < Cshadow := by
  have h1 : (0 : ℝ) < 1 - θ := by have := θ_lt_one; linarith
  unfold Cshadow
  exact div_pos (mul_pos (by norm_num) Ccoord_pos) h1

/-! ## The two eigenvectors and their norms -/

/-- The `λ`-eigenvector `![1, λ-2]`. -/
def vU : Fin 2 → ℝ := ![1, lam - 2]

/-- The `μ`-eigenvector `![1, μ-2]`. -/
def vS : Fin 2 → ℝ := ![1, mu - 2]

/-- `‖vU‖ ≤ 2` (in fact `= 1`, but `≤ 2` is all we need). -/
lemma norm_vU_le : ‖vU‖ ≤ 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  intro j
  fin_cases j
  · simp only [vU, Matrix.cons_val_zero, Real.norm_eq_abs, Fin.mk_zero]
    rw [abs_le]; constructor <;> norm_num
  · simp only [vU, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs, Fin.mk_one]
    rw [abs_le]; unfold lam; constructor <;> nlinarith [sqrt5_lt_three, two_lt_sqrt5]

/-- `‖vS‖ ≤ 2` (in fact `= (1+√5)/2`, but `≤ 2` is all we need). -/
lemma norm_vS_le : ‖vS‖ ≤ 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  intro j
  fin_cases j
  · simp only [vS, Matrix.cons_val_zero, Real.norm_eq_abs, Fin.mk_zero]
    rw [abs_le]; constructor <;> norm_num
  · simp only [vS, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs, Fin.mk_one]
    rw [abs_le]; unfold mu; constructor <;> nlinarith [sqrt5_lt_three, two_lt_sqrt5]

/-! ## Eigenbasis coordinates (L4) -/

/-- The `λ`-coordinate of `e` in the eigenbasis `{vU, vS}`. -/
def eigCoordU (e : Fin 2 → ℝ) : ℝ := (e 1 - (mu - 2) * e 0) / (lam - mu)

/-- The `μ`-coordinate of `e` in the eigenbasis `{vU, vS}`. -/
def eigCoordS (e : Fin 2 → ℝ) : ℝ := ((lam - 2) * e 0 - e 1) / (lam - mu)

/-- Every vector decomposes in the eigenbasis: `e = eigCoordU e • vU + eigCoordS e • vS`. -/
theorem eig_decomp (e : Fin 2 → ℝ) : e = eigCoordU e • vU + eigCoordS e • vS := by
  have hlm : lam - mu ≠ 0 := by
    rw [lam_sub_mu]; exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  funext j
  fin_cases j <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vU, vS, eigCoordU, eigCoordS,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one] <;>
    field_simp [hlm] <;>
    ring

/-- The `λ`-coordinate is sup-norm bounded by `Ccoord · ‖e‖`. -/
theorem abs_eigCoordU_le (e : Fin 2 → ℝ) : |eigCoordU e| ≤ Ccoord * ‖e‖ := by
  have hs5pos : (0 : ℝ) < Real.sqrt 5 := by have := two_lt_sqrt5; linarith
  have hnorm0 : |e 0| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e 0
  have hmu2 : |mu - 2| ≤ 2 := by
    rw [abs_le]; unfold mu; constructor <;> nlinarith [sqrt5_lt_three, two_lt_sqrt5]
  have htri : |e 1 - (mu - 2) * e 0| ≤ |e 1| + |(mu - 2) * e 0| := by
    have h := abs_add_le (e 1) (-((mu - 2) * e 0))
    simpa [sub_eq_add_neg, abs_neg] using h
  have hprod : |(mu - 2) * e 0| ≤ 2 * ‖e‖ := by
    rw [abs_mul]; exact mul_le_mul hmu2 hnorm0 (abs_nonneg _) (by norm_num)
  have hnorm1 : |e 1| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e 1
  have hnum : |e 1 - (mu - 2) * e 0| ≤ 3 * ‖e‖ := by linarith
  unfold eigCoordU Ccoord
  rw [abs_div, show |lam - mu| = Real.sqrt 5 from by
        rw [lam_sub_mu, abs_of_nonneg (Real.sqrt_nonneg 5)], div_le_iff₀ hs5pos]
  nlinarith [hnum, norm_nonneg e,
    mul_nonneg (norm_nonneg e) (by linarith [two_lt_sqrt5] : (0 : ℝ) ≤ Real.sqrt 5 - 2)]

/-- The `μ`-coordinate is sup-norm bounded by `Ccoord · ‖e‖`. -/
theorem abs_eigCoordS_le (e : Fin 2 → ℝ) : |eigCoordS e| ≤ Ccoord * ‖e‖ := by
  have hs5pos : (0 : ℝ) < Real.sqrt 5 := by have := two_lt_sqrt5; linarith
  have hnorm0 : |e 0| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e 0
  have hlam2 : |lam - 2| ≤ 2 := by
    rw [abs_le]; unfold lam; constructor <;> nlinarith [sqrt5_lt_three, two_lt_sqrt5]
  have htri : |(lam - 2) * e 0 - e 1| ≤ |(lam - 2) * e 0| + |e 1| := by
    have h := abs_add_le ((lam - 2) * e 0) (-(e 1))
    simpa [sub_eq_add_neg, abs_neg] using h
  have hprod : |(lam - 2) * e 0| ≤ 2 * ‖e‖ := by
    rw [abs_mul]; exact mul_le_mul hlam2 hnorm0 (abs_nonneg _) (by norm_num)
  have hnorm1 : |e 1| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e 1
  have hnum : |(lam - 2) * e 0 - e 1| ≤ 3 * ‖e‖ := by linarith
  unfold eigCoordS Ccoord
  rw [abs_div, show |lam - mu| = Real.sqrt 5 from by
        rw [lam_sub_mu, abs_of_nonneg (Real.sqrt_nonneg 5)], div_le_iff₀ hs5pos]
  nlinarith [hnum, norm_nonneg e,
    mul_nonneg (norm_nonneg e) (by linarith [two_lt_sqrt5] : (0 : ℝ) ≤ Real.sqrt 5 - 2)]

/-! ## The two geometric ratio bounds -/

/-- Unstable ratio bound: `λⁱ/(λⁿ-1) ≤ μ^(n-i)/(1-μ)` for `1 ≤ n`, `i ≤ n`.  Uses
`λⁿ-1 ≥ λⁿ(1-μ)` (equivalent to `λⁿμ = λⁿ⁻¹ ≥ 1`) and `λⁱ/λⁿ = μ^(n-i)`. -/
lemma lam_ratio_le {n i : ℕ} (hn : 1 ≤ n) (hi : i ≤ n) :
    lam ^ i / (lam ^ n - 1) ≤ mu ^ (n - i) / (1 - mu) := by
  have hlam_pos : 0 < lam := by linarith [one_lt_lam]
  have hlamn : (1 : ℝ) < lam ^ n := one_lt_pow₀ one_lt_lam (by omega)
  have hden : 0 < lam ^ n - 1 := by linarith
  have h1mu : 0 < 1 - mu := by have := mu_lt_one; linarith
  have hmuinv : mu = lam⁻¹ := (inv_eq_of_mul_eq_one_right lam_mul_mu).symm
  have hlamn_pos : 0 < lam ^ n := pow_pos hlam_pos n
  have hexp : lam ^ n = lam ^ (n - 1) * lam := by rw [← pow_succ]; congr 1; omega
  have hval : lam ^ n * mu = lam ^ (n - 1) := by rw [hexp, mul_assoc, lam_mul_mu, mul_one]
  have hge1 : (1 : ℝ) ≤ lam ^ n * mu := by rw [hval]; exact one_le_pow₀ one_lt_lam.le
  have hkey : lam ^ n * (1 - mu) ≤ lam ^ n - 1 := by nlinarith [hge1]
  have hcpos : 0 < lam ^ n * (1 - mu) := mul_pos hlamn_pos h1mu
  have hln : lam ^ i / lam ^ n = mu ^ (n - i) := by
    have hsplit : lam ^ n = lam ^ i * lam ^ (n - i) := by rw [← pow_add]; congr 1; omega
    rw [hsplit, hmuinv, inv_pow, ← div_div, div_self (ne_of_gt (pow_pos hlam_pos i)), one_div]
  calc lam ^ i / (lam ^ n - 1)
      ≤ lam ^ i / (lam ^ n * (1 - mu)) :=
        div_le_div_of_nonneg_left (pow_pos hlam_pos i).le hcpos hkey
    _ = mu ^ (n - i) / (1 - mu) := by rw [← hln, div_div]

/-- Stable ratio bound: `μⁱ/(1-μⁿ) ≤ μⁱ/(1-μ)` for `1 ≤ n` (since `μⁿ ≤ μ`). -/
lemma mu_ratio_le {n : ℕ} (hn : 1 ≤ n) (i : ℕ) :
    mu ^ i / (1 - mu ^ n) ≤ mu ^ i / (1 - mu) := by
  have h1mu : 0 < 1 - mu := by have := mu_lt_one; linarith
  have hmun : mu ^ n ≤ mu := by
    calc mu ^ n ≤ mu ^ 1 := pow_le_pow_of_le_one mu_pos.le mu_lt_one.le hn
      _ = mu := pow_one mu
  have hle : 1 - mu ≤ 1 - mu ^ n := by linarith
  exact div_le_div_of_nonneg_left (pow_nonneg mu_pos.le i) h1mu hle

/-! ## The explicit shadow solution (L5) -/

/-- The explicit solution `w` of `(catℝⁿ - 1) w = e`, obtained by dividing each eigenbasis
coordinate of `e` by the corresponding eigenvalue gap `λⁿ-1`, `μⁿ-1`. -/
def catShadowSol (n : ℕ) (e : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (eigCoordU e / (lam ^ n - 1)) • vU + (eigCoordS e / (mu ^ n - 1)) • vS

set_option linter.unusedVariables false in
/-- The forward image `catℝⁱ ·ᵥ w` in closed eigenbasis form.  The hypothesis `1 ≤ n` is carried
for uniformity with the downstream closing lemmas (the identity itself holds for every `n`). -/
theorem catPow_mulVec_catShadowSol (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (e : Fin 2 → ℝ) :
    (catℝ ^ i) *ᵥ catShadowSol n e
      = (eigCoordU e * lam ^ i / (lam ^ n - 1)) • vU
        + (eigCoordS e * mu ^ i / (mu ^ n - 1)) • vS := by
  unfold catShadowSol vU vS
  rw [mulVec_add, mulVec_smul, mulVec_smul, catℝ_pow_mulVec_eigen_lam, catℝ_pow_mulVec_eigen_mu,
    smul_smul, smul_smul,
    show eigCoordU e / (lam ^ n - 1) * lam ^ i = eigCoordU e * lam ^ i / (lam ^ n - 1) from by ring,
    show eigCoordS e / (mu ^ n - 1) * mu ^ i = eigCoordS e * mu ^ i / (mu ^ n - 1) from by ring]

/-- The shadow solution solves the cohomological equation `(catℝⁿ - 1) w = e`. -/
theorem sub_mulVec_catShadowSol (n : ℕ) (hn : 1 ≤ n) (e : Fin 2 → ℝ) :
    (catℝ ^ n) *ᵥ catShadowSol n e - catShadowSol n e = e := by
  have hlamden : lam ^ n - 1 ≠ 0 := by
    have : (1 : ℝ) < lam ^ n := one_lt_pow₀ one_lt_lam (by omega); linarith
  have hmuden : mu ^ n - 1 ≠ 0 := by
    have : mu ^ n < 1 := pow_lt_one₀ mu_pos.le mu_lt_one (by omega); linarith
  rw [catPow_mulVec_catShadowSol n hn n e]
  unfold catShadowSol
  have key : ∀ a b c d : ℝ, a • vU + b • vS - (c • vU + d • vS) = (a - c) • vU + (b - d) • vS := by
    intro a b c d; rw [sub_smul, sub_smul]; abel
  rw [key,
    show eigCoordU e * lam ^ n / (lam ^ n - 1) - eigCoordU e / (lam ^ n - 1) = eigCoordU e from by
      field_simp [hlamden],
    show eigCoordS e * mu ^ n / (mu ^ n - 1) - eigCoordS e / (mu ^ n - 1) = eigCoordS e from by
      field_simp [hmuden]]
  exact (eig_decomp e).symm

/-! ## The two-sided shadowing bound (L6) -/

/-- **Two-sided shadowing bound.** For `1 ≤ n` and `i ≤ n`, the forward image of the shadow
solution decays like a two-sided geometric series:
`‖catℝⁱ ·ᵥ w‖ ≤ Cshadow · ‖e‖ · (θ^(n-i) + θ^i)`. -/
theorem norm_catPow_catShadowSol_le (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (hi : i ≤ n) (e : Fin 2 → ℝ) :
    ‖(catℝ ^ i) *ᵥ catShadowSol n e‖ ≤ Cshadow * ‖e‖ * (θ ^ (n - i) + θ ^ i) := by
  have hlam_pos : 0 < lam := by linarith [one_lt_lam]
  have hlamn : (1 : ℝ) < lam ^ n := one_lt_pow₀ one_lt_lam (by omega)
  have hlamden : 0 < lam ^ n - 1 := by linarith
  have hmun : mu ^ n < 1 := pow_lt_one₀ mu_pos.le mu_lt_one (by omega)
  have hmn1 : mu ^ n - 1 < 0 := by linarith
  have h1mu : 0 < 1 - mu := by have := mu_lt_one; linarith
  have hnorme : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  rw [catPow_mulVec_catShadowSol n hn i e]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hUterm : |eigCoordU e * lam ^ i / (lam ^ n - 1)| * ‖vU‖
      ≤ Cshadow * ‖e‖ * θ ^ (n - i) := by
    have habs : |eigCoordU e * lam ^ i / (lam ^ n - 1)|
        = |eigCoordU e| * (lam ^ i / (lam ^ n - 1)) := by
      rw [abs_div, abs_mul, abs_of_pos (pow_pos hlam_pos i), abs_of_pos hlamden, mul_div_assoc]
    rw [habs]
    have hratio : lam ^ i / (lam ^ n - 1) ≤ mu ^ (n - i) / (1 - mu) := lam_ratio_le hn hi
    have hnn1 : (0 : ℝ) ≤ lam ^ i / (lam ^ n - 1) := (div_pos (pow_pos hlam_pos i) hlamden).le
    have hnn2 : (0 : ℝ) ≤ Ccoord * ‖e‖ := mul_nonneg Ccoord_nonneg hnorme
    have hnn3 : (0 : ℝ) ≤ mu ^ (n - i) / (1 - mu) := div_nonneg (pow_nonneg mu_pos.le _) h1mu.le
    calc |eigCoordU e| * (lam ^ i / (lam ^ n - 1)) * ‖vU‖
        ≤ Ccoord * ‖e‖ * (mu ^ (n - i) / (1 - mu)) * 2 :=
          mul_le_mul (mul_le_mul (abs_eigCoordU_le e) hratio hnn1 hnn2) norm_vU_le
            (norm_nonneg vU) (mul_nonneg hnn2 hnn3)
      _ = Cshadow * ‖e‖ * θ ^ (n - i) := by simp only [Cshadow, θ]; ring
  have hSterm : |eigCoordS e * mu ^ i / (mu ^ n - 1)| * ‖vS‖
      ≤ Cshadow * ‖e‖ * θ ^ i := by
    have habs : |eigCoordS e * mu ^ i / (mu ^ n - 1)|
        = |eigCoordS e| * (mu ^ i / (1 - mu ^ n)) := by
      rw [abs_div, abs_mul, abs_of_pos (pow_pos mu_pos i), abs_of_neg hmn1, neg_sub, mul_div_assoc]
    rw [habs]
    have hratio : mu ^ i / (1 - mu ^ n) ≤ mu ^ i / (1 - mu) := mu_ratio_le hn i
    have hnn1 : (0 : ℝ) ≤ mu ^ i / (1 - mu ^ n) := div_nonneg (pow_nonneg mu_pos.le _) (by linarith)
    have hnn2 : (0 : ℝ) ≤ Ccoord * ‖e‖ := mul_nonneg Ccoord_nonneg hnorme
    have hnn3 : (0 : ℝ) ≤ mu ^ i / (1 - mu) := div_nonneg (pow_nonneg mu_pos.le _) h1mu.le
    calc |eigCoordS e| * (mu ^ i / (1 - mu ^ n)) * ‖vS‖
        ≤ Ccoord * ‖e‖ * (mu ^ i / (1 - mu)) * 2 :=
          mul_le_mul (mul_le_mul (abs_eigCoordS_le e) hratio hnn1 hnn2) norm_vS_le
            (norm_nonneg vS) (mul_nonneg hnn2 hnn3)
      _ = Cshadow * ‖e‖ * θ ^ i := by simp only [Cshadow, θ]; ring
  have hsplit : Cshadow * ‖e‖ * (θ ^ (n - i) + θ ^ i)
      = Cshadow * ‖e‖ * θ ^ (n - i) + Cshadow * ‖e‖ * θ ^ i := by ring
  rw [hsplit]
  exact add_le_add hUterm hSterm

/-! ## The summed `ExpClosing`-shape bound (L7) -/

/-- The geometric partial-sum bound `∑_{i<n} t^i ≤ (1-t)⁻¹` for `0 ≤ t < 1`. (A local copy of
`ErgodicTheory.Livsic.geomSum_range_le_inv_one_sub`, kept to leave the Examples layer free of Livsic
imports.) -/
theorem geomSum_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, t ^ i ≤ (1 - t)⁻¹ := by
  have hsum := summable_geometric_of_lt_one h0 h1
  have hle := Summable.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg h0 i) hsum
  rwa [tsum_geometric_of_lt_one h0 h1] at hle

/-- **Summed shadowing bound** (the `ExpClosing` shape).  For `0 < α ≤ 1`, the `α`-th powers of the
forward shadow norms sum to a constant multiple of `‖e‖^α`:
`∑_{i<n} ‖catℝⁱ ·ᵥ w‖^α ≤ (2·Cshadow^α / (1 - θ^α)) · ‖e‖^α`. -/
theorem sum_rpow_norm_catShadow_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (e : Fin 2 → ℝ) :
    ∑ i ∈ Finset.range n, ‖(catℝ ^ i) *ᵥ catShadowSol n e‖ ^ α
      ≤ (2 * (Cshadow ^ α) / (1 - θ ^ α)) * ‖e‖ ^ α := by
  have hnorme : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have hCsh : 0 < Cshadow := Cshadow_pos
  have hθ0 : 0 < θ := θ_pos
  have hθ1 : θ < 1 := θ_lt_one
  have hθα0 : 0 < θ ^ α := Real.rpow_pos_of_pos hθ0 α
  have hθα1 : θ ^ α < 1 := Real.rpow_lt_one hθ0.le hθ1 hα0
  have hpr : ∀ m : ℕ, (θ ^ m) ^ α = (θ ^ α) ^ m := fun m => by
    rw [← Real.rpow_natCast θ m, ← Real.rpow_mul hθ0.le, ← Real.rpow_natCast (θ ^ α) m,
      ← Real.rpow_mul hθ0.le, mul_comm]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [Finset.range_zero, Finset.sum_empty]
    have hnum0 : (0 : ℝ) ≤ 2 * Cshadow ^ α :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hCsh.le α)
    have hden0 : (0 : ℝ) ≤ 1 - θ ^ α := by linarith
    exact mul_nonneg (div_nonneg hnum0 hden0) (Real.rpow_nonneg hnorme α)
  · have hterm : ∀ i ∈ Finset.range n,
        ‖(catℝ ^ i) *ᵥ catShadowSol n e‖ ^ α
          ≤ (Cshadow * ‖e‖) ^ α * ((θ ^ α) ^ (n - i) + (θ ^ α) ^ i) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      have hb := norm_catPow_catShadowSol_le n hn i (le_of_lt hi) e
      have hMnn : (0 : ℝ) ≤ Cshadow * ‖e‖ := mul_nonneg hCsh.le hnorme
      have hfac : (0 : ℝ) ≤ θ ^ (n - i) + θ ^ i :=
        add_nonneg (pow_nonneg hθ0.le _) (pow_nonneg hθ0.le _)
      calc ‖(catℝ ^ i) *ᵥ catShadowSol n e‖ ^ α
          ≤ (Cshadow * ‖e‖ * (θ ^ (n - i) + θ ^ i)) ^ α :=
            Real.rpow_le_rpow (norm_nonneg _) hb hα0.le
        _ = (Cshadow * ‖e‖) ^ α * (θ ^ (n - i) + θ ^ i) ^ α := Real.mul_rpow hMnn hfac
        _ ≤ (Cshadow * ‖e‖) ^ α * ((θ ^ (n - i)) ^ α + (θ ^ i) ^ α) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hMnn α)
            exact Real.rpow_add_le_add_rpow (pow_nonneg hθ0.le _) (pow_nonneg hθ0.le _) hα0.le hα1
        _ = (Cshadow * ‖e‖) ^ α * ((θ ^ α) ^ (n - i) + (θ ^ α) ^ i) := by rw [hpr, hpr]
    have hgeom_refl : ∑ i ∈ Finset.range n, (θ ^ α) ^ (n - i) ≤ (1 - θ ^ α)⁻¹ := by
      have hrefl : ∑ i ∈ Finset.range n, (θ ^ α) ^ (n - i)
          = ∑ i ∈ Finset.range n, (θ ^ α) ^ (i + 1) := by
        rw [← Finset.sum_range_reflect (fun i => (θ ^ α) ^ (n - i)) n]
        apply Finset.sum_congr rfl
        intro i hi; simp only [Finset.mem_range] at hi
        congr 1; omega
      rw [hrefl]
      calc ∑ i ∈ Finset.range n, (θ ^ α) ^ (i + 1)
          ≤ ∑ i ∈ Finset.range n, (θ ^ α) ^ i := by
            apply Finset.sum_le_sum
            intro i _
            rw [pow_succ]
            exact mul_le_of_le_one_right (pow_nonneg hθα0.le i) hθα1.le
        _ ≤ (1 - θ ^ α)⁻¹ := geomSum_le hθα0.le hθα1 n
    have hgeom_std : ∑ i ∈ Finset.range n, (θ ^ α) ^ i ≤ (1 - θ ^ α)⁻¹ :=
      geomSum_le hθα0.le hθα1 n
    calc ∑ i ∈ Finset.range n, ‖(catℝ ^ i) *ᵥ catShadowSol n e‖ ^ α
        ≤ ∑ i ∈ Finset.range n, (Cshadow * ‖e‖) ^ α * ((θ ^ α) ^ (n - i) + (θ ^ α) ^ i) :=
          Finset.sum_le_sum hterm
      _ = (Cshadow * ‖e‖) ^ α * ∑ i ∈ Finset.range n, ((θ ^ α) ^ (n - i) + (θ ^ α) ^ i) := by
          rw [← Finset.mul_sum]
      _ = (Cshadow * ‖e‖) ^ α *
            (∑ i ∈ Finset.range n, (θ ^ α) ^ (n - i) + ∑ i ∈ Finset.range n, (θ ^ α) ^ i) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (Cshadow * ‖e‖) ^ α * (2 * (1 - θ ^ α)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (mul_nonneg hCsh.le hnorme) α)
          linarith [hgeom_refl, hgeom_std]
      _ = 2 * Cshadow ^ α / (1 - θ ^ α) * ‖e‖ ^ α := by
          rw [Real.mul_rpow hCsh.le hnorme]; ring

end

end ErgodicTheory.CatMapToral
