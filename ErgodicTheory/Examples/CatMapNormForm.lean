/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapToral
import Mathlib.NumberTheory.Real.Irrational

/-!
# The invariant norm form of the cat map and the Diophantine growth bound

For the Arnold cat-map matrix `A = !![2,1;1,1]` this module records the **integer norm form**
`Q(p,q) = p² - p q - q²`, the norm form of the ring `ℤ[φ]` (discriminant `5`).  It is `A`-invariant
(`Qform_pow_mulVec`) and — being the norm of a nonzero element of `ℤ[φ]` — never vanishes on a
nonzero lattice vector (`Qform_ne_zero`), hence has absolute value `≥ 1`.

Factoring `Q` over the eigen-line coordinates `a₊ = ⟨![1, λ-2], ·⟩` and `a₋ = ⟨![1, μ-2], ·⟩`
gives `a₊(v) · a₋(v) = Q(v)`, with `a₊` scaling by `λᵏ` under `Aᵏ`.  Combining the lower bound
`|Q| ≥ 1` with the elementary sup-norm bounds `|a₋| ≤ λ · ‖·‖`, `|a₊| ≤ (λ-1) · ‖·‖` yields the
quantitative **expansion estimate**

`(√5 - 2) · λᵏ / ‖n‖ ≤ ‖Aᵏ n‖`   (`lemma_beta`),

the Diophantine input behind the quantitative (exponential) mixing of the hyperbolic toral
automorphism (Einsiedler–Ward, *Ergodic Theory*, Ch. 2 mechanism).

## Main results

* `ErgodicTheory.CatMapToral.Qform` — the norm form `p² - p q - q²`.
* `ErgodicTheory.CatMapToral.Qform_pow_mulVec` — exact `A`-invariance of `Q`.
* `ErgodicTheory.CatMapToral.Qform_ne_zero` — `Q(n) ≠ 0` for `n ≠ 0`.
* `ErgodicTheory.CatMapToral.aplus_mul_aminus_toR` — `a₊ · a₋ = Q` on the lattice.
* `ErgodicTheory.CatMapToral.aplus_pow` — `a₊(Aᵏ v) = λᵏ a₊(v)`.
* `ErgodicTheory.CatMapToral.lemma_beta` — the Diophantine growth bound.
-/

open Matrix

namespace ErgodicTheory.CatMapToral

noncomputable section

/-! ## The sup-norm and the integer→real cast -/

/-- Sup-norm (`ℓ^∞`) of a real `Fin 2`-vector. -/
def nr (v : Fin 2 → ℝ) : ℝ := max |v 0| |v 1|

/-- Entrywise integer→real cast of a `Fin 2`-vector. -/
def toR (n : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (n i : ℝ)

/-- The sup-norm is nonnegative. -/
lemma nr_nonneg (v : Fin 2 → ℝ) : 0 ≤ nr v := le_max_of_le_left (abs_nonneg _)

/-- The first coordinate is dominated by the sup-norm. -/
lemma abs_le_nr_0 (v : Fin 2 → ℝ) : |v 0| ≤ nr v := le_max_left _ _

/-- The second coordinate is dominated by the sup-norm. -/
lemma abs_le_nr_1 (v : Fin 2 → ℝ) : |v 1| ≤ nr v := le_max_right _ _

/-! ## The invariant integer norm form `Q(p,q) = p² - p q - q²` -/

/-- The `A`-invariant integer norm form of the cat map: the norm of `ℤ[φ]` (discriminant `5`). -/
def Qform (n : Fin 2 → ℤ) : ℤ := n 0 ^ 2 - n 0 * n 1 - n 1 ^ 2

/-- `catℤ *ᵥ n` written out componentwise. -/
lemma catℤ_mulVec_apply (n : Fin 2 → ℤ) :
    catℤ *ᵥ n = ![2 * n 0 + n 1, n 0 + n 1] := by
  funext i
  fin_cases i <;> simp [catℤ, mulVec, dotProduct, Fin.sum_univ_two]

/-- One step of the cat map leaves the norm form invariant. -/
lemma Qform_mulVec (n : Fin 2 → ℤ) : Qform (catℤ *ᵥ n) = Qform n := by
  simp only [Qform, catℤ_mulVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Every power of the cat map leaves the norm form invariant. -/
lemma Qform_pow_mulVec (k : ℕ) (n : Fin 2 → ℤ) : Qform (catℤ ^ k *ᵥ n) = Qform n := by
  induction k with
  | zero => simp
  | succ m ih => rw [pow_succ', ← mulVec_mulVec, Qform_mulVec, ih]

/-- The norm form is nonzero on nonzero lattice vectors: else `(2p-q)² = 5 q²` makes `√5` rational,
contradicting its irrationality. -/
lemma Qform_ne_zero {n : Fin 2 → ℤ} (hn : n ≠ 0) : Qform n ≠ 0 := by
  intro h
  simp only [Qform] at h
  by_cases hq : n 1 = 0
  · apply hn
    have hsq : (n 0) ^ 2 = 0 := by rw [hq] at h; linear_combination h
    have hn0 : n 0 = 0 := by
      have := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
      exact this
    funext i
    fin_cases i <;> simp only [Pi.zero_apply]
    · exact hn0
    · exact hq
  · have hb : (n 1 : ℚ) ≠ 0 := by exact_mod_cast hq
    have hQℚ : (n 0 : ℚ) ^ 2 - (n 0 : ℚ) * (n 1 : ℚ) - (n 1 : ℚ) ^ 2 = 0 := by
      exact_mod_cast h
    set c : ℚ := (2 * (n 0 : ℚ) - (n 1 : ℚ)) / (n 1 : ℚ) with hc
    have hc2 : c ^ 2 = 5 := by
      rw [hc, div_pow, div_eq_iff (pow_ne_zero 2 hb)]
      linear_combination 4 * hQℚ
    have hirr : Irrational (Real.sqrt 5) := (by decide : Nat.Prime 5).irrational_sqrt
    apply hirr
    refine ⟨|c|, ?_⟩
    have h5 : ((c : ℝ)) ^ 2 = 5 := by rw [← Rat.cast_pow, hc2]; norm_num
    rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, h5]

/-- Absolute value of the norm form is at least one on nonzero lattice vectors. -/
lemma one_le_abs_Qform {n : Fin 2 → ℤ} (hn : n ≠ 0) : 1 ≤ |Qform n| := by
  have hz : Qform n ≠ 0 := Qform_ne_zero hn
  rcases lt_or_gt_of_ne hz with h | h
  · rw [abs_of_neg h]; omega
  · rw [abs_of_pos h]; omega

/-! ## Eigen-line coordinates and the factorisation `a₊ a₋ = Q` -/

/-- Coordinate along the expanding eigen-covector `![1, λ-2]`. -/
def aplus (v : Fin 2 → ℝ) : ℝ := v 0 + (lam - 2) * v 1

/-- Coordinate along the contracting eigen-covector `![1, μ-2]`. -/
def aminus (v : Fin 2 → ℝ) : ℝ := v 0 + (mu - 2) * v 1

/-- The two eigen-coordinates multiply to the norm form. -/
lemma aplus_mul_aminus (v : Fin 2 → ℝ) :
    aplus v * aminus v = v 0 ^ 2 - v 0 * v 1 - v 1 ^ 2 := by
  simp only [aplus, aminus]
  linear_combination (v 0 * v 1 - 2 * v 1 ^ 2) * lam_add_mu + (v 1 ^ 2) * lam_mul_mu

/-- On the lattice, `a₊ · a₋` equals the integer norm form. -/
lemma aplus_mul_aminus_toR (n : Fin 2 → ℤ) :
    aplus (toR n) * aminus (toR n) = (Qform n : ℝ) := by
  rw [aplus_mul_aminus]
  simp only [toR, Qform]
  push_cast
  ring

/-- `a₊` as pairing with the expanding eigen-covector. -/
lemma aplus_eq_dot (v : Fin 2 → ℝ) :
    aplus v = (![1, lam - 2] : Fin 2 → ℝ) ⬝ᵥ v := by
  simp only [aplus, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul]

/-- `a₊` scales by `λᵏ` under the `k`-th power of the cat map. -/
lemma aplus_pow (k : ℕ) (v : Fin 2 → ℝ) :
    aplus (catℝ ^ k *ᵥ v) = lam ^ k * aplus v := by
  rw [aplus_eq_dot, aplus_eq_dot, dotProduct_pow_mulVec, catℝ_pow_mulVec_eigen_lam,
    smul_dotProduct, smul_eq_mul]

/-! ## Sup-norm bounds on the eigen-coordinates -/

/-- `|μ - 2| = λ - 1`. -/
lemma abs_mu_sub_two : |mu - 2| = lam - 1 := by
  have hneg : mu - 2 < 0 := by unfold mu; linarith [two_lt_sqrt5]
  rw [abs_of_neg hneg]; unfold lam mu; ring

/-- The contracting coordinate is bounded by `λ · ‖·‖`. -/
lemma abs_aminus_le (v : Fin 2 → ℝ) : |aminus v| ≤ lam * nr v := by
  have h1 : |aminus v| ≤ |v 0| + (lam - 1) * |v 1| := by
    unfold aminus
    calc |v 0 + (mu - 2) * v 1| ≤ |v 0| + |(mu - 2) * v 1| := abs_add_le _ _
      _ = |v 0| + |mu - 2| * |v 1| := by rw [abs_mul]
      _ = |v 0| + (lam - 1) * |v 1| := by rw [abs_mu_sub_two]
  have hn0 := abs_le_nr_0 v
  have hn1 := abs_le_nr_1 v
  have hp : (0 : ℝ) ≤ lam - 1 := by linarith [one_lt_lam]
  nlinarith [h1, hn0, hn1, mul_le_mul_of_nonneg_left hn1 hp]

/-- The expanding coordinate is bounded by `(λ - 1) · ‖·‖`. -/
lemma abs_aplus_le (v : Fin 2 → ℝ) : |aplus v| ≤ (lam - 1) * nr v := by
  have hlam2 : (0 : ℝ) ≤ lam - 2 := by unfold lam; linarith [two_lt_sqrt5]
  have h1 : |aplus v| ≤ |v 0| + (lam - 2) * |v 1| := by
    unfold aplus
    calc |v 0 + (lam - 2) * v 1| ≤ |v 0| + |(lam - 2) * v 1| := abs_add_le _ _
      _ = |v 0| + |lam - 2| * |v 1| := by rw [abs_mul]
      _ = |v 0| + (lam - 2) * |v 1| := by rw [abs_of_nonneg hlam2]
  have hn0 := abs_le_nr_0 v
  have hn1 := abs_le_nr_1 v
  nlinarith [h1, hn0, hn1, mul_le_mul_of_nonneg_left hn1 hlam2]

/-! ## The Diophantine growth bound -/

/-- Casting an integer orbit step to `ℝ` is the corresponding real orbit step. -/
lemma toR_pow_mulVec (k : ℕ) (n : Fin 2 → ℤ) :
    toR (catℤ ^ k *ᵥ n) = catℝ ^ k *ᵥ toR n := by
  exact cast_pow_mulVec k n

/-- The explicit positive constant: `(λ-1) · λ · (√5 - 2) = 1`. -/
lemma beta_const_identity : (lam - 1) * lam * (Real.sqrt 5 - 2) = 1 := by
  unfold lam
  linear_combination ((Real.sqrt 5 + 2) / 4) * sqrt5_sq

/-- The sup-norm of a nonzero lattice vector is strictly positive. -/
lemma nr_toR_pos {n : Fin 2 → ℤ} (hn : n ≠ 0) : 0 < nr (toR n) := by
  rcases eq_or_lt_of_le (nr_nonneg (toR n)) with h | h
  · exfalso
    apply hn
    have h0 : |toR n 0| ≤ 0 := (abs_le_nr_0 (toR n)).trans (le_of_eq h.symm)
    have h1 : |toR n 1| ≤ 0 := (abs_le_nr_1 (toR n)).trans (le_of_eq h.symm)
    funext i
    fin_cases i <;> simp only [Pi.zero_apply]
    · have h' : ((n 0 : ℝ)) = 0 := abs_nonpos_iff.mp h0
      exact_mod_cast h'
    · have h' : ((n 1 : ℝ)) = 0 := abs_nonpos_iff.mp h1
      exact_mod_cast h'
  · exact h

/-- **Diophantine growth bound.**  For a nonzero lattice vector `n`, the forward orbit sup-norm
grows at least like `λᵏ`: `(√5 - 2) · λᵏ / ‖n‖ ≤ ‖Aᵏ n‖`.  The engine is the never-vanishing
invariant norm form `|Q| ≥ 1` factored through the expanding eigen-coordinate. -/
lemma lemma_beta {n : Fin 2 → ℤ} (hn : n ≠ 0) (k : ℕ) :
    (Real.sqrt 5 - 2) * lam ^ k / nr (toR n) ≤ nr (toR (catℤ ^ k *ᵥ n)) := by
  have hnrpos : 0 < nr (toR n) := nr_toR_pos hn
  have hlampos : 0 < lam := by linarith [one_lt_lam]
  have hlamk_pos : 0 < lam ^ k := pow_pos hlampos k
  have htpos : 0 < Real.sqrt 5 - 2 := by linarith [two_lt_sqrt5]
  have hdenpos : 0 < lam * nr (toR n) := mul_pos hlampos hnrpos
  -- `|Q| ≥ 1` transported to the eigen-coordinate product
  have hQ1 : (1 : ℝ) ≤ |aplus (toR n) * aminus (toR n)| := by
    rw [aplus_mul_aminus_toR, ← Int.cast_abs]
    exact_mod_cast one_le_abs_Qform hn
  have hamin : |aminus (toR n)| ≤ lam * nr (toR n) := abs_aminus_le (toR n)
  have hsplit : |aplus (toR n)| * |aminus (toR n)| = |aplus (toR n) * aminus (toR n)| :=
    (abs_mul _ _).symm
  have hlow : 1 ≤ |aplus (toR n)| * (lam * nr (toR n)) := by
    calc (1 : ℝ) ≤ |aplus (toR n)| * |aminus (toR n)| := by rw [hsplit]; exact hQ1
      _ ≤ |aplus (toR n)| * (lam * nr (toR n)) :=
          mul_le_mul_of_nonneg_left hamin (abs_nonneg _)
  -- the iterate's expanding coordinate scales by `λᵏ`
  have hiter : aplus (toR (catℤ ^ k *ᵥ n)) = lam ^ k * aplus (toR n) := by
    rw [toR_pow_mulVec, aplus_pow]
  have hbound : |aplus (toR (catℤ ^ k *ᵥ n))| ≤ (lam - 1) * nr (toR (catℤ ^ k *ᵥ n)) :=
    abs_aplus_le _
  have habs_iter : |aplus (toR (catℤ ^ k *ᵥ n))| = lam ^ k * |aplus (toR n)| := by
    rw [hiter, abs_mul, abs_of_pos hlamk_pos]
  rw [habs_iter] at hbound
  have step1 : lam ^ k * |aplus (toR n)| * (lam * nr (toR n))
      ≤ (lam - 1) * nr (toR (catℤ ^ k *ᵥ n)) * (lam * nr (toR n)) :=
    mul_le_mul_of_nonneg_right hbound hdenpos.le
  have step2 : lam ^ k ≤ lam ^ k * (|aplus (toR n)| * (lam * nr (toR n))) :=
    le_mul_of_one_le_right hlamk_pos.le hlow
  have chain : lam ^ k ≤ (lam - 1) * nr (toR (catℤ ^ k *ᵥ n)) * (lam * nr (toR n)) := by
    calc lam ^ k ≤ lam ^ k * (|aplus (toR n)| * (lam * nr (toR n))) := step2
      _ = lam ^ k * |aplus (toR n)| * (lam * nr (toR n)) := by ring
      _ ≤ (lam - 1) * nr (toR (catℤ ^ k *ᵥ n)) * (lam * nr (toR n)) := step1
  have chain' : lam ^ k ≤ (lam - 1) * lam * (nr (toR (catℤ ^ k *ᵥ n)) * nr (toR n)) := by
    have e : (lam - 1) * nr (toR (catℤ ^ k *ᵥ n)) * (lam * nr (toR n))
        = (lam - 1) * lam * (nr (toR (catℤ ^ k *ᵥ n)) * nr (toR n)) := by ring
    rw [e] at chain; exact chain
  set I := nr (toR (catℤ ^ k *ᵥ n)) with hI
  set P := nr (toR n) with hP
  have hbeta' : (Real.sqrt 5 - 2) * ((lam - 1) * lam) = 1 := by
    linear_combination beta_const_identity
  have hfin : (Real.sqrt 5 - 2) * lam ^ k
      ≤ (Real.sqrt 5 - 2) * ((lam - 1) * lam * (I * P)) :=
    mul_le_mul_of_nonneg_left chain' htpos.le
  rw [div_le_iff₀ hnrpos]
  calc (Real.sqrt 5 - 2) * lam ^ k
      ≤ (Real.sqrt 5 - 2) * ((lam - 1) * lam * (I * P)) := hfin
    _ = ((Real.sqrt 5 - 2) * ((lam - 1) * lam)) * (I * P) := by ring
    _ = I * P := by rw [hbeta']; ring

end

end ErgodicTheory.CatMapToral
