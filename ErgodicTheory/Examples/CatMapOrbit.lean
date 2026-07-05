/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The cat-map index orbit is infinite

For the Arnold cat-map matrix `M = !![2,1;1,1] : Matrix (Fin 2) (Fin 2) ℤ`, this file proves
that the forward orbit `p ↦ Mᵖ ·ᵥ v` of any nonzero integer vector `v` is **injective in `p`**,
hence the orbit is an infinite set.  This is the number-theoretic heart of the ergodicity proof
for the hyperbolic toral automorphism: a Fourier coefficient that is constant along such an orbit
and `ℓ²`-summable must vanish.

The argument is the eigen-covector / growth one (Walkden, *Ergodic Theory*, Lecture 17): the matrix
`M` is symmetric with two real eigenvalues `λ = (3+√5)/2 > 1` and `λ⁻¹ = (3-√5)/2 ∈ (0,1)`,
neither a root of unity.  Pairing a vector with the two eigen-covectors `w` (for `λ`) and `u`
(for `λ⁻¹`) gives two real functionals `φ, ψ` with `φ(Mᵏ v) = λᵏ φ(v)` and `ψ(Mᵏ v) = λ⁻ᵏ ψ(v)`.
If `Mᵏ v = v` for some `k ≥ 1` then `φ(v) = λᵏ φ(v)` and `ψ(v) = λ⁻ᵏ ψ(v)` with `λᵏ ≠ 1`, forcing
`φ(v) = ψ(v) = 0`; since `w, u` span, `v = 0`.

## Main results

* `ErgodicTheory.CatMapToral.catℤ` — the integer cat-map matrix `!![2,1;1,1]`.
* `ErgodicTheory.CatMapToral.eq_zero_of_pow_mulVec_eq` — `Mᵏ ·ᵥ v = v`, `k ≥ 1` ⇒ `v = 0` over ℝ.
* `ErgodicTheory.CatMapToral.orbit_injective` — `p ↦ Mᵖ ·ᵥ v` is injective for nonzero integer `v`.
* `ErgodicTheory.CatMapToral.orbit_infinite` — the orbit `{Mᵖ ·ᵥ v | p}` is infinite for nonzero `v`.
-/

open Matrix

namespace ErgodicTheory.CatMapToral

/-! ## The cat-map matrix and its real eigen-data -/

/-- The Arnold cat-map matrix `!![2,1;1,1]` over `ℤ`. -/
def catℤ : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]

/-- The cat-map matrix over `ℝ` (entrywise integer cast). -/
noncomputable def catℝ : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]

/-- The dominant eigenvalue `λ = (3 + √5)/2 > 1`. -/
noncomputable def lam : ℝ := (3 + Real.sqrt 5) / 2

/-- `√5 < 3` (since `5 < 9`). -/
lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have : Real.sqrt 5 < Real.sqrt 9 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  rwa [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this

/-- `2 < √5` (since `4 < 5`). -/
lemma two_lt_sqrt5 : 2 < Real.sqrt 5 := by
  have : Real.sqrt 4 < Real.sqrt 5 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this

/-- `(√5)² = 5`. -/
lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- The dominant eigenvalue is hyperbolic: `1 < λ`. -/
lemma one_lt_lam : 1 < lam := by
  unfold lam
  have := two_lt_sqrt5
  linarith

/-- `λ` satisfies the characteristic equation `λ² = 3λ - 1`. -/
lemma lam_sq : lam ^ 2 = 3 * lam - 1 := by
  unfold lam
  have h : Real.sqrt 5 ^ 2 = 5 := sqrt5_sq
  nlinarith [h]

/-- The stable eigenvalue `μ = (3 - √5)/2`. -/
noncomputable def mu : ℝ := (3 - Real.sqrt 5) / 2

/-- `μ` satisfies the same characteristic equation `μ² = 3μ - 1`. -/
lemma mu_sq : mu ^ 2 = 3 * mu - 1 := by
  unfold mu
  have h : Real.sqrt 5 ^ 2 = 5 := sqrt5_sq
  nlinarith [h]

/-- The two eigenvalues are distinct: `λ - μ = √5 ≠ 0`. -/
lemma lam_sub_mu : lam - mu = Real.sqrt 5 := by
  unfold lam mu; ring

/-! ## The growth functionals coming from the two eigen-covectors

Because `catℝ` is symmetric, an eigenvector is simultaneously an eigen-covector.  Pairing with
`![1, λ-2]` and `![1, μ-2]` (the eigenvectors for `λ` and `μ`) gives two linear functionals that
scale by `λ` and `μ` respectively under one step of the dynamics.
-/

/-- Evaluate `catℝ *ᵥ v` componentwise as a `Fin 2` vector. -/
lemma catℝ_mulVec_apply (v : Fin 2 → ℝ) :
    catℝ *ᵥ v = ![2 * v 0 + v 1, v 0 + v 1] := by
  funext i
  fin_cases i <;> simp [catℝ, mulVec, dotProduct, Fin.sum_univ_two]

/-- One application of the cat-map matrix to the `λ`-eigenvector scales it by `λ`. -/
lemma catℝ_mulVec_eigen_lam : catℝ *ᵥ ![1, lam - 2] = lam • ![1, lam - 2] := by
  rw [catℝ_mulVec_apply, Matrix.smul_cons, smul_eq_mul, Matrix.smul_cons, smul_eq_mul,
    Matrix.smul_empty]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (2 : ℝ) * 1 + (lam - 2) = lam * 1 by ring,
    show (1 : ℝ) + (lam - 2) = lam * (lam - 2) by linear_combination -lam_sq]

/-- One application of the cat-map matrix to the `μ`-eigenvector scales it by `μ`. -/
lemma catℝ_mulVec_eigen_mu : catℝ *ᵥ ![1, mu - 2] = mu • ![1, mu - 2] := by
  rw [catℝ_mulVec_apply, Matrix.smul_cons, smul_eq_mul, Matrix.smul_cons, smul_eq_mul,
    Matrix.smul_empty]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (2 : ℝ) * 1 + (mu - 2) = mu * 1 by ring,
    show (1 : ℝ) + (mu - 2) = mu * (mu - 2) by linear_combination -mu_sq]

/-- `catℝ` is symmetric, hence equal to its transpose. -/
lemma catℝ_transpose : catℝᵀ = catℝ := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The `k`-th power of `catℝ` scales the `λ`-eigenvector by `λᵏ`. -/
lemma catℝ_pow_mulVec_eigen_lam (k : ℕ) :
    catℝ ^ k *ᵥ ![1, lam - 2] = lam ^ k • ![1, lam - 2] := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mulVec_mulVec, catℝ_mulVec_eigen_lam, mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- The `k`-th power of `catℝ` scales the `μ`-eigenvector by `μᵏ`. -/
lemma catℝ_pow_mulVec_eigen_mu (k : ℕ) :
    catℝ ^ k *ᵥ ![1, mu - 2] = mu ^ k • ![1, mu - 2] := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mulVec_mulVec, catℝ_mulVec_eigen_mu, mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- Adjoint identity for the symmetric matrix `catℝ` and its powers:
`w ⬝ᵥ (catℝᵏ *ᵥ v) = (catℝᵏ *ᵥ w) ⬝ᵥ v`. -/
lemma dotProduct_pow_mulVec (k : ℕ) (w v : Fin 2 → ℝ) :
    w ⬝ᵥ (catℝ ^ k *ᵥ v) = (catℝ ^ k *ᵥ w) ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_pow, catℝ_transpose]

/-! ## A `+1`-eigenvector of a power forces the zero vector -/

/-- If `catℝᵏ ·ᵥ v = v` for some `k ≥ 1`, then `v = 0`.  Pairing with the two eigen-covectors
collapses both coordinates: the `λ`-pairing gives `λᵏ ⟨w,v⟩ = ⟨w,v⟩` with `λᵏ ≠ 1`, hence
`⟨w,v⟩ = 0`; likewise `⟨u,v⟩ = 0`; the two covectors are independent, so `v = 0`. -/
lemma eq_zero_of_pow_mulVec_eq {k : ℕ} (hk : 1 ≤ k) {v : Fin 2 → ℝ}
    (hv : catℝ ^ k *ᵥ v = v) : v = 0 := by
  -- `λᵏ ≠ 1` because `λ > 1`; later `μᵏ ≠ 1` because `0 < μ < 1` forces `μᵏ < 1`.
  have hlam_pow : lam ^ k ≠ 1 := by
    have : 1 < lam ^ k := one_lt_pow₀ one_lt_lam (by omega)
    linarith
  -- `⟨w, v⟩ = 0` from `λᵏ ⟨w,v⟩ = ⟨w,v⟩`.
  have hw : (![1, lam - 2] : Fin 2 → ℝ) ⬝ᵥ v = 0 := by
    have key : lam ^ k * ((![1, lam - 2] : Fin 2 → ℝ) ⬝ᵥ v)
        = (![1, lam - 2] : Fin 2 → ℝ) ⬝ᵥ v := by
      have h1 : (![1, lam - 2] : Fin 2 → ℝ) ⬝ᵥ (catℝ ^ k *ᵥ v)
          = (![1, lam - 2] : Fin 2 → ℝ) ⬝ᵥ v := by rw [hv]
      rw [dotProduct_pow_mulVec, catℝ_pow_mulVec_eigen_lam, smul_dotProduct, smul_eq_mul] at h1
      exact h1
    -- `(λᵏ - 1) * c = λᵏ c - c = c - c = 0` and `λᵏ - 1 ≠ 0` give `c = 0`.
    have hfac : (lam ^ k - 1) * ((![1, lam - 2] : Fin 2 → ℝ) ⬝ᵥ v) = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith [h] : lam ^ k = 1) hlam_pow
    · exact h
  -- Symmetric argument for `μᵏ`.  Here `μ ∈ (0,1)` so also `μᵏ ≠ 1`.
  have hmu_lt_one : mu < 1 := by
    unfold mu; have := two_lt_sqrt5; linarith
  have hmu_pos : 0 < mu := by
    unfold mu; have := sqrt5_lt_three; linarith
  have hmu_pow : mu ^ k ≠ 1 := by
    have : mu ^ k < 1 := pow_lt_one₀ hmu_pos.le hmu_lt_one (by omega)
    linarith
  have hu : (![1, mu - 2] : Fin 2 → ℝ) ⬝ᵥ v = 0 := by
    have key : mu ^ k * ((![1, mu - 2] : Fin 2 → ℝ) ⬝ᵥ v)
        = (![1, mu - 2] : Fin 2 → ℝ) ⬝ᵥ v := by
      have h1 : (![1, mu - 2] : Fin 2 → ℝ) ⬝ᵥ (catℝ ^ k *ᵥ v)
          = (![1, mu - 2] : Fin 2 → ℝ) ⬝ᵥ v := by rw [hv]
      rw [dotProduct_pow_mulVec, catℝ_pow_mulVec_eigen_mu, smul_dotProduct, smul_eq_mul] at h1
      exact h1
    have hfac : (mu ^ k - 1) * ((![1, mu - 2] : Fin 2 → ℝ) ⬝ᵥ v) = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith [h] : mu ^ k = 1) hmu_pow
    · exact h
  -- Expand both dot products and solve the linear system.
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul] at hw hu
  -- `hw : v 0 + (lam - 2) * v 1 = 0`,  `hu : v 0 + (mu - 2) * v 1 = 0`.
  -- Subtract: `(lam - mu) * v 1 = 0`, and `lam - mu = √5 ≠ 0`, so `v 1 = 0`, then `v 0 = 0`.
  have hdiff : (lam - mu) * v 1 = 0 := by linear_combination hw - hu
  have hlm : lam - mu ≠ 0 := by
    rw [lam_sub_mu]; have := two_lt_sqrt5; linarith
  have hv1 : v 1 = 0 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact absurd h hlm
    · exact h
  have hv0 : v 0 = 0 := by
    rw [hv1, mul_zero, add_zero] at hw; exact hw
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

/-! ## From the eigen-collapse to orbit injectivity and infiniteness -/

/-- The real cat-map matrix is the entrywise integer cast of the integer one. -/
lemma catℝ_eq_map_catℤ : catℝ = catℤ.map ((↑) : ℤ → ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [catℝ, catℤ]

/-- `det catℝ = 1`, hence every power has nonzero determinant. -/
lemma det_catℝ : catℝ.det = 1 := by
  rw [catℝ, Matrix.det_fin_two_of]; norm_num

/-- `catℝ ^ p` is the entrywise integer cast of `catℤ ^ p`. -/
lemma catℝ_pow_eq_map (p : ℕ) : catℝ ^ p = (catℤ ^ p).map ((↑) : ℤ → ℝ) := by
  rw [catℝ_eq_map_catℤ]
  exact (Matrix.map_pow catℤ (Int.castRingHom ℝ) p).symm

/-- Casting an integer orbit step to `ℝ` is the corresponding real orbit step. -/
lemma cast_pow_mulVec (p : ℕ) (v : Fin 2 → ℤ) :
    (fun i => ((catℤ ^ p *ᵥ v) i : ℝ)) = catℝ ^ p *ᵥ (fun i => (v i : ℝ)) := by
  funext i
  rw [catℝ_pow_eq_map]
  exact RingHom.map_mulVec (Int.castRingHom ℝ) (catℤ ^ p) v i

/-- **Orbit injectivity.** For nonzero integer `v`, the forward orbit `p ↦ catℤᵖ ·ᵥ v` is
injective. -/
theorem orbit_injective {v : Fin 2 → ℤ} (hv : v ≠ 0) :
    Function.Injective (fun p : ℕ => catℤ ^ p *ᵥ v) := by
  -- It suffices to show: `p < q ⇒ catℤᵖ ·ᵥ v ≠ catℤ^q ·ᵥ v`; then the map is injective.
  have key : ∀ p q : ℕ, p < q → catℤ ^ p *ᵥ v ≠ catℤ ^ q *ᵥ v := by
    intro p q hlt hpq
    -- Cast to `ℝ`.
    have hcast : catℝ ^ p *ᵥ (fun i => (v i : ℝ)) = catℝ ^ q *ᵥ (fun i => (v i : ℝ)) := by
      rw [← cast_pow_mulVec, ← cast_pow_mulVec, hpq]
    set vℝ : Fin 2 → ℝ := fun i => (v i : ℝ) with hvℝ
    -- `catℝ ^ (q - p) *ᵥ (catℝ ^ p *ᵥ vℝ) = catℝ ^ p *ᵥ vℝ`.
    have hqp : q = (q - p) + p := by omega
    have hstep : catℝ ^ (q - p) *ᵥ (catℝ ^ p *ᵥ vℝ) = catℝ ^ p *ᵥ vℝ := by
      rw [mulVec_mulVec, ← pow_add, ← hqp, ← hcast]
    have hw0 : catℝ ^ p *ᵥ vℝ = 0 := eq_zero_of_pow_mulVec_eq (by omega) hstep
    -- `catℝ ^ p` is invertible (`det = 1`), so `vℝ = 0`, contradicting `v ≠ 0`.
    have hdet : (catℝ ^ p).det ≠ 0 := by rw [det_pow, det_catℝ]; norm_num
    have hvℝ0 : vℝ = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw0
    apply hv
    funext i
    have := congrFun hvℝ0 i
    simp only [hvℝ, Pi.zero_apply] at this
    exact_mod_cast this
  intro p q hpq
  rcases lt_trichotomy p q with h | h | h
  · exact absurd hpq (key p q h)
  · exact h
  · exact absurd hpq.symm (key q p h)

/-- **Orbit infiniteness.** For nonzero integer `v`, the orbit `{catℤᵖ ·ᵥ v | p}` is infinite. -/
theorem orbit_infinite {v : Fin 2 → ℤ} (hv : v ≠ 0) :
    (Set.range (fun p : ℕ => catℤ ^ p *ᵥ v)).Infinite :=
  Set.infinite_range_of_injective (orbit_injective hv)

end ErgodicTheory.CatMapToral
