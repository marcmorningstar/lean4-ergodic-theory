/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ExteriorNorm
import Oseledets.Cocycle.FurstenbergKesten
import Oseledets.Ergodic.Kingman
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Oseledets singular-value (scalar) layer

This module builds the **scalar (singular-value) layer** of the Oseledets multiplicative
ergodic theorem: the genuine ergodic limits
`Γ_k = lim_n (1/n) log ∏_{i<k} σᵢ(A⁽ⁿ⁾)` and the per-exponent limits
`λᵢ = Γ_{i+1} − Γ_i` (the logarithms of the eigenvalues of the limiting matrix `Λ`),
*without ever constructing `Λ` as a matrix limit*.

The analytic input is the already-proved submultiplicativity of the product of the top-`k`
singular values (`ExteriorNorm.prod_singularValues_comp_le`), turned into a subadditive
cocycle and fed to Kingman's ergodic theorem (`tendsto_kingman_ergodic`).

## Main definitions

* `Oseledets.gram` — the Gram matrix `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾` of the cocycle iterate.
* `Oseledets.Sprod` — the product of the top-`k` singular values of `toEuclideanLin (A⁽ⁿ⁾)`.

## Main results

* `LinearMap.singularValues_le_opNorm` / `Oseledets.sigma_le_opNorm` (**infra M-1**) —
  `σᵢ(f) ≤ ‖f‖` and `σᵢ(toEuclideanLin M) ≤ ‖M‖`.
* `Oseledets.Sprod_submul`, `Oseledets.logSprod_subadditive`,
  `Oseledets.isSubadditiveCocycle_logSprod` (**L1**).
* `Oseledets.integrable_logSprod`, `Oseledets.bddBelow_logSprod` (**L3**).
* `Oseledets.tendsto_GammaK` (**L4**) — the genuine ergodic `Γ_k` limit.
* `Oseledets.lamSing`, `Oseledets.tendsto_log_singularValue`, `Oseledets.lamSing_antitone`
  (**L5**).
* `Oseledets.sq_singularValues_eq_gram_eigenvalue` (**L6**).
-/

open Module InnerProductSpace MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator Matrix

noncomputable section

/-! ## Infra M-1: a singular value is bounded by the operator norm

`σᵢ(f) ≤ ‖f‖` for a linear map `f` between finite-dimensional inner product spaces.
This is genuinely missing from Mathlib (`SingularValues.lean` has no connection to the
operator norm); it is upstreamable. The proof: the right singular vectors `uᵢ` (an
orthonormal eigenvector basis of `adjoint f ∘ₗ f`) satisfy `‖f uᵢ‖ = σᵢ(f)`, and
`‖f uᵢ‖ ≤ ‖f‖ · ‖uᵢ‖ = ‖f‖`. -/

namespace LinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The norm of the image of a right singular vector is the corresponding singular value:
`‖f uᵢ‖ = σᵢ(f)`, where `u` is the orthonormal eigenvector basis of `adjoint f ∘ₗ f`. This is
the analytic heart of the singular value decomposition. -/
theorem norm_apply_eigenvectorBasis_eq_singularValues (f : E →ₗ[ℝ] F) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (i : Fin n) :
    ‖f ((f.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i)‖ = f.singularValues i := by
  set hT := f.isSymmetric_adjoint_comp_self with hThT
  set u := hT.eigenvectorBasis hn with hu
  -- `⟪f uᵢ, f uᵢ⟫ = ⟪(adjoint f ∘ₗ f) uᵢ, uᵢ⟫ = eigenvalue · ⟪uᵢ, uᵢ⟫ = σᵢ²`.
  have key : (inner ℝ (f (u i)) (f (u i)) : ℝ) = f.singularValues i ^ 2 := by
    have h1 : (inner ℝ (f (u i)) (f (u i)) : ℝ)
        = inner ℝ ((LinearMap.adjoint f ∘ₗ f) (u i)) (u i) := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    rw [h1, show (LinearMap.adjoint f ∘ₗ f) (u i) = (hT.eigenvalues hn i : ℝ) • u i from
          hT.apply_eigenvectorBasis hn i, inner_smul_left, u.inner_eq_ite i i,
        f.sq_singularValues_fin hn i]
    simp
  have hsq : ‖f (u i)‖ ^ 2 = f.singularValues i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]; exact key
  nlinarith [norm_nonneg (f (u i)), f.singularValues_nonneg i, hsq]

/-- **Infra M-1.** Every singular value of a linear map between finite-dimensional inner
product spaces is bounded by its operator norm: `σᵢ(f) ≤ ‖f‖`. -/
theorem singularValues_le_opNorm (f : E →ₗ[ℝ] F) (i : ℕ) :
    f.singularValues i ≤ ‖LinearMap.toContinuousLinearMap f‖ := by
  set n := Module.finrank ℝ E with hn
  by_cases hi : i < n
  · -- `σᵢ = ‖f uᵢ‖ ≤ ‖f‖ · ‖uᵢ‖ = ‖f‖`.
    set u := f.isSymmetric_adjoint_comp_self.eigenvectorBasis hn.symm with hu
    have heq : f.singularValues i = ‖f (u ⟨i, hi⟩)‖ :=
      (f.norm_apply_eigenvectorBasis_eq_singularValues hn.symm ⟨i, hi⟩).symm
    have hbound : ‖f (u ⟨i, hi⟩)‖ ≤ ‖LinearMap.toContinuousLinearMap f‖ * ‖u ⟨i, hi⟩‖ := by
      have := (LinearMap.toContinuousLinearMap f).le_opNorm (u ⟨i, hi⟩)
      rwa [LinearMap.coe_toContinuousLinearMap'] at this
    have hu1 : ‖u ⟨i, hi⟩‖ = 1 := u.orthonormal.1 _
    rw [hu1, mul_one] at hbound
    rw [heq]; exact hbound
  · -- `σᵢ = 0` for `i ≥ n`.
    rw [f.singularValues_of_finrank_le (not_lt.mp hi)]
    exact norm_nonneg _

end LinearMap

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## The Gram matrix and the singular-value product -/

/-- The **Gram matrix** `Qₙ = (A⁽ⁿ⁾)ᵀ · A⁽ⁿ⁾` of the cocycle iterate. Its eigenvalues are the
squared singular values of `A⁽ⁿ⁾` (see `sq_singularValues_eq_gram_eigenvalue`). -/
def gram (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    Matrix (Fin d) (Fin d) ℝ :=
  (cocycle A T n x)ᵀ * cocycle A T n x

/-- The **top-`k` singular value product** of the cocycle iterate, as a Euclidean linear map. -/
def Sprod (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (k n : ℕ) (x : X) : ℝ :=
  ∏ i ∈ Finset.range k,
    (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i

/-- `toEuclideanLin` turns a matrix product into a composition of linear maps. -/
private theorem toEuclideanLin_mul (M N : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.toEuclideanLin (M * N)
      = (Matrix.toEuclideanLin M) ∘ₗ (Matrix.toEuclideanLin N) := by
  ext v i
  simp only [Matrix.toEuclideanLin_apply, LinearMap.comp_apply, Matrix.mulVec_mulVec]

/-! ## L1: subadditivity of `log Sprod` -/

/-- **L1 — submultiplicativity of `Sprod`.** `∏σ(A⁽ᵐ⁺ⁿ⁾) ≤ ∏σ(A⁽ᵐ⁾∘Tⁿ) · ∏σ(A⁽ⁿ⁾)`. -/
theorem Sprod_submul (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (k m n : ℕ) (x : X) :
    Sprod A T k (m + n) x ≤ Sprod A T k m (T^[n] x) * Sprod A T k n x := by
  unfold Sprod
  rw [cocycle_add, toEuclideanLin_mul]
  exact ExteriorNorm.prod_singularValues_comp_le k (Matrix.toEuclideanLin (cocycle A T n x))
    (Matrix.toEuclideanLin (cocycle A T m (T^[n] x)))

/-- **L1 — subadditivity of `log Sprod`** in the plain (`T^[n]`-shifted) split, provided each
`Sprod` is positive (true for an invertible cocycle and `k ≤ d`). -/
theorem logSprod_subadditive (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (k m n : ℕ) (x : X)
    (hpos : ∀ (j : ℕ) (y : X), 0 < Sprod A T k j y) :
    Real.log (Sprod A T k (m + n) x)
      ≤ Real.log (Sprod A T k m (T^[n] x)) + Real.log (Sprod A T k n x) := by
  have hsub := Sprod_submul A T k m n x
  calc Real.log (Sprod A T k (m + n) x)
      ≤ Real.log (Sprod A T k m (T^[n] x) * Sprod A T k n x) :=
        Real.log_le_log (hpos (m + n) x) hsub
    _ = Real.log (Sprod A T k m (T^[n] x)) + Real.log (Sprod A T k n x) :=
        Real.log_mul (ne_of_gt (hpos m (T^[n] x))) (ne_of_gt (hpos n x))

/-- **L1 — Kingman index convention.** `log Sprod` is a subadditive cocycle in Kingman's sense
`g(m+n,x) ≤ g(m,x) + g(n,T^[m]x)`, obtained from the symmetric cocycle split. -/
theorem isSubadditiveCocycle_logSprod {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ) (k : ℕ)
    (hpos : ∀ (j : ℕ) (y : X), 0 < Sprod A T k j y) :
    IsSubadditiveCocycle T (fun n x => Real.log (Sprod A T k n x)) := by
  refine ⟨fun m n x => ?_⟩
  -- Use the symmetric split `cocycle (m+n) x = cocycle n (T^[m] x) * cocycle m x`.
  have hcoc : cocycle A T (m + n) x = cocycle A T n (T^[m] x) * cocycle A T m x := by
    rw [show m + n = n + m by ring, cocycle_add]
  have hsub : Sprod A T k (m + n) x ≤ Sprod A T k n (T^[m] x) * Sprod A T k m x := by
    unfold Sprod; rw [hcoc, toEuclideanLin_mul]
    exact ExteriorNorm.prod_singularValues_comp_le k (Matrix.toEuclideanLin (cocycle A T m x))
      (Matrix.toEuclideanLin (cocycle A T n (T^[m] x)))
  calc Real.log (Sprod A T k (m + n) x)
      ≤ Real.log (Sprod A T k n (T^[m] x) * Sprod A T k m x) :=
        Real.log_le_log (hpos (m + n) x) hsub
    _ = Real.log (Sprod A T k m x) + Real.log (Sprod A T k n (T^[m] x)) := by
        rw [Real.log_mul (ne_of_gt (hpos n (T^[m] x))) (ne_of_gt (hpos m x))]; ring

/-! ## Infra M-1 (matrix form) and singular-value sandwich bounds -/

/-- **Infra M-1 (matrix form).** Each singular value of `toEuclideanLin M` is at most the L2
operator norm `‖M‖`: `σᵢ(toEuclideanLin M) ≤ ‖M‖`. -/
theorem sigma_le_opNorm (M : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) :
    (Matrix.toEuclideanLin M).singularValues i ≤ ‖M‖ :=
  (Matrix.toEuclideanLin M).singularValues_le_opNorm i

/-- A lower bound on every singular value of an invertible matrix: `(‖M⁻¹‖)⁻¹ ≤ σᵢ`, for
`i < d`. (`uᵢ = M⁻¹(M uᵢ)`, so `1 = ‖uᵢ‖ ≤ ‖M⁻¹‖ · ‖M uᵢ‖ = ‖M⁻¹‖ · σᵢ`.) -/
theorem inv_opNorm_inv_le_sigma {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.det ≠ 0) {i : ℕ}
    (hi : i < d) : (‖M⁻¹‖)⁻¹ ≤ (Matrix.toEuclideanLin M).singularValues i := by
  set f := Matrix.toEuclideanLin M with hf
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set u := f.isSymmetric_adjoint_comp_self.eigenvectorBasis hfin with hu
  -- `σᵢ = ‖f uᵢ‖`.
  have hσ : f.singularValues i = ‖f (u ⟨i, hi⟩)‖ :=
    (f.norm_apply_eigenvectorBasis_eq_singularValues hfin ⟨i, hi⟩).symm
  -- `M⁻¹ * M = 1`, so `toEuclideanLin M⁻¹ (f uᵢ) = uᵢ`.
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hM)
  have hround : Matrix.toEuclideanLin M⁻¹ (f (u ⟨i, hi⟩)) = u ⟨i, hi⟩ := by
    rw [hf, ← LinearMap.comp_apply, ← toEuclideanLin_mul, hinv]
    simp
  -- `‖uᵢ‖ ≤ ‖M⁻¹‖ · ‖f uᵢ‖`.
  have hbound : ‖u ⟨i, hi⟩‖ ≤ ‖M⁻¹‖ * ‖f (u ⟨i, hi⟩)‖ := by
    have hle := (Matrix.toEuclideanLin M⁻¹).singularValues_le_opNorm 0
    have hople : ‖(Matrix.toEuclideanLin M⁻¹) (f (u ⟨i, hi⟩))‖
        ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M⁻¹)‖ * ‖f (u ⟨i, hi⟩)‖ := by
      have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M⁻¹)).le_opNorm
        (f (u ⟨i, hi⟩))
      rwa [LinearMap.coe_toContinuousLinearMap'] at this
    rw [hround] at hople
    have hnorm : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M⁻¹)‖ = ‖M⁻¹‖ := rfl
    rw [hnorm] at hople
    exact hople
  have hu1 : ‖u ⟨i, hi⟩‖ = 1 := u.orthonormal.1 _
  rw [hu1] at hbound
  have hinvpos : 0 < ‖M⁻¹‖ := by
    rw [norm_pos_iff]
    intro hz
    have hdet : (M⁻¹).det ≠ 0 := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hM
    exact hdet (by rw [hz, Matrix.det_zero]; exact ⟨⟨i, hi⟩⟩)
  rw [hσ, inv_le_iff_one_le_mul₀ hinvpos]
  linarith [hbound]

/-! ## Positivity of `Sprod` (the Kingman `hpos` proviso, for `k ≤ d`) -/

/-- `toEuclideanLin M` is injective when `M` is invertible (`det M ≠ 0`). -/
theorem injective_toEuclideanLin {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.det ≠ 0) :
    Function.Injective (Matrix.toEuclideanLin M) := by
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hM)
  have hid : (Matrix.toEuclideanLin M⁻¹) ∘ₗ (Matrix.toEuclideanLin M) = LinearMap.id := by
    rw [← toEuclideanLin_mul, hinv]
    ext v i
    simp [Matrix.toEuclideanLin_apply, Matrix.one_mulVec]
  exact Function.LeftInverse.injective (g := Matrix.toEuclideanLin M⁻¹)
    (fun a => by rw [← LinearMap.comp_apply, hid, LinearMap.id_apply])

/-- Each of the top-`d` singular values of an invertible cocycle iterate is strictly positive. -/
theorem singularValues_cocycle_pos {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    (hA : ∀ x, (A x).det ≠ 0) (n : ℕ) (x : X) {i : ℕ} (hi : i < d) :
    0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i := by
  have hdet : (cocycle A T n x).det ≠ 0 := det_cocycle_ne_zero hA n x
  have hinj : Function.Injective (Matrix.toEuclideanLin (cocycle A T n x)) :=
    injective_toEuclideanLin hdet
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hpos := (Matrix.toEuclideanLin
    (cocycle A T n x)).injective_iff_forall_lt_finrank_singularValues_pos.mp hinj
  exact hpos i (by rw [hfin]; exact hi)

/-- **`hpos` for `k ≤ d`.** `Sprod A T k n x > 0` for an invertible cocycle and `k ≤ d`. -/
theorem Sprod_pos {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    (hA : ∀ x, (A x).det ≠ 0) {k : ℕ} (hk : k ≤ d) (n : ℕ) (x : X) :
    0 < Sprod A T k n x :=
  Finset.prod_pos fun i hi =>
    singularValues_cocycle_pos hA n x (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)

/-! ## L3: integrability and bounded-below of `log Sprod`

The sandwich `−k·log‖(A⁽ⁿ⁾)⁻¹‖ ≤ log Sprod ≤ k·log‖A⁽ⁿ⁾‖` (from M-1 and its inverse
companion) dominates `log Sprod` by integrable functions, reusing the Furstenberg–Kesten
integrability plumbing. -/

variable [NeZero d]

/-- **Upper Fekete bound.** `log Sprod_k ≤ k · log‖A⁽ⁿ⁾‖`. -/
theorem logSprod_le {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    (hA : ∀ x, (A x).det ≠ 0) {k : ℕ} (hk : k ≤ d) (n : ℕ) (x : X) :
    Real.log (Sprod A T k n x) ≤ (k : ℝ) * Real.log ‖cocycle A T n x‖ := by
  rw [Sprod, Real.log_prod (fun i hi =>
    ne_of_gt (singularValues_cocycle_pos hA n x (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)))]
  have hbnd : ∀ i ∈ Finset.range k,
      Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)
        ≤ Real.log ‖cocycle A T n x‖ := by
    intro i hi
    have hpos := singularValues_cocycle_pos (T := T) hA n x
      (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    exact Real.log_le_log hpos (sigma_le_opNorm _ i)
  calc ∑ i ∈ Finset.range k,
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)
      ≤ ∑ _i ∈ Finset.range k, Real.log ‖cocycle A T n x‖ := Finset.sum_le_sum hbnd
    _ = (k : ℝ) * Real.log ‖cocycle A T n x‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Lower Fekete bound.** `−k · log‖(A⁽ⁿ⁾)⁻¹‖ ≤ log Sprod_k`. -/
theorem neg_le_logSprod {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    (hA : ∀ x, (A x).det ≠ 0) {k : ℕ} (hk : k ≤ d) (n : ℕ) (x : X) :
    - ((k : ℝ) * Real.log ‖(cocycle A T n x)⁻¹‖) ≤ Real.log (Sprod A T k n x) := by
  rw [Sprod, Real.log_prod (fun i hi =>
    ne_of_gt (singularValues_cocycle_pos hA n x (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)))]
  have hdet : (cocycle A T n x).det ≠ 0 := det_cocycle_ne_zero hA n x
  have hbnd : ∀ i ∈ Finset.range k,
      - Real.log ‖(cocycle A T n x)⁻¹‖
        ≤ Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i) := by
    intro i hi
    have hik := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
    have hlb := inv_opNorm_inv_le_sigma hdet hik
    have hinvpos : 0 < ‖(cocycle A T n x)⁻¹‖ := norm_inv_cocycle_pos hA n x
    -- `-log‖M⁻¹‖ = log (‖M⁻¹‖)⁻¹ ≤ log σᵢ`.
    rw [← Real.log_inv]
    exact Real.log_le_log (by positivity) hlb
  calc - ((k : ℝ) * Real.log ‖(cocycle A T n x)⁻¹‖)
      = ∑ _i ∈ Finset.range k, (- Real.log ‖(cocycle A T n x)⁻¹‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ Finset.range k,
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i) :=
        Finset.sum_le_sum hbnd

variable {μ : Measure X} {T : X → X}

/-- Measurability of the determinant of a measurable square-matrix-valued function (entrywise a
polynomial in the measurable entries). Used to read off measurability of the compound-matrix
entries, which are minors of the cocycle iterate. -/
theorem measurable_det_comp {k : ℕ} {N : X → Matrix (Fin k) (Fin k) ℝ}
    (hN : Measurable N) : Measurable (fun x => (N x).det) := by
  have hentry : ∀ i j : Fin k, Measurable fun x => N x i j := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hN)
  simp only [Matrix.det_apply]
  refine Finset.measurable_sum _ fun σ _ => ?_
  refine Measurable.const_smul ?_ _
  exact Finset.measurable_prod _ fun i _ => hentry _ _

/-- Measurability of `x ↦ Sprod A T k n x`. By the **compound-matrix bridge**
`ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound`, the product of the top-`k` singular
values equals the L2 operator norm of the `k`-th **compound matrix** `C_k(A⁽ⁿ⁾ x)`, whose entries
are the `k × k` minors of `A⁽ⁿ⁾ x`. Each minor is the determinant of a submatrix of the
(measurable) cocycle iterate, hence measurable; the matrix-valued map is then measurable
entrywise, and the (continuous) L2 operator norm preserves measurability. No exterior-power /
linear-map continuity is needed. -/
theorem measurable_Sprod {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    (hAmeas : Measurable A) (hTmeas : Measurable T) (k n : ℕ) :
    Measurable (fun x => Sprod A T k n x) := by
  -- `Sprod = ‖compoundMatrix k (cocycle A T n x)‖`.
  have heq : (fun x => Sprod A T k n x)
      = fun x => ‖ExteriorNorm.compoundMatrix k (cocycle A T n x)‖ := by
    funext x
    rw [Sprod, ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound]
  rw [heq]
  -- The L2 operator norm is measurable on the entrywise σ-algebra; reduce to the compound matrix.
  refine measurable_l2_opNorm.comp ?_
  have hcoc : Measurable fun x => cocycle A T n x := measurable_cocycle hAmeas hTmeas n
  -- A matrix-valued map is measurable iff each entry is; each entry is a minor (a determinant).
  refine measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => ?_
  simp only [ExteriorNorm.compoundMatrix, Matrix.of_apply]
  -- The submatrix entries are measurable (entries of the measurable cocycle), so its det is too.
  refine measurable_det_comp ?_
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.submatrix_apply]
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hcoc)

/-- **L3 — integrability of `log Sprod`.** Each level `gₙ = log Sprod_k` is integrable, dominated
by the two (integrable) Furstenberg–Kesten log-norm cocycles. -/
theorem integrable_logSprod (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hTmeas : Measurable T) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) {k : ℕ} (hk : k ≤ d) (n : ℕ) :
    Integrable (fun x => Real.log (Sprod A T k n x)) μ := by
  -- The dominating bounds (FK integrability), scaled by `k`.
  have hU : Integrable (fun x => (k : ℝ) * Real.log ‖cocycle A T n x‖) μ :=
    (integrable_logNorm_cocycle hT hA hAmeas hTmeas hint hint' n).const_mul _
  have hL : Integrable (fun x => - ((k : ℝ) * Real.log ‖(cocycle A T n x)⁻¹‖)) μ :=
    ((integrable_logNorm_inv_cocycle hT hA hAmeas hTmeas hint hint' n).const_mul _).neg
  -- Measurability of `log Sprod` (from measurability of `Sprod`).
  have hmeas : AEStronglyMeasurable (fun x => Real.log (Sprod A T k n x)) μ :=
    (Real.measurable_log.comp (measurable_Sprod hAmeas hTmeas k n)).aestronglyMeasurable
  exact integrable_of_le_of_le hmeas
    (Filter.Eventually.of_forall fun x => neg_le_logSprod hA hk n x)
    (Filter.Eventually.of_forall fun x => logSprod_le hA hk n x) hL hU

/-- **L3 — bounded-below proviso (Fekete lower bound).** The normalized integrals of `log Sprod`
are bounded below by `−k · ∫ log⁺‖A⁻¹‖`, keeping the Kingman limit finite. -/
theorem bddBelow_logSprod (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hTmeas : Measurable T) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) {k : ℕ} (hk : k ≤ d) :
    BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1)) := by
  refine ⟨- ((k : ℝ) * ∫ x, Real.posLog ‖(A x)⁻¹‖ ∂μ), ?_⟩
  rintro _ ⟨n, rfl⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hpos]
  -- lower bound on the integral of `log Sprod`.
  have hlb : ∀ x, - ((k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖(A y)⁻¹‖) (n + 1) x)
      ≤ Real.log (Sprod A T k (n + 1) x) := by
    intro x
    refine le_trans ?_ (neg_le_logSprod hA hk (n + 1) x)
    have hub := logNorm_inv_cocycle_le_birkhoffSum (T := T) hA (n + 1) x
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hub, hknn]
  have hmono : - ((k : ℝ) * ∫ x, birkhoffSum T (fun y => Real.posLog ‖(A y)⁻¹‖) (n + 1) x ∂μ)
      ≤ ∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ := by
    rw [← integral_const_mul, ← integral_neg]
    exact integral_mono (((integrable_birkhoffSum hT hint' (n + 1)).const_mul _).neg)
      (integrable_logSprod hT hA hAmeas hTmeas hint hint' hk (n + 1)) hlb
  rw [integral_birkhoffSum hT hint' (n + 1), nsmul_eq_mul] at hmono
  push_cast at hmono ⊢
  nlinarith [hmono]

/-! ## L6: squared singular values are the Gram eigenvalues -/

/-- The adjoint of `toEuclideanLin M` composed with `toEuclideanLin M` equals `toEuclideanLin`
of the Gram matrix `Mᵀ M` (over `ℝ`). -/
theorem adjoint_comp_self_eq_gram (M : Matrix (Fin d) (Fin d) ℝ) :
    (Matrix.toEuclideanLin M).adjoint ∘ₗ (Matrix.toEuclideanLin M)
      = Matrix.toEuclideanLin (Mᵀ * M) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    show (Mᵀ * M) = Mᴴ * M by rw [Matrix.conjTranspose_eq_transpose_of_trivial]]
  ext v i
  simp only [LinearMap.comp_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

/-- **L6 — the eigenvalue bridge.** The squared singular values of `toEuclideanLin M` are the
eigenvalues of the symmetric operator `adjoint ∘ self = toEuclideanLin (Mᵀ M)`, i.e. the
eigenvalues of the Gram matrix `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾`. This delivers the eigenvalues of the
Oseledets limit `Λ` as genuine ergodic limits (via `tendsto_GammaK`) without constructing `Λ`. -/
theorem sq_singularValues_eq_gram_eigenvalue {n : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = n) (i : Fin n) :
    (Matrix.toEuclideanLin M).singularValues i ^ 2
      = (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues hn i :=
  (Matrix.toEuclideanLin M).sq_singularValues_fin hn i

/-! ## L4: the genuine ergodic `Γ_k` limit -/

/-- **L4 — the genuine ergodic `Γ_k` limit** (spike form). Under ergodicity, with the
Furstenberg–Kesten-style integrability (`hint`) and bounded-below (`hbdd`) provisos and the
positivity proviso (`hpos`, valid for `k ≤ d` on an invertible cocycle), the normalized
`log Sprod_k` converges `μ`-a.e. to a constant `Γ_k`. -/
theorem tendsto_GammaK [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (k : ℕ)
    (hpos : ∀ (j : ℕ) (y : X), 0 < Sprod A T k j y)
    (hint : ∀ n, Integrable (fun x => Real.log (Sprod A T k n x)) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1))) :
    ∃ Γk : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Sprod A T k n x)) atTop (𝓝 Γk) :=
  tendsto_kingman_ergodic hT (g := fun n x => Real.log (Sprod A T k n x))
    (isSubadditiveCocycle_logSprod A k hpos) hint hbdd

/-- **L4 — the genuine ergodic `Γ_k` limit** (with the L3 provisos discharged). For an ergodic
measure-preserving `T`, an everywhere-invertible measurable cocycle generator with
`log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹`, and `k ≤ d`, the normalized `log Sprod_k` converges `μ`-a.e. to a
constant `Γ_k`. -/
theorem tendsto_GammaK_of_integrableLogNorm [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    {k : ℕ} (hk : k ≤ d) :
    ∃ Γk : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Sprod A T k n x)) atTop (𝓝 Γk) := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  exact tendsto_GammaK hT A k (fun j y => Sprod_pos hA hk j y)
    (fun n => integrable_logSprod hmp hA hAmeas hTmeas hint hint' hk n)
    (bddBelow_logSprod hmp hA hAmeas hTmeas hint hint' hk)

/-! ## L5: the per-singular-value exponents -/

/-- **L5 — per-`σ` exponent.** Differencing the `Γ_k` limits: if `(1/n) log Sprod_{i+1} → a` and
`(1/n) log Sprod_i → b` for `μ`-a.e. `x` and the singular values are positive (`k ≤ d`), then the
normalized log of the `i`-th singular value converges to `a − b` (the `i`-th Lyapunov exponent
`λᵢ = Γ_{i+1} − Γ_i`). -/
theorem tendsto_log_singularValue {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) {i : ℕ} (hi : i < d) {a b : ℝ} {x : X}
    (ha : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Sprod A T (i + 1) n x)) atTop (𝓝 a))
    (hb : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Sprod A T i n x)) atTop (𝓝 b)) :
    Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
      atTop (𝓝 (a - b)) := by
  -- `log Sprod_{i+1} − log Sprod_i = log σᵢ` (the telescoping factor at index `i`).
  have hsplit : ∀ n : ℕ,
      (n : ℝ)⁻¹ * Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)
        = (n : ℝ)⁻¹ * Real.log (Sprod A T (i + 1) n x)
          - (n : ℝ)⁻¹ * Real.log (Sprod A T i n x) := by
    intro n
    have hSi1 : Sprod A T (i + 1) n x
        = Sprod A T i n x
          * (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i := by
      rw [Sprod, Sprod, Finset.prod_range_succ]
    have hSi_pos : 0 < Sprod A T i n x := Sprod_pos hA (le_of_lt hi) n x
    have hσ_pos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i :=
      singularValues_cocycle_pos hA n x hi
    rw [hSi1, Real.log_mul (ne_of_gt hSi_pos) (ne_of_gt hσ_pos)]
    ring
  refine (ha.sub hb).congr (fun n => (hsplit n).symm)

/-- **L5 — antitonicity of the per-`σ` exponents.** For each fixed `n` and `x`, the normalized
logs of the singular values are antitone in the index (since the singular values themselves are
antitone). -/
theorem antitone_log_singularValue (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) :
    Antitone fun i : ℕ =>
      (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i :=
  (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_antitone

end Oseledets

end
