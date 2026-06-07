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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.UniformSpace.Cauchy

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
open scoped Matrix.Norms.L2Operator Matrix MatrixOrder RealInnerProductSpace

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

/-! ## L7a: the Gram matrix is PosSemidef / self-adjoint, and the matrix root `qpow`

The Gram matrix `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾` is positive semidefinite and self-adjoint, so the
continuous functional calculus applies to it. The candidate Oseledets limit at level `n` is the
matrix `(Qₙ)^{1/(2n)} = cfc (·^{1/(2n)}) Qₙ`, whose eigenvalues are the `1/n`-th powers of the
singular values of `A⁽ⁿ⁾`. -/

/-- **L7a.** The Gram matrix `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾` is positive semidefinite. -/
theorem gram_posSemidef (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    (gram A T n x).PosSemidef := by
  unfold gram
  have h : (cocycle A T n x)ᴴ * cocycle A T n x = (cocycle A T n x)ᵀ * cocycle A T n x := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **L7a.** The Gram matrix `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾` is self-adjoint, hence the continuous
functional calculus applies to it. -/
theorem gram_isSelfAdjoint (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    IsSelfAdjoint (gram A T n x) :=
  (gram_posSemidef A T n x).isHermitian.isSelfAdjoint

/-- **L7a.** The candidate Oseledets limit at level `n`: the matrix `1/(2n)`-th power
`(Qₙ)^{1/(2n)} = cfc (·^{1/(2n)}) Qₙ` of the Gram matrix, defined via the continuous functional
calculus on the (self-adjoint, positive semidefinite) Gram matrix `Qₙ`. Its eigenvalues are the
`1/n`-th powers of the singular values of `A⁽ⁿ⁾`, which converge to `e^{λᵢ}`
(see `eigenvalues_qpow_tendsto`). -/
def qpow (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹)) (gram A T n x)

/-- `qpow A T n x` is self-adjoint (a CFC of a real-valued function is always self-adjoint). -/
theorem qpow_isSelfAdjoint (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    IsSelfAdjoint (qpow A T n x) :=
  cfc_predicate _ _

/-! ## L7b: the eigenvalues of `qpow` converge to `e^{λᵢ}`

The eigenvalues of `qpow A T n x = (Qₙ)^{1/(2n)}` are the `1/n`-th powers of the singular values
of `A⁽ⁿ⁾`. Since `(1/n) log σᵢ → λᵢ` a.e. (`tendsto_log_singularValue`), these converge to
`e^{λᵢ}`. The CFC of a monotone function applied to a Hermitian matrix has, as its sorted
eigenvalues, that function applied to the sorted eigenvalues of the matrix; we package this as a
helper and then chain it with the singular-value layer. -/

/-- The roots of the characteristic polynomial of `cfc f A` (for Hermitian `A`) are `f` applied to
the eigenvalues of `A` (cast into `𝕜`). The matrix analogue of
`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`. -/
theorem roots_charpoly_cfc_eq {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).charpoly.roots
      = Multiset.map (RCLike.ofReal ∘ (f ∘ hA.eigenvalues)) Finset.univ.val := by
  rw [Matrix.IsHermitian.charpoly_cfc_eq hA f, Polynomial.roots_prod]
  · simp [Function.comp_def]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- For a Hermitian matrix `A` with nonnegative eigenvalues and a function `f` that is monotone on
`[0, ∞)` (hence preserves the descending order of the eigenvalues), the sorted eigenvalues
`eigenvalues₀` of `cfc f A` are `f` applied to the sorted eigenvalues of `A`. The matrix analogue
(with a monotonicity-on-the-spectrum hypothesis) of
`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`. The `MonotoneOn` form is needed because
the relevant function `t ↦ t^{1/(2n)}` is `Real.rpow`, which is monotone only on `[0, ∞)`. -/
theorem eigenvalues₀_cfc_of_monotoneOn {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*}
    [RCLike 𝕜] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Set.Ici 0)) (hpos : ∀ i, 0 ≤ hA.eigenvalues₀ i) :
    ((cfc_predicate f A : IsSelfAdjoint (cfc f A)).isHermitian).eigenvalues₀
      = f ∘ hA.eigenvalues₀ := by
  -- `f ∘ eigenvalues₀` is antitone, because `eigenvalues₀` is antitone into `[0, ∞)` and `f` is
  -- monotone there.
  have hanti : Antitone (f ∘ hA.eigenvalues₀) := by
    intro i j hij
    exact hf (hpos j) (hpos i) (Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
  -- Both sides, sorted descending, agree as lists.
  rw [← List.ofFn_inj,
    ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀]
  -- The real parts of the roots of `(cfc f A).charpoly` are `f ∘ eigenvalues₀` over `univ`.
  have hroots : (cfc f A).charpoly.roots.map RCLike.re
      = Multiset.map (f ∘ hA.eigenvalues₀) Finset.univ.val := by
    rw [roots_charpoly_cfc_eq hA f, Multiset.map_map]
    simp only [Matrix.IsHermitian.eigenvalues, Function.comp_def, RCLike.ofReal_re]
    -- Reindex `univ` by the bijection `(equivOfCardEq).symm`.
    have hmap : Multiset.map
        (fun i => f (hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)))
        Finset.univ.val
        = Multiset.map (fun j => f (hA.eigenvalues₀ j))
          (Finset.univ.map (Fintype.equivOfCardEq (Fintype.card_fin _)).symm.toEmbedding).val := by
      rw [Finset.map_val, Multiset.map_map]; rfl
    rw [hmap, Finset.map_univ_equiv]
  rw [hroots]
  -- Sorting an already-antitone tuple is the identity.
  simp only [Fin.univ_val_map, Function.comp_def, Multiset.coe_sort]
  refine List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hanti.sortedGE_ofFn

/-- The sorted eigenvalues `eigenvalues₀` of the Gram matrix `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾` are the squared
singular values of `A⁽ⁿ⁾`: `eigenvalues₀ (Qₙ) i = σᵢ(A⁽ⁿ⁾)²`. This bridges the matrix-eigenvalue
layer (`Matrix.IsHermitian.eigenvalues₀`) to the committed singular-value layer
(`sq_singularValues_eq_gram_eigenvalue`). -/
theorem gram_eigenvalues₀_eq_sq_singularValues (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) (i : Fin (Fintype.card (Fin d))) :
    (gram_posSemidef A T n x).isHermitian.eigenvalues₀ i
      = (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i ^ 2 := by
  set M := cocycle A T n x with hM
  -- `eigenvalues₀` of the Gram matrix = eigenvalues of `toEuclideanLin (gram)` (linear-map layer).
  have hsym₁ : (Matrix.toEuclideanLin (gram A T n x)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (gram_posSemidef A T n x).isHermitian
  -- The committed `adjoint ∘ self` operator equals `toEuclideanLin (gram)`.
  have hop : (Matrix.toEuclideanLin M).adjoint ∘ₗ (Matrix.toEuclideanLin M)
      = Matrix.toEuclideanLin (gram A T n x) := by
    rw [gram, ← hM]; exact adjoint_comp_self_eq_gram M
  have hsym₂ : ((Matrix.toEuclideanLin M).adjoint ∘ₗ (Matrix.toEuclideanLin M)).IsSymmetric :=
    (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = Fintype.card (Fin d) :=
    finrank_euclideanSpace
  -- The two symmetric operators are equal, hence have equal eigenvalue functions.
  have heig : hsym₂.eigenvalues hfr = hsym₁.eigenvalues hfr := by
    rw [LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff hsym₂ hfr hsym₁ hfr, hop]
  -- `eigenvalues₀` of the Gram matrix is by definition the linear-map eigenvalues.
  have hdef : (gram_posSemidef A T n x).isHermitian.eigenvalues₀ i = hsym₁.eigenvalues hfr i := by
    rfl
  rw [hdef, ← heig]
  -- The committed bridge: `σᵢ² = eigenvalues (adjoint ∘ self)`.
  exact (sq_singularValues_eq_gram_eigenvalue M hfr i).symm

/-- **L7b — the eigenvalues of `qpow` are the `1/n`-th powers of the singular values.** The sorted
eigenvalues of `qpow A T n x = (Qₙ)^{1/(2n)}` are `σᵢ(A⁽ⁿ⁾)^{1/n}`. -/
theorem eigenvalues₀_qpow_eq (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    (i : Fin (Fintype.card (Fin d))) :
    (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
      = (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i ^ ((n : ℝ)⁻¹) := by
  -- The function `t ↦ t^{1/(2n)}` is monotone on `[0, ∞)` and the Gram eigenvalues are nonneg.
  have hmono : MonotoneOn (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹)) (Set.Ici 0) :=
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by positivity)
  have hpos : ∀ j, 0 ≤ (gram_posSemidef A T n x).isHermitian.eigenvalues₀ j := by
    intro j
    rw [gram_eigenvalues₀_eq_sq_singularValues]; positivity
  -- The eigenvalues of `qpow = cfc (·^{1/(2n)}) (gram)` are `(·^{1/(2n)})` of the Gram eigenvalues.
  have hcfc := eigenvalues₀_cfc_of_monotoneOn (gram_posSemidef A T n x).isHermitian hmono hpos
  -- `qpow_isSelfAdjoint` is definitionally `cfc_predicate (·^{1/(2n)}) (gram)`.
  have hi : (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
      = (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹))
          ((gram_posSemidef A T n x).isHermitian.eigenvalues₀ i) := by
    rw [show (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
        = ((cfc_predicate (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹))
            (gram A T n x) : IsSelfAdjoint _).isHermitian).eigenvalues₀ i from rfl, hcfc]
    rfl
  rw [hi, gram_eigenvalues₀_eq_sq_singularValues]
  -- `(σᵢ²)^{1/(2n)} = σᵢ^{1/n}` via `rpow` rules (`σᵢ ≥ 0`).
  set σ := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i with hσ
  have hσnn : 0 ≤ σ := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg i
  simp only
  rw [← Real.rpow_natCast σ 2, ← Real.rpow_mul hσnn]
  congr 1
  push_cast
  field_simp

/-- **L7b — the eigenvalues of `qpow` converge to `e^{λᵢ}`.** If, at a point `x`, the normalized log
of the `i`-th singular value of `A⁽ⁿ⁾` converges to `λᵢ` (which holds `μ`-a.e. by
`tendsto_log_singularValue`), then the `i`-th sorted eigenvalue of `qpow A T n x = (Qₙ)^{1/(2n)}`
converges to `e^{λᵢ}`. This is the eigenvalue layer of the Oseledets limit: the eigenvalues of the
candidate matrix limit are the exponentials of the Lyapunov exponents. Stated per eigenvalue-index
`i` (eigenvalues may repeat across distinct exponents — that is harmless here; the
per-distinct-exponent constraint only bites for the spectral projectors in L7c). -/
theorem eigenvalues_qpow_tendsto {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    (hA : ∀ x, (A x).det ≠ 0) {x : X} (i : Fin (Fintype.card (Fin d))) {lam : ℝ}
    (hlam : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
      atTop (𝓝 lam)) :
    Tendsto (fun n : ℕ => (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i)
      atTop (𝓝 (Real.exp lam)) := by
  have hid : (i : ℕ) < d := lt_of_lt_of_eq i.isLt (Fintype.card_fin d)
  -- For each `n ≥ 1`, the eigenvalue `σᵢ^{1/n} = exp((1/n) log σᵢ)` (using `σᵢ > 0`).
  have hev : ∀ n : ℕ, 1 ≤ n →
      (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
        = Real.exp ((n : ℝ)⁻¹ *
            Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)) := by
    intro n hn
    have hσpos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i :=
      singularValues_cocycle_pos hA n x hid
    rw [eigenvalues₀_qpow_eq, Real.rpow_def_of_pos hσpos]
    ring_nf
  -- The exponent sequence converges to `lam`, so its exponential converges to `e^{lam}`.
  have hexp : Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)))
      atTop (𝓝 (Real.exp lam)) :=
    (Real.continuous_exp.tendsto lam).comp hlam
  -- The eigenvalue sequence agrees with the exponential sequence eventually (for `n ≥ 1`).
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn using (hev n hn).symm

/-! ## The L7 statement (`oseledetsLimit` existence)

The Prop that downstream tasks (L7c onward) discharge: a.e., the matrix sequence
`(Qₙ)^{1/(2n)} = qpow A T n x` converges, in the (complete, finite-dimensional) matrix metric, to
a single matrix `Λ x`. -/

/-- **L7 statement.** A.e. the `1/(2n)`-th matrix power of the Gram matrix converges (in the
finite-dimensional matrix metric) to a single matrix `Λ x`. This is the existence statement of the
Oseledets limit; it is proved jointly with its eigen-data conclusions downstream (the hard
gapped-projection-Cauchy estimate, L7c). -/
def L7_statement (μ : Measure X) (T : X → X) (A : X → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ Λ : X → Matrix (Fin d) (Fin d) ℝ,
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => qpow A T n x) atTop (𝓝 (Λ x))

/-! ## L7c.0: the band spectral projector and its basic algebra

The spectral projectors of the Oseledets matrix limit are obtained as limits of *band spectral
projectors* of the candidate matrices `qpow A T n x = (Qₙ)^{1/(2n)}`: cut the spectrum at a
continuous threshold function `χ` via the continuous functional calculus. For a `χ` that equals the
`0/1` indicator of a spectral gap on the (finite) spectrum, `cfc χ (qpow)` is the orthogonal
projector onto the top eigenvalue-block. This subsection records the projector and its self-adjoint
/ idempotent algebra; the gap hypothesis discharging idempotence is supplied downstream (L7c.4). -/

/-- **L7c.0.** The band spectral projector of `qpow A T n x` cut at a continuous threshold function
`χ`: `bandProjector A T χ n x = cfc χ (qpow A T n x)`. For a `χ` that equals the `0/1` indicator of
a spectral gap on the (finite) spectrum it is the orthogonal projector onto the top
eigenvalue-block; the projector identity is provided conditionally below. -/
def bandProjector (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (χ : ℝ → ℝ) (n : ℕ) (x : X) :
    Matrix (Fin d) (Fin d) ℝ :=
  cfc χ (qpow A T n x)

/-- **L7c.0.** The band spectral projector is self-adjoint (a CFC of a real-valued function is
always self-adjoint). -/
theorem bandProjector_isSelfAdjoint (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (χ : ℝ → ℝ)
    (n : ℕ) (x : X) : IsSelfAdjoint (bandProjector A T χ n x) :=
  cfc_predicate _ _

/-- **L7c.0.** If the cutoff `χ` is idempotent on the spectrum of `qpow` (i.e. `χ = χ²` there — true
for a `0/1` indicator separated from the spectrum by a gap), the band projector is idempotent: a
genuine orthogonal projector. Conditional; the gap hypothesis that supplies `hidem` is discharged in
L7c.4. -/
theorem bandProjector_mul_self (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) {χ : ℝ → ℝ} (n : ℕ)
    (x : X) (hχ : ContinuousOn χ (spectrum ℝ (qpow A T n x)))
    (hidem : (spectrum ℝ (qpow A T n x)).EqOn (fun t => χ t * χ t) χ) :
    bandProjector A T χ n x * bandProjector A T χ n x = bandProjector A T χ n x := by
  rw [bandProjector, ← cfc_mul χ χ _, cfc_congr hidem]

/-! ## L7c.1: the band projector is the top-block eigenprojector

For a cutoff `χ` equal on the (finite) spectrum of `qpow A T n x` to the `0/1` indicator of
`(c, ∞)`, the band projector `bandProjector A T χ n x = cfc χ (qpow…)` is a genuine orthogonal
projector (self-adjoint idempotent) whose **rank** equals the number of eigenvalues of `qpow`
strictly above `c` — i.e. the dimension of the top eigenvalue-block. The explicit Hermitian-CFC
triple-product formula `cfc χ A = U · diag(χ ∘ eigenvalues) · Uᴴ` (compiled in the probe
`scratch_l7c3bc_eigproj.lean`) makes the projector concrete; the rank is the count of nonzero
diagonal entries, and a `{0,1}`-valued `χ` selects exactly the eigenvalues above the cut. -/

/-- **L7c.1.** When `χ` equals the `0/1` indicator of `(c, ∞)` on the spectrum of `qpow`, the band
projector is idempotent (a genuine orthogonal projector). Specialization of `bandProjector_mul_self`
to the indicator cutoff, whose continuity hypothesis is discharged because the spectrum is finite
and the indicator is `0/1`-valued (hence `χ² = χ` on it). -/
theorem bandProjector_indicator_mul_self (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) {c : ℝ}
    (n : ℕ) (x : X) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
        * bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
      = bandProjector A T (Set.indicator (Set.Ioi c) 1) n x := by
  -- On the spectrum, the `0/1`-valued indicator satisfies `χ² = χ`.
  have hidem : (spectrum ℝ (qpow A T n x)).EqOn
      (fun t => Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) t * Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) t)
      (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) := by
    intro t _
    by_cases ht : t ∈ Set.Ioi c
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  -- `ContinuousOn` of any function on the (finite) spectrum holds.
  have hcont : ContinuousOn (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ))
      (spectrum ℝ (qpow A T n x)) :=
    (Matrix.finite_real_spectrum (A := qpow A T n x)).continuousOn _
  rw [bandProjector, ← cfc_mul _ _ _ hcont hcont, cfc_congr hidem]

/-- The explicit Hermitian-CFC triple product: for a Hermitian matrix `M`, `cfc χ M` equals the
unitary conjugate of the diagonal matrix of `χ` applied to the eigenvalues,
`U · diag(RCLike.ofReal ∘ χ ∘ eigenvalues) · Uᴴ`. Matrix analogue lifting the probe step
`hA.cfc χ = U · diag(ofReal ∘ χ ∘ eig) · star U`. -/
theorem cfc_eq_eigenvectorUnitary_conj {m : Type*} [Fintype m] [DecidableEq m] {𝕜 : Type*}
    [RCLike 𝕜] {M : Matrix m m 𝕜} (hM : M.IsHermitian) (χ : ℝ → ℝ) :
    cfc χ M
      = (hM.eigenvectorUnitary : Matrix m m 𝕜)
          * Matrix.diagonal (RCLike.ofReal ∘ χ ∘ hM.eigenvalues)
          * star (hM.eigenvectorUnitary : Matrix m m 𝕜) := by
  rw [hM.cfc_eq χ, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]

/-- **L7c.1 — rank of the band projector.** The rank of `bandProjector A T χ n x = cfc χ (qpow…)`
is the number of eigenvalues `i` of `qpow A T n x` with `χ (eigenvalues i) ≠ 0`. Computed from the
explicit Hermitian-CFC triple product `U · diag(χ ∘ eig) · Uᴴ`: conjugation by the (invertible)
eigenvector unitary preserves rank, and the rank of the diagonal is the count of nonzero entries. -/
theorem bandProjector_rank (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (χ : ℝ → ℝ)
    (n : ℕ) (x : X) :
    (bandProjector A T χ n x).rank
      = Fintype.card {i : Fin d //
          χ ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues i) ≠ 0} := by
  classical
  set hM := (qpow_isSelfAdjoint A T n x).isHermitian with hMdef
  set U : Matrix (Fin d) (Fin d) ℝ := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  -- The eigenvector unitary has unit determinant (both `U` and `star U`).
  have hUstar : U * star U = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hdetU : IsUnit U.det :=
    IsUnit.of_mul_eq_one (a := U.det) (star U).det
      (by rw [← Matrix.det_mul, hUstar, Matrix.det_one])
  have hdetUs : IsUnit (star U).det :=
    IsUnit.of_mul_eq_one (a := (star U).det) U.det
      (by rw [← Matrix.det_mul, Unitary.coe_star_mul_self hM.eigenvectorUnitary, Matrix.det_one])
  -- The band projector is the unitary conjugate of the diagonal of `χ ∘ eigenvalues`.
  rw [bandProjector, cfc_eq_eigenvectorUnitary_conj hM χ, ← hU]
  -- Strip the unitary factors (rank is invariant under multiplication by invertible matrices).
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetUs,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdetU, Matrix.rank_diagonal]
  -- The nonzero diagonal entries are exactly the indices with `χ (eigenvalues i) ≠ 0`.
  refine Fintype.card_congr (Equiv.subtypeEquivRight (fun i => ?_))
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, ne_eq]

/-! ## L7c.1 (frame form): the band projector is `U_top · U_topᵀ`

The Frobenius back-transport `ExteriorNorm.norm_proj_sub_le_wedge` consumes the band projector in the
shape `P = U Uᵀ` with `Uᵀ U = 1` (orthonormal columns). The `0/1` indicator cutoff selects exactly
the eigenvectors of `qpow` with eigenvalue `> c`; through the explicit Hermitian-CFC triple product
`cfc χ M = U · diag(χ ∘ eig) · Uᴴ` (`cfc_eq_eigenvectorUnitary_conj`), the band projector equals
`U_top · U_topᵀ`, where `U_top` is the column-submatrix of the eigenvector unitary selecting the
columns above the cut. The selected columns are orthonormal (`U_topᵀ U_top = 1`). -/

/-- **Diag-selection.** For a real matrix `U` and the `0/1` indicator of `(c, ∞)` precomposed with a
scalar `e : Fin d → ℝ`, conjugating the indicator diagonal by `U` selects the columns of `U` whose
`e`-value exceeds `c`: `U · diag(𝟙_{(c,∞)} ∘ e) · Uᵀ = U_S · U_Sᵀ`, where `U_S` is the
column-submatrix of `U` on `S = {i | c < e i}`. -/
theorem diag_indicator_conj_eq_submatrix (U : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (e : Fin d → ℝ) :
    U * Matrix.diagonal (fun i => Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) (e i)) * Uᵀ
      = (U.submatrix id (Subtype.val : {i // c < e i} → Fin d))
          * (U.submatrix id (Subtype.val : {i // c < e i} → Fin d))ᵀ := by
  classical
  ext a b
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [← Finset.sum_subtype (s := Finset.univ.filter (fun i => c < e i))
      (p := fun i => c < e i) (fun i => by simp) (fun i => U a i * U b i)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : c < e i
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hi), Pi.one_apply, if_pos hi, one_mul]
  · rw [Set.indicator_of_notMem (by simpa using hi), if_neg hi, zero_mul, mul_zero]

/-- **Orthonormal columns of the selected submatrix.** If `U` has orthonormal columns
(`Uᵀ U = 1`, e.g. an eigenvector unitary), then any column-subselection of `U` still has orthonormal
columns: `U_Sᵀ U_S = 1`. (`U_S = U.submatrix id Subtype.val` over a subtype of column indices.) -/
theorem submatrix_transpose_mul_self_eq_one (U : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (e : Fin d → ℝ) (hU : Uᵀ * U = 1) :
    (U.submatrix id (Subtype.val : {i // c < e i} → Fin d))ᵀ
        * (U.submatrix id (Subtype.val : {i // c < e i} → Fin d)) = 1 := by
  classical
  ext s t
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  have hsum : ∑ a, U a (s : Fin d) * U a (t : Fin d) = (Uᵀ * U) (s : Fin d) (t : Fin d) := by
    rw [Matrix.mul_apply]; simp [Matrix.transpose_apply]
  rw [hsum, hU, Matrix.one_apply, Matrix.one_apply]
  by_cases hst : s = t
  · simp [hst]
  · rw [if_neg hst, if_neg (fun h => hst (Subtype.ext h))]

/-- **CFC indicator = `U_top · U_topᵀ`.** For a Hermitian real matrix `M` with eigenvector unitary
`U` and eigenvalues `eig`, the band projector cut by the `0/1` indicator of `(c, ∞)` is
`U_top · U_topᵀ`, where `U_top` is the column-submatrix of `U` selecting the eigenvectors with
eigenvalue `> c`. Combines `cfc_eq_eigenvectorUnitary_conj` (the triple product
`U · diag(χ ∘ eig) · Uᴴ`) with `diag_indicator_conj_eq_submatrix`. -/
theorem cfc_indicator_eq_submatrix_mul (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.IsHermitian) (c : ℝ) :
    cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) M
      = (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).submatrix id
            (Subtype.val : {i // c < hM.eigenvalues i} → Fin d)
          * ((hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).submatrix id
            (Subtype.val : {i // c < hM.eigenvalues i} → Fin d))ᵀ := by
  classical
  rw [cfc_eq_eigenvectorUnitary_conj hM (Set.indicator (Set.Ioi c) 1)]
  have hdiag : (Matrix.diagonal
        (RCLike.ofReal ∘ Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) ∘ hM.eigenvalues)
      : Matrix (Fin d) (Fin d) ℝ)
      = Matrix.diagonal (fun i => Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) (hM.eigenvalues i)) := by
    congr 1
  rw [hdiag, Matrix.star_eq_conjTranspose,
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial,
    diag_indicator_conj_eq_submatrix]

/-- **L7c.1 (frame form) — the band-projector frame extraction.** The band projector of `qpow` cut
by the `0/1` indicator of `(c, ∞)` is `U_top · U_topᵀ`, with `U_top` the column-submatrix of the
eigenvector unitary of `qpow A T n x` selecting the eigenvectors with eigenvalue `> c`, and the
selected columns are orthonormal (`U_topᵀ U_top = 1`). This is the `P = U Uᵀ` input consumed by the
Frobenius back-transport `ExteriorNorm.norm_proj_sub_le_wedge`. -/
theorem bandProjector_indicator_eq_frame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {c : ℝ} (n : ℕ) (x : X) :
    let hM := (qpow_isSelfAdjoint A T n x).isHermitian
    let Utop := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).submatrix id
      (Subtype.val : {i // c < hM.eigenvalues i} → Fin d)
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x = Utop * Utopᵀ
      ∧ Utopᵀ * Utop = 1 := by
  intro hM Utop
  refine ⟨?_, ?_⟩
  · exact cfc_indicator_eq_submatrix_mul (qpow A T n x) hM c
  · exact submatrix_transpose_mul_self_eq_one
      (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) c hM.eigenvalues
      (Unitary.coe_star_mul_self hM.eigenvectorUnitary)

/-! ## L7c.5: Cauchy packaging — summable increments give a convergent (band-projector) sequence

The hard mathematical content of L7c (the gapped-projection-Cauchy estimate, L7c.3/L7c.4) produces
the *summability* of the consecutive-norm increments of the band projectors. Once that is in hand,
convergence is pure soft analysis: matrices form a finite-dimensional, hence complete, normed space,
so a sequence with summable increments is Cauchy and converges. We package this abstractly (no
dynamics) so it is upstreamable and reusable for any matrix sequence — and keep a `cfc χ (H n)`
specialization that plugs directly into `bandProjector`. -/

/-- A matrix sequence whose consecutive-difference norms `‖f (n+1) - f n‖` are summable is Cauchy
(matrices over `ℝ` are a finite-dimensional, hence complete, normed space). General soft-analysis
fact, independent of the continuous functional calculus. -/
theorem cauchySeq_of_summable_norm_sub {d : ℕ} {f : ℕ → Matrix (Fin d) (Fin d) ℝ}
    (hsum : Summable (fun n => ‖f (n + 1) - f n‖)) : CauchySeq f := by
  refine cauchySeq_of_summable_dist ?_
  refine hsum.congr (fun n => ?_)
  rw [dist_eq_norm, norm_sub_rev]

/-- **L7c.5 (packaging).** A sequence of band-projector-shaped matrices `cfc χ (H n)` whose
consecutive-norm increments are summable is Cauchy. The mathematical content lives in supplying the
summability (L7c.3/L7c.4); this is the soft-analysis packaging. -/
theorem cauchySeq_cfc_of_summable {d : ℕ} (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (χ : ℝ → ℝ)
    (hsum : Summable (fun n => ‖cfc χ (H (n + 1)) - cfc χ (H n)‖)) :
    CauchySeq (fun n => cfc χ (H n)) :=
  cauchySeq_of_summable_norm_sub hsum

/-- **L7c.5 (packaging).** A band-projector-shaped sequence `cfc χ (H n)` with summable
consecutive-norm increments converges (matrices are a complete space). The limit is the candidate
Oseledets spectral projector. -/
theorem exists_tendsto_cfc_of_summable {d : ℕ} (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (χ : ℝ → ℝ)
    (hsum : Summable (fun n => ‖cfc χ (H (n + 1)) - cfc χ (H n)‖)) :
    ∃ L, Tendsto (fun n => cfc χ (H n)) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_cfc_of_summable H χ hsum)

/-! ## L7c.3a: the rank-1 Rayleigh-gap sin-Θ core

The irreducible analytic kernel of the gapped band-projector Cauchy estimate (L7c.3). It is an
elementary (Parseval + one scalar inequality) replacement for an abstract Davis–Kahan sin-Θ
theorem, which Mathlib lacks entirely. Stated abstractly for a symmetric operator on any real inner
product space (upstreamable, no dynamics): if a unit vector `v'` nearly maximizes the Rayleigh
quotient of `C`, it is close to the top eigenvector `v₀`, with the squared sine of the angle
controlled by the Rayleigh deficit divided by the spectral gap. The cocycle consumer (L7c.3) takes
`C = ⋀^k Qₙ` and `v'` the top eigenvector of `⋀^k Qₙ₊₁`, where the deficit is the one-step
distortion. -/

/-- **L7c.3a — the rank-1 Rayleigh-gap sin-Θ bound.** For a symmetric operator `C` with a top unit
eigenvector `v₀` of eigenvalue `μ₀`, whose `v₀`-orthogonal complement has Rayleigh quotient bounded
above by a strictly smaller `μ₁`, any unit vector `v'` whose Rayleigh quotient is within `ε` of `μ₀`
makes a small angle with `v₀`: the squared sine `‖v' - ⟪v', v₀⟫ v₀‖²` is at most `ε / (μ₀ - μ₁)`. -/
theorem sin_sq_le_rayleigh_deficit_div_gap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : E →ₗ[ℝ] E} (hC : C.IsSymmetric)
    {μ₀ μ₁ : ℝ} {v₀ : E} (hv₀ : ‖v₀‖ = 1) (hev : C v₀ = μ₀ • v₀) (hgap : μ₁ < μ₀)
    (hμ₁ : ∀ w : E, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ μ₁ * ‖w‖ ^ 2)
    {v' : E} (hv' : ‖v'‖ = 1) {ε : ℝ} (hRay : μ₀ - ε ≤ ⟪C v', v'⟫_ℝ) :
    ‖v' - (⟪v', v₀⟫_ℝ) • v₀‖ ^ 2 ≤ ε / (μ₀ - μ₁) := by
  set p : ℝ := ⟪v', v₀⟫_ℝ with hp
  set w : E := v' - p • v₀ with hw
  have hv₀v₀ : ⟪v₀, v₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  have hwv₀ : ⟪w, v₀⟫_ℝ = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, hv₀v₀, hp]; ring
  have hv₀w : ⟪v₀, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact hwv₀
  have hdecomp : v' = p • v₀ + w := by rw [hw]; abel
  -- Pythagoras: `1 = p² + ‖w‖²`.
  have hpv : ‖p • v₀‖ ^ 2 = p ^ 2 := by
    rw [norm_smul, hv₀, mul_one, Real.norm_eq_abs, sq_abs]
  have hpyth : (1 : ℝ) = p ^ 2 + ‖w‖ ^ 2 := by
    have h2 : ‖v'‖ ^ 2 = ‖p • v₀‖ ^ 2 + 2 * ⟪p • v₀, w⟫_ℝ + ‖w‖ ^ 2 := by
      rw [hdecomp]; exact norm_add_sq_real _ _
    rw [hv', hpv, real_inner_smul_left, hv₀w] at h2
    nlinarith [h2]
  -- Rayleigh decomposition: `⟪C v', v'⟫ = μ₀ p² + ⟪C w, w⟫`.
  have hCwv₀ : ⟪C w, v₀⟫_ℝ = 0 := by
    simp [hC w v₀, hev, real_inner_smul_right, hwv₀]
  have hray : ⟪C v', v'⟫_ℝ = μ₀ * p ^ 2 + ⟪C w, w⟫_ℝ := by
    have hCv' : C v' = (p * μ₀) • v₀ + C w := by
      rw [hdecomp, map_add, map_smul, hev, smul_smul]
    rw [hCv', hdecomp]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hv₀v₀, hv₀w, hCwv₀, mul_zero, add_zero, mul_one]
    ring
  have hb : ⟪C w, w⟫_ℝ ≤ μ₁ * ‖w‖ ^ 2 := hμ₁ w hwv₀
  -- the algebraic kernel: `c + s = 1`, `μ₀ - ε ≤ μ₀ c + b`, `b ≤ μ₁ s` force `s ≤ ε/(μ₀-μ₁)`.
  set s : ℝ := ‖w‖ ^ 2 with hs
  have hgap' : 0 < μ₀ - μ₁ := by linarith
  rw [le_div_iff₀ hgap']
  have hp2 : p ^ 2 = 1 - s := by rw [hs] at hpyth ⊢; linarith
  rw [hray, hp2] at hRay
  nlinarith [hRay, hb]

/-! ## L7c.2: the tempered one-step factor

The relative-gap projector-increment bound (L7c.3) carries a one-step distortion factor
`‖A(Tⁿx)‖·‖A(Tⁿx)⁻¹‖`. For the increments to be summable a.e. (L7c.4) this factor must be
*tempered*: its normalized logarithm vanishes a.e. This is the orbital-tail consequence of
Birkhoff's theorem (`ae_tendsto_orbit_div_atTop_zero`: `n⁻¹·g(Tⁿx) → 0` a.e. for integrable `g`)
applied to the integrable signed log-norms `log‖A·‖` and `log‖A·⁻¹‖` (`integrable_logNorm_cocycle`
at `n = 1`, where `cocycle A T 1 = A`). -/

/-- **L7c.2 — the tempered one-step factor.** The normalized log-norm of the one-step generator
along the orbit vanishes a.e.: `(1/n)·log‖A(Tⁿx)‖ → 0`. -/
theorem tendsto_logNorm_orbit_div_atTop_zero {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ] (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖A (T^[n] x)‖) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_orbit_div_atTop_zero hT
    (integrable_logNorm_cocycle hT hA hAmeas hTmeas hint hint' 1)] with x hx
  simpa using hx

/-- **L7c.2 — the tempered one-step factor (inverse).** The normalized log-norm of the inverse of
the one-step generator along the orbit vanishes a.e.: `(1/n)·log‖A(Tⁿx)⁻¹‖ → 0`. -/
theorem tendsto_logNorm_inv_orbit_div_atTop_zero {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ] (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖(A (T^[n] x))⁻¹‖) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_orbit_div_atTop_zero hT
    (integrable_logNorm_inv_cocycle hT hA hAmeas hTmeas hint hint' 1)] with x hx
  simpa using hx

/-! ## L7c.3a (corrected core): refined Davis–Kahan off-diagonal sin-Θ

The Rayleigh-DEFICIT bound `sin_sq_le_rayleigh_deficit_div_gap` is *true* but the WRONG tool for the
gapped band-projector summability: feeding it the only provable deficit `ε ≤ (1−1/κ²)μ₀` yields
`sin²θ ≤ (1−1/κ²)/(1−r²)`, which is NOT summable along the orbit (the one-step `κ` is tempered with
positive mean, so `1−1/κ²` does not decay), and the route is structurally circular (`ε ≈ μ₀ sin²θ`).
The summable estimate needs the refined Davis–Kahan sin-Θ in **off-diagonal/residual form**: the
numerator is the off-diagonal block `C v₀ − ⟪C v₀, v₀⟫ v₀`, which (for the cocycle compound) carries
the extra `σₖ/σₖ₋₁` factor the deficit route loses. See `oseledets-l7c-route.md` §J. -/

/-- **L7c.3a (corrected core) — refined off-diagonal rank-1 sin-Θ.** For a perturbed operator `C`
with top unit eigenvector `vt` (eigenvalue `μ₀`), an unperturbed top eigenline `v₀`, and a Rayleigh
ceiling `ν < μ₀` of `C` on `v₀^⊥`, the sine of the angle between `vt` and `v₀` is bounded by the
*off-diagonal residual* `‖C v₀ − ⟪C v₀, v₀⟫ v₀‖` over the gap `μ₀ − ν`. Elementary (Rayleigh +
Cauchy–Schwarz + `|⟪vt,v₀⟫| ≤ 1`); no symmetry, no functional calculus. This replaces the
deficit-form `sin_sq_le_rayleigh_deficit_div_gap` as the load-bearing sin-Θ core. -/
theorem offdiag_sin_le_residual_div_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : E →ₗ[ℝ] E} {μ₀ ν : ℝ} {v₀ vt : E} (hv₀ : ‖v₀‖ = 1) (hvtnorm : ‖vt‖ = 1)
    (hev : C vt = μ₀ • vt) (hgap : ν < μ₀)
    (hν : ∀ w : E, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ ν * ‖w‖ ^ 2) :
    ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ ≤ ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν) := by
  set p : ℝ := ⟪vt, v₀⟫_ℝ with hp
  set w : E := vt - p • v₀ with hw
  set res : E := C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀ with hres
  have hv₀v₀ : ⟪v₀, v₀⟫_ℝ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  have hwv₀ : ⟪w, v₀⟫_ℝ = (0 : ℝ) := by
    rw [hw, inner_sub_left, real_inner_smul_left, hv₀v₀, hp]; ring
  have hv₀w : ⟪v₀, w⟫_ℝ = (0 : ℝ) := by rw [real_inner_comm]; exact hwv₀
  have hdecomp : vt = p • v₀ + w := by rw [hw]; abel
  have hresw : ⟪res, w⟫_ℝ = ⟪C v₀, w⟫_ℝ := by
    rw [hres, inner_sub_left, real_inner_smul_left, hv₀w, mul_zero, sub_zero]
  have hvtw : ⟪vt, w⟫_ℝ = ‖w‖ ^ 2 := by
    rw [hdecomp, inner_add_left, real_inner_smul_left, hv₀w, mul_zero,
      zero_add, real_inner_self_eq_norm_sq]
  have hCvtw : ⟪C vt, w⟫_ℝ = μ₀ * ‖w‖ ^ 2 := by rw [hev, real_inner_smul_left, hvtw]
  have hexpand : ⟪C vt, w⟫_ℝ = p * ⟪C v₀, w⟫_ℝ + ⟪C w, w⟫_ℝ := by
    rw [hdecomp, map_add, map_smul, inner_add_left, real_inner_smul_left]
  have hpres : p * ⟪res, w⟫_ℝ = μ₀ * ‖w‖ ^ 2 - ⟪C w, w⟫_ℝ := by
    rw [hresw]; have h := hCvtw.symm.trans hexpand; linarith [h]
  have hCww : ⟪C w, w⟫_ℝ ≤ ν * ‖w‖ ^ 2 := hν w hwv₀
  have hpabs : |p| ≤ 1 := by
    have hcs := abs_real_inner_le_norm vt v₀
    rw [hv₀, hvtnorm, mul_one] at hcs
    exact hcs
  have hCS : ⟪res, w⟫_ℝ ≤ ‖res‖ * ‖w‖ := real_inner_le_norm res w
  have hCS' : -(‖res‖ * ‖w‖) ≤ ⟪res, w⟫_ℝ := by
    have := real_inner_le_norm (-res) w
    rw [inner_neg_left, norm_neg] at this; linarith
  have hp_res : p * ⟪res, w⟫_ℝ ≤ ‖res‖ * ‖w‖ := by
    rcases le_or_gt 0 (⟪res, w⟫_ℝ) with hge | hlt
    · calc p * ⟪res, w⟫_ℝ ≤ |p| * ⟪res, w⟫_ℝ := by
            apply mul_le_mul_of_nonneg_right (le_abs_self p) hge
        _ ≤ 1 * ⟪res, w⟫_ℝ := by apply mul_le_mul_of_nonneg_right hpabs hge
        _ = ⟪res, w⟫_ℝ := one_mul _
        _ ≤ ‖res‖ * ‖w‖ := hCS
    · calc p * ⟪res, w⟫_ℝ ≤ |p| * |⟪res, w⟫_ℝ| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ 1 * |⟪res, w⟫_ℝ| := by apply mul_le_mul_of_nonneg_right hpabs (abs_nonneg _)
        _ = |⟪res, w⟫_ℝ| := one_mul _
        _ ≤ ‖res‖ * ‖w‖ := by rw [abs_le]; exact ⟨hCS', hCS⟩
  have hkey : (μ₀ - ν) * ‖w‖ ^ 2 ≤ ‖res‖ * ‖w‖ := by
    calc (μ₀ - ν) * ‖w‖ ^ 2 ≤ μ₀ * ‖w‖ ^ 2 - ⟪C w, w⟫_ℝ := by nlinarith [hCww]
      _ = p * ⟪res, w⟫_ℝ := hpres.symm
      _ ≤ ‖res‖ * ‖w‖ := hp_res
  have hgap' : 0 < μ₀ - ν := by linarith
  rcases eq_or_lt_of_le (norm_nonneg w) with hw0 | hwpos
  · rw [hw, ← hw0]; positivity
  · rw [hw] at hwpos ⊢
    rw [le_div_iff₀ hgap']
    have h2 : (μ₀ - ν) * ‖vt - p • v₀‖ * ‖vt - p • v₀‖ ≤ ‖res‖ * ‖vt - p • v₀‖ := by
      have : (μ₀ - ν) * ‖vt - p • v₀‖ ^ 2 = (μ₀ - ν) * ‖vt - p • v₀‖ * ‖vt - p • v₀‖ := by ring
      rw [hw] at hkey; linarith [hkey, this]
    have hcancel := le_of_mul_le_mul_right h2 hwpos
    linarith [hcancel]

/-! ## L7c.4 (engine): summability by the root test

The corrected per-step bound has the shape `‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·κ(⋀ᵏB)²·rₙ` with
`rₙ = σₖ(Mₙ)/σₖ₋₁(Mₙ)` geometric (`(1/n)log rₙ → λₖ−λₖ₋₁ < 0`) and `κ(⋀ᵏB)²` subexponential
(`(1/n)log → 0`). Their product is summable by the root test. These are the scalar engines. -/

/-- **L7c.4 — geometric tail ⟹ summable.** A nonnegative sequence eventually dominated by `ρⁿ`
(`0 ≤ ρ < 1`) is summable. -/
theorem summable_of_eventually_le_geometric (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hev : ∀ᶠ n in atTop, a n ≤ ρ ^ n) :
    Summable a := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  apply summable_of_sum_range_le (c := (∑ i ∈ Finset.range N, a i) + (1 - ρ)⁻¹)
  · intro n; exact ha n
  intro n
  have hgeo : (0:ℝ) ≤ (1 - ρ)⁻¹ := by positivity
  rcases le_or_gt n N with h | h
  · have hsub : ∑ i ∈ Finset.range n, a i ≤ ∑ i ∈ Finset.range N, a i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) (fun i _ _ => ha i)
    linarith [hsub]
  · have hsplit : ∑ i ∈ Finset.range n, a i
        = (∑ i ∈ Finset.range N, a i) + ∑ i ∈ Finset.Ico N n, a i := by
      rw [← Finset.sum_range_add_sum_Ico _ (le_of_lt h)]
    rw [hsplit]
    have htail : ∑ i ∈ Finset.Ico N n, a i ≤ (1 - ρ)⁻¹ := by
      calc ∑ i ∈ Finset.Ico N n, a i
          ≤ ∑ i ∈ Finset.Ico N n, ρ ^ i := by
            apply Finset.sum_le_sum; intro i hi
            exact hN i (Finset.mem_Ico.mp hi).1
        _ ≤ ∑' i, ρ ^ i :=
            Summable.sum_le_tsum _ (fun i _ => by positivity)
              (summable_geometric_of_lt_one hρ0 hρ1)
        _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ1
    linarith [htail]

/-- **L7c.4 — root test (log form).** For an eventually-positive `a` whose normalized log tends to a
negative limit `L`, `a` is summable. The engine that turns the geometric×subexponential per-step
projector bound into summability (take `L = λₖ − λₖ₋₁ < 0`). -/
theorem summable_of_logLimit_neg (a : ℕ → ℝ) (hnn : ∀ n, 0 ≤ a n) (hpos : ∀ᶠ n in atTop, 0 < a n)
    {L : ℝ} (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop (𝓝 L)) :
    Summable a := by
  set ρ : ℝ := Real.exp (L / 2) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hev : ∀ᶠ n in atTop, a n ≤ ρ ^ n := by
    have hlt : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * Real.log (a n) < L / 2 := by
      have := hlog.eventually (eventually_lt_nhds (show L < L/2 by linarith))
      exact this
    have hn1 : ∀ᶠ n in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    filter_upwards [hlt, hpos, hn1] with n hn hp hn1
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hloga : Real.log (a n) < (L/2) * n := by
      rw [inv_mul_eq_div, div_lt_iff₀ hnpos] at hn
      linarith [hn]
    have : a n < ρ ^ n := by
      rw [hρdef, ← Real.exp_nat_mul]
      calc a n = Real.exp (Real.log (a n)) := (Real.exp_log hp).symm
        _ < Real.exp ((L/2) * n) := by exact Real.exp_lt_exp.mpr hloga
        _ = Real.exp (↑n * (L/2)) := by rw [mul_comm]
    exact le_of_lt this
  exact summable_of_eventually_le_geometric a hnn (le_of_lt hρ0) hρ1 hev

end Oseledets

end
