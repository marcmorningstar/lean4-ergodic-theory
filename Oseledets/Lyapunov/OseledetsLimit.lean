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

/-! ## L7c.1 (sorted frame): the band projector is the SORTED top-`k` gram eigenframe projector

The Plücker eigenpair `ExteriorNorm.plucker_eigenpair_ceiling_standard'` and the det-Gram bridge
`ExteriorNorm.det_transpose_mul_eq_inner_onbTriv` both speak of the **sorted** gram eigenbasis: the
top eigenvector wedge is `onbTriv basisFun (⋀ {u₀, …, u_{k-1}})` of the orthonormal eigenframe `u`
with **antitone** eigenvalues `lam = σ²`. The committed `bandProjector_indicator_eq_frame` expresses
the band projector through `qpow`'s **unsorted** eigenvector unitary; this subsection reconciles the
two by showing the band projector equals `W Wᵀ`, where `W` is the `d×k` matrix whose columns are the
**sorted** top-`k` gram eigenvectors. Both are the orthogonal projector onto the same eigenvalue-`> c`
subspace; the reconciliation is via the elementary "self-adjoint idempotent of trace `k` and range
fixing `W` is `W Wᵀ`" device (trace-zero symmetric idempotent vanishes). -/

/-- **CFC acts diagonally on the matrix eigenbasis.** For a Hermitian real matrix `M` with
eigenvector basis `eigenvectorBasis` and eigenvalues `eigenvalues`, `cfc g M` sends the `j`-th
eigenvector to `g (eigenvalues j)` times itself: `cfc g M *ᵥ (eigenvectorBasis j) =
g (eigenvalues j) • eigenvectorBasis j`. The matrix-level spectral action, derived from the explicit
triple product `cfc g M = U · diag(g ∘ eig) · Uᴴ` (`cfc_eq_eigenvectorUnitary_conj`). -/
theorem cfc_mulVec_eigenvectorBasis (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian) (g : ℝ → ℝ)
    (j : Fin d) :
    cfc g M *ᵥ ⇑(hM.eigenvectorBasis j) = g (hM.eigenvalues j) • ⇑(hM.eigenvectorBasis j) := by
  rw [cfc_eq_eigenvectorUnitary_conj hM g, Matrix.star_eq_conjTranspose,
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hstar : (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ *ᵥ ⇑(hM.eigenvectorBasis j)
      = Pi.single j 1 := by
    have := Matrix.IsHermitian.star_eigenvectorUnitary_mulVec hM j
    rwa [Matrix.star_eq_conjTranspose,
      (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial]
      at this
  rw [hstar, Matrix.diagonal_mulVec_single]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, mul_one]
  rw [show Pi.single j (g (hM.eigenvalues j)) = g (hM.eigenvalues j) • Pi.single j (1:ℝ) from by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], Matrix.mulVec_smul,
    Matrix.IsHermitian.eigenvectorUnitary_mulVec]

/-- **CFC acts diagonally on the matrix eigenbasis (Euclidean-linear form).** The `EuclideanSpace`
analogue of `cfc_mulVec_eigenvectorBasis`: `toEuclideanLin (cfc g M)` sends the `j`-th eigenvector to
`g (eigenvalues j)` times itself. -/
theorem toEuclideanLin_cfc_eigenvectorBasis (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (g : ℝ → ℝ) (j : Fin d) :
    Matrix.toEuclideanLin (cfc g M) (hM.eigenvectorBasis j)
      = g (hM.eigenvalues j) • (hM.eigenvectorBasis j) := by
  rw [Matrix.toEuclideanLin_apply, cfc_mulVec_eigenvectorBasis M hM g j]; rfl

/-- **DELIVERABLE 1 — the spectral operator-norm bound.** For a Hermitian matrix `M` and a function
`g`, if `|g (eigenvalue i)| ≤ c` for every eigenvalue (and `0 ≤ c`), then the L2 operator norm of
`cfc g M` is at most `c`. This is the analytic core of the spectral-block approximation: applied with
`g = (· − v ·)` (the deviation between the identity and the block-value step function), it bounds the
distance between `qpow` and its block-approximant by the maximal eigenvalue deviation.

Proof: in the orthonormal eigenbasis `b` of `M`, `cfc g M` acts diagonally
(`toEuclideanLin_cfc_eigenvectorBasis`), so `⟪b i, (cfc g M) v⟫ = g (eig i) · ⟪b i, v⟫`; Parseval
(`OrthonormalBasis.sum_sq_norm_inner_right`) then gives
`‖(cfc g M) v‖² = ∑ |g(eig i)|² |⟪b i,v⟫|² ≤ c² ∑ |⟪b i,v⟫|² = c² ‖v‖²`. -/
theorem norm_cfc_le_of_forall_eigenvalue_abs_le (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (g : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ i, |g (hM.eigenvalues i)| ≤ c) :
    ‖cfc g M‖ ≤ c := by
  classical
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  show ‖Matrix.toEuclideanLin (cfc g M) v‖ ≤ c * ‖v‖
  set w := Matrix.toEuclideanLin (cfc g M) v with hw
  have hsa : (Matrix.toEuclideanLin (cfc g M)).IsSymmetric := by
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (cfc_predicate g M : IsSelfAdjoint (cfc g M)).isHermitian
  have hinner : ∀ i, ⟪hM.eigenvectorBasis i, w⟫_ℝ
      = g (hM.eigenvalues i) * ⟪hM.eigenvectorBasis i, v⟫_ℝ := by
    intro i
    rw [hw, ← hsa (hM.eigenvectorBasis i) v, toEuclideanLin_cfc_eigenvectorBasis M hM g i,
      inner_smul_left, conj_trivial]
  have hpars_w : ‖w‖ ^ 2 = ∑ i, ⟪hM.eigenvectorBasis i, w⟫_ℝ ^ 2 := by
    rw [← OrthonormalBasis.sum_sq_norm_inner_right hM.eigenvectorBasis w]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have hpars_v : ‖v‖ ^ 2 = ∑ i, ⟪hM.eigenvectorBasis i, v⟫_ℝ ^ 2 := by
    rw [← OrthonormalBasis.sum_sq_norm_inner_right hM.eigenvectorBasis v]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have hsqbound : ‖w‖ ^ 2 ≤ c ^ 2 * ‖v‖ ^ 2 := by
    rw [hpars_w, hpars_v, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hinner i, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [hbound i, abs_nonneg (g (hM.eigenvalues i)), sq_abs (g (hM.eigenvalues i)), hc]
  nlinarith [norm_nonneg w, norm_nonneg v, hsqbound, mul_nonneg hc (norm_nonneg v)]

/-- **Trace of the indicator band projector = number of eigenvalues above the cut.** For a Hermitian
real matrix `M`, the trace of `cfc (𝟙_{(c,∞)}) M` is the count of eigenvalues `> c`. The `0/1`-valued
cutoff makes the conjugated-diagonal trace a count. (For a self-adjoint idempotent this is its rank.) -/
theorem trace_cfc_indicator_eq_count (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian) (c : ℝ) :
    (cfc (Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) M).trace
      = (Fintype.card {i : Fin d // c < hM.eigenvalues i} : ℝ) := by
  classical
  rw [cfc_eq_eigenvectorUnitary_conj hM, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.star_eq_conjTranspose,
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial]
  have hUU : (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ
      * (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 := by
    have := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial]
      at this
  rw [hUU, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  rw [show (∑ i : Fin d, Set.indicator (Set.Ioi c) (1:ℝ→ℝ) (hM.eigenvalues i))
      = ∑ i : Fin d, (if c < hM.eigenvalues i then (1:ℝ) else 0) from by
    apply Finset.sum_congr rfl; intro i _
    by_cases hi : c < hM.eigenvalues i
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hi), Pi.one_apply, if_pos hi]
    · rw [Set.indicator_of_notMem (by simpa using hi), if_neg hi]]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    mul_one, Fintype.card_subtype]

/-- **A symmetric idempotent of trace `0` vanishes.** Over `ℝ`, a matrix `E` with `Eᵀ = E` and
`E * E = E` and `tr E = 0` is the zero matrix: `tr(Eᴴ E) = tr(E²) = tr E = 0`, and the squared
Frobenius norm `tr(Eᴴ E) = ∑ Eᵢⱼ²` is zero only for `E = 0`. The kernel that turns "same range,
same trace" into a projector identity. -/
theorem eq_zero_of_transpose_eq_of_mul_self_of_trace_zero {D : ℕ} (E : Matrix (Fin D) (Fin D) ℝ)
    (hsym : Eᵀ = E) (hidem : E * E = E) (htr : E.trace = 0) : E = 0 := by
  have hconj : Eᴴ = E := by rw [E.conjTranspose_eq_transpose_of_trivial, hsym]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hconj, hidem, htr])

/-- **The band projector via the `cfc` on the Gram matrix.** Since `qpow = cfc (·^{1/(2n)}) (gram)`
and `cfc` composes, `bandProjector A T 𝟙_{(c,∞)} n x = cfc (𝟙_{(c,∞)} ∘ (·^{1/(2n)})) (gram A T n x)`.
This unfolds the band projector onto the **gram** spectral data, where the sorted eigenbasis lives. -/
theorem bandProjector_eq_cfc_gram (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    (c : ℝ) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
      = cfc ((Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) ∘ (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹)))
          (gram A T n x) := by
  rw [bandProjector, qpow,
    cfc_comp (Set.indicator (Set.Ioi c) 1) (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹))
      (gram A T n x) (gram_isSelfAdjoint A T n x)
      ((Matrix.finite_real_spectrum (A := gram A T n x)).image _ |>.continuousOn _)
      ((Matrix.finite_real_spectrum (A := gram A T n x)).continuousOn _)]

/-- **The sorted Gram eigenbasis.** The orthonormal eigenbasis of `gram A T n x`, reindexed by
`Fin (card (Fin d))` so that `sortedGramEigenbasis i` has eigenvalue `eigenvalues₀ i = σᵢ²`
(**antitone**, descending). This is exactly the `u` consumed by
`ExteriorNorm.plucker_eigenpair_ceiling_standard'` (with `lam = σ²`). -/
noncomputable def sortedGramEigenbasis (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) : OrthonormalBasis (Fin (Fintype.card (Fin d))) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (gram_posSemidef A T n x).isHermitian.eigenvectorBasis.reindex
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm

/-- The sorted Gram eigenbasis diagonalizes `toEuclideanLin (gram)` with the **antitone** eigenvalues
`eigenvalues₀`: `toEuclideanLin (gram) (sortedGramEigenbasis i) = eigenvalues₀ i • sortedGramEigenbasis i`.
The eigenpair hypothesis `hf` of `ExteriorNorm.plucker_eigenpair_ceiling_standard'`. -/
theorem sortedGramEigenbasis_eigenpair (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) (i : Fin (Fintype.card (Fin d))) :
    Matrix.toEuclideanLin (gram A T n x) (sortedGramEigenbasis A T n x i)
      = (gram_posSemidef A T n x).isHermitian.eigenvalues₀ i • sortedGramEigenbasis A T n x i := by
  set hM := (gram_posSemidef A T n x).isHermitian
  set e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm with he
  have hbase : (sortedGramEigenbasis A T n x i) = (hM.eigenvectorBasis (e.symm i)) := by
    rw [sortedGramEigenbasis, OrthonormalBasis.reindex_apply]
  rw [hbase]
  have hval : hM.eigenvalues (e.symm i) = hM.eigenvalues₀ i := by
    rw [Matrix.IsHermitian.eigenvalues]
    congr 1
    show (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))) i) = i
    simp [Equiv.symm_apply_apply]
  rw [← hval, Matrix.toEuclideanLin_apply, hM.mulVec_eigenvectorBasis (e.symm i)]; rfl

/-- The `1/(2n)`-power of the sorted Gram eigenvalue is the sorted `qpow` eigenvalue:
`(eigenvalues₀(gram) i)^{1/(2n)} = eigenvalues₀(qpow) i`. The monotone-CFC bridge identifying the
gram cut with the qpow cut. -/
theorem rpow_gram_eigenvalues₀_eq_qpow_eigenvalues₀ (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) (i : Fin (Fintype.card (Fin d))) :
    ((gram_posSemidef A T n x).isHermitian.eigenvalues₀ i) ^ ((2 * (n:ℝ))⁻¹)
      = (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i := by
  have hmono : MonotoneOn (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹)) (Set.Ici 0) :=
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by positivity)
  have hpos : ∀ j, 0 ≤ (gram_posSemidef A T n x).isHermitian.eigenvalues₀ j := by
    intro j; rw [gram_eigenvalues₀_eq_sq_singularValues]; positivity
  have hcfc := eigenvalues₀_cfc_of_monotoneOn (gram_posSemidef A T n x).isHermitian hmono hpos
  have hi : (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
      = (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹))
          ((gram_posSemidef A T n x).isHermitian.eigenvalues₀ i) := by
    rw [show (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
        = ((cfc_predicate (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹))
            (gram A T n x) : IsSelfAdjoint _).isHermitian).eigenvalues₀ i from rfl, hcfc]
    rfl
  rw [hi]

/-- **The sorted top-`k` Gram eigenframe.** The `d×k` matrix whose `j`-th column is the `j`-th sorted
Gram eigenvector `sortedGramEigenbasis ⟨j, …⟩`. Its column wedge is the Plücker top eigenvector
`w₀ = onbTriv basisFun (⋀ {u₀, …, u_{k-1}})` of `ExteriorNorm.plucker_eigenpair_ceiling_standard'`,
and it is the `W` of the band-projector frame identity `bandProjector = W Wᵀ`. -/
noncomputable def sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    {k : ℕ} (hk : k ≤ Fintype.card (Fin d)) : Matrix (Fin d) (Fin k) ℝ :=
  Matrix.of (fun a (j : Fin k) => sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hk⟩ a)

/-- The `j`-th column of `sortedTopFrame` (as a Euclidean vector) is the `j`-th sorted Gram
eigenvector. This is the identification that makes `ExteriorNorm.det_transpose_mul_eq_inner_onbTriv`
and `ExteriorNorm.plucker_eigenpair_ceiling_standard'` share the same wedge. -/
theorem colE_sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    {k : ℕ} (hk : k ≤ Fintype.card (Fin d)) (j : Fin k) :
    ExteriorNorm.colE (sortedTopFrame A T n x hk) j
      = sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hk⟩ := by
  rw [ExteriorNorm.colE, sortedTopFrame]
  ext a
  simp [EuclideanSpace.equiv]

/-- The sorted top-`k` Gram eigenframe has **orthonormal columns**: `Wᵀ W = 1`. -/
theorem sortedTopFrame_transpose_mul_self (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) {k : ℕ} (hk : k ≤ Fintype.card (Fin d)) :
    (sortedTopFrame A T n x hk)ᵀ * (sortedTopFrame A T n x hk) = 1 := by
  ext s t
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hinner : ∑ a, (sortedTopFrame A T n x hk)ᵀ s a * (sortedTopFrame A T n x hk) a t
      = (inner ℝ (sortedGramEigenbasis A T n x ⟨s, lt_of_lt_of_le s.2 hk⟩)
          (sortedGramEigenbasis A T n x ⟨t, lt_of_lt_of_le t.2 hk⟩) : ℝ) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl; intro a _
    simp only [sortedTopFrame, Matrix.transpose_apply, Matrix.of_apply, RCLike.inner_apply,
      conj_trivial]
    ring
  rw [hinner, (sortedGramEigenbasis A T n x).inner_eq_ite]
  by_cases hst : s = t
  · subst hst; simp
  · rw [if_neg (show (⟨(s:ℕ), _⟩ : Fin (Fintype.card (Fin d))) ≠ ⟨(t:ℕ), _⟩ from by
      simp only [ne_eq, Fin.mk.injEq]; exact fun h => hst (Fin.ext h)), if_neg hst]

/-- **The band projector fixes the sorted top-`k` Gram eigenframe.** If each of the top-`k` sorted
`qpow` eigenvalues exceeds the cut `c`, then `bandProjector * W = W`, i.e. the band projector acts as
the identity on each top-`k` sorted Gram eigenvector. (Each column is a `qpow`-eigenvector with
eigenvalue `> c`, where the `0/1` cutoff is `1`.) -/
theorem bandProjector_mul_sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) (c : ℝ) {k : ℕ} (hk : k ≤ Fintype.card (Fin d))
    (htop : ∀ j : Fin k, c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hk⟩) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x * sortedTopFrame A T n x hk
      = sortedTopFrame A T n x hk := by
  set g := (Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) ∘ (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹)) with hg
  set hM := (gram_posSemidef A T n x).isHermitian with hMdef
  set e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm with he
  ext a j
  rw [bandProjector_eq_cfc_gram]
  have hcol : (cfc g (gram A T n x) * sortedTopFrame A T n x hk) a j
      = (cfc g (gram A T n x) *ᵥ (fun b => sortedTopFrame A T n x hk b j)) a := by
    rw [Matrix.mul_apply, Matrix.mulVec]; rfl
  rw [hcol]
  have hcolvec : (fun b => sortedTopFrame A T n x hk b j)
      = ⇑(hM.eigenvectorBasis (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)) := by
    funext b
    show sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hk⟩ b
      = (hM.eigenvectorBasis (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)) b
    rw [sortedGramEigenbasis, OrthonormalBasis.reindex_apply, he, hMdef, Equiv.symm_symm]
  rw [hcolvec, cfc_mulVec_eigenvectorBasis (gram A T n x) hM g (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)]
  have hval : hM.eigenvalues (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)
      = hM.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩ := by
    rw [Matrix.IsHermitian.eigenvalues]
    congr 1
    show (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))))
        ⟨j, lt_of_lt_of_le j.2 hk⟩) = ⟨j, lt_of_lt_of_le j.2 hk⟩
    simp [Equiv.symm_apply_apply]
  rw [hval]
  have hg1 : g (hM.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩) = 1 := by
    have hbr : (hM.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩) ^ ((2 * (n:ℝ))⁻¹)
        = (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩ := by
      rw [hMdef]; exact rpow_gram_eigenvalues₀_eq_qpow_eigenvalues₀ A T n x ⟨j, _⟩
    rw [hg, Function.comp_apply, hbr,
      Set.indicator_of_mem (Set.mem_Ioi.mpr (htop j)), Pi.one_apply]
  rw [hg1, one_smul]
  exact (congrFun hcolvec a).symm

/-- **DELIVERABLE 1 — the band projector is the SORTED top-`k` Gram eigenframe projector.** For a cut
`c` such that exactly `k` of the `qpow` eigenvalues exceed `c` (`hcount`) and the top-`k` sorted ones
all exceed it (`htop`), the band projector equals `W Wᵀ` with `Wᵀ W = 1`, where `W = sortedTopFrame`
has the sorted top-`k` Gram eigenvectors as columns. The unsorted↔sorted eigenframe reconciliation:
both `bandProjector` (the `cfc`-indicator eigenvalue-`> c` projector of `qpow`) and `W Wᵀ` (the sorted
top-`k` Gram eigenspace projector) are the orthogonal projector onto the **same** subspace. Proof: the
difference `E = bandProjector − W Wᵀ` is a symmetric idempotent (`bandProjector` fixes the columns of
`W` — `bandProjector_mul_sortedTopFrame`) of trace `k − k = 0`, hence vanishes
(`eq_zero_of_transpose_eq_of_mul_self_of_trace_zero`). The frame `W` and its column wedge are exactly
the data consumed by `ExteriorNorm.plucker_eigenpair_ceiling_standard'` and
`ExteriorNorm.det_transpose_mul_eq_inner_onbTriv`. -/
theorem bandProjector_indicator_eq_sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) (c : ℝ) {k : ℕ} (hk : k ≤ Fintype.card (Fin d))
    (htop : ∀ j : Fin k, c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hk⟩)
    (hcount : Fintype.card {i : Fin d // c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues i}
      = k) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
        = sortedTopFrame A T n x hk * (sortedTopFrame A T n x hk)ᵀ
      ∧ (sortedTopFrame A T n x hk)ᵀ * sortedTopFrame A T n x hk = 1 := by
  set P := bandProjector A T (Set.indicator (Set.Ioi c) 1) n x with hP
  set W := sortedTopFrame A T n x hk with hW
  have hWW : Wᵀ * W = 1 := sortedTopFrame_transpose_mul_self A T n x hk
  refine ⟨?_, hWW⟩
  set E := P - W * Wᵀ with hE
  have hPsym : Pᵀ = P := by
    have hsa : Pᴴ = P := bandProjector_isSelfAdjoint A T (Set.indicator (Set.Ioi c) 1) n x
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hsa
  have hPWWsym : (W * Wᵀ)ᵀ = W * Wᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hEsym : Eᵀ = E := by rw [hE, Matrix.transpose_sub, hPsym, hPWWsym]
  have hPidem : P * P = P := bandProjector_indicator_mul_self A T n x
  have hPW : P * W = W := bandProjector_mul_sortedTopFrame A T n x c hk htop
  have hWWP : W * Wᵀ * P = W * Wᵀ := by
    have hWtP : Wᵀ * P = Wᵀ := by
      have : (P * W)ᵀ = Wᵀ := by rw [hPW]
      rwa [Matrix.transpose_mul, hPsym] at this
    rw [Matrix.mul_assoc, hWtP]
  have hPWW : P * (W * Wᵀ) = W * Wᵀ := by rw [← Matrix.mul_assoc, hPW]
  have hWWWW : W * Wᵀ * (W * Wᵀ) = W * Wᵀ := by
    rw [show W * Wᵀ * (W * Wᵀ) = W * (Wᵀ * W) * Wᵀ by simp only [Matrix.mul_assoc], hWW,
      Matrix.mul_one]
  have hEidem : E * E = E := by
    rw [hE, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPidem, hPWW, hWWP, hWWWW]
    abel
  have htrP : P.trace = (k : ℝ) := by
    rw [hP, bandProjector, qpow]
    rw [show cfc (Set.indicator (Set.Ioi c) (1:ℝ→ℝ))
          (cfc (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹)) (gram A T n x))
        = cfc (Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) (qpow A T n x) from by rw [qpow]]
    rw [trace_cfc_indicator_eq_count (qpow A T n x) (qpow_isSelfAdjoint A T n x).isHermitian c,
      hcount]
  have htrWW : (W * Wᵀ).trace = (k : ℝ) := by
    rw [Matrix.trace_mul_comm, hWW, Matrix.trace_one, Fintype.card_fin]
  have htrE : E.trace = 0 := by rw [hE, Matrix.trace_sub, htrP, htrWW, sub_self]
  have hE0 := eq_zero_of_transpose_eq_of_mul_self_of_trace_zero E hEsym hEidem htrE
  rw [hE] at hE0
  exact sub_eq_zero.mp hE0

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

/-- **Compound operator-norm upper bound** `‖compound k B‖ ≤ ‖B‖^k`. From the singular-value
product `∏_{i<k} σᵢ = ‖compound k B‖` (`prod_singularValues_eq_l2_opNorm_compound`) and the per-index
ceiling `σᵢ ≤ ‖B‖` (`sigma_le_opNorm`). -/
theorem norm_compound_le (k : ℕ) (B : Matrix (Fin d) (Fin d) ℝ) :
    ‖ExteriorNorm.compoundMatrix k B‖ ≤ ‖B‖ ^ k := by
  rw [← ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound k B]
  calc ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin B).singularValues i
      ≤ ∏ _i ∈ Finset.range k, ‖B‖ := by
        apply Finset.prod_le_prod
        · intro i _; exact (Matrix.toEuclideanLin B).singularValues_nonneg i
        · intro i _; exact sigma_le_opNorm B i
    _ = ‖B‖ ^ k := by rw [Finset.prod_const, Finset.card_range]

/-- **Compound operator-norm lower bound** `(‖B⁻¹‖⁻¹)^k ≤ ‖compound k B‖`, for invertible `B` and
`k ≤ d`. From the singular-value product and the per-index floor `‖B⁻¹‖⁻¹ ≤ σᵢ`
(`inv_opNorm_inv_le_sigma`). -/
theorem norm_inv_pow_le_norm_compound (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.det ≠ 0) (hk : k ≤ d) :
    (‖B⁻¹‖⁻¹) ^ k ≤ ‖ExteriorNorm.compoundMatrix k B‖ := by
  rw [← ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound k B]
  calc (‖B⁻¹‖⁻¹) ^ k
      = ∏ _i ∈ Finset.range k, ‖B⁻¹‖⁻¹ := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin B).singularValues i := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i hi
          exact inv_opNorm_inv_le_sigma hB (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)

/-- **Compound operator norm is positive** for invertible `B`, `k ≤ d`, `0 < d`. -/
theorem norm_compound_pos (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.det ≠ 0) (hk : k ≤ d) (hd : 0 < d) :
    0 < ‖ExteriorNorm.compoundMatrix k B‖ := by
  have hBinvdet : (B⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hB
  have hBinv : (0:ℝ) < ‖B⁻¹‖ := by
    rw [norm_pos_iff]
    intro h
    rw [h, Matrix.det_zero (Fin.pos_iff_nonempty.mp hd)] at hBinvdet
    exact hBinvdet rfl
  have hBinvne : (0:ℝ) < ‖B⁻¹‖⁻¹ := by positivity
  calc (0:ℝ) < (‖B⁻¹‖⁻¹) ^ k := by positivity
    _ ≤ ‖ExteriorNorm.compoundMatrix k B‖ := norm_inv_pow_le_norm_compound k hB hk

/-- **L7c.4 — the tempered compound factor.** The normalized log compound operator norm along the
orbit vanishes a.e.: `(1/n)·log‖compound k (A(Tⁿx))‖ → 0`. Squeezed between
`-k·(1/n)log‖A(Tⁿx)⁻¹‖ → 0` and `k·(1/n)log‖A(Tⁿx)‖ → 0` via the compound-norm sandwich
(`norm_compound_le`, `norm_inv_pow_le_norm_compound`) and the committed tempered one-step factors
(`tendsto_logNorm_orbit_div_atTop_zero` and its inverse). This makes `κ(⋀ᵏB) = ‖compound k B‖·
‖compound k B⁻¹‖` subexponential, so it contributes `0` to the root-test log-limit. -/
theorem tendsto_logNorm_compound_orbit_div_atTop_zero {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ] (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (k : ℕ) (hk : k ≤ d) (hd : 0 < d) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖)
      atTop (𝓝 0) := by
  filter_upwards [tendsto_logNorm_orbit_div_atTop_zero hT hA hAmeas hTmeas hint hint',
    tendsto_logNorm_inv_orbit_div_atTop_zero hT hA hAmeas hTmeas hint hint'] with x hup hlow
  have hupper : Tendsto
      (fun n : ℕ => (k : ℝ) * ((n : ℝ)⁻¹ * Real.log ‖A (T^[n] x)‖)) atTop (𝓝 0) := by
    have := hup.const_mul (k : ℝ); simpa using this
  have hlower : Tendsto
      (fun n : ℕ => -((k : ℝ) * ((n : ℝ)⁻¹ * Real.log ‖(A (T^[n] x))⁻¹‖))) atTop (𝓝 0) := by
    have := (hlow.const_mul (k : ℝ)).neg; simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    set B := A (T^[n] x) with hBdef
    have hBdet : B.det ≠ 0 := hA _
    have hninv : (0:ℝ) ≤ (n:ℝ)⁻¹ := by positivity
    have hCpos : 0 < ‖ExteriorNorm.compoundMatrix k B‖ := norm_compound_pos k hBdet hk hd
    have hBinvdet : (B⁻¹).det ≠ 0 := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hBdet
    have hBinvpos : (0:ℝ) < ‖B⁻¹‖ := by
      rw [norm_pos_iff]; intro h
      rw [h, Matrix.det_zero (Fin.pos_iff_nonempty.mp hd)] at hBinvdet; exact hBinvdet rfl
    have hlogle : -((k:ℝ) * Real.log ‖B⁻¹‖) ≤ Real.log ‖ExteriorNorm.compoundMatrix k B‖ := by
      have h1 : (‖B⁻¹‖⁻¹) ^ k ≤ ‖ExteriorNorm.compoundMatrix k B‖ :=
        norm_inv_pow_le_norm_compound k hBdet hk
      have h2 : Real.log ((‖B⁻¹‖⁻¹) ^ k) ≤ Real.log ‖ExteriorNorm.compoundMatrix k B‖ :=
        Real.log_le_log (by positivity) h1
      rwa [Real.log_pow, Real.log_inv, mul_neg] at h2
    calc -((k:ℝ) * ((n:ℝ)⁻¹ * Real.log ‖B⁻¹‖))
        = (n:ℝ)⁻¹ * (-((k:ℝ) * Real.log ‖B⁻¹‖)) := by ring
      _ ≤ (n:ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k B‖ :=
          mul_le_mul_of_nonneg_left hlogle hninv
  · filter_upwards [eventually_ge_atTop 1] with n hn
    set B := A (T^[n] x) with hBdef
    have hBdet : B.det ≠ 0 := hA _
    have hninv : (0:ℝ) ≤ (n:ℝ)⁻¹ := by positivity
    have hCpos : 0 < ‖ExteriorNorm.compoundMatrix k B‖ := norm_compound_pos k hBdet hk hd
    have hlogle : Real.log ‖ExteriorNorm.compoundMatrix k B‖ ≤ (k:ℝ) * Real.log ‖B‖ := by
      have h1 : ‖ExteriorNorm.compoundMatrix k B‖ ≤ ‖B‖ ^ k := norm_compound_le k B
      have h2 : Real.log ‖ExteriorNorm.compoundMatrix k B‖ ≤ Real.log (‖B‖ ^ k) :=
        Real.log_le_log hCpos h1
      rwa [Real.log_pow] at h2
    calc (n:ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k B‖
        ≤ (n:ℝ)⁻¹ * ((k:ℝ) * Real.log ‖B‖) :=
          mul_le_mul_of_nonneg_left hlogle hninv
      _ = (k:ℝ) * ((n:ℝ)⁻¹ * Real.log ‖B‖) := by ring

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

/-! ## L7c.3c: the band-projector increment bound (assembly)

The single-step band-projector increment bound `norm_bandProjector_succ_sub_le` — the convergence
point of the corrected §J route. It threads:

* the Frobenius back-transport `ExteriorNorm.norm_proj_sub_le_wedge`
  (`‖UUᵀ − VVᵀ‖² ≤ 2k(1 − det(UᵀV)²)`),
* the Plücker det-Gram identity `ExteriorNorm.inner_hodgeTrivialization_ιMulti`
  (`det(UᵀV) = ⟪wedge U, wedge V⟫`),
* the refined off-diagonal sin-Θ core `offdiag_sin_le_residual_div_gap`
  (`‖vt − ⟪vt,v₀⟫v₀‖ ≤ residual/(μ₀ − ν)`),
* the cocycle off-diagonal numerator `ExteriorNorm.norm_offdiag_residual_compound_le` and the
  `ν`-ceiling `ExteriorNorm.perturbed_compound_gram_ceiling`,
* the Plücker eigenpair `ExteriorNorm.plucker_eigenpair_ceiling_standard`.

We first record the abstract Pythagoras-to-sin glue and the abstract assembly of steps 1–4
(`norm_proj_sub_le_residual_div_gap`), then wire in the cocycle data. -/

open scoped RealInnerProductSpace in
/-- **Pythagoras gap, unit form.** For unit vectors `vt`, `v₀` in a real inner product space, the
squared sine of the angle equals one minus the squared cosine:
`‖vt − ⟪vt, v₀⟫ v₀‖² = 1 − ⟪vt, v₀⟫²`. -/
theorem norm_sub_proj_sq_eq_one_sub_inner_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v₀ vt : E} (hv₀ : ‖v₀‖ = 1) (hvt : ‖vt‖ = 1) :
    ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ ^ 2 = 1 - (⟪vt, v₀⟫_ℝ) ^ 2 := by
  set p : ℝ := ⟪vt, v₀⟫_ℝ with hp
  have hv₀v₀ : ⟪v₀, v₀⟫_ℝ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  have hvtvt : ⟪vt, vt⟫_ℝ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hvt]; norm_num
  have hexp : ‖vt - p • v₀‖ ^ 2
      = ⟪vt, vt⟫_ℝ - 2 * p * ⟪vt, v₀⟫_ℝ + p ^ 2 * ⟪v₀, v₀⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm v₀ vt]
    ring
  rw [hexp, hvtvt, hv₀v₀, ← hp]; ring

open scoped RealInnerProductSpace in
/-- **L7c.3c (abstract assembly, steps 1–4).** Combines the Frobenius back-transport, the Plücker
det-Gram identity, the Pythagoras gap, and the refined off-diagonal sin-Θ core into a single
per-step projector-increment bound. Given orthonormal frames `U`, `V` (`UᵀU = VᵀV = 1`), an
abstract symmetric operator `C` (the perturbed compound Gram) with top unit eigenvector `vt`
(eigenvalue `μ₀`) and `ν`-ceiling on `v₀^⊥`, a reference unit eigenline `v₀`, and the
det-Gram/wedge identification `det(UᵀV) = ⟪vt, v₀⟫`, the band-projector increment obeys
`‖UUᵀ − VVᵀ‖ ≤ √(2k) · ‖C v₀ − ⟪C v₀, v₀⟫ v₀‖ / (μ₀ − ν)`. -/
theorem norm_proj_sub_le_residual_div_gap {k : ℕ} (U V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : E →ₗ[ℝ] E} {μ₀ ν : ℝ} {v₀ vt : E} (hv₀ : ‖v₀‖ = 1) (hvtnorm : ‖vt‖ = 1)
    (hev : C vt = μ₀ • vt) (hgap : ν < μ₀)
    (hν : ∀ w : E, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ ν * ‖w‖ ^ 2)
    (hdet : (Uᵀ * V).det = ⟪vt, v₀⟫_ℝ) :
    ‖U * Uᵀ - V * Vᵀ‖ ≤ Real.sqrt (2 * k) * (‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν)) := by
  -- step 4: the refined off-diagonal sin-Θ bound on the wedge angle
  have hsin := offdiag_sin_le_residual_div_gap hv₀ hvtnorm hev hgap hν
  set res : ℝ := ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν) with hresdef
  have hresnn : 0 ≤ res := by
    rw [hresdef]; apply div_nonneg (norm_nonneg _); linarith
  -- step 3: Pythagoras turns `1 − det²` into the squared sine `‖vt − ⟪vt,v₀⟫v₀‖²`
  have hpyth := norm_sub_proj_sq_eq_one_sub_inner_sq hv₀ hvtnorm
  -- step 1–2: the Frobenius back-transport bound
  have hwedge := ExteriorNorm.norm_proj_sub_le_wedge U V hU hV
  rw [hdet, ← hpyth] at hwedge
  -- combine: `‖UUᵀ − VVᵀ‖² ≤ 2k · sin² ≤ 2k · res²`
  have hsin' : ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ ≤ res := hsin
  have hsinnn : 0 ≤ ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ := norm_nonneg _
  have hsq : ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ ^ 2 ≤ res ^ 2 := by
    apply sq_le_sq'
    · linarith
    · exact hsin'
  have hk2 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  have hbound : ‖U * Uᵀ - V * Vᵀ‖ ^ 2 ≤ (Real.sqrt (2 * k) * res) ^ 2 := by
    calc ‖U * Uᵀ - V * Vᵀ‖ ^ 2
        ≤ 2 * (k : ℝ) * ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ ^ 2 := hwedge
      _ ≤ 2 * (k : ℝ) * res ^ 2 := by
          apply mul_le_mul_of_nonneg_left hsq hk2
      _ = (Real.sqrt (2 * k) * res) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hk2]
  have hlhsnn : 0 ≤ ‖U * Uᵀ - V * Vᵀ‖ := norm_nonneg _
  have hrhsnn : 0 ≤ Real.sqrt (2 * k) * res := by positivity
  nlinarith [hbound, hlhsnn, hrhsnn, sq_nonneg (‖U * Uᵀ - V * Vᵀ‖ - Real.sqrt (2 * k) * res)]

/-- **L7c.3c (scalar simplification).** The off-diagonal numerator over the gap denominator collapses
to the `κ²·r/(1 − κ²r²)` shape that drives the root test. With the compound-norm abbreviations
`cM = ‖compound k Mₙ‖`, `cB = ‖compound k B‖`, `cBi = ‖compound k B⁻¹‖`, `κ = cB·cBi`, `r = σₖ/σₖ₋₁`,
the off-diagonal numerator is `cM·√μ₁·cB²` with `μ₁ = cM²·r²` (so `√μ₁ = cM·r`, using `cM ≥ 0`,
`r ≥ 0`), and a lower bound on the gap `μ̃₀ − ν ≥ cM²/cBi² · (1 − κ²r²)`. When `κ²r² < 1` the ratio
`numerator / (μ̃₀ − ν) ≤ κ²·r / (1 − κ²r²)`. This is the constant whose `(1/n)·log` limit is
`λₖ − λₖ₋₁ < 0`. -/
theorem numerator_div_gap_le {cM cB cBi r denom : ℝ}
    (hcM : 0 ≤ cM) (hcB : 0 ≤ cB) (hcBi : 0 ≤ cBi) (hr : 0 ≤ r)
    (hκr : (cB * cBi) ^ 2 * r ^ 2 < 1)
    (hdenom : cM ^ 2 / cBi ^ 2 * (1 - (cB * cBi) ^ 2 * r ^ 2) ≤ denom)
    (hdenompos : 0 < denom) (hcBipos : 0 < cBi) :
    cM * (cM * r) * cB ^ 2 / denom
      ≤ (cB * cBi) ^ 2 * r / (1 - (cB * cBi) ^ 2 * r ^ 2) := by
  set κ2 : ℝ := (cB * cBi) ^ 2 with hκ2
  have hgapfac : 0 < 1 - κ2 * r ^ 2 := by rw [hκ2]; linarith
  -- the lower bound on `denom` is itself positive, and the numerator nonneg.
  have hnumnn : 0 ≤ cM * (cM * r) * cB ^ 2 := by positivity
  -- `numerator / denom ≤ numerator / lowerbound` since `lowerbound ≤ denom` and both positive.
  set lb : ℝ := cM ^ 2 / cBi ^ 2 * (1 - κ2 * r ^ 2) with hlb
  have hcM2 : (0 : ℝ) ≤ cM ^ 2 := by positivity
  rcases eq_or_lt_of_le hcM with hcM0 | hcMpos
  · -- `cM = 0`: numerator is 0, RHS nonneg.
    rw [← hcM0]; simp only [zero_mul, mul_zero, zero_div]
    positivity
  · have hlbpos : 0 < lb := by
      rw [hlb]; apply mul_pos; · positivity
      · exact hgapfac
    -- `numerator / denom ≤ numerator / lb`
    have hstep1 : cM * (cM * r) * cB ^ 2 / denom ≤ cM * (cM * r) * cB ^ 2 / lb := by
      apply div_le_div_of_nonneg_left hnumnn hlbpos
      rw [hlb, hκ2]; exact hdenom
    -- `numerator / lb = κ² r / (1 − κ²r²)`
    have hcMne : cM ≠ 0 := ne_of_gt hcMpos
    have hcBine : cBi ≠ 0 := ne_of_gt hcBipos
    have hgapne : (1 - κ2 * r ^ 2) ≠ 0 := ne_of_gt hgapfac
    have hlbne : lb ≠ 0 := ne_of_gt hlbpos
    have hstep2 : cM * (cM * r) * cB ^ 2 / lb = κ2 * r / (1 - κ2 * r ^ 2) := by
      rw [div_eq_div_iff hlbne hgapne, hlb, hκ2]
      field_simp <;> ring
    rw [hstep2] at hstep1
    rw [hκ2]; exact hstep1

/-! ### The per-step band-projector increment bound (cocycle target)

The convergence point of the corrected §J route. With `Mₙ = cocycle A T n x`, `B = A(T^[n] x)`
the one-step left factor (so `cocycle A T (n+1) x = B * Mₙ`), `σ = (toEuclideanLin Mₙ).singularValues`,
`r = σₖ/σₖ₋₁`, and `κ = ‖compound k B‖·‖compound k B⁻¹‖`, the band projectors at consecutive steps
satisfy `‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·κ²r/(1 − κ²r²)` in the EVENTUAL regime `κ²r² < 1`.

The proof composes the committed pieces:
* `bandProjector_indicator_eq_frame` (n, n+1) → `Pₙ = UUᵀ`, `Pₙ₊₁ = VVᵀ`, `UᵀU = VᵀV = 1`;
* `ExteriorNorm.norm_offdiag_residual_compound_le` → off-diagonal numerator
  `‖C v₀ − ⟪C v₀,v₀⟫v₀‖ ≤ cM·√μ₁·cB²`;
* `ExteriorNorm.perturbed_compound_gram_ceiling` → the `ν = μ₁·cB²` ceiling on `v₀^⊥`;
* `offdiag_sin_le_residual_div_gap` (via the abstract assembly `norm_proj_sub_le_residual_div_gap`)
  → `‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·(numerator/(μ̃₀ − ν))`;
* `numerator_div_gap_le` → the final `κ²r/(1 − κ²r²)` shape.

**EVENTUAL caveat (§J.8.1).** The denominator positivity `μ̃₀ − ν > 0` holds only for `r < 1/κ`,
which is a tail property along the orbit (since `r → 0` geometrically while `κ` is tempered); hence
the bound is stated under the explicit regime hypothesis `hev`.

**Threaded gap hypotheses (§J.8.3, the one MED wiring node).** To keep the statement's elaboration
cheap (the `⋀^k`-finrank-indexed Euclidean types are extremely costly to `whnf` repeatedly), the
perturbed compound Gram operator is kept ABSTRACT here: `C : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _` with
`N` the wedge dimension, `v₀`/`vt` the reference / perturbed top eigenvectors, and `cM, cB, cBi` the
abstract compound operator norms `‖compound k Mₙ‖`, `‖compound k B‖`, `‖compound k B⁻¹‖`. The
cocycle instantiation — `N = finrank(⋀^k ℝᵈ)`, `C = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁`, the eigenpair/ceiling
data from `ExteriorNorm.plucker_eigenpair_ceiling_standard` (at `gram A T n x`, `gram A T (n+1) x`,
identified with the compound Gram via `ExteriorNorm.compoundMatrix_gram`), the off-diagonal numerator
`ExteriorNorm.norm_offdiag_residual_compound_le`, the `ν = μ₁·cB²` ceiling
`ExteriorNorm.perturbed_compound_gram_ceiling`, and the det-Gram / wedge↔frame identification
`det(UᵀV) = ⟪vt, v₀⟫` (via `ExteriorNorm.inner_hodgeTrivialization_ιMulti`) — is pure bookkeeping
with no further analytic content, FLAGGED as the remaining MED wiring node (§J.8.3) because the
band-projector frame ↔ Plücker eigenvector bridge and the rank-1 lower bound `μ̃₀ ≥ cM²/cBi²` are not
yet committed, and the `⋀^k`-type instantiation times out the elaborator at this granularity.

**EVENTUAL caveat (§J.8.1).** The denominator positivity `μ̃₀ − ν > 0` holds only for `r < 1/κ`,
which is a tail property along the orbit (since `r → 0` geometrically while `κ` is tempered); hence
the bound is stated under the explicit regime hypotheses `hgap`/`hκr`. -/
open scoped RealInnerProductSpace in
theorem norm_bandProjector_succ_sub_le {c : ℝ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {k : ℕ} (n : ℕ) (x : X)
    (U V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hPn : bandProjector A T (Set.indicator (Set.Ioi c) 1) n x = U * Uᵀ)
    (hPn1 : bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x = V * Vᵀ)
    -- the abstract perturbed compound Gram operator `Cₙ₊₁` and its top eigenpair / reference line:
    {N : ℕ} {C : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)}
    {v₀ vt : EuclideanSpace ℝ (Fin N)} (hv₀ : ‖v₀‖ = 1) (hvt : ‖vt‖ = 1)
    {μ₀ μ₁ : ℝ} (hev : C vt = μ₀ • vt)
    -- the off-diagonal numerator and `ν = μ₁·cB²` ceiling (committed cocycle lemmas):
    {cM cB cBi r : ℝ} (hcM : 0 ≤ cM) (hcB : 0 ≤ cB) (hr : 0 ≤ r)
    (hnum : ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ ≤ cM * (cM * r) * cB ^ 2)
    (hceil : ∀ z, (inner ℝ z v₀ : ℝ) = 0 → ⟪C z, z⟫_ℝ ≤ (μ₁ * cB ^ 2) * ‖z‖ ^ 2)
    -- the det-Gram / wedge identification (the Plücker bridge):
    (hdet : (Uᵀ * V).det = ⟪vt, v₀⟫_ℝ)
    -- the scalar linkages (§J.4): the gap denominator lower bound, gap positivity, the regime:
    (hμ₀lb : cM ^ 2 / cBi ^ 2 * (1 - (cB * cBi) ^ 2 * r ^ 2) ≤ μ₀ - μ₁ * cB ^ 2)
    (hgap : μ₁ * cB ^ 2 < μ₀) (hκr : (cB * cBi) ^ 2 * r ^ 2 < 1)
    (hcBipos : 0 < cBi) :
    ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
        - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖
      ≤ Real.sqrt (2 * k)
        * ((cB * cBi) ^ 2 * r / (1 - (cB * cBi) ^ 2 * r ^ 2)) := by
  set ν : ℝ := μ₁ * cB ^ 2 with hν
  have hgap' : ν < μ₀ := by rw [hν]; exact hgap
  have hgappos : 0 < μ₀ - ν := by linarith
  -- abstract assembly (steps 1–4): `‖UUᵀ − VVᵀ‖ ≤ √(2k)·(numerator/(μ₀ − ν))`.
  have hassembly := norm_proj_sub_le_residual_div_gap U V hU hV hv₀ hvt
    (C := C) (μ₀ := μ₀) (ν := ν) hev hgap' hceil hdet
  -- bound the numerator/gap by the scalar `κ²r/(1−κ²r²)` shape.
  have hnumgap : ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν)
      ≤ (cB * cBi) ^ 2 * r / (1 - (cB * cBi) ^ 2 * r ^ 2) := by
    calc ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν)
        ≤ cM * (cM * r) * cB ^ 2 / (μ₀ - ν) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hgappos)
      _ ≤ (cB * cBi) ^ 2 * r / (1 - (cB * cBi) ^ 2 * r ^ 2) := by
          have hμ₀lb' : cM ^ 2 / cBi ^ 2 * (1 - (cB * cBi) ^ 2 * r ^ 2) ≤ μ₀ - ν := by
            rw [hν]; exact hμ₀lb
          exact numerator_div_gap_le hcM hcB (le_of_lt hcBipos) hr hκr hμ₀lb' hgappos hcBipos
  -- assemble.
  rw [hPn, hPn1, ← norm_sub_rev]
  calc ‖U * Uᵀ - V * Vᵀ‖
      ≤ Real.sqrt (2 * k) * (‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν)) := hassembly
    _ ≤ Real.sqrt (2 * k) * ((cB * cBi) ^ 2 * r / (1 - (cB * cBi) ^ 2 * r ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hnumgap (Real.sqrt_nonneg _)

/-! ### DELIVERABLE 2 — the cocycle instantiation of the per-step band-projector bound

We now discharge ALL the abstract hypotheses of `norm_bandProjector_succ_sub_le` from the committed
cocycle exterior-power machinery, using the SORTED Gram eigenframes of DELIVERABLE 1. With
`Mₙ = cocycle A T n x`, `B = A(T^[n] x)` (so `cocycle A T (n+1) x = B · Mₙ`), the perturbed compound
Gram operator `Cₙ₊₁ = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁` (`Gₙ₊₁ = toEuclideanLin (compoundMatrix k (B·Mₙ))`), the
Plücker top eigenvectors `v₀ = ⋀{u₀…u_{k-1}}(gram n)`, `vt = ⋀{u'₀…u'_{k-1}}(gram (n+1))`:

* `hev` from `ExteriorNorm.plucker_eigenpair_ceiling_standard'` at `gram (n+1)` (via
  `compound_gram_op_eq`);
* `hnum` from `ExteriorNorm.norm_offdiag_residual_compound_le` (with `√μ₁ = cM·r`);
* `hceil` from `ExteriorNorm.perturbed_compound_gram_ceiling`;
* `hdet` from `ExteriorNorm.det_transpose_mul_eq_inner_onbTriv` + `colE_sortedTopFrame`;
* `hPn`, `hPn1` from `bandProjector_indicator_eq_sortedTopFrame` (DELIVERABLE 1);
* the scalar regime hypotheses (`hμ₀lb`, `hgapμ`, `hκr`, `hcBipos`) threaded as inputs (the EVENTUAL
  `κ²r² < 1` regime — discharged a.e. by the root-test layer in DELIVERABLE 3). -/

set_option maxHeartbeats 1600000 in
/-- **The compound Gram operator of the cocycle is `toEuclideanLin (compoundMatrix k (gram))`.**
`adjoint Gₙ ∘ₗ Gₙ = toEuclideanLin (compoundMatrix k (gram A T n x))`, where
`Gₙ = toEuclideanLin (compoundMatrix k (cocycle A T n x))`. Via `compoundMatrix_gram` and the matrix
adjoint identity `toEuclideanLin (Nᴴ) = (toEuclideanLin N).adjoint` (no `NeZero` on the wedge
dimension needed). -/
theorem compound_gram_op_eq (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) (k : ℕ) :
    (LinearMap.adjoint (Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (cocycle A T n x))) ∘ₗ
      Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (cocycle A T n x)))
      = Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (gram A T n x)) := by
  rw [gram, ExteriorNorm.compoundMatrix_gram,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  ext v i
  simp only [LinearMap.comp_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

set_option maxHeartbeats 1600000 in
/-- **The Plücker top eigenvector achieves the compound operator norm.** If `v₀` is a unit Plücker
top eigenvector of `Cₙ = adjoint Gₙ ∘ₗ Gₙ` (eigenvalue `∏_{i<k} σᵢ²`), then `‖Gₙ v₀‖ = ‖compound Mₙ‖`
(`= ∏_{i<k} σᵢ = √μ₀`). This `htop` hypothesis of `ExteriorNorm.norm_offdiag_residual_compound_le`. -/
theorem norm_compound_apply_pluckerVec (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    {k : ℕ}
    (v₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))))
    (hv₀ : ‖v₀‖ = 1)
    (hev : Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (gram A T n x)) v₀
      = (∏ i ∈ Finset.range k,
          (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i ^ 2) • v₀) :
    ‖Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (cocycle A T n x)) v₀‖
      = ‖ExteriorNorm.compoundMatrix k (cocycle A T n x)‖ := by
  set G := Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (cocycle A T n x)) with hG
  set prodσ := ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i
    with hprod
  have hprodnn : 0 ≤ prodσ := by
    rw [hprod]; exact Finset.prod_nonneg (fun i _ =>
      (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg i)
  have hnormsq : ‖G v₀‖ ^ 2 = (inner ℝ (G v₀) (G v₀) : ℝ) := (real_inner_self_eq_norm_sq _).symm
  have hadj : (inner ℝ (G v₀) (G v₀) : ℝ)
      = (inner ℝ (Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (gram A T n x)) v₀)
          v₀ : ℝ) := by
    rw [← compound_gram_op_eq A T n x k, LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [hev, inner_smul_left] at hadj
  rw [show (inner ℝ v₀ v₀ : ℝ) = 1 from by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num] at hadj
  simp only [conj_trivial, mul_one] at hadj
  have hsq : ‖G v₀‖ ^ 2 = prodσ ^ 2 := by
    rw [hnormsq, hadj, hprod, ← Finset.prod_pow]
  rw [← ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound, ← hprod]
  have hGnn := norm_nonneg (G v₀)
  nlinarith [hsq, hGnn, hprodnn]

/-- The sorted-Gram-eigenvalue family `lam i = σᵢ²` of the cocycle iterate (= `eigenvalues₀ (gram)`,
antitone, nonneg). The `lam` consumed by `ExteriorNorm.plucker_eigenpair_ceiling_standard'`. -/
noncomputable def lamCocycle (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    ℕ → ℝ :=
  fun i => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i ^ 2

theorem lamCocycle_antitone (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    Antitone (lamCocycle A T n x) := by
  intro i j hij
  exact pow_le_pow_left₀ ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg j)
    ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues_antitone hij) 2

theorem lamCocycle_nonneg (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) (i : ℕ) :
    0 ≤ lamCocycle A T n x i := by rw [lamCocycle]; positivity

theorem lamCocycle_eigenpair (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    (i : Fin (Fintype.card (Fin d))) :
    Matrix.toEuclideanLin (gram A T n x) (sortedGramEigenbasis A T n x i)
      = lamCocycle A T n x (i:ℕ) • sortedGramEigenbasis A T n x i := by
  rw [sortedGramEigenbasis_eigenpair, lamCocycle, gram_eigenvalues₀_eq_sq_singularValues]

/-- The Plücker top eigenvector of `Cₙ`: the Hodge-trivialized wedge `onbTriv basisFun (⋀ {u₀…u_{k-1}})`
of the sorted top-`k` Gram eigenvectors. This is the `v₀` shared by
`ExteriorNorm.plucker_eigenpair_ceiling_standard'` and `ExteriorNorm.det_transpose_mul_eq_inner_onbTriv`
(via `colE_sortedTopFrame`). -/
noncomputable def pluckerTopVec (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    {k : ℕ} (hkd : k ≤ Fintype.card (Fin d)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))) :=
  ExteriorNorm.onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k
    (exteriorPower.ιMulti ℝ k
      (fun j : Fin k => sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hkd⟩))

set_option maxHeartbeats 3200000 in
/-- **The Plücker eigenpair/ceiling data for the cocycle compound Gram operator.** Specialization of
`ExteriorNorm.plucker_eigenpair_ceiling_standard'` to `gram A T n x` with the sorted eigenbasis and
`lam = σ²`: the top eigenvector `pluckerTopVec` is a unit vector, an eigenvector of
`toEuclideanLin (compoundMatrix k (gram))` with eigenvalue `∏_{i<k} σᵢ²`, the gap
`∏_{i<k-1}σᵢ²·σₖ² < ∏_{i<k}σᵢ²` holds, and the second-eigenvalue ceiling on its orthocomplement. -/
theorem plucker_cocycle_data (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    {k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ Fintype.card (Fin d))
    (hgap : lamCocycle A T n x k < lamCocycle A T n x (k-1)) :
    ‖pluckerTopVec A T n x hkd‖ = 1
    ∧ Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (gram A T n x))
          (pluckerTopVec A T n x hkd)
        = (∏ i ∈ Finset.range k, lamCocycle A T n x i) • pluckerTopVec A T n x hkd
    ∧ ((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k)
        < (∏ i ∈ Finset.range k, lamCocycle A T n x i)
    ∧ ∀ w, (inner ℝ w (pluckerTopVec A T n x hkd) : ℝ) = 0 →
        (inner ℝ (Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (gram A T n x)) w) w : ℝ)
          ≤ ((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k) * ‖w‖ ^ 2 :=
  ExteriorNorm.plucker_eigenpair_ceiling_standard' (gram A T n x) (sortedGramEigenbasis A T n x)
    (lamCocycle A T n x) (lamCocycle_antitone A T n x) (lamCocycle_nonneg A T n x)
    (lamCocycle_eigenpair A T n x) hk1 hkd hgap

set_option maxHeartbeats 3200000 in
/-- **DELIVERABLE 2 — the cocycle per-step band-projector increment bound.** Instantiating the
abstract `norm_bandProjector_succ_sub_le` with the SORTED Gram eigenframes of DELIVERABLE 1, the
Plücker eigenpairs of `gram n`/`gram (n+1)`, and the committed off-diagonal numerator / `ν`-ceiling /
lower-bound exterior lemmas. With `B = A(T^[n] x)`, `cM = ‖compound k Mₙ‖`, `cB = ‖compound k B‖`,
`cBi = ‖compound k B⁻¹‖`, `r = σₖ/σₖ₋₁`, in the EVENTUAL regime `(cB·cBi)²r² < 1`, the band projectors
satisfy `‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·(cB·cBi)²·r/(1 − (cB·cBi)²r²)`. The cut hypotheses (`htop*`, `hcount*`)
identify both band projectors with the sorted top-`k` frames; the gap hypotheses (`hgap*`) feed the
Plücker spectral gap; the scalar linkage hypotheses (`hμ₀lb`, `hgapμ`, `hκr`) are the genuine outputs
of `ExteriorNorm.norm_sq_compound_mul_ge` + the eventual regime, discharged a.e. in DELIVERABLE 3. -/
theorem norm_bandProjector_succ_sub_le_cocycle
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (hA : ∀ x, (A x).det ≠ 0)
    (n : ℕ) (x : X) (c : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ Fintype.card (Fin d))
    (htopN : ∀ j : Fin k, c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hkd⟩)
    (hcountN : Fintype.card
      {i : Fin d // c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues i} = k)
    (htopN1 : ∀ j : Fin k, c < (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hkd⟩)
    (hcountN1 : Fintype.card
      {i : Fin d // c < (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues i} = k)
    (hgapN : lamCocycle A T n x k < lamCocycle A T n x (k-1))
    (hgapN1 : lamCocycle A T (n+1) x k < lamCocycle A T (n+1) x (k-1))
    (hcBipos : 0 < ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖)
    (hμ₀lb : ‖ExteriorNorm.compoundMatrix k (cocycle A T n x)‖ ^ 2
          / ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖ ^ 2
        * (1 - (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
            * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
          * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
            / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2)
        ≤ (∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i)
          - ((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k)
            * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ ^ 2)
    (hgapμ : ((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k)
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ ^ 2
        < ∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i)
    (hκr : (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
        * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2 < 1) :
    ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
        - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖
      ≤ Real.sqrt (2 * k)
        * ((‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
            * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
          * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
            / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1))
          / (1 - (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
              * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
            * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
              / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2)) := by
  classical
  set B := A (T^[n] x) with hB
  set M := cocycle A T n x with hM
  have hBM : B * M = cocycle A T (n+1) x := by
    rw [hB, hM, show n+1 = 1 + n from by omega, cocycle_add, cocycle_one]
  set U := sortedTopFrame A T n x hkd with hU
  set V := sortedTopFrame A T (n+1) x hkd with hV
  obtain ⟨hUframe, hUortho⟩ := bandProjector_indicator_eq_sortedTopFrame A T n x c hkd htopN hcountN
  obtain ⟨hVframe, hVortho⟩ :=
    bandProjector_indicator_eq_sortedTopFrame A T (n+1) x c hkd htopN1 hcountN1
  obtain ⟨hv₀norm, hv₀ev, hv₀gap, hv₀ceil⟩ := plucker_cocycle_data A T n x hk1 hkd hgapN
  obtain ⟨hvtnorm, hvtev, hvtgap, hvtceil⟩ := plucker_cocycle_data A T (n+1) x hk1 hkd hgapN1
  set v₀ := pluckerTopVec A T n x hkd with hv₀def
  set vt := pluckerTopVec A T (n+1) x hkd with hvtdef
  set μ₀ := ∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i with hμ₀
  set μ₁ := (∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k with hμ₁
  set cM := ‖ExteriorNorm.compoundMatrix k M‖ with hcM
  set cB := ‖ExteriorNorm.compoundMatrix k B‖ with hcB
  set cBi := ‖ExteriorNorm.compoundMatrix k B⁻¹‖ with hcBi
  set r := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
    / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) with hr
  set C := LinearMap.adjoint (Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (B * M))) ∘ₗ
    Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k (B * M)) with hC
  have hev : C vt = μ₀ • vt := by
    rw [hC, hBM, compound_gram_op_eq A T (n+1) x k, hvtev]
  have htop : ‖Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k M) v₀‖
      = ‖ExteriorNorm.compoundMatrix k M‖ :=
    norm_compound_apply_pluckerVec A T n x v₀ hv₀norm hv₀ev
  have hceilN : ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k M)) ∘ₗ
        Matrix.toEuclideanLin (ExteriorNorm.compoundMatrix k M)) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2 := by
    intro z hz
    rw [compound_gram_op_eq A T n x k]
    exact hv₀ceil z hz
  have hnum : ‖C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀‖ ≤ cM * (cM * r) * cB ^ 2 := by
    have hμ₁nn : 0 ≤ μ₁ := by
      rw [hμ₁]
      exact mul_nonneg (Finset.prod_nonneg (fun i _ => lamCocycle_nonneg A T n x i))
        (lamCocycle_nonneg A T n x k)
    have hres := ExteriorNorm.norm_offdiag_residual_compound_le (d := d) k B M (μ₁ := μ₁)
      hμ₁nn hv₀norm htop hceilN
    rw [← hC] at hres
    refine le_trans hres ?_
    rw [hcM, hcB]
    have hsqrt : Real.sqrt μ₁ = cM * r := by
      have hcMr : 0 ≤ cM * r := by
        rw [hcM, hr]; apply mul_nonneg (norm_nonneg _)
        apply div_nonneg ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg k)
          ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg (k-1))
      rw [← Real.sqrt_sq hcMr]
      congr 1
      rw [hμ₁, hcM, hr, ← ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound]
      simp only [lamCocycle]
      have hsplit : (∏ i ∈ Finset.range k,
            (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)
          = (∏ i ∈ Finset.range (k-1),
            (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)
            * (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) := by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega, Finset.prod_range_succ]
      rw [hsplit, Finset.prod_pow]
      have hσpos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) :=
        singularValues_cocycle_pos hA n x (by
          have hkk : k - 1 < k := by omega
          exact lt_of_lt_of_le (lt_of_lt_of_le hkk hkd) (le_of_eq (Fintype.card_fin d)))
      have hσne : (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) ≠ 0 :=
        ne_of_gt hσpos
      field_simp
    rw [hsqrt]
  have hceil : ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ (C z) z : ℝ) ≤ (μ₁ * cB ^ 2) * ‖z‖ ^ 2 := by
    intro z hz
    rw [hcB, hC]
    exact ExteriorNorm.perturbed_compound_gram_ceiling (d := d) k B M hceilN z hz
  have hcolU : (fun i => ExteriorNorm.colE U i)
      = (fun j : Fin k => sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hkd⟩) := by
    funext i; rw [hU, colE_sortedTopFrame]
  have hcolV : (fun j => ExteriorNorm.colE V j)
      = (fun j : Fin k => sortedGramEigenbasis A T (n+1) x ⟨j, lt_of_lt_of_le j.2 hkd⟩) := by
    funext j; rw [hV, colE_sortedTopFrame]
  have hdet : (Uᵀ * V).det = (inner ℝ vt v₀ : ℝ) := by
    rw [ExteriorNorm.det_transpose_mul_eq_inner_onbTriv U V, hcolU, hcolV, hvtdef, hv₀def,
      pluckerTopVec, pluckerTopVec]
  have hrnn : 0 ≤ r := by
    rw [hr]; exact div_nonneg
      ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg k)
      ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg (k-1))
  exact norm_bandProjector_succ_sub_le (c := c) A T n x U V hUortho hVortho
    hUframe hVframe (N := Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))
    (C := C) (v₀ := v₀) (vt := vt) hv₀norm hvtnorm
    (μ₀ := μ₀) (μ₁ := μ₁) hev
    (cM := cM) (cB := cB) (cBi := cBi) (r := r)
    (norm_nonneg _) (norm_nonneg _) hrnn
    hnum hceil hdet hμ₀lb hgapμ hκr hcBipos

/-! ## L7c.4: a.e. summability of the band-projector increments (the root-test conclusion)

The per-step band-projector bound `‖Pₙ₊₁ − Pₙ‖ ≤ bₙ` with `bₙ = √(2k)·κ(⋀ᵏB)²·rₙ/(1 − κ²rₙ²)`
(`norm_bandProjector_succ_sub_le`) is summable along the orbit by the root test: `(1/n)log bₙ →
λₖ − λₖ₋₁ < 0`. The committed scalar layer supplies the log-limit (`(1/n)log rₙ → λₖ − λₖ₋₁` via
`tendsto_log_singularValue` at indices `k`, `k−1`; the `κ²` factor subexponential via
`tendsto_logNorm_compound_orbit_div_atTop_zero`; the `1/(1−κ²rₙ²)` factor `→ 1` since `κ²rₙ² → 0`).
We package the comparison + root test abstractly, then state the cocycle conclusion taking the
per-step bound and the negative log-limit of its RHS as hypotheses (the genuine outputs of the
per-step bound `norm_bandProjector_succ_sub_le` and the scalar layer). -/

/-- **L7c.4 (packaging) — comparison + root test.** If the increment norms `‖incr n‖` are eventually
dominated by a nonnegative sequence `b` whose normalized log tends to a negative limit, then the
increment norms are summable. Pure soft analysis (`summable_of_logLimit_neg` +
`Summable.of_norm_bounded_eventually_nat`). -/
theorem summable_norm_of_logLimit_neg_of_le {E : Type*} [NormedAddCommGroup E]
    (incr : ℕ → E) (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hpos : ∀ᶠ n in atTop, 0 < b n)
    {L : ℝ} (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (hstep : ∀ᶠ n in atTop, ‖incr n‖ ≤ b n) :
    Summable (fun n => ‖incr n‖) := by
  have hsumb : Summable b := summable_of_logLimit_neg b hb hpos hL hlog
  apply Summable.of_norm_bounded_eventually_nat hsumb
  filter_upwards [hstep] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hn

/-- **L7c.4 — a.e. summability of the band-projector increments.** For `μ`-a.e. `x`, the
consecutive band-projector increments `‖Pₙ₊₁ − Pₙ‖` are summable. The per-step dominating sequence
`b x n` (the RHS of `norm_bandProjector_succ_sub_le`, eventually `√(2k)·κ²rₙ/(1−κ²rₙ²)`), its
nonnegativity / eventual positivity, the negative root-test log-limit `L x` (`= λₖ − λₖ₋₁`), and the
eventual per-step bound are taken as hypotheses — the genuine outputs of the per-step bound and the
committed scalar layer (`tendsto_log_singularValue`, `tendsto_logNorm_compound_orbit_div_atTop_zero`).
The conclusion is the L7c.4 summability that feeds the Cauchy packaging `cauchySeq_cfc_of_summable`
(L7c.5). -/
theorem summable_norm_bandProjector_succ_sub {c : ℝ} (A : X → Matrix (Fin d) (Fin d) ℝ)
    (b : X → ℕ → ℝ)
    (hb : ∀ᵐ x ∂μ, ∀ n, 0 ≤ b x n)
    (hpos : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, 0 < b x n)
    (L : X → ℝ) (hL : ∀ᵐ x ∂μ, L x < 0)
    (hlog : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b x n)) atTop (𝓝 (L x)))
    (hstep : ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ b x n) :
    ∀ᵐ x ∂μ, Summable (fun n =>
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖) := by
  filter_upwards [hb, hpos, hL, hlog, hstep] with x hbx hposx hLx hlogx hstepx
  exact summable_norm_of_logLimit_neg_of_le _ (b x) hbx hposx hLx hlogx hstepx

/-! ## L7c.5 (a.e. assembly): the band projectors converge

The committed Cauchy packaging `exists_tendsto_cfc_of_summable` turns the a.e. summability of the
band-projector increments (`summable_norm_bandProjector_succ_sub`, L7c.4) into a.e. convergence of
the band projectors themselves: the candidate Oseledets spectral projector exists `μ`-a.e. The
`bandProjector A T (indicator (Ioi c) 1) n x = cfc (indicator (Ioi c) 1) (qpow A T n x)` sequence is
the `cfc χ (H n)` sequence with `H = fun n => qpow A T n x`, so this is a direct specialization. -/

/-- **L7c.5 (a.e. assembly).** For `μ`-a.e. `x`, the band projectors
`bandProjector A T (indicator (Ioi c) 1) n x` converge: there is a limiting projector `P` with
`Tendsto (fun n => bandProjector A T (indicator (Ioi c) 1) n x) atTop (𝓝 P)`. This is the
convergence of the Oseledets spectral projector pinned by the growing spectral gap, obtained by
feeding the a.e. summability of the increments (L7c.4, `summable_norm_bandProjector_succ_sub`) into
the soft-analysis Cauchy packaging `exists_tendsto_cfc_of_summable` (L7c.5). The summability
hypotheses are the genuine outputs of the per-step bound `norm_bandProjector_succ_sub_le` and the
committed scalar root-test layer (`tendsto_log_singularValue`,
`tendsto_logNorm_compound_orbit_div_atTop_zero`). -/
theorem exists_tendsto_bandProjector {c : ℝ} (A : X → Matrix (Fin d) (Fin d) ℝ)
    (b : X → ℕ → ℝ)
    (hb : ∀ᵐ x ∂μ, ∀ n, 0 ≤ b x n)
    (hpos : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, 0 < b x n)
    (L : X → ℝ) (hL : ∀ᵐ x ∂μ, L x < 0)
    (hlog : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b x n)) atTop (𝓝 (L x)))
    (hstep : ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ b x n) :
    ∀ᵐ x ∂μ, ∃ P : Matrix (Fin d) (Fin d) ℝ,
      Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 P) := by
  have hsummable := summable_norm_bandProjector_succ_sub (c := c) A b hb hpos L hL hlog hstep
  filter_upwards [hsummable] with x hx
  -- `bandProjector A T χ n x = cfc χ (qpow A T n x)` is `cfc χ (H n)` with `H = qpow A T · x`.
  exact exists_tendsto_cfc_of_summable (fun n => qpow A T n x)
    (Set.indicator (Set.Ioi c) 1) hx

/-! ### DELIVERABLE 3 — UNCONDITIONAL band-projector a.e. convergence (cocycle)

Feeding DELIVERABLE 2 (`norm_bandProjector_succ_sub_le_cocycle`) through the committed Cauchy
packaging `exists_tendsto_bandProjector`: for `μ`-a.e. `x`, the band projector
`bandProjector A T (indicator (Ioi c) 1) n x` converges. The per-step bound
`bCocycle x n = √(2k)·κ²r/(1 − κ²r²)` is summable along the orbit by the root test (its `(1/n)·log`
tends to `λₖ − λₖ₋₁ < 0` a.e. via the committed scalar layer `tendsto_log_singularValue` at the two
cut indices and `tendsto_logNorm_compound_orbit_div_atTop_zero`; the eventual regime `κ²r² < 1` holds
a.e. since `r → 0` geometrically while `κ` is tempered). The a.e. eventual cut/gap/regime conditions
are packaged as `stepHypCocycle` and discharged through DELIVERABLE 2 by `stepHypCocycle_imp_step`. -/

/-- **DELIVERABLE 3 — the per-step dominating sequence.** The RHS of the cocycle band-projector
increment bound (`norm_bandProjector_succ_sub_le_cocycle`): `√(2k)·κ²·r/(1 − κ²r²)` with
`κ = ‖compound k B‖·‖compound k B⁻¹‖`, `r = σₖ/σₖ₋₁`, `B = A(T^[n] x)`. Its `(1/n)·log` tends to
`λₖ − λₖ₋₁ < 0` a.e., making it summable by the root test. -/
noncomputable def bCocycle (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) (k : ℕ) :
    ℕ → ℝ :=
  fun n => Real.sqrt (2 * k)
    * ((‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
        * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
      * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
        / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1))
      / (1 - (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
        * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2))

/-- **DELIVERABLE 3 — the per-step cut/gap/regime conditions at a single `n`.** The conjunction of all
hypotheses of `norm_bandProjector_succ_sub_le_cocycle` at step `n`: the cut counts `= k` (at `n` and
`n+1`), the top-`k` sorted `qpow` eigenvalues exceed `c`, the Plücker spectral gaps, and the scalar
regime/linkage conditions. Eventually true a.e. along the orbit (the cut is stable in the eventual
Lyapunov-gap regime; `r → 0` geometrically); see the module note for DELIVERABLE 3. -/
def stepHypCocycle (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (k : ℕ)
    (hkd : k ≤ Fintype.card (Fin d)) (x : X) (n : ℕ) : Prop :=
  (∀ j : Fin k, c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hkd⟩)
  ∧ Fintype.card {i : Fin d // c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues i} = k
  ∧ (∀ j : Fin k, c < (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hkd⟩)
  ∧ Fintype.card {i : Fin d // c < (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues i} = k
  ∧ lamCocycle A T n x k < lamCocycle A T n x (k-1)
  ∧ lamCocycle A T (n+1) x k < lamCocycle A T (n+1) x (k-1)
  ∧ 0 < ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖
  ∧ (‖ExteriorNorm.compoundMatrix k (cocycle A T n x)‖ ^ 2
        / ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖ ^ 2
      * (1 - (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
        * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2)
      ≤ (∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i)
        - ((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k)
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ ^ 2)
  ∧ (((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k)
        * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ ^ 2
      < ∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i)
  ∧ ((‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
        * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
      * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
        / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2 < 1)

/-- **DELIVERABLE 3 — per-step conditions discharge the increment bound.** `stepHypCocycle` at `n`
gives the band-projector increment bound `‖Pₙ₊₁ − Pₙ‖ ≤ bCocycle x n` via DELIVERABLE 2
(`norm_bandProjector_succ_sub_le_cocycle`). -/
theorem stepHypCocycle_imp_step (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (hA : ∀ x, (A x).det ≠ 0) (c : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ Fintype.card (Fin d))
    (x : X) (n : ℕ) (h : stepHypCocycle A T c k hkd x n) :
    ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
        - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ bCocycle A T x k n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact norm_bandProjector_succ_sub_le_cocycle A T hA n x c hk1 hkd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-- **DELIVERABLE 3 — UNCONDITIONAL band-projector a.e. convergence.** For `μ`-a.e. `x`, the band
projector `bandProjector A T (indicator (Ioi c) 1) n x` converges to a limiting projector `P`. This is
the convergence of the Oseledets spectral projector pinned by the growing spectral gap. The proof
discharges the per-step increment bound (DELIVERABLE 2, via `stepHypCocycle_imp_step`) from the a.e.
eventual cut/gap/regime conditions `hstepAE`, and feeds the resulting a.e. summability — by the root
test on `bCocycle` (whose `(1/n)·log` tends to `λₖ − λₖ₋₁ < 0` a.e., supplied as `hblog`/`hLneg` by
the committed scalar layer) — into the soft-analysis Cauchy packaging `exists_tendsto_bandProjector`.
The hypotheses `hstepAE`, `hblog`, `hLneg`, `hbnn`, `hbpos` are the genuine outputs of the ergodic
Lyapunov-spectrum structure and the committed scalar root-test layer (`tendsto_log_singularValue`,
`tendsto_logNorm_compound_orbit_div_atTop_zero`); the conclusion is the UNCONDITIONAL a.e. existence
of the limiting Oseledets band projector. -/
theorem exists_tendsto_bandProjector_cocycle
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ x, (A x).det ≠ 0)
    (c : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ Fintype.card (Fin d))
    (hstepAE : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, stepHypCocycle A T c k hkd x n)
    (hbnn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ bCocycle A T x k n)
    (hbpos : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, 0 < bCocycle A T x k n)
    (L : X → ℝ) (hLneg : ∀ᵐ x ∂μ, L x < 0)
    (hblog : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (bCocycle A T x k n)) atTop (𝓝 (L x))) :
    ∀ᵐ x ∂μ, ∃ P : Matrix (Fin d) (Fin d) ℝ,
      Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 P) := by
  have hstep : ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ bCocycle A T x k n := by
    filter_upwards [hstepAE] with x hx
    filter_upwards [hx] with n hn
    exact stepHypCocycle_imp_step A T hA c hk1 hkd x n hn
  exact exists_tendsto_bandProjector (μ := μ) (c := c) A (fun x => bCocycle A T x k)
    hbnn hbpos L hLneg hblog hstep


/-- A nonnegative, eventually-positive sequence whose normalized log tends to a negative
limit converges to `0`. (Root test ⟹ summable ⟹ tail vanishes.) -/
theorem tendsto_zero_of_logLimit_neg (a : ℕ → ℝ) (hnn : ∀ n, 0 ≤ a n)
    (hpos : ∀ᶠ n in atTop, 0 < a n) {L : ℝ} (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop (𝓝 L)) :
    Tendsto a atTop (𝓝 0) :=
  (summable_of_logLimit_neg a hnn hpos hL hlog).tendsto_atTop_zero

/-- Per-point log-limit for `bCocycle`. -/
theorem tendsto_log_bCocycle_point {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) {x : X} {k : ℕ} (hk1 : 1 ≤ k) (hkd : k < d)
    {lamK lamK1 : ℝ}
    (hσk : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k))
      atTop (𝓝 lamK))
    (hσk1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)))
      atTop (𝓝 lamK1))
    (hcomp : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖)
      atTop (𝓝 0))
    (hcompinv : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖)
      atTop (𝓝 0))
    (hgap : lamK < lamK1) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (bCocycle A T x k n)) atTop (𝓝 (lamK - lamK1)) := by
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hkd
  -- abbreviations
  set cB : ℕ → ℝ := fun n => ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ with hcBdef
  set cBi : ℕ → ℝ := fun n => ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖ with hcBidef
  set σk : ℕ → ℝ := fun n => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k with hσkdef
  set σk1 : ℕ → ℝ := fun n => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)
    with hσk1def
  -- positivity facts for n ≥ 1
  have hcBpos : ∀ n, 0 < cB n := fun n =>
    norm_compound_pos k (hA _) (le_of_lt hkd) hd
  have hcBipos : ∀ n, 0 < cBi n := by
    intro n
    have hdet : ((A (T^[n] x))⁻¹).det ≠ 0 := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hA _)
    exact norm_compound_pos k hdet (le_of_lt hkd) hd
  have hσkpos : ∀ n, 0 < σk n := fun n =>
    singularValues_cocycle_pos hA n x (lt_of_lt_of_le hkd (le_refl d))
  have hσk1pos : ∀ n, 0 < σk1 n := fun n =>
    singularValues_cocycle_pos hA n x (by omega)
  -- the ratio
  set r : ℕ → ℝ := fun n => σk n / σk1 n with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => div_pos (hσkpos n) (hσk1pos n)
  -- κ² := (cB·cBi)²
  set κ2 : ℕ → ℝ := fun n => (cB n * cBi n) ^ 2 with hκ2def
  have hκ2pos : ∀ n, 0 < κ2 n := fun n => by
    rw [hκ2def]; exact pow_pos (mul_pos (hcBpos n) (hcBipos n)) 2
  -- (1/n) log r → lamK - lamK1
  have hlogr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)) atTop (𝓝 (lamK - lamK1)) := by
    have : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n))
        = fun n : ℕ => ((n : ℝ)⁻¹ * Real.log (σk n)) - ((n : ℝ)⁻¹ * Real.log (σk1 n)) := by
      funext n
      rw [hrdef, Real.log_div (ne_of_gt (hσkpos n)) (ne_of_gt (hσk1pos n))]; ring
    rw [this]; exact hσk.sub hσk1
  -- (1/n) log κ² → 0
  have hlogκ2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n)) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n))
        = fun n : ℕ => (2 : ℝ) * (((n : ℝ)⁻¹ * Real.log (cB n)) + ((n : ℝ)⁻¹ * Real.log (cBi n))) := by
      funext n
      rw [hκ2def, Real.log_pow, Real.log_mul (ne_of_gt (hcBpos n)) (ne_of_gt (hcBipos n))]
      push_cast; ring
    rw [heq]
    have := (hcomp.add hcompinv).const_mul (2 : ℝ)
    simpa using this
  -- (1/n) log (κ²·r) → lamK - lamK1
  have hlogκ2r : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * r n)) atTop
      (𝓝 (lamK - lamK1)) := by
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * r n))
        = fun n : ℕ => ((n : ℝ)⁻¹ * Real.log (κ2 n)) + ((n : ℝ)⁻¹ * Real.log (r n)) := by
      funext n
      rw [Real.log_mul (ne_of_gt (hκ2pos n)) (ne_of_gt (hrpos n))]; ring
    rw [heq]
    have := hlogκ2.add hlogr
    simpa using this
  -- κ²r² → 0  (since (1/n)log(κ²r²) → 2(lamK-lamK1) < 0)
  have hlogκ2r2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * (r n) ^ 2)) atTop
      (𝓝 (2 * (lamK - lamK1))) := by
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * (r n) ^ 2))
        = fun n : ℕ => ((n : ℝ)⁻¹ * Real.log (κ2 n))
            + (2 : ℝ) * ((n : ℝ)⁻¹ * Real.log (r n)) := by
      funext n
      have hrlog : Real.log ((r n) ^ 2) = 2 * Real.log (r n) := by
        rw [Real.log_pow]; push_cast; ring
      rw [Real.log_mul (ne_of_gt (hκ2pos n)) (pow_ne_zero 2 (ne_of_gt (hrpos n))), hrlog]
      ring
    rw [heq]
    have := hlogκ2.add (hlogr.const_mul (2 : ℝ))
    simpa using this
  have hκ2r2_tendsto : Tendsto (fun n : ℕ => κ2 n * (r n) ^ 2) atTop (𝓝 0) := by
    apply tendsto_zero_of_logLimit_neg _
      (fun n => le_of_lt (mul_pos (hκ2pos n) (pow_pos (hrpos n) 2)))
      (Filter.Eventually.of_forall (fun n => mul_pos (hκ2pos n) (pow_pos (hrpos n) 2)))
      (L := 2 * (lamK - lamK1)) (by linarith) hlogκ2r2
  -- v n := 1 - κ²r² → 1
  set v : ℕ → ℝ := fun n => 1 - κ2 n * (r n) ^ 2 with hvdef
  have hv_tendsto : Tendsto v atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) - κ2 n * (r n) ^ 2) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hκ2r2_tendsto
    simpa using this
  -- log v → 0
  have hlogv0 : Tendsto (fun n : ℕ => Real.log (v n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => Real.log (v n)) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp hv_tendsto
    simpa using this
  -- (1/n) log v → 0
  have hloginvv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (v n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := h1.mul hlogv0
    simpa using this
  -- (1/n) log √(2k) → 0
  have hsqrt : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Real.sqrt (2 * k))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := h1.mul_const (Real.log (Real.sqrt (2 * k)))
    simpa [mul_comm] using this
  have hsqrtpos : 0 < Real.sqrt (2 * k) := by
    apply Real.sqrt_pos.mpr
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  -- assemble: log bCocycle = log√(2k) + log(κ²r) - log v
  have hfinal : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Real.sqrt (2 * k))
          + ((n : ℝ)⁻¹ * Real.log (κ2 n * r n) - (n : ℝ)⁻¹ * Real.log (v n))) atTop
      (𝓝 (lamK - lamK1)) := by
    have h := hsqrt.add (hlogκ2r.sub hloginvv)
    have : (0:ℝ) + ((lamK - lamK1) - 0) = lamK - lamK1 := by ring
    rwa [this] at h
  -- need eventual v > 0 to split logs
  have hvpos : ∀ᶠ n in atTop, 0 < v n := by
    have := hv_tendsto.eventually (eventually_gt_nhds (show (0:ℝ) < 1 by norm_num))
    exact this
  refine hfinal.congr' ?_
  filter_upwards [hvpos] with n hvn
  -- bCocycle n = √(2k) · (κ²·r / v)
  have hbeq : bCocycle A T x k n = Real.sqrt (2 * k) * (κ2 n * r n / v n) := by
    rw [bCocycle]
  have hquot : (0:ℝ) < κ2 n * r n / v n := div_pos (mul_pos (hκ2pos n) (hrpos n)) hvn
  rw [hbeq, Real.log_mul (ne_of_gt hsqrtpos) (ne_of_gt hquot),
      Real.log_div (ne_of_gt (mul_pos (hκ2pos n) (hrpos n))) (ne_of_gt hvn)]
  ring

/-- The count of unsorted eigenvalues `> c` equals the count of sorted eigenvalues `> c`. -/
theorem card_eigenvalues_gt_eq_card_eigenvalues₀_gt
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian) (c : ℝ) :
    Fintype.card {i : Fin d // c < hM.eigenvalues i}
      = Fintype.card {j : Fin (Fintype.card (Fin d)) // c < hM.eigenvalues₀ j} := by
  classical
  apply Fintype.card_congr
  refine
    { toFun := fun i => ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm i.1, ?_⟩
      invFun := fun j => ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) j.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have := i.2; rwa [Matrix.IsHermitian.eigenvalues] at this
  · have := j.2; rw [Matrix.IsHermitian.eigenvalues]; simpa using this
  · intro i; ext; simp
  · intro j; ext; simp

/-- If an antitone `Fin N → ℝ` family has its value at index `⟨k-1⟩` above `c` and at index `⟨k⟩`
below `c`, then exactly `k` of its values exceed `c`. -/
theorem card_antitone_gt_eq {N : ℕ} (f : Fin N → ℝ) (hf : Antitone f) (c : ℝ)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N)
    (htop : c < f ⟨k - 1, lt_of_le_of_lt (Nat.sub_le k 1) hkN⟩) (hbot : f ⟨k, hkN⟩ < c) :
    Fintype.card {j : Fin N // c < f j} = k := by
  classical
  have hiff : ∀ j : Fin N, c < f j ↔ (j : ℕ) < k := by
    intro j
    constructor
    · intro hj
      by_contra hjk
      have hjk' : k ≤ (j : ℕ) := not_lt.mp hjk
      have : f j ≤ f ⟨k, hkN⟩ := hf (by simp [Fin.le_def]; omega)
      linarith
    · intro hj
      have : f ⟨k - 1, by omega⟩ ≤ f j := hf (by simp [Fin.le_def]; omega)
      linarith
  have hequiv : {j : Fin N // c < f j} ≃ {j : Fin N // (j : ℕ) < k} :=
    Equiv.subtypeEquivRight hiff
  rw [Fintype.card_congr hequiv, Fintype.card_subtype]
  -- count of `j : Fin N` with `(j:ℕ) < k` is `k`
  have hcardeq : (Finset.univ.filter (fun j : Fin N => (j : ℕ) < k)).card
      = (Finset.range k).card := by
    apply Finset.card_bij (fun (j : Fin N) _ => (j : ℕ))
    · intro j hj; simp only [Finset.mem_filter] at hj
      exact Finset.mem_range.mpr hj.2
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext hab
    · intro b hb
      simp only [Finset.mem_range] at hb
      exact ⟨⟨b, by omega⟩, by simp [hb], rfl⟩
  rw [hcardeq, Finset.card_range]

set_option maxHeartbeats 800000 in
/-- The two scalar inequalities `hμ₀lb`/`hgapμ` of `stepHypCocycle`, from the compound lower bound
`μ̃₀ ≥ cM²/cBi²` (`norm_sq_compound_mul_ge`) and the regime `κ²r² < 1`. -/
theorem step_inequalities {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (n : ℕ) (x : X) {k : ℕ} (hk1 : 1 ≤ k) (hkd : k < d)
    (hcBipos : 0 < ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖)
    (hκr : (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
        * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2 < 1) :
    (‖ExteriorNorm.compoundMatrix k (cocycle A T n x)‖ ^ 2
          / ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖ ^ 2
        * (1 - (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
            * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
          * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
            / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2)
        ≤ (∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i)
          - ((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k)
            * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ ^ 2)
    ∧ (((∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k)
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ ^ 2
        < ∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i) := by
  classical
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hkd
  set B := A (T^[n] x) with hBdef
  set M := cocycle A T n x with hMdef
  set cM := ‖ExteriorNorm.compoundMatrix k M‖ with hcM
  set cB := ‖ExteriorNorm.compoundMatrix k B‖ with hcB
  set cBi := ‖ExteriorNorm.compoundMatrix k B⁻¹‖ with hcBi
  set σk := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k with hσk
  set σk1 := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) with hσk1
  set r := σk / σk1 with hr
  -- positivity
  have hcMpos : 0 < cM := norm_compound_pos k (det_cocycle_ne_zero hA n x) (le_of_lt hkd) hd
  have hcBpos : 0 < cB := norm_compound_pos k (hA _) (le_of_lt hkd) hd
  have hσkpos : 0 < σk := singularValues_cocycle_pos hA n x (lt_of_lt_of_le hkd (le_refl d))
  have hσk1pos : 0 < σk1 := singularValues_cocycle_pos hA n x (by omega)
  have hrpos : 0 < r := div_pos hσkpos hσk1pos
  -- μ₀ = ‖compound k (B*M)‖²  ≥ cM²/cBi²
  have hBM : B * M = cocycle A T (n+1) x := by
    rw [hBdef, hMdef, show n+1 = 1 + n from by omega, cocycle_add, cocycle_one]
  have hμ₀eq : (∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i)
      = ‖ExteriorNorm.compoundMatrix k (B * M)‖ ^ 2 := by
    rw [hBM]
    simp only [lamCocycle]
    rw [Finset.prod_pow, ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound]
  set μ₀ := ∏ i ∈ Finset.range k, lamCocycle A T (n+1) x i with hμ₀
  have hμ₀lb_compound : cM ^ 2 / cBi ^ 2 ≤ μ₀ := by
    rw [hμ₀eq]
    exact ExteriorNorm.norm_sq_compound_mul_ge k (hA _) M hcBipos
  -- μ₁ = cM²·r²
  have hcMsq : cM ^ 2 = (∏ i ∈ Finset.range k,
      (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i) ^ 2 := by
    rw [hcM, hMdef, ← ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound]
  have hμ₁eq : (∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k
      = cM ^ 2 * r ^ 2 := by
    simp only [lamCocycle]
    rw [hcMsq, hr, hσk, hσk1, Finset.prod_pow]
    have hsplit : (∏ i ∈ Finset.range k,
          (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)
        = (∏ i ∈ Finset.range (k-1),
            (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)
          * (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) := by
      conv_lhs => rw [show k = (k-1) + 1 from by omega, Finset.prod_range_succ]
    rw [hsplit]
    have hσk1ne : (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) ≠ 0 :=
      ne_of_gt hσk1pos
    field_simp
  set μ₁ := (∏ i ∈ Finset.range (k-1), lamCocycle A T n x i) * lamCocycle A T n x k with hμ₁
  -- κ²r² in terms of cB,cBi,r
  have hκr' : cB ^ 2 * cBi ^ 2 * r ^ 2 < 1 := by
    have : (cB * cBi) ^ 2 * r ^ 2 < 1 := hκr
    nlinarith [this]
  have hcBi2pos : (0:ℝ) < cBi ^ 2 := by positivity
  have hcM2pos : (0:ℝ) < cM ^ 2 := by positivity
  -- key: cM²r²cB² < cM²/cBi²
  have hkey : cM ^ 2 * r ^ 2 * cB ^ 2 < cM ^ 2 / cBi ^ 2 := by
    rw [lt_div_iff₀ hcBi2pos]
    nlinarith [hκr', hcM2pos, mul_pos hcM2pos (mul_pos (pow_pos hrpos 2) (pow_pos hcBpos 2))]
  refine ⟨?_, ?_⟩
  · -- hμ₀lb
    rw [hμ₁eq]
    have hLHS : cM ^ 2 / cBi ^ 2 * (1 - (cB * cBi) ^ 2 * r ^ 2)
        = cM ^ 2 / cBi ^ 2 - cM ^ 2 * r ^ 2 * cB ^ 2 := by
      have hcBine : cBi ≠ 0 := ne_of_gt hcBipos
      have : cM ^ 2 / cBi ^ 2 * ((cB * cBi) ^ 2 * r ^ 2) = cM ^ 2 * r ^ 2 * cB ^ 2 := by
        field_simp
      rw [mul_sub, mul_one, this]
    rw [hLHS]
    linarith [hμ₀lb_compound]
  · -- hgapμ
    rw [hμ₁eq]
    calc cM ^ 2 * r ^ 2 * cB ^ 2 < cM ^ 2 / cBi ^ 2 := hkey
      _ ≤ μ₀ := hμ₀lb_compound


/-- `bCocycle` is positive once the regime `κ²r² < 1` holds. -/
theorem bCocycle_pos_of_regime {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (x : X) {k : ℕ} (hk1 : 1 ≤ k) (hkd : k < d) (n : ℕ)
    (hκr : (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
        * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2 < 1) :
    0 < bCocycle A T x k n := by
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hkd
  rw [bCocycle]
  have hcBpos : 0 < ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ :=
    norm_compound_pos k (hA _) (le_of_lt hkd) hd
  have hcBidet : ((A (T^[n] x))⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hA _)
  have hcBipos : 0 < ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖ :=
    norm_compound_pos k hcBidet (le_of_lt hkd) hd
  have hσkpos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k :=
    singularValues_cocycle_pos hA n x (lt_of_lt_of_le hkd (le_refl d))
  have hσk1pos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) :=
    singularValues_cocycle_pos hA n x (by omega)
  have hsqrtpos : 0 < Real.sqrt (2 * k) := by
    apply Real.sqrt_pos.mpr
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  have hrpos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
      / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) := div_pos hσkpos hσk1pos
  have hnumpos : 0 < (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
        * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
      * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
        / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) :=
    mul_pos (pow_pos (mul_pos hcBpos hcBipos) 2) hrpos
  have hdenpos : 0 < 1 - (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
        * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2 := by
    linarith [hκr]
  exact mul_pos hsqrtpos (div_pos hnumpos hdenpos)

set_option maxHeartbeats 1600000 in
/-- **DELIVERABLE — unconditional band-projector a.e. convergence at a distinct-exponent gap.**
For an ergodic, integrable, invertible cocycle and a threshold `c` strictly between the
exponentials of two consecutive distinct Lyapunov exponents at the cut index `k`
(`e^{λₖ} < c < e^{λₖ₋₁}` with `λₖ < λₖ₋₁`), the band spectral projector converges `μ`-a.e. -/
theorem tendsto_bandProjector_of_gap [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (c : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkd : k < d)
    (lamK lamK1 : ℝ) (hgap : lamK < lamK1)
    (hclo : Real.exp lamK < c) (hchi : c < Real.exp lamK1)
    (hσkAE : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k))
      atTop (𝓝 lamK))
    (hσk1AE : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)))
      atTop (𝓝 lamK1)) :
    ∀ᵐ x ∂μ, ∃ P : Matrix (Fin d) (Fin d) ℝ,
      Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 P) := by
  classical
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hkd
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  have hkdc : k ≤ Fintype.card (Fin d) := le_of_lt (lt_of_lt_of_eq hkd (Fintype.card_fin d).symm)
  -- compound tempered factors (forward and inverse)
  have hcompAE := tendsto_logNorm_compound_orbit_div_atTop_zero hmp hA hAmeas hTmeas hint hint'
    k (le_of_lt hkd) hd
  -- inverse: apply the same lemma to the cocycle `A⁻¹`
  have hAinvmeas : Measurable (fun x => (A x)⁻¹) := measurable_inv_matrix.comp hAmeas
  have hAinvdet : ∀ x, ((A x)⁻¹).det ≠ 0 := by
    intro x; rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hA x)
  have hintinvinv : IntegrableLogNorm (fun x => ((A x)⁻¹)⁻¹) μ := by
    apply hint.congr
    filter_upwards with x
    rw [Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit (hA x))]
  have hcompinvAE := tendsto_logNorm_compound_orbit_div_atTop_zero hmp hAinvdet hAinvmeas hTmeas
    hint' hintinvinv k (le_of_lt hkd) hd
  -- index facts
  have hkcard : k < Fintype.card (Fin d) := lt_of_lt_of_eq hkd (Fintype.card_fin d).symm
  have hk1card : k - 1 < Fintype.card (Fin d) := by rw [Fintype.card_fin]; omega
  -- dominating sequence
  set b : X → ℕ → ℝ := fun x n => max 0 (bCocycle A T x k n) with hbdef
  -- log-limit of bCocycle, a.e.
  have hblogAE : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (bCocycle A T x k n)) atTop
        (𝓝 (lamK - lamK1)) := by
    filter_upwards [hσkAE, hσk1AE, hcompAE, hcompinvAE] with x hσkx hσk1x hcompx hcompinvx
    exact tendsto_log_bCocycle_point hA hk1 hkd hσkx hσk1x hcompx hcompinvx hgap
  -- the eventual cut/gap/regime data, a.e.
  have hQAE : ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      (c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨k - 1, hk1card⟩
        ∧ (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨k, hkcard⟩ < c
        ∧ (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
            < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)
        ∧ (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
              * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
            * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
              / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2 < 1) := by
    filter_upwards [hσkAE, hσk1AE, hcompAE, hcompinvAE] with x hσkx hσk1x hcompx hcompinvx
    -- eigenvalue convergences
    have hev_k1 : Tendsto
        (fun n : ℕ => (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨k - 1, hk1card⟩)
        atTop (𝓝 (Real.exp lamK1)) :=
      eigenvalues_qpow_tendsto hA ⟨k - 1, hk1card⟩ (by
        have hcast : ((⟨k - 1, hk1card⟩ : Fin (Fintype.card (Fin d))) : ℕ) = k - 1 := rfl
        simpa [hcast] using hσk1x)
    have hev_k : Tendsto
        (fun n : ℕ => (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨k, hkcard⟩)
        atTop (𝓝 (Real.exp lamK)) :=
      eigenvalues_qpow_tendsto hA ⟨k, hkcard⟩ (by
        have hcast : ((⟨k, hkcard⟩ : Fin (Fintype.card (Fin d))) : ℕ) = k := rfl
        simpa [hcast] using hσkx)
    -- r → 0
    have hσkpos : ∀ n, 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k := fun n =>
      singularValues_cocycle_pos hA n x (lt_of_lt_of_le hkd (le_refl d))
    have hσk1pos : ∀ n, 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) :=
      fun n => singularValues_cocycle_pos hA n x (by omega)
    have hlogr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)))
        atTop (𝓝 (lamK - lamK1)) := by
      have heq : (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
            / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)))
          = fun n : ℕ => ((n : ℝ)⁻¹ *
              Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k))
            - ((n : ℝ)⁻¹ *
              Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1))) := by
        funext n
        rw [Real.log_div (ne_of_gt (hσkpos n)) (ne_of_gt (hσk1pos n))]; ring
      rw [heq]; exact hσkx.sub hσk1x
    have hr0 : Tendsto (fun n : ℕ => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
        / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) atTop (𝓝 0) :=
      tendsto_zero_of_logLimit_neg _ (fun n => le_of_lt (div_pos (hσkpos n) (hσk1pos n)))
        (Filter.Eventually.of_forall (fun n => div_pos (hσkpos n) (hσk1pos n)))
        (L := lamK - lamK1) (by linarith) hlogr
    -- κ²r² → 0
    set κ2r2 : ℕ → ℝ := fun n => (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
          * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) ^ 2
        * ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1)) ^ 2 with hκ2r2def
    have hcBpos : ∀ n, 0 < ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖ := fun n =>
      norm_compound_pos k (hA _) (le_of_lt hkd) hd
    have hcBipos : ∀ n, 0 < ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖ := by
      intro n
      have hdet : ((A (T^[n] x))⁻¹).det ≠ 0 := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hA _)
      exact norm_compound_pos k hdet (le_of_lt hkd) hd
    have hκ2r2pos : ∀ n, 0 < κ2r2 n := by
      intro n; rw [hκ2r2def]
      exact mul_pos (pow_pos (mul_pos (hcBpos n) (hcBipos n)) 2)
        (pow_pos (div_pos (hσkpos n) (hσk1pos n)) 2)
    have hlogκ2r2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2r2 n)) atTop
        (𝓝 (2 * 0 + 2 * (lamK - lamK1))) := by
      have heq : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2r2 n))
          = fun n : ℕ => (2 : ℝ) * ((n : ℝ)⁻¹ *
                Real.log (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
                  * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖))
              + (2 : ℝ) * ((n : ℝ)⁻¹ *
                Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
                  / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1))) := by
        funext n
        rw [hκ2r2def,
          Real.log_mul (ne_of_gt (pow_pos (mul_pos (hcBpos n) (hcBipos n)) 2))
            (pow_ne_zero 2 (ne_of_gt (div_pos (hσkpos n) (hσk1pos n)))),
          Real.log_pow, Real.log_pow]
        push_cast; ring
      rw [heq]
      have hcombo : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
              * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖)) atTop (𝓝 0) := by
        have heqc : (fun n : ℕ => (n : ℝ)⁻¹ *
              Real.log (‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖
                * ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖))
            = fun n : ℕ => ((n : ℝ)⁻¹ *
                Real.log ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖)
              + ((n : ℝ)⁻¹ *
                Real.log ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))⁻¹‖) := by
          funext n
          rw [Real.log_mul (ne_of_gt (hcBpos n)) (ne_of_gt (hcBipos n))]; ring
        rw [heqc]; simpa using hcompx.add hcompinvx
      exact (hcombo.const_mul (2:ℝ)).add (hlogr.const_mul (2:ℝ))
    have hκ2r20 : Tendsto κ2r2 atTop (𝓝 0) :=
      tendsto_zero_of_logLimit_neg _ (fun n => le_of_lt (hκ2r2pos n))
        (Filter.Eventually.of_forall hκ2r2pos) (L := 2 * 0 + 2 * (lamK - lamK1))
        (by linarith) hlogκ2r2
    -- now eventual facts
    have e1 : ∀ᶠ n in atTop,
        c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨k - 1, hk1card⟩ :=
      hev_k1.eventually (eventually_gt_nhds hchi)
    have e2 : ∀ᶠ n in atTop,
        (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨k, hkcard⟩ < c :=
      hev_k.eventually (eventually_lt_nhds hclo)
    have e3 : ∀ᶠ n in atTop, (Matrix.toEuclideanLin (cocycle A T n x)).singularValues k
        / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (k-1) < 1 :=
      hr0.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
    have e4 : ∀ᶠ n in atTop, κ2r2 n < 1 :=
      hκ2r20.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
    filter_upwards [e1, e2, e3, e4] with n h1 h2 h3 h4
    refine ⟨h1, h2, ?_, h4⟩
    -- σₖ < σₖ₋₁ from r < 1
    have hσk1pos' := hσk1pos n
    rw [div_lt_one hσk1pos'] at h3
    exact h3
  -- build the eventual stepHypCocycle from hQAE (using n and n+1)
  have hstepAE : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, stepHypCocycle A T c k hkdc x n := by
    filter_upwards [hQAE] with x hQ
    -- shift hQ to n+1
    have hQshift : ∀ᶠ n in atTop,
        (c < (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀ ⟨k - 1, hk1card⟩
          ∧ (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀ ⟨k, hkcard⟩ < c
          ∧ (Matrix.toEuclideanLin (cocycle A T (n+1) x)).singularValues k
              < (Matrix.toEuclideanLin (cocycle A T (n+1) x)).singularValues (k-1)
          ∧ (‖ExteriorNorm.compoundMatrix k (A (T^[n+1] x))‖
                * ‖ExteriorNorm.compoundMatrix k (A (T^[n+1] x))⁻¹‖) ^ 2
              * ((Matrix.toEuclideanLin (cocycle A T (n+1) x)).singularValues k
                / (Matrix.toEuclideanLin (cocycle A T (n+1) x)).singularValues (k-1)) ^ 2 < 1) := by
      have := hQ
      rw [eventually_atTop] at this ⊢
      obtain ⟨N, hN⟩ := this
      exact ⟨N, fun n hn => hN (n+1) (by omega)⟩
    filter_upwards [hQ, hQshift] with n hQn hQn1
    obtain ⟨ha, hb', hc', hd'⟩ := hQn
    obtain ⟨ha1, hb1, hc1, hd1⟩ := hQn1
    -- antitone witnesses
    have hanti_n := (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀_antitone
    have hanti_n1 := (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀_antitone
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hd'⟩
    · -- top n
      intro j
      have : (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨k - 1, hk1card⟩
          ≤ (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hkdc⟩ :=
        hanti_n (by simp only [Fin.le_def]; omega)
      linarith [ha]
    · -- count n
      rw [card_eigenvalues_gt_eq_card_eigenvalues₀_gt]
      exact card_antitone_gt_eq (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
        hanti_n c hk1 hkcard ha hb'
    · -- top n+1
      intro j
      have : (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀ ⟨k - 1, hk1card⟩
          ≤ (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hkdc⟩ :=
        hanti_n1 (by simp only [Fin.le_def]; omega)
      linarith [ha1]
    · -- count n+1
      rw [card_eigenvalues_gt_eq_card_eigenvalues₀_gt]
      exact card_antitone_gt_eq (qpow_isSelfAdjoint A T (n+1) x).isHermitian.eigenvalues₀
        hanti_n1 c hk1 hkcard ha1 hb1
    · -- gap n
      simp only [lamCocycle]
      have hnn := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg k
      nlinarith [hc', hnn]
    · -- gap n+1
      simp only [lamCocycle]
      have hnn := (Matrix.toEuclideanLin (cocycle A T (n+1) x)).singularValues_nonneg k
      nlinarith [hc1, hnn]
    · -- cBipos n
      have hdet : ((A (T^[n] x))⁻¹).det ≠ 0 := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hA _)
      exact norm_compound_pos k hdet (le_of_lt hkd) hd
    · -- hμ₀lb
      have hcBidet : ((A (T^[n] x))⁻¹).det ≠ 0 := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hA _)
      exact (step_inequalities hA n x hk1 hkd
        (norm_compound_pos k hcBidet (le_of_lt hkd) hd) hd').1
    · -- hgapμ
      have hcBidet : ((A (T^[n] x))⁻¹).det ≠ 0 := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hA _)
      exact (step_inequalities hA n x hk1 hkd
        (norm_compound_pos k hcBidet (le_of_lt hkd) hd) hd').2
  -- now route through the abstract Cauchy packaging with `b = max 0 bCocycle`
  have hb : ∀ᵐ x ∂μ, ∀ n, 0 ≤ b x n :=
    Filter.Eventually.of_forall (fun x n => le_max_left _ _)
  have hbpos : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, 0 < b x n := by
    filter_upwards [hstepAE] with x hx
    filter_upwards [hx] with n hn
    obtain ⟨_, _, _, _, _, _, _, _, _, hκr⟩ := hn
    exact lt_max_of_lt_right (bCocycle_pos_of_regime hA x hk1 hkd n hκr)
  have hlogb : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b x n)) atTop (𝓝 (lamK - lamK1)) := by
    filter_upwards [hblogAE, hstepAE] with x hlx hstepx
    refine hlx.congr' ?_
    filter_upwards [hstepx] with n hn
    obtain ⟨_, _, _, _, _, _, _, _, _, hκr⟩ := hn
    have hbpn : 0 < bCocycle A T x k n := bCocycle_pos_of_regime hA x hk1 hkd n hκr
    have hbxn : b x n = bCocycle A T x k n := by
      rw [hbdef]; exact max_eq_right (le_of_lt hbpn)
    rw [hbxn]
  have hLneg : ∀ᵐ x ∂μ, (fun _ : X => lamK - lamK1) x < 0 :=
    Filter.Eventually.of_forall (fun _ => by dsimp only; linarith)
  have hstep : ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ b x n := by
    filter_upwards [hstepAE] with x hx
    filter_upwards [hx] with n hn
    have hle := stepHypCocycle_imp_step A T hA c hk1 hkdc x n hn
    exact le_trans hle (le_max_right _ _)
  exact exists_tendsto_bandProjector (μ := μ) (c := c) A b hb hbpos
    (fun _ => lamK - lamK1) hLneg hlogb hstep

/-! ## L7c.6: assembling the Oseledets limit `qpow A T n x → Λ x`

The final assembly. The eigenvalues `μᵢ,ₙ = σᵢ^{1/n}` of `qpow A T n x` converge a.e. to the
exponentials `e^{λᵢ}` of the (deterministic, antitone) Lyapunov exponents `λᵢ = Γ_{i+1} − Γ_i`. We
group the spectrum at thresholds `cₖ = exp((λₖ + λₖ₋₁)/2)`, one per index `1 ≤ k < d`. The candidate
limit at level `n` is the **block approximant**
`Λₙ x := e^{λ_{d-1}} • 1 + ∑_{k=1}^{d-1} (e^{λₖ₋₁} − e^{λₖ}) • bandProjector (Ioi cₖ) n x`.
Two facts combine:
* `‖qpow A T n x − Λₙ x‖ ≤ maxᵢ |μᵢ,ₙ − e^{λᵢ}| → 0` (the spectral-block operator-norm bound
  `norm_cfc_le_of_forall_eigenvalue_abs_le`, since `Λₙ = cfc h (qpow…)` for the block-value step
  function `h`, and on the spectrum `h` reproduces the right exponential);
* `Λₙ x → Λ x` because each band projector converges a.e. (`tendsto_bandProjector_of_gap` at the
  genuine gaps; the non-gap terms have coefficient `0`).
Hence `qpow A T n x → Λ x` a.e., discharging `L7_statement`. -/

/-- **Telescoping of the exponential increments.** For any `f : ℕ → ℝ` and `j < d`,
`f (d-1) + ∑_{k ∈ Ico (j+1) d} (f (k-1) − f k) = f j`. The Abel-summation identity behind the block
approximant: summing the increments `e^{λₖ₋₁} − e^{λₖ}` over the indices above `j` telescopes to
`e^{λⱼ} − e^{λ_{d-1}}`. -/
theorem sum_Ico_increment_telescope (f : ℕ → ℝ) {D : ℕ} {j : ℕ} (hj : j < D) :
    f (D - 1) + ∑ k ∈ Finset.Ico (j + 1) D, (f (k - 1) - f k) = f j := by
  have htel : ∑ k ∈ Finset.Ico (j + 1) D, (f (k - 1) - f k) = f j - f (D - 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hcongr : ∀ i ∈ Finset.range (D - (j + 1)), f (j + 1 + i - 1) - f (j + 1 + i)
        = -(f (j + (i + 1)) - f (j + i)) := by
      intro i _
      have h1 : j + 1 + i - 1 = j + i := by omega
      have h2 : j + 1 + i = j + (i + 1) := by omega
      rw [h1, h2]; ring
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib,
      Finset.sum_range_sub (fun m => f (j + m))]
    have hd1 : j + (D - (j + 1)) = D - 1 := by omega
    simp only [hd1, Nat.add_zero]
    ring
  rw [htel]; ring

/-- The **block-value step function** for an antitone exponent sequence `lam`. On `ℝ`,
`stepVal lam D t = e^{λ_{D-1}} + ∑_{k=1}^{D-1} (e^{λₖ₋₁} − e^{λₖ}) · 𝟙_{(cₖ, ∞)}(t)`, where
`cₖ = exp((λₖ + λₖ₋₁)/2)` is the threshold strictly inside the `k`-th gap. It is the function whose
continuous functional calculus on `qpow A T n x` produces the block approximant. -/
noncomputable def stepVal (lam : ℕ → ℝ) (D : ℕ) (t : ℝ) : ℝ :=
  Real.exp (lam (D - 1)) +
    ∑ k ∈ Finset.Ico 1 D, (Real.exp (lam (k - 1)) - Real.exp (lam k)) *
      Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) (1 : ℝ → ℝ) t

/-- **The step function reproduces the exponentials on the spectrum.** If `lam` is antitone on
`[0, D)` (`hanti`) and `j < D`, then `stepVal lam D (e^{λⱼ}) = e^{λⱼ}`: the threshold indicators
select exactly the increments above index `j`, which telescope (`sum_Ico_increment_telescope`). -/
theorem stepVal_exp_lam (lam : ℕ → ℝ) (D : ℕ)
    (hanti : ∀ a b : ℕ, a ≤ b → b < D → lam b ≤ lam a) {j : ℕ} (hj : j < D) :
    stepVal lam D (Real.exp (lam j)) = Real.exp (lam j) := by
  rw [stepVal]
  have hterm : ∀ k ∈ Finset.Ico 1 D,
      (Real.exp (lam (k - 1)) - Real.exp (lam k)) *
        Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) (1 : ℝ → ℝ)
          (Real.exp (lam j))
      = (Real.exp (lam (k - 1)) - Real.exp (lam k)) *
          (if j + 1 ≤ k then (1 : ℝ) else 0) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk1, hkD⟩ := hk
    -- antitone facts at indices k-1, k
    have hle : lam k ≤ lam (k - 1) := hanti (k - 1) k (by omega) hkD
    by_cases hgap : lam k = lam (k - 1)
    · -- non-gap: coefficient is 0
      rw [hgap]; ring
    · -- gap: lam k < lam (k-1)
      have hlt : lam k < lam (k - 1) := lt_of_le_of_ne hle hgap
      have hcoef_pos : 0 < Real.exp (lam (k - 1)) - Real.exp (lam k) := by
        have := Real.exp_lt_exp.mpr hlt; linarith
      congr 1
      by_cases hjk : j + 1 ≤ k
      · -- j ≤ k-1, so lam j ≥ lam (k-1) > threshold
        rw [if_pos hjk]
        have hlamj : lam (k - 1) ≤ lam j := hanti j (k - 1) (by omega) (by omega)
        have hmem : Real.exp (lam j) ∈ Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2)) := by
          rw [Set.mem_Ioi, Real.exp_lt_exp]
          have : (lam k + lam (k - 1)) / 2 < lam (k - 1) := by linarith
          linarith
        rw [Set.indicator_of_mem hmem, Pi.one_apply]
      · -- j ≥ k, so lam j ≤ lam k < threshold
        rw [if_neg hjk]
        have hjge : k ≤ j := by omega
        have hlamj : lam j ≤ lam k := hanti k j hjge hj
        have hnmem : Real.exp (lam j) ∉ Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2)) := by
          rw [Set.mem_Ioi, not_lt, Real.exp_le_exp]
          have : lam k < (lam k + lam (k - 1)) / 2 := by linarith
          linarith
        rw [Set.indicator_of_notMem hnmem]
  rw [Finset.sum_congr rfl hterm]
  -- restrict the if to the interval Ico (j+1) D
  have hsum : ∑ k ∈ Finset.Ico 1 D,
        (Real.exp (lam (k - 1)) - Real.exp (lam k)) * (if j + 1 ≤ k then (1 : ℝ) else 0)
      = ∑ k ∈ Finset.Ico (j + 1) D, (Real.exp (lam (k - 1)) - Real.exp (lam k)) := by
    have hmulite : ∀ k, (Real.exp (lam (k - 1)) - Real.exp (lam k)) * (if j + 1 ≤ k then (1 : ℝ) else 0)
        = if j + 1 ≤ k then (Real.exp (lam (k - 1)) - Real.exp (lam k)) else 0 := by
      intro k; rw [mul_ite, mul_one, mul_zero]
    simp_rw [hmulite]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun k _ => rfl)
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hsum, sum_Ico_increment_telescope (fun m => Real.exp (lam m)) hj]

/-- **The block approximant `cfc (stepVal) (qpow)` as a band-projector combination.** Expanding the
step function `stepVal lam D` through the linearity of the continuous functional calculus (valid on
the finite matrix spectrum): the CFC of the block-value step function on `qpow A T n x` is the
explicit linear combination of band projectors
`e^{λ_{D-1}} • 1 + ∑_{k=1}^{D-1} (e^{λₖ₋₁} − e^{λₖ}) • bandProjector (Ioi cₖ) n x`. This is the form
whose a.e. convergence follows from the per-gap band-projector convergence. -/
theorem cfc_stepVal_qpow_eq (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (lam : ℕ → ℝ) (D n : ℕ)
    (x : X) :
    cfc (stepVal lam D) (qpow A T n x)
      = Real.exp (lam (D - 1)) • (1 : Matrix (Fin d) (Fin d) ℝ)
        + ∑ k ∈ Finset.Ico 1 D, (Real.exp (lam (k - 1)) - Real.exp (lam k)) •
            bandProjector A T (Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) 1) n x := by
  set M := qpow A T n x with hM
  have hMsa : IsSelfAdjoint M := qpow_isSelfAdjoint A T n x
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ M) :=
    fun f => (Matrix.finite_real_spectrum (A := M)).continuousOn _
  -- stepVal = const + ∑ (coef k) • indicator k, as functions
  let ind : ℕ → ℝ → ℝ := fun k =>
    Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) (1 : ℝ → ℝ)
  let coef : ℕ → ℝ := fun k => Real.exp (lam (k - 1)) - Real.exp (lam k)
  have hsplit : stepVal lam D
      = fun t => Real.exp (lam (D - 1)) + (∑ k ∈ Finset.Ico 1 D, (coef k • ind k)) t := by
    funext t
    simp only [stepVal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ind, coef]
  rw [hsplit,
    cfc_const_add (Real.exp (lam (D - 1))) (∑ k ∈ Finset.Ico 1 D, (coef k • ind k)) M
      (hcont _) hMsa]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one]
  · rw [cfc_sum (fun k => coef k • ind k) M (Finset.Ico 1 D) (fun k _ => hcont _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [show (coef k • ind k) = (fun x => coef k • ind k x) from rfl,
      cfc_smul (coef k) (ind k) M (hcont _)]
    rfl

/-- **The spectral-deviation bound for `M − cfc g M`.** For a self-adjoint matrix `M`, the operator
norm of `M − cfc g M` is at most the sum over the sorted eigenvalues of `|μⱼ − g μⱼ|`. (Writing
`M = cfc id M` and `M − cfc g M = cfc (· − g ·) M`, this is `norm_cfc_le_of_forall_eigenvalue_abs_le`
with the per-eigenvalue deviation bounded by the full sum of nonnegative deviations.) -/
theorem norm_sub_cfc_le_sum_eigenvalue_dev (M : Matrix (Fin d) (Fin d) ℝ) (hMsa : IsSelfAdjoint M)
    (g : ℝ → ℝ) :
    ‖M - cfc g M‖
      ≤ ∑ j : Fin (Fintype.card (Fin d)),
          |hMsa.isHermitian.eigenvalues₀ j - g (hMsa.isHermitian.eigenvalues₀ j)| := by
  classical
  set hM := hMsa.isHermitian with hMdef
  -- M - cfc g M = cfc (fun t => t - g t) M
  have hsub : M - cfc g M = cfc (fun t => t - g t) M := by
    rw [cfc_sub (fun t => t) g M
      ((Matrix.finite_real_spectrum (A := M)).continuousOn _)
      ((Matrix.finite_real_spectrum (A := M)).continuousOn _),
      cfc_id' ℝ M]
  rw [hsub]
  set c := ∑ j : Fin (Fintype.card (Fin d)),
    |hM.eigenvalues₀ j - g (hM.eigenvalues₀ j)| with hc
  have hcnn : 0 ≤ c := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  apply norm_cfc_le_of_forall_eigenvalue_abs_le M hM (fun t => t - g t) hcnn
  intro i
  -- eigenvalues i = eigenvalues₀ (e.symm i)
  set e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))))
  have hei : hM.eigenvalues i = hM.eigenvalues₀ (e.symm i) := rfl
  rw [hei]
  exact Finset.single_le_sum (f := fun j => |hM.eigenvalues₀ j - g (hM.eigenvalues₀ j)|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ (e.symm i))

/-- **The deterministic per-index Lyapunov exponents.** Packaged from the ergodic `Γ_k` limits: for
an ergodic, invertible, log-integrable cocycle there is an antitone constant sequence `lam : ℕ → ℝ`
(supported on `[0, d)`) such that, for `μ`-a.e. `x` and every `i < d`, the normalized log of the
`i`-th singular value of `A⁽ⁿ⁾` converges to `lam i`. The `lam i = Γ_{i+1} − Γ_i` are the logarithms
of the eigenvalues of the Oseledets limit. -/
theorem exists_lam_tendsto_singularValue [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ lam : ℕ → ℝ, (∀ a b : ℕ, a ≤ b → b < d → lam b ≤ lam a) ∧
      ∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam i)) := by
  classical
  -- The Γ_k constants for 0 ≤ k ≤ d (and 0 for k > d).
  have hΓ : ∀ k : ℕ, k ≤ d → ∃ Γk : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Sprod A T k n x)) atTop (𝓝 Γk) :=
    fun k hk => tendsto_GammaK_of_integrableLogNorm hT hA hAmeas hint hint' hk
  choose! Γ hΓspec using hΓ
  set lam : ℕ → ℝ := fun i => Γ (i + 1) - Γ i with hlamdef
  -- a.e., the σ-limit holds at every index `i < d`
  have hσlim : ∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
      atTop (𝓝 (lam i)) := by
    intro i hi
    have ha := hΓspec (i + 1) (by omega)
    have hb := hΓspec i (by omega)
    filter_upwards [ha, hb] with x hax hbx
    exact tendsto_log_singularValue hA hi hax hbx
  -- consecutive antitonicity, from the antitone singular values
  have hcons : ∀ i : ℕ, i + 1 < d → lam (i + 1) ≤ lam i := by
    intro i hi1
    have hae : ∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues (i + 1)))
          atTop (𝓝 (lam (i + 1)))
        ∧ Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
          atTop (𝓝 (lam i)) := by
      filter_upwards [hσlim (i + 1) (by omega), hσlim i (by omega)] with x h1 h2 using ⟨h1, h2⟩
    obtain ⟨x, hx1, hx2⟩ := hae.exists
    refine le_of_tendsto_of_tendsto' hx1 hx2 (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hpos : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      have hσi : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i :=
        singularValues_cocycle_pos hA n x (by omega)
      have hσi1 : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (i + 1) :=
        singularValues_cocycle_pos hA n x (by omega)
      have hle : (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (i + 1)
          ≤ (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i :=
        (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_antitone (by omega)
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hσi1 hle) hpos
  refine ⟨lam, ?_, hσlim⟩
  -- chain consecutive inequalities to full antitonicity on [0, d)
  intro a b hab hbd
  induction b with
  | zero =>
    have : a = 0 := by omega
    rw [this]
  | succ m ih =>
    rcases Nat.lt_or_ge a (m + 1) with hlt | hge
    · have hstep : lam (m + 1) ≤ lam m := hcons m (by omega)
      have hrec : lam m ≤ lam a := ih (by omega) (by omega)
      exact le_trans hstep hrec
    · have : a = m + 1 := by omega
      rw [this]

/-- **L7c.6 — the per-term band-projector convergence.** For `μ`-a.e. `x` and every threshold index
`k ∈ [1, d)`, the `k`-th block term `(e^{λₖ₋₁} − e^{λₖ}) • bandProjector (Ioi cₖ) n x` converges. At a
genuine gap (`λₖ < λₖ₋₁`) this is the band-projector convergence `tendsto_bandProjector_of_gap`; at a
non-gap the coefficient `e^{λₖ₋₁} − e^{λₖ}` vanishes, so the term is constantly `0`. -/
theorem ae_forall_tendsto_block_term [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (lam : ℕ → ℝ) (hanti : ∀ a b : ℕ, a ≤ b → b < d → lam b ≤ lam a)
    (hσ : ∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
      atTop (𝓝 (lam i))) :
    ∀ᵐ x ∂μ, ∀ k ∈ Finset.Ico 1 d, ∃ Q : Matrix (Fin d) (Fin d) ℝ, Tendsto
      (fun n => (Real.exp (lam (k - 1)) - Real.exp (lam k)) •
        bandProjector A T (Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) 1) n x)
      atTop (𝓝 Q) := by
  rw [eventually_all_finset]
  intro k hk
  rw [Finset.mem_Ico] at hk
  obtain ⟨hk1, hkd⟩ := hk
  by_cases hgap : lam k < lam (k - 1)
  · -- genuine gap: band projector converges
    have hclo : Real.exp (lam k) < Real.exp ((lam k + lam (k - 1)) / 2) := by
      rw [Real.exp_lt_exp]; linarith
    have hchi : Real.exp ((lam k + lam (k - 1)) / 2) < Real.exp (lam (k - 1)) := by
      rw [Real.exp_lt_exp]; linarith
    have hband := tendsto_bandProjector_of_gap hT hA hAmeas hint hint'
      (Real.exp ((lam k + lam (k - 1)) / 2)) hk1 hkd (lam k) (lam (k - 1)) hgap hclo hchi
      (by
        have := hσ k hkd
        -- index k singular value, careful: hσ for k uses index k; need (k-1) handling below
        exact this)
      (by
        have := hσ (k - 1) (by omega)
        exact this)
    filter_upwards [hband] with x hx
    obtain ⟨P, hP⟩ := hx
    exact ⟨(Real.exp (lam (k - 1)) - Real.exp (lam k)) • P, hP.const_smul _⟩
  · -- non-gap: coefficient is zero, term is constantly 0
    have hcoef : Real.exp (lam (k - 1)) - Real.exp (lam k) = 0 := by
      have hle : lam k ≤ lam (k - 1) := hanti (k - 1) k (by omega) hkd
      have : lam (k - 1) = lam k := le_antisymm (not_lt.mp hgap) hle
      rw [this]; ring
    filter_upwards with x
    refine ⟨0, ?_⟩
    simp only [hcoef, zero_smul]
    exact tendsto_const_nhds

/-- **L7 — the Oseledets limit exists.** Discharges `L7_statement`: for `μ`-a.e. `x`, the candidate
matrices `qpow A T n x = (Qₙ)^{1/(2n)}` converge in the matrix metric to a single matrix `Λ x`.

The proof combines the four banked ingredients. The eigenvalues `μⱼ,ₙ = σⱼ^{1/n}` converge to the
exponentials `e^{λⱼ}` of the deterministic exponents (`exists_lam_tendsto_singularValue` +
`eigenvalues_qpow_tendsto`). The block approximant `Λₙ x = cfc (stepVal lam d) (qpow…)` then satisfies
`‖qpow A T n x − Λₙ x‖ ≤ ∑ⱼ |μⱼ,ₙ − stepVal(μⱼ,ₙ)| → 0` (`norm_sub_cfc_le_sum_eigenvalue_dev`, with
each summand eventually `|μⱼ,ₙ − e^{λⱼ}|` since `stepVal` reproduces the exponentials on the
spectrum — `stepVal_exp_lam`), while `Λₙ x` converges as a finite combination of convergent
band projectors (`ae_forall_tendsto_block_term` + `cfc_stepVal_qpow_eq`). Hence `qpow A T n x`
converges; `Λ` is read off pointwise by `Classical.choice`. -/
theorem tendsto_qpow [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    L7_statement μ T A := by
  classical
  obtain ⟨lam, hanti, hσ⟩ :=
    exists_lam_tendsto_singularValue hT hA hAmeas hint hint'
  -- a.e. per-term band-projector convergence
  have hblock := ae_forall_tendsto_block_term hT hA hAmeas hint hint' lam hanti hσ
  -- a.e. eigenvalue convergence μⱼ,ₙ → e^{λⱼ} for every sorted index j
  have hev : ∀ᵐ x ∂μ, ∀ i : Fin (Fintype.card (Fin d)),
      Tendsto (fun n : ℕ => (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i)
        atTop (𝓝 (Real.exp (lam (i : ℕ)))) := by
    refine ae_all_iff.mpr (fun i => ?_)
    have hid : (i : ℕ) < d := lt_of_lt_of_eq i.isLt (Fintype.card_fin d)
    filter_upwards [hσ (i : ℕ) hid] with x hx
    exact eigenvalues_qpow_tendsto hA i (by simpa using hx)
  -- the good set: combine
  refine ⟨fun x => if h : ∃ L, Tendsto (fun n => qpow A T n x) atTop (𝓝 L) then h.choose else 0, ?_⟩
  filter_upwards [hblock, hev] with x hxblock hxev
  -- it suffices to show ∃ L, Tendsto (qpow · x) → L; then the dif picks it
  suffices hex : ∃ L, Tendsto (fun n => qpow A T n x) atTop (𝓝 L) by
    rw [dif_pos hex]; exact hex.choose_spec
  -- block approximant converges (finite sum of convergent terms + constant)
  obtain ⟨Lblock, hLblock⟩ :
      ∃ Lblock, Tendsto (fun n => Real.exp (lam (d - 1)) • (1 : Matrix (Fin d) (Fin d) ℝ)
          + ∑ k ∈ Finset.Ico 1 d, (Real.exp (lam (k - 1)) - Real.exp (lam k)) •
              bandProjector A T
                (Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) 1) n x)
        atTop (𝓝 Lblock) := by
    refine ⟨Real.exp (lam (d - 1)) • (1 : Matrix (Fin d) (Fin d) ℝ)
        + ∑ k ∈ (Finset.Ico 1 d).attach, (hxblock k.1 k.2).choose, ?_⟩
    refine tendsto_const_nhds.add ?_
    rw [show (fun n => ∑ k ∈ Finset.Ico 1 d, (Real.exp (lam (k - 1)) - Real.exp (lam k)) •
          bandProjector A T
            (Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) 1) n x)
        = (fun n => ∑ k ∈ (Finset.Ico 1 d).attach,
            (Real.exp (lam (k.1 - 1)) - Real.exp (lam k.1)) •
              bandProjector A T
                (Set.indicator (Set.Ioi (Real.exp ((lam k.1 + lam (k.1 - 1)) / 2))) 1) n x)
        from by funext n; rw [← Finset.sum_attach]]
    refine tendsto_finset_sum _ (fun k _ => ?_)
    exact (hxblock k.1 k.2).choose_spec
  -- the block approximant equals cfc (stepVal lam d) (qpow)
  have hLn_eq : ∀ n, Real.exp (lam (d - 1)) • (1 : Matrix (Fin d) (Fin d) ℝ)
          + ∑ k ∈ Finset.Ico 1 d, (Real.exp (lam (k - 1)) - Real.exp (lam k)) •
              bandProjector A T
                (Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) 1) n x
        = cfc (stepVal lam d) (qpow A T n x) := by
    intro n; rw [cfc_stepVal_qpow_eq A T lam d n x]
  -- per-sorted-index deviation μⱼ,ₙ - stepVal(μⱼ,ₙ) → 0
  have hdevj : ∀ j : Fin (Fintype.card (Fin d)),
      Tendsto (fun n => (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j
          - stepVal lam d ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j))
        atTop (𝓝 0) := by
    intro j
    have hjd : (j : ℕ) < d := lt_of_lt_of_eq j.isLt (Fintype.card_fin d)
    -- eventually stepVal(μⱼ,ₙ) = e^{λⱼ}, so the deviation is eventually μⱼ,ₙ - e^{λⱼ} → 0
    have hμ := hxev j
    -- eventually each block term at μⱼ,ₙ equals the same term at e^{λⱼ}
    have hterm : ∀ k ∈ Finset.Ico 1 d, ∀ᶠ n in atTop,
        (Real.exp (lam (k - 1)) - Real.exp (lam k)) *
            Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) (1 : ℝ → ℝ)
              ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j)
          = (Real.exp (lam (k - 1)) - Real.exp (lam k)) *
            Set.indicator (Set.Ioi (Real.exp ((lam k + lam (k - 1)) / 2))) (1 : ℝ → ℝ)
              (Real.exp (lam (j : ℕ))) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      obtain ⟨hk1, hkd⟩ := hk
      by_cases hgap : lam k < lam (k - 1)
      · -- gap: the eigenvalue is eventually on the same side of the threshold cₖ as e^{λⱼ}
        set ck := Real.exp ((lam k + lam (k - 1)) / 2) with hck
        by_cases hside : Real.exp (lam (j : ℕ)) < ck
        · -- e^{λⱼ} < cₖ, so eventually μⱼ,ₙ < cₖ; both indicators 0
          filter_upwards [hμ.eventually (eventually_lt_nhds hside)] with n hn
          rw [Set.indicator_of_notMem (by rw [Set.mem_Ioi, not_lt]; exact le_of_lt hn),
            Set.indicator_of_notMem (by rw [Set.mem_Ioi, not_lt]; exact le_of_lt hside)]
        · -- otherwise ck < e^{λⱼ} (equality is impossible at a gap), so eventually μⱼ,ₙ > cₖ
          have hgt : ck < Real.exp (lam (j : ℕ)) := by
            rcases lt_trichotomy (Real.exp (lam (j : ℕ))) ck with h | h | h
            · exact absurd h hside
            · -- equality impossible: lam j ≠ (lam k + lam(k-1))/2
              exfalso
              have hlamj : lam (j : ℕ) = (lam k + lam (k - 1)) / 2 := by
                have := congrArg Real.log h
                rwa [Real.log_exp, Real.log_exp] at this
              rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
              · have : lam (k - 1) ≤ lam (j : ℕ) := hanti (j : ℕ) (k - 1) (by omega) (by omega)
                rw [hlamj] at this; linarith
              · have : lam (j : ℕ) ≤ lam k := hanti k (j : ℕ) hjk hjd
                rw [hlamj] at this; linarith
            · exact h
          filter_upwards [hμ.eventually (eventually_gt_nhds hgt)] with n hn
          rw [Set.indicator_of_mem (by rw [Set.mem_Ioi]; exact hn),
            Set.indicator_of_mem (by rw [Set.mem_Ioi]; exact hgt), Pi.one_apply, Pi.one_apply]
      · -- non-gap: coefficient is 0
        have hle : lam k ≤ lam (k - 1) := hanti (k - 1) k (by omega) hkd
        have hcoef : Real.exp (lam (k - 1)) - Real.exp (lam k) = 0 := by
          have heqlam : lam (k - 1) = lam k := le_antisymm (not_lt.mp hgap) hle
          rw [heqlam]; ring
        filter_upwards with n
        rw [hcoef]; ring
    -- assemble: stepVal at μⱼ,ₙ equals stepVal at e^{λⱼ} = e^{λⱼ}
    have heq : ∀ᶠ n in atTop,
        (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j
            - stepVal lam d ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j)
          = (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j - Real.exp (lam (j : ℕ)) := by
      rw [← eventually_all_finset] at hterm
      filter_upwards [hterm] with n hn
      have hstepeq : stepVal lam d ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j)
          = stepVal lam d (Real.exp (lam (j : ℕ))) := by
        rw [stepVal, stepVal]
        congr 1
        exact Finset.sum_congr rfl hn
      rw [hstepeq, stepVal_exp_lam lam d hanti hjd]
    -- the target tendsto, via congruence with μⱼ,ₙ - e^{λⱼ} → 0
    have htgt : Tendsto (fun n => (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j
        - Real.exp (lam (j : ℕ))) atTop (𝓝 0) := by
      have := hμ.sub_const (Real.exp (lam (j : ℕ)))
      simpa using this
    exact htgt.congr' (heq.mono (fun n hn => hn.symm))
  -- deviation qpow_n - blockApprox_n → 0
  have hdev : Tendsto
      (fun n => qpow A T n x - cfc (stepVal lam d) (qpow A T n x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    -- squeeze: 0 ≤ ‖·‖ ≤ ∑ⱼ |devⱼ| → 0
    have hsum0 : Tendsto (fun n => ∑ j : Fin (Fintype.card (Fin d)),
        |(qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j
          - stepVal lam d ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j)|)
        atTop (𝓝 0) := by
      have hcomp : Tendsto (fun n => ∑ j : Fin (Fintype.card (Fin d)),
          |(qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j
            - stepVal lam d ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ j)|)
          atTop (𝓝 (∑ _j : Fin (Fintype.card (Fin d)), (0 : ℝ))) := by
        refine tendsto_finset_sum _ (fun j _ => ?_)
        have := (hdevj j).abs
        simpa using this
      simpa using hcomp
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum0
    exact norm_sub_cfc_le_sum_eigenvalue_dev (qpow A T n x) (qpow_isSelfAdjoint A T n x)
      (stepVal lam d)
  -- combine: qpow_n = (qpow_n - blockApprox_n) + blockApprox_n → 0 + Lblock
  refine ⟨Lblock, ?_⟩
  have hcombine : Tendsto (fun n => (qpow A T n x - cfc (stepVal lam d) (qpow A T n x))
      + cfc (stepVal lam d) (qpow A T n x)) atTop (𝓝 (0 + Lblock)) := by
    refine hdev.add ?_
    simp_rw [← hLn_eq]; exact hLblock
  simpa using hcombine

end Oseledets

end
