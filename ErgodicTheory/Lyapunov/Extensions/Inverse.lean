/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.Spectrum

/-!
# The inverse (time-reversed) singular-value spectrum

This module is purely *additive* on top of the spectrum object
`ErgodicTheory.exponents : Fin d → ℝ` (defined in `ErgodicTheory/Lyapunov/Spectrum.lean`). It
records the **inverse-matrix-cocycle** reciprocity: the singular values of `M⁻¹` are the
reciprocals, in reversed order, of the singular values of `M`, and consequently the Lyapunov
exponents of the *inverse cocycle* `n ↦ (cocycle A T n x)⁻¹` are the negatives, in reversed order,
of the exponents of `A`.

## The honest caveat on "time reversal"

With a *one-sided* (possibly non-invertible) base map `T`, this is the **inverse-matrix-cocycle**
statement only: it concerns the matrix inverse `(cocycle A T n x)⁻¹` of the forward cocycle
iterate, not a genuine two-sided time-reversed cocycle. The genuine time-reversed cocycle
`cocycle (fun y => (A (T⁻¹ y))⁻¹) T⁻¹` requires `T` to be invertible (an automorphism) with
`T⁻¹` measure-preserving; that two-sided development is deferred to the two-sided / backward
Oseledets work and is **not** attempted here. The reciprocity proved here is exactly the
matrix-level statement, which is what the existing one-sided machinery supports.

The inverse-integrability hypothesis `hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ` (already
part of the standing hypotheses) is precisely what makes the inverse spectrum exist: it is the
symmetric counterpart of `hint` that keeps both extremal exponents finite. We note this
explicitly because it is *the* hypothesis carrying the inverse spectrum.

## Main results

* `ErgodicTheory.singularValues_inv` — the **SVD reciprocal-reversed identity**: for an invertible
  matrix `M`, `σᵢ(M⁻¹) = (σ_{rev i}(M))⁻¹`, where `rev` is the order reversal on `Fin d`.
* `ErgodicTheory.singularValues_inv_mul` — the product form `σᵢ(M⁻¹) · σ_{rev i}(M) = 1`.
* `ErgodicTheory.tendsto_log_singularValue_inv_cocycle` — for each sorted index `i` and `μ`-a.e.
  `x`, the normalized log of the `i`-th singular value of the *inverse cocycle iterate*
  `(cocycle A T n x)⁻¹` converges to `- exponents … (rev i)`: the inverse exponents are the
  negatives in reversed order.
* `ErgodicTheory.topExponent_inv_eq_neg_bot` — the top exponent of the inverse cocycle equals the
  negative of the bottom exponent of `A`, tying the positive and negative ends of the spectrum.

## References

* L. Arnold, *Random Dynamical Systems*, Springer Monographs in Mathematics, 1998.
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58.
-/

open Module InnerProductSpace MeasureTheory Filter Topology
open scoped Matrix

namespace ErgodicTheory

/-! ## The eigenvalue reciprocal-reversal lemma (operator level) -/

section Eigenvalues

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-- If a self-adjoint operator `S` is diagonalized by the orthonormal basis `b` with (real)
diagonal entries `c`, then its characteristic polynomial is `∏ i, (X - C (c i))`. This is the
basis-independence of `charpoly` applied to a (not necessarily sorted) eigenbasis. -/
private theorem charpoly_eq_prod_of_diagonalizing (S : E →ₗ[ℝ] E)
    (b : OrthonormalBasis (Fin n) ℝ E) (c : Fin n → ℝ)
    (hSb : ∀ i, S (b i) = (c i : ℝ) • b i) :
    S.charpoly = ∏ i, (Polynomial.X - Polynomial.C (c i)) := by
  rw [← S.charpoly_toMatrix b.toBasis]
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis S = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hSb j,
      OrthonormalBasis.coe_toBasis_repr_apply, map_smul]
    simp only [OrthonormalBasis.repr_self, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hmat, Matrix.charpoly_diagonal]

/-- **Eigenvalue reciprocal-reversal.** Let `S` be a self-adjoint operator with all eigenvalues
strictly positive (hence invertible), and let `S'` be self-adjoint with `S' (b i) = (ev i)⁻¹ • b i`
on the (sorted) eigenbasis `b` of `S` — i.e. `S'` is the inverse of `S`. Then the sorted
eigenvalues of `S'` are the reciprocals of the eigenvalues of `S` in reversed order:
`eigenvalues(S') i = (eigenvalues(S) (rev i))⁻¹`. -/
private theorem eigenvalues_inv_eq_rev {S S' : E →ₗ[ℝ] E} (hS : S.IsSymmetric)
    (hS' : S'.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (hpos : ∀ i, 0 < hS.eigenvalues hn i)
    (hSS' : ∀ i, S' (hS.eigenvectorBasis hn i)
      = (hS.eigenvalues hn i)⁻¹ • hS.eigenvectorBasis hn i) (i : Fin n) :
    hS'.eigenvalues hn i = (hS.eigenvalues hn (Fin.rev i))⁻¹ := by
  set ev := hS.eigenvalues hn with hev
  -- The reversed-reciprocal function is antitone.
  have hanti : Antitone (fun j : Fin n => (ev (Fin.rev j))⁻¹) := by
    intro a b hab
    have hrev : ev (Fin.rev a) ≤ ev (Fin.rev b) :=
      hS.eigenvalues_antitone hn (Fin.rev_anti hab)
    exact inv_anti₀ (hpos (Fin.rev a)) hrev
  -- The characteristic polynomial of `S'` factors with reciprocal roots.
  have hchar : S'.charpoly = ∏ j, (Polynomial.X - Polynomial.C ((ev j)⁻¹)) :=
    charpoly_eq_prod_of_diagonalizing S' (hS.eigenvectorBasis hn) (fun j => (ev j)⁻¹) hSS'
  -- Its roots are the reciprocal eigenvalues (with multiplicity).
  have hroots : S'.charpoly.roots = Multiset.map (fun j : Fin n => (ev j)⁻¹) Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  -- Compare the two `List.ofFn` enumerations: both sortedGE, same multiset.
  have hlist : List.ofFn (hS'.eigenvalues hn)
      = List.ofFn (fun j : Fin n => (ev (Fin.rev j))⁻¹) := by
    rw [← hS'.sort_roots_charpoly_eq_eigenvalues hn]
    -- The sorted roots and the antitone `ofFn` are two sortedGE lists with equal multiset.
    refine List.Perm.eq_of_sortedGE (Multiset.pairwise_sort _ _).sortedGE hanti.sortedGE_ofFn ?_
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq, hroots]
    -- `RCLike.re` is the identity on `ℝ`; `rev` is a bijection on `univ`.
    rw [Multiset.map_map]
    -- RHS: `↑(List.ofFn h) = univ.val.map h`, then drop `rev` by reindexing along `Fin.revPerm`.
    rw [← Fin.univ_val_map]
    conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
    refine Multiset.map_congr rfl (fun j _ => ?_)
    simp
  -- read off the per-index equality
  exact congrFun (List.ofFn_inj.mp hlist) i

/-- **Eigenvalue reciprocal-reversal, inverse form.** If `S` is self-adjoint with all eigenvalues
strictly positive and `S'` is a self-adjoint left inverse of `S` (`S' ∘ₗ S = id`), then
`eigenvalues(S') i = (eigenvalues(S) (rev i))⁻¹`. -/
private theorem eigenvalues_of_comp_eq_id {S S' : E →ₗ[ℝ] E} (hS : S.IsSymmetric)
    (hS' : S'.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (hpos : ∀ i, 0 < hS.eigenvalues hn i) (hSS' : S' ∘ₗ S = LinearMap.id) (i : Fin n) :
    hS'.eigenvalues hn i = (hS.eigenvalues hn (Fin.rev i))⁻¹ := by
  refine eigenvalues_inv_eq_rev hS hS' hn hpos (fun j => ?_) i
  -- From `S(b j) = ev j • b j` and `S'(S(b j)) = b j` we get `S'(b j) = (ev j)⁻¹ • b j`.
  have hSb : S (hS.eigenvectorBasis hn j) = (hS.eigenvalues hn j : ℝ) • hS.eigenvectorBasis hn j :=
    hS.apply_eigenvectorBasis hn j
  have hround : S' (S (hS.eigenvectorBasis hn j)) = hS.eigenvectorBasis hn j := by
    rw [← LinearMap.comp_apply, hSS', LinearMap.id_apply]
  rw [hSb, map_smul] at hround
  have hne : (hS.eigenvalues hn j : ℝ) ≠ 0 := ne_of_gt (hpos j)
  rw [eq_comm, inv_smul_eq_iff₀ hne]
  exact hround.symm

end Eigenvalues

/-! ## The SVD reciprocal-reversed identity (matrix level) -/

section Matrix

variable {d : ℕ} [NeZero d]

open scoped Matrix.Norms.L2Operator

omit [NeZero d] in
/-- `toEuclideanLin` turns a matrix product into a composition of linear maps. -/
private theorem toEuclideanLin_mul' (M N : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.toEuclideanLin (M * N)
      = (Matrix.toEuclideanLin M) ∘ₗ (Matrix.toEuclideanLin N) := by
  ext v i
  simp only [Matrix.toLpLin_apply, LinearMap.comp_apply, Matrix.mulVec_mulVec]

/-- **The SVD reciprocal-reversed identity.** For an invertible matrix `M`, the singular values
of `M⁻¹` are the reciprocals, in reversed order, of the singular values of `M`:
`σᵢ(M⁻¹) = (σ_{rev i}(M))⁻¹`.

The proof routes the squared singular values through the Gram operators: `σᵢ(M⁻¹)²` is the
`i`-th sorted eigenvalue of `(M⁻¹)ᵀ M⁻¹`, which is the inverse of `M Mᵀ`; the eigenvalue
reciprocal-reversal lemma identifies this with the reciprocal-reversed eigenvalue of `M Mᵀ`,
and `M Mᵀ` is cospectral with the Gram matrix `Mᵀ M` (by `Matrix.charpoly_mul_comm`), whose
`(rev i)`-th eigenvalue is `σ_{rev i}(M)²`. Taking square roots (all quantities nonnegative)
yields the claim. -/
theorem singularValues_inv {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.det ≠ 0) (i : Fin d) :
    (Matrix.toEuclideanLin M⁻¹).singularValues i
      = ((Matrix.toEuclideanLin M).singularValues (Fin.rev i))⁻¹ := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set fM := Matrix.toEuclideanLin M with hfM
  set fI := Matrix.toEuclideanLin M⁻¹ with hfI
  -- The two Gram operators (self-adjoint).
  set Sinv := LinearMap.adjoint fI ∘ₗ fI with hSinv
  set R := Matrix.toEuclideanLin (M * Mᵀ) with hR
  have hSinv_eq : Sinv = Matrix.toEuclideanLin ((M⁻¹)ᵀ * M⁻¹) := by
    rw [hSinv, hfI, adjoint_comp_self_eq_gram]
  have hSinv_sym : Sinv.IsSymmetric := fI.isSymmetric_adjoint_comp_self
  have hR_eq : R = LinearMap.adjoint (Matrix.toEuclideanLin Mᵀ) ∘ₗ Matrix.toEuclideanLin Mᵀ := by
    rw [adjoint_comp_self_eq_gram, hR, Matrix.transpose_transpose]
  have hR_sym : R.IsSymmetric := by
    rw [hR_eq]; exact (Matrix.toEuclideanLin Mᵀ).isSymmetric_adjoint_comp_self
  -- The Gram operator of `M`, self-adjoint.
  set G := LinearMap.adjoint fM ∘ₗ fM with hG
  have hG_eq : G = Matrix.toEuclideanLin (Mᵀ * M) := by rw [hG, hfM, adjoint_comp_self_eq_gram]
  have hG_sym : G.IsSymmetric := fM.isSymmetric_adjoint_comp_self
  -- squared singular values are the Gram eigenvalues (used both ways below).
  have hsqI : fI.singularValues i ^ 2 = hSinv_sym.eigenvalues hfin i :=
    fI.sq_singularValues_fin hfin i
  have hsqM : ∀ j : Fin d, fM.singularValues j ^ 2 = hG_sym.eigenvalues hfin j :=
    fun j => fM.sq_singularValues_fin hfin j
  -- `M` (hence `fM`) is injective, so all its singular values are positive.
  have hMpos : ∀ j : Fin d, 0 < fM.singularValues j := by
    intro j
    have hinj : Function.Injective fM := by rw [hfM]; exact injective_toEuclideanLin hM
    rw [hfM] at hinj
    exact ((Matrix.toEuclideanLin M).injective_iff_forall_lt_finrank_singularValues_pos.mp hinj)
      j (by rw [hfin]; exact j.isLt)
  -- `R = M Mᵀ` is cospectral with the Gram matrix `Mᵀ M = adjoint fM ∘ fM` (charpoly_mul_comm).
  have hcharpoly : ∀ N : Matrix (Fin d) (Fin d) ℝ,
      (Matrix.toEuclideanLin N).charpoly = N.charpoly := by
    intro N
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]
  have hcospec : hR_sym.eigenvalues hfin = hG_sym.eigenvalues hfin := by
    rw [LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff hR_sym hfin hG_sym hfin, hR, hG_eq,
      hcharpoly, hcharpoly, Matrix.charpoly_mul_comm]
  -- `R` is positive definite: cospectral with `G`, whose eigenvalues are the positive `σⱼ²`.
  have hRpos : ∀ j, 0 < hR_sym.eigenvalues hfin j := by
    intro j
    rw [hcospec, ← hsqM j]
    exact pow_pos (hMpos j) 2
  -- `Sinv` is a left inverse of `R`: `((M⁻¹)ᵀ M⁻¹) (M Mᵀ) = 1`.
  have hcomp : Sinv ∘ₗ R = LinearMap.id := by
    rw [hSinv_eq, hR, ← toEuclideanLin_mul']
    have hmat : (M⁻¹)ᵀ * M⁻¹ * (M * Mᵀ) = 1 := by
      have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hM)
      have h2 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hM)
      calc (M⁻¹)ᵀ * M⁻¹ * (M * Mᵀ)
          = (M⁻¹)ᵀ * (M⁻¹ * M) * Mᵀ := by noncomm_ring
        _ = (M⁻¹)ᵀ * Mᵀ := by rw [h1, Matrix.mul_one]
        _ = (M * M⁻¹)ᵀ := by rw [← Matrix.transpose_mul]
        _ = 1 := by rw [h2, Matrix.transpose_one]
    rw [hmat]
    ext v i; simp
  -- `eigenvalues(Sinv) i = (eigenvalues(R) (rev i))⁻¹`.
  have hev_inv : hSinv_sym.eigenvalues hfin i = (hR_sym.eigenvalues hfin (Fin.rev i))⁻¹ :=
    eigenvalues_of_comp_eq_id hR_sym hSinv_sym hfin hRpos hcomp i
  -- square the goal: `σᵢ(M⁻¹)² = (σ_{rev i}(M)²)⁻¹`.
  have hsq_goal : fI.singularValues i ^ 2 = ((fM.singularValues (Fin.rev i))⁻¹) ^ 2 := by
    rw [hsqI, hev_inv, hcospec, inv_pow, hsqM (Fin.rev i)]
  have hInn : 0 ≤ fI.singularValues i := fI.singularValues_nonneg i
  have hMinn : 0 ≤ (fM.singularValues (Fin.rev i))⁻¹ := le_of_lt (inv_pos.mpr (hMpos (Fin.rev i)))
  exact (sq_eq_sq₀ hInn hMinn).mp hsq_goal

/-- **The SVD reciprocity, product form.** For an invertible matrix `M`, the `i`-th singular
value of `M⁻¹` and the `(rev i)`-th singular value of `M` are reciprocal:
`σᵢ(M⁻¹) · σ_{rev i}(M) = 1`. -/
theorem singularValues_inv_mul {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.det ≠ 0) (i : Fin d) :
    (Matrix.toEuclideanLin M⁻¹).singularValues i
      * (Matrix.toEuclideanLin M).singularValues (Fin.rev i) = 1 := by
  have hMpos : 0 < (Matrix.toEuclideanLin M).singularValues (Fin.rev i) := by
    have hinj : Function.Injective (Matrix.toEuclideanLin M) := injective_toEuclideanLin hM
    exact ((Matrix.toEuclideanLin M).injective_iff_forall_lt_finrank_singularValues_pos.mp hinj)
      (Fin.rev i) (by rw [finrank_euclideanSpace_fin]; exact (Fin.rev i).isLt)
  rw [singularValues_inv hM i, inv_mul_cancel₀ (ne_of_gt hMpos)]

end Matrix

/-! ## The inverse cocycle's exponents (cocycle level) -/

section Cocycle

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]
variable {μ : Measure X} {T : X → X}
variable [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

/-- **The inverse cocycle's singular-value exponents.** For each sorted index `i` and `μ`-a.e.
`x`, the normalized log of the `i`-th singular value of the *inverse cocycle iterate*
`(cocycle A T n x)⁻¹` converges to `- exponents … (rev i)`: the Lyapunov exponents of the
inverse(-matrix) cocycle are the negatives, in reversed order, of the exponents of `A`.

This is the singular-value reciprocity `singularValues_inv` (applied to the invertible
iterate `cocycle A T n x`) combined with `exponents_tendsto_log_singularValue`. See the module
docstring for the honest caveat: with a one-sided base map `T` this is the inverse-matrix
cocycle, not the genuine two-sided time-reversed cocycle. -/
theorem tendsto_log_singularValue_inv_cocycle (i : Fin d) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)⁻¹).singularValues (i : ℕ)))
      atTop (𝓝 (- exponents hT hA hAmeas hint hint' (Fin.rev i))) := by
  -- a.e., the forward `(rev i)`-th singular-value exponent converges to `exponents (rev i)`.
  filter_upwards [exponents_tendsto_log_singularValue hT hA hAmeas hint hint' (Fin.rev i)]
    with x hx
  -- rewrite the inverse singular value via the reciprocal-reversed identity
  have hrw : ∀ n : ℕ, (n : ℝ)⁻¹ *
      Real.log ((Matrix.toEuclideanLin (cocycle A T n x)⁻¹).singularValues (i : ℕ))
      = - ((n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues ((Fin.rev i) : ℕ))) := by
    intro n
    have hdet : (cocycle A T n x).det ≠ 0 := det_cocycle_ne_zero hA n x
    have hpos : 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues ((Fin.rev i) : ℕ) :=
      singularValues_cocycle_pos hA n x (Fin.rev i).isLt
    rw [show ((i : ℕ)) = ((i : Fin d) : ℕ) from rfl, singularValues_inv hdet i,
      show ((Fin.rev i : Fin d) : ℕ) = ((Fin.rev i) : ℕ) from rfl, Real.log_inv]
    ring
  have htend : Tendsto
      (fun n : ℕ => - ((n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues ((Fin.rev i) : ℕ))))
      atTop (𝓝 (- exponents hT hA hAmeas hint hint' (Fin.rev i))) := hx.neg
  exact htend.congr (fun n => (hrw n).symm)

/-- **Positive ↔ negative spectrum bridge.** The top exponent of the inverse(-matrix) cocycle
equals the negative of the bottom exponent of `A`: writing `λ_bot := exponents … (last index)`
for the smallest Lyapunov exponent of `A`, the inverse cocycle's `0`-th (largest) exponent is
`- λ_bot`. This ties the bottom of the forward spectrum to the top of the reversed spectrum,
complementing the sign characterizations of `ExponentSums`. -/
theorem topExponent_inv_eq_neg_bot :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)⁻¹).singularValues 0))
      atTop (𝓝 (- exponents hT hA hAmeas hint hint'
        ⟨d - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne d)) one_pos⟩)) := by
  have h := tendsto_log_singularValue_inv_cocycle hT hA hAmeas hint hint'
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)
  -- `rev 0 = ⟨d-1, _⟩` is the bottom (smallest) index.
  have hrev : Fin.rev (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)
      = ⟨d - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne d)) one_pos⟩ := by
    ext; simp [Fin.rev]
  rw [hrev] at h
  exact h

end Cocycle

end ErgodicTheory
