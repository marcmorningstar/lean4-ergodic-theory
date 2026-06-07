/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator norm of the exterior power and the product of singular values

For finite-dimensional real inner product spaces `E`, `F`, this module studies the operator
norm of the `k`-th exterior power `⋀^k f` of a linear map `f : E →ₗ[ℝ] F`, and connects it to
the singular values of `f`.

The headline facts are:

* `exteriorOpNorm_comp_le` — **submultiplicativity** of the exterior-power operator norm under
  composition. This is pure functoriality (`exteriorPower.map_comp`) combined with the
  submultiplicativity of the continuous-linear-map operator norm, and is fully proved.
* `exteriorOpNorm_eq_prod_singularValues` — the bridge identifying the exterior operator norm
  with the product of the top-`k` singular values `∏_{i<k} σᵢ(f)`.
* `prod_singularValues_comp_le` — the consequence
  `∏_{i<k} σᵢ(g ∘ f) ≤ (∏_{i<k} σᵢ(g)) · (∏_{i<k} σᵢ(f))`, feeding the Oseledets
  singular-value exponents (via Kingman) in the next module.

## Implementation notes — the diamond trap

The type `⋀[ℝ]^k E` is definitionally `↥(Submodule …)` and already carries an `AddCommGroup`
instance coming from the ambient submodule. Asserting or installing a *fresh*
`NormedAddCommGroup (⋀[ℝ]^k E)` would create an `AddCommGroup`/topology **diamond** that breaks
even `IsTopologicalAddGroup` synthesis on `⋀^k E`.

To stay diamond-free we never put a normed structure on `⋀^k E`. Instead we carry an explicit
**linear trivialization** `ε : ⋀^k E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)` as *data* and measure the
operator norm of the conjugated map in the genuine Euclidean target. The canonical such
trivialization (`exteriorTrivialization`) exists because `⋀^k E` is a finite free `ℝ`-module.
-/

open Module InnerProductSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace ExteriorNorm

/-! ## The submultiplicativity engine

We carry explicit linear trivializations `ε : ⋀^k · ≃ₗ EuclideanSpace ℝ (Fin n)` as data and
take the operator norm of the conjugated exterior map in the genuine Euclidean target. -/

section Engine

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {k nE nF nG : ℕ}

/-- The `k`-th exterior map `⋀^k f`, conjugated through trivializations of source and target
exterior powers into genuine Euclidean spaces. -/
def conjExteriorMap (k : ℕ)
    (εE : (⋀[ℝ]^k E) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nE))
    (εF : (⋀[ℝ]^k F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nF)) (f : E →ₗ[ℝ] F) :
    EuclideanSpace ℝ (Fin nE) →ₗ[ℝ] EuclideanSpace ℝ (Fin nF) :=
  εF.toLinearMap ∘ₗ (exteriorPower.map k f) ∘ₗ εE.symm.toLinearMap

/-- The exterior-power operator norm of `f`, measured through the trivializations `εE`, `εF`.
When `εE`, `εF` are the orthonormal-wedge isometries for the Hodge inner product, this is the
genuine `‖⋀^k f‖`. -/
def exteriorOpNorm (k : ℕ)
    (εE : (⋀[ℝ]^k E) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nE))
    (εF : (⋀[ℝ]^k F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nF)) (f : E →ₗ[ℝ] F) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (conjExteriorMap k εE εF f)‖

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
lemma exteriorOpNorm_nonneg (k : ℕ)
    (εE : (⋀[ℝ]^k E) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nE))
    (εF : (⋀[ℝ]^k F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nF)) (f : E →ₗ[ℝ] F) :
    0 ≤ exteriorOpNorm k εE εF f :=
  norm_nonneg _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- **Submultiplicativity of the exterior-power operator norm.** Pure functoriality
(`exteriorPower.map_comp`, with the middle trivialization telescoping) together with the
submultiplicativity of the continuous-linear-map operator norm (`opNorm_comp_le`). -/
theorem exteriorOpNorm_comp_le (k : ℕ)
    (εE : (⋀[ℝ]^k E) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nE))
    (εF : (⋀[ℝ]^k F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nF))
    (εG : (⋀[ℝ]^k G) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin nG))
    (f : E →ₗ[ℝ] F) (g : F →ₗ[ℝ] G) :
    exteriorOpNorm k εE εG (g ∘ₗ f)
      ≤ exteriorOpNorm k εF εG g * exteriorOpNorm k εE εF f := by
  unfold exteriorOpNorm
  -- `⋀^k (g ∘ f)` conjugated telescopes: the inner `εF⁻¹ ∘ εF` cancels.
  have hcomp : conjExteriorMap k εE εG (g ∘ₗ f)
      = (conjExteriorMap k εF εG g) ∘ₗ (conjExteriorMap k εE εF f) := by
    unfold conjExteriorMap
    rw [exteriorPower.map_comp]
    ext x
    simp [LinearMap.comp_apply]
  have key : LinearMap.toContinuousLinearMap (conjExteriorMap k εE εG (g ∘ₗ f))
      = (LinearMap.toContinuousLinearMap (conjExteriorMap k εF εG g)).comp
          (LinearMap.toContinuousLinearMap (conjExteriorMap k εE εF f)) := by
    apply ContinuousLinearMap.coe_injective
    ext x
    simp only [LinearMap.coe_toContinuousLinearMap]
    rw [hcomp]; rfl
  rw [key]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end Engine

/-! ## Existence of trivializations

Every `⋀^k E` (a finite free `ℝ`-module) admits a linear equiv to a Euclidean space, via its
finrank basis. -/

section Trivialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A canonical linear trivialization of `⋀^k E` into a Euclidean space, via the finrank basis. -/
def exteriorTrivialization (k : ℕ) :
    (⋀[ℝ]^k E) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :=
  (Module.finBasis ℝ (⋀[ℝ]^k E)).equivFun ≪≫ₗ (EuclideanSpace.equiv _ ℝ).symm.toLinearEquiv

end Trivialization

/-! ## The Hodge trivialization

For an inner product space `E`, the **Hodge trivialization** of `⋀^k E` is the linear equiv to
`EuclideanSpace` that sends the orthonormal *wedge basis* — the `k`-fold wedges
`e_{i₁} ∧ ⋯ ∧ e_{i_k}` of the standard orthonormal basis `{eᵢ}` of `E` — to the standard
Euclidean basis. It is a concrete piece of `data` (no inner product is installed on `⋀^k E`,
avoiding the `AddCommGroup`/topology diamond). Measuring the exterior operator norm through this
trivialization gives the genuine `‖⋀^k f‖` for the Hodge inner product. -/

section Hodge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Classical in
/-- The wedge basis of `⋀^k E` induced by the standard orthonormal basis of `E`: its elements are
the `k`-fold wedge products of distinct standard basis vectors. As a `Basis` it is `data`, and
under the Hodge inner product it is orthonormal. -/
def wedgeBasis (k : ℕ) :
    Basis (Set.powersetCard (Fin (Module.finrank ℝ E)) k) ℝ (⋀[ℝ]^k E) :=
  (stdOrthonormalBasis ℝ E).toBasis.exteriorPower k

open scoped Classical in
/-- The reindexing equiv `powersetCard (Fin (finrank E)) k ≃ Fin (finrank (⋀^k E))` witnessing
that both index sets have the same cardinality `(finrank E).choose k`. -/
def wedgeIndexEquiv (k : ℕ) :
    Set.powersetCard (Fin (Module.finrank ℝ E)) k ≃ Fin (Module.finrank ℝ (⋀[ℝ]^k E)) :=
  Fintype.equivFinOfCardEq (by
    rw [exteriorPower.finrank_eq, ← Nat.card_eq_fintype_card, Set.powersetCard.card,
      Nat.card_eq_fintype_card, Fintype.card_fin])

open scoped Classical in
/-- The **Hodge trivialization** of `⋀^k E`: the linear equiv to a Euclidean space sending the
orthonormal wedge basis to the standard Euclidean basis. -/
def hodgeTrivialization (k : ℕ) :
    (⋀[ℝ]^k E) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :=
  ((wedgeBasis (E := E) k).reindex (wedgeIndexEquiv (E := E) k)).equivFun
    ≪≫ₗ (EuclideanSpace.equiv _ ℝ).symm.toLinearEquiv

end Hodge

/-! ## The bridge to singular values

`‖⋀^k f‖ = ∏_{i<k} σᵢ(f)`, measured through the Hodge trivializations of source and target.
Mathematically: an SVD of `f` diagonalizes `⋀^k f` on the orthonormal bases of `k`-fold wedges of
singular vectors; the operator norm is attained on the top wedge `u₀ ∧ ⋯ ∧ u_{k-1}`, whose image
has norm `∏_{i<k} σᵢ(f)` (the largest wedge product, since `σ` is antitone). This requires the
SVD-decomposition packaging, the orthonormality of the wedge basis for the Hodge inner product,
and a diagonal-operator-norm computation, none of which are currently in Mathlib. -/

section Bridge

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **SVD orthogonality core.** Let `u` be the orthonormal eigenvector basis of the symmetric,
positive map `adjoint f ∘ₗ f`. Then the images `{f (uᵢ)}` of these *right singular vectors* are
pairwise orthogonal, and `‖f (uᵢ)‖² = σᵢ(f)²`. Concretely, `⟪f uᵢ, f uⱼ⟫ = δᵢⱼ · σᵢ(f)²`.

This is the analytic heart of the singular value decomposition: rescaling the nonzero `f uᵢ` to
unit length yields the left singular vectors `wᵢ` with `f uᵢ = σᵢ · wᵢ`. -/
private lemma inner_apply_eigenvectorBasis_eq (f : E →ₗ[ℝ] F) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (i j : Fin n) :
    (inner ℝ (f ((f.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i))
      (f ((f.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) j)) : ℝ)
      = if i = j then (f.singularValues i) ^ 2 else 0 := by
  set hT := f.isSymmetric_adjoint_comp_self
  set u := hT.eigenvectorBasis hn
  have key : (inner ℝ (f (u i)) (f (u j)) : ℝ)
      = inner ℝ ((LinearMap.adjoint f ∘ₗ f) (u i)) (u j) := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [key, show (LinearMap.adjoint f ∘ₗ f) (u i) = (hT.eigenvalues hn i : ℝ) • u i from
        hT.apply_eigenvectorBasis hn i, inner_smul_left, u.inner_eq_ite i j,
      f.sq_singularValues_fin hn i]
  simp only [RCLike.conj_to_real]
  split_ifs with h <;> simp

/-- The norm of the image of a right singular vector is the corresponding singular value:
`‖f uᵢ‖ = σᵢ(f)`. Immediate from the SVD orthogonality core. -/
private lemma norm_apply_eigenvectorBasis (f : E →ₗ[ℝ] F) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (i : Fin n) :
    ‖f ((f.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i)‖ = f.singularValues i := by
  have h := inner_apply_eigenvectorBasis_eq f hn i i
  simp only [if_true] at h
  have hsq : ‖f ((f.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i)‖ ^ 2
      = f.singularValues i ^ 2 := by
    rw [real_inner_self_eq_norm_sq] at h; linarith
  nlinarith [norm_nonneg (f ((f.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i)),
    f.singularValues_nonneg i, hsq]

/-! ### The det-Gram (Hodge) bilinear form and orthonormal-wedge trivializations

We carry the Hodge inner product on `⋀^k E` as a plain bilinear *form* `hodgeForm` (never as a
typeclass instance, to avoid the `AddCommGroup`/topology diamond). It is defined by reusing the
exterior-power dual pairing composed with the inner-product-to-dual map `innerₗ`, so on `ιMulti`
families it is the determinant of the Gram matrix `det ⟪vᵢ, wⱼ⟫`. -/

/-- The det-Gram (Hodge) bilinear form on `⋀^k E`, defined via the exterior dual pairing and the
inner-product-to-dual map `innerₗ E`. -/
private def hodgeForm (k : ℕ) : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k E) →ₗ[ℝ] ℝ where
  toFun ω := exteriorPower.pairingDual ℝ E k (exteriorPower.map k (innerₗ E) ω)
  map_add' x y := by simp [map_add]
  map_smul' c x := by simp [map_smul]

private lemma hodgeForm_apply (k : ℕ) (ω η : ⋀[ℝ]^k E) :
    hodgeForm k ω η
      = exteriorPower.pairingDual ℝ E k (exteriorPower.map k (innerₗ E) ω) η := rfl

/-- On `ιMulti` families, the Hodge form is the determinant of the Gram matrix `⟪vⱼ, wᵢ⟫`. -/
private lemma hodgeForm_ιMulti (k : ℕ) (v w : Fin k → E) :
    hodgeForm k (exteriorPower.ιMulti ℝ k v) (exteriorPower.ιMulti ℝ k w)
      = (Matrix.of fun i j => (inner ℝ (v j) (w i) : ℝ)).det := by
  rw [hodgeForm_apply, exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  simp [innerₗ_apply_apply]

/-- The bilinear map `(ω, η) ↦ hodgeForm (⋀^k Q ω) (⋀^k Q η)`. -/
private def hodgeFormComp (k : ℕ) (Q : E →ₗ[ℝ] F) :
    (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k E) →ₗ[ℝ] ℝ :=
  (hodgeForm k).compl₁₂ (exteriorPower.map k Q) (exteriorPower.map k Q)

/-- **Kernel (ii): the compound of an orthogonal map is orthogonal.** `⋀^k Q` preserves the Hodge
form whenever `Q` is a linear isometry (`⟪Q x, Q y⟫ = ⟪x, y⟫`). On `ιMulti` families this is the
identity `det ⟪Q vⱼ, Q wᵢ⟫ = det ⟪vⱼ, wᵢ⟫`. -/
private lemma hodgeForm_map_isometry (k : ℕ) (Q : E →ₗ[ℝ] F)
    (hQ : ∀ x y : E, (inner ℝ (Q x) (Q y) : ℝ) = inner ℝ x y) :
    hodgeFormComp k Q = hodgeForm (E := E) k := by
  ext v w
  simp only [hodgeFormComp, LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
    exteriorPower.map_apply_ιMulti]
  rw [hodgeForm_ιMulti, hodgeForm_ιMulti]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  exact hQ _ _

open scoped Classical in
/-- For an orthonormal basis `b`, the coordinate dual `b.toBasis.coord i` equals
`innerₗ E (b i) = ⟪b i, ·⟫`. -/
private lemma innerₗ_eq_coord {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (i : ι) :
    innerₗ E (b i) = b.toBasis.coord i := by
  ext x
  rw [innerₗ_apply_apply, Basis.coord_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]

open scoped Classical in
/-- **The wedge basis of an orthonormal basis is orthonormal for the Hodge form.** This is the
det-Gram of the identity Gram matrix, packaged through the exterior dual pairing
`ιMultiDual_apply_diag`/`_apply_nondiag`. -/
private lemma hodgeForm_wedgeBasis {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ E) (k : ℕ) (s t : Set.powersetCard ι k) :
    hodgeForm k (b.toBasis.exteriorPower k s) (b.toBasis.exteriorPower k t)
      = if s = t then 1 else 0 := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
  have hcoord : (innerₗ E) ∘ (b.toBasis) = b.toBasis.coord := by
    ext i
    rw [Function.comp_apply, b.coe_toBasis, innerₗ_eq_coord]
  have key : hodgeForm k (exteriorPower.ιMulti_family ℝ k b.toBasis s)
      = exteriorPower.ιMultiDual ℝ k b.toBasis s := by
    show exteriorPower.pairingDual ℝ E k
        (exteriorPower.map k (innerₗ E) (exteriorPower.ιMulti_family ℝ k b.toBasis s))
      = exteriorPower.ιMultiDual ℝ k b.toBasis s
    rw [exteriorPower.map_apply_ιMulti_family, hcoord, exteriorPower.ιMultiDual]
  rw [LinearMap.congr_fun key]
  by_cases hst : s = t
  · subst hst
    rw [exteriorPower.ιMultiDual_apply_diag]; simp
  · rw [exteriorPower.ιMultiDual_apply_nondiag ℝ k b.toBasis s t hst]; simp [hst]

section OnbTriv

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
/-- Reindexing `powersetCard ι k ≃ Fin (finrank (⋀^k E))` for an o.n. basis `b` indexed by `ι`. -/
private def wIndexEquiv (b : OrthonormalBasis ι ℝ E) (k : ℕ) :
    Set.powersetCard ι k ≃ Fin (Module.finrank ℝ (⋀[ℝ]^k E)) :=
  Fintype.equivFinOfCardEq (by
    rw [exteriorPower.finrank_eq, ← Nat.card_eq_fintype_card, Set.powersetCard.card,
      Nat.card_eq_fintype_card]
    congr 1
    exact (Module.finrank_eq_card_basis b.toBasis).symm)

open scoped Classical in
/-- The wedge trivialization attached to an arbitrary orthonormal basis `b` of `E`. -/
private def onbTriv (b : OrthonormalBasis ι ℝ E) (k : ℕ) :
    (⋀[ℝ]^k E) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :=
  ((b.toBasis.exteriorPower k).reindex (wIndexEquiv b k)).equivFun
    ≪≫ₗ (EuclideanSpace.equiv _ ℝ).symm.toLinearEquiv

open scoped Classical in
private lemma onbTriv_apply (b : OrthonormalBasis ι ℝ E) (k : ℕ) (x : ⋀[ℝ]^k E)
    (i : Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :
    onbTriv b k x i = ((b.toBasis.exteriorPower k).reindex (wIndexEquiv b k)).repr x i := by
  simp only [onbTriv, LinearEquiv.trans_apply, Basis.equivFun_apply]; rfl

open scoped Classical in
/-- **Parseval for the Hodge form:** in the wedge basis of an o.n. basis it diagonalises. -/
private lemma hodgeForm_eq_sum_repr (b : OrthonormalBasis ι ℝ E) (k : ℕ) (x y : ⋀[ℝ]^k E) :
    hodgeForm k x y
      = ∑ s, (((b.toBasis.exteriorPower k).repr x) s)
          * (((b.toBasis.exteriorPower k).repr y) s) := by
  classical
  conv_lhs => rw [← (b.toBasis.exteriorPower k).sum_repr x,
    ← (b.toBasis.exteriorPower k).sum_repr y]
  rw [map_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply, map_sum, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single s]
  · rw [hodgeForm_wedgeBasis]; simp; ring
  · intro t _ hts; rw [hodgeForm_wedgeBasis]; simp [hts]
  · intro h; simp at h

open scoped Classical in
/-- **The trivialization is a Hodge isometry:** the L2 inner product of trivialized vectors equals
the Hodge form. -/
private lemma inner_onbTriv (b : OrthonormalBasis ι ℝ E) (k : ℕ) (x y : ⋀[ℝ]^k E) :
    (inner ℝ (onbTriv b k x) (onbTriv b k y) : ℝ) = hodgeForm k x y := by
  classical
  rw [PiLp.inner_apply, hodgeForm_eq_sum_repr b k x y]
  simp only [RCLike.inner_apply, conj_trivial, onbTriv_apply]
  refine Fintype.sum_equiv (wIndexEquiv b k).symm _ _ (fun i => ?_)
  rw [Basis.repr_reindex_apply, Basis.repr_reindex_apply, mul_comm]

end OnbTriv

section OnbChange

variable {ιE ιE' ιF ιF' : Type*}
  [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
  [Fintype ιF] [LinearOrder ιF] [Fintype ιF'] [LinearOrder ιF']

open scoped Classical in
/-- **Kernel (i)+(ii) assembled:** change-of-coordinates between two o.n.-basis wedge
trivializations of the *same* space is an L2 isometry (the compound `⋀^k Q`). The two bases may be
indexed differently; only the space `E` (hence `finrank (⋀^k E)`) matters. -/
private def onbChange (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E)))
      ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :=
  LinearEquiv.isometryOfInner
    ((onbTriv b k).symm ≪≫ₗ (onbTriv b' k)) (fun p q => by
      simp only [LinearEquiv.trans_apply]
      rw [inner_onbTriv b' k, ← inner_onbTriv b k, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])

open scoped Classical in
private lemma onbChange_apply (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ)
    (p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E)))) :
    onbChange b b' k p = onbTriv b' k ((onbTriv b k).symm p) := rfl

open scoped Classical in
/-- **Operator-norm invariance under change of orthonormal-wedge trivialization.** Replacing the
source/target o.n.-basis trivializations (possibly indexed differently) conjugates
`conjExteriorMap` by the L2 isometries `onbChange`, leaving the operator norm unchanged. -/
private lemma exteriorOpNorm_onbTriv_eq (bE : OrthonormalBasis ιE ℝ E)
    (bE' : OrthonormalBasis ιE' ℝ E)
    (bF : OrthonormalBasis ιF ℝ F) (bF' : OrthonormalBasis ιF' ℝ F) (k : ℕ) (f : E →ₗ[ℝ] F) :
    exteriorOpNorm k (onbTriv bE k) (onbTriv bF k) f
      = exteriorOpNorm k (onbTriv bE' k) (onbTriv bF' k) f := by
  set g := conjExteriorMap k (onbTriv bE k) (onbTriv bF k) f with hg
  set g' := conjExteriorMap k (onbTriv bE' k) (onbTriv bF' k) f with hg'
  have hrel : LinearMap.toContinuousLinearMap g'
      = (onbChange bF bF' k).toLinearIsometry.toContinuousLinearMap.comp
          ((LinearMap.toContinuousLinearMap g).comp
            (onbChange bE' bE k).toLinearIsometry.toContinuousLinearMap) := by
    refine ContinuousLinearMap.ext (fun p => ?_)
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap', LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
    simp only [hg, hg', conjExteriorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      onbChange_apply, LinearEquiv.symm_apply_apply]
  rw [exteriorOpNorm, exteriorOpNorm, hrel,
    LinearIsometry.norm_toContinuousLinearMap_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end OnbChange

/-! ### Operator norm of a map with orthogonal images of an orthonormal basis -/

/-- `‖g p‖² = ∑ i, (p i)² · c i` for a Euclidean map `g` whose images of the standard basis are
pairwise orthogonal with `⟪g eᵢ, g eⱼ⟫ = if i = j then c i else 0`. -/
private lemma normSq_apply_of_ortho {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {N : ℕ} (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] W) (c : Fin N → ℝ)
    (hortho : ∀ i j, (inner ℝ (g (EuclideanSpace.basisFun (Fin N) ℝ i))
      (g (EuclideanSpace.basisFun (Fin N) ℝ j)) : ℝ) = if i = j then c i else 0)
    (p : EuclideanSpace ℝ (Fin N)) :
    ‖g p‖ ^ 2 = ∑ i, (p i) ^ 2 * c i := by
  have hp : p = ∑ i, (p i) • EuclideanSpace.basisFun (Fin N) ℝ i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr p]
    simp only [EuclideanSpace.basisFun_repr]
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [hp]
  rw [map_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, inner_smul_left, RCLike.conj_to_real, inner_sum]
  rw [Finset.sum_eq_single i]
  · rw [map_smul, inner_smul_right, hortho i i, if_pos rfl]; ring
  · intro j _ hji; rw [map_smul, inner_smul_right, hortho i j, if_neg (Ne.symm hji)]; ring
  · intro h; simp at h

/-- **Operator norm of a map with orthogonal basis images.** If `g` sends the standard orthonormal
basis to a pairwise-orthogonal family with `⟪g eᵢ, g eⱼ⟫ = if i = j then c i else 0`, `c ≥ 0`, and
`i₀` attains `max c`, then `‖g‖ = √(c i₀)`. -/
private lemma opNorm_eq_of_ortho {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {N : ℕ} (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] W) (c : Fin N → ℝ)
    (hortho : ∀ i j, (inner ℝ (g (EuclideanSpace.basisFun (Fin N) ℝ i))
      (g (EuclideanSpace.basisFun (Fin N) ℝ j)) : ℝ) = if i = j then c i else 0)
    (hc : ∀ i, 0 ≤ c i) (i₀ : Fin N) (hi₀ : ∀ i, c i ≤ c i₀) :
    ‖LinearMap.toContinuousLinearMap g‖ = Real.sqrt (c i₀) := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro p
    rw [LinearMap.coe_toContinuousLinearMap']
    rw [← Real.sqrt_sq (norm_nonneg (g p)), normSq_apply_of_ortho g c hortho p, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (hc i₀), ← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [show p i * p i = (p i) ^ 2 by ring, mul_comm (c i₀) ((p i) ^ 2)]
    exact mul_le_mul_of_nonneg_left (hi₀ i) (sq_nonneg _)
  · have hb : ‖EuclideanSpace.basisFun (Fin N) ℝ i₀‖ = 1 :=
      (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.1 i₀
    have hnorm : ‖g (EuclideanSpace.basisFun (Fin N) ℝ i₀)‖ = Real.sqrt (c i₀) := by
      rw [← Real.sqrt_sq (norm_nonneg _), normSq_apply_of_ortho g c hortho]
      congr 1
      rw [Finset.sum_eq_single i₀]
      · simp [EuclideanSpace.basisFun_apply]
      · intro j _ hj; simp [EuclideanSpace.basisFun_apply, hj]
      · intro h; simp at h
    have hle := (LinearMap.toContinuousLinearMap g).le_opNorm
      (EuclideanSpace.basisFun (Fin N) ℝ i₀)
    rw [LinearMap.coe_toContinuousLinearMap', hnorm, hb, mul_one] at hle
    exact hle

/-! ### The Gram determinant and the top-`k` product maximization -/

open Set.powersetCard in
/-- **Gram determinant with a diagonal weight.** If a Gram-type matrix has `(i, j)`-entry
`d (σ_S j)` when `σ_S j = σ_T i` and `0` otherwise (with `σ_S`, `σ_T` the ordered enumerations of
two `k`-subsets `S`, `T`), then its determinant is `∏_{a ∈ S} d a` when `S = T` and `0` otherwise.
The off-diagonal case has a zero column (an element of `S ∖ T`); the diagonal case is a literal
diagonal matrix. -/
private lemma gram_det {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    (d : ι → ℝ) (S T : Set.powersetCard ι k) :
    (Matrix.of fun i j : Fin k =>
      if (ofFinEmbEquiv.symm S j : ι) = (ofFinEmbEquiv.symm T i : ι)
        then d (ofFinEmbEquiv.symm S j) else 0).det
      = if S = T then ∏ a ∈ (S : Finset ι), d a else 0 := by
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    have hdiag : (Matrix.of fun i j : Fin k =>
        if (ofFinEmbEquiv.symm S j : ι) = (ofFinEmbEquiv.symm S i : ι)
          then d (ofFinEmbEquiv.symm S j) else 0)
        = Matrix.diagonal (fun i => d (ofFinEmbEquiv.symm S i)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg]
        intro h
        exact hij (((ofFinEmbEquiv.symm S).injective h).symm)
    rw [hdiag, Matrix.det_diagonal, ← Finset.prod_image]
    · congr 1
      ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        rw [ofFinEmbEquiv_symm_apply]
        exact Finset.orderEmbOfFin_mem S.val S.prop i
      · intro ha
        obtain ⟨i, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem S a).mpr ha
        exact ⟨i, rfl⟩
    · intro i _ j _ h
      exact (ofFinEmbEquiv.symm S).injective h
  · rw [if_neg hST]
    obtain ⟨a, haS, haT⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne S T).mp hST
    obtain ⟨j₀, hj₀⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem S a).mpr haS
    apply Matrix.det_eq_zero_of_column_eq_zero j₀
    intro i
    simp only [Matrix.of_apply, hj₀]
    rw [if_neg]
    intro h
    exact haT ((mem_range_ofFinEmbEquiv_symm_iff_mem T a).mp ⟨i, h.symm⟩)

/-- A strictly monotone `Fin k → Fin n` satisfies `i ≤ g i`. -/
private lemma le_orderEmb {k n : ℕ} (g : Fin k ↪o Fin n) (i : Fin k) :
    (i : ℕ) ≤ (g i : ℕ) := by
  have hmono : StrictMono (fun j : Fin k => (g j : ℕ)) := fun a b hab =>
    (Fin.lt_def).mp (g.strictMono hab)
  obtain ⟨iv, hiv⟩ := i
  induction iv using Nat.strong_induction_on with
  | _ iv ih =>
    cases iv with
    | zero => exact Nat.zero_le _
    | succ m =>
      have hm : m < k := Nat.lt_of_succ_lt hiv
      have ihm := ih m (Nat.lt_succ_self m) hm
      have hstep : (g ⟨m, hm⟩ : ℕ) < (g ⟨m + 1, hiv⟩ : ℕ) :=
        hmono (by simp [Fin.lt_def])
      have hv : ((⟨m, hm⟩ : Fin k) : ℕ) = m := rfl
      have hv2 : ((⟨m + 1, hiv⟩ : Fin k) : ℕ) = m + 1 := rfl
      rw [hv] at ihm
      rw [hv2]
      omega

/-- **Top-`k` prefix maximizes the product of antitone nonnegative weights.** For antitone
nonnegative `σ : Fin n → ℝ`, the product over any `k`-subset is at most the product over the
top-`k` prefix indices (any `top` with `(top i : ℕ) = i`). -/
private lemma prod_le_prod_top {n k : ℕ} (σ : Fin n → ℝ) (hσ : Antitone σ)
    (hpos : ∀ i, 0 ≤ σ i) (S : Set.powersetCard (Fin n) k)
    (top : Fin k → Fin n) (htop : ∀ i, (top i : ℕ) = i) :
    ∏ a ∈ (S : Finset (Fin n)), σ a ≤ ∏ i, σ (top i) := by
  rw [← Finset.image_orderEmbOfFin_univ (S : Finset (Fin n)) S.prop,
    Finset.prod_image (fun i _ j _ h => (Finset.orderEmbOfFin S.val S.prop).injective h)]
  apply Finset.prod_le_prod
  · intro i _; exact hpos _
  · intro i _
    apply hσ
    rw [Fin.le_iff_val_le_val, htop]
    exact le_orderEmb (Finset.orderEmbOfFin S.val S.prop) i

/-- **The bridge.** Through the Hodge trivializations of source and target, the exterior operator
norm equals the product of the top-`k` singular values:
`exteriorOpNorm k (hodgeTrivialization k) (hodgeTrivialization k) f = ∏_{i<k} σᵢ(f)`. -/
theorem exteriorOpNorm_hodge_eq_prod_singularValues (k : ℕ) (f : E →ₗ[ℝ] F) :
    exteriorOpNorm k (hodgeTrivialization k) (hodgeTrivialization k) f
      = ∏ i ∈ Finset.range k, f.singularValues i := by
  classical
  set nE := Module.finrank ℝ E with hnE
  set hT := f.isSymmetric_adjoint_comp_self with hThT
  set u := hT.eigenvectorBasis (hnE.symm : Module.finrank ℝ E = nE) with hu
  set wF := stdOrthonormalBasis ℝ F with hwF
  -- Step A: the Hodge trivialization is the o.n.-basis trivialization of the standard basis.
  have hStdE : hodgeTrivialization (E := E) k = onbTriv (stdOrthonormalBasis ℝ E) k := by
    unfold hodgeTrivialization onbTriv wedgeBasis wedgeIndexEquiv wIndexEquiv
    rfl
  have hStdF : hodgeTrivialization (E := F) k = onbTriv wF k := by
    unfold hodgeTrivialization onbTriv wedgeBasis wedgeIndexEquiv wIndexEquiv
    rfl
  -- Step B: change source o.n. basis to the SVD basis `u`.
  rw [hStdE, hStdF, exteriorOpNorm_onbTriv_eq (stdOrthonormalBasis ℝ E) u wF wF k f]
  -- Abbreviations.
  set σ : Fin nE → ℝ := fun a => f.singularValues (a : ℕ) with hσdef
  -- the Gram orthogonality of `f uᵢ`.
  have hGram : ∀ a b : Fin nE, (inner ℝ (f (u a)) (f (u b)) : ℝ)
      = if a = b then σ a ^ 2 else 0 := by
    intro a b
    rw [hσdef, hu]
    exact inner_apply_eigenvectorBasis_eq f (hnE.symm : Module.finrank ℝ E = nE) a b
  unfold exteriorOpNorm
  set N := Module.finrank ℝ (⋀[ℝ]^k E) with hN
  -- the diagonal weight for the op-norm lemma.
  set c : Fin N → ℝ := fun i =>
    ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin nE) k).val, σ a ^ 2 with hcdef
  -- `g (basisFun i) = onbTriv wF (⋀^k f (u-wedge basis at (wIndexEquiv u).symm i))`.
  have hgbasis : ∀ i : Fin N,
      conjExteriorMap k (onbTriv u k) (onbTriv wF k) f (EuclideanSpace.basisFun (Fin N) ℝ i)
      = onbTriv wF k (exteriorPower.map k f
          (u.toBasis.exteriorPower k ((wIndexEquiv u k).symm i))) := by
    intro i
    rw [conjExteriorMap]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    congr 2
    rw [LinearEquiv.symm_apply_eq]
    ext1 j
    rw [onbTriv_apply, EuclideanSpace.basisFun_apply, PiLp.ofLp_single,
      Basis.repr_reindex_apply, Basis.repr_self, Pi.single_apply, Finsupp.single_apply]
    simp only [eq_comm]
    by_cases hij : i = j <;> simp [hij]
  -- orthogonality of the basis images, with weights `c`.
  have hortho : ∀ i j : Fin N,
      (inner ℝ (conjExteriorMap k (onbTriv u k) (onbTriv wF k) f (EuclideanSpace.basisFun (Fin N) ℝ i))
        (conjExteriorMap k (onbTriv u k) (onbTriv wF k) f (EuclideanSpace.basisFun (Fin N) ℝ j))
        : ℝ) = if i = j then c i else 0 := by
    intro i j
    rw [hgbasis i, hgbasis j, inner_onbTriv]
    -- map f (wedge_S) = ιMulti_family (f ∘ u.toBasis) S
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family, exteriorPower.map_apply_ιMulti_family,
      exteriorPower.ιMulti_family, exteriorPower.ιMulti_family, hodgeForm_ιMulti]
    -- the Gram matrix matches `gram_det` with weight `σ²`.
    have hfu : (f ∘ ⇑u.toBasis) = fun a => f (u a) := by funext a; simp [u.coe_toBasis]
    rw [hfu]
    simp only [Function.comp_apply]
    have hmat : (Matrix.of fun i' j' : Fin k =>
        (inner ℝ (f (u (Set.powersetCard.ofFinEmbEquiv.symm ((wIndexEquiv u k).symm i) j')))
          (f (u (Set.powersetCard.ofFinEmbEquiv.symm ((wIndexEquiv u k).symm j) i'))) : ℝ))
        = Matrix.of fun i' j' : Fin k =>
          if (Set.powersetCard.ofFinEmbEquiv.symm ((wIndexEquiv u k).symm i) j' : Fin nE)
              = (Set.powersetCard.ofFinEmbEquiv.symm ((wIndexEquiv u k).symm j) i' : Fin nE)
            then σ (Set.powersetCard.ofFinEmbEquiv.symm ((wIndexEquiv u k).symm i) j') ^ 2
            else 0 := by
      ext i' j'
      simp only [Matrix.of_apply]
      exact hGram _ _
    rw [hmat, gram_det (fun a => σ a ^ 2)]
    -- `Si = Sj ↔ i = j`, and the diagonal product is `c i`.
    have hiff : (((wIndexEquiv u k).symm i) = ((wIndexEquiv u k).symm j)) ↔ (i = j) :=
      (wIndexEquiv u k).symm.injective.eq_iff
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (hiff.mpr hij), hcdef]
    · rw [if_neg hij, if_neg (fun h => hij (hiff.mp h))]
  -- nonnegativity of the weights.
  have hcnonneg : ∀ i, 0 ≤ c i := fun i => Finset.prod_nonneg (fun a _ => sq_nonneg _)
  -- σ is antitone and nonnegative.
  have hσanti : Antitone σ := fun a b hab => by
    simp only [hσdef]
    exact f.singularValues_antitone (by exact_mod_cast hab)
  have hσpos : ∀ a, 0 ≤ σ a := fun a => f.singularValues_nonneg _
  by_cases hkn : k ≤ nE
  · -- main case: the maximum is attained at the top-`k` prefix set.
    -- the order embedding `i ↦ ⟨i⟩ : Fin k ↪o Fin nE` and its `powersetCard` image.
    set topEmb : Fin k ↪o Fin nE :=
      { toFun := fun i => ⟨i, lt_of_lt_of_le i.2 hkn⟩
        inj' := fun i j h => by
          apply Fin.ext
          have := congrArg Fin.val h
          simpa using this
        map_rel_iff' := Iff.rfl } with htopEmb
    set topSet : Set.powersetCard (Fin nE) k := Set.powersetCard.ofFinEmbEquiv topEmb with htopSet
    have htopenum : Set.powersetCard.ofFinEmbEquiv.symm topSet = topEmb := by
      rw [htopSet, Equiv.symm_apply_apply]
    have htopval : ∀ i : Fin k, (topEmb i : Fin nE).val = (i : ℕ) := fun i => rfl
    set i₀ : Fin N := wIndexEquiv u k topSet with hi₀def
    have hS₀ : (wIndexEquiv u k).symm i₀ = topSet := by rw [hi₀def, Equiv.symm_apply_apply]
    -- `∏_{a ∈ topSet} g a = ∏_{i} g (topEmb i)` for any `g`.
    have htopprod : ∀ g : Fin nE → ℝ,
        ∏ a ∈ topSet.val, g a = ∏ j, g (topEmb j) := by
      intro g
      have hval : topSet.val = Finset.univ.image (topEmb) := by
        ext x
        rw [Finset.mem_image]
        rw [show x ∈ topSet.val ↔ x ∈ topSet from Iff.rfl, htopSet,
          Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range]
        constructor
        · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
        · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
      rw [hval, Finset.prod_image (fun x _ y _ h => topEmb.injective h)]
    -- maximality of `c i₀`.
    have hmax : ∀ i, c i ≤ c i₀ := by
      intro i
      rw [hcdef]
      simp only
      rw [hS₀, htopprod (fun a => σ a ^ 2)]
      exact prod_le_prod_top (fun a => σ a ^ 2)
        (fun a b hab => pow_le_pow_left₀ (hσpos b) (hσanti hab) 2)
        (fun a => sq_nonneg _) ((wIndexEquiv u k).symm i) topEmb htopval
    rw [opNorm_eq_of_ortho _ c hortho hcnonneg i₀ hmax]
    -- compute `√(c i₀) = ∏_{i<k} σ ⟨i⟩ = ∏_{i<k} singularValues i`.
    rw [hcdef]
    simp only
    rw [hS₀, htopprod (fun a => σ a ^ 2), Finset.prod_pow,
      Real.sqrt_sq (Finset.prod_nonneg (fun j _ => hσpos _)),
      Finset.prod_range fun i => f.singularValues i]
    apply Finset.prod_congr rfl
    intro j _
    rw [hσdef]
    rfl
  · -- edge case: `k > nE`, so `⋀^k E = 0` and both sides vanish.
    have hNzero : N = 0 := by
      have heq : N = (Module.finrank ℝ E).choose k := by
        rw [hN, exteriorPower.finrank_eq]
      rw [heq]
      exact Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hkn)
    have hopzero : ‖LinearMap.toContinuousLinearMap
        (conjExteriorMap k (onbTriv u k) (onbTriv wF k) f)‖ = 0 := by
      rw [norm_eq_zero]
      apply ContinuousLinearMap.ext
      intro p
      have hsub : Subsingleton (EuclideanSpace ℝ (Fin N)) := by
        rw [hNzero]; infer_instance
      rw [Subsingleton.elim p 0]
      simp
    rw [hopzero]
    symm
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_of_not_le hkn))
    exact f.singularValues_of_finrank_le hnE.symm.le

/-! ### The compound matrix and the operator-norm/compound bridge

For a square matrix `M`, the conjugated exterior map `⋀^k (toEuclideanLin M)` through the
orthonormal-wedge trivialization of the *standard* basis `EuclideanSpace.basisFun` is itself
`toEuclideanLin` of an explicit **compound matrix** `compoundMatrix k M`, whose entries are the
`k × k` minors of `M`. This converts the (analytically delicate) exterior operator norm into the
L2 operator norm of a concrete matrix of determinants — the form needed for measurability. -/

section Compound

variable {d : ℕ}

open scoped Classical in
/-- `onbTriv` sends the `i`-th wedge basis vector (under `(wIndexEquiv b k).symm`) to the `i`-th
standard Euclidean basis vector. -/
private lemma onbTriv_wedge_eq_basisFun {ι : Type*} [Fintype ι] [LinearOrder ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (k : ℕ)
    (i : Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :
    onbTriv b k ((b.toBasis.exteriorPower k) ((wIndexEquiv b k).symm i))
      = EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) ℝ i := by
  ext1 j
  rw [onbTriv_apply, EuclideanSpace.basisFun_apply, PiLp.ofLp_single,
    Basis.repr_reindex_apply, Basis.repr_self, Pi.single_apply, Finsupp.single_apply]
  simp only [eq_comm]
  by_cases hij : i = j <;> simp [hij]

open scoped Classical in
/-- The `t`-th coordinate of `conjExteriorMap k (onbTriv b)(onbTriv b) f` applied to the
`s`-th standard basis vector equals the Hodge form of the corresponding wedge basis vectors. -/
private lemma conjExteriorMap_basisFun_coord {ι : Type*} [Fintype ι] [LinearOrder ι]
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (bE : OrthonormalBasis ι ℝ E) {κ : Type*} [Fintype κ] [LinearOrder κ]
    (bF : OrthonormalBasis κ ℝ F) (k : ℕ) (f : E →ₗ[ℝ] F)
    (s : Fin (Module.finrank ℝ (⋀[ℝ]^k E))) (t : Fin (Module.finrank ℝ (⋀[ℝ]^k F))) :
    conjExteriorMap k (onbTriv bE k) (onbTriv bF k) f
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) ℝ s) t
      = hodgeForm k ((bF.toBasis.exteriorPower k) ((wIndexEquiv bF k).symm t))
          (exteriorPower.map k f ((bE.toBasis.exteriorPower k) ((wIndexEquiv bE k).symm s))) := by
  -- Reduce the standard basis vector to the wedge basis through `onbTriv`.
  have hsource : (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) ℝ s)
      = onbTriv bE k ((bE.toBasis.exteriorPower k) ((wIndexEquiv bE k).symm s)) :=
    (onbTriv_wedge_eq_basisFun bE k s).symm
  rw [hsource, conjExteriorMap]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  -- The `t`-coordinate is an inner product with the `t`-th standard basis vector.
  have hcoord : ∀ Y : ⋀[ℝ]^k F, (onbTriv bF k Y) t
      = (inner ℝ (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k F))) ℝ t)
          (onbTriv bF k Y) : ℝ) := by
    intro Y
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    simp
  rw [hcoord, ← onbTriv_wedge_eq_basisFun bF k t, inner_onbTriv]

open Set.powersetCard in
/-- The **compound matrix** `C_k(M)`: its `(t, s)` entry is the `k × k` minor of `M` obtained by
selecting the rows enumerated by the `t`-th `k`-subset and the columns enumerated by the `s`-th
`k`-subset (under the standard orthonormal-wedge index equivalence). -/
noncomputable def compoundMatrix (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))
      (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))) ℝ :=
  Matrix.of fun t s =>
    (M.submatrix
      (fun i : Fin k =>
        (ofFinEmbEquiv.symm ((wIndexEquiv (EuclideanSpace.basisFun (Fin d) ℝ) k).symm t)) i)
      (fun j : Fin k =>
        (ofFinEmbEquiv.symm ((wIndexEquiv (EuclideanSpace.basisFun (Fin d) ℝ) k).symm s)) j)).det

/-- The coordinate of `toEuclideanLin M` on a standard basis vector recovers a matrix entry:
`(toEuclideanLin M (eq)) p = M p q`. -/
private lemma toEuclideanLin_single_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (p q : Fin m) :
    (Matrix.toEuclideanLin M (EuclideanSpace.single q (1 : ℝ))) p = M p q := by
  have hofLp : (Matrix.toEuclideanLin M (EuclideanSpace.single q (1 : ℝ))) p
      = (M.mulVec (WithLp.ofLp (EuclideanSpace.single q (1 : ℝ)))) p := rfl
  rw [hofLp,
    show WithLp.ofLp (EuclideanSpace.single q (1 : ℝ)) = Pi.single q (1 : ℝ) from rfl,
    Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

/-- The Gram entry of the standard basis under `toEuclideanLin M` recovers the matrix entry:
`⟪eₚ, (toEuclideanLin M) e_q⟫ = M p q`. -/
private lemma inner_basisFun_toEuclideanLin (M : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d) :
    (inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) p)
      (Matrix.toEuclideanLin M ((EuclideanSpace.basisFun (Fin d) ℝ) q)) : ℝ) = M p q := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, toEuclideanLin_single_apply]

open scoped Classical in
open Set.powersetCard in
/-- **The compound bridge.** Through the orthonormal-wedge trivializations of the standard basis,
`⋀^k (toEuclideanLin M)` is `toEuclideanLin` of the compound matrix `C_k(M)`. -/
theorem conjExteriorMap_eq_toEuclideanLin_compound (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    conjExteriorMap k (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k)
        (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k) (Matrix.toEuclideanLin M)
      = Matrix.toEuclideanLin (compoundMatrix k M) := by
  -- It suffices to agree on each standard basis vector, coordinatewise.
  refine Basis.ext (EuclideanSpace.basisFun _ ℝ).toBasis (fun s => ?_)
  rw [OrthonormalBasis.coe_toBasis]
  ext t
  -- LHS coordinate is the Hodge form of the wedge basis vectors.
  rw [conjExteriorMap_basisFun_coord (EuclideanSpace.basisFun (Fin d) ℝ)
    (EuclideanSpace.basisFun (Fin d) ℝ) k (Matrix.toEuclideanLin M)]
  -- RHS coordinate is the compound entry `compoundMatrix k M t s`.
  have hRHS : (Matrix.toEuclideanLin (compoundMatrix k M)
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))) ℝ s)) t
      = compoundMatrix k M t s := by
    rw [EuclideanSpace.basisFun_apply, toEuclideanLin_single_apply]
  rw [hRHS, compoundMatrix]
  simp only [Matrix.of_apply]
  -- Expand the Hodge form to a determinant of inner products, then identify with the minor.
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family, hodgeForm_ιMulti]
  -- The Gram entry is `M (row) (col)`; det is invariant under transpose.
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.submatrix_apply]
  -- Both sides reduce to `M (rowEnum i) (colEnum j)` via `inner_basisFun_toEuclideanLin`.
  simp only [Function.comp_apply, OrthonormalBasis.coe_toBasis]
  exact inner_basisFun_toEuclideanLin M _ _

set_option maxHeartbeats 800000 in
/-- **The product of singular values is the L2 operator norm of the compound matrix.** Combining
the singular-value bridge with the compound identity: `∏_{i<k} σᵢ(toEuclideanLin M) = ‖C_k(M)‖`. -/
theorem prod_singularValues_eq_l2_opNorm_compound (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin M).singularValues i
      = ‖compoundMatrix k M‖ := by
  classical
  -- The Hodge trivialization on `EuclideanSpace ℝ (Fin d)` is the standard-basis wedge
  -- trivialization, so the singular-value bridge is the standard-basis exterior operator norm.
  have hStd : hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k
      = onbTriv (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) k := by
    unfold hodgeTrivialization onbTriv wedgeBasis wedgeIndexEquiv wIndexEquiv
    rfl
  -- Pass from the Hodge trivialization to the standard-basis (`basisFun`) trivialization.
  rw [← exteriorOpNorm_hodge_eq_prod_singularValues k (Matrix.toEuclideanLin M)]
  rw [show exteriorOpNorm k (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k)
        (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k) (Matrix.toEuclideanLin M)
      = exteriorOpNorm k (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k)
          (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k) (Matrix.toEuclideanLin M) by
    rw [hStd]
    exact exteriorOpNorm_onbTriv_eq (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace.basisFun (Fin d) ℝ) (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace.basisFun (Fin d) ℝ) k (Matrix.toEuclideanLin M)]
  -- Now identify the conjugated exterior map with `toEuclideanLin` of the compound matrix.
  rw [exteriorOpNorm, conjExteriorMap_eq_toEuclideanLin_compound k M]
  rw [Matrix.l2_opNorm_def]
  rfl

end Compound

end Bridge

/-! ## Submultiplicativity of the product of singular values -/

section Crux

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Submultiplicativity of the product of the top-`k` singular values**, assembled from the
submultiplicativity engine and the singular-value bridge:
`∏_{i<k} σᵢ(g ∘ f) ≤ (∏_{i<k} σᵢ(g)) · (∏_{i<k} σᵢ(f))`. -/
theorem prod_singularValues_comp_le (k : ℕ) (f : E →ₗ[ℝ] F) (g : F →ₗ[ℝ] G) :
    ∏ i ∈ Finset.range k, (g ∘ₗ f).singularValues i
      ≤ (∏ i ∈ Finset.range k, g.singularValues i)
        * ∏ i ∈ Finset.range k, f.singularValues i := by
  rw [← exteriorOpNorm_hodge_eq_prod_singularValues k (g ∘ₗ f),
      ← exteriorOpNorm_hodge_eq_prod_singularValues k g,
      ← exteriorOpNorm_hodge_eq_prod_singularValues k f]
  exact exteriorOpNorm_comp_le k (hodgeTrivialization k) (hodgeTrivialization k)
    (hodgeTrivialization k) f g

end Crux

end ExteriorNorm

end
