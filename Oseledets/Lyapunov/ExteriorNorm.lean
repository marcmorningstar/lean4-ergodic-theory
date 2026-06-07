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
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

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
open scoped Matrix.Norms.L2Operator Matrix

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

/-- **The top element of a non-top `k`-subset is `≥ k`.** If the ordered enumeration `e` of a
`k`-subset `S` of `Fin n` does not enumerate the top prefix `{0,…,k-1}`, then its largest element
`e ⟨k-1⟩` has value `≥ k`. (Otherwise all of `S` lies in `{0,…,k-1}`, forcing `S` = top prefix.) -/
private lemma top_elem_ge {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (e : Fin k ↪o Fin n)
    (htop : ((Finset.univ.image (fun j : Fin k => (e j))) : Finset (Fin n))
      ≠ Finset.univ.image (fun i : Fin k => (⟨i, lt_of_lt_of_le i.2 hkn⟩ : Fin n))) :
    k ≤ (e ⟨k-1, by omega⟩ : ℕ) := by
  by_contra hlt
  rw [not_le] at hlt
  apply htop
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨j, rfl⟩ := hx
    have hjlt := j.2
    have hle : (e j : ℕ) ≤ (e ⟨k-1, by omega⟩ : ℕ) := by
      have hj : j ≤ (⟨k-1, by omega⟩ : Fin k) := by rw [Fin.le_def]; simp only; omega
      exact_mod_cast (e.monotone hj)
    have hjk : (e j : ℕ) < k := lt_of_le_of_lt hle hlt
    exact ⟨⟨(e j : ℕ), hjk⟩, Fin.ext rfl⟩
  · rw [Finset.card_image_of_injective _ (fun a b h => e.injective h),
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))]

/-- **The second-largest `k`-subset product bound.** For antitone nonnegative `lam`, the product of
`lam` over the ordered enumeration `e` of a `k`-subset whose top element is `≥ k` (i.e. a non-top
subset) is at most the second-largest product `(∏_{i<k-1} lam i)·lam k`. The top factor drops from
`lam (k-1)` to `lam k`; the remaining `k-1` factors are bounded by the prefix `{0,…,k-2}`. -/
private lemma prod_le_second_aux {n : ℕ} (m : ℕ) (lam : ℕ → ℝ)
    (hanti : Antitone lam) (hpos : ∀ i, 0 ≤ lam i) (e : Fin (m+1) ↪o Fin n)
    (htopge : m + 1 ≤ (e ⟨m, by omega⟩ : ℕ)) :
    ∏ j : Fin (m+1), lam (e j : ℕ) ≤ (∏ i ∈ Finset.range m, lam i) * lam (m+1) := by
  rw [Fin.prod_univ_castSucc]
  have hlast : lam (e (Fin.last m) : ℕ) ≤ lam (m+1) := by
    apply hanti
    rw [show (Fin.last m : Fin (m+1)) = ⟨m, by omega⟩ from rfl]; exact htopge
  have hcast : ∏ j : Fin m, lam (e j.castSucc : ℕ) ≤ ∏ i ∈ Finset.range m, lam i := by
    rw [Finset.prod_range fun i => lam i]
    apply Finset.prod_le_prod (fun i _ => hpos _)
    intro i _
    apply hanti
    have := le_orderEmb e i.castSucc
    simpa using this
  calc (∏ j : Fin m, lam (e j.castSucc : ℕ)) * lam (e (Fin.last m) : ℕ)
      ≤ (∏ i ∈ Finset.range m, lam i) * lam (e (Fin.last m) : ℕ) :=
        mul_le_mul_of_nonneg_right hcast (hpos _)
    _ ≤ (∏ i ∈ Finset.range m, lam i) * lam (m+1) :=
        mul_le_mul_of_nonneg_left hlast (Finset.prod_nonneg (fun _ _ => hpos _))

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

/-! ### The Plücker bridge: eigen-diagonalization of the compound

For a symmetric map `f` with orthonormal eigenbasis `u` and eigenvalues `lam`, the compound
`⋀^k f` is diagonal in the wedge basis of `u`: it scales the wedge `u_S` by `∏_{a ∈ S} lam a`.
This is the abstract spectral core feeding the Plücker-bridge eigenpair (PB1) and the
second-eigenvalue ceiling (PB2). -/

/-- **Product reindexing.** A product of `lam` over the ordered enumeration of a `k`-subset `S`
equals the product of `lam` over `S`. -/
private lemma prod_ofFinEmbEquiv_symm {ι : Type*} [LinearOrder ι] {k : ℕ} (lam : ι → ℝ)
    (S : Set.powersetCard ι k) :
    ∏ i, lam ((Set.powersetCard.ofFinEmbEquiv.symm S) i) = ∏ a ∈ (S : Finset ι), lam a := by
  have himg : (S : Finset ι) = Finset.univ.image (Set.powersetCard.ofFinEmbEquiv.symm S) := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.image_orderEmbOfFin_univ]
  rw [himg, Finset.prod_image
    (fun i _ j _ h => (Set.powersetCard.ofFinEmbEquiv.symm S).injective h)]

/-- **`ιMulti_family` scalar pull-out.** A family rescaled entrywise by `lam` factors a product of
scalars out of the wedge: `ιMulti_family (fun j ↦ lam j • g j) S = (∏_{a ∈ S} lam a) • ιMulti_family g S`.
Multilinearity of the alternating map `ιMulti` (`AlternatingMap.map_smul_univ`). -/
private lemma ιMulti_family_smul {ι : Type*} [LinearOrder ι] {k : ℕ} (lam : ι → ℝ) (g : ι → E)
    (S : Set.powersetCard ι k) :
    exteriorPower.ιMulti_family ℝ k (fun j => lam j • g j) S
      = (∏ a ∈ (S : Finset ι), lam a) • exteriorPower.ιMulti_family ℝ k g S := by
  classical
  rw [exteriorPower.ιMulti_family, exteriorPower.ιMulti_family]
  have hcomp : (fun j => lam j • g j) ∘ (Set.powersetCard.ofFinEmbEquiv.symm S)
      = fun i => lam ((Set.powersetCard.ofFinEmbEquiv.symm S) i) •
          (g ∘ (Set.powersetCard.ofFinEmbEquiv.symm S)) i := by
    funext i; simp
  rw [hcomp, AlternatingMap.map_smul_univ, prod_ofFinEmbEquiv_symm]

open scoped Classical in
/-- **Eigen-diagonalization of the compound (abstract).** For a linear map `f` with an orthonormal
eigenbasis `u` (`f (u i) = lam i • u i`), the compound `⋀^k f` scales each wedge basis vector
`u_S` by the subset product `∏_{a ∈ S} lam a`. -/
private lemma map_exteriorPower_wedgeBasis_eq {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : E →ₗ[ℝ] E) (u : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hf : ∀ i, f (u i) = lam i • u i) (k : ℕ) (S : Set.powersetCard ι k) :
    exteriorPower.map k f (u.toBasis.exteriorPower k S)
      = (∏ a ∈ (S : Finset ι), lam a) • (u.toBasis.exteriorPower k S) := by
  classical
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
  have hfun : (⇑f ∘ ⇑u.toBasis) = fun j => lam j • (⇑u.toBasis j) := by
    funext j; simp only [Function.comp_apply, u.coe_toBasis]; exact hf j
  rw [hfun]
  exact ιMulti_family_smul lam (⇑u.toBasis) S

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

/-- `toEuclideanLin` of a matrix product is the composition of the linear maps. -/
private lemma toEuclideanLin_mul (B M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.toEuclideanLin (B * M)
      = (Matrix.toEuclideanLin B) ∘ₗ (Matrix.toEuclideanLin M) := by
  ext v i
  simp only [Matrix.toEuclideanLin_apply, LinearMap.comp_apply, Matrix.mulVec_mulVec]

open scoped Classical in
/-- **L7c.3b.0 — matrix-level Cauchy–Binet.** The `k`-th compound of a matrix product is the
product of the compounds: `C_k(B * M) = C_k(B) * C_k(M)`. This is the multiplicativity of the
compound matrix, proved via the functoriality `⋀^k(B ∘ M) = ⋀^k B ∘ ⋀^k M`
(`exteriorPower.map_comp`) transported through the standard orthonormal-wedge trivialization by
the compound bridge `conjExteriorMap_eq_toEuclideanLin_compound`. -/
theorem compoundMatrix_mul (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ) :
    compoundMatrix k (B * M) = compoundMatrix k B * compoundMatrix k M := by
  -- Work through the injective `toEuclideanLin` linear equiv.
  apply (Matrix.toEuclideanLin (n := Fin _) (m := Fin _)).injective
  rw [toEuclideanLin_mul, ← conjExteriorMap_eq_toEuclideanLin_compound,
    ← conjExteriorMap_eq_toEuclideanLin_compound, ← conjExteriorMap_eq_toEuclideanLin_compound]
  -- `toEuclideanLin (B * M) = toEuclideanLin B ∘ₗ toEuclideanLin M`, then telescope the trivializations.
  rw [toEuclideanLin_mul]
  unfold conjExteriorMap
  rw [exteriorPower.map_comp]
  ext x
  simp [LinearMap.comp_apply]

open scoped Classical in
open Set.powersetCard in
/-- **Compound of a transpose.** The `k`-th compound matrix of `Mᵀ` is the transpose of the `k`-th
compound of `M`: `C_k(Mᵀ) = C_k(M)ᵀ`. Entrywise this is `det(Mᵀ.minor) = det(M.minorᵀ)`
(`Matrix.det_transpose`), since the row/column enumerators at index `t`, `s` coincide. -/
theorem compoundMatrix_transpose (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    compoundMatrix k Mᵀ = (compoundMatrix k M)ᵀ := by
  ext t s
  rw [compoundMatrix, Matrix.transpose_apply, compoundMatrix, Matrix.of_apply, Matrix.of_apply,
    ← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_transpose]

open scoped Classical in
/-- The `k`-th compound of the Gram matrix `Mᵀ M` is `(C_k M)ᵀ (C_k M)`, i.e. the Gram matrix of the
compound. Combines `compoundMatrix_mul` with `compoundMatrix_transpose`. -/
theorem compoundMatrix_gram (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    compoundMatrix k (Mᵀ * M) = (compoundMatrix k M)ᵀ * compoundMatrix k M := by
  rw [compoundMatrix_mul, compoundMatrix_transpose]

open scoped Classical in
/-- **L7c.3b.0 (linear-map form).** `toEuclideanLin` of the `k`-th compound of a product is the
composition of the compounds. The form consumed by the rank-1 exterior Rayleigh-deficit chain
(L7c.3b), where the right-hand factor is post-composed with the inverse compound. -/
theorem toEuclideanLin_compoundMatrix_mul (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.toEuclideanLin (compoundMatrix k (B * M))
      = Matrix.toEuclideanLin (compoundMatrix k B) ∘ₗ Matrix.toEuclideanLin (compoundMatrix k M) := by
  rw [compoundMatrix_mul, toEuclideanLin_mul]

/-! ### Top singular value vs. the sum of squared singular values (Frobenius)

The Frobenius back-transport (L7c.3c) needs `‖M‖_op ≤ ‖M‖_F`. Stated through the committed
singular-value bridge (`toEuclideanLin`) to avoid the L2-operator vs. Frobenius
`NormedAddCommGroup`-instance diamond on `Matrix`. The core inequality is that the top squared
singular value is at most the sum of all squared singular values; the sum equals
`tr(MᵀM) = ‖M‖_F²`. -/

/-- **L7c.3c.0 core.** The top squared singular value of `toEuclideanLin M` is at most the sum of
all squared singular values. The sum over `Fin d` equals `tr(MᵀM) = ‖M‖_F²` (the Hilbert–Schmidt
norm squared); combined with `‖M‖_op = σ₀` this yields `‖M‖_op ≤ ‖M‖_F`. -/
theorem singularValues_zero_sq_le_sum (M : Matrix (Fin d) (Fin d) ℝ) :
    (Matrix.toEuclideanLin M).singularValues 0 ^ 2
      ≤ ∑ i : Fin d, (Matrix.toEuclideanLin M).singularValues i ^ 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: the top singular value vanishes (`finrank = 0 ≤ 0`) and the sum is empty.
    subst hd
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) ≤ 0 := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
    rw [(Matrix.toEuclideanLin M).singularValues_of_finrank_le hfr]
    simp
  · -- `d > 0`: the `i = 0` term is one nonneg summand of the sum.
    have hmem := Finset.single_le_sum
      (f := fun i : Fin d => (Matrix.toEuclideanLin M).singularValues i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ (⟨0, hd⟩ : Fin d))
    simpa using hmem

/-- **L7c.3c.0.** The top singular value of `toEuclideanLin M` is at most the Frobenius norm
`√(∑ σᵢ²)`. Immediate from `singularValues_zero_sq_le_sum` and `Real.sqrt`. -/
theorem opNorm_le_frobenius (M : Matrix (Fin d) (Fin d) ℝ) :
    (Matrix.toEuclideanLin M).singularValues 0
      ≤ Real.sqrt (∑ i : Fin d, (Matrix.toEuclideanLin M).singularValues i ^ 2) := by
  rw [show (Matrix.toEuclideanLin M).singularValues 0
      = Real.sqrt ((Matrix.toEuclideanLin M).singularValues 0 ^ 2) from
    (Real.sqrt_sq ((Matrix.toEuclideanLin M).singularValues_nonneg 0)).symm]
  exact Real.sqrt_le_sqrt (singularValues_zero_sq_le_sum M)

/-- **L7c.3c.0 — the L2 operator-norm Frobenius bridge.** The squared L2 operator norm `‖M‖²` of a
matrix is at most the sum of the squared singular values of `toEuclideanLin M` (the squared
Frobenius norm). The L2 matrix norm `‖M‖` is by definition the operator norm of `toEuclideanLin M`
on `EuclideanSpace`; expanding any vector in the singular-value eigenbasis `u` of
`adjoint f ∘ₗ f` (with `f = toEuclideanLin M`), the images `f uⱼ` are pairwise orthogonal with
`‖f uⱼ‖ = σⱼ`, so `‖f v‖² = ∑ⱼ ⟪uⱼ, v⟫² σⱼ² ≤ (∑ σᵢ²) ‖v‖²`. -/
theorem l2_opNorm_sq_le_sum_singularValues (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖M‖ ^ 2 ≤ ∑ i : Fin d, (Matrix.toEuclideanLin M).singularValues i ^ 2 := by
  set f := Matrix.toEuclideanLin M with hf
  set S := ∑ i : Fin d, f.singularValues i ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set hT := f.isSymmetric_adjoint_comp_self with hhT
  set u := hT.eigenvectorBasis hfin with hu
  -- pointwise bound `‖f v‖² ≤ S ‖v‖²`
  have hpt : ∀ v : EuclideanSpace ℝ (Fin d), ‖f v‖ ^ 2 ≤ S * ‖v‖ ^ 2 := by
    intro v
    have hexp : f v = ∑ j, (inner ℝ (u j) v : ℝ) • f (u j) := by
      conv_lhs => rw [← u.sum_repr' v]
      rw [map_sum]; simp_rw [map_smul]
    have horth : ∀ i j, i ≠ j → (inner ℝ (f (u i)) (f (u j)) : ℝ) = 0 := by
      intro i j hij
      have h1 : (inner ℝ (f (u i)) (f (u j)) : ℝ)
          = inner ℝ ((LinearMap.adjoint f ∘ₗ f) (u j)) (u i) := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_comm]
      rw [h1, show (LinearMap.adjoint f ∘ₗ f) (u j) = (hT.eigenvalues hfin j : ℝ) • u j from
            hT.apply_eigenvectorBasis hfin j, inner_smul_left, u.inner_eq_ite j i]
      simp [Ne.symm hij]
    have hnormfu : ∀ j, ‖f (u j)‖ ^ 2 = f.singularValues j ^ 2 := by
      intro j
      have key : (inner ℝ (f (u j)) (f (u j)) : ℝ) = f.singularValues j ^ 2 := by
        have h1 : (inner ℝ (f (u j)) (f (u j)) : ℝ)
            = inner ℝ ((LinearMap.adjoint f ∘ₗ f) (u j)) (u j) := by
          rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
        rw [h1, show (LinearMap.adjoint f ∘ₗ f) (u j) = (hT.eigenvalues hfin j : ℝ) • u j from
              hT.apply_eigenvectorBasis hfin j, inner_smul_left, u.inner_eq_ite j j,
            f.sq_singularValues_fin hfin j]
        simp
      rw [← real_inner_self_eq_norm_sq]; exact key
    have hsq : ‖f v‖ ^ 2 = ∑ j, (inner ℝ (u j) v : ℝ) ^ 2 * ‖f (u j)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hexp, inner_sum]
      simp_rw [sum_inner, inner_smul_left, inner_smul_right]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single j]
      · rw [real_inner_self_eq_norm_sq]
        simp only [starRingEnd_apply, star_trivial]; ring
      · intro i _ hij
        rw [horth j i (Ne.symm hij)]; ring
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsq]
    have hpars : ∑ j, (inner ℝ (u j) v : ℝ) ^ 2 = ‖v‖ ^ 2 := by
      have := u.sum_sq_norm_inner_right v
      simp only [Real.norm_eq_abs, sq_abs] at this
      exact this
    calc ∑ j, (inner ℝ (u j) v : ℝ) ^ 2 * ‖f (u j)‖ ^ 2
        = ∑ j, (inner ℝ (u j) v : ℝ) ^ 2 * f.singularValues j ^ 2 := by
          apply Finset.sum_congr rfl; intro j _; rw [hnormfu]
      _ ≤ ∑ j, (inner ℝ (u j) v : ℝ) ^ 2 * S := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          rw [hS]
          exact Finset.single_le_sum
            (f := fun i : Fin d => f.singularValues i ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      _ = S * ‖v‖ ^ 2 := by rw [← Finset.sum_mul, hpars]; ring
  -- bound the operator norm by `√S`
  have hnorm_le : ‖M‖ ≤ Real.sqrt S := by
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg S)
    intro v
    show ‖_‖ ≤ Real.sqrt S * ‖v‖
    rw [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', ← hf]
    have h2 := hpt v
    have hrhs : 0 ≤ Real.sqrt S * ‖v‖ := mul_nonneg (Real.sqrt_nonneg S) (norm_nonneg v)
    nlinarith [norm_nonneg (f v), Real.sq_sqrt hSnn, h2, hrhs]
  nlinarith [hnorm_le, norm_nonneg M, Real.sq_sqrt hSnn, Real.sqrt_nonneg S]

/-- The sum of the squared singular values of `toEuclideanLin N` equals the trace of the Gram
matrix `tr(Nᵀ N)` (the squared Frobenius norm). Both sides are the trace of the self-adjoint
operator `adjoint f ∘ₗ f = toEuclideanLin (Nᵀ N)`: in the singular-value eigenbasis its diagonal
entries are the eigenvalues `σᵢ²`, while as a matrix its trace is `tr(Nᵀ N)`. -/
theorem sum_sq_singularValues_eq_trace (N : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i : Fin d, (Matrix.toEuclideanLin N).singularValues i ^ 2 = (Nᵀ * N).trace := by
  set f := Matrix.toEuclideanLin N with hf
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set hT := f.isSymmetric_adjoint_comp_self with hhT
  set u := hT.eigenvectorBasis hfin with hu
  -- `∑ σᵢ² = trace (adjoint f ∘ₗ f)`, computed in the eigenbasis `u`.
  have h1 : ∑ i : Fin d, f.singularValues i ^ 2
      = LinearMap.trace ℝ _ (LinearMap.adjoint f ∘ₗ f) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ u.toBasis (LinearMap.adjoint f ∘ₗ f), Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      show (LinearMap.adjoint f ∘ₗ f) (u i) = (hT.eigenvalues hfin i : ℝ) • u i from
        hT.apply_eigenvectorBasis hfin i, map_smul, Finsupp.smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis_repr_apply, u.repr_self, f.sq_singularValues_fin hfin i]
    simp
  -- `adjoint f ∘ₗ f = toEuclideanLin (Nᵀ N)`.
  have h2 : LinearMap.adjoint f ∘ₗ f = Matrix.toEuclideanLin (Nᵀ * N) := by
    rw [toEuclideanLin_mul, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  -- `trace (toEuclideanLin G) = tr G`.
  rw [h1, h2, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

/-- `toEuclideanLin` of a (rectangular) matrix product is the composition of the linear maps. -/
private lemma toEuclideanLin_mul_rect {a b c : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (M : Matrix (Fin b) (Fin c) ℝ) :
    Matrix.toEuclideanLin (B * M)
      = (Matrix.toEuclideanLin B) ∘ₗ (Matrix.toEuclideanLin M) := by
  ext v i
  simp only [Matrix.toEuclideanLin_apply, LinearMap.comp_apply, Matrix.mulVec_mulVec]

/-- A matrix `U` with orthonormal columns (`Uᵀ U = 1`) is an isometry, so its L2 operator norm is
at most `1`. -/
theorem norm_le_one_of_cols_orthonormal {k : ℕ} (U : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  show ‖Matrix.toEuclideanLin U x‖ ≤ ‖x‖
  have hsq : ‖Matrix.toEuclideanLin U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    have hadj : (inner ℝ (Matrix.toEuclideanLin U x) (Matrix.toEuclideanLin U x) : ℝ)
        = inner ℝ
            ((LinearMap.adjoint (Matrix.toEuclideanLin U) ∘ₗ Matrix.toEuclideanLin U) x) x := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    rw [hadj]
    congr 1
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← toEuclideanLin_mul_rect,
      Matrix.conjTranspose_eq_transpose_of_trivial, hU]
    simp
  nlinarith [norm_nonneg (Matrix.toEuclideanLin U x), norm_nonneg x, hsq]

/-- The eigenvalues of the Gram matrix `Wᵀ W` are bounded by the squared L2 operator norm `‖W‖²`.
Each eigenvalue `μᵢ` of the Hermitian matrix `G = Wᵀ W`, with unit eigenvector `bᵢ`, equals
`‖toEuclideanLin W (bᵢ)‖² ≤ ‖W‖²`. -/
theorem gram_eigenvalues_le_opNorm_sq {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ)
    (hGherm : (Wᵀ * W).IsHermitian) (i : Fin k) : hGherm.eigenvalues i ≤ ‖W‖ ^ 2 := by
  set G := Wᵀ * W with hG
  set b := hGherm.eigenvectorBasis with hb
  set W' := Matrix.toEuclideanLin W with hW'
  have hGlin : Matrix.toEuclideanLin G = LinearMap.adjoint W' ∘ₗ W' := by
    rw [hG, toEuclideanLin_mul, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hmuleq : hGherm.eigenvalues i = ‖W' (b i)‖ ^ 2 := by
    have hmv : G *ᵥ ⇑(b i) = hGherm.eigenvalues i • ⇑(b i) := hGherm.mulVec_eigenvectorBasis i
    have hinner : (inner ℝ (Matrix.toEuclideanLin G (b i)) (b i) : ℝ)
        = hGherm.eigenvalues i := by
      have hsmul : Matrix.toEuclideanLin G (b i) = hGherm.eigenvalues i • (b i) := by
        rw [Matrix.toEuclideanLin_apply, hmv]; rfl
      rw [hsmul, inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i]
      simp
    rw [← hinner, hGlin, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq]
  rw [hmuleq]
  have hbnd : ‖W' (b i)‖ ≤ ‖W‖ * ‖b i‖ := by
    have hle := (LinearMap.toContinuousLinearMap W').le_opNorm (b i)
    rwa [LinearMap.coe_toContinuousLinearMap',
      show ‖LinearMap.toContinuousLinearMap W'‖ = ‖W‖ from rfl] at hle
  rw [b.orthonormal.1 i, mul_one] at hbnd
  nlinarith [norm_nonneg (W' (b i)), norm_nonneg W, hbnd]

/-- **L7c.3c.1 — the Frobenius back-transport.** For matrices `U, V` with orthonormal columns
(`Uᵀ U = 1`, `Vᵀ V = 1`), the squared L2 operator norm of the difference of the orthogonal
projectors `U Uᵀ` and `V Vᵀ` is bounded by `2 k (1 - det(Uᵀ V)²)`. Chain: self-adjoint idempotents
of trace `k`; `‖P − P'‖²_op ≤ ∑σᵢ² = tr((P−P')²) = 2k − 2 tr(P P')`; `tr(P P') = ‖Uᵀ V‖_F² = tr(G)`
for the Gram `G = (Uᵀ V)ᵀ (Uᵀ V)`; then the elementary AM-GM `k ∏ tᵢ ≤ ∑ tᵢ` over the eigenvalues
`tᵢ ∈ [0, 1]` of `G`, with `∏ tᵢ = det G = det(Uᵀ V)²`. -/
theorem norm_proj_sub_le_wedge {k : ℕ} (U V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ‖U * Uᵀ - V * Vᵀ‖ ^ 2 ≤ 2 * k * (1 - (Uᵀ * V).det ^ 2) := by
  set P := U * Uᵀ with hP
  set P' := V * Vᵀ with hP'
  -- self-adjoint idempotents of trace `k`
  have hPidem : P * P = P := by
    rw [hP, show U * Uᵀ * (U * Uᵀ) = U * (Uᵀ * U) * Uᵀ by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one]
  have hP'idem : P' * P' = P' := by
    rw [hP', show V * Vᵀ * (V * Vᵀ) = V * (Vᵀ * V) * Vᵀ by simp only [Matrix.mul_assoc], hV,
      Matrix.mul_one]
  have hPsymm : Pᵀ = P := by rw [hP, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP'symm : P'ᵀ = P' := by rw [hP', Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPtrace : P.trace = (k : ℝ) := by
    rw [hP, Matrix.trace_mul_comm, hU, Matrix.trace_one, Fintype.card_fin]
  have hP'trace : P'.trace = (k : ℝ) := by
    rw [hP', Matrix.trace_mul_comm, hV, Matrix.trace_one, Fintype.card_fin]
  -- `‖P − P'‖²_op ≤ ∑σᵢ(P−P')² = tr((P−P')ᵀ(P−P')) = tr((P−P')²)`
  have hsymm : (P - P')ᵀ = P - P' := by rw [Matrix.transpose_sub, hPsymm, hP'symm]
  have hnorm : ‖P - P'‖ ^ 2 ≤ ((P - P')ᵀ * (P - P')).trace :=
    le_trans (l2_opNorm_sq_le_sum_singularValues _) (le_of_eq (sum_sq_singularValues_eq_trace _))
  rw [hsymm] at hnorm
  -- `tr((P−P')²) = 2k − 2 tr(P P')`
  have htrid : ((P - P') * (P - P')).trace = 2 * (k : ℝ) - 2 * (P * P').trace := by
    have hexp : (P - P') * (P - P') = P * P - P * P' - P' * P + P' * P' := by
      rw [sub_mul, mul_sub, mul_sub]; abel
    rw [hexp, hPidem, hP'idem, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      hPtrace, hP'trace, Matrix.trace_mul_comm P' P]
    ring
  rw [htrid] at hnorm
  -- `tr(P P') = tr((Uᵀ V)ᵀ (Uᵀ V))`
  have htrPP' : (P * P').trace = ((Uᵀ * V)ᵀ * (Uᵀ * V)).trace := by
    have step1 : (P * P').trace = ((Uᵀ * V) * (Uᵀ * V)ᵀ).trace := by
      rw [hP, hP', show U * Uᵀ * (V * Vᵀ) = U * (Uᵀ * V * Vᵀ) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm U (Uᵀ * V * Vᵀ)]
      congr 1
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [step1, Matrix.trace_mul_comm]
  -- the Gram `G = (Uᵀ V)ᵀ (Uᵀ V)`: PosSemidef Hermitian, eigenvalues in `[0, 1]`
  set W := Uᵀ * V with hW
  have hWconj : Wᴴ = Wᵀ := Matrix.conjTranspose_eq_transpose_of_trivial _
  have hPSD : (Wᵀ * W).PosSemidef := by
    have hps := Matrix.posSemidef_conjTranspose_mul_self W
    rwa [hWconj] at hps
  set G := Wᵀ * W with hG
  set hGherm := hPSD.isHermitian with hGhermdef
  set t : Fin k → ℝ := hGherm.eigenvalues with ht
  have htnn : ∀ i, 0 ≤ t i := fun i => hPSD.eigenvalues_nonneg i
  have hWnorm : ‖W‖ ≤ 1 := by
    have hUtnorm : ‖(Uᵀ : Matrix (Fin k) (Fin d) ℝ)‖ ≤ 1 := by
      rw [show (Uᵀ : Matrix (Fin k) (Fin d) ℝ) = Uᴴ from
        (Matrix.conjTranspose_eq_transpose_of_trivial U).symm, Matrix.l2_opNorm_conjTranspose]
      exact norm_le_one_of_cols_orthonormal U hU
    calc ‖W‖ = ‖Uᵀ * V‖ := by rw [hW]
      _ ≤ ‖Uᵀ‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 :=
          mul_le_mul hUtnorm (norm_le_one_of_cols_orthonormal V hV) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have ht1 : ∀ i, t i ≤ 1 := by
    intro i
    calc t i ≤ ‖W‖ ^ 2 := gram_eigenvalues_le_opNorm_sq W hGherm i
      _ ≤ 1 ^ 2 := by gcongr
      _ = 1 := one_pow 2
  have htrG : G.trace = ∑ i, t i := by
    rw [ht, hGhermdef, hGherm.trace_eq_sum_eigenvalues]; simp
  have hdetG : G.det = ∏ i, t i := by
    rw [ht, hGhermdef, hGherm.det_eq_prod_eigenvalues]; simp
  have hdetGW : G.det = W.det ^ 2 := by rw [hG, Matrix.det_mul, Matrix.det_transpose]; ring
  -- AM-GM: `k ∏ tᵢ ≤ ∑ tᵢ` (each `tᵢ ∈ [0, 1]`)
  have hAMGM : (k : ℝ) * ∏ i, t i ≤ ∑ i, t i := by
    have hprod_le : ∀ j : Fin k, ∏ i, t i ≤ t j := by
      intro j
      calc ∏ i, t i = t j * ∏ i ∈ Finset.univ.erase j, t i :=
            (Finset.mul_prod_erase Finset.univ t (Finset.mem_univ j)).symm
        _ ≤ t j * 1 := by
            apply mul_le_mul_of_nonneg_left _ (htnn j)
            exact Finset.prod_le_one (fun i _ => htnn i) (fun i _ => ht1 i)
        _ = t j := mul_one _
    calc (k : ℝ) * ∏ i, t i
        = ∑ _j : Fin k, ∏ i, t i := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j, t j := Finset.sum_le_sum (fun j _ => hprod_le j)
  -- assemble
  have hPP'trace : (P * P').trace = ∑ i, t i := htrPP'.trans htrG
  rw [hPP'trace] at hnorm
  have hprodeq : ∏ i, t i = (Uᵀ * V).det ^ 2 := by rw [← hdetG, hdetGW, hW]
  have hfinal : 2 * (k : ℝ) - 2 * ∑ i, t i ≤ 2 * (k : ℝ) * (1 - (Uᵀ * V).det ^ 2) := by
    rw [← hprodeq]; nlinarith [hAMGM]
  exact le_trans hnorm hfinal

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

/-! ## L7c.3b — the rank-1 exterior Rayleigh-deficit bound

The orchestrator (L7c.3c) reduces the band-projector increment to a rank-1 dominant-eigenvector
`sin Θ` estimate (the committed/forthcoming `sin_sq_le_rayleigh_deficit_div_gap`). This section
provides the deficit-side pieces feeding that core: the per-vector compound operator-norm step
(Lemma 1), the Rayleigh quotient identity and top-eigenvalue ceiling `μ₀ = ‖compound‖²`
(Lemma 2), and the assembled deficit bound `μ₀ − ⟨C_n v', v'⟩ ≤ (1 − 1/κ²)·μ₀` (Lemma 3),
with `κ = ‖compound B‖·‖(compound B)⁻¹‖` the compound condition number. -/

section Rayleigh

variable {d : ℕ}

/-- Per-vector L2 operator-norm bound for `toEuclideanLin`: `‖toEuclideanLin N w‖ ≤ ‖N‖·‖w‖`.
Routed through the bundled continuous-linear-map `toEuclideanCLM`, whose operator norm is the L2
matrix norm `‖N‖` by `Matrix.l2_opNorm_toEuclideanCLM`. -/
theorem norm_toEuclideanLin_apply_le (N : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin N w‖ ≤ ‖N‖ * ‖w‖ := by
  have hc : (Matrix.toEuclideanLin N w) = Matrix.toEuclideanCLM (𝕜 := ℝ) N w := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
  rw [hc]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N w‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖ * ‖w‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) N).le_opNorm w
    _ = ‖N‖ * ‖w‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]

/-- The `k`-th compound of the identity matrix is the identity. Via the compound bridge
`conjExteriorMap_eq_toEuclideanLin_compound`, since `⋀^k id = id` (`exteriorPower.map_id`). -/
theorem compoundMatrix_one (k : ℕ) :
    compoundMatrix k (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  apply (Matrix.toEuclideanLin (n := Fin _) (m := Fin _)).injective
  rw [← conjExteriorMap_eq_toEuclideanLin_compound]
  have h1 : Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) = LinearMap.id := by
    ext v i; simp
  rw [h1]
  unfold conjExteriorMap
  rw [exteriorPower.map_id]
  have h2 : Matrix.toEuclideanLin
      (1 : Matrix (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))
        (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))) ℝ) = LinearMap.id := by
    ext v i; simp
  rw [h2]
  ext x; simp

/-- For invertible `B`, `compound k B⁻¹` is a right inverse of `compound k B`
(`compoundMatrix_mul` + `compoundMatrix_one`). -/
theorem compoundMatrix_mul_inv (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0) :
    compoundMatrix k B * compoundMatrix k B⁻¹ = 1 := by
  rw [← compoundMatrix_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), compoundMatrix_one]

/-- For invertible `B`, `compound k B⁻¹` is a left inverse of `compound k B`. -/
theorem compoundMatrix_inv_mul (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0) :
    compoundMatrix k B⁻¹ * compoundMatrix k B = 1 := by
  rw [← compoundMatrix_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), compoundMatrix_one]

/-- The compound factorisation `compound M = (compound B)⁻¹ · compound(B · M)`, for invertible
`B`. Used in Lemma 3 to lower-bound `‖compound M‖` by `‖compound(B·M)‖`. -/
theorem compoundMatrix_eq_inv_mul (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    compoundMatrix k M = compoundMatrix k B⁻¹ * compoundMatrix k (B * M) := by
  rw [← compoundMatrix_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hB),
    Matrix.one_mul]

/-- **L7c.4 deliverable (1) — the rank-1 lower bound `μ̃₀ ≥ cM²/cBi²`.** For invertible `B`, the
squared compound operator norm of the perturbed cocycle step `B · M` (= the top eigenvalue `μ̃₀` of
`Cₙ₊₁ = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁`) is bounded below by `cM²/cBi²`, where `cM = ‖compound k M‖` and
`cBi = ‖compound k B⁻¹‖`. Route: `compound k M = compound k B⁻¹ · compound k (B·M)` gives
`cM ≤ cBi·‖compound(B·M)‖`, hence `‖compound(B·M)‖ ≥ cM/cBi`; squaring yields the bound. -/
theorem norm_sq_compound_mul_ge (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0)
    (M : Matrix (Fin d) (Fin d) ℝ) (hcBipos : 0 < ‖compoundMatrix k B⁻¹‖) :
    ‖compoundMatrix k M‖ ^ 2 / ‖compoundMatrix k B⁻¹‖ ^ 2
      ≤ ‖compoundMatrix k (B * M)‖ ^ 2 := by
  -- `cM ≤ cBi · ‖compound(B·M)‖` from the compound factorisation + submultiplicativity.
  have hstep : ‖compoundMatrix k M‖
      ≤ ‖compoundMatrix k B⁻¹‖ * ‖compoundMatrix k (B * M)‖ := by
    conv_lhs => rw [compoundMatrix_eq_inv_mul k hB M]
    exact Matrix.l2_opNorm_mul _ _
  rw [div_le_iff₀ (by positivity)]
  have hcMnn : 0 ≤ ‖compoundMatrix k M‖ := norm_nonneg _
  nlinarith [hstep, hcMnn, norm_nonneg (compoundMatrix k (B * M)), hcBipos]

set_option maxHeartbeats 800000 in
/-- **Lemma 1 — the rank-1 per-vector step.** The squared norm of the compound of a product,
applied to `w`, is dominated by `‖compound B‖²` times the squared norm of the `M`-compound at `w`:
`‖compound(B·M) w‖² ≤ ‖compound B‖²·‖compound M w‖²`. This relates the Rayleigh quotients of the
compound Gram operators `C_{n+1}` (from `B·M`) and `C_n` (from `M`). Via
`toEuclideanLin_compoundMatrix_mul` + the per-vector operator-norm step. -/
theorem rayleigh_compound_mul_le (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))) :
    ‖Matrix.toEuclideanLin (compoundMatrix k (B * M)) w‖ ^ 2
      ≤ ‖compoundMatrix k B‖ ^ 2
        * ‖Matrix.toEuclideanLin (compoundMatrix k M) w‖ ^ 2 := by
  rw [toEuclideanLin_compoundMatrix_mul, LinearMap.comp_apply]
  set a := ‖Matrix.toEuclideanLin (compoundMatrix k M) w‖ with ha
  set b := ‖compoundMatrix k B‖ with hb
  have h : ‖Matrix.toEuclideanLin (compoundMatrix k B)
      (Matrix.toEuclideanLin (compoundMatrix k M) w)‖ ≤ b * a :=
    norm_toEuclideanLin_apply_le _ _
  have han : 0 ≤ a := norm_nonneg _
  have hbn : 0 ≤ b := norm_nonneg _
  calc ‖Matrix.toEuclideanLin (compoundMatrix k B)
        (Matrix.toEuclideanLin (compoundMatrix k M) w)‖ ^ 2
      ≤ (b * a) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) h
    _ = b ^ 2 * a ^ 2 := by ring

/-- **Lemma 2 (Rayleigh identity).** The Rayleigh quotient of the compound Gram operator
`C_n = adjoint(compound M) ∘ₗ compound M` at `w` equals `‖compound M w‖²`. -/
theorem rayleigh_compound_eq_norm_sq (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))) :
    (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
        Matrix.toEuclideanLin (compoundMatrix k M)) w) w : ℝ)
      = ‖Matrix.toEuclideanLin (compoundMatrix k M) w‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- **Lemma 2 (top-eigenvalue ceiling).** The Rayleigh quotient of the compound Gram operator is
bounded by `‖compound M‖²·‖w‖²`; equivalently the top eigenvalue `μ₀` of
`C_n = adjoint(compound M) ∘ₗ compound M` is `‖compound M‖²` (the squared operator norm of the
compound = top eigenvalue of `AᵀA`). -/
theorem rayleigh_compound_le (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))) :
    (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
        Matrix.toEuclideanLin (compoundMatrix k M)) w) w : ℝ)
      ≤ ‖compoundMatrix k M‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [rayleigh_compound_eq_norm_sq]
  have h := norm_toEuclideanLin_apply_le (compoundMatrix k M) w
  have hn := norm_nonneg (Matrix.toEuclideanLin (compoundMatrix k M) w)
  nlinarith [h, norm_nonneg (compoundMatrix k M), norm_nonneg w]

/-- Pure-real algebraic kernel of the deficit bound: from `BM ≤ CB·r` and `mu ≤ CBi·BM` (with all
nonnegative) one gets `mu² − r² ≤ (1 − 1/(CB·CBi)²)·mu²`. -/
theorem rayleigh_deficit_kernel {BM CB r CBi mu : ℝ}
    (hCBn : 0 ≤ CB) (hCBin : 0 ≤ CBi) (hmun : 0 ≤ mu)
    (hstep1 : BM ≤ CB * r) (hstep2 : mu ≤ CBi * BM) :
    mu ^ 2 - r ^ 2 ≤ (1 - 1 / (CB * CBi) ^ 2) * mu ^ 2 := by
  by_cases hκ : CB * CBi = 0
  · have h0 : (CB * CBi) ^ 2 = 0 := by rw [hκ]; ring
    rw [h0]; simp only [div_zero, sub_zero, one_mul]
    nlinarith [sq_nonneg r]
  · have hκpos : 0 < CB * CBi := lt_of_le_of_ne (by positivity) (Ne.symm hκ)
    have hchain : mu ≤ (CB * CBi) * r := by
      calc mu ≤ CBi * BM := hstep2
        _ ≤ CBi * (CB * r) := by nlinarith [hstep1, hCBin]
        _ = (CB * CBi) * r := by ring
    have hrlb : mu / (CB * CBi) ≤ r := by rw [div_le_iff₀ hκpos]; linarith
    have hr2 : (mu / (CB * CBi)) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hrlb 2
    rw [div_pow] at hr2
    have heq : mu ^ 2 - mu ^ 2 / (CB * CBi) ^ 2 = (1 - 1 / (CB * CBi) ^ 2) * mu ^ 2 := by ring
    linarith [hr2, heq.ge, heq.le]

set_option maxHeartbeats 1600000 in
/-- **Lemma 3 — the rank-1 exterior Rayleigh-deficit bound.**
For invertible `B` and a unit vector `v'` that achieves the operator norm of the compound
`compound (B·M)` (so `‖compound(B·M) v'‖ = ‖compound(B·M)‖`, i.e. `v'` is a top right-singular
vector / dominant eigenvector of `C_{n+1}`), the Rayleigh deficit of the operator
`C_n = adjoint(compound M) ∘ₗ compound M` at `v'` against its top value `μ₀ = ‖compound M‖²`
obeys `μ₀ − ⟨C_n v', v'⟩ ≤ (1 − 1/κ²)·μ₀` with `κ = ‖compound B‖·‖(compound B)⁻¹‖`.

This is the deficit-side input to `sin_sq_le_rayleigh_deficit_div_gap` (with
`ε := μ₀ − ⟨C_n v', v'⟩`, `μ₀ := ‖compound M‖²`). The `v'`-achieves-the-op-norm hypothesis encodes
that `v'` is the top eigenvector of `C_{n+1}`; its existence is the caller's responsibility. -/
theorem rayleigh_deficit_le (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.det ≠ 0)
    (M : Matrix (Fin d) (Fin d) ℝ)
    {v' : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))}
    (htop : ‖Matrix.toEuclideanLin (compoundMatrix k (B * M)) v'‖ = ‖compoundMatrix k (B * M)‖) :
    ‖compoundMatrix k M‖ ^ 2
        - (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
            Matrix.toEuclideanLin (compoundMatrix k M)) v') v' : ℝ)
      ≤ (1 - 1 / (‖compoundMatrix k B‖ * ‖compoundMatrix k B⁻¹‖) ^ 2)
          * ‖compoundMatrix k M‖ ^ 2 := by
  rw [rayleigh_compound_eq_norm_sq]
  -- (1) `v'` achieves the op-norm of `compound(B·M)`, then the per-vector step:
  --     `‖compound(B·M)‖ ≤ ‖compound B‖·‖compound M v'‖`.
  have hstep1 : ‖compoundMatrix k (B * M)‖
      ≤ ‖compoundMatrix k B‖ * ‖Matrix.toEuclideanLin (compoundMatrix k M) v'‖ := by
    rw [← htop, toEuclideanLin_compoundMatrix_mul, LinearMap.comp_apply]
    exact norm_toEuclideanLin_apply_le _ _
  -- (2) `‖compound M‖ ≤ ‖(compound B)⁻¹‖·‖compound(B·M)‖` from the compound factorisation.
  have hstep2 : ‖compoundMatrix k M‖
      ≤ ‖compoundMatrix k B⁻¹‖ * ‖compoundMatrix k (B * M)‖ := by
    conv_lhs => rw [compoundMatrix_eq_inv_mul k hB M]
    exact Matrix.l2_opNorm_mul _ _
  exact rayleigh_deficit_kernel (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hstep1 hstep2

end Rayleigh

/-! ## L7c.3b (corrected §J) — the off-diagonal residual estimate and the perturbed Gram ceiling

The corrected route (§J of `oseledets-l7c-route.md`) replaces the circular Rayleigh-deficit bound by
the refined Davis–Kahan sin-Θ in **off-diagonal/residual form** (`offdiag_sin_le_residual_div_gap`,
committed in `OseledetsLimit.lean`). That sin-Θ core needs two cocycle-specific inputs:

* the **off-diagonal residual numerator** `‖Cₙ₊₁ v₀ − ⟪Cₙ₊₁ v₀, v₀⟫ v₀‖ ≤ τ₀ τ₁ ‖H‖²`, where
  `Cₙ₊₁ = adjoint G' ∘ₗ G'`, `G' = H ∘ₗ G`, and `v₀` is the top eigenvector of `Cₙ = adjoint G ∘ₗ G`
  (`offdiag_residual_norm_le`);
* the **`ν`-ceiling** `∀ z ⊥ v₀, ⟪Cₙ₊₁ z, z⟫ ≤ (μ₁ ‖H‖²) ‖z‖²` transported from the `Cₙ`-ceiling
  `∀ z ⊥ v₀, ⟪Cₙ z, z⟫ ≤ μ₁ ‖z‖²` (`perturbed_gram_ceiling`).

Both are abstract operator facts (no compound/exterior structure); the cocycle specialisation in
standard coordinates (where `G = toEuclideanLin (compoundMatrix k ·)`) follows by
`toEuclideanLin_compoundMatrix_mul` (functoriality `G' = H ∘ₗ G`) and the per-vector operator-norm
bound `norm_toEuclideanLin_apply_le`. These pieces feed the band-projector increment bound (L7c.3c)
together with the committed back-transport `norm_proj_sub_le_wedge`. -/

section OffDiag

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

open scoped RealInnerProductSpace

/-- **J2.a — the off-diagonal residual is orthogonal to `v₀`.** For a unit `v₀`, the residual
`C v₀ − ⟪C v₀, v₀⟫ v₀ = (I − P) C v₀` is orthogonal to `v₀`. -/
theorem residual_orthogonal {C : E →ₗ[ℝ] E} {v₀ : E} (hv₀ : ‖v₀‖ = 1) :
    (inner ℝ (C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀) v₀ : ℝ) = 0 := by
  have hv₀v₀ : (inner ℝ v₀ v₀ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  rw [inner_sub_left, real_inner_smul_left, hv₀v₀, mul_one, sub_self]

/-- **J2.b — Rayleigh of the Gram operator is the squared norm.** `⟪(adjoint G ∘ₗ G) v, v⟫ = ‖G v‖²`
(abstract form; `rayleigh_compound_eq_norm_sq` is the compound-matrix specialisation). -/
theorem gram_rayleigh_eq_norm_sq (G : E →ₗ[ℝ] F) (v : E) :
    (inner ℝ ((LinearMap.adjoint G ∘ₗ G) v) v : ℝ) = ‖G v‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- **J2.c — the off-diagonal inner product reduction.** `⟪(adjoint G' ∘ₗ G') v₀, z⟫ = ⟪G' v₀, G' z⟫`
(plain adjoint move; for `z ⊥ v₀` this is the off-diagonal block of `Cₙ₊₁`). -/
theorem offdiag_inner_eq (G' : E →ₗ[ℝ] F) (v₀ z : E) :
    (inner ℝ ((LinearMap.adjoint G' ∘ₗ G') v₀) z : ℝ) = inner ℝ (G' v₀) (G' z) := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]

/-- **NODE 1 (L7c.3b, §J.2) — the off-diagonal residual norm estimate.**
For the perturbed Gram operator `Cₙ₊₁ = adjoint G' ∘ₗ G'` with `G' = H ∘ₗ G` (functoriality) and
`v₀` the top unit eigenvector of `Cₙ = adjoint G ∘ₗ G`, the off-diagonal residual
`Cₙ₊₁ v₀ − ⟪Cₙ₊₁ v₀, v₀⟫ v₀` has norm at most `τ₀ · τ₁ · ‖H‖²`, where `τ₀ = ‖G v₀‖` (the top
singular value of `G`) and `τ₁` is the second-singular-value ceiling on `v₀^⊥`
(`hperp : ∀ z ⊥ v₀, ‖z‖ ≤ 1 → ‖G z‖ ≤ τ₁`).

Proof (§J.2): the residual `res ⊥ v₀`; `‖res‖² = ⟪res, res⟫ = ⟪Cₙ₊₁ v₀, res⟫` (since `res ⊥ v₀`)
`= ⟪H G v₀, H G res⟫ ≤ ‖H‖²‖G v₀‖‖G res‖ ≤ ‖H‖² τ₀ τ₁ ‖res‖` by Cauchy–Schwarz, the per-vector
operator-norm bound on `H`, `htop`, and `hperp` applied to the unit normalisation of `res`. Dividing
by `‖res‖` gives the bound. -/
theorem offdiag_residual_norm_le
    {G : E →ₗ[ℝ] F} {H : F →ₗ[ℝ] F} {G' : E →ₗ[ℝ] F}
    (hcomp : G' = H ∘ₗ G)
    {v₀ : E} {τ₀ τ₁ nH : ℝ} (hτ₀ : 0 ≤ τ₀) (hτ₁ : 0 ≤ τ₁) (hnH : 0 ≤ nH) (hv₀ : ‖v₀‖ = 1)
    (htop : ‖G v₀‖ = τ₀)
    (hH : ∀ y, ‖H y‖ ≤ nH * ‖y‖)
    (hperp : ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 → ‖z‖ ≤ 1 → ‖G z‖ ≤ τ₁) :
    ‖(LinearMap.adjoint G' ∘ₗ G') v₀ - (inner ℝ ((LinearMap.adjoint G' ∘ₗ G') v₀) v₀ : ℝ) • v₀‖
      ≤ τ₀ * τ₁ * nH ^ 2 := by
  set C := LinearMap.adjoint G' ∘ₗ G' with hC
  set res := C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀ with hres
  have hresperp : (inner ℝ res v₀ : ℝ) = 0 := residual_orthogonal hv₀
  -- key inner bound: for z ⊥ v₀, ⟪res, z⟫ ≤ τ₀τ₁nH² ‖z‖
  have hkey : ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ res z : ℝ) ≤ τ₀ * τ₁ * nH ^ 2 * ‖z‖ := by
    intro z hz
    have hrz : (inner ℝ res z : ℝ) = inner ℝ (C v₀) z := by
      rw [hres, inner_sub_left, real_inner_smul_left,
        show (inner ℝ v₀ z : ℝ) = inner ℝ z v₀ from real_inner_comm z v₀, hz, mul_zero, sub_zero]
    rw [hrz, hC, offdiag_inner_eq, hcomp]
    simp only [LinearMap.comp_apply]
    rcases eq_or_lt_of_le (norm_nonneg z) with hz0 | hzpos
    · have : z = 0 := by rw [← norm_eq_zero]; exact hz0.symm
      subst this; simp
    · have hznorm : ‖z‖ ≠ 0 := ne_of_gt hzpos
      have hzu : ‖(‖z‖⁻¹ : ℝ) • z‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ hznorm]
      have hzuperp : (inner ℝ ((‖z‖⁻¹ : ℝ) • z) v₀ : ℝ) = 0 := by
        rw [real_inner_smul_left, hz, mul_zero]
      have hGzu : ‖G ((‖z‖⁻¹ : ℝ) • z)‖ ≤ τ₁ := hperp _ hzuperp hzu
      have hGz : ‖G z‖ ≤ τ₁ * ‖z‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hGzu
        rw [inv_mul_le_iff₀ hzpos] at hGzu
        linarith [hGzu]
      calc (inner ℝ (H (G v₀)) (H (G z)) : ℝ)
          ≤ ‖H (G v₀)‖ * ‖H (G z)‖ := real_inner_le_norm _ _
        _ ≤ (nH * ‖G v₀‖) * (nH * ‖G z‖) := by
            apply mul_le_mul (hH _) (hH _) (norm_nonneg _); positivity
        _ ≤ (nH * τ₀) * (nH * (τ₁ * ‖z‖)) := by rw [htop]; gcongr
        _ = τ₀ * τ₁ * nH ^ 2 * ‖z‖ := by ring
  rcases eq_or_lt_of_le (norm_nonneg res) with hr0 | hrpos
  · rw [hres] at hr0 ⊢; rw [← hr0]; positivity
  · have hself : (inner ℝ res res : ℝ) = ‖res‖ ^ 2 := real_inner_self_eq_norm_sq res
    have hb := hkey res hresperp
    rw [hself] at hb
    have hmul : ‖res‖ * ‖res‖ ≤ (τ₀ * τ₁ * nH ^ 2) * ‖res‖ := by nlinarith [hb]
    exact le_of_mul_le_mul_right hmul hrpos

/-- **NODE 1 ceiling (L7c.3b.ν, §J.3) — the `ν`-ceiling for the perturbed Gram operator.**
From a Rayleigh ceiling `∀ z ⊥ v₀, ⟪Cₙ z, z⟫ ≤ μ₁ ‖z‖²` on the unperturbed Gram operator
`Cₙ = adjoint G ∘ₗ G`, the perturbed operator `Cₙ₊₁ = adjoint G' ∘ₗ G'` with `G' = H ∘ₗ G` obeys
the amplified ceiling `∀ z ⊥ v₀, ⟪Cₙ₊₁ z, z⟫ ≤ (μ₁ ‖H‖²) ‖z‖²`. Proof: `⟪Cₙ₊₁ z, z⟫ = ‖H G z‖²
≤ ‖H‖² ‖G z‖² = ‖H‖² ⟪Cₙ z, z⟫ ≤ ‖H‖² μ₁ ‖z‖²`. This supplies the `ν := μ₁ ‖H‖²` ceiling consumed
by `offdiag_sin_le_residual_div_gap`. -/
theorem perturbed_gram_ceiling
    {G : E →ₗ[ℝ] F} {H : F →ₗ[ℝ] F} {G' : E →ₗ[ℝ] F}
    (hcomp : G' = H ∘ₗ G)
    {v₀ : E} {μ₁ nH : ℝ}
    (hH : ∀ y, ‖H y‖ ≤ nH * ‖y‖)
    (hceil : ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2) :
    ∀ z : E, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint G' ∘ₗ G') z) z : ℝ) ≤ (μ₁ * nH ^ 2) * ‖z‖ ^ 2 := by
  intro z hz
  rw [gram_rayleigh_eq_norm_sq, hcomp, LinearMap.comp_apply]
  have h1 : ‖H (G z)‖ ^ 2 ≤ nH ^ 2 * ‖G z‖ ^ 2 := by
    have := hH (G z); nlinarith [this, norm_nonneg (G z), norm_nonneg (H (G z))]
  have h2 : ‖G z‖ ^ 2 = (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) :=
    (gram_rayleigh_eq_norm_sq G z).symm
  have h3 : (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2 := hceil z hz
  calc ‖H (G z)‖ ^ 2 ≤ nH ^ 2 * ‖G z‖ ^ 2 := h1
    _ = nH ^ 2 * (inner ℝ ((LinearMap.adjoint G ∘ₗ G) z) z : ℝ) := by rw [h2]
    _ ≤ nH ^ 2 * (μ₁ * ‖z‖ ^ 2) := by apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (μ₁ * nH ^ 2) * ‖z‖ ^ 2 := by ring

end OffDiag

/-! ### The cocycle specialisation of NODE 1 (compound-matrix coordinates)

Specialising `offdiag_residual_norm_le` / `perturbed_gram_ceiling` to the cocycle Gram operators
`Cₙ = adjoint Gₙ ∘ₗ Gₙ`, `Gₙ = toEuclideanLin (compoundMatrix k Mₙ)`, with the one-step left factor
`B = A(Tⁿx)` (so `Mₙ₊₁ = B · Mₙ` and `Gₙ₊₁ = (compound B) ∘ Gₙ` by
`toEuclideanLin_compoundMatrix_mul`). The SVD ceiling `hperp` of the abstract lemma is discharged
from a `μ₁`-ceiling on `Cₙ` via `rayleigh_compound_eq_norm_sq`:
`‖Gₙ z‖² = ⟪Cₙ z, z⟫ ≤ μ₁ ‖z‖² ≤ μ₁` for `‖z‖ ≤ 1`, hence `‖Gₙ z‖ ≤ √μ₁ =: τ₁`. -/

section CompoundOffDiag

variable {d : ℕ}

open scoped RealInnerProductSpace

/-- **NODE 1 (cocycle, §J.2) — the off-diagonal residual estimate for the compound Gram operators.**
With `Gₙ = toEuclideanLin (compoundMatrix k M)`, `Cₙ = adjoint Gₙ ∘ₗ Gₙ`, the one-step left factor
`B`, and `Cₙ₊₁ = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁` for `Gₙ₊₁ = toEuclideanLin (compoundMatrix k (B * M))`: if
`v₀` is a unit vector achieving the compound operator norm `‖Gₙ v₀‖ = ‖compoundMatrix k M‖ = τ₀`
(the top right-singular vector of `Gₙ`, i.e. the top eigenvector of `Cₙ`) with a `μ₁`-Rayleigh
ceiling on `v₀^⊥`, then the off-diagonal residual obeys
`‖Cₙ₊₁ v₀ − ⟪Cₙ₊₁ v₀, v₀⟫ v₀‖ ≤ ‖compoundMatrix k M‖ · √μ₁ · ‖compoundMatrix k B‖²`.
(`τ₀ = ‖compoundMatrix k M‖`, `τ₁ = √μ₁`, `‖H‖ = ‖compoundMatrix k B‖`.) -/
theorem norm_offdiag_residual_compound_le (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ)
    {v₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))}
    {μ₁ : ℝ} (hμ₁ : 0 ≤ μ₁) (hv₀ : ‖v₀‖ = 1)
    (htop : ‖Matrix.toEuclideanLin (compoundMatrix k M) v₀‖ = ‖compoundMatrix k M‖)
    (hceil : ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k M)) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2) :
    ‖(LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k (B * M))) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k (B * M))) v₀
        - (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k (B * M))) ∘ₗ
            Matrix.toEuclideanLin (compoundMatrix k (B * M))) v₀) v₀ : ℝ) • v₀‖
      ≤ ‖compoundMatrix k M‖ * Real.sqrt μ₁ * ‖compoundMatrix k B‖ ^ 2 := by
  -- discharge `hperp`: `‖Gₙ z‖ ≤ √μ₁` for `z ⊥ v₀`, `‖z‖ ≤ 1`.
  have hperp : ∀ z, (inner ℝ z v₀ : ℝ) = 0 → ‖z‖ ≤ 1 →
      ‖Matrix.toEuclideanLin (compoundMatrix k M) z‖ ≤ Real.sqrt μ₁ := by
    intro z hz hzn
    have hsq : ‖Matrix.toEuclideanLin (compoundMatrix k M) z‖ ^ 2 ≤ μ₁ := by
      rw [← rayleigh_compound_eq_norm_sq k M z]
      calc (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
              Matrix.toEuclideanLin (compoundMatrix k M)) z) z : ℝ)
          ≤ μ₁ * ‖z‖ ^ 2 := hceil z hz
        _ ≤ μ₁ * 1 ^ 2 := by gcongr
        _ = μ₁ := by ring
    have hnn := norm_nonneg (Matrix.toEuclideanLin (compoundMatrix k M) z)
    calc ‖Matrix.toEuclideanLin (compoundMatrix k M) z‖
        = Real.sqrt (‖Matrix.toEuclideanLin (compoundMatrix k M) z‖ ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt μ₁ := Real.sqrt_le_sqrt hsq
  -- apply the abstract NODE 1 with the functoriality `G' = H ∘ₗ G`.
  exact offdiag_residual_norm_le
    (G := Matrix.toEuclideanLin (compoundMatrix k M))
    (H := Matrix.toEuclideanLin (compoundMatrix k B))
    (G' := Matrix.toEuclideanLin (compoundMatrix k (B * M)))
    (toEuclideanLin_compoundMatrix_mul k B M)
    (norm_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _) hv₀ htop
    (fun y => norm_toEuclideanLin_apply_le (compoundMatrix k B) y)
    hperp

/-- **NODE 1 ceiling (cocycle, §J.3) — the `ν`-ceiling for the perturbed compound Gram operator.**
From a `μ₁`-Rayleigh ceiling on `Cₙ = adjoint Gₙ ∘ₗ Gₙ` over `v₀^⊥`, the perturbed compound Gram
operator `Cₙ₊₁ = adjoint Gₙ₊₁ ∘ₗ Gₙ₊₁` (with `Gₙ₊₁ = toEuclideanLin (compoundMatrix k (B * M))`)
obeys the amplified ceiling `∀ z ⊥ v₀, ⟪Cₙ₊₁ z, z⟫ ≤ (μ₁ ‖compoundMatrix k B‖²) ‖z‖²`. This is the
`ν := μ₁ ‖H‖²` ceiling consumed by `offdiag_sin_le_residual_div_gap`. -/
theorem perturbed_compound_gram_ceiling (k : ℕ) (B M : Matrix (Fin d) (Fin d) ℝ)
    {v₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))}
    {μ₁ : ℝ}
    (hceil : ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k M)) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k M)) z) z : ℝ) ≤ μ₁ * ‖z‖ ^ 2) :
    ∀ z, (inner ℝ z v₀ : ℝ) = 0 →
      (inner ℝ ((LinearMap.adjoint (Matrix.toEuclideanLin (compoundMatrix k (B * M))) ∘ₗ
          Matrix.toEuclideanLin (compoundMatrix k (B * M))) z) z : ℝ)
        ≤ (μ₁ * ‖compoundMatrix k B‖ ^ 2) * ‖z‖ ^ 2 :=
  perturbed_gram_ceiling
    (G := Matrix.toEuclideanLin (compoundMatrix k M))
    (H := Matrix.toEuclideanLin (compoundMatrix k B))
    (G' := Matrix.toEuclideanLin (compoundMatrix k (B * M)))
    (toEuclideanLin_compoundMatrix_mul k B M)
    (fun y => norm_toEuclideanLin_apply_le (compoundMatrix k B) y)
    hceil

end CompoundOffDiag

/-! ## The Plücker bridge (PB1/PB2/PB3)

For a symmetric PD map `f` with orthonormal eigenbasis `u` and eigenvalues `lam`, the compound
`⋀^k f`, conjugated through the eigenbasis wedge trivialization `onbTriv u`, is a **diagonal**
Euclidean operator: it scales `basisFun i` by the subset product `∏_{a ∈ Sᵢ} lam a`. The top set
`{0,…,k-1}` (maximal by `prod_le_prod_top` for antitone weights) gives the top eigenvector
`v₀ = basisFun i₀` with eigenvalue `μ₀` (PB1), and every other weight is `≤ μ₁` (PB2). PB3 is the
det-Gram identity for the Plücker (wedge) inner product. -/

section Plucker

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Classical in
/-- **The conjugated compound is diagonal in the eigenbasis.** For a symmetric `f` with orthonormal
eigenbasis `u` and eigenvalues `lam`, conjugating `⋀^k f` through the eigenbasis wedge
trivialization `onbTriv u` yields a diagonal Euclidean operator: `basisFun i ↦ (∏_{a ∈ Sᵢ} lam a) •
basisFun i`, where `Sᵢ = (wIndexEquiv u k).symm i`. -/
private lemma conjExteriorMap_onbTriv_diag {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : E →ₗ[ℝ] E) (u : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hf : ∀ i, f (u i) = lam i • u i) (k : ℕ)
    (i : Fin (Module.finrank ℝ (⋀[ℝ]^k E))) :
    conjExteriorMap k (onbTriv u k) (onbTriv u k) f (EuclideanSpace.basisFun _ ℝ i)
      = (∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard ι k).val, lam a)
          • EuclideanSpace.basisFun _ ℝ i := by
  classical
  -- `conjExteriorMap ... (basisFun i) = onbTriv u (⋀^k f (wedge u_{Sᵢ}))`.
  rw [conjExteriorMap]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show (onbTriv u k).symm (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) ℝ i)
      = (u.toBasis.exteriorPower k) ((wIndexEquiv u k).symm i) by
    rw [LinearEquiv.symm_apply_eq]; exact (onbTriv_wedge_eq_basisFun u k i).symm]
  rw [map_exteriorPower_wedgeBasis_eq f u lam hf k, map_smul, onbTriv_wedge_eq_basisFun]

open scoped Classical in
/-- **PB3 — the Plücker (wedge) inner product is the cross-Gram determinant.** For two families
`v, w : Fin k → E`, the L2 inner product of their Hodge-trivialized wedges equals the determinant
of the cross-Gram matrix `⟪v j, w i⟫`. With orthonormal frames this is the wedge-sine identity
`⟪w_E, w_E'⟫ = det(UᵀV)` feeding the Frobenius back-transport `norm_proj_sub_le_wedge`. -/
theorem inner_hodgeTrivialization_ιMulti (k : ℕ) (v w : Fin k → E) :
    (inner ℝ (hodgeTrivialization k (exteriorPower.ιMulti ℝ k v))
        (hodgeTrivialization k (exteriorPower.ιMulti ℝ k w)) : ℝ)
      = (Matrix.of fun i j => (inner ℝ (v j) (w i) : ℝ)).det := by
  classical
  -- the Hodge trivialization is the standard o.n.-basis wedge trivialization.
  have hStd : hodgeTrivialization (E := E) k = onbTriv (stdOrthonormalBasis ℝ E) k := by
    unfold hodgeTrivialization onbTriv wedgeBasis wedgeIndexEquiv wIndexEquiv
    rfl
  rw [hStd, inner_onbTriv, hodgeForm_ιMulti]

/-! ### Abstract diagonal Euclidean operators: eigenpair and second-eigenvalue ceiling -/

/-- A Euclidean operator diagonal in the standard basis (with real weights) is symmetric. -/
private lemma diag_isSymmetric {N : ℕ}
    (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) (c : Fin N → ℝ)
    (hg : ∀ i, g (EuclideanSpace.basisFun (Fin N) ℝ i) = c i • EuclideanSpace.basisFun (Fin N) ℝ i) :
    g.IsSymmetric := by
  -- check symmetry on the standard basis, then extend bilinearly.
  have hbasis : ∀ i j, (inner ℝ (g (EuclideanSpace.basisFun (Fin N) ℝ i))
      (EuclideanSpace.basisFun (Fin N) ℝ j) : ℝ)
      = inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (g (EuclideanSpace.basisFun (Fin N) ℝ j)) := by
    intro i j
    rw [hg i, hg j, inner_smul_left, inner_smul_right,
      (EuclideanSpace.basisFun (Fin N) ℝ).inner_eq_ite i j]
    simp only [RCLike.conj_to_real]
    by_cases h : i = j <;> simp [h]
  intro x y
  have hx := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr x
  have hy := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr y
  rw [← hx, ← hy]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, EuclideanSpace.basisFun_repr]
  apply Finset.sum_congr rfl; intro i _
  congr 1
  apply Finset.sum_congr rfl; intro j _
  rw [hbasis j i]

/-- **PB1 (abstract).** A Euclidean operator `g` diagonal in the standard basis with weights `c`
(`g (basisFun i) = c i • basisFun i`) has `basisFun i₀` as an eigenvector with eigenvalue `c i₀`. -/
private lemma diag_apply_basisFun_eigenpair {N : ℕ}
    (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) (c : Fin N → ℝ)
    (hg : ∀ i, g (EuclideanSpace.basisFun (Fin N) ℝ i) = c i • EuclideanSpace.basisFun (Fin N) ℝ i)
    (i₀ : Fin N) :
    g (EuclideanSpace.basisFun (Fin N) ℝ i₀) = c i₀ • EuclideanSpace.basisFun (Fin N) ℝ i₀ :=
  hg i₀

/-- **PB2 (abstract).** For a diagonal Euclidean operator `g` with weights `c`, the Rayleigh
quotient on a vector `w` orthogonal to `basisFun i₀` is bounded by `μ₁ ‖w‖²`, provided every weight
off the top index `i₀` is `≤ μ₁` (and `0 ≤ μ₁`). -/
private lemma diag_rayleigh_ceiling {N : ℕ}
    (g : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) (c : Fin N → ℝ)
    (hg : ∀ i, g (EuclideanSpace.basisFun (Fin N) ℝ i) = c i • EuclideanSpace.basisFun (Fin N) ℝ i)
    {μ₁ : ℝ} (i₀ : Fin N) (hcap : ∀ i, i ≠ i₀ → c i ≤ μ₁) (_hμpos : 0 ≤ μ₁)
    (w : EuclideanSpace ℝ (Fin N)) (hw : (inner ℝ w (EuclideanSpace.basisFun (Fin N) ℝ i₀) : ℝ) = 0) :
    (inner ℝ (g w) w : ℝ) ≤ μ₁ * ‖w‖ ^ 2 := by
  -- expand `w` in the standard basis; the Rayleigh quotient is the weighted sum `∑ cᵢ (wᵢ)²`.
  have hwi₀ : w i₀ = 0 := by
    have := hw
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right] at this
    simpa using this
  have hexp : w = ∑ i, (w i) • EuclideanSpace.basisFun (Fin N) ℝ i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr w]
    simp only [EuclideanSpace.basisFun_repr]
  have hgw : g w = ∑ i, (w i) • (c i • EuclideanSpace.basisFun (Fin N) ℝ i) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hg i]
  -- `⟪g w, w⟫ = ∑ cᵢ (wᵢ)²`.
  have hray : (inner ℝ (g w) w : ℝ) = ∑ i, c i * (w i) ^ 2 := by
    rw [hgw, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_left, inner_smul_left, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul]
    simp only [RCLike.conj_to_real]
    ring
  -- `‖w‖² = ∑ (wᵢ)²`.
  have hnorm : ‖w‖ ^ 2 = ∑ i, (w i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RCLike.inner_apply, conj_trivial]; ring
  rw [hray, hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = i₀
  · subst hi; rw [hwi₀]; simp
  · rw [mul_comm (c i), mul_comm μ₁]
    exact mul_le_mul_of_nonneg_left (hcap i hi) (sq_nonneg _)

/-! ### The Plücker eigenpair and second-eigenvalue ceiling (PB1 + PB2 assembled) -/

open scoped Classical in
/-- **PB1 + PB2 — the Plücker bridge for a symmetric map.** Let `f` be symmetric with orthonormal
eigenbasis `u : OrthonormalBasis (Fin n)` and antitone nonnegative eigenvalues
`lam : ℕ → ℝ` (`f (u i) = lam i • u i`). At a genuine gap `lam k < lam (k-1)` (with `1 ≤ k ≤ n`),
the conjugated compound `C = ⋀^k f` (through the eigenbasis wedge trivialization `onbTriv u`) is a
**symmetric operator** with:

* **top eigenpair (PB1):** `C v₀ = μ₀ • v₀`, where `v₀ = basisFun i₀` is the Plücker image of the
  top-`k` eigenframe and `μ₀ = ∏_{i<k} lam i`;
* **second-eigenvalue ceiling (PB2):** `∀ w ⊥ v₀, ⟪C w, w⟫ ≤ μ₁ ‖w‖²` with
  `μ₁ = (∏_{i<k-1} lam i)·lam k`;
* **the gap:** `μ₁ < μ₀`.

This lands in exactly the shape consumed by `sin_sq_le_rayleigh_deficit_div_gap` (`hC`, `hv₀`,
`hev`, `hgap`, `hμ₁`). -/
theorem plucker_eigenpair_ceiling {n : ℕ} (f : E →ₗ[ℝ] E)
    (u : OrthonormalBasis (Fin n) ℝ E) (lam : ℕ → ℝ) (hanti : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hf : ∀ i, f (u i) = lam (i : ℕ) • u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hgap : lam k < lam (k - 1)) :
    ∃ i₀ : Fin (Module.finrank ℝ (⋀[ℝ]^k E)),
      (conjExteriorMap k (onbTriv u k) (onbTriv u k) f).IsSymmetric
      ∧ conjExteriorMap k (onbTriv u k) (onbTriv u k) f
          (EuclideanSpace.basisFun _ ℝ i₀)
        = (∏ i ∈ Finset.range k, lam i) • EuclideanSpace.basisFun _ ℝ i₀
      ∧ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) < (∏ i ∈ Finset.range k, lam i)
      ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))),
          (inner ℝ w (EuclideanSpace.basisFun _ ℝ i₀) : ℝ) = 0 →
          (inner ℝ ((conjExteriorMap k (onbTriv u k) (onbTriv u k) f) w) w : ℝ)
            ≤ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) * ‖w‖ ^ 2 := by
  classical
  set N := Module.finrank ℝ (⋀[ℝ]^k E) with hN
  set C := conjExteriorMap k (onbTriv u k) (onbTriv u k) f with hC
  -- the diagonal weight `c i = ∏_{a ∈ Sᵢ} lam a`.
  set c : Fin N → ℝ := fun i =>
    ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val, lam (a : ℕ) with hcdef
  -- the diagonalization: `C (basisFun i) = c i • basisFun i`.
  have hCdiag : ∀ i, C (EuclideanSpace.basisFun (Fin N) ℝ i)
      = c i • EuclideanSpace.basisFun (Fin N) ℝ i := by
    intro i
    rw [hC, conjExteriorMap_onbTriv_diag f u (fun j => lam (j : ℕ)) hf k]
  -- the top prefix embedding/set and its index `i₀`.
  set topEmb : Fin k ↪o Fin n :=
    { toFun := fun i => ⟨i, lt_of_lt_of_le i.2 hkn⟩
      inj' := fun i j h => Fin.ext (by simpa using congrArg Fin.val h)
      map_rel_iff' := Iff.rfl } with htopEmb
  set topSet : Set.powersetCard (Fin n) k := Set.powersetCard.ofFinEmbEquiv topEmb with htopSet
  set i₀ : Fin N := wIndexEquiv u k topSet with hi₀def
  have hS₀ : (wIndexEquiv u k).symm i₀ = topSet := by rw [hi₀def, Equiv.symm_apply_apply]
  have htopval : ∀ i : Fin k, (topEmb i : Fin n).val = (i : ℕ) := fun _ => rfl
  -- `∏_{a ∈ topSet} g a = ∏_{j} g (topEmb j)` for any `g`.
  have htopprod : ∀ g : Fin n → ℝ, ∏ a ∈ topSet.val, g a = ∏ j, g (topEmb j) := by
    intro g
    have hval : topSet.val = Finset.univ.image (topEmb) := by
      ext x
      rw [Finset.mem_image,
        show x ∈ topSet.val ↔ x ∈ topSet from Iff.rfl, htopSet,
        Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range]
      constructor
      · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
      · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
    rw [hval, Finset.prod_image (fun x _ y _ h => topEmb.injective h)]
  -- the top weight `c i₀ = ∏_{i<k} lam i = μ₀`.
  set μ₀ : ℝ := ∏ i ∈ Finset.range k, lam i with hμ₀
  set μ₁ : ℝ := (∏ i ∈ Finset.range (k-1), lam i) * lam k with hμ₁
  have hci₀ : c i₀ = μ₀ := by
    rw [hcdef]; simp only
    rw [hS₀, htopprod (fun a => lam (a : ℕ)), hμ₀, Finset.prod_range fun i => lam i]
    exact Finset.prod_congr rfl (fun j _ => by simp only [htopval])
  -- maximality: `c i ≤ μ₀` for all i.
  have hmax : ∀ i, c i ≤ μ₀ := by
    intro i
    rw [hcdef]; simp only
    rw [hμ₀, Finset.prod_range fun j => lam j]
    have hconv : ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val, lam (a : ℕ)
        = ∏ a ∈ ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k).val,
            (fun b : Fin n => lam (b : ℕ)) a := rfl
    rw [hconv]
    refine le_trans (prod_le_prod_top (fun b : Fin n => lam (b : ℕ)) ?_ ?_
      ((wIndexEquiv u k).symm i) topEmb htopval) ?_
    · exact fun a b hab => hanti (by exact_mod_cast (Fin.le_def.mp hab))
    · exact fun a => hpos _
    · exact le_of_eq (Finset.prod_congr rfl (fun j _ => by simp only [htopval]))
  -- second-largest: `c i ≤ μ₁` for `i ≠ i₀`.
  have hsecond : ∀ i, i ≠ i₀ → c i ≤ μ₁ := by
    intro i hi
    rw [hcdef]; simp only
    -- the enumeration of `Sᵢ` and the non-top fact.
    set S := ((wIndexEquiv u k).symm i : Set.powersetCard (Fin n) k) with hS
    set e := Set.powersetCard.ofFinEmbEquiv.symm S with he
    have hSne : S ≠ topSet := by
      intro h
      apply hi
      rw [hi₀def, ← h, hS, Equiv.apply_symm_apply]
    -- `∏_{a∈S} lam a = ∏_j lam (e j)`.
    have hprodeq : ∏ a ∈ (S : Finset (Fin n)), lam (a : ℕ) = ∏ j, lam (e j : ℕ) := by
      rw [he]; exact (prod_ofFinEmbEquiv_symm (fun a : Fin n => lam (a : ℕ)) S).symm
    rw [hprodeq]
    -- non-top: the images differ.
    have himgS : (S : Finset (Fin n)) = Finset.univ.image (fun j : Fin k => e j) := by
      have himg : (S : Finset (Fin n)) = Finset.univ.image (Set.powersetCard.ofFinEmbEquiv.symm S) := by
        rw [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.image_orderEmbOfFin_univ]
      rw [himg, he]
    have htopImg : topSet.val = Finset.univ.image topEmb := by
      have hval : topSet.val = Finset.univ.image (topEmb) := by
        ext x
        rw [Finset.mem_image,
          show x ∈ topSet.val ↔ x ∈ topSet from Iff.rfl, htopSet,
          Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range]
        constructor
        · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
        · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
      exact hval
    have hImgNe : (Finset.univ.image (fun j : Fin k => e j) : Finset (Fin n))
        ≠ Finset.univ.image (fun i : Fin k => (⟨i, lt_of_lt_of_le i.2 hkn⟩ : Fin n)) := by
      intro h
      apply hSne
      apply Subtype.ext
      rw [show (S : Finset (Fin n)) = S.val from rfl, show topSet.val = topSet.val from rfl,
        himgS, htopImg, h]
      rfl
    -- top element of `S` is `≥ k`.
    have htopge : k ≤ (e ⟨k-1, by omega⟩ : ℕ) := top_elem_ge hk1 hkn e hImgNe
    -- specialize the product bound with `m = k-1`, i.e. `k = m+1`.
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
    rw [hμ₁, Nat.add_sub_cancel]
    have hbound := prod_le_second_aux (n := n) m lam hanti hpos e (by simpa using htopge)
    exact hbound
  -- assemble.
  refine ⟨i₀, diag_isSymmetric C c hCdiag, ?_, ?_, ?_⟩
  · rw [hCdiag i₀, hci₀]
  · have hpre_pos : 0 < ∏ i ∈ Finset.range (k-1), lam i := by
      apply Finset.prod_pos
      intro j hj
      rw [Finset.mem_range] at hj
      -- `lam j ≥ lam (k-1) > lam k ≥ 0`, since `j ≤ k-1` and `lam` antitone.
      have hjle : lam (k-1) ≤ lam j := hanti (by omega)
      exact lt_of_lt_of_le (lt_of_le_of_lt (hpos k) hgap) hjle
    show μ₁ < μ₀
    calc μ₁ = (∏ i ∈ Finset.range (k-1), lam i) * lam k := rfl
      _ < (∏ i ∈ Finset.range (k-1), lam i) * lam (k-1) := mul_lt_mul_of_pos_left hgap hpre_pos
      _ = μ₀ := by
          rw [hμ₀]
          obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk1
          rw [Nat.add_comm 1 p, Nat.add_sub_cancel, Finset.prod_range_succ]
  · intro w hw
    refine diag_rayleigh_ceiling C c hCdiag i₀ hsecond ?_ w hw
    rw [hμ₁]
    have hprefix : 0 ≤ ∏ i ∈ Finset.range (k-1), lam i := Finset.prod_nonneg (fun _ _ => hpos _)
    exact mul_nonneg hprefix (hpos k)

/-! ### The reconciliation bridge: transporting the Plücker eigenpair into standard coordinates

`plucker_eigenpair_ceiling` produces the top eigenpair and second-eigenvalue ceiling of the
conjugated compound `conjExteriorMap k (onbTriv u) (onbTriv u) f` in the **eigenbasis** wedge
trivialization (`u` = an orthonormal eigenbasis of the symmetric `f`). The Rayleigh-deficit input
`rayleigh_deficit_le` lives in the **standard** trivialization, where the conjugated compound is
`toEuclideanLin (compoundMatrix k ·)` (the compound matrix). These are the *same* abstract operator
`⋀^k f` viewed through two isometric o.n.-basis wedge trivializations, hence unitarily equivalent by
the orthogonal change-of-coordinates `onbChange`. Since an isometry preserves the inner product, the
Rayleigh quotient is trivialization-independent; this lets `sin_sq_le_rayleigh_deficit_div_gap` be
applied in eigenbasis coordinates with the deficit supplied from standard coordinates. -/

section Reconciliation

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Classical in
/-- **Conjugation of `conjExteriorMap` under change of o.n.-wedge trivialization.** For the *same*
endomorphism `f`, the conjugated compounds in two o.n.-basis wedge trivializations `onbTriv b`,
`onbTriv b'` are related by the L2 isometry `W = onbChange b b' k`:
`conjExteriorMap (onbTriv b') f = W ∘ conjExteriorMap (onbTriv b) f ∘ W⁻¹`. -/
private lemma conjExteriorMap_onbChange_conj {ιE ιE' : Type*}
    [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
    (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ) (f : E →ₗ[ℝ] E)
    (p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E)))) :
    conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f p
      = onbChange b b' k (conjExteriorMap k (onbTriv b k) (onbTriv b k) f
          ((onbChange b b' k).symm p)) := by
  show conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f p
      = onbTriv b' k ((onbTriv b k).symm (conjExteriorMap k (onbTriv b k) (onbTriv b k) f
          (onbTriv b k ((onbTriv b' k).symm p))))
  simp only [conjExteriorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

open scoped Classical in
/-- **Rayleigh-quotient transport.** Because `W = onbChange b b' k` is an L2 isometry and
`conjExteriorMap (onbTriv b') f = W ∘ conjExteriorMap (onbTriv b) f ∘ W⁻¹`, the Rayleigh quotient
of the standard-trivialization compound at `y` equals that of the eigenbasis-trivialization compound
at `W y`. (Here `b` is the standard, `b'` the eigenbasis.) -/
private lemma rayleigh_onbChange_eq {ιE ιE' : Type*}
    [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
    (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ) (f : E →ₗ[ℝ] E)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E)))) :
    (inner ℝ (conjExteriorMap k (onbTriv b k) (onbTriv b k) f y) y : ℝ)
      = (inner ℝ (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (onbChange b b' k y))
          (onbChange b b' k y) : ℝ) := by
  rw [conjExteriorMap_onbChange_conj b b' k f (onbChange b b' k y),
    LinearIsometryEquiv.symm_apply_apply,
    (onbChange b b' k).inner_map_map]

open scoped Classical in
/-- **Transport of a top-eigenpair + second-eigenvalue ceiling across the change of o.n.-wedge
trivialization.** Given the top eigenpair (`hev`) and the `μ₁`-ceiling on the orthogonal complement
(`hceil`) of the conjugated compound in the `b'`-trivialization (`b'` = the eigenbasis), the same
data transports — via the orthogonal `W = onbChange b b' k` — to the `b`-trivialization (`b` = the
standard basis): the eigenvector is `v₀ = W⁻¹ (basisFun i₀)`, the eigenvalue/gap are unchanged, and
the Rayleigh ceiling holds verbatim on `v₀ᗮ`. This is the abstract (matrix-free) reconciliation core
that feeds `sin_sq_le_rayleigh_deficit_div_gap` once `conjExteriorMap (onbTriv b) f` is identified
with the standard compound. -/
lemma eigenpair_ceiling_transport {ιE ιE' : Type*}
    [Fintype ιE] [LinearOrder ιE] [Fintype ιE'] [LinearOrder ιE']
    (b : OrthonormalBasis ιE ℝ E) (b' : OrthonormalBasis ιE' ℝ E) (k : ℕ) (f : E →ₗ[ℝ] E)
    (i₀ : Fin (Module.finrank ℝ (⋀[ℝ]^k E))) (μ₀ μ₁ : ℝ)
    (hev : conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f
        (EuclideanSpace.basisFun _ ℝ i₀) = μ₀ • EuclideanSpace.basisFun _ ℝ i₀)
    (hceil : ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))),
        (inner ℝ w (EuclideanSpace.basisFun _ ℝ i₀) : ℝ) = 0 →
        (inner ℝ (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f w) w : ℝ) ≤ μ₁ * ‖w‖ ^ 2) :
    ‖(onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀)‖ = 1
    ∧ conjExteriorMap k (onbTriv b k) (onbTriv b k) f
        ((onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀))
        = μ₀ • (onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀)
    ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k E))),
        (inner ℝ w ((onbChange b b' k).symm (EuclideanSpace.basisFun _ ℝ i₀)) : ℝ) = 0 →
        (inner ℝ (conjExteriorMap k (onbTriv b k) (onbTriv b k) f w) w : ℝ) ≤ μ₁ * ‖w‖ ^ 2 := by
  set W := onbChange b b' k with hW
  set e₀ := EuclideanSpace.basisFun (Fin (Module.finrank ℝ (⋀[ℝ]^k E))) ℝ i₀ with he₀
  -- conjugation `C_b p = W⁻¹ (C_{b'} (W p))`.
  have hconj : ∀ p, conjExteriorMap k (onbTriv b k) (onbTriv b k) f p
      = W.symm (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (W p)) := by
    intro p
    rw [hW]
    have hb := conjExteriorMap_onbChange_conj b b' k f (onbChange b b' k p)
    rw [LinearIsometryEquiv.symm_apply_apply] at hb
    rw [hb, LinearIsometryEquiv.symm_apply_apply]
  have hWv₀ : W (W.symm e₀) = e₀ := LinearIsometryEquiv.apply_symm_apply W e₀
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map, he₀, EuclideanSpace.basisFun_apply,
      EuclideanSpace.norm_single, norm_one]
  · rw [hconj (W.symm e₀), hWv₀, hev, map_smul]
  · intro w hw
    rw [hconj w]
    have hWperp : (inner ℝ (W w) e₀ : ℝ) = 0 := by
      rw [← hWv₀, W.inner_map_map]; exact hw
    have hR : (inner ℝ (W.symm (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (W w))) w : ℝ)
        = (inner ℝ (conjExteriorMap k (onbTriv b' k) (onbTriv b' k) f (W w)) (W w) : ℝ) := by
      rw [← W.inner_map_map (W.symm _) w, LinearIsometryEquiv.apply_symm_apply]
    rw [hR]
    have hc := hceil (W w) hWperp
    rwa [W.norm_map] at hc

end Reconciliation

/-! ### The Plücker eigenpair in standard (compound-matrix) coordinates

The matrix-level packaging `plucker_eigenpair_ceiling_standard` transports
`plucker_eigenpair_ceiling` through the orthogonal change-of-trivialization `onbChange`
(via `eigenpair_ceiling_transport`) into the **standard** wedge trivialization
`onbTriv (EuclideanSpace.basisFun (Fin d) ℝ)`, where the compound bridge
`conjExteriorMap_eq_toEuclideanLin_compound` identifies the conjugated compound of
`toEuclideanLin Q` with `toEuclideanLin (compoundMatrix k Q)` — exactly the operator consumed by the
NODE 1 lemmas `norm_offdiag_residual_compound_le` / `perturbed_compound_gram_ceiling`.

The single declaration combining plucker ∘ transport ∘ matrix-identification timed out even at
`maxHeartbeats 1600000`. The fix is to *split* the heavy matrix-identification step into an isolated
scoped lemma (`conjExteriorMap_basisFun_toEuclideanLin_eq_compound` below — a thin alias of the
committed compound bridge, kept separate so its `⋀^k` finrank elaboration cost is contained) and to
keep the transport/assembly in its own scoped declaration. -/

section StandardCoords

variable {d : ℕ}

set_option maxHeartbeats 800000 in
/-- **(A) — the isolated matrix-identification step.** Through the standard orthonormal-wedge
trivialization (`onbTriv (EuclideanSpace.basisFun (Fin d) ℝ)`), the conjugated compound of
`toEuclideanLin M` is `toEuclideanLin (compoundMatrix k M)`. This is a thin re-export of the
committed `conjExteriorMap_eq_toEuclideanLin_compound`, isolated in its own scoped declaration so
that the (heavy) `⋀^k` finrank-indexed elaboration is paid here exactly once, keeping the
assembled `plucker_eigenpair_ceiling_standard` under budget. -/
theorem conjExteriorMap_basisFun_toEuclideanLin_eq_compound
    (k : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    conjExteriorMap k (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k)
        (onbTriv (EuclideanSpace.basisFun (Fin d) ℝ) k) (Matrix.toEuclideanLin M)
      = Matrix.toEuclideanLin (compoundMatrix k M) :=
  conjExteriorMap_eq_toEuclideanLin_compound k M

set_option maxHeartbeats 1200000 in
/-- **(B) — `plucker_eigenpair_ceiling_standard`.** The Plücker eigenpair + second-eigenvalue
ceiling in *standard* compound-matrix coordinates. For a symmetric PSD `f = toEuclideanLin Q` with
orthonormal eigenbasis `u` and antitone nonnegative eigenvalues `lam`, at a genuine gap
`lam k < lam (k-1)`, the operator `toEuclideanLin (compoundMatrix k Q)` (`= ⋀^k Q` in the standard
trivialization) has:

* **top eigenpair:** a unit vector `v₀` with `toEuclideanLin (compoundMatrix k Q) v₀ = μ₀ • v₀`,
  `μ₀ = ∏_{i<k} lam i`;
* **the gap:** `μ₁ < μ₀` with `μ₁ = (∏_{i<k-1} lam i)·lam k`;
* **second-eigenvalue ceiling:** `∀ w ⊥ v₀, ⟪(toEuclideanLin (compoundMatrix k Q)) w, w⟫ ≤ μ₁‖w‖²`.

Assembled from `plucker_eigenpair_ceiling` (eigenbasis-wedge coords) → `eigenpair_ceiling_transport`
(`onbChange` to standard `basisFun` coords) → `conjExteriorMap_basisFun_toEuclideanLin_eq_compound`
(matrix identification, isolated in (A)). This is the top spectral data of `Cₙ = ⋀^k Qₙ` that the
NODE 1 lemmas `norm_offdiag_residual_compound_le` / `perturbed_compound_gram_ceiling` consume. -/
theorem plucker_eigenpair_ceiling_standard {n : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (u : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin d)))
    (lam : ℕ → ℝ) (hanti : Antitone lam) (hpos : ∀ i, 0 ≤ lam i)
    (hf : ∀ i, Matrix.toEuclideanLin Q (u i) = lam (i : ℕ) • u i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hgap : lam k < lam (k - 1)) :
    ∃ v₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))),
      ‖v₀‖ = 1
      ∧ Matrix.toEuclideanLin (compoundMatrix k Q) v₀
          = (∏ i ∈ Finset.range k, lam i) • v₀
      ∧ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) < (∏ i ∈ Finset.range k, lam i)
      ∧ ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))),
          (inner ℝ w v₀ : ℝ) = 0 →
          (inner ℝ (Matrix.toEuclideanLin (compoundMatrix k Q) w) w : ℝ)
            ≤ ((∏ i ∈ Finset.range (k-1), lam i) * lam k) * ‖w‖ ^ 2 := by
  classical
  -- eigenbasis-coords Plücker data (PB1 + PB2).
  obtain ⟨i₀, _hsym, hev, hgapμ, hceil⟩ :=
    plucker_eigenpair_ceiling (Matrix.toEuclideanLin Q) u lam hanti hpos hf hk1 hkn hgap
  -- transport to standard (`basisFun`) wedge coordinates via the orthogonal `onbChange`.
  obtain ⟨hv₀norm, hv₀ev, hv₀ceil⟩ :=
    eigenpair_ceiling_transport (EuclideanSpace.basisFun (Fin d) ℝ) u k
      (Matrix.toEuclideanLin Q) i₀ _ _ hev hceil
  -- the transported eigenvector, named once.
  refine ⟨(onbChange (EuclideanSpace.basisFun (Fin d) ℝ) u k).symm
      (EuclideanSpace.basisFun _ ℝ i₀), hv₀norm, ?_, hgapμ, ?_⟩
  · -- identify the standard-coords conjugated compound with the compound matrix (step (A)).
    rw [← conjExteriorMap_basisFun_toEuclideanLin_eq_compound k Q]
    exact hv₀ev
  · intro w hw
    rw [← conjExteriorMap_basisFun_toEuclideanLin_eq_compound k Q]
    exact hv₀ceil w hw

end StandardCoords

end Plucker

end ExteriorNorm

end
