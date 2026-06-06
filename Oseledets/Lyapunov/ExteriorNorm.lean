/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Analysis.Normed.Module.FiniteDimension

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

/-- **The bridge.** Through the Hodge trivializations of source and target, the exterior operator
norm equals the product of the top-`k` singular values:
`exteriorOpNorm k (hodgeTrivialization k) (hodgeTrivialization k) f = ∏_{i<k} σᵢ(f)`. -/
theorem exteriorOpNorm_hodge_eq_prod_singularValues (k : ℕ) (f : E →ₗ[ℝ] F) :
    exteriorOpNorm k (hodgeTrivialization k) (hodgeTrivialization k) f
      = ∏ i ∈ Finset.range k, f.singularValues i := by
  sorry -- TODO(ExteriorNorm §3, SVD diagonalization):
        -- exteriorOpNorm k (hodgeTrivialization k) (hodgeTrivialization k) f = ∏_{i<k} σᵢ(f).
        -- Proof outline: take orthonormal SVD bases u of E, w of F with `f uⱼ = σⱼ • wⱼ` (built
        -- from `eigenvectorBasis` of `adjoint f ∘ₗ f`); then `⋀^k f` sends the wedge basis vector
        -- `u_S ↦ (∏_{j∈S} σⱼ) • w_S`, i.e. it is DIAGONAL on the orthonormal wedge bases. Since the
        -- Hodge trivializations carry these wedge bases isometrically to the Euclidean standard
        -- basis, `conjExteriorMap` becomes a diagonal Euclidean map whose operator norm is the max
        -- diagonal entry `max_{|S|=k} ∏_{j∈S} σⱼ = ∏_{j<k} σⱼ` (σ antitone).

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
