import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Spectrum of a Kronecker product of Hermitian matrices

For Hermitian matrices `A` and `B` over `ℂ`, the eigenvalues of the Kronecker
product `A ⊗ₖ B` are exactly the pairwise products `λᵢ · μⱼ` of the eigenvalues
of `A` and `B`.  Because eigenvalues are stored as *sorted* tuples, the pointwise
statement is false; the correct invariant is the equality of the *multisets* of
eigenvalues, which is what `eigenvalues_kronecker_multiset` records.

The proof is the cleanest available route: the spectral theorem writes
`A = U Dₐ Uᴴ` and `B = V D_b Vᴴ` with `U`, `V` unitary and `Dₐ`, `D_b` real
diagonal, so `A ⊗ₖ B = W (Dₐ ⊗ₖ D_b) Wᴴ` with `W = U ⊗ₖ V` unitary.  Hence
`A ⊗ₖ B` and the *diagonal* matrix `Dₐ ⊗ₖ D_b = diagonal (λ q, λ_{q.1} μ_{q.2})`
have the same characteristic polynomial, and the eigenvalue multiset is read off
from `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues` together with the roots
of a product of linear factors.
-/

open Matrix Polynomial
open scoped ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy

/-- The Kronecker product of two Hermitian matrices is Hermitian. -/
theorem _root_.Matrix.IsHermitian.kronecker {nA nB : Type*}
    {A : Matrix nA nA ℂ} {B : Matrix nB nB ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-- The multiset of roots of `∏ i, (X - C (d i))` over a finite index type is the
image multiset of `d`. -/
theorem roots_prod_X_sub_C_comp {ι : Type*} [Fintype ι] (d : ι → ℂ) :
    (∏ i, (X - C (d i))).roots = Finset.univ.val.map d := by
  have h : (∏ i, (X - C (d i)))
      = ((Finset.univ.val.map d).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [h, roots_multiset_prod_X_sub_C]

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- **Eigenvalues of a Kronecker product.**  For Hermitian `A`, `B` over `ℂ`, the
multiset of eigenvalues of `A ⊗ₖ B` equals the multiset of pairwise products
`λ_{q.1} · μ_{q.2}` of the eigenvalues of `A` and `B`. -/
theorem eigenvalues_kronecker_multiset
    {A : Matrix nA nA ℂ} {B : Matrix nB nB ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Finset.univ.val.map (hA.kronecker hB).eigenvalues)
      = (Finset.univ.val.map (fun q : nA × nB => hA.eigenvalues q.1 * hB.eigenvalues q.2)) := by
  have hAspec : A = (hA.eigenvectorUnitary : Matrix nA nA ℂ)
      * diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      * star (hA.eigenvectorUnitary : Matrix nA nA ℂ) := by
    have h := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hBspec : B = (hB.eigenvectorUnitary : Matrix nB nB ℂ)
      * diagonal (RCLike.ofReal ∘ hB.eigenvalues)
      * star (hB.eigenvectorUnitary : Matrix nB nB ℂ) := by
    have h := hB.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hUs : star (hA.eigenvectorUnitary : Matrix nA nA ℂ)
      * (hA.eigenvectorUnitary : Matrix nA nA ℂ) = 1 := Unitary.coe_star_mul_self _
  have hVs : star (hB.eigenvectorUnitary : Matrix nB nB ℂ)
      * (hB.eigenvectorUnitary : Matrix nB nB ℂ) = 1 := Unitary.coe_star_mul_self _
  set U : Matrix nA nA ℂ := (hA.eigenvectorUnitary : Matrix nA nA ℂ) with hUdef
  set V : Matrix nB nB ℂ := (hB.eigenvectorUnitary : Matrix nB nB ℂ) with hVdef
  have hAB : A ⊗ₖ B = (U ⊗ₖ V)
      * (diagonal (RCLike.ofReal ∘ hA.eigenvalues)
          ⊗ₖ diagonal (RCLike.ofReal ∘ hB.eigenvalues))
      * star (U ⊗ₖ V) := by
    conv_lhs => rw [hAspec, hBspec]
    rw [mul_kronecker_mul, mul_kronecker_mul,
      Matrix.star_eq_conjTranspose (U ⊗ₖ V), conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose U, ← Matrix.star_eq_conjTranspose V]
  have hW : star (U ⊗ₖ V) * (U ⊗ₖ V) = 1 := by
    rw [Matrix.star_eq_conjTranspose (U ⊗ₖ V), conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose U, ← Matrix.star_eq_conjTranspose V,
      ← mul_kronecker_mul, hUs, hVs, one_kronecker_one]
  have key : (A ⊗ₖ B).charpoly
      = (diagonal (RCLike.ofReal ∘ hA.eigenvalues)
          ⊗ₖ diagonal (RCLike.ofReal ∘ hB.eigenvalues)).charpoly := by
    rw [hAB, Matrix.charpoly_mul_comm, ← mul_assoc, hW, one_mul]
  apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
  rw [Multiset.map_map, Multiset.map_map,
    ← (hA.kronecker hB).roots_charpoly_eq_eigenvalues, key,
    diagonal_kronecker_diagonal, charpoly_diagonal, roots_prod_X_sub_C_comp]
  refine Multiset.map_congr rfl fun q _ => ?_
  simp only [Function.comp_apply, RCLike.ofReal_mul]

end Oseledets.OperatorEntropy
