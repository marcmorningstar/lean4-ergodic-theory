import ErgodicTheory.OperatorEntropy.Basic

/-!
# Spectrum and von Neumann entropy of a diagonal density matrix

For a real family `p : ι → ℝ`, the eigenvalues of the diagonal matrix
`diagonal (fun i => (p i : ℂ))` are exactly the values `p i` — but stored as a
*sorted* tuple, so the pointwise statement `eigenvalues i = p i` is false.  The
correct invariant is the equality of the *multisets* of eigenvalues, recorded by
`eigenvalues_diagonal_multiset`.

This is the abelian/classical corner of the operator-entropy bridge: the
headline `vonNeumannEntropy_diagonal` shows that the von Neumann entropy of a
diagonal density matrix is the classical (Shannon) entropy `∑ i, negMulLog (p i)`
of its diagonal.  The proof clones `eigenvalues_kronecker_multiset`: the
characteristic polynomial of a diagonal matrix is a product of linear factors,
whose root multiset is read off through
`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`.
-/

open Matrix Real Polynomial
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multiset of roots of `∏ i, (X - C (d i))` over a finite index type is the
image multiset of `d`.  (A local re-derivation of the `KroneckerSpectrum` helper,
kept `private` so the two modules can coexist in an aggregator.) -/
private theorem roots_prod_X_sub_C_comp {ι : Type*} [Fintype ι] (d : ι → ℂ) :
    (∏ i, (X - C (d i))).roots = Finset.univ.val.map d := by
  have h : (∏ i, (X - C (d i)))
      = ((Finset.univ.val.map d).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [h, roots_multiset_prod_X_sub_C]

/-- **Eigenvalues of a real diagonal matrix.**  For `p : ι → ℝ`, the multiset of
eigenvalues of the Hermitian matrix `diagonal (fun i => (p i : ℂ))` equals the
image multiset of `p`.  (Eigenvalues are stored sorted, so this is necessarily a
multiset — never a pointwise — equality.) -/
theorem eigenvalues_diagonal_multiset (p : ι → ℝ)
    (hd : (Matrix.diagonal (fun i => (p i : ℂ))).IsHermitian) :
    (Finset.univ.val.map hd.eigenvalues) = (Finset.univ.val.map p) := by
  apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
  rw [Multiset.map_map, Multiset.map_map,
    ← hd.roots_charpoly_eq_eigenvalues, charpoly_diagonal, roots_prod_X_sub_C_comp]
  refine Multiset.map_congr rfl fun i _ => ?_
  rfl

/-- **Von Neumann entropy of a diagonal density matrix.**  When the density matrix
is `diagonal (fun i => (p i : ℂ))`, its von Neumann entropy is the classical
(Shannon) entropy `∑ i, negMulLog (p i)` of the diagonal. -/
theorem vonNeumannEntropy_diagonal (p : ι → ℝ)
    (hpsd : (Matrix.diagonal (fun i => (p i : ℂ))).PosSemidef)
    (htr : (Matrix.diagonal (fun i => (p i : ℂ))).trace = 1) :
    vonNeumannEntropy ⟨Matrix.diagonal (fun i => (p i : ℂ)), hpsd, htr⟩
      = ∑ i, Real.negMulLog (p i) := by
  unfold vonNeumannEntropy
  have e1 : Finset.univ.val.map hpsd.1.eigenvalues = Finset.univ.val.map p :=
    eigenvalues_diagonal_multiset p hpsd.1
  have h := congrArg (fun m : Multiset ℝ => (m.map negMulLog).sum) e1
  simpa only [Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def] using h

end ErgodicTheory.OperatorEntropy
