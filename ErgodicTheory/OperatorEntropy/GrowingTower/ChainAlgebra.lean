/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.GrowingTower.Tower

/-!
# The inclusion half of the directed local system of the one-sided qubit chain

This module supplies the **inclusion** side of the one-sided qubit chain of `Tower.lean` (issue
#71, tier 1, the *directed union of finite levels* reading).  The tower's carriers
`Qbits n` (of cardinality `2 ^ n`) already carry the capacity-enlargement embedding
`shiftAdjoinQubit : A_n ↪ A_{n+1}` that adjoins a fresh qubit *on the left* (`A ↦ 1 ⊗ A`).  Here
we add the complementary **inclusion** `ι_n : A_n ↪ A_{n+1}` that appends a fresh site *at the far
(deep) end* (`x ↦ x ⊗ 1`), transported along the recursive `snocQbit` equiv that lands the fresh
factor in the *innermost* position of the nested product `Qbits (n+1) = Fin 2 × ⋯ × Fin 1`, rather
than the shallow (leftmost) slot occupied by `shiftAdjoinQubit`.  This distinction is genuine: a
naïve `Equiv.prodComm` reindex would collapse `appendQubit` back onto `shiftAdjoinQubit`, so the
recursive snoc equiv is what makes the two embeddings honestly different maps.

* `snocQbit` — the recursive equiv `Qbits (n+1) ≃ Qbits n × Fin 2` placing the fresh factor at the
  deep end;
* `appendQubit` — the far-end inclusion `x ↦ x ⊗ 1` (reindexed along `snocQbit`);
* it is a unital, multiplicative, `⋆`-preserving injection (`appendQubit_one`,
  `appendQubit_mul`, `appendQubit_star`, `appendQubit_injective`);
* the shift and the inclusion **commute** (`shiftAdjoinQubit_appendQubit`) — the genuine,
  non-trivial commutation of the shallow-end shift with the deep-end append (both realise the
  operator `1 ⊗ M ⊗ 1`), so the family `(A_n, ι_n)` is a genuine directed system carrying the shift
  endomorphism;
* the tracial/maximally mixed state is **compatible with the inclusions**: the far-end site is a
  fresh, maximally mixed degree of freedom, so pairing the `(n+1)`-level maximally mixed state
  against `appendQubit x` reproduces the `n`-level pairing against `x`
  (`appendQubit_maximallyMixed_pairing`).

## Scope

The algebraic C*-inductive-limit **type** (the completed quasi-local algebra `⋃_n A_n`) is
deliberately *not* formed: Mathlib's `Ring.DirectLimit` is `CommRing`-only, and the matrix
algebras here are noncommutative.  What is formed — and is all that the entropy-rate statements of
`Tower.lean` require — is the honest directed *system* of finite levels together with the shift
endomorphism and the compatible tracial marginals.

## Provenance

The one-sided shift and its entropy are the setting of Connes–Narnhofer–Thirring, *Dynamical
entropy of C\* algebras and von Neumann algebras*, Comm. Math. Phys. **112** (1987) 691–719.  The
quasi-local (inclusion + shift) structure of the qubit chain is standard; see Bratteli–Robinson,
*Operator Algebras and Quantum Statistical Mechanics II*, for the quasi-local algebra framework.
-/

open Matrix
open scoped Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## The far-end inclusion `A_n ↪ A_{n+1}` -/

/-- The recursive reindexing equiv `Qbits (n+1) ≃ Qbits n × Fin 2` that places the fresh qubit at
the **deep (innermost) end** of the nested product `Qbits (n+1) = Fin 2 × ⋯ × Fin 1`.  At level `0`
it is `Equiv.prodComm` (`Fin 2 × Fin 1 ≃ Fin 1 × Fin 2`); the recursive step pushes the fresh factor
one layer deeper via `Equiv.prodAssoc`.  This deep placement is what distinguishes the far-end
inclusion `appendQubit` from the shallow-end shift `shiftAdjoinQubit`. -/
def snocQbit : (n : ℕ) → (Qbits (n + 1) ≃ Qbits n × Fin 2)
  | 0 => Equiv.prodComm (Fin 2) (Qbits 0)
  | (n + 1) =>
      ((Equiv.refl (Fin 2)).prodCongr (snocQbit n)).trans
        (Equiv.prodAssoc (Fin 2) (Qbits n) (Fin 2)).symm

/-- The recursive step of `snocQbit`: on `Qbits (n+2) = Fin 2 × Qbits (n+1)` it sends `(a, w)` to
`((a, (snocQbit n w).1), (snocQbit n w).2)`, i.e. the shallow factor `a` stays outermost and the
fresh factor `(snocQbit n w).2` is pushed to the deep end. -/
theorem snocQbit_succ_apply {n : ℕ} (a : Fin 2) (w : Qbits (n + 1)) :
    snocQbit (n + 1) (a, w) = ((a, (snocQbit n w).1), (snocQbit n w).2) := rfl

/-- The inclusion `A_n ↪ A_{n+1}`: append a fresh qubit at the far (deep) end (`x ↦ x ⊗ 1`),
reindexed along the recursive `snocQbit` equiv so the fresh factor lands innermost — genuinely
distinct from the shallow-end shift `shiftAdjoinQubit`. -/
def appendQubit {n : ℕ} (M : Matrix (Qbits n) (Qbits n) ℂ) :
    Matrix (Qbits (n + 1)) (Qbits (n + 1)) ℂ :=
  (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix (snocQbit n) (snocQbit n)

/-- The inclusion maps the identity to the identity. -/
theorem appendQubit_one (n : ℕ) : appendQubit (1 : Matrix (Qbits n) (Qbits n) ℂ) = 1 := by
  unfold appendQubit
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv (snocQbit n)

/-- The inclusion is multiplicative. -/
theorem appendQubit_mul {n : ℕ} (M N : Matrix (Qbits n) (Qbits n) ℂ) :
    appendQubit (M * N) = appendQubit M * appendQubit N := by
  have hk : (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (N ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (M * N) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hsm := Matrix.submatrix_mul (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (N ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) (snocQbit n) (snocQbit n) (snocQbit n)
      (snocQbit n).bijective
  rw [hk] at hsm
  exact hsm

/-- The inclusion commutes with the conjugate transpose. -/
theorem appendQubit_star {n : ℕ} (M : Matrix (Qbits n) (Qbits n) ℂ) :
    (appendQubit M)ᴴ = appendQubit Mᴴ := by
  unfold appendQubit
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- The inclusion is injective: `x ⊗ 1` (reindexed) determines `x` through the entry identity
`appendQubit x ((snocQbit n).symm (a, 0)) ((snocQbit n).symm (b, 0)) = x a b`. -/
theorem appendQubit_injective (n : ℕ) :
    Function.Injective (appendQubit (n := n)) := by
  intro M N h
  ext a b
  have hentry := congrFun (congrFun h ((snocQbit n).symm (a, 0))) ((snocQbit n).symm (b, 0))
  simpa only [appendQubit, Matrix.submatrix_apply, Equiv.apply_symm_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one] using hentry

/-- **Shift–inclusion compatibility.** The capacity-enlargement shift `shiftAdjoinQubit`
(`A ↦ 1 ⊗ A`, shallow end) and the far-end inclusion `appendQubit` (`x ↦ x ⊗ 1`, deep end) commute:
both realise the entrywise product `1 ⊗ M ⊗ 1`.  With the deep-end (`snocQbit`) placement this is a
genuine, non-trivial commutation of two distinct embeddings.  Hence the family of finite levels is a
genuine directed system carrying the shift as an endomorphism. -/
theorem shiftAdjoinQubit_appendQubit {n : ℕ} (M : Matrix (Qbits n) (Qbits n) ℂ) :
    shiftAdjoinQubit (appendQubit M) = appendQubit (shiftAdjoinQubit M) := by
  ext ⟨a, w⟩ ⟨a', w'⟩
  simp only [shiftAdjoinQubit, appendQubit, Matrix.submatrix_apply, snocQbit_succ_apply,
    Matrix.kroneckerMap_apply]
  ring

/-! ## Compatibility of the tracial state with the inclusions -/

/-- **The maximally mixed state is compatible with the inclusions.** The far-end site adjoined by
`appendQubit` is a fresh, maximally mixed degree of freedom, so pairing the `(n+1)`-level
maximally mixed state against `appendQubit x` reproduces the `n`-level pairing against `x`.  This
is the compatible-marginals condition for the tracial state along the inclusion tower.  (No partial
trace appears: it is a trace-pairing identity, parallel to `maximallyMixed_shiftAdjoinQubit_pairing`
of `ChainState.lean`.) -/
theorem appendQubit_maximallyMixed_pairing (n : ℕ) :
    ∀ x : Matrix (Qbits n) (Qbits n) ℂ,
      ((DensityMatrix.maximallyMixed : DensityMatrix (Qbits (n + 1))).val
          * appendQubit x).trace
        = ((DensityMatrix.maximallyMixed : DensityMatrix (Qbits n)).val * x).trace := by
  intro x
  have hL : ((DensityMatrix.maximallyMixed : DensityMatrix (Qbits (n + 1))).val
        * appendQubit x).trace
      = (((Fintype.card (Qbits (n + 1)) : ℝ)⁻¹ : ℝ) : ℂ) * (x.trace * 2) := by
    have hmm : (DensityMatrix.maximallyMixed : DensityMatrix (Qbits (n + 1))).val
        = ((Fintype.card (Qbits (n + 1)) : ℝ)⁻¹ : ℝ)
          • (1 : Matrix (Qbits (n + 1)) (Qbits (n + 1)) ℂ) := rfl
    have htr : (appendQubit x).trace = x.trace * 2 := by
      have hsub : ((x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix
          (snocQbit n) (snocQbit n)).trace
          = (x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
        exact Equiv.sum_comp (snocQbit n)
          (fun j => (x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) j j)
      calc (appendQubit x).trace
          = ((x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix
              (snocQbit n) (snocQbit n)).trace := rfl
        _ = (x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace := hsub
        _ = x.trace * 2 := by
            rw [Matrix.trace_kronecker, Matrix.trace_one, Fintype.card_fin]
            push_cast
            ring
    rw [hmm, Matrix.smul_mul, one_mul, Matrix.trace_smul, htr, Complex.real_smul]
  have hR : ((DensityMatrix.maximallyMixed : DensityMatrix (Qbits n)).val * x).trace
      = (((Fintype.card (Qbits n) : ℝ)⁻¹ : ℝ) : ℂ) * x.trace := by
    have hmm : (DensityMatrix.maximallyMixed : DensityMatrix (Qbits n)).val
        = ((Fintype.card (Qbits n) : ℝ)⁻¹ : ℝ) • (1 : Matrix (Qbits n) (Qbits n) ℂ) := rfl
    rw [hmm, Matrix.smul_mul, one_mul, Matrix.trace_smul, Complex.real_smul]
  rw [hL, hR, card_Qbits, card_Qbits]
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  rw [pow_succ]
  field_simp

end ErgodicTheory.OperatorEntropy
