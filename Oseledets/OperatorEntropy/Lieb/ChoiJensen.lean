/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.OperatorConvex
import Oseledets.OperatorEntropy.Lieb.Dilation

/-!
# Multi-Kraus operator-Jensen inequality (Choi's inequality) for `-log`

This is the finite-family (multi-Kraus) generalization of the Hansen–Pedersen–Jensen /
Effros dilation inequality `Oseledets.OperatorEntropy.Lieb.hpj_affine`.  Given Kraus operators
`K : ι → Matrix q q ℂ` with `∑ᵢ Kᵢᴴ Kᵢ = 1` — i.e. the unital completely positive map
`Λ†(Y) = ∑ᵢ Kᵢᴴ Y Kᵢ` — and a positive-definite self-adjoint `X`, operator convexity of `-log`
gives the data-processing / operator-Jensen inequality

`(-log)(Λ†(X)) ≤ Λ†((-log) X)`,  i.e.  `cfc(-log)(∑ᵢ Kᵢᴴ X Kᵢ) ≤ ∑ᵢ Kᵢᴴ (cfc(-log) X) Kᵢ`.

This is the Loewner form of the DPI that unblocks the sufficiency direction of the Petz recovery
equality (issue #28), because the channel `Λ` is a Kraus channel.

## Route

We form the column isometry `V = krausCol K : Matrix (q × ι) q ℂ` (blocks `Kᵢ`), so that
`Vᴴ V = ∑ᵢ Kᵢᴴ Kᵢ = 1` and, for any block-diagonal `blockDiagonal Y`,
`Vᴴ (blockDiagonal Y) V = ∑ᵢ Kᵢᴴ Yᵢ Kᵢ` (`krausCol_conj_blockDiagonal`).  The continuous functional
calculus distributes over a block diagonal (`cfc_blockDiagonal`), reducing the claim to the
rectangular-isometry operator-Jensen inequality, which is proved by the reflection (`Fin 2`) pinch
against the unitary dilation of `V`.

## Main results

* `Oseledets.OperatorEntropy.Lieb.cfc_blockDiagonal`: `cfc f` distributes over a block diagonal.
* `Oseledets.OperatorEntropy.Lieb.krausCol_conj_blockDiagonal`: the Kraus-column Gram identity.
* `Oseledets.OperatorEntropy.Lieb.choi_neg_log_loewner`: Choi's inequality for `-log`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

/-! ## Functional calculus distributes over a block diagonal -/

set_option maxHeartbeats 800000 in -- large block-matrix / cfc spectral elaboration
/-- **`cfc f` distributes over `Matrix.blockDiagonal`.** For a family of self-adjoint blocks,
`cfc f (blockDiagonal Y) = blockDiagonal (fun i => cfc f (Y i))`.  This generalizes `cfc_blockDiag2`
from the two-block (`Fin 2`) case to an arbitrary finite family. -/
lemma cfc_blockDiagonal {ι q : Type*} [Fintype ι] [DecidableEq ι] [Fintype q] [DecidableEq q]
    (f : ℝ → ℝ) (Y : ι → Matrix q q ℂ) (hY : ∀ i, IsSelfAdjoint (Y i)) :
    cfc f (blockDiagonal Y) = blockDiagonal (fun i => cfc f (Y i)) := by
  have hYh : ∀ i, (Y i).IsHermitian := fun i => hY i
  -- spectral data
  set U : ι → Matrix q q ℂ := fun i => ((hYh i).eigenvectorUnitary : Matrix q q ℂ) with hUdef
  set E : ι → q → ℝ := fun i => (hYh i).eigenvalues with hEdef
  have hUmul : ∀ i, star (U i) * U i = 1 := fun i => Unitary.coe_star_mul_self _
  have hUmul' : ∀ i, U i * star (U i) = 1 := fun i => Unitary.coe_mul_star_self _
  -- `blockDiagonal U` is unitary
  have hBU1 : star (blockDiagonal U) * blockDiagonal U = 1 := by
    rw [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [← Matrix.star_eq_conjTranspose, hUmul]
    rw [show (fun _ : ι => (1 : Matrix q q ℂ)) = (1 : ι → Matrix q q ℂ) from rfl, blockDiagonal_one]
  have hBU2 : blockDiagonal U * star (blockDiagonal U) = 1 := by
    rw [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [← Matrix.star_eq_conjTranspose, hUmul']
    rw [show (fun _ : ι => (1 : Matrix q q ℂ)) = (1 : ι → Matrix q q ℂ) from rfl, blockDiagonal_one]
  -- per-block spectral decomposition:  `Y i = U i * diagonal(E i) * (U i)ᴴ`.
  have hspec : ∀ i, Y i = U i * diagonal (fun a => (E i a : ℂ)) * star (U i) := by
    intro i
    have h := (hYh i).spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ (hYh i).eigenvalues) = fun a => ((hYh i).eigenvalues a : ℂ) := by
      funext a; rfl
    rw [hRC] at h
    exact h
  -- the block diagonal is the unitary conjugation of the (block-)diagonal spectral matrix
  have hYeq : blockDiagonal Y
      = blockDiagonal U * blockDiagonal (fun i => diagonal (fun a => (E i a : ℂ)))
        * star (blockDiagonal U) := by
    rw [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul,
      ← blockDiagonal_mul]
    congr 1; funext i; rw [← Matrix.star_eq_conjTranspose]; exact hspec i
  -- self-adjointness of the spectral (real diagonal) block matrix
  have hΛsa : IsSelfAdjoint (blockDiagonal (fun i => diagonal (fun a => (E i a : ℂ)))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose]
    congr 1; funext i
    rw [Matrix.diagonal_conjTranspose]; congr 1; funext a; exact Complex.conj_ofReal _
  -- `cfc f` of the spectral block matrix, computed by `cfc_diagonal`
  have hcfcΛ : cfc f (blockDiagonal (fun i => diagonal (fun a => (E i a : ℂ))))
      = blockDiagonal (fun i => diagonal (fun a => (f (E i a) : ℂ))) := by
    rw [blockDiagonal_diagonal, cfc_diagonal f (fun p : q × ι => E p.2 p.1), blockDiagonal_diagonal]
  -- assemble the right-hand side back into a block product
  have hRHS : blockDiagonal (fun i => cfc f (Y i))
      = blockDiagonal U * blockDiagonal (fun i => diagonal (fun a => (f (E i a) : ℂ)))
        * star (blockDiagonal U) := by
    rw [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul,
      ← blockDiagonal_mul]
    congr 1; funext i
    rw [← Matrix.star_eq_conjTranspose]
    exact cfc_hermitian_eq (hYh i) f
  rw [hYeq, Oseledets.OperatorEntropy.cfc_conj _ _ hBU1 hBU2 hΛsa f, hcfcΛ, hRHS]

/-! ## The Kraus column isometry -/

variable {ι q : Type*} [Fintype ι] [DecidableEq ι] [Fintype q] [DecidableEq q]

/-- The "Kraus column" `V : Matrix (q × ι) q ℂ` whose `i`-th block-row is `K i`:
`krausCol K (a, i) j = K i a j`.  Its adjoint acts as `Λ†(Y) = ∑ᵢ Kᵢᴴ Yᵢ Kᵢ` on block diagonals. -/
def krausCol (K : ι → Matrix q q ℂ) : Matrix (q × ι) q ℂ :=
  Matrix.of fun p j => K p.2 p.1 j

omit [Fintype ι] [DecidableEq ι] [Fintype q] [DecidableEq q] in
@[simp] lemma krausCol_apply (K : ι → Matrix q q ℂ) (p : q × ι) (j : q) :
    krausCol K p j = K p.2 p.1 j := rfl

omit [DecidableEq q] in
/-- Multiplying a block diagonal onto a Kraus column acts block-wise:
`blockDiagonal Y * krausCol K = krausCol (fun i => Y i * K i)`. -/
lemma blockDiagonal_mul_krausCol (Y K : ι → Matrix q q ℂ) :
    blockDiagonal Y * krausCol K = krausCol (fun i => Y i * K i) := by
  ext p l
  simp only [Matrix.mul_apply, blockDiagonal_apply, krausCol_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single p.2]
  · simp only [if_true]
  · intro i _ hi
    simp only [if_neg (Ne.symm hi), zero_mul, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ p.2) h

omit [DecidableEq ι] [DecidableEq q] in
/-- The Gram product of two Kraus columns: `(krausCol K)ᴴ * krausCol G = ∑ᵢ Kᵢᴴ Gᵢ`. -/
lemma krausCol_adj_mul (K G : ι → Matrix q q ℂ) :
    (krausCol K)ᴴ * krausCol G = ∑ i, (K i)ᴴ * G i := by
  ext j l
  rw [Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.conjTranspose_apply, krausCol_apply]

omit [DecidableEq q] in
/-- **Kraus-column Gram identity.** `Vᴴ (blockDiagonal Y) V = ∑ᵢ Kᵢᴴ Yᵢ Kᵢ`. -/
lemma krausCol_conj_blockDiagonal (K : ι → Matrix q q ℂ) (Y : ι → Matrix q q ℂ) :
    (krausCol K)ᴴ * blockDiagonal Y * krausCol K = ∑ i, (K i)ᴴ * Y i * (K i) := by
  rw [Matrix.mul_assoc, blockDiagonal_mul_krausCol, krausCol_adj_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc]

omit [DecidableEq ι] [DecidableEq q] in
/-- The Kraus column is an isometry:  `Vᴴ V = ∑ᵢ Kᵢᴴ Kᵢ`. -/
lemma krausCol_isometry (K : ι → Matrix q q ℂ) :
    (krausCol K)ᴴ * krausCol K = ∑ i, (K i)ᴴ * (K i) := by
  rw [krausCol_adj_mul]

end Oseledets.OperatorEntropy.Lieb

end
