import ErgodicTheory.OperatorEntropy.CNT.Construction
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The CNT correlation matrix as a Gram matrix

The CNT/ALF correlation matrix `corrVal Φ ρ X n` of `Construction`, with entries
`⟨g, f⟩ ↦ Tr(ρ · (refine Φ X n g)ᴴ · refine Φ X n f)`, is the Gram matrix of the
Hilbert–Schmidt vectors `w_f = (refine Φ X n f) · √ρ`, reshaped into columns indexed by
`Fin d × Fin d`.  Concretely, writing `s = √ρ` for the (Hermitian) positive-semidefinite square
root of the density matrix `ρ` (here `CFC.sqrt ρ.val`, the continuous-functional-calculus square
root), the matrix

`gramVec Φ ρ X n p f = (refine Φ X n f · s) p.1 p.2`

with rows indexed by `p : Fin d × Fin d` satisfies

`corrVal Φ ρ X n = (gramVec Φ ρ X n)ᴴ · gramVec Φ ρ X n`.

Since a Gram matrix `Vᴴ V` has the same rank as `V`, and `V = gramVec` has only `d ^ 2` rows, this
gives the rank bound `rank (corrVal Φ ρ X n) ≤ d ^ 2`: the correlation density matrix of an
`n`-fold refinement is supported on a space of dimension at most `d ^ 2`, independently of `n`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

variable {d : ℕ}

/-- Trace identity underlying the Gram factorization: for a Hermitian square root `s` of `ρ`
(`sᴴ = s`, `s · s = ρ`), one has `Tr((A s)ᴴ (B s)) = Tr(ρ Aᴴ B)`. -/
private theorem trace_conj_factor_eq {m : ℕ} (ρ s A B : Matrix (Fin m) (Fin m) ℂ)
    (hsH : sᴴ = s) (hss : s * s = ρ) :
    ((A * s)ᴴ * (B * s)).trace = (ρ * Aᴴ * B).trace := by
  rw [conjTranspose_mul, hsH, Matrix.trace_mul_comm, Matrix.mul_assoc,
    ← Matrix.mul_assoc s s, hss, Matrix.trace_mul_comm]

/-- The Hilbert–Schmidt Gram vectors of the CNT construction: the columns `w_f = (refine f) · √ρ`,
reshaped into a matrix with rows indexed by `Fin d × Fin d` and columns indexed by the classical
index set `Fin n → Fin k`.  Here `√ρ = CFC.sqrt ρ.val` is the positive-semidefinite square root. -/
noncomputable def gramVec (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    Matrix (Fin d × Fin d) (Fin n → Fin k) ℂ :=
  fun p f => (refine Φ X n f * CFC.sqrt ρ.val) p.1 p.2

theorem gramVec_apply (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) (p : Fin d × Fin d) (f : Fin n → Fin k) :
    gramVec Φ ρ X n p f = (refine Φ X n f * CFC.sqrt ρ.val) p.1 p.2 := rfl

/-- **Gram factorization of the CNT correlation matrix.**  The correlation matrix is the Gram
matrix `Vᴴ V` of the Hilbert–Schmidt vectors `V = gramVec`. -/
theorem corrVal_eq_conjTranspose_mul_self (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    corrVal Φ ρ X n = (gramVec Φ ρ X n)ᴴ * gramVec Φ ρ X n := by
  have hsH : (CFC.sqrt ρ.val)ᴴ = CFC.sqrt ρ.val := (CFC.sqrt_nonneg ρ.val).posSemidef.1
  have hss : CFC.sqrt ρ.val * CFC.sqrt ρ.val = ρ.val :=
    (CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt.mp ρ.posSemidef.nonneg).symm
  ext g f
  rw [Matrix.mul_apply, corrVal_apply]
  simp only [Matrix.conjTranspose_apply, gramVec]
  rw [← trace_conjTranspose_mul_eq_sum,
    trace_conj_factor_eq ρ.val (CFC.sqrt ρ.val) (refine Φ X n g) (refine Φ X n f) hsH hss]

/-- **Rank bound for the CNT correlation matrix.**  The correlation density matrix of an `n`-fold
refinement has rank at most `d ^ 2`, uniformly in `n`: it is supported on a space whose dimension
is controlled by the `d × d` matrix algebra alone. -/
theorem rank_corrVal_le (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    (corrVal Φ ρ X n).rank ≤ d ^ 2 := by
  rw [corrVal_eq_conjTranspose_mul_self, Matrix.rank_conjTranspose_mul_self]
  calc (gramVec Φ ρ X n).rank
      ≤ Fintype.card (Fin d × Fin d) := Matrix.rank_le_card_height _
    _ = d ^ 2 := by rw [Fintype.card_prod, Fintype.card_fin]; ring

end ErgodicTheory.OperatorEntropy.CNT
