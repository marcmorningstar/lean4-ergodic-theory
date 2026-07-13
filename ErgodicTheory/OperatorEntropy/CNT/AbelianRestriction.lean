import ErgodicTheory.OperatorEntropy.CNT.SubadditivityCounterexample
import ErgodicTheory.OperatorEntropy.EntropyPure
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# The per-resolution non-commutativity certificate for CNT/ALF entropy

This module records, in per-resolution form, the sense in which the correlation entropy of the
Connes–Narnhofer–Thirring / Alicki–Fannes construction "sees" non-commutativity of the operational
partition.  We work with the same finite-dimensional witness as `SubadditivityCounterexample`: the
identity dynamics `cexEndo` on `Matrix (Fin 2) (Fin 2) ℂ` and the invariant pure state
`cexState = |0⟩⟨0|`.

The certificate is a dichotomy between **abelian** (diagonal) operational partitions and the
non-commuting partition `cexPartition`:

* **Every abelian resolution is flat.**  For any operational partition `X` whose operators are all
  diagonal, the correlation density matrix `corrMatrix cexEndo cexState X n` is a rank-one
  idempotent at every resolution `n` (`corrMatrix_cex_idempotent`), so its von Neumann entropy is
  `0` (`cex_abelian_restriction_entropy_zero`).  Diagonality is preserved by the identity dynamics,
  the pure state reads off column `0`, and the resulting correlation matrix is the outer product
  `v vᴴ` with `⟨v, v⟩ = Tr = 1`, hence a projection.
* **The non-commuting resolution is not flat.**  For `cexPartition` (whose second operator is
  strictly off-diagonal) the length-`2` correlation matrix is *not* idempotent, so its entropy is
  strictly positive (`entropy_corrMatrix_two_pos`, from `SubadditivityCounterexample`).

`cex_strictly_above_abelian` packages the two facts: correlation entropy is strictly positive at
resolution `2` on the non-commuting partition, while it vanishes at every resolution on every
abelian partition.  This is issue #59's "entropy strictly above every abelian restriction", stated
honestly at the per-resolution level: the *system-level* CNT/ALF rate vanishes identically in
finite dimension (`cntDynamicalEntropy_eq_zero`, `FiniteDimZero`), a `0 = 0` degeneracy, so the
per-resolution correlation matrices are where the non-commutativity actually lives.

References: Connes–Narnhofer–Thirring, *Dynamical entropy of C\*-algebras and von Neumann algebras*,
Comm. Math. Phys. **112** (1987); Alicki–Fannes, *Quantum Dynamical Systems*, OUP (2001).
-/

open Matrix Real
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

/-- The product of two diagonal matrices is diagonal. -/
private theorem isDiag_mul {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsDiag) (hB : B.IsDiag) : (A * B).IsDiag := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : i = l
  · rw [← hl, hB hij, mul_zero]
  · rw [hA hl, zero_mul]

/-- **Diagonality is preserved by the refinement of a diagonal partition.**  Under the identity
dynamics `cexEndo`, the time-ordered refinement of an operational partition whose operators are all
diagonal is a product of diagonal matrices, hence diagonal, at every length. -/
theorem refine_cex_isDiag {k : ℕ} (X : OperationalPartition 2 k)
    (hX : ∀ i, (X.op i).IsDiag) : ∀ (n : ℕ) (f : Fin n → Fin k),
    (refine cexEndo X n f).IsDiag
  | 0, _ => by rw [refine_zero]; exact isDiag_one
  | n + 1, f => by
      rw [refine_succ, cexEndo_toFun]
      exact isDiag_mul (hX (f 0)) (refine_cex_isDiag X hX n (Fin.tail f))

/-- The rank-one vector of the diagonal counterexample: the column-`0` diagonal entry of the
refinement word.  For a diagonal refinement the pure-state pairing collapses onto this scalar. -/
private def cexVec {k : ℕ} (X : OperationalPartition 2 k) (n : ℕ) (f : Fin n → Fin k) : ℂ :=
  (refine cexEndo X n f) 0 0

/-- **Rank-one Gram collapse.**  For a diagonal operational partition, the pure state `cexState`
pairs the two refinement words into the outer product `⟨g, f⟩ ↦ conj(v g) · v f`, where `v` is the
column-`0` diagonal entry: the off-diagonal `(1, 0)` contribution of `cex_trace` vanishes by
diagonality. -/
theorem corrVal_cex_apply {k : ℕ} (X : OperationalPartition 2 k)
    (hX : ∀ i, (X.op i).IsDiag) (n : ℕ) (g f : Fin n → Fin k) :
    corrVal cexEndo cexState X n g f = star (cexVec X n g) * cexVec X n f := by
  rw [corrVal_apply, cex_trace, refine_cex_isDiag X hX n g (show (1 : Fin 2) ≠ 0 by decide)]
  simp only [cexVec, star_zero, zero_mul, add_zero]

/-- **The abelian correlation matrix is a projection.**  For a diagonal operational partition the
correlation density matrix is the outer product `v vᴴ` with `⟨v, v⟩ = Tr = 1`, hence idempotent:
`M² = M` at every resolution `n`. -/
theorem corrMatrix_cex_idempotent {k : ℕ} (X : OperationalPartition 2 k)
    (hX : ∀ i, (X.op i).IsDiag) (n : ℕ) :
    (corrMatrix cexEndo cexState X n).val * (corrMatrix cexEndo cexState X n).val
      = (corrMatrix cexEndo cexState X n).val := by
  rw [corrMatrix_val]
  have hdiag : ∑ h : Fin n → Fin k, corrVal cexEndo cexState X n h h = 1 := by
    have h1 : (corrVal cexEndo cexState X n).trace
        = ∑ h, corrVal cexEndo cexState X n h h := by
      simp only [Matrix.trace, Matrix.diag_apply]
    rw [← h1]; exact corrVal_trace_one cexEndo cexState X n
  have hsum : ∑ h : Fin n → Fin k, cexVec X n h * star (cexVec X n h) = 1 := by
    rw [← hdiag]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [corrVal_cex_apply X hX n h h]; ring
  ext g f
  rw [Matrix.mul_apply]
  have hL : ∀ h : Fin n → Fin k,
      corrVal cexEndo cexState X n g h * corrVal cexEndo cexState X n h f
        = star (cexVec X n g) * cexVec X n f * (cexVec X n h * star (cexVec X n h)) := by
    intro h
    rw [corrVal_cex_apply X hX n g h, corrVal_cex_apply X hX n h f]; ring
  rw [Finset.sum_congr rfl fun h _ => hL h, ← Finset.mul_sum, hsum, mul_one,
    corrVal_cex_apply X hX n g f]

/-- **Headline A — every abelian resolution is flat.**  Under the identity dynamics and the
invariant pure state, every operational partition with diagonal operators has *zero* correlation
entropy at every resolution `n`: the correlation matrix is a rank-one projection. -/
theorem cex_abelian_restriction_entropy_zero {k : ℕ} (X : OperationalPartition 2 k)
    (hX : ∀ i, (X.op i).IsDiag) (n : ℕ) :
    vonNeumannEntropy (corrMatrix cexEndo cexState X n) = 0 :=
  vonNeumannEntropy_eq_zero_of_sq_eq _ (corrMatrix_cex_idempotent X hX n)

/-- **Headline B — the per-resolution non-commutativity certificate.**  Correlation entropy is
strictly positive at resolution `2` on the non-commuting partition `cexPartition`, while it vanishes
at *every* resolution on *every* abelian (diagonal) operational partition.  This is issue #59's
"entropy strictly above every abelian restriction" in its honest, per-resolution form: the
system-level CNT/ALF rate collapses to `0` in finite dimension (`cntDynamicalEntropy_eq_zero`), so
the non-commutativity is visible only at the level of the correlation matrices themselves. -/
theorem cex_strictly_above_abelian :
    (∀ {k : ℕ} (X : OperationalPartition 2 k), (∀ i, (X.op i).IsDiag) →
        ∀ n, vonNeumannEntropy (corrMatrix cexEndo cexState X n) = 0)
      ∧ 0 < vonNeumannEntropy (corrMatrix cexEndo cexState cexPartition 2) :=
  ⟨fun {_} X hX n => cex_abelian_restriction_entropy_zero X hX n, entropy_corrMatrix_two_pos⟩

end ErgodicTheory.OperatorEntropy.CNT
