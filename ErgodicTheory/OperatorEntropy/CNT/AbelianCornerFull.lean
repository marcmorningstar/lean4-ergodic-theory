import ErgodicTheory.OperatorEntropy.CNT.FiniteDimZero
import ErgodicTheory.OperatorEntropy.CNT.AbelianCorner
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# The full abelian corner: finite-dimensional CNT entropy collapses to classical KS entropy

Building on `FiniteDimZero` (the CNT/ALF entropy rate vanishes in finite dimension) and
`AbelianCorner` (the per-resolution diagonal collapse and the abelian-corner identity), this module
records the *full* system-level statements the abelian-corner story asks for, now that both sides
are known to be `0`.

Concretely, for a permutation `σ` of `Fin d` preserving a probability vector `μ`:

* `cntDynamicalEntropyAbelian_eq_zero`: the abelian-corner CNT entropy (supremum over projection
  partitions) is `0`.
* `cntDynamicalEntropyAbelianFull`: the abelian sup taken over **all** operational partitions whose
  operators are diagonal (soft/POVM partitions of the diagonal subalgebra), with
  `cntDynamicalEntropyAbelianFull_eq_zero` and the free monotonicity
  `cntDynamicalEntropyAbelian_le_full` (each projection partition is diagonal).
* `cntDynamicalEntropyAbelianFull_eq_ksEntropy`: the full diagonal sup equals the classical
  Kolmogorov–Sinai entropy `h(⇑σ)`.
* `ksEntropy_eq_cntDynamicalEntropy`: the classical KS entropy equals the **full** CNT dynamical
  entropy (supremum over *all* operational partitions, not just diagonal ones), upgrading the
  one-sided `ksEntropy_le_cntDynamicalEntropy` to an equality.

As with `AbelianCorner` and issue #24, the system-level equalities here are `0 = 0` collapses:
in finite dimension the AF entropy of a system vanishes because `rank(ρ[X⁽ⁿ⁾]) ≤ (dim H)²`
(Alicki–Fannes, *Quantum Dynamical Systems*, OUP 2001) and the CNT entropy of a finite-dimensional
algebra is `0` (Neshveyev–Størmer, *Dynamical Entropy in Operator Algebras*, Springer 2006);
likewise the Kolmogorov–Sinai entropy of a permutation of a finite set is `0`.  The genuinely
non-vacuous content lives one level down, in the per-resolution rank/entropy bound
`vonNeumannEntropy_corrMatrix_le_log` (`FiniteDimZero`) and the classical-corner identity
`vonNeumannEntropy_corrMatrix_eq_ksEntropySeq` (`AbelianCorner`).
-/

open Matrix MeasureTheory Function Real
open scoped ComplexOrder ENNReal

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

variable {d : ℕ}

/-- The abelian-corner CNT dynamical entropy vanishes in finite dimension: every projection
partition already has entropy rate `0` by `cntEntropyPartition_eq_zero`, and the constant cell map
`Fin d → Fin 1` witnesses nonemptiness. -/
theorem cntDynamicalEntropyAbelian_eq_zero (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) :
    cntDynamicalEntropyAbelian μ hμ σ = 0 := by
  unfold cntDynamicalEntropyAbelian
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => iSup_le fun c => ?_
    rw [cntEntropyPartition_eq_zero]
    exact le_of_eq EReal.coe_zero
  · refine le_iSup_of_le 1 (le_iSup_of_le (fun _ => (0 : Fin 1)) ?_)
    rw [cntEntropyPartition_eq_zero]
    exact le_of_eq EReal.coe_zero.symm

/-- The **full abelian-corner CNT dynamical entropy**: the supremum of the partition entropy rate
over **all** operational partitions whose operators are diagonal (soft/POVM partitions of the
diagonal subalgebra), not merely the sharp projection partitions of `cntDynamicalEntropyAbelian`. -/
def cntDynamicalEntropyAbelianFull (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) : EReal :=
  ⨆ k : ℕ, ⨆ X : {X : OperationalPartition d k // ∀ i, (X.op i).IsDiag},
    ((cntEntropyPartition (adPerm σ) (densityOfPMF μ hμ) X.1 : ℝ) : EReal)

/-- The full abelian-corner CNT dynamical entropy vanishes in finite dimension: every diagonal
operational partition has entropy rate `0`, and the diagonal projection partition of the constant
cell map witnesses nonemptiness. -/
theorem cntDynamicalEntropyAbelianFull_eq_zero (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) :
    cntDynamicalEntropyAbelianFull μ hμ σ = 0 := by
  unfold cntDynamicalEntropyAbelianFull
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => iSup_le fun X => ?_
    rw [cntEntropyPartition_eq_zero]
    exact le_of_eq EReal.coe_zero
  · refine le_iSup_of_le 1 (le_iSup_of_le ⟨projPartition (fun _ : Fin d => (0 : Fin 1)),
      fun i => by rw [projPartition_op]; exact Matrix.isDiag_diagonal _⟩ ?_)
    rw [cntEntropyPartition_eq_zero]
    exact le_of_eq EReal.coe_zero.symm

/-- **Free monotonicity.**  The abelian-corner CNT entropy is dominated by the full diagonal
version, since every projection partition `projPartition c` is diagonal
(`Matrix.isDiag_diagonal`). -/
theorem cntDynamicalEntropyAbelian_le_full (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) :
    cntDynamicalEntropyAbelian μ hμ σ ≤ cntDynamicalEntropyAbelianFull μ hμ σ := by
  unfold cntDynamicalEntropyAbelian cntDynamicalEntropyAbelianFull
  refine iSup_le fun k => iSup_le fun c => ?_
  refine le_iSup_of_le k (le_iSup_of_le ⟨projPartition c, fun i => ?_⟩ ?_)
  · rw [projPartition_op]; exact Matrix.isDiag_diagonal _
  · exact le_rfl

/-- **Full abelian-corner identity.**  The full diagonal CNT dynamical entropy equals the classical
Kolmogorov–Sinai entropy of `⇑σ`.  Both sides are `0`: the left by
`cntDynamicalEntropyAbelianFull_eq_zero` (finite-dimensional degeneracy), the right because the KS
entropy of a permutation of a finite set is `0` (via the existing abelian-corner identity). -/
theorem cntDynamicalEntropyAbelianFull_eq_ksEntropy
    (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) (hinv : ∀ i, μ (σ i) = μ i) (hpos : ∀ i, 0 < μ i) :
    haveI := probMeasure_isProb μ hμ
    cntDynamicalEntropyAbelianFull μ hμ σ
      = ErgodicTheory.Entropy.ksEntropy (measurePreserving_perm μ σ hinv) := by
  haveI := probMeasure_isProb μ hμ
  rw [cntDynamicalEntropyAbelianFull_eq_zero,
    ← cntDynamicalEntropyAbelian_eq_ksEntropy μ hμ σ hinv hpos, cntDynamicalEntropyAbelian_eq_zero]

/-- **KS entropy = full CNT dynamical entropy.**  The classical Kolmogorov–Sinai entropy of `⇑σ`
equals the *full* CNT dynamical entropy — the supremum over **all** operational partitions, not
only the diagonal ones — upgrading the one-sided bound `ksEntropy_le_cntDynamicalEntropy` to a full
equality.  Both sides are `0`: the KS entropy of a finite-set permutation, and (by
`cntDynamicalEntropy_eq_zero`) the finite-dimensional CNT dynamical entropy. -/
theorem ksEntropy_eq_cntDynamicalEntropy
    (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) (hinv : ∀ i, μ (σ i) = μ i) (hpos : ∀ i, 0 < μ i) :
    haveI := probMeasure_isProb μ hμ
    ErgodicTheory.Entropy.ksEntropy (measurePreserving_perm μ σ hinv)
      = cntDynamicalEntropy (adPerm σ) (densityOfPMF μ hμ) := by
  haveI := probMeasure_isProb μ hμ
  rw [← cntDynamicalEntropyAbelian_eq_ksEntropy μ hμ σ hinv hpos,
    cntDynamicalEntropyAbelian_eq_zero, cntDynamicalEntropy_eq_zero]

end ErgodicTheory.OperatorEntropy.CNT
