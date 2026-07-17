/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.GrowingTower.Tower

/-!
# Shift-invariant product states of the one-sided qubit chain

This module records the **shift-invariance** of the product-state family `rhoPow ρ` built in
`Tower.lean`.  Where the tower there packages the *growing carrier* `Qbits n` together with the
capacity-enlargement embedding `shiftAdjoinQubit` (`A ↦ 1 ⊗ A`) and the marginal-consistency law
`rhoPow_partialTraceLeft`, here we express the dual, algebraic-state side of that same picture:
every product state is **shift-invariant in the pairing sense**

`τ_{n+1}(shiftAdjoinQubit x) = τ_n(x)`,     where `τ_n(y) := trace ((rhoPow ρ n).val * y)`

(`rhoPow_shiftAdjoinQubit_pairing`).  Evaluating the enlarged state on an observable that ignores
the fresh qubit returns the previous-block expectation: the states `τ_n` fit together into one
shift-invariant state of the one-sided chain, the state-space counterpart of the marginal
consistency already in `Tower.lean`.

Among these product states the **tracial** one is the maximally mixed family
`τ_n = maximallyMixed`.  It is closed under the tensor step (`kron_maximallyMixed`), so
`rhoPow maximallyMixed n = maximallyMixed` for every `n` (`rhoPow_maximallyMixed`); it is thus in
addition **inclusion-compatible** — the same normalized trace at every level — and the pairing
specializes to `maximallyMixed_shiftAdjoinQubit_pairing`.

## Provenance

The shift-invariant states of a quantum spin chain and the tracial (maximally mixed) reference
state are standard (Connes–Narnhofer–Thirring, *Dynamical entropy of C\*-algebras and von Neumann
algebras*, Comm. Math. Phys. **112** (1987); Bratteli–Robinson, *Operator Algebras and Quantum
Statistical Mechanics II*).  The new content is the packaging on the finite growing tower: the
pairing identity above as the state-side shift-invariance matching the marginal consistency of
`Tower.lean`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## The tracial (maximally mixed) product state -/

/-- The maximally mixed state is closed under the tensor product: `mm ⊗ mm = mm`.  Concretely
`(a⁻¹ • 1) ⊗ₖ (b⁻¹ • 1) = (a·b)⁻¹ • 1` with `a = card nA`, `b = card nB`. -/
theorem kron_maximallyMixed {nA : Type*} [Fintype nA] [DecidableEq nA] [Nonempty nA]
    {nB : Type*} [Fintype nB] [DecidableEq nB] [Nonempty nB] :
    (DensityMatrix.maximallyMixed : DensityMatrix nA).kron
        (DensityMatrix.maximallyMixed : DensityMatrix nB)
      = DensityMatrix.maximallyMixed := by
  apply DensityMatrix.ext
  simp only [DensityMatrix.kron, DensityMatrix.maximallyMixed]
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul,
    Fintype.card_prod, Nat.cast_mul, mul_inv]

/-- The `n`-fold product of the maximally mixed single-qubit state is the maximally mixed state on
the whole block: the tracial state is a fixed point of the tower construction. -/
theorem rhoPow_maximallyMixed (n : ℕ) :
    rhoPow (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)) n
      = DensityMatrix.maximallyMixed := by
  induction n with
  | zero => rfl
  | succ k ih => rw [rhoPow, ih]; exact kron_maximallyMixed

/-! ## Shift-invariance of the product states (the pairing identity) -/

/-- **Shift-invariance of every product state.**  Pairing the enlarged state `rhoPow ρ (n+1)`
against an observable `shiftAdjoinQubit x = 1 ⊗ x` that acts trivially on the fresh qubit returns
the previous-block pairing against `x`:
`trace ((rhoPow ρ (n+1)).val * (1 ⊗ x)) = trace ((rhoPow ρ n).val * x)`.  This is the state-side
counterpart of the marginal consistency `rhoPow_partialTraceLeft`, exhibiting the family `τ_n` as
one shift-invariant state of the one-sided qubit chain. -/
theorem rhoPow_shiftAdjoinQubit_pairing (ρ : DensityMatrix (Fin 2)) (n : ℕ)
    (x : Matrix (Qbits n) (Qbits n) ℂ) :
    ((rhoPow ρ (n + 1)).val * shiftAdjoinQubit x).trace
      = ((rhoPow ρ n).val * x).trace := by
  have key :
      (ρ.val ⊗ₖ (rhoPow ρ n).val * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ x)).trace
        = ((rhoPow ρ n).val * x).trace := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker, ρ.trace_one, one_mul]
  rw [rhoPow]
  exact key

/-- **Shift-invariance of the tracial state.**  The maximally mixed family is shift-invariant in
the pairing sense: `trace (mm_{n+1} · (1 ⊗ x)) = trace (mm_n · x)`.  Specializes
`rhoPow_shiftAdjoinQubit_pairing` at the tracial (maximally mixed) reference state. -/
theorem maximallyMixed_shiftAdjoinQubit_pairing (n : ℕ)
    (x : Matrix (Qbits n) (Qbits n) ℂ) :
    ((DensityMatrix.maximallyMixed : DensityMatrix (Qbits (n + 1))).val
        * shiftAdjoinQubit x).trace
      = ((DensityMatrix.maximallyMixed : DensityMatrix (Qbits n)).val * x).trace := by
  have h := rhoPow_shiftAdjoinQubit_pairing
    (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)) n x
  rwa [rhoPow_maximallyMixed, rhoPow_maximallyMixed] at h

end ErgodicTheory.OperatorEntropy
