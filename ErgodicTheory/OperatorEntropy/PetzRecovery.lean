/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import ErgodicTheory.OperatorEntropy.Basic

/-!
# The algebraic Petz recovery map and the σ-recovery identity

This module develops the finite-dimensional **Petz (transpose) recovery map** in Kraus form and
proves the basic *recovery identity*: if `σ` is a state and `Λ` a completely positive
trace-preserving (CPTP) channel with invertible output `Λ(σ)`, then the Petz map
`P_{σ,Λ}` recovers `σ` from `Λ(σ)`:

  `P_{σ,Λ}(Λ σ) = σ`.

The Petz map is defined via conjugation by square roots:

  `P_{σ,Λ}(X) = √σ · Λ†( (Λ σ)^{-1/2} · X · (Λ σ)^{-1/2} ) · √σ`,

using `CFC.conjSqrt c a = √c · a · √c` and the Hilbert–Schmidt (Heisenberg) adjoint
`Λ† X = ∑ᵢ Kᵢ† X Kᵢ` of the Schrödinger channel `Λ ρ = ∑ᵢ Kᵢ ρ Kᵢ†`.

## Main definitions

* `ErgodicTheory.OperatorEntropy.KrausChannel`: a finite-dimensional CP map in Kraus form with
  `∑ᵢ Kᵢ† Kᵢ = 1` (hence trace preserving).
* `KrausChannel.toMat` / `KrausChannel.toDM`: the Schrödinger action on matrices / states.
* `KrausChannel.adj`: the Hilbert–Schmidt adjoint (Heisenberg picture).
* `petz`: the Petz recovery map.

## Main results

* `KrausChannel.toMat_trace`: the channel is trace preserving.
* `KrausChannel.adj_unital`: the adjoint is unital, `Λ† 1 = 1`.
* `KrausChannel.adj_hsAdjoint`: `adj` is the Hilbert–Schmidt adjoint of `toMat`.
* `petz_recovery`: the recovery identity `petz σ Λ (Λ σ) = σ`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite-dimensional completely positive map in **Kraus form**: a finite family of Kraus
operators `K : ι → Matrix n n ℂ` satisfying the trace-preservation condition
`∑ᵢ Kᵢ† Kᵢ = 1`. -/
structure KrausChannel (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The (finite) index set of Kraus operators. -/
  ι : Type*
  /-- The index set is finite. -/
  [fι : Fintype ι]
  /-- The Kraus operators. -/
  K : ι → Matrix n n ℂ
  /-- Trace-preservation / completeness relation. -/
  htp : ∑ i, (K i)ᴴ * (K i) = 1

attribute [instance] KrausChannel.fι

variable (Λ : KrausChannel n)

/-- The **Schrödinger action** of a Kraus channel on matrices: `Λ X = ∑ᵢ Kᵢ X Kᵢ†`. -/
def KrausChannel.toMat (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, Λ.K i * X * (Λ.K i)ᴴ

/-- The Schrödinger action is **trace preserving**: `tr (Λ X) = tr X`. -/
theorem KrausChannel.toMat_trace (X : Matrix n n ℂ) :
    (Λ.toMat X).trace = X.trace := by
  unfold KrausChannel.toMat
  rw [Matrix.trace_sum]
  have h : ∀ i, (Λ.K i * X * (Λ.K i)ᴴ).trace = ((Λ.K i)ᴴ * Λ.K i * X).trace := fun i => by
    rw [Matrix.trace_mul_comm (Λ.K i * X) ((Λ.K i)ᴴ), ← mul_assoc]
  simp_rw [h]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, Λ.htp, Matrix.one_mul]

/-- The Schrödinger action bundled as a map on **density matrices** (states). Positive
semidefiniteness follows from `PosSemidef.mul_mul_conjTranspose_same`; unit trace from
trace preservation. -/
def KrausChannel.toDM (ρ : DensityMatrix n) : DensityMatrix n where
  val := Λ.toMat ρ.val
  posSemidef := by
    unfold KrausChannel.toMat
    exact Matrix.posSemidef_sum _ fun i _ => ρ.posSemidef.mul_mul_conjTranspose_same (Λ.K i)
  trace_one := by rw [Λ.toMat_trace, ρ.trace_one]

/-- The **Hilbert–Schmidt (Heisenberg) adjoint** of a Kraus channel: `Λ† X = ∑ᵢ Kᵢ† X Kᵢ`. -/
def KrausChannel.adj (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (Λ.K i)ᴴ * X * Λ.K i

/-- The Heisenberg adjoint is **unital**: `Λ† 1 = 1`. This is exactly the Kraus
completeness relation. -/
theorem KrausChannel.adj_unital : Λ.adj 1 = 1 := by
  unfold KrausChannel.adj
  simp only [mul_one]
  exact Λ.htp

/-- `KrausChannel.adj` is the **Hilbert–Schmidt adjoint** of `KrausChannel.toMat`: for all `A B`,
`⟪A, Λ B⟫ = ⟪Λ† A, B⟫` in the Hilbert–Schmidt inner product `⟪X, Y⟫ = tr (Xᴴ Y)`. -/
theorem KrausChannel.adj_hsAdjoint (A B : Matrix n n ℂ) :
    (Aᴴ * Λ.toMat B).trace = ((Λ.adj A)ᴴ * B).trace := by
  unfold KrausChannel.toMat KrausChannel.adj
  rw [Matrix.mul_sum, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← mul_assoc]
  rw [Matrix.trace_mul_comm (Aᴴ * Λ.K i * B) ((Λ.K i)ᴴ)]
  simp only [← mul_assoc]

/-- The **Petz recovery map** of a state `σ` through a channel `Λ`:
`P_{σ,Λ}(X) = √σ · Λ†( (Λ σ)^{-1/2} · X · (Λ σ)^{-1/2} ) · √σ`, expressed via `CFC.conjSqrt`. -/
def petz (σ : DensityMatrix n) (Λ : KrausChannel n) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.conjSqrt σ.val (Λ.adj (CFC.conjSqrt (Ring.inverse (Λ.toDM σ).val) X))

/-- **Petz recovery identity.** If the channel output `Λ σ` is positive definite (invertible),
then the Petz map recovers the input state: `petz σ Λ (Λ σ) = σ`. -/
theorem petz_recovery (σ : DensityMatrix n) (Λ : KrausChannel n)
    (hpd : (Λ.toDM σ).val.PosDef) :
    petz σ Λ (Λ.toDM σ).val = σ.val := by
  unfold petz
  rw [CFC.conjSqrt_ringInverse_self _ hpd.isStrictlyPositive, Λ.adj_unital,
    CFC.conjSqrt_one σ.val σ.posSemidef.nonneg]

/-! ## Non-vacuity: the identity channel -/

/-- The **identity channel** `X ↦ X`, with a single Kraus operator `K = 1`. -/
def KrausChannel.id (n : Type*) [Fintype n] [DecidableEq n] : KrausChannel n where
  ι := Unit
  K := fun _ => 1
  htp := by simp

@[simp]
theorem KrausChannel.id_toMat (X : Matrix n n ℂ) : (KrausChannel.id n).toMat X = X := by
  simp [KrausChannel.toMat, KrausChannel.id, Finset.sum_const]

/-- The maximally mixed state is positive definite (a scalar multiple of the identity). -/
theorem DensityMatrix.maximallyMixed_posDef [Nonempty n] :
    (DensityMatrix.maximallyMixed : DensityMatrix n).val.PosDef := by
  have hpos : (0 : ℝ) < ((Fintype.card n : ℝ)⁻¹) := by
    have : 0 < Fintype.card n := Fintype.card_pos
    positivity
  change (((Fintype.card n : ℝ)⁻¹ : ℝ) • (1 : Matrix n n ℂ)).PosDef
  exact Matrix.PosDef.one.smul hpos

/-- Non-vacuity certificate: the recovery identity `petz_recovery` fires on a concrete instance —
the identity channel applied to the maximally mixed state of a two-level system. -/
example :
    petz (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)) (KrausChannel.id (Fin 2))
        ((KrausChannel.id (Fin 2)).toDM DensityMatrix.maximallyMixed).val
      = DensityMatrix.maximallyMixed.val :=
  petz_recovery _ _ <| by
    change ((KrausChannel.id (Fin 2)).toMat DensityMatrix.maximallyMixed.val).PosDef
    rw [KrausChannel.id_toMat]
    exact DensityMatrix.maximallyMixed_posDef

end ErgodicTheory.OperatorEntropy
