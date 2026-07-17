/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.RelativeEntropy
import ErgodicTheory.OperatorEntropy.RelEntropyAdditivity
import ErgodicTheory.OperatorEntropy.Additivity
import ErgodicTheory.OperatorEntropy.Subadditivity
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Issue #22 — the Stinespring reduction: isolating the DPI to ONE clean `Prop`

The data-processing inequality (DPI, monotonicity of Umegaki relative entropy under a quantum
channel) reduces, via Stinespring dilation, to a single partial-trace step, which this module
isolates as one honestly-stated `Prop`

`RelEntropyMonotoneUnderPartialTrace` : partial-trace monotonicity of relative entropy.

This `Prop` was the Lieb-concavity / joint-convexity wall of issue #22 (Mathlib-absent at the
time); it is now **discharged unconditionally** by `relEntropyMonotone_partialTrace`
(`Lieb/DataProcessingGeneral.lean`).  This module keeps it as the clean interface and proves —
**unconditionally** — the two elementary links that reduce a general Stinespring-dilated channel
to that one partial-trace step:

* `relEntropy_embed_invariant` — an **isometric embedding** `ρ ↦ (ρ ⊗ α)ᵁ` (adjoin a faithful
  ancilla, then conjugate by a unitary dilation `U`) leaves relative entropy invariant.  This is a
  one-line corollary of unitary invariance (`relEntropy_conj_invariant`) and ancilla invariance
  (`relEntropy_ancilla_invariant`).
* `partialTraceRight_kron` — tracing out an adjoined ancilla returns the input, so the trivial
  dilation `U = 1` recovers the **identity channel** (`stinespring_trivial_dilation`); the
  Stinespring channel family is therefore inhabited, and `stinespring_relEntropy_monotone` is not
  vacuous.

The headline `stinespring_relEntropy_monotone` then reads: *given* the partial-trace DPI
(`hwall`), every Stinespring-dilated channel `Λ ρ = ((ρ ⊗ α)ᵁ)_A` (with a faithful ancilla `α` and
unitary dilation `U`) is relative-entropy monotone on faithful states.  Every non-trivial content
is packed into the single `hwall` hypothesis, exactly as `IsRelEntropyMonotone` localizes the
consumer corollary in `RelativeEntropy.lean`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## The DPI wall, as a single explicit `Prop` -/

/-- **The DPI wall (as a `Prop` interface).**  *Partial-trace monotonicity of Umegaki relative
entropy*: tracing out a subsystem never increases the relative entropy of two states (faithful
second argument).  This is equivalent to strong subadditivity / Lieb's joint convexity; it was
Mathlib-absent, so here it is stated as an explicit `Prop` that downstream monotonicity results
take as a hypothesis.  It is discharged **unconditionally** by `relEntropyMonotone_partialTrace`
(`Lieb/DataProcessingGeneral.lean`).

The index types are quantified over `Type` (universe `0`) rather than `Type*`: finite-dimensional
quantum information lives in universe `0` (all index types are `Fin d` and products thereof), and a
`Type*`-polymorphic `Prop` used as a *hypothesis* fixes its own universe parameters, which could
then never be unified with those of the consumer's subsystems. -/
def RelEntropyMonotoneUnderPartialTrace : Prop :=
  ∀ {nA nE : Type} [Fintype nA] [DecidableEq nA] [Fintype nE] [DecidableEq nE]
    (ρ σ : DensityMatrix (nA × nE)), σ.val.PosDef →
      relEntropy (DensityMatrix.partialTraceRight ρ) (DensityMatrix.partialTraceRight σ)
        ≤ relEntropy ρ σ

/-! ## Tracing out an adjoined ancilla returns the input -/

section Reduction

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- **The partial trace of a product is the left factor.**  `Tr_B (ρ ⊗ α) = ρ` for any ancilla
`α` (using only `Tr α = 1`).  Hence adjoining an ancilla and immediately tracing it out is the
identity — the reduction underlying the trivial Stinespring dilation. -/
theorem partialTraceRight_kron (ρ : DensityMatrix nA) (α : DensityMatrix nB) :
    (ρ.kron α).partialTraceRight = ρ := by
  ext i i'
  change ∑ j : nB, (ρ.val ⊗ₖ α.val) (i, j) (i', j) = ρ.val i i'
  simp only [Matrix.kronecker_apply]
  rw [← Finset.mul_sum]
  have htr : (∑ j : nB, α.val j j) = 1 := by
    simpa only [Matrix.trace, Matrix.diag_apply] using α.trace_one
  rw [htr, mul_one]

/-- Tracing out the left factor of a Kronecker product recovers the right factor:
`Tr_A (ρ ⊗ σ) = σ`, since `ρ` has unit trace. -/
theorem partialTraceLeft_kron (ρ : DensityMatrix nA) (σ : DensityMatrix nB) :
    (ρ.kron σ).partialTraceLeft = σ := by
  apply DensityMatrix.ext
  ext j j'
  have htr : ∑ i : nA, ρ.val i i = 1 := ρ.trace_one
  simp only [DensityMatrix.partialTraceLeft, DensityMatrix.kron,
    partialTraceLeft_apply, Matrix.kronecker_apply, ← Finset.sum_mul, htr, one_mul]

end Reduction

/-! ## Isometric-embedding invariance and the Stinespring reduction -/

section Stinespring

variable {n e : Type*} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

/-- **Isometric-embedding invariance.**  Adjoining a faithful ancilla `α` and conjugating by a
unitary dilation `U` (an isometric embedding of `n` into `n × e`) leaves relative entropy
unchanged: `D((ρ ⊗ α)ᵁ ‖ (σ ⊗ α)ᵁ) = D(ρ ‖ σ)`.  Immediate from unitary invariance
(`relEntropy_conj_invariant`) and ancilla invariance (`relEntropy_ancilla_invariant`). -/
theorem relEntropy_embed_invariant (ρ σ : DensityMatrix n) (α : DensityMatrix e)
    (U : Matrix.unitaryGroup (n × e) ℂ) (hα : α.val.PosDef) (hσ : σ.val.PosDef) :
    relEntropy ((ρ.kron α).conj U) ((σ.kron α).conj U) = relEntropy ρ σ := by
  rw [relEntropy_conj_invariant, relEntropy_ancilla_invariant ρ σ α hα hσ]

/-- **The trivial dilation is the identity channel.**  With `U = 1` the Stinespring channel
`ρ ↦ ((ρ ⊗ α)ᵁ)_A` reduces to `ρ` — so the channel family contains the identity, witnessing that
`stinespring_relEntropy_monotone` is a statement about a non-empty class of channels (where its
conclusion is the sharp equality `D(ρ‖σ) ≤ D(ρ‖σ)`). -/
theorem stinespring_trivial_dilation (ρ : DensityMatrix n) (α : DensityMatrix e) :
    ((ρ.kron α).conj 1).partialTraceRight = ρ := by
  have hconj : (ρ.kron α).conj 1 = ρ.kron α := by
    ext i i'
    change ((1 : Matrix (n × e) (n × e) ℂ) * (ρ.kron α).val
        * star (1 : Matrix (n × e) (n × e) ℂ)) i i' = (ρ.kron α).val i i'
    rw [star_one, mul_one, one_mul]
  rw [hconj, partialTraceRight_kron]

end Stinespring

/-! ## The Stinespring reduction of the data-processing inequality -/

section MonoReduction

-- `Type` (universe `0`), so the monomorphic wall `Prop` `RelEntropyMonotoneUnderPartialTrace`
-- can be instantiated at the subsystems `n`, `e` (finite-dimensional QI lives in universe `0`).
variable {n e : Type} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

/-- **Stinespring reduction of the data-processing inequality.**  *Given* the partial-trace DPI
wall (`hwall`), every Stinespring-dilated channel `Λ ρ = ((ρ ⊗ α)ᵁ)_A` — adjoin a faithful ancilla
`α`, conjugate by a unitary dilation `U`, then trace out the ancilla — is relative-entropy
monotone on faithful states: `D(Λ ρ ‖ Λ σ) ≤ D(ρ ‖ σ)`.

The proof applies `hwall` to the two dilated states and rewrites the right-hand side with
`relEntropy_embed_invariant`; the only non-elementary input is the single `hwall` hypothesis. -/
theorem stinespring_relEntropy_monotone
    (hwall : RelEntropyMonotoneUnderPartialTrace)
    (α : DensityMatrix e) (U : Matrix.unitaryGroup (n × e) ℂ)
    (hα : α.val.PosDef) (ρ σ : DensityMatrix n) (hσ : σ.val.PosDef) :
    relEntropy (((ρ.kron α).conj U).partialTraceRight)
        (((σ.kron α).conj U).partialTraceRight)
      ≤ relEntropy ρ σ := by
  have hU : IsUnit (U : Matrix (n × e) (n × e) ℂ) :=
    ⟨⟨(U : Matrix (n × e) (n × e) ℂ), star (U : Matrix (n × e) (n × e) ℂ),
        Unitary.coe_mul_star_self U, Unitary.coe_star_mul_self U⟩, rfl⟩
  have hσkron : ((σ.kron α).conj U).val.PosDef := by
    have hval : ((σ.kron α).conj U).val
        = (U : Matrix (n × e) (n × e) ℂ) * (σ.kron α).val
          * star (U : Matrix (n × e) (n × e) ℂ) := rfl
    rw [hval, Matrix.IsUnit.posDef_star_right_conjugate_iff hU]
    exact Matrix.PosDef.kronecker hσ hα
  have hstep := hwall (nA := n) (nE := e) ((ρ.kron α).conj U) ((σ.kron α).conj U) hσkron
  rw [relEntropy_embed_invariant ρ σ α U hα hσ] at hstep
  exact hstep

end MonoReduction

end ErgodicTheory.OperatorEntropy
