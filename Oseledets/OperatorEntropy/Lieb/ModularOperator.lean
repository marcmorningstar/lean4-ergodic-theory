/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.JointConvexity

/-!
# The relative modular operator and the modular form of the relative entropy

In finite dimensions the **relative modular operator** `Δ_{σ|ρ} : X ↦ σ X ρ⁻¹` acting on the
Hilbert–Schmidt space of matrices is, in the vectorisation `X ↦ vec X`, the Kronecker matrix
`ρ⁻¹ ⊗ σᵀ`.  This is exactly the *argument* of the operator perspective for the commuting Effros
pair `(L, R) = (1 ⊗ σᵀ, ρ ⊗ 1)` used in `Oseledets.OperatorEntropy.Lieb.JointConvexity`:

`R^{-1/2} · L · R^{-1/2} = ρ⁻¹ ⊗ σᵀ = Δ_{σ|ρ}`.

Consequently the Umegaki relative entropy is realised in **modular / perspective form**: with the
vectorised identity `vec 1` and the positive functional `relForm M = ⟪vec 1, M · vec 1⟫`,

`S(ρ‖σ) = ⟪vec 1, P_{-log}(1 ⊗ σᵀ, ρ ⊗ 1) · vec 1⟫.re`,

where `P_{-log}` is the operator perspective of `-log`, i.e. `-log Δ_{σ|ρ}` sandwiched by `R^{1/2}`.
This is the concrete bridge realising `relEntropy` through the relative modular operator,
feeding the Petz-equality analysis.

## Main results

* `Oseledets.OperatorEntropy.Lieb.relModularArg`: the vectorised relative modular operator
  argument `ρ⁻¹ ⊗ σᵀ`.
* `Oseledets.OperatorEntropy.Lieb.relModularArg_eq_perspArg`: it is the perspective argument of the
  Effros pair `(1 ⊗ σᵀ, ρ ⊗ 1)`.
* `Oseledets.OperatorEntropy.Lieb.relEntropy_eq_relForm`: the modular/perspective form of the
  relative entropy.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The (vectorised) finite-dimensional **relative modular operator** argument
`Δ_{σ|ρ} : X ↦ σ X ρ⁻¹`, realised on `vec X` as the Kronecker matrix `ρ⁻¹ ⊗ σᵀ`. -/
def relModularArg (ρ σ : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := CFC.rpow ρ (-1) ⊗ₖ σᵀ

/-- The relative modular operator argument is the perspective argument of the Effros pair
`(L, R) = (1 ⊗ σᵀ, ρ ⊗ 1)`: `R^{-1/2} · L · R^{-1/2} = ρ⁻¹ ⊗ σᵀ = Δ_{σ|ρ}`. -/
theorem relModularArg_eq_perspArg {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (σ : Matrix n n ℂ) :
    CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2)) * ((1 : Matrix n n ℂ) ⊗ₖ σᵀ)
      * CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2)) = relModularArg ρ σ :=
  perspArg_kron hρ σ

/-- **Modular / perspective form of the relative entropy.** For faithful density matrices,
`S(ρ‖σ) = ⟪vec 1, P_{-log}(1 ⊗ σᵀ, ρ ⊗ 1) · vec 1⟫.re`, i.e. `relEntropy` is the positive
functional `relForm` applied to the operator perspective of `-log` at the Effros pair whose
perspective argument is the relative modular operator `Δ_{σ|ρ} = ρ⁻¹ ⊗ σᵀ`. -/
theorem relEntropy_eq_relForm (ρ σ : DensityMatrix n) (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) :
    relEntropy ρ σ = (relForm (opPersp (fun x => -Real.log x)
        ((1 : Matrix n n ℂ) ⊗ₖ σ.valᵀ) (ρ.val ⊗ₖ 1))).re := by
  rw [← relEntropyMat_eq_relEntropy ρ σ hσ, relEntropyMat, ← relForm_opPersp_neg_log hρ hσ]

end Oseledets.OperatorEntropy.Lieb

end
