/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.StinespringReduction
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessingCPTP
import ErgodicTheory.OperatorEntropy.PetzRecovery

/-!
# Issue #28 — STEP 0: the Stinespring dilation with the relative-entropy identity

The `⟸` direction of Petz's equality theorem (`petz_recovery_implies_equality` in
`Lieb/DataProcessingCPTP.lean`) is fed by the **data-processing inequality** for the on-main
*faithful-ancilla Stinespring family*

`Λ_{α,U} ρ = Tr_e (U (ρ ⊗ α) Uᴴ) = ((ρ ⊗ α)ᵁ)_A`   (`monotonicity_relEntropy_under_stinespring`).

STEP 0 packages that dilation into reusable named pieces:

* `dilatedState α U ρ` — the pre-trace dilated state `ω(ρ) = U (ρ ⊗ α) Uᴴ`.
* `dilationChannel α U ρ` — the realized channel `Tr_e (ω(ρ))`.
* `relEntropy_dilatedState` — **(ii) the relative-entropy identity**
  `D(ω ρ ‖ ω σ) = D(ρ ‖ σ)` (from `relEntropy_embed_invariant`).
* `dilatedState_posDef` — **(iii) faithfulness is transported**: `ω(ρ)` is `PosDef` when `ρ, α`
  are (from `Matrix.PosDef.kronecker` + `Matrix.IsUnit.posDef_star_right_conjugate_iff`).
* `relEntropy_dilationChannel_le` — the DPI for the channel, i.e.
  `monotonicity_relEntropy_under_stinespring` re-exported in the `dilationChannel` naming.

For the **channel-realization** part (i) `Tr_e (ω ρ) = Λ.toDM ρ` we realize the two families that
*are* faithfully realizable exactly:

* `dilationChannel_one_eq_id` — the trivial dilation `U = 1` realizes the identity channel
  `KrausChannel.id` (non-vacuity, faithful ancilla).
* `dilationChannel_unitaryConj` / `step0_unitary` — the dilation with `U = W ⊗ 1` realizes the
  **unitary channel** `ρ ↦ W ρ Wᴴ` (`KrausChannel.unitaryConj W`) *exactly, with an arbitrary
  faithful ancilla* `α`, and simultaneously delivers (ii) and (iii).  This is a complete STEP 0
  for the unitary (hence mixed-unitary) sub-family.

## The obstruction to a *general* Kraus channel (documented, not formalized)

Realizing an *arbitrary* `KrausChannel Λ` (Kraus operators `{Mᵢ}`, `∑ Mᵢᴴ Mᵢ = 1`) *exactly* by
this dilation with a **faithful** `α` is **impossible in general**.  Writing
`α = ∑ₐ pₐ |a⟩⟨a|` (all `pₐ > 0`) gives `Λ_{α,U} ρ = ∑_{a,b} pₐ K_{ba} ρ K_{ba}ᴴ` with
`K_{ba} = ⟨b|U|a⟩` the environment blocks of `U`.  A Choi-range match forces every block
`K_{ba} ∈ span{Mᵢ}`, and unitarity of `U` (`∑_b K_{ba}ᴴ K_{ba'} = δ_{aa'} 1`) then forces, for
amplitude damping (`M₀ = diag(1, √(1-γ))`, `M₁ = √γ · E₀₁`), the column families `{x^{(a)}}` and
`{y^{(a)}}` (coordinates in the `M₀, M₁` basis) to be two orthonormal bases of `ℂ^{|E|}` that are
*mutually* orthogonal — forcing `y = 0`, a contradiction.  So amplitude damping lies **outside**
the faithful-ancilla Stinespring family; the standard exact dilation of a general channel uses a
**pure** ancilla (via the isometry `V ψ = ∑ᵢ (Mᵢ ψ) ⊗ |i⟩`), which is incompatible with the
faithful-ancilla relative-entropy identity used here.  See the STEP 0 report.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## The dilation state and channel -/

section Dilation

variable {n e : Type*} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

/-- The **pre-trace dilated state** `ω(ρ) = U (ρ ⊗ α) Uᴴ`: adjoin the ancilla `α` and conjugate by
the unitary dilation `U`.  This is the object on which the relative-entropy identity holds. -/
def dilatedState (α : DensityMatrix e) (U : Matrix.unitaryGroup (n × e) ℂ)
    (ρ : DensityMatrix n) : DensityMatrix (n × e) :=
  (ρ.kron α).conj U

/-- The **Stinespring channel** realized by `(α, U)`: `Λ_{α,U} ρ = Tr_e (U (ρ ⊗ α) Uᴴ)`. -/
def dilationChannel (α : DensityMatrix e) (U : Matrix.unitaryGroup (n × e) ℂ)
    (ρ : DensityMatrix n) : DensityMatrix n :=
  (dilatedState α U ρ).partialTraceRight

/-- **(ii) The relative-entropy identity.**  The dilation `ρ ↦ ω(ρ) = U (ρ ⊗ α) Uᴴ` leaves the
Umegaki relative entropy unchanged: `D(ω ρ ‖ ω σ) = D(ρ ‖ σ)` (faithful ancilla `α`, faithful
`σ`).  Immediate from `relEntropy_embed_invariant`. -/
theorem relEntropy_dilatedState (ρ σ : DensityMatrix n) (α : DensityMatrix e)
    (U : Matrix.unitaryGroup (n × e) ℂ) (hα : α.val.PosDef) (hσ : σ.val.PosDef) :
    relEntropy (dilatedState α U ρ) (dilatedState α U σ) = relEntropy ρ σ :=
  relEntropy_embed_invariant ρ σ α U hα hσ

/-- **(iii) Faithfulness is transported.**  If `ρ` and the ancilla `α` are faithful (`PosDef`) then
so is the dilated state `ω(ρ) = U (ρ ⊗ α) Uᴴ`.  The Kronecker product of two `PosDef` matrices is
`PosDef` (`Matrix.PosDef.kronecker`), and unitary conjugation preserves `PosDef`
(`Matrix.IsUnit.posDef_star_right_conjugate_iff`). -/
theorem dilatedState_posDef (ρ : DensityMatrix n) (α : DensityMatrix e)
    (U : Matrix.unitaryGroup (n × e) ℂ) (hρ : ρ.val.PosDef) (hα : α.val.PosDef) :
    (dilatedState α U ρ).val.PosDef := by
  have hU : IsUnit (U : Matrix (n × e) (n × e) ℂ) :=
    ⟨⟨(U : Matrix (n × e) (n × e) ℂ), star (U : Matrix (n × e) (n × e) ℂ),
        Unitary.coe_mul_star_self U, Unitary.coe_star_mul_self U⟩, rfl⟩
  have hval : (dilatedState α U ρ).val
      = (U : Matrix (n × e) (n × e) ℂ) * (ρ.kron α).val
        * star (U : Matrix (n × e) (n × e) ℂ) := rfl
  rw [hval, Matrix.IsUnit.posDef_star_right_conjugate_iff hU]
  exact Matrix.PosDef.kronecker hρ hα

/-! ### Non-vacuity: the trivial dilation realizes the identity channel -/

/-- The **trivial dilation** `U = 1` gives back the input: `Λ_{α,1} ρ = ρ`. -/
theorem dilationChannel_one (ρ : DensityMatrix n) (α : DensityMatrix e) :
    dilationChannel α 1 ρ = ρ :=
  stinespring_trivial_dilation ρ α

/-- **The trivial dilation realizes the identity Kraus channel** (with an arbitrary ancilla `α`):
`Λ_{α,1} = KrausChannel.id`.  Witnesses that the faithful-ancilla Stinespring family is non-empty
and contains a genuine `KrausChannel`. -/
theorem dilationChannel_one_eq_id (ρ : DensityMatrix n) (α : DensityMatrix e) :
    dilationChannel α 1 ρ = (KrausChannel.id n).toDM ρ := by
  have hid : (KrausChannel.id n).toDM ρ = ρ := by
    apply DensityMatrix.ext
    change (KrausChannel.id n).toMat ρ.val = ρ.val
    rw [KrausChannel.id_toMat]
  rw [dilationChannel_one, hid]

/-! ### The unitary channel `ρ ↦ W ρ Wᴴ` (exact, faithful ancilla) -/

/-- `W ⊗ 1` as a unitary on the composite system `n × e`, for `W` unitary on `n`.  This is the
dilation whose partial trace realizes the unitary channel `ρ ↦ W ρ Wᴴ`. -/
def kronRightOne (W : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (n × e) ℂ :=
  ⟨(W : Matrix n n ℂ) ⊗ₖ (1 : Matrix e e ℂ),
    Matrix.kronecker_mem_unitary W.2 (one_mem _)⟩

/-- The **unitary channel** `ρ ↦ W ρ Wᴴ` as a single-Kraus-operator channel. -/
def KrausChannel.unitaryConj (W : Matrix.unitaryGroup n ℂ) : KrausChannel n where
  ι := Unit
  K := fun _ => (W : Matrix n n ℂ)
  htp := by
    simp only [Finset.univ_unique, Finset.sum_singleton, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self W

/-- The unitary Kraus channel acts as unitary conjugation on states:
`(KrausChannel.unitaryConj W).toDM ρ = W ρ Wᴴ = ρ.conj W`. -/
theorem KrausChannel.unitaryConj_toDM (W : Matrix.unitaryGroup n ℂ) (ρ : DensityMatrix n) :
    (KrausChannel.unitaryConj W).toDM ρ = ρ.conj W := by
  apply DensityMatrix.ext
  change (KrausChannel.unitaryConj W).toMat ρ.val
      = (W : Matrix n n ℂ) * ρ.val * star (W : Matrix n n ℂ)
  simp only [KrausChannel.toMat, KrausChannel.unitaryConj, Finset.univ_unique,
    Finset.sum_singleton, Matrix.star_eq_conjTranspose]

/-- The dilation by `U = W ⊗ 1` realizes unitary conjugation: `Λ_{α, W⊗1} ρ = W ρ Wᴴ`, for **any**
ancilla `α`.  Computation: `(W⊗1)(ρ⊗α)(W⊗1)ᴴ = (WρWᴴ) ⊗ α`, whose right partial trace is `WρWᴴ`. -/
theorem dilationChannel_kronRightOne (W : Matrix.unitaryGroup n ℂ) (α : DensityMatrix e)
    (ρ : DensityMatrix n) :
    dilationChannel α (kronRightOne W) ρ = ρ.conj W := by
  have hstate : dilatedState α (kronRightOne (e := e) W) ρ = (ρ.conj W).kron α := by
    apply DensityMatrix.ext
    change ((W : Matrix n n ℂ) ⊗ₖ (1 : Matrix e e ℂ)) * (ρ.val ⊗ₖ α.val)
        * star ((W : Matrix n n ℂ) ⊗ₖ (1 : Matrix e e ℂ))
      = ((W : Matrix n n ℂ) * ρ.val * star (W : Matrix n n ℂ)) ⊗ₖ α.val
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.star_eq_conjTranspose]
  unfold dilationChannel
  rw [hstate, partialTraceRight_kron]

/-- **The unitary channel is realized exactly by a faithful-ancilla Stinespring dilation:**
`Λ_{α, W⊗1} = KrausChannel.unitaryConj W` for an arbitrary ancilla `α`. -/
theorem dilationChannel_unitaryConj (W : Matrix.unitaryGroup n ℂ) (α : DensityMatrix e)
    (ρ : DensityMatrix n) :
    dilationChannel α (kronRightOne W) ρ = (KrausChannel.unitaryConj W).toDM ρ := by
  rw [dilationChannel_kronRightOne, KrausChannel.unitaryConj_toDM]

/-- **STEP 0 for the unitary sub-family (bundled).**  For a unitary `W`, an arbitrary faithful
ancilla `α`, and faithful states `ρ, σ`, the dilation `U = W ⊗ 1` realizes the Kraus channel
`KrausChannel.unitaryConj W` exactly on both states (i), transports the relative entropy (ii), and
transports faithfulness (iii). -/
theorem step0_unitary (W : Matrix.unitaryGroup n ℂ) (α : DensityMatrix e) (hα : α.val.PosDef)
    (ρ σ : DensityMatrix n) (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) :
    dilationChannel α (kronRightOne W) ρ = (KrausChannel.unitaryConj W).toDM ρ
      ∧ dilationChannel α (kronRightOne W) σ = (KrausChannel.unitaryConj W).toDM σ
      ∧ relEntropy (dilatedState α (kronRightOne W) ρ) (dilatedState α (kronRightOne W) σ)
          = relEntropy ρ σ
      ∧ (dilatedState α (kronRightOne W) ρ).val.PosDef
      ∧ (dilatedState α (kronRightOne W) σ).val.PosDef :=
  ⟨dilationChannel_unitaryConj W α ρ, dilationChannel_unitaryConj W α σ,
    relEntropy_dilatedState ρ σ α _ hα hσ, dilatedState_posDef ρ α _ hρ hα,
    dilatedState_posDef σ α _ hσ hα⟩

end Dilation

/-! ## The data-processing inequality for the dilation channel (universe `0`) -/

section Mono

-- `Type` (universe `0`) to match the monomorphic wall `RelEntropyMonotoneUnderPartialTrace`.
variable {n e : Type} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

/-- **The data-processing inequality for the dilation channel** (unconditional): the faithful-
ancilla Stinespring channel never increases relative entropy, `D(Λ_{α,U} ρ ‖ Λ_{α,U} σ) ≤ D(ρ ‖ σ)`.
This is `monotonicity_relEntropy_under_stinespring` in the `dilationChannel` naming. -/
theorem relEntropy_dilationChannel_le (α : DensityMatrix e) (U : Matrix.unitaryGroup (n × e) ℂ)
    (hα : α.val.PosDef) (ρ σ : DensityMatrix n) (hσ : σ.val.PosDef) :
    relEntropy (dilationChannel α U ρ) (dilationChannel α U σ) ≤ relEntropy ρ σ :=
  monotonicity_relEntropy_under_stinespring α U hα ρ σ hσ

end Mono

end ErgodicTheory.OperatorEntropy
