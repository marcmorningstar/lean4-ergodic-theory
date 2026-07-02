/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.PetzRecovery

/-!
# Output support of a Kraus channel on a faithful input (Petz equality, general case)

This module supplies the **de-hypothesization** lemma for the general Petz-equality theorem
(issue #28): the output-faithfulness assumptions `(Λρ).PosDef`, `(Λσ).PosDef` are *removable*,
because for a **faithful** (positive-definite) input `ρ` the support of the channel output
`Λρ = ∑ᵢ Kᵢ ρ Kᵢᴴ` is *independent of which faithful `ρ`*: it is always `⨆ᵢ range Kᵢ`, dually the
kernel is always `⨅ᵢ ker Kᵢᴴ`.

The load-bearing fact is a **kernel characterization of the output** (`kraus_mulVec_eq_zero_iff`):
for a Kraus channel `Λ` with completeness relation `∑ᵢ Kᵢᴴ Kᵢ = 1`, a *faithful* input matrix `R`
(`R.PosDef`), and a vector `x`,

  `Λ.toMat R *ᵥ x = 0  ↔  ∀ i, (Kᵢ)ᴴ *ᵥ x = 0`.

The proof evaluates the output quadratic form
`xᴴ (Λ R) x = ∑ᵢ (Kᵢᴴ x)ᴴ R (Kᵢᴴ x)`, a sum of nonnegative terms (`R ≽ 0`); it vanishes iff each
`(Kᵢᴴ x)ᴴ R (Kᵢᴴ x)` does, and since `R ≻ 0` this forces `Kᵢᴴ x = 0`. Conversely if every
`Kᵢᴴ x = 0` then each summand `Kᵢ R Kᵢᴴ *ᵥ x = Kᵢ *ᵥ (R *ᵥ (Kᵢᴴ *ᵥ x)) = 0`.

## Main results

* `kraus_dotProduct_output`: the output quadratic form
  `xᴴ (Λ R) x = ∑ᵢ (Kᵢᴴ x)ᴴ R (Kᵢᴴ x)`.
* `kraus_mulVec_eq_zero_iff`: the kernel characterization above (item 1).
* `kraus_ker_mulVecLin_eq_iInf`: `ker (Λ R) = ⨅ᵢ ker Kᵢᴴ`, independent of the faithful `R`.
* `kraus_output_ker_eq`: for two faithful inputs `R, R'`, `ker (Λ R) = ker (Λ R')` (item 2).
* `kraus_output_support_eq`: the same for two faithful states `ρ, σ` in `DensityMatrix` form,
  `ker (Λ.toDM ρ).val = ker (Λ.toDM σ).val`.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Oseledets.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Output quadratic form of a Kraus channel.** For any input matrix `R` and vector `x`,
`xᴴ (Λ R) x = ∑ᵢ (Kᵢᴴ x)ᴴ R (Kᵢᴴ x)`. This is pure adjoint algebra (no positivity used). -/
theorem kraus_dotProduct_output (Λ : KrausChannel n) (R : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (Λ.toMat R *ᵥ x)
      = ∑ i, star ((Λ.K i)ᴴ *ᵥ x) ⬝ᵥ (R *ᵥ ((Λ.K i)ᴴ *ᵥ x)) := by
  unfold KrausChannel.toMat
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star x ⬝ᵥ (((Λ.K i)ᴴᴴ * R * (Λ.K i)ᴴ) *ᵥ x)
      = star ((Λ.K i)ᴴ *ᵥ x) ⬝ᵥ (R *ᵥ ((Λ.K i)ᴴ *ᵥ x)) := by
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  rwa [conjTranspose_conjTranspose] at h

/-- **Kernel characterization of the output on a faithful input (item 1).** For a *faithful*
(positive-definite) input `R`, the output `Λ R` annihilates `x` iff every Kraus operator adjoint
does: `Λ R *ᵥ x = 0 ↔ ∀ i, (Kᵢ)ᴴ *ᵥ x = 0`. The right-hand side does **not** depend on `R`, so the
output support `⨆ᵢ range Kᵢ` is the same for every faithful input. -/
theorem kraus_mulVec_eq_zero_iff (Λ : KrausChannel n) {R : Matrix n n ℂ} (hR : R.PosDef)
    (x : n → ℂ) :
    Λ.toMat R *ᵥ x = 0 ↔ ∀ i, (Λ.K i)ᴴ *ᵥ x = 0 := by
  constructor
  · intro hx i
    have hquad : ∑ j, star ((Λ.K j)ᴴ *ᵥ x) ⬝ᵥ (R *ᵥ ((Λ.K j)ᴴ *ᵥ x)) = 0 := by
      rw [← kraus_dotProduct_output, hx, dotProduct_zero]
    have hnn : ∀ j ∈ (Finset.univ : Finset Λ.ι),
        (0 : ℂ) ≤ star ((Λ.K j)ᴴ *ᵥ x) ⬝ᵥ (R *ᵥ ((Λ.K j)ᴴ *ᵥ x)) :=
      fun j _ => hR.posSemidef.dotProduct_mulVec_nonneg _
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hquad i (Finset.mem_univ i)
    by_contra hne
    exact absurd hz (ne_of_gt (hR.dotProduct_mulVec_pos hne))
  · intro hx
    unfold KrausChannel.toMat
    rw [sum_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx i, mulVec_zero, mulVec_zero]

/-- **The output kernel is `⨅ᵢ ker Kᵢᴴ`, independent of the faithful input.** For faithful `R`,
`ker (Λ R) = ⨅ᵢ ker Kᵢᴴ` as linear-map kernels via `Matrix.mulVecLin`. -/
theorem kraus_ker_mulVecLin_eq_iInf (Λ : KrausChannel n) {R : Matrix n n ℂ} (hR : R.PosDef) :
    LinearMap.ker (Λ.toMat R).mulVecLin = ⨅ i, LinearMap.ker ((Λ.K i)ᴴ).mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_iInf]
  exact kraus_mulVec_eq_zero_iff Λ hR x

/-- **De-hypothesization (item 2), matrix form.** Two faithful inputs `R, R'` give the same output
kernel `ker (Λ R) = ker (Λ R')` (both `= ⨅ᵢ ker Kᵢᴴ`). Hence the output support is the same, which
is exactly what makes the `(Λρ).PosDef`, `(Λσ).PosDef` hypotheses in the general Petz-equality
theorem removable for faithful inputs. -/
theorem kraus_output_ker_eq (Λ : KrausChannel n) {R R' : Matrix n n ℂ}
    (hR : R.PosDef) (hR' : R'.PosDef) :
    LinearMap.ker (Λ.toMat R).mulVecLin = LinearMap.ker (Λ.toMat R').mulVecLin := by
  rw [kraus_ker_mulVecLin_eq_iInf Λ hR, kraus_ker_mulVecLin_eq_iInf Λ hR']

/-- **De-hypothesization (item 2), density-matrix form.** For two faithful states `ρ, σ` the channel
outputs `Λ.toDM ρ`, `Λ.toDM σ` have the same support: `ker (Λ.toDM ρ).val = ker (Λ.toDM σ).val`. -/
theorem kraus_output_support_eq (Λ : KrausChannel n) {ρ σ : DensityMatrix n}
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) :
    LinearMap.ker (Λ.toDM ρ).val.mulVecLin = LinearMap.ker (Λ.toDM σ).val.mulVecLin := by
  change LinearMap.ker (Λ.toMat ρ.val).mulVecLin = LinearMap.ker (Λ.toMat σ.val).mulVecLin
  exact kraus_output_ker_eq Λ hρ hσ

/-- Non-vacuity: the de-hypothesization corollary fires on a concrete faithful instance — the
identity channel on a two-level system with the (positive-definite) maximally mixed state. -/
example :
    LinearMap.ker ((KrausChannel.id (Fin 2)).toDM DensityMatrix.maximallyMixed).val.mulVecLin
      = LinearMap.ker
          ((KrausChannel.id (Fin 2)).toDM DensityMatrix.maximallyMixed).val.mulVecLin :=
  kraus_output_support_eq _ DensityMatrix.maximallyMixed_posDef
    DensityMatrix.maximallyMixed_posDef

end Oseledets.OperatorEntropy
