/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.ChoiLoewner
import Oseledets.OperatorEntropy.Lieb.ModularOperator
import Oseledets.OperatorEntropy.Lieb.PetzEqualityM3sc
import Oseledets.OperatorEntropy.PartialTrace

/-!
# Petz equality — the ρ-twisted reconciliation isometry (issue #28, STEP 1)

This module formalises the mathematical heart of the *reconciliation* step of the sufficiency
(`⟹`) direction of the Petz-equality theorem (issue #28): the **Petz / GNS-twisted isometry** `W`
and the three Carlen–Vershynina identities it satisfies (the specialisation of Carlen–Vershynina,
*Recovery map stability for the DPI*, eq. (2.3), `U⋆ Δ_{σ,ρ} U = Δ_{σ_N,ρ_N}`, to the tracial
conditional expectation = partial trace).

Working directly on **operators** (Hilbert–Schmidt maps of matrices), with a bipartite system
`ℂ^A ⊗ ℂ^B`, put `ω_A := Tr_B ω` and consider

* `petzW ω X = (X · ω_A^{-1/2} ⊗ 1_B) · ω^{1/2}`      — the ρ-twisted reconciliation isometry,
* `petzWadj ω Z = Tr_B(Z · ω^{1/2}) · ω_A^{-1/2}`      — its Hilbert–Schmidt adjoint,
* `modularMap τ ω Z = τ · Z · ω^{-1}`                  — the relative modular map `Δ_{τ,ω}`.

## Main results (all sorry-free)

* `partialTraceRight_kron_one_mul`, `partialTraceRight_mul_kron_one` — the two **partial-trace
  pull-out identities** `Tr_B((Y ⊗ 1)·M) = Y · Tr_B M` and `Tr_B(M·(Y ⊗ 1)) = Tr_B M · Y`, the
  engine of the reconciliation.
* `petzW_isometry` — identity **(i)** `W⋆ W = 1`: `petzWadj ω (petzW ω X) = X`.
* `petzW_cyclic` — identity **(ii)** `W (ω_A^{1/2}) = ω^{1/2}`: the isometry carries the *output*
  cyclic vector to the *input* one.
* `petzW_modular_compression` — identity **(iii)**, the **reconciliation** proper:
  `W⋆ Δ_{τ,ω} W (X) = τ_A · X · ω_A^{-1} = Δ_{τ_A,ω_A}(X)` (Carlen–Vershynina (2.3)).

These are the exact objects that, once transported to the *vectorised* Hilbert–Schmidt picture
(the Kronecker matrices `relModularArg` of `ModularOperator.lean`), feed the rectangular
operator-Jensen inequality `rect_isometry_neg_log_loewner` to produce the reconciliation Loewner
pair `A ≤ B` consumed by the gap-vanishing keystone `gap_mulVec_vecOne_zero_of_relForm_re_eq`
(`PetzEqualityM3sc`).

## What is *not* done here (the two remaining walls of issue #28)

1. **Vectorisation bridge.** Re-expressing `petzW` as a *rectangular matrix* on the vectorised HS
   space `ℂ^{A×A} → ℂ^{(A×B)×(A×B)}` (an ampliation composed with the two right-twists) so that
   `Wᴴ · relModularArg ω τ · W = relModularArg ω_A τ_A` reads off from the operator identity (iii)
   here.  The operator-level content is complete; only the vec/`⊗ₖ` reshuffle is outstanding.
2. **Rigidity tail (STEP 5–6).** From the gap annihilating the cyclic vector to the
   `it`-intertwining `IntertwinesIt`, via the resolvent readoff `exists_resolvent_combo`
   or the unproved operator strict convexity of `-log`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

open Oseledets.OperatorEntropy

/-! ## Functional-calculus power algebra (general index type) -/

section RpowAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `R^{1/2} · R^{1/2} = R` for a positive-definite matrix. -/
private lemma rpow_half_sq {R : Matrix ι ι ℂ} (hR : R.PosDef) :
    R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) = R := by
  rw [← CFC.rpow_add hR.isUnit, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num,
    CFC.rpow_one R hR.isStrictlyPositive.nonneg]

/-- `R^{-1/2} · R^{-1/2} = R^{-1}` for a positive-definite matrix. -/
private lemma rpow_negHalf_sq {R : Matrix ι ι ℂ} (hR : R.PosDef) :
    R ^ (-(1 / 2) : ℝ) * R ^ (-(1 / 2) : ℝ) = R ^ (-1 : ℝ) := by
  rw [← CFC.rpow_add hR.isUnit]; norm_num

/-- The conjugation cancellation `R^{-1/2} · R · R^{-1/2} = 1`. -/
private lemma rpow_negHalf_conj {R : Matrix ι ι ℂ} (hR : R.PosDef) :
    R ^ (-(1 / 2) : ℝ) * R * R ^ (-(1 / 2) : ℝ) = 1 := by
  have hsp := hR.isStrictlyPositive
  calc R ^ (-(1 / 2) : ℝ) * R * R ^ (-(1 / 2) : ℝ)
      = R ^ (-(1 / 2) : ℝ) * (R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) * R ^ (-(1 / 2) : ℝ) := by
        rw [rpow_half_sq hR]
    _ = (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) * (R ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)) := by
        noncomm_ring
    _ = 1 * 1 := by
        rw [CFC.rpow_neg_mul_rpow (1 / 2) hsp, CFC.rpow_mul_rpow_neg (1 / 2) hsp]
    _ = 1 := mul_one 1

/-- The modular collapse `R^{1/2} · R^{-1} · R^{1/2} = 1`. -/
private lemma rpow_half_negOne_half {R : Matrix ι ι ℂ} (hR : R.PosDef) :
    R ^ (1 / 2 : ℝ) * R ^ (-1 : ℝ) * R ^ (1 / 2 : ℝ) = 1 := by
  have hsp := hR.isStrictlyPositive
  calc R ^ (1 / 2 : ℝ) * R ^ (-1 : ℝ) * R ^ (1 / 2 : ℝ)
      = R ^ (1 / 2 : ℝ) * (R ^ (-(1 / 2) : ℝ) * R ^ (-(1 / 2) : ℝ)) * R ^ (1 / 2 : ℝ) := by
        rw [rpow_negHalf_sq hR]
    _ = (R ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)) * (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) := by
        noncomm_ring
    _ = 1 * 1 := by
        rw [CFC.rpow_mul_rpow_neg (1 / 2) hsp, CFC.rpow_neg_mul_rpow (1 / 2) hsp]
    _ = 1 := mul_one 1

end RpowAlgebra

/-! ## Partial-trace pull-out identities -/

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

omit [DecidableEq nA] in
/-- **Left pull-out.** An operator of the form `Y ⊗ 1_B` on the left factors out of the right
partial trace: `Tr_B((Y ⊗ 1) · M) = Y · Tr_B M`. -/
theorem partialTraceRight_kron_one_mul (Y : Matrix nA nA ℂ)
    (M : Matrix (nA × nB) (nA × nB) ℂ) :
    partialTraceRight ((Y ⊗ₖ (1 : Matrix nB nB ℂ)) * M) = Y * partialTraceRight M := by
  ext i i'
  simp only [partialTraceRight_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq nA] in
/-- **Right pull-out.** An operator of the form `Y ⊗ 1_B` on the right factors out of the right
partial trace: `Tr_B(M · (Y ⊗ 1)) = Tr_B M · Y`. -/
theorem partialTraceRight_mul_kron_one (M : Matrix (nA × nB) (nA × nB) ℂ)
    (Y : Matrix nA nA ℂ) :
    partialTraceRight (M * (Y ⊗ₖ (1 : Matrix nB nB ℂ))) = partialTraceRight M * Y := by
  ext i i'
  simp only [partialTraceRight_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

/-! ## The ρ-twisted Petz reconciliation isometry (operator form) -/

/-- The **ρ-twisted Petz reconciliation isometry** (operator form):
`W(X) = (X · ω_A^{-1/2} ⊗ 1_B) · ω^{1/2}`, where `ω_A = Tr_B ω`.  It maps the input HS space
`Matrix nA nA ℂ` into the dilated HS space `Matrix (nA × nB) (nA × nB) ℂ`. -/
def petzW (ω : Matrix (nA × nB) (nA × nB) ℂ) (X : Matrix nA nA ℂ) :
    Matrix (nA × nB) (nA × nB) ℂ :=
  ((X * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)) ⊗ₖ (1 : Matrix nB nB ℂ)) * ω ^ (1 / 2 : ℝ)

/-- The **Hilbert–Schmidt adjoint** of `petzW`: `W⋆(Z) = Tr_B(Z · ω^{1/2}) · ω_A^{-1/2}`.  The
`ω_A^{-1/2}` sits on the *right* — the placement that makes `W⋆ W = 1`. -/
def petzWadj (ω : Matrix (nA × nB) (nA × nB) ℂ) (Z : Matrix (nA × nB) (nA × nB) ℂ) :
    Matrix nA nA ℂ :=
  partialTraceRight (Z * ω ^ (1 / 2 : ℝ)) * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)

/-- The **relative modular map** `Δ_{τ,ω}(Z) = τ · Z · ω^{-1}` on the dilated HS space. -/
def modularMap (τ ω : Matrix (nA × nB) (nA × nB) ℂ) (Z : Matrix (nA × nB) (nA × nB) ℂ) :
    Matrix (nA × nB) (nA × nB) ℂ :=
  τ * Z * ω ^ (-1 : ℝ)

/-- **Reconciliation identity (i): `W⋆ W = 1`.**  The ρ-twisted isometry is a genuine isometry of
the input HS space: `petzWadj ω (petzW ω X) = X`. -/
theorem petzW_isometry (ω : Matrix (nA × nB) (nA × nB) ℂ) (hω : ω.PosDef)
    (hωA : (partialTraceRight ω).PosDef) (X : Matrix nA nA ℂ) :
    petzWadj ω (petzW ω X) = X := by
  unfold petzWadj petzW
  rw [mul_assoc, rpow_half_sq hω, partialTraceRight_kron_one_mul,
    show X * (partialTraceRight ω) ^ (-(1 / 2) : ℝ) * partialTraceRight ω
        * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)
      = X * ((partialTraceRight ω) ^ (-(1 / 2) : ℝ) * partialTraceRight ω
        * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)) from by noncomm_ring,
    rpow_negHalf_conj hωA, mul_one]

/-- **Reconciliation identity (ii): `W(ω_A^{1/2}) = ω^{1/2}`.**  The isometry carries the *output*
cyclic vector `ω_A^{1/2}` to the *input* cyclic vector `ω^{1/2}`. -/
theorem petzW_cyclic (ω : Matrix (nA × nB) (nA × nB) ℂ)
    (hωA : (partialTraceRight ω).PosDef) :
    petzW ω ((partialTraceRight ω) ^ (1 / 2 : ℝ)) = ω ^ (1 / 2 : ℝ) := by
  unfold petzW
  rw [CFC.rpow_mul_rpow_neg (1 / 2) hωA.isStrictlyPositive, Matrix.one_kronecker_one,
    Matrix.one_mul]

/-- **Reconciliation identity (iii): `W⋆ Δ_{τ,ω} W = Δ_{τ_A,ω_A}`** (Carlen–Vershynina (2.3)).  The
ρ-twisted compression of the *dilated* relative modular map `Δ_{τ,ω}` is the *output* relative
modular map `Δ_{τ_A,ω_A}(X) = τ_A · X · ω_A^{-1}`, with `τ_A = Tr_B τ`, `ω_A = Tr_B ω`.  This is the
reconciliation that turns the rectangular DPI Loewner inequality into the output-space one. -/
theorem petzW_modular_compression (τ ω : Matrix (nA × nB) (nA × nB) ℂ) (hω : ω.PosDef)
    (hωA : (partialTraceRight ω).PosDef) (X : Matrix nA nA ℂ) :
    petzWadj ω (modularMap τ ω (petzW ω X))
      = partialTraceRight τ * X * (partialTraceRight ω) ^ (-1 : ℝ) := by
  unfold petzWadj modularMap petzW
  rw [show τ * (((X * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)) ⊗ₖ (1 : Matrix nB nB ℂ))
          * ω ^ (1 / 2 : ℝ)) * ω ^ (-1 : ℝ) * ω ^ (1 / 2 : ℝ)
        = τ * ((X * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)) ⊗ₖ (1 : Matrix nB nB ℂ))
          * (ω ^ (1 / 2 : ℝ) * ω ^ (-1 : ℝ) * ω ^ (1 / 2 : ℝ)) from by noncomm_ring,
    rpow_half_negOne_half hω, mul_one, partialTraceRight_mul_kron_one,
    show partialTraceRight τ * (X * (partialTraceRight ω) ^ (-(1 / 2) : ℝ))
          * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)
        = partialTraceRight τ * X * ((partialTraceRight ω) ^ (-(1 / 2) : ℝ)
          * (partialTraceRight ω) ^ (-(1 / 2) : ℝ)) from by noncomm_ring,
    rpow_negHalf_sq hωA]

end Oseledets.OperatorEntropy.Lieb

end
