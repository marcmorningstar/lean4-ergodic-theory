/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.ChoiLoewner
import Oseledets.OperatorEntropy.Lieb.ModularOperator
import Oseledets.OperatorEntropy.Lieb.PetzEqualityM3sc
import Oseledets.OperatorEntropy.Lieb.PetzEqualityM3

/-!
# Petz equality — sufficiency assembly (issue #28)

This module assembles the reusable readoff lemmas and the forward-progress steps of the
**sufficiency (`⟹`) direction** of the Petz equality theorem (issue #28): if the Umegaki relative
entropy is preserved by a Kraus channel `Λ` (`D(ρ‖σ) = D(Λρ‖Λσ)`), then `Λ` **intertwines the
modular `it`-flows** of the input and output pairs (`IntertwinesIt`),

`Λ†( (Λρ)^{it} (Λσ)^{-it} ) = ρ^{it} σ^{-it}`   for all `t`.

## What is proved here (all sorry-free)

* `relForm_conj`, `relEntropy_eq_modularForm` — **modular realization** of the relative entropy as a
  quadratic form of `-log Δ` on the cyclic vector `ξ = vec(ρ^{1/2})` (`Δ = ρ⁻¹ ⊗ σᵀ`).
* `resolvent_linearIndependent`, `resolvent_span_top`, `exists_resolvent_combo` — the **resolvent
  readoff** on a finite spectrum: `{(x + t)⁻¹ : t > 0}` is total, so a per-`t` intertwining of the
  resolvents upgrades to an intertwining of every function of the modular operator (hence of the
  unitary powers).
* `choi_neg_log_loewner_adj` — **the single-space DPI Loewner inequality for the channel adjoint**:
  `cfc(-log)(Λ† Y) ≤ Λ†(cfc(-log) Y)`.  This is Choi's operator-Jensen inequality specialised to the
  Heisenberg adjoint `Λ† Y = ∑ᵢ Kᵢ† Y Kᵢ`, living on the *same* space `ℂⁿ` as `ρ^{it} σ^{-it}`.
* `relEntropy_modularForm_re_eq_of_relEntropy_eq` — the entropy hypothesis transported to the
  equality of the two modular quadratic forms (the input for the gap-vanishing step, at the modular
  cyclic vectors `ξ_in`, `ξ_out`).
* `gap_mulVec_vecOne_zero_of_reconciliation` — the **equality-extraction reduction**: a Loewner pair
  `A ≤ B` whose `relForm` real parts are the two entropies has a positive-semidefinite gap that
  annihilates the cyclic vector `vec 1`.  This isolates the one remaining wall (below).

## The exact remaining goal

Fully closing `equality_imp_intertwinesIt` reduces to two research-level steps not discharged here:

1. **Reconciliation (build the Loewner pair).** Produce `A ≤ B` on `ℂⁿ ⊗ ℂⁿ` (equivalently the
   per-`t` resolvent contraction `Γ_t`) with `(relForm A).re = D(Λρ‖Λσ)`, `(relForm B).re = D(ρ‖σ)`.
   The correct object is the ρ-twisted Petz isometry `W(X) = (X ω_A^{-1/2} ⊗ 1) ω^{1/2}` with
   `W⋆ Δ_{τ,ω} W = Δ_{τ_A,ω_A}` (Carlen–Vershynina (2.3)); a ρ-independent compression fails.
2. **Rigidity.** From the gap annihilating the cyclic vector, deduce the `it`-intertwining — via the
   resolvent route (`contraction_adjoint_eq` + `exists_resolvent_combo`) or the strict-convexity
   route (needs the unproved operator strict convexity of `-log`).
-/

open Matrix Real Polynomial
open scoped ComplexOrder Kronecker MatrixOrder BigOperators

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Modular realization of the relative entropy (readoff, inlined) -/

/-- **Sandwich identity for `relForm`.** For a Hermitian `B`,
`relForm (B · A · B) = ⟪B · vec 1, A · (B · vec 1)⟫` where `⟪u, v⟫ = star u ⬝ᵥ v`. -/
lemma relForm_conj {A B : Matrix (n × n) (n × n) ℂ} (hB : Bᴴ = B) :
    relForm (B * A * B) = star (B *ᵥ vecOne n) ⬝ᵥ A *ᵥ (B *ᵥ vecOne n) := by
  have hstar : star (vecOne n) ᵥ* B = star (B *ᵥ vecOne n) := by
    rw [Matrix.star_mulVec, hB]
  rw [relForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hstar]

/-- **Modular realization (step 1).**  For faithful density matrices,
`S(ρ‖σ) = Re ⟪ξ, cfc(-log)(Δ) ξ⟫` with `Δ = relModularArg ρ σ = ρ⁻¹ ⊗ σᵀ` the relative modular
operator and `ξ = (ρ^{1/2} ⊗ 1) · vec 1 = vec(ρ^{1/2})` the cyclic vector. -/
lemma relEntropy_eq_modularForm (ρ σ : DensityMatrix n) (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) :
    relEntropy ρ σ =
      (star (CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) *ᵥ vecOne n) ⬝ᵥ
        cfc (fun x => -Real.log x) (relModularArg ρ.val σ.val) *ᵥ
        (CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) *ᵥ vecOne n)).re := by
  rw [relEntropy_eq_relForm ρ σ hρ hσ]
  congr 1
  have hRin : (ρ.val ⊗ₖ (1 : Matrix n n ℂ)).PosDef := hρ.kronecker Matrix.PosDef.one
  have hB : (CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2))ᴴ
      = CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) :=
    ((IsStrictlyPositive.rpow _ (1 / 2) hRin.isStrictlyPositive).posDef).1
  have hop : opPersp (fun x => -Real.log x) ((1 : Matrix n n ℂ) ⊗ₖ σ.valᵀ) (ρ.val ⊗ₖ 1)
      = CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2)
        * cfc (fun x => -Real.log x) (relModularArg ρ.val σ.val)
        * CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) := by
    rw [opPersp, perspArg_kron hρ, relModularArg]
  rw [hop, relForm_conj hB]

/-! ## The single-space DPI Loewner inequality for the channel adjoint

The resolvent readoff lemmas (`resolvent_linearIndependent`, `resolvent_span_top`,
`exists_resolvent_combo`) live in `Oseledets.OperatorEntropy.Lieb.PetzSufficiencyB`; they are not
re-declared here (they are pulled in transitively where needed) to avoid a duplicate-declaration
clash in the final assembly. -/

/-- **Choi's operator-Jensen inequality for the channel adjoint.** For a Kraus channel `Λ` and a
self-adjoint `Y` with spectrum in `(0, ∞)`, `cfc(-log)(Λ† Y) ≤ Λ†(cfc(-log) Y)`, where
`Λ† Y = ∑ᵢ Kᵢ† Y Kᵢ` is the Heisenberg (unital) adjoint.  This is `choi_neg_log_loewner`
specialised to the Kraus operators; it lives on the single space `ℂⁿ` — the same space as the
modular flow `ρ^{it} σ^{-it}`. -/
theorem choi_neg_log_loewner_adj (Λ : KrausChannel n) (Y : Matrix n n ℂ)
    (hYsa : IsSelfAdjoint Y) (hspec : spectrum ℝ Y ⊆ Set.Ioi 0) :
    cfc (fun x => -Real.log x) (Λ.adj Y) ≤ Λ.adj (cfc (fun x => -Real.log x) Y) := by
  have h := choi_neg_log_loewner Λ.K Y Λ.htp hYsa hspec
  simpa only [KrausChannel.adj] using h

/-! ## Transporting the entropy equality to the modular quadratic forms -/

/-- **Entropy-equality transport (modular form).** The hypothesis `D(ρ‖σ) = D(Λρ‖Λσ)`, read through
`relEntropy_eq_modularForm`, is exactly the equality of the two modular quadratic forms
`Re ⟪ξ_in, (-log Δ_in) ξ_in⟫ = Re ⟪ξ_out, (-log Δ_out) ξ_out⟫` at the modular cyclic vectors
`ξ_in = vec(ρ^{1/2})`, `ξ_out = vec((Λρ)^{1/2})`.  This is the scalar equality feeding the
gap-vanishing step at the modular cyclic vector (as opposed to `vec 1`). -/
lemma relEntropy_modularForm_re_eq_of_relEntropy_eq (ρ σ : DensityMatrix n) (Λ : KrausChannel n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    (star (CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) *ᵥ vecOne n) ⬝ᵥ
        cfc (fun x => -Real.log x) (relModularArg ρ.val σ.val) *ᵥ
        (CFC.rpow (ρ.val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) *ᵥ vecOne n)).re
      = (star (CFC.rpow ((Λ.toDM ρ).val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) *ᵥ vecOne n) ⬝ᵥ
        cfc (fun x => -Real.log x) (relModularArg (Λ.toDM ρ).val (Λ.toDM σ).val) *ᵥ
        (CFC.rpow ((Λ.toDM ρ).val ⊗ₖ (1 : Matrix n n ℂ)) (1 / 2) *ᵥ vecOne n)).re := by
  rw [← relEntropy_eq_modularForm ρ σ hρ hσ,
    ← relEntropy_eq_modularForm (Λ.toDM ρ) (Λ.toDM σ) hΛρ hΛσ]
  exact hEq

/-! ## The equality-extraction reduction -/

/-- **Equality-extraction reduction.** Given the reconciliation Loewner pair `A ≤ B` on
`ℂⁿ ⊗ ℂⁿ` whose two `relForm` real parts are identified with the output and input relative
entropies, the entropy-preservation hypothesis forces the positive-semidefinite gap `B − A` to
annihilate the cyclic vector `vec 1`.

This is the clean interface to the *one remaining wall*: supplying the concrete Loewner pair
`A ≤ B` (the ρ-twisted Petz reconciliation `W⋆ Δ_{τ,ω} W = Δ_out`), after which the gap-vanishing
is delivered here, and the subsequent rigidity (gap-vanishing ⟹ `it`-intertwining) via
`contraction_adjoint_eq` / `exists_resolvent_combo` closes `equality_imp_intertwinesIt`. -/
lemma gap_mulVec_vecOne_zero_of_reconciliation (ρ σ : DensityMatrix n) (Λ : KrausChannel n)
    {A B : Matrix (n × n) (n × n) ℂ} (hle : A ≤ B)
    (hA : (relForm A).re = relEntropy (Λ.toDM ρ) (Λ.toDM σ))
    (hB : (relForm B).re = relEntropy ρ σ)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    (B - A) *ᵥ vecOne n = 0 := by
  refine gap_mulVec_vecOne_zero_of_relForm_re_eq hle ?_
  rw [hA, hB, hEq]

end Oseledets.OperatorEntropy.Lieb

end
