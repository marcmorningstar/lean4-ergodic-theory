/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.OperatorEntropy.StinespringReduction
import Oseledets.OperatorEntropy.Lieb.DataProcessingGeneral
import Oseledets.OperatorEntropy.PetzRecovery

/-!
# Issue #22 — the CPTP data-processing consumers (unconditional)

With the partial-trace data-processing wall now *discharged*
(`Oseledets.OperatorEntropy.Lieb.relEntropyMonotone_partialTrace`), the Stinespring reduction of
`StinespringReduction.lean` upgrades from *conditional* (hypothesis `hwall`) to **unconditional**.
This module wires the three named deliverables of issue #22:

* `monotonicity_relEntropy_under_CPTP` — **the data-processing inequality (DPI) for a general
  mixed-ancilla Stinespring channel**, UNCONDITIONAL.  Adjoin a faithful ancilla `α`, conjugate by
  a unitary dilation `U`, then trace out the ancilla: `D(Λ ρ ‖ Λ σ) ≤ D(ρ ‖ σ)`.  This is
  `stinespring_relEntropy_monotone` applied to the now-proved `relEntropyMonotone_partialTrace`.
* `no_section_of_strict_relEntropy_drop` / `no_stinespring_section_of_strict_relEntropy_drop` —
  **the no-recovery obstruction**: a STRICT relative-entropy drop under a coarse-graining forbids
  any faithful-monotone (in particular, any Stinespring) recovery section.  The Stinespring
  corollary discharges the monotonicity hypothesis via `monotonicity_relEntropy_under_CPTP`, hence
  is UNCONDITIONAL.
* `petz_recovery_implies_equality` — **the `⟸` direction of Petz's equality theorem**: if a
  faithful-monotone recovery map `R` inverts a faithful-monotone channel `Λ` on `ρ, σ`, then the
  DPI is TIGHT, `D(Λ ρ ‖ Λ σ) = D(ρ ‖ σ)`.  Two applications of monotonicity + `le_antisymm`.

The converse `⟹` direction (equality in DPI `⟹` Petz recoverability) is now discharged in-repo
without the Araki modular operator: `partialTrace_equality_imp_intertwinesIt`
(`Lieb.PetzEqualitySufficiency`, partial-trace channel) and `petz_equality_recovery_general`
(`Lieb.PetzEqualityGeneral`, general Kraus channel), both axiom-audited.

All index types are `Type` (universe `0`), matching the monomorphic wall `Prop`
`RelEntropyMonotoneUnderPartialTrace`: finite-dimensional quantum information lives in universe `0`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy

/-! ## Deliverable 1 — the DPI for a mixed-ancilla Stinespring channel (unconditional) -/

/-- **Data-processing inequality for a general (mixed-ancilla) Stinespring channel.**
UNCONDITIONAL: adjoining a faithful ancilla `α`, conjugating by a unitary dilation `U`, then
tracing out the ancilla never increases the Umegaki relative entropy of two faithful states,
`D(Λ ρ ‖ Λ σ) ≤ D(ρ ‖ σ)`.  This is `stinespring_relEntropy_monotone` fed the now-proved
partial-trace wall `relEntropyMonotone_partialTrace`. -/
theorem monotonicity_relEntropy_under_CPTP {n e : Type}
    [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]
    (α : DensityMatrix e) (U : Matrix.unitaryGroup (n × e) ℂ) (hα : α.val.PosDef)
    (ρ σ : DensityMatrix n) (hσ : σ.val.PosDef) :
    relEntropy (((ρ.kron α).conj U).partialTraceRight) (((σ.kron α).conj U).partialTraceRight)
      ≤ relEntropy ρ σ :=
  stinespring_relEntropy_monotone Lieb.relEntropyMonotone_partialTrace α U hα ρ σ hσ

/-! ## Deliverable 3 — the no-recovery obstruction (unconditional for Stinespring maps) -/

/-- **No faithful-monotone section under a strict relative-entropy drop.**
If a recovery map `R : m → n` satisfies the (faithful-`σ`) data-processing inequality and is a
perfect section of a coarse-graining `Λ : n → m` on the states `ρ, σ` (`R (Λ ρ) = ρ`,
`R (Λ σ) = σ`, with `Λ σ` faithful), then a STRICT drop `D(Λ ρ ‖ Λ σ) < D(ρ ‖ σ)` is impossible.

This is the faithful-restricted analogue of `no_monotone_section_of_strict_drop`; the recovery
monotonicity is supplied only for a faithful second argument, matching what
`monotonicity_relEntropy_under_CPTP` delivers. -/
theorem no_section_of_strict_relEntropy_drop {n m : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (Λ : DensityMatrix n → DensityMatrix m) (R : DensityMatrix m → DensityMatrix n)
    (hRmono : ∀ x y : DensityMatrix m, y.val.PosDef → relEntropy (R x) (R y) ≤ relEntropy x y)
    (ρ σ : DensityMatrix n) (hΛσ : (Λ σ).val.PosDef)
    (hsecρ : R (Λ ρ) = ρ) (hsecσ : R (Λ σ) = σ)
    (hstrict : relEntropy (Λ ρ) (Λ σ) < relEntropy ρ σ) : False := by
  have h := hRmono (Λ ρ) (Λ σ) hΛσ
  rw [hsecρ, hsecσ] at h
  linarith

/-- **No Stinespring recovery section under a strict relative-entropy drop** (UNCONDITIONAL).
Specialises `no_section_of_strict_relEntropy_drop` to a Stinespring recovery channel
`R x = ((x ⊗ α)ᵁ)_A`, whose faithful data-processing monotonicity is
`monotonicity_relEntropy_under_CPTP`.  Hence a strict relative-entropy drop under a coarse-graining
`Λ` rules out *any* Stinespring CP map inverting `Λ` on `ρ, σ`.  The Stinespring recovery is an
endomorphism of the input space, so the coarse-graining `Λ` is taken here as an endomorphism of the
same space `n` (e.g. a pinching / dephasing channel). -/
theorem no_stinespring_section_of_strict_relEntropy_drop {n e : Type}
    [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]
    (Λ : DensityMatrix n → DensityMatrix n)
    (α : DensityMatrix e) (U : Matrix.unitaryGroup (n × e) ℂ) (hα : α.val.PosDef)
    (ρ σ : DensityMatrix n) (hΛσ : (Λ σ).val.PosDef)
    (hsecρ : (((Λ ρ).kron α).conj U).partialTraceRight = ρ)
    (hsecσ : (((Λ σ).kron α).conj U).partialTraceRight = σ)
    (hstrict : relEntropy (Λ ρ) (Λ σ) < relEntropy ρ σ) : False :=
  no_section_of_strict_relEntropy_drop Λ (fun x => ((x.kron α).conj U).partialTraceRight)
    (fun x y hy => monotonicity_relEntropy_under_CPTP α U hα x y hy) ρ σ hΛσ hsecρ hsecσ hstrict

/-! ## Deliverable 2 — recovery `⟹` equality in DPI (the `⟸` of Petz's theorem) -/

/-- **Recovery implies equality in the data-processing inequality** (the `⟸` direction of Petz's
theorem).  If a channel `Λ` and a recovery map `R` are both faithful-monotone (satisfy the DPI for
a faithful second argument) and `R` inverts `Λ` on `ρ, σ` (`R (Λ ρ) = ρ`, `R (Λ σ) = σ`), then the
DPI is TIGHT: `D(Λ ρ ‖ Λ σ) = D(ρ ‖ σ)`.  Monotonicity of `Λ` gives `≤`; monotonicity of `R`
composed with the section identities gives `≥`; `le_antisymm` closes it.

The converse `⟹` direction (equality in the DPI `⟹` a Petz recovery map exists) is established
in-repo — see `partialTrace_equality_imp_intertwinesIt` (`Lieb.PetzEqualitySufficiency`) and
`petz_equality_recovery_general` (`Lieb.PetzEqualityGeneral`), both axiom-audited. -/
theorem petz_recovery_implies_equality {n m : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (Λ : DensityMatrix n → DensityMatrix m) (R : DensityMatrix m → DensityMatrix n)
    (hΛmono : ∀ x y : DensityMatrix n, y.val.PosDef → relEntropy (Λ x) (Λ y) ≤ relEntropy x y)
    (hRmono : ∀ x y : DensityMatrix m, y.val.PosDef → relEntropy (R x) (R y) ≤ relEntropy x y)
    (ρ σ : DensityMatrix n) (hσ : σ.val.PosDef) (hΛσ : (Λ σ).val.PosDef)
    (hsecρ : R (Λ ρ) = ρ) (hsecσ : R (Λ σ) = σ) :
    relEntropy (Λ ρ) (Λ σ) = relEntropy ρ σ := by
  refine le_antisymm (hΛmono ρ σ hσ) ?_
  have h := hRmono (Λ ρ) (Λ σ) hΛσ
  rw [hsecρ, hsecσ] at h
  exact h

end Oseledets.OperatorEntropy
