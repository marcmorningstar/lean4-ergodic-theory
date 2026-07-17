/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.QuantumSeal
import ErgodicTheory.OperatorEntropy.RelEntropyAdditivity
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessingCPTP
import ErgodicTheory.OperatorEntropy.PetzRecovery

/-!
# Issue #70 (tier Q0) — the Kronecker lift of the dephasing seal

The single-qubit **dephasing** (pinching) seal of `QuantumSeal.lean` states that no Stinespring
recovery channel undoes the coherence that dephasing erases (Petz recovery ⟺ saturation of the
data-processing inequality; Petz 1986, 2003; Ohya–Petz, *Quantum Entropy and Its Use*, Springer).
This module lifts that seal from the single qubit `M₂` to the *partial-dephasing* channel on
`M₂ ⊗ M_blk` for an **arbitrary block algebra** `blk` — dephase the first qubit, leave the block
untouched — and shows the strict relative-entropy drop, hence the no-recovery obstruction, survives
the tensoring **uniformly in the block**.  In particular it holds at every level `M_{2ⁿ}` of a
growing tower (take `blk` to be that level), which is the intended tier-Q0 payload.

## Main definitions

* `dephaseKronId blk` — the partial-dephasing channel `Δ ⊗ id_blk` on `M₂ ⊗ M_blk`, with Kraus
  operators `Kᵢ ⊗ 1` for the qubit-dephasing Kraus operators `Kᵢ`.

## Main results

* `dephaseKronId_toDM_kron` — the channel factorizes on product states,
  `(Δ ⊗ id)(x ⊗ β) = (Δ x) ⊗ β`.
* `relEntropy_drop_rhoR_diagState` — the qubit-level strict data-processing drop that
  `quantum_seal_dephase_faithful` feeds to the Petz engine, factored out as a standalone lemma
  (reference pair `(ρ_r, diagState s)`, whose dephasing images `I/2 ≠ diagState s` are distinct).
* `relEntropy_strict_drop_dephasing_kron` — that strict drop, tensored with a faithful block `β`,
  survives (via ancilla invariance of the relative entropy).
* `quantum_seal_dephase_kron_faithful` — the headline: no Stinespring recovery of the partially
  dephased faithful state `ρ_r ⊗ β`, **uniformly in the block** `β`.  A pure-input variant
  `quantum_seal_dephase_kron` mirrors `quantum_seal_dephase`.

## Scope (honesty)

This is a **channel-level (single-step) seal per stage**, not a flow seal — exactly the caveat of
`QuantumSeal.lean`.  "Uniform in `n`" means the system-side block `blk` is arbitrary (in particular
every tower level `M_{2ⁿ}`); the recovery map is quantified over **all** faithful-ancilla
Stinespring dilations on the *enlarged* system `M₂ ⊗ M_blk`.  The reference pair
`(ρ_r, diagState s)` has *distinct* dephasing images, so the no-common-recovery statement carries
genuine content and is not the degenerate `Λρ = Λσ` collapse (see the QA note in
`QuantumSeal.lean`).
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## A sum–Kronecker distributivity helper -/

/-- Pulling a finite sum out of the left factor of a Kronecker product:
`∑ i, (Mᵢ ⊗ N) = (∑ i, Mᵢ) ⊗ N`. -/
lemma sum_kronecker_right {ι' κ μ : Type*} [Fintype ι']
    (M : ι' → Matrix κ κ ℂ) (N : Matrix μ μ ℂ) :
    (∑ i, M i ⊗ₖ N) = (∑ i, M i) ⊗ₖ N :=
  (map_sum ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)).flip N) M Finset.univ).symm

/-! ## The partial-dephasing channel `Δ ⊗ id` -/

/-- The **partial-dephasing (pinching) channel** `Δ ⊗ id_blk` on `M₂ ⊗ M_blk`: it dephases the
first qubit (killing its coherences) and leaves the block algebra `M_blk` untouched.  Its Kraus
operators are `Kᵢ ⊗ 1` for the qubit-dephasing Kraus operators `Kᵢ` (the diagonal projections). -/
def dephaseKronId (blk : Type*) [Fintype blk] [DecidableEq blk] :
    KrausChannel (Fin 2 × blk) where
  ι := Fin 2
  K := fun i => dephase.K i ⊗ₖ (1 : Matrix blk blk ℂ)
  htp := by
    have hstep : ∀ i : Fin 2,
        (dephase.K i ⊗ₖ (1 : Matrix blk blk ℂ))ᴴ * (dephase.K i ⊗ₖ (1 : Matrix blk blk ℂ))
          = ((dephase.K i)ᴴ * dephase.K i) ⊗ₖ (1 : Matrix blk blk ℂ) := by
      intro i
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul]
    have hsum : (∑ i : Fin 2, (dephase.K i)ᴴ * dephase.K i) = 1 := dephase.htp
    simp_rw [hstep]
    rw [sum_kronecker_right, hsum, Matrix.one_kronecker_one]

/-! ## The channel factorizes on product states -/

/-- **Partial dephasing factorizes on product states:** `(Δ ⊗ id)(x ⊗ β) = (Δ x) ⊗ β`.  The Kraus
sum `∑ᵢ (Kᵢ ⊗ 1)(x ⊗ β)(Kᵢ ⊗ 1)ᴴ` splits over the tensor factors, leaving the block `β` inert. -/
theorem dephaseKronId_toDM_kron {blk : Type*} [Fintype blk] [DecidableEq blk]
    (x : DensityMatrix (Fin 2)) (β : DensityMatrix blk) :
    (dephaseKronId blk).toDM (x.kron β) = (dephase.toDM x).kron β := by
  apply DensityMatrix.ext
  change (∑ i : Fin 2, (dephase.K i ⊗ₖ (1 : Matrix blk blk ℂ)) * (x.val ⊗ₖ β.val)
      * (dephase.K i ⊗ₖ (1 : Matrix blk blk ℂ))ᴴ)
    = (∑ i : Fin 2, dephase.K i * x.val * (dephase.K i)ᴴ) ⊗ₖ β.val
  have hstep : ∀ i : Fin 2,
      (dephase.K i ⊗ₖ (1 : Matrix blk blk ℂ)) * (x.val ⊗ₖ β.val)
          * (dephase.K i ⊗ₖ (1 : Matrix blk blk ℂ))ᴴ
        = (dephase.K i * x.val * (dephase.K i)ᴴ) ⊗ₖ β.val := by
    intro i
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  simp_rw [hstep]
  rw [sum_kronecker_right]

/-! ## The qubit-level strict drops (reference pair `(·, diagState s)`) -/

/-- **Strict data-processing drop for the faithful `ρ_r` against the fixed point `diagState s`.**
This is the qubit-level strict drop that `quantum_seal_dephase_faithful` feeds to the Petz engine,
factored out as a standalone lemma.  `ρ_r` and its dephasing image `I/2` share the
computational-basis diagonal `(½, ½)`, so the cross terms against `diagState s` coincide and cancel
in the difference; the drop is `log 2 − h₂((1+r)/2) > 0`.  The
dephasing images are distinct (`Δρ_r = I/2 ≠ diagState s = Δ(diagState s)`), so the pair is
non-degenerate. -/
theorem relEntropy_drop_rhoR_diagState (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    relEntropy (dephase.toDM (rhoR r hr0 hr1)) (dephase.toDM (diagState s hs0 hs1))
      < relEntropy (rhoR r hr0 hr1) (diagState s hs0 hs1) := by
  rw [dephase_rhoR, dephase_diagState, relEntropy_diagState, relEntropy_diagState,
    rhoR_val_re, rhoR_val_re, maximallyMixed_val_re, maximallyMixed_val_re,
    vonNeumannEntropy_maximallyMixed, Fintype.card_fin]
  have hlt := vonNeumannEntropy_rhoR_lt r hr0 hr1
  have h2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
  rw [h2]
  linarith

/-- **Strict data-processing drop for the pure `|+⟩⟨+|` against the fixed point `diagState s`.**
The qubit-level pure-input strict drop feeding `quantum_seal_dephase`.  The drop is
`S(I/2) − S(|+⟩⟨+|) = log 2 > 0`. -/
theorem relEntropy_drop_plusState_diagState (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    relEntropy (dephase.toDM plusState) (dephase.toDM (diagState s hs0 hs1))
      < relEntropy plusState (diagState s hs0 hs1) := by
  rw [dephase_plusState, dephase_diagState, relEntropy_diagState, relEntropy_diagState,
    plusState_val_re, plusState_val_re, maximallyMixed_val_re, maximallyMixed_val_re,
    vonNeumannEntropy_plusState, vonNeumannEntropy_maximallyMixed, Fintype.card_fin]
  have h2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
  rw [h2]
  linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-! ## The strict drop survives the block tensoring -/

/-- **The strict drop survives `⊗ β`** (faithful family).  Partial dephasing of `ρ_r ⊗ β` against
`diagState s ⊗ β` strictly lowers the relative entropy: the block `β` is a common faithful ancilla,
so `relEntropy` is unchanged by it (ancilla invariance), and the qubit-level strict drop
`relEntropy_drop_rhoR_diagState` carries through. -/
theorem relEntropy_strict_drop_dephasing_kron {blk : Type*} [Fintype blk] [DecidableEq blk]
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (β : DensityMatrix blk) (hβ : β.val.PosDef) :
    relEntropy ((dephaseKronId blk).toDM ((rhoR r hr0 hr1).kron β))
        ((dephaseKronId blk).toDM ((diagState s hs0 hs1).kron β))
      < relEntropy ((rhoR r hr0 hr1).kron β) ((diagState s hs0 hs1).kron β) := by
  have hσ1 : (dephase.toDM (diagState s hs0 hs1)).val.PosDef := by
    rw [dephase_diagState]; exact diagState_posDef s hs0 hs1
  rw [dephaseKronId_toDM_kron, dephaseKronId_toDM_kron,
    relEntropy_ancilla_invariant _ _ β hβ hσ1,
    relEntropy_ancilla_invariant _ _ β hβ (diagState_posDef s hs0 hs1)]
  exact relEntropy_drop_rhoR_diagState r hr0 hr1 s hs0 hs1

/-- **The strict drop survives `⊗ β`** (pure family).  Partial dephasing of `|+⟩⟨+| ⊗ β` against
`diagState s ⊗ β` strictly lowers the relative entropy. -/
theorem relEntropy_strict_drop_dephasing_kron_pure {blk : Type*} [Fintype blk] [DecidableEq blk]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (β : DensityMatrix blk) (hβ : β.val.PosDef) :
    relEntropy ((dephaseKronId blk).toDM (plusState.kron β))
        ((dephaseKronId blk).toDM ((diagState s hs0 hs1).kron β))
      < relEntropy (plusState.kron β) ((diagState s hs0 hs1).kron β) := by
  have hσ1 : (dephase.toDM (diagState s hs0 hs1)).val.PosDef := by
    rw [dephase_diagState]; exact diagState_posDef s hs0 hs1
  rw [dephaseKronId_toDM_kron, dephaseKronId_toDM_kron,
    relEntropy_ancilla_invariant _ _ β hβ hσ1,
    relEntropy_ancilla_invariant _ _ β hβ (diagState_posDef s hs0 hs1)]
  exact relEntropy_drop_plusState_diagState s hs0 hs1

/-! ## The headline seals — uniform in the block -/

/-- **Q0: no Stinespring recovery of a partially dephased faithful state, uniform in the block.**
For an *arbitrary* block `blk` (in particular every tower level `M_{2ⁿ}`) and a faithful block state
`β`, the partial-dephasing channel `Δ ⊗ id_blk` sends the faithful coherent state `ρ_r ⊗ β` to
`(I/2) ⊗ β`, whereas the diagonal reference `diagState s ⊗ β` is a fixed point.  The relative
entropy against `diagState s ⊗ β` strictly drops (by `log 2 − h₂((1+r)/2) > 0`, unchanged by the
block), so no faithful-ancilla Stinespring channel on the enlarged system `M₂ ⊗ M_blk` inverts the
partial dephasing on `ρ_r ⊗ β` and `diagState s ⊗ β` simultaneously.  The reference pair has
distinct dephasing images (`(I/2) ⊗ β ≠ diagState s ⊗ β`), so the obstruction is genuine (Petz
1986/2003; Ohya–Petz, *Quantum Entropy and Its Use*, Springer). -/
theorem quantum_seal_dephase_kron_faithful {blk : Type} [Fintype blk] [DecidableEq blk]
    {e : Type} [Fintype e] [DecidableEq e]
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (β : DensityMatrix blk) (hβ : β.val.PosDef)
    (α : DensityMatrix e) (U : Matrix.unitaryGroup ((Fin 2 × blk) × e) ℂ) (hα : α.val.PosDef)
    (hsecρ :
      ((((dephaseKronId blk).toDM ((rhoR r hr0 hr1).kron β)).kron α).conj U).partialTraceRight
        = (rhoR r hr0 hr1).kron β)
    (hsecσ :
      ((((dephaseKronId blk).toDM ((diagState s hs0 hs1).kron β)).kron α).conj U).partialTraceRight
        = (diagState s hs0 hs1).kron β) : False := by
  refine no_stinespring_section_of_strict_relEntropy_drop (dephaseKronId blk).toDM α U hα
    ((rhoR r hr0 hr1).kron β) ((diagState s hs0 hs1).kron β) ?_ hsecρ hsecσ ?_
  · have himg : (dephaseKronId blk).toDM ((diagState s hs0 hs1).kron β)
        = (diagState s hs0 hs1).kron β := by
      rw [dephaseKronId_toDM_kron, dephase_diagState]
    rw [himg]
    exact Matrix.PosDef.kronecker (diagState_posDef s hs0 hs1) hβ
  · exact relEntropy_strict_drop_dephasing_kron r hr0 hr1 s hs0 hs1 β hβ

/-- **Q0 (pure variant): no Stinespring recovery of a partially dephased pure state, uniform in the
block.**  Mirrors `quantum_seal_dephase` with the maximally coherent qubit `|+⟩⟨+|` tensored with an
arbitrary faithful block `β`.

Note (honesty): for a pure input the section hypothesis `hsecρ` is already unsatisfiable on rank
grounds alone — a faithful-ancilla Stinespring channel maps the faithful dephased input to a
full-rank state, never the rank-deficient `plusState ⊗ β` — so the faithful variant
`quantum_seal_dephase_kron_faithful` is the evidentially honest no-recovery headline. -/
theorem quantum_seal_dephase_kron {blk : Type} [Fintype blk] [DecidableEq blk]
    {e : Type} [Fintype e] [DecidableEq e]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (β : DensityMatrix blk) (hβ : β.val.PosDef)
    (α : DensityMatrix e) (U : Matrix.unitaryGroup ((Fin 2 × blk) × e) ℂ) (hα : α.val.PosDef)
    (hsecρ : ((((dephaseKronId blk).toDM (plusState.kron β)).kron α).conj U).partialTraceRight
      = plusState.kron β)
    (hsecσ :
      ((((dephaseKronId blk).toDM ((diagState s hs0 hs1).kron β)).kron α).conj U).partialTraceRight
        = (diagState s hs0 hs1).kron β) : False := by
  refine no_stinespring_section_of_strict_relEntropy_drop (dephaseKronId blk).toDM α U hα
    (plusState.kron β) ((diagState s hs0 hs1).kron β) ?_ hsecρ hsecσ ?_
  · have himg : (dephaseKronId blk).toDM ((diagState s hs0 hs1).kron β)
        = (diagState s hs0 hs1).kron β := by
      rw [dephaseKronId_toDM_kron, dephase_diagState]
    rw [himg]
    exact Matrix.PosDef.kronecker (diagState_posDef s hs0 hs1) hβ
  · exact relEntropy_strict_drop_dephasing_kron_pure s hs0 hs1 β hβ

end ErgodicTheory.OperatorEntropy
