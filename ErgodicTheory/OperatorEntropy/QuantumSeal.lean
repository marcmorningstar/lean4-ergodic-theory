/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.EntropyPure
import ErgodicTheory.OperatorEntropy.RelEntropyAdditivity
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessingCPTP
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Issue #59 (tiers T2a/T2b) — the quantum recovery seal for the dephasing channel

The **dephasing** (pinching) channel `Δ` on a qubit destroys the off-diagonal coherences of a
state.  Feeding it a state with coherence produces a strict drop of the Umegaki relative entropy
against the fixed point `I/2`; by Petz's theorem (recovery ⟺ saturation of the data-processing
inequality; Petz 1986, 2003) no Stinespring recovery channel can undo it.  This is the finite-
dimensional **no-way-back seal**: the coherence the dephasing MASA erases is information the
environment carries away irreversibly (Wilde, *Quantum Information Theory*, recoverability).

Two headline obstructions, both discharged from
`no_stinespring_section_of_strict_relEntropy_drop`.  The reference state `σ` is the *faithful
diagonal* state `diagState s = diag((1+s)/2, (1−s)/2)` (`0 < s < 1`), a fixed point of the
dephasing (`dephase (diagState s) = diagState s`).  Crucially `dephase ρ ≠ dephase σ` for the
coherent inputs below (they dephase to `I/2 ≠ diagState s`), so the two Stinespring-section
hypotheses have *distinct* left-hand sides and the obstruction is genuine — see the QA note.

* `quantum_seal_dephase` (**T2a**) — the maximally coherent pure state `|+⟩⟨+|` dephases to `I/2`,
  a strict relative-entropy drop of `S(I/2) − S(|+⟩⟨+|) = log 2 > 0` against `diagState s`; no
  Stinespring section recovers it.
* `quantum_seal_dephase_faithful` (**T2b**) — the *faithful* one-parameter family
  `ρ_r = ½!![1,r;r,1]` (`0 < r < 1`, PosDef) dephases to `I/2` with a strict drop
  `log 2 − h₂((1+r)/2) > 0`, where `h₂` is the binary entropy.  A faithful-state seal.

**QA note — the reference state must be off the dephasing image.**  Taking `σ := I/2` (as an
earlier draft did) is *degenerate*: then `dephase ρ = I/2 = dephase σ`, so the two section
hypotheses `R (dephase ρ) = ρ` and `R (dephase σ) = σ` share an identical left-hand side and force
`ρ = σ` set-theoretically — `False` follows with no entropy input at all, and the no-recovery
content is vacuous.  The honest packaging therefore uses a reference state whose dephasing image
differs from that of `ρ`; `diagState s` (any `0 < s < 1`) does this while remaining a faithful
dephasing fixed point.  The `σ = I/2` strict-DPI drops are still recorded honestly, as the
standalone lemmas `relEntropy_drop_plusState_mm` / `relEntropy_drop_rhoR_mm` — they are genuine
strict data-processing instances, just not no-recovery *sections*.

The Petz-map corollary (that the explicit Petz recovery map fails on `ρ_r`) would need the
"recovery ⟹ DPI saturation" direction (`petz_recovery_implies_equality`), which requires the
*monotonicity* of the dephasing channel itself — a general-`KrausChannel` data-processing
inequality that is not available in repo (only the faithful-ancilla Stinespring family is).  It is
therefore intentionally omitted; the Stinespring-seal headlines above are the complete deliverable.
-/

open Matrix Real
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## The dephasing (pinching) channel on a qubit -/

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the leave-one-out
-- `unusedSimpArgs` linter (each branch reads off a different `!![…]`/diagonal corner).
set_option linter.unusedSimpArgs false in
/-- The **dephasing / pinching channel** on a qubit: `Δ ρ = P₀ ρ P₀ + P₁ ρ P₁`, killing the
off-diagonal (coherence) entries.  Kraus operators are the two rank-one diagonal projections. -/
def dephase : KrausChannel (Fin 2) where
  ι := Fin 2
  K := ![Matrix.diagonal ![1, 0], Matrix.diagonal ![0, 1]]
  htp := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_add]
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, Pi.add_apply, Pi.mul_apply, Pi.star_apply]

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- **Action of the dephasing channel:** it keeps the diagonal and erases the coherences. -/
theorem dephase_toDM_val (ρ : DensityMatrix (Fin 2)) :
    (dephase.toDM ρ).val = Matrix.diagonal ![ρ.val 0 0, ρ.val 1 1] := by
  have hexp : dephase.toMat ρ.val
      = Matrix.diagonal ![1, 0] * ρ.val * (Matrix.diagonal ![1, 0])ᴴ
        + Matrix.diagonal ![0, 1] * ρ.val * (Matrix.diagonal ![0, 1])ᴴ := by
    change (∑ i : Fin 2, ![Matrix.diagonal ![1, 0], Matrix.diagonal ![0, 1]] i * ρ.val
        * (![Matrix.diagonal ![1, 0], Matrix.diagonal ![0, 1]] i)ᴴ) = _
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  change dephase.toMat ρ.val = _
  rw [hexp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.add_apply]

/-! ## The maximally coherent pure state `|+⟩⟨+|` -/

/-- The **maximally coherent qubit state** `|+⟩⟨+| = ½!![1,1;1,1]`. -/
def plusState : DensityMatrix (Fin 2) where
  val := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]
  posSemidef := by
    have hH : (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2])ᴴ = !![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    have hsq : (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2]) * (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2])
        = !![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2] := by
      rw [Matrix.mul_fin_two]; norm_num
    have hfac : (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2])
        = (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2])ᴴ * (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2]) := by
      rw [hH, hsq]
    rw [hfac]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_one := by rw [Matrix.trace_fin_two_of]; norm_num

/-- `|+⟩⟨+|` is a projection: `P² = P`. -/
theorem plusState_sq : plusState.val * plusState.val = plusState.val := by
  change (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2]) * (!![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2])
      = !![(1 : ℂ) / 2, 1 / 2; 1 / 2, 1 / 2]
  rw [Matrix.mul_fin_two]; norm_num

/-- `|+⟩⟨+|` is pure: zero von Neumann entropy. -/
theorem vonNeumannEntropy_plusState : vonNeumannEntropy plusState = 0 :=
  vonNeumannEntropy_eq_zero_of_sq_eq plusState plusState_sq

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- Dephasing `|+⟩⟨+|` produces the maximally mixed state `I/2`. -/
theorem dephase_plusState : dephase.toDM plusState = DensityMatrix.maximallyMixed := by
  apply DensityMatrix.ext
  rw [dephase_toDM_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusState, DensityMatrix.maximallyMixed, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.smul_apply, Fintype.card_fin, Complex.real_smul]

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- Dephasing fixes the maximally mixed state `I/2`. -/
theorem dephase_maximallyMixed :
    dephase.toDM (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2))
      = DensityMatrix.maximallyMixed := by
  apply DensityMatrix.ext
  rw [dephase_toDM_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DensityMatrix.maximallyMixed, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.smul_apply, Fintype.card_fin, Complex.real_smul]

/-! ## The faithful family `ρ_r = ½!![1,r;r,1]` -/

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- The diagonal state `diag((1+r)/2, (1−r)/2)` — the eigenbasis form of `ρ_r`. -/
def diagState (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : DensityMatrix (Fin 2) where
  val := Matrix.diagonal fun i => ((![(1 + r) / 2, (1 - r) / 2] i : ℝ) : ℂ)
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      rw [Complex.zero_le_real] <;> linarith
  trace_one := by
    rw [Matrix.trace_diagonal, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    push_cast; ring

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- The eigenvalues of `diagState` are positive, so it is faithful (PosDef). -/
theorem diagState_posDef (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (diagState r hr0 hr1).val.PosDef := by
  change (Matrix.diagonal fun i => ((![(1 + r) / 2, (1 - r) / 2] i : ℝ) : ℂ)).PosDef
  rw [Matrix.posDef_diagonal_iff]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    rw [Complex.zero_lt_real] <;> linarith

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- Von Neumann entropy of the diagonal state is the classical (Shannon) entropy of its diagonal. -/
theorem diagState_entropy (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    vonNeumannEntropy (diagState r hr0 hr1)
      = Real.negMulLog ((1 + r) / 2) + Real.negMulLog ((1 - r) / 2) := by
  have h := vonNeumannEntropy_diagonal ![(1 + r) / 2, (1 - r) / 2]
    (diagState r hr0 hr1).posSemidef (diagState r hr0 hr1).trace_one
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  exact h

-- Branchy `simp only` matrix trace read-off; the two-corner diagonal cons args trip the linter.
set_option linter.unusedSimpArgs false in
/-- **Relative entropy against a diagonal reference state.**  For any qubit state `ρ`,
`D(ρ ‖ diagState s) = −S(ρ) − (ρ₀₀ log((1+s)/2) + ρ₁₁ log((1−s)/2))`.  The cross term is the
classical `Tr(ρ · log σ)` with `σ = diagState s` diagonal in the computational basis, so it reads
off the computational-basis diagonal of `ρ` against the eigenvalues `(1±s)/2`. -/
theorem relEntropy_diagState (ρ : DensityMatrix (Fin 2)) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    relEntropy ρ (diagState s hs0 hs1)
      = -vonNeumannEntropy ρ
        - ((ρ.val 0 0).re * Real.log ((1 + s) / 2)
          + (ρ.val 1 1).re * Real.log ((1 - s) / 2)) := by
  rw [relEntropy_eq_negS_sub]
  congr 1
  have hcfc : (diagState s hs0 hs1).posSemidef.1.cfc Real.log
      = Matrix.diagonal (fun i => (Real.log ((![(1 + s) / 2, (1 - s) / 2] i : ℝ)) : ℂ)) := by
    rw [← Matrix.IsHermitian.cfc_eq]
    exact cfc_log_diagonal (fun i => ((![(1 + s) / 2, (1 - s) / 2] i : ℝ)))
  rw [hcfc, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_diagonal, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-! ### The Hadamard unitary diagonalizing `ρ_r` -/

/-- Scalar `1/√2`, as a complex number. -/
def hadC : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem hadC_sq : hadC * hadC = 1 / 2 := by
  have h : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [hadC, ← Complex.ofReal_mul, h]; norm_num

theorem hadC_star : star hadC = hadC := by simp [hadC]

/-- The (unnormalized) Hadamard matrix `!![1,1;1,−1]`. -/
def had0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

theorem had0_star : star had0 = had0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [had0, Matrix.star_apply, Matrix.of_apply]

theorem had0_sq : had0 * had0 = (2 : ℂ) • 1 := by
  rw [had0, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] <;> norm_num

theorem had0_mmm (a b : ℂ) : had0 * !![a, 0; 0, b] * had0 = !![a + b, a - b; a - b, a + b] := by
  rw [had0, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply] <;> ring

/-- The real self-adjoint **Hadamard matrix** `(1/√2)!![1,1;1,−1]`. -/
def hadMat : Matrix (Fin 2) (Fin 2) ℂ := hadC • had0

theorem hadMat_star : star hadMat = hadMat := by
  rw [hadMat, star_smul, hadC_star, had0_star]

theorem hadMat_sq : hadMat * hadMat = 1 := by
  rw [hadMat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hadC_sq, had0_sq, smul_smul,
    show ((1 : ℂ) / 2 * 2) = 1 by norm_num, one_smul]

/-- The Hadamard unitary as an element of the unitary group. -/
def hadU : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨hadMat, by rw [Matrix.mem_unitaryGroup_iff, hadMat_star]; exact hadMat_sq⟩

theorem hadU_coe : (hadU : Matrix (Fin 2) (Fin 2) ℂ) = hadMat := rfl

/-- The faithful family `ρ_r = ½!![1,r;r,1]`, defined as the Hadamard conjugate of `diagState`. -/
def rhoR (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : DensityMatrix (Fin 2) :=
  (diagState r hr0 hr1).conj hadU

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- The diagonal form: `diagState.val = !![(1+r)/2, 0; 0, (1−r)/2]`. -/
theorem diagState_val_fin (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (diagState r hr0 hr1).val
      = !![(((1 + r) / 2 : ℝ) : ℂ), 0; 0, (((1 - r) / 2 : ℝ) : ℂ)] := by
  change (Matrix.diagonal fun i => ((![(1 + r) / 2, (1 - r) / 2] i : ℝ) : ℂ)) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.of_apply]

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- **The dephasing channel fixes a diagonal state.**  `dephase (diagState s) = diagState s`: the
dephasing keeps the diagonal, and `diagState s` has no off-diagonal coherence to erase. -/
theorem dephase_diagState (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    dephase.toDM (diagState s hs0 hs1) = diagState s hs0 hs1 := by
  apply DensityMatrix.ext
  rw [dephase_toDM_val, diagState_val_fin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

/-- Explicit matrix form of `ρ_r`. -/
theorem rhoR_val (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (rhoR r hr0 hr1).val = !![(1 : ℂ) / 2, (r : ℂ) / 2; (r : ℂ) / 2, 1 / 2] := by
  change (hadU : Matrix (Fin 2) (Fin 2) ℂ) * (diagState r hr0 hr1).val
      * star (hadU : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [hadU_coe, hadMat_star, diagState_val_fin]
  simp only [hadMat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hadC_sq]
  rw [had0_mmm]
  have hab : (((1 + r) / 2 : ℝ) : ℂ) + (((1 - r) / 2 : ℝ) : ℂ) = 1 := by push_cast; ring
  have hab' : (((1 + r) / 2 : ℝ) : ℂ) - (((1 - r) / 2 : ℝ) : ℂ) = (r : ℂ) := by push_cast; ring
  simp only [hab, hab']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] <;> ring

/-- `ρ_r` is faithful (PosDef): unitary conjugation preserves positive-definiteness. -/
theorem rhoR_posDef (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : (rhoR r hr0 hr1).val.PosDef := by
  change ((hadU : Matrix (Fin 2) (Fin 2) ℂ) * (diagState r hr0 hr1).val
      * star (hadU : Matrix (Fin 2) (Fin 2) ℂ)).PosDef
  rw [Matrix.star_eq_conjTranspose]
  refine (diagState_posDef r hr0 hr1).mul_mul_conjTranspose_same ?_
  rw [Matrix.vecMul_injective_iff_isUnit]
  exact (⟨(hadU : Matrix (Fin 2) (Fin 2) ℂ), star (hadU : Matrix (Fin 2) (Fin 2) ℂ),
    Unitary.coe_mul_star_self hadU, Unitary.coe_star_mul_self hadU⟩ :
    (Matrix (Fin 2) (Fin 2) ℂ)ˣ).isUnit

/-- Dephasing `ρ_r` produces the maximally mixed state `I/2` (its coherence `r/2` is erased). -/
theorem dephase_rhoR (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    dephase.toDM (rhoR r hr0 hr1) = DensityMatrix.maximallyMixed := by
  apply DensityMatrix.ext
  rw [dephase_toDM_val, rhoR_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DensityMatrix.maximallyMixed, Matrix.of_apply, Matrix.smul_apply,
      Fintype.card_fin, Complex.real_smul]

/-- Von Neumann entropy of `ρ_r` is the binary entropy `h₂((1+r)/2)`. -/
theorem vonNeumannEntropy_rhoR (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    vonNeumannEntropy (rhoR r hr0 hr1) = Real.binEntropy ((1 + r) / 2) := by
  unfold rhoR
  rw [vonNeumannEntropy_conj, diagState_entropy,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  congr 2
  ring

/-- The binary entropy of `(1+r)/2` (with `r > 0`) is strictly below `log 2`. -/
theorem vonNeumannEntropy_rhoR_lt (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    vonNeumannEntropy (rhoR r hr0 hr1) < Real.log 2 := by
  rw [vonNeumannEntropy_rhoR, Real.binEntropy_lt_log_two]
  intro heq
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at heq
  linarith

/-! ## Computational-basis diagonal read-offs

All three coherent inputs (`|+⟩⟨+|`, `I/2`, `ρ_r`) share the *same* computational-basis diagonal
`(½, ½)`, so their relative entropies against `diagState s` differ only through the von Neumann
entropy term (the cross term `Tr(ρ log σ)` is common). -/

-- Branchy `fin_cases`/`simp` matrix computation; cross-branch simp args trip the linter.
set_option linter.unusedSimpArgs false in
/-- The computational-basis diagonal entries of `|+⟩⟨+|` are `½`. -/
theorem plusState_val_diag (i : Fin 2) : plusState.val i i = ((1 / 2 : ℝ) : ℂ) := by
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num]
  fin_cases i <;>
    simp only [Fin.mk_zero, Fin.mk_one, plusState, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply]

/-- Real part of the diagonal of `|+⟩⟨+|` is `½`. -/
theorem plusState_val_re (i : Fin 2) : (plusState.val i i).re = 1 / 2 := by
  rw [plusState_val_diag, Complex.ofReal_re]

/-- The computational-basis diagonal entries of the maximally mixed qubit are `½`. -/
theorem maximallyMixed_val_diag (i : Fin 2) :
    (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)).val i i = ((1 / 2 : ℝ) : ℂ) := by
  simp only [DensityMatrix.maximallyMixed, Matrix.smul_apply, Matrix.one_apply_eq,
    Fintype.card_fin, Complex.real_smul, mul_one]
  push_cast; ring

/-- Real part of the diagonal of the maximally mixed qubit is `½`. -/
theorem maximallyMixed_val_re (i : Fin 2) :
    ((DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)).val i i).re = 1 / 2 := by
  rw [maximallyMixed_val_diag, Complex.ofReal_re]

-- The two `fin_cases` branches read off opposite corners of `!![…]`, so each branch leaves half
-- the `cons`/`head` simp lemmas idle; the leave-one-out unusedSimpArgs linter flags them all.
set_option linter.unusedSimpArgs false in
/-- The computational-basis diagonal entries of `ρ_r` are `½` (its coherence lives off-diagonal). -/
theorem rhoR_val_diag (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (i : Fin 2) :
    (rhoR r hr0 hr1).val i i = ((1 / 2 : ℝ) : ℂ) := by
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num]
  fin_cases i <;>
    · rw [rhoR_val]
      simp only [Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.of_apply]

/-- Real part of the diagonal of `ρ_r` is `½`. -/
theorem rhoR_val_re (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (i : Fin 2) :
    ((rhoR r hr0 hr1).val i i).re = 1 / 2 := by
  rw [rhoR_val_diag, Complex.ofReal_re]

/-! ## The `σ = I/2` strict data-processing drops (honest, but NOT no-recovery sections)

These record the strict relative-entropy drop of the dephasing channel against its own fixed point
`I/2`.  They are genuine strict DPI instances, but they cannot be packaged as no-recovery
Stinespring *sections*: with `σ = I/2`, `dephase ρ = I/2 = dephase σ`, so the two section
hypotheses would share an identical left-hand side and force `ρ = σ` for free (see the module QA
note).  The honest no-recovery headlines below therefore use `σ = diagState s` instead. -/

/-- Strict data-processing drop for `|+⟩⟨+|` against `I/2`:
`D(dephase|+⟩⟨+| ‖ dephase(I/2)) = 0 < log 2 = D(|+⟩⟨+| ‖ I/2)`. -/
theorem relEntropy_drop_plusState_mm :
    relEntropy (dephase.toDM plusState)
        (dephase.toDM (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)))
      < relEntropy plusState DensityMatrix.maximallyMixed := by
  rw [dephase_plusState, dephase_maximallyMixed, relEntropy_self_eq_zero,
    relEntropy_maximallyMixed, vonNeumannEntropy_plusState, sub_zero, Fintype.card_fin]
  exact Real.log_pos (by norm_num)

/-- Strict data-processing drop for the faithful `ρ_r` against `I/2`:
`0 < log 2 − h₂((1+r)/2) = D(ρ_r ‖ I/2)`. -/
theorem relEntropy_drop_rhoR_mm (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    relEntropy (dephase.toDM (rhoR r hr0 hr1))
        (dephase.toDM (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)))
      < relEntropy (rhoR r hr0 hr1) DensityMatrix.maximallyMixed := by
  rw [dephase_rhoR, dephase_maximallyMixed, relEntropy_self_eq_zero, relEntropy_maximallyMixed,
    Fintype.card_fin]
  have hlt := vonNeumannEntropy_rhoR_lt r hr0 hr1
  have h2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
  rw [h2]
  linarith

/-! ## T2a — the pure-state dephasing seal (non-degenerate reference `diagState s`) -/

/-- **T2a: no Stinespring recovery of a dephased pure state.**  The maximally coherent state
`|+⟩⟨+|` dephases to `I/2`, whereas the faithful diagonal reference `diagState s` is a dephasing
fixed point (`dephase ρ ≠ dephase σ`).  The relative entropy against `diagState s` strictly drops
by `S(I/2) − S(|+⟩⟨+|) = log 2 > 0` (the common cross term cancels).  Hence no faithful-ancilla
Stinespring channel inverts the dephasing on `|+⟩⟨+|` and `diagState s` simultaneously (Petz
recovery ⟺ DPI saturation; the drop is strict). -/
theorem quantum_seal_dephase {e : Type} [Fintype e] [DecidableEq e]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (α : DensityMatrix e) (U : Matrix.unitaryGroup (Fin 2 × e) ℂ) (hα : α.val.PosDef)
    (hsecρ : (((dephase.toDM plusState).kron α).conj U).partialTraceRight = plusState)
    (hsecσ : (((dephase.toDM (diagState s hs0 hs1)).kron α).conj U).partialTraceRight
      = diagState s hs0 hs1) : False := by
  refine no_stinespring_section_of_strict_relEntropy_drop dephase.toDM α U hα
    plusState (diagState s hs0 hs1) ?_ hsecρ hsecσ ?_
  · rw [dephase_diagState]; exact diagState_posDef s hs0 hs1
  · rw [dephase_plusState, dephase_diagState, relEntropy_diagState, relEntropy_diagState,
      plusState_val_re, plusState_val_re, maximallyMixed_val_re, maximallyMixed_val_re,
      vonNeumannEntropy_plusState, vonNeumannEntropy_maximallyMixed, Fintype.card_fin]
    have h2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [h2]
    linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-! ## T2b — the faithful-state dephasing seal (non-degenerate reference `diagState s`) -/

/-- **T2b: no Stinespring recovery of a dephased faithful state.**  The faithful coherent state
`ρ_r = ½!![1,r;r,1]` (`0 < r < 1`) dephases to `I/2`, while the faithful diagonal reference
`diagState s` is a dephasing fixed point.  The relative entropy against `diagState s` strictly drops
by `log 2 − h₂((1+r)/2) > 0`, where `h₂` is the binary entropy.  Hence no faithful-ancilla
Stinespring channel inverts the dephasing on `ρ_r` and `diagState s` simultaneously.  Unlike a
pure-state seal this is a *faithful* (full-rank) input, so the seal is not an artefact of purity —
it is coherence, destroyed by the dephasing MASA, that no reversal recovers (Petz 1986/2003; Wilde,
recoverability). -/
theorem quantum_seal_dephase_faithful {e : Type} [Fintype e] [DecidableEq e]
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (α : DensityMatrix e) (U : Matrix.unitaryGroup (Fin 2 × e) ℂ) (hα : α.val.PosDef)
    (hsecρ : (((dephase.toDM (rhoR r hr0 hr1)).kron α).conj U).partialTraceRight
      = rhoR r hr0 hr1)
    (hsecσ : (((dephase.toDM (diagState s hs0 hs1)).kron α).conj U).partialTraceRight
      = diagState s hs0 hs1) : False := by
  refine no_stinespring_section_of_strict_relEntropy_drop dephase.toDM α U hα
    (rhoR r hr0 hr1) (diagState s hs0 hs1) ?_ hsecρ hsecσ ?_
  · rw [dephase_diagState]; exact diagState_posDef s hs0 hs1
  · rw [dephase_rhoR, dephase_diagState, relEntropy_diagState, relEntropy_diagState,
      rhoR_val_re, rhoR_val_re, maximallyMixed_val_re, maximallyMixed_val_re,
      vonNeumannEntropy_maximallyMixed, Fintype.card_fin]
    have hlt := vonNeumannEntropy_rhoR_lt r hr0 hr1
    have h2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [h2]
    linarith

end ErgodicTheory.OperatorEntropy
