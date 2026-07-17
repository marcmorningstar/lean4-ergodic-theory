/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.GrowingTower.Tower
import ErgodicTheory.OperatorEntropy.GrowingTower.SealLift
import ErgodicTheory.OperatorEntropy.CNT.NonCommutativeCertificate

/-!
# Issue #70 (tier Q2) — the alive-and-sealed growing quantum world

This module **bundles** the three faces of the growing-finite qubit tower into a single witnessed
object, `GrowingQuantumWorld`, and exhibits a concrete instance
(`growingQuantumWorld_exists`).  All three ingredients are already proved in the sibling modules;
the new content here is only the *bundling* — packaging aliveness, the per-stage seal, and the
non-commutativity certificate as one coherent structure, and checking they can be satisfied
simultaneously by one concrete family.

The world combines:

* **Aliveness (spatial entropy production).**  The tower enlarges its capacity by one fresh qubit
  per step; on the faithful local state `ρ_r = ½!![1, r; r, 1]` (`0 < r < 1`) the per-step von
  Neumann entropy rate `blockEntropy ρ_r n / n` converges to the *positive* constant `S(ρ_r) > 0`
  (`tendsto_blockEntropy_div`, `blockEntropy_rhoR_pos`).  Equivalently the block entropy grows
  linearly, `blockEntropy ρ_r n = n · S(ρ_r)` (`blockEntropy_eq`).

* **The per-stage dephasing seal, at the world's own block states.**  At every level `n` the
  partial-dephasing channel `Δ ⊗ id` on `M₂ ⊗ M_{2ⁿ}` admits *no* faithful-ancilla Stinespring
  recovery that simultaneously inverts it on the coherent state `ρ_r ⊗ ρ_r^{⊗n}` and on the
  diagonal reference `diagState s ⊗ ρ_r^{⊗n}` (`quantum_seal_dephase_kron_faithful`).  The block
  here is the world's **own** length-`n` block `ρ_r^{⊗n}` (positive definite by
  `rhoPow_posDef`), so this is the honest "seal at every level of the tower" reading; the recovery
  is quantified over *all* Stinespring dilations on the enlarged system, and the reference pair has
  distinct dephasing images, so the obstruction is genuine (not the degenerate `Λρ = Λσ` collapse).

* **A non-commutativity certificate on the base factor.**  The single-qubit dynamics `qDynamics`
  does not preserve the canonical MASA, and the seal's eigenprojection `eigProj` is off-diagonal —
  `qDynamics_seal_no_common_canonical_masa` (CNT 1987).  This certifies the **base qubit factor**;
  via `shiftAdjoinQubit` (`A ↦ 1 ⊗ A`) it embeds into every level, but it is **not** a re-proved
  per-level MASA statement — it is the base-factor certificate transported by the tower embedding.

## Scope and provenance (honesty)

This is the **growing-finite** tower — one fresh qubit adjoined per step — *not* the completed
thermodynamic-limit chain `⊗_{ℤ} M₂` (that idealization is the subject of issue #71).  The rate is
a **spatial / per-step** growth rate; there is no tension with the *temporal* fixed-dimension
vanishing `cntDynamicalEntropy_eq_zero` elsewhere in this cluster (fixed algebra, trivial dynamics
⇒ zero temporal rate; growing algebra ⇒ positive spatial rate).

The **bundling** is the new content of this module.  Its three ingredients are standard:
additivity of the von Neumann entropy under tensor products (Nielsen–Chuang, *Quantum Computation
and Quantum Information*, §11.3; Ohya–Petz, *Quantum Entropy and Its Use*, Springer); the
data-processing / Petz-recovery seal (Petz 1986, 2003; Ohya–Petz); and the Connes–Narnhofer–Thirring
non-commutativity of the dynamics against a canonical MASA (Connes–Narnhofer–Thirring,
*Comm. Math. Phys.* **112** (1987)).
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## Positive definiteness of the length-`n` block state -/

/-- **The length-`n` block `ρ^{⊗ n}` of a faithful single-qubit state is positive definite.**
By induction: the base block on `Fin 1` is the maximally mixed (scalar) state, positive definite;
the inductive step is a Kronecker product of positive-definite factors. -/
theorem rhoPow_posDef (ρ : DensityMatrix (Fin 2)) (hρ : ρ.val.PosDef) (n : ℕ) :
    (rhoPow ρ n).val.PosDef := by
  induction n with
  | zero => exact DensityMatrix.maximallyMixed_posDef
  | succ k ih => exact Matrix.PosDef.kronecker hρ ih

/-! ## The per-stage seal predicate -/

/-- **The per-stage dephasing-seal predicate at the world's own block states.**  For the faithful
local state `ρ_r` and diagonal reference `diagState s`: at every level `n`, the partial-dephasing
channel on `M₂ ⊗ M_{2ⁿ}` admits no faithful-ancilla Stinespring recovery that simultaneously
inverts it on the coherent state `ρ_r ⊗ ρ_r^{⊗n}` and on the reference `diagState s ⊗ ρ_r^{⊗n}`;
the block is the world's own length-`n` block `ρ_r^{⊗n}`. -/
def WorldSealed (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : Prop :=
  ∀ (n : ℕ) {e : Type} [Fintype e] [DecidableEq e]
    (α : DensityMatrix e)
    (U : Matrix.unitaryGroup ((Fin 2 × Qbits n) × e) ℂ), α.val.PosDef →
    ((((dephaseKronId (Qbits n)).toDM
        ((rhoR r hr0 hr1).kron (rhoPow (rhoR r hr0 hr1) n))).kron α).conj U).partialTraceRight
      = (rhoR r hr0 hr1).kron (rhoPow (rhoR r hr0 hr1) n) →
    ((((dephaseKronId (Qbits n)).toDM
        ((diagState s hs0 hs1).kron (rhoPow (rhoR r hr0 hr1) n))).kron α).conj U).partialTraceRight
      = (diagState s hs0 hs1).kron (rhoPow (rhoR r hr0 hr1) n) →
    False

/-! ## The aliveness and non-commutativity predicates -/

/-- **The aliveness (spatial entropy-rate) predicate.**  The per-step von Neumann entropy rate
`blockEntropy ρ_r n / n` converges to the single-qubit entropy `S(ρ_r)`. -/
def WorldAlive (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : Prop :=
  Filter.Tendsto (fun n => blockEntropy (rhoR r hr0 hr1) n / n) Filter.atTop
    (nhds (vonNeumannEntropy (rhoR r hr0 hr1)))

/-- **The base-factor non-commutativity certificate (CNT 1987).**  The single-qubit dynamics does
not preserve the canonical MASA, and the seal's eigenprojection is off-diagonal. -/
def BaseNonCommutative : Prop :=
  ¬ CNT.PreservesDiag CNT.qDynamics ∧
    ¬ (Matrix.diagonal (Matrix.diag CNT.eigProj) * CNT.eigProj
        = CNT.eigProj * Matrix.diagonal (Matrix.diag CNT.eigProj))

/-! ## The bundled world -/

/-- **The alive-and-sealed growing quantum world.**  A single object bundling the three faces of
the growing-finite qubit tower for one concrete faithful local state `ρ_r` and one diagonal
reference `diagState s`: positive spatial entropy production (aliveness), a per-stage dephasing
seal at the world's own block states (uniform over the level and over all Stinespring recovery
dilations), and a base-factor non-commutativity certificate.  See the module docstring for scope
and provenance. -/
structure GrowingQuantumWorld where
  /-- Coherence parameter of the faithful local state `ρ_r = ½!![1, r; r, 1]`. -/
  r : ℝ
  /-- Diagonal-bias parameter of the seal's reference state `diagState s`. -/
  s : ℝ
  /-- The local state `ρ_r` is faithful: `0 < r`. -/
  hr0 : 0 < r
  /-- The local state `ρ_r` is faithful: `r < 1`. -/
  hr1 : r < 1
  /-- The reference `diagState s` is faithful: `0 < s`. -/
  hs0 : 0 < s
  /-- The reference `diagState s` is faithful: `s < 1`. -/
  hs1 : s < 1
  /-- **Aliveness (positivity of the rate).** The single-qubit von Neumann entropy `S(ρ_r)` is
  strictly positive, so the tower produces a positive amount of entropy per step. -/
  rate_pos : 0 < vonNeumannEntropy (rhoR r hr0 hr1)
  /-- **Aliveness (convergence of the per-step rate).** The per-step (spatial) entropy rate
  `blockEntropy ρ_r n / n` converges to the positive constant `S(ρ_r)` (see `WorldAlive`). -/
  rate : WorldAlive r hr0 hr1
  /-- **The per-stage dephasing seal, at the world's own block states.** At every level `n`, no
  faithful-ancilla Stinespring recovery inverts the partial dephasing on both the coherent
  `ρ_r ⊗ ρ_r^{⊗n}` and the reference `diagState s ⊗ ρ_r^{⊗n}`; the block is the world's own
  length-`n` block `ρ_r^{⊗n}` — the honest "seal at every level of the tower" reading (see
  `WorldSealed`). -/
  perStageSeal : WorldSealed r hr0 hr1 s hs0 hs1
  /-- **Base-factor non-commutativity certificate (CNT 1987).** The single-qubit dynamics does not
  preserve the canonical MASA and the seal's eigenprojection is off-diagonal. This certifies the
  *base qubit factor*; it embeds into every level via `shiftAdjoinQubit`, but is not a re-proved
  per-level MASA statement (see `BaseNonCommutative`). -/
  noncommutative : BaseNonCommutative

/-! ## The concrete witness -/

/-- **A concrete alive-and-sealed growing quantum world exists.**  Take the balanced faithful local
state `ρ_{1/2}` and the balanced diagonal reference `diagState (1/2)`: aliveness holds because the
single-qubit binary entropy `h₂(3/4) > 0` is positive, the per-stage seal is
`quantum_seal_dephase_kron_faithful` instantiated at the world's own block state `ρ_{1/2}^{⊗n}`
(positive definite by `rhoPow_posDef`), and the base-factor non-commutativity certificate is
`CNT.qDynamics_seal_no_common_canonical_masa`. -/
theorem growingQuantumWorld_exists : Nonempty GrowingQuantumWorld := by
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hs0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hs1 : (1 : ℝ) / 2 < 1 := by norm_num
  refine ⟨{
    r := 1 / 2
    s := 1 / 2
    hr0 := hr0
    hr1 := hr1
    hs0 := hs0
    hs1 := hs1
    rate_pos := ?_
    rate := tendsto_blockEntropy_div (rhoR (1 / 2) hr0 hr1)
    perStageSeal := ?_
    noncommutative := CNT.qDynamics_seal_no_common_canonical_masa }⟩
  · rw [vonNeumannEntropy_rhoR]
    exact Real.binEntropy_pos (by norm_num) (by norm_num)
  · intro n e _ _ α U hα hsecρ hsecσ
    exact quantum_seal_dephase_kron_faithful (1 / 2) hr0 hr1 (1 / 2) hs0 hs1
      (rhoPow (rhoR (1 / 2) hr0 hr1) n) (rhoPow_posDef _ (rhoR_posDef (1 / 2) hr0 hr1) n)
      α U hα hsecρ hsecσ

/-! ## The linear-growth face -/

/-- **The linear-growth law of a growing quantum world.**  The block entropy of the world's local
state grows exactly linearly: `blockEntropy ρ_r n = n · S(ρ_r)`. -/
theorem GrowingQuantumWorld.blockEntropy_linear (W : GrowingQuantumWorld) (n : ℕ) :
    blockEntropy (rhoR W.r W.hr0 W.hr1) n = n * vonNeumannEntropy (rhoR W.r W.hr0 W.hr1) :=
  blockEntropy_eq (rhoR W.r W.hr0 W.hr1) n

end ErgodicTheory.OperatorEntropy
