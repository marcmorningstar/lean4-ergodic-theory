/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.PetzVecBridge
import ErgodicTheory.OperatorEntropy.Lieb.PetzKadison

/-!
# The abstract-channel Petz map as a contraction (issue #28, GENERAL case, PHASE 0)

For a general Kraus channel `Λ` with `ρ, σ, Λρ, Λσ` all faithful (`PosDef`), the **channel Petz
map** on the Hilbert–Schmidt space
`W_Λ(X) = Λ†(X · (Λρ)^{-1/2}) · ρ^{1/2}`
is a **contraction** (not an isometry): `‖W_Λ X‖ ≤ ‖X‖`.  This module builds the four matrix facts
of the contraction rigidity spine, replacing the isometry-based reconciliation
(`petzWvec` of `PetzVecBridge`) that only exists for the mixed-ancilla dilation:

* `petzWChan` / `petzWChanVec` (`vec_petzWChan`): the map and its vectorised matrix form.
* `petzWChanVec_contraction`: `Wᵥᴴ Wᵥ ≤ 1` (contraction, from Kadison–Schwarz).
* `petzWChan_cyclic` / `petzWChan_cyclic_norm`: `Wᵥ (vec (Λρ)^{1/2}) = vec ρ^{1/2}` and the
  norm-saturation of the contraction at the output cyclic vector.
* `petzWChanVec_modular_le`: the **weighted Kadison–Schwarz** Löwner inequality
  `Wᵥᴴ Δ_in Wᵥ ≤ Δ_out`, where `Δ_in = σ ⊗ₖ (ρ⁻¹)ᵀ` and `Δ_out = (Λσ) ⊗ₖ ((Λρ)⁻¹)ᵀ` are the
  input/output relative modular operators (in the `A ↦ a A b⁻¹` HS convention, matching
  `PetzReconciliation.modularMap` / `PetzVecBridge.modArgVec`).

## The mathematical core

Both the contraction (`Δ_in = Δ_out = 1`) and the modular inequality follow from a single **column
contraction** for the Kraus adjoint: with `∑ᵢ Kᵢᴴ Kᵢ = 1`,
`‖∑ᵢ aᵢ Kᵢ‖²_HS ≤ ∑ᵢ ‖aᵢ‖²_HS`  (`KrausChannel.column_contraction`),
proved by the manifestly-positive Gram identity `∑ᵢ (aᵢ − P Kᵢᴴ)ᴴ(aᵢ − P Kᵢᴴ) ⪰ 0` with
`P = ∑ᵢ aᵢ Kᵢ`.  The contraction is the special case `aᵢ = Kᵢᴴ Y`, `Y = X(Λρ)^{-1/2}` (the KMS
weight `ρ` being carried by the trace); the modular inequality is `aᵢ = σ^{1/2} Kᵢᴴ Y`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

open ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Hilbert–Schmidt inner product through `vec` -/

omit [Fintype n] [DecidableEq n] in
/-- `vec` commutes with finite sums (pointwise). -/
lemma vec_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix n n ℂ) :
    vec (∑ i ∈ s, M i) = ∑ i ∈ s, vec (M i) := by
  funext p
  simp only [vec_apply, Matrix.sum_apply, Finset.sum_apply]

/-! ## The Kraus column contraction (the Gram core) -/

/-- **Kraus column contraction.**  For a trace-preserving Kraus channel (`∑ᵢ Kᵢᴴ Kᵢ = 1`) and any
family `a : ι → Matrix n n ℂ`, the Hilbert–Schmidt norm contracts under the "isometric column"
`(Kᵢ)`:
`‖∑ᵢ aᵢ Kᵢ‖²_HS ≤ ∑ᵢ ‖aᵢ‖²_HS`.
This is the Gram-identity core from which both the Petz contraction and the weighted modular
inequality are read off. -/
theorem KrausChannel.column_contraction (Λ : KrausChannel n) (a : Λ.ι → Matrix n n ℂ) :
    ((∑ i, a i * Λ.K i)ᴴ * ∑ i, a i * Λ.K i).trace ≤ (∑ i, (a i)ᴴ * a i).trace := by
  set P := ∑ i, a i * Λ.K i with hP
  have hPadj : Pᴴ = ∑ i, (Λ.K i)ᴴ * (a i)ᴴ := by
    rw [hP, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_mul]
  -- The Gram identity at trace level.
  have hgram : (∑ i, (a i - P * (Λ.K i)ᴴ)ᴴ * (a i - P * (Λ.K i)ᴴ)).trace
      = (∑ i, (a i)ᴴ * a i).trace - (Pᴴ * P).trace := by
    have hexpand : ∀ i, (a i - P * (Λ.K i)ᴴ)ᴴ * (a i - P * (Λ.K i)ᴴ)
        = (a i)ᴴ * a i - (a i)ᴴ * P * (Λ.K i)ᴴ - Λ.K i * Pᴴ * a i
          + Λ.K i * (Pᴴ * P) * (Λ.K i)ᴴ := by
      intro i
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      noncomm_ring
    rw [Finset.sum_congr rfl fun i _ => hexpand i, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_sub]
    -- T2 = tr(Pᴴ P)
    have hT2 : (∑ i, (a i)ᴴ * P * (Λ.K i)ᴴ).trace = (Pᴴ * P).trace := by
      rw [Matrix.trace_sum]
      have : ∀ i, ((a i)ᴴ * P * (Λ.K i)ᴴ).trace = ((Λ.K i)ᴴ * (a i)ᴴ * P).trace := fun i => by
        rw [Matrix.trace_mul_cycle]
      simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul, ← hPadj]
    -- T3 = tr(Pᴴ P)
    have hT3 : (∑ i, Λ.K i * Pᴴ * a i).trace = (Pᴴ * P).trace := by
      rw [Matrix.trace_sum]
      have : ∀ i, (Λ.K i * Pᴴ * a i).trace = (Pᴴ * (a i * Λ.K i)).trace := fun i => by
        rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
      simp_rw [this, ← Matrix.trace_sum, ← Matrix.mul_sum, ← hP]
    -- T4 = tr(Pᴴ P)
    have hT4 : (∑ i, Λ.K i * (Pᴴ * P) * (Λ.K i)ᴴ).trace = (Pᴴ * P).trace := by
      rw [Matrix.trace_sum]
      have : ∀ i, (Λ.K i * (Pᴴ * P) * (Λ.K i)ᴴ).trace = ((Λ.K i)ᴴ * Λ.K i * (Pᴴ * P)).trace :=
        fun i => by rw [Matrix.trace_mul_cycle]
      simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul, Λ.htp, Matrix.one_mul]
    rw [hT2, hT3, hT4]
    ring
  have hpsd : (0 : ℂ) ≤ (∑ i, (a i - P * (Λ.K i)ᴴ)ᴴ * (a i - P * (Λ.K i)ᴴ)).trace :=
    (Matrix.posSemidef_sum _ fun i _ =>
      Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  rw [hgram] at hpsd
  exact sub_nonneg.mp hpsd

/-! ## The Heisenberg-adjoint trace pairing -/

/-- The trace pairing `tr(Λ† Z · ρ) = tr(Λρ · Z)`, i.e. `Λ†` is the HS adjoint of `Λ`. -/
theorem KrausChannel.trace_adj_mul (Λ : KrausChannel n) (Z W : Matrix n n ℂ) :
    (Λ.adj Z * W).trace = (Λ.toMat W * Z).trace := by
  unfold KrausChannel.adj KrausChannel.toMat
  rw [Matrix.sum_mul, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Λ.K i)ᴴ * Z * Λ.K i * W = (Λ.K i)ᴴ * (Z * (Λ.K i * W)) by noncomm_ring,
    Matrix.trace_mul_comm, show Z * (Λ.K i * W) * (Λ.K i)ᴴ = Z * (Λ.K i * W * (Λ.K i)ᴴ) by
      noncomm_ring, Matrix.trace_mul_comm, show Λ.K i * W * (Λ.K i)ᴴ * Z
        = Λ.K i * W * (Λ.K i)ᴴ * Z by noncomm_ring]

/-! ## The channel Petz map and its vectorisation -/

/-- The **channel Petz map** on the Hilbert–Schmidt space:
`W_Λ(X) = Λ†(X · (Λρ)^{-1/2}) · ρ^{1/2}`. -/
def petzWChan (Λ : KrausChannel n) (ρ : DensityMatrix n) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  Λ.adj (X * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ)) * ρ.val ^ (1 / 2 : ℝ)

/-- The **vectorised channel Petz map**: the matrix on the vec space `(n × n)` with
`vec (petzWChan Λ ρ X) = petzWChanVec Λ ρ *ᵥ vec X`.  It is the Kraus sum of Kronecker blocks
`Kᵢᴴ ⊗ₖ ((Λρ)^{-1/2} Kᵢ ρ^{1/2})ᵀ`. -/
def petzWChanVec (Λ : KrausChannel n) (ρ : DensityMatrix n) : Matrix (n × n) (n × n) ℂ :=
  ∑ i, (Λ.K i)ᴴ ⊗ₖ ((Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * Λ.K i * ρ.val ^ (1 / 2 : ℝ))ᵀ

/-- **Matricisation of the channel Petz map.**
`vec (petzWChan Λ ρ X) = petzWChanVec Λ ρ *ᵥ vec X`. -/
lemma vec_petzWChan (Λ : KrausChannel n) (ρ : DensityMatrix n) (X : Matrix n n ℂ) :
    vec (petzWChan Λ ρ X) = petzWChanVec Λ ρ *ᵥ vec X := by
  have key : petzWChan Λ ρ X
      = ∑ i, (Λ.K i)ᴴ * X
          * ((Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * Λ.K i * ρ.val ^ (1 / 2 : ℝ)) := by
    unfold petzWChan KrausChannel.adj
    rw [Matrix.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by noncomm_ring
  rw [key, petzWChanVec, Matrix.sum_mulVec, vec_sum]
  exact Finset.sum_congr rfl fun i _ => vec_mul_mul _ _ _

/-! ## The contraction (identity `(i)`) -/

/-- The Hilbert–Schmidt trace contraction of the channel Petz map:
`tr((W X)ᴴ (W X)) ≤ tr(Xᴴ X)`.  This is the Kadison–Schwarz contraction with the KMS weight `ρ`. -/
theorem petzWChan_trace_contraction (Λ : KrausChannel n) (ρ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hΛρ : (Λ.toDM ρ).val.PosDef) (X : Matrix n n ℂ) :
    ((petzWChan Λ ρ X)ᴴ * petzWChan Λ ρ X).trace ≤ (Xᴴ * X).trace := by
  set Y := X * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) with hY
  set r := ρ.val ^ (1 / 2 : ℝ) with hr
  set P := Λ.adj Y with hPdef
  have hrH : rᴴ = r := (CFC.rpow_nonneg (a := ρ.val) (y := (1 / 2 : ℝ))).posSemidef.1
  -- (W X)ᴴ (W X) = r Pᴴ P r
  have hWW : (petzWChan Λ ρ X)ᴴ * petzWChan Λ ρ X = r * (Pᴴ * P) * r := by
    unfold petzWChan
    rw [← hY, ← hr, ← hPdef, Matrix.conjTranspose_mul, hrH]
    noncomm_ring
  -- trace = tr(Pᴴ P ρ)
  have hrr : r * r = ρ.val := by
    rw [hr, ← CFC.rpow_add hρ.isUnit]; norm_num
    rw [CFC.rpow_one _ hρ.isStrictlyPositive.nonneg]
  have htrWW : ((petzWChan Λ ρ X)ᴴ * petzWChan Λ ρ X).trace = (Pᴴ * P * ρ.val).trace := by
    rw [hWW, Matrix.trace_mul_cycle, Matrix.trace_mul_comm, hrr]
  -- Kadison–Schwarz defect D ⪰ 0
  set D := Λ.adj (Yᴴ * Y) - Pᴴ * P with hD
  have hDpsd : D.PosSemidef := by
    rw [hD, hPdef, Λ.kadison_schwarz_eq Y]
    exact Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_conjTranspose_mul_self _
  -- tr(D ρ) ≥ 0
  have hDρ : (0 : ℂ) ≤ (D * ρ.val).trace := by
    have : (D * ρ.val).trace = (r * D * r).trace := by
      rw [← hrr, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    rw [this]
    have hpsd : (r * D * r).PosSemidef := by
      have := hDpsd.conjTranspose_mul_mul_same r
      rwa [hrH] at this
    exact hpsd.trace_nonneg
  -- tr(Pᴴ P ρ) = tr(Λ†(YᴴY) ρ) - tr(D ρ) ≤ tr(Λ†(YᴴY) ρ)
  have hsplit : (Pᴴ * P * ρ.val).trace = (Λ.adj (Yᴴ * Y) * ρ.val).trace - (D * ρ.val).trace := by
    rw [hD, sub_mul, Matrix.trace_sub]; ring
  -- tr(Λ†(YᴴY) ρ) = tr(Xᴴ X)
  have hfin : (Λ.adj (Yᴴ * Y) * ρ.val).trace = (Xᴴ * X).trace := by
    rw [KrausChannel.trace_adj_mul]
    -- tr(Λρ · YᴴY) with Y = X (Λρ)^{-1/2}
    have hsp := hΛρ.isStrictlyPositive
    have hsH : ((Λ.toDM ρ).val ^ (-(1 / 2) : ℝ))ᴴ = (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) :=
      (CFC.rpow_nonneg (a := (Λ.toDM ρ).val) (y := (-(1 / 2) : ℝ))).posSemidef.1
    -- `(Λρ)^{-1/2} · Λρ · (Λρ)^{-1/2} = 1`; split the *middle* factor `Λ.toMat ρ.val`
    -- (syntactically distinct from the `rpow` bases) to avoid rewriting the exponent bases.
    have hcollapse : (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * Λ.toMat ρ.val
        * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) = 1 := by
      have hmid : Λ.toMat ρ.val
          = (Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM ρ).val ^ (1 / 2 : ℝ) := by
        have hLtoMat : Λ.toMat ρ.val = (Λ.toDM ρ).val := rfl
        rw [hLtoMat, ← CFC.rpow_add hΛρ.isUnit]; norm_num
        rw [CFC.rpow_one _ hsp.nonneg]
      rw [hmid,
        show (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)
            * (Λ.toDM ρ).val ^ (1 / 2 : ℝ)) * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ)
          = ((Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * (Λ.toDM ρ).val ^ (1 / 2 : ℝ))
            * ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ)) by noncomm_ring,
        CFC.rpow_neg_mul_rpow (1 / 2) hsp, CFC.rpow_mul_rpow_neg (1 / 2) hsp, Matrix.one_mul]
    -- `YᴴY = (Λρ)^{-1/2} (XᴴX) (Λρ)^{-1/2}`
    have hYY : Yᴴ * Y
        = (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * (Xᴴ * X) * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) := by
      rw [hY, Matrix.conjTranspose_mul, hsH]; noncomm_ring
    rw [hYY,
      show Λ.toMat ρ.val * ((Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * (Xᴴ * X)
          * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ))
        = (Λ.toMat ρ.val * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * (Xᴴ * X))
          * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) by noncomm_ring,
      Matrix.trace_mul_comm,
      show (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ)
          * (Λ.toMat ρ.val * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * (Xᴴ * X))
        = ((Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) * Λ.toMat ρ.val * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ))
          * (Xᴴ * X) by noncomm_ring,
      hcollapse, Matrix.one_mul]
  rw [htrWW, hsplit]
  calc (Λ.adj (Yᴴ * Y) * ρ.val).trace - (D * ρ.val).trace
      ≤ (Λ.adj (Yᴴ * Y) * ρ.val).trace := sub_le_self _ hDρ
    _ = (Xᴴ * X).trace := hfin

/-- **Contraction (i): `Wᵥᴴ Wᵥ ≤ 1`.**  The vectorised channel Petz map is a contraction of the
Hilbert–Schmidt space (Kadison–Schwarz), replacing the isometry `petzWvec_isometry`. -/
theorem petzWChanVec_contraction (Λ : KrausChannel n) (ρ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hΛρ : (Λ.toDM ρ).val.PosDef) :
    (petzWChanVec Λ ρ)ᴴ * petzWChanVec Λ ρ ≤ 1 := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self _)) ?_
  intro x
  obtain ⟨X, rfl⟩ := vec_surjective x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← vec_petzWChan,
    vec_dotProduct_eq_trace, vec_dotProduct_eq_trace, sub_nonneg]
  exact petzWChan_trace_contraction Λ ρ hρ hΛρ X

/-! ## The output cyclic vector (identity `(ii)`) -/

/-- **Cyclic vector (ii): `Wᵥ (vec (Λρ)^{1/2}) = vec ρ^{1/2}`.**  The contraction carries the output
cyclic vector to the input cyclic vector, using unitality of `Λ†` on the faithful `Λρ`. -/
theorem petzWChan_cyclic (Λ : KrausChannel n) (ρ : DensityMatrix n)
    (hΛρ : (Λ.toDM ρ).val.PosDef) :
    petzWChanVec Λ ρ *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)) = vec (ρ.val ^ (1 / 2 : ℝ)) := by
  rw [← vec_petzWChan]
  have hcyc : petzWChan Λ ρ ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)) = ρ.val ^ (1 / 2 : ℝ) := by
    unfold petzWChan
    rw [CFC.rpow_mul_rpow_neg (1 / 2) hΛρ.isStrictlyPositive, Λ.adj_unital, Matrix.one_mul]
  rw [hcyc]

/-- **Norm-saturation of the contraction at the output cyclic vector.**  The contraction
`Wᵥᴴ Wᵥ ≤ 1` is saturated at the output cyclic vector `vec (Λρ)^{1/2}`:
`‖Wᵥ (vec (Λρ)^{1/2})‖² = ‖vec (Λρ)^{1/2}‖²` (both `= tr ρ = tr Λρ = 1`).  This is the
rigidity input: the cyclic vector is a fixed vector of `Wᵥᴴ Wᵥ`. -/
theorem petzWChan_cyclic_norm (Λ : KrausChannel n) (ρ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hΛρ : (Λ.toDM ρ).val.PosDef) :
    star (petzWChanVec Λ ρ *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
        ⬝ᵥ (petzWChanVec Λ ρ *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
      = star (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))) ⬝ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)) := by
  rw [petzWChan_cyclic Λ ρ hΛρ, vec_dotProduct_eq_trace, vec_dotProduct_eq_trace]
  have hsq : ∀ a : Matrix n n ℂ, a.PosDef → (a ^ (1 / 2 : ℝ))ᴴ * a ^ (1 / 2 : ℝ) = a := by
    intro a ha
    rw [(CFC.rpow_nonneg (a := a) (y := (1 / 2 : ℝ))).posSemidef.1, ← CFC.rpow_add ha.isUnit,
      show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, CFC.rpow_one _ ha.isStrictlyPositive.nonneg]
  rw [hsq ρ.val hρ, hsq (Λ.toDM ρ).val hΛρ, ρ.trace_one, (Λ.toDM ρ).trace_one]

/-! ## The weighted modular Löwner inequality (identity `(iii)`) -/

/-- `a^{-1} = a^{-1/2} · a^{-1/2}` for a positive-definite matrix. -/
private lemma rpow_negOne_split {a : Matrix n n ℂ} (ha : a.PosDef) :
    a ^ (-1 : ℝ) = a ^ (-(1 / 2) : ℝ) * a ^ (-(1 / 2) : ℝ) := by
  rw [show (-1 : ℝ) = (-(1 / 2) : ℝ) + (-(1 / 2) : ℝ) by norm_num, CFC.rpow_add ha.isUnit]

/-- **Weighted Kadison–Schwarz (trace form).**  The σ-weighted contraction of the channel Petz map:
`tr((W X)ᴴ σ (W X) ρ⁻¹) ≤ tr(Xᴴ (Λσ) X (Λρ)⁻¹)`.  This is the trace shadow of the modular Löwner
inequality, obtained from `KrausChannel.column_contraction` with `aᵢ = σ^{1/2} Kᵢᴴ Y`,
`Y = X (Λρ)^{-1/2}`. -/
theorem petzWChan_trace_modular (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) (hΛρ : (Λ.toDM ρ).val.PosDef) (X : Matrix n n ℂ) :
    ((petzWChan Λ ρ X)ᴴ * (σ.val * petzWChan Λ ρ X * ρ.val ^ (-1 : ℝ))).trace
      ≤ (Xᴴ * ((Λ.toDM σ).val * X * (Λ.toDM ρ).val ^ (-1 : ℝ))).trace := by
  set s := (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ) with hs
  set r := ρ.val ^ (1 / 2 : ℝ) with hr
  set t := σ.val ^ (1 / 2 : ℝ) with ht
  set Y := X * s with hY
  set P := Λ.adj Y with hPdef
  have hsH : sᴴ = s := (CFC.rpow_nonneg (a := (Λ.toDM ρ).val) (y := (-(1 / 2) : ℝ))).posSemidef.1
  have hrH : rᴴ = r := (CFC.rpow_nonneg (a := ρ.val) (y := (1 / 2 : ℝ))).posSemidef.1
  have htH : tᴴ = t := (CFC.rpow_nonneg (a := σ.val) (y := (1 / 2 : ℝ))).posSemidef.1
  have htt : t * t = σ.val := by
    rw [ht, ← CFC.rpow_add hσ.isUnit, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num,
      CFC.rpow_one _ hσ.isStrictlyPositive.nonneg]
  have hrnegr : r * ρ.val ^ (-1 : ℝ) * r = 1 := by
    rw [hr, rpow_negOne_split hρ,
      show ρ.val ^ (1 / 2 : ℝ) * (ρ.val ^ (-(1 / 2) : ℝ) * ρ.val ^ (-(1 / 2) : ℝ))
          * ρ.val ^ (1 / 2 : ℝ)
        = (ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ))
          * (ρ.val ^ (-(1 / 2) : ℝ) * ρ.val ^ (1 / 2 : ℝ)) by noncomm_ring,
      CFC.rpow_mul_rpow_neg (1 / 2) hρ.isStrictlyPositive,
      CFC.rpow_neg_mul_rpow (1 / 2) hρ.isStrictlyPositive, Matrix.one_mul]
  have hss : s * s = (Λ.toDM ρ).val ^ (-1 : ℝ) := by rw [hs]; exact (rpow_negOne_split hΛρ).symm
  have hWXeq : petzWChan Λ ρ X = P * r := rfl
  -- L1: LHS trace collapses (via r ρ⁻¹ r = 1) to tr(Pᴴ σ P)
  have hL1 : ((petzWChan Λ ρ X)ᴴ * (σ.val * petzWChan Λ ρ X * ρ.val ^ (-1 : ℝ))).trace
      = (Pᴴ * σ.val * P).trace := by
    rw [hWXeq, Matrix.conjTranspose_mul, hrH,
      show r * Pᴴ * (σ.val * (P * r) * ρ.val ^ (-1 : ℝ))
        = r * (Pᴴ * σ.val * P * r * ρ.val ^ (-1 : ℝ)) by noncomm_ring,
      Matrix.trace_mul_comm r (Pᴴ * σ.val * P * r * ρ.val ^ (-1 : ℝ)),
      show Pᴴ * σ.val * P * r * ρ.val ^ (-1 : ℝ) * r
        = Pᴴ * σ.val * P * (r * ρ.val ^ (-1 : ℝ) * r) by noncomm_ring, hrnegr, Matrix.mul_one]
  -- t·P = ∑ᵢ aᵢ Kᵢ with aᵢ = t Kᵢᴴ Y
  have htP : t * P = ∑ i, t * (Λ.K i)ᴴ * Y * Λ.K i := by
    rw [hPdef]
    unfold KrausChannel.adj
    rw [Matrix.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by noncomm_ring
  have hPσP : Pᴴ * σ.val * P = (t * P)ᴴ * (t * P) := by
    rw [Matrix.conjTranspose_mul, htH, ← htt]; noncomm_ring
  -- ∑ᵢ ‖aᵢ‖² = Yᴴ (Λσ) Y
  have hsumaa : (∑ i, (t * (Λ.K i)ᴴ * Y)ᴴ * (t * (Λ.K i)ᴴ * Y))
      = Yᴴ * (Λ.toDM σ).val * Y := by
    rw [show (Λ.toDM σ).val = ∑ i, Λ.K i * σ.val * (Λ.K i)ᴴ from rfl, Matrix.mul_sum,
      Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, htH]
    rw [← htt]; noncomm_ring
  -- the bound target trace = the output modular trace
  have hRHS : (∑ i, (t * (Λ.K i)ᴴ * Y)ᴴ * (t * (Λ.K i)ᴴ * Y)).trace
      = (Xᴴ * ((Λ.toDM σ).val * X * (Λ.toDM ρ).val ^ (-1 : ℝ))).trace := by
    rw [hsumaa, hY, Matrix.conjTranspose_mul, hsH,
      show s * Xᴴ * (Λ.toDM σ).val * (X * s) = s * (Xᴴ * (Λ.toDM σ).val * X * s) by noncomm_ring,
      Matrix.trace_mul_comm s (Xᴴ * (Λ.toDM σ).val * X * s),
      show Xᴴ * (Λ.toDM σ).val * X * s * s = Xᴴ * ((Λ.toDM σ).val * X * (s * s)) by noncomm_ring,
      hss]
  calc ((petzWChan Λ ρ X)ᴴ * (σ.val * petzWChan Λ ρ X * ρ.val ^ (-1 : ℝ))).trace
      = (Pᴴ * σ.val * P).trace := hL1
    _ = ((∑ i, t * (Λ.K i)ᴴ * Y * Λ.K i)ᴴ * ∑ i, t * (Λ.K i)ᴴ * Y * Λ.K i).trace := by
          rw [hPσP, htP]
    _ ≤ (∑ i, (t * (Λ.K i)ᴴ * Y)ᴴ * (t * (Λ.K i)ᴴ * Y)).trace :=
          KrausChannel.column_contraction Λ (fun i => t * (Λ.K i)ᴴ * Y)
    _ = (Xᴴ * ((Λ.toDM σ).val * X * (Λ.toDM ρ).val ^ (-1 : ℝ))).trace := hRHS

/-- **Modular Löwner inequality (iii): `Wᵥᴴ Δ_in Wᵥ ≤ Δ_out`.**  The weighted Kadison–Schwarz
compression of the input relative modular operator `Δ_in = σ ⊗ₖ (ρ⁻¹)ᵀ` (acting `A ↦ σ A ρ⁻¹`) is
dominated, in the Löwner order, by the output relative modular operator
`Δ_out = (Λσ) ⊗ₖ ((Λρ)⁻¹)ᵀ` (acting `X ↦ (Λσ) X (Λρ)⁻¹`).  This is the contraction analog of the
isometric compression `petzWvec_modular_compression`, and is the third input to the rigidity
spine. -/
theorem petzWChanVec_modular_le (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) (hΛρ : (Λ.toDM ρ).val.PosDef)
    (hΛσ : (Λ.toDM σ).val.PosDef) :
    (petzWChanVec Λ ρ)ᴴ * (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ) * petzWChanVec Λ ρ
      ≤ (Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ := by
  have hDin_pd : (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ).PosDef :=
    hσ.kronecker (IsStrictlyPositive.rpow ρ.val (-1) hρ.isStrictlyPositive).posDef.transpose
  have hDout_pd : ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ).PosDef :=
    hΛσ.kronecker
      (IsStrictlyPositive.rpow (Λ.toDM ρ).val (-1) hΛρ.isStrictlyPositive).posDef.transpose
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine hDout_pd.1.sub ?_
    change ((petzWChanVec Λ ρ)ᴴ * (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ) * petzWChanVec Λ ρ)ᴴ
      = (petzWChanVec Λ ρ)ᴴ * (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ) * petzWChanVec Λ ρ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hDin_pd.1.eq, ← Matrix.mul_assoc]
  · intro x
    obtain ⟨X, rfl⟩ := vec_surjective x
    rw [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg,
      ← vec_mul_mul, vec_dotProduct_eq_trace,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← vec_petzWChan, ← vec_mul_mul,
      Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← vec_petzWChan, vec_dotProduct_eq_trace]
    exact petzWChan_trace_modular Λ ρ σ hρ hσ hΛρ X

end ErgodicTheory.OperatorEntropy.Lieb

end

