/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Additivity
import ErgodicTheory.OperatorEntropy.EntropyPure
import ErgodicTheory.OperatorEntropy.EntropyStrictPos
import ErgodicTheory.OperatorEntropy.QuantumSeal
import ErgodicTheory.OperatorEntropy.Subadditivity
import ErgodicTheory.OperatorEntropy.StinespringReduction
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The growing-finite qubit tower and its per-step entropy rate

This module bundles the finite qubit blocks `M₂ ↪ M₄ ↪ M₈ ↪ ⋯` into a **growing tower**: at
step `n` the carrier is the `n`-fold qubit index `Qbits n` (of cardinality `2 ^ n`), and the
distinguished state is the product `ρ^{⊗ n}` of a fixed single-qubit state `ρ`.  Each step
**enlarges the capacity** by adjoining one fresh qubit (`shiftAdjoinQubit`, the embedding
`M_{2^n} ↪ M_{2^{n+1}}`, `A ↦ 1 ⊗ A`), and the family is an honest consistent family of finite
marginals: tracing out the fresh qubit recovers the previous block
(`rhoPow_partialTraceLeft`).

The main quantitative law is the exact block-entropy identity

`blockEntropy ρ n = n · S(ρ)`     (`blockEntropy_eq`),

an immediate consequence of additivity of the von Neumann entropy under the tensor product
(`vonNeumannEntropy_additive_kronecker`).  From it:

* the per-step (spatial) rate converges: `blockEntropy ρ n / n → S(ρ)`
  (`tendsto_blockEntropy_div`), as an eventually-constant sequence;
* at the maximally mixed single-qubit state the law reads `blockEntropy = n · log 2`
  (`blockEntropy_maximallyMixed`) — this is exactly issue #70's `n · log 2` claim, holding here
  as an *equality* at the maximally mixed state (where `S(ρ) = log 2` is maximal; for a general
  `ρ` the honest law is `n · S(ρ) ≤ n · log 2`);
* whenever `ρ` is not a pure state the rate is a *positive* constant (`blockEntropy_pos`,
  `blockEntropy_rate_pos`), instantiated on the concrete faithful family `ρ_r`
  (`blockEntropy_rhoR_pos`).

## Scope and provenance

This is deliberately **not** the completed (thermodynamic-limit) spin chain `⊗_{ℤ} M₂`; it is the
*growing-finite* tower, and the rate above is a **spatial / per-step** growth rate (one fresh
qubit per step).  It is complementary to — and consistent with — the *temporal* fixed-dimension
statement `cntDynamicalEntropy_eq_zero` elsewhere in this cluster: there the algebra is fixed and
the dynamics trivial, so the temporal rate vanishes; here the algebra grows and the spatial rate
is `S(ρ)`.

The standard ingredient (additivity of von Neumann entropy under tensor products, hence
`S(ρ^{⊗n}) = n · S(ρ)`) is textbook (Nielsen–Chuang, *Quantum Computation and Quantum
Information*, §11.3; Ohya–Petz, *Quantum Entropy and Its Use*).  The new content here is the
tower bundling — the growing carrier `Qbits`, the capacity-enlargement embedding
`shiftAdjoinQubit`, the marginal-consistency `rhoPow_partialTraceLeft`, and the packaged rate.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## The growing carrier `Qbits n` (`card = 2 ^ n`) -/

/-- Carrier index of the length-`n` qubit block; its cardinality is `2 ^ n`. -/
def Qbits : ℕ → Type
  | 0 => Fin 1
  | (n + 1) => Fin 2 × Qbits n

instance instFintypeQbits : (n : ℕ) → Fintype (Qbits n)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | (n + 1) => @instFintypeProd _ _ inferInstance (instFintypeQbits n)

instance instDecEqQbits : (n : ℕ) → DecidableEq (Qbits n)
  | 0 => inferInstanceAs (DecidableEq (Fin 1))
  | (n + 1) =>
      have := instDecEqQbits n
      inferInstanceAs (DecidableEq (Fin 2 × Qbits n))

instance instNonemptyQbits : (n : ℕ) → Nonempty (Qbits n)
  | 0 => inferInstanceAs (Nonempty (Fin 1))
  | (n + 1) =>
      have := instNonemptyQbits n
      inferInstanceAs (Nonempty (Fin 2 × Qbits n))

/-- The length-`n` qubit block has cardinality `2 ^ n`. -/
theorem card_Qbits (n : ℕ) : Fintype.card (Qbits n) = 2 ^ n := by
  induction n with
  | zero => simp [Qbits]
  | succ k ih =>
      have : Fintype.card (Qbits (k + 1)) = Fintype.card (Fin 2) * Fintype.card (Qbits k) :=
        Fintype.card_prod (Fin 2) (Qbits k)
      rw [this, ih, Fintype.card_fin, pow_succ]
      ring

/-! ## The product state `ρ^{⊗ n}` and its block entropy -/

/-- The `n`-fold product state `ρ^{⊗ n}` on the length-`n` block; the base case is the unique
state on `Fin 1` (which carries zero entropy). -/
noncomputable def rhoPow (ρ : DensityMatrix (Fin 2)) : (n : ℕ) → DensityMatrix (Qbits n)
  | 0 => DensityMatrix.maximallyMixed
  | (n + 1) => ρ.kron (rhoPow ρ n)

/-- The von Neumann entropy of the length-`n` block `ρ^{⊗ n}`. -/
noncomputable def blockEntropy (ρ : DensityMatrix (Fin 2)) (n : ℕ) : ℝ :=
  vonNeumannEntropy (rhoPow ρ n)

/-- **The block-entropy law.** `blockEntropy ρ n = n · S(ρ)`: entropy is additive under the
tensor product, so the `n`-fold product state carries `n` times the single-qubit entropy. -/
theorem blockEntropy_eq (ρ : DensityMatrix (Fin 2)) (n : ℕ) :
    blockEntropy ρ n = n * vonNeumannEntropy ρ := by
  induction n with
  | zero =>
      simp only [blockEntropy, rhoPow, Nat.cast_zero, zero_mul]
      rw [vonNeumannEntropy_maximallyMixed, card_Qbits, pow_zero, Nat.cast_one, Real.log_one]
  | succ k ih =>
      have hstep : blockEntropy ρ (k + 1) = vonNeumannEntropy ρ + blockEntropy ρ k :=
        vonNeumannEntropy_additive_kronecker ρ (rhoPow ρ k)
      rw [hstep, ih, Nat.cast_succ]
      ring

/-! ## Capacity enlargement: the embedding `M_{2^n} ↪ M_{2^{n+1}}` -/

/-- The capacity-enlargement step embedding `M_{2^n} ↪ M_{2^{n+1}}` by adjoining a fresh qubit
on the left: `A ↦ 1 ⊗ A`. -/
def shiftAdjoinQubit {n : ℕ} (M : Matrix (Qbits n) (Qbits n) ℂ) :
    Matrix (Qbits (n + 1)) (Qbits (n + 1)) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ M

/-- The embedding maps the identity to the identity. -/
theorem shiftAdjoinQubit_one (n : ℕ) :
    shiftAdjoinQubit (1 : Matrix (Qbits n) (Qbits n) ℂ) = 1 := by
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Qbits n) (Qbits n) ℂ) = 1 :=
    Matrix.one_kronecker_one
  exact h

/-- The embedding is multiplicative. -/
theorem shiftAdjoinQubit_mul {n : ℕ} (M N : Matrix (Qbits n) (Qbits n) ℂ) :
    shiftAdjoinQubit (M * N) = shiftAdjoinQubit M * shiftAdjoinQubit N := by
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (M * N)
      = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ M) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ N) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  exact h

/-- The embedding commutes with the conjugate transpose. -/
theorem shiftAdjoinQubit_star {n : ℕ} (M : Matrix (Qbits n) (Qbits n) ℂ) :
    (shiftAdjoinQubit M)ᴴ = shiftAdjoinQubit Mᴴ := by
  have h : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ M)ᴴ
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Mᴴ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  exact h

/-- The embedding is injective: `1 ⊗ M` determines `M` through the entry identity
`(1 ⊗ M) (i, a) (i, b) = M a b`. -/
theorem shiftAdjoinQubit_injective (n : ℕ) :
    Function.Injective (shiftAdjoinQubit (n := n)) := by
  intro M N h
  ext a b
  have hentry := congrFun (congrFun h ((0 : Fin 2), a)) ((0 : Fin 2), b)
  simpa only [shiftAdjoinQubit, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul]
    using hentry

/-! ## Marginal consistency (finite marginals form a consistent family) -/

/-- **Marginal compatibility of the tower.** Tracing out the fresh qubit of the length-`(n+1)`
block recovers the length-`n` block, so the `rhoPow ρ` family is an honest consistent family of
finite marginals. -/
theorem rhoPow_partialTraceLeft (ρ : DensityMatrix (Fin 2)) (n : ℕ) :
    (rhoPow ρ (n + 1)).partialTraceLeft = rhoPow ρ n := by
  rw [rhoPow, partialTraceLeft_kron]

/-! ## Positivity of the rate and a concrete witness -/

/-- **Positivity of the block entropy for a non-pure state.** If `ρ` is not idempotent
(`ρ² ≠ ρ`, i.e. `ρ` is a genuine mixture) then every nonempty block carries strictly positive
entropy. -/
theorem blockEntropy_pos (ρ : DensityMatrix (Fin 2)) (hρ : ρ.val * ρ.val ≠ ρ.val)
    {n : ℕ} (hn : 0 < n) : 0 < blockEntropy ρ n := by
  rw [blockEntropy_eq]
  have hS : 0 < vonNeumannEntropy ρ := vonNeumannEntropy_pos_of_sq_ne ρ hρ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos hnpos hS

/-- The concrete faithful family `ρ_r = ½!![1, r; r, 1]` (`0 < r < 1`) has strictly positive
block entropy on every nonempty block: its single-qubit entropy is the binary entropy
`h₂((1+r)/2) > 0`. -/
theorem blockEntropy_rhoR_pos (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {n : ℕ} (hn : 0 < n) :
    0 < blockEntropy (rhoR r hr0 hr1) n := by
  rw [blockEntropy_eq]
  have hp0 : 0 < (1 + r) / 2 := by linarith
  have hp1 : (1 + r) / 2 < 1 := by linarith
  have hS : 0 < vonNeumannEntropy (rhoR r hr0 hr1) := by
    rw [vonNeumannEntropy_rhoR]
    exact Real.binEntropy_pos hp0 hp1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos hnpos hS

/-! ## The maximally mixed corollary and the per-step rate -/

/-- At the maximally mixed single-qubit state the block-entropy law reads `n · log 2`, recovering
issue #70's `n · log 2` claim as an equality (the maximal case, where `S(ρ) = log 2`). -/
theorem blockEntropy_maximallyMixed (n : ℕ) :
    blockEntropy (DensityMatrix.maximallyMixed) n = n * Real.log 2 := by
  rw [blockEntropy_eq, vonNeumannEntropy_maximallyMixed, Fintype.card_fin, Nat.cast_ofNat]

/-- **The per-step (spatial) entropy rate.** `blockEntropy ρ n / n → S(ρ)`: the sequence is
eventually constant equal to `S(ρ)` (for `n ≥ 1`), hence converges to it. -/
theorem tendsto_blockEntropy_div (ρ : DensityMatrix (Fin 2)) :
    Filter.Tendsto (fun n => blockEntropy ρ n / n) Filter.atTop
      (nhds (vonNeumannEntropy ρ)) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [blockEntropy_eq, mul_comm, mul_div_assoc, div_self hn0, mul_one]

/-- **The rate is a positive constant for a non-pure state.** If `ρ` is not idempotent then the
per-step entropy rate `blockEntropy ρ n / n` converges to the *positive* constant `S(ρ)` — the
issue's liminf claim upgraded to an honest limit. -/
theorem blockEntropy_rate_pos (ρ : DensityMatrix (Fin 2)) (hρ : ρ.val * ρ.val ≠ ρ.val) :
    0 < vonNeumannEntropy ρ ∧
      Filter.Tendsto (fun n => blockEntropy ρ n / n) Filter.atTop
        (nhds (vonNeumannEntropy ρ)) :=
  ⟨vonNeumannEntropy_pos_of_sq_ne ρ hρ, tendsto_blockEntropy_div ρ⟩

end ErgodicTheory.OperatorEntropy
