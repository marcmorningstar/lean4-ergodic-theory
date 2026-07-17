/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.GrowingTower.Tower
import ErgodicTheory.OperatorEntropy.GrowingTower.World
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityIntertwine
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualitySufficiency
import ErgodicTheory.OperatorEntropy.QuantumSeal

/-!
# The finite modular clock of the qubit chain (issue #71, tier 4 — finite shadow)

For a faithful (positive-definite) density matrix `ρ` we form the **modular automorphism group**
`σ_t(a) = ρ^{it} a ρ^{-it}` (`modAut`), built from the unitary power `ρ^{it}` (`upow`) of the
Tomita–Takesaki / Petz-equality infrastructure.  This is the finite-dimensional shadow of the
type-III modular flow of the qubit chain: a one-parameter `*`-automorphism group of the matrix
algebra that is **compatible with the chain embedding** (`modAut_shiftAdjoinQubit`, via
`upow_kron`) and satisfies the `β = 1` **KMS boundary identity** (`kms_boundary`).

## Contents

* `modAut`, `modAut_zero`, `modAut_add`, `modAut_mul`, `modAut_one`, `modAut_star`: the group and
  `*`-homomorphism laws of `σ_t`.
* `kms_boundary`: the `β = 1` KMS boundary identity `tr(ρ x σ_{-i}(y)) = tr(ρ y x)`.
* `modAut_shiftAdjoinQubit`: the intrinsic clock is consistent along the tower.
* **The intrinsic-clock dichotomy** — the headline making tier 4 non-vacuous:
  * `modAut_maximallyMixed_eq_id` (and `modAut_maximallyMixed_Qbits_eq_id`): the tracial
    (maximally mixed) state has **trivial** modular flow at every level of the chain;
  * `modAut_diagState_ne_id`: a non-tracial faithful product state (Powers-type, `diagState s`)
    has a **provably nontrivial** modular flow at the base qubit;
  * `modAut_rhoPow_diagState_ne_id`: that nontriviality holds at **every** level `n ≥ 1` of the
    tower, via the deep-end companion law `modAut_kron_one_left`.

## Disclosures (honest scope)

* `kms_boundary` on its own is *trace cyclicity* and holds for **every invertible** `ρ`; it is the
  boundary form of the KMS condition.  The modular-theoretic content of this module lives in the
  **dichotomy** and in the group / tower-compatibility laws, not in that identity alone.
* Not delivered here: the Tomita–Takesaki **uniqueness** of the KMS one-parameter group, and the
  genuine type-III modular theory of the completed C*-chain (GNS is Mathlib-absent).  This module
  is the finite matrix-algebra shadow of that theory.
* Nontriviality at level `n ≥ 1` is proved in `modAut_rhoPow_diagState_ne_id`, exposing the
  base-factor flow on the deep-end block `a ⊗ 1` via `modAut_kron_one_left`.

## Sources

* Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics II*, §5.3 (Prop. 5.3.7);
* Ohya–Petz, *Quantum Entropy and Its Use*, §1.3;
* R. T. Powers, *Representations of uniformly hyperfinite algebras and their associated von Neumann
  rings*, Ann. of Math. **86** (1967), for the non-tracial product-state (type-III) factors.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

open Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The modular automorphism group `σ_t(a) = ρ^{it} a ρ^{-it}` -/

/-- The **modular automorphism** `σ_t(a) = ρ^{it} a ρ^{-it}` of a faithful (positive-definite)
density matrix `ρ`, built from the unitary power `ρ^{it}` (`upow`). -/
def modAut {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (t : ℝ) (a : Matrix n n ℂ) : Matrix n n ℂ :=
  upow hρ t * a * upow hρ (-t)

/-- `σ_0 = id`. -/
theorem modAut_zero {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (a : Matrix n n ℂ) :
    modAut hρ 0 a = a := by
  simp only [modAut, upow_zero, neg_zero, one_mul, mul_one]

/-- **The one-parameter group law** `σ_s ∘ σ_t = σ_{s+t}`. -/
theorem modAut_add {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (s t : ℝ) (a : Matrix n n ℂ) :
    modAut hρ s (modAut hρ t a) = modAut hρ (s + t) a := by
  simp only [modAut]
  have e1 : upow hρ s * (upow hρ t * a * upow hρ (-t)) * upow hρ (-s)
      = upow hρ s * upow hρ t * a * (upow hρ (-t) * upow hρ (-s)) := by noncomm_ring
  have e2 : -t + -s = -(s + t) := by ring
  rw [e1, upow_add, upow_add, e2]

/-- **Multiplicativity** `σ_t(a b) = σ_t(a) σ_t(b)`. -/
theorem modAut_mul {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (t : ℝ) (a b : Matrix n n ℂ) :
    modAut hρ t (a * b) = modAut hρ t a * modAut hρ t b := by
  have hmid : upow hρ (-t) * upow hρ t = 1 := by
    rw [upow_add, neg_add_cancel, upow_zero]
  simp only [modAut]
  have e1 : upow hρ t * a * upow hρ (-t) * (upow hρ t * b * upow hρ (-t))
      = upow hρ t * a * (upow hρ (-t) * upow hρ t) * b * upow hρ (-t) := by noncomm_ring
  rw [e1, hmid, mul_one]
  noncomm_ring

/-- `σ_t(1) = 1`. -/
theorem modAut_one {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (t : ℝ) :
    modAut hρ t 1 = 1 := by
  simp only [modAut, mul_one, upow_mul_upow_neg]

/-- **Compatibility with the adjoint** `σ_t(aᴴ) = σ_t(a)ᴴ`. -/
theorem modAut_star {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (t : ℝ) (a : Matrix n n ℂ) :
    modAut hρ t (star a) = star (modAut hρ t a) := by
  simp only [modAut, star_mul, star_upow, neg_neg, mul_assoc]

/-! ## The `β = 1` KMS boundary identity -/

/-- **The `β = 1` KMS boundary identity** `tr(ρ · x · σ_{-i}(y)) = tr(ρ · y · x)`, where in the
Bratteli–Robinson II §5.3 convention `σ_{-i}(y) = ρ y ρ⁻¹`.

**Disclosure.** This identity is nothing more than trace cyclicity together with `ρ ρ⁻¹ = 1`, so it
holds for *every* invertible `ρ` — it is the boundary form of the KMS condition, not the substance
of modular theory.  The modular-theoretic content of this module is the intrinsic-clock dichotomy
(`modAut_maximallyMixed_eq_id` vs. `modAut_diagState_ne_id`) and the group / tower-compatibility
laws, not this identity in isolation. -/
theorem kms_boundary {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (x y : Matrix n n ℂ) :
    (ρ * (x * (ρ * y * ρ⁻¹))).trace = (ρ * (y * x)).trace := by
  have hu : IsUnit ρ.det := (Matrix.isUnit_iff_isUnit_det ρ).mp hρ.isUnit
  have hli : ρ⁻¹ * ρ = 1 := Matrix.nonsing_inv_mul ρ hu
  have e1 : ρ * (x * (ρ * y * ρ⁻¹)) = ρ * x * ρ * y * ρ⁻¹ := by noncomm_ring
  rw [e1, Matrix.trace_mul_comm (ρ * x * ρ * y) ρ⁻¹]
  have e2 : ρ⁻¹ * (ρ * x * ρ * y) = ρ⁻¹ * ρ * (x * (ρ * y)) := by noncomm_ring
  rw [e2, hli, one_mul, Matrix.trace_mul_comm x (ρ * y)]
  have e3 : ρ * y * x = ρ * (y * x) := by noncomm_ring
  rw [e3]

/-! ## Compatibility with the chain embedding -/

set_option maxHeartbeats 1000000 in
-- Kronecker-product defeq unification of the factor `Fintype`/`DecidableEq` instances is costly.
/-- On a factorized carrier `p × q`, the modular flow of a Kronecker product state acts on the
embedded block `1 ⊗ a` by the second factor's modular flow: `σ_t(1 ⊗ a) = 1 ⊗ σ_t(a)`, because the
first factor `A^{it}` cancels against `A^{-it}` (via `upow_kron`). -/
private theorem modAut_kron_one {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] {A : Matrix p p ℂ} {B : Matrix q q ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (A ⊗ₖ B).PosDef) (t : ℝ) (a : Matrix q q ℂ) :
    modAut hAB t (1 ⊗ₖ a) = 1 ⊗ₖ modAut hB t a := by
  simp only [modAut]
  rw [upow_kron hA hB hAB t, upow_kron hA hB hAB (-t), mul_assoc,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  congr 1
  · rw [one_mul, upow_mul_upow_neg]
  · rw [← mul_assoc]

set_option maxHeartbeats 1000000 in
-- Kronecker-product defeq unification of the factor `Fintype`/`DecidableEq` instances is costly.
/-- On a factorized carrier `p × q`, the modular flow of a Kronecker product state acts on the
embedded block `a ⊗ 1` by the first factor's modular flow: `σ_t(a ⊗ 1) = σ_t(a) ⊗ 1`, because the
second factor `B^{it}` cancels against `B^{-it}` (via `upow_kron`).  This is the deep-end companion
of `modAut_kron_one`; it exposes the base-factor flow, which is where the Powers-state
nontriviality lives. -/
private theorem modAut_kron_one_left {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] {A : Matrix p p ℂ} {B : Matrix q q ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (A ⊗ₖ B).PosDef) (t : ℝ) (a : Matrix p p ℂ) :
    modAut hAB t (a ⊗ₖ 1) = modAut hA t a ⊗ₖ 1 := by
  simp only [modAut]
  rw [upow_kron hA hB hAB t, upow_kron hA hB hAB (-t), mul_assoc,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  congr 1
  · rw [← mul_assoc]
  · rw [one_mul, upow_mul_upow_neg]

set_option maxHeartbeats 1000000 in
-- Closing by defeq forces reduction of `Qbits (n+1)` to `Fin 2 × Qbits n` and its instances.
/-- **Tower compatibility.** The intrinsic clock is consistent along the chain: on the embedded
block `1 ⊗ a`, the modular flow of the `(n+1)`-fold product state acts by the modular flow of the
`n`-fold state on `a` (via `upow_kron`, since `ρ^{it}` acts trivially on the fresh qubit). -/
theorem modAut_shiftAdjoinQubit (ρ : DensityMatrix (Fin 2)) (hρ : ρ.val.PosDef)
    (n : ℕ) (t : ℝ) (a : Matrix (Qbits n) (Qbits n) ℂ) :
    modAut (rhoPow_posDef ρ hρ (n + 1)) t (shiftAdjoinQubit a)
      = shiftAdjoinQubit (modAut (rhoPow_posDef ρ hρ n) t a) :=
  modAut_kron_one hρ (rhoPow_posDef ρ hρ n) (rhoPow_posDef ρ hρ (n + 1)) t a

/-! ## The intrinsic-clock dichotomy — the tracial half -/

/-- The unitary power of the maximally mixed state is a scalar (a constant diagonal): all its
eigenvalues coincide, so `(c • 1)^{it}` is central. -/
theorem upow_maximallyMixed [Nonempty n] (t : ℝ) :
    upow (DensityMatrix.maximallyMixed_posDef (n := n)) t
      = diagonal (fun _ : n => Complex.exp
          (((t : ℂ) * Complex.I) * (Real.log ((Fintype.card n : ℝ)⁻¹) : ℂ))) := by
  have hmm : (DensityMatrix.maximallyMixed : DensityMatrix n).val
      = diagonal (fun _ : n => (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ)) := by
    change ((Fintype.card n : ℝ)⁻¹ : ℝ) • (1 : Matrix n n ℂ) = _
    ext i j
    rw [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, Complex.real_smul]
    split_ifs <;> simp
  have hW1 : star (1 : Matrix n n ℂ) * 1 = 1 := by rw [star_one, one_mul]
  have hW2 : (1 : Matrix n n ℂ) * star 1 = 1 := by rw [star_one, mul_one]
  have hval : (DensityMatrix.maximallyMixed : DensityMatrix n).val
      = 1 * diagonal (fun _ : n => (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ))
        * star (1 : Matrix n n ℂ) := by
    rw [hmm, star_one, mul_one, one_mul]
  rw [upow_conj_diag (W := (1 : Matrix n n ℂ)) (d := fun _ : n => (Fintype.card n : ℝ)⁻¹)
      (DensityMatrix.maximallyMixed_posDef (n := n)) t hW1 hW2 hval, star_one, one_mul, mul_one]

/-- **The tracial half of the dichotomy.** The maximally mixed (tracial) state has **trivial**
modular flow: `σ_t = id` for all `t`, because `ρ = c • 1` is central so `ρ^{it}` is a scalar. -/
theorem modAut_maximallyMixed_eq_id [Nonempty n] (t : ℝ) (a : Matrix n n ℂ) :
    modAut (DensityMatrix.maximallyMixed_posDef (n := n)) t a = a := by
  have hcomm : upow (DensityMatrix.maximallyMixed_posDef (n := n)) t * a
      = a * upow (DensityMatrix.maximallyMixed_posDef (n := n)) t := by
    rw [upow_maximallyMixed]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  simp only [modAut]
  rw [hcomm, mul_assoc, upow_mul_upow_neg, mul_one]

/-- **The tracial chain state has trivial modular flow at every level.** This is
`modAut_maximallyMixed_eq_id` at the carrier `Qbits n`: the maximally mixed state on the length-`n`
block (the tracial state of the tower) is a fixed point of the whole modular group. -/
theorem modAut_maximallyMixed_Qbits_eq_id (n : ℕ) (t : ℝ) (a : Matrix (Qbits n) (Qbits n) ℂ) :
    modAut (DensityMatrix.maximallyMixed_posDef (n := Qbits n)) t a = a :=
  modAut_maximallyMixed_eq_id t a

/-! ## The intrinsic-clock dichotomy — the non-tracial (Powers-type) half -/

/-- The unitary power of the diagonal Powers state `diagState s = diag((1+s)/2, (1-s)/2)`. -/
theorem upow_diagState (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (t : ℝ) :
    upow (diagState_posDef s hs0 hs1) t
      = diagonal (fun i : Fin 2 => Complex.exp
          (((t : ℂ) * Complex.I) * (Real.log (![(1 + s) / 2, (1 - s) / 2] i) : ℂ))) := by
  have hW1 : star (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 = 1 := by rw [star_one, one_mul]
  have hW2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) * star 1 = 1 := by rw [star_one, mul_one]
  have hval : (diagState s hs0 hs1).val
      = 1 * diagonal (fun i : Fin 2 => ((![(1 + s) / 2, (1 - s) / 2] i : ℝ) : ℂ))
        * star (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [star_one, one_mul, mul_one]
    rfl
  rw [upow_conj_diag (W := (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (d := fun i : Fin 2 => ![(1 + s) / 2, (1 - s) / 2] i)
      (diagState_posDef s hs0 hs1) t hW1 hW2 hval, star_one, one_mul, mul_one]

/-- The modular flow of the Powers state on the off-diagonal unit `E₀₁` multiplies it by the phase
`exp(it · log((1+s)/(1-s)))`.  This phase is not identically `1`, which is the source of the
nontriviality. -/
theorem modAut_diagState_single (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (t : ℝ) :
    modAut (diagState_posDef s hs0 hs1) t (Matrix.single 0 1 1)
      = Complex.exp ((t : ℂ) * Complex.I * (Real.log ((1 + s) / (1 - s)) : ℂ))
        • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  ext i j
  simp only [modAut]
  rw [upow_diagState s hs0 hs1 t, upow_diagState s hs0 hs1 (-t),
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    rw [← Complex.exp_add]
    congr 1
    have ha1 : ((1 : ℝ) + s) / 2 ≠ 0 := ne_of_gt (by linarith)
    have ha2 : ((1 : ℝ) - s) / 2 ≠ 0 := ne_of_gt (by linarith)
    have h1s : (1 : ℝ) - s ≠ 0 := ne_of_gt (by linarith)
    have hdiff : Real.log ((1 + s) / 2) - Real.log ((1 - s) / 2)
        = Real.log ((1 + s) / (1 - s)) := by
      rw [← Real.log_div ha1 ha2]
      congr 1
      field_simp
    rw [← hdiff]
    push_cast
    ring
  · simp only [mul_zero, zero_mul]

/-- **The non-tracial half of the dichotomy.** A faithful non-tracial (Powers-type) product state
`diagState s` (`0 < s < 1`) has a **nontrivial** modular flow: the modular group is not the trivial
action.  Concretely, at `t₀ = π / log((1+s)/(1-s))` the flow sends the off-diagonal unit `E₀₁` to
`-E₀₁`.  This is the finite shadow of the type-III character of the Powers factors. -/
theorem modAut_diagState_ne_id (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ¬ ∀ (t : ℝ) (a : Matrix (Fin 2) (Fin 2) ℂ),
        modAut (diagState_posDef s hs0 hs1) t a = a := by
  intro h
  have hL : 0 < Real.log ((1 + s) / (1 - s)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith)]
    linarith
  set t₀ : ℝ := Real.pi / Real.log ((1 + s) / (1 - s)) with ht₀
  have hscalar : Complex.exp ((t₀ : ℂ) * Complex.I * (Real.log ((1 + s) / (1 - s)) : ℂ)) = -1 := by
    have hLc : (Real.log ((1 + s) / (1 - s)) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
    have heq : (t₀ : ℂ) * Complex.I * (Real.log ((1 + s) / (1 - s)) : ℂ)
        = (Real.pi : ℂ) * Complex.I := by
      rw [ht₀]
      push_cast
      field_simp
    rw [heq, Complex.exp_pi_mul_I]
  have hne := h t₀ (Matrix.single 0 1 1)
  rw [modAut_diagState_single s hs0 hs1 t₀, hscalar] at hne
  have h01 := congrFun (congrFun hne 0) 1
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.single_apply_same] at h01
  norm_num at h01

/-- **The non-tracial clock is nontrivial at every level of the tower.** The `n`-fold product state
`(diagState s)^{⊗ n}` (`0 < s < 1`, `n ≥ 1`) has a **nontrivial** modular flow at the length-`n`
block: the base-factor nontriviality (`modAut_diagState_ne_id`) is exposed on the deep-end block
`a ⊗ 1` via `modAut_kron_one_left`.  Descending the fresh (`rhoPow ρ (n-1)`) factor by injectivity
of `· ⊗ 1` reduces triviality at level `n` to triviality at the base qubit, which is impossible. -/
theorem modAut_rhoPow_diagState_ne_id (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {n : ℕ} (hn : 1 ≤ n) :
    ¬ ∀ (t : ℝ) (a : Matrix (Qbits n) (Qbits n) ℂ),
      modAut (rhoPow_posDef (diagState s hs0 hs1) (diagState_posDef s hs0 hs1) n) t a = a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro H
  refine modAut_diagState_ne_id s hs0 hs1 (fun t a => ?_)
  have hinj : ∀ {X Y : Matrix (Fin 2) (Fin 2) ℂ},
      X ⊗ₖ (1 : Matrix (Qbits m) (Qbits m) ℂ) = Y ⊗ₖ 1 → X = Y := by
    intro X Y hXY
    ext i j
    have hij := congrFun (congrFun hXY (i, Classical.arbitrary (Qbits m)))
      (j, Classical.arbitrary (Qbits m))
    simpa only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one] using hij
  have hHval := H t (a ⊗ₖ (1 : Matrix (Qbits m) (Qbits m) ℂ))
  have hcomb : modAut (diagState_posDef s hs0 hs1) t a ⊗ₖ (1 : Matrix (Qbits m) (Qbits m) ℂ)
      = a ⊗ₖ 1 := by
    rw [← modAut_kron_one_left (diagState_posDef s hs0 hs1)
      (rhoPow_posDef (diagState s hs0 hs1) (diagState_posDef s hs0 hs1) m)
      (rhoPow_posDef (diagState s hs0 hs1) (diagState_posDef s hs0 hs1) (m + 1)) t a]
    exact hHval
  exact hinj hcomb

end ErgodicTheory.OperatorEntropy

end
