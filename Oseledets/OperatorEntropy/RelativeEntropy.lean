/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.OperatorEntropy.Basic
import Oseledets.OperatorEntropy.Klein
import Oseledets.OperatorEntropy.Additivity
import Oseledets.OperatorEntropy.KroneckerSpectrum

/-!
# Issue #22 — Umegaki relative entropy: FEASIBLE foundations layer (verified skeleton)

This skeleton pins the EXACT statements of the feasible foundations layer of issue #22,
reusing #23's `Oseledets/OperatorEntropy/Klein.lean` (`klein_scalar`, `log_sub_bound`).

The headline keystone `relEntropy_nonneg` is a DIRECT application of `klein_scalar` — even
simpler than `vonNeumannEntropy_subadditive`, because it involves ONE change of basis between
ρ's and σ's eigenbases (no partial trace, no Kronecker).

WALL (documented, NOT attempted): `monotonicity_relEntropy_under_CPTP` / `petz_equality_recovery`
require Lieb concavity / joint convexity, which is Mathlib-absent (months-scale). Those are
localized into the explicit `IsRelEntropyMonotone` hypothesis of the consumer corollary.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Spectral data abbreviations -/

/-- Sorted real eigenvalues of a density matrix. -/
def DensityMatrix.eig (ρ : DensityMatrix n) : n → ℝ := ρ.posSemidef.1.eigenvalues

/-- The eigenvector unitary (its columns are the eigenvectors), as a plain matrix. -/
def DensityMatrix.eigVec (ρ : DensityMatrix n) : Matrix n n ℂ :=
  (ρ.posSemidef.1.eigenvectorUnitary : Matrix n n ℂ)

/-- The eigenbasis-overlap matrix `D k m = |⟨e_k(ρ) | f_m(σ)⟩|²`, where `e_k` are ρ's
eigenvectors and `f_m` are σ's.  Realized as `normSq` of `(ρ.eigVecᴴ σ.eigVec) k m`.
This is the doubly stochastic matrix fed to `klein_scalar`. -/
def crossOverlap (ρ σ : DensityMatrix n) (k m : n) : ℝ :=
  Complex.normSq ((star ρ.eigVec * σ.eigVec) k m)

/-! ## (1) The Umegaki relative entropy (spectral / overlap form) -/

/-- **Umegaki relative entropy** `D(ρ‖σ) = Tr ρ (log ρ − log σ)`, in spectral/overlap form:
`∑ₖ pₖ log pₖ − ∑ₖ,ₘ |⟨eₖ|fₘ⟩|² pₖ log qₘ` with `p, e` the eigenvalues/eigenvectors of ρ
and `q, f` those of σ.  This is `Tr ρ log ρ − Tr ρ log σ` expanded in the two eigenbases;
the first term is `−vonNeumannEntropy ρ` and the second is `Tr(ρ · log σ)`.

The spectral form is chosen because `relEntropy_nonneg` then falls directly out of
`klein_scalar` (the overlap matrix is doubly stochastic). It is total (defined for all ρ, σ;
with the Mathlib convention `log 0 = 0` the σ-singular columns contribute `0`). -/
def relEntropy (ρ σ : DensityMatrix n) : ℝ :=
  (∑ k, ρ.eig k * Real.log (ρ.eig k))
    - ∑ k, ∑ m, crossOverlap ρ σ k m * ρ.eig k * Real.log (σ.eig m)

/-- **Trace–spectral bridge (real part).**  Expanding both spectral decompositions, the trace
`Tr(ρ · f(τ))` (with `f(τ)` the Hermitian functional calculus of `τ` at `f`) is the real double
sum `∑ₖ,ₘ pₖ |⟨eₖ|gₘ⟩|² f(qₘ)` with `p, e` the eigendata of `ρ` and `q, g` that of `τ`.  This is
the workhorse identifying the spectral form of relative entropy with its trace form. -/
lemma trace_val_mul_cfc_re (ρ τ : DensityMatrix n) (f : ℝ → ℝ) :
    (ρ.val * τ.posSemidef.1.cfc f).trace.re
      = ∑ k, ∑ m, ρ.eig k * Complex.normSq ((star ρ.eigVec * τ.eigVec) k m) * f (τ.eig m) := by
  have hρ : ρ.val
      = ρ.eigVec * diagonal (fun k => (ρ.eig k : ℂ)) * star ρ.eigVec := by
    have h := ρ.posSemidef.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ ρ.posSemidef.1.eigenvalues) = fun k => (ρ.eig k : ℂ) := by
      funext k; rfl
    rw [hRC] at h
    exact h
  have hτ : τ.posSemidef.1.cfc f
      = τ.eigVec * diagonal (fun m => (f (τ.eig m) : ℂ)) * star τ.eigVec := by
    have h : τ.posSemidef.1.cfc f
        = (τ.posSemidef.1.eigenvectorUnitary : Matrix n n ℂ)
          * diagonal (RCLike.ofReal ∘ f ∘ τ.posSemidef.1.eigenvalues)
          * star (τ.posSemidef.1.eigenvectorUnitary : Matrix n n ℂ) := by
      simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    have hRC : (RCLike.ofReal ∘ f ∘ τ.posSemidef.1.eigenvalues)
        = fun m => (f (τ.eig m) : ℂ) := by funext m; rfl
    rw [hRC] at h
    exact h
  have hsQ : star (star ρ.eigVec * τ.eigVec) = star τ.eigVec * ρ.eigVec := by
    rw [star_mul, star_star]
  have e1 : ρ.val * τ.posSemidef.1.cfc f
      = ρ.eigVec * (diagonal (fun k => (ρ.eig k : ℂ)) * star ρ.eigVec * τ.posSemidef.1.cfc f) := by
    rw [hρ]; simp only [mul_assoc]
  have e2 : diagonal (fun k => (ρ.eig k : ℂ)) * star ρ.eigVec * τ.posSemidef.1.cfc f * ρ.eigVec
      = diagonal (fun k => (ρ.eig k : ℂ)) * (star ρ.eigVec * τ.posSemidef.1.cfc f * ρ.eigVec) := by
    simp only [mul_assoc]
  have e3 : star ρ.eigVec
        * (τ.eigVec * diagonal (fun m => (f (τ.eig m) : ℂ)) * star τ.eigVec) * ρ.eigVec
      = star ρ.eigVec * τ.eigVec * diagonal (fun m => (f (τ.eig m) : ℂ))
        * (star τ.eigVec * ρ.eigVec) := by
    simp only [mul_assoc]
  have htrace : (ρ.val * τ.posSemidef.1.cfc f).trace
      = ∑ k, ∑ m, (ρ.eig k : ℂ) * (Complex.normSq ((star ρ.eigVec * τ.eigVec) k m) : ℂ)
          * (f (τ.eig m) : ℂ) := by
    rw [e1, Matrix.trace_mul_comm, e2, hτ, e3, ← hsQ]
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hMkk : (star ρ.eigVec * τ.eigVec * diagonal (fun m => (f (τ.eig m) : ℂ))
          * star (star ρ.eigVec * τ.eigVec)) k k
        = ∑ m, (Complex.normSq ((star ρ.eigVec * τ.eigVec) k m) : ℂ) * (f (τ.eig m) : ℂ) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Matrix.mul_diagonal, Matrix.star_apply, Complex.star_def, mul_right_comm,
        Complex.mul_conj]
    simp only [Matrix.diagonal_mul]
    rw [hMkk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [htrace]
  have hcast : ∀ k m, (ρ.eig k : ℂ) * (Complex.normSq ((star ρ.eigVec * τ.eigVec) k m) : ℂ)
        * (f (τ.eig m) : ℂ)
      = ((ρ.eig k * Complex.normSq ((star ρ.eigVec * τ.eigVec) k m) * f (τ.eig m) : ℝ) : ℂ) := by
    intro k m; push_cast; ring
  simp only [hcast, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- **Unconditional trace decomposition.**  `D(ρ‖σ) = Tr(ρ log ρ) − Tr(ρ log σ)`, with the two
matrix logarithms supplied by the Hermitian functional calculus.  No faithfulness hypothesis is
needed (the `Real.log 0 = 0` convention makes both traces total). -/
private lemma relEntropy_eq_trace (ρ σ : DensityMatrix n) :
    relEntropy ρ σ
      = (ρ.val * ρ.posSemidef.1.cfc Real.log).trace.re
        - (ρ.val * σ.posSemidef.1.cfc Real.log).trace.re := by
  rw [trace_val_mul_cfc_re ρ ρ Real.log, trace_val_mul_cfc_re ρ σ Real.log]
  simp only [relEntropy]
  congr 1
  · have hρ1 : star ρ.eigVec * ρ.eigVec = 1 :=
      Unitary.coe_star_mul_self ρ.posSemidef.1.eigenvectorUnitary
    simp only [hρ1]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h0 : ∀ m ∈ Finset.univ, m ≠ k →
        ρ.eig k * Complex.normSq ((1 : Matrix n n ℂ) k m) * Real.log (ρ.eig m) = 0 := by
      intro m _ hmk
      rw [Matrix.one_apply_ne (Ne.symm hmk), Complex.normSq_zero, mul_zero, zero_mul]
    rw [Finset.sum_eq_single k h0 (fun hk => absurd (Finset.mem_univ k) hk),
      Matrix.one_apply_eq, Complex.normSq_one, mul_one]
  · simp only [crossOverlap]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    ring

/-- Recognizability bridge: the spectral form equals the trace form `Tr (ρ · (log ρ − log σ))`
built from the matrix logarithm via the Hermitian continuous functional calculus
`Matrix.IsHermitian.cfc Real.log` (purpose-built for matrices).  Provides the textbook
identification with the Umegaki definition `D(ρ‖σ) = Tr ρ (log ρ − log σ)`. -/
theorem relEntropy_eq_traceLog (ρ σ : DensityMatrix n) (_hσ : σ.val.PosDef) :
    relEntropy ρ σ
      = (ρ.val * (ρ.posSemidef.1.cfc Real.log - σ.posSemidef.1.cfc Real.log)).trace.re := by
  rw [relEntropy_eq_trace, mul_sub, Matrix.trace_sub, Complex.sub_re]

/-! ## (2) Klein nonnegativity — THE KEYSTONE -/

/-- **Klein's inequality / nonnegativity of relative entropy (Gibbs' inequality).**
`0 ≤ D(ρ‖σ)` for faithful σ.

PROOF (direct `klein_scalar` instantiation, `K = M = n`):
* `p = ρ.eig`, `s = σ.eig`, `D k m = crossOverlap ρ σ k m` with `Q := ρ.eigVecᴴ · σ.eigVec`,
  `D k m = normSq (Q k m)`.
* doubly stochastic: `Q · Qᴴ = ρ.eigVecᴴ (σ.eigVec σ.eigVecᴴ) ρ.eigVec = ρ.eigVecᴴ ρ.eigVec = 1`
  gives `hrow : ∑ₘ D k m = (Q Qᴴ) k k = 1`; symmetrically `Qᴴ Q = 1` gives `hcol : ∑ₖ D k m = 1`
  (exact clone of `Subadditivity.hrow/hcol`, the `Complex.mul_conj`/`normSq` pattern).
* `hsum`: `∑ p = ∑ s = 1` (unit trace).
* `hsupp`: VACUOUS because faithful σ ⇒ `σ.eig m > 0` for all m (`Matrix.PosDef.eigenvalues_pos`),
  so `s m = 0` never occurs. (This is the absolute-continuity / support hypothesis made honest.)
Then `klein_scalar` gives `∑ₖ,ₘ D k m pₖ log qₘ ≤ ∑ₖ pₖ log pₖ`, i.e. `0 ≤ relEntropy ρ σ`. -/
theorem relEntropy_nonneg (ρ σ : DensityMatrix n) (hσ : σ.val.PosDef) :
    0 ≤ relEntropy ρ σ := by
  set Q : Matrix n n ℂ := star ρ.eigVec * σ.eigVec with hQ_def
  simp only [relEntropy, crossOverlap, ← hQ_def]
  have hρss : star ρ.eigVec * ρ.eigVec = 1 :=
    Unitary.coe_star_mul_self ρ.posSemidef.1.eigenvectorUnitary
  have hρss' : ρ.eigVec * star ρ.eigVec = 1 :=
    Unitary.coe_mul_star_self ρ.posSemidef.1.eigenvectorUnitary
  have hσss : star σ.eigVec * σ.eigVec = 1 :=
    Unitary.coe_star_mul_self σ.posSemidef.1.eigenvectorUnitary
  have hσss' : σ.eigVec * star σ.eigVec = 1 :=
    Unitary.coe_mul_star_self σ.posSemidef.1.eigenvectorUnitary
  have hsQ : star Q = star σ.eigVec * ρ.eigVec := by
    rw [hQ_def, star_mul, star_star]
  have hQss' : Q * star Q = 1 := by
    rw [hsQ, hQ_def, mul_assoc, ← mul_assoc σ.eigVec, hσss', one_mul, hρss]
  have hQss : star Q * Q = 1 := by
    rw [hsQ, hQ_def, mul_assoc, ← mul_assoc ρ.eigVec, hρss', one_mul, hσss]
  have hp : ∀ k, 0 ≤ ρ.eig k := fun k => ρ.eigenvalues_nonneg k
  have hs : ∀ m, 0 ≤ σ.eig m := fun m => σ.eigenvalues_nonneg m
  have hD : ∀ k m, 0 ≤ Complex.normSq (Q k m) := fun k m => Complex.normSq_nonneg _
  have hrow : ∀ k, (∑ m, Complex.normSq (Q k m)) = 1 := by
    intro k
    have hc : ((∑ m, Complex.normSq (Q k m) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have he : (∑ m, ((Complex.normSq (Q k m) : ℝ) : ℂ)) = (Q * star Q) k k := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Matrix.star_apply, Complex.star_def, Complex.mul_conj]
      rw [he, hQss', Matrix.one_apply_eq]
    exact_mod_cast hc
  have hcol : ∀ m, (∑ k, Complex.normSq (Q k m)) = 1 := by
    intro m
    have hc : ((∑ k, Complex.normSq (Q k m) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have he : (∑ k, ((Complex.normSq (Q k m) : ℝ) : ℂ)) = (star Q * Q) m m := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]
      rw [he, hQss, Matrix.one_apply_eq]
    exact_mod_cast hc
  have hsum : (∑ k, ρ.eig k) = ∑ m, σ.eig m := by
    simp only [DensityMatrix.eig, ρ.sum_eigenvalues_eq_one, σ.sum_eigenvalues_eq_one]
  have hσ_pos : ∀ m, 0 < σ.eig m := fun m => hσ.eigenvalues_pos m
  have hsupp : ∀ m k, σ.eig m = 0 → Complex.normSq (Q k m) * ρ.eig k = 0 := by
    intro m k hsm
    exact absurd hsm (hσ_pos m).ne'
  have key : (∑ k, ∑ m, Complex.normSq (Q k m) * ρ.eig k * Real.log (σ.eig m))
      ≤ ∑ k, ρ.eig k * Real.log (ρ.eig k) := by
    have hklein := klein_scalar ρ.eig σ.eig (fun k m => Complex.normSq (Q k m))
      hp hs hD hrow hcol hsum hsupp
    rw [Finset.sum_comm]
    calc (∑ m, ∑ k, Complex.normSq (Q k m) * ρ.eig k * Real.log (σ.eig m))
        = ∑ m, (∑ k, Complex.normSq (Q k m) * ρ.eig k) * Real.log (σ.eig m) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul]
      _ ≤ ∑ k, ρ.eig k * Real.log (ρ.eig k) := hklein
  linarith [key]

/-! ## (3) Self / equality cases -/

/-- `D(ρ‖ρ) = 0`: with σ = ρ literally, `Q = ρ.eigVecᴴ ρ.eigVec = 1`, so `D k m = δ_{km}`,
and the cross term collapses to `∑ₖ pₖ log pₖ`, cancelling the first term. -/
theorem relEntropy_self_eq_zero (ρ : DensityMatrix n) : relEntropy ρ ρ = 0 := by
  have hQ1 : star ρ.eigVec * ρ.eigVec = 1 :=
    Unitary.coe_star_mul_self ρ.posSemidef.1.eigenvectorUnitary
  have hcross : ∀ k,
      (∑ m, Complex.normSq ((1 : Matrix n n ℂ) k m) * ρ.eig k * Real.log (ρ.eig m))
        = ρ.eig k * Real.log (ρ.eig k) := by
    intro k
    have h0 : ∀ m ∈ Finset.univ, m ≠ k →
        Complex.normSq ((1 : Matrix n n ℂ) k m) * ρ.eig k * Real.log (ρ.eig m) = 0 := by
      intro m _ hmk
      rw [Matrix.one_apply_ne (Ne.symm hmk), Complex.normSq_zero, zero_mul, zero_mul]
    rw [Finset.sum_eq_single k h0 (fun hk => absurd (Finset.mem_univ k) hk),
      Matrix.one_apply_eq, Complex.normSq_one, one_mul]
  simp only [relEntropy, crossOverlap, hQ1]
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl fun k _ => (hcross k).symm

/-! ## (4) Unitary invariance -/

/-- Conjugation of a density matrix by a unitary `W ↦ W ρ Wᴴ`, again a density matrix. -/
def DensityMatrix.conj (ρ : DensityMatrix n) (W : Matrix.unitaryGroup n ℂ) :
    DensityMatrix n where
  val := (W : Matrix n n ℂ) * ρ.val * star (W : Matrix n n ℂ)
  posSemidef := by
    have h := ρ.posSemidef.mul_mul_conjTranspose_same (W : Matrix n n ℂ)
    rwa [Matrix.star_eq_conjTranspose]
  trace_one := by
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose,
      Unitary.coe_star_mul_self, one_mul, ρ.trace_one]

/-- **Unitary invariance.** `D(WρWᴴ ‖ WσWᴴ) = D(ρ‖σ)`: conjugation by a unitary permutes the
eigenbases jointly, leaving the eigenvalue families and the overlap matrix invariant. -/
theorem relEntropy_conj_invariant (ρ σ : DensityMatrix n) (W : Matrix.unitaryGroup n ℂ) :
    relEntropy (ρ.conj W) (σ.conj W) = relEntropy ρ σ := by
  have hcancel : ∀ M : Matrix n n ℂ,
      ((W : Matrix n n ℂ) * M * star (W : Matrix n n ℂ)).trace = M.trace := fun M => by
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self W, one_mul]
  have hcfc_conj : ∀ μ : DensityMatrix n,
      (μ.conj W).posSemidef.1.cfc Real.log
        = (W : Matrix n n ℂ) * μ.posSemidef.1.cfc Real.log * star (W : Matrix n n ℂ) := by
    intro μ
    have hcont : ContinuousOn Real.log (spectrum ℝ μ.val) :=
      (Matrix.finite_real_spectrum (A := μ.val)).continuousOn Real.log
    have hφ : Continuous ⇑(Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W) := by
      have hc : Continuous (fun x : Matrix n n ℂ =>
          (W : Matrix n n ℂ) * x * star (W : Matrix n n ℂ)) :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hc.congr fun x => (Unitary.conjStarAlgAut_apply W x).symm
    have ha : IsSelfAdjoint μ.val := μ.posSemidef.1.isSelfAdjoint
    have hφa : IsSelfAdjoint (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W μ.val) :=
      ha.map (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W)
    have hval : (μ.conj W).val = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W μ.val := by
      simp only [Unitary.conjStarAlgAut_apply, DensityMatrix.conj]
    rw [← Matrix.IsHermitian.cfc_eq, ← Matrix.IsHermitian.cfc_eq, hval,
      ← StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W) Real.log μ.val
        hcont hφ ha hφa,
      Unitary.conjStarAlgAut_apply]
  have hconj_trace : ∀ μ ν : DensityMatrix n,
      ((μ.conj W).val * (ν.conj W).posSemidef.1.cfc Real.log).trace
        = (μ.val * ν.posSemidef.1.cfc Real.log).trace := by
    intro μ ν
    have hμval : (μ.conj W).val
        = (W : Matrix n n ℂ) * μ.val * star (W : Matrix n n ℂ) := rfl
    have hsw : star (W : Matrix n n ℂ) * (W : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self W
    rw [hcfc_conj ν, hμval]
    have hprod : (W : Matrix n n ℂ) * μ.val * star (W : Matrix n n ℂ)
          * ((W : Matrix n n ℂ) * ν.posSemidef.1.cfc Real.log * star (W : Matrix n n ℂ))
        = (W : Matrix n n ℂ) * (μ.val * ν.posSemidef.1.cfc Real.log)
          * star (W : Matrix n n ℂ) := by
      simp only [mul_assoc]
      rw [← mul_assoc (star (W : Matrix n n ℂ)) (W : Matrix n n ℂ), hsw, one_mul]
    rw [hprod, hcancel]
  rw [relEntropy_eq_trace (ρ.conj W) (σ.conj W), relEntropy_eq_trace ρ σ,
    hconj_trace ρ ρ, hconj_trace ρ σ]

/-! ## (5) Consumer corollary + the DPI/monotonicity INTERFACE (Lieb gap localized here) -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A map on density matrices is **relative-entropy monotone** (data-processing inequality / DPI)
if it never increases the Umegaki relative entropy.  Discharging this for a general CPTP map IS
the Lieb-concavity WALL of issue #22; here it is an explicit, honest hypothesis. -/
def IsRelEntropyMonotone (Λ : DensityMatrix n → DensityMatrix m) : Prop :=
  ∀ ρ σ : DensityMatrix n, relEntropy (Λ ρ) (Λ σ) ≤ relEntropy ρ σ

/-- Interface non-vacuity: the identity map is trivially relative-entropy monotone. -/
theorem isRelEntropyMonotone_id : IsRelEntropyMonotone (id : DensityMatrix n → DensityMatrix n) :=
  fun _ _ => le_refl _

/-- **No monotone section under a strict relative-entropy drop.**
If a recovery map `R : m → n` is relative-entropy monotone (DPI) and is a perfect section of a
coarse-graining `Λ : n → m` on the states `ρ, σ` (`R (Λ ρ) = ρ`, `R (Λ σ) = σ`), then a STRICT
drop `D(Λρ ‖ Λσ) < D(ρ ‖ σ)` is impossible.

Honest scope: the data-processing/monotonicity input is the EXPLICIT hypothesis `hRmono`
(the Lieb-gated piece); everything else is the trivial DPI chain. -/
theorem no_monotone_section_of_strict_drop
    (Λ : DensityMatrix n → DensityMatrix m) (R : DensityMatrix m → DensityMatrix n)
    (hRmono : IsRelEntropyMonotone R)
    (ρ σ : DensityMatrix n)
    (hsecρ : R (Λ ρ) = ρ) (hsecσ : R (Λ σ) = σ)
    (hstrict : relEntropy (Λ ρ) (Λ σ) < relEntropy ρ σ) :
    False := by
  have h := hRmono (Λ ρ) (Λ σ)
  rw [hsecρ, hsecσ] at h
  linarith

end Oseledets.OperatorEntropy
