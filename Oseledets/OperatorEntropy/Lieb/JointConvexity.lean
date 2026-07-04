/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Oseledets.OperatorEntropy.Lieb.Perspective

/-!
# Joint convexity of the Umegaki relative entropy (Lieb's theorem)

The trace-form relative entropy of positive-definite matrices,

`relEntropyMat ρ σ = (Tr (ρ · (log ρ − log σ))).re`,

is **jointly convex** in `(ρ, σ)`.  This is Lieb's theorem, obtained here from Effros' joint
convexity of the operator perspective (`operatorPerspective_jointly_convex`) via the Effros
realization: on the doubled index `n × n`, with the commuting positive-definite pair

`L = 1 ⊗ σᵀ`,  `R = ρ ⊗ 1`,

the operator perspective of `-log` realizes the relative entropy through the positive linear
functional `M ↦ ⟪vec 1, M · vec 1⟫`:

`relEntropyMat ρ σ = (⟪vec 1, P_{-log}(L, R) · vec 1⟫).re`.

Since `ρ ↦ R` and `σ ↦ L` are `ℝ`-linear and `⟪vec 1, · vec 1⟫` is a positive linear functional,
Effros' joint convexity descends to the scalar joint convexity of `relEntropyMat`.

## Main results

* `Oseledets.OperatorEntropy.Lieb.relEntropyMat`: the trace-form relative entropy.
* `Oseledets.OperatorEntropy.Lieb.relEntropyMat_jointly_convex`: Lieb's joint convexity.
* `Oseledets.OperatorEntropy.Lieb.relEntropyMat_eq_relEntropy`: the bridge to the spectral
  `relEntropy` on `DensityMatrix`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The trace-form relative entropy -/

/-- **Trace-form relative entropy** `D(ρ‖σ) = (Tr (ρ (log ρ − log σ))).re` with the matrix
logarithms supplied by the (generic) continuous functional calculus. -/
def relEntropyMat (ρ σ : Matrix n n ℂ) : ℝ :=
  (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace.re

/-- Bridge: the trace-form relative entropy agrees with the spectral `relEntropy` on density
matrices (faithful `σ`), via `relEntropy_eq_traceLog` and `Matrix.IsHermitian.cfc_eq`. -/
theorem relEntropyMat_eq_relEntropy (ρ σ : DensityMatrix n) (_hσ : σ.val.PosDef) :
    relEntropyMat ρ.val σ.val = relEntropy ρ σ := by
  rw [relEntropy_eq_traceLog ρ σ, relEntropyMat,
    Matrix.IsHermitian.cfc_eq ρ.posSemidef.1, Matrix.IsHermitian.cfc_eq σ.posSemidef.1]

/-! ## The Effros realization functional -/

/-- The vectorised identity `vec 1 : n × n → ℂ`, `(i, j) ↦ [i = j]`. -/
def vecOne (n : Type*) [DecidableEq n] : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- The positive linear functional `M ↦ ⟪vec 1, M · vec 1⟫` on `Matrix (n × n) (n × n) ℂ`. -/
def relForm (M : Matrix (n × n) (n × n) ℂ) : ℂ := star (vecOne n) ⬝ᵥ M *ᵥ vecOne n

/-- Applying `relForm` to a Kronecker product: `relForm (A ⊗ₖ C) = Tr (A Cᵀ)`. -/
lemma relForm_kron (A C : Matrix n n ℂ) : relForm (A ⊗ₖ C) = (A * Cᵀ).trace := by
  have hmv : ∀ p : n × n, ((A ⊗ₖ C) *ᵥ vecOne n) p = ∑ k, A p.1 k * C p.2 k := by
    rintro ⟨pi, pj⟩
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [vecOne, Finset.sum_ite_eq]
  have hstar : star (vecOne n) = vecOne n := by
    funext p
    simp only [Pi.star_apply, vecOne]
    rcases eq_or_ne p.1 p.2 with h | h <;> simp [h]
  simp only [relForm, dotProduct, hmv, hstar, vecOne, ite_mul, one_mul, zero_mul]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- `relForm` is additive. -/
lemma relForm_add (M₁ M₂ : Matrix (n × n) (n × n) ℂ) :
    relForm (M₁ + M₂) = relForm M₁ + relForm M₂ := by
  simp only [relForm, Matrix.add_mulVec, dotProduct_add]

/-- `relForm` is `ℝ`-homogeneous. -/
lemma relForm_smul (r : ℝ) (M : Matrix (n × n) (n × n) ℂ) :
    relForm (r • M) = (r : ℂ) • relForm M := by
  rw [relForm, relForm, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul, smul_eq_mul]

/-- `relForm` respects subtraction. -/
lemma relForm_sub (M₁ M₂ : Matrix (n × n) (n × n) ℂ) :
    relForm (M₁ - M₂) = relForm M₁ - relForm M₂ := by
  simp only [relForm, Matrix.sub_mulVec, dotProduct_sub]

/-- `relForm` is monotone for the Loewner order (values compared in `ComplexOrder`). -/
lemma relForm_mono {A B : Matrix (n × n) (n × n) ℂ} (h : A ≤ B) : relForm A ≤ relForm B := by
  have hps : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hnn : 0 ≤ star (vecOne n) ⬝ᵥ ((B - A) *ᵥ vecOne n) := hps.dotProduct_mulVec_nonneg (vecOne n)
  have hlin : star (vecOne n) ⬝ᵥ ((B - A) *ᵥ vecOne n) = relForm B - relForm A := by
    simp only [relForm, Matrix.sub_mulVec, dotProduct_sub]
  rw [hlin] at hnn
  exact sub_nonneg.mp hnn

/-! ## Entrywise conjugation and the transpose of a functional calculus -/

/-- Entrywise complex conjugation as a continuous `ℝ`-star-algebra homomorphism on matrices. -/
def conjMatₛ (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →⋆ₐ[ℝ] Matrix n n ℂ where
  toFun M := M.map (starRingEnd ℂ)
  map_one' := by ext i j; rcases eq_or_ne i j with h | h <;> simp [Matrix.one_apply, h]
  map_mul' M N := by ext i j; simp [Matrix.mul_apply, map_sum, map_mul]
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp
  commutes' r := by
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, Matrix.algebraMap_matrix_apply, h]
  map_star' M := by
    ext i j
    simp [Matrix.map_apply, Matrix.star_apply]

@[simp] lemma conjMatₛ_apply (M : Matrix n n ℂ) : conjMatₛ n M = M.map (starRingEnd ℂ) := rfl

lemma conjMatₛ_continuous : Continuous (conjMatₛ n) := by
  apply continuous_matrix
  intro i j
  exact Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))

/-- For a Hermitian matrix, entrywise conjugation is the transpose. -/
lemma conjMatₛ_hermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) : conjMatₛ n M = Mᵀ := by
  ext i j
  have h := congrFun (congrFun hM.eq i) j
  simp only [Matrix.conjTranspose_apply] at h
  simp only [conjMatₛ_apply, Matrix.map_apply, Matrix.transpose_apply, ← h, Complex.conj_conj,
    RCLike.star_def]

/-- **Transpose of a continuous functional calculus.** For a Hermitian matrix,
`cfc f (Mᵀ) = (cfc f M)ᵀ`. -/
lemma cfc_transpose (f : ℝ → ℝ) {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (hf : ContinuousOn f (spectrum ℝ M)) : cfc f (Mᵀ) = (cfc f M)ᵀ := by
  have hMsa : IsSelfAdjoint M := hM
  have hCsa : IsSelfAdjoint (cfc f M) := cfc_predicate f M
  have hkey : conjMatₛ n (cfc f M) = cfc f (conjMatₛ n M) :=
    StarAlgHomClass.map_cfc (conjMatₛ n) f M hf conjMatₛ_continuous hMsa (hMsa.map _)
  rw [conjMatₛ_hermitian hCsa, conjMatₛ_hermitian hM] at hkey
  exact hkey.symm

/-! ## Functional calculus of a Kronecker product with the identity -/

section Kron

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- Kronecker with the identity, `A ↦ A ⊗ₖ 1`, as a `ℂ`-star-algebra homomorphism. -/
def kronOneHom (nA nB : Type*) [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB] :
    Matrix nA nA ℂ →⋆ₐ[ℂ] Matrix (nA × nB) (nA × nB) ℂ where
  toFun M := M ⊗ₖ (1 : Matrix nB nB ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' M N := by rw [← Matrix.mul_kronecker_mul, mul_one]
  map_zero' := by simp
  map_add' M N := Matrix.add_kronecker M N 1
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker, Matrix.one_kronecker_one]
  map_star' M := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

@[simp] lemma kronOneHom_apply (M : Matrix nA nA ℂ) :
    kronOneHom nA nB M = M ⊗ₖ (1 : Matrix nB nB ℂ) := rfl

lemma kronOneHom_continuous : Continuous (kronOneHom nA nB) := by
  apply continuous_matrix
  intro p q
  exact (((continuous_apply q.1).comp (continuous_apply p.1)).mul continuous_const)

/-- `cfc g (A ⊗ₖ 1) = cfc g A ⊗ₖ 1`. -/
lemma cfc_kron_one (g : ℝ → ℝ) {A : Matrix nA nA ℂ} (hA : IsSelfAdjoint A)
    (hg : ContinuousOn g (spectrum ℝ A)) :
    cfc g (A ⊗ₖ (1 : Matrix nB nB ℂ)) = cfc g A ⊗ₖ 1 := by
  have h := StarAlgHomClass.map_cfc (kronOneHom nA nB) g A hg kronOneHom_continuous hA (hA.map _)
  simpa only [kronOneHom_apply] using h.symm

/-- `(A ⊗ₖ 1) ^ y = A ^ y ⊗ₖ 1` for positive-definite `A`. -/
lemma rpow_kron_one {A : Matrix nA nA ℂ} (hA : A.PosDef) (y : ℝ) :
    CFC.rpow (A ⊗ₖ (1 : Matrix nB nB ℂ)) y = CFC.rpow A y ⊗ₖ (1 : Matrix nB nB ℂ) := by
  have hA1 : (A ⊗ₖ (1 : Matrix nB nB ℂ)).PosDef := hA.kronecker Matrix.PosDef.one
  have hpos : ∀ x ∈ spectrum ℝ A, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos A hA.1).mp hA.isStrictlyPositive x hx
  have hcont : ContinuousOn (fun x : ℝ => x ^ y) (spectrum ℝ A) := fun x hx =>
    (Real.continuousAt_rpow_const x y (Or.inl (hpos x hx).ne')).continuousWithinAt
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA1.posSemidef.nonneg,
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, cfc_kron_one (fun x => x ^ y) hA.1 hcont]

/-- **Raw log-of-Kronecker.** For positive-definite `A, B`,
`log (A ⊗ₖ B) = log A ⊗ₖ 1 + 1 ⊗ₖ log B`. -/
lemma cfc_log_kron {A : Matrix nA nA ℂ} {B : Matrix nB nB ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B) = cfc Real.log A ⊗ₖ 1 + 1 ⊗ₖ cfc Real.log B := by
  have hAh : A.IsHermitian := hA.1
  have hBh : B.IsHermitian := hB.1
  set UA : Matrix nA nA ℂ := (hAh.eigenvectorUnitary : Matrix nA nA ℂ) with hUA
  set UB : Matrix nB nB ℂ := (hBh.eigenvectorUnitary : Matrix nB nB ℂ) with hUB
  set eA : nA → ℝ := hAh.eigenvalues with heA
  set eB : nB → ℝ := hBh.eigenvalues with heB
  have hUAs : star UA * UA = 1 := Unitary.coe_star_mul_self _
  have hUAs' : UA * star UA = 1 := Unitary.coe_mul_star_self _
  have hUBs : star UB * UB = 1 := Unitary.coe_star_mul_self _
  have hUBs' : UB * star UB = 1 := Unitary.coe_mul_star_self _
  have hspecA : A = UA * diagonal (fun i => (eA i : ℂ)) * star UA := by
    have h := hAh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hAh.eigenvalues) = fun i => (eA i : ℂ) := by funext i; rfl
    rw [hRC] at h; exact h
  have hspecB : B = UB * diagonal (fun j => (eB j : ℂ)) * star UB := by
    have h := hBh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hBh.eigenvalues) = fun j => (eB j : ℂ) := by funext j; rfl
    rw [hRC] at h; exact h
  have hLA : cfc Real.log A = UA * diagonal (fun i => (Real.log (eA i) : ℂ)) * star UA := by
    rw [Matrix.IsHermitian.cfc_eq hAh]
    have h : hAh.cfc Real.log = UA * diagonal (RCLike.ofReal ∘ Real.log ∘ hAh.eigenvalues)
        * star UA := by simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, hUA]
    have hRC : (RCLike.ofReal ∘ Real.log ∘ hAh.eigenvalues)
        = fun i => (Real.log (eA i) : ℂ) := by funext i; rfl
    rw [hRC] at h; exact h
  have hLB : cfc Real.log B = UB * diagonal (fun j => (Real.log (eB j) : ℂ)) * star UB := by
    rw [Matrix.IsHermitian.cfc_eq hBh]
    have h : hBh.cfc Real.log = UB * diagonal (RCLike.ofReal ∘ Real.log ∘ hBh.eigenvalues)
        * star UB := by simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, hUB]
    have hRC : (RCLike.ofReal ∘ Real.log ∘ hBh.eigenvalues)
        = fun j => (Real.log (eB j) : ℂ) := by funext j; rfl
    rw [hRC] at h; exact h
  have hWstar : star (UA ⊗ₖ UB) = star UA ⊗ₖ star UB := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]
  have hW1 : star (UA ⊗ₖ UB) * (UA ⊗ₖ UB) = 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, hUAs, hUBs, Matrix.one_kronecker_one]
  have hW2 : (UA ⊗ₖ UB) * star (UA ⊗ₖ UB) = 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, hUAs', hUBs', Matrix.one_kronecker_one]
  have hD1sa : IsSelfAdjoint (diagonal (fun i => (eA i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact Complex.conj_ofReal (eA i)
  have hD2sa : IsSelfAdjoint (diagonal (fun j => (eB j : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext j; exact Complex.conj_ofReal (eB j)
  have hMdiag : IsSelfAdjoint
      (diagonal (fun i => (eA i : ℂ)) ⊗ₖ diagonal (fun j => (eB j : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      isSelfAdjoint_iff.mp hD1sa, isSelfAdjoint_iff.mp hD2sa]
  have hAB : A ⊗ₖ B = (UA ⊗ₖ UB)
      * (diagonal (fun i => (eA i : ℂ)) ⊗ₖ diagonal (fun j => (eB j : ℂ)))
      * star (UA ⊗ₖ UB) := by
    rw [hspecA, hspecB, hWstar, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  have hDkron : diagonal (fun i => (eA i : ℂ)) ⊗ₖ diagonal (fun j => (eB j : ℂ))
      = diagonal (fun q : nA × nB => ((eA q.1 * eB q.2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]; congr 1; funext q; push_cast; ring
  have hdiagsplit : diagonal (fun q : nA × nB => (Real.log (eA q.1 * eB q.2) : ℂ))
      = diagonal (fun i => (Real.log (eA i) : ℂ)) ⊗ₖ (1 : Matrix nB nB ℂ)
        + (1 : Matrix nA nA ℂ) ⊗ₖ diagonal (fun j => (Real.log (eB j) : ℂ)) := by
    rw [← Matrix.diagonal_one (n := nB), ← Matrix.diagonal_one (n := nA),
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_add]
    congr 1; funext q
    have hne1 : eA q.1 ≠ 0 := (hA.eigenvalues_pos q.1).ne'
    have hne2 : eB q.2 ≠ 0 := (hB.eigenvalues_pos q.2).ne'
    rw [Real.log_mul hne1 hne2]; push_cast; ring
  have hWX : (UA ⊗ₖ UB) * (diagonal (fun i => (Real.log (eA i) : ℂ)) ⊗ₖ (1 : Matrix nB nB ℂ))
        * star (UA ⊗ₖ UB) = cfc Real.log A ⊗ₖ 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      hUBs', ← hLA]
  have hWY : (UA ⊗ₖ UB) * ((1 : Matrix nA nA ℂ) ⊗ₖ diagonal (fun j => (Real.log (eB j) : ℂ)))
        * star (UA ⊗ₖ UB) = 1 ⊗ₖ cfc Real.log B := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      hUAs', ← hLB]
  rw [hAB, Oseledets.OperatorEntropy.cfc_conj (UA ⊗ₖ UB)
      (diagonal (fun i => (eA i : ℂ)) ⊗ₖ diagonal (fun j => (eB j : ℂ))) hW1 hW2 hMdiag Real.log,
    hDkron, Oseledets.OperatorEntropy.cfc_log_diagonal (fun q : nA × nB => eA q.1 * eB q.2),
    hdiagsplit, Matrix.mul_add, Matrix.add_mul, hWX, hWY]

end Kron

/-- `log (ρ ^ (-1)) = - log ρ` for positive-definite `ρ`. -/
lemma cfc_log_rpow_neg_one {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    cfc Real.log (CFC.rpow ρ (-1)) = -cfc Real.log ρ := by
  have hpos : ∀ x ∈ spectrum ℝ ρ, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos ρ hρ.1).mp hρ.isStrictlyPositive x hx
  have hcontf : ContinuousOn (fun x : ℝ => x ^ (-1 : ℝ)) (spectrum ℝ ρ) := fun x hx =>
    (Real.continuousAt_rpow_const x (-1) (Or.inl (hpos x hx).ne')).continuousWithinAt
  have himg : (fun x : ℝ => x ^ (-1 : ℝ)) '' spectrum ℝ ρ ⊆ {x : ℝ | x ≠ 0} := by
    rintro y ⟨x, hx, rfl⟩
    exact (Real.rpow_pos_of_pos (hpos x hx) _).ne'
  have hcontlog : ContinuousOn Real.log ((fun x : ℝ => x ^ (-1 : ℝ)) '' spectrum ℝ ρ) :=
    Real.continuousOn_log.mono himg
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hρ.posSemidef.nonneg]
  refine Eq.trans (cfc_comp Real.log (fun x : ℝ => x ^ (-1 : ℝ)) ρ hρ.1 hcontlog hcontf).symm ?_
  rw [← cfc_neg Real.log ρ]
  refine cfc_congr fun x hx => ?_
  rw [Function.comp_apply, Real.rpow_neg_one, Real.log_inv]

/-! ## The general-index operator perspective via reindexing -/

section Transport

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The operator perspective at a general finite index (same formula as `operatorPerspective`). -/
def opPersp (f : ℝ → ℝ) (L R : Matrix m m ℂ) : Matrix m m ℂ :=
  CFC.rpow R (1 / 2) * cfc f (CFC.rpow R (-(1 / 2)) * L * CFC.rpow R (-(1 / 2)))
    * CFC.rpow R (1 / 2)

/-- Reindexing `Matrix m m ℂ` to `Matrix (Fin (card m)) (Fin (card m)) ℂ` as a star-alg-equiv. -/
def eqvFin (m : Type*) [Fintype m] [DecidableEq m] :
    Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) ℂ :=
  StarAlgEquiv.ofAlgEquiv (reindexAlgEquiv ℂ ℂ (Fintype.equivFin m)) fun M => by
    simp only [reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose]
    exact (conjTranspose_reindex (Fintype.equivFin m) (Fintype.equivFin m) M).symm

lemma eqvFin_continuous : Continuous (eqvFin m) := by
  apply continuous_matrix
  intro i j
  change Continuous fun M : Matrix m m ℂ =>
    M ((Fintype.equivFin m).symm i) ((Fintype.equivFin m).symm j)
  exact (continuous_apply _).comp (continuous_apply _)

lemma eqvFin_smul (r : ℝ) (P : Matrix m m ℂ) : eqvFin m (r • P) = r • eqvFin m P := by
  ext i j; rfl

lemma eqvFin_le_reflect {A B : Matrix m m ℂ} (h : eqvFin m A ≤ eqvFin m B) : A ≤ B := by
  rw [Matrix.le_iff] at h ⊢
  have hsub : (eqvFin m B - eqvFin m A)
      = (B - A).submatrix (Fintype.equivFin m).symm (Fintype.equivFin m).symm := by
    rw [← map_sub]; rfl
  rw [hsub] at h
  have h2 := h.submatrix (Fintype.equivFin m)
  rwa [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2

lemma eqvFin_posDef {R : Matrix m m ℂ} (hR : R.PosDef) : (eqvFin m R).PosDef := by
  have h : (eqvFin m R) = R.submatrix (Fintype.equivFin m).symm (Fintype.equivFin m).symm := rfl
  rw [h]; exact hR.submatrix (Fintype.equivFin m).symm.injective

lemma eqvFin_selfAdjoint {X : Matrix m m ℂ} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (eqvFin m X) := by
  rw [isSelfAdjoint_iff, ← map_star, isSelfAdjoint_iff.mp hX]

lemma eqvFin_spectrum (X : Matrix m m ℂ) : spectrum ℝ (eqvFin m X) = spectrum ℝ X := by
  have hval : (eqvFin m X : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) ℂ)
      = reindexAlgEquiv ℝ ℂ (Fintype.equivFin m) X := by ext i j; rfl
  rw [hval, AlgEquiv.spectrum_eq]

lemma eqvFin_cfc (f : ℝ → ℝ) {X : Matrix m m ℂ} (hX : IsSelfAdjoint X)
    (hcont : ContinuousOn f (spectrum ℝ X)) :
    eqvFin m (cfc f X) = cfc f (eqvFin m X) :=
  StarAlgHomClass.map_cfc (eqvFin m) f X hcont eqvFin_continuous hX (eqvFin_selfAdjoint hX)

lemma eqvFin_rpow {R : Matrix m m ℂ} (hR : R.PosDef) (y : ℝ) :
    eqvFin m (CFC.rpow R y) = CFC.rpow (eqvFin m R) y := by
  have hpos : ∀ x ∈ spectrum ℝ R, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos R hR.1).mp hR.isStrictlyPositive x hx
  have hcont : ContinuousOn (fun x : ℝ => x ^ y) (spectrum ℝ R) := fun x hx =>
    (Real.continuousAt_rpow_const x y (Or.inl (hpos x hx).ne')).continuousWithinAt
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hR.posSemidef.nonneg,
    CFC.rpow_eq_cfc_real (eqvFin_posDef hR).posSemidef.nonneg]
  exact eqvFin_cfc (fun x : ℝ => x ^ y) hR.1 hcont

/-- `eqvFin` intertwines the operator perspective with `operatorPerspective`. -/
lemma map_opPersp (f : ℝ → ℝ) {L R : Matrix m m ℂ} (hR : R.PosDef)
    (hX : IsSelfAdjoint (CFC.rpow R (-(1 / 2)) * L * CFC.rpow R (-(1 / 2)))) :
    eqvFin m (opPersp f L R) = operatorPerspective f (eqvFin m L) (eqvFin m R) := by
  have hcont := (Matrix.finite_real_spectrum
    (A := CFC.rpow R (-(1 / 2)) * L * CFC.rpow R (-(1 / 2)))).continuousOn f
  rw [opPersp, operatorPerspective]
  simp only [map_mul, eqvFin_rpow hR, eqvFin_cfc f hX hcont]

/-- The reindexed argument of the perspective. -/
lemma eqvFin_argX {L R : Matrix m m ℂ} (hR : R.PosDef) :
    CFC.rpow (eqvFin m R) (-(1 / 2)) * eqvFin m L * CFC.rpow (eqvFin m R) (-(1 / 2))
      = eqvFin m (CFC.rpow R (-(1 / 2)) * L * CFC.rpow R (-(1 / 2))) := by
  simp only [map_mul, eqvFin_rpow hR]

set_option maxHeartbeats 400000 in -- transport of Effros' theorem to a general finite index
/-- **Effros' theorem at a general finite index.** Joint convexity of `opPersp`. -/
theorem opPersp_jointly_convex (f : ℝ → ℝ) (I : Set ℝ) (hf : OperatorConvexOn I f)
    (L₁ R₁ L₂ R₂ : Matrix m m ℂ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    (hX₁ : IsSelfAdjoint (CFC.rpow R₁ (-(1 / 2)) * L₁ * CFC.rpow R₁ (-(1 / 2)))
      ∧ spectrum ℝ (CFC.rpow R₁ (-(1 / 2)) * L₁ * CFC.rpow R₁ (-(1 / 2))) ⊆ I)
    (hX₂ : IsSelfAdjoint (CFC.rpow R₂ (-(1 / 2)) * L₂ * CFC.rpow R₂ (-(1 / 2)))
      ∧ spectrum ℝ (CFC.rpow R₂ (-(1 / 2)) * L₂ * CFC.rpow R₂ (-(1 / 2))) ⊆ I)
    (hRc : (c • R₁ + (1 - c) • R₂).PosDef)
    (hXc : IsSelfAdjoint (CFC.rpow (c • R₁ + (1 - c) • R₂) (-(1 / 2)) * (c • L₁ + (1 - c) • L₂)
      * CFC.rpow (c • R₁ + (1 - c) • R₂) (-(1 / 2)))) :
    opPersp f (c • L₁ + (1 - c) • L₂) (c • R₁ + (1 - c) • R₂)
      ≤ c • opPersp f L₁ R₁ + (1 - c) • opPersp f L₂ R₂ := by
  have hself₁ : IsSelfAdjoint (CFC.rpow (eqvFin m R₁) (-(1 / 2)) * eqvFin m L₁
      * CFC.rpow (eqvFin m R₁) (-(1 / 2))) := by
    rw [eqvFin_argX hR₁]; exact eqvFin_selfAdjoint hX₁.1
  have hspec₁ : spectrum ℝ (CFC.rpow (eqvFin m R₁) (-(1 / 2)) * eqvFin m L₁
      * CFC.rpow (eqvFin m R₁) (-(1 / 2))) ⊆ I := by
    rw [eqvFin_argX hR₁, eqvFin_spectrum]; exact hX₁.2
  have hself₂ : IsSelfAdjoint (CFC.rpow (eqvFin m R₂) (-(1 / 2)) * eqvFin m L₂
      * CFC.rpow (eqvFin m R₂) (-(1 / 2))) := by
    rw [eqvFin_argX hR₂]; exact eqvFin_selfAdjoint hX₂.1
  have hspec₂ : spectrum ℝ (CFC.rpow (eqvFin m R₂) (-(1 / 2)) * eqvFin m L₂
      * CFC.rpow (eqvFin m R₂) (-(1 / 2))) ⊆ I := by
    rw [eqvFin_argX hR₂, eqvFin_spectrum]; exact hX₂.2
  have key := operatorPerspective_jointly_convex f I hf (eqvFin m L₁) (eqvFin m R₁)
    (eqvFin m L₂) (eqvFin m R₂) c hc (eqvFin_posDef hR₁) (eqvFin_posDef hR₂)
    ⟨hself₁, hspec₁⟩ ⟨hself₂, hspec₂⟩
  have hLc : eqvFin m (c • L₁ + (1 - c) • L₂) = c • eqvFin m L₁ + (1 - c) • eqvFin m L₂ := by
    rw [map_add, eqvFin_smul, eqvFin_smul]
  have hRc' : eqvFin m (c • R₁ + (1 - c) • R₂) = c • eqvFin m R₁ + (1 - c) • eqvFin m R₂ := by
    rw [map_add, eqvFin_smul, eqvFin_smul]
  have hRHS : eqvFin m (c • opPersp f L₁ R₁ + (1 - c) • opPersp f L₂ R₂)
      = c • eqvFin m (opPersp f L₁ R₁) + (1 - c) • eqvFin m (opPersp f L₂ R₂) := by
    rw [map_add, eqvFin_smul, eqvFin_smul]
  rw [← hLc, ← hRc', ← map_opPersp f hRc hXc, ← map_opPersp f hR₁ hX₁.1,
    ← map_opPersp f hR₂ hX₂.1, ← hRHS] at key
  exact eqvFin_le_reflect key

end Transport

/-! ## The Effros realization of the relative entropy -/

omit [Fintype n] [DecidableEq n] in
/-- `(-A) ⊗ₖ B = -(A ⊗ₖ B)`. -/
lemma neg_kron (A B : Matrix n n ℂ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  rw [← neg_one_smul ℂ A, Matrix.smul_kronecker, neg_one_smul]

/-- `ρ^{1/2} · ρ^{1/2} = ρ` for positive-definite `ρ`. -/
lemma rpowHalfMul {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    CFC.rpow ρ (1 / 2) * CFC.rpow ρ (1 / 2) = ρ := by
  simp only [CFC.rpow_eq_pow]
  rw [← CFC.rpow_add hρ.isUnit, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num,
    CFC.rpow_one ρ hρ.isStrictlyPositive.nonneg]

/-- The perspective argument for the Effros pair `(1 ⊗ σᵀ, ρ ⊗ 1)` is `ρ^{-1} ⊗ σᵀ`. -/
lemma perspArg_kron {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (σ : Matrix n n ℂ) :
    CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2)) * ((1 : Matrix n n ℂ) ⊗ₖ σᵀ)
      * CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2)) = CFC.rpow ρ (-1) ⊗ₖ σᵀ := by
  have hρhalf : CFC.rpow ρ (-(1 / 2)) * CFC.rpow ρ (-(1 / 2)) = CFC.rpow ρ (-1) := by
    simp only [CFC.rpow_eq_pow]
    rw [← CFC.rpow_add hρ.isUnit]; congr 1; norm_num
  simp only [rpow_kron_one hρ, ← Matrix.mul_kronecker_mul, mul_one, one_mul, hρhalf]

/-- The perspective argument is positive definite. -/
lemma perspArg_posDef {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    (CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2)) * ((1 : Matrix n n ℂ) ⊗ₖ σᵀ)
      * CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2))).PosDef := by
  rw [perspArg_kron hρ]
  exact (IsStrictlyPositive.rpow ρ (-1) hρ.isStrictlyPositive).posDef.kronecker hσ.transpose

/-- Spectrum of the perspective argument is positive. -/
lemma perspArg_spectrum {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    spectrum ℝ (CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2)) * ((1 : Matrix n n ℂ) ⊗ₖ σᵀ)
      * CFC.rpow (ρ ⊗ₖ (1 : Matrix n n ℂ)) (-(1 / 2))) ⊆ Set.Ioi 0 := by
  intro x hx
  have hpd := perspArg_posDef hρ hσ
  exact (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos _ hpd.1).mp hpd.isStrictlyPositive x hx

set_option maxHeartbeats 400000 in -- Effros realization: closed form of the perspective
/-- **Effros realization (closed form).** For positive-definite `ρ, σ`,
`P_{-log}(1 ⊗ σᵀ, ρ ⊗ 1) = (ρ^{1/2} (log ρ) ρ^{1/2}) ⊗ 1 − ρ ⊗ (log σ)ᵀ`. -/
lemma opPersp_neg_log_kron {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    opPersp (fun x => -Real.log x) ((1 : Matrix n n ℂ) ⊗ₖ σᵀ) (ρ ⊗ₖ 1)
      = (CFC.rpow ρ (1 / 2) * cfc Real.log ρ * CFC.rpow ρ (1 / 2)) ⊗ₖ 1
        - ρ ⊗ₖ (cfc Real.log σ)ᵀ := by
  have hρinv : (CFC.rpow ρ (-1)).PosDef :=
    (IsStrictlyPositive.rpow ρ (-1) hρ.isStrictlyPositive).posDef
  have hσT : (σᵀ).PosDef := hσ.transpose
  have hcontσ : ContinuousOn Real.log (spectrum ℝ σ) :=
    (Matrix.finite_real_spectrum (A := σ)).continuousOn Real.log
  have hcfc : cfc (fun x => -Real.log x) (CFC.rpow ρ (-1) ⊗ₖ σᵀ)
      = cfc Real.log ρ ⊗ₖ 1 - 1 ⊗ₖ (cfc Real.log σ)ᵀ := by
    have e1 : cfc (fun x => -Real.log x) (CFC.rpow ρ (-1) ⊗ₖ σᵀ)
        = -cfc Real.log (CFC.rpow ρ (-1) ⊗ₖ σᵀ) := cfc_neg Real.log _
    rw [e1, cfc_log_kron hρinv hσT, cfc_log_rpow_neg_one hρ,
      cfc_transpose Real.log hσ.1 hcontσ, neg_kron]
    abel
  rw [opPersp, perspArg_kron hρ, hcfc]
  simp only [rpow_kron_one hρ]
  rw [mul_sub, sub_mul]
  simp only [← Matrix.mul_kronecker_mul, mul_one, one_mul, rpowHalfMul hρ]

/-- **Effros realization (scalar form).** The positive functional `relForm` recovers the
trace-form relative entropy from the perspective. -/
lemma relForm_opPersp_neg_log {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relForm (opPersp (fun x => -Real.log x) ((1 : Matrix n n ℂ) ⊗ₖ σᵀ) (ρ ⊗ₖ 1))
      = (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace := by
  rw [opPersp_neg_log_kron hρ hσ, relForm_sub, relForm_kron, relForm_kron,
    Matrix.transpose_one, Matrix.mul_one, Matrix.transpose_transpose, Matrix.mul_sub,
    Matrix.trace_sub]
  congr 1
  rw [Matrix.trace_mul_comm (CFC.rpow ρ (1 / 2) * cfc Real.log ρ) (CFC.rpow ρ (1 / 2)),
    ← Matrix.mul_assoc, rpowHalfMul hρ]

omit [Fintype n] [DecidableEq n] in
/-- Convex combination of positive-definite matrices (with `c ∈ [0,1]`) is positive definite. -/
lemma posDef_convex {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : (c • A + (1 - c) • B).PosDef := by
  rcases eq_or_lt_of_le hc.1 with h | h
  · rw [← h]; simp only [zero_smul, zero_add, sub_zero, one_smul]; exact hB
  · exact (hA.smul h).add_posSemidef (hB.posSemidef.smul (by linarith [hc.2]))

set_option maxHeartbeats 400000 in -- final assembly: transport + realization + positivity
/-- **Lieb's theorem: joint convexity of the Umegaki relative entropy.** -/
theorem relEntropyMat_jointly_convex (ρ₁ ρ₂ σ₁ σ₂ : Matrix n n ℂ) (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hρ₁ : ρ₁.PosDef) (hρ₂ : ρ₂.PosDef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef) :
    relEntropyMat (c • ρ₁ + (1 - c) • ρ₂) (c • σ₁ + (1 - c) • σ₂)
      ≤ c * relEntropyMat ρ₁ σ₁ + (1 - c) * relEntropyMat ρ₂ σ₂ := by
  have hρc : (c • ρ₁ + (1 - c) • ρ₂).PosDef := posDef_convex hρ₁ hρ₂ hc
  have hσc : (c • σ₁ + (1 - c) • σ₂).PosDef := posDef_convex hσ₁ hσ₂ hc
  have hRcomb : c • (ρ₁ ⊗ₖ (1 : Matrix n n ℂ)) + (1 - c) • (ρ₂ ⊗ₖ 1)
      = (c • ρ₁ + (1 - c) • ρ₂) ⊗ₖ 1 := by
    rw [← Matrix.smul_kronecker, ← Matrix.smul_kronecker, ← Matrix.add_kronecker]
  have hLcomb : c • ((1 : Matrix n n ℂ) ⊗ₖ σ₁ᵀ) + (1 - c) • (1 ⊗ₖ σ₂ᵀ)
      = 1 ⊗ₖ (c • σ₁ + (1 - c) • σ₂)ᵀ := by
    rw [← Matrix.kronecker_smul, ← Matrix.kronecker_smul, ← Matrix.kronecker_add,
      Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
  have hRc : (c • (ρ₁ ⊗ₖ (1 : Matrix n n ℂ)) + (1 - c) • (ρ₂ ⊗ₖ 1)).PosDef := by
    rw [hRcomb]; exact hρc.kronecker Matrix.PosDef.one
  have hXc : IsSelfAdjoint (CFC.rpow (c • (ρ₁ ⊗ₖ (1 : Matrix n n ℂ)) + (1 - c) • (ρ₂ ⊗ₖ 1))
      (-(1 / 2)) * (c • ((1 : Matrix n n ℂ) ⊗ₖ σ₁ᵀ) + (1 - c) • (1 ⊗ₖ σ₂ᵀ))
      * CFC.rpow (c • (ρ₁ ⊗ₖ (1 : Matrix n n ℂ)) + (1 - c) • (ρ₂ ⊗ₖ 1)) (-(1 / 2))) := by
    rw [hRcomb, hLcomb]; exact (perspArg_posDef hρc hσc).1
  have hJC := opPersp_jointly_convex (fun x => -Real.log x) (Set.Ioi 0) operatorConvexOn_neg_log
    ((1 : Matrix n n ℂ) ⊗ₖ σ₁ᵀ) (ρ₁ ⊗ₖ 1) ((1 : Matrix n n ℂ) ⊗ₖ σ₂ᵀ) (ρ₂ ⊗ₖ 1) c hc
    (hρ₁.kronecker Matrix.PosDef.one) (hρ₂.kronecker Matrix.PosDef.one)
    ⟨(perspArg_posDef hρ₁ hσ₁).1, perspArg_spectrum hρ₁ hσ₁⟩
    ⟨(perspArg_posDef hρ₂ hσ₂).1, perspArg_spectrum hρ₂ hσ₂⟩ hRc hXc
  rw [hLcomb, hRcomb] at hJC
  have hmono := relForm_mono hJC
  rw [relForm_opPersp_neg_log hρc hσc, relForm_add, relForm_smul, relForm_smul,
    relForm_opPersp_neg_log hρ₁ hσ₁, relForm_opPersp_neg_log hρ₂ hσ₂] at hmono
  have hre := (Complex.le_def.mp hmono).1
  simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  exact hre

end Oseledets.OperatorEntropy.Lieb

end
