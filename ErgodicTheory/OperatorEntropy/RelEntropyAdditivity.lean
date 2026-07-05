/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.RelativeEntropy
import ErgodicTheory.OperatorEntropy.Additivity
import ErgodicTheory.OperatorEntropy.KroneckerSpectrum
import Mathlib.LinearAlgebra.Lagrange

/-!
# Additivity of Umegaki relative entropy under the tensor (Kronecker) product

For density matrices `ρ₁, ρ₂, σ₁, σ₂` over `ℂ` with `σ₁, σ₂` faithful (positive definite),
the Umegaki relative entropy is additive under the Kronecker product:

`D(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = D(ρ₁ ‖ σ₁) + D(ρ₂ ‖ σ₂)`  (`relEntropy_additive_kronecker`),

together with the immediate corollary of **ancilla invariance**

`D(ρ ⊗ α ‖ σ ⊗ α) = D(ρ ‖ σ)`  (`relEntropy_ancilla_invariant`).

The crux is the **operator log-of-tensor identity** for faithful `σᵢ`
(`op_log_tensor`):

`log(σ₁ ⊗ σ₂) = log σ₁ ⊗ 1 + 1 ⊗ log σ₂`,

proved by diagonalizing `σᵢ = Uᵢ Dᵢ Uᵢᴴ`, pushing `cfc Real.log` through the unitary
`W = U₁ ⊗ U₂` (`cfc_conj`), reducing to the diagonal case (`cfc_log_diagonal`), and using
`Real.log_mul` on the positive eigenvalues.  Combined with the trace–spectral bridge
(`traceBridge`, a re-derivation of the spectral form of `Tr(ρ · log τ)`) and additivity of
von Neumann entropy, the cross term collapses via `Matrix.trace_kronecker` and unit trace.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

/-! ## The functional calculus of a real diagonal matrix -/

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Continuous functional calculus of a real diagonal matrix.**  For any `e : ι → ℝ`,
`cfc Real.log (diagonal (e ·)) = diagonal (Real.log ∘ e ·)`.  Proved by replacing `Real.log` by an
interpolating polynomial on the (finite) spectrum via `cfc_congr`, evaluating the resulting
polynomial through the diagonal algebra homomorphism. -/
lemma cfc_log_diagonal (e : ι → ℝ) :
    cfc Real.log (diagonal (fun i => (e i : ℂ)))
      = diagonal (fun i => (Real.log (e i) : ℂ)) := by
  classical
  have hsa : IsSelfAdjoint (diagonal (fun i => (e i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal (e i)
  set S : Finset ℝ := Finset.image e Finset.univ with hSdef
  set p : Polynomial ℝ := Lagrange.interpolate S id Real.log with hpdef
  have hpeval : ∀ x ∈ S, p.eval x = Real.log x := by
    intro x hx
    rw [hpdef]
    have h := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := Real.log)
      (Set.injOn_id _) hx
    simpa using h
  have hspec : spectrum ℝ (diagonal (fun i => (e i : ℂ))) ⊆ (S : Set ℝ) := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have hix : e i = x := by
      have hi' : ((e i : ℂ)) = ((x : ℂ)) := hi
      exact_mod_cast hi'
    rw [hSdef]
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hix⟩)
  rw [cfc_congr (a := diagonal (fun i => (e i : ℂ)))
      (fun x hx => (hpeval x (hspec hx)).symm),
    cfc_polynomial p _ hsa]
  have hstep : Polynomial.aeval (diagonal (fun i => (e i : ℂ))) p
      = diagonal (Polynomial.aeval (fun i => (e i : ℂ)) p) := by
    change Polynomial.aeval (Matrix.diagonalAlgHom (R := ℝ) (fun i => (e i : ℂ))) p
      = Matrix.diagonalAlgHom (R := ℝ) (Polynomial.aeval (fun i => (e i : ℂ)) p)
    exact Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom (R := ℝ)) (fun i => (e i : ℂ)) p
  rw [hstep]
  congr 1
  funext i
  have key : (Polynomial.aeval (fun i => (e i : ℂ)) p) i = Polynomial.aeval ((e i : ℂ)) p := by
    have h := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : ι => ℂ) i)
      (fun i => (e i : ℂ)) p
    simpa using h.symm
  rw [key]
  change Polynomial.aeval (algebraMap ℝ ℂ (e i)) p = (Real.log (e i) : ℂ)
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    hpeval (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i))]
  rfl

end Diagonal

/-! ## Basis independence of the functional calculus under a unitary conjugation -/

section Conj

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **Conjugation invariance of the functional calculus.**  If `star W * W = 1` and
`W * star W = 1`, then `cfc f (W M Wᴴ) = W (cfc f M) Wᴴ` for self-adjoint `M`.  This is the
basis-independence of the continuous functional calculus, realized via the unitary conjugation
`⋆`-automorphism. -/
lemma cfc_conj (W M : Matrix N N ℂ) (hW1 : star W * W = 1) (hW2 : W * star W = 1)
    (hM : IsSelfAdjoint M) (f : ℝ → ℝ) :
    cfc f (W * M * star W) = W * cfc f M * star W := by
  have hmem : W ∈ unitary (Matrix N N ℂ) := Unitary.mem_iff.mpr ⟨hW1, hW2⟩
  have hcont : ContinuousOn f (spectrum ℝ M) :=
    (Matrix.finite_real_spectrum (A := M)).continuousOn f
  have hφ : Continuous ⇑(Unitary.conjStarAlgAut ℂ (Matrix N N ℂ) ⟨W, hmem⟩) := by
    have hc : Continuous (fun x : Matrix N N ℂ => W * x * star W) :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hc.congr fun x => (Unitary.conjStarAlgAut_apply ⟨W, hmem⟩ x).symm
  have hφa : IsSelfAdjoint (Unitary.conjStarAlgAut ℂ (Matrix N N ℂ) ⟨W, hmem⟩ M) := hM.map _
  have hcj : ∀ x : Matrix N N ℂ,
      Unitary.conjStarAlgAut ℂ (Matrix N N ℂ) ⟨W, hmem⟩ x = W * x * star W :=
    fun x => Unitary.conjStarAlgAut_apply ⟨W, hmem⟩ x
  rw [← hcj M,
    ← StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Matrix N N ℂ) ⟨W, hmem⟩) f M
      hcont hφ hM hφa,
    hcj]

end Conj

/-! ## The trace–spectral bridge and the spectral form of relative entropy -/

section OneType

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Trace–spectral bridge (real part).**  `Tr(ρ · f(τ)) = ∑ₖ,ₘ pₖ |⟨eₖ|gₘ⟩|² f(qₘ)` with
`p, e` the eigendata of `ρ` and `q, g` that of `τ`, where `f(τ)` is the Hermitian functional
calculus.  This is a thin alias of the `trace_val_mul_cfc_re` bridge of
`RelativeEntropy.lean`, needed to identify the spectral cross term with a matrix trace. -/
lemma traceBridge (ρ τ : DensityMatrix n) (f : ℝ → ℝ) :
    (ρ.val * τ.posSemidef.1.cfc f).trace.re
      = ∑ k, ∑ m, ρ.eig k
          * Complex.normSq ((star ρ.eigVec * τ.eigVec) k m) * f (τ.eig m) :=
  trace_val_mul_cfc_re ρ τ f

/-- **Spectral–trace form of relative entropy.**  `D(ρ‖σ) = −S(ρ) − Tr(ρ · log σ)`, with
`S` the von Neumann entropy and `log σ` the Hermitian functional calculus.  This holds
unconditionally (no faithfulness needed). -/
lemma relEntropy_eq_negS_sub (ρ σ : DensityMatrix n) :
    relEntropy ρ σ
      = -vonNeumannEntropy ρ - (ρ.val * σ.posSemidef.1.cfc Real.log).trace.re := by
  have hself : (∑ k, ρ.eig k * Real.log (ρ.eig k)) = -vonNeumannEntropy ρ := by
    rw [vonNeumannEntropy, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [Real.negMulLog_eq_neg, DensityMatrix.eig]
    ring
  rw [traceBridge ρ σ Real.log]
  simp only [relEntropy, crossOverlap]
  rw [hself]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  ring

end OneType

/-! ## The operator log-of-tensor identity and Kronecker additivity -/

section Kron

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- **Operator log-of-tensor identity.**  For faithful (positive-definite) `σ₁, σ₂`,
`log(σ₁ ⊗ σ₂) = log σ₁ ⊗ 1 + 1 ⊗ log σ₂`, with the matrix logarithm supplied by the Hermitian
functional calculus. -/
lemma op_log_tensor (σ₁ : DensityMatrix nA) (σ₂ : DensityMatrix nB)
    (h₁ : σ₁.val.PosDef) (h₂ : σ₂.val.PosDef) :
    (σ₁.kron σ₂).posSemidef.1.cfc Real.log
      = σ₁.posSemidef.1.cfc Real.log ⊗ₖ 1 + 1 ⊗ₖ σ₂.posSemidef.1.cfc Real.log := by
  have e0 : (σ₁.kron σ₂).posSemidef.1.cfc Real.log = cfc Real.log (σ₁.kron σ₂).val :=
    (Matrix.IsHermitian.cfc_eq (σ₁.kron σ₂).posSemidef.1 Real.log).symm
  have e1 : σ₁.posSemidef.1.cfc Real.log = cfc Real.log σ₁.val :=
    (Matrix.IsHermitian.cfc_eq σ₁.posSemidef.1 Real.log).symm
  have e2 : σ₂.posSemidef.1.cfc Real.log = cfc Real.log σ₂.val :=
    (Matrix.IsHermitian.cfc_eq σ₂.posSemidef.1 Real.log).symm
  have hval : (σ₁.kron σ₂).val = σ₁.val ⊗ₖ σ₂.val := rfl
  rw [e0, e1, e2, hval]
  -- spectral decompositions
  have hσ1 : σ₁.val = σ₁.eigVec * diagonal (fun i => (σ₁.eig i : ℂ)) * star σ₁.eigVec := by
    have h := σ₁.posSemidef.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ σ₁.posSemidef.1.eigenvalues) = fun i => (σ₁.eig i : ℂ) := by
      funext i; rfl
    rw [hRC] at h
    exact h
  have hσ2 : σ₂.val = σ₂.eigVec * diagonal (fun j => (σ₂.eig j : ℂ)) * star σ₂.eigVec := by
    have h := σ₂.posSemidef.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ σ₂.posSemidef.1.eigenvalues) = fun j => (σ₂.eig j : ℂ) := by
      funext j; rfl
    rw [hRC] at h
    exact h
  have hLσ1 : cfc Real.log σ₁.val
      = σ₁.eigVec * diagonal (fun i => (Real.log (σ₁.eig i) : ℂ)) * star σ₁.eigVec := by
    rw [Matrix.IsHermitian.cfc_eq σ₁.posSemidef.1]
    have h : σ₁.posSemidef.1.cfc Real.log
        = (σ₁.posSemidef.1.eigenvectorUnitary : Matrix nA nA ℂ)
          * diagonal (RCLike.ofReal ∘ Real.log ∘ σ₁.posSemidef.1.eigenvalues)
          * star (σ₁.posSemidef.1.eigenvectorUnitary : Matrix nA nA ℂ) := by
      simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    have hRC : (RCLike.ofReal ∘ Real.log ∘ σ₁.posSemidef.1.eigenvalues)
        = fun i => (Real.log (σ₁.eig i) : ℂ) := by funext i; rfl
    rw [hRC] at h
    exact h
  have hLσ2 : cfc Real.log σ₂.val
      = σ₂.eigVec * diagonal (fun j => (Real.log (σ₂.eig j) : ℂ)) * star σ₂.eigVec := by
    rw [Matrix.IsHermitian.cfc_eq σ₂.posSemidef.1]
    have h : σ₂.posSemidef.1.cfc Real.log
        = (σ₂.posSemidef.1.eigenvectorUnitary : Matrix nB nB ℂ)
          * diagonal (RCLike.ofReal ∘ Real.log ∘ σ₂.posSemidef.1.eigenvalues)
          * star (σ₂.posSemidef.1.eigenvectorUnitary : Matrix nB nB ℂ) := by
      simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    have hRC : (RCLike.ofReal ∘ Real.log ∘ σ₂.posSemidef.1.eigenvalues)
        = fun j => (Real.log (σ₂.eig j) : ℂ) := by funext j; rfl
    rw [hRC] at h
    exact h
  -- unitary facts
  have hU1s' : σ₁.eigVec * star σ₁.eigVec = 1 :=
    Unitary.coe_mul_star_self σ₁.posSemidef.1.eigenvectorUnitary
  have hU2s' : σ₂.eigVec * star σ₂.eigVec = 1 :=
    Unitary.coe_mul_star_self σ₂.posSemidef.1.eigenvectorUnitary
  have hU1s : star σ₁.eigVec * σ₁.eigVec = 1 :=
    Unitary.coe_star_mul_self σ₁.posSemidef.1.eigenvectorUnitary
  have hU2s : star σ₂.eigVec * σ₂.eigVec = 1 :=
    Unitary.coe_star_mul_self σ₂.posSemidef.1.eigenvectorUnitary
  have hWstar : star (σ₁.eigVec ⊗ₖ σ₂.eigVec) = star σ₁.eigVec ⊗ₖ star σ₂.eigVec := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]
  have hW1 : star (σ₁.eigVec ⊗ₖ σ₂.eigVec) * (σ₁.eigVec ⊗ₖ σ₂.eigVec) = 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, hU1s, hU2s, Matrix.one_kronecker_one]
  have hW2 : (σ₁.eigVec ⊗ₖ σ₂.eigVec) * star (σ₁.eigVec ⊗ₖ σ₂.eigVec) = 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, hU1s', hU2s', Matrix.one_kronecker_one]
  -- self-adjointness of the diagonal factors
  have hD1sa : IsSelfAdjoint (diagonal (fun i => (σ₁.eig i : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal (σ₁.eig i)
  have hD2sa : IsSelfAdjoint (diagonal (fun j => (σ₂.eig j : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    exact Complex.conj_ofReal (σ₂.eig j)
  have hMdiag : IsSelfAdjoint
      (diagonal (fun i => (σ₁.eig i : ℂ)) ⊗ₖ diagonal (fun j => (σ₂.eig j : ℂ))) := by
    rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      isSelfAdjoint_iff.mp hD1sa, isSelfAdjoint_iff.mp hD2sa]
  -- σ tensor spectral decomposition
  have hAB : σ₁.val ⊗ₖ σ₂.val
      = (σ₁.eigVec ⊗ₖ σ₂.eigVec)
        * (diagonal (fun i => (σ₁.eig i : ℂ)) ⊗ₖ diagonal (fun j => (σ₂.eig j : ℂ)))
        * star (σ₁.eigVec ⊗ₖ σ₂.eigVec) := by
    rw [hσ1, hσ2, hWstar, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  -- product of the two diagonal factors
  have hDkron : diagonal (fun i => (σ₁.eig i : ℂ)) ⊗ₖ diagonal (fun j => (σ₂.eig j : ℂ))
      = diagonal (fun q : nA × nB => ((σ₁.eig q.1 * σ₂.eig q.2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext q
    push_cast
    ring
  -- the log of the product diagonal splits
  have hdiagsplit : diagonal (fun q : nA × nB => (Real.log (σ₁.eig q.1 * σ₂.eig q.2) : ℂ))
      = diagonal (fun i => (Real.log (σ₁.eig i) : ℂ)) ⊗ₖ (1 : Matrix nB nB ℂ)
        + (1 : Matrix nA nA ℂ) ⊗ₖ diagonal (fun j => (Real.log (σ₂.eig j) : ℂ)) := by
    rw [← Matrix.diagonal_one (n := nB), ← Matrix.diagonal_one (n := nA),
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_add]
    congr 1
    funext q
    have hne1 : σ₁.eig q.1 ≠ 0 := (h₁.eigenvalues_pos q.1).ne'
    have hne2 : σ₂.eig q.2 ≠ 0 := (h₂.eigenvalues_pos q.2).ne'
    rw [Real.log_mul hne1 hne2]
    push_cast
    ring
  -- conjugating each summand
  have hWX : (σ₁.eigVec ⊗ₖ σ₂.eigVec)
        * (diagonal (fun i => (Real.log (σ₁.eig i) : ℂ)) ⊗ₖ (1 : Matrix nB nB ℂ))
        * star (σ₁.eigVec ⊗ₖ σ₂.eigVec)
      = cfc Real.log σ₁.val ⊗ₖ 1 := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      hU2s', ← hLσ1]
  have hWY : (σ₁.eigVec ⊗ₖ σ₂.eigVec)
        * ((1 : Matrix nA nA ℂ) ⊗ₖ diagonal (fun j => (Real.log (σ₂.eig j) : ℂ)))
        * star (σ₁.eigVec ⊗ₖ σ₂.eigVec)
      = 1 ⊗ₖ cfc Real.log σ₂.val := by
    rw [hWstar, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      hU1s', ← hLσ2]
  rw [hAB,
    cfc_conj (σ₁.eigVec ⊗ₖ σ₂.eigVec)
      (diagonal (fun i => (σ₁.eig i : ℂ)) ⊗ₖ diagonal (fun j => (σ₂.eig j : ℂ)))
      hW1 hW2 hMdiag Real.log,
    hDkron, cfc_log_diagonal (fun q : nA × nB => σ₁.eig q.1 * σ₂.eig q.2),
    hdiagsplit, Matrix.mul_add, Matrix.add_mul, hWX, hWY]

/-- **Kronecker additivity of Umegaki relative entropy (faithful form).**
`D(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = D(ρ₁ ‖ σ₁) + D(ρ₂ ‖ σ₂)` for faithful `σ₁, σ₂`. -/
theorem relEntropy_additive_kronecker (ρ₁ : DensityMatrix nA) (ρ₂ : DensityMatrix nB)
    (σ₁ : DensityMatrix nA) (σ₂ : DensityMatrix nB) (h₁ : σ₁.val.PosDef) (h₂ : σ₂.val.PosDef) :
    relEntropy (ρ₁.kron ρ₂) (σ₁.kron σ₂) = relEntropy ρ₁ σ₁ + relEntropy ρ₂ σ₂ := by
  rw [relEntropy_eq_negS_sub (ρ₁.kron ρ₂) (σ₁.kron σ₂), relEntropy_eq_negS_sub ρ₁ σ₁,
    relEntropy_eq_negS_sub ρ₂ σ₂, vonNeumannEntropy_additive_kronecker,
    op_log_tensor σ₁ σ₂ h₁ h₂]
  have hval : (ρ₁.kron ρ₂).val = ρ₁.val ⊗ₖ ρ₂.val := rfl
  rw [hval]
  have htr : ((ρ₁.val ⊗ₖ ρ₂.val)
        * (σ₁.posSemidef.1.cfc Real.log ⊗ₖ 1 + 1 ⊗ₖ σ₂.posSemidef.1.cfc Real.log)).trace.re
      = (ρ₁.val * σ₁.posSemidef.1.cfc Real.log).trace.re
        + (ρ₂.val * σ₂.posSemidef.1.cfc Real.log).trace.re := by
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    congr 1
    · rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker, ρ₂.trace_one,
        mul_one]
    · rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker, ρ₁.trace_one,
        one_mul]
  rw [htr]
  ring

end Kron

/-! ## Ancilla invariance -/

section Ancilla

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ε : Type*} [Fintype ε] [DecidableEq ε]

/-- **Ancilla invariance.**  Relative entropy is unchanged by tensoring both arguments with a
common faithful ancilla `α`: `D(ρ ⊗ α ‖ σ ⊗ α) = D(ρ ‖ σ)`. -/
theorem relEntropy_ancilla_invariant (ρ σ : DensityMatrix n) (α : DensityMatrix ε)
    (hα : α.val.PosDef) (hσ : σ.val.PosDef) :
    relEntropy (ρ.kron α) (σ.kron α) = relEntropy ρ σ := by
  rw [relEntropy_additive_kronecker ρ α σ α hσ hα, relEntropy_self_eq_zero α, add_zero]

end Ancilla

end ErgodicTheory.OperatorEntropy
