/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.ModularOperator
import Oseledets.OperatorEntropy.Lieb.Dilation
import Oseledets.OperatorEntropy.PetzRecovery

/-!
# Petz equality: from DPI saturation to the modular `it`-intertwining (module M3)

This module builds the analytic linchpin of the sufficiency (`⟹`) direction of the Petz equality
theorem (issue #28): if the Umegaki relative entropy is preserved under a channel `Λ` (data
processing saturates), then `Λ` **intertwines the modular flows** of the input and output pairs,

`Λ†( (Λρ)^{it} (Λσ)^{-it} ) = ρ^{it} σ^{-it}`   for all `t : ℝ`.

## Contents

* `OperatorStrictConvexOn`: strict operator convexity (the equality companion of
  `OperatorConvexOn`).
* `cpow` / `upow`: the complex power `A^z` and the unitary power `A^{it}` of a positive-definite
  matrix via its eigendecomposition (there is no `ℂ`-valued cfc on matrices).
* `cpow_zero`, `cpow_mul_cpow`, `upow_add`, `upow_mul_upow_neg`, `star_upow`: the basic
  one-parameter-group / unitarity laws of these powers.
* `posSemidef_offDiag_eq_zero` / `posSemidef_zeroCorner_zeroCoupling`: a positive-semidefinite
  matrix with a vanishing diagonal entry (resp. vanishing `(0,0)`-block) has the corresponding
  off-diagonal entries (resp. coupling block) vanish.
* `channelIsometry`, `channelIsometry_isometry`, `channelIsometry_adj`: the Stinespring isometry
  `V : ℂ^n → ℂ^n ⊗ ℂ^ι` of a Kraus channel (`V†V = 1`) and its dilation identity
  `V† (Y ⊗ 1) V = Λ† Y`.
* `IntertwinesIt`: the modular `it`-intertwining property.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Strict operator convexity -/

/-- `f` is **strictly operator convex** on `I`: whenever the midpoint of the operator-Jensen
inequality for `f` is attained on self-adjoint `a, b` with spectra in `I`, then `a = b`.  This is
the equality companion of `OperatorConvexOn`, isolated as a hypothesis so it can be discharged at
integration by the separately-proved strict convexity of `-log`. -/
def OperatorStrictConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (N : ℕ) (a b : Matrix (Fin N) (Fin N) ℂ),
    IsSelfAdjoint a → spectrum ℝ a ⊆ I → IsSelfAdjoint b → spectrum ℝ b ⊆ I →
    cfc f ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) = (1 / 2 : ℝ) • cfc f a + (1 / 2 : ℝ) • cfc f b →
    a = b

/-! ## Complex and unitary powers of a positive-definite matrix -/

/-- The **complex power** `A^z` of a positive-definite matrix, via its eigendecomposition
`A = U diag(λ) U⋆`: `A^z = U diag(exp(z log λ)) U⋆`.  (There is no `ℂ`-valued continuous functional
calculus on matrices, so this is defined by hand.) -/
def cpow {A : Matrix n n ℂ} (hA : A.PosDef) (z : ℂ) : Matrix n n ℂ :=
  (hA.1.eigenvectorUnitary : Matrix n n ℂ)
    * diagonal (fun i => Complex.exp (z * (Real.log (hA.1.eigenvalues i) : ℂ)))
    * star (hA.1.eigenvectorUnitary : Matrix n n ℂ)

/-- The **unitary power** `A^{it}` of a positive-definite matrix. -/
def upow {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) : Matrix n n ℂ := cpow hA ((t : ℂ) * Complex.I)

/-- Conjugation by a unitary is multiplicative in the middle factor. -/
private lemma conjBy_mul (U D E : Matrix n n ℂ) (hU : star U * U = 1) :
    U * D * star U * (U * E * star U) = U * (D * E) * star U := by
  have h : U * D * star U * (U * E * star U) = U * D * (star U * U) * E * star U := by
    noncomm_ring
  rw [h, hU, mul_one, mul_assoc U D E]

@[simp] lemma cpow_zero {A : Matrix n n ℂ} (hA : A.PosDef) : cpow hA 0 = 1 := by
  have hfun : (fun i => Complex.exp ((0 : ℂ) * (Real.log (hA.1.eigenvalues i) : ℂ)))
      = (1 : n → ℂ) := by
    funext i; rw [zero_mul, Complex.exp_zero]; rfl
  have hdiag : diagonal (fun i => Complex.exp ((0 : ℂ) * (Real.log (hA.1.eigenvalues i) : ℂ)))
      = (1 : Matrix n n ℂ) := by rw [hfun]; exact Matrix.diagonal_one
  rw [cpow, hdiag, mul_one]
  exact Unitary.coe_mul_star_self _

/-- The **one-parameter group law** `A^z · A^w = A^{z+w}`. -/
lemma cpow_mul_cpow {A : Matrix n n ℂ} (hA : A.PosDef) (z w : ℂ) :
    cpow hA z * cpow hA w = cpow hA (z + w) := by
  have hU : star (hA.1.eigenvectorUnitary : Matrix n n ℂ)
      * (hA.1.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have hfun : (fun i => Complex.exp (z * (Real.log (hA.1.eigenvalues i) : ℂ))
        * Complex.exp (w * (Real.log (hA.1.eigenvalues i) : ℂ)))
      = (fun i => Complex.exp ((z + w) * (Real.log (hA.1.eigenvalues i) : ℂ))) := by
    funext i; rw [← Complex.exp_add, ← add_mul]
  simp only [cpow]
  rw [conjBy_mul _ _ _ hU, diagonal_mul_diagonal, hfun]

@[simp] lemma upow_zero {A : Matrix n n ℂ} (hA : A.PosDef) : upow hA 0 = 1 := by
  simp only [upow, Complex.ofReal_zero, zero_mul, cpow_zero]

/-- The unitary power is a **one-parameter group**: `A^{is} · A^{it} = A^{i(s+t)}`. -/
lemma upow_add {A : Matrix n n ℂ} (hA : A.PosDef) (s t : ℝ) :
    upow hA s * upow hA t = upow hA (s + t) := by
  simp only [upow, cpow_mul_cpow]
  congr 1
  push_cast
  ring

/-- `A^{it} · A^{-it} = 1`. -/
lemma upow_mul_upow_neg {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    upow hA t * upow hA (-t) = 1 := by
  rw [upow_add, add_neg_cancel, upow_zero]

/-- Adjoint of a conjugated diagonal: `(W D W⋆)⋆ = W D⋆ W⋆`. -/
private lemma star_conj_diag (W : Matrix n n ℂ) (d : n → ℂ) :
    star (W * diagonal d * star W) = W * diagonal (star d) * star W := by
  rw [star_mul, star_mul, star_star, Matrix.star_eq_conjTranspose (diagonal d),
    Matrix.diagonal_conjTranspose, ← mul_assoc]

/-- The adjoint of a complex power conjugates the exponent: `(A^z)⋆ = A^{conj z}`. -/
lemma star_cpow {A : Matrix n n ℂ} (hA : A.PosDef) (z : ℂ) :
    star (cpow hA z) = cpow hA (starRingEnd ℂ z) := by
  have hfun : star (fun i => Complex.exp (z * (Real.log (hA.1.eigenvalues i) : ℂ)))
      = (fun i => Complex.exp (starRingEnd ℂ z * (Real.log (hA.1.eigenvalues i) : ℂ))) := by
    funext i
    rw [Pi.star_apply, ← starRingEnd_apply, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [cpow, cpow, star_conj_diag, hfun]

/-- The adjoint of a unitary power reverses the parameter: `(A^{it})⋆ = A^{-it}`. -/
lemma star_upow {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    star (upow hA t) = upow hA (-t) := by
  simp only [upow, star_cpow]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-! ## Zero-corner / zero-coupling for positive-semidefinite matrices -/

/-- **Off-diagonal vanishing.** In a positive-semidefinite matrix, if a diagonal entry vanishes
then so does the whole corresponding row: `M p p = 0 ⟹ M p q = 0`. -/
lemma posSemidef_offDiag_eq_zero {ι : Type*}
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) {p q : ι} (hpp : M p p = 0) : M p q = 0 := by
  by_cases hpq : p = q
  · rw [← hpq, hpp]
  · set f : Fin 2 → ι := ![p, q] with hf
    have hN : (M.submatrix f f).PosSemidef := hM.submatrix f
    have hdet : (0 : ℂ) ≤ (M.submatrix f f).det := hN.det_nonneg
    have e00 : (M.submatrix f f) 0 0 = M p p := by simp [Matrix.submatrix_apply, hf]
    have e01 : (M.submatrix f f) 0 1 = M p q := by simp [Matrix.submatrix_apply, hf]
    have e10 : (M.submatrix f f) 1 0 = M q p := by simp [Matrix.submatrix_apply, hf]
    have e11 : (M.submatrix f f) 1 1 = M q q := by simp [Matrix.submatrix_apply, hf]
    rw [Matrix.det_fin_two, e00, e01, e10, e11, hpp, zero_mul, zero_sub] at hdet
    have hqp : M q p = star (M p q) := (hM.1.apply q p).symm
    have key : M p q * M q p = (Complex.normSq (M p q) : ℂ) := by
      rw [hqp]; exact Complex.mul_conj (M p q)
    rw [key] at hdet
    have h2 : (0 : ℝ) ≤ -Complex.normSq (M p q) := by
      have := (Complex.le_def.mp hdet).1
      simpa using this
    exact Complex.normSq_eq_zero.mp (le_antisymm (by linarith) (Complex.normSq_nonneg _))

/-- **Zero-corner ⟹ zero-coupling.** A positive-semidefinite block matrix over `Fin 2 × Fin N`
with vanishing `(0,0)`-block has vanishing `(0,1)`-coupling block. -/
lemma posSemidef_zeroCorner_zeroCoupling {N : ℕ}
    {M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ} (hM : M.PosSemidef)
    (h00 : M.submatrix (fun j : Fin N => ((0 : Fin 2), j)) (fun j : Fin N => ((0 : Fin 2), j))
      = 0) :
    M.submatrix (fun j : Fin N => ((0 : Fin 2), j)) (fun j : Fin N => ((1 : Fin 2), j)) = 0 := by
  ext i j
  have hdiag : M ((0 : Fin 2), i) ((0 : Fin 2), i) = 0 := by
    have := congrFun (congrFun h00 i) i
    simpa [Matrix.submatrix_apply] using this
  have hz := posSemidef_offDiag_eq_zero hM (p := ((0 : Fin 2), i)) (q := ((1 : Fin 2), j)) hdiag
  simpa [Matrix.submatrix_apply] using hz

/-! ## The Stinespring isometry of a Kraus channel -/

/-- The **Stinespring isometry** `V : ℂ^n → ℂ^n ⊗ ℂ^ι` of a Kraus channel, as a matrix with rows
indexed by `n × ι` and columns by `n`: `V (a, i) k = (K i) a k`. -/
def channelIsometry (Λ : KrausChannel n) : Matrix (n × Λ.ι) n ℂ :=
  Matrix.of fun p k => Λ.K p.2 p.1 k

@[simp] lemma channelIsometry_apply (Λ : KrausChannel n) (p : n × Λ.ι) (k : n) :
    channelIsometry Λ p k = Λ.K p.2 p.1 k := rfl

/-- The dilation `V` is an **isometry**: `V⋆ V = 1`, which is exactly the Kraus completeness
relation `∑ᵢ Kᵢ⋆ Kᵢ = 1`. -/
lemma channelIsometry_isometry (Λ : KrausChannel n) :
    (channelIsometry Λ)ᴴ * channelIsometry Λ = 1 := by
  have hstep : (channelIsometry Λ)ᴴ * channelIsometry Λ = ∑ i, (Λ.K i)ᴴ * Λ.K i := by
    ext k l
    rw [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [channelIsometry, Matrix.conjTranspose_apply]
  rw [hstep, Λ.htp]

/-- **Stinespring dilation identity for the Heisenberg adjoint.** With the pure ancilla `ℂ^ι`,
`V⋆ (Y ⊗ 1) V = Λ† Y = ∑ᵢ Kᵢ⋆ Y Kᵢ`. -/
lemma channelIsometry_adj (Λ : KrausChannel n) (Y : Matrix n n ℂ) :
    letI := Classical.decEq Λ.ι
    (channelIsometry Λ)ᴴ * (Y ⊗ₖ (1 : Matrix Λ.ι Λ.ι ℂ)) * channelIsometry Λ = Λ.adj Y := by
  classical
  ext k l
  rw [Matrix.mul_apply, KrausChannel.adj, Matrix.sum_apply, Fintype.sum_prod_type]
  have hRHS : ∀ i : Λ.ι, ((Λ.K i)ᴴ * Y * Λ.K i) k l
      = ∑ b : n, ∑ a : n, star (Λ.K i a k) * Y a b * Λ.K i b l := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_apply]
  have hLHS : ∀ b j, ((channelIsometry Λ)ᴴ * (Y ⊗ₖ (1 : Matrix Λ.ι Λ.ι ℂ))) k (b, j)
      = ∑ a : n, star (Λ.K j a k) * Y a b := by
    intro b j
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro i _ hij
      apply Finset.sum_eq_zero
      intro a _
      rw [Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.one_apply, if_neg hij,
        mul_zero, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.one_apply, if_pos rfl,
        mul_one, channelIsometry_apply]
  simp_rw [hRHS, hLHS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [channelIsometry_apply]

/-! ## The modular `it`-intertwining -/

/-- **The modular `it`-intertwining property.** The channel adjoint carries the output relative
modular flow to the input one: `Λ†( (Λρ)^{it} (Λσ)^{-it} ) = ρ^{it} σ^{-it}` for all `t`. -/
def IntertwinesIt {ρ σ : DensityMatrix n} {Λ : KrausChannel n}
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef) : Prop :=
  ∀ t : ℝ, Λ.adj (upow hΛρ t * upow hΛσ (-t)) = upow hρ t * upow hσ (-t)

end Oseledets.OperatorEntropy.Lieb

end



