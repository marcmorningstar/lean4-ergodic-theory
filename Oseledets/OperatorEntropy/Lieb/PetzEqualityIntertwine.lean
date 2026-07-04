/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
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

* `cpow` / `upow`: the complex power `A^z` and the unitary power `A^{it}` of a positive-definite
  matrix via its eigendecomposition (there is no `ℂ`-valued cfc on matrices).
* `cpow_zero`, `cpow_mul_cpow`, `upow_add`, `upow_mul_upow_neg`, `star_upow`: the basic
  one-parameter-group / unitarity laws of these powers.
* `IntertwinesIt`: the modular `it`-intertwining property.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

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

/-! ## The modular `it`-intertwining -/

/-- **The modular `it`-intertwining property.** The channel adjoint carries the output relative
modular flow to the input one: `Λ†( (Λρ)^{it} (Λσ)^{-it} ) = ρ^{it} σ^{-it}` for all `t`. -/
def IntertwinesIt {ρ σ : DensityMatrix n} {Λ : KrausChannel n}
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef) : Prop :=
  ∀ t : ℝ, Λ.adj (upow hΛρ t * upow hΛσ (-t)) = upow hρ t * upow hσ (-t)

end Oseledets.OperatorEntropy.Lieb

end



