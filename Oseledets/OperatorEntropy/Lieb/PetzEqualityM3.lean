/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.PetzEqualityIntertwine
import Oseledets.OperatorEntropy.Lieb.ModularOperator
import Oseledets.OperatorEntropy.Lieb.StrictOperatorConvex

/-!
# Petz equality: the modular `it`-intertwining headline (module M3), resolvent route

This module attacks the analytic linchpin `equality_imp_intertwinesIt` of the Petz-equality
sufficiency direction (issue #28) along the **resolvent (Petz 2003)** route.

The reusable self-contained heart is the **contraction-equality lemma**
`contraction_adjoint_eq`: for a contraction `V` on inner-product spaces, saturation of the norm on
the adjoint side, `‖V⋆ ξ‖ = ‖ξ‖`, forces `V V⋆ ξ = ξ` — the partial-isometry fixed-vector fact
that turns *equality in the data-processing inequality* into a genuine intertwining relation on the
cyclic vector.  The proof is the one-line Hilbert-space computation

`‖ξ − V V⋆ ξ‖² = ‖ξ‖² − 2·Re⟪ξ, V V⋆ ξ⟫ + ‖V V⋆ ξ‖² = ‖ξ‖² − 2‖V⋆ξ‖² + ‖V V⋆ξ‖² ≤ 0`,

using `⟪ξ, V V⋆ ξ⟫ = ⟪V⋆ξ, V⋆ξ⟫` (adjoint) and `‖V V⋆ ξ‖ ≤ ‖V⋆ ξ‖` (contraction).
-/

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker InnerProductSpace

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

/-! ## The contraction-equality (partial-isometry) lemma -/

section Contraction

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Contraction-equality (partial-isometry fixed-vector) lemma.** If `V` is a contraction
(`‖V x‖ ≤ ‖x‖` for all `x`) and the norm is saturated on the adjoint side at a vector `ξ`, i.e.
`‖V⋆ ξ‖ = ‖ξ‖`, then `V` recovers `ξ` from its adjoint image: `V (V⋆ ξ) = ξ`.

This is the finite-dimensional partial-isometry fact underlying the equality case of the
data-processing inequality: equality forces the contraction to act isometrically on the relevant
cyclic vector, hence to intertwine (rather than merely dominate) the two operators. -/
theorem contraction_adjoint_eq
    (V : E →L[ℂ] F) (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (ξ : F)
    (h : ‖(ContinuousLinearMap.adjoint V) ξ‖ = ‖ξ‖) :
    V (ContinuousLinearMap.adjoint V ξ) = ξ := by
  set η := ContinuousLinearMap.adjoint V ξ with hη
  -- `⟪ξ, V η⟫ = ⟪η, η⟫` by the adjoint relation
  have hinner : (inner ℂ ξ (V η)) = (inner ℂ η η) := by
    rw [← ContinuousLinearMap.adjoint_inner_left V η ξ, ← hη]
  -- `‖η‖ = ‖ξ‖`
  have hnorm_eta : ‖η‖ = ‖ξ‖ := by rw [hη]; exact h
  -- real part of the cross term equals `‖ξ‖²`
  have hre : RCLike.re (inner ℂ ξ (V η)) = ‖ξ‖ ^ 2 := by
    rw [hinner, inner_self_eq_norm_sq (𝕜 := ℂ) η, hnorm_eta]
  -- contraction bound at `η`
  have hVη : ‖V η‖ ≤ ‖ξ‖ := by rw [← hnorm_eta]; exact hV η
  -- the squared distance is `≤ 0`
  have hbound : ‖ξ - V η‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hre]
    nlinarith [mul_self_le_mul_self (norm_nonneg (V η)) hVη, sq_nonneg ‖V η‖,
      norm_nonneg (V η), norm_nonneg ξ]
  have hzero : ‖ξ - V η‖ = 0 := by
    have hsq : ‖ξ - V η‖ ^ 2 = 0 := le_antisymm hbound (by positivity)
    exact pow_eq_zero_iff (by norm_num) |>.mp hsq
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

/-- **Symmetric contraction-equality.** If `V` is a contraction and the norm is saturated on the
*forward* side at `ξ`, i.e. `‖V ξ‖ = ‖ξ‖`, then `V⋆ V ξ = ξ`. Obtained from
`contraction_adjoint_eq` applied to the (also contractive) adjoint `V⋆`. -/
theorem contraction_self_adjoint_eq
    (V : E →L[ℂ] F) (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (ξ : E)
    (h : ‖V ξ‖ = ‖ξ‖) :
    (ContinuousLinearMap.adjoint V) (V ξ) = ξ := by
  -- the operator norm of a contraction is `≤ 1`
  have hVnorm : ‖V‖ ≤ 1 := V.opNorm_le_bound (by norm_num) (fun x => by simpa using hV x)
  -- the adjoint is norm-preserving, hence also a contraction
  have hnorm : ‖ContinuousLinearMap.adjoint V‖ = ‖V‖ :=
    ContinuousLinearMap.adjoint.norm_map V
  have hW : ∀ y, ‖(ContinuousLinearMap.adjoint V) y‖ ≤ ‖y‖ := by
    intro y
    calc ‖(ContinuousLinearMap.adjoint V) y‖
        ≤ ‖ContinuousLinearMap.adjoint V‖ * ‖y‖ := (ContinuousLinearMap.adjoint V).le_opNorm y
      _ ≤ 1 * ‖y‖ := by rw [hnorm]; gcongr
      _ = ‖y‖ := one_mul _
  -- apply the adjoint-side lemma to `W = V⋆`, whose adjoint is `V`
  have hmain := contraction_adjoint_eq (ContinuousLinearMap.adjoint V) hW ξ
    (by rw [ContinuousLinearMap.adjoint_adjoint]; exact h)
  rwa [ContinuousLinearMap.adjoint_adjoint] at hmain

end Contraction

end Oseledets.OperatorEntropy.Lieb

end
