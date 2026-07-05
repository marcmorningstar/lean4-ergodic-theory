/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.Dilation

/-!
# Joint convexity of the operator perspective (Effros' theorem, Lieb keystone)

Given an operator-convex function `f` on an interval `I`, the **operator perspective**

`P_f(L, R) = R^{1 / 2} · f(R^{-1 / 2} L R^{-1 / 2}) · R^{1 / 2}`

is jointly convex in the pair `(L, R)` (with `R` positive definite).  This is Effros' theorem,
the operator analogue of the fact that the perspective `(x, y) ↦ y f(x / y)` of a convex `f` is
jointly convex.

The proof is the Effros argument: the perspective's joint convexity is obtained by a single
application of the Hansen–Pedersen–Jensen operator-Jensen inequality (`hpj_affine`).  Writing
`R = c R₁ + (1-c) R₂`, one chooses the contraction pair

`A = √c · (R₁^{1 / 2} R^{-1 / 2})`,  `B = √(1-c) · (R₂^{1 / 2} R^{-1 / 2})`

which satisfies `A⋆A + B⋆B = R^{-1 / 2} R R^{-1 / 2} = 1`, and the self-adjoint arguments
`X = R₁^{-1 / 2} L₁ R₁^{-1 / 2}`, `Y = R₂^{-1 / 2} L₂ R₂^{-1 / 2}`.  Conjugating the resulting
Hansen–Pedersen–Jensen inequality by `R^{1 / 2}` gives exactly the joint-convexity estimate.

## Main results

* `ErgodicTheory.OperatorEntropy.Lieb.operatorPerspective`: the operator perspective.
* `ErgodicTheory.OperatorEntropy.Lieb.operatorPerspective_jointly_convex`: Effros' theorem.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

variable {N : ℕ}

/-! ## Functional-calculus power algebra for positive-definite matrices -/

/-- Every real power `M ^ y` (continuous functional calculus) is self-adjoint, since it is
nonnegative in the Loewner order. -/
lemma isSelfAdjoint_rpow (M : Matrix (Fin N) (Fin N) ℂ) (y : ℝ) :
    IsSelfAdjoint (M ^ y) :=
  IsSelfAdjoint.of_nonneg CFC.rpow_nonneg

/-- `R^{1 / 2} · R^{1 / 2} = R` for a positive-definite matrix `R`. -/
lemma rpow_half_mul_half {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.PosDef) :
    R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) = R := by
  have h : (1 / 2 + 1 / 2 : ℝ) = 1 := by norm_num
  rw [← CFC.rpow_add hR.isUnit, h, CFC.rpow_one R hR.isStrictlyPositive.nonneg]

/-- `R^{-1 / 2} · R · R^{-1 / 2} = 1` for a positive-definite matrix `R`. -/
lemma rpow_neg_half_conj {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.PosDef) :
    R ^ (-(1 / 2) : ℝ) * R * R ^ (-(1 / 2) : ℝ) = 1 := by
  have hsp := hR.isStrictlyPositive
  calc R ^ (-(1 / 2) : ℝ) * R * R ^ (-(1 / 2) : ℝ)
      = R ^ (-(1 / 2) : ℝ) * (R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) * R ^ (-(1 / 2) : ℝ) := by
        rw [rpow_half_mul_half hR]
    _ = (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) * (R ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)) := by
        simp only [mul_assoc]
    _ = 1 * 1 := by
        rw [CFC.rpow_neg_mul_rpow (1 / 2) hsp, CFC.rpow_mul_rpow_neg (1 / 2) hsp]
    _ = 1 := mul_one 1

/-- The "sandwich" cancellation: `R^{1 / 2} (R^{-1 / 2} Z R^{-1 / 2}) R^{1 / 2} = Z`. -/
lemma rpow_half_conj_neg_half {R : Matrix (Fin N) (Fin N) ℂ}
    (Z : Matrix (Fin N) (Fin N) ℂ) (hR : R.PosDef) :
    R ^ (1 / 2 : ℝ) * (R ^ (-(1 / 2) : ℝ) * Z * R ^ (-(1 / 2) : ℝ)) * R ^ (1 / 2 : ℝ) = Z := by
  have hsp := hR.isStrictlyPositive
  calc R ^ (1 / 2 : ℝ) * (R ^ (-(1 / 2) : ℝ) * Z * R ^ (-(1 / 2) : ℝ)) * R ^ (1 / 2 : ℝ)
      = (R ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)) * Z * (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) := by
        simp only [mul_assoc]
    _ = 1 * Z * 1 := by
        rw [CFC.rpow_mul_rpow_neg (1 / 2) hsp, CFC.rpow_neg_mul_rpow (1 / 2) hsp]
    _ = Z := by rw [one_mul, mul_one]

/-! ## Scalar-weighted conjugation identities -/

/-- Conjugating `M` by `t • (P Q)` with `P, Q` self-adjoint. -/
lemma smul_conj_mid (t : ℝ) (P Q M : Matrix (Fin N) (Fin N) ℂ)
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q) :
    star (t • (P * Q)) * M * (t • (P * Q)) = (t * t) • (Q * (P * M * P) * Q) := by
  have hst : star (t • (P * Q)) = t • (Q * P) := by
    rw [star_smul, star_trivial, star_mul, hP.star_eq, hQ.star_eq]
  rw [hst, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  simp only [mul_assoc]

/-- Gram form: `‖t • (P Q)‖²`-type conjugation by `t • (P Q)`. -/
lemma smul_conj_self (t : ℝ) (P Q : Matrix (Fin N) (Fin N) ℂ)
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q) :
    star (t • (P * Q)) * (t • (P * Q)) = (t * t) • (Q * (P * P) * Q) := by
  have hst : star (t • (P * Q)) = t • (Q * P) := by
    rw [star_smul, star_trivial, star_mul, hP.star_eq, hQ.star_eq]
  rw [hst, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  simp only [mul_assoc]

/-! ## The operator perspective and Effros' theorem -/

/-- The **operator perspective** of `f` at `(L, R)`:
`R^{1 / 2} · f(R^{-1 / 2} L R^{-1 / 2}) · R^{1 / 2}`. -/
def operatorPerspective (f : ℝ → ℝ) (L R : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  CFC.rpow R (1 / 2) * cfc f (CFC.rpow R (-(1 / 2)) * L * CFC.rpow R (-(1 / 2)))
    * CFC.rpow R (1 / 2)

set_option maxHeartbeats 800000 in -- large Effros dilation / cfc-conjugation assembly
/-- **Effros' theorem: the operator perspective is jointly convex.** For an operator-convex `f`
on `I`, positive-definite `R₁, R₂`, self-adjoint arguments with spectra in `I`, and `c ∈ [0, 1]`,
`P_f(cL₁+(1-c)L₂, cR₁+(1-c)R₂) ≤ c P_f(L₁, R₁) + (1-c) P_f(L₂, R₂)`. -/
theorem operatorPerspective_jointly_convex (f : ℝ → ℝ) (I : Set ℝ) (hf : OperatorConvexOn I f)
    (L₁ R₁ L₂ R₂ : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    (hX₁ : IsSelfAdjoint (CFC.rpow R₁ (-(1 / 2)) * L₁ * CFC.rpow R₁ (-(1 / 2)))
      ∧ spectrum ℝ (CFC.rpow R₁ (-(1 / 2)) * L₁ * CFC.rpow R₁ (-(1 / 2))) ⊆ I)
    (hX₂ : IsSelfAdjoint (CFC.rpow R₂ (-(1 / 2)) * L₂ * CFC.rpow R₂ (-(1 / 2)))
      ∧ spectrum ℝ (CFC.rpow R₂ (-(1 / 2)) * L₂ * CFC.rpow R₂ (-(1 / 2))) ⊆ I) :
    operatorPerspective f (c • L₁ + (1 - c) • L₂) (c • R₁ + (1 - c) • R₂)
      ≤ c • operatorPerspective f L₁ R₁ + (1 - c) • operatorPerspective f L₂ R₂ := by
  simp only [CFC.rpow_eq_pow] at hX₁ hX₂
  have hc0 : (0 : ℝ) ≤ c := hc.1
  have hc1 : (0 : ℝ) ≤ 1 - c := by linarith [hc.2]
  set R := c • R₁ + (1 - c) • R₂ with hRdef
  have hR : R.PosDef := by
    rw [hRdef]
    rcases eq_or_lt_of_le hc0 with hc0' | hc0'
    · rw [← hc0']
      simp only [zero_smul, zero_add, sub_zero, one_smul]
      exact hR₂
    · exact (hR₁.smul hc0').add_posSemidef (hR₂.posSemidef.smul hc1)
  -- self-adjointness of the powers used below
  have hRh : IsSelfAdjoint (R ^ (1 / 2 : ℝ)) := isSelfAdjoint_rpow R (1 / 2)
  -- the factoring identity through the sandwich `R^{-1 / 2} · _ · R^{-1 / 2}`
  have factor : ∀ u v : Matrix (Fin N) (Fin N) ℂ,
      R ^ (-(1 / 2) : ℝ) * (c • u + (1 - c) • v) * R ^ (-(1 / 2) : ℝ)
        = c • (R ^ (-(1 / 2) : ℝ) * u * R ^ (-(1 / 2) : ℝ))
          + (1 - c) • (R ^ (-(1 / 2) : ℝ) * v * R ^ (-(1 / 2) : ℝ)) := by
    intro u v
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  -- contraction identity `A⋆A + B⋆B = 1`
  have hAB : star (Real.sqrt c • (R₁ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
        * (Real.sqrt c • (R₁ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
      + star (Real.sqrt (1 - c) • (R₂ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
        * (Real.sqrt (1 - c) • (R₂ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ))) = 1 := by
    rw [smul_conj_self (Real.sqrt c) (R₁ ^ (1 / 2 : ℝ)) (R ^ (-(1 / 2) : ℝ))
          (isSelfAdjoint_rpow R₁ (1 / 2)) (isSelfAdjoint_rpow R (-(1 / 2))),
        smul_conj_self (Real.sqrt (1 - c)) (R₂ ^ (1 / 2 : ℝ)) (R ^ (-(1 / 2) : ℝ))
          (isSelfAdjoint_rpow R₂ (1 / 2)) (isSelfAdjoint_rpow R (-(1 / 2))),
        rpow_half_mul_half hR₁, rpow_half_mul_half hR₂,
        Real.mul_self_sqrt hc0, Real.mul_self_sqrt hc1, ← factor R₁ R₂, ← hRdef]
    exact rpow_neg_half_conj hR
  -- the Hansen–Pedersen–Jensen inequality for the chosen contraction/arguments
  have hpj := hpj_affine f I hf
    (Real.sqrt c • (R₁ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
    (Real.sqrt (1 - c) • (R₂ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
    (R₁ ^ (-(1 / 2) : ℝ) * L₁ * R₁ ^ (-(1 / 2) : ℝ))
    (R₂ ^ (-(1 / 2) : ℝ) * L₂ * R₂ ^ (-(1 / 2) : ℝ))
    hAB hX₁ hX₂
  -- conjugate the HPJ inequality by `R^{1 / 2}`
  have hconj := hRh.conjugate_le_conjugate hpj
  -- generic conjugated-term identity for the right-hand side
  have term_eq : ∀ (t : ℝ) (S M : Matrix (Fin N) (Fin N) ℂ), 0 ≤ t → S.PosDef →
      R ^ (1 / 2 : ℝ) * (star (Real.sqrt t • (S ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ))) * M
          * (Real.sqrt t • (S ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))) * R ^ (1 / 2 : ℝ)
        = t • (S ^ (1 / 2 : ℝ) * M * S ^ (1 / 2 : ℝ)) := by
    intro t S M ht _hS
    rw [smul_conj_mid (Real.sqrt t) (S ^ (1 / 2 : ℝ)) (R ^ (-(1 / 2) : ℝ)) M
          (isSelfAdjoint_rpow S (1 / 2)) (isSelfAdjoint_rpow R (-(1 / 2))),
        mul_smul_comm, smul_mul_assoc, Real.mul_self_sqrt ht,
        rpow_half_conj_neg_half (S ^ (1 / 2 : ℝ) * M * S ^ (1 / 2 : ℝ)) hR]
  -- rewrite the left-hand argument of the cfc via the factoring identity
  have hLid : star (Real.sqrt c • (R₁ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
        * (R₁ ^ (-(1 / 2) : ℝ) * L₁ * R₁ ^ (-(1 / 2) : ℝ))
        * (Real.sqrt c • (R₁ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
      + star (Real.sqrt (1 - c) • (R₂ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
        * (R₂ ^ (-(1 / 2) : ℝ) * L₂ * R₂ ^ (-(1 / 2) : ℝ))
        * (Real.sqrt (1 - c) • (R₂ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
      = R ^ (-(1 / 2) : ℝ) * (c • L₁ + (1 - c) • L₂) * R ^ (-(1 / 2) : ℝ) := by
    rw [smul_conj_mid (Real.sqrt c) (R₁ ^ (1 / 2 : ℝ)) (R ^ (-(1 / 2) : ℝ))
          (R₁ ^ (-(1 / 2) : ℝ) * L₁ * R₁ ^ (-(1 / 2) : ℝ))
          (isSelfAdjoint_rpow R₁ (1 / 2)) (isSelfAdjoint_rpow R (-(1 / 2))),
        smul_conj_mid (Real.sqrt (1 - c)) (R₂ ^ (1 / 2 : ℝ)) (R ^ (-(1 / 2) : ℝ))
          (R₂ ^ (-(1 / 2) : ℝ) * L₂ * R₂ ^ (-(1 / 2) : ℝ))
          (isSelfAdjoint_rpow R₂ (1 / 2)) (isSelfAdjoint_rpow R (-(1 / 2))),
        rpow_half_conj_neg_half L₁ hR₁, rpow_half_conj_neg_half L₂ hR₂,
        Real.mul_self_sqrt hc0, Real.mul_self_sqrt hc1, factor L₁ L₂]
  -- rewrite the right-hand side of the conjugated inequality
  have hRHS : R ^ (1 / 2 : ℝ)
        * (star (Real.sqrt c • (R₁ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
            * cfc f (R₁ ^ (-(1 / 2) : ℝ) * L₁ * R₁ ^ (-(1 / 2) : ℝ))
            * (Real.sqrt c • (R₁ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
          + star (Real.sqrt (1 - c) • (R₂ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)))
            * cfc f (R₂ ^ (-(1 / 2) : ℝ) * L₂ * R₂ ^ (-(1 / 2) : ℝ))
            * (Real.sqrt (1 - c) • (R₂ ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ))))
        * R ^ (1 / 2 : ℝ)
      = c • (R₁ ^ (1 / 2 : ℝ) * cfc f (R₁ ^ (-(1 / 2) : ℝ) * L₁ * R₁ ^ (-(1 / 2) : ℝ))
            * R₁ ^ (1 / 2 : ℝ))
        + (1 - c) • (R₂ ^ (1 / 2 : ℝ) * cfc f (R₂ ^ (-(1 / 2) : ℝ) * L₂ * R₂ ^ (-(1 / 2) : ℝ))
            * R₂ ^ (1 / 2 : ℝ)) := by
    rw [mul_add, add_mul,
        term_eq c R₁ (cfc f (R₁ ^ (-(1 / 2) : ℝ) * L₁ * R₁ ^ (-(1 / 2) : ℝ))) hc0 hR₁,
        term_eq (1 - c) R₂ (cfc f (R₂ ^ (-(1 / 2) : ℝ) * L₂ * R₂ ^ (-(1 / 2) : ℝ))) hc1 hR₂]
  rw [hLid] at hconj
  rw [hRHS] at hconj
  simp only [operatorPerspective, CFC.rpow_eq_pow]
  exact hconj

end ErgodicTheory.OperatorEntropy.Lieb

end
