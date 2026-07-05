/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.StrictLog
import ErgodicTheory.OperatorEntropy.Lieb.PetzSufficiencyB

/-!
# The rigidity tail of Petz sufficiency (issue #28, STEP 5–6)

This module proves the **abstract rigidity tail** of the sufficiency (`⟹`) direction of the Petz
equality theorem: equality in the operator-Jensen inequality for `-log` at a cyclic vector forces
the isometric compression to be *exact* on that vector, hence the isometry intertwines the whole
continuous functional calculus there.

## Strategy (resolvent route, Petz 2003)

Let `W` be an isometry (`Wᴴ W = 1`) and `Δ` positive definite.  Write `Y = Wᴴ Δ W` for the
compression.  The key algebraic fact (`isometry_quadratic_gap_identity`) is that, for every positive
definite `X` and the *error vector*

`a := X⁻¹ (W ξ) - W (Y_X⁻¹ ξ)`,   `Y_X := Wᴴ X W`,

the `X`-weighted square equals the resolvent gap quadratic form:

`⟪a, X a⟫ = ⟪ξ, (Wᴴ X⁻¹ W - Y_X⁻¹) ξ⟫`.

Because the left side is `≥ 0` (positive definiteness) and vanishes exactly when `a = 0`, this
single identity yields *both* the per-resolvent operator convexity `(Wᴴ X⁻¹ W - Y_X⁻¹) ⪰ 0` at `ξ`
*and* the rigidity: saturation `⟪ξ, (Wᴴ X⁻¹ W - Y_X⁻¹) ξ⟫ = 0` forces `X⁻¹ (W ξ) = W (Y_X⁻¹ ξ)`.

Feeding `X = Δ + t` and integrating the scalar representation `-log x = ∫₀^∞ ((x+t)⁻¹ - (1+t)⁻¹)`
(`ErgodicTheory.OperatorEntropy.Lieb.cfc_neg_log_eq_integral`) turns the `-log` gap into an integral of
these nonnegative resolvent gaps; a zero integral of a nonnegative continuous integrand is pointwise
zero, so each resolvent intertwines on `ξ`.  Finally the resolvent readoff
(`ErgodicTheory.OperatorEntropy.Lieb.exists_resolvent_combo`) upgrades resolvent intertwining to
`cfc g`-intertwining for every continuous `g`.

## Main results

* `isometry_quadratic_gap_identity`: the `X`-weighted square identity above.
* `isometry_resolvent_gap_nonneg`: the per-resolvent operator convexity at `ξ`.
* `isometry_resolvent_saturation_intertwines`: saturation at `ξ` ⟹ resolvent intertwining.
-/

open Matrix MeasureTheory Set
open scoped MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

variable {M N : ℕ}

/-! ## Adjoint bookkeeping -/

/-- Adjoint move for the sesquilinear form: `⟪P ξ, v⟫ = ⟪ξ, Pᴴ v⟫`. -/
lemma star_mulVec_dotProduct (P : Matrix (Fin M) (Fin N) ℂ) (ξ : Fin N → ℂ) (v : Fin M → ℂ) :
    star (P *ᵥ ξ) ⬝ᵥ v = star ξ ⬝ᵥ (Pᴴ *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec]

/-- An isometry `W` (`Wᴴ W = 1`) acts injectively by `mulVec`. -/
lemma mulVec_injective_of_isometry (W : Matrix (Fin M) (Fin N) ℂ) (hW : Wᴴ * W = 1) :
    Function.Injective (W *ᵥ ·) := by
  intro a b hab
  have hab' : W *ᵥ a = W *ᵥ b := hab
  have h : Wᴴ *ᵥ (W *ᵥ a) = Wᴴ *ᵥ (W *ᵥ b) := by rw [hab']
  rwa [mulVec_mulVec, mulVec_mulVec, hW, one_mulVec, one_mulVec] at h

/-- The isometric compression `Wᴴ X W` of a positive definite matrix is positive definite. -/
lemma posDef_isometry_compression (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} (hW : Wᴴ * W = 1) (hX : X.PosDef) :
    (Wᴴ * X * W).PosDef :=
  hX.conjTranspose_mul_mul_same (mulVec_injective_of_isometry W hW)

/-! ## The quadratic gap identity -/

/-- **The `X`-weighted square = resolvent gap quadratic form.**  For an isometry `W`, positive
definite `X`, compression `Y := Wᴴ X W`, and the error vector `a := X⁻¹ (W ξ) - W (Y⁻¹ ξ)`, the
`X`-weighted square of `a` equals the gap quadratic form at `ξ`:

`star a ⬝ᵥ (X *ᵥ a) = star ξ ⬝ᵥ ((Wᴴ X⁻¹ W - Y⁻¹) *ᵥ ξ)`. -/
lemma isometry_quadratic_gap_identity (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} (ξ : Fin N → ℂ) (hW : Wᴴ * W = 1) (hX : X.PosDef) :
    star (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ))
        ⬝ᵥ (X *ᵥ (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ)))
      = star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ) := by
  set Y := Wᴴ * X * W with hYdef
  have hY : Y.PosDef := posDef_isometry_compression W hW hX
  have hXdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit
  have hYdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  have hX1 : X⁻¹ * X = 1 := nonsing_inv_mul X hXdet
  have hX2 : X * X⁻¹ = 1 := mul_nonsing_inv X hXdet
  have hY2 : Y * Y⁻¹ = 1 := mul_nonsing_inv Y hYdet
  have hXinvH : X⁻¹ᴴ = X⁻¹ := hX.1.inv
  have hYinvH : Y⁻¹ᴴ = Y⁻¹ := hY.1.inv
  -- `P` and its adjoint
  set P : Matrix (Fin M) (Fin N) ℂ := X⁻¹ * W - W * Y⁻¹ with hPdef
  have hPH : Pᴴ = Wᴴ * X⁻¹ - Y⁻¹ * Wᴴ := by
    rw [hPdef]
    simp only [conjTranspose_sub, conjTranspose_mul, hXinvH, hYinvH]
  -- the pure matrix identity `Pᴴ X P = Wᴴ X⁻¹ W - Y⁻¹`
  have hYWXW : Wᴴ * X * W = Y := hYdef.symm
  have hPXP : Pᴴ * X * P = Wᴴ * X⁻¹ * W - Y⁻¹ := by
    have hPXe : Pᴴ * X = Wᴴ - Y⁻¹ * Wᴴ * X := by
      rw [hPH, Matrix.sub_mul, Matrix.mul_assoc Wᴴ X⁻¹ X, hX1, Matrix.mul_one]
    rw [hPXe, hPdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
    -- goal: (Wᴴ*(X⁻¹*W) - (Y⁻¹*Wᴴ*X)*(X⁻¹*W)) - (Wᴴ*(W*Y⁻¹) - (Y⁻¹*Wᴴ*X)*(W*Y⁻¹))
    --        = Wᴴ*X⁻¹*W - Y⁻¹
    have t1 : Wᴴ * (X⁻¹ * W) = Wᴴ * X⁻¹ * W := (Matrix.mul_assoc Wᴴ X⁻¹ W).symm
    have t2 : Y⁻¹ * Wᴴ * X * (X⁻¹ * W) = Y⁻¹ := by
      rw [Matrix.mul_assoc (Y⁻¹ * Wᴴ) X (X⁻¹ * W), ← Matrix.mul_assoc X X⁻¹ W, hX2,
        Matrix.one_mul, Matrix.mul_assoc Y⁻¹ Wᴴ W, hW, Matrix.mul_one]
    have t3 : Wᴴ * (W * Y⁻¹) = Y⁻¹ := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
    have t4 : Y⁻¹ * Wᴴ * X * (W * Y⁻¹) = Y⁻¹ := by
      have hreassoc : Y⁻¹ * Wᴴ * X * (W * Y⁻¹) = Y⁻¹ * (Wᴴ * X * W) * Y⁻¹ := by
        simp only [Matrix.mul_assoc]
      rw [hreassoc, hYWXW, nonsing_inv_mul Y hYdet, Matrix.one_mul]
    rw [t1, t2, t3, t4]
    abel
  -- rewrite the error vector as `P *ᵥ ξ`
  have ha_eq : X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Y⁻¹ *ᵥ ξ) = P *ᵥ ξ := by
    rw [hPdef, sub_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [ha_eq]
  calc star (P *ᵥ ξ) ⬝ᵥ (X *ᵥ (P *ᵥ ξ))
      = star (P *ᵥ ξ) ⬝ᵥ ((X * P) *ᵥ ξ) := by rw [mulVec_mulVec]
    _ = star ξ ⬝ᵥ (Pᴴ *ᵥ ((X * P) *ᵥ ξ)) := star_mulVec_dotProduct P ξ _
    _ = star ξ ⬝ᵥ ((Pᴴ * (X * P)) *ᵥ ξ) := by rw [mulVec_mulVec]
    _ = star ξ ⬝ᵥ ((Pᴴ * X * P) *ᵥ ξ) := by rw [Matrix.mul_assoc]
    _ = star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - Y⁻¹) *ᵥ ξ) := by rw [hPXP]

/-! ## Per-resolvent nonnegativity and rigidity -/

/-- **Per-resolvent operator convexity at `ξ`.** The compression gap `Wᴴ X⁻¹ W - Y⁻¹` (with
`Y = Wᴴ X W`) has nonnegative quadratic form at `ξ`. -/
lemma isometry_resolvent_gap_nonneg (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} (ξ : Fin N → ℂ) (hW : Wᴴ * W = 1) (hX : X.PosDef) :
    0 ≤ (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)).re := by
  rw [← isometry_quadratic_gap_identity W ξ hW hX]
  have := hX.posSemidef.dotProduct_mulVec_nonneg
    (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ))
  exact (Complex.nonneg_iff.mp this).1

/-- **Per-resolvent rigidity.** If the compression gap quadratic form vanishes at `ξ`, then the
isometry intertwines the resolvent on `ξ`: `X⁻¹ (W ξ) = W (Y⁻¹ ξ)`. -/
lemma isometry_resolvent_saturation_intertwines (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} (ξ : Fin N → ℂ) (hW : Wᴴ * W = 1) (hX : X.PosDef)
    (hsat : (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - (Wᴴ * X * W)⁻¹) *ᵥ ξ)).re = 0) :
    X⁻¹ *ᵥ (W *ᵥ ξ) = W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ) := by
  set a := X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ ((Wᴴ * X * W)⁻¹ *ᵥ ξ) with hadef
  have hid : (star a ⬝ᵥ (X *ᵥ a)).re = 0 := by
    rw [hadef, isometry_quadratic_gap_identity W ξ hW hX]; exact hsat
  by_contra hne
  have ha : a ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < star a ⬝ᵥ (X *ᵥ a) := hX.dotProduct_mulVec_pos ha
  have : 0 < (star a ⬝ᵥ (X *ᵥ a)).re := (Complex.pos_iff.mp hpos).1
  rw [hid] at this
  exact lt_irrefl 0 this

/-! ## The resolvent shift and its isometric compression -/

/-- `Wᴴ · (algebraMap c) · W = algebraMap c` for an isometry `W`. -/
lemma isometry_conj_algebraMap (W : Matrix (Fin M) (Fin N) ℂ) (hW : Wᴴ * W = 1) (c : ℝ) :
    Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c * W
      = algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, hW]

/-- `Wᴴ · (Δ + algebraMap c) · W = WᴴΔW + algebraMap c`. -/
lemma isometry_conj_add_algebraMap (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (hW : Wᴴ * W = 1) (c : ℝ) :
    Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c) * W
      = Wᴴ * Δ * W + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) c := by
  rw [Matrix.mul_add, Matrix.add_mul, isometry_conj_algebraMap W hW c]

/-! ## The scalar quadratic-form functional as a continuous linear map -/

/-- The quadratic form `A ↦ ⟪η, A η⟫` as an `ℝ`-linear continuous map on matrices. -/
def qformCLM {k : ℕ} (η : Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star η ⬝ᵥ (A *ᵥ η)
      map_add' := fun A B => by rw [add_mulVec, dotProduct_add]
      map_smul' := fun r A => by
        simp only [RingHom.id_apply]
        rw [Matrix.smul_mulVec, dotProduct_smul] }

lemma qformCLM_apply {k : ℕ} (η : Fin k → ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    qformCLM η A = star η ⬝ᵥ (A *ᵥ η) := rfl

/-- Compressed form: `qformCLM (W ξ) A = ⟪ξ, (Wᴴ A W) ξ⟫`. -/
lemma qformCLM_conj (W : Matrix (Fin M) (Fin N) ℂ) (ξ : Fin N → ℂ)
    (A : Matrix (Fin M) (Fin M) ℂ) :
    qformCLM (W *ᵥ ξ) A = star ξ ⬝ᵥ ((Wᴴ * A * W) *ᵥ ξ) := by
  rw [qformCLM_apply, star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec]

/-! ## Continuity of the resolvent integrand -/

/-- `t ↦ cfc (resIntegrand t) M` is continuous on `(0, ∞)` for positive definite `M`. -/
lemma continuousOn_cfc_resIntegrand {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.PosDef) :
    ContinuousOn (fun t => cfc (resIntegrand t) M) (Ioi (0 : ℝ)) := by
  have heq : (fun t => cfc (resIntegrand t) M)
      = fun t => diagConjCLM (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)
          (fun i => resIntegrand t (hM.1.eigenvalues i)) := by
    funext t; exact cfc_eq_diagConj M hM.1 (resIntegrand t)
  rw [heq]
  apply (diagConjCLM _).continuous.comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  have hpos : 0 < hM.1.eigenvalues i := hM.eigenvalues_pos i
  simp only [resIntegrand]
  apply ContinuousOn.sub
  · apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht; have : (0 : ℝ) < t := ht; positivity
  · apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht; have : (0 : ℝ) < t := ht; positivity

/-! ## The rigidity tail: `-log` gap ⟹ resolvent intertwining -/

/-- **Rigidity tail (resolvent form).** If the isometry `W` (`Wᴴ W = 1`) saturates the
operator-Jensen inequality for `-log` at the cyclic vector `ξ`, then it intertwines every resolvent
of `Δ` on `ξ`: for all `t > 0`,

`(Δ + t)⁻¹ (W ξ) = W ((WᴴΔW + t)⁻¹ ξ)`. -/
theorem isometry_resolvent_intertwine_of_neg_log_eq (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (ξ : Fin N → ℂ) (hW : Wᴴ * W = 1) (hΔ : Δ.PosDef)
    (hgap : (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ
              = cfc (fun x => -Real.log x) (Wᴴ * Δ * W) *ᵥ ξ) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Wᴴ * Δ * W + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ) := by
  classical
  have hWΔW : (Wᴴ * Δ * W).PosDef := posDef_isometry_compression W hW hΔ
  -- The two real-linear functionals composed with `Re`.
  set LMre : Matrix (Fin M) (Fin M) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (qformCLM (W *ᵥ ξ)) with hLMre
  set LNre : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (qformCLM ξ) with hLNre
  -- The nonnegative integrand `F = g1 - g2`.
  set F : ℝ → ℝ := fun t => LMre (cfc (resIntegrand t) Δ)
    - LNre (cfc (resIntegrand t) (Wᴴ * Δ * W)) with hF
  -- Positive definiteness of the shifted matrices.
  have hXt : ∀ t : ℝ, 0 < t → (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t).PosDef :=
    fun t ht => hΔ.add_posSemidef (posDef_algebraMap ht).posSemidef
  -- Integrability of the resolvent integrand families.
  have hintM : IntegrableOn (fun t => cfc (resIntegrand t) Δ) (Ioi 0) :=
    integrableOn_cfc_resIntegrand Δ hΔ
  have hintN : IntegrableOn (fun t => cfc (resIntegrand t) (Wᴴ * Δ * W)) (Ioi 0) :=
    integrableOn_cfc_resIntegrand (Wᴴ * Δ * W) hWΔW
  have hg1int : IntegrableOn (fun t => LMre (cfc (resIntegrand t) Δ)) (Ioi 0) :=
    LMre.integrable_comp hintM
  have hg2int : IntegrableOn (fun t => LNre (cfc (resIntegrand t) (Wᴴ * Δ * W))) (Ioi 0) :=
    LNre.integrable_comp hintN
  -- `F t` equals the gap quadratic form at the shift `Δ + t`.
  have hFeq : ∀ t : ℝ, 0 < t → F t
      = (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
          - (Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W)⁻¹) *ᵥ ξ)).re := by
    intro t ht
    have hAdd := isometry_conj_add_algebraMap W Δ hW t
    have hLMval : LMre (cfc (resIntegrand t) Δ)
        = (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W) *ᵥ ξ)).re
          - (star ξ ⬝ᵥ (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) ((1 + t)⁻¹) *ᵥ ξ)).re := by
      rw [hLMre, ContinuousLinearMap.comp_apply, cfc_resIntegrand_eq Δ hΔ ht,
        map_sub, qformCLM_conj, qformCLM_conj, isometry_conj_algebraMap W hW ((1 + t)⁻¹),
        Complex.reCLM_apply, Complex.sub_re]
    have hLNval : LNre (cfc (resIntegrand t) (Wᴴ * Δ * W))
        = (star ξ ⬝ᵥ ((Wᴴ * Δ * W + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ)).re
          - (star ξ ⬝ᵥ (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) ((1 + t)⁻¹) *ᵥ ξ)).re := by
      rw [hLNre, ContinuousLinearMap.comp_apply, cfc_resIntegrand_eq (Wᴴ * Δ * W) hWΔW ht,
        map_sub, qformCLM_apply, qformCLM_apply, Complex.reCLM_apply, Complex.sub_re]
    simp only [hF]
    rw [hLMval, hLNval, hAdd, sub_mulVec, dotProduct_sub, Complex.sub_re]
    ring
  -- Nonnegativity of `F` on `(0, ∞)`.
  have hFnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F t := by
    intro t ht
    rw [hFeq t ht]
    exact isometry_resolvent_gap_nonneg W ξ hW (hXt t ht)
  -- Continuity of `F` on `(0, ∞)`.
  have hFcont : ContinuousOn F (Ioi 0) := by
    simp only [hF]
    exact (LMre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand Δ hΔ)).sub
      (LNre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand (Wᴴ * Δ * W) hWΔW))
  have hFint : IntegrableOn F (Ioi 0) := by simp only [hF]; exact hg1int.sub hg2int
  -- The integral of `F` vanishes (from the `-log` saturation `hgap`).
  have hInt0 : ∫ t in Ioi 0, F t = 0 := by
    have hI1 : ∫ t in Ioi 0, LMre (cfc (resIntegrand t) Δ)
        = LMre (cfc (fun x => -Real.log x) Δ) := by
      rw [LMre.integral_comp_comm hintM, ← cfc_neg_log_eq_integral Δ hΔ]
    have hI2 : ∫ t in Ioi 0, LNre (cfc (resIntegrand t) (Wᴴ * Δ * W))
        = LNre (cfc (fun x => -Real.log x) (Wᴴ * Δ * W)) := by
      rw [LNre.integral_comp_comm hintN, ← cfc_neg_log_eq_integral (Wᴴ * Δ * W) hWΔW]
    have hLeq : LMre (cfc (fun x => -Real.log x) Δ)
        = LNre (cfc (fun x => -Real.log x) (Wᴴ * Δ * W)) := by
      rw [hLMre, hLNre, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        qformCLM_conj, qformCLM_apply, hgap]
    simp only [hF]
    rw [integral_sub hg1int hg2int, hI1, hI2, hLeq, sub_self]
  -- Nonnegative continuous integrand with zero integral ⟹ pointwise zero.
  have hae0 : F =ᵐ[volume.restrict (Ioi 0)] 0 := by
    have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi 0)] F :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hFnn)
    exact (setIntegral_eq_zero_iff_of_nonneg_ae hnn_ae hFint).mp hInt0
  have hFzero : Set.EqOn F 0 (Ioi 0) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae0 isOpen_Ioi hFcont continuousOn_const
  -- Conclude the resolvent intertwining pointwise via the per-`t` rigidity.
  intro t ht
  have hsat : (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
      - (Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W)⁻¹) *ᵥ ξ)).re = 0 := by
    rw [← hFeq t ht]; exact hFzero ht
  have hri := isometry_resolvent_saturation_intertwines W ξ hW (hXt t ht) hsat
  rw [hri, isometry_conj_add_algebraMap W Δ hW t]

end ErgodicTheory.OperatorEntropy.Lieb

end
