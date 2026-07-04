/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.OperatorEntropy.Lieb.PetzChannelContraction
import Oseledets.OperatorEntropy.Lieb.ContractionRigiditySkeleton
import Oseledets.OperatorEntropy.Lieb.PetzEqualitySufficiency
import Oseledets.OperatorEntropy.Lieb.PetzKadison

/-!
# Petz equality — sufficiency for a general Kraus channel (issue #28, route b″)

This module clones the *mixed-ancilla sufficiency chain* of `PetzEqualitySufficiency` but with the
**channel contraction** `W = petzWChanVec Λ ρ` (from `PetzChannelContraction`) in place of the
isometric reconciliation `petzWvec`.  For a general Kraus channel `Λ` with all four states faithful
(`ρ, σ, Λρ, Λσ` positive definite), if data processing is saturated
(`D(ρ‖σ) = D(Λρ‖Λσ)`), then the channel adjoint intertwines the modular flows (`IntertwinesIt`),
whence the Petz recovery map reconstructs the input state (`petz σ Λ (Λρ) = ρ`).

## Contraction vs. isometry

The isometric spine `RigidityTail.isometry_resolvent_intertwine_of_neg_log_eq` is replaced by the
inlined contraction spine `contraction_resolvent_intertwine_of_re_eq` (below).  Two
structural adaptations are needed relative to the isometric clone:

* The compression is an **inequality** `Wᴴ Δ W ≤ Δout` (`petzWChanVec_modular_le`), not the exact
  compression of the isometry; the output modular operator `Δout = (Λσ) ⊗ₖ ((Λρ)⁻¹)ᵀ` is a genuinely
  separate operator (not `Wᴴ Δ W`).
* The `-log` **saturation is scalar** (`channel_modular_gap`): the entropy equality gives only the
  equality of the two `-log` modular *quadratic forms* at the output cyclic vector, not the vector
  equation `(Wᴴ (−log Δ) W) ξ = (−log Δout) ξ` (which is unavailable — the whole-space Loewner
  `Wᴴ (−log Δ) W ⪰ −log Δout` fails for a contraction).  The scalar variant
  `contraction_resolvent_intertwine_of_re_eq` sources the vanishing integral from this scalar
  equality directly (the only place the isometric/contraction spines used the vector `hgap`).

## No injectivity hypothesis

Earlier versions of this chain carried `hWinj : Function.Injective (petzWChanVec Λ ρ).mulVec`,
used to invert the compression `Y := Wᴴ (Δ+t) W`.  That hypothesis is *not* automatic from
faithfulness of the four states: for an information-losing channel (e.g. the completely
depolarising channel, whose adjoint `Λ†(Y) = (tr Y / n) · 1` collapses everything onto scalars)
the map `petzWChanVec Λ ρ` is far from injective, even though `Λρ = 1/n` is faithful.

The hypothesis has been **removed**.  The gap decomposition `contraction_gap_decomp` rewrites the
resolvent gap at `ξ`, using only the contraction defect `WᴴW ξ = ξ`, as

`⟪ξ, (Wᴴ X⁻¹ W − Out⁻¹) ξ⟫ = ⟪b, X b⟫ + ⟪η, (Out − Y) η⟫`

with `η := Out⁻¹ ξ` and `b := X⁻¹(Wξ) − W η`: the `Y⁻¹` bridge of the injective proof is replaced
by `Out⁻¹ Y Out⁻¹`, which cancels between the two summands, so `Y` is never inverted.  Both
summands are nonnegative (from `X.PosDef` and `Y ≤ Out`, the latter via `compression_shift_le`),
and gap-zero forces `b = 0`, which is the per-`t` intertwining directly
(`contraction_perT_intertwine_of_gap_zero`).  Consequently `petz_equality_recovery_general` holds
for **all** faithful-state Kraus channels, including non-injective/depolarising ones.
-/

open Matrix Real MeasureTheory Set
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

open Oseledets.OperatorEntropy

/-! ## The scalar-sourced contraction rigidity spine (`Fin`-indexed) -/

section FinSkeleton

variable {M N : ℕ}

/-! ### The injectivity-free gap decomposition (the `hWinj`-removal crux)

The compression `Y := Wᴴ X W` is singular when `W` is not injective, so the isometric-style
`Y⁻¹` bridge of `ContractionRigiditySkeleton` is unavailable.  The three lemmas below replace
it: the gap decomposition never inverts `Y`, and its two summands directly give nonnegativity
of the resolvent gap and the per-`t` intertwining at saturation. -/

/-- **Gap decomposition (injectivity-free).**  For a contraction `W` (only the defect
`WᴴW ξ = ξ` is used), positive-definite shifts `X` and `Out`, with `η := Out⁻¹ ξ`,
`b := X⁻¹(Wξ) − W η`, `Y := Wᴴ X W`:

`⟪ξ, (Wᴴ X⁻¹ W − Out⁻¹) ξ⟫ = ⟪b, X b⟫ + ⟪η, (Out − Y) η⟫`.

The `Y⁻¹` of the injective proof is replaced by `Out⁻¹ Y Out⁻¹`, which cancels between the two
summands — the compression `Y` is never inverted.  This is the single identity that removes
`hWinj` from the whole issue-#28 chain. -/
lemma contraction_gap_decomp (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} {Out : Matrix (Fin N) (Fin N) ℂ} (ξ : Fin N → ℂ)
    (hX : X.PosDef) (hOut : Out.PosDef)
    (hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0) :
    star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - Out⁻¹) *ᵥ ξ)
      = star (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Out⁻¹ *ᵥ ξ))
            ⬝ᵥ (X *ᵥ (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Out⁻¹ *ᵥ ξ)))
        + star (Out⁻¹ *ᵥ ξ) ⬝ᵥ ((Out - Wᴴ * X * W) *ᵥ (Out⁻¹ *ᵥ ξ)) := by
  set Y := Wᴴ * X * W with hYdef
  -- unit/hermitian facts
  have hXdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit
  have hOutdet : IsUnit Out.det := (Matrix.isUnit_iff_isUnit_det Out).mp hOut.isUnit
  have hX1 : X⁻¹ * X = 1 := nonsing_inv_mul X hXdet
  have hX2 : X * X⁻¹ = 1 := mul_nonsing_inv X hXdet
  have hOut1 : Out⁻¹ * Out = 1 := nonsing_inv_mul Out hOutdet
  have hXinvH : X⁻¹ᴴ = X⁻¹ := hX.1.inv
  have hOutinvH : Out⁻¹ᴴ = Out⁻¹ := hOut.1.inv
  have hWWH : (Wᴴ * W)ᴴ = Wᴴ * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hWWξ : (Wᴴ * W) *ᵥ ξ = ξ := by
    have h := hdefect
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  -- `b = P *ᵥ ξ` with `P := X⁻¹ * W − W * Out⁻¹`.
  set P : Matrix (Fin M) (Fin N) ℂ := X⁻¹ * W - W * Out⁻¹ with hPdef
  have hb_eq : X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Out⁻¹ *ᵥ ξ) = P *ᵥ ξ := by
    rw [hPdef, sub_mulVec, mulVec_mulVec, mulVec_mulVec]
  -- `Pᴴ = Wᴴ X⁻¹ − Out⁻¹ Wᴴ`.
  have hPH : Pᴴ = Wᴴ * X⁻¹ - Out⁻¹ * Wᴴ := by
    rw [hPdef]
    simp only [conjTranspose_sub, conjTranspose_mul, hXinvH, hOutinvH]
  -- the pure matrix identity for the `X`-square (no defect, no `Y⁻¹`).
  have hPXP : Pᴴ * X * P
      = Wᴴ * X⁻¹ * W - Wᴴ * W * Out⁻¹ - Out⁻¹ * (Wᴴ * W) + Out⁻¹ * Y * Out⁻¹ := by
    have hPXe : Pᴴ * X = Wᴴ - Out⁻¹ * Wᴴ * X := by
      rw [hPH, Matrix.sub_mul, Matrix.mul_assoc Wᴴ X⁻¹ X, hX1, Matrix.mul_one]
    rw [hPXe, hPdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
    have t1 : Wᴴ * (X⁻¹ * W) = Wᴴ * X⁻¹ * W := (Matrix.mul_assoc Wᴴ X⁻¹ W).symm
    have t2 : Wᴴ * (W * Out⁻¹) = Wᴴ * W * Out⁻¹ := (Matrix.mul_assoc Wᴴ W Out⁻¹).symm
    have t3 : Out⁻¹ * Wᴴ * X * (X⁻¹ * W) = Out⁻¹ * (Wᴴ * W) := by
      rw [Matrix.mul_assoc (Out⁻¹ * Wᴴ) X (X⁻¹ * W), ← Matrix.mul_assoc X X⁻¹ W, hX2,
        Matrix.one_mul, Matrix.mul_assoc Out⁻¹ Wᴴ W]
    have t4 : Out⁻¹ * Wᴴ * X * (W * Out⁻¹) = Out⁻¹ * Y * Out⁻¹ := by
      rw [hYdef]
      simp only [Matrix.mul_assoc]
    rw [t1, t2, t3, t4]
    abel
  -- the output-conjugation identity for the `(Out − Y)` piece (no defect).
  have hOutconj : Out⁻¹ * (Out - Y) * Out⁻¹ = Out⁻¹ - Out⁻¹ * Y * Out⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hOut1, Matrix.one_mul]
  -- rewrite the two summands as `star ξ ⬝ᵥ (· *ᵥ ξ)`.
  have hAterm : star (P *ᵥ ξ) ⬝ᵥ (X *ᵥ (P *ᵥ ξ))
      = star ξ ⬝ᵥ ((Pᴴ * X * P) *ᵥ ξ) := by
    calc star (P *ᵥ ξ) ⬝ᵥ (X *ᵥ (P *ᵥ ξ))
        = star (P *ᵥ ξ) ⬝ᵥ ((X * P) *ᵥ ξ) := by rw [mulVec_mulVec]
      _ = star ξ ⬝ᵥ (Pᴴ *ᵥ ((X * P) *ᵥ ξ)) := star_mulVec_dotProduct P ξ _
      _ = star ξ ⬝ᵥ ((Pᴴ * (X * P)) *ᵥ ξ) := by rw [mulVec_mulVec]
      _ = star ξ ⬝ᵥ ((Pᴴ * X * P) *ᵥ ξ) := by rw [Matrix.mul_assoc]
  have hBterm : star (Out⁻¹ *ᵥ ξ) ⬝ᵥ ((Out - Y) *ᵥ (Out⁻¹ *ᵥ ξ))
      = star ξ ⬝ᵥ ((Out⁻¹ - Out⁻¹ * Y * Out⁻¹) *ᵥ ξ) := by
    calc star (Out⁻¹ *ᵥ ξ) ⬝ᵥ ((Out - Y) *ᵥ (Out⁻¹ *ᵥ ξ))
        = star ξ ⬝ᵥ (Out⁻¹ᴴ *ᵥ ((Out - Y) *ᵥ (Out⁻¹ *ᵥ ξ))) :=
          star_mulVec_dotProduct Out⁻¹ ξ _
      _ = star ξ ⬝ᵥ (Out⁻¹ *ᵥ ((Out - Y) *ᵥ (Out⁻¹ *ᵥ ξ))) := by rw [hOutinvH]
      _ = star ξ ⬝ᵥ ((Out⁻¹ * (Out - Y) * Out⁻¹) *ᵥ ξ) := by
          rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
      _ = star ξ ⬝ᵥ ((Out⁻¹ - Out⁻¹ * Y * Out⁻¹) *ᵥ ξ) := by rw [hOutconj]
  -- the two defect collapses.
  have hD1 : star ξ ⬝ᵥ ((Wᴴ * W * Out⁻¹) *ᵥ ξ) = star ξ ⬝ᵥ (Out⁻¹ *ᵥ ξ) := by
    rw [← Matrix.mulVec_mulVec, ← hWWH, ← star_mulVec_dotProduct, hWWξ]
  have hD2 : star ξ ⬝ᵥ ((Out⁻¹ * (Wᴴ * W)) *ᵥ ξ) = star ξ ⬝ᵥ (Out⁻¹ *ᵥ ξ) := by
    rw [← Matrix.mulVec_mulVec, hWWξ]
  -- assemble.
  rw [hb_eq, hAterm, hBterm, hPXP]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add]
  rw [hD1, hD2]
  ring

/-- **Total resolvent-gap nonnegativity, injectivity-free** (replaces the `A+B`/`Y⁻¹`-split of
the injective spine).  Under the compression bound `Wᴴ X W ≤ Out` and the contraction defect,
the whole gap `Re ⟪ξ,(Wᴴ X⁻¹ W − Out⁻¹) ξ⟫` is `≥ 0`, being the sum of two nonnegative
quadratic forms. -/
lemma contraction_total_gap_nonneg (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} {Out : Matrix (Fin N) (Fin N) ℂ} (ξ : Fin N → ℂ)
    (hX : X.PosDef) (hOut : Out.PosDef) (hYle : Wᴴ * X * W ≤ Out)
    (hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0) :
    0 ≤ (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - Out⁻¹) *ᵥ ξ)).re := by
  rw [contraction_gap_decomp W ξ hX hOut hdefect, Complex.add_re]
  have hApos : 0 ≤ (star (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Out⁻¹ *ᵥ ξ))
      ⬝ᵥ (X *ᵥ (X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Out⁻¹ *ᵥ ξ)))).re :=
    (Complex.nonneg_iff.mp
      (hX.posSemidef.dotProduct_mulVec_nonneg _)).1
  have hBps : (Out - Wᴴ * X * W).PosSemidef := Matrix.le_iff.mp hYle
  have hBpos : 0 ≤ (star (Out⁻¹ *ᵥ ξ) ⬝ᵥ ((Out - Wᴴ * X * W) *ᵥ (Out⁻¹ *ᵥ ξ))).re :=
    (Complex.nonneg_iff.mp (hBps.dotProduct_mulVec_nonneg _)).1
  exact add_nonneg hApos hBpos

/-- **Per-`t` recovery intertwining, injectivity-free** (the per-`t` saturation step of the
inlined scalar spine).  If the
whole gap vanishes at `ξ`, then the first summand `⟪b, X b⟫` of `contraction_gap_decomp`
vanishes, whence `X.PosDef` forces `b = 0`, i.e. `X⁻¹(Wξ) = W(Out⁻¹ξ)` — the intertwining
conclusion *directly*, with no `Y⁻¹` bridge. -/
lemma contraction_perT_intertwine_of_gap_zero (W : Matrix (Fin M) (Fin N) ℂ)
    {X : Matrix (Fin M) (Fin M) ℂ} {Out : Matrix (Fin N) (Fin N) ℂ} (ξ : Fin N → ℂ)
    (hX : X.PosDef) (hOut : Out.PosDef) (hYle : Wᴴ * X * W ≤ Out)
    (hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0)
    (hGzero : (star ξ ⬝ᵥ ((Wᴴ * X⁻¹ * W - Out⁻¹) *ᵥ ξ)).re = 0) :
    X⁻¹ *ᵥ (W *ᵥ ξ) = W *ᵥ (Out⁻¹ *ᵥ ξ) := by
  set b := X⁻¹ *ᵥ (W *ᵥ ξ) - W *ᵥ (Out⁻¹ *ᵥ ξ)
  -- the two summands are each ≥ 0 and sum (in `.re`) to 0, hence each is 0.
  have hBps : (Out - Wᴴ * X * W).PosSemidef := Matrix.le_iff.mp hYle
  have hApos : 0 ≤ (star b ⬝ᵥ (X *ᵥ b)).re :=
    (Complex.nonneg_iff.mp (hX.posSemidef.dotProduct_mulVec_nonneg b)).1
  have hBpos : 0 ≤ (star (Out⁻¹ *ᵥ ξ) ⬝ᵥ ((Out - Wᴴ * X * W) *ᵥ (Out⁻¹ *ᵥ ξ))).re :=
    (Complex.nonneg_iff.mp (hBps.dotProduct_mulVec_nonneg _)).1
  have hsum : (star b ⬝ᵥ (X *ᵥ b)).re
      + (star (Out⁻¹ *ᵥ ξ) ⬝ᵥ ((Out - Wᴴ * X * W) *ᵥ (Out⁻¹ *ᵥ ξ))).re = 0 := by
    rw [← Complex.add_re, ← contraction_gap_decomp W ξ hX hOut hdefect]; exact hGzero
  have hAzero : (star b ⬝ᵥ (X *ᵥ b)).re = 0 := by linarith
  -- `X.PosDef` ⟹ `b = 0`.
  by_contra hne
  have hb0 : b ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < star b ⬝ᵥ (X *ᵥ b) := hX.dotProduct_mulVec_pos hb0
  have hposre : 0 < (star b ⬝ᵥ (X *ᵥ b)).re := (Complex.pos_iff.mp hpos).1
  rw [hAzero] at hposre
  exact lt_irrefl 0 hposre

/-! ### The scalar-sourced spine, now injectivity-free -/

/-- **Contraction rigidity tail (scalar-sourced resolvent form).**  The inlined contraction spine;
like the isometric `RigidityTail.isometry_resolvent_intertwine_of_neg_log_eq`, except the `-log`
saturation is supplied as the *scalar* equality of the two `-log` modular quadratic forms at `ξ`
(`hReEq`) rather than the vector equation `(Wᴴ (−log Δ) W) ξ = (−log Δout) ξ`.  The scalar suffices
because the spine only ever used the vector saturation to certify that the resolvent-gap integral
vanishes.  Unlike the skeleton spine, **no injectivity of `W` is assumed**: nonnegativity and the
per-`t` saturation step come from `contraction_total_gap_nonneg` and
`contraction_perT_intertwine_of_gap_zero`, which never invert the compression `Wᴴ (Δ+t) W`. -/
theorem contraction_resolvent_intertwine_of_re_eq (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (Δout : Matrix (Fin N) (Fin N) ℂ) (ξ : Fin N → ℂ)
    (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ)
    (hReEq : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
              = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) Δout *ᵥ ξ).re) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ) := by
  classical
  have hdefect : (1 - Wᴴ * W) *ᵥ ξ = 0 := contraction_defect_mulVec_eq_zero W ξ hWc hsat
  have hWWξ : (Wᴴ * W) *ᵥ ξ = ξ := by
    have h := hdefect
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  have hregvec : ∀ c : ℝ, (Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c * W) *ᵥ ξ
      = algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) c *ᵥ ξ := by
    intro c
    have hmat : Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) c * W = c • (Wᴴ * W) := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [hmat, Matrix.smul_mulVec, hWWξ, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  set LMre : Matrix (Fin M) (Fin M) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (qformCLM (W *ᵥ ξ)) with hLMre
  set LNre : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (qformCLM ξ) with hLNre
  set F : ℝ → ℝ := fun t => LMre (cfc (resIntegrand t) Δ)
    - LNre (cfc (resIntegrand t) Δout) with hF
  have hXt : ∀ t : ℝ, 0 < t → (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t).PosDef :=
    fun t ht => hΔ.add_posSemidef (posDef_algebraMap ht).posSemidef
  have hintM : IntegrableOn (fun t => cfc (resIntegrand t) Δ) (Ioi 0) :=
    integrableOn_cfc_resIntegrand Δ hΔ
  have hintN : IntegrableOn (fun t => cfc (resIntegrand t) Δout) (Ioi 0) :=
    integrableOn_cfc_resIntegrand Δout hΔout
  have hg1int : IntegrableOn (fun t => LMre (cfc (resIntegrand t) Δ)) (Ioi 0) :=
    LMre.integrable_comp hintM
  have hg2int : IntegrableOn (fun t => LNre (cfc (resIntegrand t) Δout)) (Ioi 0) :=
    LNre.integrable_comp hintN
  have hFeq : ∀ t : ℝ, 0 < t → F t
      = (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
          - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)).re := by
    intro t ht
    have hLMval : LMre (cfc (resIntegrand t) Δ)
        = (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W) *ᵥ ξ)).re
          - (star ξ ⬝ᵥ (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) ((1 + t)⁻¹) *ᵥ ξ)).re := by
      rw [hLMre, ContinuousLinearMap.comp_apply, cfc_resIntegrand_eq Δ hΔ ht,
        map_sub, qformCLM_conj, qformCLM_conj, hregvec ((1 + t)⁻¹),
        Complex.reCLM_apply, Complex.sub_re]
    have hLNval : LNre (cfc (resIntegrand t) Δout)
        = (star ξ ⬝ᵥ ((Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ)).re
          - (star ξ ⬝ᵥ (algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) ((1 + t)⁻¹) *ᵥ ξ)).re := by
      rw [hLNre, ContinuousLinearMap.comp_apply, cfc_resIntegrand_eq Δout hΔout ht,
        map_sub, qformCLM_apply, qformCLM_apply, Complex.reCLM_apply, Complex.sub_re]
    simp only [hF]
    rw [hLMval, hLNval, sub_mulVec, dotProduct_sub, Complex.sub_re]
    ring
  have hFnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F t := by
    intro t ht
    rw [hFeq t ht]
    have hX := hXt t ht
    have hOut : (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t).PosDef :=
      hΔout.add_posSemidef (posDef_algebraMap ht).posSemidef
    have hle : Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W
        ≤ Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t :=
      compression_shift_le W Δ Δout hWc hcompLe ht
    exact contraction_total_gap_nonneg W ξ hX hOut hle hdefect
  have hFcont : ContinuousOn F (Ioi 0) := by
    simp only [hF]
    exact (LMre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand Δ hΔ)).sub
      (LNre.continuous.comp_continuousOn (continuousOn_cfc_resIntegrand Δout hΔout))
  have hFint : IntegrableOn F (Ioi 0) := by simp only [hF]; exact hg1int.sub hg2int
  have hInt0 : ∫ t in Ioi 0, F t = 0 := by
    have hI1 : ∫ t in Ioi 0, LMre (cfc (resIntegrand t) Δ)
        = LMre (cfc (fun x => -Real.log x) Δ) := by
      rw [LMre.integral_comp_comm hintM, ← cfc_neg_log_eq_integral Δ hΔ]
    have hI2 : ∫ t in Ioi 0, LNre (cfc (resIntegrand t) Δout)
        = LNre (cfc (fun x => -Real.log x) Δout) := by
      rw [LNre.integral_comp_comm hintN, ← cfc_neg_log_eq_integral Δout hΔout]
    have hLeq : LMre (cfc (fun x => -Real.log x) Δ) = LNre (cfc (fun x => -Real.log x) Δout) := by
      rw [hLMre, hLNre, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        qformCLM_conj, qformCLM_apply, Complex.reCLM_apply, Complex.reCLM_apply]
      exact hReEq
    simp only [hF]
    rw [integral_sub hg1int hg2int, hI1, hI2, hLeq, sub_self]
  have hae0 : F =ᵐ[volume.restrict (Ioi 0)] 0 := by
    have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi 0)] F :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hFnn)
    exact (setIntegral_eq_zero_iff_of_nonneg_ae hnn_ae hFint).mp hInt0
  have hFzero : Set.EqOn F 0 (Ioi 0) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae0 isOpen_Ioi hFcont continuousOn_const
  intro t ht
  have hGzero : (star ξ ⬝ᵥ ((Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ * W
      - (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹) *ᵥ ξ)).re = 0 := by
    rw [← hFeq t ht]; exact hFzero ht
  have hOut : (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t).PosDef :=
    hΔout.add_posSemidef (posDef_algebraMap ht).posSemidef
  exact contraction_perT_intertwine_of_gap_zero W ξ (hXt t ht) hOut
    (compression_shift_le W Δ Δout hWc hcompLe ht) hdefect hGzero

end FinSkeleton

/-! ## The scalar `-log` modular gap for the channel contraction -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Channel `-log` modular gap (scalar).**  For a Kraus channel `Λ` with all four states faithful,
if data processing is saturated (`D(ρ‖σ) = D(Λρ‖Λσ)`), then the two `-log` modular quadratic forms
agree at the output cyclic vector `ξ = vec((Λρ)^{1/2})`:

`Re ⟪ξ, Wᴴ (−log Δ) W ξ⟫ = Re ⟪ξ, (−log Δout) ξ⟫`,

with `W = petzWChanVec Λ ρ`, `Δ = σ ⊗ₖ (ρ⁻¹)ᵀ`, `Δout = (Λσ) ⊗ₖ ((Λρ)⁻¹)ᵀ`.  The left form is
`D(ρ‖σ)` (via `qform_conj`, `petzWChan_cyclic`, `kronForm_re_eq_relEntropy`); the right is
`D(Λρ‖Λσ)`. -/
theorem channel_modular_gap (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    (star (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
        ⬝ᵥ ((petzWChanVec Λ ρ)ᴴ * cfc (fun x => -Real.log x) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ)
              * petzWChanVec Λ ρ) *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))).re
      = (star (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
        ⬝ᵥ cfc (fun x => -Real.log x) ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ)
              *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))).re := by
  rw [qform_conj (petzWChanVec Λ ρ)
        (cfc (fun x => -Real.log x) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ))
        (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ))),
      petzWChan_cyclic Λ ρ hΛρ,
      kronForm_re_eq_relEntropy ρ σ hρ hσ,
      kronForm_re_eq_relEntropy (Λ.toDM ρ) (Λ.toDM σ) hΛρ hΛσ]
  exact hEq

/-! ## The scalar-sourced contraction rigidity, at arbitrary finite index -/

/-- **Contraction rigidity (general square index).**  The `Fin`-indexed scalar spine
`contraction_resolvent_intertwine_of_re_eq` transported to an arbitrary finite square index type
`p` via the `Fintype.equivFin` reindexing. -/
lemma contraction_resolvent_intertwine_general {p : Type*} [Fintype p] [DecidableEq p]
    (W Δ Δout : Matrix p p ℂ) (ξ : p → ℂ)
    (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ)
    (hReEq : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
              = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) Δout *ᵥ ξ).re) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Δout + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ ξ) := by
  classical
  intro t ht
  set e : p ≃ Fin (Fintype.card p) := Fintype.equivFin p with he
  set W' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ :=
    W.submatrix e.symm e.symm with hW'def
  set Δ' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ :=
    Δ.submatrix e.symm e.symm with hΔ'def
  set Δout' : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ :=
    Δout.submatrix e.symm e.symm with hΔout'def
  set ξ' : Fin (Fintype.card p) → ℂ := ξ ∘ e.symm with hξ'def
  have hW'H : W'ᴴ = Wᴴ.submatrix e.symm e.symm := by rw [hW'def, conjTranspose_submatrix]
  have hcompS : ∀ S : Matrix p p ℂ,
      W'ᴴ * S.submatrix e.symm e.symm * W' = (Wᴴ * S * W).submatrix e.symm e.symm := by
    intro S
    rw [hW'H, hW'def, submatrix_mul_equiv, submatrix_mul_equiv]
  have hW'W' : W'ᴴ * W' = (Wᴴ * W).submatrix e.symm e.symm := by
    rw [hW'H, hW'def, submatrix_mul_equiv]
  have hmulVecQ : ∀ A : Matrix p p ℂ, A.submatrix e.symm e.symm *ᵥ ξ' = (A *ᵥ ξ) ∘ e.symm := by
    intro A
    rw [hξ'def, submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hmulVecP : ∀ (A : Matrix p p ℂ) (v : p → ℂ),
      A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
    intro A v
    rw [submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hmulVecWq : ∀ u : p → ℂ, W' *ᵥ (u ∘ e.symm) = (W *ᵥ u) ∘ e.symm := by
    intro u
    rw [hW'def, submatrix_mulVec_equiv]
    simp [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hWξ : W' *ᵥ ξ' = (W *ᵥ ξ) ∘ e.symm := by rw [hξ'def]; exact hmulVecWq ξ
  have hdot : ∀ u v : p → ℂ, star (u ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = star u ⬝ᵥ v := by
    intro u v
    simp only [dotProduct, Pi.star_apply, Function.comp_apply]
    exact Equiv.sum_comp e.symm (fun j => star (u j) * v j)
  have hsubeq : ∀ A B : Matrix p p ℂ,
      A.submatrix e.symm e.symm - B.submatrix e.symm e.symm = (A - B).submatrix e.symm e.symm := by
    intro A B; ext i j; simp [Matrix.submatrix_apply, Matrix.sub_apply]
  have hΔ'pd : Δ'.PosDef := by rw [hΔ'def]; exact hΔ.submatrix e.symm.injective
  have hΔout'pd : Δout'.PosDef := by rw [hΔout'def]; exact hΔout.submatrix e.symm.injective
  have hW'c : W'ᴴ * W' ≤ 1 := by
    rw [Matrix.le_iff]
    have h := (Matrix.le_iff.mp hWc).submatrix e.symm
    have heq : (1 : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) - W'ᴴ * W'
        = (1 - Wᴴ * W).submatrix e.symm e.symm := by
      rw [hW'W', ← hsubeq 1 (Wᴴ * W), Matrix.submatrix_one_equiv]
    rw [heq]; exact h
  have hcompLe' : W'ᴴ * Δ' * W' ≤ Δout' := by
    rw [Matrix.le_iff]
    have h := (Matrix.le_iff.mp hcompLe).submatrix e.symm
    have heq : Δout' - W'ᴴ * Δ' * W' = (Δout - Wᴴ * Δ * W).submatrix e.symm e.symm := by
      rw [hΔout'def, hΔ'def, hcompS Δ, hsubeq]
    rw [heq]; exact h
  have hsat' : star (W' *ᵥ ξ') ⬝ᵥ (W' *ᵥ ξ') = star ξ' ⬝ᵥ ξ' := by
    rw [hWξ, hξ'def, hdot (W *ᵥ ξ) (W *ᵥ ξ), hdot ξ ξ]; exact hsat
  have hcfcΔ : cfc (fun x => -Real.log x) Δ'
      = (cfc (fun x => -Real.log x) Δ).submatrix e.symm e.symm := by
    have hlog : ContinuousOn (fun x => -Real.log x) (spectrum ℝ Δ) :=
      (Matrix.finite_real_spectrum (A := Δ)).continuousOn _
    have hbridge : ∀ X : Matrix p p ℂ, eqvFin p X = X.submatrix e.symm e.symm := fun _ => rfl
    have hE := eqvFin_cfc (fun x => -Real.log x) hΔ.1 hlog
    rw [hbridge, hbridge] at hE
    rw [hΔ'def]; exact hE.symm
  have hcfcΔout : cfc (fun x => -Real.log x) Δout'
      = (cfc (fun x => -Real.log x) Δout).submatrix e.symm e.symm := by
    have hlog : ContinuousOn (fun x => -Real.log x) (spectrum ℝ Δout) :=
      (Matrix.finite_real_spectrum (A := Δout)).continuousOn _
    have hbridge : ∀ X : Matrix p p ℂ, eqvFin p X = X.submatrix e.symm e.symm := fun _ => rfl
    have hE := eqvFin_cfc (fun x => -Real.log x) hΔout.1 hlog
    rw [hbridge, hbridge] at hE
    rw [hΔout'def]; exact hE.symm
  have hqform_reindex : ∀ A : Matrix p p ℂ,
      star ξ' ⬝ᵥ A.submatrix e.symm e.symm *ᵥ ξ' = star ξ ⬝ᵥ A *ᵥ ξ := by
    intro A
    rw [hmulVecQ A, hξ'def]; exact hdot ξ (A *ᵥ ξ)
  have hReEq' : (star ξ' ⬝ᵥ (W'ᴴ * cfc (fun x => -Real.log x) Δ' * W') *ᵥ ξ').re
      = (star ξ' ⬝ᵥ cfc (fun x => -Real.log x) Δout' *ᵥ ξ').re := by
    rw [hcfcΔ, hcompS (cfc (fun x => -Real.log x) Δ), hcfcΔout,
      hqform_reindex (Wᴴ * cfc (fun x => -Real.log x) Δ * W),
      hqform_reindex (cfc (fun x => -Real.log x) Δout)]
    exact hReEq
  have hFin := contraction_resolvent_intertwine_of_re_eq W' Δ' Δout' ξ'
    hW'c hΔ'pd hΔout'pd hcompLe' hsat' hReEq' t ht
  have hΔam : Δ' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t
      = (Δ + algebraMap ℝ (Matrix p p ℂ) t).submatrix e.symm e.symm := by
    rw [hΔ'def]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Algebra.algebraMap_eq_smul_one,
      Matrix.one_apply, Matrix.smul_apply]
  have hΔoutam : Δout' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t
      = (Δout + algebraMap ℝ (Matrix p p ℂ) t).submatrix e.symm e.symm := by
    rw [hΔout'def]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Algebra.algebraMap_eq_smul_one,
      Matrix.one_apply, Matrix.smul_apply]
  have hLtrans : (Δ' + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t)⁻¹
        *ᵥ (W' *ᵥ ξ')
      = ((Δ + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)) ∘ e.symm := by
    rw [hΔam, inv_submatrix_equiv, hWξ, hmulVecP]
  have hRtrans : W' *ᵥ ((Δout'
          + algebraMap ℝ (Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) ℂ) t)⁻¹ *ᵥ ξ')
      = (W *ᵥ ((Δout + algebraMap ℝ (Matrix p p ℂ) t)⁻¹ *ᵥ ξ)) ∘ e.symm := by
    rw [hΔoutam, inv_submatrix_equiv, hmulVecQ, hmulVecWq]
  rw [hLtrans, hRtrans] at hFin
  funext i
  have hi := congrFun hFin (e i)
  simpa [Function.comp_def, Equiv.symm_apply_apply] using hi

/-- **Contraction cfc-intertwining (general square index).**  Under the scalar `-log` saturation
`hReEq`, the contraction `W` intertwines every continuous function of the modular operator:
`W (cfc g Δout ξ) = cfc g Δ (W ξ)`.  The resolvent intertwining
(`contraction_resolvent_intertwine_general`) is upgraded via `exists_resolvent_combo`. -/
lemma contraction_cfc_intertwine {p : Type*} [Fintype p] [DecidableEq p]
    (W Δ Δout : Matrix p p ℂ) (ξ : p → ℂ)
    (hWc : Wᴴ * W ≤ 1)
    (hΔ : Δ.PosDef) (hΔout : Δout.PosDef) (hcompLe : Wᴴ * Δ * W ≤ Δout)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ)
    (hReEq : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
              = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) Δout *ᵥ ξ).re)
    (g : ℝ → ℝ) :
    W *ᵥ (cfc g Δout *ᵥ ξ) = cfc g Δ *ᵥ (W *ᵥ ξ) := by
  classical
  have hres := contraction_resolvent_intertwine_general W Δ Δout ξ
    hWc hΔ hΔout hcompLe hsat hReEq
  have hΔpos : ∀ x ∈ spectrum ℝ Δ, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos Δ hΔ.1).mp hΔ.isStrictlyPositive x hx
  have hΔoutpos : ∀ x ∈ spectrum ℝ Δout, 0 < x := fun x hx =>
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos Δout hΔout.1).mp
      hΔout.isStrictlyPositive x hx
  have hUpos : ∀ i : ↥(spectrum ℝ Δ ∪ spectrum ℝ Δout), 0 < (i : ℝ) := by
    rintro ⟨x, hx | hx⟩
    · exact hΔpos x hx
    · exact hΔoutpos x hx
  haveI : Finite ↥(spectrum ℝ Δ ∪ spectrum ℝ Δout) :=
    ((Matrix.finite_real_spectrum (A := Δ)).union
      (Matrix.finite_real_spectrum (A := Δout))).to_subtype
  obtain ⟨c, hc⟩ := exists_resolvent_combo
    (ι := ↥(spectrum ℝ Δ ∪ spectrum ℝ Δout))
    (fun i => (i : ℝ)) Subtype.coe_injective hUpos (fun i => ((g (i : ℝ) : ℂ)))
  have hcombo : ∀ y ∈ spectrum ℝ Δ ∪ spectrum ℝ Δout,
      g y = ∑ t ∈ c.support, (c t).re * (y + (t : ℝ))⁻¹ := by
    intro y hy
    have hci := hc ⟨y, hy⟩
    dsimp only at hci
    have hre := congrArg Complex.re hci
    rw [Complex.ofReal_re, Complex.re_sum] at hre
    rw [hre]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hz : ((y : ℂ) + ((t : ℝ) : ℂ)) = (((y + (t : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [hz, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hL : W *ᵥ (cfc g Δout *ᵥ ξ)
      = ∑ t ∈ c.support, (c t).re •
          (W *ᵥ ((Δout + algebraMap ℝ (Matrix p p ℂ) (t : ℝ))⁻¹ *ᵥ ξ)) := by
    rw [cfc_eq_resolvent_combo g Δout hΔout c _ Set.subset_union_right hcombo,
      Matrix.sum_mulVec, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hR : cfc g Δ *ᵥ (W *ᵥ ξ)
      = ∑ t ∈ c.support, (c t).re •
          ((Δ + algebraMap ℝ (Matrix p p ℂ) (t : ℝ))⁻¹ *ᵥ (W *ᵥ ξ)) := by
    rw [cfc_eq_resolvent_combo g Δ hΔ c _ Set.subset_union_left hcombo, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.smul_mulVec]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hres (t : ℝ) t.2]

/-! ## The channel unitary-power intertwining and the `it`-cocycle intertwining -/

/-- **Channel unitary-power intertwining.**  Under entropy saturation, the contraction
intertwines the unitary power of the modular operator on the output cyclic vector:
`W (Δout^{it} ξ) = Δ^{it} (W ξ)`, with `W ξ = vec(ρ^{1/2})`.  No injectivity of the channel Petz
map is assumed. -/
theorem channel_upow_intertwine (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) (t : ℝ)
    (hΔoutpd : ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ).PosDef)
    (hΔpd : (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ).PosDef) :
    petzWChanVec Λ ρ *ᵥ (upow hΔoutpd t *ᵥ vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
      = upow hΔpd t *ᵥ vec (ρ.val ^ (1 / 2 : ℝ)) := by
  have hWc := petzWChanVec_contraction Λ ρ hρ hΛρ
  have hcompLe := petzWChanVec_modular_le Λ ρ σ hρ hσ hΛρ hΛσ
  have hsat := petzWChan_cyclic_norm Λ ρ hρ hΛρ
  have hReEq := channel_modular_gap Λ ρ σ hρ hσ hΛρ hΛσ hEq
  have hIc := contraction_cfc_intertwine (petzWChanVec Λ ρ) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ)
    ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ) (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
    hWc hΔpd hΔoutpd hcompLe hsat hReEq (fun x => Real.cos (t * Real.log x))
  have hIs := contraction_cfc_intertwine (petzWChanVec Λ ρ) (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ)
    ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ) (vec ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)))
    hWc hΔpd hΔoutpd hcompLe hsat hReEq (fun x => Real.sin (t * Real.log x))
  rw [petzWChan_cyclic Λ ρ hΛρ] at hIc hIs
  have hu1 : upow hΔoutpd t = cpow hΔoutpd ((t : ℂ) * Complex.I) := rfl
  have hu2 : upow hΔpd t = cpow hΔpd ((t : ℂ) * Complex.I) := rfl
  rw [hu1, hu2, cpow_eq_cfc_cos_sin hΔoutpd t, cpow_eq_cfc_cos_sin hΔpd t]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hIc, hIs]

/-- **Channel `it`-cocycle intertwining (`IntertwinesIt`).**  Under entropy saturation
`D(ρ‖σ) = D(Λρ‖Λσ)`, the channel adjoint intertwines the modular `it`-flows:
`Λ†((Λρ)^{it}(Λσ)^{-it}) = ρ^{it} σ^{-it}` for all `t`.  Read off *directly* (the vectorised
Petz map already contains `Λ†`, so no ampliation is needed). -/
theorem channel_equality_imp_intertwinesIt (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    IntertwinesIt hρ hσ hΛρ hΛσ := by
  intro t
  have hρinv : (ρ.val ^ (-1 : ℝ)).PosDef :=
    (IsStrictlyPositive.rpow ρ.val (-1) hρ.isStrictlyPositive).posDef
  have hΛρinv : ((Λ.toDM ρ).val ^ (-1 : ℝ)).PosDef :=
    (IsStrictlyPositive.rpow (Λ.toDM ρ).val (-1) hΛρ.isStrictlyPositive).posDef
  have hΔpd : (σ.val ⊗ₖ (ρ.val ^ (-1 : ℝ))ᵀ).PosDef := hσ.kronecker hρinv.transpose
  have hΔoutpd : ((Λ.toDM σ).val ⊗ₖ ((Λ.toDM ρ).val ^ (-1 : ℝ))ᵀ).PosDef :=
    hΛσ.kronecker hΛρinv.transpose
  have hstar := channel_upow_intertwine Λ ρ σ hρ hσ hΛρ hΛσ hEq t hΔoutpd hΔpd
  rw [modArg_upow_mulVec hΛσ hΛρ hΔoutpd t ((Λ.toDM ρ).val ^ (1 / 2 : ℝ)),
      modArg_upow_mulVec hσ hρ hΔpd t (ρ.val ^ (1 / 2 : ℝ)),
      ← vec_petzWChan] at hstar
  have hbase : petzWChan Λ ρ (upow hΛσ t * (Λ.toDM ρ).val ^ (1 / 2 : ℝ) * upow hΛρ (-t))
      = upow hσ t * ρ.val ^ (1 / 2 : ℝ) * upow hρ (-t) := by
    apply Matrix.ext
    intro i j
    have := congrFun hstar (i, j)
    simpa only [vec_apply] using this
  -- collapse the `(Λρ)^{±1/2}` twist on the input column and commute `ρ^{1/2}`
  have hΛρcol : upow hΛσ t * (Λ.toDM ρ).val ^ (1 / 2 : ℝ) * upow hΛρ (-t)
          * (Λ.toDM ρ).val ^ (-(1 / 2) : ℝ)
        = upow hΛσ t * upow hΛρ (-t) := by
    rw [rpow_eq_cpow_ofReal hΛρ (1 / 2), rpow_eq_cpow_ofReal hΛρ (-(1 / 2)),
        show upow hΛρ (-t) = cpow hΛρ (((-t : ℝ) : ℂ) * Complex.I) from rfl]
    rw [show upow hΛσ t * cpow hΛρ ((1 / 2 : ℝ) : ℂ) * cpow hΛρ (((-t : ℝ) : ℂ) * Complex.I)
            * cpow hΛρ ((-(1 / 2) : ℝ) : ℂ)
          = upow hΛσ t * (cpow hΛρ ((1 / 2 : ℝ) : ℂ) * cpow hΛρ (((-t : ℝ) : ℂ) * Complex.I)
            * cpow hΛρ ((-(1 / 2) : ℝ) : ℂ)) from by noncomm_ring,
        cpow_mul_cpow, cpow_mul_cpow]
    congr 2
    push_cast; ring
  have hRHScol : upow hσ t * ρ.val ^ (1 / 2 : ℝ) * upow hρ (-t)
        = upow hσ t * upow hρ (-t) * ρ.val ^ (1 / 2 : ℝ) := by
    rw [rpow_eq_cpow_ofReal hρ (1 / 2),
        show upow hρ (-t) = cpow hρ (((-t : ℝ) : ℂ) * Complex.I) from rfl,
        mul_assoc, mul_assoc, cpow_mul_cpow, cpow_mul_cpow]
    congr 2
    push_cast; ring
  unfold petzWChan at hbase
  rw [hΛρcol, hRHScol] at hbase
  -- cancel `ρ^{1/2}`
  have hsqrtInv : ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ) = 1 :=
    CFC.rpow_mul_rpow_neg (1 / 2) hρ.isStrictlyPositive
  have hcancel : Λ.adj (upow hΛσ t * upow hΛρ (-t)) = upow hσ t * upow hρ (-t) :=
    calc Λ.adj (upow hΛσ t * upow hΛρ (-t))
        = Λ.adj (upow hΛσ t * upow hΛρ (-t))
            * (ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ)) := by rw [hsqrtInv, mul_one]
      _ = Λ.adj (upow hΛσ t * upow hΛρ (-t))
            * ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ) := by rw [mul_assoc]
      _ = upow hσ t * upow hρ (-t) * ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ) := by rw [hbase]
      _ = upow hσ t * upow hρ (-t)
            * (ρ.val ^ (1 / 2 : ℝ) * ρ.val ^ (-(1 / 2) : ℝ)) := by rw [mul_assoc]
      _ = upow hσ t * upow hρ (-t) := by rw [hsqrtInv, mul_one]
  calc Λ.adj (upow hΛρ t * upow hΛσ (-t))
      = Λ.adj (star (upow hΛσ t * upow hΛρ (-t))) := by
        rw [star_mul, star_upow, star_upow, neg_neg]
    _ = star (Λ.adj (upow hΛσ t * upow hΛρ (-t))) := by
        simp only [Matrix.star_eq_conjTranspose]; exact Λ.adj_conjTranspose _
    _ = star (upow hσ t * upow hρ (-t)) := by rw [hcancel]
    _ = upow hρ t * upow hσ (-t) := by rw [star_mul, star_upow, star_upow, neg_neg]

/-- **General Petz recovery from equality (issue #28, fully general).**  For a Kraus channel `Λ`
with all four states faithful, saturation of data processing `D(ρ‖σ) = D(Λρ‖Λσ)` forces the
Petz recovery map to reconstruct the input state: `petz σ Λ (Λ ρ) = ρ`.  No injectivity of the
vectorised Petz map is assumed — the theorem covers information-losing (e.g. depolarising)
channels. -/
theorem petz_equality_recovery_general (Λ : KrausChannel n) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    petz σ Λ (Λ.toDM ρ).val = ρ.val :=
  intertwinesIt_imp_recovery ρ σ Λ hρ hσ hΛρ hΛσ
    (channel_equality_imp_intertwinesIt Λ ρ σ hρ hσ hΛρ hΛσ hEq)

end Oseledets.OperatorEntropy.Lieb

end

