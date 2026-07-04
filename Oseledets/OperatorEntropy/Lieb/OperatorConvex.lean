/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operator convexity of `-log` (Lieb foundations)

This module proves that `x ↦ -Real.log x` is **operator convex** on `Set.Ioi 0`, i.e. its ℝ-cfc
is convex in the Loewner order on self-adjoint matrices with spectrum in `(0, ∞)`. The argument
transports the computation onto the `C⋆`-algebra `CStarMatrix` (where `CFC.concaveOn_log` lives)
via the `ℝ`-linear star-algebra equivalence `toCStar`, which preserves the order, self-adjointness,
and the continuous functional calculus.

## Main results

* `Oseledets.OperatorEntropy.Lieb.operatorConvexOn_neg_log`: `-log` is operator convex on `(0, ∞)`.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

/-- `f` is operator convex on `I`: its ℝ-cfc is convex (Loewner order) in every matrix order. -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ConvexOn ℝ {a : Matrix (Fin m) (Fin m) ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I}
    (fun a => cfc f a)

section Transport

variable {m : ℕ}

/-- The `ℝ`-linear star-algebra equivalence between the two type copies
`Matrix (Fin m) (Fin m) ℂ` and `CStarMatrix (Fin m) (Fin m) ℂ`, obtained by restricting scalars of
`CStarMatrix.ofMatrixStarAlgEquiv` from `ℂ` to `ℝ`. Its underlying map is the identity on the
shared carrier, but it transports the Loewner order, self-adjointness, and the continuous
functional calculus between the two copies. -/
private def toCStar : Matrix (Fin m) (Fin m) ℂ ≃⋆ₐ[ℝ] CStarMatrix (Fin m) (Fin m) ℂ :=
  (CStarMatrix.ofMatrixStarAlgEquiv).restrictScalars ℝ

/-- The order is transported by `toCStar`. Since both orders are defined through the same
`StarOrderedRing` structure (`0 ≤ x ↔ x ∈ closure {star s * s}`) and the two carriers, together
with `star`, `*`, `+`, are definitionally equal, this holds by `Iff.rfl` after unfolding
`StarOrderedRing.nonneg_iff` on both sides. -/
private lemma nonneg_toCStar (a : Matrix (Fin m) (Fin m) ℂ) :
    (0 : CStarMatrix (Fin m) (Fin m) ℂ) ≤ toCStar a ↔ (0 : Matrix (Fin m) (Fin m) ℂ) ≤ a := by
  rw [StarOrderedRing.nonneg_iff, StarOrderedRing.nonneg_iff]
  exact Iff.rfl

private lemma isUnit_toCStar (a : Matrix (Fin m) (Fin m) ℂ) :
    IsUnit (toCStar a) ↔ IsUnit a := by
  refine ⟨fun h => ?_, fun h => h.map toCStar⟩
  have := h.map toCStar.symm
  rwa [toCStar.symm_apply_apply] at this

private lemma toCStar_symm_mono {u v : CStarMatrix (Fin m) (Fin m) ℂ} (h : u ≤ v) :
    toCStar.symm u ≤ toCStar.symm v := by
  rw [← sub_nonneg] at h ⊢
  rw [show toCStar.symm v - toCStar.symm u = toCStar.symm (v - u) from
      (map_sub toCStar.symm v u).symm,
    ← nonneg_toCStar (toCStar.symm (v - u)), toCStar.apply_symm_apply]
  exact h

private lemma isStrictlyPositive_toCStar (a : Matrix (Fin m) (Fin m) ℂ) :
    IsStrictlyPositive (toCStar a) ↔ IsStrictlyPositive a := by
  rw [IsStrictlyPositive.iff_of_unital, IsStrictlyPositive.iff_of_unital, nonneg_toCStar,
    isUnit_toCStar]

private lemma mem_bridge (a : Matrix (Fin m) (Fin m) ℂ) :
    IsStrictlyPositive (toCStar a) ↔ (IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Ioi 0) := by
  rw [isStrictlyPositive_toCStar]
  refine ⟨fun h => ⟨h.isSelfAdjoint, fun x hx =>
      (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) a h.isSelfAdjoint).mp h x hx⟩,
    fun ⟨hsa, hsp⟩ => ?_⟩
  exact (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) a hsa).mpr fun x hx => hsp hx

/-- The continuous functional calculus of `fun x => -log x` is transported by `toCStar`:
`cfc (-log) a` (native ℝ-cfc on `Matrix`) equals `toCStar.symm (-(CFC.log (toCStar a)))`, moving
the computation onto the `C⋆`-algebra `CStarMatrix` where `CFC.log` and `CFC.concaveOn_log` live. -/
private lemma cfc_neg_log_eq {a : Matrix (Fin m) (Fin m) ℂ} (hsa : IsSelfAdjoint a)
    (hsp : spectrum ℝ a ⊆ Set.Ioi 0) :
    cfc (fun r => -Real.log r) a = toCStar.symm (-(CFC.log (toCStar a))) := by
  haveI : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin m) (Fin m) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hsub : spectrum ℝ a ⊆ {(0 : ℝ)}ᶜ := fun x hx => (hsp hx).ne'
  have hcontlog : ContinuousOn Real.log (spectrum ℝ a) := Real.continuousOn_log.mono hsub
  have hcont_e : Continuous (toCStar : Matrix (Fin m) (Fin m) ℂ → CStarMatrix (Fin m) (Fin m) ℂ) :=
    CStarMatrix.ofMatrixL.continuous.congr (fun _ => rfl)
  have hmap : toCStar (cfc Real.log a) = cfc Real.log (toCStar a) :=
    StarAlgHomClass.map_cfc toCStar Real.log a hcontlog hcont_e hsa (hsa.map toCStar)
  have hCFC : CFC.log (toCStar a) = cfc Real.log (toCStar a) := rfl
  rw [cfc_neg, hCFC, ← hmap, ← map_neg toCStar, toCStar.symm_apply_apply]

end Transport

theorem operatorConvexOn_neg_log : OperatorConvexOn (Set.Ioi 0) (fun x => -Real.log x) := by
  intro m
  have hbase : ConvexOn ℝ {a : CStarMatrix (Fin m) (Fin m) ℂ | IsStrictlyPositive a}
      (-CFC.log) := CFC.concaveOn_log.neg
  have hconv : Convex ℝ
      {a : Matrix (Fin m) (Fin m) ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Ioi 0} := by
    intro x hx y hy s t hs ht hst
    rw [Set.mem_setOf_eq, ← mem_bridge, map_add toCStar, map_smul toCStar, map_smul toCStar]
    exact hbase.1 ((mem_bridge x).mpr hx) ((mem_bridge y).mpr hy) hs ht hst
  refine ⟨hconv, ?_⟩
  intro x hx y hy s t hs ht hst
  have hmem := hconv hx hy hs ht hst
  obtain ⟨hxsa, hxsp⟩ := hx
  obtain ⟨hysa, hysp⟩ := hy
  obtain ⟨hsum_sa, hsum_sp⟩ := hmem
  have hex : IsStrictlyPositive (toCStar x) := (mem_bridge x).mpr ⟨hxsa, hxsp⟩
  have hey : IsStrictlyPositive (toCStar y) := (mem_bridge y).mpr ⟨hysa, hysp⟩
  change cfc (fun r => -Real.log r) (s • x + t • y)
    ≤ s • cfc (fun r => -Real.log r) x + t • cfc (fun r => -Real.log r) y
  rw [cfc_neg_log_eq hsum_sa hsum_sp, cfc_neg_log_eq hxsa hxsp, cfc_neg_log_eq hysa hysp,
    ← map_smul toCStar.symm, ← map_smul toCStar.symm, ← map_add toCStar.symm]
  apply toCStar_symm_mono
  rw [map_add toCStar, map_smul toCStar, map_smul toCStar]
  exact hbase.2 hex hey hs ht hst

end Oseledets.OperatorEntropy.Lieb
