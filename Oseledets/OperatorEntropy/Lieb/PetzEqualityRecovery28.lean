/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.PetzEqualitySufficiency
import Oseledets.OperatorEntropy.Lieb.PetzKadison
import Oseledets.OperatorEntropy.Lieb.Step0Dilation

/-!
# Issue #28 — last mile: Petz equality ⟹ recovery for the mixed-ancilla Stinespring class
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

open Oseledets.OperatorEntropy

variable {n e : Type*} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

/-! ## Proof-transport for `upow` -/

lemma upow_congr {A B : Matrix n n ℂ} (h : A = B) (hA : A.PosDef) (t : ℝ) :
    upow hA t = upow (h ▸ hA) t := by
  subst h; rfl

/-! ## The mixed-ancilla Kraus operators (entrywise, product-free)

To sidestep the `CStarMatrix`/`Matrix` `HMul` ambiguity (issue #25) that a *rectangular* matrix
product `⟨b|ₙ · Um` would otherwise trigger, the Kraus operators are defined **entrywise** as
genuine `Matrix n n ℂ` objects.  Every matrix product below is then square (`n × n`, or the
ancilla-square `Um · (· ⊗ₖ α) · Umᴴ`), never rectangular. -/

/-- The `(a, b)`-th mixed-ancilla Kraus operator, written entrywise:
`K_{a,b} i j = ∑_c U_{(i,b),(j,c)} · (√α)_{c,a}`.  It equals `⟨b|ₙ · Um · (|·⟩ₙ ⊗ √α |a⟩)` but is
built directly as a square matrix so no rectangular product ever reaches the elaborator. -/
def mixedKraus (α : DensityMatrix e) (Um : Matrix (n × e) (n × e) ℂ) (a b : e) :
    Matrix n n ℂ :=
  Matrix.of fun i j => ∑ c : e, Um (i, b) (j, c) * (α.val ^ (1 / 2 : ℝ)) c a

omit [Fintype n] [DecidableEq n] in
lemma mixedKraus_apply (α : DensityMatrix e) (Um : Matrix (n × e) (n × e) ℂ)
    (a b : e) (i j : n) :
    mixedKraus α Um a b i j = ∑ c : e, Um (i, b) (j, c) * (α.val ^ (1 / 2 : ℝ)) c a := rfl

/-! ## Facts about the Hermitian square root `√α` -/

section SqrtFacts

variable (α : DensityMatrix e)

omit [Fintype n] [DecidableEq n] in
lemma sqrt_isHermitian : (α.val ^ (1 / 2 : ℝ))ᴴ = α.val ^ (1 / 2 : ℝ) :=
  (CFC.rpow_nonneg (a := α.val) (y := (1 / 2 : ℝ))).posSemidef.1

omit [Fintype n] [DecidableEq n] in
lemma sqrt_star_apply (a b : e) :
    star ((α.val ^ (1 / 2 : ℝ)) a b) = (α.val ^ (1 / 2 : ℝ)) b a := by
  have h : (α.val ^ (1 / 2 : ℝ))ᴴ b a = (α.val ^ (1 / 2 : ℝ)) b a := by rw [sqrt_isHermitian]
  rwa [Matrix.conjTranspose_apply] at h

omit [Fintype n] [DecidableEq n] in
lemma sqrt_mul_self (hα : α.val.PosDef) :
    (α.val ^ (1 / 2 : ℝ)) * (α.val ^ (1 / 2 : ℝ)) = α.val := by
  rw [← CFC.rpow_add hα.isStrictlyPositive.isUnit,
    show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, CFC.rpow_one _ hα.posSemidef.nonneg]

omit [Fintype n] [DecidableEq n] in
/-- The ancilla contraction of two `√α` columns: `∑_a (√α)_{c,a} (√α)_{a,c'} = α_{c,c'}`. -/
lemma sqrt_contract (hα : α.val.PosDef) (c c' : e) :
    (∑ a : e, (α.val ^ (1 / 2 : ℝ)) c a * (α.val ^ (1 / 2 : ℝ)) a c') = α.val c c' := by
  rw [← Matrix.mul_apply, sqrt_mul_self α hα]

end SqrtFacts

/-! ## Ancilla and index-block contractions of the entrywise Kraus operators -/

omit [Fintype n] [DecidableEq n] in
/-- The `√α`-contraction over the input ancilla index (star on the **first** factor).  This is where
the `√α · √α = α` collapse happens. -/
lemma mixedKraus_contract_left (α : DensityMatrix e) (hα : α.val.PosDef)
    (Um : Matrix (n × e) (n × e) ℂ) (b : e) (i i' j0 j0' : n) :
    (∑ a : e, star (mixedKraus α Um a b i j0) * mixedKraus α Um a b i' j0')
      = ∑ c : e, ∑ c' : e, star (Um (i, b) (j0, c)) * Um (i', b) (j0', c') * α.val c' c := by
  have hR : (∑ c : e, ∑ c' : e, star (Um (i, b) (j0, c)) * Um (i', b) (j0', c') * α.val c' c)
      = ∑ c : e, ∑ c' : e, ∑ a : e, star (Um (i, b) (j0, c)) * Um (i', b) (j0', c')
          * ((α.val ^ (1 / 2 : ℝ)) c' a * (α.val ^ (1 / 2 : ℝ)) a c) := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [← sqrt_contract α hα c' c, Finset.mul_sum]
  have key : ∀ a : e, star (mixedKraus α Um a b i j0) * mixedKraus α Um a b i' j0'
      = ∑ c : e, ∑ c' : e, (star (Um (i, b) (j0, c)) * (α.val ^ (1 / 2 : ℝ)) a c)
          * (Um (i', b) (j0', c') * (α.val ^ (1 / 2 : ℝ)) c' a) := by
    intro a
    rw [mixedKraus_apply, mixedKraus_apply, star_sum]
    simp only [star_mul', sqrt_star_apply α]
    rw [Finset.sum_mul_sum]
  rw [hR]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

omit [Fintype n] [DecidableEq n] in
/-- The `√α`-contraction over the input ancilla index (star on the **second** factor). -/
lemma mixedKraus_contract_right (α : DensityMatrix e) (hα : α.val.PosDef)
    (Um : Matrix (n × e) (n × e) ℂ) (b : e) (i i' j1 j2 : n) :
    (∑ a : e, mixedKraus α Um a b i j1 * star (mixedKraus α Um a b i' j2))
      = ∑ c : e, ∑ c' : e, Um (i, b) (j1, c) * star (Um (i', b) (j2, c')) * α.val c c' := by
  have hR : (∑ c : e, ∑ c' : e, Um (i, b) (j1, c) * star (Um (i', b) (j2, c')) * α.val c c')
      = ∑ c : e, ∑ c' : e, ∑ a : e, Um (i, b) (j1, c) * star (Um (i', b) (j2, c'))
          * ((α.val ^ (1 / 2 : ℝ)) c a * (α.val ^ (1 / 2 : ℝ)) a c') := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [← sqrt_contract α hα c c', Finset.mul_sum]
  have key : ∀ a : e, mixedKraus α Um a b i j1 * star (mixedKraus α Um a b i' j2)
      = ∑ c : e, ∑ c' : e, (Um (i, b) (j1, c) * (α.val ^ (1 / 2 : ℝ)) c a)
          * (star (Um (i', b) (j2, c')) * (α.val ^ (1 / 2 : ℝ)) a c') := by
    intro a
    rw [mixedKraus_apply, mixedKraus_apply, star_sum]
    simp only [star_mul', sqrt_star_apply α]
    rw [Finset.sum_mul_sum]
  rw [hR]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

omit [DecidableEq n] [DecidableEq e] in
/-- Reordering four nested sums, moving the `(c, c')`-block outward past the `(b, i)`-block. -/
private lemma reorder_bicc (F : e → n → e → e → ℂ) :
    (∑ b : e, ∑ i : n, ∑ c : e, ∑ c' : e, F b i c c')
      = ∑ c : e, ∑ c' : e, ∑ i : n, ∑ b : e, F b i c c' := by
  rw [Finset.sum_comm]
  have hL : (∑ i : n, ∑ b : e, ∑ c : e, ∑ c' : e, F b i c c')
      = ∑ P : n × e, ∑ Q : e × e, F P.2 P.1 Q.1 Q.2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_prod_type]
  have hR : (∑ c : e, ∑ c' : e, ∑ i : n, ∑ b : e, F b i c c')
      = ∑ Q : e × e, ∑ P : n × e, F P.2 P.1 Q.1 Q.2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hL, hR, Finset.sum_comm]

omit [DecidableEq n] [DecidableEq e] in
/-- Reordering five nested sums: `(c, c', b, i, i')` into the adjoint's `(b, i', i, c, c')`. -/
private lemma reorder_adjFinal (H : e → e → e → n → n → ℂ) :
    (∑ c : e, ∑ c' : e, ∑ b : e, ∑ i : n, ∑ i' : n, H c c' b i i')
      = ∑ b : e, ∑ i' : n, ∑ i : n, ∑ c : e, ∑ c' : e, H c c' b i i' := by
  have hstep1 : (∑ c : e, ∑ c' : e, ∑ b : e, ∑ i : n, ∑ i' : n, H c c' b i i')
      = ∑ b : e, ∑ i : n, ∑ i' : n, ∑ c : e, ∑ c' : e, H c c' b i i' := by
    have hs : (∑ c : e, ∑ c' : e, ∑ b : e, ∑ i : n, ∑ i' : n, H c c' b i i')
        = ∑ Q : e × e, ∑ P : e × n × n, H Q.1 Q.2 P.1 P.2.1 P.2.2 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Fintype.sum_prod_type]
    have ht : (∑ b : e, ∑ i : n, ∑ i' : n, ∑ c : e, ∑ c' : e, H c c' b i i')
        = ∑ P : e × n × n, ∑ Q : e × e, H Q.1 Q.2 P.1 P.2.1 P.2.2 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [Fintype.sum_prod_type]
    rw [hs, ht, Finset.sum_comm]
  rw [hstep1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-! ## The mixed-ancilla Kraus channel — trace preservation -/

lemma sum_braket_htp (α : DensityMatrix e) (hα : α.val.PosDef)
    (Um : Matrix (n × e) (n × e) ℂ) (hUm1 : star Um * Um = 1) :
    (∑ p : e × e, (mixedKraus α Um p.1 p.2)ᴴ * (mixedKraus α Um p.1 p.2)) = 1 := by
  have hUU : Umᴴ * Um = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hUm1
  ext j0 j0'
  rw [Matrix.sum_apply, Matrix.one_apply]
  have hunit : ∀ c c' : e, (∑ i : n, ∑ b : e, star (Um (i, b) (j0, c)) * Um (i, b) (j0', c'))
      = (Umᴴ * Um) (j0, c) (j0', c') := by
    intro c c'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.conjTranspose_apply]
  have hent : ∀ b a : e, ((mixedKraus α Um a b)ᴴ * (mixedKraus α Um a b)) j0 j0'
      = ∑ i : n, star (mixedKraus α Um a b i j0) * mixedKraus α Um a b i j0' := by
    intro b a
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply]
  have hLHS : (∑ p : e × e, ((mixedKraus α Um p.1 p.2)ᴴ * (mixedKraus α Um p.1 p.2)) j0 j0')
      = ∑ c : e, ∑ c' : e, ((Umᴴ * Um) (j0, c) (j0', c')) * α.val c' c := by
    rw [Fintype.sum_prod_type_right]
    simp only [hent]
    -- reorder ∑ b ∑ a ∑ i → ∑ b ∑ i ∑ a, then contract the ancilla index
    have hswap : ∀ b : e,
        (∑ a : e, ∑ i : n, star (mixedKraus α Um a b i j0) * mixedKraus α Um a b i j0')
          = ∑ i : n, ∑ a : e, star (mixedKraus α Um a b i j0) * mixedKraus α Um a b i j0' :=
      fun b => Finset.sum_comm
    simp only [hswap]
    simp only [mixedKraus_contract_left α hα Um]
    -- now ∑ b, ∑ i, ∑ c, ∑ c', star(Um) * Um * α c' c
    rw [reorder_bicc (fun b i c c' =>
      star (Um (i, b) (j0, c)) * Um (i, b) (j0', c') * α.val c' c)]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [← hunit c c', Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  rw [hLHS, hUU]
  by_cases hjj : j0 = j0'
  · subst hjj
    rw [if_pos rfl]
    have htr : (∑ c : e, α.val c c) = 1 := by
      simpa only [Matrix.trace, Matrix.diag_apply] using α.trace_one
    rw [← htr]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro c'' _ hc''
      rw [Matrix.one_apply_ne (fun h => hc'' (congrArg Prod.snd h).symm), zero_mul]
    · simp
  · rw [if_neg hjj]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun c' _ => ?_
    rw [Matrix.one_apply_ne (fun h => hjj (congrArg Prod.fst h)), zero_mul]

/-- The **mixed-ancilla Stinespring channel** `Λ_{α,Um} ρ = Tr_e(Um(ρ⊗α)Umᴴ)` as a Kraus channel. -/
def mixedAncillaChannel (α : DensityMatrix e) (hα : α.val.PosDef)
    (Um : Matrix (n × e) (n × e) ℂ) (hUm1 : star Um * Um = 1) : KrausChannel n where
  ι := e × e
  K := fun p => mixedKraus α Um p.1 p.2
  htp := sum_braket_htp α hα Um hUm1

lemma mixedAncilla_toMat (α : DensityMatrix e) (hα : α.val.PosDef)
    (Um : Matrix (n × e) (n × e) ℂ) (hUm1 : star Um * Um = 1) (X : Matrix n n ℂ) :
    (mixedAncillaChannel α hα Um hUm1).toMat X
      = partialTraceRight (Um * (X ⊗ₖ α.val) * Umᴴ) := by
  ext i0 i0'
  rw [partialTraceRight_apply]
  -- RHS entry expansion
  have hin : ∀ (f : e) (j2 : n) (c' : e),
      (Um * (X ⊗ₖ α.val)) (i0, f) (j2, c') * Umᴴ (j2, c') (i0', f)
        = ∑ j1 : n, ∑ c : e,
            Um (i0, f) (j1, c) * X j1 j2 * star (Um (i0', f) (j2, c')) * α.val c c' := by
    intro f j2 c'
    rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j1 _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.kronecker_apply]
    ring
  have hRent : ∀ f : e, (Um * (X ⊗ₖ α.val) * Umᴴ) (i0, f) (i0', f)
      = ∑ j2 : n, ∑ j1 : n, ∑ c : e, ∑ c' : e,
          Um (i0, f) (j1, c) * X j1 j2 * star (Um (i0', f) (j2, c')) * α.val c c' := by
    intro f
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [hin]
    refine Finset.sum_congr rfl fun j2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j1 _ => ?_
    rw [Finset.sum_comm]
  have hunfold : (mixedAncillaChannel α hα Um hUm1).toMat X
      = ∑ p : e × e, mixedKraus α Um p.1 p.2 * X * (mixedKraus α Um p.1 p.2)ᴴ := rfl
  have hent : ∀ b a : e, (mixedKraus α Um a b * X * (mixedKraus α Um a b)ᴴ) i0 i0'
      = ∑ j2 : n, ∑ j1 : n,
          (mixedKraus α Um a b i0 j1 * X j1 j2) * star (mixedKraus α Um a b i0' j2) := by
    intro b a
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j2 _ => ?_
    rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.sum_mul]
  have hL : (mixedAncillaChannel α hα Um hUm1).toMat X i0 i0'
      = ∑ b : e, ∑ j2 : n, ∑ j1 : n, ∑ c : e, ∑ c' : e,
          Um (i0, b) (j1, c) * X j1 j2 * star (Um (i0', b) (j2, c')) * α.val c c' := by
    rw [hunfold, Matrix.sum_apply, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hent]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j1 _ => ?_
    have hpull : (∑ a : e,
          (mixedKraus α Um a b i0 j1 * X j1 j2) * star (mixedKraus α Um a b i0' j2))
        = X j1 j2 * ∑ a : e, mixedKraus α Um a b i0 j1 * star (mixedKraus α Um a b i0' j2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hpull, mixedKraus_contract_right α hα Um b i0 i0' j1 j2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    ring
  rw [hL]
  rw [show (∑ f : e, (Um * (X ⊗ₖ α.val) * Umᴴ) (i0, f) (i0', f))
      = ∑ b : e, ∑ j2 : n, ∑ j1 : n, ∑ c : e, ∑ c' : e,
          Um (i0, b) (j1, c) * X j1 j2 * star (Um (i0', b) (j2, c')) * α.val c c'
      from Finset.sum_congr rfl fun f _ => hRent f]

lemma mixedAncilla_toDM (α : DensityMatrix e) (hα : α.val.PosDef)
    (U : Matrix.unitaryGroup (n × e) ℂ) (ρ : DensityMatrix n) :
    (mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
        (Unitary.coe_star_mul_self U)).toDM ρ = dilationChannel α U ρ := by
  apply DensityMatrix.ext
  change (mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
      (Unitary.coe_star_mul_self U)).toMat ρ.val = _
  rw [mixedAncilla_toMat]
  change _ = partialTraceRight (dilatedState α U ρ).val
  congr 1

lemma mixedAncilla_adj (α : DensityMatrix e) (hα : α.val.PosDef)
    (Um : Matrix (n × e) (n × e) ℂ) (hUm1 : star Um * Um = 1) (Y : Matrix n n ℂ) :
    (mixedAncillaChannel α hα Um hUm1).adj Y
      = partialTraceRight
          (Umᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ)) * Um * ((1 : Matrix n n ℂ) ⊗ₖ α.val)) := by
  ext j0 j0'
  rw [partialTraceRight_apply]
  -- RHS entry expansion of the three-factor core `Umᴴ (Y⊗1) Um`.
  have hA3 : ∀ (f : e) (r : n) (s : e),
      (Umᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ)) * Um) (j0, f) (r, s)
        = ∑ b : e, ∑ i : n, ∑ i' : n,
            star (Um (i, b) (j0, f)) * Y i i' * Um (i', b) (r, s) := by
    intro f r s
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hinner : ∀ (i' : n) (b : e),
        (Umᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ))) (j0, f) (i', b)
          = ∑ i : n, star (Um (i, b) (j0, f)) * Y i i' := by
      intro i' b
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single b]
      · rw [Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one]
      · intro g _ hg
        rw [Matrix.kronecker_apply, Matrix.one_apply_ne hg, mul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    simp only [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hRent : ∀ f : e,
      (Umᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ)) * Um * ((1 : Matrix n n ℂ) ⊗ₖ α.val)) (j0, f) (j0', f)
        = ∑ c : e, ∑ b : e, ∑ i : n, ∑ i' : n,
            star (Um (i, b) (j0, f)) * Y i i' * Um (i', b) (j0', c) * α.val c f := by
    intro f
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hcol : ∀ (r : n) (s : e),
        (Umᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ)) * Um) (j0, f) (r, s)
            * ((1 : Matrix n n ℂ) ⊗ₖ α.val) (r, s) (j0', f)
          = (if r = j0' then (1 : ℂ) else 0)
              * ((Umᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ)) * Um) (j0, f) (r, s) * α.val s f) := by
      intro r s
      rw [Matrix.kronecker_apply, Matrix.one_apply]
      ring
    simp only [hcol]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single j0']
    · rw [if_pos rfl, one_mul, hA3 f j0' s]
      simp only [Finset.sum_mul]
    · intro r _ hr; rw [if_neg hr, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j0') h
  -- LHS entry expansion
  have hent : ∀ b a : e, ((mixedKraus α Um a b)ᴴ * Y * (mixedKraus α Um a b)) j0 j0'
      = ∑ i' : n, ∑ i : n,
          star (mixedKraus α Um a b i j0) * Y i i' * mixedKraus α Um a b i' j0' := by
    intro b a
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply]
  have hunfold : (mixedAncillaChannel α hα Um hUm1).adj Y
      = ∑ p : e × e, (mixedKraus α Um p.1 p.2)ᴴ * Y * (mixedKraus α Um p.1 p.2) := rfl
  have hL : (mixedAncillaChannel α hα Um hUm1).adj Y j0 j0'
      = ∑ b : e, ∑ i' : n, ∑ i : n, ∑ c : e, ∑ c' : e,
          star (Um (i, b) (j0, c)) * Y i i' * Um (i', b) (j0', c') * α.val c' c := by
    rw [hunfold, Matrix.sum_apply, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hent]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpull : (∑ a : e,
          star (mixedKraus α Um a b i j0) * Y i i' * mixedKraus α Um a b i' j0')
        = Y i i' * ∑ a : e, star (mixedKraus α Um a b i j0) * mixedKraus α Um a b i' j0' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hpull, mixedKraus_contract_left α hα Um b i i' j0 j0', Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    ring
  rw [hL]
  have hR2 : (∑ f : e,
      (Umᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ)) * Um * ((1 : Matrix n n ℂ) ⊗ₖ α.val)) (j0, f) (j0', f))
      = ∑ b : e, ∑ i' : n, ∑ i : n, ∑ c : e, ∑ c' : e,
          star (Um (i, b) (j0, c)) * Y i i' * Um (i', b) (j0', c') * α.val c' c := by
    rw [Finset.sum_congr rfl (fun f (_ : f ∈ Finset.univ) => hRent f)]
    exact reorder_adjFinal (fun c c' b i i' =>
      star (Um (i, b) (j0, c)) * Y i i' * Um (i', b) (j0', c') * α.val c' c)
  rw [hR2]

/-! ## Two raw partial-trace facts -/

omit [Fintype n] [DecidableEq n] in
lemma partialTraceRight_kron_scalar (Z : Matrix n n ℂ) (α : DensityMatrix e) :
    partialTraceRight (Z ⊗ₖ α.val) = Z := by
  ext i i'
  rw [partialTraceRight_apply]
  simp only [Matrix.kronecker_apply, ← Finset.mul_sum]
  have htr : (∑ j : e, α.val j j) = 1 := by
    simpa only [Matrix.trace, Matrix.diag_apply] using α.trace_one
  rw [htr, mul_one]

/-! ## Unitary-conjugation form of the modular power -/

lemma upow_conj {N : Type*} [Fintype N] [DecidableEq N] {M : Matrix N N ℂ} (hM : M.PosDef)
    (W : Matrix.unitaryGroup N ℂ) (hWMW : ((W : Matrix N N ℂ) * M * star (W : Matrix N N ℂ)).PosDef)
    (t : ℝ) :
    upow hWMW t = (W : Matrix N N ℂ) * upow hM t * star (W : Matrix N N ℂ) := by
  classical
  set V : Matrix N N ℂ := (hM.1.eigenvectorUnitary : Matrix N N ℂ) with hV
  set d : N → ℝ := hM.1.eigenvalues with hd
  have hV1 : star V * V = 1 := Unitary.coe_star_mul_self _
  have hV2 : V * star V = 1 := Unitary.coe_mul_star_self _
  have hMspec : M = V * diagonal (fun i => (d i : ℂ)) * star V := by
    have h := hM.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hRC : (RCLike.ofReal ∘ hM.1.eigenvalues) = fun i => (d i : ℂ) := by funext i; rfl
    rw [hRC] at h; exact h
  set Wm : Matrix N N ℂ := (W : Matrix N N ℂ) with hWm
  set WV : Matrix N N ℂ := Wm * V with hWV
  have hWs1 : star Wm * Wm = 1 := Unitary.coe_star_mul_self _
  have hWs2 : Wm * star Wm = 1 := Unitary.coe_mul_star_self _
  have hstarWV : star WV = star V * star Wm := by rw [hWV, star_mul]
  have hWV1 : star WV * WV = 1 := by
    rw [hstarWV, hWV, ← mul_assoc, mul_assoc (star V) (star Wm) Wm, hWs1, mul_one, hV1]
  have hWV2 : WV * star WV = 1 := by
    rw [hstarWV, hWV, ← mul_assoc, mul_assoc Wm V (star V), hV2, mul_one, hWs2]
  have hWMWspec : Wm * M * star Wm = WV * diagonal (fun i => (d i : ℂ)) * star WV := by
    rw [hMspec, hstarWV, hWV]
    simp only [mul_assoc]
  rw [upow_conj_diag hWMW t hWV1 hWV2 hWMWspec, upow_conj_diag hM t hV1 hV2 hMspec]
  rw [hstarWV, hWV, hWm]
  simp only [mul_assoc]

/-! ## The dilation transport of the sufficiency intertwining -/

theorem stinespring_intertwinesIt (α : DensityMatrix e) (hα : α.val.PosDef)
    (U : Matrix.unitaryGroup (n × e) ℂ) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
        (Unitary.coe_star_mul_self U)).toDM ρ).val.PosDef)
    (hΛσ : ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
        (Unitary.coe_star_mul_self U)).toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ
      = relEntropy ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
          (Unitary.coe_star_mul_self U)).toDM ρ)
        ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
          (Unitary.coe_star_mul_self U)).toDM σ)) :
    IntertwinesIt (Λ := mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
      (Unitary.coe_star_mul_self U)) hρ hσ hΛρ hΛσ := by
  have hne : Nonempty e := by
    rw [← not_isEmpty_iff]; intro h
    have := α.trace_one
    simp only [Matrix.trace, Matrix.diag_apply, Finset.univ_eq_empty, Finset.sum_empty] at this
    exact one_ne_zero this.symm
  set Λ := mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
    (Unitary.coe_star_mul_self U) with hΛ
  have hω : (dilatedState α U ρ).val.PosDef := dilatedState_posDef ρ α U hρ hα
  have hτ : (dilatedState α U σ).val.PosDef := dilatedState_posDef σ α U hσ hα
  have hωA : (partialTraceRight (dilatedState α U ρ).val).PosDef := posDef_partialTraceRight hω
  have hτA : (partialTraceRight (dilatedState α U σ).val).PosDef := posDef_partialTraceRight hτ
  have htoρ : Λ.toDM ρ = (dilatedState α U ρ).partialTraceRight := by
    rw [hΛ, mixedAncilla_toDM]; rfl
  have htoσ : Λ.toDM σ = (dilatedState α U σ).partialTraceRight := by
    rw [hΛ, mixedAncilla_toDM]; rfl
  have hmatρ : (Λ.toDM ρ).val = partialTraceRight (dilatedState α U ρ).val := by rw [htoρ]; rfl
  have hmatσ : (Λ.toDM σ).val = partialTraceRight (dilatedState α U σ).val := by rw [htoσ]; rfl
  have hEq' : relEntropy (dilatedState α U ρ).partialTraceRight
      (dilatedState α U σ).partialTraceRight = relEntropy (dilatedState α U ρ)
        (dilatedState α U σ) := by
    rw [relEntropy_dilatedState ρ σ α U hα hσ, ← htoρ, ← htoσ, ← hEq]
  have hsuff := partialTrace_equality_imp_intertwinesIt (dilatedState α U ρ) (dilatedState α U σ)
    hω hτ hωA hτA hEq'
  intro t
  have hcoc : upow hΛρ t * upow hΛσ (-t) = upow hωA t * upow hτA (-t) := by
    rw [upow_congr hmatρ hΛρ t, upow_congr hmatσ hΛσ (-t)]
  rw [hcoc, mixedAncilla_adj]
  set uU : Matrix (n × e) (n × e) ℂ := (U : Matrix (n × e) (n × e) ℂ) with huU
  have hstar := hsuff t
  have hUs : star uU * uU = 1 := Unitary.coe_star_mul_self U
  have hUstar : uUᴴ = star uU := (Matrix.star_eq_conjTranspose _).symm
  have hcancel : ∀ A : Matrix (n × e) (n × e) ℂ, star uU * (uU * A * star uU) * uU = A := by
    intro A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUs, Matrix.one_mul,
      Matrix.mul_assoc, hUs, Matrix.mul_one]
  have hρα : (ρ.val ⊗ₖ α.val).PosDef := hρ.kronecker hα
  have hσα : (σ.val ⊗ₖ α.val).PosDef := hσ.kronecker hα
  have hωval : (dilatedState α U ρ).val = uU * (ρ.val ⊗ₖ α.val) * star uU := rfl
  have hτval : (dilatedState α U σ).val = uU * (σ.val ⊗ₖ α.val) * star uU := rfl
  set P := upow hρα t with hP
  set Q := upow hσα (-t) with hQ
  have hωconj : upow hω t = uU * P * star uU := by
    rw [upow_congr hωval hω t]; exact upow_conj hρα U _ t
  have hτconj : upow hτ (-t) = uU * Q * star uU := by
    rw [upow_congr hτval hτ (-t)]; exact upow_conj hσα U _ (-t)
  have hkron1 : P = upow hρ t ⊗ₖ upow hα t := upow_kron hρ hα hρα t
  have hkron2 : Q = upow hσ (-t) ⊗ₖ upow hα (-t) := upow_kron hσ hα hσα (-t)
  have hmid : uU * P * star uU * (uU * Q * star uU) = uU * (P * Q) * star uU := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star uU) uU, hUs, Matrix.one_mul]
  have hYcoc : (upow hωA t * upow hτA (-t)) ⊗ₖ (1 : Matrix e e ℂ) = uU * (P * Q) * star uU := by
    rw [hstar, hωconj, hτconj, hmid]
  have hPQ : P * Q = (upow hρ t * upow hσ (-t)) ⊗ₖ (1 : Matrix e e ℂ) := by
    rw [hkron1, hkron2, ← Matrix.mul_kronecker_mul, upow_mul_upow_neg]
  rw [hYcoc, hUstar, hcancel (P * Q), hPQ, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul, partialTraceRight_kron_scalar]

/-! ## Petz recovery for the mixed-ancilla Stinespring class -/

/-- **Petz equality ⟹ recovery for the mixed-ancilla Stinespring class.** If the Umegaki relative
entropy is preserved by the faithful-ancilla Stinespring channel `Λ_{α,U} ρ = Tr_e(U(ρ⊗α)Uᴴ)`, then
the Petz recovery map of `σ` reconstructs the input state `ρ` from its image `Λ ρ`. -/
theorem petz_equality_recovery (α : DensityMatrix e) (hα : α.val.PosDef)
    (U : Matrix.unitaryGroup (n × e) ℂ) (ρ σ : DensityMatrix n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
        (Unitary.coe_star_mul_self U)).toDM ρ).val.PosDef)
    (hΛσ : ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
        (Unitary.coe_star_mul_self U)).toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ
      = relEntropy ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
          (Unitary.coe_star_mul_self U)).toDM ρ)
        ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
          (Unitary.coe_star_mul_self U)).toDM σ)) :
    petz σ (mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
        (Unitary.coe_star_mul_self U))
        ((mixedAncillaChannel α hα (U : Matrix (n × e) (n × e) ℂ)
          (Unitary.coe_star_mul_self U)).toDM ρ).val = ρ.val :=
  intertwinesIt_imp_recovery ρ σ _ hρ hσ hΛρ hΛσ
    (stinespring_intertwinesIt α hα U ρ σ hρ hσ hΛρ hΛσ hEq)

end Oseledets.OperatorEntropy.Lieb
