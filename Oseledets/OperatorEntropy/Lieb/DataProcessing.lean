/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Oseledets.OperatorEntropy.StinespringReduction
import Oseledets.OperatorEntropy.Lieb.JointConvexity

/-!
# Issue #22 — the data-processing inequality via the Weyl (Heisenberg–Weyl) twirl

This module discharges the partial-trace monotonicity `Prop`
`RelEntropyMonotoneUnderPartialTrace` (the DPI wall isolated in `StinespringReduction.lean`)
from Lieb's joint convexity (`JointConvexity.lean`).

The engine is the **Weyl 1-design twirl** on the traced-out factor `nE` (of dimension
`d := Fintype.card nE`).  Fixing an equivalence `e : nE ≃ ZMod d`, the discrete clock and shift
operators `Z, X` generate the `d²` Weyl unitaries `W a b = Xᵃ Zᵇ`, and

`(1/d²) ∑_{a,b} (1 ⊗ W a b) ρ (1 ⊗ W a b)ᴴ = (Tr_E ρ) ⊗ (d⁻¹ • 1)`  (`twirl_sum`).

Combining this depolarising identity with the finite Jensen inequality for the (jointly convex)
relative entropy (`relEntropyMat_convex_sum`) yields, for faithful states, the data-processing
inequality `D(Tr_E ρ ‖ Tr_E σ) ≤ D(ρ ‖ σ)` (`relEntropyMonotone_partialTrace_faithful`).

Key steps:
* `pinch_char_sum` — orthogonality of the standard additive character (`ZMod.stdAddChar`);
* `clock_pinch` — `∑_b Z^b M (Z^b)ᴴ = d • (E-diagonal pinch of M)`;
* `shift_spread` — `∑_a X^a (pinch) (X^a)ᴴ = (Tr_E) ⊗ 1`;
* `twirl_sum` — the assembled depolarising identity;
* `relEntropyMat_convex_sum` — finite Jensen from the 2-point Lieb convexity via `ConvexOn`;
* `posDef_partialTraceRight` — the partial trace of a faithful state is faithful.
-/

open Matrix Real AddChar
open scoped ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

/-! ## The Weyl twirl over a factor equipped with a cyclic labelling -/

section Twirl

variable {nA nE : Type*} [Fintype nA] [DecidableEq nA] [Fintype nE] [DecidableEq nE]
variable {d : ℕ} [NeZero d] (e : nE ≃ ZMod d)

/-- Character orthogonality (the "pinch" phase sum): for `k k' : ZMod d`,
`∑_b χ(b·k)·conj(χ(b·k')) = d·[k = k']` where `χ = ZMod.stdAddChar`. -/
lemma pinch_char_sum (k k' : ZMod d) :
    (∑ b : ZMod d, ZMod.stdAddChar (b * k)
        * (starRingEnd ℂ) (ZMod.stdAddChar (b * k')))
      = if k = k' then (d : ℂ) else 0 := by
  have hR : 0 < ringChar (ZMod d) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne d)
  have hchar : ∀ b : ZMod d,
      ZMod.stdAddChar (b * k) * (starRingEnd ℂ) (ZMod.stdAddChar (b * k'))
        = ZMod.stdAddChar (b * (k - k')) := by
    intro b
    rw [AddChar.starComp_apply hR, AddChar.inv_apply, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hchar]
  rw [AddChar.sum_mulShift (k - k') (ZMod.isPrimitive_stdAddChar d)]
  simp only [ZMod.card, sub_eq_zero, Nat.cast_ite, Nat.cast_zero]

/-- The clock (phase) operator `Z^b` on `ℂ^nE`, diagonal in the `e`-basis. -/
def clockMat (b : ZMod d) : Matrix nE nE ℂ :=
  diagonal fun t => ZMod.stdAddChar (b * e t)

/-- The shift operator `X^a` on `ℂ^nE`: the permutation matrix of `s ↦ e⁻¹(e s + a)`,
written in column-solved form `[s = e⁻¹(e x - a)]`. -/
def shiftMat (a : ZMod d) : Matrix nE nE ℂ :=
  fun x s => if s = e.symm (e x - a) then 1 else 0

/-- The Weyl operator `W a b = X^a Z^b`. -/
def Wmat (a b : ZMod d) : Matrix nE nE ℂ := shiftMat e a * clockMat e b

/-- The `E`-diagonal pinch of `M`: keep only the entries with equal `E`-labels. -/
def Epinch (M : Matrix (nA × nE) (nA × nE) ℂ) : Matrix (nA × nE) (nA × nE) ℂ :=
  fun p q => if p.2 = q.2 then M p q else 0

omit [Fintype nA] [Fintype nE] in
/-- `1 ⊗ Z^b` is the diagonal matrix of the phases on the whole system. -/
lemma one_kron_clock (b : ZMod d) :
    (1 : Matrix nA nA ℂ) ⊗ₖ clockMat e b
      = diagonal fun p : nA × nE => ZMod.stdAddChar (b * e p.2) := by
  simp only [clockMat]
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext p
  rw [one_mul]

/-- **Clock pinch.**  `∑_b (1 ⊗ Z^b) M (1 ⊗ Z^b)ᴴ = d • (E-diagonal pinch of M)`. -/
lemma clock_pinch (M : Matrix (nA × nE) (nA × nE) ℂ) :
    (∑ b : ZMod d, (1 ⊗ₖ clockMat e b) * M * (1 ⊗ₖ clockMat e b)ᴴ)
      = (d : ℂ) • Epinch M := by
  ext p q
  rw [Matrix.sum_apply, Matrix.smul_apply]
  have hsummand : ∀ b : ZMod d,
      (((1 : Matrix nA nA ℂ) ⊗ₖ clockMat e b) * M
          * ((1 : Matrix nA nA ℂ) ⊗ₖ clockMat e b)ᴴ) p q
        = M p q * (ZMod.stdAddChar (b * e p.2)
            * (starRingEnd ℂ) (ZMod.stdAddChar (b * e q.2))) := by
    intro b
    rw [one_kron_clock, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [Pi.star_apply, starRingEnd_apply]
    ring
  simp_rw [hsummand]
  rw [← Finset.mul_sum, pinch_char_sum]
  simp only [e.injective.eq_iff, Epinch]
  split_ifs with h
  · rw [smul_eq_mul, mul_comm]
  · rw [mul_zero, smul_zero]

omit [Fintype nA] [Fintype nE] [NeZero d] in
/-- Entrywise value of `1 ⊗ X^a`. -/
lemma oneShift_apply (a : ZMod d) (p u : nA × nE) :
    ((1 : Matrix nA nA ℂ) ⊗ₖ shiftMat e a) p u
      = (if p.1 = u.1 then (1 : ℂ) else 0)
        * (if u.2 = e.symm (e p.2 - a) then 1 else 0) := by
  rw [Matrix.kronecker_apply, Matrix.one_apply, shiftMat]

omit [Fintype nA] [Fintype nE] [NeZero d] in
/-- `1 ⊗ X^a` vanishes off the graph of the shifted permutation. -/
lemma oneShift_apply_ne (a : ZMod d) (p u : nA × nE)
    (hu : u ≠ (p.1, e.symm (e p.2 - a))) :
    ((1 : Matrix nA nA ℂ) ⊗ₖ shiftMat e a) p u = 0 := by
  rw [oneShift_apply]
  split_ifs with h1 h2
  · exact absurd (Prod.ext h1.symm h2 : u = (p.1, e.symm (e p.2 - a))) hu
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

omit [Fintype nA] [Fintype nE] [NeZero d] in
/-- `1 ⊗ X^a` is `1` on the graph of the shifted permutation. -/
lemma oneShift_apply_self (a : ZMod d) (p : nA × nE) :
    ((1 : Matrix nA nA ℂ) ⊗ₖ shiftMat e a) p (p.1, e.symm (e p.2 - a)) = 1 := by
  rw [oneShift_apply]
  simp

omit [NeZero d] in
/-- **Conjugation by `1 ⊗ X^a` is a relabelling** (submatrix by the inverse shift). -/
lemma one_kron_shift_conj (a : ZMod d) (N : Matrix (nA × nE) (nA × nE) ℂ) :
    (1 ⊗ₖ shiftMat e a) * N * (1 ⊗ₖ shiftMat e a)ᴴ
      = N.submatrix (fun p => (p.1, e.symm (e p.2 - a)))
          (fun p => (p.1, e.symm (e p.2 - a))) := by
  ext p q
  have hAN : ∀ v, (((1 : Matrix nA nA ℂ) ⊗ₖ shiftMat e a) * N) p v
      = N (p.1, e.symm (e p.2 - a)) v := by
    intro v
    rw [Matrix.mul_apply, Finset.sum_eq_single (p.1, e.symm (e p.2 - a))]
    · rw [oneShift_apply_self, one_mul]
    · intro u _ hu
      rw [oneShift_apply_ne e a p u hu, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply, Finset.sum_eq_single (q.1, e.symm (e q.2 - a))]
  · rw [hAN, Matrix.conjTranspose_apply, oneShift_apply_self, star_one, mul_one,
      Matrix.submatrix_apply]
  · intro v _ hv
    rw [Matrix.conjTranspose_apply, oneShift_apply_ne e a q v hv, star_zero,
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Shift spread.**  Averaging the pinch over all shifts yields the partial trace tensored
with the identity: `∑_a (1 ⊗ X^a) (pinch M) (1 ⊗ X^a)ᴴ = (Tr_E M) ⊗ 1`. -/
lemma shift_spread (M : Matrix (nA × nE) (nA × nE) ℂ) :
    (∑ a : ZMod d, (1 ⊗ₖ shiftMat e a) * (Epinch M) * (1 ⊗ₖ shiftMat e a)ᴴ)
      = partialTraceRight M ⊗ₖ (1 : Matrix nE nE ℂ) := by
  simp_rw [one_kron_shift_conj]
  ext p q
  rw [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.one_apply]
  simp_rw [Matrix.submatrix_apply, Epinch]
  have hcond : ∀ a : ZMod d,
      (e.symm (e p.2 - a) = e.symm (e q.2 - a)) ↔ p.2 = q.2 := by
    intro a
    rw [e.symm.injective.eq_iff, sub_left_inj, e.injective.eq_iff]
  simp_rw [hcond]
  by_cases hpq : p.2 = q.2
  · simp_rw [if_pos hpq]
    rw [mul_one, partialTraceRight_apply, ← hpq]
    exact Equiv.sum_comp ((Equiv.subLeft (e p.2)).trans e.symm)
      (fun z => M (p.1, z) (q.1, z))
  · simp_rw [if_neg hpq]
    rw [Finset.sum_const_zero, mul_zero]

/-- `1 ⊗ W a b` factors as `(1 ⊗ X^a)(1 ⊗ Z^b)`. -/
lemma one_kron_Wmat (a b : ZMod d) :
    (1 : Matrix nA nA ℂ) ⊗ₖ Wmat e a b
      = (1 ⊗ₖ shiftMat e a) * (1 ⊗ₖ clockMat e b) := by
  rw [Wmat, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- **The Weyl twirl (depolarising identity).**
`∑_{a,b} (1 ⊗ W a b) M (1 ⊗ W a b)ᴴ = d • ((Tr_E M) ⊗ 1)`. -/
lemma twirl_sum (M : Matrix (nA × nE) (nA × nE) ℂ) :
    (∑ a : ZMod d, ∑ b : ZMod d, (1 ⊗ₖ Wmat e a b) * M * (1 ⊗ₖ Wmat e a b)ᴴ)
      = (d : ℂ) • (partialTraceRight M ⊗ₖ (1 : Matrix nE nE ℂ)) := by
  have hb : ∀ a : ZMod d,
      (∑ b : ZMod d, (1 ⊗ₖ Wmat e a b) * M * (1 ⊗ₖ Wmat e a b)ᴴ)
        = (1 ⊗ₖ shiftMat e a) * ((d : ℂ) • Epinch M) * (1 ⊗ₖ shiftMat e a)ᴴ := by
    intro a
    have hterm : ∀ b : ZMod d, (1 ⊗ₖ Wmat e a b) * M * (1 ⊗ₖ Wmat e a b)ᴴ
        = (1 ⊗ₖ shiftMat e a)
            * ((1 ⊗ₖ clockMat e b) * M * (1 ⊗ₖ clockMat e b)ᴴ)
            * (1 ⊗ₖ shiftMat e a)ᴴ := by
      intro b
      rw [one_kron_Wmat, Matrix.conjTranspose_mul]
      simp only [mul_assoc]
    simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, clock_pinch]
  calc (∑ a : ZMod d, ∑ b : ZMod d, (1 ⊗ₖ Wmat e a b) * M * (1 ⊗ₖ Wmat e a b)ᴴ)
      = ∑ a : ZMod d,
          (1 ⊗ₖ shiftMat e a) * ((d : ℂ) • Epinch M) * (1 ⊗ₖ shiftMat e a)ᴴ :=
        Finset.sum_congr rfl (fun a _ => hb a)
    _ = (d : ℂ) • (partialTraceRight M ⊗ₖ (1 : Matrix nE nE ℂ)) := by
        simp_rw [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, shift_spread]

/-! ### Unitarity of the Weyl operators -/

/-- `Z^b` is unitary (`star Z^b · Z^b = 1`). -/
lemma clockMat_star_mul (b : ZMod d) : star (clockMat e b) * clockMat e b = 1 := by
  have hR : 0 < ringChar (ZMod d) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne d)
  simp only [clockMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext t
  rw [Pi.star_apply, ← starRingEnd_apply, AddChar.starComp_apply hR, AddChar.inv_apply,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

omit [Fintype nA] [NeZero d] in
/-- `X^a` is unitary (`star X^a · X^a = 1`). -/
lemma shiftMat_star_mul (a : ZMod d) : star (shiftMat e a) * shiftMat e a = 1 := by
  ext s s'
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (e.symm (e s + a))]
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    have hx0 : e.symm (e (e.symm (e s + a)) - a) = s := by
      rw [Equiv.apply_symm_apply, add_sub_cancel_right, Equiv.symm_apply_apply]
    simp only [shiftMat, hx0, if_true, star_one, one_mul]
    rcases eq_or_ne s s' with hss | hss
    · rw [if_pos hss.symm, if_pos hss]
    · rw [if_neg (fun h => hss h.symm), if_neg hss]
  · intro x _ hx
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    have hne : s ≠ e.symm (e x - a) := by
      intro hc
      apply hx
      have hc' : e s = e x - a := by rw [hc, Equiv.apply_symm_apply]
      rw [Equiv.eq_symm_apply, hc']
      ring
    simp only [shiftMat]
    rw [if_neg hne, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype nA] in
/-- `W a b` is unitary (`star (W a b) · W a b = 1`). -/
lemma Wmat_star_mul (a b : ZMod d) : star (Wmat e a b) * Wmat e a b = 1 := by
  rw [Wmat, star_mul, mul_assoc,
    ← mul_assoc (star (shiftMat e a)) (shiftMat e a) (clockMat e b),
    shiftMat_star_mul, one_mul, clockMat_star_mul]

/-- `1 ⊗ W a b` is unitary (`star (1 ⊗ W a b) · (1 ⊗ W a b) = 1`). -/
lemma one_kron_Wmat_star_mul (a b : ZMod d) :
    star ((1 : Matrix nA nA ℂ) ⊗ₖ Wmat e a b) * ((1 : Matrix nA nA ℂ) ⊗ₖ Wmat e a b) = 1 := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.star_eq_conjTranspose, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Wmat_star_mul, Matrix.one_kronecker_one]

end Twirl

/-! ## Finite Jensen inequality for the jointly convex relative entropy -/

section Convexity

-- `PosDef`/`relEntropyMat` need `Fintype`/`DecidableEq` in the proofs (via `posDef_convex`,
-- `cfc`), but these instances are inferred, not syntactic, in the statements.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive-definite matrices form a convex set. -/
lemma convex_posDef : Convex ℝ {A : Matrix n n ℂ | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  rw [Set.mem_setOf_eq] at hA hB ⊢
  have hb' : b = 1 - a := by linarith
  rw [hb']
  exact posDef_convex hA hB ⟨ha, by linarith⟩

/-- Pairs of positive-definite matrices form a convex set. -/
lemma convex_posDefPairs :
    Convex ℝ {q : Matrix n n ℂ × Matrix n n ℂ | q.1.PosDef ∧ q.2.PosDef} := by
  have hset : {q : Matrix n n ℂ × Matrix n n ℂ | q.1.PosDef ∧ q.2.PosDef}
      = {A : Matrix n n ℂ | A.PosDef} ×ˢ {A : Matrix n n ℂ | A.PosDef} := by
    ext q; simp only [Set.mem_setOf_eq, Set.mem_prod]
  rw [hset]
  exact convex_posDef.prod convex_posDef

/-- Lieb's joint convexity packaged as a `ConvexOn` statement on the pairs of faithful states. -/
lemma convexOn_relEntropyMat :
    ConvexOn ℝ {q : Matrix n n ℂ × Matrix n n ℂ | q.1.PosDef ∧ q.2.PosDef}
      (fun q => relEntropyMat q.1 q.2) := by
  refine ⟨convex_posDefPairs, fun x hx y hy a b ha hb hab => ?_⟩
  rw [Set.mem_setOf_eq] at hx hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hcv := relEntropyMat_jointly_convex x.1 y.1 x.2 y.2 a ⟨ha, by linarith⟩
    hx.1 hy.1 hx.2 hy.2
  simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    using hcv

/-- **Finite Jensen inequality** for the (jointly convex) relative entropy: for a finite
convex combination of faithful states, `D(∑ wᵢ ρᵢ ‖ ∑ wᵢ σᵢ) ≤ ∑ wᵢ D(ρᵢ ‖ σᵢ)`. -/
lemma relEntropyMat_convex_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρ σ : ι → Matrix n n ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hρ : ∀ i ∈ s, (ρ i).PosDef) (hσ : ∀ i ∈ s, (σ i).PosDef) :
    relEntropyMat (∑ i ∈ s, w i • ρ i) (∑ i ∈ s, w i • σ i)
      ≤ ∑ i ∈ s, w i * relEntropyMat (ρ i) (σ i) := by
  have hmem : ∀ i ∈ s,
      ((ρ i, σ i) : Matrix n n ℂ × Matrix n n ℂ)
        ∈ {q : Matrix n n ℂ × Matrix n n ℂ | q.1.PosDef ∧ q.2.PosDef} :=
    fun i hi => ⟨hρ i hi, hσ i hi⟩
  have hJ := convexOn_relEntropyMat.map_sum_le hw hsum hmem
  simpa only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    using hJ

end Convexity

/-! ## The partial trace of a faithful state is faithful -/

section PartialTrace

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- The partial trace of a positive-definite state over a nonempty factor is positive definite. -/
lemma posDef_partialTraceRight [Nonempty nB] {M : Matrix (nA × nB) (nA × nB) ℂ}
    (hM : M.PosDef) : (partialTraceRight M).PosDef := by
  obtain ⟨j0⟩ := ‹Nonempty nB›
  rw [partialTraceRight_eq_sum_submatrix,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j0)]
  refine Matrix.PosDef.add_posSemidef
    (hM.submatrix (fun a b hab => (Prod.ext_iff.mp hab).1)) ?_
  exact Matrix.posSemidef_sum _ (fun j _ => hM.posSemidef.submatrix _)

end PartialTrace

/-! ## Data-processing inequality for faithful states -/

section Faithful

variable {nA nE : Type} [Fintype nA] [DecidableEq nA] [Fintype nE] [DecidableEq nE]

/-- **Data-processing inequality (faithful case).**  For positive-definite states `ρ, σ`, the
partial trace never increases the Umegaki relative entropy. -/
theorem relEntropyMonotone_partialTrace_faithful (ρ σ : DensityMatrix (nA × nE))
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef) :
    relEntropy (DensityMatrix.partialTraceRight ρ) (DensityMatrix.partialTraceRight σ)
      ≤ relEntropy ρ σ := by
  haveI hNE : Nonempty nE := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI : IsEmpty (nA × nE) := inferInstance
    have ht := σ.trace_one
    simp only [Matrix.trace, Matrix.diag_apply, Finset.univ_eq_empty, Finset.sum_empty] at ht
    exact one_ne_zero ht.symm
  set d := Fintype.card nE with hd
  haveI hd0 : NeZero d := ⟨Fintype.card_ne_zero⟩
  have hdpos : (0 : ℝ) < d := by rw [hd]; exact_mod_cast Fintype.card_pos
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have e : nE ≃ ZMod d := Fintype.equivOfCardEq (hd.symm.trans (ZMod.card d).symm)
  set τ : DensityMatrix nE := DensityMatrix.maximallyMixed with hτ
  have hτval : τ.val = ((d : ℝ)⁻¹) • (1 : Matrix nE nE ℂ) := by
    rw [hτ]; simp only [DensityMatrix.maximallyMixed, ← hd]
  have hτpd : τ.val.PosDef := by
    rw [hτval]
    have hcx : ((d : ℝ)⁻¹) • (1 : Matrix nE nE ℂ)
        = diagonal (fun _ : nE => ((d : ℝ)⁻¹ : ℂ)) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
      by_cases h : i = j
      · simp [h, Complex.real_smul]
      · simp [h]
    rw [hcx, Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast inv_pos.mpr hdpos
  have hptrσ : (DensityMatrix.partialTraceRight σ).val.PosDef := posDef_partialTraceRight hσ
  -- unitarity of the Weyl operators on the whole system
  have hstar : ∀ ab : ZMod d × ZMod d,
      star ((1 : Matrix nA nA ℂ) ⊗ₖ Wmat e ab.1 ab.2)
          * ((1 : Matrix nA nA ℂ) ⊗ₖ Wmat e ab.1 ab.2) = 1 :=
    fun ab => one_kron_Wmat_star_mul e ab.1 ab.2
  have hunit : ∀ ab : ZMod d × ZMod d,
      (1 : Matrix nA nA ℂ) ⊗ₖ Wmat e ab.1 ab.2 ∈ Matrix.unitaryGroup (nA × nE) ℂ :=
    fun ab => Matrix.mem_unitaryGroup_iff'.mpr (hstar ab)
  have hIsUnit : ∀ ab : ZMod d × ZMod d,
      IsUnit ((1 : Matrix nA nA ℂ) ⊗ₖ Wmat e ab.1 ab.2) := by
    intro ab
    have h2 : ((1 : Matrix nA nA ℂ) ⊗ₖ Wmat e ab.1 ab.2)
        * star ((1 : Matrix nA nA ℂ) ⊗ₖ Wmat e ab.1 ab.2) = 1 :=
      (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hstar ab)
    exact ⟨⟨_, _, h2, hstar ab⟩, rfl⟩
  -- the twirled families and weights
  set Wg : ZMod d × ZMod d → Matrix.unitaryGroup (nA × nE) ℂ :=
    fun ab => ⟨(1 : Matrix nA nA ℂ) ⊗ₖ Wmat e ab.1 ab.2, hunit ab⟩ with hWg
  set w : ZMod d × ZMod d → ℝ := fun _ => ((d : ℝ) ^ 2)⁻¹ with hw
  set R : ZMod d × ZMod d → Matrix (nA × nE) (nA × nE) ℂ :=
    fun ab => (ρ.conj (Wg ab)).val with hR
  set S : ZMod d × ZMod d → Matrix (nA × nE) (nA × nE) ℂ :=
    fun ab => (σ.conj (Wg ab)).val with hS
  -- Rab, Sab are positive definite
  have hRpd : ∀ ab, (R ab).PosDef := by
    intro ab
    rw [hR]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (hIsUnit ab)).mpr hρ
  have hSpd : ∀ ab, (S ab).PosDef := by
    intro ab
    rw [hS]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (hIsUnit ab)).mpr hσ
  -- scalar identity used in the twirl-to-density bridge
  have hscal : ∀ Y : Matrix (nA × nE) (nA × nE) ℂ,
      ((d : ℝ) ^ 2)⁻¹ • ((d : ℂ) • Y) = (d : ℝ)⁻¹ • Y := by
    intro Y
    have hce : (d : ℂ) • Y = (d : ℝ) • Y := by simp only [Nat.cast_smul_eq_nsmul]
    rw [hce, smul_smul]
    congr 1
    field_simp
  -- twirl bridge: ∑ w • R = ((Tr_E ρ) ⊗ τ).val
  have hRsum : (∑ ab : ZMod d × ZMod d, w ab • R ab)
      = ((DensityMatrix.partialTraceRight ρ).kron τ).val := by
    have h1 : (∑ ab : ZMod d × ZMod d, R ab)
        = (d : ℂ) • (partialTraceRight ρ.val ⊗ₖ (1 : Matrix nE nE ℂ)) := by
      simp only [hR, hWg, DensityMatrix.conj, Matrix.star_eq_conjTranspose,
        Fintype.sum_prod_type]
      exact twirl_sum e ρ.val
    simp only [hw, ← Finset.smul_sum, h1, hscal]
    change (d : ℝ)⁻¹ • _ = partialTraceRight ρ.val ⊗ₖ τ.val
    rw [hτval, Matrix.kronecker_smul]
  have hSsum : (∑ ab : ZMod d × ZMod d, w ab • S ab)
      = ((DensityMatrix.partialTraceRight σ).kron τ).val := by
    have h1 : (∑ ab : ZMod d × ZMod d, S ab)
        = (d : ℂ) • (partialTraceRight σ.val ⊗ₖ (1 : Matrix nE nE ℂ)) := by
      simp only [hS, hWg, DensityMatrix.conj, Matrix.star_eq_conjTranspose,
        Fintype.sum_prod_type]
      exact twirl_sum e σ.val
    simp only [hw, ← Finset.smul_sum, h1, hscal]
    change (d : ℝ)⁻¹ • _ = partialTraceRight σ.val ⊗ₖ τ.val
    rw [hτval, Matrix.kronecker_smul]
  -- LHS equals the relEntropy of the twirled density matrices
  have hσkron : ((DensityMatrix.partialTraceRight σ).kron τ).val.PosDef :=
    Matrix.PosDef.kronecker hptrσ hτpd
  have hLHS : relEntropyMat (∑ ab, w ab • R ab) (∑ ab, w ab • S ab)
      = relEntropy (DensityMatrix.partialTraceRight ρ) (DensityMatrix.partialTraceRight σ) := by
    rw [hRsum, hSsum,
      relEntropyMat_eq_relEntropy ((DensityMatrix.partialTraceRight ρ).kron τ)
        ((DensityMatrix.partialTraceRight σ).kron τ) hσkron,
      relEntropy_ancilla_invariant _ _ τ hτpd hptrσ]
  -- each twirled term has the same relative entropy as the original
  have hterm : ∀ ab, relEntropyMat (R ab) (S ab) = relEntropy ρ σ := by
    intro ab
    rw [hR, hS,
      relEntropyMat_eq_relEntropy (ρ.conj (Wg ab)) (σ.conj (Wg ab))
        ((Matrix.IsUnit.posDef_star_right_conjugate_iff (hIsUnit ab)).mpr hσ),
      relEntropy_conj_invariant]
  -- weights sum to one
  have hwsum : (∑ ab : ZMod d × ZMod d, w ab) = 1 := by
    simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
      nsmul_eq_mul]
    rw [Nat.cast_mul]
    field_simp
  -- assemble
  rw [← hLHS]
  have hconv := relEntropyMat_convex_sum (Finset.univ : Finset (ZMod d × ZMod d)) w R S
    (fun _ _ => by rw [hw]; positivity) hwsum (fun ab _ => hRpd ab) (fun ab _ => hSpd ab)
  calc relEntropyMat (∑ ab, w ab • R ab) (∑ ab, w ab • S ab)
      ≤ ∑ ab, w ab * relEntropyMat (R ab) (S ab) := hconv
    _ = ∑ ab, w ab * relEntropy ρ σ := by simp_rw [hterm]
    _ = (∑ ab, w ab) * relEntropy ρ σ := by rw [Finset.sum_mul]
    _ = relEntropy ρ σ := by rw [hwsum, one_mul]

end Faithful

end Oseledets.OperatorEntropy.Lieb
