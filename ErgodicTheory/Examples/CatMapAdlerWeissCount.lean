/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapAdlerWeissMeasure
import ErgodicTheory.Entropy.Ruelle.PosAtomCount

/-!
# Admissible-path count for the Adler–Weiss partition of the cat map

This module carries out the **transfer-matrix count** of the positive-measure atoms of the flat
iterated join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ catAWPartition` of the Arnold cat map `catTorus` and its Adler–Weiss
Markov partition `catAWPartition` (six cells: a null junk cell plus the five projected golden
branches).  The upshot is the crude Ruelle bound

`ksEntropyPartition catTorus catAWPartition ≤ log λ₊`,   `λ₊ = (3+√5)/2 = φ²`.

## Strategy

* **Transition forcing** (`awCell_succ_inter_preimage_empty`): the geometric keystone
  `branch_step`, pushed through the injectivity of `catProj` on the fundamental domain
  `awBox 0 ∪ awBox 1`, shows a point of branch cell `e` maps into branch cell `e'` only when the
  target rectangle of `e` equals the source rectangle of `e'`.
* **Null atoms**: any join itinerary visiting the junk cell (`ksJoin_cell_null_of_junk`) or making a
  forbidden transition (`ksJoin_cell_null_of_nonadmissible`) has a null atom, hence is uncounted by
  `posAtomCount`.
* **Admissible count**: the surviving itineraries inject into *admissible* symbol sequences
  `g : Fin (n+1) → Fin 5` (`Adm`), whose weighted count `W n = λ₊ⁿ·(3φ+2)` is controlled by the
  golden weight identity `∑_{src e' = b} w e' = λ₊·w(b)` (`weight_sum_src`).
* **Assembly**: `catAW_posAtomCount_le` gives `posAtomCount ≤ (3φ+2)·λ₊ⁿ`, and the
  positive-measure atom-count backbone `ksEntropyPartition_le_of_posAtomCount_growth` converts the
  growth rate into the entropy bound `catAW_ksEntropyPartition_le`.
-/

open MeasureTheory Matrix Function Filter

noncomputable section

/-- Normalise the circle measure to total mass `1`, matching the imported cat-map measure modules so
that `volume : Measure T2` lines up with `catAWPartition` and `measurePreserving_catTorus`. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_awCount :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_awCount :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_awCount :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

open ErgodicTheory.Entropy

/-! ## The two golden rectangles are disjoint in the plane -/

/-- The two Adler–Weiss rectangles are disjoint in the plane: their unstable windows `[0,φ)` and
`[φ,φ²)` do not overlap. -/
lemma awBox_disjoint {b b' : Fin 2} (h : b ≠ b') : Disjoint (awBox b) (awBox b') := by
  rw [Set.disjoint_left]
  intro v hv hv'
  fin_cases b <;> fin_cases b' <;>
    first
    | exact absurd rfl h
    | (simp only [awBox, Set.mem_setOf_eq, Set.mem_Ico] at hv hv'
       linarith [hv.1.1, hv.1.2, hv'.1.1, hv'.1.2])

/-! ## Transition forcing -/

/-- **Transition forcing.**  A point of the branch cell `awCell e.succ` maps under `catTorus` into
the branch cell `awCell e'.succ` only if the target rectangle of `e` coincides with the source
rectangle of `e'`.  Contrapositive: if `tgt e ≠ src e'` the corresponding two-step cylinder is
empty.  The keystone `branch_step` places the image in `awBox (tgt e)`; the projected branch places
it in `awBox (src e')`; injectivity of `catProj` on `awBox 0 ∪ awBox 1` identifies the two lifts, so
the point lies in `awBox (tgt e) ∩ awBox (src e')`, which is empty when the rectangles differ. -/
theorem awCell_succ_inter_preimage_empty {e e' : Fin 5} (h : tgt e ≠ src e') :
    awCell e.succ ∩ catTorus ⁻¹' (awCell e'.succ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hx'⟩
  rw [awCell_succ] at hx
  rw [Set.mem_preimage, awCell_succ] at hx'
  obtain ⟨r, hr, hxr⟩ := hx
  obtain ⟨r', hr', hxr'⟩ := hx'
  have hs : catℝ *ᵥ r - off e ∈ awBox (tgt e) := branch_step e hr
  have hcat : catTorus x = catProj (catℝ *ᵥ r - off e) := by
    rw [catProj_sub, catProj_off, sub_zero, catProj_mulVec, hxr]
  have heq : catProj (catℝ *ᵥ r - off e) = catProj r' := hcat.symm.trans hxr'.symm
  have hsu : catℝ *ᵥ r - off e ∈ awBox 0 ∪ awBox 1 := awBox_subset_awUnion (tgt e) hs
  have hr'u : r' ∈ awBox 0 ∪ awBox 1 :=
    awBox_subset_awUnion (src e') (branchBox_subset_awBox_src e' hr')
  have hsr' : catℝ *ᵥ r - off e = r' := catProj_injOn_awUnion hsu hr'u heq
  have hr'tgt : r' ∈ awBox (tgt e) := hsr' ▸ hs
  exact (Set.disjoint_left.mp (awBox_disjoint h) hr'tgt)
    (branchBox_subset_awBox_src e' hr')

/-! ## Null join atoms -/

/-- **Junk atoms are null.**  A join itinerary `f` visiting the junk cell (`f k = 0`) has an atom
contained in `(catTorusᵏ)⁻¹` of the null junk cell, so it is itself null. -/
theorem ksJoin_cell_null_of_junk {N : ℕ} (f : Fin N → Fin 6) (k : Fin N) (hk : f k = 0) :
    (volume : Measure T2) ((ksJoin measurePreserving_catTorus catAWPartition N).cells f) = 0 := by
  have hcell : catAWPartition.cells (f k) = awCell 0 :=
    (congrArg catAWPartition.cells hk).trans rfl
  have hsub : (ksJoin measurePreserving_catTorus catAWPartition N).cells f
      ⊆ (catTorus^[(k : ℕ)]) ⁻¹' catAWPartition.cells (f k) := by
    rw [ksJoin_cells, ksJoinCells_apply]; exact Set.iInter_subset _ k
  refine measure_mono_null hsub ?_
  rw [(measurePreserving_catTorus.iterate (k : ℕ)).measure_preimage
    ((catAWPartition.measurable (f k)).nullMeasurableSet), hcell]
  exact volume_awCell_zero

/-- **Forbidden-transition atoms are empty.**  If `f` makes a forbidden step at consecutive indices
`a, b` (`b = a+1`, `f a = e.succ`, `f b = e'.succ`, `tgt e ≠ src e'`), then its atom is empty: a
point would force `catTorusᵃ x ∈ awCell e.succ` and `catTorus (catTorusᵃ x) ∈ awCell e'.succ`,
contradicting `awCell_succ_inter_preimage_empty`. -/
theorem ksJoin_cell_null_of_nonadmissible {N : ℕ} (f : Fin N → Fin 6) (a b : Fin N)
    (hab : (b : ℕ) = (a : ℕ) + 1) {e e' : Fin 5}
    (hfa : f a = e.succ) (hfb : f b = e'.succ) (h : tgt e ≠ src e') :
    (volume : Measure T2) ((ksJoin measurePreserving_catTorus catAWPartition N).cells f) = 0 := by
  suffices hE : (ksJoin measurePreserving_catTorus catAWPartition N).cells f = ∅ by
    rw [hE]; exact measure_empty
  rw [ksJoin_cells, ksJoinCells_apply, Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Set.mem_iInter] at hx
  have hxa := hx a
  have hxb := hx b
  rw [Set.mem_preimage, hfa] at hxa
  rw [Set.mem_preimage, hfb] at hxb
  have hb' : catTorus^[(b : ℕ)] x = catTorus (catTorus^[(a : ℕ)] x) := by
    rw [hab, Function.iterate_succ_apply']
  rw [hb'] at hxb
  exact (Set.eq_empty_iff_forall_notMem.mp (awCell_succ_inter_preimage_empty h))
    (catTorus^[(a : ℕ)] x) ⟨hxa, hxb⟩

/-! ## Admissible symbol sequences and their weighted count -/

/-- The branch weight `w e = φ` when the target rectangle of `e` is `R₁`, and `= 1` when it is `R₂`.
Encoded directly as `![φ,1,φ,1,φ]` following `tgt = ![0,1,0,1,0]`. -/
def w : Fin 5 → ℝ := ![phiAW, 1, phiAW, 1, phiAW]

/-- The weight attached to a target rectangle: `φ` for `R₁`, `1` for `R₂`. -/
def wOfTgt : Fin 2 → ℝ := ![phiAW, 1]

/-- The branch weight depends only on the target rectangle: `w e = wOfTgt (tgt e)`. -/
lemma w_eq_wOfTgt_tgt (e : Fin 5) : w e = wOfTgt (tgt e) := by
  fin_cases e <;> rfl

/-- Every branch weight is at least `1`. -/
lemma one_le_w (e : Fin 5) : (1 : ℝ) ≤ w e := by
  fin_cases e <;> norm_num [w] <;> linarith [one_lt_phiAW]

/-- **The golden weight identity.**  Summing the branch weights over all admissible successors of a
state with target rectangle `b` yields `λ₊` times the weight of `b`: `∑_{src e' = b} w e' = λ₊·w(b)`
(`2φ+1 = φ³ = λ₊·φ` from `R₁`, `1+φ = φ² = λ₊·1` from `R₂`). -/
lemma weight_sum_src (b : Fin 2) :
    ∑ e' : Fin 5, (if b = src e' then w e' else 0) = lam * wOfTgt b := by
  fin_cases b <;>
    rw [Fin.sum_univ_five] <;>
    norm_num [src, w, wOfTgt, lam_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four] <;>
    nlinarith [phiAW_sq]

/-- A symbol sequence `g : Fin (n+1) → Fin 5` is **admissible** when every consecutive pair follows
a legal Markov transition: the target rectangle of `g i` equals the source of `g (i+1)`. -/
def Adm {n : ℕ} (g : Fin (n + 1) → Fin 5) : Prop :=
  ∀ i : Fin n, tgt (g i.castSucc) = src (g i.succ)

instance decidableAdm {n : ℕ} : DecidablePred (Adm : (Fin (n + 1) → Fin 5) → Prop) :=
  fun g => inferInstanceAs (Decidable (∀ i : Fin n, tgt (g i.castSucc) = src (g i.succ)))

/-- Admissibility of an appended sequence factors as admissibility of the prefix plus a legal final
transition. -/
lemma Adm_snoc {n : ℕ} (g' : Fin (n + 1) → Fin 5) (e' : Fin 5) :
    Adm (Fin.snoc g' e') ↔ Adm g' ∧ tgt (g' (Fin.last n)) = src e' := by
  constructor
  · intro hAll
    refine ⟨fun j => ?_, ?_⟩
    · have hj := hAll j.castSucc
      rwa [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc] at hj
    · have hl := hAll (Fin.last n)
      rwa [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] at hl
  · rintro ⟨hg, hb⟩ i
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]; exact hb
    | cast j => rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]; exact hg j

/-- The append bijection `(prefix, last symbol) ≃ full sequence`. -/
def snocEquiv (n : ℕ) : (Fin (n + 1) → Fin 5) × Fin 5 ≃ (Fin (n + 1 + 1) → Fin 5) where
  toFun p := Fin.snoc p.1 p.2
  invFun g := (Fin.init g, g (Fin.last (n + 1)))
  left_inv p := by obtain ⟨g', e'⟩ := p; simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv g := by simp only [Fin.snoc_init_self]

@[simp] lemma snocEquiv_apply {n : ℕ} (g' : Fin (n + 1) → Fin 5) (e' : Fin 5) :
    snocEquiv n (g', e') = Fin.snoc g' e' := rfl

/-- The **weighted admissible count** `W n = ∑_{g adm} w(last symbol)`, summed over admissible
sequences of length `n+1`, weighting each by the weight of its final symbol.  Cells of measure zero
are excluded via the indicator. -/
noncomputable def W (n : ℕ) : ℝ :=
  ∑ g : Fin (n + 1) → Fin 5, if Adm g then w (g (Fin.last n)) else 0

/-- **Base case** `W 0 = 3φ+2`: length-`1` sequences are all admissible, and the weights sum to
`φ+1+φ+1+φ = 3φ+2`. -/
lemma W_zero : W 0 = 3 * phiAW + 2 := by
  rw [W]
  have hsum : (∑ g : Fin 1 → Fin 5, if Adm g then w (g (Fin.last 0)) else 0)
      = ∑ g : Fin 1 → Fin 5, w (g (Fin.last 0)) :=
    Finset.sum_congr rfl (fun g _ => if_pos (fun i => i.elim0))
  rw [hsum, Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 5))
      (fun g => w (g (Fin.last 0))) (fun e => w e)
      (fun g => congrArg (fun x => w (g x))
        ((Fin.fin_one_eq_zero (Fin.last 0)).trans (Fin.fin_one_eq_zero (default : Fin 1)).symm))]
  simp only [Fin.sum_univ_five, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

/-- **Recursion** `W (n+1) = λ₊·W n`: regrouping admissible extensions by their final transition and
applying the golden weight identity `weight_sum_src`. -/
lemma W_succ (n : ℕ) : W (n + 1) = lam * W n := by
  have key : ∀ g' : Fin (n + 1) → Fin 5,
      (∑ e' : Fin 5,
          if Adm (Fin.snoc g' e') then
            w ((Fin.snoc g' e' : Fin (n + 1 + 1) → Fin 5) (Fin.last (n + 1))) else 0)
        = lam * (if Adm g' then w (g' (Fin.last n)) else 0) := by
    intro g'
    simp only [Adm_snoc, Fin.snoc_last]
    by_cases hA : Adm g'
    · rw [if_pos hA]
      simp only [hA, true_and]
      rw [w_eq_wOfTgt_tgt (g' (Fin.last n)), weight_sum_src]
    · rw [if_neg hA, mul_zero]
      exact Finset.sum_eq_zero (fun e' _ => if_neg (fun hh => hA hh.1))
  rw [W]
  rw [← Equiv.sum_comp (snocEquiv n)
      (fun g : Fin (n + 1 + 1) → Fin 5 => if Adm g then w (g (Fin.last (n + 1))) else 0)]
  rw [Fintype.sum_prod_type]
  simp only [snocEquiv_apply]
  rw [W, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun g' _ => key g')

/-- **Closed form** `W n = λ₊ⁿ·(3φ+2)`. -/
lemma W_eq (n : ℕ) : W n = lam ^ n * (3 * phiAW + 2) := by
  induction n with
  | zero => rw [W_zero, pow_zero, one_mul]
  | succ k ih => rw [W_succ, ih, pow_succ]; ring

/-- The number of admissible sequences is bounded by the weighted count (each weight is `≥ 1`). -/
lemma admCard_le_W (n : ℕ) :
    ((Finset.univ.filter (Adm : (Fin (n + 1) → Fin 5) → Prop)).card : ℝ) ≤ W n := by
  rw [W, Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum (fun g _ => ?_)
  by_cases hA : Adm g
  · rw [if_pos hA, if_pos hA]; exact one_le_w _
  · rw [if_neg hA, if_neg hA]

/-! ## The junk/forbidden itineraries are excluded from the positive-measure count -/

/-- A retraction `Fin 6 → Fin 5` sending the junk symbol `0` to `0` and each `e.succ` to `e`. -/
def red : Fin 6 → Fin 5 := Fin.cases 0 id

lemma red_succ (e : Fin 5) : red e.succ = e := by
  simp only [red, Fin.cases_succ, id_eq]

lemma succ_red_of_ne {i : Fin 6} (h : i ≠ 0) : (red i).succ = i := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 5, i = j.succ := ⟨i.pred h, (Fin.succ_pred i h).symm⟩
  rw [red_succ]

/-- **The positive-measure atoms inject into admissible sequences.**  A positive-measure atom never
visits the junk cell (`ksJoin_cell_null_of_junk`) and never makes a forbidden transition
(`ksJoin_cell_null_of_nonadmissible`), so `red ∘ f` is an admissible `Fin (n+1) → Fin 5` sequence,
and the map is injective because each symbol is nonzero. -/
theorem posAtomCount_le_admCard (n : ℕ) :
    posAtomCount measurePreserving_catTorus catAWPartition (n + 1)
      ≤ (Finset.univ.filter (Adm : (Fin (n + 1) → Fin 5) → Prop)).card := by
  rw [posAtomCount]
  refine Finset.card_le_card_of_injOn (fun f => red ∘ f) ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
    intro i
    have hfa : f i.castSucc ≠ 0 := fun h0 => hf (ksJoin_cell_null_of_junk f i.castSucc h0)
    have hfb : f i.succ ≠ 0 := fun h0 => hf (ksJoin_cell_null_of_junk f i.succ h0)
    rw [Function.comp_apply, Function.comp_apply]
    by_contra hne
    exact hf (ksJoin_cell_null_of_nonadmissible f i.castSucc i.succ
      (by rw [Fin.val_succ, Fin.val_castSucc]) (succ_red_of_ne hfa).symm
      (succ_red_of_ne hfb).symm hne)
  · intro f hf f' hf' hff
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf hf'
    funext k
    have hfk : f k ≠ 0 := fun h0 => hf (ksJoin_cell_null_of_junk f k h0)
    have hf'k : f' k ≠ 0 := fun h0 => hf' (ksJoin_cell_null_of_junk f' k h0)
    have hkk := congrFun hff k
    simp only [Function.comp_apply] at hkk
    rw [← succ_red_of_ne hfk, ← succ_red_of_ne hf'k, hkk]

/-! ## Assembly -/

/-- **The positive-measure atom count grows like `λ₊ⁿ`.**  Combining the injection into admissible
sequences with the closed form `W n = λ₊ⁿ·(3φ+2)`. -/
theorem catAW_posAtomCount_le {n : ℕ} (hn : 1 ≤ n) :
    (posAtomCount measurePreserving_catTorus catAWPartition n : ℝ)
      ≤ (3 * phiAW + 2) * lam ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc (posAtomCount measurePreserving_catTorus catAWPartition (m + 1) : ℝ)
      ≤ ((Finset.univ.filter (Adm : (Fin (m + 1) → Fin 5) → Prop)).card : ℝ) := by
        exact_mod_cast posAtomCount_le_admCard m
    _ ≤ W m := admCard_le_W m
    _ = lam ^ m * (3 * phiAW + 2) := W_eq m
    _ ≤ (3 * phiAW + 2) * lam ^ (m + 1) := by
        rw [pow_succ]
        have hl : (1 : ℝ) ≤ lam := by rw [lam_eq]; linarith [phiAW_pos]
        have hC : (0 : ℝ) ≤ 3 * phiAW + 2 := by linarith [phiAW_pos]
        have hlm : (0 : ℝ) ≤ lam ^ m := pow_nonneg lam_pos.le m
        nlinarith [mul_nonneg (mul_nonneg hC hlm) (by linarith [hl] : (0 : ℝ) ≤ lam - 1)]

/-- **Crude Ruelle bound for the Adler–Weiss partition.**  The Kolmogorov–Sinai entropy of the
Adler–Weiss partition under the cat map is at most `log λ₊ = log((3+√5)/2)`, the logarithm of the
expanding eigenvalue.  This feeds the positive-measure atom-count backbone
`ksEntropyPartition_le_of_posAtomCount_growth` with the growth rate `posAtomCount ≤ (3φ+2)·λ₊ⁿ`. -/
theorem catAW_ksEntropyPartition_le :
    ksEntropyPartition measurePreserving_catTorus catAWPartition
      ≤ Real.log ((3 + Real.sqrt 5) / 2) := by
  have hlp : 0 < lam := lam_pos
  have hCge : (1 : ℝ) ≤ 3 * phiAW + 2 := by nlinarith [one_lt_phiAW]
  have hmain : ksEntropyPartition measurePreserving_catTorus catAWPartition ≤ Real.log lam := by
    refine ksEntropyPartition_le_of_posAtomCount_growth
      measurePreserving_catTorus catAWPartition hCge ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hexp : Real.exp ((n : ℝ) * Real.log lam) = lam ^ n := by
      rw [Real.exp_nat_mul, Real.exp_log hlp]
    rw [hexp]
    exact catAW_posAtomCount_le hn
  exact hmain

end ErgodicTheory.CatMapToral

end
