/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapCoverMeasure
import ErgodicTheory.Examples.CatMapAdlerWeiss
import ErgodicTheory.Entropy.Partition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-!
# The Adler–Weiss golden two-box geometry as a genuine measure partition

This module turns the *pure geometry* of `ErgodicTheory.Examples.CatMapAdlerWeiss` (the two golden
rectangles, the five affine branches, the covering-projection injectivity on each branch) into a
genuine finite **`MeasurePartition`** of the torus `T2` under `volume`, with explicitly computed
cell measures.

The engine is the **tiling extension** of the per-tile measure identity of
`ErgodicTheory.Examples.CatMapCoverMeasure`:

* `volume_catProj_image_of_injOn` — for a measurable `K` on which the covering projection `catProj`
  is injective, `volume (catProj '' K) = volume K`, obtained by summing the exact per-tile identity
  over the integer tiling `⋃ₘ boxIoc m` (injectivity makes the tile-images pairwise disjoint).

On top of it we compute, in the golden field `ℚ[φ]`:

* `volume_branchBox` — each branch is an affine image of a `(p,q)`-rectangle, so
  `volume (branchBox e) = ofReal ((pb e − pa e)·qHeight(src e)/(φ+2))` (via
  `Measure.addHaar_image_linearMap` with the inverse coordinate matrix `bbInv`);
* `volume_awCell_succ` — pushing that through `catProj` (injective on a branch) gives the cell
  measure of `awCell (e+1)`;
* `sum_volume_awCell_succ` — the five cell measures sum to `1` (`∑ (widthₑ·heightₑ) = φ+2`);
* `disjoint_catProj_image_branchBox` — the branch images are pairwise disjoint (via
  `catProj_injOn_awUnion`, injectivity of the covering projection on `R₁ ∪ R₂`), hence the junk cell
  `awCell 0` is null (`volume_awCell_zero`);
* `catAWPartition` — the assembled `MeasurePartition volume (Fin 6)`.
-/

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
imported cat-map measure modules so that `volume : Measure T2` lines up. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_awMeas :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_awMeas :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_awMeas :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## The tiling extension of the per-tile measure identity -/

/-- **The tiling extension.**  If `catProj` is injective on a measurable set `K`, then the
projection preserves the measure: `volume (catProj '' K) = volume K`.  We decompose `K` along the
integer
tiling `⋃ₘ boxIoc m`; injectivity forces the tile-images `catProj '' (K ∩ boxIoc m)` to be pairwise
disjoint (a shared torus point would give two `K`-points with equal projection, hence equal by
`InjOn`, yet lying in two disjoint boxes).  Summing the exact per-tile identity over the tiling on
both sides yields equal `tsum`s. -/
theorem volume_catProj_image_of_injOn {K : Set (Fin 2 → ℝ)} (hK : MeasurableSet K)
    (hinj : Set.InjOn catProj K) :
    (volume : Measure T2) (catProj '' K) = volume K := by
  have hpieces_meas : ∀ m, MeasurableSet (catProj '' (K ∩ boxIoc m)) := fun m =>
    measurableSet_catProj_image_inter_box hK m
  have hdisj_torus :
      Pairwise (Function.onFun Disjoint (fun m : Fin 2 → ℤ => catProj '' (K ∩ boxIoc m))) := by
    intro m m' hmm
    rw [Function.onFun, Set.disjoint_left]
    rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
    have hxy : x = y := hinj hx.1 hy.1 (hxp.trans hyp.symm)
    subst hxy
    exact (Set.disjoint_left.mp (pairwise_disjoint_boxIoc hmm) hx.2) hy.2
  have hcov : catProj '' K = ⋃ m : Fin 2 → ℤ, catProj '' (K ∩ boxIoc m) := by
    rw [← Set.image_iUnion]; congr 1
    rw [← Set.inter_iUnion, iUnion_boxIoc, Set.inter_univ]
  have hdisj_plane :
      Pairwise (Function.onFun Disjoint (fun m : Fin 2 → ℤ => K ∩ boxIoc m)) := by
    intro m m' hmm
    exact (pairwise_disjoint_boxIoc hmm).mono Set.inter_subset_right Set.inter_subset_right
  rw [hcov, measure_iUnion hdisj_torus hpieces_meas]
  simp_rw [volume_catProj_image_inter_box hK]
  rw [← measure_iUnion hdisj_plane (fun m => hK.inter (measurableSet_boxIoc m))]
  congr 1
  rw [← Set.inter_iUnion, iUnion_boxIoc, Set.inter_univ]

/-! ## Measurability of the branches and their projections -/

/-- `pC` is measurable (an explicit linear functional). -/
lemma measurable_pC : Measurable pC := by
  unfold pC
  exact (measurable_const.mul (measurable_pi_apply 0)).add (measurable_pi_apply 1)

/-- `qC` is measurable (an explicit linear functional). -/
lemma measurable_qC : Measurable qC := by
  unfold qC
  exact (measurable_pi_apply 0).sub (measurable_const.mul (measurable_pi_apply 1))

/-- Each branch is measurable (an intersection of two half-open eigencoordinate slabs). -/
lemma measurableSet_branchBox (e : Fin 5) : MeasurableSet (branchBox e) := by
  rw [branchBox, Set.setOf_and]
  exact (measurable_pC measurableSet_Ico).inter (measurable_qC measurableSet_Ico)

/-- Each projected branch is measurable (via the tiling of measurable per-tile images). -/
theorem measurableSet_catProj_image_branchBox (e : Fin 5) :
    MeasurableSet (catProj '' branchBox e) := by
  have hcov : catProj '' branchBox e
      = ⋃ m : Fin 2 → ℤ, catProj '' (branchBox e ∩ boxIoc m) := by
    rw [← Set.image_iUnion]; congr 1
    rw [← Set.inter_iUnion, iUnion_boxIoc, Set.inter_univ]
  rw [hcov]
  exact MeasurableSet.iUnion fun m =>
    measurableSet_catProj_image_inter_box (measurableSet_branchBox e) m

/-! ## The volume of each branch via the inverse coordinate matrix -/

/-- The inverse of the eigen-coordinate matrix `!![φ,1;1,−φ]`.  It sends `(p,q)` to the vector with
`pC = p`, `qC = q`; its determinant is `−1/(φ+2)`. -/
def bbInv : Matrix (Fin 2) (Fin 2) ℝ :=
  !![phiAW / (phiAW + 2), 1 / (phiAW + 2); 1 / (phiAW + 2), -phiAW / (phiAW + 2)]

/-- `φ + 2 ≠ 0`. -/
lemma phiAW_add_two_ne : (phiAW + 2) ≠ 0 := ne_of_gt (by linarith [phiAW_pos])

/-- First coordinate of `bbInv ·ᵥ w`. -/
lemma bbInv_apply_zero (w : Fin 2 → ℝ) :
    (bbInv *ᵥ w) 0 = (phiAW * w 0 + w 1) / (phiAW + 2) := by
  simp only [bbInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val']
  ring

/-- Second coordinate of `bbInv ·ᵥ w`. -/
lemma bbInv_apply_one (w : Fin 2 → ℝ) :
    (bbInv *ᵥ w) 1 = (w 0 - phiAW * w 1) / (phiAW + 2) := by
  simp only [bbInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val']
  ring

/-- The unstable coordinate reads off the first entry of the preimage under `bbInv`. -/
lemma pC_bbInv (w : Fin 2 → ℝ) : pC (bbInv *ᵥ w) = w 0 := by
  have hne := phiAW_add_two_ne
  rw [pC, bbInv_apply_zero, bbInv_apply_one]
  field_simp
  linear_combination (w 0) * phiAW_sq

/-- The stable coordinate reads off the second entry of the preimage under `bbInv`. -/
lemma qC_bbInv (w : Fin 2 → ℝ) : qC (bbInv *ᵥ w) = w 1 := by
  have hne := phiAW_add_two_ne
  rw [qC, bbInv_apply_zero, bbInv_apply_one]
  field_simp
  linear_combination (w 1) * phiAW_sq

/-- `bbInv` inverts the eigen-coordinate map: `bbInv ·ᵥ (pC v, qC v) = v`. -/
lemma bbInv_pC_qC (v : Fin 2 → ℝ) : bbInv *ᵥ ![pC v, qC v] = v := by
  have hne := phiAW_add_two_ne
  have h0 : (bbInv *ᵥ ![pC v, qC v]) 0 = v 0 := by
    rw [bbInv_apply_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pC, qC]
    field_simp
    linear_combination (v 0) * phiAW_sq
  have h1 : (bbInv *ᵥ ![pC v, qC v]) 1 = v 1 := by
    rw [bbInv_apply_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pC, qC]
    field_simp
    linear_combination (v 1) * phiAW_sq
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- **The branch as an affine image of a `(p,q)`-rectangle.** -/
lemma branchBox_eq_image (e : Fin 5) :
    branchBox e = (Matrix.toLin' bbInv) ''
      (Set.univ.pi ![Set.Ico (pa e) (pb e), Set.Ico (0 : ℝ) (qHeight (src e))]) := by
  ext v
  simp only [branchBox, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨![pC v, qC v], ?_, ?_⟩
    · rw [Set.mem_univ_pi]; intro i
      fin_cases i
      · simpa using hp
      · simpa using hq
    · rw [Matrix.toLin'_apply]; exact bbInv_pC_qC v
  · rintro ⟨w, hw, rfl⟩
    rw [Set.mem_univ_pi] at hw
    have h0 := hw 0; have h1 := hw 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [Matrix.toLin'_apply, pC_bbInv, qC_bbInv]
    exact ⟨h0, h1⟩

/-- Each branch's unstable window has nonnegative width. -/
lemma pb_sub_pa_nonneg (e : Fin 5) : 0 ≤ pb e - pa e := by
  fin_cases e <;>
    norm_num [pa, pb] <;>
    nlinarith [one_lt_phiAW, phiAW_lt_two, phiAW_sq]

/-- Each branch's stable height is nonnegative. -/
lemma qHeight_src_nonneg (e : Fin 5) : 0 ≤ qHeight (src e) := by
  fin_cases e <;>
    norm_num [qHeight, src] <;>
    linarith [one_lt_phiAW]

/-- **The volume of a branch.**  `branchBox e` is the image of the `(p,q)`-rectangle
`[pa e, pb e) × [0, qHeight(src e))` under `toLin' bbInv`, whose determinant has absolute value
`1/(φ+2)`, so its `volume` is `(pb e − pa e)·qHeight(src e)/(φ+2)`. -/
lemma volume_branchBox (e : Fin 5) :
    (volume : Measure (Fin 2 → ℝ)) (branchBox e)
      = ENNReal.ofReal ((pb e - pa e) * qHeight (src e) / (phiAW + 2)) := by
  have hne := phiAW_add_two_ne
  have hpos : (0 : ℝ) < phiAW + 2 := by linarith [phiAW_pos]
  have hdet : bbInv.det = -1 / (phiAW + 2) := by
    simp only [bbInv, Matrix.det_fin_two_of]
    field_simp
    linear_combination -phiAW_sq
  have habs : |bbInv.det| = 1 / (phiAW + 2) := by
    rw [hdet, abs_div, abs_neg, abs_one, abs_of_pos hpos]
  have hbox : (volume : Measure (Fin 2 → ℝ))
      (Set.univ.pi ![Set.Ico (pa e) (pb e), Set.Ico (0 : ℝ) (qHeight (src e))])
      = ENNReal.ofReal (pb e - pa e) * ENNReal.ofReal (qHeight (src e)) := by
    rw [volume_pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.volume_Ico]
    rw [show qHeight (src e) - 0 = qHeight (src e) from by ring]
  rw [branchBox_eq_image, Measure.addHaar_image_linearMap, LinearMap.det_toLin', habs, hbox,
    ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg zero_le_one hpos.le),
    ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg zero_le_one hpos.le) (pb_sub_pa_nonneg e))]
  congr 1
  ring

/-! ## The cell measures -/

/-- **The measure of a branch cell.**  Pushing `volume_branchBox` through the covering projection
(injective on the branch, by `catProj_injOn_branchBox`) via the tiling extension. -/
theorem volume_awCell_succ (e : Fin 5) :
    (volume : Measure T2) (awCell e.succ)
      = ENNReal.ofReal ((pb e - pa e) * qHeight (src e) / (phiAW + 2)) := by
  rw [awCell_succ,
    volume_catProj_image_of_injOn (measurableSet_branchBox e) (catProj_injOn_branchBox e),
    volume_branchBox e]

/-- **The five branch cell measures sum to `1`.**  In the golden field the numerators
`∑ (pb e − pa e)·qHeight(src e) = 2φ² − φ = φ + 2`, cancelling the common denominator `φ + 2`. -/
theorem sum_volume_awCell_succ :
    ∑ e : Fin 5, (volume : Measure T2) (awCell e.succ) = 1 := by
  have hpos : (0 : ℝ) < phiAW + 2 := by linarith [phiAW_pos]
  simp_rw [volume_awCell_succ]
  rw [← ENNReal.ofReal_sum_of_nonneg fun e _ => by
    exact div_nonneg (mul_nonneg (pb_sub_pa_nonneg e) (qHeight_src_nonneg e)) hpos.le]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
  congr 1
  simp only [Fin.sum_univ_five, pa, pb, qHeight, src, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four]
  field_simp
  nlinarith [phiAW_sq]

/-! ## Pairwise disjointness of the branches and the branch cells -/

/-- The five branch windows `[pa e, pb e)` are pairwise disjoint (they are the consecutive
subintervals `[0,φ−1),[φ−1,1),[1,φ),[φ,2),[2,φ²)` of `[0,φ²)`), so the branches are pairwise
disjoint in the plane. -/
lemma branchBox_disjoint {e e' : Fin 5} (h : e ≠ e') :
    Disjoint (branchBox e) (branchBox e') := by
  rw [Set.disjoint_left]
  rintro v ⟨hvp, _⟩ ⟨hvp', _⟩
  rw [Set.mem_Ico] at hvp hvp'
  obtain ⟨hva, hvb⟩ := hvp
  obtain ⟨hva', hvb'⟩ := hvp'
  fin_cases e <;> fin_cases e' <;>
    first
    | exact absurd rfl h
    | (norm_num [pa, pb] at hva hvb hva' hvb';
       nlinarith [one_lt_phiAW, phiAW_lt_two, phiAW_sq, hva, hvb, hva', hvb'])

/-- **The branch cells are pairwise disjoint** on the torus.  Two lifts with equal projection lie in
`R₁ ∪ R₂`, on which `catProj` is injective, so they coincide; but distinct branches are disjoint in
the plane. -/
theorem disjoint_catProj_image_branchBox {e e' : Fin 5} (h : e ≠ e') :
    Disjoint (catProj '' branchBox e) (catProj '' branchBox e') := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
  have hxu : x ∈ awBox 0 ∪ awBox 1 :=
    awBox_subset_awUnion (src e) (branchBox_subset_awBox_src e hx)
  have hyu : y ∈ awBox 0 ∪ awBox 1 :=
    awBox_subset_awUnion (src e') (branchBox_subset_awBox_src e' hy)
  have hxy : x = y := catProj_injOn_awUnion hxu hyu (hxp.trans hyp.symm)
  subst hxy
  exact (Set.disjoint_left.mp (branchBox_disjoint h) hx) hy

/-! ## The junk cell is null and the partition -/

/-- The five branch cells fill the torus up to the null junk cell: their union has full measure. -/
theorem volume_iUnion_catProj_image_branchBox :
    (volume : Measure T2) (⋃ e, catProj '' branchBox e) = 1 := by
  rw [measure_iUnion (fun e e' h => disjoint_catProj_image_branchBox h)
    (fun e => measurableSet_catProj_image_branchBox e), tsum_fintype]
  simp_rw [← awCell_succ]
  exact sum_volume_awCell_succ

/-- **The junk cell is null.**  It is the complement of the full-measure union of branch cells. -/
theorem volume_awCell_zero : (volume : Measure T2) (awCell 0) = 0 := by
  rw [awCell_zero]
  have hmU : MeasurableSet (⋃ e, catProj '' branchBox e) :=
    MeasurableSet.iUnion fun e => measurableSet_catProj_image_branchBox e
  rw [measure_compl hmU (measure_ne_top _ _), measure_univ,
    volume_iUnion_catProj_image_branchBox, tsub_self]

/-- **The Adler–Weiss measure partition.**  The six cells `awCell` (the null junk complement plus
the five projected branches) form a genuine finite `MeasurePartition` of `(T2, volume)`. -/
def catAWPartition : Entropy.MeasurePartition (volume : Measure T2) (Fin 6) where
  cells := awCell
  measurable := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [awCell_zero]
      exact (MeasurableSet.iUnion fun e => measurableSet_catProj_image_branchBox e).compl
    · intro e; rw [awCell_succ]; exact measurableSet_catProj_image_branchBox e
  aedisjoint := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ e =>
        rw [Function.onFun, awCell_zero, awCell_succ]
        refine Disjoint.aedisjoint ?_
        rw [Set.disjoint_left]
        intro p hp hp2
        exact hp (Set.mem_iUnion.2 ⟨e, hp2⟩)
    | succ e =>
      induction j using Fin.cases with
      | zero =>
        rw [Function.onFun, awCell_zero, awCell_succ]
        refine Disjoint.aedisjoint ?_
        rw [Set.disjoint_right]
        intro p hp hp2
        exact hp (Set.mem_iUnion.2 ⟨e, hp2⟩)
      | succ e' =>
        rw [Function.onFun, awCell_succ, awCell_succ]
        refine Disjoint.aedisjoint (disjoint_catProj_image_branchBox ?_)
        exact fun hee => hij (by rw [hee])
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro p
    by_cases hp : p ∈ ⋃ e, catProj '' branchBox e
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hp
      exact Set.mem_iUnion.2 ⟨e.succ, by rw [awCell_succ]; exact he⟩
    · exact Set.mem_iUnion.2 ⟨0, by rw [awCell_zero]; exact hp⟩

end ErgodicTheory.CatMapToral

end
