/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapAWContraction
import ErgodicTheory.Examples.CatMapAdlerWeissCount
import ErgodicTheory.Entropy.LowerBoundGlue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-!
# Strict positivity of the coarse Adler–Weiss partition entropy for the cat map

This module proves the first **positive** Kolmogorov–Sinai lower bound for a *coarse*
(non-generating) two-cell partition of the Arnold cat map `catTorus`.  The coarse partition merges
the five Adler–Weiss branch cells by the source rectangle `src`, leaving only the two golden
rectangles `R₁, R₂` (index `Fin 2`), so it is a genuine *factor* of the Adler–Weiss Markov
partition.  Its symbolic factor is the merged golden subshift whose topological entropy lies in
`[log λ − log 2, log 2]`; here we pin down the lower bound.

The lower bound is proved on the junk-absorbing partition `coarseAWPartitionJunk`, which is provably
cell-equal to `coarseAWPartition` (empty-junk exact tiling); the bridge and the single-object
bracket live in `CatMapTowerPositivity` (`coarseAWPartitionJunk_cells_eq`,
`ksEntropy_mapCoarseSymb_bracket`, `ksEntropy_twoSymbolSuspFlow_bracket`).

## Strategy

The substantive new estimate is the **fine forward-cylinder volume bound**: for an admissible word
`g : Fin (n+1) → Fin 5`, the forward cylinder
`⋂ₖ catTorus⁻ᵏ (catProj '' branchBox (g k))` has `volume ≤ 2(φ−1)φ/(φ+2) · (1/λ)ⁿ`.  In
eigencoordinates a fine cylinder lifts to an affine sub-box of `branchBox (g 0)` whose *unstable*
`pC`-width contracts by `λ⁻ⁿ` (each further symbol pulls the unstable window back through one more
expanding branch, `awRep_step`), while the *stable* `qC`-height stays `≤ φ`.  The image measure of
such a box is `width · height / (φ+2)` (the `bbInv` affine toolkit of
`CatMapAdlerWeissMeasure`).

A coarse `n`-join atom is the union of the fine cylinders over compatible admissible words, and the
**transfer-matrix fibre count** of such words is `≤ 5 · 2ⁿ` (admissibility forces each interior
symbol into `≤ 2` choices; the `(src, tgt, bit)` triple is injective on `Fin 5`).  Multiplying the
per-cylinder bound by the count gives a coarse-atom bound `≤ C · (2/λ)ⁿ`, which the entropy
lower-bound glue converts into `log λ − log 2 ≤ ksEntropyPartition`, strictly positive because
`λ = (3+√5)/2 > 2`.

## Main results

* `ErgodicTheory.CatMapToral.coarseAWPartitionJunk` — the two-cell coarse partition.
* `ErgodicTheory.CatMapToral.volume_fineCyl_le` — the fine forward-cylinder volume bound.
* `ErgodicTheory.CatMapToral.coarseAW_ksEntropyPartition_ge` —
  `log λ − log 2 ≤ ksEntropyPartition`.
* `ErgodicTheory.CatMapToral.coarseAW_ksEntropyPartition_pos` — strict positivity.
-/

open MeasureTheory Matrix Function Filter Topology
open scoped ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
imported cat-map measure modules so that `volume : Measure T2` lines up. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_coarsePos :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_coarsePos :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_coarsePos :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.Entropy

variable {α : Type*} [MeasurableSpace α]

/-- **Partition-level entropy lower bound from geometric atom-measure decay.** If every atom of the
`n`-fold iterated join of a finite measurable partition `P` has measure at most `C · θⁿ`
(`0 < θ`, `0 < C`), then `-log θ ≤ ksEntropyPartition hT P`. This is the partition-relative core of
`ksEntropy_ge_of_atom_measure_le` (which lifts it further to the system entropy). -/
theorem ksEntropyPartition_ge_of_atom_measure_le {ι : Type*} [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C)
    (hatom : ∀ n (f : Fin n → ι),
      μ (ksJoinCells P.cells T n f) ≤ ENNReal.ofReal (C * θ ^ n)) :
    -Real.log θ ≤ ksEntropyPartition hT P := by
  refine ksEntropyPartition_ge_of_seq_bound hT P (L := -Real.log θ) (c := Real.log C) ?_
  intro n
  have hθn : (0 : ℝ) < θ ^ n := pow_pos hθ n
  have hε : (0 : ℝ) < C * θ ^ n := mul_pos hC hθn
  have hle : ∀ f : Fin n → ι, (μ ((ksJoin hT P n).cells f)).toReal ≤ C * θ ^ n := fun f =>
    ENNReal.toReal_le_of_le_ofReal hε.le (hatom n f)
  have hlb : ksEntropySeq hT P n ≥ -Real.log (C * θ ^ n) :=
    entropy_ge_neg_log_of_forall_le (ksJoin hT P n) hle
  have hrw : -Real.log (C * θ ^ n) = (n : ℝ) * -Real.log θ - Real.log C := by
    rw [Real.log_mul hC.ne' hθn.ne', Real.log_pow]; ring
  rw [hrw] at hlb
  exact hlb

end ErgodicTheory.Entropy

namespace ErgodicTheory.CatMapToral

open ErgodicTheory.Entropy

/-! ## The closed eigencoordinate box and its measure -/

/-- A closed eigencoordinate box: unstable coordinate in `[c, d]`, stable coordinate in `[a, b]`. -/
def pqIcc (c d a b : ℝ) : Set (Fin 2 → ℝ) :=
  {v | pC v ∈ Set.Icc c d ∧ qC v ∈ Set.Icc a b}

/-- **The closed box as an affine image.** `pqIcc c d a b` is the image of the coordinate box
`[c,d] × [a,b]` under `toLin' bbInv`. -/
lemma pqIcc_eq_image (c d a b : ℝ) :
    pqIcc c d a b
      = (Matrix.toLin' bbInv) '' (Set.univ.pi ![Set.Icc c d, Set.Icc a b]) := by
  ext v
  simp only [pqIcc, Set.mem_setOf_eq, Set.mem_image]
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

/-- **The closed box is compact** (a continuous linear image of a compact box). -/
lemma isCompact_pqIcc (c d a b : ℝ) : IsCompact (pqIcc c d a b) := by
  rw [pqIcc_eq_image]
  refine IsCompact.image ?_ (LinearMap.continuous_of_finiteDimensional _)
  refine isCompact_univ_pi ?_
  intro i
  fin_cases i <;> exact isCompact_Icc

/-- **The measure of the closed box.** For `c ≤ d` and `a ≤ b`,
`volume (pqIcc c d a b) = (d-c)(b-a)/(φ+2)`, since `|det bbInv| = 1/(φ+2)`. -/
lemma volume_pqIcc (c d a b : ℝ) (hcd : c ≤ d) :
    (volume : Measure (Fin 2 → ℝ)) (pqIcc c d a b)
      = ENNReal.ofReal ((d - c) * (b - a) / (phiAW + 2)) := by
  have hne := phiAW_add_two_ne
  have hpos : (0 : ℝ) < phiAW + 2 := by linarith [phiAW_pos]
  have hdet : bbInv.det = -1 / (phiAW + 2) := by
    simp only [bbInv, Matrix.det_fin_two_of]
    field_simp
    linear_combination -phiAW_sq
  have habs : |bbInv.det| = 1 / (phiAW + 2) := by
    rw [hdet, abs_div, abs_neg, abs_one, abs_of_pos hpos]
  have hbox : (volume : Measure (Fin 2 → ℝ))
      (Set.univ.pi ![Set.Icc c d, Set.Icc a b])
      = ENNReal.ofReal (d - c) * ENNReal.ofReal (b - a) := by
    rw [volume_pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.volume_Icc]
  rw [pqIcc_eq_image, Measure.addHaar_image_linearMap, LinearMap.det_toLin', habs, hbox,
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ d - c),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (phiAW + 2))]
  congr 1
  ring

/-! ## The two golden rectangles tile into the five branches -/

/-- The image of a golden rectangle is the union of its source branch cells' images:
`awBox i = ⋃_{src e = i} branchBox e`.  The five unstable windows tile the two boxes. -/
lemma awBox_eq_iUnion_src (i : Fin 2) :
    awBox i = ⋃ e : Fin 5, ⋃ (_ : src e = i), branchBox e := by
  apply Set.Subset.antisymm
  · intro v hv
    fin_cases i
    · -- R₁: pC ∈ [0,φ) splits into [0,φ−1) ∪ [φ−1,1) ∪ [1,φ)
      simp only [awBox, Set.mem_setOf_eq, Set.mem_Ico] at hv
      obtain ⟨⟨hp0, hp1⟩, hq0, hq1⟩ := hv
      rcases lt_or_ge (pC v) (phiAW - 1) with h | h
      · refine Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2 ⟨rfl, ?_⟩⟩
        norm_num [branchBox, Set.mem_setOf_eq, Set.mem_Ico, pa, pb, qHeight, src,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
          Matrix.head_cons]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
      · rcases lt_or_ge (pC v) 1 with h' | h'
        · refine Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2 ⟨rfl, ?_⟩⟩
          norm_num [branchBox, Set.mem_setOf_eq, Set.mem_Ico, pa, pb, qHeight, src,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
          Matrix.head_cons]
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
        · refine Set.mem_iUnion.2 ⟨2, Set.mem_iUnion.2 ⟨rfl, ?_⟩⟩
          norm_num [branchBox, Set.mem_setOf_eq, Set.mem_Ico, pa, pb, qHeight, src,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
          Matrix.head_cons]
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · -- R₂: pC ∈ [φ,φ²) splits into [φ,2) ∪ [2,φ²)
      simp only [awBox, Set.mem_setOf_eq, Set.mem_Ico] at hv
      obtain ⟨⟨hp0, hp1⟩, hq0, hq1⟩ := hv
      rcases lt_or_ge (pC v) 2 with h | h
      · refine Set.mem_iUnion.2 ⟨3, Set.mem_iUnion.2 ⟨rfl, ?_⟩⟩
        norm_num [branchBox, Set.mem_setOf_eq, Set.mem_Ico, pa, pb, qHeight, src,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
          Matrix.head_cons]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
      · refine Set.mem_iUnion.2 ⟨4, Set.mem_iUnion.2 ⟨rfl, ?_⟩⟩
        norm_num [branchBox, Set.mem_setOf_eq, Set.mem_Ico, pa, pb, qHeight, src,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
          Matrix.head_cons]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · refine Set.iUnion_subset fun e => Set.iUnion_subset fun he => ?_
    rw [← he]; exact branchBox_subset_awBox_src e

/-- Each projected golden rectangle is measurable (a finite union of measurable branch images). -/
lemma measurableSet_catProj_image_awBox_junk (i : Fin 2) :
    MeasurableSet (catProj '' awBox i) := by
  rw [awBox_eq_iUnion_src, Set.image_iUnion]
  refine MeasurableSet.iUnion fun e => ?_
  rw [Set.image_iUnion]
  exact MeasurableSet.iUnion fun _ => measurableSet_catProj_image_branchBox e

/-! ## The coarse two-cell partition -/

/-- The **coarse Adler–Weiss partition** on `T2`, merging the five branch cells by source rectangle
into the two golden rectangles.  Cell `1` is the projected rectangle `R₂ = catProj '' awBox 1`; cell
`0` is its complement (`= catProj '' awBox 0` together with the null junk cell). -/
def coarseCell : Fin 2 → Set T2
  | 0 => (catProj '' awBox 1)ᶜ
  | 1 => catProj '' awBox 1

/-- **The coarse Adler–Weiss measure partition.** -/
def coarseAWPartitionJunk : Entropy.MeasurePartition (volume : Measure T2) (Fin 2) where
  cells := coarseCell
  measurable := by
    intro i
    fin_cases i
    · exact (measurableSet_catProj_image_awBox_junk 1).compl
    · exact measurableSet_catProj_image_awBox_junk 1
  aedisjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (refine Disjoint.aedisjoint ?_
         simp only [coarseCell]
         first
         | exact disjoint_compl_left
         | exact disjoint_compl_right)
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro p
    by_cases hp : p ∈ catProj '' awBox 1
    · exact Set.mem_iUnion.2 ⟨1, hp⟩
    · exact Set.mem_iUnion.2 ⟨0, hp⟩

/-! ## Fine forward cylinders -/

/-- The **fine forward cylinder** of a symbol word `g : Fin (n+1) → Fin 5`:
`⋂ₖ catTorus⁻ᵏ (catProj '' branchBox (g k))`. -/
def fineCyl {n : ℕ} (g : Fin (n + 1) → Fin 5) : Set T2 :=
  ⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' branchBox (g k))

/-- **The lift chain of a fine-cylinder point.** For an admissible word `g` and a point `x` of the
fine cylinder, there is a chain of branch representatives `r k ∈ branchBox (g k)` projecting to the
orbit `catTorus^[k] x`, with each step the affine branch map `r (k+1) = catℝ ·ᵥ r k − off (g k)`
(from `awRep_step`, using injectivity of the covering projection on each golden rectangle). -/
lemma exists_chain {n : ℕ} (g : Fin (n + 1) → Fin 5) (hg : Adm g) {x : T2}
    (hx : ∀ k : Fin (n + 1), catTorus^[(k : ℕ)] x ∈ catProj '' branchBox (g k)) :
    ∃ r : Fin (n + 1) → (Fin 2 → ℝ),
      (∀ k, r k ∈ branchBox (g k)) ∧ (∀ k, catProj (r k) = catTorus^[(k : ℕ)] x) ∧
      (∀ k : Fin n, r k.succ = catℝ *ᵥ r k.castSucc - off (g k.castSucc)) := by
  choose r hmem hproj using hx
  refine ⟨r, hmem, hproj, fun k => ?_⟩
  refine awRep_step (hg k) (hmem k.castSucc) (hmem k.succ) ?_
  rw [hproj k.succ, hproj k.castSucc,
    show (k.succ : ℕ) = (k.castSucc : ℕ) + 1 by rw [Fin.val_succ, Fin.val_castSucc],
    Function.iterate_succ_apply']

/-- **Covariance of two lift chains.** Two lift chains along the same admissible word have a
difference that is exactly transported by the matrix power: `r k − r' k = catℝᵏ ·ᵥ (r 0 − r' 0)`.
The per-step affine offsets `off (g k)` cancel in the difference. -/
lemma chain_covariant {n : ℕ} (g : Fin (n + 1) → Fin 5)
    (r r' : Fin (n + 1) → (Fin 2 → ℝ))
    (hs : ∀ k : Fin n, r k.succ = catℝ *ᵥ r k.castSucc - off (g k.castSucc))
    (hs' : ∀ k : Fin n, r' k.succ = catℝ *ᵥ r' k.castSucc - off (g k.castSucc)) :
    ∀ k : Fin (n + 1), r k - r' k = (catℝ ^ (k : ℕ)) *ᵥ (r 0 - r' 0) := by
  intro k
  induction k using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [hs j, hs' j,
      show catℝ *ᵥ r j.castSucc - off (g j.castSucc)
          - (catℝ *ᵥ r' j.castSucc - off (g j.castSucc))
        = catℝ *ᵥ (r j.castSucc - r' j.castSucc) from by rw [mulVec_sub]; abel,
      ih, mulVec_mulVec, ← pow_succ', Fin.val_succ, Fin.val_castSucc]

/-- **The fine forward-cylinder volume bound.** For an admissible word `g : Fin (n+1) → Fin 5`, the
fine forward cylinder has `volume ≤ 2(φ−1)φ/(φ+2) · (1/λ)ⁿ`.  In eigencoordinates the cylinder lifts
into a closed box of `pC`-width `≤ 2(φ−1)λ⁻ⁿ` (unstable contraction) and `qC`-height `≤ φ`; the
`bbInv` affine measure toolkit gives the image bound. -/
lemma volume_fineCyl_le {n : ℕ} (g : Fin (n + 1) → Fin 5) (hg : Adm g) :
    (volume : Measure T2) (fineCyl g)
      ≤ ENNReal.ofReal (2 * (phiAW - 1) * phiAW / (phiAW + 2) * (1 / lam) ^ n) := by
  have hp := phiAW_pos
  have ho := one_lt_phiAW
  have hlamn : (0 : ℝ) < lam ^ n := pow_pos lam_pos n
  have hlamne : lam ^ n ≠ 0 := hlamn.ne'
  have hphi2 : (0 : ℝ) < phiAW + 2 := by linarith
  rcases Set.eq_empty_or_nonempty (fineCyl g) with hE | ⟨x0, hx0⟩
  · rw [hE]; simp
  · obtain ⟨r0, hr0mem, hr0proj, hr0step⟩ :=
      exists_chain g hg (fun k => Set.mem_iInter.1 hx0 k)
    set W : ℝ := (pb (g (Fin.last n)) - pa (g (Fin.last n))) / lam ^ n with hW
    set H : ℝ := qHeight (src (g 0)) with hH
    have hWnn : 0 ≤ W := div_nonneg (pb_sub_pa_nonneg _) hlamn.le
    have hWeq : lam ^ n * W = pb (g (Fin.last n)) - pa (g (Fin.last n)) := by
      rw [hW, mul_comm, div_mul_cancel₀ _ hlamne]
    have hsub : fineCyl g ⊆ catProj '' pqIcc (pC (r0 0) - W) (pC (r0 0) + W) 0 H := by
      intro x hx
      obtain ⟨r, hrmem, hrproj, hrstep⟩ :=
        exists_chain g hg (fun k => Set.mem_iInter.1 hx k)
      refine ⟨r 0, ?_, by rw [hrproj 0]; simp⟩
      rw [pqIcc, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · have hcov := chain_covariant g r r0 hrstep hr0step (Fin.last n)
        rw [Fin.val_last] at hcov
        have hpc : pC (r (Fin.last n)) - pC (r0 (Fin.last n))
            = lam ^ n * (pC (r 0) - pC (r0 0)) := by
          have h := congrArg pC hcov
          rw [pC_sub, pC_pow_mulVec, pC_sub] at h
          exact h
        have hrl := hrmem (Fin.last n)
        have hr0l := hr0mem (Fin.last n)
        simp only [branchBox, Set.mem_setOf_eq, Set.mem_Ico] at hrl hr0l
        have hW1 : pC (r 0) - pC (r0 0) < W := by
          refine lt_of_mul_lt_mul_left ?_ hlamn.le
          calc lam ^ n * (pC (r 0) - pC (r0 0)) = pC (r (Fin.last n)) - pC (r0 (Fin.last n)) :=
                hpc.symm
            _ < pb (g (Fin.last n)) - pa (g (Fin.last n)) := by linarith [hrl.1.2, hr0l.1.1]
            _ = lam ^ n * W := hWeq.symm
        have hW2 : -W < pC (r 0) - pC (r0 0) := by
          refine lt_of_mul_lt_mul_left ?_ hlamn.le
          calc lam ^ n * (-W) = -(pb (g (Fin.last n)) - pa (g (Fin.last n))) := by
                rw [mul_neg, hWeq]
            _ < pC (r (Fin.last n)) - pC (r0 (Fin.last n)) := by linarith [hrl.1.1, hr0l.1.2]
            _ = lam ^ n * (pC (r 0) - pC (r0 0)) := hpc
        rw [Set.mem_Icc]; constructor <;> linarith [hW1, hW2]
      · have hr0b := hrmem 0
        simp only [branchBox, Set.mem_setOf_eq, Set.mem_Ico] at hr0b
        rw [Set.mem_Icc, hH]
        exact ⟨hr0b.2.1, hr0b.2.2.le⟩
    calc (volume : Measure T2) (fineCyl g)
        ≤ volume (catProj '' pqIcc (pC (r0 0) - W) (pC (r0 0) + W) 0 H) := measure_mono hsub
      _ ≤ volume (pqIcc (pC (r0 0) - W) (pC (r0 0) + W) 0 H) :=
          catProj_image_volume_le _ (isCompact_pqIcc _ _ _ _)
      _ = ENNReal.ofReal (2 * W * H / (phiAW + 2)) := by
          rw [volume_pqIcc _ _ _ _ (by linarith : pC (r0 0) - W ≤ pC (r0 0) + W)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (2 * (phiAW - 1) * phiAW / (phiAW + 2) * (1 / lam) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have hqh : H ≤ phiAW := qHeight_src_le _
          have hHnn : 0 ≤ H := qHeight_src_nonneg _
          have hpwn : pb (g (Fin.last n)) - pa (g (Fin.last n)) ≤ phiAW - 1 := pWidth_le _
          have hone : (1 / lam) ^ n = 1 / lam ^ n := by rw [div_pow, one_pow]
          have hWval : W = (pb (g (Fin.last n)) - pa (g (Fin.last n))) * (1 / lam ^ n) := by
            rw [hW]; ring
          rw [hone, hWval,
            show 2 * ((pb (g (Fin.last n)) - pa (g (Fin.last n))) * (1 / lam ^ n)) * H
                / (phiAW + 2)
              = (2 * (pb (g (Fin.last n)) - pa (g (Fin.last n))) * H / (phiAW + 2))
                * (1 / lam ^ n) from by ring,
            show 2 * (phiAW - 1) * phiAW / (phiAW + 2) * (1 / lam ^ n)
              = (2 * (phiAW - 1) * phiAW / (phiAW + 2)) * (1 / lam ^ n) from by ring]
          refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (one_div_pos.mpr hlamn))
          rw [div_le_div_iff_of_pos_right hphi2]
          nlinarith [mul_le_mul hpwn hqh hHnn (show (0 : ℝ) ≤ phiAW - 1 by linarith)]

/-! ## Forbidden fine cylinders are null -/

/-- **Non-admissible fine cylinders are null.** A word making a forbidden Markov transition has an
empty fine cylinder (the two-step cylinder `awCell e.succ ∩ catTorus⁻¹ (awCell e'.succ)` is empty
when `tgt e ≠ src e'`, by `awCell_succ_inter_preimage_empty`). -/
lemma fineCyl_null_of_not_adm {n : ℕ} (g : Fin (n + 1) → Fin 5) (hg : ¬ Adm g) :
    (volume : Measure T2) (fineCyl g) = 0 := by
  rw [Adm, not_forall] at hg
  obtain ⟨i, hi⟩ := hg
  have hkey := awCell_succ_inter_preimage_empty hi
  have hsub : fineCyl g ⊆ catTorus^[((i.castSucc : Fin (n + 1)) : ℕ)] ⁻¹'
      (awCell (g i.castSucc).succ ∩ catTorus ⁻¹' awCell (g i.succ).succ) := by
    intro x hx
    rw [fineCyl, Set.mem_iInter] at hx
    rw [Set.mem_preimage, Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · have h1 := hx i.castSucc
      rwa [Set.mem_preimage, ← awCell_succ] at h1
    · have h2 := hx i.succ
      rw [Set.mem_preimage, ← awCell_succ,
        show (i.succ : ℕ) = ((i.castSucc : Fin (n + 1)) : ℕ) + 1 from by
          rw [Fin.val_succ, Fin.val_castSucc],
        Function.iterate_succ_apply'] at h2
      rw [Set.mem_preimage]
      exact h2
  rw [hkey, Set.preimage_empty, Set.subset_empty_iff] at hsub
  rw [hsub, measure_empty]

/-! ## The transfer-matrix fibre count -/

/-- A distinguishing bit for the two branches with `(src, tgt) = (0,0)`: `bit e2 = 1`, all others
`0`.  The triple `(src, tgt, bit)` is injective on `Fin 5`. -/
def bit : Fin 5 → Fin 2 := ![0, 0, 1, 0, 0]

/-- The triple `(src, tgt, bit)` separates the five branches. -/
lemma srcTgtBit_inj : ∀ e e' : Fin 5,
    src e = src e' → tgt e = tgt e' → bit e = bit e' → e = e' := by
  decide

/-- **The transfer-matrix fibre count.** For a fixed coarse pattern `t`, the number of admissible
words `g` with `src ∘ g = t` is at most `2ⁿ · 5`: admissibility pins `tgt (g k)` to `t (k+1)`, so
`(src, tgt, bit)` recovers each interior symbol from one bit, while the last symbol gives a `5`. -/
lemma compat_card_le {n : ℕ} (t : Fin (n + 1) → Fin 2) :
    (Finset.univ.filter
        (fun g : Fin (n + 1) → Fin 5 => (∀ k, src (g k) = t k) ∧ Adm g)).card ≤ 2 ^ n * 5 := by
  have h1 : Fintype.card (Fin n → Fin 2) = 2 ^ n := by rw [Fintype.card_pi]; simp
  refine le_trans (Finset.card_le_card_of_injOn
    (fun g => (fun j : Fin n => bit (g j.castSucc), g (Fin.last n)))
    (fun _ _ => Finset.mem_univ _) ?_) ?_
  · intro g hg g' hg' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg hg'
    obtain ⟨hgsrc, hgadm⟩ := hg
    obtain ⟨hg'src, hg'adm⟩ := hg'
    have hbit : ∀ j : Fin n, bit (g j.castSucc) = bit (g' j.castSucc) := fun j =>
      congrFun (congrArg Prod.fst heq) j
    have hlast : g (Fin.last n) = g' (Fin.last n) := congrArg Prod.snd heq
    funext k
    induction k using Fin.lastCases with
    | last => exact hlast
    | cast j =>
      refine srcTgtBit_inj _ _ ?_ ?_ (hbit j)
      · rw [hgsrc, hg'src]
      · rw [hgadm j, hg'adm j, hgsrc, hg'src]
  · rw [Finset.card_univ, Fintype.card_prod, h1, Fintype.card_fin]

/-! ## The coarse cell sits in its rectangle up to the null junk -/

/-- Each coarse cell sits inside the projected rectangle together with the null junk cell. -/
lemma coarseCell_sub (i : Fin 2) : coarseCell i ⊆ catProj '' awBox i ∪ awCell 0 := by
  fin_cases i
  · intro x hx
    by_cases hu : x ∈ ⋃ e, catProj '' branchBox e
    · obtain ⟨e, he⟩ := Set.mem_iUnion.1 hu
      have h01 : catProj '' branchBox e ⊆ catProj '' awBox 0 ∪ catProj '' awBox 1 := by
        rw [← Set.image_union]
        exact Set.image_mono
          ((branchBox_subset_awBox_src e).trans (awBox_subset_awUnion (src e)))
      rcases h01 he with h | h
      · exact Or.inl h
      · exact absurd h hx
    · exact Or.inr (by rw [awCell_zero]; exact hu)
  · exact fun x hx => Or.inl hx

/-! ## The clean atom measure bound -/

/-- **The clean-atom measure bound.** The clean coarse `n`-join atom (using the exact projected
rectangles) has measure at most `5 · 2(φ−1)φ/(φ+2) · (2/λ)ⁿ`: it is the union of the fine cylinders
over compatible words, whose admissible count is `≤ 2ⁿ·5` and whose individual measures are
`≤ 2(φ−1)φ/(φ+2)·(1/λ)ⁿ`. -/
lemma volume_cleanAtom_le {n : ℕ} (t : Fin (n + 1) → Fin 2) :
    (volume : Measure T2) (⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' awBox (t k)))
      ≤ ENNReal.ofReal
          (5 * (2 * (phiAW - 1) * phiAW / (phiAW + 2)) * (2 / lam) ^ n) := by
  set S := Finset.univ.filter (fun g : Fin (n + 1) → Fin 5 => ∀ k, src (g k) = t k) with hS
  have hcover : (⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' awBox (t k)))
      ⊆ ⋃ g ∈ S, fineCyl g := by
    intro x hx
    rw [Set.mem_iInter] at hx
    have hchoice : ∀ k, ∃ e : Fin 5, src e = t k ∧
        catTorus^[(k : ℕ)] x ∈ catProj '' branchBox e := by
      intro k
      have hxk := hx k
      rw [Set.mem_preimage, awBox_eq_iUnion_src] at hxk
      simp only [Set.image_iUnion, Set.mem_iUnion] at hxk
      obtain ⟨e, he_src, hmem⟩ := hxk
      exact ⟨e, he_src, hmem⟩
    choose g hgsrc hgmem using hchoice
    refine Set.mem_iUnion₂.2 ⟨g, ?_, Set.mem_iInter.2 (fun k => hgmem k)⟩
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hgsrc⟩
  have hcardle : (S.filter Adm).card ≤ 2 ^ n * 5 := by
    rw [hS, Finset.filter_filter]
    exact compat_card_le t
  have hBcnn : (0 : ℝ) ≤ 2 * (phiAW - 1) * phiAW / (phiAW + 2) := by
    apply div_nonneg
    · nlinarith [phiAW_pos, one_lt_phiAW]
    · linarith [phiAW_pos]
  have htnn : (0 : ℝ) ≤ (1 / lam) ^ n := pow_nonneg (le_of_lt (one_div_pos.mpr lam_pos)) n
  calc (volume : Measure T2)
        (⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' awBox (t k)))
      ≤ volume (⋃ g ∈ S, fineCyl g) := measure_mono hcover
    _ ≤ ∑ g ∈ S, volume (fineCyl g) := measure_biUnion_finset_le S _
    _ ≤ ∑ g ∈ S, (if Adm g then
          ENNReal.ofReal (2 * (phiAW - 1) * phiAW / (phiAW + 2) * (1 / lam) ^ n) else 0) := by
        refine Finset.sum_le_sum fun g _ => ?_
        by_cases hadm : Adm g
        · rw [if_pos hadm]; exact volume_fineCyl_le g hadm
        · rw [if_neg hadm]; exact le_of_eq (fineCyl_null_of_not_adm g hadm)
    _ = ((S.filter Adm).card : ℝ≥0∞)
          * ENNReal.ofReal (2 * (phiAW - 1) * phiAW / (phiAW + 2) * (1 / lam) ^ n) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ n * 5 : ℕ) : ℝ≥0∞)
          * ENNReal.ofReal (2 * (phiAW - 1) * phiAW / (phiAW + 2) * (1 / lam) ^ n) := by
        exact mul_le_mul' (by exact_mod_cast hcardle) le_rfl
    _ = ENNReal.ofReal (((2 ^ n * 5 : ℕ) : ℝ)
          * (2 * (phiAW - 1) * phiAW / (phiAW + 2) * (1 / lam) ^ n)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = ENNReal.ofReal (5 * (2 * (phiAW - 1) * phiAW / (phiAW + 2)) * (2 / lam) ^ n) := by
        congr 1
        push_cast
        rw [div_pow, one_pow, div_pow]
        ring

/-! ## The coarse atom measure bound and the entropy lower bound -/

/-- The positive constant `C = 5(φ−1)φλ/(φ+2)` of the coarse-atom bound. -/
def coarseC : ℝ := 5 * (phiAW - 1) * phiAW * lam / (phiAW + 2)

lemma coarseC_pos : 0 < coarseC := by
  rw [coarseC]
  apply div_pos
  · have h1 : 0 < phiAW - 1 := by linarith [one_lt_phiAW]
    have := phiAW_pos; have := lam_pos
    positivity
  · linarith [phiAW_pos]

/-- `1 ≤ C`, needed for the trivial `n = 0` atom. -/
lemma one_le_coarseC : 1 ≤ coarseC := by
  rw [coarseC, le_div_iff₀ (by linarith [phiAW_pos] : (0 : ℝ) < phiAW + 2)]
  have hsq := phiAW_sq
  rw [lam_eq]
  nlinarith [phiAW_pos, one_lt_phiAW]

/-- **The coarse-atom measure bound.** Every atom of the coarse `N`-join has measure at most
`C · (2/λ)ᴺ`.  For `N = 0` the atom is the whole space (`1 ≤ C`); for `N = n+1` the coarse atom sits
in the clean atom up to the null junk, and `volume_cleanAtom_le` applies. -/
lemma volume_coarseAtom_le (N : ℕ) (f : Fin N → Fin 2) :
    (volume : Measure T2) (ksJoinCells coarseAWPartitionJunk.cells catTorus N f)
      ≤ ENNReal.ofReal (coarseC * (2 / lam) ^ N) := by
  cases N with
  | zero =>
    rw [ksJoinCells_apply, Set.iInter_of_empty, measure_univ, pow_zero, mul_one]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal one_le_coarseC
  | succ n =>
    have hlam0 : lam ≠ 0 := lam_pos.ne'
    have hphi2 : (0 : ℝ) < phiAW + 2 := by linarith [phiAW_pos]
    -- coarse atom ⊆ clean atom ∪ (null junk union)
    have hjunk : MeasurableSet (awCell 0) := by
      rw [awCell_zero]
      exact (MeasurableSet.iUnion fun e => measurableSet_catProj_image_branchBox e).compl
    have hnull : (volume : Measure T2)
        (⋃ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' awCell 0) = 0 := by
      refine measure_iUnion_null fun k => ?_
      rw [(measurePreserving_catTorus.iterate (k : ℕ)).measure_preimage hjunk.nullMeasurableSet,
        volume_awCell_zero]
    have hsub : ksJoinCells coarseAWPartitionJunk.cells catTorus (n + 1) f
        ⊆ (⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' awBox (f k)))
          ∪ ⋃ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' awCell 0 := by
      intro x hx
      rw [ksJoinCells_apply, Set.mem_iInter] at hx
      by_cases hall : ∀ k, catTorus^[(k : ℕ)] x ∈ catProj '' awBox (f k)
      · exact Or.inl (Set.mem_iInter.2 fun k => hall k)
      · rw [not_forall] at hall
        obtain ⟨k, hk⟩ := hall
        have hmem : catTorus^[(k : ℕ)] x ∈ coarseCell (f k) := hx k
        rcases coarseCell_sub (f k) hmem with h | h
        · exact absurd h hk
        · exact Or.inr (Set.mem_iUnion.2 ⟨k, h⟩)
    calc (volume : Measure T2) (ksJoinCells coarseAWPartitionJunk.cells catTorus (n + 1) f)
        ≤ volume ((⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' awBox (f k)))
            ∪ ⋃ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' awCell 0) := measure_mono hsub
      _ ≤ volume (⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' awBox (f k)))
            + volume (⋃ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' awCell 0) := measure_union_le _ _
      _ = volume (⋂ k : Fin (n + 1), catTorus^[(k : ℕ)] ⁻¹' (catProj '' awBox (f k))) := by
          rw [hnull, add_zero]
      _ ≤ ENNReal.ofReal (5 * (2 * (phiAW - 1) * phiAW / (phiAW + 2)) * (2 / lam) ^ n) :=
          volume_cleanAtom_le f
      _ = ENNReal.ofReal (coarseC * (2 / lam) ^ (n + 1)) := by
          congr 1
          rw [coarseC, pow_succ]
          field_simp

/-- **Quantitative coarse-partition entropy lower bound.**
`log λ − log 2 ≤ ksEntropyPartition catTorus coarseAWPartitionJunk`. -/
theorem coarseAW_ksEntropyPartition_ge :
    Real.log lam - Real.log 2
      ≤ ksEntropyPartition measurePreserving_catTorus coarseAWPartitionJunk := by
  have hθ : (0 : ℝ) < 2 / lam := div_pos two_pos lam_pos
  have hmain := ksEntropyPartition_ge_of_atom_measure_le measurePreserving_catTorus
    coarseAWPartitionJunk hθ coarseC_pos volume_coarseAtom_le
  rwa [show -Real.log (2 / lam) = Real.log lam - Real.log 2 from by
    rw [Real.log_div two_ne_zero lam_pos.ne']; ring] at hmain

/-- **Strict positivity of the coarse Adler–Weiss partition entropy.**  The first positive
Kolmogorov–Sinai lower bound for a coarse (non-generating) partition of the cat map:
`0 < ksEntropyPartition catTorus coarseAWPartitionJunk`, since `λ = (3+√5)/2 > 2`. -/
theorem coarseAW_ksEntropyPartition_pos :
    0 < ksEntropyPartition measurePreserving_catTorus coarseAWPartitionJunk := by
  have hpos : 0 < Real.log lam - Real.log 2 := by
    have hlt : Real.log 2 < Real.log lam := by
      apply Real.log_lt_log (by norm_num)
      rw [lam]; have := two_lt_sqrt5; linarith
    linarith
  exact lt_of_lt_of_le hpos coarseAW_ksEntropyPartition_ge

end ErgodicTheory.CatMapToral

end
