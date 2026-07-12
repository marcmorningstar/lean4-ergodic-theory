/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.LowerBoundGlue
import ErgodicTheory.Examples.CatMapToral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The `5 × 5` grid partition of the 2-torus and the cat-map entropy lower bound

This module builds the explicit **`5 × 5` grid partition** of the 2-torus
`𝕋² = Fin 2 → UnitAddCircle`, whose cells are products of the half-open coordinate subintervals
`[i/5, (i+1)/5) × [j/5, (j+1)/5)` (read off through the `[0,1)`-representative
`AddCircle.equivIco 1 0`). It is a genuine finite measurable partition (measurable cells, pairwise
disjoint, covering the torus), each cell having diameter at most `1/5` in the sup metric.

Combining the abstract lower-bound glue `ErgodicTheory.Entropy.ksEntropy_ge_of_atom_measure_le`
with a geometric atom-measure bound (supplied as a hypothesis) yields the conditional lower bound
`log((3+√5)/2) ≤ h(catTorus)` on the Kolmogorov–Sinai entropy of the Arnold cat map, and hence its
strict positivity.

## Main definitions

* `ErgodicTheory.CatMapToral.gridCell` — a single `[i/5,(i+1)/5) × [j/5,(j+1)/5)` grid cell.
* `ErgodicTheory.CatMapToral.catGridPartition` — the `5 × 5` grid as a `MeasurePartition`.

## Main results

* `ErgodicTheory.CatMapToral.dist_le_of_mem_gridCell` — a grid cell has sup-diameter `≤ 1/5`.
* `ErgodicTheory.CatMapToral.catTorus_ksEntropy_ge_of_gridAtom_bound` — conditional entropy lower
  bound `log((3+√5)/2) ≤ h(catTorus)`.
* `ErgodicTheory.CatMapToral.catTorus_ksEntropy_pos_of_gridAtom_bound` — conditional strict
  positivity `0 < h(catTorus)`.
-/

open MeasureTheory Function Filter Topology Set
open scoped ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching
`ErgodicTheory.Examples.CatMapToral`. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_grid :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_grid :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_grid :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance instFactZeroLtOne_grid : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

namespace ErgodicTheory.CatMapToral

/-! ## Elementary interval combinatorics of the `5`-grid -/

/-- Every `r ∈ [0,1)` lies in a unique subinterval `[i/5, (i+1)/5)` with `i : Fin 5`; existence. -/
lemma exists_gridIdx {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ i : Fin 5, r ∈ Set.Ico (((i : ℕ) : ℝ) / 5) ((((i : ℕ) : ℝ) + 1) / 5) := by
  set m : ℤ := ⌊5 * r⌋ with hm
  have hm_nonneg : 0 ≤ m := Int.floor_nonneg.mpr (by linarith)
  have hm_lt : m < 5 := by rw [hm]; exact Int.floor_lt.mpr (by push_cast; linarith)
  have hlt5 : m.toNat < 5 := by omega
  set i : Fin 5 := ⟨m.toNat, hlt5⟩ with hi
  have hival : ((i : ℕ) : ℝ) = (m : ℝ) := by
    have hv : (i : ℕ) = m.toNat := rfl
    rw [hv]; exact_mod_cast Int.toNat_of_nonneg hm_nonneg
  refine ⟨i, ?_, ?_⟩
  · rw [hival]
    have hle : (m : ℝ) ≤ 5 * r := by rw [hm]; exact Int.floor_le _
    linarith
  · rw [hival]
    have hlt : 5 * r < (m : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one _
    linarith

/-- The subinterval index of a point of `[0,1)` is unique. -/
lemma gridIdx_unique {i i' : Fin 5} {r : ℝ}
    (h : r ∈ Set.Ico (((i : ℕ) : ℝ) / 5) ((((i : ℕ) : ℝ) + 1) / 5))
    (h' : r ∈ Set.Ico (((i' : ℕ) : ℝ) / 5) ((((i' : ℕ) : ℝ) + 1) / 5)) : i = i' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have c1 : ((i : ℕ) : ℝ) < ((i' : ℕ) : ℝ) + 1 := by linarith
  have c2 : ((i' : ℕ) : ℝ) < ((i : ℕ) : ℝ) + 1 := by linarith
  have d1 : (i : ℕ) < (i' : ℕ) + 1 := by exact_mod_cast c1
  have d2 : (i' : ℕ) < (i : ℕ) + 1 := by exact_mod_cast c2
  exact Fin.ext (by omega)

/-! ## The grid partition -/

/-- A single grid cell `[i/5, (i+1)/5) × [j/5, (j+1)/5)`, read off through the `[0,1)`
representatives of the two coordinates. -/
def gridCell (i j : Fin 5) : Set T2 :=
  {y | (AddCircle.equivIco 1 0 (y 0) : ℝ) ∈
        Set.Ico (((i : ℕ) : ℝ) / 5) ((((i : ℕ) : ℝ) + 1) / 5) ∧
      (AddCircle.equivIco 1 0 (y 1) : ℝ) ∈
        Set.Ico (((j : ℕ) : ℝ) / 5) ((((j : ℕ) : ℝ) + 1) / 5)}

/-- The coordinate representative map `y ↦ (equivIco 1 0 (y k) : ℝ)` is measurable. -/
lemma measurable_gridRep (k : Fin 2) :
    Measurable (fun y : T2 => (AddCircle.equivIco (1 : ℝ) 0 (y k) : ℝ)) := by
  have hme : Measurable (fun x : UnitAddCircle =>
      (AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1))) :=
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  exact (measurable_subtype_coe.comp hme).comp (measurable_pi_apply k)

/-- The `[0,1)` representative of any coordinate lies in `[0,1)`. -/
lemma gridRep_mem_Ico (k : Fin 2) (y : T2) :
    (0 : ℝ) ≤ (AddCircle.equivIco (1 : ℝ) 0 (y k) : ℝ) ∧
      (AddCircle.equivIco (1 : ℝ) 0 (y k) : ℝ) < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 (y k)).2
  simp only [Set.mem_Ico] at h
  exact ⟨h.1, by linarith [h.2]⟩

/-- The **`5 × 5` grid partition** of the 2-torus. -/
def catGridPartition : Entropy.MeasurePartition (volume : Measure T2) (Fin 5 × Fin 5) where
  cells := fun ij => gridCell ij.1 ij.2
  measurable := by
    intro ij
    refine MeasurableSet.inter ?_ ?_
    · exact (measurable_gridRep 0) measurableSet_Ico
    · exact (measurable_gridRep 1) measurableSet_Ico
  aedisjoint := by
    intro ij ij' hne
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_left]
    rintro y ⟨hy0, hy1⟩ ⟨hy0', hy1'⟩
    have hi : ij.1 = ij'.1 := gridIdx_unique hy0 hy0'
    have hj : ij.2 = ij'.2 := gridIdx_unique hy1 hy1'
    exact hne (Prod.ext hi hj)
  cover := by
    apply Set.eq_univ_of_univ_subset
    intro y _
    obtain ⟨i, hi⟩ := exists_gridIdx (gridRep_mem_Ico 0 y).1 (gridRep_mem_Ico 0 y).2
    obtain ⟨j, hj⟩ := exists_gridIdx (gridRep_mem_Ico 1 y).1 (gridRep_mem_Ico 1 y).2
    exact Set.mem_iUnion.mpr ⟨(i, j), ⟨hi, hj⟩⟩

@[simp]
lemma catGridPartition_cells (ij : Fin 5 × Fin 5) :
    catGridPartition.cells ij = gridCell ij.1 ij.2 := rfl

/-! ## The sup-diameter bound -/

/-- Two coordinates of `AddCircle 1` whose `[0,1)`-representatives lie in a common length-`1/5`
subinterval are within `1/5` in the quotient metric. -/
lemma dist_coord_le {a b : UnitAddCircle}
    (hab : |(AddCircle.equivIco (1 : ℝ) 0 a : ℝ) - (AddCircle.equivIco (1 : ℝ) 0 b : ℝ)| ≤ 1 / 5) :
    dist a b ≤ 1 / 5 := by
  set ra : ℝ := (AddCircle.equivIco (1 : ℝ) 0 a : ℝ) with hra
  set rb : ℝ := (AddCircle.equivIco (1 : ℝ) 0 b : ℝ) with hrb
  have hcoe_a : ((ra : ℝ) : UnitAddCircle) = a := by rw [hra]; exact AddCircle.coe_equivIco
  have hcoe_b : ((rb : ℝ) : UnitAddCircle) = b := by rw [hrb]; exact AddCircle.coe_equivIco
  calc dist a b = dist ((ra : ℝ) : UnitAddCircle) ((rb : ℝ) : UnitAddCircle) := by
        rw [hcoe_a, hcoe_b]
    _ = ‖((ra : ℝ) : UnitAddCircle) - ((rb : ℝ) : UnitAddCircle)‖ := dist_eq_norm _ _
    _ = ‖((ra - rb : ℝ) : UnitAddCircle)‖ := by rw [AddCircle.coe_sub]
    _ ≤ ‖(ra - rb : ℝ)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |ra - rb| := Real.norm_eq_abs _
    _ ≤ 1 / 5 := hab

/-- **Grid cells have sup-diameter `≤ 1/5`.** If `x, y` lie in the same grid cell, then their
distance in the sup metric on `Fin 2 → UnitAddCircle` is at most `1/5`. -/
lemma dist_le_of_mem_gridCell {i j : Fin 5} {x y : T2}
    (hx : x ∈ gridCell i j) (hy : y ∈ gridCell i j) : dist x y ≤ 1 / 5 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hd0 : |(AddCircle.equivIco (1 : ℝ) 0 (x 0) : ℝ) -
      (AddCircle.equivIco (1 : ℝ) 0 (y 0) : ℝ)| ≤ 1 / 5 := by
    obtain ⟨hx0a, hx0b⟩ := hx0
    obtain ⟨hy0a, hy0b⟩ := hy0
    rw [abs_le]; constructor <;> linarith
  have hd1 : |(AddCircle.equivIco (1 : ℝ) 0 (x 1) : ℝ) -
      (AddCircle.equivIco (1 : ℝ) 0 (y 1) : ℝ)| ≤ 1 / 5 := by
    obtain ⟨hx1a, hx1b⟩ := hx1
    obtain ⟨hy1a, hy1b⟩ := hy1
    rw [abs_le]; constructor <;> linarith
  rw [dist_pi_le_iff (by norm_num)]
  intro k
  fin_cases k
  · exact dist_coord_le hd0
  · exact dist_coord_le hd1

/-! ## The conditional entropy lower bound -/

/-- **Conditional Kolmogorov–Sinai lower bound for the Arnold cat map.** If every atom of the
`n`-fold iterated join of the grid partition under `catTorus` has volume at most
`(9√5/25) · λ · μⁿ` (with `λ = (3+√5)/2`, `μ = (3-√5)/2`), then `log λ ≤ h(catTorus)`. This feeds
the geometric atom-measure bound into the abstract glue
`ErgodicTheory.Entropy.ksEntropy_ge_of_atom_measure_le` with `θ = μ` and `C = (9√5/25)·λ`, using
`-log μ = log λ` (since `λμ = 1`). -/
theorem catTorus_ksEntropy_ge_of_gridAtom_bound
    (hwall : ∀ (n : ℕ) (f : Fin n → Fin 5 × Fin 5),
      (volume : Measure T2)
          (Entropy.ksJoinCells catGridPartition.cells catTorus n f)
        ≤ ENNReal.ofReal ((9 * Real.sqrt 5 / 25) * ((3 + Real.sqrt 5) / 2)
            * ((3 - Real.sqrt 5) / 2) ^ n)) :
    ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal)
      ≤ Entropy.ksEntropy measurePreserving_catTorus := by
  have hmu_pos : (0 : ℝ) < (3 - Real.sqrt 5) / 2 := by
    have := sqrt5_lt_three; linarith
  have hC_pos : (0 : ℝ) < 9 * Real.sqrt 5 / 25 * ((3 + Real.sqrt 5) / 2) := by
    have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  -- `λμ = 1`, hence `-log μ = log λ`.
  have hprod : (3 + Real.sqrt 5) / 2 * ((3 - Real.sqrt 5) / 2) = 1 := by
    have h := sqrt5_sq; nlinarith [h]
  have hlam_pos : (0 : ℝ) < (3 + Real.sqrt 5) / 2 := by
    have := Real.sqrt_nonneg 5; linarith
  have hlog : -Real.log ((3 - Real.sqrt 5) / 2) = Real.log ((3 + Real.sqrt 5) / 2) := by
    have hsum : Real.log ((3 + Real.sqrt 5) / 2) + Real.log ((3 - Real.sqrt 5) / 2) = 0 := by
      rw [← Real.log_mul hlam_pos.ne' hmu_pos.ne', hprod, Real.log_one]
    linarith
  have key := Entropy.ksEntropy_ge_of_atom_measure_le measurePreserving_catTorus
    catGridPartition (θ := (3 - Real.sqrt 5) / 2)
    (C := 9 * Real.sqrt 5 / 25 * ((3 + Real.sqrt 5) / 2)) hmu_pos hC_pos
    (fun n f => hwall n f)
  rwa [hlog] at key

/-- **Conditional strict positivity of the cat-map Kolmogorov–Sinai entropy.** Under the same
geometric atom-measure bound, `0 < h(catTorus)`, because `log((3+√5)/2) > 0`. -/
theorem catTorus_ksEntropy_pos_of_gridAtom_bound
    (hwall : ∀ (n : ℕ) (f : Fin n → Fin 5 × Fin 5),
      (volume : Measure T2)
          (Entropy.ksJoinCells catGridPartition.cells catTorus n f)
        ≤ ENNReal.ofReal ((9 * Real.sqrt 5 / 25) * ((3 + Real.sqrt 5) / 2)
            * ((3 - Real.sqrt 5) / 2) ^ n)) :
    (0 : EReal) < Entropy.ksEntropy measurePreserving_catTorus := by
  have hpos : (0 : ℝ) < Real.log ((3 + Real.sqrt 5) / 2) := by
    refine Real.log_pos ?_
    have := two_lt_sqrt5; linarith
  refine lt_of_lt_of_le ?_ (catTorus_ksEntropy_ge_of_gridAtom_bound hwall)
  exact_mod_cast hpos

end ErgodicTheory.CatMapToral
