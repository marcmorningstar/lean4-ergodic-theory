/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Covering numbers from volume (Mañé's Lemma 12.5)

In a finite-dimensional real normed space `E` equipped with an additive Haar measure `μ`, the
`ε`-covering number of a set `S` is controlled by the volume of `S` (more precisely by the volume of
a closed thickening of `S`).  This is the metric-entropy counterpart of the elementary fact that one
cannot pack too many disjoint balls inside a set of finite measure.

The geometric core is a *packing* estimate: an `ε`-separated subset of `S` gives rise to pairwise
**disjoint** closed balls of radius `ε / 2`, each contained in the closed `ε/2`-thickening of `S`.
Summing the (centre-independent) volumes of these balls yields

`packingNumber ε S * μ (closedBall 0 (ε/2)) ≤ μ (cthickening (ε/2) S)`.

Combining with `Metric.coveringNumber_le_packingNumber` and the Haar ball-volume scaling
`MeasureTheory.Measure.addHaar_closedBall` turns this into an explicit dimensional bound

`coveringNumber ε S ≤ V / (ε/2) ^ d * (constant)`,

stated below for `EuclideanSpace ℝ (Fin d)` as
`Metric.coveringNumber_le_addHaar_div_of_addHaar_le`.

This is the abstract input behind Mañé's *Lemma 12.5* (Ricardo Mañé, *Ergodic theory and
differentiable dynamics*, Springer 1987), used in the Margulis–Ruelle inequality to bound the number
of partition elements meeting the image of a box by the volume distortion of the map.

## Main statements

* `Metric.IsSeparated.pairwiseDisjoint_closedBall`: an `ε`-separated set has pairwise disjoint
  closed balls of radius `ε / 2`.
* `MeasureTheory.encard_mul_addHaar_closedBall_le_addHaar_cthickening`: for a separated `C ⊆ S`,
  `C.encard * μ (closedBall 0 (ε/2)) ≤ μ (cthickening (ε/2) S)`.
* `MeasureTheory.packingNumber_mul_addHaar_closedBall_le_addHaar_cthickening`: the packing-number
  form of the previous estimate.
* `MeasureTheory.coveringNumber_mul_addHaar_closedBall_le_addHaar_cthickening`: the covering-number
  form (via `coveringNumber ≤ packingNumber`).
* `Metric.coveringNumber_le_addHaar_div_of_addHaar_le`: the explicit dimensional bound
  `coveringNumber ε S ≤ V / ((ε/2) ^ d * μ (ball 0 1))` on `EuclideanSpace ℝ (Fin d)`.
-/

open Metric MeasureTheory Set Function
open scoped ENNReal NNReal

namespace ENat

/-- The coercion `ℕ∞ → ℝ≥0∞` is sub-additive over suprema: `↑(⨆ i, g i) ≤ ⨆ i, ↑(g i)`.

This is the easy direction of `ENat.toENNReal_iSup` (the full equality lives in a Mathlib file
not in this import closure).  It is all that is needed for the supremum in `packingNumber`. -/
theorem toENNReal_iSup_le {ι : Sort*} (g : ι → ℕ∞) :
    ((⨆ i, g i : ℕ∞) : ℝ≥0∞) ≤ ⨆ i, ((g i : ℕ∞) : ℝ≥0∞) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne (⨆ i, g i) ⊤ with htop | hfin
  · rw [htop, ENat.toENNReal_top, top_le_iff, iSup_eq_top]
    rw [iSup_eq_top] at htop
    intro b hb
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hb.ne
    obtain ⟨i, hi⟩ := htop (n : ℕ∞) (ENat.coe_lt_top n)
    refine ⟨i, hn.trans_le ?_⟩
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.2 hi.le
  · obtain ⟨i, hi⟩ := ENat.exists_eq_iSup_of_lt_top hfin.lt_top
    rw [← hi]
    exact le_iSup (fun i ↦ ((g i : ℕ∞) : ℝ≥0∞)) i

/-- If each coerced term times `c` is bounded by `V`, then so is the coerced supremum times `c`.
A convenience wrapper used to pass a volume bound through the supremum in `packingNumber`. -/
theorem toENNReal_iSup_mul_le {ι : Sort*} (g : ι → ℕ∞) (c V : ℝ≥0∞)
    (h : ∀ i, ((g i : ℕ∞) : ℝ≥0∞) * c ≤ V) : ((⨆ i, g i : ℕ∞) : ℝ≥0∞) * c ≤ V :=
  calc ((⨆ i, g i : ℕ∞) : ℝ≥0∞) * c
      ≤ (⨆ i, ((g i : ℕ∞) : ℝ≥0∞)) * c := by gcongr; exact toENNReal_iSup_le g
    _ = ⨆ i, ((g i : ℕ∞) : ℝ≥0∞) * c := ENNReal.iSup_mul _ _
    _ ≤ V := iSup_le h

end ENat

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] {ε : ℝ≥0} {C : Set E}

/-- An `ε`-separated set gives pairwise **disjoint** closed balls of radius `ε / 2`.

If two points `x ≠ y` are `ε`-separated (`ε < edist x y`) then their closed balls of radius `ε / 2`
are disjoint: a common point `z` would force `dist x y ≤ dist x z + dist z y ≤ ε`, contradicting the
separation. -/
theorem IsSeparated.pairwiseDisjoint_closedBall (hC : IsSeparated (ε : ℝ≥0∞) C) :
    C.PairwiseDisjoint fun x ↦ closedBall x (ε / 2 : ℝ) := by
  intro x hx y hy hxy
  rw [Function.onFun, Set.disjoint_left]
  rintro z hzx hzy
  have hsep : (ε : ℝ) < dist x y := by
    have h := hC hx hy hxy
    simp only at h
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h
    exact h
  have hx' : dist x z ≤ (ε : ℝ) / 2 := by
    rw [dist_comm]; exact mem_closedBall.1 hzx
  have hy' : dist z y ≤ (ε : ℝ) / 2 := mem_closedBall.1 hzy
  have : dist x y ≤ (ε : ℝ) := by
    calc dist x y ≤ dist x z + dist z y := dist_triangle x z y
      _ ≤ (ε : ℝ) / 2 + (ε : ℝ) / 2 := by gcongr
      _ = (ε : ℝ) := by ring
  exact absurd this (not_le.2 hsep)

end Metric

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} {S C : Set E}

/-- **Packing-from-volume, set form.**  If `C ⊆ S` is `ε`-separated, the number of points in `C`
times the volume of a closed ball of radius `ε / 2` is at most the volume of the closed
`ε/2`-thickening of `S`.

The closed balls of radius `ε / 2` centred at points of `C` are pairwise disjoint
(`Metric.IsSeparated.pairwiseDisjoint_closedBall`), each contained in `cthickening (ε/2) S`, and
each of the (centre-independent) volume `μ (closedBall 0 (ε/2))`. -/
theorem encard_mul_addHaar_closedBall_le_addHaar_cthickening
    (hCS : C ⊆ S) (hC : IsSeparated (ε : ℝ≥0∞) C) :
    C.encard * μ (Metric.closedBall (0 : E) (ε / 2 : ℝ))
      ≤ μ (Metric.cthickening (ε / 2 : ℝ) S) := by
  have hdisj := hC.pairwiseDisjoint_closedBall
  -- The disjoint balls live inside the closed `ε/2`-thickening of `S`.
  have hsub : (⋃ x : C, Metric.closedBall (x : E) (ε / 2 : ℝ))
      ⊆ Metric.cthickening (ε / 2 : ℝ) S := by
    refine iUnion_subset fun x ↦ ?_
    exact Metric.closedBall_subset_cthickening (hCS x.2) _
  -- Disjointness of the subtype-indexed family.
  have hpd : Pairwise (AEDisjoint μ on fun x : C ↦ Metric.closedBall (x : E) (ε / 2 : ℝ)) := by
    intro x y hxy
    refine (hdisj x.2 y.2 ?_).aedisjoint
    exact fun h ↦ hxy (Subtype.ext h)
  -- Each ball is measurable and has the same (centre `0`) volume.
  have hmeas : ∀ x : C, NullMeasurableSet (Metric.closedBall (x : E) (ε / 2 : ℝ)) μ := fun x ↦
    measurableSet_closedBall.nullMeasurableSet
  have hvol : ∀ x : C, μ (Metric.closedBall (x : E) (ε / 2 : ℝ))
      = μ (Metric.closedBall (0 : E) (ε / 2 : ℝ)) :=
    fun x ↦ Measure.addHaar_closedBall_center μ _ _
  calc C.encard * μ (Metric.closedBall (0 : E) (ε / 2 : ℝ))
      = ∑' _ : C, μ (Metric.closedBall (0 : E) (ε / 2 : ℝ)) :=
        (ENNReal.tsum_set_const C _).symm
    _ = ∑' x : C, μ (Metric.closedBall (x : E) (ε / 2 : ℝ)) :=
        tsum_congr fun x ↦ (hvol x).symm
    _ ≤ μ (⋃ x : C, Metric.closedBall (x : E) (ε / 2 : ℝ)) :=
        tsum_meas_le_meas_iUnion_of_disjoint₀ μ hmeas hpd
    _ ≤ μ (Metric.cthickening (ε / 2 : ℝ) S) := measure_mono hsub

/-- **Packing-from-volume, packing-number form.**  The packing number of `S` for radius `ε` times
the volume of a closed ball of radius `ε / 2` is at most the volume of the closed
`ε/2`-thickening of `S`. -/
theorem packingNumber_mul_addHaar_closedBall_le_addHaar_cthickening (S : Set E) :
    packingNumber ε S * μ (Metric.closedBall (0 : E) (ε / 2 : ℝ))
      ≤ μ (Metric.cthickening (ε / 2 : ℝ) S) := by
  rw [packingNumber]
  refine ENat.toENNReal_iSup_mul_le _ _ _ fun C ↦ ?_
  refine ENat.toENNReal_iSup_mul_le _ _ _ fun hCS ↦ ?_
  refine ENat.toENNReal_iSup_mul_le _ _ _ fun hC ↦ ?_
  exact encard_mul_addHaar_closedBall_le_addHaar_cthickening μ hCS hC

/-- **Packing-from-volume, covering-number form.**  The covering number of `S` for radius `ε` times
the volume of a closed ball of radius `ε / 2` is at most the volume of the closed
`ε/2`-thickening of `S`.  Immediate from the packing form via
`Metric.coveringNumber_le_packingNumber`. -/
theorem coveringNumber_mul_addHaar_closedBall_le_addHaar_cthickening (S : Set E) :
    coveringNumber ε S * μ (Metric.closedBall (0 : E) (ε / 2 : ℝ))
      ≤ μ (Metric.cthickening (ε / 2 : ℝ) S) :=
  le_trans (by gcongr; exact coveringNumber_le_packingNumber ε S)
    (packingNumber_mul_addHaar_closedBall_le_addHaar_cthickening μ S)

end MeasureTheory

namespace Metric

open MeasureTheory

variable {d : ℕ} {ε : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin d))} {V : ℝ≥0∞}

/-- **Covering number from volume (Mañé's Lemma 12.5), explicit dimensional form.**

In `EuclideanSpace ℝ (Fin d)` with an additive Haar measure `μ`, if a set `S` has
`μ (cthickening (ε/2) S) ≤ V` and `ε > 0`, then its `ε`-covering number is bounded by

`V / ((ε / 2) ^ d * μ (ball 0 1))`,

i.e. (up to the dimensional constant `μ (ball 0 1)`) by `V / (ε/2) ^ d`.  In particular, since
`cthickening (ε/2) S` has finite measure whenever `S` does, this gives an explicit finite covering
number for bounded measurable sets. -/
theorem coveringNumber_le_addHaar_div_of_addHaar_le (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [μ.IsAddHaarMeasure] (hε : 0 < ε) (hV : μ (cthickening (ε / 2 : ℝ) S) ≤ V) :
    coveringNumber ε S ≤ V / (ENNReal.ofReal ((ε / 2 : ℝ) ^ d) * μ (ball 0 1)) := by
  -- Volume of the relevant ball, written with `finrank = d`.
  have hr : (0 : ℝ) ≤ (ε / 2 : ℝ) := by positivity
  have hεr : (0 : ℝ) < (ε / 2 : ℝ) := by
    have : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    linarith
  have hball : μ (closedBall (0 : EuclideanSpace ℝ (Fin d)) (ε / 2 : ℝ))
      = ENNReal.ofReal ((ε / 2 : ℝ) ^ d) * μ (ball 0 1) := by
    rw [Measure.addHaar_closedBall μ 0 hr, finrank_euclideanSpace_fin]
  have hpos : 0 < ENNReal.ofReal ((ε / 2 : ℝ) ^ d) * μ (ball 0 1) := by
    refine ENNReal.mul_pos ?_ ?_
    · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos hεr d
    · exact (measure_ball_pos μ 0 (by norm_num)).ne'
  have hfin : ENNReal.ofReal ((ε / 2 : ℝ) ^ d) * μ (ball 0 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ball_lt_top).ne
  -- Rearrange `coveringNumber * ballVol ≤ V` into the division form.
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hfin), ← hball]
  exact le_trans (coveringNumber_mul_addHaar_closedBall_le_addHaar_cthickening μ S) hV

end Metric
