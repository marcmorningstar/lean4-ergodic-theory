/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.Skyscraper
import Oseledets.Krieger.TowerBase
import Oseledets.Krieger.SmallSet
import Oseledets.Krieger.FirstReturn

/-!
# The Rokhlin (Kakutani) tower lemma (issue #15)

This file assembles the **Rokhlin tower lemma**: for an ergodic, measure-preserving automorphism
`e` of a standard Borel probability space with a non-atomic measure, and for any height `N ≥ 1` and
any `ε > 0`, there is a measurable base set `B` whose first `N` iterates `eⁱ '' B` are pairwise
disjoint and whose union covers all but `ε` of the space:

`1 - ENNReal.ofReal ε < μ (⋃ i : Fin N, eⁱ '' B)`.

This is the key input to Krieger's generator theorem.

## Proof outline

Fix a small positive base set `A` with `μ A < ε / N` (`exists_small_pos_measurableSet`). The base
is the **tower base** `B := towerBase e A N`, the complete-block starts of the skyscraper over `A`.

* The `N` levels `eⁱ '' B` are pairwise disjoint (`pairwise_disjoint_levels`).
* Their union `C := coveredSet e A N` covers all but `ε`: the skyscraper covers a.e. point
  (`skyscraper_ae_univ`), the uncovered part of the skyscraper lies in the top incomplete floors
  (`compl_inter_skyscraper_subset_topFloors`), and those have measure
  `≤ ∑ k, ((k+1) mod N) · μ (returnLevel e A (k+1)) ≤ N · μ A < ε`
  (`measure_topFloors_le`, `tsum_returnLevel_eq`, `residual_lt_eps`).

## Main results

* `rokhlin_tower_aux` — the inner statement, carrying the benign working hypothesis `ε ≤ 1`.
* `rokhlin_tower` — the headline lemma; a WLOG wrapper reducing `ε` to `min ε 1`.
-/

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace Oseledets.Krieger

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]

/-- Inner form of the Rokhlin tower lemma, carrying the benign working hypothesis `ε ≤ 1`: there is
a measurable base whose first `N` iterates are pairwise disjoint and cover all but `ε`. -/
theorem rokhlin_tower_aux [NoAtoms μ] (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    (herg : Ergodic (e : α → α) μ) (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ B : Set α, MeasurableSet B ∧
      Pairwise (Function.onFun Disjoint (fun i : Fin N => (e : α → α)^[i] '' B)) ∧
      1 - ENNReal.ofReal ε < μ (⋃ i : Fin N, (e : α → α)^[i] '' B) := by
  -- STEP 1: a small positive base `A` with `μ A < ofReal (ε/N)`.
  have hδpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / N) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨A, hA, hApos, hAsmall⟩ :=
    exists_small_pos_measurableSet (μ := μ) (δ := ENNReal.ofReal (ε / N)) hδpos
  -- STEP 2/3: the tower base `B := towerBase e A N`.
  refine ⟨towerBase e A N, measurableSet_towerBase e hA N, ?_, ?_⟩
  · -- Level disjointness.
    exact pairwise_disjoint_levels e A hN
  · -- Measure bound on `C := ⋃ i, eⁱ '' B = coveredSet e A N`.
    set C : Set α := ⋃ i : Fin N, (e : α → α)^[i] '' towerBase e A N with hCdef
    have hCmeas : MeasurableSet C := by
      refine MeasurableSet.iUnion fun i => ?_
      exact measurableSet_iterate_image e (i : ℕ) (measurableSet_towerBase e hA N)
    -- Via `measure_gt_of_compl_lt`, reduce to `μ Cᶜ < ofReal ε` and `ofReal ε ≤ 1`.
    apply measure_gt_of_compl_lt hCmeas
    · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hε1
    · -- `μ Cᶜ < ofReal ε`: `Cᶜ ⊆ (Cᶜ ∩ skyscraper) ∪ skyscraperᶜ`, the latter null.
      have htile : skyscraper e A =ᵐ[μ] (univ : Set α) :=
        skyscraper_ae_univ e he herg hA hApos
      -- `C` is defeq to `coveredSet e A N`.
      have hcover : Cᶜ ∩ skyscraper e A ⊆ topFloors e A N :=
        compl_inter_skyscraper_subset_topFloors e A (N := N) hN
      have htopmeas : μ (topFloors e A N)
          ≤ ∑' k, ((k + 1) % N : ℕ) * μ (returnLevel e A (k + 1)) :=
        measure_topFloors_le e he hA hN
      have hsky0 : μ (skyscraper e A)ᶜ = 0 := by
        have : (skyscraper e A)ᶜ =ᵐ[μ] (∅ : Set α) := by
          rw [← compl_univ]; exact htile.compl
        simpa using measure_congr this
      have hCcbound : μ Cᶜ ≤ μ (topFloors e A N) := by
        have hsub : Cᶜ ⊆ (Cᶜ ∩ skyscraper e A) ∪ (skyscraper e A)ᶜ := by
          intro y hy
          by_cases hys : y ∈ skyscraper e A
          · exact Or.inl ⟨hy, hys⟩
          · exact Or.inr hys
        calc μ Cᶜ ≤ μ ((Cᶜ ∩ skyscraper e A) ∪ (skyscraper e A)ᶜ) := measure_mono hsub
          _ ≤ μ (Cᶜ ∩ skyscraper e A) + μ (skyscraper e A)ᶜ := measure_union_le _ _
          _ ≤ μ (topFloors e A N) + 0 :=
              add_le_add (measure_mono hcover) (le_of_eq hsky0)
          _ = μ (topFloors e A N) := by rw [add_zero]
      have hres : μ (topFloors e A N) < ENNReal.ofReal ε :=
        residual_lt_eps hN hε (fun k => μ (returnLevel e A (k + 1)))
          (tsum_returnLevel_eq e he hA) hAsmall htopmeas
      exact lt_of_le_of_lt hCcbound hres

/-- **The Rokhlin (Kakutani) tower lemma.** For an ergodic, measure-preserving automorphism `e` of
a standard Borel probability space with non-atomic `μ`, any height `N ≥ 1`, and any `ε > 0`, there
is a measurable base `B` whose first `N` iterates `eⁱ '' B` are pairwise disjoint and whose union
covers all but `ε` of the space.

The proof reduces `ε` to `min ε 1 ≤ 1` and applies `rokhlin_tower_aux`; since `min ε 1 ≤ ε`, the
stronger small-`ε` bound implies the target. -/
theorem rokhlin_tower [NoAtoms μ] (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    (herg : Ergodic (e : α → α) μ) (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : Set α, MeasurableSet B ∧
      Pairwise (Function.onFun Disjoint (fun i : Fin N => (e : α → α)^[i] '' B)) ∧
      1 - ENNReal.ofReal ε < μ (⋃ i : Fin N, (e : α → α)^[i] '' B) := by
  obtain ⟨B, hBmeas, hBdisj, hBbound⟩ :=
    rokhlin_tower_aux e he herg N hN (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨B, hBmeas, hBdisj, lt_of_le_of_lt ?_ hBbound⟩
  -- `1 - ofReal ε ≤ 1 - ofReal (min ε 1)` since `min ε 1 ≤ ε`.
  gcongr
  exact min_le_left _ _

end Oseledets.Krieger
