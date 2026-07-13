/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapSymbolicTower
import ErgodicTheory.Examples.CatMapCoarsePositivity

/-!
# Reconciling the two coarse Adler–Weiss partitions and the merged-tower positivity

Two sibling modules describe the *same* two-cell coarse Adler–Weiss factor of the Arnold cat map
`catTorus` through different — but provably identical — partitions:

* `ErgodicTheory.Examples.CatMapCoarsePartition` records the **exact-cover** partition
  `coarseAWPartition` whose cells are the two projected golden rectangles
  `i ↦ catProj '' awBox i`.  The cover is exact because the fine branch tiling has an empty junk
  cell; this is the partition the flow tower (`CatMapSymbolicTower`) identifies with the merged
  two-symbol subshift.
* `ErgodicTheory.Examples.CatMapCoarsePositivity` proves the library's first *positive*
  Kolmogorov–Sinai lower bound `log λ − log 2 ≤ h(catTorus, ·)` for a **junk-absorbing** partition
  `coarseAWPartitionJunk` (cell `1 = catProj '' awBox 1`, cell `0 = (catProj '' awBox 1)ᶜ`), whose
  complement cell swallows the null junk.

Because the two projected rectangles are disjoint (`disjoint_catProj_image_awBox`) and cover the
torus (`coarseAWPartition.cover`), `catProj '' awBox 0 = (catProj '' awBox 1)ᶜ`, so the two
partitions have **identical cells**.  `Entropy.ksEntropyPartition_congr_cells` transports the
positive lower bound from the junk partition to the exact-cover one, and the tower's identifications
carry it up to the merged two-symbol base system and its suspension flow, closing the bracket

`log λ − log 2 ≤ h(merged) ≤ log 2`

at both the base and the flow level (with `log λ = log((3 + √5)/2)` the cat-map entropy).

## Main results

* `ErgodicTheory.CatMapToral.coarseAWPartition_ksEntropyPartition_pos` /
  `_ge` — positivity and the quantitative lower bound for the exact-cover partition.
* `ErgodicTheory.CatMapToral.ksEntropy_mapCoarseSymb_pos` / `_ge` /
  `_bracket` — the merged two-symbol base system.
* `ErgodicTheory.CatMapToral.ksEntropy_twoSymbolSuspFlow_pos` / `_ge` /
  `_bracket` — the two-symbol suspension flow.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1`, matching the imported cat-map measure modules so
that `volume : Measure T2` lines up with the Adler–Weiss data. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_towerPos :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_towerPos :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_towerPos :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

open ErgodicTheory.Entropy ErgodicTheory.Multifractal ErgodicTheory.Krieger

/-! ## The two coarse partitions have identical cells -/

/-- **The zeroth projected rectangle is the complement of the first.**  The two projected golden
rectangles are disjoint (`disjoint_catProj_image_awBox`) and cover the torus
(`coarseAWPartition.cover`), so each is the complement of the other. -/
theorem catProj_image_awBox_zero_eq_compl :
    catProj '' awBox (0 : Fin 2) = (catProj '' awBox (1 : Fin 2))ᶜ := by
  refine subset_antisymm ?_ ?_
  · rw [Set.subset_compl_iff_disjoint_right]
    exact disjoint_catProj_image_awBox (by decide)
  · intro x hx
    have hmem : x ∈ ⋃ i, coarseAWPartition.cells i := by
      rw [coarseAWPartition.cover]; trivial
    rw [Set.mem_iUnion] at hmem
    obtain ⟨i, hi⟩ := hmem
    fin_cases i
    · exact hi
    · exact absurd hi hx

/-- **The junk partition and the exact-cover partition share their cell family.**  Cell `1` is
`catProj '' awBox 1` in both; cell `0` is `(catProj '' awBox 1)ᶜ = catProj '' awBox 0`. -/
theorem coarseAWPartitionJunk_cells_eq :
    (coarseAWPartitionJunk.cells : Fin 2 → Set T2) = coarseAWPartition.cells := by
  funext i
  fin_cases i
  · exact catProj_image_awBox_zero_eq_compl.symm
  · rfl

/-! ## Positivity transported to the exact-cover partition -/

/-- **Quantitative lower bound for the exact-cover partition.**  The positive bound
`log λ − log 2 ≤ ksEntropyPartition catTorus coarseAWPartition`, transported from the junk partition
through the identical-cells congruence. -/
theorem coarseAWPartition_ksEntropyPartition_ge :
    Real.log lam - Real.log 2
      ≤ ksEntropyPartition measurePreserving_catTorus coarseAWPartition := by
  rw [← ksEntropyPartition_congr_cells measurePreserving_catTorus
      coarseAWPartitionJunk coarseAWPartition coarseAWPartitionJunk_cells_eq]
  exact coarseAW_ksEntropyPartition_ge

/-- **Strict positivity for the exact-cover partition.**
`0 < ksEntropyPartition catTorus coarseAWPartition`. -/
theorem coarseAWPartition_ksEntropyPartition_pos :
    0 < ksEntropyPartition measurePreserving_catTorus coarseAWPartition := by
  rw [← ksEntropyPartition_congr_cells measurePreserving_catTorus
      coarseAWPartitionJunk coarseAWPartition coarseAWPartitionJunk_cells_eq]
  exact coarseAW_ksEntropyPartition_pos

/-! ## The merged two-symbol base system -/

/-- **The merged two-symbol base system has positive entropy.**  Compose the exact-cover partition
positivity with the tower identification `h(merged) = h(catTorus, coarseAWPartition)`. -/
theorem ksEntropy_mapCoarseSymb_pos :
    0 < ksEntropy measurePreserving_biShiftEquiv_mapCoarseSymb := by
  rw [ksEntropy_mapCoarseSymb_eq, ← EReal.coe_zero, EReal.coe_lt_coe_iff]
  exact coarseAWPartition_ksEntropyPartition_pos

/-- **Quantitative merged-system lower bound** `log λ − log 2 ≤ h(merged)`. -/
theorem ksEntropy_mapCoarseSymb_ge :
    ((Real.log lam - Real.log 2 : ℝ) : EReal)
      ≤ ksEntropy measurePreserving_biShiftEquiv_mapCoarseSymb := by
  rw [ksEntropy_mapCoarseSymb_eq, EReal.coe_le_coe_iff]
  exact coarseAWPartition_ksEntropyPartition_ge

/-- **The merged-system entropy bracket** `log λ − log 2 ≤ h(merged) ≤ log 2`. -/
theorem ksEntropy_mapCoarseSymb_bracket :
    ((Real.log lam - Real.log 2 : ℝ) : EReal)
        ≤ ksEntropy measurePreserving_biShiftEquiv_mapCoarseSymb
      ∧ ksEntropy measurePreserving_biShiftEquiv_mapCoarseSymb ≤ ((Real.log 2 : ℝ) : EReal) :=
  ⟨ksEntropy_mapCoarseSymb_ge, ksEntropy_mapCoarseSymb_le⟩

/-! ## The two-symbol suspension flow -/

/-- The two-symbol unit-roof suspension is a probability space (mirrors the tower's local
instance). -/
local instance instProbSuspZ_towerPos : IsProbabilityMeasure
    (suspensionMeasure biShiftEquiv (measurable_oneRoof (α₀ := Fin 2))
      (Measure.map coarseSymb (volume : Measure T2))) :=
  isProbabilityMeasure_suspensionMeasure_unit biShiftEquiv measurable_oneRoof rfl _

/-- **The two-symbol suspension flow has positive entropy.**  The unit-roof time-`1` descent carries
the positive merged base entropy to the flow. -/
theorem ksEntropy_twoSymbolSuspFlow_pos :
    0 < ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
        (measurable_oneRoof (α₀ := Fin 2)) measurePreserving_biShiftEquiv_mapCoarseSymb
        oneRoof_le one_pos 1) := by
  rw [ksEntropy_suspensionFlowMap_unitRoof_one biShiftEquiv measurable_oneRoof rfl
    measurePreserving_biShiftEquiv_mapCoarseSymb oneRoof_le]
  exact ksEntropy_mapCoarseSymb_pos

/-- **Quantitative two-symbol flow lower bound** `log λ − log 2 ≤ h(ζ²_1)`. -/
theorem ksEntropy_twoSymbolSuspFlow_ge :
    ((Real.log lam - Real.log 2 : ℝ) : EReal)
      ≤ ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
        (measurable_oneRoof (α₀ := Fin 2)) measurePreserving_biShiftEquiv_mapCoarseSymb
        oneRoof_le one_pos 1) := by
  rw [ksEntropy_suspensionFlowMap_unitRoof_one biShiftEquiv measurable_oneRoof rfl
    measurePreserving_biShiftEquiv_mapCoarseSymb oneRoof_le]
  exact ksEntropy_mapCoarseSymb_ge

/-- **The two-symbol suspension-flow entropy bracket** `log λ − log 2 ≤ h(ζ²_1) ≤ log 2`: the merged
flow is genuinely chaotic yet strictly below the golden cat-suspension flow. -/
theorem ksEntropy_twoSymbolSuspFlow_bracket :
    ((Real.log lam - Real.log 2 : ℝ) : EReal)
        ≤ ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
          (measurable_oneRoof (α₀ := Fin 2)) measurePreserving_biShiftEquiv_mapCoarseSymb
          oneRoof_le one_pos 1)
      ∧ ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
          (measurable_oneRoof (α₀ := Fin 2)) measurePreserving_biShiftEquiv_mapCoarseSymb
          oneRoof_le one_pos 1) ≤ ((Real.log 2 : ℝ) : EReal) :=
  ⟨ksEntropy_twoSymbolSuspFlow_ge, ksEntropy_twoSymbolSuspFlow_le⟩

end ErgodicTheory.CatMapToral

end
