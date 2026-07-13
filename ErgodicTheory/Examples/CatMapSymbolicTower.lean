/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapAdlerWeissFactor
import ErgodicTheory.Examples.CatMapCoarsePartition
import ErgodicTheory.Examples.CatMapEntropy
import ErgodicTheory.Examples.CatMapSuspensionFlow
import ErgodicTheory.Continuous.SuspensionFactor
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Multifractal.BernoulliTwoSidedGenerating
import ErgodicTheory.Multifractal.BernoulliSuspensionEntropy
import ErgodicTheory.Entropy.FactorEntropy
import ErgodicTheory.Entropy.GeneratorTheoremTwoSided
import ErgodicTheory.Entropy.ProductIdEntropy
import ErgodicTheory.Entropy.KSEntropyConjugacy
import ErgodicTheory.Krieger.GeneratingOfSeparating

/-!
# The depth-two symbolic tower on the Arnold cat lineage (issue #58, tier 3)

Two stacked symbolic codings of the Arnold cat map `catTorus`, one a **measure conjugacy**, the
other a genuine non-injective **`1`-block factor** with a strict entropy drop, promoted to the two
suspension (mapping-torus) flows.

## Stage 1 — the Adler–Weiss coding (a conjugacy)

`awSymbFull : T2 → BiShift (Fin 5)` is the two-sided golden Adler–Weiss itinerary
(`ErgodicTheory.Examples.CatMapAdlerWeissFactor`): an *exact* factor map onto the golden subshift
of finite type that is **injective on the nose** (`injective_awSymbFull`).  As a coding stage it
*preserves* entropy — the issue's expectation of a strict drop at every step is impossible for a
coding, and we disclose this: `ksEntropy` of the `SFT₅` image system equals `log((3 + √5)/2)`, the
cat-map entropy.

## Stage 2 — the `1`-block source merge (a genuine factor)

`mergeSrc : BiShift (Fin 5) → BiShift (Fin 2)`, `y ↦ (k ↦ src (y k))`, is a **`1`-block code**
(Lind–Marcus, *Symbolic Dynamics*, Ch. 1, §1.5 (sliding block codes)): it lumps the five golden
branches to the two golden
rectangles they sit inside.  Composed with the coding this is the **coarse itinerary**
`coarseSymb x = (k ↦ src (awSymb x k))`, a factor onto the two-symbol shift whose merged system has
Kolmogorov–Sinai entropy `= h(catTorus, coarseAWPartition) ≤ log 2 < log((3 + √5)/2)`: the strict
drop of a genuine lumping (Kemeny–Snell lumpability).

## The flow tower

Instantiating the unit-roof suspension functor (`ErgodicTheory.suspensionFactorMap`) twice gives two
suspension-flow factor maps at time `1`; the first is injective (the conjugacy stage), the second is
the strict-drop lumping.  A general unit-roof time-`1` entropy descent
(`ksEntropy_suspensionFlowMap_unitRoof_one`) transports the base pins to the flows, yielding the
strict flow-entropy drop `h(ζ²_1) ≤ log 2 < log((3 + √5)/2) = h(ζ^{cat}_1)`.

Positivity of the merged level (`h ≥ log λ − log 2`) is delivered in a sibling module and wired at
integration.  That lower bound is proved on the junk-absorbing partition `coarseAWPartitionJunk`,
which is provably cell-equal to `coarseAWPartition` (empty-junk exact tiling); the bridge and the
single-object bracket live in `CatMapTowerPositivity` (`coarseAWPartitionJunk_cells_eq`,
`ksEntropy_mapCoarseSymb_bracket`, `ksEntropy_twoSymbolSuspFlow_bracket`).

## References

* R. L. Adler and B. Weiss, *Similarity of automorphisms of the torus*, Memoirs AMS **98** (1970).
* D. Lind and B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, CUP (1995), Ch. 1,
  §1.5 (sliding block codes).
* J. G. Kemeny and J. L. Snell, *Finite Markov Chains*, Springer (1976) (lumpability).
* W. Ambrose and S. Kakutani, *Structure and continuity of measurable flows*, Duke Math. J. **9**
  (1942), 25–42.
-/

open MeasureTheory Function Filter
open scoped ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1`, matching the imported cat-map measure modules so
that `volume : Measure T2` lines up with the Adler–Weiss data. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_tower :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_tower :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_tower :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Generic tools -/

namespace ErgodicTheory.Entropy

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- **Partition entropy depends only on the cells.**  Two finite measurable partitions with equal
cell families have equal partition-relative Kolmogorov–Sinai entropy, since the iterated-join
entropy sequence is a function of the cells alone. -/
theorem ksEntropyPartition_congr_cells {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P Q : MeasurePartition μ ι) (h : P.cells = Q.cells) :
    ksEntropyPartition hT P = ksEntropyPartition hT Q := by
  unfold ksEntropyPartition
  refine Subadditive.lim_eq_of_eq _ _ (funext fun n => ?_)
  rw [ksEntropySeq, ksEntropySeq, ksJoin_cells, ksJoin_cells, h]

end ErgodicTheory.Entropy

namespace ErgodicTheory

/-- **Pushforward invariance under a semiconjugacy.**  If `T` preserves `μ`, `π` intertwines `T`
with `S` (`π ∘ T = S ∘ π`), and `S` is measurable, then `S` preserves the pushforward `π_* μ`. -/
theorem measurePreserving_map_of_semiconj {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {T : A → A} {S : B → B} {π : A → B} {μ : Measure A} (hT : MeasurePreserving T μ μ)
    (hπ : Measurable π) (hS : Measurable S) (h : π ∘ T = S ∘ π) :
    MeasurePreserving S (Measure.map π μ) (Measure.map π μ) := by
  refine ⟨hS, ?_⟩
  rw [Measure.map_map hS hπ, ← h, ← Measure.map_map hπ hT.measurable, hT.map_eq]

open ErgodicTheory.Multifractal ErgodicTheory.Krieger in
/-- **The time-`0` coordinate partition two-sidedly generates for any measure.**  The generating
property `⨆ n, comap (ziter biShiftEquiv n) σ(coordPartitionZ) = mα` is measure-independent: it is a
statement about the coordinate σ-algebras of the two-sided full shift, discharged by the same three
identities used for the Bernoulli measure. -/
theorem coordPartitionZ_isGeneratingTwoSided_any {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀]
    [MeasurableSingletonClass α₀] (μ : Measure (BiShift α₀)) :
    IsGeneratingTwoSided (biShiftEquiv (α₀ := α₀)) (coordPartitionZ μ) := by
  unfold IsGeneratingTwoSided
  simp_rw [generatedSigmaAlgebra_coordPartitionZ_eq, comap_ziter_coordSigmaZ]
  exact pi_eq_iSup_coordSigmaZ.symm

/-! ### The unit-roof time-`1` suspension entropy descent -/

section UnitRoofFlow

open Multifractal Set

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- For a probability base measure and the constant unit roof `τ ≡ 1`, the suspension measure is a
probability measure (the roof integral is `1`). -/
theorem isProbabilityMeasure_suspensionMeasure_unit (hτ1 : τ = fun _ => (1 : ℝ)) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (suspensionMeasure T hτ μ) := by
  refine isProbabilityMeasure_suspensionMeasure T hτ μ (fun x => ?_) ?_ ?_
  · simp [hτ1]
  · rw [hτ1]; exact integrable_const 1
  · have hone : ∫ x, τ x ∂μ = 1 := by rw [hτ1]; simp
    rw [hone]; exact one_pos

/-- **The fundamental-domain box transport.**  The inverse fundamental-domain embedding
`(x, t) ↦ [x, t]` pushes the product `μ × fibreMeasure` on `X × [0,1)` to the (unit-roof) suspension
probability measure.  `suspensionUnitInv = suspensionMk ∘ (id × Subtype.val)`, so the pushforward
factors through the box restriction of `μ × volume` and lands on `suspensionMeasure₀ =
suspensionMeasure` (unit roof). -/
theorem map_suspensionUnitInv_eq_gen (hτ1 : τ = fun _ => (1 : ℝ)) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    Measure.map (suspensionUnitInv T hτ) (μ.prod fibreMeasure) = suspensionMeasure T hτ μ := by
  have hinv_eq : (suspensionUnitInv T hτ)
      = suspensionMk T hτ ∘ Prod.map id Subtype.val := by funext y; rfl
  have hmk : Measurable (suspensionMk T hτ) := measurable_suspensionMk T hτ
  have hincl : Measurable (Prod.map (id : X → X)
      (Subtype.val : ↥(Set.Ico (0 : ℝ) 1) → ℝ)) := measurable_id.prodMap measurable_subtype_coe
  rw [hinv_eq, ← Measure.map_map hmk hincl,
    ← Measure.map_prod_map μ fibreMeasure measurable_id measurable_subtype_coe, Measure.map_id]
  unfold fibreMeasure
  rw [map_comap_subtype_coe measurableSet_Ico]
  have hpr : μ.prod ((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1))
      = (μ.prod volume).restrict (Set.univ ×ˢ Set.Ico (0 : ℝ) 1) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hdom : (Set.univ : Set X) ×ˢ Set.Ico (0 : ℝ) 1 = suspensionDomain τ := by
    ext p
    simp only [suspensionDomain, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ico, hτ1]
  rw [hpr, hdom, suspensionMeasure_eq_of_unitRoof T hτ hτ1]
  rfl

/-- The fundamental-domain equivalence is measure preserving, sending the suspension probability
measure to `μ × fibreMeasure`.  Flip of the inverse-direction transport. -/
theorem measurePreserving_suspensionUnitEquiv_gen (hτ1 : τ = fun _ => (1 : ℝ)) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    MeasurePreserving ⇑(suspensionUnitMeasurableEquiv T hτ hτ1)
      (suspensionMeasure T hτ μ) (μ.prod fibreMeasure) := by
  have h : MeasurePreserving ⇑(suspensionUnitMeasurableEquiv T hτ hτ1).symm
      (μ.prod fibreMeasure) (suspensionMeasure T hτ μ) :=
    ⟨(suspensionUnitMeasurableEquiv T hτ hτ1).symm.measurable,
      map_suspensionUnitInv_eq_gen T hτ hτ1 μ⟩
  exact MeasurePreserving.symm (suspensionUnitMeasurableEquiv T hτ hτ1).symm h

/-- **The equivalence conjugates the time-`1` map to the frozen product `T × id`.**  For `τ ≡ 1`,
`ζ_1 [x, s] = [x, s + 1]`, and the equivalence maps `[x, s]` to `(baseIter ⌊s⌋ x, fract s)`; both
give `(T (baseIter ⌊s⌋ x), fract s)` since `⌊s+1⌋ = ⌊s⌋+1` and `fract (s+1) = fract s`. -/
theorem suspensionUnitEquiv_comp_flow_gen (hτ1 : τ = fun _ => (1 : ℝ)) :
    ⇑(suspensionUnitMeasurableEquiv T hτ hτ1) ∘ suspensionFlowMap T hτ 1
      = Prod.map ⇑T id ∘ ⇑(suspensionUnitMeasurableEquiv T hτ hτ1) := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspensionUnitFwd T hτ hτ1 (suspensionFlowMap T hτ 1 (suspensionMk T hτ (x, s)))
    = Prod.map ⇑T id (suspensionUnitFwd T hτ hτ1 (suspensionMk T hτ (x, s)))
  rw [suspensionFlowMap_mk, suspensionTranslate_apply, suspensionUnitFwd_mk, suspensionUnitFwd_mk]
  refine Prod.ext ?_ ?_
  · change suspensionBaseProjRaw T hτ ((x, s).1, (x, s).2 + 1)
      = ⇑T (suspensionBaseProjRaw T hτ (x, s))
    rw [suspensionBaseProjRaw_apply, suspensionBaseProjRaw_apply, Int.floor_add_one, baseIter_succ']
  · apply Subtype.ext
    change Int.fract ((x, s).2 + 1) = Int.fract (x, s).2
    rw [Int.fract_add_one]

/-- **Unit-roof time-`1` suspension entropy descent.**  For a measure-preserving base automorphism
`T` on a standard Borel probability space and the constant unit roof `τ ≡ 1`, the time-`1` map
suspension flow has the same Kolmogorov–Sinai entropy as the base map.  The fundamental-domain
equivalence conjugates the time-`1` map to the frozen product `T × id`, whose entropy is `h(T)`
(`ksEntropy_prod_id_eq`). -/
theorem ksEntropy_suspensionFlowMap_unitRoof_one [StandardBorelSpace X]
    (hτ1 : τ = fun _ => (1 : ℝ)) {μ : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (suspensionMeasure T hτ μ)]
    (hT : MeasurePreserving (⇑T) μ μ) (hge : ∀ x, (1 : ℝ) ≤ τ x) :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap T hτ hT hge one_pos 1)
      = Entropy.ksEntropy hT := by
  haveI : StandardBorelSpace ↥(Set.Ico (0 : ℝ) 1) := measurableSet_Ico.standardBorel
  rw [Entropy.ksEntropy_congr_of_conjugacy
        (measurePreserving_suspensionFlowMap T hτ hT hge one_pos 1)
        (hT.prod (MeasurePreserving.id fibreMeasure))
        (suspensionUnitMeasurableEquiv T hτ hτ1)
        (measurePreserving_suspensionUnitEquiv_gen T hτ hτ1 μ)
        (suspensionUnitEquiv_comp_flow_gen T hτ hτ1),
    Entropy.ksEntropy_prod_id_eq hT]

end UnitRoofFlow

end ErgodicTheory

/-! ## The symbolic factors -/

namespace ErgodicTheory.CatMapToral

open ErgodicTheory.Multifractal ErgodicTheory.Entropy ErgodicTheory.Krieger

/-- The **`1`-block source-merge code** `mergeSrc : BiShift (Fin 5) → BiShift (Fin 2)`,
`y ↦ (k ↦ src (y k))`: relabel each golden branch symbol by the golden rectangle it sits in. -/
def mergeSrc : BiShift (Fin 5) → BiShift (Fin 2) := fun y k => src (y k)

/-- The `1`-block merge is measurable (per-coordinate `src ∘ eval k`, `src` finite). -/
theorem measurable_mergeSrc : Measurable mergeSrc := by
  refine measurable_pi_iff.2 fun k => ?_
  exact (measurable_of_finite src).comp (measurable_pi_apply k)

/-- The `1`-block merge intertwines the two shifts exactly: `mergeSrc ∘ biShiftMap =
biShiftMap ∘ mergeSrc` (both send `y` to `k ↦ src (y (k+1))`). -/
theorem mergeSrc_equivariant (y : BiShift (Fin 5)) :
    mergeSrc (biShiftMap y) = biShiftMap (mergeSrc y) := rfl

/-- The **coarse (merged) itinerary** `coarseSymb x = (k ↦ src (awSymb x k))`: the two-symbol
Adler–Weiss coding, the `1`-block merge of the golden branch itinerary. -/
def coarseSymb : T2 → BiShift (Fin 2) := fun x k => src (awSymb x k)

/-- The coarse itinerary is the `1`-block merge of the full golden itinerary:
`coarseSymb = mergeSrc ∘ awSymbFull`. -/
theorem coarseSymb_eq_comp : coarseSymb = mergeSrc ∘ awSymbFull := rfl

/-- The coarse itinerary is measurable. -/
theorem measurable_coarseSymb : Measurable coarseSymb :=
  measurable_mergeSrc.comp measurable_awSymbFull

/-- **Exact equivariance of the coarse itinerary:** `coarseSymb (catTorus x) = biShiftMap
(coarseSymb x)`.  The `src`-merge of the shifted golden itinerary. -/
theorem coarseSymb_equivariant (x : T2) :
    coarseSymb (catTorus x) = biShiftMap (coarseSymb x) := by
  funext k
  change src (awSymb (catTorus x) k) = src (awSymb x (k + 1))
  rw [awSymb_shift]

/-! ### The three base factor maps -/

/-- **Stage-2 factor map (SFT₅ → 2-shift).**  The `1`-block merge is a factor map from the golden
image system `(BiShift (Fin 5), biShiftMap, awSymbFull_* volume)` onto the two-symbol image system
`(BiShift (Fin 2), biShiftMap, coarseSymb_* volume)`.  Its measure transport is `Measure.map_map`:
`mergeSrc_* (awSymbFull_* volume) = coarseSymb_* volume`. -/
theorem isFactorMap_mergeSrc :
    Entropy.IsFactorMap mergeSrc biShiftMap biShiftMap
      (Measure.map awSymbFull (volume : Measure T2))
      (Measure.map coarseSymb (volume : Measure T2)) := by
  refine ⟨⟨measurable_mergeSrc, ?_⟩, measurable_biShiftMap, funext mergeSrc_equivariant⟩
  rw [coarseSymb_eq_comp, ← Measure.map_map measurable_mergeSrc measurable_awSymbFull]

/-- **Composite factor map (cat → 2-shift).**  The coarse itinerary is a factor map from the cat-map
system `(T2, catTorus, volume)` onto the two-symbol image system. -/
theorem isFactorMap_coarseSymb :
    Entropy.IsFactorMap coarseSymb catTorus biShiftMap
      (volume : Measure T2) (Measure.map coarseSymb (volume : Measure T2)) :=
  ⟨⟨measurable_coarseSymb, rfl⟩, measurable_biShiftMap, funext coarseSymb_equivariant⟩

/-! ### Base measures and their shift-invariance -/

/-- The **golden `SFT₅` image measure** `awSymbFull_* volume` is a probability measure. -/
instance instIsProbabilityMeasure_mapAwSymbFull :
    IsProbabilityMeasure (Measure.map awSymbFull (volume : Measure T2)) :=
  Measure.isProbabilityMeasure_map measurable_awSymbFull.aemeasurable

/-- The **two-symbol image measure** `coarseSymb_* volume` is a probability measure. -/
instance instIsProbabilityMeasure_mapCoarseSymb :
    IsProbabilityMeasure (Measure.map coarseSymb (volume : Measure T2)) :=
  Measure.isProbabilityMeasure_map measurable_coarseSymb.aemeasurable

/-- The shift preserves the golden image measure (the pushforward of an invariant measure along a
factor is invariant). -/
theorem measurePreserving_biShiftEquiv_mapAwSymbFull :
    MeasurePreserving (⇑(biShiftEquiv (α₀ := Fin 5)))
      (Measure.map awSymbFull (volume : Measure T2))
      (Measure.map awSymbFull (volume : Measure T2)) :=
  measurePreserving_map_of_semiconj measurePreserving_catTorus measurable_awSymbFull
    biShiftEquiv.measurable (funext awSymbFull_equivariant)

/-- The shift preserves the two-symbol image measure. -/
theorem measurePreserving_biShiftEquiv_mapCoarseSymb :
    MeasurePreserving (⇑(biShiftEquiv (α₀ := Fin 2)))
      (Measure.map coarseSymb (volume : Measure T2))
      (Measure.map coarseSymb (volume : Measure T2)) :=
  measurePreserving_map_of_semiconj measurePreserving_catTorus measurable_coarseSymb
    biShiftEquiv.measurable (funext coarseSymb_equivariant)

/-! ### The merged base entropy: `= h(catTorus, coarseAWPartition) ≤ log 2` -/

/-- The pulled-back two-symbol coordinate partition coincides, cell by cell, with the coarse
Adler–Weiss partition: pulling `{y | y 0 = i}` back along `coarseSymb` gives
`{x | src (awSymb x 0) = i} = catProj '' awBox i` (`mem_coarse_iff` at time `0`, where the
zeroth iterate is the identity). -/
theorem coordPartitionZ_pulledBack_coarseSymb_cells :
    ((coordPartitionZ (Measure.map coarseSymb (volume : Measure T2))).pulledBack
        (isFactorMap_coarseSymb.1)).cells = coarseAWPartition.cells := by
  funext i
  ext x
  rw [MeasurePartition.pulledBack_cells]
  simp only [coordPartitionZ, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro h
    have := (mem_coarse_iff x 0 i).mpr (by simpa [coarseSymb] using h)
    rwa [Krieger.ziter_zero, id_eq] at this
  · intro h
    have hc := (mem_coarse_iff x 0 i).mp (by rwa [Krieger.ziter_zero, id_eq])
    simpa [coarseSymb] using hc

/-- **The merged (two-symbol) system entropy equals `h(catTorus, coarseAWPartition)`.**  The
coordinate partition two-sidedly generates the merged shift, so the generator theorem collapses
`h(merged)` to the partition entropy of the coordinate partition; the factor-relative invariance
carries it back through `coarseSymb` to the coarse Adler–Weiss partition on the cat map. -/
theorem ksEntropy_mapCoarseSymb_eq :
    Entropy.ksEntropy measurePreserving_biShiftEquiv_mapCoarseSymb
      = ((Entropy.ksEntropyPartition measurePreserving_catTorus coarseAWPartition : ℝ)
          : EReal) := by
  rw [Entropy.ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided
        biShiftEquiv measurePreserving_biShiftEquiv_mapCoarseSymb
        (coordPartitionZ (Measure.map coarseSymb (volume : Measure T2)))
        (coordPartitionZ_isGeneratingTwoSided_any _)]
  rw [EReal.coe_eq_coe_iff]
  rw [← Entropy.factor_relative_eq measurePreserving_catTorus
        measurePreserving_biShiftEquiv_mapCoarseSymb isFactorMap_coarseSymb.1
        (funext coarseSymb_equivariant) (coordPartitionZ _)]
  exact Entropy.ksEntropyPartition_congr_cells measurePreserving_catTorus _ _
    coordPartitionZ_pulledBack_coarseSymb_cells

/-- **The merged system sits strictly below the cat-map entropy.**
`h(merged) = h(catTorus, coarseAWPartition) ≤ log 2 < log((3 + √5)/2) = h(catTorus)`. -/
theorem ksEntropy_mapCoarseSymb_le :
    Entropy.ksEntropy measurePreserving_biShiftEquiv_mapCoarseSymb
      ≤ ((Real.log 2 : ℝ) : EReal) := by
  rw [ksEntropy_mapCoarseSymb_eq, EReal.coe_le_coe_iff]
  exact coarseAWPartition_ksEntropy_le

/-! ### The golden `SFT₅` image entropy: `= log((3 + √5)/2)` (the conjugacy stage) -/

/-- The pulled-back golden coordinate partition is the fine Adler–Weiss branch partition:
its cell at `e` is the branch cell `{x | awSymb x 0 = e} = awCell e.succ`. -/
theorem coordPartitionZ_pulledBack_awSymbFull_cells (e : Fin 5) (x : T2) :
    x ∈ ((coordPartitionZ (Measure.map awSymbFull (volume : Measure T2))).pulledBack
        (isFactorMap_awSymbFull.1)).cells e ↔ awSymb x 0 = e := by
  rw [MeasurePartition.pulledBack_cells]
  simp only [coordPartitionZ, Set.mem_preimage, Set.mem_setOf_eq, awSymbFull]

/-- **The fine golden itinerary partition two-sidedly generates for the cat map.**  Two points with
matching golden itineraries along the whole two-sided orbit are equal (`injective_awSymbFull`), so
the fine branch cells separate points; Blackwell's bridge upgrades this to two-sided generation. -/
theorem isGeneratingTwoSided_pulledBack_awSymbFull :
    IsGeneratingTwoSided catTorusEquiv
      ((coordPartitionZ (Measure.map awSymbFull (volume : Measure T2))).pulledBack
        (isFactorMap_awSymbFull.1)) := by
  refine isGeneratingTwoSided_of_separating catTorusEquiv _ (fun x y hxy => ?_)
  have hne : awSymbFull x ≠ awSymbFull y := fun h => hxy (injective_awSymbFull h)
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hne
  refine ⟨n, awSymb x n, ?_, ?_⟩
  · rw [coordPartitionZ_pulledBack_awSymbFull_cells]
    have h1 : Krieger.ziter catTorusEquiv 0 (Krieger.ziter catTorusEquiv n x)
        ∈ awCell (awSymb (Krieger.ziter catTorusEquiv n x) 0).succ :=
      awSymb_mem (Krieger.ziter catTorusEquiv n x) 0
    rw [Krieger.ziter_zero, id_eq] at h1
    exact (awSymb_eq_of_mem x n h1).symm
  · rw [coordPartitionZ_pulledBack_awSymbFull_cells]
    intro hcontra
    have h1 : Krieger.ziter catTorusEquiv 0 (Krieger.ziter catTorusEquiv n y)
        ∈ awCell (awSymb (Krieger.ziter catTorusEquiv n y) 0).succ :=
      awSymb_mem (Krieger.ziter catTorusEquiv n y) 0
    rw [Krieger.ziter_zero, id_eq] at h1
    exact hn ((awSymb_eq_of_mem y n h1).trans hcontra).symm

/-- **The golden `SFT₅` image system has the cat-map entropy** `log((3 + √5)/2)`.  The stage-1
Adler–Weiss coding is a measure conjugacy, so it preserves entropy: the coordinate partition
generates on the image while its cat-side pullback (the fine golden partition) generates on the cat
map, and factor-relative invariance identifies the two partition entropies with `h(catTorus)`. -/
theorem ksEntropy_mapAwSymbFull_eq :
    Entropy.ksEntropy measurePreserving_biShiftEquiv_mapAwSymbFull
      = ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal) := by
  rw [Entropy.ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided
        biShiftEquiv measurePreserving_biShiftEquiv_mapAwSymbFull
        (coordPartitionZ (Measure.map awSymbFull (volume : Measure T2)))
        (coordPartitionZ_isGeneratingTwoSided_any _),
    ← Entropy.factor_relative_eq measurePreserving_catTorusEquiv
        measurePreserving_biShiftEquiv_mapAwSymbFull isFactorMap_awSymbFull.1
        (funext awSymbFull_equivariant) (coordPartitionZ _),
    ← EReal.coe_eq_coe_iff.mpr rfl]
  have hgen := Entropy.ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided
    catTorusEquiv measurePreserving_catTorusEquiv
    ((coordPartitionZ (Measure.map awSymbFull (volume : Measure T2))).pulledBack
      (isFactorMap_awSymbFull.1))
    isGeneratingTwoSided_pulledBack_awSymbFull
  rw [← hgen]
  exact catTorus_ksEntropy_eq

/-! ## The two suspension-flow factor maps and the strict flow-entropy drop -/

/-- The stage-`2` measure transport `mergeSrc_* (awSymbFull_* volume) = coarseSymb_* volume`. -/
theorem map_mergeSrc_mapAwSymbFull :
    Measure.map mergeSrc (Measure.map awSymbFull (volume : Measure T2))
      = Measure.map coarseSymb (volume : Measure T2) := by
  rw [coarseSymb_eq_comp]
  exact Measure.map_map measurable_mergeSrc measurable_awSymbFull

/-- The three unit-roof suspension probability measures. -/
local instance instProbSuspX : IsProbabilityMeasure
    (suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2)) :=
  isProbabilityMeasure_suspensionMeasure_unit catTorusEquiv measurable_catRoof rfl volume

local instance instProbSuspY : IsProbabilityMeasure
    (suspensionMeasure biShiftEquiv (measurable_oneRoof (α₀ := Fin 5))
      (Measure.map awSymbFull (volume : Measure T2))) :=
  isProbabilityMeasure_suspensionMeasure_unit biShiftEquiv measurable_oneRoof rfl _

local instance instProbSuspZ : IsProbabilityMeasure
    (suspensionMeasure biShiftEquiv (measurable_oneRoof (α₀ := Fin 2))
      (Measure.map coarseSymb (volume : Measure T2))) :=
  isProbabilityMeasure_suspensionMeasure_unit biShiftEquiv measurable_oneRoof rfl _

/-- The Adler–Weiss coding intertwines the base automorphisms as `MeasurableEquiv`s. -/
theorem hsemiconj_awSymbFull (x : T2) :
    awSymbFull (catTorusEquiv x) = biShiftEquiv (awSymbFull x) := by
  rw [catTorusEquiv_apply, biShiftEquiv_apply]; exact awSymbFull_equivariant x

/-- The `1`-block merge intertwines the shift with itself as a `MeasurableEquiv`. -/
theorem hsemiconj_mergeSrc (y : BiShift (Fin 5)) :
    mergeSrc (biShiftEquiv y) = biShiftEquiv (mergeSrc y) := by
  rw [biShiftEquiv_apply, biShiftEquiv_apply]; exact mergeSrc_equivariant y

/-- **Stage-1 suspension-flow factor map** (cat suspension → golden `SFT₅` suspension), the descent
of the Adler–Weiss coding to the mapping-torus flows (unit roofs). -/
noncomputable def flowFactor1 :
    SuspensionSpace catTorusEquiv measurable_catRoof
      → SuspensionSpace biShiftEquiv (measurable_oneRoof (α₀ := Fin 5)) :=
  suspensionFactorMap catTorusEquiv biShiftEquiv measurable_catRoof measurable_oneRoof rfl rfl
    awSymbFull hsemiconj_awSymbFull

/-- **Stage-2 suspension-flow factor map** (golden `SFT₅` suspension → two-symbol suspension), the
descent of the `1`-block source merge to the flows. -/
noncomputable def flowFactor2 :
    SuspensionSpace biShiftEquiv (measurable_oneRoof (α₀ := Fin 5))
      → SuspensionSpace biShiftEquiv (measurable_oneRoof (α₀ := Fin 2)) :=
  suspensionFactorMap biShiftEquiv biShiftEquiv measurable_oneRoof measurable_oneRoof rfl rfl
    mergeSrc hsemiconj_mergeSrc

/-- Stage 1 is an `Entropy.IsFactorMap` of the two time-`1` suspension-flow maps. -/
theorem isFactorMap_flowFactor1 :
    Entropy.IsFactorMap flowFactor1 (suspensionFlowMap catTorusEquiv measurable_catRoof 1)
      (suspensionFlowMap biShiftEquiv measurable_oneRoof 1)
      (suspensionMeasure catTorusEquiv measurable_catRoof volume)
      (suspensionMeasure biShiftEquiv measurable_oneRoof
        (Measure.map awSymbFull (volume : Measure T2))) :=
  isFactorMap_suspensionFactorMap catTorusEquiv biShiftEquiv measurable_catRoof measurable_oneRoof
    rfl rfl awSymbFull measurable_awSymbFull hsemiconj_awSymbFull

/-- **Stage 1 is injective** — the conjugacy stage.  Injectivity of the Adler–Weiss coding lifts to
the suspension flows. -/
theorem injective_flowFactor1 : Function.Injective flowFactor1 :=
  injective_suspensionFactorMap catTorusEquiv biShiftEquiv measurable_catRoof measurable_oneRoof
    rfl rfl awSymbFull hsemiconj_awSymbFull injective_awSymbFull

/-- Stage 2 is an `Entropy.IsFactorMap` of the two time-`1` suspension-flow maps. -/
theorem isFactorMap_flowFactor2 :
    Entropy.IsFactorMap flowFactor2 (suspensionFlowMap biShiftEquiv measurable_oneRoof 1)
      (suspensionFlowMap biShiftEquiv measurable_oneRoof 1)
      (suspensionMeasure biShiftEquiv measurable_oneRoof
        (Measure.map awSymbFull (volume : Measure T2)))
      (suspensionMeasure biShiftEquiv measurable_oneRoof
        (Measure.map coarseSymb (volume : Measure T2))) := by
  have h := isFactorMap_suspensionFactorMap biShiftEquiv biShiftEquiv measurable_oneRoof
    measurable_oneRoof rfl rfl mergeSrc measurable_mergeSrc hsemiconj_mergeSrc
    (μ := Measure.map awSymbFull (volume : Measure T2))
  rwa [map_mergeSrc_mapAwSymbFull] at h

/-! ### The flow-entropy pins -/

/-- **Cat-suspension flow entropy** (`h(ζ^{cat}_1) = log((3 + √5)/2)`).  The unit-roof time-`1`
descent carries the cat-map base entropy to the flow. -/
theorem ksEntropy_catSuspFlow :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap catTorusEquiv measurable_catRoof
        measurePreserving_catTorusEquiv catRoof_ge_one one_pos 1)
      = ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal) := by
  rw [ksEntropy_suspensionFlowMap_unitRoof_one catTorusEquiv measurable_catRoof rfl
    measurePreserving_catTorusEquiv catRoof_ge_one]
  exact catTorus_ksEntropy_eq

/-- **Golden `SFT₅`-suspension flow entropy** (`= log((3 + √5)/2)`, the conjugacy stage preserving
entropy).  The unit-roof time-`1` descent carries the `SFT₅` base entropy to the flow. -/
theorem ksEntropy_sft5SuspFlow :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
        (measurable_oneRoof (α₀ := Fin 5)) measurePreserving_biShiftEquiv_mapAwSymbFull
        oneRoof_le one_pos 1)
      = ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal) := by
  rw [ksEntropy_suspensionFlowMap_unitRoof_one biShiftEquiv measurable_oneRoof rfl
    measurePreserving_biShiftEquiv_mapAwSymbFull oneRoof_le]
  exact ksEntropy_mapAwSymbFull_eq

/-- **Two-symbol-suspension flow entropy ceiling** (`≤ log 2`, the strict-drop lumping stage). -/
theorem ksEntropy_twoSymbolSuspFlow_le :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
        (measurable_oneRoof (α₀ := Fin 2)) measurePreserving_biShiftEquiv_mapCoarseSymb
        oneRoof_le one_pos 1)
      ≤ ((Real.log 2 : ℝ) : EReal) := by
  rw [ksEntropy_suspensionFlowMap_unitRoof_one biShiftEquiv measurable_oneRoof rfl
    measurePreserving_biShiftEquiv_mapCoarseSymb oneRoof_le]
  exact ksEntropy_mapCoarseSymb_le

/-- **The strict flow-entropy drop of the lumping stage:**
`h(ζ²_1) ≤ log 2 < log((3 + √5)/2) = h(ζ^{cat}_1)`. -/
theorem ksEntropy_twoSymbolSuspFlow_lt_catSuspFlow :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
        (measurable_oneRoof (α₀ := Fin 2)) measurePreserving_biShiftEquiv_mapCoarseSymb
        oneRoof_le one_pos 1)
      < Entropy.ksEntropy (measurePreserving_suspensionFlowMap catTorusEquiv measurable_catRoof
        measurePreserving_catTorusEquiv catRoof_ge_one one_pos 1) := by
  rw [ksEntropy_catSuspFlow]
  refine lt_of_le_of_lt ksEntropy_twoSymbolSuspFlow_le ?_
  rw [EReal.coe_lt_coe_iff]
  exact log_two_lt_log_lam

/-- **The depth-two symbolic flow tower on the cat lineage.**  Packaged: stages `1` and `2` are
both `Entropy.IsFactorMap`s of the time-`1` flow maps; stage 1 is injective (the conjugacy
stage); and the lumping stage `2` has a strict flow-entropy drop
`h(ζ²_1) < h(ζ^{cat}_1) = log((3 + √5)/2)`. -/
theorem catSymbolicFlowTower :
    Entropy.IsFactorMap flowFactor1 (suspensionFlowMap catTorusEquiv measurable_catRoof 1)
        (suspensionFlowMap biShiftEquiv measurable_oneRoof 1)
        (suspensionMeasure catTorusEquiv measurable_catRoof volume)
        (suspensionMeasure biShiftEquiv measurable_oneRoof
          (Measure.map awSymbFull (volume : Measure T2)))
      ∧ Function.Injective flowFactor1
      ∧ Entropy.IsFactorMap flowFactor2 (suspensionFlowMap biShiftEquiv measurable_oneRoof 1)
        (suspensionFlowMap biShiftEquiv measurable_oneRoof 1)
        (suspensionMeasure biShiftEquiv measurable_oneRoof
          (Measure.map awSymbFull (volume : Measure T2)))
        (suspensionMeasure biShiftEquiv measurable_oneRoof
          (Measure.map coarseSymb (volume : Measure T2)))
      ∧ Entropy.ksEntropy (measurePreserving_suspensionFlowMap biShiftEquiv
          (measurable_oneRoof (α₀ := Fin 2)) measurePreserving_biShiftEquiv_mapCoarseSymb
          oneRoof_le one_pos 1)
        < Entropy.ksEntropy (measurePreserving_suspensionFlowMap catTorusEquiv measurable_catRoof
          measurePreserving_catTorusEquiv catRoof_ge_one one_pos 1) :=
  ⟨isFactorMap_flowFactor1, injective_flowFactor1, isFactorMap_flowFactor2,
    ksEntropy_twoSymbolSuspFlow_lt_catSuspFlow⟩

end ErgodicTheory.CatMapToral

end
