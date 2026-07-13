/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapAdlerWeissGenerator
import ErgodicTheory.Multifractal.BernoulliTwoSided
import ErgodicTheory.Entropy.FactorMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The Adler–Weiss coding as a measure-theoretic factor and a conjugacy onto its range

This module upgrades the *geometry* of the Adler–Weiss Markov partition (Adler–Weiss,
*Similarity of automorphisms of the torus*, Memoirs AMS **98**, 1970; see also Adler,
*Symbolic dynamics and Markov partitions*, Bull. AMS **35** (1998), 1–56) into two structural
results about the Arnold cat map `catTorus` on the sup-metric torus `T2`:

* **Tier 1 — a genuine factor map.**  The two-sided Adler–Weiss itinerary
  `awSymbFull : T2 → BiShift (Fin 5)`, `awSymbFull x k = awSymb x k`, is a
  `Entropy.IsFactorMap` from `(T2, catTorus, volume)` onto the two-sided full shift
  `(BiShift (Fin 5), biShiftMap, Measure.map awSymbFull volume)`.  The intertwining is an
  **exact** (everywhere, not merely a.e.) equality `awSymbFull ∘ catTorus = biShiftMap ∘ awSymbFull`
  — this is possible only because the repo's *half-open* golden tiling has an empty (not merely
  null) junk cell, so every point has a well-defined symbol at every time.  The pushforward
  concentrates on the golden subshift of finite type: `map_awSymbFull_biSFTCarrier` shows the
  admissible-sequence carrier `biSFTCarrier awM` has full measure `1`.

* **Tier 2 — full injectivity and a conjugacy onto the range.**  Because matching two-sided
  itineraries force equality of points (`eq_of_matching_awCells`, the contraction estimate), the
  coding `awSymbFull` is **injective** on the nose — again no boundary null set is discarded.  It is
  therefore a `MeasurableEmbedding` (`Measurable.measurableEmbedding`, `T2` standard Borel), and the
  induced measurable equivalence onto its range `awSymbEquivRange : T2 ≃ᵐ Set.range awSymbFull` is
  **measure preserving** from `volume` to the pushforward measure comapped to the range,
  `(Measure.map awSymbFull volume).comap Subtype.val` (`measurePreserving_awSymbEquivRange`).

The pushforward `Measure.map awSymbFull volume` is the Markov measure of the golden Adler–Weiss
data; identifying its cylinder values with the explicit golden transition probabilities is a
follow-up (the factor map and the conjugacy onto the range are complete without it).

`awM` is the `5×5` golden admissibility matrix (`awM e e' = decide (tgt e = src e')`), and
`biSFTCarrier M` is the carrier of the two-sided subshift of finite type it defines.
-/

open MeasureTheory Function
open scoped ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
imported cat-map measure modules so that `volume : Measure T2` lines up. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_awFactor :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_awFactor :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_awFactor :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory

open ErgodicTheory.Multifractal

/-- The **carrier of the two-sided subshift of finite type** defined by a `k × k` Boolean
transition matrix `M`: the bi-infinite sequences all of whose consecutive coordinate pairs are
`M`-admissible. -/
def biSFTCarrier {k : ℕ} (M : Fin k → Fin k → Bool) : Set (BiShift (Fin k)) :=
  {x | ∀ i : ℤ, M (x i) (x (i + 1)) = true}

/-- The subshift-of-finite-type carrier is measurable: it is a countable intersection over `i : ℤ`
of the preimages of a (finite, hence measurable) admissible-pair set under the measurable
coordinate-pair map `x ↦ (x i, x (i+1))`. -/
theorem measurableSet_biSFTCarrier {k : ℕ} (M : Fin k → Fin k → Bool) :
    MeasurableSet (biSFTCarrier M) := by
  rw [biSFTCarrier, Set.setOf_forall]
  refine MeasurableSet.iInter fun i => ?_
  have hpair : Measurable (fun x : BiShift (Fin k) => (x i, x (i + 1))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1))
  exact hpair (Set.toFinite {p : Fin k × Fin k | M p.1 p.2 = true}).measurableSet

end ErgodicTheory

namespace ErgodicTheory.CatMapToral

open ErgodicTheory.Multifractal

/-! ## The golden admissibility matrix -/

/-- The `5 × 5` **golden Adler–Weiss transition matrix**: branch `e` may be followed by branch `e'`
exactly when the target rectangle of `e` is the source rectangle of `e'`. -/
def awM : Fin 5 → Fin 5 → Bool := fun e e' => decide (tgt e = src e')

/-! ## Uniqueness of the Adler–Weiss symbol -/

/-- The Adler–Weiss symbol is the **unique** branch whose projected cell contains the orbit point:
if `ziter catTorusEquiv k x` lies in `awCell e.succ`, then `awSymb x k = e`.  Two distinct branch
cells are disjoint, so the symbol's own cell (`awSymb_mem`) forces `e`. -/
lemma awSymb_eq_of_mem (x : T2) (k : ℤ) {e : Fin 5}
    (h : Krieger.ziter catTorusEquiv k x ∈ awCell e.succ) : awSymb x k = e := by
  by_contra hne
  have hm := awSymb_mem x k
  rw [awCell_succ] at hm h
  exact Set.disjoint_left.mp (disjoint_catProj_image_branchBox hne) hm h

/-- Characterisation of the Adler–Weiss symbol by cell membership. -/
lemma awSymb_eq_iff (x : T2) (k : ℤ) (e : Fin 5) :
    awSymb x k = e ↔ Krieger.ziter catTorusEquiv k x ∈ awCell e.succ := by
  constructor
  · rintro rfl; exact awSymb_mem x k
  · exact awSymb_eq_of_mem x k

/-! ## The full two-sided itinerary and its measurability -/

/-- The **full two-sided Adler–Weiss itinerary** of `x`: the bi-infinite sequence of branch symbols
`k ↦ awSymb x k`. -/
noncomputable def awSymbFull : T2 → BiShift (Fin 5) := fun x k => awSymb x k

/-- Each coordinate `x ↦ awSymb x k` of the itinerary is measurable: over a finite alphabet the
preimage of `{e}` is `(ziter catTorusEquiv k)⁻¹' (awCell e.succ)`, a measurable set. -/
lemma measurable_awSymb_coord (k : ℤ) : Measurable (fun x : T2 => awSymb x k) := by
  refine measurable_to_countable' fun e => ?_
  have hpre : (fun x : T2 => awSymb x k) ⁻¹' {e}
      = Krieger.ziter catTorusEquiv k ⁻¹' awCell e.succ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact awSymb_eq_iff x k e
  rw [hpre, awCell_succ]
  exact Krieger.measurable_ziter catTorusEquiv k (measurableSet_catProj_image_branchBox e)

/-- The full itinerary map `awSymbFull` is measurable (measurable in each coordinate). -/
theorem measurable_awSymbFull : Measurable awSymbFull := by
  rw [measurable_pi_iff]
  exact fun k => measurable_awSymb_coord k

/-! ## Exact equivariance -/

/-- **Exact one-step equivariance of the symbol.**  `awSymb (catTorus x) k = awSymb x (k+1)`: one
dynamical step relabels the time index, since `ziter catTorusEquiv (k+1) x = ziter k (catTorus x)`.
This is an *everywhere* identity — the half-open tiling leaves no boundary exceptions. -/
lemma awSymb_shift (x : T2) (k : ℤ) : awSymb (catTorus x) k = awSymb x (k + 1) := by
  refine awSymb_eq_of_mem (catTorus x) k ?_
  have hz : Krieger.ziter catTorusEquiv (k + 1) x
      = Krieger.ziter catTorusEquiv k (catTorus x) := by
    rw [Krieger.ziter_add, Function.comp_apply, Krieger.ziter_one, catTorusEquiv_apply]
  rw [← hz]
  exact awSymb_mem x (k + 1)

/-- **The itinerary intertwines the dynamics exactly:**
`awSymbFull (catTorus x) = biShiftMap (awSymbFull x)`. -/
theorem awSymbFull_equivariant (x : T2) :
    awSymbFull (catTorus x) = biShiftMap (awSymbFull x) := by
  funext k
  change awSymb (catTorus x) k = awSymb x (k + 1)
  exact awSymb_shift x k

/-! ## The itinerary lands in the golden subshift of finite type -/

/-- Every itinerary is **admissible**: `awSymbFull x` lies in the golden SFT carrier. -/
theorem awSymbFull_mem_biSFTCarrier (x : T2) : awSymbFull x ∈ biSFTCarrier awM := fun i => by
  simpa only [awM, decide_eq_true_eq] using awSymb_admissible x i

/-- The itinerary map lands entirely in the golden SFT carrier. -/
theorem preimage_biSFTCarrier_eq_univ : awSymbFull ⁻¹' biSFTCarrier awM = Set.univ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ, iff_true]
  exact awSymbFull_mem_biSFTCarrier x

/-! ## Tier 1: the factor map -/

/-- **Tier-1 headline.**  The Adler–Weiss itinerary is a *factor map* from the cat-map system
`(T2, catTorus, volume)` onto the two-sided full shift `(BiShift (Fin 5), biShiftMap)` equipped
with the pushforward measure.  The intertwining is exact everywhere. -/
theorem isFactorMap_awSymbFull :
    Entropy.IsFactorMap awSymbFull catTorus biShiftMap
      (volume : Measure T2) (Measure.map awSymbFull volume) :=
  ⟨⟨measurable_awSymbFull, rfl⟩, measurable_biShiftMap, funext awSymbFull_equivariant⟩

/-- **Carrier full-measure upgrade.**  The pushforward measure is carried by the golden subshift of
finite type: `(Measure.map awSymbFull volume) (biSFTCarrier awM) = 1`.  Indeed the whole torus maps
into the carrier, and `volume` is a probability measure. -/
theorem map_awSymbFull_biSFTCarrier :
    (Measure.map awSymbFull volume) (biSFTCarrier awM) = 1 := by
  rw [Measure.map_apply measurable_awSymbFull (measurableSet_biSFTCarrier awM),
    preimage_biSFTCarrier_eq_univ, measure_univ]

/-! ## Tier 2: injectivity and the conjugacy onto the range -/

/-- **The coding is injective on the nose.**  Two points with the same full itinerary share every
Adler–Weiss cell along the two-sided orbit, so `eq_of_matching_awCells` (the contraction estimate)
forces them equal.  No boundary null set is discarded — the injectivity is exact. -/
theorem injective_awSymbFull : Function.Injective awSymbFull := by
  intro x y hxy
  refine eq_of_matching_awCells (fun k e hxe => ?_)
  have hfun : ∀ j : ℤ, awSymb x j = awSymb y j := fun j => congrFun hxy j
  have hx : awSymb x k = e := awSymb_eq_of_mem x k hxe
  exact (awSymb_eq_iff y k e).mp ((hfun k).symm.trans hx)

/-- **Tier-2 headline.**  The exactly-injective, measurable itinerary from the standard Borel torus
into the countably separated shift space is a `MeasurableEmbedding`. -/
theorem measurableEmbedding_awSymbFull : MeasurableEmbedding awSymbFull :=
  measurable_awSymbFull.measurableEmbedding injective_awSymbFull

/-- The induced **measurable equivalence onto the range** of the Adler–Weiss coding. -/
noncomputable def awSymbEquivRange : T2 ≃ᵐ Set.range awSymbFull :=
  measurableEmbedding_awSymbFull.equivRange

/-- **The conjugacy onto the range is measure preserving.**  The equivalence `awSymbEquivRange`
carries `volume` on `T2` to the pushforward measure comapped to the range,
`(Measure.map awSymbFull volume).comap Subtype.val`.  Together with `isFactorMap_awSymbFull` and
`map_awSymbFull_biSFTCarrier`, this packages the Adler–Weiss coding as a measurable isomorphism of
`(T2, volume)` onto its (full-measure, golden-SFT) image. -/
theorem measurePreserving_awSymbEquivRange :
    MeasurePreserving awSymbEquivRange (volume : Measure T2)
      ((Measure.map awSymbFull volume).comap Subtype.val) := by
  have hsub : MeasurableEmbedding (Subtype.val : Set.range awSymbFull → BiShift (Fin 5)) :=
    MeasurableEmbedding.subtype_coe measurableEmbedding_awSymbFull.measurableSet_range
  have hcomp : (Subtype.val : Set.range awSymbFull → BiShift (Fin 5)) ∘ awSymbEquivRange
      = awSymbFull := by
    funext x
    exact congrArg Subtype.val
      (MeasurableEmbedding.equivRange_apply measurableEmbedding_awSymbFull x)
  refine ⟨awSymbEquivRange.measurable, ?_⟩
  have hmap : Measure.map (Subtype.val : Set.range awSymbFull → BiShift (Fin 5))
      (Measure.map awSymbEquivRange volume) = Measure.map awSymbFull volume := by
    rw [Measure.map_map hsub.measurable awSymbEquivRange.measurable, hcomp]
  rw [← hmap]
  exact (hsub.comap_map (Measure.map awSymbEquivRange volume)).symm

end ErgodicTheory.CatMapToral
