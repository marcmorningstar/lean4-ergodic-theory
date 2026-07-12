/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapCover
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Measure toolkit for the cat-map cover projection

This module supplies the **measure-theoretic toolkit** for the universal-cover projection
`catProj : (Fin 2 → ℝ) → T2` of the Arnold cat map (see
`ErgodicTheory.Examples.CatMapCover`), where `T2 = UnitAddTorus (Fin 2) = Fin 2 → UnitAddCircle`
carries the product Haar probability measure `volume` (with `UnitAddCircle` normalised to
`AddCircle.haarAddCircle`, matching the Fourier convention of `CatMapToral`).

The projection reduces each real coordinate modulo `1`; restricted to a unit box
`boxIoc m = ∏ᵢ Ioc (mᵢ) (mᵢ + 1)` it is a measure-preserving bijection onto `T2`.  We record:

* `measurePreserving_catProj_restrict` — `catProj` is measure-preserving from
  `volume.restrict (boxIoc m)` onto `volume` (assembled from `measurePreserving_pi` and
  `UnitAddCircle.measurePreserving_mk`);
* `measurableSet_catProj_image_of_subset_box` — the image of a measurable subset of a box is
  measurable (through the chart `UnitAddTorus.measurableEquivPiIoc`);
* `volume_catProj_image_of_subset_box` — the per-tile measure identity
  `volume (catProj '' D) = volume D` for measurable `D ⊆ boxIoc 0`;
* `volume_catProj_image_inter_box` — the translated per-tile identity for `K ∩ boxIoc m`;
* `catProj_image_volume_le` — **the export**: `volume (catProj '' K) ≤ volume K` for compact `K`,
  by covering `K` with the integer tiling `⋃ₘ boxIoc m`.

The interval convention is uniformly **`Ioc`** (half-open on the right), matching
`AddCircle.measurePreserving_mk`, `UnitAddTorus.measurableEquivPiIoc`, and `iUnion_Ioc_intCast`.
-/

open MeasureTheory UnitAddTorus Matrix

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching
`ErgodicTheory.Examples.CatMapToral`: with this `MeasureSpace` instance, `volume` on
`UnitAddTorus (Fin 2)` is the product Haar probability measure on `𝕋²`. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_covMeas :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_covMeas :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_covMeas :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## The measure bridge on the circle and torus -/

/-- `volume` on `T2` is a probability measure (product of probability measures). -/
instance instIsProbabilityMeasureVolumeT2 : IsProbabilityMeasure (volume : Measure T2) :=
  inferInstance

/-- **Translation invariance workhorse** on `Fin 2 → ℝ`: translating a set by a constant vector
preserves its Lebesgue measure. -/
theorem volume_addLeft_image (t : Fin 2 → ℝ) (S : Set (Fin 2 → ℝ)) :
    volume ((fun x => t + x) '' S) = volume S := by
  rw [Set.image_add_left, measure_preimage_add]

/-! ## The unit boxes -/

/-- The half-open unit box anchored at the integer vector `m`:
`boxIoc m = ∏ᵢ Ioc (mᵢ) (mᵢ + 1)`. -/
def boxIoc (m : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  Set.univ.pi fun i => Set.Ioc ((m i : ℝ)) ((m i : ℝ) + 1)

/-- Each box is measurable. -/
theorem measurableSet_boxIoc (m : Fin 2 → ℤ) : MeasurableSet (boxIoc m) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- **Every real vector lies in some integer box.** -/
theorem exists_boxIoc_mem (x : Fin 2 → ℝ) : ∃ m : Fin 2 → ℤ, x ∈ boxIoc m := by
  have hcov : ∀ i, ∃ n : ℤ, x i ∈ Set.Ioc (n : ℝ) (n + 1) := by
    intro i
    have hx : x i ∈ ⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1) := by
      rw [iUnion_Ioc_intCast]; exact Set.mem_univ _
    exact Set.mem_iUnion.1 hx
  choose m hm using hcov
  exact ⟨m, Set.mem_univ_pi.2 hm⟩

/-- The integer tiling covers everything. -/
theorem iUnion_boxIoc : (⋃ m : Fin 2 → ℤ, boxIoc m) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨m, hm⟩ := exists_boxIoc_mem x
  exact Set.mem_iUnion.2 ⟨m, hm⟩

/-- Distinct boxes are disjoint. -/
theorem pairwise_disjoint_boxIoc :
    Pairwise (Function.onFun Disjoint boxIoc) := by
  intro m m' hmm
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ m' i := Function.ne_iff.1 hmm
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  obtain ⟨h1a, h1b⟩ := (Set.mem_univ_pi.1 hx) i
  obtain ⟨h2a, h2b⟩ := (Set.mem_univ_pi.1 hx') i
  have e1 : (m i : ℝ) < (m' i : ℝ) + 1 := lt_of_lt_of_le h1a h2b
  have e2 : (m' i : ℝ) < (m i : ℝ) + 1 := lt_of_lt_of_le h2a h1b
  have f1 : m i < m' i + 1 := by exact_mod_cast e1
  have f2 : m' i < m i + 1 := by exact_mod_cast e2
  omega

/-! ## Measurability of `catProj` and the measure-preserving restriction -/

/-- `catProj` is measurable. -/
theorem measurable_catProj : Measurable (catProj : (Fin 2 → ℝ) → T2) := by
  apply measurable_pi_iff.2
  intro i
  exact AddCircle.measurable_mk'.comp (measurable_pi_apply i)

/-- The base set of the chart's subtype: the closed-open unit cube anchored at `0`.  It coincides
with `boxIoc 0`. -/
theorem boxIoc_zero_eq_setOf :
    boxIoc 0 = {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)} := by
  ext x
  simp only [boxIoc, Set.mem_univ_pi, Set.mem_setOf_eq, Pi.zero_apply, Int.cast_zero]

/-! ## The chart identification and image measurability

On `boxIoc 0` the projection `catProj` is exactly the inverse of the measurable, measure-preserving
chart `UnitAddTorus.measurableEquivPiIoc 0 : T2 ≃ᵐ {x // ∀ i, x i ∈ Ioc 0 1}`.  Because Mathlib's
`measurableEquivPiIoc` is stated with the very same `⟨AddCircle.haarAddCircle⟩` normalisation used
here, its measure-preservation transfers directly (avoiding the incompatible *default* AddCircle
`volume`, which is `1 • haar`, not `haar`). -/

/-- **Chart identification.**  For `D ⊆ boxIoc 0`, `catProj '' D` is the chart image of `D`. -/
theorem catProj_image_eq_symm_image {D : Set (Fin 2 → ℝ)} (hsub : D ⊆ boxIoc 0) :
    catProj '' D
      = (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))).symm ''
          (Subtype.val ⁻¹' D) := by
  ext p
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨x, hxD, rfl⟩
    refine ⟨⟨x, ?_⟩, hxD, rfl⟩
    intro i; simpa using (Set.mem_univ_pi.1 (hsub hxD)) i
  · rintro ⟨y, hyD, rfl⟩
    exact ⟨y.1, hyD, rfl⟩

/-- **The image of a measurable subset of a box is measurable.** -/
theorem measurableSet_catProj_image_of_subset_box {D : Set (Fin 2 → ℝ)} (hD : MeasurableSet D)
    (hsub : D ⊆ boxIoc 0) : MeasurableSet (catProj '' D) := by
  rw [catProj_image_eq_symm_image hsub]
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))).symm.measurableEmbedding
    |>.measurableSet_image.2 (measurable_subtype_coe hD)

/-! ## The per-tile measure identities -/

/-- **Per-tile measure identity.**  For measurable `D ⊆ boxIoc 0`, the projection preserves the
measure: `volume (catProj '' D) = volume D`.  Transported from the measure-preserving chart
`measurePreserving_equivPiIoc` (`Measure.comap_subtype_coe_apply` unfolds the subtype measure). -/
theorem volume_catProj_image_of_subset_box {D : Set (Fin 2 → ℝ)}
    (hsub : D ⊆ boxIoc 0) : (volume : Measure T2) (catProj '' D) = volume D := by
  set E := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ)) with hE
  have MPE : MeasurePreserving E.symm (Measure.comap Subtype.val volume) (volume : Measure T2) :=
    (UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin 2 => (0 : ℝ))).symm
  have hsmeas : MeasurableSet {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)} := by
    rw [← boxIoc_zero_eq_setOf]; exact measurableSet_boxIoc 0
  rw [catProj_image_eq_symm_image hsub, ← MPE.map_eq, MeasurableEquiv.map_apply,
    Set.preimage_image_eq _ E.symm.injective]
  have hDs : D ⊆ {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)} := by
    rw [← boxIoc_zero_eq_setOf]; exact hsub
  have hcs := comap_subtype_coe_apply hsmeas volume (Subtype.val ⁻¹' D)
  rw [Subtype.image_preimage_val, Set.inter_eq_right.2 hDs] at hcs
  exact hcs

/-- **Shift a tile into `boxIoc 0`.**  For measurable `K` and any integer box `boxIoc m`,
translating `K ∩ boxIoc m` by the integer vector `-m` yields a measurable set `D ⊆ boxIoc 0` with
the *same*
projection (the shift is invisible to `catProj`) and the *same* volume (translation invariance).
This is the shared construction behind both the measurability and the volume per-tile identities. -/
theorem exists_shift_into_boxIoc_zero {K : Set (Fin 2 → ℝ)} (hK : MeasurableSet K)
    (m : Fin 2 → ℤ) :
    ∃ D : Set (Fin 2 → ℝ), MeasurableSet D ∧ D ⊆ boxIoc 0 ∧
      catProj '' D = catProj '' (K ∩ boxIoc m) ∧ volume D = volume (K ∩ boxIoc m) := by
  set t : Fin 2 → ℝ := fun i => (-(m i) : ℝ) with ht
  set S : Set (Fin 2 → ℝ) := K ∩ boxIoc m with hS
  -- `catProj` is invariant under the integer shift by `t`.
  have hcomp : ∀ x : Fin 2 → ℝ, catProj (t + x) = catProj x := by
    intro x; funext i
    simp only [catProj, Pi.add_apply, AddCircle.coe_add]
    have ht0 : ((t i : ℝ) : UnitAddCircle) = 0 := by
      rw [ht, show ((fun i => (-(m i) : ℝ)) i : ℝ) = (((-(m i)) : ℤ) : ℝ) by push_cast; ring]
      exact coe_intCast_eq_zero (-(m i))
    rw [ht0, zero_add]
  refine ⟨(fun x => t + x) '' S, ?_, ?_, ?_, ?_⟩
  · -- Measurable, as the homeomorphic image of a measurable set.
    exact (Homeomorph.addLeft t).measurableEmbedding.measurableSet_image.2
      (hK.inter (measurableSet_boxIoc m))
  · -- The shifted tile lands in `boxIoc 0`.
    rintro y ⟨x, hxS, rfl⟩
    rw [boxIoc, Set.mem_univ_pi]
    intro i
    obtain ⟨h1, h2⟩ := (Set.mem_univ_pi.1 hxS.2) i
    refine ⟨?_, ?_⟩
    · simp only [ht, Pi.add_apply, Pi.zero_apply, Int.cast_zero]; linarith
    · simp only [ht, Pi.add_apply, Pi.zero_apply, Int.cast_zero]; linarith
  · -- Image of the shifted tile equals image of the tile.
    rw [← Set.image_comp]; exact Set.image_congr' hcomp
  · -- Equal volume, by translation invariance.
    exact volume_addLeft_image t S

/-- **Per-tile image measurability (translated).**  For measurable `K` and any integer box, the
projected slice `catProj '' (K ∩ boxIoc m)` is measurable: shift the tile into `boxIoc 0`, where the
chart identifies the image. -/
theorem measurableSet_catProj_image_inter_box {K : Set (Fin 2 → ℝ)} (hK : MeasurableSet K)
    (m : Fin 2 → ℤ) : MeasurableSet (catProj '' (K ∩ boxIoc m)) := by
  obtain ⟨D, hDmeas, hDsub, himg, _⟩ := exists_shift_into_boxIoc_zero hK m
  rw [← himg]
  exact measurableSet_catProj_image_of_subset_box hDmeas hDsub

/-- **Translated per-tile identity.**  For measurable `K`, projecting `K ∩ boxIoc m` preserves the
measure.  Shift the tile into `boxIoc 0` (an integer shift, invisible to `catProj` and volume-
preserving) and apply the `boxIoc 0` identity. -/
theorem volume_catProj_image_inter_box {K : Set (Fin 2 → ℝ)} (hK : MeasurableSet K)
    (m : Fin 2 → ℤ) :
    (volume : Measure T2) (catProj '' (K ∩ boxIoc m)) = volume (K ∩ boxIoc m) := by
  obtain ⟨D, _, hDsub, himg, hvol⟩ := exists_shift_into_boxIoc_zero hK m
  rw [← himg, volume_catProj_image_of_subset_box hDsub]
  exact hvol

/-! ## The export -/

/-- **The export.**  The projection cannot increase measure: for any compact `K ⊆ Fin 2 → ℝ`,
`volume (catProj '' K) ≤ volume K`.  Cover `K` by the integer tiling `⋃ₘ boxIoc m`, project each
tile with the exact per-tile identity, and sum over the (pairwise disjoint) tiles. -/
theorem catProj_image_volume_le (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) :
    (volume : Measure T2) (catProj '' K) ≤ volume K := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hcov : catProj '' K ⊆ ⋃ m : Fin 2 → ℤ, catProj '' (K ∩ boxIoc m) := by
    intro p hp
    rw [Set.mem_image] at hp
    obtain ⟨x, hxK, rfl⟩ := hp
    obtain ⟨m, hm⟩ := exists_boxIoc_mem x
    rw [Set.mem_iUnion]
    exact ⟨m, Set.mem_image_of_mem _ ⟨hxK, hm⟩⟩
  calc (volume : Measure T2) (catProj '' K)
      ≤ (volume : Measure T2) (⋃ m : Fin 2 → ℤ, catProj '' (K ∩ boxIoc m)) := measure_mono hcov
    _ ≤ ∑' m : Fin 2 → ℤ, (volume : Measure T2) (catProj '' (K ∩ boxIoc m)) := measure_iUnion_le _
    _ = ∑' m : Fin 2 → ℤ, volume (K ∩ boxIoc m) :=
        tsum_congr fun m => volume_catProj_image_inter_box hKm m
    _ = volume K := by
        have hdisj : Pairwise (Function.onFun Disjoint (fun m : Fin 2 → ℤ => K ∩ boxIoc m)) := by
          intro m m' hmm
          exact (pairwise_disjoint_boxIoc hmm).mono Set.inter_subset_right Set.inter_subset_right
        rw [← measure_iUnion hdisj (fun m => hKm.inter (measurableSet_boxIoc m))]
        congr 1
        rw [← Set.inter_iUnion, iUnion_boxIoc, Set.inter_univ]

end ErgodicTheory.CatMapToral
