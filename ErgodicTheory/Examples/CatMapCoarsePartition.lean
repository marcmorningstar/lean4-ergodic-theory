/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapEntropy
import ErgodicTheory.Entropy.KSEntropyBounds
import ErgodicTheory.Entropy.Join

/-!
# The coarse two-rectangle Adler–Weiss partition and the `log 2` entropy ceiling

This module records the **original Adler–Weiss Markov partition** of the Arnold cat map
`catTorus` — the two golden rectangles `R₁ = catProj '' awBox 0` and `R₂ = catProj '' awBox 1`,
*before* the branch subdivision into the five affine pieces of
`ErgodicTheory.Examples.CatMapAdlerWeiss`.  Because the branch tiling is exact (the junk cell is
empty, `awCell_zero_eq_empty`), the two projected rectangles partition the torus exactly, giving a
genuine two-cell `MeasurePartition` `coarseAWPartition`.

Its partition-relative Kolmogorov–Sinai entropy is the entropy of the **merged symbolic factor**
`src ∘ awSymb` (the coarse itinerary letter of `x` at time `k` is `src (awSymb x k)`,
`mem_coarse_iff`).  A two-cell partition has entropy at most `log 2`
(`coarseAWPartition_ksEntropy_le`), which is *strictly* below the system entropy
`log λ₊ = log((3 + √5)/2)` (`log_two_lt_log_lam`); so the coarse partition, unlike the fine
generator `catAWPartition`, is far from being a generator.

The `src`/`tgt` bookkeeping is interchangeable via the one-step shift: admissibility gives
`tgt (awSymb x k) = src (awSymb x (k+1))`, so a `tgt`-merged factor is the `src`-merged factor
shifted by one time step.  We deliver the `src`-based statements, which are the natural
partition-side ones.

## Main definitions

* `ErgodicTheory.Entropy.ksEntropyPartition_le_log_card` — the abstract ceiling: any finite
  measure partition into `card ι` cells has partition-relative KS entropy at most `log (card ι)`.
* `ErgodicTheory.CatMapToral.coarseAWPartition` — the two-cell coarse Adler–Weiss partition.

## Main results

* `coarseCell_eq_union` — each coarse cell is the union of the fine cells with matching source.
* `mem_coarse_iff` — the coarse itinerary letter of `x` at time `k` is `src (awSymb x k)`.
* `coarseAWPartition_ksEntropy_le` — `h(catTorus, coarse) ≤ log 2`.
* `log_two_lt_log_lam` — `log 2 < log((3 + √5)/2)`, the strict gap to the system entropy.
-/

open MeasureTheory

noncomputable section

/-- Normalise the circle measure to total mass `1`, matching the imported cat-map measure modules so
that `volume : Measure T2` lines up with the Adler–Weiss partitions. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_coarse :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_coarse :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_coarse :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The abstract `log (card)` ceiling for a partition-relative entropy -/

namespace ErgodicTheory.Entropy

variable {α : Type*} [MeasurableSpace α]

/-- **The abstract entropy ceiling.**  For a measure-preserving `T` on a probability space and a
finite measurable partition `P` into `card ι` cells, the partition-relative Kolmogorov–Sinai
entropy is at most `log (card ι)`.  Compose the single-step bound
`ksEntropyPartition hT P ≤ H(P)` (`ksEntropyPartition_le_entropy`) with the static Jensen ceiling
`H(P) ≤ log (card ι)` (`entropy_le_log_card_partition`). -/
lemma ksEntropyPartition_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) :
    ksEntropyPartition hT P ≤ Real.log (Fintype.card ι) :=
  (ksEntropyPartition_le_entropy hT P).trans (entropy_le_log_card_partition P)

end ErgodicTheory.Entropy

namespace ErgodicTheory.CatMapToral

/-! ## The two golden rectangles tile each box; the coarse cells -/

/-- **The source matches the box.**  A lift `v` lying both in the golden rectangle `awBox i` and in
the branch `branchBox e` forces `src e = i`: the branch sits inside `awBox (src e)`, and distinct
golden rectangles are disjoint in the plane. -/
lemma src_eq_of_mem_branchBox_of_mem_awBox {v : Fin 2 → ℝ} {e : Fin 5} {i : Fin 2}
    (hv : v ∈ awBox i) (hb : v ∈ branchBox e) : src e = i := by
  by_contra hne
  exact Set.disjoint_left.mp (awBox_disjoint hne) (branchBox_subset_awBox_src e hb) hv

/-- **Each golden rectangle is tiled by its branches.**  `awBox i` is the union of the branches
whose source is `i` (the windows `[0,φ−1),[φ−1,1),[1,φ)` tile `R₁`; `[φ,2),[2,φ²)` tile `R₂`). -/
theorem awBox_eq_iUnion_branchBox (i : Fin 2) :
    awBox i = ⋃ e ∈ {e : Fin 5 | src e = i}, branchBox e := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · intro hv
    obtain ⟨e, he⟩ := exists_branchBox_of_mem_awUnion (awBox_subset_awUnion i hv)
    exact ⟨e, src_eq_of_mem_branchBox_of_mem_awBox hv he, he⟩
  · rintro ⟨e, hsrc, hb⟩
    rw [← hsrc]
    exact branchBox_subset_awBox_src e hb

/-- **The projected rectangle is the union of its projected branches.** -/
theorem catProj_image_awBox_eq_iUnion (i : Fin 2) :
    catProj '' awBox i = ⋃ e ∈ {e : Fin 5 | src e = i}, catProj '' branchBox e := by
  rw [awBox_eq_iUnion_branchBox i, Set.image_iUnion₂]

/-- **Fine-refines-coarse.**  Each coarse cell `catProj '' awBox i` is the union of the fine cells
`awCell e.succ` whose branch has source `i`. -/
theorem coarseCell_eq_union (i : Fin 2) :
    catProj '' awBox i = ⋃ e ∈ {e : Fin 5 | src e = i}, awCell e.succ := by
  simp_rw [awCell_succ]
  exact catProj_image_awBox_eq_iUnion i

/-- Each projected golden rectangle is measurable (a finite union of the measurable projected
branches). -/
theorem measurableSet_catProj_image_awBox (i : Fin 2) :
    MeasurableSet (catProj '' awBox i) := by
  rw [catProj_image_awBox_eq_iUnion i]
  exact MeasurableSet.biUnion (Set.toFinite _).countable
    (fun e _ => measurableSet_catProj_image_branchBox e)

/-- **The two coarse cells are disjoint on the torus.**  Two lifts with equal projection lie in
`R₁ ∪ R₂`, on which `catProj` is injective, so they coincide; but distinct golden rectangles are
disjoint in the plane. -/
theorem disjoint_catProj_image_awBox {b b' : Fin 2} (h : b ≠ b') :
    Disjoint (catProj '' awBox b) (catProj '' awBox b') := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
  have hxy : x = y :=
    catProj_injOn_awUnion (awBox_subset_awUnion b hx) (awBox_subset_awUnion b' hy)
      (hxp.trans hyp.symm)
  subst hxy
  exact Set.disjoint_left.mp (awBox_disjoint h) hx hy

/-- **The coarse Adler–Weiss partition.**  The two projected golden rectangles
`R₁ = catProj '' awBox 0` and `R₂ = catProj '' awBox 1` form a genuine two-cell `MeasurePartition`
of `(T2, volume)`.  This is the classical Adler–Weiss Markov partition before the branch
subdivision; the cover is *exact* because the fine branch tiling has an empty junk cell
(`awUnion_eq_univ`). -/
def coarseAWPartition : Entropy.MeasurePartition (volume : Measure T2) (Fin 2) where
  cells := fun i => catProj '' awBox i
  measurable := measurableSet_catProj_image_awBox
  aedisjoint := fun i j hij => (disjoint_catProj_image_awBox hij).aedisjoint
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ ⋃ e, catProj '' branchBox e := by rw [awUnion_eq_univ]; trivial
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.2 ⟨src e, Set.image_mono (branchBox_subset_awBox_src e) he⟩

/-! ## The coarse itinerary letter -/

/-- **The coarse itinerary letter.**  The point `ziter catTorusEquiv k x` lies in the coarse cell
`catProj '' awBox i` exactly when the source of its Adler–Weiss branch symbol is `i`:
`src (awSymb x k) = i`.  (By the shift `tgt (awSymb x k) = src (awSymb x (k+1))`, the equivalent
`tgt`-merged letter is this one advanced by a step.) -/
theorem mem_coarse_iff (x : T2) (k : ℤ) (i : Fin 2) :
    Krieger.ziter catTorusEquiv k x ∈ catProj '' awBox i ↔ src (awSymb x k) = i := by
  have hmem : Krieger.ziter catTorusEquiv k x ∈ catProj '' branchBox (awSymb x k) := by
    rw [← awCell_succ]; exact awSymb_mem x k
  constructor
  · intro hp
    by_contra hne
    have hb : Krieger.ziter catTorusEquiv k x ∈ catProj '' awBox (src (awSymb x k)) :=
      Set.image_mono (branchBox_subset_awBox_src _) hmem
    exact Set.disjoint_left.mp (disjoint_catProj_image_awBox hne) hb hp
  · intro hsi
    have hb : Krieger.ziter catTorusEquiv k x ∈ catProj '' awBox (src (awSymb x k)) :=
      Set.image_mono (branchBox_subset_awBox_src _) hmem
    rwa [hsi] at hb

/-! ## The `log 2` entropy ceiling and the strict gap to the system entropy -/

/-- **The coarse entropy ceiling.**  The partition-relative Kolmogorov–Sinai entropy of the coarse
two-cell Adler–Weiss partition is at most `log 2` (the abstract `log (card)` ceiling for two
cells). -/
theorem coarseAWPartition_ksEntropy_le :
    Entropy.ksEntropyPartition measurePreserving_catTorus coarseAWPartition ≤ Real.log 2 := by
  have h := Entropy.ksEntropyPartition_le_log_card measurePreserving_catTorus coarseAWPartition
  simpa using h

/-- **The strict gap.**  `log 2 < log((3 + √5)/2) = log λ₊`: the coarse two-cell ceiling is strictly
below the system entropy, so the coarse partition is not a generator.  Reduce to `2 < (3+√5)/2`,
i.e. `1 < √5`, from `2 < √5` (`two_lt_sqrt5`). -/
theorem log_two_lt_log_lam : Real.log 2 < Real.log ((3 + Real.sqrt 5) / 2) :=
  Real.log_lt_log (by norm_num) (by have := two_lt_sqrt5; linarith)

end ErgodicTheory.CatMapToral

end
