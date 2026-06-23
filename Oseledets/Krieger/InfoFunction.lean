/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.KSEntropy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The information function of the iterated join

This file builds the **information-function foundation** for the Shannon–McMillan–Breiman
upper bound (Algoet–Cover) that feeds Krieger's name-count argument (issue #15, milestone M2).

For a measure-preserving transformation `T` of a probability space `(α, μ)` and a finite
measurable partition `P`, every point `x` has an `n`-step **itinerary** `f : Fin n → ι` recording,
for each `0 ≤ k < n`, which cell of `P` the iterate `Tᵏ x` lies in. The **atom of `x`** is the
cell `⋂ₖ T⁻ᵏ (P_{f k})` of the iterated join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` that contains `x`, and the
**information function** is `iₙ(x) = -log μ(atom of x)`, the surprise of learning the `n`-name of
`x`.

Because the cells of `P` may overlap on a `μ`-null set, a naive `Classical.choose`-itinerary is
not pointwise measurable. We therefore build the itinerary as a *least-index selector*: among the
(non-empty, since the cells cover) set of admissible codes we pick the smallest in a fixed
enumeration. This selector is genuinely measurable, so the atom map and the information function
are measurable on the nose; the least-index cell agrees `μ`-almost everywhere with the chosen cell
(the discarded part lies in a pairwise a.e.-disjoint union), so the information function integrates
to the join entropy `H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P)`.

## Main definitions

* `Oseledets.Krieger.itinerary`: the `n`-step least-index code `f : Fin n → ι` of a point.
* `Oseledets.Krieger.atomOf`: the atom `⋂ₖ T⁻ᵏ (P_{f k})` of the iterated join containing `x`.
* `Oseledets.Krieger.infoFun`: the information function `iₙ(x) = -log μ(atom of x)`.

## Main results

* `Oseledets.Krieger.itinerary_spec`: `Tᵏ x ∈ P_{itinerary x k}` for all `k`.
* `Oseledets.Krieger.mem_atomOf`: `x ∈ atomOf x`.
* `Oseledets.Krieger.measurableSet_atomOf`: the atom is measurable.
* `Oseledets.Krieger.measurable_infoFun`: the information function is measurable.
* `Oseledets.Krieger.infoFun_nonneg`: the information function is nonnegative.
* `Oseledets.Krieger.integral_infoFun_eq`: `∫ iₙ dμ = H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P) = ksEntropySeq …`.

## References

* P. Algoet and T. Cover, *A sandwich proof of the Shannon–McMillan–Breiman theorem*,
  Ann. Probab. **16** (1988), 899–909.
* T. Downarowicz, *Entropy in Dynamical Systems*, Cambridge Univ. Press (2011), Lemma 4.2.5.
-/

open MeasureTheory Function Filter

namespace Oseledets.Krieger

open Oseledets.Entropy

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [Fintype ι]
  {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

section Itinerary

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)

/-- The set of **admissible `n`-codes** of a point `x`: those `f : Fin n → ι` such that
`x` lies in the iterated-join cell at `f`, i.e. `Tᵏ x ∈ P_{f k}` for every `k`. This set is
non-empty for every `x` because the cells of `P` cover the whole space. -/
def admissibleCodes (x : α) : Set (Fin n → ι) :=
  {f | x ∈ (ksJoin hT P n).cells f}

omit [IsProbabilityMeasure μ] in
/-- Every point has an admissible code: choosing, at each coordinate `k`, the `P`-cell containing
`Tᵏ x` (possible because the cells cover) yields a code whose iterated-join cell contains `x`. -/
lemma admissibleCodes_nonempty (x : α) : (admissibleCodes hT P n x).Nonempty := by
  have hx : ∀ k : Fin n, ∃ i, (T^[(k : ℕ)]) x ∈ P.cells i := fun k => by
    have : (T^[(k : ℕ)]) x ∈ ⋃ i, P.cells i := P.cover ▸ Set.mem_univ _
    exact Set.mem_iUnion.mp this
  choose f hf using hx
  refine ⟨f, ?_⟩
  rw [admissibleCodes, Set.mem_setOf_eq, ksJoin_cells, ksJoinCells_apply, Set.mem_iInter]
  exact fun k => hf k

end Itinerary

/-- The fixed enumeration of the (finite) code type `Fin n → ι`, used to break ties in the
least-index itinerary selector. We linearly order the finite type by transporting the order of
`Fin (card)` along the canonical equivalence. This is kept a `local` instance so it does not leak a
`LinearOrder (Fin n → ι)` onto downstream files. -/
noncomputable local instance instLinearOrderFinArrow {ι : Type*} [Fintype ι] {n : ℕ} :
    LinearOrder (Fin n → ι) :=
  LinearOrder.lift' (Fintype.equivFin (Fin n → ι))
    (Fintype.equivFin (Fin n → ι)).injective

section Selector

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)

open Classical in
/-- The **`n`-step itinerary** of a point `x`: the least admissible code, i.e. the smallest
`f : Fin n → ι` (in the fixed enumeration) for which `Tᵏ x ∈ P_{f k}` for all `k`. Using the least
admissible code rather than an arbitrary `Classical.choose` makes the selector measurable: its
fibers are differences of the (measurable) iterated-join cells. -/
noncomputable def itinerary (x : α) : Fin n → ι :=
  (Set.Finite.toFinset (Set.toFinite (admissibleCodes hT P n x))).min'
    (by
      rw [Set.Finite.toFinset_nonempty]
      exact admissibleCodes_nonempty hT P n x)

omit [IsProbabilityMeasure μ] in
/-- The itinerary is an admissible code: it lies in the admissible set of `x`. -/
lemma itinerary_mem (x : α) : itinerary hT P n x ∈ admissibleCodes hT P n x := by
  have := Finset.min'_mem (Set.Finite.toFinset (Set.toFinite (admissibleCodes hT P n x)))
    (by rw [Set.Finite.toFinset_nonempty]; exact admissibleCodes_nonempty hT P n x)
  rwa [Set.Finite.mem_toFinset] at this

omit [IsProbabilityMeasure μ] in
/-- **Itinerary specification.** For each `k`, the `k`-th iterate `Tᵏ x` lies in the `P`-cell
indexed by the `k`-th coordinate of the itinerary of `x`. -/
lemma itinerary_spec (x : α) (k : Fin n) :
    (T^[(k : ℕ)]) x ∈ P.cells (itinerary hT P n x k) := by
  have hx := itinerary_mem hT P n x
  rw [admissibleCodes, Set.mem_setOf_eq, ksJoin_cells, ksJoinCells_apply, Set.mem_iInter] at hx
  exact hx k

omit [IsProbabilityMeasure μ] in
/-- The itinerary of `x` is the *least* admissible code: no strictly smaller code is admissible. -/
lemma itinerary_le {x : α} {f : Fin n → ι} (hf : x ∈ (ksJoin hT P n).cells f) :
    itinerary hT P n x ≤ f := by
  refine Finset.min'_le _ _ ?_
  rw [Set.Finite.mem_toFinset]
  exact hf

omit [IsProbabilityMeasure μ] in
/-- The fiber of the itinerary over a code `g` is the cell at `g` with the strictly smaller cells
removed. This explicit description is the engine of the measurability of `itinerary`. -/
lemma itinerary_eq_iff (x : α) (g : Fin n → ι) :
    itinerary hT P n x = g ↔
      x ∈ (ksJoin hT P n).cells g ∧ ∀ g' < g, x ∉ (ksJoin hT P n).cells g' := by
  constructor
  · rintro rfl
    refine ⟨itinerary_mem hT P n x, fun g' hg' hmem => ?_⟩
    exact absurd (itinerary_le hT P n hmem) (not_le.mpr hg')
  · rintro ⟨hmem, hmin⟩
    refine le_antisymm (itinerary_le hT P n hmem) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hmin _ hlt (itinerary_mem hT P n x)

end Selector

section Atom

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)

/-- The **atom of `x`** (with respect to the `n`-fold iterated join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`): the cell
`⋂ₖ T⁻ᵏ (P_{itinerary x k})` of the join that contains `x`. -/
noncomputable def atomOf (x : α) : Set α := (ksJoin hT P n).cells (itinerary hT P n x)

omit [IsProbabilityMeasure μ] in
/-- A point lies in its own atom. -/
lemma mem_atomOf (x : α) : x ∈ atomOf hT P n x := by
  rw [atomOf, ksJoin_cells, ksJoinCells_apply, Set.mem_iInter]
  exact fun k => itinerary_spec hT P n x k

omit [IsProbabilityMeasure μ] in
/-- The atom of `x` is a measurable set: it is a cell of the iterated-join partition. -/
lemma measurableSet_atomOf (x : α) : MeasurableSet (atomOf hT P n x) :=
  (ksJoin hT P n).measurable _

omit [IsProbabilityMeasure μ] in
/-- The atom of `x` equals the iterated-join cell at the itinerary of `x`. -/
lemma atomOf_eq (x : α) : atomOf hT P n x = (ksJoin hT P n).cells (itinerary hT P n x) := rfl

end Atom

section Measurable

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)

omit [IsProbabilityMeasure μ] in
/-- The itinerary fiber `{x | itinerary x = g}` is measurable: it is the difference of the
measurable cell at `g` and the (finite) union of the strictly smaller cells. -/
lemma measurableSet_itinerary_eq (g : Fin n → ι) :
    MeasurableSet {x | itinerary hT P n x = g} := by
  classical
  have hset : {x | itinerary hT P n x = g}
      = (ksJoin hT P n).cells g ∩ ⋂ g' ∈ {g' | g' < g}, ((ksJoin hT P n).cells g')ᶜ := by
    ext x
    rw [Set.mem_setOf_eq, itinerary_eq_iff hT P n x g, Set.mem_inter_iff, Set.mem_iInter₂]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h g' hg'; exact h g' hg'
    · intro h g' hg'; exact h g' hg'
  rw [hset]
  refine ((ksJoin hT P n).measurable g).inter ?_
  refine MeasurableSet.biInter (Set.to_countable _) fun g' _ => ?_
  exact ((ksJoin hT P n).measurable g').compl

end Measurable

section InfoFunction

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)

/-- The **information function** `iₙ(x) = -log μ(atom of x)` of the iterated join
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P`: the surprise of learning the `n`-name of `x`. Its integral is the join entropy
`H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P)`. -/
noncomputable def infoFun (x : α) : ℝ := -Real.log (μ (atomOf hT P n x)).toReal

/-- The information weight attached to a code `g`: `-log μ(cell g)`. The information function is the
composite of this weight with the itinerary. -/
noncomputable def infoWeight (g : Fin n → ι) : ℝ :=
  -Real.log (μ ((ksJoin hT P n).cells g)).toReal

omit [IsProbabilityMeasure μ] in
/-- The information function factors through the itinerary: `iₙ(x) = infoWeight (itinerary x)`. -/
lemma infoFun_eq_infoWeight_itinerary (x : α) :
    infoFun hT P n x = infoWeight hT P n (itinerary hT P n x) := by
  rw [infoFun, infoWeight, atomOf]

omit [IsProbabilityMeasure μ] in
/-- The information function is a finite sum of indicators of the (pairwise disjoint, covering)
itinerary fibers, weighted by the corresponding information weight. This is the *simple-function*
form that drives both its measurability and the integral computation. -/
lemma infoFun_eq_sum_indicator (x : α) :
    infoFun hT P n x
      = ∑ g : Fin n → ι,
          Set.indicator {x | itinerary hT P n x = g} (fun _ => infoWeight hT P n g) x := by
  classical
  -- Exactly one summand is non-zero, namely the one at `g = itinerary x`.
  rw [Finset.sum_eq_single (itinerary hT P n x)]
  · rw [Set.indicator_of_mem (by rw [Set.mem_setOf_eq])]
    exact infoFun_eq_infoWeight_itinerary hT P n x
  · intro g _ hg
    refine Set.indicator_of_notMem ?_ _
    rw [Set.mem_setOf_eq]
    exact fun h => hg h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [IsProbabilityMeasure μ] in
/-- The information function is measurable: in its simple-function form it is a finite sum of
indicators of the (measurable) itinerary fibers with constant values, each of which is measurable.
This avoids equipping the finite code type with a measurable structure. -/
lemma measurable_infoFun : Measurable (infoFun hT P n) := by
  classical
  rw [funext (infoFun_eq_sum_indicator hT P n)]
  refine Finset.measurable_sum Finset.univ fun g _ => ?_
  exact (measurable_const).indicator (measurableSet_itinerary_eq hT P n g)

/-- The information weight of any code is nonnegative: the cell measure is at most `1`, so its
logarithm is nonpositive and its negation is nonnegative. -/
lemma infoWeight_nonneg (g : Fin n → ι) : 0 ≤ infoWeight hT P n g := by
  rw [infoWeight, neg_nonneg]
  refine Real.log_nonpos ENNReal.toReal_nonneg ?_
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ)
    (s := (ksJoin hT P n).cells g))
  rwa [ENNReal.toReal_one] at h

/-- The information function is nonnegative: it is the information weight of the itinerary, and
every cell of a probability space has measure at most `1`. -/
lemma infoFun_nonneg (x : α) : 0 ≤ infoFun hT P n x := by
  rw [infoFun_eq_infoWeight_itinerary]
  exact infoWeight_nonneg hT P n _

end InfoFunction

section Integral

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)

omit [IsProbabilityMeasure μ] in
/-- The itinerary fibers cover the whole space: every point has an itinerary. -/
lemma iUnion_itinerary_fiber : ⋃ g, {x | itinerary hT P n x = g} = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact fun x => Set.mem_iUnion.mpr ⟨itinerary hT P n x, rfl⟩

omit [IsProbabilityMeasure μ] in
/-- The itinerary fiber over `g` is contained in the cell at `g`. -/
lemma itinerary_fiber_subset_cell (g : Fin n → ι) :
    {x | itinerary hT P n x = g} ⊆ (ksJoin hT P n).cells g := by
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  rw [← hx]
  exact itinerary_mem hT P n x

omit [IsProbabilityMeasure μ] in
/-- The difference between the cell at `g` and the itinerary fiber over `g` lies in the union of
the *other* cells, hence is `μ`-null (the cells are pairwise a.e.-disjoint). Consequently the
fiber has the same measure as the cell. -/
lemma measure_itinerary_fiber (g : Fin n → ι) :
    μ {x | itinerary hT P n x = g} = μ ((ksJoin hT P n).cells g) := by
  classical
  -- The complement of the fiber inside the cell.
  set C := (ksJoin hT P n).cells g with hC
  set F := {x | itinerary hT P n x = g} with hF
  have hsub : F ⊆ C := itinerary_fiber_subset_cell hT P n g
  -- A point of `C \ F` lies in a *different* cell, so `C \ F ⊆ C ∩ ⋃ g' ≠ g, cell g'`.
  have hdiff : C \ F ⊆ C ∩ ⋃ g' ∈ ({g' | g' ≠ g} : Set (Fin n → ι)), (ksJoin hT P n).cells g' := by
    intro x hx
    obtain ⟨hxC, hxF⟩ := hx
    rw [hF, Set.mem_setOf_eq] at hxF
    -- `x ∈ C = cell g` but `itinerary x ≠ g`, so `itinerary x` is a *different* admissible code.
    have hmem : x ∈ (ksJoin hT P n).cells (itinerary hT P n x) := itinerary_mem hT P n x
    exact ⟨hxC, Set.mem_biUnion (by simpa using hxF) hmem⟩
  -- That intersection is `μ`-null: each `cell g'` with `g' ≠ g` is a.e. disjoint from `cell g`.
  have hnull : μ (C \ F) = 0 := by
    refine measure_mono_null hdiff ?_
    rw [Set.inter_iUnion₂]
    refine (measure_biUnion_null_iff (Set.to_countable _)).mpr fun g' hg' => ?_
    -- `cell g'` and `cell g = C` are a.e. disjoint, so their intersection is null.
    have hae : AEDisjoint μ C ((ksJoin hT P n).cells g') := by
      rw [hC]
      exact (ksJoin hT P n).aedisjoint (Ne.symm (by simpa using hg'))
    exact hae
  -- Conclude equal measures from `F ⊆ C` and `μ (C \ F) = 0`.
  have hFmeas : MeasurableSet F := hF ▸ measurableSet_itinerary_eq hT P n g
  have hsplit : μ (C ∩ F) + μ (C \ F) = μ C := measure_inter_add_diff C hFmeas
  rw [Set.inter_eq_right.mpr hsub, hnull, add_zero] at hsplit
  exact hsplit

/-- The information function is integrable: it is bounded (a finite combination of indicators of
sets of finite measure) on a probability space. -/
lemma integrable_infoFun : Integrable (infoFun hT P n) μ := by
  classical
  rw [funext (infoFun_eq_sum_indicator hT P n)]
  refine integrable_finsetSum Finset.univ fun g _ => ?_
  refine (integrable_const (infoWeight hT P n g)).indicator ?_
  exact measurableSet_itinerary_eq hT P n g

/-- **The information function integrates to the join entropy.** Following Algoet–Cover
(Downarowicz, Lemma 4.2.5), the average information `∫ iₙ dμ` equals the Shannon entropy
`H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P)` of the `n`-fold iterated join. The proof writes `iₙ` as a sum of indicators of
the itinerary fibers (`infoFun_eq_sum_indicator`), integrates termwise using that each fiber has
the same measure as the corresponding cell (`measure_itinerary_fiber`), and recognizes the summand
`μ(cell g) · (-log μ(cell g))` as `negMulLog (μ(cell g)).toReal`. -/
theorem integral_infoFun_eq :
    ∫ x, infoFun hT P n x ∂μ = ksEntropySeq hT P n := by
  classical
  -- Expand `iₙ` as a sum of indicators and integrate termwise.
  rw [funext (infoFun_eq_sum_indicator hT P n),
    integral_finsetSum Finset.univ
      (fun g _ => (integrable_const (infoWeight hT P n g)).indicator
        (measurableSet_itinerary_eq hT P n g))]
  -- Each indicator integrates to `infoWeight g · μ(fiber g).toReal = negMulLog (μ(cell g)).toReal`.
  rw [ksEntropySeq, entropy_def]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [integral_indicator (measurableSet_itinerary_eq hT P n g), setIntegral_const,
    measureReal_def, measure_itinerary_fiber hT P n g, smul_eq_mul]
  simp only [infoWeight, Real.negMulLog]
  ring

end Integral

end Oseledets.Krieger
