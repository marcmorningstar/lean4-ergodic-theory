/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A small positive measurable set from non-atomicity

This file proves that on a standard Borel probability space `(α, μ)` whose measure `μ` has no
atoms, for every threshold `δ > 0` there is a measurable set `A` with `0 < μ A < δ`
(`Oseledets.Krieger.exists_small_pos_measurableSet`).

This statement is *genuinely absent from Mathlib*: the docstring of
`Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean` records, as an open `TODO`, the question
of whether `NoAtoms` should be strengthened to the divisibility property
`∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`, of which the result here is the global instance
(`s = univ`). No constructive small-positive-set lemma exists in the library, so we build one from
scratch.

## Construction

We use the measurable embedding `f := MeasureTheory.embeddingReal α : α → ℝ` of the standard Borel
space `α` into the reals (`MeasureTheory.measurableEmbedding_embeddingReal`). For a level `n : ℕ`
and an integer `k : ℤ`, the *dyadic cell*

`dyadicCell f n k := f ⁻¹' Set.Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n)`

is the `f`-preimage of a half-open dyadic interval. The cell at level `n` *through a point* `x` is
`dyadicCell f n ⌊f x * 2 ^ n⌋`; equivalently it is `{y | ⌊f y * 2 ^ n⌋ = ⌊f x * 2 ^ n⌋}`. These
cells through a fixed `x` are measurable, contain `x`, are nested decreasingly in `n`, and shrink
to `{x}` (because `f` is injective and the intervals have radius `2 ^ (-n) → 0`); hence their
measure tends to `0` by continuity from above. The set

`Z := {x | ∃ n, μ (dyadicCell f n ⌊f x * 2 ^ n⌋) = 0}`

is contained in a countable union of null dyadic cells, so `μ Z = 0 < μ univ`; picking
`x ∉ Z` makes every cell through `x` have positive measure, while the measure still tends to `0`,
so some cell has measure in `(0, δ)`.

## Main statement

* `Oseledets.Krieger.exists_small_pos_measurableSet` : on a standard Borel probability space with a
  non-atomic measure, every positive threshold bounds a positive-measure measurable set from below.

This is a building block for the Rokhlin tower / Krieger generator development (issue #15).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

section Cells

variable (f : α → ℝ)

/-- The dyadic cell at level `n` and index `k`: the `f`-preimage of the half-open dyadic interval
`[k / 2 ^ n, (k + 1) / 2 ^ n)`. -/
def dyadicCell (n : ℕ) (k : ℤ) : Set α :=
  f ⁻¹' Set.Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n)

/-- The dyadic cell at level `n` **through the point `x`**: the cell whose index is the floor of
`f x * 2 ^ n`. Equivalently `{y | ⌊f y * 2 ^ n⌋ = ⌊f x * 2 ^ n⌋}` (see `mem_cell`). -/
def cell (n : ℕ) (x : α) : Set α :=
  dyadicCell f n ⌊f x * 2 ^ n⌋

variable {f}

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- A point `y` lies in the dyadic cell `dyadicCell f n k` iff `⌊f y * 2 ^ n⌋ = k`. -/
theorem mem_dyadicCell {n : ℕ} {k : ℤ} {y : α} :
    y ∈ dyadicCell f n k ↔ ⌊f y * 2 ^ n⌋ = k := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicCell, Set.mem_preimage, Set.mem_Ico, div_le_iff₀ h2, lt_div_iff₀ h2, Int.floor_eq_iff]

omit [StandardBorelSpace α] in
/-- Every dyadic cell is the `f`-preimage of a measurable set, hence measurable whenever `f` is. -/
theorem measurableSet_dyadicCell (hf : Measurable f) (n : ℕ) (k : ℤ) :
    MeasurableSet (dyadicCell f n k) :=
  (measurableSet_Ico).preimage hf

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- Membership in the cell through `x` is equality of dyadic floors. -/
theorem mem_cell {n : ℕ} {x y : α} :
    y ∈ cell f n x ↔ ⌊f y * 2 ^ n⌋ = ⌊f x * 2 ^ n⌋ :=
  mem_dyadicCell

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- `x` belongs to its own cell. -/
theorem self_mem_cell (n : ℕ) (x : α) : x ∈ cell f n x :=
  mem_cell.mpr rfl

omit [StandardBorelSpace α] in
/-- The cell through `x` is measurable when `f` is. -/
theorem measurableSet_cell (hf : Measurable f) (n : ℕ) (x : α) :
    MeasurableSet (cell f n x) :=
  measurableSet_dyadicCell hf _ _

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- **Dyadic nesting.** The level-`(n+1)` cell through `x` is contained in the level-`n` cell. The
key arithmetic fact is `⌊t * 2 ^ n⌋ = ⌊t * 2 ^ (n+1)⌋ / 2` (`Int.floor_div_natCast` applied to
`t * 2 ^ (n+1) = (t * 2 ^ n) * 2`), so equality of the finer floors forces equality of the coarser
ones. -/
theorem cell_succ_subset (n : ℕ) (x : α) : cell f (n + 1) x ⊆ cell f n x := by
  intro y hy
  rw [mem_cell] at hy ⊢
  have key : ∀ t : ℝ, ⌊t * 2 ^ n⌋ = ⌊t * 2 ^ (n + 1)⌋ / 2 := by
    intro t
    have hdiv : t * 2 ^ (n + 1) / (2 : ℕ) = t * 2 ^ n := by
      push_cast; ring
    have := Int.floor_div_natCast (t * 2 ^ (n + 1)) 2
    rw [hdiv] at this
    rw [this]
    norm_num
  rw [key (f y), key (f x), hy]

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- The cells through `x` form an antitone sequence in the level `n`. -/
theorem antitone_cell (x : α) : Antitone (fun n => cell f n x) :=
  antitone_nat_of_succ_le fun n => cell_succ_subset n x

omit [MeasurableSpace α] [StandardBorelSpace α] in
/-- **Cells shrink to the point.** Any `y` in every cell through `x` satisfies `f y = f x`: for each
`n`, both `f y * 2 ^ n` and `f x * 2 ^ n` lie in `[k, k + 1)` for the common floor `k`, so they are
within distance `1`, i.e. `|f y - f x| < 2 ^ (-n)`, which forces `f y = f x` as `n → ∞`. -/
theorem iInter_cell_subset (hf : Function.Injective f) (x : α) :
    ⋂ n, cell f n x ⊆ {x} := by
  intro y hy
  simp only [Set.mem_iInter, mem_cell] at hy
  rw [Set.mem_singleton_iff]
  -- Show `f y = f x`, then conclude `y = x` by injectivity.
  refine hf ?_
  by_contra hne
  -- `|f y - f x| > 0`; pick `n` with `2 ^ n > 1 / |f y - f x|` to get a contradiction.
  have hpos : (0 : ℝ) < |f y - f x| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |f y - f x|) (by norm_num : (1 : ℝ) < 2)
  -- From the common floor at level `n`: both `f y * 2 ^ n, f x * 2 ^ n ∈ [k, k+1)`.
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  set k := ⌊f x * 2 ^ n⌋ with hk
  have hyk : ⌊f y * 2 ^ n⌋ = k := hy n
  have hy1 : (k : ℝ) ≤ f y * 2 ^ n := by rw [← hyk]; exact Int.floor_le _
  have hy2 : f y * 2 ^ n < k + 1 := by rw [← hyk]; exact Int.lt_floor_add_one _
  have hx1 : (k : ℝ) ≤ f x * 2 ^ n := Int.floor_le _
  have hx2 : f x * 2 ^ n < k + 1 := Int.lt_floor_add_one _
  -- The scaled difference is bounded by `1`, contradicting the choice of `n`.
  have hdist : |f y - f x| * 2 ^ n < 1 := by
    have hsub : |f y * 2 ^ n - f x * 2 ^ n| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    calc |f y - f x| * 2 ^ n = |(f y - f x) * 2 ^ n| := by
            rw [abs_mul, abs_of_pos h2]
      _ = |f y * 2 ^ n - f x * 2 ^ n| := by ring_nf
      _ < 1 := hsub
  rw [div_lt_iff₀ hpos] at hn
  nlinarith [hn, hdist]

end Cells

section Measure

variable {μ : Measure α}

/-- **Continuity from above for cells.** The measure of the cell through `x` tends to `0`: the cells
are antitone and shrink to (a subset of) `{x}`, a null set under `NoAtoms`, so by continuity from
above (`tendsto_measure_iInter_atTop`) the measures converge to `μ (⋂ n, cell f n x) = 0`. -/
theorem tendsto_measure_cell [IsProbabilityMeasure μ] [NoAtoms μ]
    (hf : MeasurableEmbedding (embeddingReal α)) (x : α) :
    Tendsto (fun n => μ (cell (embeddingReal α) n x)) atTop (𝓝 0) := by
  have hmeas : ∀ n, NullMeasurableSet (cell (embeddingReal α) n x) μ := fun n =>
    (measurableSet_cell hf.measurable n x).nullMeasurableSet
  have hfin : ∃ n, μ (cell (embeddingReal α) n x) ≠ ∞ := ⟨0, measure_ne_top μ _⟩
  have htends :=
    tendsto_measure_iInter_atTop (μ := μ) hmeas (antitone_cell x) hfin
  -- The limiting intersection is null: it sits inside `{x}`.
  have hzero : μ (⋂ n, cell (embeddingReal α) n x) = 0 := by
    refine measure_mono_null (iInter_cell_subset hf.injective x) ?_
    simp
  rwa [hzero] at htends

end Measure

variable {μ : Measure α}

/-- **Small positive measurable set.**

On a standard Borel probability space whose measure `μ` has no atoms, for every threshold `δ > 0`
there is a measurable set `A` with `0 < μ A` and `μ A < δ`.

This fills a gap in Mathlib: the `NoAtoms` file's `TODO` notes that the divisibility property
`∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t < μ s` (of which this is the `s = univ` instance) is not part of
the library. The construction is via the measurable embedding `MeasureTheory.embeddingReal` into
the reals and the dyadic cells `dyadicCell`/`cell` built from it. It is a building block for the
Rokhlin tower / Krieger generator development (issue #15). -/
theorem exists_small_pos_measurableSet [IsProbabilityMeasure μ] [NoAtoms μ] {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∃ A : Set α, MeasurableSet A ∧ 0 < μ A ∧ μ A < δ := by
  classical
  set f := embeddingReal α with hfdef
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal α
  -- The "bad" set: points whose cell already has measure zero at some level.
  set Z : Set α := {x | ∃ n, μ (cell f n x) = 0} with hZdef
  -- `Z` is contained in a countable union of null dyadic cells, hence null.
  have hZnull : μ Z = 0 := by
    -- For a pair `p = (n, k)`, take the cell `dyadicCell f n k` if it is null, else `∅`.
    set g : ℕ × ℤ → Set α := fun p =>
      if μ (dyadicCell f p.1 p.2) = 0 then dyadicCell f p.1 p.2 else ∅ with hgdef
    have hZsub : Z ⊆ ⋃ p : ℕ × ℤ, g p := by
      intro x hx
      obtain ⟨n, hn⟩ := hx
      refine Set.mem_iUnion.mpr ⟨(n, ⌊f x * 2 ^ n⌋), ?_⟩
      have hxcell : x ∈ cell f n x := self_mem_cell n x
      -- `cell f n x = dyadicCell f n ⌊f x * 2 ^ n⌋`, which is null by `hn`.
      have hnull : μ (dyadicCell f n ⌊f x * 2 ^ n⌋) = 0 := hn
      simp only [hgdef]
      rw [if_pos hnull]
      exact hxcell
    refine measure_mono_null hZsub ?_
    refine measure_iUnion_null fun p => ?_
    simp only [hgdef]
    by_cases h : μ (dyadicCell f p.1 p.2) = 0
    · rwa [if_pos h]
    · rw [if_neg h]; simp
  -- The complement of `Z` has nonzero measure, so it is nonempty: pick `x ∉ Z`.
  have hZc : μ Zᶜ ≠ 0 := by
    intro hc
    have hle : μ (univ : Set α) ≤ μ Z + μ Zᶜ := by
      rw [← Set.union_compl_self Z]; exact measure_union_le _ _
    rw [hZnull, hc, measure_univ] at hle
    simp at hle
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hZc
  -- For this `x` every cell has positive measure, yet the measures tend to `0`.
  have hxpos : ∀ n, 0 < μ (cell f n x) := by
    intro n
    rw [hZdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists] at hx
    exact zero_lt_iff.mpr (hx n)
  have htends : Tendsto (fun n => μ (cell f n x)) atTop (𝓝 0) :=
    tendsto_measure_cell hf x
  -- Eventually the measure drops below `δ`; pick such an `n`.
  have hev : ∀ᶠ n in atTop, μ (cell f n x) < δ :=
    htends.eventually_lt (tendsto_const_nhds) hδ
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨cell f n x, measurableSet_cell hf.measurable n x, hxpos n, hn⟩

end Oseledets.Krieger
