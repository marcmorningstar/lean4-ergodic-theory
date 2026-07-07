/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Analytic sets are universally measurable (the Suslin–operation route)

This module proves the classical theorem of Lusin that **every analytic subset of a standard Borel
(Polish) space is universally measurable**: for any measure `μ`,

`theorem MeasureTheory.AnalyticSet.nullMeasurableSet :`
`    AnalyticSet s → ∀ μ, NullMeasurableSet s μ`.

Mathlib supplies the analytic-set construction (`MeasureTheory.AnalyticSet`) and Suslin's theorem
(`AnalyticSet.measurableSet_of_compl`), but *not* universal measurability — a Borel projection is
analytic without an analytic complement, so Suslin's theorem does not apply. We build the missing
piece bottom-up via the **Suslin operation** and the classical fact that the σ-algebra of
`μ`-measurable (here: `NullMeasurableSet`) sets is **closed under the Suslin operation**
(Kechris, *Classical DST*, Thm 29.7; Cohn, *Measure Theory*, Thm 8.4.1).

## Structure

* `SuslinScheme.suslinOp` — the Suslin operation `𝒜 P = ⋃ f, ⋂ n, P (f|n)` over a scheme of sets
  indexed by finite integer sequences `List ℕ`.
* `nullMeasurableSet_suslinOp_finite` / `nullMeasurableSet_suslinOp` — **the core**: the Suslin
  operation applied to a scheme of `NullMeasurableSet`s is `NullMeasurableSet`, first for a finite
  measure and then for an arbitrary measure (via `μ.restrict` to a hull of `𝒜 P` of finite measure
  or `of_null`).
* `analyticSet_eq_suslinOp_closed` — every analytic set is the Suslin operation of a scheme of
  **closed** (hence measurable) sets, derived from `AnalyticSet` = continuous image of `ℕ → ℕ`.
* `MeasureTheory.AnalyticSet.nullMeasurableSet` — the assembled target theorem.

## Reusable infrastructure

The Suslin operation, its monotone regularisation, and the measurability-of-the-Suslin-operation
lemma are general descriptive-set-theory tools, independent of the multiplicative ergodic theorem.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace MeasureTheory

/-! ### The Suslin operation -/

namespace SuslinScheme

variable {X : Type*}

/-- Restriction of `f : ℕ → ℕ` to its first `n` values, as a `List ℕ`. This is the finite sequence
`f|n = ⟨f 0, …, f (n-1)⟩` indexing nodes of the Baire-space tree. -/
def restr (f : ℕ → ℕ) (n : ℕ) : List ℕ := List.ofFn fun i : Fin n => f i

@[simp] theorem restr_zero (f : ℕ → ℕ) : restr f 0 = [] := by simp [restr]

theorem restr_length (f : ℕ → ℕ) (n : ℕ) : (restr f n).length = n := by simp [restr]

/-- The **Suslin operation** applied to a scheme `P : List ℕ → Set X`:
`𝒜 P = ⋃_{f : ℕ → ℕ} ⋂_{n} P (f|n)`. -/
def suslinOp (P : List ℕ → Set X) : Set X :=
  ⋃ f : ℕ → ℕ, ⋂ n : ℕ, P (restr f n)

theorem mem_suslinOp {P : List ℕ → Set X} {x : X} :
    x ∈ suslinOp P ↔ ∃ f : ℕ → ℕ, ∀ n, x ∈ P (restr f n) := by
  simp [suslinOp, mem_iUnion, mem_iInter]

/-- `restr f` of the successor length appends one entry to `restr f n`. -/
theorem restr_succ (f : ℕ → ℕ) (n : ℕ) : restr f (n + 1) = restr f n ++ [f n] := by
  simp only [restr]
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

/-- `restr f n` is recovered as the length-`n` prefix of `restr f (n+1)`. -/
theorem take_restr_succ (f : ℕ → ℕ) (n : ℕ) : (restr f (n + 1)).take n = restr f n := by
  rw [restr_succ, List.take_left' (by simp [restr_length])]

/-- The **partial Suslin set at a node** `s : List ℕ`: the union, over all `f : ℕ → ℕ` extending
`s` (i.e. with `restr f s.length = s`), of `⋂ n, P (f|n)`. We have `partial [] = suslinOp P`. -/
def partialSuslin (P : List ℕ → Set X) (s : List ℕ) : Set X :=
  ⋃ (f : ℕ → ℕ) (_ : restr f s.length = s), ⋂ n : ℕ, P (restr f n)

theorem mem_partialSuslin {P : List ℕ → Set X} {s : List ℕ} {x : X} :
    x ∈ partialSuslin P s ↔ ∃ f : ℕ → ℕ, restr f s.length = s ∧ ∀ n, x ∈ P (restr f n) := by
  simp only [partialSuslin, mem_iUnion, mem_iInter]
  tauto

/-- At the root, the partial Suslin set is the full Suslin operation. -/
theorem partialSuslin_nil (P : List ℕ → Set X) : partialSuslin P [] = suslinOp P := by
  ext x
  rw [mem_partialSuslin, mem_suslinOp]
  simp [List.length_nil, restr_zero]

/-- Every point of the partial Suslin set at `s` lies in `P s` itself (take `n = s.length`). -/
theorem partialSuslin_subset_node (P : List ℕ → Set X) (s : List ℕ) :
    partialSuslin P s ⊆ P s := by
  intro x hx
  rw [mem_partialSuslin] at hx
  obtain ⟨f, hf, hfn⟩ := hx
  have := hfn s.length
  rwa [hf] at this

/-- **The branching identity** `A s = ⋃ₖ A (s ++ [k])`: the partial Suslin set at a node is the
union of those at its immediate children. -/
theorem partialSuslin_eq_iUnion_child (P : List ℕ → Set X) (s : List ℕ) :
    partialSuslin P s = ⋃ k : ℕ, partialSuslin P (s ++ [k]) := by
  ext x
  simp only [mem_iUnion, mem_partialSuslin]
  constructor
  · rintro ⟨f, hf, hfn⟩
    refine ⟨f s.length, f, ?_, hfn⟩
    rw [List.length_append, List.length_singleton, restr_succ, hf]
  · rintro ⟨k, f, hf, hfn⟩
    refine ⟨f, ?_, hfn⟩
    have hlen : (s ++ [k]).length = s.length + 1 := by simp
    rw [hlen] at hf
    have h2 := take_restr_succ f s.length
    rw [hf] at h2
    simpa using h2.symm

end SuslinScheme

/-! ### Measurability of the Suslin operation -/

section Measurability

open SuslinScheme

variable {X : Type*} [MeasurableSpace X]

/-- **Measurability of the Suslin operation, finite case.** If every node set `P s` is measurable
and `μ` is a finite measure, then the Suslin operation `𝒜 P` is `NullMeasurableSet`.

This is the classical theorem that the σ-algebra of measurable sets is closed under the Suslin
operation (Kechris 29.7, Cohn 8.4.1). The proof regularises the partial Suslin sets
`A s = partialSuslin P s` by measurable hulls intersected with the node set,
`B s = toMeasurable μ (A s) ∩ P s`, exploits the branching identity
`A s = ⋃ₖ A (s ++ [k])` to show each leakage set `B s \ ⋃ₖ B (s ++ [k])` is `μ`-null, and a König-
type branch-building argument to show `𝒜 P` differs from the measurable set `B []` by the null
union of these leakages. -/
theorem nullMeasurableSet_suslinOp_finite (μ : Measure X) [IsFiniteMeasure μ]
    {P : List ℕ → Set X} (hP : ∀ s, MeasurableSet (P s)) :
    NullMeasurableSet (suslinOp P) μ := by
  -- The regularised hulls of the partial Suslin sets, kept inside their node set.
  set A : List ℕ → Set X := partialSuslin P with hA
  set B : List ℕ → Set X := fun s => toMeasurable μ (A s) ∩ P s with hB
  -- Basic facts about `B`.
  have hBmeas : ∀ s, MeasurableSet (B s) := fun s =>
    (measurableSet_toMeasurable _ _).inter (hP s)
  have hAsubB : ∀ s, A s ⊆ B s := by
    intro s
    refine subset_inter (subset_toMeasurable _ _) ?_
    exact (partialSuslin_subset_node P s)
  have hBsubP : ∀ s, B s ⊆ P s := fun s => inter_subset_right
  have hmeasB : ∀ s, μ (B s) = μ (A s) := by
    intro s
    refine le_antisymm ?_ (measure_mono (hAsubB s))
    calc μ (B s) ≤ μ (toMeasurable μ (A s)) := measure_mono inter_subset_left
      _ = μ (A s) := measure_toMeasurable _
  -- The child-union of a node's hulls.
  set U : List ℕ → Set X := fun s => ⋃ k : ℕ, B (s ++ [k]) with hU
  have hUmeas : ∀ s, MeasurableSet (U s) := fun s =>
    MeasurableSet.iUnion fun k => hBmeas _
  -- `A s ⊆ U s` since `A s = ⋃ₖ A (s ++ [k]) ⊆ ⋃ₖ B (s ++ [k])`.
  have hAsubU : ∀ s, A s ⊆ U s := by
    intro s
    rw [hA, partialSuslin_eq_iUnion_child]
    exact iUnion_mono fun k => hAsubB _
  -- The leakage set at `s`, and its nullity.
  set D : List ℕ → Set X := fun s => B s \ U s with hD
  have hDmeas : ∀ s, MeasurableSet (D s) := fun s => (hBmeas s).diff (hUmeas s)
  have hDnull : ∀ s, μ (D s) = 0 := by
    intro s
    have hsub : A s ⊆ B s ∩ U s := subset_inter (hAsubB s) (hAsubU s)
    have h1 : μ (A s) ≤ μ (B s ∩ U s) := measure_mono hsub
    have h2 : μ (B s ∩ U s) ≤ μ (B s) := measure_mono inter_subset_left
    have h3 : μ (B s ∩ U s) = μ (B s) := le_antisymm h2 (by rw [← hmeasB s] at h1; exact h1)
    -- `D s = B s \ (B s ∩ U s)` and the two have equal finite measure.
    have hDeq : D s = B s \ (B s ∩ U s) := by
      rw [hD]; ext x; simp only [mem_diff, mem_inter_iff]; tauto
    rw [hDeq, measure_diff inter_subset_left
      ((hBmeas s).inter (hUmeas s)).nullMeasurableSet (measure_ne_top μ _), h3, tsub_self]
  -- The total leakage is a countable union of null measurable sets, hence null measurable.
  set N : Set X := ⋃ s : List ℕ, D s with hN
  have hNmeas : MeasurableSet N := MeasurableSet.iUnion fun s => hDmeas s
  have hNnull : μ N = 0 := by
    rw [hN]
    refine measure_iUnion_null fun s => hDnull s
  -- Key inclusion: `B [] \ N ⊆ 𝒜 P`. Build a branch by following membership in `B`.
  have hkey : B [] \ N ⊆ suslinOp P := by
    intro x hx
    obtain ⟨hxB0, hxN⟩ := hx
    -- `x ∉ D s` for every `s`, i.e. `x ∈ B s → x ∈ U s`.
    have hstep : ∀ s, x ∈ B s → ∃ k, x ∈ B (s ++ [k]) := by
      intro s hxs
      have : x ∉ D s := fun h => hxN (mem_iUnion.2 ⟨s, h⟩)
      rw [hD, mem_diff, not_and, not_not] at this
      have := this hxs
      rw [hU, mem_iUnion] at this
      exact this
    -- A child-choosing function carrying the membership witness.
    choose g hg using hstep
    -- Build the branch as a tower of nodes carrying `x ∈ B ·`, by recursion on a subtype.
    let step : {s : List ℕ // x ∈ B s} → {s : List ℕ // x ∈ B s} :=
      fun p => ⟨p.1 ++ [g p.1 p.2], hg p.1 p.2⟩
    let branch : ℕ → {s : List ℕ // x ∈ B s} :=
      fun n => step^[n] ⟨[], hxB0⟩
    have hbranch0 : (branch 0).1 = [] := rfl
    have hbranchsucc : ∀ n, (branch (n + 1)).1 = (branch n).1 ++ [g (branch n).1 (branch n).2] := by
      intro n
      simp only [branch, Function.iterate_succ_apply']
      rfl
    have hxbranch : ∀ n, x ∈ B (branch n).1 := fun n => (branch n).2
    -- The branch function `k n`, with `restr k n = (branch n).1`.
    let k : ℕ → ℕ := fun n => g (branch n).1 (branch n).2
    have hrestr : ∀ n, restr k n = (branch n).1 := by
      intro n
      induction n with
      | zero => simp [hbranch0]
      | succ m ih => rw [restr_succ, ih, hbranchsucc m]
    -- Conclude: `x ∈ ⋂ n, P (restr k n)`, hence `x ∈ 𝒜 P`.
    rw [mem_suslinOp]
    refine ⟨k, fun n => ?_⟩
    rw [hrestr n]
    exact hBsubP _ (hxbranch n)
  -- `𝒜 P ⊆ B []` and `B [] \ 𝒜 P ⊆ N` (null), so `𝒜 P` is `NullMeasurableSet`.
  have hSsubB0 : suslinOp P ⊆ B [] := by
    rw [← partialSuslin_nil P]; exact hAsubB []
  -- `B [] = 𝒜 P ∪ (B [] \ 𝒜 P)` and the difference is null.
  have hdiffnull : μ (B [] \ suslinOp P) = 0 := by
    refine measure_mono_null ?_ hNnull
    -- `B [] \ 𝒜 P ⊆ N`: if `x ∈ B [] \ N` then `x ∈ 𝒜 P` by `hkey`, contrapositive.
    intro x hx
    by_contra hxN
    exact hx.2 (hkey ⟨hx.1, hxN⟩)
  -- `𝒜 P = B [] \ (B [] \ 𝒜 P)`.
  have hSeq : suslinOp P = B [] \ (B [] \ suslinOp P) := by
    rw [diff_diff_right_self, inter_eq_right.2 hSsubB0]
  rw [hSeq]
  exact (hBmeas []).nullMeasurableSet.diff (NullMeasurableSet.of_null hdiffnull)

/-- **Measurability of the Suslin operation, σ-finite case.** For an `SFinite` measure `μ`, the
Suslin operation applied to a scheme of measurable sets is `NullMeasurableSet`. Reduce to the
finite case via a finite measure `ν` with `μ ≪ ν` (`exists_isFiniteMeasure_absolutelyContinuous`)
and transfer along `μ ≪ ν` with `NullMeasurableSet.mono_ac`. -/
theorem nullMeasurableSet_suslinOp (μ : Measure X) [SFinite μ]
    {P : List ℕ → Set X} (hP : ∀ s, MeasurableSet (P s)) :
    NullMeasurableSet (suslinOp P) μ := by
  obtain ⟨ν, _, hμν, _⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  exact (nullMeasurableSet_suslinOp_finite ν hP).mono_ac hμν

end Measurability

/-! ### Every analytic set is a Suslin operation of closed sets -/

section AnalyticToSuslin

open SuslinScheme PiNat

variable {X : Type*} [TopologicalSpace X]

/-- Equality of `restr`-truncations is agreement of the sequences on an initial segment. -/
theorem restr_eq_iff {f g : ℕ → ℕ} {n : ℕ} : restr f n = restr g n ↔ ∀ i < n, f i = g i := by
  rw [restr, restr, List.ofFn_inj]
  constructor
  · intro h i hi
    have := congrFun h ⟨i, hi⟩
    simpa using this
  · intro h
    funext i
    exact h i i.2

/-- The agreement set `{y | restr y n = restr g n}` is exactly the Baire-space cylinder
`PiNat.cylinder g n`. -/
theorem agree_eq_cylinder (g : ℕ → ℕ) (n : ℕ) :
    {y : ℕ → ℕ | restr y n = restr g n} = cylinder g n := by
  ext y
  rw [mem_setOf_eq, restr_eq_iff, PiNat.mem_cylinder_iff]

/-- **Every analytic set is the Suslin operation of a scheme of closed sets.** For a continuous
`f : (ℕ → ℕ) → X` into a regular (e.g. Polish) space, `range f = 𝒜 P` where
`P s = closure (f '' {y | y extends s})`. The scheme sets are closed.

Forward: `f g ∈ closure (f '' cylinder g n)` for every `n`. Backward: if `x` lies in every
`closure (f '' cylinder g n)`, then since the cylinders form a neighbourhood basis of `g` and `f`
is continuous, `x` lies in every closed neighbourhood of `f g`; by regularity `x = f g`. -/
theorem analyticSet_eq_suslinOp_closed [RegularSpace X] [T1Space X] {f : (ℕ → ℕ) → X}
    (hf : Continuous f) :
    ∃ P : List ℕ → Set X, (∀ s, IsClosed (P s)) ∧ range f = suslinOp P := by
  refine ⟨fun s => closure (f '' {y : ℕ → ℕ | restr y s.length = s}), fun s => isClosed_closure, ?_⟩
  ext x
  rw [mem_suslinOp]
  constructor
  · -- `x = f g ∈ closure (f '' cylinder g n)` for all `n`.
    rintro ⟨g, rfl⟩
    refine ⟨g, fun n => ?_⟩
    rw [restr_length, agree_eq_cylinder]
    exact subset_closure (mem_image_of_mem f (self_mem_cylinder g n))
  · -- From membership in all closures, recover `x = f g` by regularity.
    rintro ⟨g, hg⟩
    have hgcyl : ∀ n, x ∈ closure (f '' cylinder g n) := by
      intro n
      have := hg n
      rwa [restr_length, agree_eq_cylinder] at this
    -- `x` lies in every closed neighbourhood of `f g`.
    suffices hx : x = f g by rw [hx]; exact mem_range_self g
    by_contra hne
    -- In a regular space there is a closed neighbourhood `K` of `f g` with `x ∉ K`.
    obtain ⟨K, hKnhds, hKclosed, hxK⟩ :
        ∃ K, K ∈ 𝓝 (f g) ∧ IsClosed K ∧ x ∉ K := by
      have : ({x}ᶜ : Set X) ∈ 𝓝 (f g) := isOpen_compl_singleton.mem_nhds (Ne.symm hne)
      obtain ⟨K, ⟨hKnhds, hKclosed⟩, hKsub⟩ := (closed_nhds_basis (f g)).mem_iff.1 this
      exact ⟨K, hKnhds, hKclosed, fun hxK => hKsub hxK rfl⟩
    -- By continuity, `f ⁻¹' interior K` is an open neighbourhood of `g`.
    have hKint : interior K ∈ 𝓝 (f g) := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hKnhds)
    have hpre_nhds : f ⁻¹' interior K ∈ 𝓝 g := hf.continuousAt.preimage_mem_nhds hKint
    have hpre_open : IsOpen (f ⁻¹' interior K) := isOpen_interior.preimage hf
    obtain ⟨c, ⟨y, n, rfl⟩, hgc, hcsub⟩ :=
      (isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open
        (mem_of_mem_nhds hpre_nhds) hpre_open
    -- `f '' cylinder ⊆ interior K ⊆ K`, so its closure is in `K`, but `x ∉ K`.
    rw [← mem_cylinder_iff_eq.1 hgc] at hcsub
    have hsubK : closure (f '' cylinder g n) ⊆ K := by
      refine closure_minimal ?_ hKclosed
      calc f '' cylinder g n ⊆ f '' (f ⁻¹' interior K) := image_mono hcsub
        _ ⊆ interior K := image_preimage_subset _ _
        _ ⊆ K := interior_subset
    exact hxK (hsubK (hgcyl n))

end AnalyticToSuslin

/-! ### Universal measurability of analytic sets -/

section UniversalMeasurability

open SuslinScheme

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Analytic sets are universally measurable for every σ-finite measure** (Lusin's theorem, via
the Suslin operation). Every analytic subset of a standard Borel (Polish) space is
`NullMeasurableSet` for every `SFinite` measure `μ` — in particular for every finite, probability
or σ-finite measure, including the probability measure of the multiplicative ergodic theorem.

The proof composes the two halves built above: an analytic set is the Suslin operation of a scheme
of closed (hence measurable) sets (`analyticSet_eq_suslinOp_closed`), and the Suslin operation of a
measurable scheme is `NullMeasurableSet` (`nullMeasurableSet_suslinOp`).

The `SFinite` hypothesis is essential: see `not_nullMeasurableSet_count_of_not_measurableSet` — for
the (non-σ-finite) counting measure, `NullMeasurableSet` collapses to Borel measurability, so a
non-Borel analytic set is *not* null measurable. -/
theorem AnalyticSet.nullMeasurableSet_sFinite {s : Set X} (hs : AnalyticSet s) (μ : Measure X)
    [SFinite μ] : NullMeasurableSet s μ := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, hrange⟩
  · exact nullMeasurableSet_empty
  · obtain ⟨P, hclosed, hPeq⟩ := analyticSet_eq_suslinOp_closed hf
    rw [← hrange, hPeq]
    exact nullMeasurableSet_suslinOp μ fun t => (hclosed t).measurableSet

end UniversalMeasurability

/-! ### The σ-finiteness hypothesis is necessary -/

section Necessity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- For the counting measure, `NullMeasurableSet` collapses to ordinary measurability: the only
`count`-null set is `∅`, so a set agrees `count`-almost-everywhere with a measurable set only if it
*equals* one. -/
theorem nullMeasurableSet_count_iff {s : Set X} :
    NullMeasurableSet s (Measure.count : Measure X) ↔ MeasurableSet s := by
  refine ⟨fun ⟨t, htm, hst⟩ => ?_, fun h => h.nullMeasurableSet⟩
  have : {x | s x ≠ t x} = (∅ : Set X) := by
    have := hst
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa [Measure.count_eq_zero_iff] using this
  have heq : s = t := by
    ext x
    by_contra h
    exact absurd (show x ∈ {x | s x ≠ t x} from h) (by rw [this]; exact id)
  rw [heq]; exact htm

/-- **The σ-finiteness hypothesis in `AnalyticSet.nullMeasurableSet_sFinite` cannot be dropped.**
If an analytic set `s` is *not* Borel measurable, then it is **not** `NullMeasurableSet` for the
counting measure. Since non-Borel analytic sets exist (Suslin: the analytic sets strictly contain
the Borel sets), the universal-measurability statement is *false* for general (non-σ-finite)
measures. -/
theorem not_nullMeasurableSet_count_of_not_measurableSet {s : Set X}
    (hs : ¬ MeasurableSet s) : ¬ NullMeasurableSet s (Measure.count : Measure X) :=
  fun h => hs (nullMeasurableSet_count_iff.1 h)

end Necessity

end MeasureTheory

end
