/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# First-return level sets and tower primitives (Rokhlin tower, issue #15)

This file develops the *first-return level-set* machinery underlying the Rokhlin (Kakutani)
tower lemma. For a measurable automorphism `e : α ≃ᵐ α` of a standard Borel probability space
and a measurable set `A`, the **first-return level set** `returnLevel e A k` collects the points
of `A` whose orbit first returns to `A` at time exactly `k`.

## Main definitions

* `Oseledets.Krieger.returnLevel e A k` — points `x ∈ A` with `eᵏ x ∈ A` and `eⁱ x ∉ A`
  for all `1 ≤ i < k`.

## Main results

* `measurableSet_returnLevel` — `returnLevel e A k` is measurable when `A` is.
* `measure_iterate_image` — iterating a measure-preserving automorphism preserves measure of
  images (the "tower floor" measure primitive).
* `disjoint_iterate_image` — iterating an injection preserves disjointness of images.
* `returnLevels_cover` — Poincaré recurrence: a.e. point of `A` first returns, so `A` is, up to
  a null set, the disjoint union `⋃ k, returnLevel e A (k+1)` of its first-return level sets.
* `tsum_returnLevel_eq` — the weak partition identity `∑' k, μ (returnLevel e A (k+1)) = μ A`.

## Index convention

`returnLevel e A 0 = A` is degenerate (the "first return before time `0`" conditions are vacuous),
so genuine first-return decompositions are indexed by `returnLevel e A (k+1)` for `k : ℕ`, i.e. by
return times `≥ 1`. Downstream tower constructions should index floors by `k : ℕ` via
`returnLevel e A (k+1)` (return time `k + 1`).

## Implementation notes

Only the *weak* partition identity `∑' k, μ (returnLevel e A (k+1)) = μ A`
(`tsum_returnLevel_eq`) is established here, which is all the Rokhlin tower construction needs.
Kac's full return-time theorem (`∑' k, (k+1) · μ (returnLevel e A (k+1)) = μ (⋃ orbit)`) is *not*
required.
-/

open MeasureTheory Filter Set
open scoped Topology Function

namespace Oseledets.Krieger

variable {α : Type*} [MeasurableSpace α]

/-- The **first-return level set**: points `x ∈ A` whose orbit under `e` returns to `A` for the
first time at time exactly `k`, i.e. `eᵏ x ∈ A` while `eⁱ x ∉ A` for every `1 ≤ i < k`.

Note `returnLevel e A 0 = A` is degenerate (the intermediate conditions are vacuous); the genuine
first-return decomposition is indexed by `returnLevel e A (k+1)`, return times `≥ 1`. -/
def returnLevel (e : α ≃ᵐ α) (A : Set α) (k : ℕ) : Set α :=
  A ∩ (e : α → α)^[k] ⁻¹' A ∩
    {x | ∀ i, 1 ≤ i → i < k → (e : α → α)^[i] x ∉ A}

/-- The "no earlier return" factor of `returnLevel` written as a bounded intersection of
measurable preimage complements. -/
theorem noEarlierReturn_eq (e : α ≃ᵐ α) (A : Set α) (k : ℕ) :
    {x | ∀ i, 1 ≤ i → i < k → (e : α → α)^[i] x ∉ A}
      = ⋂ i ∈ Finset.Ico 1 k, ((e : α → α)^[i] ⁻¹' A)ᶜ := by
  ext x
  simp only [mem_setOf_eq, mem_iInter, Finset.mem_Ico, mem_compl_iff, mem_preimage,
    and_imp]

/-- **F3a.** The first-return level set is measurable whenever `A` is. -/
theorem measurableSet_returnLevel (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet (returnLevel e A k) := by
  refine (hA.inter ?_).inter ?_
  · exact hA.preimage (e.measurable.iterate k)
  · rw [noEarlierReturn_eq]
    refine MeasurableSet.biInter (Finset.Ico 1 k).countable_toSet ?_
    intro i _
    exact (hA.preimage (e.measurable.iterate i)).compl

variable {μ : Measure α}

/-- **T1.** Iterating a measure-preserving automorphism preserves the measure of images:
`μ (eⁱ '' B) = μ B`. (The "tower floor" measure primitive.) -/
theorem measure_iterate_image (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    (i : ℕ) {B : Set α} (hB : MeasurableSet B) : μ ((e : α → α)^[i] '' B) = μ B := by
  -- `eⁱ '' B = (e.symm)ⁱ ⁻¹' B` since `(e.symm)ⁱ` is a two-sided inverse of `eⁱ`.
  have hLI : Function.LeftInverse (e.symm : α → α)^[i] (e : α → α)^[i] :=
    Function.LeftInverse.iterate e.symm_apply_apply i
  have hRI : Function.RightInverse (e.symm : α → α)^[i] (e : α → α)^[i] :=
    Function.RightInverse.iterate e.apply_symm_apply i
  have hinv : ((e : α → α)^[i] '' B) = (e.symm : α → α)^[i] ⁻¹' B :=
    congrFun (Set.image_eq_preimage_of_inverse hLI hRI) B
  rw [hinv]
  have hsymm : MeasurePreserving (e.symm : α → α) μ μ := MeasurePreserving.symm e he
  exact (hsymm.iterate i).measure_preimage hB.nullMeasurableSet

/-- **T2.** Iterating an injection preserves disjointness of images. -/
theorem disjoint_iterate_image (e : α ≃ᵐ α) (i : ℕ) {s t : Set α} (h : Disjoint s t) :
    Disjoint ((e : α → α)^[i] '' s) ((e : α → α)^[i] '' t) :=
  h.image (u := Set.univ) (Set.injOn_of_injective (e.injective.iterate i))
    (Set.subset_univ s) (Set.subset_univ t)

/-- The first-return level sets `returnLevel e A (k+1)` are pairwise disjoint: distinct
first-return times. -/
theorem pairwise_disjoint_returnLevel (e : α ≃ᵐ α) (A : Set α) :
    Pairwise (Disjoint on fun k => returnLevel e A (k + 1)) := by
  -- WLOG `j < k`; a point with first return `k+1` cannot have first return `j+1`.
  have key : ∀ j k : ℕ, j < k →
      Disjoint (returnLevel e A (j + 1)) (returnLevel e A (k + 1)) := by
    intro j k hjk
    rw [Set.disjoint_left]
    rintro x hxj hxk
    -- `x ∈ returnLevel e A (j+1)` gives `e^[j+1] x ∈ A`.
    have hmem : (e : α → α)^[j + 1] x ∈ A := hxj.1.2
    -- `x ∈ returnLevel e A (k+1)` forbids return at `i = j+1` (since `1 ≤ j+1 < k+1`).
    have hno : (e : α → α)^[j + 1] x ∉ A := hxk.2 (j + 1) (Nat.le_add_left 1 j) (by omega)
    exact hno hmem
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact key j k h
  · exact (key k j h).symm

variable [IsProbabilityMeasure μ]

/-- **F3b.** First-return cover (Poincaré recurrence): a.e. point of `A` returns to `A`, hence `A`
agrees, up to a null set, with the union of its first-return level sets
`⋃ k, returnLevel e A (k+1)` over return times `≥ 1`. -/
theorem returnLevels_cover (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    {A : Set α} (hA : MeasurableSet A) :
    A =ᵐ[μ] ⋃ k : ℕ, returnLevel e A (k + 1) := by
  -- Poincaré recurrence: a.e. `x ∈ A` returns to `A` infinitely often.
  have hcons : Conservative (e : α → α) μ := he.conservative
  have hrec : ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ n in atTop, (e : α → α)^[n] x ∈ A :=
    hcons.ae_mem_imp_frequently_image_mem hA.nullMeasurableSet
  -- The reverse inclusion is everywhere: each level set sits inside `A`.
  have hsub : (⋃ k : ℕ, returnLevel e A (k + 1)) ⊆ A := by
    refine iUnion_subset fun k => ?_
    intro x hx
    exact hx.1.1
  -- Promote the recurrence to the a.e. set equality via `ae_eq_set`.
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · -- `A \ (⋃ ...)` is null: every recurrent point lands in some level set.
    refine measure_mono_null ?_ (ae_iff.1 hrec)
    intro x hx
    simp only [mem_diff, mem_iUnion, not_exists] at hx
    obtain ⟨hxA, hxnot⟩ := hx
    -- Suppose `x` recurs; produce a least return time `≥ 1` and contradict `hxnot`.
    simp only [mem_setOf_eq, Classical.not_imp]
    refine ⟨hxA, ?_⟩
    intro hfreq
    -- From frequency at `atTop`, get some `n ≥ 1` with `eⁿ x ∈ A`.
    obtain ⟨n, hn1, hnA⟩ := (frequently_atTop.1 hfreq) 1
    have hP : ∃ k, 1 ≤ k ∧ (e : α → α)^[k] x ∈ A := ⟨n, hn1, hnA⟩
    classical
    obtain ⟨hk1, hkA⟩ := Nat.find_spec hP
    -- `Nat.find hP ≥ 1`, so write it as `m + 1`; show `x ∈ returnLevel e A (m+1)`.
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hP = m + 1 := ⟨Nat.find hP - 1, by omega⟩
    refine hxnot m ⟨⟨hxA, ?_⟩, ?_⟩
    · rw [← hm]; exact hkA
    · -- No earlier return: minimality of `Nat.find`.
      intro i hi1 hilt hiA
      exact Nat.find_min hP (by omega) ⟨hi1, hiA⟩
  · -- `(⋃ ...) \ A` is empty (genuine subset), hence null.
    rw [Set.diff_eq_empty.2 hsub]
    exact measure_empty

/-- **F3c.** Weak partition identity: the first-return level sets partition `A` up to a null set,
so their measures sum to `μ A`. (This is all the Rokhlin tower needs; Kac's full theorem is
not.) -/
theorem tsum_returnLevel_eq (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    {A : Set α} (hA : MeasurableSet A) :
    (∑' k : ℕ, μ (returnLevel e A (k + 1))) = μ A := by
  have hmeas : ∀ k : ℕ, MeasurableSet (returnLevel e A (k + 1)) := fun k =>
    measurableSet_returnLevel e hA (k + 1)
  have hdisj : Pairwise (Disjoint on fun k => returnLevel e A (k + 1)) :=
    pairwise_disjoint_returnLevel e A
  -- countable disjoint additivity
  have hunion : μ (⋃ k : ℕ, returnLevel e A (k + 1))
      = ∑' k : ℕ, μ (returnLevel e A (k + 1)) :=
    measure_iUnion hdisj hmeas
  -- the union has the measure of `A` by F3b
  have hcover : μ (⋃ k : ℕ, returnLevel e A (k + 1)) = μ A :=
    (measure_congr (returnLevels_cover e he hA)).symm
  rw [← hunion, hcover]

end Oseledets.Krieger
