/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.FirstReturn
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# The skyscraper over a base set and the tiling-a.e. theorem (Rokhlin tower, issue #15)

For a measurable automorphism `e : α ≃ᵐ α` of a standard Borel probability space and a measurable
base set `A`, the **skyscraper** over `A` is the disjoint union of the towers above the first-return
level sets of `A`,

`skyscraper e A = ⋃ k, ⋃ j ≤ k, eʲ '' (returnLevel e A (k+1))`.

This file establishes the two structural facts the Rokhlin (Kakutani) tower lemma needs from the
skyscraper:

* its floors are pairwise disjoint (the **crux** `disjoint_skyscraper_floors`), and
* it covers almost every point when `0 < μ A` (the **tiling** theorem `skyscraper_ae_univ`).

## Main definitions

* `Oseledets.Krieger.skyscraper e A` — the skyscraper over `A`.
* `Oseledets.Krieger.sweepOut e A` — the forward sweep-out `⋃ j, eʲ '' A`.
* `Oseledets.Krieger.preimageSweep e A` — the orbit-hits-`A` set `⋃ n, eⁿ ⁻¹' A`.

## Main results

* `disjoint_skyscraper_floors` — distinct skyscraper floors `eʲ '' (returnLevel e A (k+1))` are
  disjoint; this is the combinatorial crux of the tower construction.
* `skyscraper_ae_univ` — when `0 < μ A`, the skyscraper covers almost every point. Its proof
  factors through the ergodicity of the sweep-out (`sweepOut_ae_univ`) and a re-basing argument
  (`sweepOut_diff_skyscraper_subset`) that consumes Poincaré recurrence.

## Implementation notes

`returnLevel e A (k+1)` has return time `k+1`, so its "no earlier return" condition forbids returns
at times `1 ≤ i ≤ k`; a floor of column `k+1` is `eʲ '' (returnLevel e A (k+1))` with `j ≤ k`.
-/

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace Oseledets.Krieger

variable {α : Type*} [MeasurableSpace α]

/-! ## The skyscraper and its membership characterization -/

/-- The **skyscraper** over `A`: the union of the towers above the first-return level sets,
`⋃ k, ⋃ j ≤ k, eʲ '' (returnLevel e A (k+1))`. -/
def skyscraper (e : α ≃ᵐ α) (A : Set α) : Set α :=
  ⋃ k : ℕ, ⋃ j ∈ Finset.range (k + 1), (e : α → α)^[j] '' (returnLevel e A (k + 1))

/-- Membership: `y` is in the skyscraper iff there are `j ≤ k` and `x ∈ returnLevel e A (k+1)`
with `y = eʲ x`. -/
theorem mem_skyscraper_iff (e : α ≃ᵐ α) (A : Set α) (y : α) :
    y ∈ skyscraper e A ↔
      ∃ k j : ℕ, j ≤ k ∧ ∃ x ∈ returnLevel e A (k + 1), (e : α → α)^[j] x = y := by
  simp only [skyscraper, mem_iUnion, Finset.mem_range, mem_image]
  constructor
  · rintro ⟨k, j, hjk, x, hx, hxy⟩
    exact ⟨k, j, by omega, x, hx, hxy⟩
  · rintro ⟨k, j, hjk, x, hx, hxy⟩
    exact ⟨k, j, by omega, x, hx, hxy⟩

/-- Image of a measurable set under a forward iterate is measurable. `eʲ '' s` rewrites to the
preimage `(e.symm)ʲ ⁻¹' s` (the same trick as `measure_iterate_image`), which is measurable. -/
theorem measurableSet_iterate_image (e : α ≃ᵐ α) (j : ℕ) {s : Set α} (hs : MeasurableSet s) :
    MeasurableSet ((e : α → α)^[j] '' s) := by
  have hLI : Function.LeftInverse (e.symm : α → α)^[j] (e : α → α)^[j] :=
    Function.LeftInverse.iterate e.symm_apply_apply j
  have hRI : Function.RightInverse (e.symm : α → α)^[j] (e : α → α)^[j] :=
    Function.RightInverse.iterate e.apply_symm_apply j
  rw [congrFun (Set.image_eq_preimage_of_inverse hLI hRI) s]
  exact hs.preimage (e.symm.measurable.iterate j)

/-- The skyscraper is measurable: it is a countable union of measurable floors. -/
theorem measurableSet_skyscraper (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) :
    MeasurableSet (skyscraper e A) := by
  refine MeasurableSet.iUnion fun k => ?_
  refine MeasurableSet.biUnion (Finset.range (k + 1)).countable_toSet fun j _ => ?_
  exact measurableSet_iterate_image e j (measurableSet_returnLevel e hA (k + 1))

/-! ## The sweep-out sets and ergodicity -/

/-- The backward sweep-out: points whose backward orbit hits `A` (= forward image of `A`). -/
def sweepOut (e : α ≃ᵐ α) (A : Set α) : Set α := ⋃ j : ℕ, (e : α → α)^[j] '' A

/-- Forward sweep-out via preimages (the orbit-hits-`A` set). -/
def preimageSweep (e : α ≃ᵐ α) (A : Set α) : Set α := ⋃ n : ℕ, (e : α → α)^[n] ⁻¹' A

/-- `preimageSweep` is measurable. -/
theorem measurableSet_preimageSweep (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) :
    MeasurableSet (preimageSweep e A) :=
  MeasurableSet.iUnion fun n => hA.preimage (e.measurable.iterate n)

/-- `e ⁻¹' preimageSweep ⊆ preimageSweep`: orbit-hits-`A` is forward sub-invariant. -/
theorem preimage_preimageSweep_subset (e : α ≃ᵐ α) (A : Set α) :
    (e : α → α) ⁻¹' preimageSweep e A ⊆ preimageSweep e A := by
  intro x hx
  simp only [preimageSweep, mem_preimage, mem_iUnion] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  -- `hn : e^[n] (e x) ∈ A`. Goal: `∃ m, e^[m] x ∈ A`. Take `m = n + 1`.
  refine ⟨n + 1, ?_⟩
  rwa [Function.iterate_succ_apply]

/-- EASY HALF: every skyscraper floor `eʲ '' (returnLevel e A (k+1))` sits inside `eʲ '' A`,
hence inside `sweepOut`. -/
theorem skyscraper_subset_sweepOut (e : α ≃ᵐ α) (A : Set α) :
    skyscraper e A ⊆ sweepOut e A := by
  rw [skyscraper, sweepOut]
  refine iUnion_subset fun k => ?_
  refine iUnion₂_subset fun j _ => ?_
  -- `eʲ '' rl(k+1) ⊆ eʲ '' A ⊆ ⋃ j, eʲ '' A`.
  refine subset_trans (Set.image_mono ?_) (subset_iUnion (fun j => (e : α → α)^[j] '' A) j)
  intro x hx; exact hx.1.1

/-- `e '' sweepOut ⊆ sweepOut`: the orbit-forward set is image-sub-invariant. -/
theorem image_sweepOut_subset (e : α ≃ᵐ α) (A : Set α) :
    (e : α → α) '' sweepOut e A ⊆ sweepOut e A := by
  rw [sweepOut, Set.image_iUnion]
  refine iUnion_subset fun j => ?_
  -- `e '' (eʲ '' A) = e^[j+1] '' A ⊆ ⋃ j, eʲ '' A`.
  rw [← Set.image_comp, ← Function.iterate_succ']
  exact subset_iUnion (fun j => (e : α → α)^[j] '' A) (j + 1)

variable {μ : Measure α} [IsProbabilityMeasure μ]

/-- `sweepOut` is measurable. -/
theorem measurableSet_sweepOut (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) :
    MeasurableSet (sweepOut e A) :=
  MeasurableSet.iUnion fun j => measurableSet_iterate_image e j hA

/-- Ergodicity (preimage version): if `0 < μ A` then a.e. point's forward orbit hits `A`,
i.e. `preimageSweep e A =ᵐ univ`. Uses `Ergodic.ae_empty_or_univ_of_preimage_ae_le`. -/
theorem preimageSweep_ae_univ (e : α ≃ᵐ α) (herg : Ergodic (e : α → α) μ)
    {A : Set α} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    preimageSweep e A =ᵐ[μ] (univ : Set α) := by
  set V := preimageSweep e A with hVdef
  have hVmeas : MeasurableSet V := measurableSet_preimageSweep e hA
  -- `A ⊆ V` (the `n = 0` term), so `0 < μ A ≤ μ V`, hence `V` is not a.e. empty.
  have hAV : A ⊆ V := by
    intro x hx
    simp only [hVdef, preimageSweep, mem_iUnion, mem_preimage]
    exact ⟨0, by simpa using hx⟩
  have hVpos : 0 < μ V := lt_of_lt_of_le hApos (measure_mono hAV)
  have hle : (e : α → α) ⁻¹' V ≤ᵐ[μ] V :=
    HasSubset.Subset.eventuallyLE (preimage_preimageSweep_subset e A)
  rcases herg.ae_empty_or_univ_of_preimage_ae_le hVmeas.nullMeasurableSet hle with h | h
  · exact absurd (measure_congr h) (by simp [hVpos.ne'])
  · exact h

/-- Ergodicity (image version): `0 < μ A ⟹ sweepOut e A =ᵐ univ`. -/
theorem sweepOut_ae_univ (e : α ≃ᵐ α) (herg : Ergodic (e : α → α) μ)
    {A : Set α} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    sweepOut e A =ᵐ[μ] (univ : Set α) := by
  set V := sweepOut e A with hVdef
  have hVmeas : MeasurableSet V := measurableSet_sweepOut e hA
  have hAV : A ⊆ V := by
    intro x hx
    rw [hVdef, sweepOut, mem_iUnion]
    exact ⟨0, by simpa using hx⟩
  have hVpos : 0 < μ V := lt_of_lt_of_le hApos (measure_mono hAV)
  have hle : (e : α → α) '' V ≤ᵐ[μ] V :=
    HasSubset.Subset.eventuallyLE (image_sweepOut_subset e A)
  rcases herg.ae_empty_or_univ_of_image_ae_le hVmeas.nullMeasurableSet hle with h | h
  · exact absurd (measure_congr h) (by simp [hVpos.ne'])
  · exact h

/-- The non-returning bases `D := A \ ⋃ k, rl(k+1)` are null (Poincaré, via
`returnLevels_cover`). -/
theorem measure_nonReturning_eq_zero (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    {A : Set α} (hA : MeasurableSet A) :
    μ (A \ ⋃ k : ℕ, returnLevel e A (k + 1)) = 0 := by
  -- `A =ᵐ ⋃ k, rl(k+1)` (Poincaré), so the difference is null.
  have hcov := returnLevels_cover e he hA
  rw [ae_eq_set] at hcov
  exact hcov.1

/-- The re-basing inclusion. An uncovered sweep-out point re-bases to a non-returning base:
`sweepOut \ skyscraper ⊆ ⋃ j, eʲ '' D` where `D := A \ ⋃ k, rl(k+1)`.

For `y = eʲ x` with `x ∈ A`, let `j₀` be the least `m` with `(e.symm)ᵐ y ∈ A` and set
`x₀ = (e.symm)^[j₀] y ∈ A`. By minimality `x₀` has no forward return in `(0, j₀]`. Either `x₀`
first-returns at some `r > j₀` (then `y` is genuine floor `j₀` of column `r`, so `y ∈ skyscraper`,
excluded), or `x₀` never returns and `x₀ ∈ D`, so `y = e^[j₀] x₀ ∈ e^[j₀] '' D`. -/
theorem sweepOut_diff_skyscraper_subset (e : α ≃ᵐ α) (A : Set α) :
    sweepOut e A \ skyscraper e A
      ⊆ ⋃ j : ℕ, (e : α → α)^[j] '' (A \ ⋃ k, returnLevel e A (k + 1)) := by
  classical
  rintro y ⟨hysweep, hyno⟩
  -- `y ∈ sweepOut`: backward orbit hits `A`. Take least `j₀`.
  have hex : ∃ m : ℕ, (e.symm : α → α)^[m] y ∈ A := by
    rw [sweepOut, mem_iUnion] at hysweep
    obtain ⟨j, x, hxA, hxy⟩ := hysweep
    refine ⟨j, ?_⟩
    have hinv : (e.symm : α → α)^[j] ((e : α → α)^[j] x) = x :=
      Function.LeftInverse.iterate e.symm_apply_apply j x
    rw [← hxy, hinv]; exact hxA
  set j₀ := Nat.find hex with hj₀def
  have hj₀A : (e.symm : α → α)^[j₀] y ∈ A := Nat.find_spec hex
  have hj₀min : ∀ m, m < j₀ → (e.symm : α → α)^[m] y ∉ A := fun m hm => Nat.find_min hex hm
  set x₀ := (e.symm : α → α)^[j₀] y with hx₀def
  -- Forward iterate of `x₀` for `i ≤ j₀`: `e^[i] x₀ = (e.symm)^[j₀ - i] y`.
  have hforward : ∀ i, i ≤ j₀ → (e : α → α)^[i] x₀ = (e.symm : α → α)^[j₀ - i] y := by
    intro i hi
    rw [hx₀def]
    conv_lhs => rw [show j₀ = i + (j₀ - i) by omega, Function.iterate_add_apply]
    rw [Function.LeftInverse.iterate e.apply_symm_apply i]
  -- `y = e^[j₀] x₀`.
  have hyx₀ : (e : α → α)^[j₀] x₀ = y := by
    have := hforward j₀ le_rfl
    rwa [Nat.sub_self] at this
  -- `x₀` has no forward return in `(0, j₀]`: for `0 < i ≤ j₀`, `e^[i] x₀ ∉ A`.
  have hnoreturn : ∀ i, 0 < i → i ≤ j₀ → (e : α → α)^[i] x₀ ∉ A := by
    intro i hi0 hij
    rw [hforward i hij]
    exact hj₀min (j₀ - i) (by omega)
  -- Now: `x₀ ∈ D` (= `A \ ⋃ rl`), else `y ∈ skyscraper`, contradiction.
  rw [mem_iUnion]
  refine ⟨j₀, x₀, ⟨hj₀A, ?_⟩, hyx₀⟩
  rw [mem_iUnion]; rintro ⟨k, hxk⟩
  -- `x₀ ∈ rl(k+1)`: first return at `k+1`. Then `j₀ ≤ k` (else `e^[k+1] x₀ ∉ A`).
  have hjk : j₀ ≤ k := by
    by_contra h
    push Not at h  -- `k < j₀`, so `k + 1 ≤ j₀`.
    have : (e : α → α)^[k + 1] x₀ ∉ A := hnoreturn (k + 1) (by omega) (by omega)
    exact this hxk.1.2
  -- Then `y = e^[j₀] x₀` is floor `j₀ ≤ k` of column `k+1`, contradicting `hyno`.
  apply hyno
  rw [skyscraper, mem_iUnion]
  refine ⟨k, ?_⟩
  rw [mem_iUnion₂]
  refine ⟨j₀, Finset.mem_range.2 (by omega), x₀, hxk, hyx₀⟩

/-- **Tiling theorem.** When `0 < μ A`, the skyscraper covers almost every point:
`skyscraper e A =ᵐ univ`. Indeed `skyscraper ⊆ sweepOut =ᵐ univ`, and `sweepOut \ skyscraper`
is null by the re-basing inclusion together with `μ (eʲ '' D) = μ D = 0`. -/
theorem skyscraper_ae_univ (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    (herg : Ergodic (e : α → α) μ) {A : Set α} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    skyscraper e A =ᵐ[μ] (univ : Set α) := by
  have hsweep : sweepOut e A =ᵐ[μ] (univ : Set α) := sweepOut_ae_univ e herg hA hApos
  have hsub : skyscraper e A ⊆ sweepOut e A := skyscraper_subset_sweepOut e A
  have hDnull : μ (A \ ⋃ k : ℕ, returnLevel e A (k + 1)) = 0 :=
    measure_nonReturning_eq_zero e he hA
  have hdiff0 : μ (sweepOut e A \ skyscraper e A) = 0 := by
    refine measure_mono_null (sweepOut_diff_skyscraper_subset e A) ?_
    refine measure_iUnion_null fun j => ?_
    rw [measure_iterate_image e he j
      ((hA.diff (MeasurableSet.iUnion fun k => measurableSet_returnLevel e hA (k + 1))))]
    exact hDnull
  have hskysweep : skyscraper e A =ᵐ[μ] sweepOut e A := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Set.diff_eq_empty.2 hsub]; exact measure_empty
    · exact hdiff0
  exact hskysweep.trans hsweep

/-! ## The crux: skyscraper floors are pairwise disjoint -/

/-- **The crux.** Skyscraper floors are pairwise disjoint across all `(j, k)`: for
`(j₁, k₁) ≠ (j₂, k₂)` with `j₁ ≤ k₁` and `j₂ ≤ k₂`, the floors
`eʲ¹ '' (returnLevel e A (k₁+1))` and `eʲ² '' (returnLevel e A (k₂+1))` are disjoint. -/
theorem disjoint_skyscraper_floors (e : α ≃ᵐ α) (A : Set α)
    {j₁ k₁ j₂ k₂ : ℕ} (hj₁ : j₁ ≤ k₁) (hj₂ : j₂ ≤ k₂) (hne : (j₁, k₁) ≠ (j₂, k₂)) :
    Disjoint ((e : α → α)^[j₁] '' (returnLevel e A (k₁ + 1)))
      ((e : α → α)^[j₂] '' (returnLevel e A (k₂ + 1))) := by
  -- Directed claim: for `a₁ ≤ a₂`, floors are disjoint unless `(a₁, b₁) = (a₂, b₂)`.
  have key : ∀ {a₁ b₁ a₂ b₂ : ℕ}, a₁ ≤ b₁ → a₂ ≤ b₂ → a₁ ≤ a₂ → (a₁, b₁) ≠ (a₂, b₂) →
      Disjoint ((e : α → α)^[a₁] '' (returnLevel e A (b₁ + 1)))
        ((e : α → α)^[a₂] '' (returnLevel e A (b₂ + 1))) := by
    intro a₁ b₁ a₂ b₂ ha₁ ha₂ hle hne'
    rw [Set.disjoint_left]
    rintro y ⟨x₁, hx₁, hxy₁⟩ ⟨x₂, hx₂, hxy₂⟩
    -- `y = e^[a₁] x₁ = e^[a₂] x₂`.
    rcases eq_or_lt_of_le hle with rfl | hlt
    · -- `a₁ = a₂`. By injectivity `x₁ = x₂`, so `b₁ ≠ b₂`, and the level sets are disjoint.
      have hxeq : x₁ = x₂ := (e.injective.iterate a₁) (by rw [hxy₁, hxy₂])
      subst hxeq
      have hbne : b₁ ≠ b₂ := by
        intro h; exact hne' (by rw [h])
      have hpw := pairwise_disjoint_returnLevel e A (i := b₁) (j := b₂) hbne
      simp only [Function.onFun] at hpw
      rw [Set.disjoint_left] at hpw
      exact hpw hx₁ hx₂
    · -- `a₁ < a₂`. Applying `(e.symm)^[a₁]` to `e^[a₁] x₁ = e^[a₂] x₂` gives `x₁ = e^[d] x₂`,
      -- with `d := a₂ - a₁` and `1 ≤ d ≤ b₂`.
      set d := a₂ - a₁ with hd
      have hd1 : 1 ≤ d := by omega
      have hdb : d ≤ b₂ := by omega
      have hx1eq : x₁ = (e : α → α)^[d] x₂ := by
        have happ : (e.symm : α → α)^[a₁] ((e : α → α)^[a₁] x₁)
            = (e.symm : α → α)^[a₁] ((e : α → α)^[a₂] x₂) := by rw [hxy₁, hxy₂]
        rw [Function.LeftInverse.iterate e.symm_apply_apply a₁] at happ
        have : (e.symm : α → α)^[a₁] ((e : α → α)^[a₂] x₂) = (e : α → α)^[d] x₂ := by
          rw [hd]
          conv_lhs => rw [show a₂ = a₁ + (a₂ - a₁) by omega, Function.iterate_add_apply]
          rw [Function.LeftInverse.iterate e.symm_apply_apply a₁]
        rw [this] at happ
        exact happ
      -- `x₁ ∈ A`, but `x₁ = e^[d] x₂` with `1 ≤ d ≤ b₂` means `x₂` returns at `d` — contradiction.
      have hx1A : x₁ ∈ A := hx₁.1.1
      have hx2no : (e : α → α)^[d] x₂ ∉ A := hx₂.2 d hd1 (by omega)
      rw [hx1eq] at hx1A
      exact hx2no hx1A
  -- Apply `key` in the appropriate direction.
  rcases le_total j₁ j₂ with hle | hle
  · exact key hj₁ hj₂ hle hne
  · exact (key hj₂ hj₁ hle (fun h => hne (by simp [Prod.ext_iff] at h ⊢; omega))).symm

end Oseledets.Krieger
