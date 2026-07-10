/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MeasureTheory.CoanalyticReduction

/-!
# The Saint Raymond and Kunugui–Novikov section theorems

Building on the weak reduction principle `ErgodicTheory.weak_reduction_coanalytic`, this module
formalises two structural theorems for Borel subsets of a product of Polish spaces.

## Main statements

* `ErgodicTheory.saintRaymond_closedSections` (Srivastava 4.7.1, Saint Raymond): for disjoint
  analytic `A₀, A₁ ⊆ X × Y` whose `A₀`-sections are closed, and a countable basis `(Vₙ)` of `Y`,
  there are Borel `Bₙ ⊆ X` with `A₁ ⊆ ⋃ₙ Bₙ ×ˢ Vₙ` and `A₀ ∩ ⋃ₙ Bₙ ×ˢ Vₙ = ∅`.
* `ErgodicTheory.kunuguiNovikov_openSections` (Srivastava 4.7.2, Kunugui–Novikov): a Borel
  `B ⊆ X × Y` all of whose sections are open is a countable union of Borel rectangles `Bₙ ×ˢ Vₙ`.

## The proof

Saint Raymond's theorem replaces `A₁` by a Borel Lusin separator (via
`MeasureTheory.AnalyticSet.measurablySeparable`), then applies the weak reduction principle to the
coanalytic family `A₁' ∩ (Cₙ ×ˢ Vₙ)` (where `Cₙ = {x | Vₙ misses the section (A₀)ₓ}`), and
Lusin-separates each analytic projection `π_X(Dₙ)` from the analytic `(Cₙ)ᶜ`. Kunugui–Novikov is
the special case `A₀ = Bᶜ`, `A₁ = B` (closed sections of `Bᶜ` = open sections of `B`).

Reference: S. M. Srivastava, *A Course on Borel Sets*, Springer GTM 180, Theorems 4.7.1 and 4.7.2.
-/

open Set MeasureTheory

namespace ErgodicTheory

section SaintRaymond

variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Srivastava 4.7.1 (Saint Raymond).** For disjoint analytic `A₀, A₁ ⊆ X × Y` with the
`A₀`-sections closed, and `(Vₙ)` a countable basis of `Y`, there are Borel `Bₙ ⊆ X` with
`A₁ ⊆ ⋃ₙ Bₙ ×ˢ Vₙ` and `A₀ ∩ ⋃ₙ Bₙ ×ˢ Vₙ = ∅`. -/
theorem saintRaymond_closedSections {A₀ A₁ : Set (X × Y)}
    (h₀ : AnalyticSet A₀) (h₁ : AnalyticSet A₁) (hdisj : Disjoint A₀ A₁)
    (hsec : ∀ x, IsClosed {y | (x, y) ∈ A₀})
    {V : ℕ → Set Y} (hV : ∀ n, IsOpen (V n))
    (hbasis : ∀ (y : Y) (u : Set Y), IsOpen u → y ∈ u → ∃ n, y ∈ V n ∧ V n ⊆ u) :
    ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n)) ∧ (A₁ ⊆ ⋃ n, B n ×ˢ V n) ∧
      (A₀ ∩ ⋃ n, B n ×ˢ V n) = ∅ := by
  classical
  -- WLOG `A₁` is Borel: replace it by a Borel separator (Lusin separation).
  obtain ⟨A₁', hA₁'sub, hA₁'disj, hA₁'meas⟩ := h₁.measurablySeparable h₀ hdisj.symm
  -- `Cₙ = {x | Vₙ misses the section (A₀)ₓ}`; its complement is analytic (a projection).
  set C : ℕ → Set X := fun n => {x | ∀ y ∈ V n, (x, y) ∉ A₀} with hC
  have hCc : ∀ n, AnalyticSet ((C n)ᶜ) := by
    intro n
    have hCeq : (C n)ᶜ = Prod.fst '' (A₀ ∩ ((univ : Set X) ×ˢ V n)) := by
      ext x
      constructor
      · intro hx
        simp only [hC, mem_compl_iff, mem_setOf_eq, not_forall, not_not, exists_prop] at hx
        obtain ⟨y, hyV, hyA⟩ := hx
        exact ⟨(x, y), ⟨hyA, ⟨mem_univ _, hyV⟩⟩, rfl⟩
      · rintro ⟨⟨x', y⟩, ⟨hyA, ⟨-, hyV⟩⟩, rfl⟩
        simp only [hC, mem_compl_iff, mem_setOf_eq, not_forall, not_not, exists_prop]
        exact ⟨y, hyV, hyA⟩
    rw [hCeq]
    exact (AnalyticSet.inter' h₀
      ((isOpen_univ.prod (hV n)).measurableSet.analyticSet)).image_of_continuous continuous_fst
  -- the closed-section decomposition of `A₀ᶜ` over the basis
  have hcompl : A₀ᶜ = ⋃ n, (C n) ×ˢ V n := by
    ext ⟨x, y⟩
    simp only [mem_compl_iff, mem_iUnion, mem_prod, hC, mem_setOf_eq]
    constructor
    · intro hxy
      obtain ⟨n, hyn, hsub⟩ := hbasis y {y' | (x, y') ∉ A₀} (hsec x).isOpen_compl hxy
      exact ⟨n, fun y' hy' => hsub hy', hyn⟩
    · rintro ⟨n, hxC, hyV⟩
      exact hxC y hyV
  -- the coanalytic sequence fed to 4.6.5: `Sₙ = A₁' ∩ (Cₙ ×ˢ Vₙ)`, whose union is the Borel `A₁'`
  set S : ℕ → Set (X × Y) := fun n => A₁' ∩ ((C n) ×ˢ V n) with hS
  have hA₁'inA₀c : A₁' ⊆ A₀ᶜ := fun p hp hp0 => (disjoint_left.1 hA₁'disj) hp0 hp
  have hSU : ⋃ n, S n = A₁' := by
    have h1 : ⋃ n, S n = A₁' ∩ ⋃ n, ((C n) ×ˢ V n) := by
      simp only [hS]
      exact (inter_iUnion _ _).symm
    rw [h1, ← hcompl, inter_eq_left]
    exact hA₁'inA₀c
  have hScompl : ∀ n, AnalyticSet ((S n)ᶜ) := by
    intro n
    have hSc : (S n)ᶜ = A₁'ᶜ ∪ (((C n)ᶜ ×ˢ (univ : Set Y)) ∪ ((univ : Set X) ×ˢ (V n)ᶜ)) := by
      simp only [hS]
      ext ⟨x, y⟩
      simp only [mem_compl_iff, mem_inter_iff, mem_union, mem_prod, mem_univ, true_and, and_true]
      tauto
    rw [hSc]
    exact AnalyticSet.union' hA₁'meas.compl.analyticSet
      (AnalyticSet.union' (AnalyticSet.prod' (hCc n) MeasurableSet.univ.analyticSet)
        (AnalyticSet.prod' MeasurableSet.univ.analyticSet (hV n).isClosed_compl.analyticSet))
  have hUmeas : MeasurableSet (⋃ n, S n) := by rw [hSU]; exact hA₁'meas
  obtain ⟨D, hDmeas, hDsub, hDU, -⟩ := weak_reduction_coanalytic hScompl hUmeas
  -- separate each projection `π_X(Dₙ)` (analytic) from `Cₙᶜ` (analytic)
  have hDS : ∀ n, D n ⊆ A₁' ∩ ((C n) ×ˢ V n) := by
    intro n
    have h := hDsub n
    simpa only [hS] using h
  have hsep : ∀ n, ∃ B : Set X, MeasurableSet B ∧ Prod.fst '' (D n) ⊆ B ∧ B ⊆ C n := by
    intro n
    have hproj : AnalyticSet (Prod.fst '' (D n)) :=
      ((hDmeas n).analyticSet).image_of_continuous continuous_fst
    have hdisj2 : Disjoint (Prod.fst '' (D n)) ((C n)ᶜ) := by
      rw [disjoint_left]
      rintro x ⟨⟨x', y⟩, hD, rfl⟩ hxC
      exact hxC ((hDS n hD).2.1)
    obtain ⟨B, hsubB, hdisjB, hmeasB⟩ := hproj.measurablySeparable (hCc n) hdisj2
    refine ⟨B, hmeasB, hsubB, fun x hx => ?_⟩
    by_contra hxC
    exact (disjoint_left.1 hdisjB) hxC hx
  choose B hBmeas hBsub hBsubC using hsep
  refine ⟨B, hBmeas, ?_, ?_⟩
  · refine hA₁'sub.trans ?_
    rw [← hSU, ← hDU]
    rintro ⟨x, y⟩ hp
    obtain ⟨n, hn⟩ := mem_iUnion.1 hp
    refine mem_iUnion.2 ⟨n, ?_⟩
    exact ⟨hBsub n ⟨(x, y), hn, rfl⟩, (hDS n hn).2.2⟩
  · ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_iUnion, mem_prod, mem_empty_iff_false, iff_false, not_and,
      not_exists]
    intro hA₀ n hxB hyV
    exact (hBsubC n hxB) y hyV hA₀

/-- **Srivastava 4.7.2 (Kunugui–Novikov).** A Borel `B ⊆ X × Y` with open sections is a countable
union of Borel rectangles over any countable basis `(Vₙ)` of `Y`. -/
theorem kunuguiNovikov_openSections {B : Set (X × Y)}
    (hB : MeasurableSet B) (hsec : ∀ x, IsOpen {y | (x, y) ∈ B})
    {V : ℕ → Set Y} (hV : ∀ n, IsOpen (V n))
    (hbasis : ∀ (y : Y) (u : Set Y), IsOpen u → y ∈ u → ∃ n, y ∈ V n ∧ V n ⊆ u) :
    ∃ Bn : ℕ → Set X, (∀ n, MeasurableSet (Bn n)) ∧ B = ⋃ n, Bn n ×ˢ V n := by
  have hsecc : ∀ x, IsClosed {y | (x, y) ∈ Bᶜ} := fun x => (hsec x).isClosed_compl
  obtain ⟨Bn, hBnmeas, hBsub, hBdisj⟩ :=
    saintRaymond_closedSections hB.compl.analyticSet hB.analyticSet disjoint_compl_left
      hsecc hV hbasis
  refine ⟨Bn, hBnmeas, subset_antisymm hBsub fun p hp => ?_⟩
  by_contra hpB
  have hmem : p ∈ Bᶜ ∩ ⋃ n, Bn n ×ˢ V n := ⟨hpB, hp⟩
  rw [hBdisj] at hmem
  exact hmem

end SaintRaymond

end ErgodicTheory
