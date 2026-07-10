/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MeasureTheory.AnalyticSetLemmas
import ErgodicTheory.MeasureTheory.NovikovSeparation

/-!
# The weak reduction principle for coanalytic sets

This module formalises the **weak reduction principle** for coanalytic sets (Srivastava 4.6.5), a
direct consequence of the generalized first separation theorem
`ErgodicTheory.generalized_first_separation`.

## Main statement

`ErgodicTheory.weak_reduction_coanalytic`: if `(Sₙ)` is a countable family of sets whose
complements are analytic (i.e. the `Sₙ` are coanalytic) and whose union `⋃ₙ Sₙ` is Borel, then
there are pairwise-disjoint measurable sets `Dₙ ⊆ Sₙ` with the same union.

## The proof

Apply the generalized first separation theorem to the analytic sets
`(⋃ₘ Sₘ) ∩ (Sₙ)ᶜ` (analytic by `MeasureTheory.AnalyticSet.inter'`), whose intersection over `n` is
empty. The resulting Borel separators `D'ₙ` yield the measurable pieces
`(⋃ₘ Sₘ) \ D'ₙ ⊆ Sₙ`; disjointifying (`disjointed`) gives the pairwise-disjoint family with the
required union.

Reference: S. M. Srivastava, *A Course on Borel Sets*, Springer GTM 180, Theorem 4.6.5.
-/

open Set Function MeasureTheory

namespace ErgodicTheory

section Reduction

variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- **Srivastava 4.6.5 (weak reduction principle for coanalytic sets).** If `(Sₙ)` have analytic
complements and `⋃ₙ Sₙ` is Borel, there are pairwise-disjoint measurable `Dₙ ⊆ Sₙ` with the same
union. -/
theorem weak_reduction_coanalytic {S : ℕ → Set Z} (hS : ∀ n, AnalyticSet (S n)ᶜ)
    (hU : MeasurableSet (⋃ n, S n)) :
    ∃ D : ℕ → Set Z, (∀ n, MeasurableSet (D n)) ∧ (∀ n, D n ⊆ S n) ∧
      (⋃ n, D n) = (⋃ n, S n) ∧ Pairwise (Disjoint on D) := by
  have hA : ∀ n, AnalyticSet ((⋃ m, S m) ∩ (S n)ᶜ) := fun n =>
    AnalyticSet.inter' hU.analyticSet (hS n)
  have hint : ⋂ n, ((⋃ m, S m) ∩ (S n)ᶜ) = ∅ := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨n, hn⟩ := mem_iUnion.1 (h 0).1
    exact (h n).2 hn
  obtain ⟨D', hD'meas, hD'sub, hD'int⟩ := generalized_first_separation hA hint
  have key : ∀ n, (⋃ m, S m) \ D' n ⊆ S n := by
    intro n x hx
    by_contra hxS
    exact hx.2 (hD'sub n ⟨hx.1, hxS⟩)
  have hcover : ⋃ n, ((⋃ m, S m) \ D' n) = ⋃ m, S m := by
    ext x
    simp only [mem_iUnion, mem_diff]
    constructor
    · rintro ⟨n, hxU, -⟩
      exact hxU
    · intro hxU
      by_contra h
      push Not at h
      have hxint : x ∈ ⋂ n, D' n := mem_iInter.2 fun n => h n hxU
      rw [hD'int] at hxint
      exact hxint
  refine ⟨disjointed (fun n => (⋃ m, S m) \ D' n),
    fun n => MeasurableSet.disjointed (fun m => hU.diff (hD'meas m)) n,
    fun n => (disjointed_subset _ n).trans (key n), ?_, disjoint_disjointed _⟩
  rw [iUnion_disjointed, hcover]

end Reduction

end ErgodicTheory
