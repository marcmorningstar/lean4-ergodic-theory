/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Small analytic-set closure helpers

Three closure properties of analytic sets that are genuine gaps in Mathlib's `AnalyticSet` API and
are consumed by the Novikov/Kunugui–Novikov development (`ErgodicTheory.MeasureTheory`):

* `MeasureTheory.AnalyticSet.inter'` — binary intersection of analytic sets is analytic (from
  `MeasureTheory.AnalyticSet.iInter` over `Bool`);
* `MeasureTheory.AnalyticSet.union'` — binary union of analytic sets is analytic (from
  `MeasureTheory.AnalyticSet.iUnion` over `Bool`);
* `MeasureTheory.AnalyticSet.prod'` — a product of analytic sets is analytic.

All three are natural **upstream candidates** for Mathlib's
`Mathlib.MeasureTheory.Constructions.Polish.Basic`.

Reference: S. M. Srivastava, *A Course on Borel Sets*, Springer GTM 180, §4.3 (analytic sets and
their closure properties); A. S. Kechris, *Classical Descriptive Set Theory*, §14.
-/

open Set

namespace MeasureTheory

section AnalyticHelpers

variable {Z : Type*} [TopologicalSpace Z]

/-- Binary intersection of analytic sets is analytic (from `AnalyticSet.iInter` over `Bool`). -/
theorem AnalyticSet.inter' [T2Space Z] {s t : Set Z} (hs : AnalyticSet s) (ht : AnalyticSet t) :
    AnalyticSet (s ∩ t) := by
  have h : s ∩ t = ⋂ b : Bool, cond b s t := by
    ext x
    constructor
    · rintro ⟨hxs, hxt⟩
      refine mem_iInter.2 fun b => ?_
      cases b
      · exact hxt
      · exact hxs
    · intro hx
      exact ⟨mem_iInter.1 hx true, mem_iInter.1 hx false⟩
  rw [h]
  refine AnalyticSet.iInter fun b => ?_
  cases b
  · exact ht
  · exact hs

/-- Binary union of analytic sets is analytic (from `AnalyticSet.iUnion` over `Bool`). -/
theorem AnalyticSet.union' {s t : Set Z} (hs : AnalyticSet s) (ht : AnalyticSet t) :
    AnalyticSet (s ∪ t) := by
  have h : s ∪ t = ⋃ b : Bool, cond b s t := by
    ext x
    constructor
    · rintro (hxs | hxt)
      · exact mem_iUnion.2 ⟨true, hxs⟩
      · exact mem_iUnion.2 ⟨false, hxt⟩
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.1 hx
      cases b
      · exact Or.inr hb
      · exact Or.inl hb
  rw [h]
  refine AnalyticSet.iUnion fun b => ?_
  cases b
  · exact ht
  · exact hs

end AnalyticHelpers

/-- A product of analytic sets is analytic. -/
theorem AnalyticSet.prod' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : AnalyticSet s) (ht : AnalyticSet t) :
    AnalyticSet (s ×ˢ t) := by
  rw [analyticSet_iff_exists_polishSpace_range] at hs ht ⊢
  obtain ⟨β, hβt, hβp, f, hf, hfr⟩ := hs
  obtain ⟨γ, hγt, hγp, g, hg, hgr⟩ := ht
  exact ⟨β × γ, by infer_instance, by infer_instance, Prod.map f g, hf.prodMap hg,
    by rw [Set.range_prodMap, hfr, hgr]⟩

end MeasureTheory
