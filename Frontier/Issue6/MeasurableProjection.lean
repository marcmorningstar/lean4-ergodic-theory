/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue6.CastaingSelection
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Weak measurability of a subspace family from its measurable graph

This module discharges the last genuinely measure-theoretic node of the singular ("issue #6")
multiplicative ergodic theorem: from a **measurable graph** `{(x, v) | v ∈ V x}` of a
subspace-valued family `V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))` over a **standard Borel**
base `X`, the scalar distance maps `x ↦ infDist c (V x)` are `μ`-a.e. measurable
(`AEMeasurable`). This is exactly the `MeasurableInfDist`-style weak-measurability hypothesis
consumed by the (`sorry`-free) Castaing/polarisation converter of
`Frontier.Issue6.CastaingSelection`, now in its a.e. form.

## The route: projection of a Borel set is analytic, analytic sets are universally measurable

The sublevel set splits as a projection of the graph:
`{x | infDist c (V x) < r} = Prod.fst '' ({(x, v) | v ∈ V x} ∩ (Set.univ ×ˢ Metric.ball c r))`
(`infDist_lt_iff`, using `0 ∈ V x` for nonemptiness). The right-hand side is the image, under the
**continuous** projection `Prod.fst : X × EuclideanSpace ℝ (Fin d) → X`, of a measurable subset of
the standard Borel product `X × EuclideanSpace ℝ (Fin d)`. By the Lusin–Souslin machinery in
Mathlib (`MeasurableSet.analyticSet_image`) such an image is an **analytic set**.

Analytic sets in a standard Borel space are **universally measurable**: each is `NullMeasurableSet`
with respect to (the completion of) every measure — the classical theorem of Lusin via Choquet
capacitability. *Mathlib has the analytic-set API but not this universal-measurability theorem*
(`AnalyticSet.measurableSet_of_compl` only delivers measurability for analytic sets whose
complement is also analytic — Suslin's theorem — which does not apply to a projection in general).
It is isolated here as the single hypothesis-shaped residual `AnalyticSet.nullMeasurableSet`.

Granted that one classical fact, every sublevel set is `NullMeasurableSet`, hence `x ↦ infDist c
(V x)` is `NullMeasurable` (via `measurable_of_Iio` on the `NullMeasurableSpace` σ-algebra), hence
`AEMeasurable` (`NullMeasurable.aemeasurable`, ℝ being countably generated). This is the correct
a.e. formulation for the (a.e.) multiplicative ergodic theorem.

## Why this is the right reduction

`infDist c (V x) = ‖c − (V x).starProjection c‖` (`Frontier.infDist_eq_norm_sub_starProjection`),
so the weak measurability proved here is interderivable with measurability of the orthogonal
projector itself: the node is irreducible, and reducing it to *one* universally-true classical
measure-theory lemma (analytic ⟹ universally measurable) is the sharpest possible isolation —
strictly tighter than the Arsenin–Kunugui "σ-compact sections" route, which the present analytic
argument bypasses entirely.

## Main results

* `Frontier.analyticSet_infDist_lt`: under `[StandardBorelSpace X]`, a measurable graph makes
  `{x | infDist c (V x) < r}` an `AnalyticSet` (`sorry`-free).
* `Frontier.AnalyticSet.nullMeasurableSet` (the **isolated classical residual**, `sorry`,
  BLOCKED): an analytic set in a standard Borel space is `NullMeasurableSet` for every measure.
* `Frontier.nullMeasurableSet_infDist_lt`: the sublevel sets are `NullMeasurableSet`.
* `Frontier.aemeasurable_infDist_of_measurableGraph`: **the deliverable** — a measurable graph
  yields `AEMeasurable (fun x => infDist c (V x)) μ` for every `c` and every measure `μ`.

Literature: N. Lusin, *Leçons sur les ensembles analytiques* (1930); G. Choquet, *Theory of
capacities* (1953); S. M. Srivastava, *A Course on Borel Sets*, Thm 4.3.1 (every analytic set is
universally measurable). C. González-Tokman, A. Quas, *A semi-invertible operator Oseledets
theorem* (ETDS 2014), Appendix B.
-/

open scoped Matrix
open Metric MeasureTheory Submodule Set

namespace Frontier

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-! ### The sublevel set is the projection of the graph, hence analytic -/

section Analytic

omit [MeasurableSpace X] in
/-- **The distance sublevel set is the projection of the graph through a ball.** For any `c` and
`r`, `{x | infDist c (V x) < r}` equals the projection onto `X` of the graph intersected with the
slab `univ ×ˢ ball c r`. The membership equivalence is `Metric.infDist_lt_iff` (the section
`V x` is nonempty as `0 ∈ V x`), turning `infDist c (V x) < r` into the existence of a graph point
`v ∈ V x` with `v ∈ ball c r`. -/
theorem image_fst_graph_inter_ball (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    {x | infDist c (V x) < r}
      = Prod.fst '' ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
          ∩ (Set.univ ×ˢ Metric.ball c r)) := by
  ext x
  simp only [mem_setOf_eq, mem_image, mem_inter_iff, Set.mem_prod, mem_univ, true_and,
    mem_ball, Prod.exists, exists_and_right]
  constructor
  · intro hx
    rcases (infDist_lt_iff ⟨0, (V x).zero_mem⟩).mp hx with ⟨v, hvV, hvdist⟩
    exact ⟨x, ⟨⟨v, hvV, by rwa [dist_comm] at hvdist⟩, rfl⟩⟩
  · rintro ⟨x', ⟨⟨v, hvV, hvdist⟩, rfl⟩⟩
    exact (infDist_lt_iff ⟨0, (V x').zero_mem⟩).mpr ⟨v, hvV, by rwa [dist_comm]⟩

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

/-- **A measurable graph makes the distance sublevel set analytic.** Over a standard Borel base
`X`, if the graph `{(x, v) | v ∈ V x}` is measurable then `{x | infDist c (V x) < r}` is an
`AnalyticSet`. By `image_fst_graph_inter_ball` it is the image, under the continuous projection
`Prod.fst`, of a measurable subset of the standard Borel product
`X × EuclideanSpace ℝ (Fin d)`; `MeasurableSet.analyticSet_image` (Lusin–Souslin) makes the
continuous image of a Borel set analytic. -/
theorem analyticSet_infDist_lt
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    AnalyticSet {x | infDist c (V x) < r} := by
  rw [image_fst_graph_inter_ball]
  have hmeas : MeasurableSet ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
      ∩ (Set.univ ×ˢ Metric.ball c r)) :=
    hgraph.inter (MeasurableSet.univ.prod measurableSet_ball)
  exact hmeas.analyticSet_image measurable_fst

end Analytic

/-! ### Analytic sets are universally measurable (the isolated classical residual) -/

section UniversalMeasurability

/-- **Analytic sets in a standard Borel space are universally measurable (the isolated classical
residual).** Every `AnalyticSet` is `NullMeasurableSet` with respect to every measure `μ`.

**This is the single remaining measure-theoretic gap and is left `sorry` (BLOCKED).** It is the
classical theorem of Lusin (via Choquet's capacitability theorem): an analytic set `A` is
`μ`-measurable up to a null set for every σ-finite measure, because `A` is `μ⋆`-capacitable and
hence Carathéodory-measurable for the outer measure of the completion. *Mathlib has the
analytic-set construction (`MeasureTheory.AnalyticSet`) and Suslin's theorem
(`AnalyticSet.measurableSet_of_compl`: analytic with analytic complement ⟹ Borel measurable), but
not the universal-measurability theorem.* Suslin's theorem does not suffice here: a projection of a
Borel set is analytic but its complement need not be analytic, so genuine universal measurability
(capacitability) is required.

The precise missing Mathlib fact is therefore: *every analytic subset of a standard Borel space is
`NullMeasurableSet` for every measure* (equivalently: is measurable for the Carathéodory σ-algebra
of `μ.toOuterMeasure`). Once available, the rest of this module is `sorry`-free. -/
theorem _root_.MeasureTheory.AnalyticSet.nullMeasurableSet
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {s : Set X} (hs : AnalyticSet s) (μ : Measure X) : NullMeasurableSet s μ := by
  sorry -- BLOCKED: Lusin's universal-measurability theorem for analytic sets (Choquet
        -- capacitability) is absent from Mathlib; Suslin's `AnalyticSet.measurableSet_of_compl`
        -- needs an analytic complement, which a Borel projection does not have. See the docstring.

end UniversalMeasurability

/-! ### Assembling a.e. weak measurability -/

section AEMeasurable

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

/-- **The distance sublevel sets are null measurable.** Combining `analyticSet_infDist_lt` with the
(isolated) universal measurability of analytic sets `AnalyticSet.nullMeasurableSet`. -/
theorem nullMeasurableSet_infDist_lt (μ : Measure X)
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    NullMeasurableSet {x | infDist c (V x) < r} μ :=
  (analyticSet_infDist_lt hgraph c r).nullMeasurableSet μ

/-- **A measurable graph yields a.e. weak measurability (the deliverable, a.e. form).** Over a
standard Borel base `X` and for every measure `μ`, a measurable graph `{(x, v) | v ∈ V x}` makes
`x ↦ infDist c (V x)` `AEMeasurable` for every `c`.

Each `Iio`-preimage `{x | infDist c (V x) < r}` is `NullMeasurableSet`
(`nullMeasurableSet_infDist_lt`); `measurable_of_Iio` over the `NullMeasurableSpace` σ-algebra
upgrades this to `NullMeasurable (fun x => infDist c (V x)) μ`, and `NullMeasurable.aemeasurable`
(ℝ countably generated) to `AEMeasurable`. This is the a.e. analogue of
`Frontier.MeasurableInfDist`, the correct hypothesis for the a.e. multiplicative ergodic
theorem. -/
theorem aemeasurable_infDist_of_measurableGraph (μ : Measure X)
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (c : EuclideanSpace ℝ (Fin d)) :
    AEMeasurable (fun x => infDist c (V x)) μ := by
  -- `NullMeasurable` of the distance map into ℝ, via the `Iio` preimages: `NullMeasurable f μ` is
  -- by definition measurability into the `NullMeasurableSpace X μ` σ-algebra.
  have hnull : NullMeasurable (fun x => infDist c (V x)) μ := by
    show @Measurable (NullMeasurableSpace X μ) ℝ _ _ (fun x => infDist c (V x))
    refine measurable_of_Iio fun r => ?_
    -- The `Iio` preimage equals the sublevel set; the goal is `NullMeasurableSet` by definition.
    show NullMeasurableSet ((fun x => infDist c (V x)) ⁻¹' Set.Iio r) μ
    have hpre : (fun x => infDist c (V x)) ⁻¹' Set.Iio r = {x | infDist c (V x) < r} := by
      ext x; simp [Set.mem_Iio]
    rw [hpre]
    exact nullMeasurableSet_infDist_lt μ hgraph c r
  exact hnull.aemeasurable

end AEMeasurable

end Frontier
