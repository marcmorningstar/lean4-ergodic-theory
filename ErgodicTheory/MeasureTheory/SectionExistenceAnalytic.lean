/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MeasureTheory.ProbabilityMeasurePolish
import ErgodicTheory.MeasureTheory.PushforwardContinuous
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UnitInterval

/-!
# Analyticity of the section-existence set (issue #61, tiers 1 + 2)

For a compact metric (Borel) space `X`, consider the parameter tuple

`p = (T, S, π, μ, ν) ∈ C(X,X) × C(X,X) × C(X,X) × P(X) × P(X)`

together with a candidate continuous section `s ∈ C(X,X)`.  The **section relation**
`SectionRel p s` bundles the five equalizer conditions that make `s` a genuine continuous,
measure-preserving equivariant section of the factor map `π` intertwining the base dynamics `T`
with the factor dynamics `S`:

* `π ∘ T = S ∘ π`   — `π` is a topological semiconjugacy `(X, T) → (X, S)`;
* `π_* μ = ν`       — `π` transports the base measure `μ` to the factor measure `ν`;
* `π ∘ s = id`      — `s` is a continuous right inverse (section) of `π`;
* `s ∘ S = T ∘ s`   — `s` is equivariant (intertwines `S` with `T`);
* `s_* ν = μ`       — `s` is measure-preserving.

## Main results

* `ErgodicTheory.isClosed_sectionRel` — the relation is a closed subset of `Params × C(X,X)`:
  every conjunct is an equalizer of jointly continuous maps into a Hausdorff space (composition is
  jointly continuous, `ContinuousMap.continuous_comp'`; pushforward is jointly continuous,
  `MeasureTheory.continuous_probabilityMeasure_map_compact`).
* `ErgodicTheory.sectionExists_analyticSet` (**tier 1**) — the set of parameters admitting *some*
  continuous section, `{p | ∃ s, SectionRel p s}`, is **analytic**: it is the continuous image
  `Prod.fst '' (closed relation)` of a closed subset of a Polish space.
* `ErgodicTheory.isSealed_coanalyticSet` (**tier 2**) — dually, the set of *sealed* parameters
  (`IsSealed p`, i.e. admitting no continuous section) is **coanalytic** (its complement is
  analytic).

The identity parameter certifies non-vacuity (`ErgodicTheory.sectionRel_id`,
`ErgodicTheory.sectionExists_nonempty`).

## Scope (honest disclosure)

This is the issue's sanctioned "restricted class first" reading.  The formalised statement is about
**continuous** sections over **compact-metric parametrised** systems, for which `C(X,X)`,
`P(X)`, and their products are all Polish (assembled in `ProbabilityMeasurePolish`) — so the
descriptive-set-theoretic hierarchy applies verbatim.

* The **classical** section-existence problem of Foreman–Rudolph–Weiss (Ann. of Math. **173**
  (2011), and Foreman–Weiss) is stated for **arbitrary measurable** sections over the `L⁰`/`MALG`
  parametrisation of measure-preserving systems.  Formalising *that* needs `L⁰` (measurable maps
  mod null sets) as a Polish space — infrastructure Mathlib currently lacks — so it is out of scope
  here (disclosed, not silently narrowed).
* The **tier-3** hardness statement (that the sealed set is `Σ¹₁`-complete / not Borel) needs the
  Borel-reduction and `Σ¹₁`-completeness machinery of descriptive set theory (Kechris §14, §27),
  which is also absent from Mathlib; it is disclosed here with the FRW / Foreman–Weiss citations and
  is a separate mini-project.
* A concrete **sealed witness** (a parameter for which no continuous measure-preserving equivariant
  section exists — e.g. the #58 merge factor, which admits combinatorial 1-block sections but whose
  measure-preservation condition genuinely bites) would show `{p | IsSealed p}` is nonempty; a
  formal such witness is deliberately left to its own follow-up.

Reference: A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156, §14, §17.E, §27; M. Foreman,
D. J. Rudolph, B. Weiss, *The conjugacy problem in ergodic theory*, Ann. of Math. **173** (2011).
-/

open Set MeasureTheory
open scoped unitInterval

namespace ErgodicTheory

section SectionExistence

variable {X : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- The Polish parameter space `C(X,X) × C(X,X) × C(X,X) × P(X) × P(X)`, holding
`(T, S, π, μ, ν)`: the base map, factor map, factor projection, base measure, factor measure. -/
abbrev Params (X : Type*) [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] : Type _ :=
  C(X, X) × C(X, X) × C(X, X) × ProbabilityMeasure X × ProbabilityMeasure X

/-- The space of continuous maps on a compact, second-countable metric space is **Polish**:
`ContinuousMap.instMetricSpace` (uniform metric) + completeness on a compact domain
(`CompleteSpace C(X,X)`) give complete metrizability, and
`ContinuousMap.instSecondCountableTopology` gives second countability. -/
instance polishSpace_continuousMap : PolishSpace C(X, X) := inferInstance

/-- The **section relation**: `s` is a continuous, measure-preserving, equivariant section of the
factor map `π` intertwining `T` and `S`, for the parameter tuple `p = (T, S, π, μ, ν)`.

The five conjuncts are `π ∘ T = S ∘ π`, `π_* μ = ν`, `π ∘ s = id`, `s ∘ S = T ∘ s`, `s_* ν = μ`. -/
def SectionRel (p : Params X) (s : C(X, X)) : Prop :=
  p.2.2.1.comp p.1 = p.2.1.comp p.2.2.1 ∧
    p.2.2.2.1.map p.2.2.1.continuous.measurable.aemeasurable = p.2.2.2.2 ∧
    p.2.2.1.comp s = ContinuousMap.id X ∧
    s.comp p.2.1 = p.1.comp s ∧
    p.2.2.2.2.map s.continuous.measurable.aemeasurable = p.2.2.2.1

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- Joint continuity of composition `a ↦ (f a).comp (g a)` on `C(X,X)` (needs `X` locally compact,
supplied by `CompactSpace X`), from `ContinuousMap.continuous_comp'`. -/
private theorem continuous_comp_pair {α : Type*} [TopologicalSpace α] {f g : α → C(X, X)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a ↦ (f a).comp (g a) :=
  ContinuousMap.continuous_comp'.comp (hg.prodMk hf)

omit [SecondCountableTopology X] in
/-- Joint continuity of the pushforward `a ↦ (m a)_* (k a)` on `C(X,X) × P(X)`, from
`MeasureTheory.continuous_probabilityMeasure_map_compact`. -/
private theorem continuous_map_pair {α : Type*} [TopologicalSpace α] {k : α → C(X, X)}
    {m : α → ProbabilityMeasure X} (hk : Continuous k) (hm : Continuous m) :
    Continuous fun a ↦ (m a).map (k a).continuous.measurable.aemeasurable :=
  MeasureTheory.continuous_probabilityMeasure_map_compact.comp (hk.prodMk hm)

/-- **The section relation is closed** in `Params × C(X,X)`.  Each of the five conjuncts is an
equalizer of two jointly continuous maps into a Hausdorff space (`C(X,X)` is metric;
`ProbabilityMeasure X` is `T2` via `HasOuterApproxClosed`), and a finite intersection of closed
sets is closed. -/
theorem isClosed_sectionRel :
    IsClosed {q : Params X × C(X, X) | SectionRel q.1 q.2} := by
  -- projections to the components, all continuous
  have hT : Continuous fun q : Params X × C(X, X) ↦ q.1.1 := continuous_fst.fst
  have hS : Continuous fun q : Params X × C(X, X) ↦ q.1.2.1 := continuous_fst.snd.fst
  have hπ : Continuous fun q : Params X × C(X, X) ↦ q.1.2.2.1 := continuous_fst.snd.snd.fst
  have hμ : Continuous fun q : Params X × C(X, X) ↦ q.1.2.2.2.1 :=
    continuous_fst.snd.snd.snd.fst
  have hν : Continuous fun q : Params X × C(X, X) ↦ q.1.2.2.2.2 :=
    continuous_fst.snd.snd.snd.snd
  have hs : Continuous fun q : Params X × C(X, X) ↦ q.2 := continuous_snd
  -- the five equalizers
  have ha : IsClosed {q : Params X × C(X, X) | q.1.2.2.1.comp q.1.1 = q.1.2.1.comp q.1.2.2.1} :=
    isClosed_eq (continuous_comp_pair hπ hT) (continuous_comp_pair hS hπ)
  have hb : IsClosed {q : Params X × C(X, X) |
      q.1.2.2.2.1.map q.1.2.2.1.continuous.measurable.aemeasurable = q.1.2.2.2.2} :=
    isClosed_eq (continuous_map_pair hπ hμ) hν
  have hc : IsClosed {q : Params X × C(X, X) | q.1.2.2.1.comp q.2 = ContinuousMap.id X} :=
    isClosed_eq (continuous_comp_pair hπ hs) continuous_const
  have hd : IsClosed {q : Params X × C(X, X) | q.2.comp q.1.2.1 = q.1.1.comp q.2} :=
    isClosed_eq (continuous_comp_pair hs hS) (continuous_comp_pair hT hs)
  have he : IsClosed {q : Params X × C(X, X) |
      q.1.2.2.2.2.map q.2.continuous.measurable.aemeasurable = q.1.2.2.2.1} :=
    isClosed_eq (continuous_map_pair hs hν) hμ
  have hset : {q : Params X × C(X, X) | SectionRel q.1 q.2}
      = {q : Params X × C(X, X) | q.1.2.2.1.comp q.1.1 = q.1.2.1.comp q.1.2.2.1}
        ∩ ({q : Params X × C(X, X) |
            q.1.2.2.2.1.map q.1.2.2.1.continuous.measurable.aemeasurable = q.1.2.2.2.2}
          ∩ ({q : Params X × C(X, X) | q.1.2.2.1.comp q.2 = ContinuousMap.id X}
            ∩ ({q : Params X × C(X, X) | q.2.comp q.1.2.1 = q.1.1.comp q.2}
              ∩ {q : Params X × C(X, X) |
                  q.1.2.2.2.2.map q.2.continuous.measurable.aemeasurable = q.1.2.2.2.1}))) := by
    ext q
    simp only [SectionRel, mem_setOf_eq, mem_inter_iff]
  rw [hset]
  exact ha.inter (hb.inter (hc.inter (hd.inter he)))

/-- **Tier 1 headline.**  The set of parameters admitting *some* continuous, measure-preserving,
equivariant section, `{p | ∃ s, SectionRel p s}`, is an **analytic** set: it is the projection
`Prod.fst '' (closed relation)` of the closed section relation, and a continuous image of an
analytic (here closed, hence analytic) subset of a Polish space is analytic. -/
theorem sectionExists_analyticSet :
    AnalyticSet {p : Params X | ∃ s : C(X, X), SectionRel p s} := by
  have himg : {p : Params X | ∃ s : C(X, X), SectionRel p s}
      = Prod.fst '' {q : Params X × C(X, X) | SectionRel q.1 q.2} := by
    ext p
    simp only [mem_setOf_eq, mem_image]
    constructor
    · rintro ⟨s, hs⟩; exact ⟨(p, s), hs, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, hq⟩
  rw [himg]
  exact isClosed_sectionRel.analyticSet.image_of_continuous continuous_fst

/-- A set is **coanalytic** when its complement is analytic (`Σ¹₁` dual). -/
def CoanalyticSet {α : Type*} [TopologicalSpace α] (t : Set α) : Prop := AnalyticSet tᶜ

/-- A parameter is **sealed** when it admits no continuous, measure-preserving, equivariant
section. -/
def IsSealed (p : Params X) : Prop := ¬ ∃ s : C(X, X), SectionRel p s

/-- **Tier 2 headline.**  The set of sealed parameters (admitting no continuous section) is
**coanalytic**: its complement is exactly the analytic section-existence set of tier 1. -/
theorem isSealed_coanalyticSet : CoanalyticSet {p : Params X | IsSealed p} := by
  unfold CoanalyticSet
  have hcompl : {p : Params X | IsSealed p}ᶜ = {p : Params X | ∃ s : C(X, X), SectionRel p s} := by
    ext p
    simp only [IsSealed, mem_compl_iff, mem_setOf_eq, not_not]
  rw [hcompl]
  exact sectionExists_analyticSet

/-! ### Non-vacuity: the identity parameter -/

omit [CompactSpace X] [SecondCountableTopology X] in
/-- Pushing a probability measure forward by the identity map returns it unchanged. -/
private theorem map_id_self (ν : ProbabilityMeasure X) :
    ν.map (ContinuousMap.id X).continuous.measurable.aemeasurable = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  simp only [ContinuousMap.coe_id, Measure.map_id]

/-- **Non-vacuity certificate.**  The identity parameter `(id, id, id, ν, ν)` admits the identity
section: `s = id` satisfies every conjunct of `SectionRel`. -/
theorem sectionRel_id (ν : ProbabilityMeasure X) :
    SectionRel ((ContinuousMap.id X, ContinuousMap.id X, ContinuousMap.id X, ν, ν) : Params X)
      (ContinuousMap.id X) := by
  refine ⟨rfl, map_id_self ν, ?_, rfl, map_id_self ν⟩
  exact ContinuousMap.id_comp _

/-- The analytic section-existence set is nonempty (witnessed by the identity parameter). -/
theorem sectionExists_nonempty (ν : ProbabilityMeasure X) :
    {p : Params X | ∃ s : C(X, X), SectionRel p s}.Nonempty :=
  ⟨(ContinuousMap.id X, ContinuousMap.id X, ContinuousMap.id X, ν, ν),
    ContinuousMap.id X, sectionRel_id ν⟩

end SectionExistence

/-! ### Concrete instance certificates on the unit interval -/

/-- The parameter space is well-defined and Polish on `X = [0,1]`. -/
example : PolishSpace (Params unitInterval) := inferInstance

/-- Tier 1 is non-vacuous on `[0,1]`. -/
example (ν : ProbabilityMeasure unitInterval) :
    {p : Params unitInterval | ∃ s : C(unitInterval, unitInterval), SectionRel p s}.Nonempty :=
  sectionExists_nonempty ν

/-- Tier 1: the section-existence set on `[0,1]` is analytic. -/
example :
    AnalyticSet {p : Params unitInterval | ∃ s : C(unitInterval, unitInterval), SectionRel p s} :=
  sectionExists_analyticSet

/-- Tier 2: the sealed set on `[0,1]` is coanalytic. -/
example : CoanalyticSet {p : Params unitInterval | IsSealed p} :=
  isSealed_coanalyticSet

end ErgodicTheory
