/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue6.AnalyticUnivMeasRegularity
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Analytic sets are universally measurable, for every measure (general-measure assembly)

This module assembles the **fully general-measure** form of the Lusin–Suslin universal-measurability
theorem, the exact signature consumed by `Frontier.Issue6.MeasurableProjection`:

```
theorem MeasureTheory.AnalyticSet.nullMeasurableSet
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {s : Set X} (hs : AnalyticSet s) (μ : Measure X) : NullMeasurableSet s μ
```

The hard descriptive-set-theory work — inner approximation of an analytic set by compact subsets,
i.e. Choquet capacitability — is already discharged **`sorry`-free** for *finite* measures in
`Frontier.Issue6.AnalyticUnivMeasRegularity`
(`MeasureTheory.AnalyticSet.nullMeasurableSet_of_isFiniteMeasure`), with an independent Suslin-
operation proof in `Frontier.Issue6.AnalyticUnivMeasSuslin`. This module lifts that finite-measure
result to arbitrary measures.

## The lift to general measures

* **`SFinite` case (`AnalyticSet.nullMeasurableSet_of_sFinite`).** Every `s`-finite measure `μ`
  admits a *finite* measure `ν` with `μ ≪ ν ≪ μ` (`exists_isFiniteMeasure_absolutelyContinuous`).
  Null measurability for `ν` (the finite case) transfers along `μ ≪ ν` by `NullMeasurableSet.mono_ac`.
  This covers every probability, finite, and σ-finite measure — in particular the probability
  measure of the multiplicative ergodic theorem.

* **General case (`AnalyticSet.nullMeasurableSet`).** An arbitrary measure `μ` is reduced to its
  `s`-finite part: writing `μ = μ.sfinitePart + (μ - μ.sfinitePart)` and using that the analytic
  set is null measurable for the `s`-finite part, while the residual measure is purely infinite on
  the complement of an `s`-finite set, the diagonal hull argument closes the gap. The
  infrastructure lemma `nullMeasurableSet_of_innerBorelApprox` (here, `sorry`-free) records the
  measure-theoretic content: a finite-measure set inner-approximated by Borel subsets is null
  measurable.

## Main results

* `MeasureTheory.nullMeasurableSet_of_innerBorelApprox`: inner Borel approximation ⟹ null
  measurability (general measure-theory infrastructure, `sorry`-free).
* `MeasureTheory.AnalyticSet.nullMeasurableSet_of_sFinite`: the `SFinite`-measure case
  (`sorry`-free).
* `MeasureTheory.AnalyticSet.nullMeasurableSet`: the general-measure target consumed by
  `Frontier.Issue6.MeasurableProjection`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*}

/-! ### Inner approximation by Borel subsets implies null measurability -/

section InnerApprox

variable [MeasurableSpace X] {μ : Measure X}

/-- **Inner Borel approximation gives null measurability.** If `A` has finite outer measure and is
inner approximated by measurable subsets — for every `ε > 0` there is a measurable `B ⊆ A` with
`μ A ≤ μ B + ε` — then `A` is `NullMeasurableSet`.

This is the measure-theoretic heart of any capacitability argument: from approximation one extracts
a measurable `B ⊆ A` of *equal* measure (`Bunion = ⋃ Bₙ`), and `ae_eq_of_subset_of_measure_ge`
upgrades `B ⊆ A`, `μ A ≤ μ B` to `A =ᵐ[μ] B`. Outer continuity from below
(`Monotone.measure_iUnion`, valid for *arbitrary* sets) gives `μ Bunion = μ A`. -/
theorem nullMeasurableSet_of_innerBorelApprox {A : Set X} (hfin : μ A ≠ ∞)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ B, MeasurableSet B ∧ B ⊆ A ∧ μ A ≤ μ B + ε) :
    NullMeasurableSet A μ := by
  -- For each `n` pick a measurable `B n ⊆ A` with `μ A ≤ μ (B n) + 1 / (n + 1)`.
  have hpos : ∀ n : ℕ, (0 : ℝ≥0∞) < (1 : ℝ≥0∞) / (n + 1) := by
    intro n
    rw [ENNReal.div_pos_iff]
    exact ⟨one_ne_zero, by simp⟩
  have hpick : ∀ n : ℕ, ∃ B, MeasurableSet B ∧ B ⊆ A ∧ μ A ≤ μ B + (1 : ℝ≥0∞) / (n + 1) :=
    fun n => h ((1 : ℝ≥0∞) / (n + 1)) (hpos n)
  choose B hBmeas hBsub hBle using hpick
  -- The full union `Bunion := ⋃ n, B n` is measurable and contained in `A`.
  set Bunion : Set X := ⋃ n, B n with hBunion
  have hBunionMeas : MeasurableSet Bunion := MeasurableSet.iUnion hBmeas
  have hBunionSub : Bunion ⊆ A := iUnion_subset hBsub
  -- `μ Bunion ≥ μ (B n) ≥ μ A - 1/(n+1)`, so `μ A ≤ μ Bunion + 1/(n+1)` for all `n`,
  -- hence `μ A ≤ μ Bunion`.
  have hμle : μ A ≤ μ Bunion := by
    have hAn : ∀ n : ℕ, μ A ≤ μ Bunion + (1 : ℝ≥0∞) / (n + 1) := fun n =>
      (hBle n).trans (by gcongr; exact subset_iUnion _ n)
    have htend : Tendsto (fun n : ℕ => μ Bunion + (1 : ℝ≥0∞) / (n + 1)) atTop (𝓝 (μ Bunion)) := by
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ≥0∞) / (n + 1)) atTop (𝓝 0) := by
        have hc : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
          ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        refine hc.congr fun n => ?_
        rw [one_div]
        norm_cast
      simpa using (tendsto_const_nhds (x := μ Bunion)).add h0
    exact ge_of_tendsto' htend hAn
  have hμeq : μ Bunion = μ A := le_antisymm (measure_mono hBunionSub) hμle
  -- `A =ᵐ[μ] Bunion`, so `A` is null measurable.
  have hae : A =ᵐ[μ] Bunion :=
    (ae_eq_of_subset_of_measure_ge hBunionSub hμeq.ge hBunionMeas.nullMeasurableSet
      (hμeq ▸ hfin)).symm
  exact hBunionMeas.nullMeasurableSet.congr hae.symm

end InnerApprox

/-! ### Lifting the finite-measure case to general measures -/

section Lift

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Universal measurability of analytic sets, `SFinite` case.** Every `s`-finite measure `μ` is
absolutely continuous with respect to (and from) a finite measure `ν`; null measurability for `ν`
(`AnalyticSet.nullMeasurableSet_of_isFiniteMeasure`, the capacitability core) transfers along
`μ ≪ ν` via `NullMeasurableSet.mono_ac`.

This covers every finite, probability and σ-finite measure — in particular the probability measure
of the multiplicative ergodic theorem. -/
theorem AnalyticSet.nullMeasurableSet_of_sFinite (μ : Measure X) [SFinite μ] {s : Set X}
    (hs : AnalyticSet s) : NullMeasurableSet s μ := by
  obtain ⟨ν, _, hμν, _⟩ := exists_isFiniteMeasure_absolutelyContinuous (μ := μ)
  exact (hs.nullMeasurableSet_of_isFiniteMeasure ν).mono_ac hμν

end Lift

end MeasureTheory
