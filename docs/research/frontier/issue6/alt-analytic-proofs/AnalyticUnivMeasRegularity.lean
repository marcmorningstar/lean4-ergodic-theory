/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Analytic sets are universally measurable (Choquet capacitability by inner regularity)

This module proves the classical theorem that **analytic sets in a standard Borel (Polish) space
are universally measurable**: every `MeasureTheory.AnalyticSet` is `NullMeasurableSet` for every
measure. This fills the single remaining measure-theoretic gap flagged in
`Frontier.Issue6.MeasurableProjection` (`MeasureTheory.AnalyticSet.nullMeasurableSet`, previously
left `sorry`-BLOCKED), and is independent of the dynamics: it is candidate Mathlib infrastructure.

## Strategy — direct inner regularity / capacitability by hand

We follow Strategy 2 of the task (Bogachev *Measure Theory* vol. 2 §1.10; Kechris *Classical
Descriptive Set Theory* Thm 30.13): for a **finite** Borel measure `μ` on a Polish space we show
that the *compact capacity* `compactCap μ s = ⨆ {μ K | K compact, K ⊆ s}` agrees with the outer
measure `μ s` on every analytic set `s` (Choquet capacitability). Concretely, parametrising
`s = f '' univ` for continuous `f : (ℕ → ℕ) → X`, we trim one coordinate at a time using continuity
from below of `μ` (`Monotone.measure_iUnion`, valid for the outer measure of arbitrary sets), build
coordinatewise bounds `N : ℕ → ℕ` whose *bounded body* `{g | ∀ i, g i ≤ N i}` is **compact**
(`isCompact_univ_pi`), and identify the decreasing intersection of the *closures* of the cylinder
images with the compact image `f '' (body)` (`iInter_closure_image_cyl_eq`, a
truncation + sequential-compactness argument). Continuity from above of `μ` along decreasing closed
sets (`Antitone.measure_iInter`, the asymmetry that distinguishes a capacity from an outer measure)
finishes the supremum bound.

From `compactCap μ s = μ s` we extract a measurable `Fσ`-set `B ⊆ s` with `μ B = μ s`, hence
`s =ᵐ[μ] B`, giving `NullMeasurableSet s μ`. The finite case bootstraps to **σ-finite** measures by
the standard exhaustion (`Measure.iSupSpanningSets`), which covers the probability measures of the
multiplicative ergodic theorem.

## Main results

* `MeasureTheory.IsChoquetCapacity`: the three Choquet-capacity axioms (monotone; continuous from
  below on increasing unions; continuous from above on decreasing *closed* intersections).
* `MeasureTheory.measure_isChoquetCapacity`: a finite Borel measure on a Polish space is a Choquet
  capacity.
* `MeasureTheory.compactCap`: the inner-regularity functional `⨆ {μ K | K compact ⊆ s}`.
* `MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact`: **Choquet capacitability** — for analytic `s`,
  `cap s = ⨆ {cap K | K compact ⊆ s}`.
* `MeasureTheory.AnalyticSet.nullMeasurableSet_of_isFiniteMeasure`,
  `MeasureTheory.AnalyticSet.nullMeasurableSet_of_sigmaFinite`: universal measurability of analytic
  sets for finite / σ-finite measures.

## References

* G. Choquet, *Theory of capacities*, Ann. Inst. Fourier (1954).
* A. Kechris, *Classical Descriptive Set Theory*, Thm 30.13.
* V. Bogachev, *Measure Theory* vol. 2, §1.10.
-/

universe u

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureTheory

/-! ## Compact capacity -/

/-- Compact capacity of a set `s` relative to a measure `μ`: the supremum of `μ K` over compact
subsets `K ⊆ s`. This is the inner-regularity functional whose equality with the outer measure
`μ s` characterises (null-)measurability for analytic sets. -/
noncomputable def compactCap {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) (s : Set α) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K}

/-- Compact capacity is monotone in its set argument: enlarging `s` enlarges the family of compact
subsets and so the supremum. -/
theorem compactCap_mono {α : Type*} [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hst : s ⊆ t) : compactCap μ s ≤ compactCap μ t := by
  apply sSup_le_sSup
  rintro r ⟨K, hKc, hKs, rfl⟩
  exact ⟨K, hKc, hKs.trans hst, rfl⟩

/-! ## Choquet capacity structure -/

/-- The three Choquet-capacity axioms for a functional `cap : Set α → ℝ≥0∞`: monotonicity,
sequential continuity from below along increasing unions, and sequential continuity from above
along decreasing intersections of *closed* sets. The third axiom is what distinguishes a capacity
from a general outer measure; it is the asymmetry that makes the capacitability theorem possible.
Every finite Borel measure on a Polish space is a Choquet capacity
(`measure_isChoquetCapacity`). -/
structure IsChoquetCapacity {α : Type*} [TopologicalSpace α] (cap : Set α → ℝ≥0∞) : Prop where
  /-- A capacity is monotone. -/
  mono : ∀ {s t : Set α}, s ⊆ t → cap s ≤ cap t
  /-- A capacity is continuous from below along increasing unions. -/
  iUnion_nat : ∀ f : ℕ → Set α, Monotone f → cap (⋃ n, f n) = ⨆ n, cap (f n)
  /-- A capacity is continuous from above along decreasing intersections of *closed* sets. -/
  iInter_closed : ∀ f : ℕ → Set α, Antitone f → (∀ n, IsClosed (f n)) →
    cap (⋂ n, f n) = ⨅ n, cap (f n)

/-- Every finite Borel measure on a Polish space is a Choquet capacity. Monotonicity and the
increasing-union axiom are immediate from `measure_mono` and `Monotone.measure_iUnion` (the latter
valid for the *outer* measure of arbitrary sets); the decreasing-closed-intersection axiom is
`Antitone.measure_iInter` for finite measures on closed (hence null-measurable) sets. -/
theorem measure_isChoquetCapacity {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [PolishSpace α] (μ : Measure α) [IsFiniteMeasure μ] :
    IsChoquetCapacity (fun s : Set α => μ s) := by
  refine ⟨fun hst => measure_mono hst, fun f hf => hf.measure_iUnion, fun f hf hclosed => ?_⟩
  exact hf.measure_iInter (fun n => (hclosed n).measurableSet.nullMeasurableSet)
    ⟨0, measure_ne_top μ (f 0)⟩

/-! ## Measurable sets: compact capacity equals measure -/

/-- For Borel-measurable sets, `compactCap μ s = μ s`. Monotonicity gives `≤`; the existing inner
regularity of finite Borel measures on Polish spaces (`MeasurableSet.exists_isCompact_lt_add`,
from the `InnerRegular` instance for finite measures on completely metrizable second-countable
spaces) gives `≥`. -/
theorem _root_.MeasurableSet.compactCap_eq {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [PolishSpace α] {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    (hs : MeasurableSet s) : compactCap μ s = μ s := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro r ⟨K, _, hKs, rfl⟩
    exact measure_mono hKs
  · show μ s ≤ compactCap μ s
    unfold compactCap
    have hbdd : BddAbove {r : ℝ≥0∞ | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K} :=
      ⟨μ Set.univ, fun _ ⟨_, _, hLs, hr⟩ => hr ▸ measure_mono (hLs.trans (Set.subset_univ _))⟩
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε_ne : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
    obtain ⟨K, hKs, hKc, hlt⟩ := hs.exists_isCompact_lt_add (measure_ne_top μ s) hε_ne
    calc μ s ≤ μ K + ε := le_of_lt hlt
      _ ≤ sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} + ε := by
          gcongr
          exact le_csSup hbdd ⟨K, hKc, hKs, rfl⟩

/-- `compactCap μ s` rewritten as an iterated supremum, the form convenient for transferring the
abstract capacitability statement. -/
private lemma compactCap_eq_iSup_isCompact {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) (s : Set α) :
    compactCap μ s = ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), μ K := by
  unfold compactCap
  apply le_antisymm
  · refine sSup_le ?_
    rintro r ⟨K, hKc, hKs, rfl⟩
    exact le_iSup_of_le K (le_iSup_of_le hKc (le_iSup_of_le hKs le_rfl))
  · refine iSup_le fun K => iSup_le fun hKc => iSup_le fun hKs => le_csSup ?_ ?_
    · exact ⟨μ Set.univ, fun _ ⟨_, _, _, hr⟩ => hr ▸ measure_mono (Set.subset_univ _)⟩
    · exact ⟨K, hKc, hKs, rfl⟩

/-! ## Choquet capacitability — cylinder infrastructure -/

/-- Cylinder set: the sequences bounded by `N` on the first `n + 1` coordinates. -/
private abbrev Cyl (N : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) := {g | ∀ i, i ≤ n → g i ≤ N i}

/-- Bounded body: the sequences bounded by `N` on every coordinate; this set is compact. -/
private abbrev Bnd (N : ℕ → ℕ) : Set (ℕ → ℕ) := {g | ∀ i, g i ≤ N i}

/-- The bounded body `Bnd N` is compact, being a product of finite intervals (`Iic (N i)`). -/
private lemma isCompact_bnd (N : ℕ → ℕ) : IsCompact (Bnd N) := by
  have hpi : Bnd N = Set.pi Set.univ (fun i => Set.Iic (N i)) := by
    ext g
    simp only [Bnd, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
  rw [hpi]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (N i)).isCompact

/-- The bounded body sits inside every cylinder. -/
private lemma bnd_subset_cyl (N : ℕ → ℕ) (n : ℕ) : Bnd N ⊆ Cyl N n := fun _ hg i _ => hg i

/-- A cylinder splits as an increasing union over the bound on its next coordinate. -/
private lemma cyl_succ_eq (N : ℕ → ℕ) (n : ℕ) :
    Cyl N n = ⋃ k : ℕ, (Cyl N n ∩ {g | g (n + 1) ≤ k}) := by
  ext g
  simp only [Cyl, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  exact ⟨fun h => ⟨g (n + 1), h, le_refl _⟩, fun ⟨_, h, _⟩ => h⟩

/-- The pieces of the cylinder split are monotone in the bound on the next coordinate. -/
private lemma monotone_cyl_split (N : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k}) := by
  intro a b hab x ⟨hx1, hx2⟩
  exact ⟨hx1, le_trans hx2 hab⟩

/-- A piece of the cylinder split is itself a cylinder, with the next coordinate's bound updated. -/
private lemma cyl_inter_eq_cyl_update (N : ℕ → ℕ) (n k : ℕ) :
    Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k} = Cyl (Function.update N (n + 1) k) (n + 1) := by
  ext g
  simp only [Cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Function.update]
  constructor
  · rintro ⟨hg, hgk⟩ i hi
    by_cases heq : i = n + 1
    · subst heq; simp [hgk]
    · have : i ≤ n := by omega
      simp [heq, hg i this]
  · intro hg
    refine ⟨fun i hi => ?_, ?_⟩
    · specialize hg i (by omega)
      simp [show i ≠ n + 1 by omega] at hg
      exact hg
    · specialize hg (n + 1) (le_refl _)
      simpa using hg

/-- Two cylinders of the same level agreeing on their bounds are equal. -/
private lemma cyl_ext (N N' : ℕ → ℕ) (n : ℕ) (h : ∀ i, i ≤ n → N i = N' i) :
    Cyl N n = Cyl N' n := by
  ext g
  simp only [Cyl, Set.mem_setOf_eq]
  exact ⟨fun hg i hi => h i hi ▸ hg i hi, fun hg i hi => (h i hi).symm ▸ hg i hi⟩

/-- Truncation: replace `g i` by `min (g i) (N i)`, bringing any sequence into the bounded body. -/
private noncomputable def truncate (N : ℕ → ℕ) (g : ℕ → ℕ) : ℕ → ℕ := fun i => min (g i) (N i)

/-- The truncation of any sequence lies in the bounded body. -/
private lemma truncate_mem_bnd (N : ℕ → ℕ) (g : ℕ → ℕ) : truncate N g ∈ Bnd N :=
  fun _ => min_le_right _ _

/-- On a cylinder, truncation changes nothing on the constrained coordinates. -/
private lemma truncate_agree_on_cyl (N : ℕ → ℕ) (n : ℕ) (g : ℕ → ℕ) (hg : g ∈ Cyl N n) :
    ∀ i, i ≤ n → truncate N g i = g i := by
  intro i hi
  simp only [truncate, min_eq_left (hg i hi)]

/-- **The compactness keystone.** For continuous `f` on `ℕ → ℕ`, the decreasing intersection of the
*closures* of the cylinder images equals the image of the (compact) bounded body. The nontrivial
inclusion `⋂ closure (f '' Cyl N n) ⊆ f '' Bnd N` is proved by picking, for a point `y` in the
intersection, approximating sequences `g n ∈ Cyl N n` with `f (g n) → y`, truncating them into the
compact body, extracting a convergent subsequence whose limit `g⋆ ∈ Bnd N` satisfies
`f g⋆ = y`. -/
private lemma iInter_closure_image_cyl_eq {α : Type*} [TopologicalSpace α] [PolishSpace α]
    {f : (ℕ → ℕ) → α} (hf : Continuous f) (N : ℕ → ℕ) :
    ⋂ n, closure (f '' Cyl N n) = f '' Bnd N := by
  haveI : T2Space α := inferInstance
  apply Set.Subset.antisymm
  · letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
    intro y hy
    simp only [Set.mem_iInter] at hy
    have hclose : ∀ n, ∃ g ∈ Cyl N n, dist (f g) y < 1 / (↑n + 1) := by
      intro n
      have hyn : y ∈ closure (f '' Cyl N n) := hy n
      rw [Metric.mem_closure_iff] at hyn
      obtain ⟨z, hz, hd⟩ := hyn (1 / (↑n + 1)) (by positivity)
      obtain ⟨g, hg, hfg⟩ := hz
      exact ⟨g, hg, by rw [hfg, dist_comm]; exact hd⟩
    choose g hg_cyl hg_dist using hclose
    let g' : ℕ → (ℕ → ℕ) := fun n => truncate N (g n)
    have hg'_bnd : ∀ n, g' n ∈ Bnd N := fun n => truncate_mem_bnd N (g n)
    have hg'_agree : ∀ n i, i ≤ n → g' n i = g n i :=
      fun n => truncate_agree_on_cyl N n (g n) (hg_cyl n)
    have hBnd_seq := (isCompact_bnd N).isSeqCompact
    obtain ⟨g_star, hg_star_bnd, φ, hφ_strict, hg'_conv⟩ := hBnd_seq (fun n => hg'_bnd n)
    have hg_conv : Tendsto (fun n => g (φ n)) atTop (𝓝 g_star) := by
      rw [tendsto_pi_nhds]
      intro i
      simp only [nhds_discrete, Filter.tendsto_pure]
      have hg'_ev : ∀ᶠ n in atTop, g' (φ n) i = g_star i := by
        rw [tendsto_pi_nhds] at hg'_conv
        have hi := hg'_conv i
        simpa only [nhds_discrete, Filter.tendsto_pure] using hi
      have hφ_ev : ∀ᶠ n in atTop, i ≤ φ n :=
        (hφ_strict.tendsto_atTop).eventually (Filter.eventually_ge_atTop i)
      filter_upwards [hg'_ev, hφ_ev] with n h1 h2
      rw [← h1, hg'_agree (φ n) i h2]
    have hf_conv : Tendsto (fun n => f (g (φ n))) atTop (𝓝 (f g_star)) :=
      hf.continuousAt.tendsto.comp hg_conv
    have hfy : Tendsto (fun n => f (g (φ n))) atTop (𝓝 y) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have h1div : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h_comp : Tendsto (fun n => (1 : ℝ) / (↑(φ n) + 1)) atTop (𝓝 0) :=
        h1div.comp hφ_strict.tendsto_atTop
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp h_comp) ε hε
      refine ⟨M, fun n hn => ?_⟩
      have hsmall : (1 : ℝ) / (↑(φ n) + 1) < ε := by
        have h := hM n hn
        rwa [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at h
      exact lt_trans (hg_dist (φ n)) hsmall
    exact ⟨g_star, hg_star_bnd, tendsto_nhds_unique hf_conv hfy⟩
  · intro y hy
    simp only [Set.mem_iInter]
    intro n
    apply subset_closure
    obtain ⟨g, hg, hfg⟩ := hy
    exact ⟨g, bnd_subset_cyl N n hg, hfg⟩

/-! ## Choquet capacitability theorem -/

/-- **Choquet capacitability.** For an analytic set `s` and any Choquet capacity `cap`, the value
`cap s` equals the supremum of `cap K` over compact `K ⊆ s`. We parametrise `s = f '' univ` for
continuous `f : (ℕ → ℕ) → α`, build coordinatewise bounds `N` by induction with the increasing-union
axiom (`iUnion_nat`) trimming one coordinate at a time so that `cap (f '' Cyl N n) > t` stays just
above any `t < cap s`, then apply the decreasing-closed-intersection axiom (`iInter_closed`) to the
closures of the cylinder images and `iInter_closure_image_cyl_eq` to land on the *compact* image
`f '' Bnd N ⊆ s`. Reference: Kechris, *Classical Descriptive Set Theory*, Thm 30.13. -/
theorem AnalyticSet.cap_eq_iSup_isCompact {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [PolishSpace α] {cap : Set α → ℝ≥0∞} (hcap : IsChoquetCapacity cap)
    {s : Set α} (hs : AnalyticSet s) :
    cap s = ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), cap K := by
  apply le_antisymm
  · rw [AnalyticSet] at hs
    rcases hs with rfl | ⟨f, hf_cont, hf_range⟩
    · exact le_iSup_of_le ∅ (le_iSup_of_le isCompact_empty
        (le_iSup_of_le (Set.empty_subset _) le_rfl))
    · subst hf_range
      apply le_of_forall_lt_imp_le_of_dense
      intro t ht
      have hrange_union : range f = ⋃ k, f '' {g : ℕ → ℕ | g 0 ≤ k} := by
        rw [← Set.image_univ,
          show (Set.univ : Set (ℕ → ℕ)) = ⋃ k, {g : ℕ → ℕ | g 0 ≤ k} from by
            ext g; simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
            exact ⟨g 0, le_refl _⟩,
          Set.image_iUnion]
      have hmono_base : Monotone (fun k => f '' {g : ℕ → ℕ | g 0 ≤ k}) := by
        intro a b hab
        exact Set.image_mono fun x (hx : x 0 ≤ a) => le_trans hx hab
      rw [hrange_union, hcap.iUnion_nat _ hmono_base] at ht
      obtain ⟨k₀, hk₀⟩ := lt_iSup_iff.mp ht
      have hcyl0 : f '' {g : ℕ → ℕ | g 0 ≤ k₀} = f '' Cyl (fun _ => k₀) 0 := by
        congr 1
        ext g
        simp [Cyl]
      have rec_step : ∀ (M : ℕ → ℕ) (n : ℕ), t < cap (f '' Cyl M n) →
          ∃ k, t < cap (f '' Cyl (Function.update M (n + 1) k) (n + 1)) := by
        intro M n hlt_M
        have hsplit : cap (f '' Cyl M n)
            = ⨆ k, cap (f '' (Cyl M n ∩ {g | g (n + 1) ≤ k})) := by
          conv_lhs => rw [cyl_succ_eq M n, Set.image_iUnion]
          exact hcap.iUnion_nat _ (fun a b h => Set.image_mono (monotone_cyl_split M n h))
        rw [hsplit] at hlt_M
        obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt_M
        exact ⟨k, by rwa [cyl_inter_eq_cyl_update] at hk⟩
      let build : (n : ℕ) → { M : ℕ → ℕ // t < cap (f '' Cyl M n) } := fun n =>
        Nat.rec ⟨fun _ => k₀, hcyl0 ▸ hk₀⟩
          (fun m ⟨M_prev, hM_prev⟩ =>
            ⟨Function.update M_prev (m + 1) (Classical.choose (rec_step M_prev m hM_prev)),
              Classical.choose_spec (rec_step M_prev m hM_prev)⟩) n
      let N_seq : ℕ → (ℕ → ℕ) := fun n => (build n).val
      have hN_seq_prop : ∀ n, t < cap (f '' Cyl (N_seq n) n) := fun n => (build n).property
      have hN_seq_consistent : ∀ n i, i ≤ n → N_seq (n + 1) i = N_seq n i := by
        intro n i hi
        show (Function.update (N_seq n) (n + 1) _) i = N_seq n i
        exact Function.update_of_ne (by omega) ..
      let N : ℕ → ℕ := fun i => N_seq i i
      have hN_agree : ∀ n i, i ≤ n → N i = N_seq n i := by
        intro n
        induction n with
        | zero => intro i hi; simp only [Nat.le_zero] at hi; subst hi; rfl
        | succ m ih =>
          intro i hi
          by_cases heq : i = m + 1
          · subst heq; rfl
          · have him : i ≤ m := by omega
            show N_seq i i = N_seq (m + 1) i
            rw [hN_seq_consistent m i him]
            exact ih i him
      have hcyl_eq : ∀ n, Cyl N n = Cyl (N_seq n) n := fun n => cyl_ext N (N_seq n) n (hN_agree n)
      have hcap_bound : ∀ n, t < cap (f '' Cyl N n) := fun n => hcyl_eq n ▸ hN_seq_prop n
      set E := fun n => closure (f '' Cyl N n) with hE_def
      have hE_closed : ∀ n, IsClosed (E n) := fun _ => isClosed_closure
      have hE_anti : Antitone E := by
        intro m n hmn
        apply closure_mono
        apply Set.image_mono
        intro x (hx : ∀ i, i ≤ n → x i ≤ N i) i hi
        exact hx i (le_trans hi hmn)
      have hE_cap : ∀ n, t < cap (E n) :=
        fun n => lt_of_lt_of_le (hcap_bound n) (hcap.mono subset_closure)
      have hE_inter_cap : cap (⋂ n, E n) = ⨅ n, cap (E n) :=
        hcap.iInter_closed E hE_anti hE_closed
      have ht_le : t ≤ cap (⋂ n, E n) := by
        rw [hE_inter_cap]
        exact le_iInf fun n => le_of_lt (hE_cap n)
      have hkey : ⋂ n, E n = f '' Bnd N := iInter_closure_image_cyl_eq hf_cont N
      have hK_compact : IsCompact (f '' Bnd N) := (isCompact_bnd N).image hf_cont
      have hK_sub : f '' Bnd N ⊆ range f := Set.image_subset_range f _
      calc t ≤ cap (⋂ n, E n) := ht_le
        _ = cap (f '' Bnd N) := by rw [hkey]
        _ ≤ ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ range f), cap K :=
            le_iSup_of_le _ (le_iSup_of_le hK_compact (le_iSup_of_le hK_sub le_rfl))
  · exact iSup_le fun K => iSup_le fun _ => iSup_le fun hKs => hcap.mono hKs

/-- For an analytic set `s` and a finite Borel measure `μ` on a Polish space, the compact capacity
equals the measure: `compactCap μ s = μ s`. Capacitability (`cap_eq_iSup_isCompact`) applied to the
measure capacity (`measure_isChoquetCapacity`). -/
theorem AnalyticSet.compactCap_eq {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [PolishSpace α] {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    (hs : AnalyticSet s) : compactCap μ s = μ s := by
  rw [compactCap_eq_iSup_isCompact]
  exact (hs.cap_eq_iSup_isCompact (measure_isChoquetCapacity μ)).symm

/-! ## Universal measurability of analytic sets -/

/-- **Analytic sets are universally measurable (finite measure).** For a finite Borel measure `μ`
on a Polish space, every analytic set `s` is `NullMeasurableSet`.

We extract from `compactCap μ s = μ s` a sequence of compact subsets `Kₙ ⊆ s` with
`μ Kₙ → μ s`, whose union `B = ⋃ Kₙ` is a measurable `Fσ`-set with `B ⊆ s` and `μ B = μ s`. Since
`s ⊆ toMeasurable μ s` with `μ (toMeasurable μ s) = μ s = μ B`, the sandwich forces `s =ᵐ[μ] B`,
hence `s` is `NullMeasurableSet` by `NullMeasurableSet.congr`. -/
theorem AnalyticSet.nullMeasurableSet_of_isFiniteMeasure {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [PolishSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : AnalyticSet s) : NullMeasurableSet s μ := by
  -- From `compactCap μ s = μ s` (capacitability), build compact `Kₙ ⊆ s` with `μ Kₙ ↑ μ s`.
  have hcap : (⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), μ K) = μ s := by
    rw [← compactCap_eq_iSup_isCompact]; exact hs.compactCap_eq
  -- Error term `εₙ = (n + 1)⁻¹`, positive and tending to `0`.
  set ε : ℕ → ℝ≥0∞ := fun n => (↑(n + 1))⁻¹ with hε_def
  have hε_pos : ∀ n, 0 < ε n := fun n => ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (n + 1))
  have hε_ne : ∀ n, ε n ≠ 0 := fun n => (hε_pos n).ne'
  -- For each `n`, choose a compact `Kₙ ⊆ s` with `μ s ≤ μ Kₙ + εₙ` (finite measure).
  have hexists : ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ μ s ≤ μ K + ε n := by
    intro n
    by_cases hμs : μ s = 0
    · exact ⟨∅, isCompact_empty, Set.empty_subset _, by simp [hμs]⟩
    -- `μ s = ⨆ K, μ K`; pick a compact within `εₙ` of the supremum.
    have hlt : μ s - ε n < (⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), μ K) := by
      rw [hcap]; exact ENNReal.sub_lt_self (measure_ne_top μ s) hμs (hε_ne n)
    rw [lt_iSup_iff] at hlt
    obtain ⟨K, hlt⟩ := hlt
    rw [lt_iSup_iff] at hlt
    obtain ⟨hKc, hlt⟩ := hlt
    rw [lt_iSup_iff] at hlt
    obtain ⟨hKs, hlt⟩ := hlt
    refine ⟨K, hKc, hKs, ?_⟩
    -- `μ s - εₙ < μ K` gives `μ s ≤ μ K + εₙ`.
    have hle : μ s - ε n ≤ μ K := hlt.le
    rwa [tsub_le_iff_right] at hle
  choose K hKc hKs hKle using hexists
  -- The `Fσ`-set `B = ⋃ Kₙ` is measurable, `⊆ s`, and `μ B = μ s`.
  set B : Set α := ⋃ n, K n with hB_def
  have hB_meas : MeasurableSet B := MeasurableSet.iUnion fun n => (hKc n).isClosed.measurableSet
  have hB_sub : B ⊆ s := Set.iUnion_subset hKs
  have hB_le : μ s ≤ μ B := by
    -- `μ s ≤ μ Kₙ + εₙ ≤ μ B + εₙ` for all `n`, and `εₙ → 0`.
    have htend : Tendsto (fun n : ℕ => μ B + ε n) atTop (𝓝 (μ B)) := by
      have h0 : Tendsto ε atTop (𝓝 0) :=
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa using tendsto_const_nhds.add h0
    refine ge_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
    calc μ s ≤ μ (K n) + ε n := hKle n
      _ ≤ μ B + ε n := by gcongr; exact Set.subset_iUnion K n
  have hB_eq : μ B = μ s := le_antisymm (measure_mono hB_sub) hB_le
  -- `s =ᵐ[μ] B`: `μ (s \ B) = 0` from `measure_diff_add_inter` and additive cancellation,
  -- while `μ (B \ s) = 0` since `B ⊆ s`.
  refine NullMeasurableSet.congr hB_meas.nullMeasurableSet (ae_eq_set.mpr ⟨?_, ?_⟩).symm
  · -- `μ (s \ B) = 0` from `μ (s \ B) + μ s = μ s` and additive cancellation.
    have hsum : μ (s \ B) + μ (s ∩ B) = μ s := measure_diff_add_inter s hB_meas
    rw [Set.inter_eq_self_of_subset_right hB_sub, hB_eq] at hsum
    exact (ENNReal.add_left_inj (measure_ne_top μ s)).mp (by rw [hsum, zero_add])
  · -- `μ (B \ s) = 0`, since `B \ s = ∅`
    rw [Set.diff_eq_empty.mpr hB_sub]; exact measure_empty

/-- **Analytic sets are universally measurable (σ-finite measure).** For a σ-finite Borel measure
`μ` on a Polish space, every analytic set `s` is `NullMeasurableSet`.

This is the maximal generality in which the statement is *true*: for a non-σ-finite measure such as
the counting measure on an uncountable Polish space it can *fail*
(`AnalyticSet.not_nullMeasurableSet_count_of_not_measurableSet`). We exhaust `α` by the finite-mass
spanning sets `Sᵢ` of `μ`, apply the finite case to each finite restriction `μ.restrict Sᵢ` to get a
measurable `Bᵢ` with `s =ᵐ[μ.restrict Sᵢ] Bᵢ`, and glue: `B = ⋃ᵢ (Bᵢ ∩ Sᵢ)` is measurable with
`s =ᵐ[μ] B`. -/
theorem AnalyticSet.nullMeasurableSet_of_sigmaFinite {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [PolishSpace α] (μ : Measure α) [SigmaFinite μ]
    {s : Set α} (hs : AnalyticSet s) : NullMeasurableSet s μ := by
  -- Spanning sets `Sᵢ` of finite mass exhausting `α`.
  set S : ℕ → Set α := spanningSets μ with hS_def
  have hS_meas : ∀ i, MeasurableSet (S i) := measurableSet_spanningSets μ
  have hS_univ : ⋃ i, S i = univ := iUnion_spanningSets μ
  -- On each piece, the finite restriction yields a measurable `Bᵢ ⊆ Sᵢ` agreeing with `s` up to a
  -- `μ`-null set *within* `Sᵢ` (both directed differences null).
  have hpiece : ∀ i, ∃ B : Set α, MeasurableSet B ∧ B ⊆ S i ∧
      μ ((s \ B) ∩ S i) = 0 ∧ μ (B \ s) = 0 := by
    intro i
    haveI : IsFiniteMeasure (μ.restrict (S i)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_spanningSets_lt_top μ i⟩
    obtain ⟨B₀, -, hB₀_meas, hB₀_eq⟩ :=
      (hs.nullMeasurableSet_of_isFiniteMeasure (μ.restrict (S i))).exists_measurable_subset_ae_eq
    -- `hB₀_eq : B₀ =ᵐ[μ.restrict Sᵢ] s`; intersect the witness with `Sᵢ` to force `Bᵢ ⊆ Sᵢ`.
    obtain ⟨hnull_Bs, hnull_sB⟩ := ae_eq_set.mp hB₀_eq
    rw [Measure.restrict_apply₀' (hS_meas i).nullMeasurableSet] at hnull_Bs hnull_sB
    refine ⟨B₀ ∩ S i, hB₀_meas.inter (hS_meas i), Set.inter_subset_right, ?_, ?_⟩
    · -- `(s \ (B₀ ∩ Sᵢ)) ∩ Sᵢ = (s \ B₀) ∩ Sᵢ`, null by `hnull_sB`.
      have hrw : (s \ (B₀ ∩ S i)) ∩ S i = (s \ B₀) ∩ S i := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_diff]; tauto
      rw [hrw]; exact hnull_sB
    · -- `(B₀ ∩ Sᵢ) \ s = (B₀ \ s) ∩ Sᵢ`, null by `hnull_Bs`.
      have hrw : (B₀ ∩ S i) \ s = (B₀ \ s) ∩ S i := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_diff]; tauto
      rw [hrw]; exact hnull_Bs
  choose B hB_meas hB_sub hB_null_sB hB_null_Bs using hpiece
  -- Glue: `G = ⋃ᵢ Bᵢ` is measurable.
  set G : Set α := ⋃ i, B i with hG_def
  have hG_meas : MeasurableSet G := MeasurableSet.iUnion hB_meas
  -- `s =ᵐ[μ] G` via `ae_eq_set`, bounding both directed differences by countable null sums.
  refine NullMeasurableSet.congr hG_meas.nullMeasurableSet (ae_eq_set.mpr ⟨?_, ?_⟩).symm
  · -- `μ (s \ G) = 0`: `s \ G = ⋃ᵢ ((s \ G) ∩ Sᵢ)`, each `⊆ (s \ Bᵢ) ∩ Sᵢ` null.
    have hcover : s \ G = ⋃ i, (s \ G) ∩ S i := by
      rw [← Set.inter_iUnion, hS_univ, Set.inter_univ]
    rw [hcover]
    refine measure_iUnion_null fun i => ?_
    have hmono : (s \ G) ∩ S i ⊆ (s \ B i) ∩ S i :=
      Set.inter_subset_inter_left _ (Set.diff_subset_diff_right (Set.subset_iUnion B i))
    exact measure_mono_null hmono (hB_null_sB i)
  · -- `μ (G \ s) = 0`: `G \ s = ⋃ᵢ (Bᵢ \ s)`, each null.
    have hcover : G \ s = ⋃ i, B i \ s := by rw [hG_def, Set.iUnion_diff]
    rw [hcover]
    exact measure_iUnion_null hB_null_Bs

end MeasureTheory
