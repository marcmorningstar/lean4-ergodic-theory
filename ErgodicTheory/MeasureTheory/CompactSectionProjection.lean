/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MeasureTheory.KunuguiNovikov
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The Novikov compact-section projection theorem

This module reaches the **Novikov projection theorem** (Srivastava 4.7.11): a Borel subset of a
product of Polish spaces whose sections are compact has a Borel projection. It is the headline of
the Kunugui–Novikov development and the last measure-theoretic input to the everywhere-Borel
singular Lyapunov filtration (`ErgodicTheory.Singular.SingularFiltrationBorel`).

## Main statements

* `ErgodicTheory.exists_nat_basis`: an enumerated countable basis of a second-countable space.
* `ErgodicTheory.exists_finer_polish_isClosed_of_closedSections` (Srivastava 4.7.4): a Borel
  `B ⊆ X × Y` with closed sections becomes closed after refining the Polish topology on `X` only.
* `ErgodicTheory.measurableSet_image_fst_of_isCompact_sections_of_compactSpace`: the projection is
  Borel when `Y` is compact (proper-map projection along the compact fibre).
* `ErgodicTheory.exists_continuous_injective_toCube`: every Polish space injects continuously into
  the compact Polish cube `ℕ → Icc 0 1`.
* `ErgodicTheory.measurableSet_image_fst_of_isCompact_sections` (Srivastava 4.7.11, Novikov): the
  general compact-section projection theorem, obtained from the compact case by pushing `B` into the
  cube along a continuous injection (a measurable embedding by Lusin–Souslin).

## The proof

For the compact-fibre case, refine `X`'s topology so that `B` is closed (4.7.4, using the
Kunugui–Novikov rectangle structure of `Bᶜ` and a clopenable refinement), project along the proper
map `Prod.fst` (compact fibre), and transfer Borel-ness back through `borel_eq_borel_of_le`. The
general case compactifies `Y` via a continuous injection into `ℕ → Icc 0 1`.

Reference: S. M. Srivastava, *A Course on Borel Sets*, Springer GTM 180, §4.7 (Theorems 4.7.4 and
4.7.11); A. S. Kechris, *Classical Descriptive Set Theory*, §28 (Arsenin–Kunugui).
-/

open Set Function MeasureTheory Metric Topology

namespace ErgodicTheory

section Novikov4711

variable {X Y : Type*}
  [tX : TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Enumerated countable basis of a second-countable space (with possible `∅` entries). -/
theorem exists_nat_basis (Z : Type*) [TopologicalSpace Z] [SecondCountableTopology Z] :
    ∃ V : ℕ → Set Z, (∀ n, IsOpen (V n)) ∧
      ∀ (y : Z) (u : Set Z), IsOpen u → y ∈ u → ∃ n, y ∈ V n ∧ V n ⊆ u := by
  obtain ⟨b, hbc, -, hbbasis⟩ := TopologicalSpace.exists_countable_basis Z
  have hcount : (insert (∅ : Set Z) b).Countable := hbc.insert ∅
  obtain ⟨V, hV⟩ := hcount.exists_eq_range ⟨∅, mem_insert _ _⟩
  refine ⟨V, ?_, ?_⟩
  · intro n
    have hmem : V n ∈ insert (∅ : Set Z) b := hV ▸ mem_range_self n
    rcases mem_insert_iff.1 hmem with h | h
    · rw [h]; exact isOpen_empty
    · exact hbbasis.isOpen h
  · intro y u hu hyu
    obtain ⟨t, htb, hyt, htsub⟩ := hbbasis.exists_subset_of_mem_open hyu hu
    have hmem : t ∈ insert (∅ : Set Z) b := mem_insert_of_mem _ htb
    rw [hV] at hmem
    obtain ⟨n, rfl⟩ := hmem
    exact ⟨n, hyt, htsub⟩

/-- **Srivastava 4.7.4.** A Borel `B ⊆ X × Y` with closed sections becomes closed after refining
the Polish topology on `X` only (a countable clopenable refinement of the `4.7.2` rectangles). -/
theorem exists_finer_polish_isClosed_of_closedSections {B : Set (X × Y)}
    (hB : MeasurableSet B) (hsec : ∀ x, IsClosed {y | (x, y) ∈ B}) :
    ∃ t' : TopologicalSpace X, t' ≤ tX ∧ @PolishSpace X t' ∧
      IsClosed[@instTopologicalSpaceProd X Y t' _] B := by
  obtain ⟨V, hV, hbasis⟩ := exists_nat_basis Y
  have hsecc : ∀ x, IsOpen {y | (x, y) ∈ Bᶜ} := fun x => (hsec x).isOpen_compl
  obtain ⟨Bn, hBnmeas, hBc⟩ := kunuguiNovikov_openSections hB.compl hsecc hV hbasis
  choose m mle mpolish mclosed mopen using fun n => (hBnmeas n).isClopenable
  obtain ⟨t', ht'm, ht'le, ht'polish⟩ := PolishSpace.exists_polishSpace_forall_le m mle mpolish
  refine ⟨t', ht'le, ht'polish, ?_⟩
  have hopen : IsOpen[@instTopologicalSpaceProd X Y t' _] Bᶜ := by
    rw [hBc]
    exact isOpen_iUnion fun n => IsOpen.prod ((mopen n).mono (ht'm n)) (hV n)
  have hcl := hopen.isClosed_compl
  rwa [compl_compl] at hcl

/-- **Srivastava 4.7.11 for compact fibre space.** If `Y` is moreover compact, a Borel
`B ⊆ X × Y` with compact sections has Borel projection: refine the topology of `X` to make `B`
closed (4.7.4), project along the compact fibre (proper map), and transfer Borel-ness back
(`borel_eq_borel_of_le`, Lusin–Souslin). -/
theorem measurableSet_image_fst_of_isCompact_sections_of_compactSpace [CompactSpace Y]
    {B : Set (X × Y)} (hB : MeasurableSet B) (hsec : ∀ x, IsCompact {y | (x, y) ∈ B}) :
    MeasurableSet (Prod.fst '' B) := by
  obtain ⟨t', ht'le, ht'polish, hBclosed⟩ :=
    exists_finer_polish_isClosed_of_closedSections hB fun x => (hsec x).isClosed
  have hclosed_img : IsClosed[t'] (Prod.fst '' B) :=
    (@isProperMap_fst_of_compactSpace X Y t' _ _).isClosedMap _ hBclosed
  have hb' : @borel X t' = @borel X tX :=
    MeasureTheory.borel_eq_borel_of_le ht'polish inferInstance ht'le
  have hmeq : ‹MeasurableSpace X› = @borel X tX := BorelSpace.measurable_eq
  have h1 : MeasurableSet[@borel X t'] ((Prod.fst '' B)ᶜ) :=
    MeasurableSpace.measurableSet_generateFrom hclosed_img.isOpen_compl
  have h2 : MeasurableSet[@borel X t'] (Prod.fst '' B) := by simpa using h1.compl
  rw [hb', ← hmeq] at h2
  exact h2

/-- Any Polish space admits a continuous injection into the compact Polish cube
`ℕ → Icc (0:ℝ) 1` (no embedding needed: continuity + injectivity suffice downstream). -/
theorem exists_continuous_injective_toCube (Y : Type*) [TopologicalSpace Y] [PolishSpace Y] :
    ∃ e : Y → (ℕ → Set.Icc (0 : ℝ) 1), Continuous e ∧ Function.Injective e := by
  classical
  cases isEmpty_or_nonempty Y with
  | inl h =>
    haveI := h
    refine ⟨isEmptyElim, ?_, fun a => isEmptyElim a⟩
    exact continuous_iff_continuousAt.2 fun y => isEmptyElim y
  | inr h =>
    haveI := h
    letI := TopologicalSpace.upgradeIsCompletelyMetrizable Y
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Y
    refine ⟨fun y n => ⟨min (dist y (u n)) 1, ⟨le_min dist_nonneg zero_le_one, min_le_right _ _⟩⟩,
      ?_, ?_⟩
    · refine continuous_pi fun n => Continuous.subtype_mk ?_ _
      exact (continuous_id.dist continuous_const).min continuous_const
    · intro y y' hyy'
      have hd : ∀ n, min (dist y (u n)) 1 = min (dist y' (u n)) 1 := fun n =>
        congrArg Subtype.val (congrFun hyy' n)
      have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → dist y y' ≤ 2 * ε := by
        intro ε hε hε1
        obtain ⟨n, hn⟩ := hu.exists_dist_lt y hε
        have hdn := hd n
        have h1 : min (dist y (u n)) 1 = dist y (u n) := min_eq_left (by linarith)
        rw [h1] at hdn
        have h2 : dist y' (u n) ≤ dist y (u n) := by
          by_cases hc : dist y' (u n) ≤ 1
          · rw [min_eq_left hc] at hdn
            exact le_of_eq hdn.symm
          · push Not at hc
            rw [min_eq_right hc.le] at hdn
            linarith
        calc dist y y' ≤ dist y (u n) + dist (u n) y' := dist_triangle _ _ _
          _ = dist y (u n) + dist y' (u n) := by rw [dist_comm (u n) y']
          _ ≤ ε + ε := by linarith
          _ = 2 * ε := by ring
      have hle : dist y y' ≤ 0 := by
        by_contra hpos
        push Not at hpos
        have hq := key (min (dist y y' / 4) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)
        have hm : min (dist y y' / 4) 1 ≤ dist y y' / 4 := min_le_left _ _
        linarith
      exact eq_of_dist_eq_zero (le_antisymm hle dist_nonneg)

/-- **Srivastava 4.7.11 (Novikov): Leaf 1.** A Borel `B ⊆ X × Y` (`X, Y` Polish) with compact
sections has Borel projection. WLOG-compactification: push `B` into `X × (ℕ → Icc 0 1)` along a
continuous injection (a measurable embedding by Lusin–Souslin); compact sections are preserved
(and stay closed in the cube since compact sets are absolutely closed). -/
theorem measurableSet_image_fst_of_isCompact_sections {B : Set (X × Y)}
    (hB : MeasurableSet B) (hsec : ∀ x, IsCompact {y | (x, y) ∈ B}) :
    MeasurableSet (Prod.fst '' B) := by
  classical
  haveI : PolishSpace (Set.Icc (0 : ℝ) 1) := isClosed_Icc.polishSpace
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.1 isCompact_Icc
  obtain ⟨e, econt, einj⟩ := exists_continuous_injective_toCube Y
  borelize (ℕ → Set.Icc (0 : ℝ) 1)
  have hemb : MeasurableEmbedding e := econt.measurableEmbedding einj
  have hprodemb : MeasurableEmbedding (Prod.map (id : X → X) e) :=
    MeasurableEmbedding.id.prodMap hemb
  have hB' : MeasurableSet (Prod.map (id : X → X) e '' B) := hprodemb.measurableSet_image.2 hB
  have hsec' : ∀ x, IsCompact {h : ℕ → Set.Icc (0 : ℝ) 1 |
      (x, h) ∈ Prod.map (id : X → X) e '' B} := by
    intro x
    have hi : {h : ℕ → Set.Icc (0 : ℝ) 1 | (x, h) ∈ Prod.map (id : X → X) e '' B}
        = e '' {y | (x, y) ∈ B} := by
      ext h
      constructor
      · rintro ⟨⟨x', y⟩, hxy, heq⟩
        have hx : x' = x := congrArg Prod.fst heq
        have hh : e y = h := congrArg Prod.snd heq
        subst hx
        exact ⟨y, hxy, hh⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(x, y), hy, rfl⟩
    rw [hi]
    exact (hsec x).image econt
  have himg : Prod.fst '' (Prod.map (id : X → X) e '' B) = Prod.fst '' B := by
    rw [Set.image_image]
    exact Set.image_congr fun p _ => rfl
  have hres := measurableSet_image_fst_of_isCompact_sections_of_compactSpace hB' hsec'
  rwa [himg] at hres

end Novikov4711

end ErgodicTheory
