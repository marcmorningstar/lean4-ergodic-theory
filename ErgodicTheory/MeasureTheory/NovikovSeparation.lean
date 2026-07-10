/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The generalized first separation theorem (Novikov)

This module formalises the **generalized first separation theorem** for a countable family of
analytic sets — the ℕ-ary generalization, due to Novikov (with the elegant proof of Mokobodzki), of
Mathlib's binary Lusin separation `MeasureTheory.measurablySeparable_range_of_disjoint`.

## Main statement

`ErgodicTheory.generalized_first_separation` (Srivastava 4.6.1): if `Aₙ` are analytic sets with
`⋂ₙ Aₙ = ∅`, there are measurable supersets `Bₙ ⊇ Aₙ` with `⋂ₙ Bₙ = ∅` — the family is *Borel
separated*.

## The proof

Following Srivastava, we say a countable family `E` is **Borel separated** (`ErgodicTheory.SepFam`)
when such measurable supersets exist. The engine is the combinatorial Lemma 4.6.2, formalised
here as the single-entry split `ErgodicTheory.sepFam_of_forall_update` /
`ErgodicTheory.exists_not_sepFam_update` and its inductive one-stage form
`ErgodicTheory.stage_step`. Applied to the images `Aₙ = range fₙ` of continuous maps
`fₙ : (ℕ → ℕ) → X` from Baire space, the Mokobodzki recursion refines cylinders one coordinate at a
time; the diagonal limit points would all coincide unless the family is separated, forcing
`⋂ₙ Aₙ ≠ ∅` — the contrapositive of `ErgodicTheory.sepFam_ranges`.

Reference: S. M. Srivastava, *A Course on Borel Sets*, Springer GTM 180, §4.6 (Theorem 4.6.1 and
Lemma 4.6.2); template: Mathlib's `measurablySeparable_range_of_disjoint`
(`Mathlib.MeasureTheory.Constructions.Polish.Basic`).
-/

open Set Function PiNat MeasureTheory Metric Topology

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

/-- A countable family of sets is *Borel separated* if there are measurable supersets with empty
intersection (Srivastava's terminology after 4.6.1). -/
def SepFam (E : ℕ → Set X) : Prop :=
  ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n)) ∧ (∀ n, E n ⊆ B n) ∧ ⋂ n, B n = ∅

/-- The core of the combinatorial Lemma 4.6.2 (initial step, at an arbitrary position `j`):
if every refinement of the `j`-th entry by a member of a countable decomposition is Borel
separated, so is the original family. -/
lemma sepFam_of_forall_update {E : ℕ → Set X} {j : ℕ} {G : ℕ → Set X}
    (hEj : E j ⊆ ⋃ m, G m) (h : ∀ m, SepFam (Function.update E j (G m))) : SepFam E := by
  choose B hmeas hsub hempty using h
  classical
  refine ⟨fun n => if n = j then ⋃ m, B m j else ⋂ m, B m n, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    by_cases hn : n = j
    · rw [if_pos hn]
      exact MeasurableSet.iUnion fun m => hmeas m j
    · rw [if_neg hn]
      exact MeasurableSet.iInter fun m => hmeas m n
  · intro n
    dsimp only
    by_cases hn : n = j
    · subst hn
      rw [if_pos rfl]
      intro x hx
      rcases mem_iUnion.1 (hEj hx) with ⟨m, hm⟩
      refine mem_iUnion.2 ⟨m, hsub m n ?_⟩
      rw [Function.update_self]
      exact hm
    · rw [if_neg hn]
      intro x hx
      refine mem_iInter.2 fun m => hsub m n ?_
      rw [Function.update_of_ne hn]
      exact hx
  · ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hx
    have hxj := hx j
    rw [if_pos rfl] at hxj
    rcases mem_iUnion.1 hxj with ⟨m₀, hm₀⟩
    have hmem : x ∈ ⋂ n, B m₀ n := by
      refine mem_iInter.2 fun n => ?_
      by_cases hn : n = j
      · subst hn; exact hm₀
      · have h' := hx n
        rw [if_neg hn] at h'
        exact mem_iInter.1 h' m₀
    rw [hempty m₀] at hmem
    exact hmem

/-- Existential form of the single-entry split (Lemma 4.6.2's engine). -/
lemma exists_not_sepFam_update {E : ℕ → Set X} (hE : ¬ SepFam E) (j : ℕ) {G : ℕ → Set X}
    (hEj : E j ⊆ ⋃ m, G m) : ∃ m, ¬ SepFam (Function.update E j (G m)) := by
  by_contra h
  push Not at h
  exact hE (sepFam_of_forall_update hEj h)

section Ranges

variable (f : ℕ → (ℕ → ℕ) → X)

/-- The stage-`k` family: the `n`-th entry is the image of the length-`(k−n)` cylinder around
`σ n`. For `n ≥ k` the cylinder is the whole Baire space, so the entry is `range (f n)`. -/
def famE (σ : ℕ → ℕ → ℕ) (k : ℕ) : ℕ → Set X := fun n => f n '' cylinder (σ n) (k - n)

/-- The intermediate (mixed-length) family during one stage: entries `n < j` have already been
extended to length `k+1−n`, the rest still have `k−n`. -/
def famMix (σ : ℕ → ℕ → ℕ) (k j : ℕ) : ℕ → Set X :=
  fun n => f n '' cylinder (σ n) ((if n < j then k + 1 else k) - n)

/-- One full stage of the Mokobodzki recursion: extend every entry's cylinder by one coordinate,
preserving non-separatedness. This is Lemma 4.6.2 in its inductive form. -/
lemma stage_step {σ : ℕ → ℕ → ℕ} {k : ℕ} (hσ : ¬ SepFam (famE f σ k)) :
    ∃ σ' : ℕ → ℕ → ℕ, (∀ n, σ' n ∈ cylinder (σ n) (k - n)) ∧
      ¬ SepFam (famE f σ' (k + 1)) := by
  classical
  have main : ∀ j, j ≤ k + 1 → ∃ σ' : ℕ → ℕ → ℕ,
      (∀ n, σ' n ∈ cylinder (σ n) (k - n)) ∧ (∀ n, j ≤ n → σ' n = σ n) ∧
      ¬ SepFam (famMix f σ' k j) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨σ, fun n => self_mem_cylinder _ _, fun n _ => rfl, ?_⟩
      have : famMix f σ k 0 = famE f σ k := by
        funext n
        simp [famMix, famE]
      rw [this]
      exact hσ
    | succ j IH =>
      intro hj
      obtain ⟨σ', hmem, hfix, hsep⟩ := IH (le_trans (Nat.le_succ j) hj)
      have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
      -- decompose the `j`-th entry into one-longer cylinders
      have hdecomp : famMix f σ' k j j ⊆
          ⋃ m, f j '' cylinder (Function.update (σ' j) (k - j) m) (k + 1 - j) := by
        have h1 : famMix f σ' k j j = f j '' cylinder (σ' j) (k - j) := by
          simp [famMix]
        have h2 : cylinder (σ' j) (k - j)
            = ⋃ m, cylinder (Function.update (σ' j) (k - j) m) ((k - j) + 1) :=
          (iUnion_cylinder_update (σ' j) (k - j)).symm
        have h3 : (k - j) + 1 = k + 1 - j := by omega
        rw [h1, h2, image_iUnion, h3]
      obtain ⟨m₀, hm₀⟩ := exists_not_sepFam_update hsep j hdecomp
      set σ'' := Function.update σ' j (Function.update (σ' j) (k - j) m₀) with hσ''
      have hupd : Function.update (famMix f σ' k j) j
          (f j '' cylinder (Function.update (σ' j) (k - j) m₀) (k + 1 - j))
          = famMix f σ'' k (j + 1) := by
        funext n
        by_cases hn : n = j
        · subst hn
          rw [Function.update_self]
          simp only [famMix, hσ'', Function.update_self]
          rw [if_pos (Nat.lt_succ_self _)]
        · rw [Function.update_of_ne hn]
          simp only [famMix, hσ'', Function.update_of_ne hn]
          have hif : ((if n < j + 1 then k + 1 else k) : ℕ) = if n < j then k + 1 else k := by
            rcases Nat.lt_trichotomy n j with h | h | h
            · rw [if_pos h, if_pos (by omega)]
            · exact absurd h hn
            · rw [if_neg (by omega), if_neg (by omega)]
          rw [hif]
      rw [hupd] at hm₀
      refine ⟨σ'', ?_, ?_, hm₀⟩
      · intro n
        by_cases hn : n = j
        · subst hn
          rw [hσ'', Function.update_self, hfix n le_rfl]
          exact update_mem_cylinder _ _ _
        · rw [hσ'', Function.update_of_ne hn]
          exact hmem n
      · intro n hn
        have hnj : n ≠ j := by omega
        rw [hσ'', Function.update_of_ne hnj]
        exact hfix n (by omega)
  obtain ⟨σ', hmem, -, hsep⟩ := main (k + 1) le_rfl
  refine ⟨σ', hmem, ?_⟩
  have : famMix f σ' k (k + 1) = famE f σ' (k + 1) := by
    funext n
    by_cases hn : n < k + 1
    · simp [famMix, famE, hn]
    · have h1 : k + 1 - n = 0 := by omega
      have h2 : k - n = 0 := by omega
      simp [famMix, famE, hn, h1, h2]
  rw [this] at hsep
  exact hsep

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]

/-- **Srivastava 4.6.1, ranges version.** If `fₙ : ℕ→ℕ → X` are continuous with
`⋂ₙ range fₙ = ∅`, the family `(range fₙ)` is Borel separated. -/
theorem sepFam_ranges (hf : ∀ n, Continuous (f n))
    (hint : ⋂ n, range (f n) = ∅) : SepFam (fun n => range (f n)) := by
  classical
  by_contra hns
  -- the state space of the recursion: a stage number and cylinder centers, not separated
  let A := { q : ℕ × (ℕ → ℕ → ℕ) // ¬ SepFam (famE f q.2 q.1) }
  have hstep : ∀ q : A, ∃ q' : A, q'.1.1 = q.1.1 + 1 ∧
      ∀ n, q'.1.2 n ∈ cylinder (q.1.2 n) (q.1.1 - n) := by
    rintro ⟨⟨k, σ⟩, hq⟩
    obtain ⟨σ', hmem, hsep⟩ := stage_step f hq
    exact ⟨⟨⟨k + 1, σ'⟩, hsep⟩, rfl, hmem⟩
  choose F hFk hFmem using hstep
  have hq0 : ¬ SepFam (famE f (fun _ _ => 0) 0) := by
    have : famE f (fun _ _ => 0) 0 = fun n => range (f n) := by
      funext n
      simp [famE, cylinder_zero]
    rw [this]
    exact hns
  let p : ℕ → A := fun k => F^[k] ⟨⟨0, fun _ _ => 0⟩, hq0⟩
  have prec : ∀ k, p (k + 1) = F (p k) := fun k => by
    simp only [p, iterate_succ', comp_apply]
  have pk_fst : ∀ k, (p k).1.1 = k := by
    intro k
    induction k with
    | zero => rfl
    | succ k IH => rw [prec, hFk, IH]
  -- stationarity: coordinate `i` of entry `n` is fixed from stage `n+i+1` on
  have stat : ∀ n i k, n + i + 1 ≤ k → (p k).1.2 n i = (p (n + i + 1)).1.2 n i := by
    intro n i
    refine Nat.le_induction rfl ?_
    intro k hk IH
    have hcoord : (F (p k)).1.2 n i = (p k).1.2 n i := by
      have hmem := hFmem (p k) n
      rw [pk_fst] at hmem
      exact mem_cylinder_iff.1 hmem i (by omega)
    rw [prec, hcoord, IH]
  -- the diagonal limit points
  set α : ℕ → ℕ → ℕ := fun n i => (p (n + i + 1)).1.2 n i with hα
  have M : ∀ k, ¬ SepFam (fun n => f n '' cylinder (α n) (k - n)) := by
    intro k
    have hpk := (p k).2
    have heq : famE f (p k).1.2 (p k).1.1 = fun n => f n '' cylinder (α n) (k - n) := by
      funext n
      simp only [famE, pk_fst]
      have hmem : α n ∈ cylinder ((p k).1.2 n) (k - n) := by
        refine mem_cylinder_iff.2 fun i hi => ?_
        simp only [hα]
        exact (stat n i k (by omega)).symm
      rw [mem_cylinder_iff_eq.1 hmem]
    rw [heq] at hpk
    exact hpk
  -- the diagonal points cannot all coincide
  obtain ⟨i, j, hij⟩ : ∃ i j, f i (α i) ≠ f j (α j) := by
    by_contra h
    push Not at h
    have : f 0 (α 0) ∈ ⋂ n, range (f n) :=
      mem_iInter.2 fun n => (h 0 n) ▸ mem_range_self _
    rw [hint] at this
    exact this
  have hne : i ≠ j := fun h => hij (by rw [h])
  obtain ⟨u, v, u_open, v_open, hu, hv, huv⟩ := t2_separation hij
  letI : MetricSpace (ℕ → ℕ) := metricSpaceNatNat
  obtain ⟨εi, εipos, hεi⟩ : ∃ εi : ℝ, εi > 0 ∧ Metric.ball (α i) εi ⊆ f i ⁻¹' u :=
    Metric.mem_nhds_iff.1 ((hf i).continuousAt.preimage_mem_nhds (u_open.mem_nhds hu))
  obtain ⟨εj, εjpos, hεj⟩ : ∃ εj : ℝ, εj > 0 ∧ Metric.ball (α j) εj ⊆ f j ⁻¹' v :=
    Metric.mem_nhds_iff.1 ((hf j).continuousAt.preimage_mem_nhds (v_open.mem_nhds hv))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < min εi εj :=
    exists_pow_lt_of_lt_one (lt_min εipos εjpos) (by norm_num)
  -- at a late enough stage, `u`, `v`, `univ, univ, …` separates the family: contradiction
  apply M (max (i + N) (j + N))
  set k := max (i + N) (j + N) with hk
  have hcyl : ∀ (a : ℕ) (ε : ℝ) (w : Set X), N ≤ k - a → Metric.ball (α a) ε ⊆ f a ⁻¹' w →
      (1 / 2 : ℝ) ^ N < ε → f a '' cylinder (α a) (k - a) ⊆ w := by
    intro a ε w hka hball hε
    rw [image_subset_iff]
    refine (cylinder_anti _ hka).trans ?_
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    calc dist y (α a) ≤ (1 / 2 : ℝ) ^ N := mem_cylinder_iff_dist_le.1 hy
      _ < ε := hε
  refine ⟨fun n => if n = i then u else if n = j then v else univ, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    by_cases h1 : n = i
    · rw [if_pos h1]; exact u_open.measurableSet
    by_cases h2 : n = j
    · rw [if_neg h1, if_pos h2]; exact v_open.measurableSet
    · rw [if_neg h1, if_neg h2]; exact MeasurableSet.univ
  · intro n
    dsimp only
    by_cases h1 : n = i
    · subst h1
      rw [if_pos rfl]
      exact hcyl _ εi u (by omega) hεi (hN.trans_le (min_le_left _ _))
    by_cases h2 : n = j
    · subst h2
      rw [if_neg h1, if_pos rfl]
      exact hcyl _ εj v (by omega) hεj (hN.trans_le (min_le_right _ _))
    · rw [if_neg h1, if_neg h2]
      exact subset_univ _
  · ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hx
    have hxi := hx i
    rw [if_pos rfl] at hxi
    have hxj := hx j
    rw [if_neg (Ne.symm hne), if_pos rfl] at hxj
    exact (disjoint_left.1 huv hxi) hxj

end Ranges

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X]

/-- **The generalized first separation theorem (Novikov; Srivastava 4.6.1).** A countable family
of analytic sets with empty intersection is Borel separated: there are measurable `Bₙ ⊇ Aₙ` with
`⋂ₙ Bₙ = ∅`. -/
theorem generalized_first_separation {A : ℕ → Set X} (hA : ∀ n, AnalyticSet (A n))
    (hint : ⋂ n, A n = ∅) :
    ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n)) ∧ (∀ n, A n ⊆ B n) ∧ ⋂ n, B n = ∅ := by
  classical
  by_cases hne : ∃ n₀, A n₀ = ∅
  · obtain ⟨n₀, hn₀⟩ := hne
    refine ⟨fun n => if n = n₀ then ∅ else univ, fun n => ?_, fun n => ?_, ?_⟩
    · dsimp only
      by_cases hn : n = n₀
      · rw [if_pos hn]; exact MeasurableSet.empty
      · rw [if_neg hn]; exact MeasurableSet.univ
    · dsimp only
      by_cases hn : n = n₀
      · subst hn; rw [if_pos rfl, hn₀]
      · rw [if_neg hn]; exact subset_univ _
    · refine subset_antisymm (fun x hx => ?_) (empty_subset _)
      have hmem := mem_iInter.1 hx n₀
      rw [if_pos rfl] at hmem
      exact hmem
  · push Not at hne
    have hex : ∀ n, ∃ g : (ℕ → ℕ) → X, Continuous g ∧ range g = A n := by
      intro n
      have h := hA n
      rw [AnalyticSet] at h
      rcases h with h | h
      · exact absurd h (nonempty_iff_ne_empty.1 (hne n))
      · exact h
    choose g hg hrange using hex
    have := sepFam_ranges g hg (by simp_rw [hrange]; exact hint)
    obtain ⟨B, h1, h2, h3⟩ := this
    exact ⟨B, h1, fun n => (hrange n) ▸ h2 n, h3⟩

end ErgodicTheory
