/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.Skyscraper

/-!
# The complete-block tower base and the residual estimate (Rokhlin tower, issue #15)

To build a Rokhlin tower of height `N`, one selects from the skyscraper over a small base set `A`
only those floors that start a **complete block** of height `N`. This file constructs that
**tower base** and proves the two facts the tower lemma needs from it:

* the `N` translates `eⁱ '' B`, `i : Fin N`, are pairwise disjoint
  (`pairwise_disjoint_levels`), and
* the uncovered residual `(⋃ i, eⁱ '' B)ᶜ` is small — it is contained, up to the null skyscraper
  complement, in the **top incomplete floors**, whose measure is bounded by
  `∑ k, ((k+1) mod N) · μ (returnLevel e A (k+1))` (`measure_topFloors_le`).

## Main definitions

* `Oseledets.Krieger.towerBase e A N` — the union of floors `e^[m·N] '' (returnLevel e A (k+1))`
  that begin a complete height-`N` block (guard `(m+1)·N ≤ k+1`).
* `Oseledets.Krieger.coveredSet e A N` — the union `⋃ i : Fin N, eⁱ '' (towerBase e A N)`.
* `Oseledets.Krieger.topFloors e A N` — the top incomplete floors `⌊(k+1)/N⌋·N ≤ j ≤ k` of each
  column.

## Main results

* `pairwise_disjoint_levels` — the `N` translates of the tower base are pairwise disjoint.
* `compl_inter_skyscraper_subset_topFloors` — `(coveredSet)ᶜ ∩ skyscraper ⊆ topFloors`.
* `measure_topFloors_le` — `μ (topFloors e A N) ≤ ∑ k, ((k+1) mod N) · μ (returnLevel e A (k+1))`.
* `residual_lt_eps`, `residual_arith`, `tsum_residual_le`, `measure_gt_of_compl_lt` — the `ℝ≥0∞`
  arithmetic assembling the residual bound `< ε`.
-/

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace Oseledets.Krieger

variable {α : Type*} [MeasurableSpace α]

/-! ## The complete-block tower base and level disjointness -/

/-- The tower base `B`: floors at heights `m·N` that START a complete block of height `N` inside a
column of height `k+1` (guard `(m+1)·N ≤ k+1` ensures only complete blocks). -/
def towerBase (e : α ≃ᵐ α) (A : Set α) (N : ℕ) : Set α :=
  ⋃ k : ℕ, ⋃ m : ℕ, ⋃ (_ : (m + 1) * N ≤ k + 1),
    (e : α → α)^[m * N] '' (returnLevel e A (k + 1))

/-- Measurability of the tower base. -/
theorem measurableSet_towerBase (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) (N : ℕ) :
    MeasurableSet (towerBase e A N) := by
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun m =>
    MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_iterate_image e (m * N) (measurableSet_returnLevel e hA (k + 1))

/-- The key floor-rewrite: for the level `i`, `eⁱ '' B` is the union of floors at heights
`m·N + i`. -/
theorem image_towerBase (e : α ≃ᵐ α) (A : Set α) (N : ℕ) (i : ℕ) :
    (e : α → α)^[i] '' towerBase e A N =
      ⋃ k : ℕ, ⋃ m : ℕ, ⋃ (_ : (m + 1) * N ≤ k + 1),
        (e : α → α)^[m * N + i] '' (returnLevel e A (k + 1)) := by
  simp only [towerBase, Set.image_iUnion]
  refine iUnion_congr fun k => iUnion_congr fun m => iUnion_congr fun _ => ?_
  -- `eⁱ '' (e^[m·N] '' rl) = e^[i + m·N] '' rl = e^[m·N + i] '' rl`.
  rw [← Set.image_comp, ← Function.iterate_add]
  rw [show i + m * N = m * N + i by ring]

/-- **Level disjointness.** The `N` levels `eⁱ '' B`, `i : Fin N`, are pairwise disjoint.
The hypothesis `1 ≤ N` is kept for a uniform call shape; `i : Fin N` already forces `N ≥ 1`
where it matters. -/
theorem pairwise_disjoint_levels (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (_hN : 1 ≤ N) :
    Pairwise
      (Function.onFun Disjoint (fun i : Fin N => (e : α → α)^[i] '' towerBase e A N)) := by
  intro i₁ i₂ hne
  simp only [Function.onFun]
  rw [image_towerBase, image_towerBase]
  -- Each floor of level `i₁` is disjoint from each floor of level `i₂`.
  rw [Set.disjoint_iUnion_left]
  intro k₁
  rw [Set.disjoint_iUnion_left]
  intro m₁
  rw [Set.disjoint_iUnion_left]
  intro hguard₁
  rw [Set.disjoint_iUnion_right]
  intro k₂
  rw [Set.disjoint_iUnion_right]
  intro m₂
  rw [Set.disjoint_iUnion_right]
  intro hguard₂
  -- Apply the crux with floor heights `j₁ = m₁·N + i₁ ≤ k₁` and `j₂ = m₂·N + i₂ ≤ k₂`.
  have hi₁ : (i₁ : ℕ) < N := i₁.isLt
  have hi₂ : (i₂ : ℕ) < N := i₂.isLt
  have hj₁k₁ : m₁ * N + (i₁ : ℕ) ≤ k₁ := by
    have : (m₁ + 1) * N ≤ k₁ + 1 := hguard₁
    nlinarith [hi₁, this]
  have hj₂k₂ : m₂ * N + (i₂ : ℕ) ≤ k₂ := by
    have : (m₂ + 1) * N ≤ k₂ + 1 := hguard₂
    nlinarith [hi₂, this]
  -- Heights differ: they are `≢ mod N` since `i₁ ≠ i₂` are both `< N`.
  have hheights : m₁ * N + (i₁ : ℕ) ≠ m₂ * N + (i₂ : ℕ) := by
    intro h
    have hmodgen : ∀ (m i : ℕ), i < N → (m * N + i) % N = i := by
      intro m i hi
      rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hi]
    have : (i₁ : ℕ) = (i₂ : ℕ) := by
      rw [← hmodgen m₁ i₁ hi₁, ← hmodgen m₂ i₂ hi₂, h]
    exact hne (Fin.ext this)
  have hpairne : (m₁ * N + (i₁ : ℕ), k₁) ≠ (m₂ * N + (i₂ : ℕ), k₂) := by
    intro h
    exact hheights (Prod.ext_iff.1 h).1
  exact disjoint_skyscraper_floors e A hj₁k₁ hj₂k₂ hpairne

/-! ## The residual arithmetic in `ℝ≥0∞` -/

section ResidualArith

variable {μ : Measure α}

/-- The core arithmetic: with `δ := ofReal (ε/N)`, `a < δ` implies `N · a < ofReal ε`. -/
theorem residual_arith {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) {a : ℝ≥0∞}
    (ha : a < ENNReal.ofReal (ε / N)) :
    (N : ℝ≥0∞) * a < ENNReal.ofReal ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hNε : (N : ℝ≥0∞) * ENNReal.ofReal (ε / N) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc (N : ℝ≥0∞) * a
      < (N : ℝ≥0∞) * ENNReal.ofReal (ε / N) :=
        ENNReal.mul_lt_mul_right hNne (ENNReal.natCast_ne_top N) ha
    _ = ENNReal.ofReal ε := hNε

/-- The tsum residual bound: `∑ c_k · x_k ≤ N · ∑ x_k` when `c_k ≤ N`. -/
theorem tsum_residual_le {N : ℕ} (x : ℕ → ℝ≥0∞) (c : ℕ → ℕ) (hc : ∀ k, c k ≤ N) :
    (∑' k, (c k : ℝ≥0∞) * x k) ≤ (N : ℝ≥0∞) * ∑' k, x k := by
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun k => by gcongr; exact_mod_cast hc k

/-- Final assembly arithmetic: for a probability measure, `μ Cᶜ < ofReal ε` and `ofReal ε ≤ 1`
imply `1 - ofReal ε < μ C`. -/
theorem measure_gt_of_compl_lt [IsProbabilityMeasure μ] {C : Set α} (hC : MeasurableSet C)
    {ε : ℝ} (hε1 : ENNReal.ofReal ε ≤ 1) (hcompl : μ Cᶜ < ENNReal.ofReal ε) :
    1 - ENNReal.ofReal ε < μ C := by
  rw [prob_compl_eq_one_sub hC] at hcompl
  have hCle1 : μ C ≤ 1 := by
    rw [← measure_univ (μ := μ)]; exact measure_mono (subset_univ _)
  rw [ENNReal.sub_lt_iff_lt_right (measure_ne_top μ C) hCle1] at hcompl
  rw [ENNReal.sub_lt_iff_lt_right ENNReal.ofReal_ne_top hε1]
  rwa [add_comm] at hcompl

end ResidualArith

/-! ## The residual-covering combinatorics -/

/-- The covered set `C = ⋃ i < N, eⁱ '' B`. -/
def coveredSet (e : α ≃ᵐ α) (A : Set α) (N : ℕ) : Set α :=
  ⋃ i : Fin N, (e : α → α)^[i] '' towerBase e A N

/-- The **top incomplete floors**: in column `k+1`, the floors at heights
`⌊(k+1)/N⌋·N ≤ j ≤ k`. These are the `(k+1) mod N` uncovered floors. -/
def topFloors (e : α ≃ᵐ α) (A : Set α) (N : ℕ) : Set α :=
  ⋃ k : ℕ, ⋃ j : ℕ, ⋃ (_ : ((k + 1) / N) * N ≤ j ∧ j ≤ k),
    (e : α → α)^[j] '' (returnLevel e A (k + 1))

/-- Combinatorial heart (pure `ℕ`): if a floor height `j ≤ k` is NOT a top floor
(i.e. `j < ⌊(k+1)/N⌋·N`), then it lies in a complete block: there is `m` with `(m+1)·N ≤ k+1`
and `j = m·N + (j mod N)`, `j mod N < N`. -/
theorem nonTop_covered {N : ℕ} (hN : 1 ≤ N) {j k : ℕ} (_hjk : j ≤ k)
    (hnotTop : j < ((k + 1) / N) * N) :
    ∃ m : ℕ, (m + 1) * N ≤ k + 1 ∧ ∃ i : ℕ, i < N ∧ j = m * N + i := by
  refine ⟨j / N, ?_, j % N, Nat.mod_lt _ (by omega), ?_⟩
  · -- `(j/N + 1)·N ≤ k+1` from `j < ⌊(k+1)/N⌋·N`.
    have h1 : j / N < (k + 1) / N := by
      by_contra h
      push Not at h  -- `(k+1)/N ≤ j/N`
      have hmul : ((k + 1) / N) * N ≤ (j / N) * N := by gcongr
      have hle : (j / N) * N ≤ j := Nat.div_mul_le_self j N
      omega
    have h2 : j / N + 1 ≤ (k + 1) / N := h1
    calc (j / N + 1) * N ≤ ((k + 1) / N) * N := by gcongr
      _ ≤ k + 1 := Nat.div_mul_le_self (k + 1) N
  · -- `j = (j/N)·N + j%N`.
    have h := Nat.div_add_mod j N  -- `N · (j / N) + j % N = j`
    have hc : N * (j / N) = (j / N) * N := Nat.mul_comm _ _
    omega

/-- The floor count of the top incomplete block of column `k+1`: the number of integers `j` with
`⌊(k+1)/N⌋·N ≤ j ≤ k` is exactly `(k+1) mod N`. -/
theorem topBlock_count {N : ℕ} (_hN : 1 ≤ N) (k : ℕ) :
    k + 1 - ((k + 1) / N) * N = (k + 1) % N := by
  have h := Nat.div_add_mod (k + 1) N  -- `N · ((k+1)/N) + (k+1)%N = k+1`
  have hc : N * ((k + 1) / N) = ((k + 1) / N) * N := Nat.mul_comm _ _
  omega

/-- The residual `< ε` inequality, assembled at the `ℝ≥0∞` level: if `∑ x_k = μA`,
`μA < ofReal(ε/N)`, and `S ≤ ∑ ((k+1) mod N) · x_k`, then `S < ofReal ε`. -/
theorem residual_lt_eps {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (x : ℕ → ℝ≥0∞)
    {μA : ℝ≥0∞} (hsum : (∑' k, x k) = μA) (hμA : μA < ENNReal.ofReal (ε / N))
    {S : ℝ≥0∞} (hS : S ≤ ∑' k, ((k + 1) % N : ℕ) * x k) :
    S < ENNReal.ofReal ε := by
  have hmod : ∀ k, (k + 1) % N ≤ N := fun k => le_of_lt (Nat.mod_lt _ (by omega))
  calc S ≤ ∑' k, ((k + 1) % N : ℕ) * x k := hS
    _ ≤ (N : ℝ≥0∞) * ∑' k, x k := tsum_residual_le x (fun k => (k + 1) % N) hmod
    _ = (N : ℝ≥0∞) * μA := by rw [hsum]
    _ < ENNReal.ofReal ε := residual_arith hN hε hμA

/-- A skyscraper floor `(j, k)` with `j < ⌊(k+1)/N⌋·N` lies in the covered set: `j = m·N + i` is a
complete-block floor (`nonTop_covered`). -/
theorem floor_subset_coveredSet (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N)
    {j k : ℕ} (hjk : j ≤ k) (hnotTop : j < ((k + 1) / N) * N) :
    (e : α → α)^[j] '' (returnLevel e A (k + 1)) ⊆ coveredSet e A N := by
  obtain ⟨m, hmk, i, hiN, hji⟩ := nonTop_covered hN hjk hnotTop
  rintro y ⟨x, hx, rfl⟩
  rw [coveredSet, mem_iUnion]
  refine ⟨⟨i, hiN⟩, ?_⟩
  -- `y = eʲ x = e^[m·N + i] x = eⁱ (e^[m·N] x)`, and `e^[m·N] x ∈ towerBase`.
  refine ⟨(e : α → α)^[m * N] x, ?_, ?_⟩
  · rw [towerBase, mem_iUnion]
    refine ⟨k, ?_⟩
    rw [mem_iUnion]; refine ⟨m, ?_⟩
    rw [mem_iUnion]; exact ⟨hmk, ⟨x, hx, rfl⟩⟩
  · rw [← Function.iterate_add_apply, show i + m * N = j by omega]

/-- The residual structure: `(coveredSet)ᶜ ∩ skyscraper ⊆ topFloors`. A skyscraper point sits at
some floor `(j, k)`, `j ≤ k`; if it is not covered then `j ≥ ⌊(k+1)/N⌋·N` (else
`floor_subset_coveredSet`), so it is a top floor. -/
theorem compl_inter_skyscraper_subset_topFloors (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N) :
    (coveredSet e A N)ᶜ ∩ skyscraper e A ⊆ topFloors e A N := by
  rintro y ⟨hyC, hysky⟩
  rw [mem_skyscraper_iff] at hysky
  obtain ⟨k, j, hjk, x, hx, hxy⟩ := hysky
  by_cases htop : ((k + 1) / N) * N ≤ j
  · -- Top floor.
    rw [topFloors, mem_iUnion]
    refine ⟨k, ?_⟩
    rw [mem_iUnion]; refine ⟨j, ?_⟩
    rw [mem_iUnion]; exact ⟨⟨htop, hjk⟩, ⟨x, hx, hxy⟩⟩
  · -- Not top: `j < ⌊(k+1)/N⌋·N ⟹ y ∈ C`, contradicting `y ∈ Cᶜ`.
    push Not at htop
    exact absurd (floor_subset_coveredSet e A hN hjk htop ⟨x, hx, hxy⟩) hyC

/-! ## The residual measure bound -/

section Measure
variable {μ : Measure α}

/-- `topFloors` rewritten with a `Finset.Icc` bUnion over the column floors. -/
theorem topFloors_eq_biUnion (e : α ≃ᵐ α) (A : Set α) (N : ℕ) :
    topFloors e A N
      = ⋃ k : ℕ, ⋃ j ∈ Finset.Icc (((k + 1) / N) * N) k,
          (e : α → α)^[j] '' (returnLevel e A (k + 1)) := by
  rw [topFloors]
  refine iUnion_congr fun k => ?_
  ext y
  simp only [mem_iUnion, Finset.mem_Icc, exists_prop]

/-- The residual measure bound:
`μ (topFloors e A N) ≤ ∑ k, ((k+1) mod N) · μ (returnLevel e A (k+1))`.
Countable + finite subadditivity, `measure_iterate_image` to normalize each floor measure, then the
floor count `topBlock_count`. -/
theorem measure_topFloors_le (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ)
    {A : Set α} (hA : MeasurableSet A) {N : ℕ} (hN : 1 ≤ N) :
    μ (topFloors e A N) ≤ ∑' k : ℕ, ((k + 1) % N : ℕ) * μ (returnLevel e A (k + 1)) := by
  rw [topFloors_eq_biUnion]
  refine le_trans (measure_iUnion_le _) ?_
  refine ENNReal.tsum_le_tsum fun k => ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hfloor : ∀ j ∈ Finset.Icc (((k + 1) / N) * N) k,
      μ ((e : α → α)^[j] '' (returnLevel e A (k + 1))) = μ (returnLevel e A (k + 1)) :=
    fun j _ => measure_iterate_image e he j (measurableSet_returnLevel e hA (k + 1))
  rw [Finset.sum_congr rfl hfloor, Finset.sum_const]
  rw [Nat.card_Icc]
  have hcard : k + 1 - ((k + 1) / N) * N = (k + 1) % N := topBlock_count hN k
  rw [hcard, nsmul_eq_mul]

end Measure

end Oseledets.Krieger
