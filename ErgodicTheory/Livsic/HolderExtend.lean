/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# McShane extension for Hölder functions

This file proves that a real-valued function that is Hölder continuous with constant `C` and
exponent `r ≤ 1` on a subset `s` of a metric space admits a Hölder extension to the whole space
with the *same* constant and exponent.

The construction mirrors `LipschitzOnWith.extend_real` (the McShane/Whitney extension for Lipschitz
functions): the extension is the infimal convolution
`v x := ⨅ y ∈ s, (u y + C * dist x y ^ r)`.
The only extra ingredient over the Lipschitz case is the subadditivity of `t ↦ t ^ r` for
`0 ≤ r ≤ 1` (`Real.rpow_add_le_add_rpow`), which replaces the linearity of `t ↦ t` used in the
triangle-inequality step.

## Main results

* `ErgodicTheory.holderOnWith_of_dist_le` / `ErgodicTheory.holderWith_of_dist_le`: the `ℝ`-valued
  repackaging of the `edist`-based Hölder predicates from a `dist`-based bound (on a set, resp.
  everywhere); shared with `ErgodicTheory.Livsic.Abstract`.
* `ErgodicTheory.exists_holderWith_extension`: the McShane extension theorem.

This lemma is deliberately kept independent of the rest of the development (it imports only
Mathlib); it is the extension step consumed by the abstract Livšic theorem.
-/

namespace ErgodicTheory

open Set Metric
open scoped NNReal ENNReal

/-- A real-valued map satisfying a metric (`dist`-based) Hölder bound *on a set `s`* is
`HolderOnWith` on `s`. This is the `ℝ`-valued repackaging of the `edist`-based definition of
`HolderOnWith`, shared with `ErgodicTheory.Livsic.Abstract` (which derives the on-orbit Hölder
modulus from it). -/
theorem holderOnWith_of_dist_le {X : Type*} [PseudoMetricSpace X] {C r : ℝ≥0} {v : X → ℝ}
    {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (v x) (v y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderOnWith C r v s := by
  intro x hx y hy
  simp only [edist_dist]
  calc ENNReal.ofReal (dist (v x) (v y))
      ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) := ENNReal.ofReal_le_ofReal (h x hx y hy)
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (dist x y) ^ (r : ℝ) := by
        rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg]

/-- A real-valued map satisfying a metric (`dist`-based) Hölder bound everywhere is `HolderWith`.
The `univ` specialization of `holderOnWith_of_dist_le` via `holderOnWith_univ`. -/
theorem holderWith_of_dist_le {X : Type*} [PseudoMetricSpace X] {C r : ℝ≥0} {v : X → ℝ}
    (h : ∀ x y, dist (v x) (v y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r v :=
  holderOnWith_univ.mp (holderOnWith_of_dist_le (s := Set.univ) fun x _ y _ => h x y)

/-- **McShane extension for Hölder functions.** A real-valued function `u` that is Hölder
continuous with constant `C` and exponent `r ≤ 1` on a subset `s` of a metric space extends to a
function `v` that is Hölder continuous on the whole space with the *same* constant `C` and
exponent `r`, and agrees with `u` on `s`. -/
theorem exists_holderWith_extension {X : Type*} [MetricSpace X] {C r : ℝ≥0} (hr0 : 0 < r)
    (hr1 : r ≤ 1) {s : Set X} {u : X → ℝ} (hu : HolderOnWith C r u s) :
    ∃ v : X → ℝ, HolderWith C r v ∧ Set.EqOn u v s := by
  have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  rcases eq_empty_or_nonempty s with rfl | hs
  · exact ⟨fun _ => 0, holderWith_of_dist_le fun x y => by
      simp only [dist_self]; positivity, eqOn_empty _ _⟩
  have : Nonempty s := hs.to_subtype
  -- The infimal-convolution extension.
  let v : X → ℝ := fun y => ⨅ x : s, u ↑x + (C : ℝ) * dist y ↑x ^ (r : ℝ)
  -- One-sided Hölder bound coming from the hypothesis, in `ℝ`.
  have hub : ∀ p : X, p ∈ s → ∀ q : X, q ∈ s →
      u p - u q ≤ (C : ℝ) * dist p q ^ (r : ℝ) := by
    intro p hp q hq
    have hd := hu.dist_le hp hq
    rw [Real.dist_eq] at hd
    exact (le_abs_self _).trans hd
  -- Subadditive triangle inequality for `dist ^ r` (uses `r ≤ 1`).
  have hpow : ∀ p q t : X,
      dist p q ^ (r : ℝ) ≤ dist p t ^ (r : ℝ) + dist t q ^ (r : ℝ) := by
    intro p q t
    calc dist p q ^ (r : ℝ)
        ≤ (dist p t + dist t q) ^ (r : ℝ) :=
          Real.rpow_le_rpow dist_nonneg (dist_triangle p t q) r.coe_nonneg
      _ ≤ dist p t ^ (r : ℝ) + dist t q ^ (r : ℝ) :=
          Real.rpow_add_le_add_rpow dist_nonneg dist_nonneg r.coe_nonneg hr1'
  -- The infimum defining `v` is bounded below.
  have B : ∀ a : X, BddBelow (range fun x : s => u ↑x + (C : ℝ) * dist a ↑x ^ (r : ℝ)) := by
    intro a
    obtain ⟨z, hz⟩ := hs
    refine ⟨u z - (C : ℝ) * dist z a ^ (r : ℝ), ?_⟩
    rintro w ⟨t, rfl⟩
    dsimp only
    have hmul := mul_le_mul_of_nonneg_left (hpow z ↑t a) C.coe_nonneg
    rw [mul_add] at hmul
    have := hub z hz ↑t t.2
    linarith
  -- `v` agrees with `u` on `s`.
  have E : Set.EqOn u v s := by
    intro x hx
    refine le_antisymm (le_ciInf fun z => ?_) ?_
    · have := hub x hx ↑z z.2
      linarith
    · refine (ciInf_le (B x) ⟨x, hx⟩).trans_eq ?_
      rw [dist_self, Real.zero_rpow hr0'.ne', mul_zero, add_zero]
  -- `v` is `HolderWith C r`.
  refine ⟨v, holderWith_of_dist_le fun a b => ?_, E⟩
  rw [Real.dist_eq, abs_sub_le_iff]
  have key : ∀ p q : X, v p ≤ v q + (C : ℝ) * dist p q ^ (r : ℝ) := by
    intro p q
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun z => ?_
    rw [sub_le_iff_le_add]
    calc v p ≤ u ↑z + (C : ℝ) * dist p ↑z ^ (r : ℝ) := ciInf_le (B p) z
      _ ≤ u ↑z + (C : ℝ) * dist q ↑z ^ (r : ℝ) + (C : ℝ) * dist p q ^ (r : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left (hpow p ↑z q) C.coe_nonneg
          rw [mul_add] at hmul
          linarith
  refine ⟨by linarith [key a b], ?_⟩
  have := key b a
  rw [dist_comm b a] at this
  linarith

end ErgodicTheory
