/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed

/-!
# Mixing kills eigenvalues

This module records the elementary spectral input needed for time-1 ergodicity of a
suspension flow (GitHub issue #35, step B): a **measurable eigenfunction with a
unimodular eigenvalue different from `1` of a strongly-mixing transformation vanishes
almost everywhere**.

The argument is purely set-theoretic — no `L²` theory, no Fourier analysis. If `g` is a
measurable eigenfunction, `g ∘ f = l • g` with `‖l‖ = 1`, `l ≠ 1`, and `g` is not a.e.
zero, then:

* the powers `lⁿ` stay a fixed distance `δ = ‖l - 1‖/2` away from `1` infinitely often
  (`frequently_pow_far_from_one`, the two-consecutive-powers trick);
* the level set `{g ≠ 0}` has positive measure, so — covering the punctured plane by
  countably many admissible balls — some ball `B = ball q ρ` with `q ≠ 0` and
  `2ρ ≤ ‖q‖ δ` has `μ (g ⁻¹' B) > 0` (`exists_ball_pos_measure`);
* writing `A := g ⁻¹' B`, whenever `‖lⁿ - 1‖ ≥ δ` the rotated ball is disjoint from `B`,
  so `A ∩ fⁿ ⁻¹' A = ∅` frequently, forcing `μ.real (A ∩ fⁿ ⁻¹' A) = 0` along a
  subsequence — contradicting strong mixing, which drives it to `μ.real A ^ 2 > 0`.

## Main results

* `ErgodicTheory.frequently_pow_far_from_one`: unimodular non-trivial powers stay away
  from `1` frequently.
* `ErgodicTheory.exists_ball_pos_measure`: a not-a.e.-zero measurable `ℂ`-function hits a
  small admissible ball with positive measure.
* `ErgodicTheory.eigenfunction_ae_zero_of_mixing`: the headline — mixing kills eigenvalues.

## References

* P. Walters, *An Introduction to Ergodic Theory*, §1.7 (mixing has no non-trivial
  eigenvalues), Theorem 1.24 and surrounding discussion.
* I. P. Cornfeld, S. V. Fomin, Ya. G. Sinai, *Ergodic Theory*, Ch. 10.
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory

/-- For a unimodular `l ≠ 1`, the powers `lⁿ` stay away from `1` infinitely often:
`‖lⁿ - 1‖ ≥ ‖l - 1‖/2` frequently. If two *consecutive* powers were both within
`‖l - 1‖/2` of `1`, then `‖l - 1‖ = ‖l^{n+1} - lⁿ‖ ≤ ‖l^{n+1} - 1‖ + ‖lⁿ - 1‖ < ‖l - 1‖`,
a contradiction. -/
theorem frequently_pow_far_from_one {l : ℂ} (hl : ‖l‖ = 1) (hl1 : l ≠ 1) :
    ∃ᶠ n in atTop, ‖l ^ n - 1‖ ≥ ‖l - 1‖ / 2 := by
  rw [Filter.frequently_atTop]
  intro a
  set d := ‖l - 1‖ with hd
  have hdpos : 0 < d := by
    rw [hd, norm_pos_iff]
    exact sub_ne_zero.mpr hl1
  by_contra hcon
  push Not at hcon
  have h1 : ‖l ^ a - 1‖ < d / 2 := hcon a le_rfl
  have h2 : ‖l ^ (a + 1) - 1‖ < d / 2 := hcon (a + 1) (Nat.le_succ a)
  have hkey : ‖l ^ (a + 1) - l ^ a‖ = d := by
    have hfac : l ^ (a + 1) - l ^ a = l ^ a * (l - 1) := by ring
    rw [hfac, norm_mul, norm_pow, hl, one_pow, one_mul]
  have htri : ‖l ^ (a + 1) - l ^ a‖ ≤ ‖l ^ (a + 1) - 1‖ + ‖l ^ a - 1‖ := by
    have h := norm_sub_le (l ^ (a + 1) - 1) (l ^ a - 1)
    rwa [sub_sub_sub_cancel_right] at h
  linarith

/-- A measurable `ℂ`-valued function that is **not** almost everywhere zero hits some
small *admissible* ball with positive measure: there is a ball `Metric.ball q ρ` whose
centre `q` is nonzero, whose radius satisfies `2ρ ≤ ‖q‖ δ`, and whose `g`-preimage has
positive measure. Here `δ > 0` is an arbitrary separation parameter.

The proof covers the punctured plane by the admissible balls `ball z (‖z‖ δ/2)` (`z ∈ ℂ`),
extracts a *countable* subcover using second countability of `ℂ`, and observes that the
positive-measure level set `{g ≠ 0}` cannot be swallowed by a countable union of
null preimages. -/
theorem exists_ball_pos_measure {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} (hne : ¬ g =ᵐ[μ] 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (q : ℂ) (ρ : ℝ), q ≠ 0 ∧ 0 < ρ ∧ 2 * ρ ≤ ‖q‖ * δ ∧ 0 < μ (g ⁻¹' Metric.ball q ρ) := by
  set S : ℂ → Set ℂ := fun z => Metric.ball z (‖z‖ * δ / 2) with hS_def
  -- countable subcover of the punctured plane by admissible balls
  obtain ⟨T, hTc, hU⟩ := TopologicalSpace.isOpen_iUnion_countable S (fun _ => Metric.isOpen_ball)
  -- the support of `g` has positive measure
  have hgpos : μ {x | g x ≠ 0} ≠ 0 := by
    intro hz
    refine hne ?_
    have hae : ∀ᵐ x ∂μ, g x = 0 := by rw [ae_iff]; simpa using hz
    filter_upwards [hae] with x hx; simp [hx]
  -- the support is contained in the countable union of preimages
  have hsub : {x | g x ≠ 0} ⊆ ⋃ i ∈ T, g ⁻¹' S i := by
    intro x hx
    have hball : g x ∈ S (g x) := by
      change g x ∈ Metric.ball (g x) (‖g x‖ * δ / 2)
      rw [Metric.mem_ball, dist_self]
      have : 0 < ‖g x‖ := norm_pos_iff.mpr hx
      positivity
    have hmem : g x ∈ ⋃ i ∈ T, S i := hU.ge (Set.mem_iUnion.mpr ⟨g x, hball⟩)
    obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hgi⟩
  have hbig : μ (⋃ i ∈ T, g ⁻¹' S i) ≠ 0 := by
    have hmono : μ {x | g x ≠ 0} ≤ μ (⋃ i ∈ T, g ⁻¹' S i) := measure_mono hsub
    intro hz
    rw [hz] at hmono
    exact hgpos (le_zero_iff.mp hmono)
  -- one of the countably many preimages has positive measure
  obtain ⟨q, hqT, hqpos⟩ : ∃ i ∈ T, μ (g ⁻¹' S i) ≠ 0 := by
    by_contra hcon
    refine hbig ((measure_biUnion_null_iff hTc).mpr ?_)
    intro i hi
    by_contra h
    exact hcon ⟨i, hi, h⟩
  -- the chosen ball is admissible: nonzero centre
  have hq0 : q ≠ 0 := by
    rintro rfl
    refine hqpos ?_
    change μ (g ⁻¹' Metric.ball (0 : ℂ) (‖(0 : ℂ)‖ * δ / 2)) = 0
    simp
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  refine ⟨q, ‖q‖ * δ / 2, hq0, div_pos (mul_pos hqnorm hδ) two_pos, le_of_eq (by ring),
    pos_iff_ne_zero.mpr hqpos⟩

set_option maxHeartbeats 400000 in
-- `hf : Measurable f` is kept for API symmetry with the eigenfunction/cocycle interface of
-- issue #35, though strong mixing already carries all the measure-theoretic dynamics used.
set_option linter.unusedVariables false in
/-- **Mixing kills eigenvalues.** A measurable eigenfunction `g` (with `g ∘ f = l • g`) of
a strongly-mixing transformation `f`, whose eigenvalue `l` is unimodular (`‖l‖ = 1`) but
different from `1`, vanishes almost everywhere.

Strong mixing enters only through the *diagonal* set correlations
`μ.real (A ∩ fᵏ ⁻¹' A) → μ.real A * μ.real A`. If `g` were not a.e. zero, pick an
admissible ball `B = ball q ρ` (`exists_ball_pos_measure`) with `A := g ⁻¹' B` of positive
measure. Iterating the eigenrelation gives `g (fⁿ x) = lⁿ g x`, so a point of
`A ∩ fⁿ ⁻¹' A` would place both `g x` and `lⁿ g x` inside `B`, forcing
`‖lⁿ q - q‖ < 2ρ ≤ ‖q‖ δ ≤ ‖q‖ ‖lⁿ - 1‖ = ‖lⁿ q - q‖` whenever `‖lⁿ - 1‖ ≥ δ`. By
`frequently_pow_far_from_one` this happens frequently, so `μ.real (A ∩ fⁿ ⁻¹' A) = 0`
along a subsequence — impossible, since mixing pushes it to `μ.real A ^ 2 > 0`. -/
theorem eigenfunction_ae_zero_of_mixing {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → X} {g : X → ℂ} {l : ℂ}
    (hmix : ∀ ⦃A : Set X⦄, MeasurableSet A →
      Tendsto (fun k => μ.real (A ∩ f^[k] ⁻¹' A)) atTop (𝓝 (μ.real A * μ.real A)))
    (hf : Measurable f) (hg : Measurable g)
    (heig : ∀ x, g (f x) = l * g x) (hl : ‖l‖ = 1) (hl1 : l ≠ 1) :
    g =ᵐ[μ] 0 := by
  by_contra hne
  -- separation constant
  set δ := ‖l - 1‖ / 2 with hδ_def
  have hδ : 0 < δ := by
    rw [hδ_def]
    have : (0 : ℝ) < ‖l - 1‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hl1
    linarith
  -- the positive-measure admissible ball
  obtain ⟨q, ρ, hq0, hρ0, hcov, hApos⟩ := exists_ball_pos_measure hne hδ
  set A : Set X := g ⁻¹' Metric.ball q ρ with hA_def
  have hA : MeasurableSet A := by
    rw [hA_def]; exact hg measurableSet_ball
  have hArpos : 0 < μ.real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hApos.ne' (measure_ne_top μ A)
  have hL : 0 < μ.real A * μ.real A := mul_pos hArpos hArpos
  -- iterated eigenrelation
  have heigpow : ∀ (n : ℕ) (x : X), g (f^[n] x) = l ^ n * g x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [Function.iterate_succ', Function.comp_apply, heig, ih]
        ring
  -- when `lⁿ` is far from `1`, the diagonal intersection is empty
  have hdisj : ∀ n : ℕ, δ ≤ ‖l ^ n - 1‖ → A ∩ f^[n] ⁻¹' A = ∅ := by
    intro n hn
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    rw [hA_def, Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hx1
    rw [hA_def, Set.mem_preimage, Set.mem_preimage, Metric.mem_ball, dist_eq_norm,
      heigpow n x] at hx2
    -- hx1 : ‖g x - q‖ < ρ,  hx2 : ‖lⁿ * g x - q‖ < ρ
    have e1 : ‖l ^ n * q - q‖ = ‖l ^ n - 1‖ * ‖q‖ := by
      rw [show l ^ n * q - q = (l ^ n - 1) * q by ring, norm_mul]
    have e2 : ‖l ^ n * q - l ^ n * g x‖ = ‖g x - q‖ := by
      rw [show l ^ n * q - l ^ n * g x = l ^ n * (q - g x) by ring, norm_mul, norm_pow, hl,
        one_pow, one_mul, norm_sub_rev]
    have tri : ‖l ^ n * q - q‖ ≤ ‖l ^ n * q - l ^ n * g x‖ + ‖l ^ n * g x - q‖ := by
      have h := norm_add_le (l ^ n * q - l ^ n * g x) (l ^ n * g x - q)
      rwa [show (l ^ n * q - l ^ n * g x) + (l ^ n * g x - q) = l ^ n * q - q by ring] at h
    have hlt : ‖l ^ n * q - q‖ < 2 * ρ := by
      have hsum : ‖l ^ n * q - q‖ < ρ + ρ :=
        calc ‖l ^ n * q - q‖
            ≤ ‖l ^ n * q - l ^ n * g x‖ + ‖l ^ n * g x - q‖ := tri
          _ = ‖g x - q‖ + ‖l ^ n * g x - q‖ := by rw [e2]
          _ < ρ + ρ := by linarith
      linarith
    have hge : 2 * ρ ≤ ‖l ^ n * q - q‖ := by
      rw [e1]
      have hmul : ‖q‖ * δ ≤ ‖l ^ n - 1‖ * ‖q‖ := by
        rw [mul_comm ‖q‖ δ]
        exact mul_le_mul_of_nonneg_right hn (norm_nonneg q)
      linarith
    linarith
  -- along a subsequence the diagonal correlation is exactly zero
  have hfreq0 : ∃ᶠ n in atTop, μ.real (A ∩ f^[n] ⁻¹' A) = 0 := by
    refine (frequently_pow_far_from_one hl hl1).mono ?_
    intro n hn
    rw [hdisj n hn, measureReal_empty]
  -- but mixing keeps it eventually positive
  have hev : ∀ᶠ n in atTop, 0 < μ.real (A ∩ f^[n] ⁻¹' A) :=
    (hmix hA).eventually_const_lt hL
  obtain ⟨n, hn0, hnpos⟩ := (hfreq0.and_eventually hev).exists
  rw [hn0] at hnpos
  exact lt_irrefl 0 hnpos

end ErgodicTheory
