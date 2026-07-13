/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.LiminfLimsup
import ErgodicTheory.Multifractal.RenyiEntropy
import ErgodicTheory.Multifractal.Defs

/-!
# The dynamical Rényi entropy rate and its factor-map monotonicity

For a probability measure `μ` on the one-sided full shift `Shift A = ℕ → A` over a finite alphabet,
the **length-`n` Rényi entropy** `H_q^{(n)}(μ)` is the Rényi entropy (of order `q`) of the family of
length-`n` cylinder masses `w ↦ μ(cylinder w)`. Its normalized `limsup`/`liminf`,
`renyiRateSup μ q = limsup_n H_q^{(n)}(μ) / n` and the corresponding `liminf`, are the upper/lower
**Rényi entropy rates**.

This file proves that a **one-block code** (a symbol map `φ : A → B` lifted coordinatewise to
`blockCode φ : Shift A → Shift B`) does not increase the Rényi entropy rate: pushing `μ` forward
along `blockCode φ` can only decrease `renyiRateSup` and `renyiRateInf`, for every order
`0 ≤ q`, `q ≠ 1`.

The mechanism is entirely **per length `n`**, so **no stationarity or shift-invariance of `μ` is
assumed**:

* the preimage of a length-`n` cylinder of `Shift B` under `blockCode φ` is the finite disjoint
  union of the length-`n` cylinders of `Shift A` over the fiber of the induced word map
  `wordMap φ n`, so by measure additivity the pushed cylinder masses are exactly the *merged*
  weights `mergedWeights (wordMap φ n)` of the original cylinder masses
  (`cylinderMass_map_blockCode`);
* the static data-processing inequality `renyiEntropy_merge_le`
  (`ErgodicTheory/Multifractal/RenyiEntropy.lean`) then gives the per-`n` bound
  `H_q^{(n)}(map) ≤ H_q^{(n)}(μ)` (`renyiEntropySeq_map_blockCode_le`);
* dividing by `n` and passing to `limsup`/`liminf` — using the uniform bounds
  `0 ≤ H_q^{(n)}(μ) / n ≤ C_q` that make the normalized sequence order-bounded — yields the rate
  monotonicity (`renyiRateSup_map_blockCode_le`, `renyiRateInf_map_blockCode_le`).

## Scope boundary (why one-block codes, and why `q ≠ 1`)

The rate *limit* (existence of `lim_n H_q^{(n)} / n`, its hidden-Markov closed forms — Rached,
Alajaji and Campbell, IEEE Trans. Inform. Theory 47 (2001); Breitner and Skorski
(arXiv:1709.09699)) is a genuinely
harder question and is **not** needed for, nor addressed by, the monotonicity here — the argument is
purely per-`n`. Moreover the fully isomorphism-invariant *dynamical* Rényi entropy degenerates
(Takens and Verbitskiy, Israel J. Math. 127 (2002): it collapses to `+∞` for `q < 1` and to the
Kolmogorov–Sinai entropy for `q ≥ 1`), so monotonicity under *general* measurable factors is
ill-posed for `q ≠ 1`. The honest, non-degenerate statement is exactly the **one-block (symbol)
code** monotonicity proved here; `q = 1` is the unique order at which the rate is monotone under
arbitrary factors (the Kolmogorov–Sinai case, handled elsewhere in this library).

## Main definitions

* `ErgodicTheory.Multifractal.cylinderMass`, `renyiEntropySeq`, `renyiRateSup`, `renyiRateInf`.
* `ErgodicTheory.Multifractal.blockCode`, `wordMap`.

## Main results

* `ErgodicTheory.Multifractal.cylinderMass_map_blockCode`: the one-block pushforward identity.
* `ErgodicTheory.Multifractal.renyiEntropySeq_map_blockCode_le`: the per-length data-processing
  inequality.
* `ErgodicTheory.Multifractal.renyiRateSup_map_blockCode_le`,
  `renyiRateInf_map_blockCode_le`: the rate monotonicity.

## References

* A. Rényi, *On measures of entropy and information*, Proc. 4th Berkeley Symp. (1961).
* T. van Erven and P. Harremoës, *Rényi divergence and Kullback–Leibler divergence*, IEEE Trans.
  Inform. Theory 60 (2014), no. 7.
* F. Takens and E. Verbitskiy, *Rényi entropies of aperiodic dynamical systems*,
  Israel J. Math. 127 (2002), 279–302.
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

-- The alphabets carry a shared instance block that is used across many lemmas, each of which uses a
-- different subset (some need `Fintype`/`DecidableEq` only in a proof, some only for a measure).
-- The purely type-level "unused-in-type" style linters would otherwise fire spuriously, so they are
-- disabled for this file; every instance below is genuinely used somewhere.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ErgodicTheory.Multifractal

variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable {B : Type*} [Fintype B] [Nonempty B] [DecidableEq B] [MeasurableSpace B]
  [MeasurableSingletonClass B]

/-! ### Cylinder sets and their masses -/

/-- The length-`n` **cylinder set** of a word `w : Fin n → A`: the sequences agreeing with `w` on
the first `n` coordinates. -/
def cylinder (n : ℕ) (w : Fin n → A) : Set (Shift A) := {x | ∀ k : Fin n, x (k : ℕ) = w k}

/-- The length-`n` cylinder is measurable: it is the finite intersection of the coordinate
constraints `{x | x k = w k}`. -/
theorem measurableSet_cylinder (n : ℕ) (w : Fin n → A) : MeasurableSet (cylinder n w) := by
  have hrw : cylinder n w = ⋂ k : Fin n, (fun x : Shift A => x (k : ℕ)) ⁻¹' {w k} := by
    ext x
    simp only [cylinder, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hrw]
  exact MeasurableSet.iInter fun k => (measurable_pi_apply (k : ℕ)) (measurableSet_singleton (w k))

/-- Distinct length-`n` words give disjoint cylinders. -/
theorem cylinder_disjoint {n : ℕ} {w w' : Fin n → A} (h : w ≠ w') :
    Disjoint (cylinder n w) (cylinder n w') := by
  rw [Set.disjoint_left]
  rintro x hx hx'
  exact h (funext fun k => (hx k).symm.trans (hx' k))

/-- The length-`n` cylinders cover the whole shift space. -/
theorem iUnion_cylinder (n : ℕ) : (⋃ w : Fin n → A, cylinder n w) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, cylinder, Set.mem_setOf_eq]
  exact ⟨fun k => x (k : ℕ), fun k => rfl⟩

/-- The **length-`n` cylinder mass** of a word `w` under `μ`: the real number `μ(cylinder w)`. -/
noncomputable def cylinderMass (μ : Measure (Shift A)) (n : ℕ) (w : Fin n → A) : ℝ :=
  (μ (cylinder n w)).toReal

/-- Cylinder masses are nonnegative. -/
theorem cylinderMass_nonneg (μ : Measure (Shift A)) (n : ℕ) (w : Fin n → A) :
    0 ≤ cylinderMass μ n w := ENNReal.toReal_nonneg

/-- For a probability measure the length-`n` cylinder masses sum to `1` (the cylinders partition the
space). -/
theorem sum_cylinderMass (μ : Measure (Shift A)) [IsProbabilityMeasure μ] (n : ℕ) :
    ∑ w : Fin n → A, cylinderMass μ n w = 1 := by
  have hpair : Pairwise (Disjoint on fun w : Fin n → A => cylinder n w) :=
    fun w w' h => cylinder_disjoint h
  have hsum : ∑ w : Fin n → A, μ (cylinder n w) = 1 := by
    have hmi := measure_iUnion (μ := μ) hpair (measurableSet_cylinder n)
    rw [iUnion_cylinder, measure_univ, tsum_fintype] at hmi
    exact hmi.symm
  simp only [cylinderMass]
  rw [← ENNReal.toReal_sum (fun w _ => measure_ne_top μ _), hsum, ENNReal.toReal_one]

/-- For a probability measure some length-`n` cylinder has positive mass. -/
theorem exists_pos_cylinderMass (μ : Measure (Shift A)) [IsProbabilityMeasure μ] (n : ℕ) :
    ∃ w : Fin n → A, 0 < cylinderMass μ n w := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hz : ∑ w : Fin n → A, cylinderMass μ n w = 0 :=
    Finset.sum_eq_zero (fun w _ => le_antisymm (hcon w) (cylinderMass_nonneg μ n w))
  rw [sum_cylinderMass] at hz
  exact one_ne_zero hz

/-! ### The Rényi entropy sequence and rates -/

/-- The **length-`n` Rényi entropy** of `μ`: the Rényi entropy (order `q`) of the length-`n`
cylinder-mass family. -/
noncomputable def renyiEntropySeq (μ : Measure (Shift A)) (q : ℝ) (n : ℕ) : ℝ :=
  renyiEntropy (cylinderMass μ n) q

/-- The **upper Rényi entropy rate** `limsup_n H_q^{(n)}(μ) / n`. -/
noncomputable def renyiRateSup (μ : Measure (Shift A)) (q : ℝ) : ℝ :=
  limsup (fun n => renyiEntropySeq μ q n / n) atTop

/-- The **lower Rényi entropy rate** `liminf_n H_q^{(n)}(μ) / n`. -/
noncomputable def renyiRateInf (μ : Measure (Shift A)) (q : ℝ) : ℝ :=
  liminf (fun n => renyiEntropySeq μ q n / n) atTop

/-! ### One-block codes -/

/-- The **one-block code** induced by a symbol map `φ : A → B`: relabel every coordinate by `φ`. -/
def blockCode (φ : A → B) : Shift A → Shift B := fun x k => φ (x k)

/-- The one-block code is measurable. -/
theorem measurable_blockCode (φ : A → B) : Measurable (blockCode φ) :=
  measurable_pi_lambda _ fun k => (measurable_of_finite φ).comp (measurable_pi_apply k)

/-- The **induced word map** `wordMap φ n : (Fin n → A) → (Fin n → B)`, post-composition by `φ`. -/
def wordMap (φ : A → B) (n : ℕ) : (Fin n → A) → (Fin n → B) := fun v k => φ (v k)

/-! ### The one-block pushforward identity -/

/-- The `blockCode φ`-preimage of a length-`n` `B`-cylinder is the disjoint union of the length-`n`
`A`-cylinders over the fiber of the word map `wordMap φ n`. -/
theorem preimage_blockCode_cylinder (φ : A → B) (n : ℕ) (w' : Fin n → B) :
    blockCode φ ⁻¹' cylinder n w'
      = ⋃ v ∈ Finset.univ.filter (fun v => wordMap φ n v = w'), cylinder n v := by
  ext x
  simp only [Set.mem_preimage, cylinder, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
    Finset.mem_univ, true_and, exists_prop, blockCode]
  constructor
  · intro hx
    exact ⟨fun k => x (k : ℕ), funext fun k => hx k, fun k => rfl⟩
  · rintro ⟨v, hv, hxv⟩ k
    rw [hxv k]
    exact congrFun hv k

/-- Measure additivity over the fiber: the mass of the preimage of a `B`-cylinder is the sum of the
`A`-cylinder masses over the word-map fiber. -/
theorem measure_preimage_blockCode_cylinder (μ : Measure (Shift A)) (φ : A → B) (n : ℕ)
    (w' : Fin n → B) :
    μ (blockCode φ ⁻¹' cylinder n w')
      = ∑ v ∈ Finset.univ.filter (fun v => wordMap φ n v = w'), μ (cylinder n v) := by
  rw [preimage_blockCode_cylinder,
    measure_biUnion_finset (fun v _ v' _ hne => cylinder_disjoint hne)
      (fun v _ => measurableSet_cylinder n v)]

/-- **One-block pushforward identity.** The length-`n` cylinder masses of the pushforward
`Measure.map (blockCode φ) μ` are the *merged* cylinder masses of `μ` along the word map
`wordMap φ n`. -/
theorem cylinderMass_map_blockCode (μ : Measure (Shift A)) [IsFiniteMeasure μ] (φ : A → B) (n : ℕ)
    (w' : Fin n → B) :
    cylinderMass (Measure.map (blockCode φ) μ) n w'
      = mergedWeights (wordMap φ n) (cylinderMass μ n) w' := by
  rw [cylinderMass, Measure.map_apply (measurable_blockCode φ) (measurableSet_cylinder n w'),
    measure_preimage_blockCode_cylinder, ENNReal.toReal_sum (fun v _ => measure_ne_top μ _)]
  rfl

/-! ### The per-length data-processing inequality -/

/-- **Per-length data-processing inequality.** For every length `n` and order `0 ≤ q`, `q ≠ 1`, the
one-block pushforward does not increase the length-`n` Rényi entropy. -/
theorem renyiEntropySeq_map_blockCode_le (μ : Measure (Shift A)) [IsProbabilityMeasure μ]
    (φ : A → B) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≠ 1) (n : ℕ) :
    renyiEntropySeq (Measure.map (blockCode φ) μ) q n ≤ renyiEntropySeq μ q n := by
  have hfun : cylinderMass (Measure.map (blockCode φ) μ) n
      = mergedWeights (wordMap φ n) (cylinderMass μ n) := funext (cylinderMass_map_blockCode μ φ n)
  simp only [renyiEntropySeq, hfun]
  exact renyiEntropy_merge_le (wordMap φ n) (fun v => cylinderMass_nonneg μ n v)
    (exists_pos_cylinderMass μ n) hq0 hq1

/-! ### Order-boundedness of the normalized sequence -/

/-- The normalized length-`n` Rényi entropy is nonnegative. -/
theorem renyiEntropySeq_div_nonneg (μ : Measure (Shift A)) [IsProbabilityMeasure μ] {q : ℝ}
    (hq1 : q ≠ 1) (n : ℕ) : 0 ≤ renyiEntropySeq μ q n / n :=
  div_nonneg (renyiEntropy_nonneg (fun v => cylinderMass_nonneg μ n v) (sum_cylinderMass μ n)
    (exists_pos_cylinderMass μ n) hq1) (Nat.cast_nonneg n)

/-- The logarithm of the number of length-`n` words is `n log (card A)`. -/
private lemma log_card_word (n : ℕ) :
    Real.log (Fintype.card (Fin n → A)) = n * Real.log (Fintype.card A) := by
  rw [show Fintype.card (Fin n → A) = Fintype.card A ^ n by
        rw [Fintype.card_fun, Fintype.card_fin], Nat.cast_pow, Real.log_pow]

/-- The normalized length-`n` Rényi entropy is uniformly bounded above by a constant `C_q`. Combined
with nonnegativity this makes the normalized sequence order-bounded, hence its `limsup`/`liminf` are
monotone under the per-length inequality. -/
theorem exists_upper_bound (μ : Measure (Shift A)) [IsProbabilityMeasure μ] {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≠ 1) : ∃ C : ℝ, ∀ n : ℕ, renyiEntropySeq μ q n / n ≤ C := by
  have hlogA : 0 ≤ Real.log (Fintype.card A) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  rcases lt_or_gt_of_ne hq1 with hlt | hgt
  · refine ⟨(1 - q)⁻¹ * Real.log (Fintype.card A), fun n => ?_⟩
    have hc : 0 ≤ (1 - q)⁻¹ := le_of_lt (inv_pos.mpr (by linarith))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]; exact mul_nonneg hc hlogA
    · rw [renyiEntropySeq, div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
      calc renyiEntropy (cylinderMass μ n) q
          ≤ (1 - q)⁻¹ * Real.log (Fintype.card (Fin n → A)) :=
            renyiEntropy_le_of_lt (fun v => cylinderMass_nonneg μ n v) (sum_cylinderMass μ n)
              (exists_pos_cylinderMass μ n) hq0 hlt
        _ = (1 - q)⁻¹ * Real.log (Fintype.card A) * n := by rw [log_card_word]; ring
  · refine ⟨(q / (q - 1)) * Real.log (Fintype.card A), fun n => ?_⟩
    have hc : 0 ≤ q / (q - 1) := le_of_lt (div_pos (by linarith) (by linarith))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]; exact mul_nonneg hc hlogA
    · rw [renyiEntropySeq, div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
      calc renyiEntropy (cylinderMass μ n) q
          ≤ (q / (q - 1)) * Real.log (Fintype.card (Fin n → A)) :=
            renyiEntropy_le_of_gt (fun v => cylinderMass_nonneg μ n v) (sum_cylinderMass μ n)
              (exists_pos_cylinderMass μ n) hgt
        _ = (q / (q - 1)) * Real.log (Fintype.card A) * n := by rw [log_card_word]; ring

/-! ### The Rényi entropy rate is monotone under one-block codes -/

/-- **Upper Rényi entropy rate monotonicity under one-block codes.** For every order `0 ≤ q`,
`q ≠ 1`, the pushforward along a one-block code does not increase the upper Rényi entropy rate. No
stationarity of `μ` is assumed — the bound is per length `n`. -/
theorem renyiRateSup_map_blockCode_le (μ : Measure (Shift A)) [IsProbabilityMeasure μ] (φ : A → B)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≠ 1) :
    renyiRateSup (Measure.map (blockCode φ) μ) q ≤ renyiRateSup μ q := by
  haveI : IsProbabilityMeasure (Measure.map (blockCode φ) μ) :=
    Measure.isProbabilityMeasure_map (measurable_blockCode φ).aemeasurable
  obtain ⟨C, hC⟩ := exists_upper_bound μ hq0 hq1
  have hpt : ∀ n : ℕ, renyiEntropySeq (Measure.map (blockCode φ) μ) q n / (n : ℝ)
      ≤ renyiEntropySeq μ q n / (n : ℝ) := by
    intro n
    gcongr
    exact renyiEntropySeq_map_blockCode_le μ φ hq0 hq1 n
  exact limsup_le_limsup (Eventually.of_forall hpt)
    (isCoboundedUnder_le_of_le atTop
      (fun n => renyiEntropySeq_div_nonneg (Measure.map (blockCode φ) μ) hq1 n))
    (isBoundedUnder_of ⟨C, hC⟩)

/-- **Lower Rényi entropy rate monotonicity under one-block codes.** -/
theorem renyiRateInf_map_blockCode_le (μ : Measure (Shift A)) [IsProbabilityMeasure μ] (φ : A → B)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≠ 1) :
    renyiRateInf (Measure.map (blockCode φ) μ) q ≤ renyiRateInf μ q := by
  haveI : IsProbabilityMeasure (Measure.map (blockCode φ) μ) :=
    Measure.isProbabilityMeasure_map (measurable_blockCode φ).aemeasurable
  obtain ⟨C, hC⟩ := exists_upper_bound μ hq0 hq1
  have hpt : ∀ n : ℕ, renyiEntropySeq (Measure.map (blockCode φ) μ) q n / (n : ℝ)
      ≤ renyiEntropySeq μ q n / (n : ℝ) := by
    intro n
    gcongr
    exact renyiEntropySeq_map_blockCode_le μ φ hq0 hq1 n
  exact liminf_le_liminf (Eventually.of_forall hpt)
    (isBoundedUnder_of ⟨0, fun n =>
      renyiEntropySeq_div_nonneg (Measure.map (blockCode φ) μ) hq1 n⟩)
    (isCoboundedUnder_ge_of_le atTop hC)

end ErgodicTheory.Multifractal
