/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.RenyiRate
import ErgodicTheory.Multifractal.BernoulliEntropy
import Mathlib.Probability.Distributions.Uniform

/-!
# The Bernoulli closed form for the dynamical Rényi entropy rate

For the i.i.d. (Bernoulli) measure `bern ν` on the one-sided full shift `Shift A` over a finite
alphabet `A` with single-symbol law `ν`, this file computes the length-`n` Rényi entropy and its
rate in **closed form**: everything factorizes over coordinates, so the rate is *exactly* the static
single-symbol Rényi entropy of the law `ν`, realized as an honest `limsup = liminf` limit.

The chain of identities (each for an arbitrary order `q`, and — where the entropy is invoked — for
`q ≠ 1`):

* **Cylinder masses are products** (`cylinderMass_bern`): the length-`n` cylinder mass of a word
  `w` is `∏ k, (ν {w k}).toReal`, by the product-measure evaluation `Measure.infinitePi_pi` on the
  cylinder box (reusing the repo's `cylinder_eq_pi`).
* **Power-sum factorization** (`partitionFunction_cylinderMass_bern`): the length-`n` partition
  function factors as `Z_q^{(n)} = (Z_q)^n`, where the base `Z_q = partitionFunction (fun a =>
  (ν {a}).toReal)` is the single-symbol partition function. The guard `0 < ∏ k, p k` factors through
  the coordinates (`guard_prod_eq_prod_guard`), and the sum-over-words / product-over-coord. swap
  (`Finset.sum_prod_piFinset`) collapses `∑_w ∏_k g(p (w k))` to `(∑_a g(p a))^n`.
* **Exact rate** (`renyiEntropySeq_bern`, `renyiRateSup_bern`, `renyiRateInf_bern`): hence
  `H_q^{(n)}(bern ν) = n · H_q(ν)` (via `Real.log_pow`), so the normalized sequence is eventually
  constant `H_q(ν)`, and both the upper and lower rates equal `H_q(ν)`.
* **Merged-Bernoulli pushforward** (`map_blockCode_bern`): pushing a Bernoulli measure forward along
  a one-block code `blockCode φ` is again Bernoulli, with the mapped single-symbol law:
  `Measure.map (blockCode φ) (bern ν) = bern (Measure.map φ ν)`. This is the coordinatewise
  pushforward of a product measure, proved by checking agreement on measurable boxes
  (`Measure.eq_infinitePi`); the mapped marginals are the merged weights
  (`measureReal_map_singleton`).

## The tier-3 strict witness

Combining the exact rate with the strict static data-processing inequality
(`renyiEntropy_merge_lt`), a one-block code that **glues two atoms of positive `ν`-mass** strictly
lowers the Rényi entropy rate, for every order `q ∈ (0,1) ∪ (1,∞)`
(`renyiRateSup_map_blockCode_bern_lt`, `renyiRateInf_map_blockCode_bern_lt`). A concrete
instantiation over `A = Fin 3 → B = Fin 2` with the uniform law and an atom-gluing symbol map
certifies the strict drop non-vacuously (`renyiRate_strict_drop_uniformFin3`).

## The `q = 1` anchor and the honest scope boundary

These Bernoulli rates realize the `q`-family of Rényi entropy rates as a **factor-monotone** family
on the one-block-code category (`ErgodicTheory/Multifractal/RenyiRate.lean`) with strict drops on
proper merges (this file). This is exactly the `c`-function picture. The boundary is sharp: the
fully isomorphism-invariant *dynamical* Rényi entropy **degenerates** for `q ≠ 1` (Takens and
Verbitskiy, Israel J. Math. 127 (2002): it collapses to `+∞` for `q < 1` and to the
Kolmogorov–Sinai entropy for `q ≥ 1`), so monotonicity under *general* measurable factors is FALSE
for `q ≠ 1` — a Markov chain that is Ornstein-isomorphic to a Bernoulli shift has a different
order-`2` Rényi entropy. Thus `q = 1` (the Kolmogorov–Sinai case) is the unique order at which the
rate is monotone under arbitrary factors, exactly the anticipated dichotomy; the honest
non-degenerate statement for `q ≠ 1` is the one-block (symbol) code monotonicity, whose Bernoulli
strict witnesses are supplied here.

## Main results

* `ErgodicTheory.Multifractal.cylinderMass_bern`
* `ErgodicTheory.Multifractal.partitionFunction_cylinderMass_bern`
* `ErgodicTheory.Multifractal.renyiEntropySeq_bern`
* `ErgodicTheory.Multifractal.renyiRateSup_bern`, `renyiRateInf_bern`
* `ErgodicTheory.Multifractal.map_blockCode_bern`
* `ErgodicTheory.Multifractal.measureReal_map_singleton`
* `ErgodicTheory.Multifractal.renyiRateSup_map_blockCode_bern_lt`,
  `renyiRateInf_map_blockCode_bern_lt`
* `ErgodicTheory.Multifractal.renyiRate_strict_drop_uniformFin3`

## References

* A. Rényi, *On measures of entropy and information*, Proc. 4th Berkeley Symp. (1961).
* F. Takens and E. Verbitskiy, *Rényi entropies of aperiodic dynamical systems*,
  Israel J. Math. 127 (2002), 279–302.
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

-- The alphabets share an instance block used across many lemmas, each of which needs a different
-- subset; the purely type-level "unused-in-type" linters would fire spuriously (every instance is
-- genuinely used somewhere), so they are disabled for this file — matching `RenyiRate.lean`.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ErgodicTheory.Multifractal

variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable {B : Type*} [Fintype B] [Nonempty B] [DecidableEq B] [MeasurableSpace B]
  [MeasurableSingletonClass B]

/-! ### Coordinate factorization of the guarded power -/

/-- The guarded power `if 0 < x then x^q else 0` is **multiplicative** over a finite product of
nonnegative reals: `(if 0 < ∏ k, x k then (∏ k, x k)^q else 0) = ∏ k, (if 0 < x k then (x k)^q
else 0)`. When every factor is positive the product is positive and `rpow` distributes over the
product (`Real.finsetProd_rpow`); when some factor vanishes both sides are `0`. -/
private lemma guard_prod_eq_prod_guard {m : ℕ} (x : Fin m → ℝ) (hx : ∀ k, 0 ≤ x k) (q : ℝ) :
    (if 0 < ∏ k, x k then (∏ k, x k) ^ q else 0)
      = ∏ k, (if 0 < x k then (x k) ^ q else 0) := by
  classical
  by_cases h : 0 < ∏ k, x k
  · rw [if_pos h]
    have hall : ∀ k, 0 < x k := by
      intro k
      by_contra hk
      have hxk : x k = 0 := le_antisymm (not_lt.1 hk) (hx k)
      have hz : (∏ j, x j) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hxk
      rw [hz] at h; exact lt_irrefl 0 h
    rw [← Real.finsetProd_rpow Finset.univ x (fun k _ => hx k) q]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [if_pos (hall k)]
  · rw [if_neg h]
    have hzero : (∏ k, x k) = 0 :=
      le_antisymm (not_lt.1 h) (Finset.prod_nonneg (fun k _ => hx k))
    obtain ⟨k₀, _, hk₀⟩ := Finset.prod_eq_zero_iff.1 hzero
    refine (Finset.prod_eq_zero (Finset.mem_univ k₀) ?_).symm
    rw [hk₀, if_neg (lt_irrefl (0 : ℝ))]

/-- The length-`m` partition function of the coordinatewise product family `w ↦ ∏ k, p (w k)`
factors as the `m`-th power of the single-symbol partition function `Z_q(p)`. The guarded power is
multiplicative over coordinates (`guard_prod_eq_prod_guard`) and the sum-over-words /
product-over-coordinates swap (`Finset.sum_prod_piFinset`) collapses the sum. -/
private lemma partitionFunction_prod_eq_pow {m : ℕ} (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (q : ℝ) :
    partitionFunction (fun w : Fin m → A => ∏ k, p (w k)) q = (partitionFunction p q) ^ m := by
  classical
  simp only [partitionFunction]
  have hmul : ∀ w : Fin m → A,
      (if 0 < ∏ k, p (w k) then (∏ k, p (w k)) ^ q else 0)
        = ∏ k, (if 0 < p (w k) then (p (w k)) ^ q else 0) := fun w =>
    guard_prod_eq_prod_guard (fun k => p (w k)) (fun k => hp (w k)) q
  simp_rw [hmul]
  have hswap : ∑ w : Fin m → A, ∏ k, (if 0 < p (w k) then (p (w k)) ^ q else 0)
      = ∏ _k : Fin m, ∑ a, (if 0 < p a then (p a) ^ q else 0) := by
    rw [← Fintype.piFinset_univ (α := Fin m) (β := fun _ => A)]
    exact Finset.sum_prod_piFinset Finset.univ
      (fun (_ : Fin m) (a : A) => if 0 < p a then (p a) ^ q else 0)
  rw [hswap, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The Bernoulli cylinder mass -/

variable (ν : Measure A) [IsProbabilityMeasure ν]

/-- The `bern ν`-mass of a length-`n` cylinder `cylinder n w` is the product `∏ k, ν {w k}` of
single-symbol masses. The cylinder is the measurable box (`cylinder_eq_pi`) whose product-measure
value is the finite product of coordinate masses (`Measure.infinitePi_pi`). -/
theorem bern_cylinder (n : ℕ) (w : Fin n → A) :
    bern ν (cylinder n w) = ∏ k : Fin n, ν {w k} := by
  have hset : cylinder n w = {x : Shift A | ∀ k : Fin n, x (k : ℕ) = w k} := rfl
  rw [hset, cylinder_eq_pi, bern, Measure.infinitePi_pi (μ := fun _ : ℕ => ν) ?mble]
  case mble =>
    intro i _
    by_cases hi : i < n
    · rw [dif_pos hi]; exact measurableSet_singleton _
    · rw [dif_neg hi]; exact MeasurableSet.univ
  rw [Finset.prod_range fun i => ν (if hi : i < n then {w ⟨i, hi⟩} else Set.univ)]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [dif_pos k.2]

/-- **Cylinder masses are products.** The length-`n` cylinder mass of a word `w` under the Bernoulli
measure `bern ν` is `∏ k, (ν {w k}).toReal`. -/
theorem cylinderMass_bern (n : ℕ) (w : Fin n → A) :
    cylinderMass (bern ν) n w = ∏ k : Fin n, (ν {w k}).toReal := by
  rw [cylinderMass, bern_cylinder, ENNReal.toReal_prod]

/-- **Power-sum factorization.** The length-`n` partition function of the Bernoulli cylinder masses
factors as the `n`-th power of the single-symbol partition function
`Z_q = partitionFunction (fun a => (ν {a}).toReal)`. -/
theorem partitionFunction_cylinderMass_bern (q : ℝ) (n : ℕ) :
    partitionFunction (cylinderMass (bern ν) n) q
      = (partitionFunction (fun a => (ν {a}).toReal) q) ^ n := by
  have hcm : (cylinderMass (bern ν) n)
      = (fun w : Fin n → A => ∏ k, (fun a => (ν {a}).toReal) (w k)) := by
    funext w; rw [cylinderMass_bern]
  rw [hcm, partitionFunction_prod_eq_pow (fun a => (ν {a}).toReal)
    (fun a => ENNReal.toReal_nonneg) q]

/-! ### The exact Rényi entropy rate of the Bernoulli measure -/

/-- **Exact length-`n` entropy.** For the Bernoulli measure, the length-`n` Rényi entropy is
`n · H_q(ν)`, where `H_q(ν) = renyiEntropy (fun a => (ν {a}).toReal) q` is the single-symbol Rényi
entropy. (This is the logarithm of the `n`-th power of the single-symbol partition function.) -/
theorem renyiEntropySeq_bern (q : ℝ) (n : ℕ) :
    renyiEntropySeq (bern ν) q n = (n : ℝ) * renyiEntropy (fun a => (ν {a}).toReal) q := by
  rw [renyiEntropySeq, renyiEntropy, partitionFunction_cylinderMass_bern, Real.log_pow,
    renyiEntropy]
  ring

/-- **Exact upper rate.** The upper Rényi entropy rate of the Bernoulli measure equals the
single-symbol Rényi entropy `H_q(ν)`: the normalized sequence `n · H_q(ν) / n` is eventually the
constant `H_q(ν)`, whose `limsup` is itself. -/
theorem renyiRateSup_bern (q : ℝ) :
    renyiRateSup (bern ν) q = renyiEntropy (fun a => (ν {a}).toReal) q := by
  rw [renyiRateSup]
  have hev : (fun n : ℕ => renyiEntropySeq (bern ν) q n / n)
      =ᶠ[atTop] (fun _ => renyiEntropy (fun a => (ν {a}).toReal) q) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [renyiEntropySeq_bern]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_comm, mul_div_assoc, div_self hn0, mul_one]
  rw [Filter.limsup_congr hev, Filter.limsup_const]

/-- **Exact lower rate.** The lower Rényi entropy rate of the Bernoulli measure equals the
single-symbol Rényi entropy `H_q(ν)`. Together with `renyiRateSup_bern` this shows the rate is an
honest limit (`limsup = liminf`). -/
theorem renyiRateInf_bern (q : ℝ) :
    renyiRateInf (bern ν) q = renyiEntropy (fun a => (ν {a}).toReal) q := by
  rw [renyiRateInf]
  have hev : (fun n : ℕ => renyiEntropySeq (bern ν) q n / n)
      =ᶠ[atTop] (fun _ => renyiEntropy (fun a => (ν {a}).toReal) q) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [renyiEntropySeq_bern]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_comm, mul_div_assoc, div_self hn0, mul_one]
  rw [Filter.liminf_congr hev, Filter.liminf_const]

/-! ### The merged-Bernoulli pushforward identity -/

/-- **Marginal identity.** The single-symbol mass of the pushforward `Measure.map φ ν` at `b` is the
merged weight (fiber sum) of the single-symbol masses of `ν`:
`(Measure.map φ ν {b}).toReal = mergedWeights φ (fun a => (ν {a}).toReal) b`. -/
theorem measureReal_map_singleton (φ : A → B) (b : B) :
    ((Measure.map φ ν) {b}).toReal = mergedWeights φ (fun a => (ν {a}).toReal) b := by
  rw [Measure.map_apply (measurable_of_finite φ) (measurableSet_singleton b)]
  have hset : (φ ⁻¹' {b}) = (↑(Finset.univ.filter (fun a => φ a = b)) : Set A) := by
    ext a
    simp [Set.mem_preimage]
  rw [hset, ← MeasureTheory.sum_measure_singleton,
    ENNReal.toReal_sum (fun a _ => measure_ne_top ν _)]
  simp only [mergedWeights]

/-- **Merged-Bernoulli pushforward.** The one-block pushforward of a Bernoulli measure is again
Bernoulli, with the mapped single-symbol law:
`Measure.map (blockCode φ) (bern ν) = bern (Measure.map φ ν)`. This is the coordinatewise
pushforward of a product measure; it is checked on measurable boxes
(`Measure.eq_infinitePi`), where the preimage of a box is the box of preimages and both sides
evaluate by `Measure.infinitePi_pi` to the same finite product of mapped marginals. -/
theorem map_blockCode_bern (φ : A → B) :
    Measure.map (blockCode φ) (bern ν) = bern (Measure.map φ ν) := by
  haveI : IsProbabilityMeasure (Measure.map φ ν) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite φ).aemeasurable
  change Measure.map (blockCode φ) (bern ν)
      = Measure.infinitePi (fun _ : ℕ => Measure.map φ ν)
  refine Measure.eq_infinitePi (μ := fun _ : ℕ => Measure.map φ ν) ?_
  intro s t ht
  have hbox : MeasurableSet (Set.pi (↑s) t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply (measurable_blockCode φ) hbox]
  have hpre : blockCode φ ⁻¹' (Set.pi (↑s) t) = Set.pi (↑s) (fun i => φ ⁻¹' t i) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, blockCode]
  rw [hpre, bern, Measure.infinitePi_pi (μ := fun _ : ℕ => ν)
    (fun i _ => measurable_of_finite φ (ht i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Measure.map_apply (measurable_of_finite φ) (ht i)]

/-! ### The tier-3 strict witness -/

/-- **Strict upper-rate drop under a merge.** For every order `q ∈ (0,1) ∪ (1,∞)`, a one-block code
`φ` that glues two distinct symbols `i ≠ j` of positive `ν`-mass strictly lowers the upper Rényi
entropy rate. Combines the exact-rate identity, the merged-Bernoulli pushforward and the strict
static data-processing inequality `renyiEntropy_merge_lt`. -/
theorem renyiRateSup_map_blockCode_bern_lt (φ : A → B) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≠ 1) {i j : A} (hij : i ≠ j) (hfi : 0 < (ν {i}).toReal)
    (hfj : 0 < (ν {j}).toReal) (hf : φ i = φ j) :
    renyiRateSup (Measure.map (blockCode φ) (bern ν)) q < renyiRateSup (bern ν) q := by
  haveI : IsProbabilityMeasure (Measure.map φ ν) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite φ).aemeasurable
  rw [map_blockCode_bern, renyiRateSup_bern, renyiRateSup_bern]
  have hfun : (fun b => ((Measure.map φ ν) {b}).toReal)
      = mergedWeights φ (fun a => (ν {a}).toReal) := funext (measureReal_map_singleton ν φ)
  rw [hfun]
  exact renyiEntropy_merge_lt φ (fun _ => ENNReal.toReal_nonneg) hq0 hq1 hij hfi hfj hf

/-- **Strict lower-rate drop under a merge.** The lower Rényi entropy rate strictly drops under a
merge of two positive-mass atoms, for every order `q ∈ (0,1) ∪ (1,∞)`. -/
theorem renyiRateInf_map_blockCode_bern_lt (φ : A → B) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≠ 1) {i j : A} (hij : i ≠ j) (hfi : 0 < (ν {i}).toReal)
    (hfj : 0 < (ν {j}).toReal) (hf : φ i = φ j) :
    renyiRateInf (Measure.map (blockCode φ) (bern ν)) q < renyiRateInf (bern ν) q := by
  haveI : IsProbabilityMeasure (Measure.map φ ν) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite φ).aemeasurable
  rw [map_blockCode_bern, renyiRateInf_bern, renyiRateInf_bern]
  have hfun : (fun b => ((Measure.map φ ν) {b}).toReal)
      = mergedWeights φ (fun a => (ν {a}).toReal) := funext (measureReal_map_singleton ν φ)
  rw [hfun]
  exact renyiEntropy_merge_lt φ (fun _ => ENNReal.toReal_nonneg) hq0 hq1 hij hfi hfj hf

/-! ### A concrete non-vacuous witness -/

/-- **Concrete strict drop.** With the uniform law on `A = Fin 3`, the order-`2` upper Rényi entropy
rate strictly drops under the one-block code `Fin 3 → Fin 2` that glues the two atoms `1, 2` (of
positive mass `1/3`). This certifies the tier-3 strict witness with explicit finite spaces (so it is
non-vacuous at compile time). -/
theorem renyiRate_strict_drop_uniformFin3 :
    renyiRateSup (Measure.map (blockCode (fun _ : Fin 3 => (0 : Fin 2)))
        (bern (PMF.uniformOfFintype (Fin 3)).toMeasure)) 2
      < renyiRateSup (bern (PMF.uniformOfFintype (Fin 3)).toMeasure) 2 := by
  have hmass : ∀ a : Fin 3, 0 < ((PMF.uniformOfFintype (Fin 3)).toMeasure {a}).toReal := by
    intro a
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
    exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 (by simp)) (ENNReal.inv_ne_top.2 (by simp))
  exact renyiRateSup_map_blockCode_bern_lt
    (PMF.uniformOfFintype (Fin 3)).toMeasure (fun _ : Fin 3 => (0 : Fin 2))
    (q := 2) (i := 1) (j := 2) (by norm_num) (by norm_num) (by decide)
    (hmass 1) (hmass 2) rfl

end ErgodicTheory.Multifractal
