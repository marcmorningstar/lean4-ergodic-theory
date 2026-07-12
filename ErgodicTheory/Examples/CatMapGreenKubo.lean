/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapToral
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Dist

/-!
# Green–Kubo variance asymptotics and Chebyshev concentration for the cat map

For the Arnold cat map `catTorus : 𝕋² → 𝕋²` (a measure-preserving, ergodic hyperbolic toral
automorphism, see `ErgodicTheory.Examples.CatMapToral`) and a bounded measurable real observable
`f`, this file develops the **quantitative** consequences of exponential decay of correlations for
the fluctuations of the Birkhoff sums `Sₙ = ∑_{k<n} f ∘ Tᵏ`.

The full dynamical central limit theorem is out of reach in current Mathlib (there is no martingale
CLT), so we formalize the two honest quantitative deliverables that *do* follow from summable
correlations:

* **(A) Green–Kubo variance asymptotics.**  With `ρ(k) = cov[f, f∘Tᵏ]` (the autocovariance) and the
  hypothesis of geometric decay `|ρ(k)| ≤ C·θᵏ` (`0 ≤ θ < 1`), the normalized variance converges to
  the **Green–Kubo variance**
  `σ² = ρ(0) + 2·∑' k, ρ(k+1)`
  (`catGreenKubo_tendsto`), `σ² ≥ 0` (`catSigmaSq_nonneg`), and one has a linear variance bound
  `Var(Sₙ) ≤ B·n` (`catVariance_le`).
* **(B) Chebyshev concentration.**  From the linear variance bound, the empirical average
  `Sₙ/n` concentrates around the space mean `∫ f` at the rate `B / (n·ε²)`
  (`catChebyshev`, `catChebyshev_real`).

The exponential decay `|ρ(k)| ≤ C·θᵏ` is taken as a **hypothesis**; a companion development supplies
it for Fourier-decaying observables.  See e.g. Y. Coudène, *Ergodic Theory and Dynamical Systems*,
or N. Chernov's averaging notes, for the classical Green–Kubo / summable-correlations statements.

## Main results

* `ErgodicTheory.CatMapToral.catAutoCorr` — the autocovariance `ρ(k) = cov[f, f∘Tᵏ]`.
* `ErgodicTheory.CatMapToral.variance_birkhoffSum_collapse` — the Toeplitz collapse
  `Var(Sₙ) = 2·∑_{d<n}(n-d)ρ(d) - n·ρ(0)`.
* `ErgodicTheory.CatMapToral.catVariance_le` — the linear variance bound.
* `ErgodicTheory.CatMapToral.catGreenKubo_tendsto` — `Var(Sₙ)/n → σ²`.
* `ErgodicTheory.CatMapToral.catSigmaSq_nonneg` — `0 ≤ σ²`.
* `ErgodicTheory.CatMapToral.catChebyshev` / `catChebyshev_real` — Chebyshev concentration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The circle carries its Haar probability measure, matching `CatMapToral`. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catGreenKubo :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catGreenKubo :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catGreenKubo :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

local instance : IsProbabilityMeasure (volume : Measure T2) := inferInstance

variable (f : T2 → ℝ) {M : ℝ}

/-! ## The autocovariance -/

/-- The **autocovariance** `ρ(k) = cov[f, f∘Tᵏ]` of the observable `f` under the cat map. -/
def catAutoCorr (f : T2 → ℝ) (k : ℕ) : ℝ :=
  covariance f (fun x => f (catTorus^[k] x)) volume

/-! ## `L²`-membership and stationarity bookkeeping -/

/-- Each shifted observable `f∘Tⁱ` lies in `L²` (bounded on a probability space). -/
lemma catMemLp_comp (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) (i : ℕ) :
    MemLp (fun x => f (catTorus^[i] x)) 2 volume := by
  refine MemLp.of_bound ?_ M (Filter.Eventually.of_forall fun x => ?_)
  · exact (hfm.comp (measurePreserving_catTorus.iterate i).measurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hfb _

/-- Composition with the (measure-preserving) `i`-th iterate leaves covariances invariant. -/
lemma covariance_comp_iterate (g h : T2 → ℝ) (i : ℕ)
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    covariance (fun x => g (catTorus^[i] x)) (fun x => h (catTorus^[i] x)) volume
      = covariance g h volume := by
  have hS := measurePreserving_catTorus.iterate i
  have key := covariance_map (μ := volume) (X := g) (Y := h) (Z := catTorus^[i])
    (by rw [hS.map_eq]; exact hg) (by rw [hS.map_eq]; exact hh) hS.aemeasurable
  rw [hS.map_eq] at key
  exact key.symm

/-- Stationarity, ordered form: for `i ≤ j`, `cov[f∘Tⁱ, f∘Tʲ] = ρ(j-i)`. -/
lemma covariance_terms_le (i j : ℕ) (hij : i ≤ j) (hfm : Measurable f) :
    covariance (fun x => f (catTorus^[i] x)) (fun x => f (catTorus^[j] x)) volume
      = catAutoCorr f (j - i) := by
  have hrw : (fun x => f (catTorus^[j] x))
      = fun x => (fun y => f (catTorus^[j - i] y)) (catTorus^[i] x) := by
    funext x
    have hx : catTorus^[j] x = catTorus^[j - i] (catTorus^[i] x) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [hx]
  rw [hrw, covariance_comp_iterate f (fun y => f (catTorus^[j - i] y)) i
    hfm.aestronglyMeasurable
    (hfm.comp (measurePreserving_catTorus.iterate (j - i)).measurable).aestronglyMeasurable]
  rfl

/-- Stationarity: `cov[f∘Tⁱ, f∘Tʲ] = ρ(|i-j|)` (`Nat.dist`). -/
lemma covariance_terms (i j : ℕ) (hfm : Measurable f) :
    covariance (fun x => f (catTorus^[i] x)) (fun x => f (catTorus^[j] x)) volume
      = catAutoCorr f (Nat.dist i j) := by
  rcases le_total i j with h | h
  · rw [covariance_terms_le f i j h hfm, Nat.dist_eq_sub_of_le h]
  · rw [covariance_comm, covariance_terms_le f j i h hfm, Nat.dist_comm i j,
      Nat.dist_eq_sub_of_le h]

/-! ## Variance of a Birkhoff sum as a double sum, and the Toeplitz collapse -/

/-- The variance of the Birkhoff sum is the double sum of stationary covariances. -/
lemma variance_birkhoffSum (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) (n : ℕ) :
    variance (birkhoffSum catTorus f n) volume
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, catAutoCorr f (Nat.dist i j) := by
  have hmem : ∀ i ∈ Finset.range n, MemLp (fun x => f (catTorus^[i] x)) 2 volume :=
    fun i _ => catMemLp_comp f hfm hfb i
  have hvar := variance_fun_sum' (μ := volume)
    (X := fun i x => f (catTorus^[i] x)) (s := Finset.range n) hmem
  rw [show (birkhoffSum catTorus f n)
    = (fun x => ∑ i ∈ Finset.range n, f (catTorus^[i] x)) from rfl, hvar]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => covariance_terms f i j hfm

/-- **Toeplitz collapse** (abstract): a double sum of a function of the distance collapses to a
single weighted sum, `∑_{i,j<n} h(|i-j|) = 2·∑_{d<n}(n-d)·h(d) - n·h(0)`. -/
lemma sum_sum_dist (h : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, h (Nat.dist i j)
      = 2 * ∑ d ∈ Finset.range n, ((n : ℝ) - (d : ℝ)) * h d - (n : ℝ) * h 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdin : ∀ i ∈ Finset.range n, h (Nat.dist i n) = h (n - i) := by
      intro i hi
      rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt (Finset.mem_range.mp hi))]
    have hdnj : ∀ j ∈ Finset.range n, h (Nat.dist n j) = h (n - j) := by
      intro j hj
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt (Finset.mem_range.mp hj))]
    have hLHS : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), h (Nat.dist i j))
        = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, h (Nat.dist i j))
          + 2 * (∑ i ∈ Finset.range n, h (n - i)) + h 0 := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl hdin, Finset.sum_congr rfl hdnj, Nat.dist_self]
      ring
    have hE2 : ∑ i ∈ Finset.range n, h (n - i)
        = ∑ d ∈ Finset.range n, h d + h n - h 0 := by
      have hrefl : ∑ i ∈ Finset.range n, h (n - i) = ∑ i ∈ Finset.range n, h (i + 1) := by
        rw [← Finset.sum_range_reflect (fun i => h (i + 1)) n]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi; congr 1; omega
      rw [hrefl]
      have h1 := Finset.sum_range_succ' h n
      have h2 := Finset.sum_range_succ h n
      linarith [h1, h2]
    have hE1 : ∑ d ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℝ) - (d : ℝ)) * h d
        = ∑ d ∈ Finset.range n, ((n : ℝ) - (d : ℝ)) * h d + ∑ d ∈ Finset.range n, h d + h n := by
      rw [Finset.sum_range_succ]
      have hlast : (((n + 1 : ℕ) : ℝ) - (n : ℝ)) * h n = h n := by push_cast; ring
      rw [hlast, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      push_cast; ring
    rw [hLHS, ih, hE2, hE1]
    push_cast
    ring

/-- **Toeplitz collapse** for the cat-map variance:
`Var(Sₙ) = 2·∑_{d<n}(n-d)·ρ(d) - n·ρ(0)`. -/
lemma variance_birkhoffSum_collapse (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) (n : ℕ) :
    variance (birkhoffSum catTorus f n) volume
      = 2 * ∑ d ∈ Finset.range n, ((n : ℝ) - (d : ℝ)) * catAutoCorr f d
        - (n : ℝ) * catAutoCorr f 0 := by
  rw [variance_birkhoffSum f hfm hfb n, sum_sum_dist (catAutoCorr f) n]

/-! ## Summability from geometric decay -/

/-- The autocovariances are summable (comparison to a geometric series). -/
lemma summable_catAutoCorr {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hdecay : ∀ k, |catAutoCorr f k| ≤ C * θ ^ k) :
    Summable (fun d => catAutoCorr f d) := by
  have hgeo : Summable (fun d : ℕ => C * θ ^ d) :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left C
  exact (Summable.of_nonneg_of_le (fun d => abs_nonneg _) hdecay hgeo).of_abs

/-- The `d`-weighted autocovariances are summable (comparison to `∑ d·θᵈ`). -/
lemma summable_nat_mul_catAutoCorr {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hdecay : ∀ k, |catAutoCorr f k| ≤ C * θ ^ k) :
    Summable (fun d : ℕ => (d : ℝ) * catAutoCorr f d) := by
  have hθabs : ‖θ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hθ0]; exact hθ1
  have hgeo : Summable (fun d : ℕ => C * ((d : ℝ) * θ ^ d)) :=
    ((hasSum_coe_mul_geometric_of_norm_lt_one hθabs).summable).mul_left C
  refine (Summable.of_nonneg_of_le (fun d => abs_nonneg _) (fun d => ?_) hgeo).of_abs
  rw [abs_mul, Nat.abs_cast]
  calc (d : ℝ) * |catAutoCorr f d| ≤ (d : ℝ) * (C * θ ^ d) := by
        gcongr; exact hdecay d
    _ = C * ((d : ℝ) * θ ^ d) := by ring

/-! ## The linear variance bound -/

/-- **Linear variance bound.**  Geometric decay of correlations gives `Var(Sₙ) ≤ B·n` with the
explicit constant `B = C·(2/(1-θ) + 1)`. -/
lemma catVariance_le (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) {C θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hdecay : ∀ k, |catAutoCorr f k| ≤ C * θ ^ k) (n : ℕ) :
    variance (birkhoffSum catTorus f n) volume ≤ C * (2 / (1 - θ) + 1) * (n : ℝ) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hC0 : 0 ≤ C := by
    have := hdecay 0; rw [pow_zero, mul_one] at this; exact le_trans (abs_nonneg _) this
  have hA : 2 * ∑ d ∈ Finset.range n, ((n : ℝ) - (d : ℝ)) * catAutoCorr f d
      ≤ 2 * ∑ d ∈ Finset.range n, (n : ℝ) * (C * θ ^ d) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Finset.sum_le_sum
    intro d hd
    have hdn : (d : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hd)
    have hnd0 : (0 : ℝ) ≤ (n : ℝ) - (d : ℝ) := by linarith
    have hz : (0 : ℝ) ≤ C * θ ^ d := mul_nonneg hC0 (pow_nonneg hθ0 d)
    calc ((n : ℝ) - (d : ℝ)) * catAutoCorr f d
        ≤ ((n : ℝ) - (d : ℝ)) * (C * θ ^ d) := by
          apply mul_le_mul_of_nonneg_left _ hnd0
          exact le_trans (le_abs_self _) (hdecay d)
      _ ≤ (n : ℝ) * (C * θ ^ d) := by
          apply mul_le_mul_of_nonneg_right _ hz; linarith
  have hB : -((n : ℝ) * catAutoCorr f 0) ≤ (n : ℝ) * C := by
    have hρ0 : -C ≤ catAutoCorr f 0 := by
      have := hdecay 0; rw [pow_zero, mul_one] at this
      exact (abs_le.mp this).1
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n)
      (by linarith : (0 : ℝ) ≤ C + catAutoCorr f 0)]
  have hgeo_sum : ∑ d ∈ Finset.range n, θ ^ d ≤ (1 - θ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hθ0 hθ1]
    exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hθ0 i)
      (summable_geometric_of_lt_one hθ0 hθ1)
  have hcoef : (0 : ℝ) ≤ 2 * (n : ℝ) * C :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hC0
  rw [variance_birkhoffSum_collapse f hfm hfb n]
  calc 2 * ∑ d ∈ Finset.range n, ((n : ℝ) - (d : ℝ)) * catAutoCorr f d
        - (n : ℝ) * catAutoCorr f 0
      ≤ 2 * ∑ d ∈ Finset.range n, (n : ℝ) * (C * θ ^ d) + (n : ℝ) * C := by linarith [hA, hB]
    _ = 2 * (n : ℝ) * C * (∑ d ∈ Finset.range n, θ ^ d) + (n : ℝ) * C := by
        have hs : ∑ d ∈ Finset.range n, (n : ℝ) * (C * θ ^ d)
            = (n : ℝ) * C * ∑ d ∈ Finset.range n, θ ^ d := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
        rw [hs]; ring
    _ ≤ 2 * (n : ℝ) * C * ((1 - θ)⁻¹) + (n : ℝ) * C := by
        have hstep := mul_le_mul_of_nonneg_left hgeo_sum hcoef
        linarith [hstep]
    _ = C * (2 / (1 - θ) + 1) * (n : ℝ) := by rw [div_eq_mul_inv]; ring

/-! ## The Green–Kubo limit -/

/-- The **Green–Kubo variance** `σ² = ρ(0) + 2·∑' k, ρ(k+1)`. -/
def catSigmaSq (f : T2 → ℝ) : ℝ :=
  catAutoCorr f 0 + 2 * ∑' k, catAutoCorr f (k + 1)

/-- The Green–Kubo variance equals `2·∑' d, ρ(d) - ρ(0)`. -/
lemma catSigmaSq_eq (hsum : Summable (fun d => catAutoCorr f d)) :
    catSigmaSq f = 2 * (∑' d, catAutoCorr f d) - catAutoCorr f 0 := by
  simp only [catSigmaSq]
  rw [hsum.tsum_eq_zero_add]
  ring

/-- **Green–Kubo asymptotics.**  Under geometric decay of correlations, the normalized variance
`Var(Sₙ)/n` converges to the Green–Kubo variance `σ²`. -/
theorem catGreenKubo_tendsto (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) {C θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hdecay : ∀ k, |catAutoCorr f k| ≤ C * θ ^ k) :
    Tendsto (fun n => variance (birkhoffSum catTorus f n) volume / (n : ℝ)) atTop
      (𝓝 (catSigmaSq f)) := by
  have hsum1 := summable_catAutoCorr f hθ0 hθ1 hdecay
  have hsum2 := summable_nat_mul_catAutoCorr f hθ0 hθ1 hdecay
  set T : ℝ := ∑' d, catAutoCorr f d with hT
  set tailSum : ℝ := ∑' d : ℕ, (d : ℝ) * catAutoCorr f d with htailSum
  have hA : Tendsto (fun n => ∑ i ∈ Finset.range n, catAutoCorr f i) atTop (𝓝 T) :=
    hsum1.hasSum.tendsto_sum_nat
  have hB : Tendsto (fun n => ∑ i ∈ Finset.range n, (i : ℝ) * catAutoCorr f i) atTop (𝓝 tailSum) :=
    hsum2.hasSum.tendsto_sum_nat
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hg : Tendsto (fun n : ℕ =>
      2 * (∑ i ∈ Finset.range n, catAutoCorr f i)
        - 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, (i : ℝ) * catAutoCorr f i)
        - catAutoCorr f 0) atTop (𝓝 (catSigmaSq f)) := by
    have hlim : (2 * T - 2 * (0 * tailSum) - catAutoCorr f 0) = catSigmaSq f := by
      rw [catSigmaSq_eq f hsum1, ← hT]; ring
    rw [← hlim]
    exact ((hA.const_mul 2).sub ((hInv.mul hB).const_mul 2)).sub_const _
  refine Tendsto.congr' ?_ hg
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [variance_birkhoffSum_collapse f hfm hfb n, eq_div_iff hn0]
  have hsplit : ∑ d ∈ Finset.range n, ((n : ℝ) - (d : ℝ)) * catAutoCorr f d
      = (n : ℝ) * ∑ d ∈ Finset.range n, catAutoCorr f d
        - ∑ d ∈ Finset.range n, (d : ℝ) * catAutoCorr f d := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit]
  field_simp

/-- **Nonnegativity of the Green–Kubo variance.**  `σ²` is a limit of nonnegative variances. -/
lemma catSigmaSq_nonneg (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) {C θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hdecay : ∀ k, |catAutoCorr f k| ≤ C * θ ^ k) :
    0 ≤ catSigmaSq f := by
  refine ge_of_tendsto (catGreenKubo_tendsto f hfm hfb hθ0 hθ1 hdecay) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n _
  exact div_nonneg (variance_nonneg _ _) (by positivity)

/-! ## Chebyshev concentration -/

/-- The Birkhoff sum lies in `L²`. -/
lemma memLp_birkhoffSum (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) (n : ℕ) :
    MemLp (birkhoffSum catTorus f n) 2 volume := by
  rw [show (birkhoffSum catTorus f n)
      = ∑ i ∈ Finset.range n, (fun x => f (catTorus^[i] x)) by
    funext x; simp [birkhoffSum, Finset.sum_apply]]
  exact memLp_finsetSum' (Finset.range n) (fun i _ => catMemLp_comp f hfm hfb i)

/-- The integral of `f∘Tⁱ` is the integral of `f` (measure preservation). -/
lemma integral_comp_iterate (hfm : Measurable f) (i : ℕ) :
    ∫ x, f (catTorus^[i] x) ∂volume = ∫ x, f x ∂volume := by
  have hS := measurePreserving_catTorus.iterate i
  have hae : AEStronglyMeasurable f (Measure.map (catTorus^[i]) volume) := by
    rw [hS.map_eq]; exact hfm.aestronglyMeasurable
  rw [← MeasureTheory.integral_map hS.aemeasurable hae, hS.map_eq]

/-- The mean of the Birkhoff sum is `n·(∫ f)`. -/
lemma integral_birkhoffSum (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) (n : ℕ) :
    ∫ x, birkhoffSum catTorus f n x ∂volume = (n : ℝ) * ∫ x, f x ∂volume := by
  rw [show (birkhoffSum catTorus f n)
    = (fun x => ∑ i ∈ Finset.range n, f (catTorus^[i] x)) from rfl,
    MeasureTheory.integral_finsetSum (Finset.range n)
      (fun i _ => (catMemLp_comp f hfm hfb i).integrable (by norm_num))]
  simp_rw [integral_comp_iterate f hfm]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Chebyshev concentration.**  Given a linear variance bound `Var(Sₙ) ≤ B·n`, the empirical
average `Sₙ/n` deviates from the space mean `∫ f` by at least `ε` with probability at most
`B / (n·ε²)`. -/
theorem catChebyshev (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) {B : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hVar : variance (birkhoffSum catTorus f n) volume ≤ B * (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    volume {x : T2 | ε ≤ |birkhoffSum catTorus f n x / (n : ℝ) - ∫ y, f y ∂volume|}
      ≤ ENNReal.ofReal (B / ((n : ℝ) * ε ^ 2)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set Y := birkhoffSum catTorus f n with hYdef
  set m : ℝ := ∫ y, f y ∂volume with hm
  have hYmem : MemLp Y 2 volume := memLp_birkhoffSum f hfm hfb n
  have hμY : (volume : Measure T2)[Y] = (n : ℝ) * m := integral_birkhoffSum f hfm hfb n
  have hset : {x : T2 | ε ≤ |Y x / (n : ℝ) - m|}
      = {x : T2 | (n : ℝ) * ε ≤ |Y x - (volume : Measure T2)[Y]|} := by
    ext x
    simp only [Set.mem_setOf_eq, hμY]
    rw [show Y x / (n : ℝ) - m = (Y x - (n : ℝ) * m) / (n : ℝ) by field_simp,
      abs_div, abs_of_pos hn0, le_div_iff₀ hn0, mul_comm]
  rw [hset]
  refine (meas_ge_le_variance_div_sq (μ := volume) hYmem (c := (n : ℝ) * ε)
    (by positivity)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hεn : ε ≠ 0 := hε.ne'
  calc variance Y volume / ((n : ℝ) * ε) ^ 2
      ≤ (B * (n : ℝ)) / ((n : ℝ) * ε) ^ 2 := by gcongr
    _ = B / ((n : ℝ) * ε ^ 2) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring

/-- Real-valued Chebyshev concentration (`Measure.real` form). -/
theorem catChebyshev_real (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M) {B : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hVar : variance (birkhoffSum catTorus f n) volume ≤ B * (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    (volume : Measure T2).real
        {x : T2 | ε ≤ |birkhoffSum catTorus f n x / (n : ℝ) - ∫ y, f y ∂volume|}
      ≤ B / ((n : ℝ) * ε ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hBn : 0 ≤ B / ((n : ℝ) * ε ^ 2) := by
    have hVnn : (0 : ℝ) ≤ variance (birkhoffSum catTorus f n) volume := variance_nonneg _ _
    have hBnn : (0 : ℝ) ≤ (n : ℝ) * B := by
      rw [mul_comm]; exact le_trans hVnn hVar
    have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_right hBnn hn0
    positivity
  have hle := catChebyshev f hfm hfb hn hVar hε
  unfold Measure.real
  rw [← ENNReal.toReal_ofReal hBn]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

end ErgodicTheory.CatMapToral
