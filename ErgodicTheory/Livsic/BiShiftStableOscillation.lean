/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.BiShiftFull
import ErgodicTheory.Livsic.BiShiftMetric
import ErgodicTheory.Livsic.BiShiftProductStructure
import ErgodicTheory.MeasureTheory.LusinContinuousOn

/-!
# The stable-pair oscillation bound for the measurable Livšic transfer

This module supplies the analytic core of the **unbounded** measurable tier of the two-sided Livšic
rigidity theorem (GitHub issue #34, step W3): the **stable-pair essential-oscillation bound** for
the measurable Livšic transfer function on the two-sided Bernoulli shift.

Let `φ` be an `r`-Hölder observable on the bilateral full shift `BiShift α₀` over a finite discrete
alphabet, and let `u` be a merely **measurable** (unbounded) a.e. solution of the cohomological
equation `φ = u ∘ σ̃ − u` for the two-sided Bernoulli measure `bernZ ν`. Splitting the shift space
into `past ⊗ future`, we show that for `bernZ ν`-almost-every pair of points sharing a common future
(two pasts `a₁, a₂` and one future `b`), the transfer function `u` oscillates by at most the
depth-independent Hölder constant

> `|u (a₂, b) − u (a₁, b)| ≤ C · θ / (1 − θ)`,  `θ = (1/2)^r`.

This is the measure-theoretic version of the **stable-holonomy identity** of Katok–Hasselblatt,
*Introduction to the Modern Theory of Dynamical Systems* (CUP 1995), Theorem 19.2.4 (see also
A. Wilkinson, *The cohomological equation for partially hyperbolic diffeomorphisms*, §2): points
on a common stable leaf must carry transfer values differing only by the summed forward shadowing
cost. The classical Hölder-version construction of `u` and its Birkhoff return-density input are
replaced here by

* a **clamp-ready** depth-independent oscillation bound coming purely from the Hölder modulus and
  the geometric contraction of same-future pairs (`birkhoffSum_stable_bound`), and
* a **reverse-Fatou** common-returns argument (`measure_not_frequently_le`) that avoids the Birkhoff
  ergodic theorem entirely: Lusin's theorem (`lusin_continuousOn`) carves a compact set `K` of
  almost full measure on which `u` is continuous, marginal preservation forces the forward orbit of
  an a.e. pair to return to `K` at a common unbounded set of times, and the deterministic
  common-returns lemma (`abs_sub_le_of_common_returns`) then clamps the oscillation.

The `ε → 0` sharpening runs the argument along `ε = 1/(k+1)`; the resulting bound `C·θ/(1−θ)` is
`ε`-independent, so the exceptional set has measure zero.

## Main results

* `birkhoffSum_stable_bound` — same-future Birkhoff shadowing bound, uniform in `N`.
* `stable_pair_osc` — the headline stable-pair oscillation bound (Lusin + reverse Fatou + the two
  deterministic lemmas; no ergodic theorem and no boundedness of `u`).

(The deterministic clamp `abs_sub_le_of_common_returns` — telescoping along orbits + a common
return subsequence to a set of uniform continuity of `u` + geometric contraction forces
`|u y − u x| ≤ Cs`, no measure theory, generic in the map `T` — lives here as the shared public
home; the unstable mirror `ErgodicTheory.Livsic.BiShiftUnstableOscillation` imports and reuses it.
The past ⊗ future product substrate and the reverse-Fatou complement helper
`measure_not_frequently_le` are the public ones of `ErgodicTheory.Livsic.BiShiftProductStructure`.)

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  §19.2, Theorem 19.2.4 (stable-holonomy identity).
* A. Wilkinson, *The cohomological equation for partially hyperbolic diffeomorphisms*, Astérisque
  (2013), §2.
* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.

Issue #34.
-/

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal Real

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

/-! ### Instance checks

`BiShift α₀` over a finite discrete alphabet is a Polish Borel space (a countable product of
compact metrizable factors), so `lusin_continuousOn` applies to `bernZ ν`. -/

section InstanceChecks

attribute [local instance] biShiftMetricSpace

-- Polish: countable product of finite discrete spaces
example : PolishSpace (BiShift (Fin 2)) := inferInstance

-- Borel compatibility for the concrete alphabet
example : BorelSpace (BiShift (Fin 2)) := inferInstance

end InstanceChecks

/-! ### Same-future geometry: distance decay and the Birkhoff shadowing bound -/

section StableGeometry

attribute [local instance] biShiftMetricSpace

variable {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]

/-- Two sequences with the same future contract under forward iteration:
`dist (σ̃^N x) (σ̃^N y) ≤ (1/2)^N`. -/
theorem dist_iterate_le_of_eqOn_future {x y : BiShift α₀}
    (hxy : ∀ j : ℤ, 0 ≤ j → x j = y j) (N : ℕ) :
    dist (biShiftMap^[N] x) (biShiftMap^[N] y) ≤ (1 / 2 : ℝ) ^ N := by
  have hmem : biShiftMap^[N] x ∈ symCyl (biShiftMap^[N] y) N := by
    intro j hj
    rw [biShiftMap_iterate_apply, biShiftMap_iterate_apply]
    exact hxy (j + N) (by omega)
  rw [dist_eq_distZ]
  exact (mem_symCyl_iff_distZ_le _ _ N).1 hmem

/-- **Same-future Birkhoff shadowing bound**, uniform in `N`: for a Hölder `φ` and points with
equal futures, `|S_N φ y − S_N φ x| ≤ C·θ/(1−θ)`, `θ = (1/2)^r`. -/
theorem birkhoffSum_stable_bound {C r : ℝ≥0} {φ : BiShift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr : 0 < r) {x y : BiShift α₀}
    (hxy : ∀ j : ℤ, 0 ≤ j → x j = y j) (N : ℕ) :
    |birkhoffSum biShiftMap φ N y - birkhoffSum biShiftMap φ N x|
      ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := by
  set θ : ℝ := (1 / 2 : ℝ) ^ (r : ℝ) with hθdef
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hθpos : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hθlt : θ < 1 := by rw [hθdef]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hrpos
  have h1θ : 0 < 1 - θ := by linarith
  have hterm : ∀ k ∈ Finset.range N,
      |φ (biShiftMap^[k] y) - φ (biShiftMap^[k] x)| ≤ (C : ℝ) * θ ^ (k + 1) := by
    intro k _
    have hmem : biShiftMap^[k] y ∈ symCyl (biShiftMap^[k] x) (k + 1) := by
      intro j hj
      rw [biShiftMap_iterate_apply, biShiftMap_iterate_apply]
      exact (hxy (j + k) (by omega)).symm
    have hdist : dist (biShiftMap^[k] y) (biShiftMap^[k] x) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
      rw [dist_eq_distZ]
      exact (mem_symCyl_iff_distZ_le _ _ (k + 1)).1 hmem
    have hpow : ((1 / 2 : ℝ) ^ (k + 1)) ^ (r : ℝ) = θ ^ (k + 1) := by rw [half_pow_rpow, hθdef]
    have hH := hφ.dist_le_of_le hdist
    rw [Real.dist_eq, hpow] at hH
    exact hH
  have hbs : birkhoffSum biShiftMap φ N y - birkhoffSum biShiftMap φ N x
      = ∑ k ∈ Finset.range N, (φ (biShiftMap^[k] y) - φ (biShiftMap^[k] x)) := by
    simp only [birkhoffSum, Finset.sum_sub_distrib]
  have hfac : ∑ k ∈ Finset.range N, θ ^ (k + 1) = θ * ∑ k ∈ Finset.range N, θ ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_succ']
  have hgeom : ∑ k ∈ Finset.range N, θ ^ k ≤ (1 - θ)⁻¹ :=
    geomSum_range_le_inv_one_sub hθpos.le hθlt N
  rw [hbs]
  calc |∑ k ∈ Finset.range N, (φ (biShiftMap^[k] y) - φ (biShiftMap^[k] x))|
      ≤ ∑ k ∈ Finset.range N, |φ (biShiftMap^[k] y) - φ (biShiftMap^[k] x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (C : ℝ) * θ ^ (k + 1) := Finset.sum_le_sum hterm
    _ = (C : ℝ) * ∑ k ∈ Finset.range N, θ ^ (k + 1) := by rw [Finset.mul_sum]
    _ = (C : ℝ) * (θ * ∑ k ∈ Finset.range N, θ ^ k) := by rw [hfac]
    _ ≤ (C : ℝ) * (θ * (1 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgeom hθpos.le) (by positivity)
    _ = (C : ℝ) * θ / (1 - θ) := by ring

/-- **Deterministic core.** If the cohomological telescoping holds at `x` and `y`, the Birkhoff
differences are uniformly bounded by `Cs`, the forward orbits contract together, and the pair
returns to a compact `K` (on which `u` is continuous) at a common unbounded set of times, then
`|u y − u x| ≤ Cs`. No measure theory, no boundedness of `u`. Generic in the map `T`.

(This is the single shared public copy of the deterministic core: the unstable mirror
`BiShiftUnstableOscillation` imports this module and reuses it, so both symmetric halves and the
glue module `BiShiftMeasurableRigidity` reference one definition, with no duplication or collision.)
-/
theorem abs_sub_le_of_common_returns
    {T : BiShift α₀ → BiShift α₀} {ψ u : BiShift α₀ → ℝ} {K : Set (BiShift α₀)} {Cs : ℝ}
    (hK : IsCompact K) (huK : ContinuousOn u K) {x y : BiShift α₀}
    (htelx : ∀ N, birkhoffSum T ψ N x = u (T^[N] x) - u x)
    (htely : ∀ N, birkhoffSum T ψ N y = u (T^[N] y) - u y)
    (hsum : ∀ N, |birkhoffSum T ψ N y - birkhoffSum T ψ N x| ≤ Cs)
    (hdist : ∀ N : ℕ, dist (T^[N] x) (T^[N] y) ≤ (1 / 2 : ℝ) ^ N)
    (hfreq : ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ T^[N] x ∈ K ∧ T^[N] y ∈ K) :
    |u y - u x| ≤ Cs := by
  have hlt : ∀ e : ℝ, 0 < e → |u y - u x| < Cs + e := by
    intro e he
    have hUC : UniformContinuousOn u K := hK.uniformContinuousOn_of_continuous huK
    rw [Metric.uniformContinuousOn_iff] at hUC
    obtain ⟨δ, hδ, hUC⟩ := hUC e he
    obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨N, hNge, hxK, hyK⟩ := hfreq N₀
    have hdN : dist (T^[N] x) (T^[N] y) < δ :=
      lt_of_le_of_lt
        (le_trans (hdist N) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hNge)) hN₀
    have hu_close : |u (T^[N] y) - u (T^[N] x)| < e := by
      have h := hUC _ hxK _ hyK hdN
      rw [Real.dist_eq] at h
      rw [abs_sub_comm]
      exact h
    have hkey : u y - u x
        = (u (T^[N] y) - u (T^[N] x)) - (birkhoffSum T ψ N y - birkhoffSum T ψ N x) := by
      have h1 := htelx N
      have h2 := htely N
      linarith
    have hA := abs_lt.1 hu_close
    have hS := abs_le.1 (hsum N)
    rw [hkey, abs_lt]
    constructor <;> linarith [hA.1, hA.2, hS.1, hS.2]
  by_contra hc
  rw [not_le] at hc
  have := hlt (|u y - u x| - Cs) (by linarith)
  linarith

end StableGeometry

/-! ### The measure-level stable oscillation lemma -/

section StableOsc

attribute [local instance] biShiftMetricSpace

variable {α₀ : Type*} [Finite α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
variable (ν : Measure α₀) [IsProbabilityMeasure ν]

/-- **Stable oscillation of the transfer function.** If `φ` is `r`-Hölder and `u` is a measurable
a.e. transfer function for `φ` over `bernZ ν`, then for a.e. stable pair (two pasts, one shared
future) the values of `u` differ by at most `C·θ/(1−θ)`. Lusin + reverse Fatou + the
deterministic common-returns lemma; no ergodic theorem, no boundedness of `u`. -/
theorem stable_pair_osc {C r : ℝ≥0} {φ u : BiShift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr : 0 < r) (hu : Measurable u)
    (hae : IsAeCoboundaryOf (bernZ ν) biShiftMap φ u) :
    ∀ᵐ w ∂(stablePairMeasure ν),
      |u (stableSnd w) - u (stableFst w)|
        ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := by
  classical
  haveI : Fintype α₀ := Fintype.ofFinite α₀
  set Cs : ℝ := (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) with hCs
  set lam : Measure (StablePairs α₀) := stablePairMeasure ν with hlam
  -- measure preservation of the shift and telescoping
  have hmp : MeasurePreserving biShiftMap (bernZ ν) (bernZ ν) := by
    rw [← coe_biShiftEquiv]
    exact measurePreserving_biShiftEquiv_bernZ ν
  have htel := ae_birkhoffSum_eq_endpoint hmp hae
  -- pull telescoping back along the two marginals
  have htel1 : ∀ᵐ w ∂lam, ∀ N,
      birkhoffSum biShiftMap φ N (stableFst w)
        = u (biShiftMap^[N] (stableFst w)) - u (stableFst w) := by
    have hmap := (measurePreserving_stableFst ν).map_eq
    exact ae_of_ae_map (measurePreserving_stableFst ν).measurable.aemeasurable
      (by rw [hmap]; exact htel)
  have htel2 : ∀ᵐ w ∂lam, ∀ N,
      birkhoffSum biShiftMap φ N (stableSnd w)
        = u (biShiftMap^[N] (stableSnd w)) - u (stableSnd w) := by
    have hmap := (measurePreserving_stableSnd ν).map_eq
    exact ae_of_ae_map (measurePreserving_stableSnd ν).measurable.aemeasurable
      (by rw [hmap]; exact htel)
  -- the target set and the per-ε bound
  rw [ae_iff]
  set B : Set (StablePairs α₀) := {w | ¬ |u (stableSnd w) - u (stableFst w)| ≤ Cs} with hB
  have key : ∀ k : ℕ, lam B ≤ 2 * ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro k
    set ε : ℝ≥0∞ := ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ with hε
    have hεne : ε ≠ 0 := by
      rw [hε]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (k + 1))
    -- Lusin compact for u
    obtain ⟨K, hKco, hKmass, hKcont⟩ := lusin_continuousOn (μ := bernZ ν) hu hεne
    have hKmeas : MeasurableSet K := hKco.isClosed.measurableSet
    -- the common-return events
    set A : ℕ → Set (StablePairs α₀) := fun N =>
      {w | biShiftMap^[N] (stableFst w) ∈ K ∧ biShiftMap^[N] (stableSnd w) ∈ K} with hA
    have hAcompl : ∀ N, lam (A N)ᶜ ≤ 2 * ε := by
      intro N
      have hATc : (A N)ᶜ ⊆
          (fun w => biShiftMap^[N] (stableFst w)) ⁻¹' Kᶜ ∪
          (fun w => biShiftMap^[N] (stableSnd w)) ⁻¹' Kᶜ := by
        intro w hw
        rw [Set.mem_compl_iff, hA, Set.mem_setOf_eq, not_and_or] at hw
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hiter : MeasurePreserving (biShiftMap^[N]) (bernZ ν) (bernZ ν) := hmp.iterate N
      have hm1 : lam ((fun w => biShiftMap^[N] (stableFst w)) ⁻¹' Kᶜ) = bernZ ν Kᶜ := by
        have hcomp : MeasurePreserving (fun w => biShiftMap^[N] (stableFst w)) lam (bernZ ν) :=
          hiter.comp (measurePreserving_stableFst ν)
        exact hcomp.measure_preimage hKmeas.compl.nullMeasurableSet
      have hm2 : lam ((fun w => biShiftMap^[N] (stableSnd w)) ⁻¹' Kᶜ) = bernZ ν Kᶜ := by
        have hcomp : MeasurePreserving (fun w => biShiftMap^[N] (stableSnd w)) lam (bernZ ν) :=
          hiter.comp (measurePreserving_stableSnd ν)
        exact hcomp.measure_preimage hKmeas.compl.nullMeasurableSet
      calc lam (A N)ᶜ ≤ lam ((fun w => biShiftMap^[N] (stableFst w)) ⁻¹' Kᶜ)
            + lam ((fun w => biShiftMap^[N] (stableSnd w)) ⁻¹' Kᶜ) :=
            le_trans (measure_mono hATc) (measure_union_le _ _)
        _ = bernZ ν Kᶜ + bernZ ν Kᶜ := by rw [hm1, hm2]
        _ ≤ ε + ε := add_le_add hKmass.le hKmass.le
        _ = 2 * ε := by rw [two_mul]
    -- the non-frequent set
    have hnotfreq := measure_not_frequently_le lam (A := A) hAcompl
    -- deterministic step: telescoping + frequent returns force membership in the good set
    have hdet : ∀ᵐ w ∂lam,
        (∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N) → |u (stableSnd w) - u (stableFst w)| ≤ Cs := by
      filter_upwards [htel1, htel2] with w hw1 hw2 hfreq
      have hfut : ∀ j : ℤ, 0 ≤ j → (stableFst w) j = (stableSnd w) j :=
        fun j hj => stableFst_stableSnd_eq_on_nonneg w j hj
      refine abs_sub_le_of_common_returns hKco hKcont hw1 hw2
        (fun N => birkhoffSum_stable_bound hφ hr hfut N)
        (fun N => dist_iterate_le_of_eqOn_future hfut N)
        (fun N₀ => ?_)
      obtain ⟨N, hN, hw⟩ := hfreq N₀
      exact ⟨N, hN, hw.1, hw.2⟩
    -- combine: B is a.e. contained in the non-frequent set
    have hBsub : lam B ≤ lam {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N} + 0 := by
      rw [add_zero]
      have hincl : B ⊆ {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N}
          ∪ {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
              → |u (stableSnd w) - u (stableFst w)| ≤ Cs)} := by
        intro w hwB
        by_cases hfr : ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N
        · exact Or.inr (fun himp => hwB (himp hfr))
        · exact Or.inl hfr
      have hz : lam {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
          → |u (stableSnd w) - u (stableFst w)| ≤ Cs)} = 0 := by
        rw [← ae_iff] at *
        exact hdet
      calc lam B ≤ lam ({w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N}
            ∪ {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
                → |u (stableSnd w) - u (stableFst w)| ≤ Cs)}) := measure_mono hincl
        _ ≤ lam {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N}
            + lam {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
                → |u (stableSnd w) - u (stableFst w)| ≤ Cs)} := measure_union_le _ _
        _ = lam {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N} := by rw [hz, add_zero]
    rw [add_zero] at hBsub
    exact le_trans hBsub hnotfreq
  -- conclude lam B = 0 from the vanishing sequence of bounds
  by_contra hne
  have hpos : 0 < lam B := pos_iff_ne_zero.mpr hne
  have hfin : lam B ≠ ∞ := measure_ne_top lam B
  -- pick k with 2 * (k+1)⁻¹ < lam B
  have hhalf_pos : lam B / 2 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hne, by norm_num⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hhalf_pos
  have hmono : ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((n : ℕ) : ℝ≥0∞)⁻¹ := by
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)
  have hlt : 2 * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ < lam B := by
    calc 2 * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ 2 * ((n : ℕ) : ℝ≥0∞)⁻¹ := by
          exact mul_le_mul_right hmono 2
      _ < 2 * (lam B / 2) := by
          calc 2 * ((n : ℕ) : ℝ≥0∞)⁻¹ = ((n : ℕ) : ℝ≥0∞)⁻¹ * 2 := mul_comm _ _
            _ < (lam B / 2) * 2 := ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) hn
            _ = 2 * (lam B / 2) := mul_comm _ _
      _ = lam B := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
  exact absurd (key n) (not_le.mpr hlt)

end StableOsc

end ErgodicTheory
