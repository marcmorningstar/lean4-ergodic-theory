/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.BiShiftMetric
import ErgodicTheory.Livsic.BiShiftClosing
import ErgodicTheory.Livsic.BiShiftDenseOrbit
import ErgodicTheory.Livsic.Abstract
import ErgodicTheory.Livsic.ContinuousRigidity
import ErgodicTheory.Livsic.BoundedRigidity
import ErgodicTheory.Multifractal.BernoulliTwoSided

/-!
# The Livšic theorem for the two-sided full shift

This is the two-sided (invertible) finale of the abstract Livšic cohomological rigidity theorem
(GitHub issue #32, tier 1): the headline instance of `ErgodicTheory.isHolderCoboundary_iff`
(Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, Theorem 19.2.1) for
the **two-sided full shift** `biShiftMap` on `BiShift α₀ := ∀ _ : ℤ, α₀`, the bilateral analogue of
the one-sided `ErgodicTheory.Livsic.livsic_fullShift`.

The two-sided full shift carries **no admissibility bookkeeping** — every bi-infinite word is legal
— so all the geometric inputs of the abstract theorem are available unconditionally:

* the metric substrate is the `ℤ`-indexed θ-ultrametric `ErgodicTheory.biShiftMetricSpace`, built
  against the pre-existing product topology so `CompactSpace`/`BorelSpace` are inherited with no
  diamond (the `Sanity` certificates of `ErgodicTheory.Livsic.BiShiftMetric`);
* continuity of the shift is `ErgodicTheory.lipschitzWith_two_biShiftMap`;
* the summed exponential closing property is `ErgodicTheory.expClosing_biShiftMap`, whose per-step
  shadowing cost follows the **two-sided profile** `θ^min(i, n-i)` (small near both ends of the
  central block), giving the closing constant `K = 2/(1 - (1/2)^r)` — *twice* the one-sided one;
* the dense forward orbit is `ErgodicTheory.exists_denseRange_biShiftMap_orbit`.

The measure-theoretic rigidity tiers are stated for the **same** two-sided Bernoulli measure
`ErgodicTheory.Multifractal.bernZ ν` that carries the shift's ergodicity
(`ErgodicTheory.Multifractal.ergodic_biShiftEquiv_bernZ`); no metric/measure diamond arises because
`biShiftMetricSpace` reuses the product topology whose Borel structure is `bernZ`'s domain (again
the `Sanity` certificates).

## Main results

* `livsic_biShift` — the headline equivalence
  `IsHolderCoboundary biShiftMap φ ↔ HasVanishingPeriodicSums biShiftMap φ`, for a general nonempty
  encodable finite discrete alphabet `α₀` under the local `ℤ`-indexed θ-ultrametric.
* `livsic_biShift_fin` — its specialization to the `m`-symbol two-sided full shift
  `BiShift (Fin m)`.
* `bernZ_symCyl_pos` — a fully supported two-sided Bernoulli measure charges every symmetric
  cylinder with **positive** mass.
* `isOpenPosMeasure_bernZ` — hence `bernZ ν` charges every nonempty open set (`IsOpenPosMeasure`).
* `isHolderCoboundary_of_continuous_aeCoboundary_biShift` — continuous-tier rigidity: a
  **continuous** a.e. solution of the cohomological equation (w.r.t. a fully supported `bernZ ν`)
  forces `φ` to be a Hölder coboundary.
* `birkhoffSum_shadowing_bound_biShift` — depth-independent two-sided Hölder shadowing along a
  symmetric cylinder (the right edge limits the radius, so the clean one-sided `(1/2)^(N-i)` decay
  survives).
* `hasVanishingPeriodicSums_of_bounded_aeCoboundary_biShift` /
  `isHolderCoboundary_of_bounded_aeCoboundary_biShift` — bounded-tier rigidity: a **bounded**
  measurable a.e. solution likewise forces `φ` to be a Hölder coboundary.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.1 (existence), §6.4 (Anosov closing), §19.2 (Livšic).
-/

open MeasureTheory Function Set
open scoped NNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

attribute [local instance] biShiftMetricSpace

/-! ### The headline two-sided full-shift Livšic equivalence -/

/-- **Livšic for the two-sided full shift** (Katok–Hasselblatt 19.2.1). Over a nonempty encodable
finite discrete alphabet `α₀`, with the `ℤ`-indexed θ-ultrametric on `BiShift α₀`, a Hölder
observable `φ` (exponent `0 < r ≤ 1`) is a **Hölder coboundary** for the bilateral left shift
**iff** all of its periodic Birkhoff sums vanish.

This instantiates the abstract `isHolderCoboundary_iff`: continuity of the shift is
`lipschitzWith_two_biShiftMap`, compactness is Tychonoff over the finite alphabet (inherited with no
diamond from the product topology), the summed exponential closing property is
`expClosing_biShiftMap` (`δ = 1`, closing constant `K = 2/(1 - (1/2)^r) ≥ 0`, reflecting the
two-sided `θ^min(i, n-i)` shadowing profile), and the dense forward orbit is
`exists_denseRange_biShiftMap_orbit`. -/
theorem livsic_biShift {α₀ : Type*} [Nonempty α₀] [Encodable α₀] [Finite α₀]
    [TopologicalSpace α₀] [DiscreteTopology α₀]
    {C r : ℝ≥0} {φ : BiShift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsHolderCoboundary biShiftMap φ ↔ HasVanishingPeriodicSums biShiftMap φ := by
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr0
  obtain ⟨x₀, hdense⟩ := exists_denseRange_biShiftMap_orbit (α₀ := α₀)
  have hlt1 : (1 / 2 : ℝ) ^ (r : ℝ) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hrpos
  have hden : (0 : ℝ) < 1 - (1 / 2 : ℝ) ^ (r : ℝ) := by linarith
  have hK : (0 : ℝ) ≤ 2 / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) :=
    (div_pos (by norm_num : (0 : ℝ) < 2) hden).le
  exact isHolderCoboundary_iff lipschitzWith_two_biShiftMap.continuous hr0 hr1 hφ
    one_pos hK (expClosing_biShiftMap hrpos) hdense

/-- **Livšic for the `m`-symbol two-sided full shift** (`m ≠ 0`). The specialization of
`livsic_biShift` to `BiShift (Fin m)`: a Hölder `φ` is a Hölder coboundary for the bilateral shift
iff all its periodic Birkhoff sums vanish. -/
theorem livsic_biShift_fin (m : ℕ) [NeZero m] {C r : ℝ≥0} {φ : BiShift (Fin m) → ℝ}
    (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsHolderCoboundary biShiftMap φ ↔ HasVanishingPeriodicSums biShiftMap φ :=
  livsic_biShift hφ hr0 hr1

/-! ### Positivity of the two-sided Bernoulli measure on symmetric cylinders -/

/-- **Symmetric-cylinder positivity.** The symmetric cylinder `symCyl x N` (all sequences agreeing
with `x` on `|j| < N`) has **positive** `bernZ ν`-mass whenever `ν` is fully supported
(`0 < ν {a}` for every symbol `a`). The cylinder is the finite box `Set.pi ↑(Finset.Ioo (-N) N)` of
singletons; `bernZ_pi_eq_prod` evaluates its mass to the finite product `∏ ν {x j}` of nonzero
single-symbol masses, which is nonzero since `ℝ≥0∞` has no zero divisors. -/
theorem bernZ_symCyl_pos {α₀ : Type*} [MeasurableSpace α₀]
    [MeasurableSingletonClass α₀] {ν : Measure α₀} [IsProbabilityMeasure ν]
    (hpos : ∀ a, 0 < ν {a}) (x : BiShift α₀) (N : ℕ) :
    0 < bernZ ν (symCyl x N) := by
  have hbox : symCyl x N = Set.pi (↑(Finset.Ioo (-(N : ℤ)) (N : ℤ))) (fun j => {x j}) := by
    rw [Finset.coe_Ioo]
    ext y
    simp only [symCyl, Set.mem_setOf_eq, Set.mem_pi, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · intro h j hj
      exact h j (by omega)
    · intro h j hj
      exact h j (by omega)
  rw [hbox, bernZ_pi_eq_prod ν (Finset.Ioo (-(N : ℤ)) (N : ℤ)) (fun j => {x j})
      (fun j => measurableSet_singleton (x j)), pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => (hpos (x j)).ne')

/-- **Full support ⇒ open-positive.** A fully supported (`ν {a} ≠ 0` for every symbol `a`) two-sided
Bernoulli measure `bernZ ν` charges every nonempty open set, i.e. it is an `IsOpenPosMeasure`.
Proof: a nonempty open `U` contains a metric ball `ball x ε ⊆ U`; choosing `n` with `(1/2)^n < ε`
makes the
symmetric cylinder `symCyl x n` a subset of that ball (the cylinder ↔ ball dictionary
`mem_symCyl_iff_distZ_le`), and `bernZ_symCyl_pos` charges the cylinder — so `U` inherits positive
mass. -/
theorem isOpenPosMeasure_bernZ {α₀ : Type*} [TopologicalSpace α₀]
    [DiscreteTopology α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀] (ν : Measure α₀)
    [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0) :
    (bernZ ν).IsOpenPosMeasure := by
  refine ⟨fun U hU hUne => ?_⟩
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hcyl_sub : symCyl x n ⊆ U := by
    intro z hz
    refine hball ?_
    rw [Metric.mem_ball]
    calc dist z x = distZ z x := dist_eq_distZ z x
      _ ≤ (1 / 2 : ℝ) ^ n := (mem_symCyl_iff_distZ_le z x n).1 hz
      _ < ε := hn
  have hpos : 0 < bernZ ν (symCyl x n) :=
    bernZ_symCyl_pos (fun a => pos_iff_ne_zero.mpr (hν a)) x n
  exact fun hUzero => hpos.ne' (measure_mono_null hcyl_sub hUzero)

/-! ### Continuous-tier two-sided rigidity -/

/-- **Continuous-tier two-sided rigidity.** Let `ν` be a fully supported probability law on the
finite discrete alphabet. If a Hölder `φ` (`0 < r ≤ 1`) equals the coboundary of a **continuous**
transfer function `u` only `bernZ ν`-almost-everywhere, then `φ` is a genuine Hölder coboundary.
Chain: full support makes `bernZ ν` open-positive (`isOpenPosMeasure_bernZ`), so the a.e. equation
upgrades to vanishing periodic sums (`hasVanishingPeriodicSums_of_continuous_coboundary`), and
`livsic_biShift` promotes that to a Hölder coboundary. -/
theorem isHolderCoboundary_of_continuous_aeCoboundary_biShift
    {α₀ : Type*} [Nonempty α₀] [Encodable α₀] [Finite α₀]
    [TopologicalSpace α₀] [DiscreteTopology α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ u : BiShift α₀ → ℝ} (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hu : Continuous u) (hcob : IsAeCoboundaryOf (bernZ ν) biShiftMap φ u) :
    IsHolderCoboundary biShiftMap φ := by
  haveI := isOpenPosMeasure_bernZ ν hν
  have hvps := hasVanishingPeriodicSums_of_continuous_coboundary
    lipschitzWith_two_biShiftMap.continuous hu (hφ.continuous hr0) hcob
  exact (livsic_biShift hφ hr0 hr1).2 hvps

/-! ### Depth-independent two-sided Hölder shadowing -/

/-- **Depth-independent two-sided Hölder shadowing.** If `φ` is `r`-Hölder (`HolderWith C r φ`,
`r > 0`) for the `ℤ`-indexed θ-ultrametric, and `x` lies in the symmetric cylinder `symCyl p N`
(agrees with `p` on `|j| < N`), then the Birkhoff sums of `φ` at `x` and `p` differ by at most
`C · θ / (1 − θ)` with `θ = (1/2)^r < 1` — a constant **independent of the window `N`**.

Mechanism: for `0 ≤ i < N`, the shifted points `biShiftMap^[i] x` and `biShiftMap^[i] p` agree on
the symmetric window `|j| < N − i` — the **right edge** `i + (N − i) = N` limits the radius, so the
two-sided shadow keeps the clean one-sided `(1/2)^(N−i)` decay. Hölder turns this into
`|φ(σ^i x) − φ(σ^i p)| ≤ C · θ^(N−i)`; summing over `i < N`, reindexing, and bounding the finite
geometric partial sum by `∑ θ^i ≤ (1−θ)⁻¹` gives the constant. -/
theorem birkhoffSum_shadowing_bound_biShift {α₀ : Type*} [TopologicalSpace α₀]
    [DiscreteTopology α₀] {C r : ℝ≥0} {φ : BiShift α₀ → ℝ} (hφ : HolderWith C r φ) (hr : 0 < r)
    (p : BiShift α₀) (N : ℕ) {x : BiShift α₀} (hx : x ∈ symCyl p N) :
    |birkhoffSum biShiftMap φ N x - birkhoffSum biShiftMap φ N p|
      ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := by
  set θ : ℝ := (1 / 2 : ℝ) ^ (r : ℝ) with hθdef
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hθpos : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hθlt : θ < 1 := by rw [hθdef]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hrpos
  have h1θ : 0 < 1 - θ := by linarith
  -- Per-index Hölder bound on the shifted points, via the symmetric-cylinder window.
  have hterm : ∀ i ∈ Finset.range N,
      |φ (biShiftMap^[i] x) - φ (biShiftMap^[i] p)| ≤ (C : ℝ) * θ ^ (N - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hmem : biShiftMap^[i] x ∈ symCyl (biShiftMap^[i] p) (N - i) := by
      intro j hj
      rw [biShiftMap_iterate_apply, biShiftMap_iterate_apply]
      exact hx (j + i) (by omega)
    have hdist : dist (biShiftMap^[i] x) (biShiftMap^[i] p) ≤ (1 / 2 : ℝ) ^ (N - i) := by
      rw [dist_eq_distZ]
      exact (mem_symCyl_iff_distZ_le _ _ (N - i)).1 hmem
    have hpow : ((1 / 2 : ℝ) ^ (N - i)) ^ (r : ℝ) = θ ^ (N - i) := by rw [half_pow_rpow, hθdef]
    have hH := hφ.dist_le_of_le hdist
    rw [Real.dist_eq, hpow] at hH
    exact hH
  -- Rewrite the Birkhoff difference as a sum of per-term differences.
  have hbs : birkhoffSum biShiftMap φ N x - birkhoffSum biShiftMap φ N p
      = ∑ i ∈ Finset.range N, (φ (biShiftMap^[i] x) - φ (biShiftMap^[i] p)) := by
    simp only [birkhoffSum, Finset.sum_sub_distrib]
  -- Reindex the geometric tail and factor out one `θ`.
  have hreflect : ∑ i ∈ Finset.range N, θ ^ (N - i)
      = ∑ i ∈ Finset.range N, θ ^ (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => θ ^ (i + 1)) N]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 1
    omega
  have hfac : ∑ i ∈ Finset.range N, θ ^ (i + 1) = θ * ∑ i ∈ Finset.range N, θ ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ']
  have hgeom : ∑ i ∈ Finset.range N, θ ^ i ≤ (1 - θ)⁻¹ :=
    geomSum_range_le_inv_one_sub hθpos.le hθlt N
  rw [hbs]
  calc |∑ i ∈ Finset.range N, (φ (biShiftMap^[i] x) - φ (biShiftMap^[i] p))|
      ≤ ∑ i ∈ Finset.range N, |φ (biShiftMap^[i] x) - φ (biShiftMap^[i] p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, (C : ℝ) * θ ^ (N - i) := Finset.sum_le_sum hterm
    _ = (C : ℝ) * ∑ i ∈ Finset.range N, θ ^ (N - i) := by rw [Finset.mul_sum]
    _ = (C : ℝ) * (θ * ∑ i ∈ Finset.range N, θ ^ i) := by rw [hreflect, hfac]
    _ ≤ (C : ℝ) * (θ * (1 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgeom hθpos.le) (by positivity)
    _ = (C : ℝ) * θ / (1 - θ) := by ring

/-! ### Bounded-tier two-sided rigidity -/

/-- **Bounded-tier two-sided rigidity (periodic-sum form).** Let `ν` be a fully supported
probability law on the (discrete) alphabet `α₀`, and give the two-sided full shift its i.i.d.
Bernoulli measure `bernZ ν`. If `φ` is an `r`-Hölder observable (`r > 0`) that is `bernZ ν`-a.e. the
coboundary of a **bounded** measurable transfer function `u` (`|u| ≤ M`), then `φ` has **vanishing
periodic sums**.

This instantiates the abstract core `vanishingPeriodicSum_of_bounded_shadowing` with
`D m := symCyl p (n*m)`, using `bernZ_symCyl_pos` for positivity of each symmetric cylinder and
`birkhoffSum_shadowing_bound_biShift` for the depth-independent shadowing constant. Measure
preservation of the shift is `measurePreserving_biShiftEquiv_bernZ` (via `coe_biShiftEquiv`). No
boundedness on `u` beyond `|u| ≤ M`, and no ergodicity, are used. -/
theorem hasVanishingPeriodicSums_of_bounded_aeCoboundary_biShift
    {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]
    [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ u : BiShift α₀ → ℝ} (hφ : HolderWith C r φ) (hr : 0 < r)
    {M : ℝ} (hu_bdd : ∀ x, |u x| ≤ M)
    (hae : IsAeCoboundaryOf (bernZ ν) biShiftMap φ u) :
    HasVanishingPeriodicSums biShiftMap φ := by
  intro n p hp
  have hper : IsPeriodicPt biShiftMap n p := hp
  have hmp : MeasurePreserving biShiftMap (bernZ ν) (bernZ ν) := by
    rw [← coe_biShiftEquiv]
    exact measurePreserving_biShiftEquiv_bernZ ν
  exact vanishingPeriodicSum_of_bounded_shadowing (D := fun m => symCyl p (n * m))
    hmp hper hae hu_bdd
    (fun m => (bernZ_symCyl_pos (fun a => pos_iff_ne_zero.mpr (hν a)) p (n * m)).ne')
    (fun m x hx => birkhoffSum_shadowing_bound_biShift hφ hr p (n * m) hx)

/-- **Bounded-tier two-sided rigidity.** With `ν` fully supported as above, if a Hölder `φ`
(`0 < r ≤ 1`) equals the coboundary of a **bounded** measurable transfer function `u` (`|u| ≤ M`)
only `bernZ ν`-almost-everywhere, then `φ` is a genuine Hölder coboundary. Chain: the bounded a.e.
equation forces vanishing periodic sums via the periodic-orbit shadowing argument
(`hasVanishingPeriodicSums_of_bounded_aeCoboundary_biShift`), and `livsic_biShift` promotes it. -/
theorem isHolderCoboundary_of_bounded_aeCoboundary_biShift
    {α₀ : Type*} [Nonempty α₀] [Encodable α₀] [Finite α₀]
    [TopologicalSpace α₀] [DiscreteTopology α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ u : BiShift α₀ → ℝ} (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    {M : ℝ} (hu_bdd : ∀ x, |u x| ≤ M)
    (hae : IsAeCoboundaryOf (bernZ ν) biShiftMap φ u) :
    IsHolderCoboundary biShiftMap φ := by
  have hvps := hasVanishingPeriodicSums_of_bounded_aeCoboundary_biShift ν hν hφ hr0 hu_bdd hae
  exact (livsic_biShift hφ hr0 hr1).2 hvps

end ErgodicTheory
