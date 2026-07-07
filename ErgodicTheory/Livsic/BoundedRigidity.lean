/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.ContinuousRigidity
import ErgodicTheory.Livsic.ShiftMetric
import ErgodicTheory.Multifractal.SymbolicDimensionBernoulli
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Measurable-Livšic rigidity: the bounded-transfer-function tier

This file is the **bounded-measurable tier** of the Livšic rigidity programme (issue #29), the
middle rung of the three-tier structure recorded in `ErgodicTheory.Livsic.ContinuousRigidity`:

1. **Continuous tier** (`ErgodicTheory.Livsic.ContinuousRigidity`). `u` continuous, `μ` fully
   supported ⇒ the a.e. cohomological equation upgrades to an *everywhere* equation and the trivial
   telescoping direction finishes.
2. **Bounded-measurable tier (this file).** `u` merely *measurable* but **bounded**. The everywhere
   upgrade is unavailable, so we run a periodic-orbit shadowing argument on the cylinders of the
   full shift. The endpoint difference `u (T^[N] x) − u x` of the a.e. telescoped Birkhoff sum is
   controlled *uniformly in `N`* precisely because `u` is bounded — this is what makes the tier work
   and is exactly where unboundedness would break it.
3. **Unbounded-measurable tier — deliberately deferred.** For genuinely unbounded measurable `u` the
   uniform endpoint control fails; the theorem becomes the classical Livšic *regularity* theorem
   (Katok–Hasselblatt, Theorem 19.2.4), whose proof needs a Lusin-continuity/regularity argument.
   Left as a follow-up issue.

## The argument (bounded `u`)

Let `T` preserve a probability measure `μ`, let `p` be `n`-periodic (`T^[n] p = p`) and set
`c := birkhoffSum T φ n p`. Suppose `φ = u ∘ T − u` `μ`-a.e. with `|u| ≤ M`. For each `m`, the
depth-`n*m` cylinder `D m` around `p` has **positive** measure (full-support alphabet), and on it
the Birkhoff sum shadows that of `p` up to a **uniform** additive constant `B`:
`|birkhoffSum T φ (n*m) x − birkhoffSum T φ (n*m) p| ≤ B` for `x ∈ D m`. Then:

1. **Periodicity:** `birkhoffSum T φ (n*m) p = m • c` (`birkhoffSum_periodic_eq_nsmul`).
2. **Telescoping a.e.:** for a.e. `x`, `birkhoffSum T φ N x = u (T^[N] x) − u x` for all `N`
   (`ae_birkhoffSum_eq_endpoint`); with `|u| ≤ M` this is bounded by `2M` uniformly in `N`.
3. **Pick a witness:** `D m` has positive measure, so it meets the full-measure telescoping set;
   pick `x ∈ D m` there. Then `|m • c| ≤ B + 2M`, a bound **independent of `m`**. As `c ≠ 0` forces
   `m·|c| → ∞`, we conclude `c = 0`.

The abstract core `vanishingPeriodicSum_of_bounded_shadowing` is proved for a general
measure-preserving `T` on any probability space; the shift-specific inputs are the two lemmas
`bern_cylinder_pos` (Bernoulli cylinders are charged) and `birkhoffSum_shadowing_bound` (a Hölder
observable shadows along a cylinder with a constant independent of the depth), assembled into the
headline `hasVanishingPeriodicSums_of_bounded_aeCoboundary` for the full shift.

## Main results

* `birkhoffSum_periodic_eq_nsmul` — the periodic Birkhoff sum is `m` copies of one period.
* `ae_birkhoffSum_eq_endpoint` — a.e. telescoping of the coboundary to the endpoint difference.
* `vanishingPeriodicSum_of_bounded_shadowing` — the abstract bounded-`u` rigidity core.
* `bern_cylinder_pos` — full-support Bernoulli measure charges every cylinder.
* `birkhoffSum_shadowing_bound` — depth-independent Hölder shadowing along a cylinder.
* `hasVanishingPeriodicSums_of_bounded_aeCoboundary` — the bounded-tier Livšic rigidity theorem for
  the full shift with a fully supported Bernoulli measure.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.4.
* A. Wilkinson, *The cohomological equation for partially hyperbolic diffeomorphisms*, Astérisque
  (2013), §2.
-/

open MeasureTheory Filter Function Set
open scoped Topology NNReal

namespace ErgodicTheory.Livsic

open ErgodicTheory.Multifractal

/-! ### Step 1 — the Birkhoff sum around a periodic orbit is `m` copies of one period -/

section Abstract

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- **Periodic Birkhoff sum.** If `p` is `n`-periodic then the depth-`n*m` Birkhoff sum at `p` is
`m` copies of the single-period sum `birkhoffSum T φ n p`. Induction on `m` via `birkhoffSum_add`,
using `T^[n*m] p = p`. -/
theorem birkhoffSum_periodic_eq_nsmul {T : X → X} (φ : X → ℝ) {n : ℕ} {p : X}
    (hp : IsPeriodicPt T n p) (m : ℕ) :
    birkhoffSum T φ (n * m) p = m • birkhoffSum T φ n p := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hfix : T^[n * k] p = p := (hp.mul_const k).eq
    rw [Nat.mul_succ, birkhoffSum_add, ih, hfix, succ_nsmul]

/-! ### Step 2 — a.e. telescoping of the coboundary -/

/-- **A.e. telescoping.** If `T` preserves `μ` and `φ = u ∘ T − u` `μ`-a.e., then for `μ`-a.e. `x`
the Birkhoff sums of `φ` telescope to the endpoint difference `u (T^[N] x) − u x` *for every* `N`
simultaneously. The a.e. equation is pulled back along each iterate `T^[k]` (which preserves `μ`),
`ae_all_iff` gathers the countably many `k`, and `Finset.sum_range_sub` telescopes. -/
theorem ae_birkhoffSum_eq_endpoint {T : X → X} {μ : Measure X} {φ u : X → ℝ}
    (hmp : MeasurePreserving T μ μ) (hcob : φ =ᵐ[μ] fun x => u (T x) - u x) :
    ∀ᵐ x ∂μ, ∀ N : ℕ, birkhoffSum T φ N x = u (T^[N] x) - u x := by
  -- Pull `hcob` back along every iterate `T^[k]`.
  have hstep : ∀ k : ℕ, ∀ᵐ x ∂μ,
      φ (T^[k] x) = u (T^[k + 1] x) - u (T^[k] x) := by
    intro k
    have hk : (fun x => φ (T^[k] x)) =ᵐ[μ] fun x => u (T (T^[k] x)) - u (T^[k] x) :=
      (hmp.iterate k).quasiMeasurePreserving.ae_eq hcob
    filter_upwards [hk] with x hx
    rw [hx, Function.iterate_succ_apply']
  rw [← ae_all_iff] at hstep
  filter_upwards [hstep] with x hx N
  -- Telescope `∑_{k<N} (F (k+1) − F k) = F N − F 0`, `F k = u (T^[k] x)`.
  have : birkhoffSum T φ N x
      = ∑ k ∈ Finset.range N, (u (T^[k + 1] x) - u (T^[k] x)) := by
    simp only [birkhoffSum]
    exact Finset.sum_congr rfl fun k _ => hx k
  rw [this, Finset.sum_range_sub (fun k => u (T^[k] x)) N]
  simp

/-! ### Step 3 — the abstract bounded-`u` rigidity core -/

/-- **Bounded-`u` measurable Livšic rigidity (abstract core).**

Hypotheses:
* `hmp : MeasurePreserving T μ μ` with `μ` a probability measure;
* `hp : IsPeriodicPt T n p`;
* `hcob : φ =ᵐ[μ] (u ∘ T − u)` — a measurable a.e. coboundary;
* `hbdd : ∀ x, |u x| ≤ M` — the transfer function is **bounded**;
* `hDpos : ∀ m, μ (D m) ≠ 0` and
  `hshadow : ∀ m, ∀ x ∈ D m, |birkhoffSum T φ (n*m) x − birkhoffSum T φ (n*m) p| ≤ B`
  — a per-`m` positive-measure shadowing set with a **uniform** additive constant `B`.

Conclusion: `birkhoffSum T φ n p = 0`.

This is the whole logical content of the measurable rigidity theorem in the bounded regime. The
uniformity of `B` and `2M` in `m` is exactly the place where unboundedness of `u` would break the
argument. -/
theorem vanishingPeriodicSum_of_bounded_shadowing
    {T : X → X} {μ : Measure X} [IsProbabilityMeasure μ] {φ u : X → ℝ}
    {n : ℕ} {p : X} {M B : ℝ} {D : ℕ → Set X}
    (hmp : MeasurePreserving T μ μ) (hp : IsPeriodicPt T n p)
    (hcob : φ =ᵐ[μ] fun x => u (T x) - u x) (hbdd : ∀ x, |u x| ≤ M)
    (hDpos : ∀ m, μ (D m) ≠ 0)
    (hshadow : ∀ m, ∀ x ∈ D m,
      |birkhoffSum T φ (n * m) x - birkhoffSum T φ (n * m) p| ≤ B) :
    birkhoffSum T φ n p = 0 := by
  set c := birkhoffSum T φ n p with hc
  -- The full-measure telescoping set.
  have htel := ae_birkhoffSum_eq_endpoint hmp hcob
  -- For every `m`, produce a witness `x ∈ D m` on which telescoping holds.
  have key : ∀ m : ℕ, |(m : ℝ) * c| ≤ B + 2 * M := by
    intro m
    -- `D m` meets the co-null telescoping set (else `D m` would be null).
    obtain ⟨x, hxD, hxtel⟩ :
        ∃ x, x ∈ D m ∧ ∀ N, birkhoffSum T φ N x = u (T^[N] x) - u x := by
      by_contra h
      have hsub : D m ⊆ {x | ¬ ∀ N, birkhoffSum T φ N x = u (T^[N] x) - u x} :=
        fun x hx hP => h ⟨x, hx, hP⟩
      exact hDpos m (measure_mono_null hsub (ae_iff.1 htel))
    -- Bound the endpoint difference by `2M`.
    have hxbound : |birkhoffSum T φ (n * m) x| ≤ 2 * M := by
      rw [hxtel (n * m)]
      have h1 := abs_le.1 (hbdd (T^[n * m] x))
      have h2 := abs_le.1 (hbdd x)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    -- Shadowing: `birkhoffSum φ (nm) p` is within `B` of the bounded quantity.
    have hsh := hshadow m x hxD
    have hpsum : birkhoffSum T φ (n * m) p = (m : ℝ) * c := by
      rw [birkhoffSum_periodic_eq_nsmul φ hp m, nsmul_eq_mul]
    -- Combine: `|m·c| = |bs p| ≤ |bs x| + |bs p − bs x| ≤ 2M + B`.
    have hsh' : |birkhoffSum T φ (n * m) p - birkhoffSum T φ (n * m) x| ≤ B := by
      rw [abs_sub_comm]; exact hsh
    have hbp : |birkhoffSum T φ (n * m) p| ≤ 2 * M + B := by
      have htri := abs_sub_abs_le_abs_sub
        (birkhoffSum T φ (n * m) p) (birkhoffSum T φ (n * m) x)
      linarith
    calc |(m : ℝ) * c| = |birkhoffSum T φ (n * m) p| := by rw [hpsum]
      _ ≤ 2 * M + B := hbp
      _ = B + 2 * M := by ring
  -- If `c ≠ 0`, `m·|c|` is unbounded, contradicting `key`.
  by_contra hcne
  have hcpos : 0 < |c| := abs_pos.2 hcne
  obtain ⟨m, hm⟩ := exists_nat_gt ((B + 2 * M) / |c|)
  have hmc : (B + 2 * M) < (m : ℝ) * |c| := by
    rw [div_lt_iff₀ hcpos] at hm; linarith
  have := key m
  rw [abs_mul, Nat.abs_cast] at this
  linarith

end Abstract

/-! ### Shift instantiation, part 1 — cylinder positivity -/

section CylinderPositivity

variable {α₀ : Type*} [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- **Cylinder positivity.** The depth-`k` cylinder `{x | ∀ i < k, x i = p i}` around `p` has
positive `bern ν`-mass when `ν` is fully supported (charges every symbol, `ν {a} ≠ 0`). The cylinder
is the measurable box `Set.pi (range k) (fun i => {p i})`, evaluated by `Measure.infinitePi_pi` to
the finite product `∏_{i<k} ν {p i}` of nonzero single-symbol masses, which is nonzero since `ℝ≥0∞`
has no zero divisors. -/
theorem bern_cylinder_pos (ν : Measure α₀) [IsProbabilityMeasure ν]
    (hν : ∀ a : α₀, ν {a} ≠ 0) (p : ∀ _ : ℕ, α₀) (k : ℕ) :
    bern ν {x : ∀ _ : ℕ, α₀ | ∀ i < k, x i = p i} ≠ 0 := by
  have hbox : {x : Shift α₀ | ∀ i < k, x i = p i}
      = Set.pi (↑(Finset.range k)) (fun i => {p i}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
      Set.mem_singleton_iff]
  rw [hbox, bern,
    Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (fun i _ => measurableSet_singleton (p i))]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hν (p i))

end CylinderPositivity

/-! ### Shift instantiation, part 2 — depth-independent Hölder shadowing -/

section Shadowing

variable {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]

attribute [local instance] PiNat.metricSpace

/-- **Depth-independent Hölder shadowing.** If `φ` is `r`-Hölder (`HolderWith C r φ`, `r > 0`) for
the `PiNat` ultrametric on the full shift, and `x` agrees with `p` on the first `N` coordinates,
then the Birkhoff sums of `φ` at `x` and `p` differ by at most `C · θ / (1 − θ)` with
`θ = (1/2)^r < 1` — a constant **independent of the depth `N`**.

Mechanism: for `i < N`, the shifted points `σ^i x` and `σ^i p` agree on their first `N − i`
coordinates, so `dist (σ^i x) (σ^i p) ≤ (1/2)^(N−i)` (`agree_iff_dist_le`); Hölder turns this into
`|φ(σ^i x) − φ(σ^i p)| ≤ C · θ^(N−i)`; summing over `i < N`, reindexing, and bounding the finite
geometric partial sum by the full geometric series `∑ θ^i = (1−θ)⁻¹` gives the constant. -/
theorem birkhoffSum_shadowing_bound {C r : ℝ≥0} {φ : Shift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr : 0 < r) (p : Shift α₀) (N : ℕ)
    {x : Shift α₀} (hx : ∀ i < N, x i = p i) :
    |birkhoffSum shiftMap φ N x - birkhoffSum shiftMap φ N p|
      ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := by
  set θ : ℝ := (1 / 2 : ℝ) ^ (r : ℝ) with hθdef
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hθpos : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hθlt : θ < 1 := by
    rw [hθdef]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hrpos
  have h1θ : 0 < 1 - θ := by linarith
  -- Per-index Hölder bound on the shifted points.
  have hterm : ∀ i ∈ Finset.range N,
      |φ (shiftMap^[i] x) - φ (shiftMap^[i] p)| ≤ (C : ℝ) * θ ^ (N - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hagree : ∀ j < N - i, (shiftMap^[i] x) j = (shiftMap^[i] p) j := by
      intro j hj
      rw [shiftMap_iterate_apply, shiftMap_iterate_apply]
      exact hx (j + i) (by omega)
    have hdist : dist (shiftMap^[i] x) (shiftMap^[i] p) ≤ (1 / 2 : ℝ) ^ (N - i) :=
      (agree_iff_dist_le (N - i) _ _).1 hagree
    have hpow : ((1 / 2 : ℝ) ^ (N - i)) ^ (r : ℝ) = θ ^ (N - i) := by
      rw [half_pow_rpow, hθdef]
    have hH := hφ.dist_le_of_le hdist
    rw [Real.dist_eq, hpow] at hH
    exact hH
  -- Rewrite the Birkhoff difference as a sum of per-term differences.
  have hbs : birkhoffSum shiftMap φ N x - birkhoffSum shiftMap φ N p
      = ∑ i ∈ Finset.range N, (φ (shiftMap^[i] x) - φ (shiftMap^[i] p)) := by
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
  calc |∑ i ∈ Finset.range N, (φ (shiftMap^[i] x) - φ (shiftMap^[i] p))|
      ≤ ∑ i ∈ Finset.range N, |φ (shiftMap^[i] x) - φ (shiftMap^[i] p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, (C : ℝ) * θ ^ (N - i) := Finset.sum_le_sum hterm
    _ = (C : ℝ) * ∑ i ∈ Finset.range N, θ ^ (N - i) := by rw [Finset.mul_sum]
    _ = (C : ℝ) * (θ * ∑ i ∈ Finset.range N, θ ^ i) := by rw [hreflect, hfac]
    _ ≤ (C : ℝ) * (θ * (1 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgeom hθpos.le) (by positivity)
    _ = (C : ℝ) * θ / (1 - θ) := by ring

end Shadowing

/-! ### Shift instantiation, part 3 — the assembled bounded-tier theorem -/

section Assembly

variable {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

attribute [local instance] PiNat.metricSpace

/-- **Bounded-tier Livšic rigidity for the full shift.** Let `ν` be a fully supported probability
law on the (discrete) alphabet `α₀` (`ν {a} ≠ 0` for every symbol `a`), and give the one-sided full
shift its i.i.d. Bernoulli measure `bern ν`. If `φ` is an `r`-Hölder observable (`r > 0`) that is
`bern ν`-a.e. the coboundary of a **bounded** measurable transfer function `u` (`|u| ≤ M`), then `φ`
has **vanishing periodic sums**: `birkhoffSum shiftMap φ n p = 0` for every `n`-periodic point `p`.

This instantiates the abstract core `vanishingPeriodicSum_of_bounded_shadowing` with
`D m := {x | ∀ i < n*m, x i = p i}`, using `bern_cylinder_pos` for positivity of each cylinder and
`birkhoffSum_shadowing_bound` for the depth-independent shadowing constant. No boundedness on `u`
beyond `|u| ≤ M` and no ergodicity are used; measure preservation of the shift is
`measurePreserving_shiftMap_bern`.

Deviation from the mission's proposed hypotheses: measurability of `u` is *not* required by this
tier (the abstract core never differentiates or integrates `u`, it only uses the pointwise bound and
the a.e. coboundary equation), so that hypothesis is dropped. -/
theorem hasVanishingPeriodicSums_of_bounded_aeCoboundary
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ u : Shift α₀ → ℝ} (hφ : HolderWith C r φ) (hr : 0 < r)
    {M : ℝ} (hu_bdd : ∀ x, |u x| ≤ M)
    (hae : IsAeCoboundaryOf (bern ν) shiftMap φ u) :
    HasVanishingPeriodicSums shiftMap φ := by
  intro n p hp
  have hper : IsPeriodicPt shiftMap n p := hp
  exact vanishingPeriodicSum_of_bounded_shadowing
    (measurePreserving_shiftMap_bern ν) hper hae hu_bdd
    (fun m => bern_cylinder_pos ν hν p (n * m))
    (fun m x hx => birkhoffSum_shadowing_bound hφ hr p (n * m) hx)

end Assembly

end ErgodicTheory.Livsic
