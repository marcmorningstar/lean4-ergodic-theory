/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.UpperSMB
import Mathlib.Topology.MetricSpace.PiNat

/-!
# The symbolic side of the entropy–dimension identity on the full shift

For an ergodic shift-invariant probability measure `μ` on the **one-sided full shift**
`Shift α₀ := ∀ _ : ℕ, α₀` over a finite alphabet, equipped with Mathlib's `PiNat` ultrametric
(`dist x y = (1/2) ^ firstDiff x y`), this file builds the *symbolic side* of the
foliation-free analogue of the expanding-Pesin / Ledrappier–Young identity:

the **pointwise dimension exists `μ`-a.e. and equals `h / log 2`**, where `h` is the
Kolmogorov–Sinai entropy of the time-`0` coordinate partition.

The construction proceeds in four nodes.

* **A0 (setup).** The shift map, its measurability, the time-`0` coordinate partition, and the
  registration of `PiNat.metricSpace` as a *local* instance (it is deliberately not a global
  Mathlib instance).
* **A1 (atom = cylinder).** The `n`-step join atom `atomOf` of the coordinate partition equals
  the length-`n` `PiNat` cylinder, hence a closed ball of radius `(1/2) ^ n`. Consequently the
  mass of that ball equals the mass of the atom.
* **A2 (SMB on dyadic radii).** Combining A1 with the unconditional pointwise
  Shannon–McMillan–Breiman theorem (`ae_tendsto_div_infoFun_self`), the dyadic mass quotient
  `log μ.real(B(x,(1/2)^n)) / log ((1/2)^n)` converges `μ`-a.e. to `h / log 2`.
* **A3 (dyadic → continuum).** In the ultrametric `PiNat`, the closed ball is *constant* on each
  dyadic gap `(1/2)^(n+1) ≤ r < (1/2)^n`, so the continuum quotient is squeezed between its two
  dyadic endpoint values. Since `log r → -∞` as `r → 0⁺`, the squeeze closes and the continuum
  limit equals the dyadic one. This is a pure ultrametric sandwich — no covering or doubling theory.

The dimension assembly (A5/A6) and the Bernoulli witness (A7) are separate, later nodes.

## Main results

* `Oseledets.Multifractal.atomOf_coordPartition_eq_cylinder`
* `Oseledets.Multifractal.closedBall_eq_atomOf`
* `Oseledets.Multifractal.ae_tendsto_logMass_div_dyadic`
* `Oseledets.Multifractal.ae_tendsto_logMass_div_continuum`

## References

* L. Barreira, *Dimension and Recurrence in Hyperbolic Dynamics*, Birkhäuser (2008), Ch. 4.
* T. Downarowicz, *Entropy in Dynamical Systems*, Cambridge Univ. Press (2011).
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal

namespace Oseledets.Multifractal

open Oseledets.Entropy Oseledets.Krieger

/-! ### A0 — setup -/

/-- The **one-sided full shift space** over the alphabet `α₀`: bi-infinite-to-the-right sequences
`ℕ → α₀`. We give it the `PiNat` ultrametric as a *local* instance below. -/
abbrev Shift (α₀ : Type*) : Type _ := ∀ _ : ℕ, α₀

variable {α₀ : Type*} [Fintype α₀] [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

-- `PiNat` requires the discrete topology on each coordinate to define its metric; for a constant
-- finite-alphabet shift this is the standard discrete topology, registered locally.
attribute [local instance] PiNat.metricSpace

/-- The **left shift map** on the one-sided full shift: `(shiftMap x) n = x (n + 1)`. -/
def shiftMap : Shift α₀ → Shift α₀ := fun x n => x (n + 1)

omit [Fintype α₀] [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSingletonClass α₀] in
/-- The shift map is measurable: each coordinate of its output is a (measurable) coordinate
projection of its input. -/
theorem measurable_shiftMap : Measurable (shiftMap (α₀ := α₀)) := by
  refine measurable_pi_lambda _ fun n => ?_
  exact measurable_pi_apply (n + 1)

omit [Fintype α₀] [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀] in
/-- The `k`-th iterate of the shift advances every index by `k`: `shiftMap^[k] x n = x (n + k)`. -/
theorem shiftMap_iterate_apply (k : ℕ) (x : Shift α₀) (n : ℕ) :
    (shiftMap^[k] x) n = x (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', shiftMap, ih]
    congr 1
    omega

variable {μ : Measure (Shift α₀)} [IsProbabilityMeasure μ]

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] in
/-- The **time-`0` coordinate partition** of the full shift: the cell at `i` is the clopen
set `{x | x 0 = i}` of sequences starting with the symbol `i`. The cells are pairwise disjoint and
cover the whole space, so they form a genuine measurable partition. -/
def coordPartition (μ : Measure (Shift α₀)) : MeasurePartition μ α₀ where
  cells := fun i => {x | x 0 = i}
  measurable := fun i => by
    have : {x : Shift α₀ | x 0 = i} = (fun x : Shift α₀ => x 0) ⁻¹' {i} := by
      ext x; simp [Set.mem_preimage]
    rw [this]
    exact (measurable_pi_apply 0) (measurableSet_singleton i)
  aedisjoint := by
    intro i j hij
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_left]
    rintro x hx hx'
    rw [Set.mem_setOf_eq] at hx hx'
    exact hij (hx.symm.trans hx')
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact Set.mem_iUnion.mpr ⟨x 0, rfl⟩

/-! ### A1 — the join atom is the cylinder -/

variable (hσmp : MeasurePreserving (shiftMap (α₀ := α₀)) μ μ)

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [IsProbabilityMeasure μ] in
/-- The `k`-th itinerary symbol of `x` (for the coordinate partition) is just the `k`-th coordinate
of `x`. Because the coordinate cells are genuinely disjoint, the least-index selector is *forced*
to pick the coordinate `x k` — the itinerary inequality becomes an equality. -/
theorem itinerary_coordPartition_eq (n : ℕ) (x : Shift α₀) (k : Fin n) :
    itinerary hσmp (coordPartition μ) n x k = x (k : ℕ) := by
  have hspec := itinerary_spec hσmp (coordPartition μ) n x k
  -- `shiftMap^[k] x ∈ {y | y 0 = itinerary x k}`, i.e. `(shiftMap^[k] x) 0 = itinerary x k`.
  simp only [coordPartition, Set.mem_setOf_eq] at hspec
  rw [shiftMap_iterate_apply, Nat.zero_add] at hspec
  exact hspec.symm

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [IsProbabilityMeasure μ] in
/-- Membership in the `k`-th preimage cell of the join atom is just `y k = x k`: indeed the cell is
`{z | z 0 = x k}` (using `itinerary_coordPartition_eq`) and `(shiftMap^[k] y) 0 = y k`. -/
theorem mem_atom_coord_iff (n : ℕ) (x y : Shift α₀) (k : Fin n) :
    y ∈ (shiftMap^[(k : ℕ)]) ⁻¹' (coordPartition μ).cells
        (itinerary hσmp (coordPartition μ) n x k) ↔ y (k : ℕ) = x (k : ℕ) := by
  rw [Set.mem_preimage, itinerary_coordPartition_eq]
  change (shiftMap^[(k : ℕ)]) y 0 = x (k : ℕ) ↔ y (k : ℕ) = x (k : ℕ)
  rw [shiftMap_iterate_apply, Nat.zero_add]

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [IsProbabilityMeasure μ] in
/-- **A1 (atom = cylinder).** The `n`-step join atom of `x` for the coordinate partition is exactly
the length-`n` `PiNat` cylinder around `x`. -/
theorem atomOf_coordPartition_eq_cylinder (n : ℕ) (x : Shift α₀) :
    atomOf hσmp (coordPartition μ) n x = PiNat.cylinder x n := by
  ext y
  rw [atomOf, ksJoin_cells, ksJoinCells_apply, Set.mem_iInter, PiNat.mem_cylinder_iff]
  constructor
  · intro h i hi
    exact (mem_atom_coord_iff hσmp n x y ⟨i, hi⟩).mp (h ⟨i, hi⟩)
  · intro h k
    exact (mem_atom_coord_iff hσmp n x y k).mpr (h (k : ℕ) k.2)

omit [Fintype α₀] [Nonempty α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀] in
/-- The length-`n` cylinder is the closed ball of radius `(1/2)^n`: in the `PiNat` ultrametric,
`y ∈ cylinder x n ↔ dist x y ≤ (1/2)^n`. -/
theorem cylinder_eq_closedBall (n : ℕ) (x : Shift α₀) :
    PiNat.cylinder x n = Metric.closedBall x ((1 / 2 : ℝ) ^ n) := by
  ext y
  rw [Metric.mem_closedBall, PiNat.mem_cylinder_iff_dist_le, dist_comm]

omit [Nonempty α₀] [IsProbabilityMeasure μ] in
/-- **A1 corollary (ball = atom).** The closed ball of dyadic radius `(1/2)^n` is the `n`-step join
atom, so its mass equals the atom mass. -/
theorem closedBall_eq_atomOf (n : ℕ) (x : Shift α₀) :
    Metric.closedBall x ((1 / 2 : ℝ) ^ n) = atomOf hσmp (coordPartition μ) n x := by
  rw [atomOf_coordPartition_eq_cylinder hσmp n x, cylinder_eq_closedBall]

/-! ### A2 — pointwise SMB on dyadic radii -/

omit [Nonempty α₀] [IsProbabilityMeasure μ] in
/-- The dyadic mass quotient is, for `n ≥ 1`, exactly `(infoFunₙ x / n) / log 2`: the numerator
`log μ.real(B(x,(1/2)^n)) = -infoFunₙ(x)` (A1) and the denominator
`log ((1/2)^n) = -n·log 2`. -/
theorem logMass_div_dyadic_eq (n : ℕ) (hn : 1 ≤ n) (x : Shift α₀) :
    Real.log (μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ n))) / Real.log ((1 / 2 : ℝ) ^ n)
      = (infoFun hσmp (coordPartition μ) n x / n) / Real.log 2 := by
  have hlog2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- numerator: `log μ.real(ball) = -infoFunₙ x`.
  have hnum : Real.log (μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ n)))
      = -infoFun hσmp (coordPartition μ) n x := by
    rw [closedBall_eq_atomOf hσmp n x, infoFun, neg_neg, measureReal_def]
  -- denominator: `log ((1/2)^n) = -(n · log 2)`.
  have hden : Real.log ((1 / 2 : ℝ) ^ n) = -((n : ℝ) * Real.log 2) := by
    rw [Real.log_pow, one_div, Real.log_inv]; ring
  rw [hnum, hden, neg_div_neg_eq, div_div]

/-- **A2 (pointwise SMB on dyadic radii).** The dyadic mass quotient
`log μ.real(B(x,(1/2)^n)) / log ((1/2)^n)` converges `μ`-a.e. to `h / log 2`, where `h` is the
Kolmogorov–Sinai entropy of the coordinate partition. -/
theorem ae_tendsto_logMass_div_dyadic (hσ : Ergodic (shiftMap (α₀ := α₀)) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => Real.log (μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ n)))
      / Real.log ((1 / 2 : ℝ) ^ n)) atTop
      (𝓝 (ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ) / Real.log 2)) := by
  -- The unconditional pointwise SMB: `infoFunₙ x / n → h` a.e.
  have hsmb := ae_tendsto_div_infoFun_self hσ (coordPartition μ)
  filter_upwards [hsmb] with x hx
  -- `(infoFunₙ x / n) / log 2 → h / log 2`, and the dyadic quotient agrees eventually.
  have hlim : Tendsto (fun n => (infoFun hσ.toMeasurePreserving (coordPartition μ) n x / n)
      / Real.log 2) atTop (𝓝 (ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ)
        / Real.log 2)) :=
    hx.div_const _
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (logMass_div_dyadic_eq hσ.toMeasurePreserving n hn x).symm

/-! ### A3 — dyadic → continuum interpolation -/

omit [Fintype α₀] [Nonempty α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
  [IsProbabilityMeasure μ] in
/-- **Ball constancy on a dyadic gap.** In the `PiNat` ultrametric every distance lies in
`{0} ∪ {(1/2)^m}`, so a closed ball whose radius `r` lies in the dyadic gap
`(1/2)^M ≤ r < (1/2)^(M-1)` coincides with the dyadic ball `B(x,(1/2)^M)`. -/
theorem closedBall_eq_of_mem_gap {M : ℕ} (hM : 1 ≤ M) {r : ℝ} (x : Shift α₀)
    (hlo : (1 / 2 : ℝ) ^ M ≤ r) (hhi : r < (1 / 2 : ℝ) ^ (M - 1)) :
    Metric.closedBall x r = Metric.closedBall x ((1 / 2 : ℝ) ^ M) := by
  ext y
  simp only [Metric.mem_closedBall]
  constructor
  · -- `dist y x ≤ r < (1/2)^(M-1)` forces `dist y x ≤ (1/2)^M` since `dist` is `0` or `(1/2)^k`.
    intro hxy
    rcases eq_or_ne y x with rfl | hne
    · rw [PiNat.dist_self]; positivity
    rw [PiNat.dist_eq_of_ne hne] at hxy ⊢
    -- `(1/2)^firstDiff ≤ r < (1/2)^(M-1)` ⟹ `firstDiff ≥ M` ⟹ `(1/2)^firstDiff ≤ (1/2)^M`.
    have hfd : M ≤ PiNat.firstDiff y x := by
      by_contra hlt
      rw [not_le] at hlt
      have hle : PiNat.firstDiff y x ≤ M - 1 := by omega
      have : (1 / 2 : ℝ) ^ (M - 1) ≤ (1 / 2 : ℝ) ^ PiNat.firstDiff y x :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
      linarith [hxy.trans_lt hhi]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hfd
  · -- `dist x y ≤ (1/2)^M ≤ r`.
    intro hxy
    exact hxy.trans hlo

/-- The dyadic scale index of a radius `r`: the least `M` with `(1/2)^M ≤ r`, packaged as
`⌈log r / log (1/2)⌉₊`. For `r ∈ (0,1)` it satisfies `(1/2)^M ≤ r < (1/2)^(M-1)`. -/
noncomputable def dyadicIdx (r : ℝ) : ℕ := ⌈Real.log r / Real.log (1 / 2 : ℝ)⌉₊

/-- `log (1/2) = -log 2 < 0`. -/
private theorem log_half_neg : Real.log (1 / 2 : ℝ) < 0 := by
  rw [one_div, Real.log_inv]
  simp [Real.log_pos]

omit [Fintype α₀] [Nonempty α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
  [IsProbabilityMeasure μ] in
/-- For `0 < r < 1`, the dyadic index `M := dyadicIdx r` brackets `r`: `(1/2)^M ≤ r < (1/2)^(M-1)`
and `M ≥ 1`. This is the bracketing that makes the ball constant on the gap. -/
theorem dyadicIdx_spec {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    1 ≤ dyadicIdx r ∧ (1 / 2 : ℝ) ^ dyadicIdx r ≤ r ∧ r < (1 / 2 : ℝ) ^ (dyadicIdx r - 1) := by
  set a : ℝ := Real.log r / Real.log (1 / 2 : ℝ) with ha
  have hlh : Real.log (1 / 2 : ℝ) < 0 := log_half_neg
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have ha_pos : 0 < a := by rw [ha]; exact div_pos_of_neg_of_neg hlogr hlh
  set M : ℕ := dyadicIdx r with hM
  have hM_def : M = ⌈a⌉₊ := rfl
  have hM1 : 1 ≤ M := by
    rw [hM_def]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- `a ≤ M` and `M - 1 < a` (since `M ≥ 1`, `M < a + 1`).
  have hle : a ≤ (M : ℝ) := hM_def ▸ Nat.le_ceil a
  have hlt : (M : ℝ) < a + 1 := hM_def ▸ Nat.ceil_lt_add_one ha_pos.le
  refine ⟨hM1, ?_, ?_⟩
  · -- `a ≤ M` ⟹ `log r / log(1/2) ≤ M` ⟹ `log r ≥ M log(1/2)` ⟹ `(1/2)^M ≤ r`.
    have hstep : (M : ℝ) * Real.log (1 / 2 : ℝ) ≤ Real.log r := by
      rw [ha, div_le_iff_of_neg hlh] at hle
      linarith
    rw [← Real.log_pow] at hstep
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ M := by positivity
    exact (Real.log_le_log_iff hpos hr0).mp hstep
  · -- `M - 1 < a` ⟹ `log r < (M-1) log(1/2)` ⟹ `r < (1/2)^(M-1)`.
    have hMR : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM1, Nat.cast_one]
    have hstep : Real.log r < ((M : ℝ) - 1) * Real.log (1 / 2 : ℝ) := by
      have : ((M : ℝ) - 1) < a := by linarith
      rw [ha, lt_div_iff_of_neg hlh] at this
      linarith
    rw [← hMR, ← Real.log_pow] at hstep
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (M - 1) := by positivity
    exact (Real.log_lt_log_iff hr0 hpos).mp hstep

/-- Monotonicity of `c / t` in `t` over the negatives, for a nonpositive numerator: if
`c ≤ 0` and `t₁ ≤ t₂ < 0` then `c / t₁ ≤ c / t₂`. -/
private theorem div_le_div_of_nonpos_neg_denom {c t₁ t₂ : ℝ} (hc : c ≤ 0) (ht2 : t₂ < 0)
    (ht : t₁ ≤ t₂) : c / t₁ ≤ c / t₂ := by
  have ht1 : t₁ < 0 := lt_of_le_of_lt ht ht2
  rw [div_le_iff_of_neg ht1, div_mul_eq_mul_div, div_le_iff_of_neg ht2]
  exact mul_le_mul_of_nonpos_left ht hc

omit [Fintype α₀] [Nonempty α₀] [MeasurableSingletonClass α₀] in
/-- The continuum mass quotient on a gap, written via the dyadic sequence value at `M`. For
`(1/2)^M ≤ r < (1/2)^(M-1)` the numerator is the dyadic numerator `a(M) ≤ 0` (ball constancy) and
`log r ∈ [-M·log 2, -(M-1)·log 2)`, giving a two-sided bound by the dyadic quotients. -/
theorem logMass_div_continuum_bounds
    (x : Shift α₀) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hM2 : 2 ≤ dyadicIdx r) :
    let D := fun n : ℕ => Real.log (μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ n)))
      / Real.log ((1 / 2 : ℝ) ^ n)
    let M := dyadicIdx r
    D M ≤ Real.log (μ.real (Metric.closedBall x r)) / Real.log r ∧
      Real.log (μ.real (Metric.closedBall x r)) / Real.log r ≤ D M * (M / (M - 1)) := by
  intro D M
  obtain ⟨hM1, hlo, hhi⟩ := dyadicIdx_spec hr0 hr1
  -- ball constancy collapses the numerator to the dyadic one.
  have hball : Metric.closedBall x r = Metric.closedBall x ((1 / 2 : ℝ) ^ M) :=
    closedBall_eq_of_mem_gap hM1 x hlo hhi
  rw [hball]
  set a : ℝ := Real.log (μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ M))) with ha
  -- numerator nonpositivity: mass ≤ 1.
  have hmass_le : μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ M)) ≤ 1 := by
    rw [measureReal_def]
    have h := ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one (μ := μ) (s := Metric.closedBall x ((1 / 2 : ℝ) ^ M)))
    rwa [ENNReal.toReal_one] at h
  have ha_nonpos : a ≤ 0 := Real.log_nonpos measureReal_nonneg hmass_le
  -- denominators.
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogr_neg : Real.log r < 0 := Real.log_neg hr0 hr1
  have hMR : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM1, Nat.cast_one]
  have hMpos : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMm1_pos : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    linarith
  -- the bracketing of `log r`.
  have hlogr_lo : -(M : ℝ) * Real.log 2 ≤ Real.log r := by
    have hh : Real.log ((1 / 2 : ℝ) ^ M) ≤ Real.log r := Real.log_le_log (by positivity) hlo
    rw [Real.log_pow, one_div, Real.log_inv] at hh
    have : (M : ℝ) * -Real.log 2 ≤ Real.log r := hh
    linarith
  have hlogr_hi : Real.log r < -((M : ℝ) - 1) * Real.log 2 := by
    have hh : Real.log r < Real.log ((1 / 2 : ℝ) ^ (M - 1)) := Real.log_lt_log hr0 hhi
    rw [Real.log_pow, hMR, one_div, Real.log_inv] at hh
    have : Real.log r < ((M : ℝ) - 1) * -Real.log 2 := hh
    linarith
  -- rewrite the dyadic sequence values `D M` in closed form.
  have hDM : D M = a / (-(M : ℝ) * Real.log 2) := by
    change Real.log (μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ M)))
        / Real.log ((1 / 2 : ℝ) ^ M) = a / (-(M : ℝ) * Real.log 2)
    rw [← ha, Real.log_pow, one_div, Real.log_inv]; ring_nf
  refine ⟨?_, ?_⟩
  · -- lower bound `D M ≤ a / log r`.
    rw [hDM]
    refine div_le_div_of_nonpos_neg_denom ha_nonpos hlogr_neg ?_
    linarith
  · -- upper bound `a / log r ≤ D M * (M / (M - 1))`.
    have hupper : a / Real.log r ≤ a / (-((M : ℝ) - 1) * Real.log 2) := by
      refine div_le_div_of_nonpos_neg_denom ha_nonpos ?_ hlogr_hi.le
      have : (0 : ℝ) < ((M : ℝ) - 1) * Real.log 2 := mul_pos hMm1_pos hlog2
      linarith
    -- and `a / (-(M-1) log2) = (a / (-(M) log2)) * (M/(M-1)) = D M * (M/(M-1))`.
    have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
    have hMpos0 : (0 : ℝ) < (M : ℝ) := by linarith
    have hMm1ne : (M : ℝ) - 1 ≠ 0 := ne_of_gt hMm1_pos
    have hd1 : -((M : ℝ) - 1) * Real.log 2 ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hMm1ne) hlog2ne
    have hd2 : -(M : ℝ) * Real.log 2 * ((M : ℝ) - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hMpos0)) hlog2ne) hMm1ne
    have heq : a / (-((M : ℝ) - 1) * Real.log 2) = D M * ((M : ℝ) / ((M : ℝ) - 1)) := by
      rw [hDM, div_mul_div_comm, div_eq_div_iff hd1 hd2]
      ring
    rw [heq] at hupper
    exact hupper

/-- The dyadic index tends to infinity as the radius tends to `0` from the right: `r → 0⁺` forces
`log r → -∞`, hence `log r / log (1/2) → +∞`, and `⌈·⌉₊` preserves this. -/
theorem tendsto_dyadicIdx_nhdsGT_zero : Tendsto dyadicIdx (𝓝[>] (0 : ℝ)) atTop := by
  have hlog : Tendsto (fun r : ℝ => Real.log r / Real.log (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) atTop := by
    have h := Real.tendsto_log_nhdsGT_zero
    have hmul := h.atBot_mul_const_of_neg (r := (Real.log (1 / 2 : ℝ))⁻¹)
      (by rw [inv_lt_zero]; exact log_half_neg)
    simp only [← div_eq_mul_inv] at hmul
    exact hmul
  exact tendsto_nat_ceil_atTop.comp hlog

/-- **A3 (dyadic → continuum interpolation).** The continuum pointwise dimension exists `μ`-a.e.:
the mass quotient `log μ.real(B(x,r)) / log r` converges, as `r → 0⁺`, to `h / log 2` where `h` is
the Kolmogorov–Sinai entropy of the coordinate partition. The ultrametric makes the ball constant on
each dyadic gap, so the continuum quotient is squeezed between two dyadic quotients, both of which
converge to `h / log 2` by the dyadic SMB (A2). -/
theorem ae_tendsto_logMass_div_continuum (hσ : Ergodic (shiftMap (α₀ := α₀)) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => Real.log (μ.real (Metric.closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 (ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ)
        / Real.log 2)) := by
  set L : ℝ := ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ) / Real.log 2 with hL
  filter_upwards [ae_tendsto_logMass_div_dyadic hσ] with x hD
  set D := fun n : ℕ => Real.log (μ.real (Metric.closedBall x ((1 / 2 : ℝ) ^ n)))
    / Real.log ((1 / 2 : ℝ) ^ n) with hDdef
  set Q := fun r : ℝ => Real.log (μ.real (Metric.closedBall x r)) / Real.log r with hQdef
  have hidx : Tendsto dyadicIdx (𝓝[>] (0 : ℝ)) atTop := tendsto_dyadicIdx_nhdsGT_zero
  -- lower bounding function `r ↦ D (dyadicIdx r)` tends to `L`.
  have hlow : Tendsto (fun r => D (dyadicIdx r)) (𝓝[>] (0 : ℝ)) (𝓝 L) := hD.comp hidx
  -- upper bounding function `r ↦ D (dyadicIdx r) * (M / (M - 1))` tends to `L * 1 = L`.
  have hratio : Tendsto (fun r => ((dyadicIdx r : ℝ) / ((dyadicIdx r : ℝ) - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hseq : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) - 1)) atTop (𝓝 1) := by
      have := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (-1 : ℝ)
      refine this.congr fun m => ?_
      rw [← sub_eq_add_neg]
    exact hseq.comp hidx
  have hupp : Tendsto (fun r => D (dyadicIdx r) * ((dyadicIdx r : ℝ) / ((dyadicIdx r : ℝ) - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have := hlow.mul hratio
    rwa [mul_one] at this
  -- the eventual two-sided bound region: `0 < r < 1` with `dyadicIdx r ≥ 2`.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < 1 ∧ 2 ≤ dyadicIdx r := by
    have h0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), (0 : ℝ) < r := self_mem_nhdsWithin
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < 1 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 ≤ dyadicIdx r := hidx (eventually_ge_atTop 2)
    filter_upwards [h0, h1, h2] with r hr0 hr1 hr2
    exact ⟨hr0, hr1, hr2⟩
  -- squeeze.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [hev] with r hr
    exact (logMass_div_continuum_bounds x hr.1 hr.2.1 hr.2.2).1
  · filter_upwards [hev] with r hr
    exact (logMass_div_continuum_bounds x hr.1 hr.2.1 hr.2.2).2

end Oseledets.Multifractal
