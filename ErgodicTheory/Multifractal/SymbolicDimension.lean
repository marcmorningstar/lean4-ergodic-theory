/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.UpperSMB
import ErgodicTheory.Multifractal.HausdorffDimension
import ErgodicTheory.Entropy.GeneratorTheorem
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

* `ErgodicTheory.Multifractal.atomOf_coordPartition_eq_cylinder`
* `ErgodicTheory.Multifractal.closedBall_eq_atomOf`
* `ErgodicTheory.Multifractal.ae_tendsto_logMass_div_dyadic`
* `ErgodicTheory.Multifractal.ae_tendsto_logMass_div_continuum`

## References

* L. Barreira, *Dimension and Recurrence in Hyperbolic Dynamics*, Birkhäuser (2008), Ch. 4.
* T. Downarowicz, *Entropy in Dynamical Systems*, Cambridge Univ. Press (2011).
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

namespace ErgodicTheory.Multifractal

open ErgodicTheory.Entropy ErgodicTheory.Krieger

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

/-! ### A5 — the conditional, per-partition entropy = Hausdorff-dimension headline

Feeding the `μ`-a.e. pointwise dimension limit (A3) into the metric-space Billingsley/Frostman
bridge `dimH_eq_of_localDimension_eq` (`ErgodicTheory/Multifractal/HausdorffDimension.lean`) yields the
**symbolic entropy = dimension identity** on the explicit conull carrier set: the Hausdorff
dimension of the full-measure set on which the pointwise dimension exists equals `h / log 2`, with
`h` the Kolmogorov–Sinai entropy of the coordinate partition.

The hypotheses are honest **conditionals**: `hσ : Ergodic shiftMap μ` and `hpos : 0 < h`. Both are
genuinely satisfiable — any non-degenerate Bernoulli (i.i.d.) measure on the full shift is ergodic
shift-invariant with strictly positive entropy — so the result is non-vacuous (the shift is a
*compact* phase space, unlike the non-compact `EuclideanSpace` expanding case). No formalized
Bernoulli instance is claimed here; that witness is the separate later node A7. The dimension base
is `log 2`, fixed by the `PiNat` ultrametric (`dist x y = (1/2) ^ firstDiff x y`); it is never a
free `log β`. -/

/-- **A5 (per-partition entropy = Hausdorff dimension).** For an ergodic shift-invariant probability
measure `μ` on the full shift with *positive* Kolmogorov–Sinai entropy `h` of the coordinate
partition, there is a full-measure carrier set `s` whose Hausdorff dimension is exactly `h / log 2`.

The set `s` is the conull set on which the pointwise dimension exists (from A3,
`ae_tendsto_logMass_div_continuum`); the bridge `dimH_eq_of_localDimension_eq` converts the
everywhere-on-`s` pointwise limit `α := h / log 2 > 0` into `dimH s = α`. -/
theorem dimH_eq_ksEntropyPartition_div_log_two (hσ : Ergodic (shiftMap (α₀ := α₀)) μ)
    (hpos : 0 < ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ)) :
    ∃ s : Set (Shift α₀), μ sᶜ = 0 ∧
      dimH s
        = ENNReal.ofReal (ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ)
          / Real.log 2) := by
  set h : ℝ := ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ) with hh
  set L : ℝ := h / Real.log 2 with hLdef
  -- The conull carrier: where the continuum pointwise dimension exists and equals `L`.
  set s : Set (Shift α₀) :=
    {x | Tendsto (fun r => Real.log (μ.real (Metric.closedBall x r)) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 L)} with hsdef
  refine ⟨s, ?_, ?_⟩
  · -- `s` is conull: the a.e. limit (A3) lands exactly in `s`.
    have hae := ae_tendsto_logMass_div_continuum hσ
    rw [ae_iff] at hae
    rwa [show sᶜ = {x : Shift α₀ | ¬ Tendsto
        (fun r => Real.log (μ.real (Metric.closedBall x r)) / Real.log r)
        (𝓝[>] (0 : ℝ)) (𝓝 L)} from rfl]
  · -- Positivity of `L = h / log 2` packaged as a positive `ℝ≥0`.
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hLpos : 0 < L := by rw [hLdef]; exact div_pos hpos hlog2
    set α : ℝ≥0 := L.toNNReal with hαdef
    have hαpos : 0 < α := by rw [hαdef]; exact Real.toNNReal_pos.mpr hLpos
    have hαL : (α : ℝ) = L := by rw [hαdef, Real.coe_toNNReal L hLpos.le]
    -- Apply the metric bridge with positive exponent `α` on the conull `s`.
    have hbridge := dimH_eq_of_localDimension_eq (μ := μ) (α := α) hαpos
      (s := s) (by
        have hae := ae_tendsto_logMass_div_continuum hσ
        rw [ae_iff] at hae
        rwa [show sᶜ = {x : Shift α₀ | ¬ Tendsto
            (fun r => Real.log (μ.real (Metric.closedBall x r)) / Real.log r)
            (𝓝[>] (0 : ℝ)) (𝓝 L)} from rfl])
      (fun x hx => by rw [hαL]; exact hx)
    rw [hbridge, ← ENNReal.ofReal_coe_nnreal, hαL]

/-! ### A6 — partition independence ⇒ the genuine entropy = dimension headline

The coordinate partition is a **generator** for the shift: its forward-`shiftMap`-saturated
σ-algebra is the whole product σ-algebra. The Kolmogorov–Sinai generator theorem then upgrades A5
to the partition-*independent* identity `h_μ(σ) = ksEntropy = dimension · log 2`. -/

open ErgodicTheory.Entropy MeasurableSpace

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [IsProbabilityMeasure μ] in
/-- The σ-algebra generated by the coordinate partition is the `0`-th coordinate σ-algebra
`comap (eval 0) m_{α₀}`: the cells `{x | x 0 = i}` are exactly the singleton preimages of the `0`-th
projection, and over a finite alphabet a measurable subset of `α₀` is a finite union of singletons,
so the two generated σ-algebras coincide. -/
theorem generatedSigmaAlgebra_coordPartition_eq :
    generatedSigmaAlgebra μ (coordPartition μ)
      = MeasurableSpace.comap (fun x : Shift α₀ => x 0) inferInstance := by
  refine le_antisymm ?_ ?_
  · -- `σ(cells) ≤ comap (eval 0) m`: each cell is a singleton preimage, hence comap-measurable.
    refine generateFrom_le ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨{i}, measurableSet_singleton i, rfl⟩
  · -- `comap (eval 0) m ≤ σ(cells)`: a measurable `s ⊆ α₀` is `⋃ i ∈ s, {i}`, so its preimage is a
    -- finite union of cells.
    rw [comap_eq_generateFrom]
    refine generateFrom_le ?_
    rintro _ ⟨s, _, rfl⟩
    have hpre : (fun x : Shift α₀ => x 0) ⁻¹' s
        = ⋃ i ∈ s, (coordPartition μ).cells i := by
      ext x
      simp only [coordPartition, Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq,
        exists_prop]
      constructor
      · intro hx; exact ⟨x 0, hx, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact hi
    rw [hpre]
    refine Set.Finite.measurableSet_biUnion s.toFinite (fun i _ => ?_)
    exact measurableSet_generateFrom ⟨i, rfl⟩

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [IsProbabilityMeasure μ] in
/-- **A6 generator fact.** The coordinate partition is a generating partition for the shift:
`⨆ n, comap (shiftMap^[n]) σ(coordPartition) = MeasurableSpace.pi`. The pullback of the `0`-th
coordinate σ-algebra along `shiftMap^[n]` is the `n`-th coordinate σ-algebra (since
`(shiftMap^[n] x) 0 = x n`), and the product σ-algebra is, by definition, the supremum of all the
coordinate σ-algebras. -/
theorem coordPartition_isGenerating (_hσmp : MeasurePreserving (shiftMap (α₀ := α₀)) μ μ) :
    IsGenerating μ (shiftMap (α₀ := α₀)) (coordPartition μ) := by
  -- Per-`n` pullback identity: `comap (shiftMap^[n]) σ(P) = comap (eval n) m`.
  have hcoord : ∀ n : ℕ, MeasurableSpace.comap (shiftMap^[n])
      (generatedSigmaAlgebra μ (coordPartition μ))
      = MeasurableSpace.comap (fun x : Shift α₀ => x n) inferInstance := by
    intro n
    rw [generatedSigmaAlgebra_coordPartition_eq, comap_comp]
    congr 1
    funext x
    exact (shiftMap_iterate_apply n x 0).trans (by rw [Nat.zero_add])
  -- Unfold `IsGenerating` and rewrite each pullback; the supremum is `MeasurableSpace.pi = mα`.
  unfold IsGenerating
  simp_rw [hcoord]
  rfl

/-- The coordinate partition reindexed onto `Fin (card α₀)` via `(Fintype.equivFin α₀).symm`. This
is the canonical `Fin`-indexed presentation needed to feed `coordPartition` into the
`Fin n`-indexed Kolmogorov–Sinai generator theorem. -/
def coordPartitionFin (μ : Measure (Shift α₀)) :
    MeasurePartition μ (Fin (Fintype.card α₀)) where
  cells := fun j => (coordPartition μ).cells ((Fintype.equivFin α₀).symm j)
  measurable := fun j => (coordPartition μ).measurable _
  aedisjoint := fun j k hjk =>
    (coordPartition μ).aedisjoint (fun he => hjk ((Fintype.equivFin α₀).symm.injective he))
  cover := by
    rw [← (coordPartition μ).cover]
    exact (Fintype.equivFin α₀).symm.surjective.iUnion_comp (coordPartition μ).cells

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] [IsProbabilityMeasure μ] in
/-- The σ-algebra generated by the reindexed coordinate partition equals that of the original: a
bijective reindexing leaves the *range* of cells unchanged. -/
theorem generatedSigmaAlgebra_coordPartitionFin_eq :
    generatedSigmaAlgebra μ (coordPartitionFin μ)
      = generatedSigmaAlgebra μ (coordPartition μ) := by
  unfold generatedSigmaAlgebra
  congr 1
  rw [coordPartitionFin]
  exact (Fintype.equivFin α₀).symm.surjective.range_comp (coordPartition μ).cells

omit [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀] in
/-- **Reindexing invariance of the partition-relative entropy.** The reindexed coordinate partition
has the same Kolmogorov–Sinai entropy as the original: the iterated-join entropy sequences agree
(`entropy_reindex` along `f ↦ e ∘ f`), and the Fekete limit is determined by that sequence. -/
theorem ksEntropyPartition_coordPartitionFin_eq
    (hσmp : MeasurePreserving (shiftMap (α₀ := α₀)) μ μ) :
    ksEntropyPartition hσmp (coordPartitionFin μ)
      = ksEntropyPartition hσmp (coordPartition μ) := by
  -- The two iterated-join entropy sequences coincide.
  have hseq : ksEntropySeq hσmp (coordPartitionFin μ)
      = ksEntropySeq hσmp (coordPartition μ) := by
    funext n
    rw [ksEntropySeq, ksEntropySeq, ksJoin_cells, ksJoin_cells]
    rw [← entropy_reindex μ (Equiv.piCongrRight (fun _ : Fin n => (Fintype.equivFin α₀).symm))
      (ksJoinCells (coordPartition μ).cells (shiftMap (α₀ := α₀)) n)]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    have hcell : ksJoinCells (coordPartitionFin μ).cells (shiftMap (α₀ := α₀)) n f
        = ksJoinCells (coordPartition μ).cells (shiftMap (α₀ := α₀)) n
            (Equiv.piCongrRight (fun _ : Fin n => (Fintype.equivFin α₀).symm) f) := by
      rw [ksJoinCells_apply, ksJoinCells_apply]
      refine Set.iInter_congr (fun k => ?_)
      simp only [Equiv.piCongrRight_apply, Pi.map_apply]
      rfl
    rw [hcell]
  -- The Fekete limit is determined by the entropy sequence (uniqueness of limits).
  have h1 := tendsto_ksEntropySeq hσmp (coordPartitionFin μ)
  rw [hseq] at h1
  exact tendsto_nhds_unique h1 (tendsto_ksEntropySeq hσmp (coordPartition μ))

/-- **A6 headline — the entropy = Hausdorff-dimension identity.** For an ergodic shift-invariant
probability measure `μ` on the full shift with *positive* Kolmogorov–Sinai entropy, there is a
full-measure carrier set `s` whose Hausdorff dimension equals `h_μ(σ) / log 2`, with `h_μ(σ)` the
**partition-independent** Kolmogorov–Sinai entropy of the system (`ksEntropy`).

This is the genuine `h_μ(σ) = dimension · log 2` identity: the coordinate partition is a generator
(`coordPartition_isGenerating`), so the Kolmogorov–Sinai generator theorem
(`ksEntropy_eq_ksEntropyPartition_of_generating`) identifies the system entropy `ksEntropy` with the
coordinate partition's entropy, which A5 ties to the dimension. The hypotheses (`Ergodic shiftMap`,
positive entropy) are honest conditionals, satisfiable by any non-degenerate Bernoulli measure —
the shift is compact, so the statement is non-vacuous (the Bernoulli witness is the later node A7);
no instance is claimed here. The base `log 2` is fixed by the `PiNat` ultrametric. -/
theorem dimH_eq_ksEntropy_div_log_two (hσ : Ergodic (shiftMap (α₀ := α₀)) μ)
    (hpos : 0 < ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ)) :
    ∃ s : Set (Shift α₀), μ sᶜ = 0 ∧
      dimH s
        = ENNReal.ofReal ((ErgodicTheory.Entropy.ksEntropy hσ.toMeasurePreserving).toReal
          / Real.log 2) := by
  -- The generator theorem on the `Fin`-reindexed coordinate partition: `ksEntropy = h(P, σ)`.
  have hgenFin : IsGenerating μ (shiftMap (α₀ := α₀)) (coordPartitionFin μ) := by
    unfold IsGenerating
    rw [generatedSigmaAlgebra_coordPartitionFin_eq]
    exact coordPartition_isGenerating hσ.toMeasurePreserving
  have hred := ksEntropy_eq_ksEntropyPartition_of_generating hσ.toMeasurePreserving
    (coordPartitionFin μ) hgenFin
  -- `(ksEntropy).toReal = h(coordPartition, σ)` via the reindexing equality and `EReal.toReal_coe`.
  have htoReal : (ErgodicTheory.Entropy.ksEntropy hσ.toMeasurePreserving).toReal
      = ksEntropyPartition hσ.toMeasurePreserving (coordPartition μ) := by
    rw [hred, EReal.toReal_coe, ksEntropyPartition_coordPartitionFin_eq hσ.toMeasurePreserving]
  rw [htoReal]
  exact dimH_eq_ksEntropyPartition_div_log_two hσ hpos

end ErgodicTheory.Multifractal
