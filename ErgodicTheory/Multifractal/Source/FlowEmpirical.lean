/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.Flow
import ErgodicTheory.Ergodic.Birkhoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-time empirical cell-mass observables of a measure-preserving flow

This file builds the **finite-resolution empirical-mass observable** layer for a
measure-preserving one-parameter flow `φ : ErgodicTheory.MeasurePreservingFlow μ` on a probability
space `(X, μ)`. The central object is the *finite-time empirical cell mass*

`empiricalCellMass φ C T x = T⁻¹ · ∫_0^T 𝟙_C (φ t x) dt`,

a continuous-time Birkhoff average measuring the fraction of the orbit segment of length `T`
through `x` that lies in the cell `C`. This is exactly the dynamical analogue of the
empirical-measure mass `μ_T^x(C)` whose `T → ∞` limit (under ergodicity) recovers the true
mass `μ(C)` — the input to coarse-grained multifractal analysis.

## Main results

* `ErgodicTheory.Multifractal.empiricalCellMass` (def): the finite-time empirical cell mass, a
  continuous-time Birkhoff average. The companion `unitWindow φ C x = ∫_0^1 𝟙_C (φ s x) ds`
  is the single-step (unit-window) observable.

* `ErgodicTheory.Multifractal.integral_empiricalCellMass_eq` (**the non-vacuity anchor**): for
  every finite `T > 0`, the *space average* of the finite-time empirical mass equals the true
  mass, `∫_x empiricalCellMass φ C T x ∂μ = (μ C).toReal`. This proves the scaffolding genuinely
  computes `μ(C)`; the proof is a Fubini swap plus measure-preservation of each time-`t` map.

* `ErgodicTheory.Multifractal.empiricalCellMass_natCast_eq`: at *integer* times the empirical mass
  is the discrete Birkhoff average of the unit-window observable under the time-`1` map,
  `empiricalCellMass φ C N x = birkhoffAverage ℝ (φ 1) (unitWindow φ C) N x`. This reduces the
  continuous-time convergence to the repository's discrete pointwise ergodic theorem.

* `ErgodicTheory.Multifractal.integral_unitWindow_eq`: the unit-window space average equals the true
  mass, `∫_x unitWindow φ C x ∂μ = (μ C).toReal` (same Fubini computation, `T = 1`).

* `ErgodicTheory.Multifractal.tendsto_empiricalCellMass_ae`: under an ergodicity hypothesis on the
  time-`1` map and integrability of the unit window, the integer-time empirical masses converge
  `μ`-a.e. to the true mass `μ.real C`.

## Honest hypotheses

`MeasurePreservingFlow` supplies only *per-time* measurability of `φ t`, **not** joint
`(t, x)`-measurability, so `t ↦ 𝟙_C (φ t x)` is not known integrable. Every statement that
integrates over time therefore carries the precise joint-integrability / interval-integrability
hypothesis it needs (`hjoint`, `hii`, `hint`); none is fabricated from the structure.

`Ergodic (φ 1) μ` is likewise **never derived**: ergodicity of the time-`1` map of a flow can
genuinely fail (e.g. without roof aperiodicity for a suspension), so it is carried as a
hypothesis in the convergence statement.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ErgodicTheory.Multifractal

open ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-! ### N2a — the finite-time empirical cell mass -/

/-- The **finite-time empirical cell mass** of the flow `φ` for the cell `C`, horizon `T`, and
base point `x`: a continuous-time Birkhoff average

`empiricalCellMass φ C T x = T⁻¹ · ∫_0^T 𝟙_C (φ t x) dt`,

the time-averaged fraction of the length-`T` orbit segment through `x` lying in `C`. The
definition requires no hypothesis: `intervalIntegral` of a non-integrable integrand is
junk-valued, which is acceptable for a definition. -/
noncomputable def empiricalCellMass (φ : MeasurePreservingFlow μ) (C : Set X) (T : ℝ)
    (x : X) : ℝ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T, Set.indicator C (fun _ => (1 : ℝ)) (φ t x)

/-- The **unit-window observable** `unitWindow φ C x = ∫_0^1 𝟙_C (φ s x) ds`: the mass
accumulated by the length-`1` orbit segment through `x`. It is the single-step generator whose
discrete Birkhoff average reproduces the integer-time empirical masses. -/
noncomputable def unitWindow (φ : MeasurePreservingFlow μ) (C : Set X) (x : X) : ℝ :=
  ∫ s in (0 : ℝ)..1, Set.indicator C (fun _ => (1 : ℝ)) (φ s x)

/-! ### A shared Fubini computation: the time-`t` inner integral is constant -/

omit [IsProbabilityMeasure μ] in
/-- The cell indicator pulled back along a flow map is the indicator of the preimage:
`𝟙_C (φ t x) = 𝟙_{φ t ⁻¹' C} x`. -/
theorem indicator_flow_apply (φ : MeasurePreservingFlow μ) (C : Set X) (t : ℝ) (x : X) :
    Set.indicator C (fun _ => (1 : ℝ)) (φ t x)
      = Set.indicator (φ t ⁻¹' C) (fun _ => (1 : ℝ)) x :=
  (Set.indicator_comp_right (φ t) (g := fun _ => (1 : ℝ))).symm

omit [IsProbabilityMeasure μ] in
/-- For each time `t`, the *space average* of the cell indicator along the flow is the true
mass: `∫_x 𝟙_C (φ t x) ∂μ = μ.real C`. Uses measure-preservation of `φ t` to identify
`μ.real (φ t ⁻¹' C) = μ.real C`. -/
theorem integral_indicator_flow_eq (φ : MeasurePreservingFlow μ) {C : Set X}
    (hC : MeasurableSet C) (t : ℝ) :
    ∫ x, Set.indicator C (fun _ => (1 : ℝ)) (φ t x) ∂μ = μ.real C := by
  have hpre : MeasurableSet (φ t ⁻¹' C) := (φ.measurable t) hC
  calc
    ∫ x, Set.indicator C (fun _ => (1 : ℝ)) (φ t x) ∂μ
        = ∫ x, Set.indicator (φ t ⁻¹' C) (fun _ => (1 : ℝ)) x ∂μ := by
          simp only [indicator_flow_apply]
      _ = μ.real (φ t ⁻¹' C) := integral_indicator_one hpre
      _ = μ.real C := (φ.measurePreserving t).measureReal_preimage hC.nullMeasurableSet

/-! ### N3a — THE NON-VACUITY ANCHOR -/

/-- **The non-vacuity anchor.** For every finite horizon `T > 0`, the *space average* of the
finite-time empirical cell mass equals the true mass of the cell:

`∫_x empiricalCellMass φ C T x ∂μ = (μ C).toReal`.

This is the campaign's vacuity guard: it certifies that the empirical-mass scaffolding genuinely
computes `μ(C)`, for **every** finite `T`, not merely in a limit.

The proof pulls out `T⁻¹`, swaps the order of integration by Fubini
(`intervalIntegral_integral_swap`, which needs the joint integrability hypothesis `hjoint`),
evaluates the now-inner space integral `∫_x 𝟙_C (φ t x) ∂μ = μ.real C` (constant in `t`, via
measure-preservation), and finishes with `T⁻¹ · (T · μ.real C) = μ.real C`.

The hypothesis `hjoint` is the honest joint-integrability requirement Fubini needs: the
structure `MeasurePreservingFlow` supplies only per-time measurability, so `(t, x) ↦ 𝟙_C(φ t x)`
is **not** known integrable from the structure and must be supplied. -/
theorem integral_empiricalCellMass_eq (φ : MeasurePreservingFlow μ) {C : Set X}
    (hC : MeasurableSet C) {T : ℝ} (hT : 0 < T)
    (hjoint : Integrable
      (Function.uncurry fun t x => Set.indicator C (fun _ => (1 : ℝ)) (φ t x))
      ((volume.restrict (Set.uIoc 0 T)).prod μ)) :
    ∫ x, empiricalCellMass φ C T x ∂μ = (μ C).toReal := by
  have hswap :
      ∫ x, (∫ t in (0 : ℝ)..T, Set.indicator C (fun _ => (1 : ℝ)) (φ t x)) ∂μ
        = ∫ t in (0 : ℝ)..T, μ.real C := by
    rw [← intervalIntegral_integral_swap hjoint]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact integral_indicator_flow_eq φ hC t
  calc
    ∫ x, empiricalCellMass φ C T x ∂μ
        = T⁻¹ * ∫ x, (∫ t in (0 : ℝ)..T, Set.indicator C (fun _ => (1 : ℝ)) (φ t x)) ∂μ := by
          rw [← integral_const_mul]; rfl
      _ = T⁻¹ * ∫ t in (0 : ℝ)..T, μ.real C := by rw [hswap]
      _ = T⁻¹ * (T * μ.real C) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      _ = μ.real C := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hT), one_mul]
      _ = (μ C).toReal := measureReal_def μ C

/-- The unit-window space average equals the true mass: `∫_x unitWindow φ C x ∂μ = (μ C).toReal`.
Same Fubini computation as the non-vacuity anchor, specialized to `T = 1`. -/
theorem integral_unitWindow_eq (φ : MeasurePreservingFlow μ) {C : Set X}
    (hC : MeasurableSet C)
    (hjoint : Integrable
      (Function.uncurry fun s x => Set.indicator C (fun _ => (1 : ℝ)) (φ s x))
      ((volume.restrict (Set.uIoc 0 1)).prod μ)) :
    ∫ x, unitWindow φ C x ∂μ = (μ C).toReal := by
  have hmass : ∫ x, empiricalCellMass φ C 1 x ∂μ = (μ C).toReal :=
    integral_empiricalCellMass_eq φ hC one_pos hjoint
  rw [← hmass]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [empiricalCellMass, unitWindow, inv_one, one_mul]

/-! ### N3b — reduction to the repository's discrete Birkhoff theorem -/

omit [IsProbabilityMeasure μ] in
/-- **The unit-window slice.** For a natural index `k`, the time integral of the cell indicator
over the unit interval `[k, k+1]` equals the unit-window observable evaluated at the `k`-th
iterate of the time-`1` map:

`∫_k^{k+1} 𝟙_C (φ t x) dt = unitWindow φ C ((φ 1)^[k] x)`.

The substitution `t = s + k` (`intervalIntegral.integral_comp_add_right`) shifts the interval to
`[0, 1]`; flow additivity `φ (s + k) = φ s ∘ φ k` and `φ (k) = (φ 1)^[k]` rewrite the
integrand. -/
theorem integral_unit_slice_eq (φ : MeasurePreservingFlow μ) (C : Set X) (k : ℕ) (x : X) :
    (∫ t in (k : ℝ)..(k + 1), Set.indicator C (fun _ => (1 : ℝ)) (φ t x))
      = unitWindow φ C ((φ 1)^[k] x) := by
  have hshift :
      (∫ s in (0 : ℝ)..1, Set.indicator C (fun _ => (1 : ℝ)) (φ (s + (k : ℝ)) x))
        = ∫ t in (0 + (k : ℝ))..(1 + (k : ℝ)), Set.indicator C (fun _ => (1 : ℝ)) (φ t x) :=
    intervalIntegral.integral_comp_add_right
      (fun t => Set.indicator C (fun _ => (1 : ℝ)) (φ t x)) (k : ℝ)
  rw [show (0 : ℝ) + (k : ℝ) = (k : ℝ) by ring, show (1 : ℝ) + (k : ℝ) = (k : ℝ) + 1 by ring]
    at hshift
  rw [← hshift]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  have hadd : φ (s + (k : ℝ)) x = φ s ((φ 1)^[k] x) := by
    rw [φ.apply_add s (k : ℝ) x, φ.natCast_eq_iterate k]
  rw [hadd]

omit [IsProbabilityMeasure μ] in
/-- **Integer-time identity.** At integer horizons the finite-time empirical cell mass is the
discrete Birkhoff average of the unit-window observable under the time-`1` map:

`empiricalCellMass φ C N x = birkhoffAverage ℝ (φ 1) (unitWindow φ C) N x`.

The time integral over `[0, N]` is split into adjacent unit windows
(`intervalIntegral.sum_integral_adjacent_intervals`), each identified with the unit window at
the corresponding iterate (`integral_unit_slice_eq`); the resulting sum is the Birkhoff sum, and
the leading `N⁻¹` makes it the Birkhoff average.

The hypothesis `hii` is the honest per-window interval-integrability requirement (each
`∫_k^{k+1}` must be well-defined for the splitting lemma); it cannot be derived from
`MeasurePreservingFlow`, which gives only per-time measurability. -/
theorem empiricalCellMass_natCast_eq (φ : MeasurePreservingFlow μ) (C : Set X) (N : ℕ) (x : X)
    (hii : ∀ k < N, IntervalIntegrable
      (fun t => Set.indicator C (fun _ => (1 : ℝ)) (φ t x)) volume (k : ℝ) (k + 1)) :
    empiricalCellMass φ C (N : ℝ) x = birkhoffAverage ℝ (φ 1) (unitWindow φ C) N x := by
  have hsplit :
      (∑ k ∈ Finset.range N,
          ∫ t in (k : ℝ)..((k : ℝ) + 1), Set.indicator C (fun _ => (1 : ℝ)) (φ t x))
        = ∫ t in (0 : ℝ)..(N : ℝ), Set.indicator C (fun _ => (1 : ℝ)) (φ t x) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun t => Set.indicator C (fun _ => (1 : ℝ)) (φ t x))
      (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := N)
      (fun k hk => by simpa using hii k hk)
    simpa using h
  have hbirk :
      birkhoffSum (φ 1) (unitWindow φ C) N x
        = ∫ t in (0 : ℝ)..(N : ℝ), Set.indicator C (fun _ => (1 : ℝ)) (φ t x) := by
    rw [birkhoffSum]
    rw [← hsplit]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (integral_unit_slice_eq φ C k x).symm
  rw [empiricalCellMass, birkhoffAverage, smul_eq_mul, ← hbirk]

/-- **Convergence to the true mass.** Under ergodicity of the time-`1` map `φ 1` and
integrability of the unit-window observable, the integer-time empirical cell masses converge
`μ`-a.e. to the true mass `μ.real C`:

`∀ᵐ x, (fun N : ℕ => empiricalCellMass φ C N x) → μ.real C`.

The proof feeds `unitWindow φ C` into the repository's pointwise ergodic theorem
`ErgodicTheory.tendsto_birkhoffAverage_ae_integral`, whose limit `∫ unitWindow φ C ∂μ` equals
`μ.real C` by `integral_unitWindow_eq`, then transports the limit across the integer-time
identity `empiricalCellMass_natCast_eq`.

`Ergodic (φ 1) μ` is a **hypothesis**: it is never derived (it can genuinely fail for a flow
without further structure). The interval-integrability data `hii` is the honest per-window
requirement of the integer-time identity, and `hjoint` is the joint-integrability requirement of
the unit-window average. -/
theorem tendsto_empiricalCellMass_ae (φ : MeasurePreservingFlow μ) {C : Set X}
    (hC : MeasurableSet C) (herg : Ergodic (φ 1) μ)
    (hint : Integrable (unitWindow φ C) μ)
    (hjoint : Integrable
      (Function.uncurry fun s x => Set.indicator C (fun _ => (1 : ℝ)) (φ s x))
      ((volume.restrict (Set.uIoc 0 1)).prod μ))
    (hii : ∀ x : X, ∀ k : ℕ, IntervalIntegrable
      (fun t => Set.indicator C (fun _ => (1 : ℝ)) (φ t x)) volume (k : ℝ) (k + 1)) :
    ∀ᵐ x ∂μ,
      Tendsto (fun N : ℕ => empiricalCellMass φ C (N : ℝ) x) atTop (𝓝 (μ.real C)) := by
  have hmean : ∫ y, unitWindow φ C y ∂μ = μ.real C := by
    rw [integral_unitWindow_eq φ hC hjoint, ← measureReal_def]
  have hbirk := tendsto_birkhoffAverage_ae_integral herg hint
  rw [hmean] at hbirk
  filter_upwards [hbirk] with x hx
  refine hx.congr (fun N => ?_)
  exact (empiricalCellMass_natCast_eq φ C N x (fun k _ => hii x k)).symm

end ErgodicTheory.Multifractal
