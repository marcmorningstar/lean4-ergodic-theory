/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.ContinuousRigidity
import ErgodicTheory.Livsic.FullShift
import ErgodicTheory.Multifractal.BernoulliErgodic
import Mathlib.Dynamics.Ergodic.Function

/-!
# Livšic rigidity: the measurable tier (uniqueness and conditional regularity)

This is the **measurable-solution tier** of the full-shift Livšic rigidity programme (issue #34),
building on the continuous tier (`ErgodicTheory.Livsic.ContinuousRigidity`) and the assembled
full-shift theorem (`ErgodicTheory.Livsic.FullShift`).  Two results are proved, both over a fully
supported i.i.d. Bernoulli measure `bern ν` on the one-sided full shift.

## Main results

* `ErgodicTheory.Livsic.aeCoboundary_unique_mod_const` — **uniqueness modulo constants.** Any two
  *measurable* transfer functions solving the same cohomological equation `φ = u ∘ shiftMap − u`
  only `bern ν`-almost-everywhere differ by a `bern ν`-a.e. constant.  This is a direct consequence
  of **ergodicity** of the Bernoulli shift (`ergodic_shiftMap_bern`): the a.e. difference is a.e.
  `shiftMap`-invariant, hence a.e. constant (`Ergodic.ae_eq_const_of_ae_eq_comp₀`).

* `ErgodicTheory.Livsic.measurable_solution_ae_eq_holder` — **conditional regularity.** If a Hölder
  observable `φ` has vanishing periodic sums *and* admits some measurable a.e. transfer function
  `u`, then `u` differs by a `bern ν`-a.e. constant from a genuine **Hölder** transfer function `u₀`
  (the one produced by the substantive backward direction of `livsic_fullShift`).  In other words,
  once vanishing periodic sums are known, every measurable a.e. solution is a.e. the Hölder solution
  up to an additive constant.

## What is *not* proved here (and where it lives instead)

The genuinely hard, **unconditional** measurable Livšic regularity theorem — *"a measurable a.e.
solution of the cohomological equation, with no boundedness or periodic-sum hypothesis, forces the
potential to have vanishing periodic sums (equivalently, to be a Hölder coboundary)"* — is **not**
established in *this file* for unbounded `u`.  For a bounded measurable `u` the periodic-orbit
shadowing argument of `ErgodicTheory.Livsic.BoundedRigidity` discharges it; the unbounded case is
the classical Livšic *regularity* theorem (Katok–Hasselblatt, Theorem 19.2.4), whose proof runs a
Lusin-continuity argument on the **two-sided natural extension** and is genuinely two-sided.  That
tier is **discharged** in `ErgodicTheory.Livsic.MeasurableRigidityFull`
(`hasVanishingPeriodicSums_of_measurable_aeCoboundary` / `livsic_measurable_rigidity`, via the
stable/unstable essential-oscillation bounds, reverse Fatou, and the clamp onto the bounded tier —
no Hölder-version construction).  The `aeCoboundary_unique_mod_const` uniqueness statement here is
one of its two ingredients (the other being the existence/regularity statement for the a.e.
solution), and `measurable_solution_ae_eq_holder` feeds the finale's a.e. identification
`measurable_aeCoboundary_ae_eq_holder`.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.4.
-/

open MeasureTheory Function Filter
open scoped NNReal

attribute [local instance] PiNat.metricSpace

namespace ErgodicTheory.Livsic

open ErgodicTheory.Multifractal

/-! ### Uniqueness of the a.e. transfer function modulo constants -/

section Uniqueness

variable {α₀ : Type*} [MeasurableSpace α₀] {ν : Measure α₀} [IsProbabilityMeasure ν]

/-- **Uniqueness modulo constants for a.e. coboundaries of the Bernoulli shift.** If two measurable
transfer functions `u₁`, `u₂` both solve the same cohomological equation
`φ = u ∘ shiftMap − u` only `bern ν`-almost-everywhere, then `u₁ − u₂` is `bern ν`-a.e. constant.

Proof: subtracting the two a.e. equations makes `u₁ − u₂` a.e. `shiftMap`-invariant
(`(u₁ − u₂) ∘ shiftMap =ᵐ u₁ − u₂`); ergodicity of the Bernoulli shift
(`ergodic_shiftMap_bern`) then forces an a.e.-invariant measurable function to be a.e. constant
(`Ergodic.ae_eq_const_of_ae_eq_comp₀`). -/
theorem aeCoboundary_unique_mod_const {u₁ u₂ : Shift α₀ → ℝ} {φ : Shift α₀ → ℝ}
    (hu₁ : Measurable u₁) (hu₂ : Measurable u₂)
    (h₁ : IsAeCoboundaryOf (bern ν) shiftMap φ u₁)
    (h₂ : IsAeCoboundaryOf (bern ν) shiftMap φ u₂) :
    ∃ c : ℝ, (fun x => u₁ x - u₂ x) =ᵐ[bern ν] fun _ => c := by
  have hinv : (fun x => u₁ x - u₂ x) ∘ shiftMap =ᵐ[bern ν] fun x => u₁ x - u₂ x := by
    filter_upwards [h₁, h₂] with x hx1 hx2
    have e1 : φ x = u₁ (shiftMap x) - u₁ x := hx1
    have e2 : φ x = u₂ (shiftMap x) - u₂ x := hx2
    change u₁ (shiftMap x) - u₂ (shiftMap x) = u₁ x - u₂ x
    linarith
  obtain ⟨c, hc⟩ := (ergodic_shiftMap_bern ν).ae_eq_const_of_ae_eq_comp₀
    (hu₁.sub hu₂).nullMeasurable hinv
  exact ⟨c, hc⟩

end Uniqueness

/-! ### Conditional regularity of a measurable a.e. solution -/

section Regularity

variable {α₀ : Type*} [Nonempty α₀] [Encodable α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [Finite α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
  {ν : Measure α₀} [IsProbabilityMeasure ν]

/-- **Conditional measurable regularity for the full shift.** Suppose the Hölder observable `φ`
(exponent `0 < r ≤ 1`) has vanishing periodic sums and admits *some* measurable transfer function
`u` solving `φ = u ∘ shiftMap − u` only `bern ν`-a.e.  Then there is a genuine **Hölder** transfer
function `u₀` (with `φ = u₀ ∘ shiftMap − u₀` *everywhere*) such that `u − u₀` is `bern ν`-a.e.
constant.

Route: vanishing periodic sums feed the substantive backward direction of `livsic_fullShift` to
produce the Hölder solution `u₀`; being Hölder, `u₀` is continuous hence measurable, and it is an
exact (so a.e.) coboundary of `φ`; the two measurable a.e. solutions `u` and `u₀` then differ by an
a.e. constant by `aeCoboundary_unique_mod_const`. -/
theorem measurable_solution_ae_eq_holder {C r : ℝ≥0} {φ : Shift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hvan : HasVanishingPeriodicSums shiftMap φ)
    {u : Shift α₀ → ℝ} (hu : Measurable u) (hcob : IsAeCoboundaryOf (bern ν) shiftMap φ u) :
    ∃ (u₀ : Shift α₀ → ℝ) (C₀ r₀ : ℝ≥0) (c : ℝ), 0 < r₀ ∧ HolderWith C₀ r₀ u₀ ∧
      (∀ x, φ x = u₀ (shiftMap x) - u₀ x) ∧ (fun x => u x - u₀ x) =ᵐ[bern ν] fun _ => c := by
  obtain ⟨C₀, r₀, u₀, hr₀, hu₀, hsol⟩ := (livsic_fullShift hφ hr0 hr1).mpr hvan
  letI : BorelSpace (Shift α₀) := Pi.borelSpace
  have hu₀meas : Measurable u₀ := (hu₀.continuous hr₀).measurable
  have hcob₀ : IsAeCoboundaryOf (bern ν) shiftMap φ u₀ := ae_of_all _ hsol
  obtain ⟨c, hc⟩ := aeCoboundary_unique_mod_const hu hu₀meas hcob hcob₀
  exact ⟨u₀, C₀, r₀, c, hr₀, hu₀, hsol, hc⟩

end Regularity

end ErgodicTheory.Livsic
