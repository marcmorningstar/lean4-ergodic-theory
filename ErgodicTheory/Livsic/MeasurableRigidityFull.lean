/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.BiShiftMeasurableRigidity
import ErgodicTheory.Livsic.BiShiftFactor
import ErgodicTheory.Livsic.FullShift
import ErgodicTheory.Livsic.MeasurableRigidity

/-!
# The full measurable Livšic rigidity theorem (Katok–Hasselblatt 19.2.4)

This is the finale (step **W6**) of the unbounded measurable Livšic rigidity programme (GitHub issue
#34): **measurable** a.e. solutions of the cohomological equation with Hölder data have vanishing
periodic obstructions, and the resulting full equivalence for the one-sided Bernoulli full shift.

The proof runs entirely through the **two-sided natural extension** over the Bernoulli product
structure: the one-sided shift `(Shift α₀, shiftMap, bern ν)` is a measure-theoretic factor of the
invertible two-sided shift `(BiShift α₀, biShiftMap, bernZ ν)` via the restriction map
`toShift : BiShift α₀ → Shift α₀` (`ErgodicTheory.Livsic.BiShiftFactor`). Hölder data,
measurability, and the a.e. cohomological equation all transport *up* the factor, so the two-sided
measurable-tier headline
`hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift`
(`ErgodicTheory.Livsic.BiShiftMeasurableRigidity`, via the stable/unstable essential-oscillation
bounds and the clamp — no Hölder-version construction of the transfer function, no Birkhoff ergodic
theorem, reverse Fatou throughout) applies to `φ ∘ toShift`. A **periodic lift** (a one-sided
`n`-periodic point `p` lifts to the bi-infinite `n`-periodization `pZ j = p ((j % n).toNat)`, which
is `biShiftMap`-`n`-periodic and whose Birkhoff sum of `φ ∘ toShift` equals that of `φ` along `p`)
then descends vanishing periodic sums back to the one-sided shift.

## Main results

* `hasVanishingPeriodicSums_of_measurable_aeCoboundary` — **the one-sided headline**: a Hölder
  observable that is the `bern ν`-a.e. coboundary of a merely **measurable** transfer function has
  vanishing periodic sums.
* `livsic_measurable_rigidity` — **the full Katok–Hasselblatt 19.2.4 equivalence**: over a fully
  supported Bernoulli measure, a Hölder observable (`0 < r ≤ 1`) admits a measurable a.e. transfer
  function **iff** all of its periodic Birkhoff sums vanish. The forward direction is the headline
  above; the backward direction produces the genuine Hölder solution (`livsic_fullShift`), which is
  continuous, hence measurable and an exact — so a.e. — coboundary.
* `measurable_aeCoboundary_ae_eq_holder` — the a.e. solution is `bern ν`-a.e. the Hölder solution up
  to a constant (uniqueness composition; from `measurable_solution_ae_eq_holder`).

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.4.
* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.

Issue #34.
-/

open MeasureTheory Function Filter
open scoped NNReal

namespace ErgodicTheory.Livsic

open ErgodicTheory.Multifractal

attribute [local instance] PiNat.metricSpace biShiftMetricSpace

/-! ### The periodic lift and the descent along the factor -/

section Descent

variable {α₀ : Type*}

/-- **Descent of vanishing periodic sums along the factor.** If the lifted observable `φ ∘ toShift`
has vanishing periodic sums for the two-sided shift, then `φ` has vanishing periodic sums for the
one-sided shift. Every one-sided `n`-periodic point `p` (with `n ≥ 1`) lifts to the bi-infinite
`n`-periodization `pZ j = p ((j % n).toNat)`, which is `biShiftMap`-`n`-periodic
(`Int.add_mul_emod_self_left`), restricts to `p` (`toShift pZ = p`, via `n`-periodicity of `p`), and
whose Birkhoff sum of `φ ∘ toShift` equals the Birkhoff sum of `φ` along `p` (the factor intertwines
the shifts, `Function.Semiconj.iterate_right`). -/
private theorem descend_vanishing {φ : Shift α₀ → ℝ}
    (hvanZ : HasVanishingPeriodicSums biShiftMap (φ ∘ toShift)) :
    HasVanishingPeriodicSums shiftMap φ := by
  intro n p hp
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp [birkhoffSum]
  · -- `p` is genuinely `n`-periodic on `ℕ`
    have hpper : ∀ m : ℕ, p (m + n) = p m := by
      intro m
      have h := congrFun hp m
      rwa [shiftMap_iterate_apply] at h
    -- hence `p` is invariant under reduction mod `n`
    have hpmod : ∀ m : ℕ, p (m % n) = p m := by
      intro m
      have haux : ∀ t a : ℕ, p (a + n * t) = p a := by
        intro t
        induction t with
        | zero => intro a; simp
        | succ k ih =>
          intro a
          have hstep : a + n * (k + 1) = (a + n * k) + n := by ring
          rw [hstep, hpper, ih a]
      calc p (m % n) = p (m % n + n * (m / n)) := (haux (m / n) (m % n)).symm
        _ = p m := by rw [Nat.mod_add_div]
    -- the bi-infinite `n`-periodization
    set pZ : BiShift α₀ := fun j : ℤ => p ((j % (n : ℤ)).toNat) with hpZdef
    have htoShiftpZ : toShift pZ = p := by
      funext m
      simp only [toShift, hpZdef]
      have hmod : ((m : ℤ) % (n : ℤ)).toNat = m % n := by omega
      rw [hmod]; exact hpmod m
    have hperZ : biShiftMap^[n] pZ = pZ := by
      funext j
      rw [ErgodicTheory.biShiftMap_iterate_apply]
      simp only [hpZdef]
      have hemod : (j + (n : ℤ)) % (n : ℤ) = j % (n : ℤ) := by
        have hrw : j + (n : ℤ) = j + n * 1 := by ring
        rw [hrw, Int.add_mul_emod_self_left]
      rw [hemod]
    -- the lifted Birkhoff sum along `pZ` equals the Birkhoff sum along `p`
    have hsc : Function.Semiconj (toShift (α₀ := α₀)) biShiftMap shiftMap := toShift_biShiftMap
    have hsum_eq : birkhoffSum biShiftMap (φ ∘ toShift) n pZ = birkhoffSum shiftMap φ n p := by
      simp only [birkhoffSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Function.comp_apply]
      rw [hsc.iterate_right k pZ, htoShiftpZ]
    have hvan := hvanZ n pZ hperZ
    rwa [hsum_eq] at hvan

end Descent

/-! ### The one-sided measurable headline -/

section OneSided

variable {α₀ : Type*} [Finite α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- **One-sided measurable-tier Livšic rigidity (headline).** Let `ν` be a fully supported
probability law on the finite discrete alphabet `α₀`. If a Hölder observable `φ` (`r > 0`) is the
`bern ν`-a.e. coboundary of a merely **measurable** (possibly **unbounded**) transfer function `u`,
then `φ` has **vanishing periodic sums** for the one-sided full shift.

Route: transport `φ, u` up the natural-extension factor `toShift` (Hölder data by
`holderWith_comp_toShift`, measurability by `measurable_comp_toShift`, the a.e. equation by
`isAeCoboundaryOf_comp_toShift`); apply the two-sided measurable headline
`hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift`; descend by the periodic lift
(`descend_vanishing`). -/
theorem hasVanishingPeriodicSums_of_measurable_aeCoboundary
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ : Shift α₀ → ℝ} (hφ : HolderWith C r φ) (hr : 0 < r)
    {u : Shift α₀ → ℝ} (hu : Measurable u) (hae : IsAeCoboundaryOf (bern ν) shiftMap φ u) :
    HasVanishingPeriodicSums shiftMap φ := by
  have hvanZ : HasVanishingPeriodicSums biShiftMap (φ ∘ toShift) :=
    hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift ν hν
      (holderWith_comp_toShift hφ) hr (measurable_comp_toShift hu)
      (isAeCoboundaryOf_comp_toShift ν hae)
  exact descend_vanishing hvanZ

end OneSided

/-! ### The full Katok–Hasselblatt 19.2.4 equivalence -/

section Full

variable {α₀ : Type*} [Nonempty α₀] [Encodable α₀] [Finite α₀] [TopologicalSpace α₀]
  [DiscreteTopology α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- **Full measurable Livšic rigidity for the one-sided full shift (Katok–Hasselblatt 19.2.4).**
Over a fully supported Bernoulli measure `bern ν` on a nonempty encodable finite discrete alphabet,
a Hölder observable `φ` (`0 < r ≤ 1`) admits *some* **measurable** `bern ν`-a.e. transfer function
solving `φ = u ∘ shiftMap − u` **iff** all of its periodic Birkhoff sums vanish.

* **(⇒)** the measurable one-sided headline `hasVanishingPeriodicSums_of_measurable_aeCoboundary`
  (via the two-sided natural extension: stable/unstable essential oscillation + clamp, reverse
  Fatou, no Hölder-version construction, no Birkhoff ergodic theorem).
* **(⇐)** vanishing periodic sums feed the substantive backward direction of `livsic_fullShift` to
  produce a genuine **Hölder** transfer function, which — being Hölder — is continuous, hence
  measurable, and is an exact (so a.e.) coboundary. -/
theorem livsic_measurable_rigidity
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ : Shift α₀ → ℝ} (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∃ u, Measurable u ∧ IsAeCoboundaryOf (bern ν) shiftMap φ u) ↔
      HasVanishingPeriodicSums shiftMap φ := by
  constructor
  · rintro ⟨u, hu, hcob⟩
    exact hasVanishingPeriodicSums_of_measurable_aeCoboundary ν hν hφ hr0 hu hcob
  · intro hvan
    obtain ⟨C₀, r₀, u₀, hr₀, hu₀, hsol⟩ := (livsic_fullShift hφ hr0 hr1).mpr hvan
    letI : BorelSpace (Shift α₀) := Pi.borelSpace
    have hu₀meas : Measurable u₀ := (hu₀.continuous hr₀).measurable
    exact ⟨u₀, hu₀meas, ae_of_all _ hsol⟩

/-- **Uniqueness composition.** If a Hölder `φ` (`0 < r ≤ 1`) admits a measurable `bern ν`-a.e.
transfer function `u`, then — since the resulting vanishing periodic sums produce the genuine Hölder
solution `u₀` — `u` differs from `u₀` by a `bern ν`-a.e. constant. Directly composes the full
equivalence `livsic_measurable_rigidity` with the conditional regularity
`measurable_solution_ae_eq_holder`. -/
theorem measurable_aeCoboundary_ae_eq_holder
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ : Shift α₀ → ℝ} (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    {u : Shift α₀ → ℝ} (hu : Measurable u) (hcob : IsAeCoboundaryOf (bern ν) shiftMap φ u) :
    ∃ (u₀ : Shift α₀ → ℝ) (C₀ r₀ : ℝ≥0) (c : ℝ), 0 < r₀ ∧ HolderWith C₀ r₀ u₀ ∧
      (∀ x, φ x = u₀ (shiftMap x) - u₀ x) ∧ (fun x => u x - u₀ x) =ᵐ[bern ν] fun _ => c := by
  have hvan : HasVanishingPeriodicSums shiftMap φ :=
    (livsic_measurable_rigidity ν hν hφ hr0 hr1).mp ⟨u, hu, hcob⟩
  exact measurable_solution_ae_eq_holder hφ hr0 hr1 hvan hu hcob

end Full

end ErgodicTheory.Livsic
