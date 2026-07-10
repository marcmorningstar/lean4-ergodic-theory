/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Abstract
import ErgodicTheory.Livsic.FullShiftClosing
import ErgodicTheory.Livsic.DenseOrbit
import ErgodicTheory.Livsic.ShiftMetric
import ErgodicTheory.Livsic.ContinuousRigidity
import ErgodicTheory.Livsic.BoundedRigidity

/-!
# The Livšic theorem for the one-sided full shift

This is the headline instance of the abstract Livšic cohomological rigidity theorem (issue #29) for
the **one-sided full shift** `shiftMap` on `Shift α₀ := ∀ _ : ℕ, α₀`, the simplest mixing subshift
of finite type. The full shift carries **no admissibility bookkeeping** — every finite word is legal
— so the geometric hypothesis of the abstract theorem (the summed exponential closing property) is
available unconditionally (`ErgodicTheory.Livsic.expClosing_shiftMap`), and the metric substrate,
the dense forward orbit, and the closing constant assemble into the clean equivalence

`IsHolderCoboundary shiftMap φ ↔ HasVanishingPeriodicSums shiftMap φ`

for every Hölder observable `φ` (exponent `0 < r ≤ 1`).

## Main results

* `livsic_fullShift` — the headline equivalence, for a general nonempty encodable finite discrete
  alphabet `α₀` under the local `PiNat` ultrametric.
* `livsic_fullShift_fin` — its specialization to the `m`-symbol full shift `Shift (Fin m)`.
* `not_isCoboundary_of_periodicSum_ne_zero` (in `ErgodicTheory.Livsic.Defs`) — the bare obstruction
  certificate: one non-vanishing periodic sum defeats every coboundary.
* `phi_not_isCoboundary` / `phi_not_isHolderCoboundary` / `psi_isHolderCoboundary` — the non-vacuity
  witnesses on `Shift (Fin 2)`: the locally constant `φ` is **not** a coboundary (nonzero sum at the
  fixed point `fun _ => 1`), while `ψ = φ ∘ shiftMap − φ` **is** a Hölder coboundary.
* `psi_hasVanishingPeriodicSums` / `psi_isHolderCoboundary_via_livsic` — a round-trip re-deriving
  `ψ`'s Hölder-coboundary property **through** the substantive backward direction of
  `livsic_fullShift` (`.mpr`), exercising the hard direction end-to-end on a concrete witness.
* `isOpenPosMeasure_bern` — a fully supported Bernoulli measure charges every nonempty open set.
* `isHolderCoboundary_of_continuous_aeCoboundary` — continuous-tier rigidity: a **continuous** a.e.
  solution of the cohomological equation (w.r.t. a fully supported `bern ν`) forces `φ` to be a
  Hölder coboundary.
* `isHolderCoboundary_of_bounded_aeCoboundary` — bounded-tier rigidity: a **bounded** measurable
  a.e. solution likewise forces `φ` to be a Hölder coboundary.

## Companion tiers (formerly deferred, since discharged)

* general subshifts of finite type — `ErgodicTheory.Livsic.SubshiftFiniteType` (issue #32);
* the two-sided (invertible) shift — `ErgodicTheory.Livsic.BiShiftFull` (issue #32);
* the unbounded measurable regularity tier (the classical Livšic *regularity* theorem, via a
  Lusin-continuity argument on the two-sided natural extension) —
  `ErgodicTheory.Livsic.MeasurableRigidityFull` (issue #34).

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.1 (existence) and Theorem 19.2.4 (regularity tiers).
* W. Parry, M. Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic dynamics*,
  Astérisque **187–188** (1990), Ch. 3, Prop. 3.7 (one-sided/expanding closing).
-/

open MeasureTheory Function Set
open scoped NNReal

attribute [local instance] PiNat.metricSpace

namespace ErgodicTheory.Livsic

open ErgodicTheory.Multifractal

/-! ### The headline full-shift Livšic equivalence -/

section FullShift

variable {α₀ : Type*} [Nonempty α₀] [Encodable α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [Finite α₀]

/-- **Livšic for the one-sided full shift.** Over a nonempty encodable finite discrete alphabet
`α₀`, with the `PiNat` ultrametric on `Shift α₀`, a Hölder observable `φ` (exponent `0 < r ≤ 1`) is
a **Hölder coboundary** for the left shift **iff** all of its periodic Birkhoff sums vanish.

This instantiates the abstract `isHolderCoboundary_iff` (Katok–Hasselblatt 19.2.1): continuity of
the shift is `lipschitzWith_two_shiftMap`, compactness is Tychonoff over the finite alphabet, the
summed exponential closing property is `expClosing_shiftMap` (with `δ = 1`, closing constant
`K = (1/2)^r / (1 − (1/2)^r) ≥ 0`), and the dense forward orbit is
`exists_denseRange_shiftMap_orbit_alphabet`. -/
theorem livsic_fullShift {C r : ℝ≥0} {φ : Shift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsHolderCoboundary shiftMap φ ↔ HasVanishingPeriodicSums shiftMap φ := by
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr0
  obtain ⟨x₀, hdense⟩ := exists_denseRange_shiftMap_orbit_alphabet α₀
  have hnum : (0 : ℝ) < (1 / 2 : ℝ) ^ (r : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt1 : (1 / 2 : ℝ) ^ (r : ℝ) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hrpos
  have hden : (0 : ℝ) < 1 - (1 / 2 : ℝ) ^ (r : ℝ) := by linarith
  have hK : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := (div_pos hnum hden).le
  exact isHolderCoboundary_iff lipschitzWith_two_shiftMap.continuous hr0 hr1 hφ
    one_pos hK (expClosing_shiftMap hrpos) hdense

end FullShift

/-- **Livšic for the `m`-symbol full shift** (`m ≠ 0`). The specialization of `livsic_fullShift` to
`Shift (Fin m)`: a Hölder `φ` is a Hölder coboundary for the shift iff all its periodic Birkhoff
sums vanish. -/
theorem livsic_fullShift_fin (m : ℕ) [NeZero m] {C r : ℝ≥0} {φ : Shift (Fin m) → ℝ}
    (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsHolderCoboundary shiftMap φ ↔ HasVanishingPeriodicSums shiftMap φ :=
  livsic_fullShift hφ hr0 hr1

/-! ### Non-vacuity witnesses on the binary full shift `Shift (Fin 2)` -/

/-- **Obstruction witness.** The locally constant potential `phi x = if x 0 = 0 then 0 else 1` on
the binary full shift is **not** a coboundary: its period-`1` Birkhoff sum at the fixed point
`fun _ => 1` is `phi (fun _ => 1) = 1 ≠ 0`, so the bare obstruction certificate
`not_isCoboundary_of_periodicSum_ne_zero` applies. -/
theorem phi_not_isCoboundary : ¬ IsCoboundary shiftMap phi := by
  refine not_isCoboundary_of_periodicSum_ne_zero (n := 1) (p := fun _ : ℕ => (1 : Fin 2)) ?_ ?_
  · rw [Function.iterate_one]; exact shift_const_fixed
  · rw [birkhoffSum_one, phi_apply_const_one]; exact one_ne_zero

/-- Consequently `phi` is not a **Hölder** coboundary either (a Hölder coboundary is a coboundary).
This is the genuine obstruction: `phi` is `HolderWith 1 1` (`holder_phi`) yet, having a nonzero
periodic sum, cannot be written `u ∘ shiftMap − u` for any Hölder `u`. -/
theorem phi_not_isHolderCoboundary : ¬ IsHolderCoboundary shiftMap phi :=
  fun h => phi_not_isCoboundary h.isCoboundary

/-- **Positive witness.** `ψ = φ ∘ shiftMap − φ` is, by construction, a Hölder coboundary of the
binary full shift, with the `HolderWith 1 1` transfer function `phi` (`holder_phi`). -/
theorem psi_isHolderCoboundary : IsHolderCoboundary shiftMap psi :=
  ⟨1, 1, phi, one_pos, holder_phi, fun x => psi_eq_coboundary x⟩

/-- The positive witness `ψ` has **vanishing periodic sums** — the trivial-direction obligation any
coboundary must meet. Immediate from its explicit coboundary structure `ψ = φ ∘ shiftMap − φ` via
`IsCoboundary.hasVanishingPeriodicSums`. -/
theorem psi_hasVanishingPeriodicSums : HasVanishingPeriodicSums shiftMap psi :=
  IsCoboundary.hasVanishingPeriodicSums ⟨phi, fun x => psi_eq_coboundary x⟩

/-- **End-to-end exercise of the substantive Livšic direction.** `ψ` is Hölder — `φ` is
`1`-Lipschitz (`holder_phi`) and `shiftMap` is `2`-Lipschitz (`lipschitzWith_two_shiftMap`), so the
difference `ψ = φ ∘ shiftMap − φ` is `3`-Lipschitz, hence `HolderWith 3 1` — and it has vanishing
periodic sums (`psi_hasVanishingPeriodicSums`). Feeding those through the **hard** backward
direction of `livsic_fullShift` (`.mpr`, the dense-orbit reconstruction of a transfer function from
the periodic data) re-derives that `ψ` is a Hölder coboundary. Unlike `psi_isHolderCoboundary`
(which just exhibits the by-construction transfer function `φ`), this routes the conclusion through
the reconstruction, exercising the substantive half of the equivalence on a concrete witness. -/
theorem psi_isHolderCoboundary_via_livsic : IsHolderCoboundary shiftMap psi := by
  have hp : LipschitzWith 1 phi := holderWith_one.mp holder_phi
  have hsub : LipschitzWith (1 * 2 + 1) psi :=
    (hp.comp lipschitzWith_two_shiftMap).sub hp
  have hconst : (1 * 2 + 1 : ℝ≥0) = 3 := by norm_num
  rw [hconst] at hsub
  exact (livsic_fullShift (holderWith_one.mpr hsub) one_pos le_rfl).mpr
    psi_hasVanishingPeriodicSums

/-! ### Rigidity corollaries over a fully supported Bernoulli measure -/

/-- **Full support ⇒ open-positive.** A fully supported (`ν {a} ≠ 0` for every symbol `a`) Bernoulli
measure `bern ν` on the full shift charges every nonempty open set, i.e. it is an
`IsOpenPosMeasure`. Proof: a nonempty open `U` contains a metric ball `ball x ε ⊆ U`; choosing `n`
with `(1/2)^n < ε` makes the depth-`n` cylinder around `x` a subset of that ball, and
`bern_cylinder_pos` charges the cylinder — so `U` inherits positive mass. -/
theorem isOpenPosMeasure_bern {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]
    [MeasurableSpace α₀] [MeasurableSingletonClass α₀] (ν : Measure α₀) [IsProbabilityMeasure ν]
    (hν : ∀ a : α₀, ν {a} ≠ 0) :
    (bern ν).IsOpenPosMeasure := by
  refine ⟨fun U hU hUne => ?_⟩
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hcyl_sub : {z : Shift α₀ | ∀ i < n, z i = x i} ⊆ U := by
    intro z hz
    refine hball ?_
    rw [Metric.mem_ball]
    have hd : dist z x ≤ (1 / 2 : ℝ) ^ n :=
      PiNat.mem_cylinder_iff_dist_le.1 (PiNat.mem_cylinder_iff.2 hz)
    exact lt_of_le_of_lt hd hn
  have hpos : bern ν {z : Shift α₀ | ∀ i < n, z i = x i} ≠ 0 := bern_cylinder_pos ν hν x n
  exact fun hUzero => hpos (measure_mono_null hcyl_sub hUzero)

section Rigidity

variable {α₀ : Type*} [Nonempty α₀] [Encodable α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [Finite α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- **Continuous-tier full-shift rigidity.** Let `ν` be a fully supported probability law on the
finite discrete alphabet. If a Hölder `φ` (`0 < r ≤ 1`) equals the coboundary of a **continuous**
transfer function `u` only `bern ν`-almost-everywhere, then `φ` is a genuine Hölder coboundary.
Chain: full support makes `bern ν` open-positive (`isOpenPosMeasure_bern`), so the a.e. equation
upgrades to vanishing periodic sums (`hasVanishingPeriodicSums_of_continuous_coboundary`), and
`livsic_fullShift` promotes that to a Hölder coboundary. -/
theorem isHolderCoboundary_of_continuous_aeCoboundary
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ u : Shift α₀ → ℝ} (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hu : Continuous u) (hcob : IsAeCoboundaryOf (bern ν) shiftMap φ u) :
    IsHolderCoboundary shiftMap φ := by
  haveI := isOpenPosMeasure_bern ν hν
  have hvps := hasVanishingPeriodicSums_of_continuous_coboundary
    lipschitzWith_two_shiftMap.continuous hu (hφ.continuous hr0) hcob
  exact (livsic_fullShift hφ hr0 hr1).2 hvps

/-- **Bounded-tier full-shift rigidity.** With `ν` fully supported as above, if a Hölder `φ`
(`0 < r ≤ 1`) equals the coboundary of a **bounded** measurable transfer function `u` (`|u| ≤ M`)
only `bern ν`-almost-everywhere, then `φ` is a genuine Hölder coboundary. Chain: the bounded a.e.
equation forces vanishing periodic sums via the periodic-orbit shadowing argument
(`hasVanishingPeriodicSums_of_bounded_aeCoboundary`), and `livsic_fullShift` promotes it. -/
theorem isHolderCoboundary_of_bounded_aeCoboundary
    (ν : Measure α₀) [IsProbabilityMeasure ν] (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ u : Shift α₀ → ℝ} (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    {M : ℝ} (hu_bdd : ∀ x, |u x| ≤ M) (hae : IsAeCoboundaryOf (bern ν) shiftMap φ u) :
    IsHolderCoboundary shiftMap φ := by
  have hvps := hasVanishingPeriodicSums_of_bounded_aeCoboundary ν hν hφ hr0 hu_bdd hae
  exact (livsic_fullShift hφ hr0 hr1).2 hvps

end Rigidity

end ErgodicTheory.Livsic
