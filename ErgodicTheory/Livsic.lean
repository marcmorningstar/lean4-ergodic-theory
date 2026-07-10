/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.HolderExtend
import ErgodicTheory.Livsic.Abstract
import ErgodicTheory.Livsic.ShiftMetric
import ErgodicTheory.Livsic.DenseOrbit
import ErgodicTheory.Livsic.FullShiftClosing
import ErgodicTheory.Livsic.ContinuousRigidity
import ErgodicTheory.Livsic.BoundedRigidity
import ErgodicTheory.Livsic.FullShift
import ErgodicTheory.Livsic.ErgodicDenseOrbit
import ErgodicTheory.Livsic.DoublingClosing
import ErgodicTheory.Livsic.Doubling
import ErgodicTheory.Livsic.SubshiftFiniteType
import ErgodicTheory.Livsic.SubshiftDenseOrbit
import ErgodicTheory.Livsic.BiShiftMetric
import ErgodicTheory.Livsic.BiShiftClosing
import ErgodicTheory.Livsic.BiShiftDenseOrbit
import ErgodicTheory.Livsic.BiShiftFull
import ErgodicTheory.Livsic.FlowCoboundary
import ErgodicTheory.Livsic.MeasurableRigidity
import ErgodicTheory.Livsic.BiShiftFactor
import ErgodicTheory.Livsic.BiShiftProductStructure
import ErgodicTheory.Livsic.BiShiftStableOscillation
import ErgodicTheory.Livsic.BiShiftUnstableOscillation
import ErgodicTheory.Livsic.BiShiftMeasurableRigidity
import ErgodicTheory.Livsic.MeasurableRigidityFull

/-!
# The Livšic cohomological rigidity theorem

This is the aggregator module for the **Livšic (Livshits) theorem** (issue #29): over a
hyperbolic-type map `T : X → X`, a Hölder observable `φ` is a Hölder coboundary `φ = u ∘ T − u`
**iff** all of its periodic Birkhoff sums vanish. It collects the abstract theorem, its metric
substrate on the one-sided full shift, the headline full-shift instance, and the measurable-rigidity
tiers.

## Layout

* `ErgodicTheory.Livsic.Defs` — the vocabulary (`IsCoboundary`, `IsHolderCoboundary`,
  `HasVanishingPeriodicSums`, the abstracted summed exponential closing property `ExpClosing`), the
  trivial telescoping direction, and the bare obstruction certificate
  `not_isCoboundary_of_periodicSum_ne_zero`.
* `ErgodicTheory.Livsic.HolderExtend` — the McShane–Whitney Hölder extension theorem
  `exists_holderWith_extension`, the extension step used by the abstract theorem.
* `ErgodicTheory.Livsic.Abstract` — the substantive direction (Katok–Hasselblatt 19.2.1) and the
  headline equivalence `isHolderCoboundary_iff` for an abstract compact system with a dense orbit.
* `ErgodicTheory.Livsic.ShiftMetric` — the `PiNat` metric facts about the full shift
  (`lipschitzWith_two_shiftMap`, the coordinate-agreement ↔ distance dictionary, the ultrametric
  instance).
* `ErgodicTheory.Livsic.DenseOrbit` — a dense forward shift orbit over any nonempty encodable
  alphabet, plus the concrete non-vacuity potentials on `Shift (Fin 2)`.
* `ErgodicTheory.Livsic.FullShiftClosing` — the exponential closing property for the one-sided full
  shift (`expClosing_shiftMap`), by pure periodization.
* `ErgodicTheory.Livsic.ContinuousRigidity` — the continuous-transfer-function rigidity tier.
* `ErgodicTheory.Livsic.BoundedRigidity` — the bounded-measurable-transfer-function rigidity tier,
  via periodic-orbit shadowing on cylinders of a fully supported Bernoulli measure.
* `ErgodicTheory.Livsic.FullShift` — the headline instance `livsic_fullShift` (and its `Fin m`
  specialization), the `Shift (Fin 2)` non-vacuity witnesses, and the two rigidity corollaries over
  a fully supported Bernoulli measure.
* `ErgodicTheory.Livsic.ErgodicDenseOrbit` — the generic topological-dynamics input
  `ergodic_exists_denseRange_iterate`: an ergodic map on a second-countable open-positive
  probability space has a point with dense forward orbit (feeds the doubling-map and cat-map
  instances).
* `ErgodicTheory.Livsic.DoublingClosing` / `ErgodicTheory.Livsic.Doubling` — the **smooth expanding
  instance** (issue #33) for the doubling map `y ↦ 2 • y` on `UnitAddCircle`: the rounding closing
  construction `expClosing_doublingMap` and the headline equivalence `livsic_doublingMap`, with the
  obstruction witness `const_one_not_isCoboundary_doublingMap` and the positive witness
  `norm_coboundary_isHolderCoboundary`.
* `ErgodicTheory.Livsic.SubshiftFiniteType` / `ErgodicTheory.Livsic.SubshiftDenseOrbit` — the
  **one-sided subshift-of-finite-type tier**: the unconditional `δ = 1/2` closing property
  `expClosing_sftShiftMap` (admissible with no connecting word or irreducibility hypothesis), the
  conditional equivalence `livsic_sft`, the dense-orbit construction
  `exists_denseRange_sftShiftMap_orbit` under a `SafeSymbol`, and the headline **golden-mean shift**
  instance `livsic_goldenMean` (with the properness certificate `goldenMean_proper`).
* `ErgodicTheory.Livsic.BiShiftMetric` / `…BiShiftClosing` / `…BiShiftDenseOrbit` /
  `…BiShiftFull` — the **two-sided (invertible) full-shift tier** (issue #32): the `ℤ`-indexed
  θ-ultrametric substrate, the min-regime two-sided closing property `expClosing_biShiftMap`, the
  bilateral dense orbit `exists_denseRange_biShiftMap_orbit`, and the headline equivalence
  `livsic_biShift` with its rigidity corollaries
  `isHolderCoboundary_of_continuous_aeCoboundary_biShift` and
  `isHolderCoboundary_of_bounded_aeCoboundary_biShift` over a fully supported two-sided Bernoulli
  measure (`isOpenPosMeasure_bernZ`).
* `ErgodicTheory.Livsic.FlowCoboundary` — the **flow-coboundary obstruction tier** (issue #36): the
  regularity-free flow coboundary `IsFlowCoboundary Φ F` (the flow analogue of `IsCoboundary`,
  `u (Φ t q) − u q = ∫₀ᵗ F (Φ s q) ds`) and its periodic-orbit obstruction
  `not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero` (a nonzero closed-orbit integral defeats
  every transfer function). The concrete suspension-flow landing of this tier — the induced base
  observable and both obstruction directions on the mapping-torus flow — lives in
  `ErgodicTheory.Continuous.SuspensionCoboundary`.
* `ErgodicTheory.Livsic.MeasurableRigidity` — the **measurable-solution tier** (uniqueness modulo
  constants `aeCoboundary_unique_mod_const` via Bernoulli ergodicity, and conditional regularity
  `measurable_solution_ae_eq_holder`).
* `ErgodicTheory.Livsic.BiShiftFactor` / `…BiShiftProductStructure` / `…BiShiftStableOscillation` /
  `…BiShiftUnstableOscillation` / `…BiShiftMeasurableRigidity` / `…MeasurableRigidityFull` — the
  **unbounded measurable rigidity tier** (issue #34, the classical Livšic *regularity* theorem,
  Katok–Hasselblatt 19.2.4). Working through the two-sided natural extension (`toShift` factor over
  the past ⊗ future Bernoulli product structure `joinPF`), the two symmetric essential-oscillation
  bounds (`stable_pair_osc`, same-future pairs; `unstable_pair_osc`, same-past pairs — the classical
  **Lusin theorem** `ErgodicTheory.lusin_continuousOn` of
  `ErgodicTheory.MeasureTheory.LusinContinuousOn` + reverse Fatou, no Birkhoff ergodic theorem, no
  boundedness of the transfer function) feed the Fubini glue to make a merely **measurable** a.e.
  transfer function essentially bounded; a clamp then discharges vanishing periodic sums. The
  finale is the full equivalence
  `livsic_measurable_rigidity`: over a fully supported Bernoulli measure a Hölder observable
  admits a measurable a.e. transfer function **iff** all of its periodic Birkhoff sums vanish.

The full shift is the simplest mixing subshift of finite type (no admissibility bookkeeping), so its
closing property is unconditional. The follow-up issues #32 and #33 close the two-sided full shift,
the general one-sided SFT (with the golden-mean instance and the smooth doubling-map instance) and
the cat-map instance (`ErgodicTheory.Examples.CatMapClosing`). Issue #34 closes the unbounded
measurable regularity tier (the classical Livšic *regularity* theorem, Katok–Hasselblatt 19.2.4),
the last remaining tier of this file.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorems 19.2.1 and 19.2.4.
* W. Parry, M. Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic dynamics*,
  Astérisque **187–188** (1990), Ch. 3, Prop. 3.7.
-/
