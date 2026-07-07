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

The full shift is the simplest mixing subshift of finite type (no admissibility bookkeeping), so its
closing property is unconditional. Deferred to follow-up issues: general SFTs (transition-matrix
admissibility), the two-sided shift, and the unbounded measurable regularity tier (the classical
Livšic *regularity* theorem, Katok–Hasselblatt 19.2.4).

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorems 19.2.1 and 19.2.4.
* W. Parry, M. Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic dynamics*,
  Astérisque **187–188** (1990), Ch. 3, Prop. 3.7.
-/
