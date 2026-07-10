/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Defs
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Livšic rigidity for continuous transfer functions

This file is the **continuous-solution tier** of the measurable-Livšic rigidity programme
(issue #29). Building on the shared vocabulary of `ErgodicTheory.Livsic.Defs`
(`IsCoboundary`, `HasVanishingPeriodicSums`, the telescoping identity
`birkhoffSum_eq_of_coboundary` and the trivial direction
`IsCoboundary.hasVanishingPeriodicSums`), it proves the *easy but genuinely useful* half of the
measurable rigidity statement outright:

> If a **continuous** transfer function `u` solves the cohomological equation `φ = u ∘ T − u`
> only `μ`-almost-everywhere, for a **fully supported** measure `μ` (`μ.IsOpenPosMeasure`) and a
> continuous `φ`, then `φ` has **vanishing periodic sums**: `birkhoffSum T φ n p = 0` for every
> `n`-periodic point `p`.

## The three-tier structure of measurable Livšic rigidity

The Livšic regularity programme splits by the regularity one assumes of the a.e. transfer function
`u` solving `φ = u ∘ T − u`:

1. **Continuous tier (this file).** If `u` is already *continuous* and `μ` is fully supported, then
   the a.e. equation upgrades to an *everywhere* equation (`Continuous.ae_eq_iff_eq`), so `φ` is a
   genuine coboundary and `IsCoboundary.hasVanishingPeriodicSums` finishes. Needs **no** ergodicity,
   hyperbolicity, or Lusin/recurrence machinery.
2. **Bounded-measurable tier** (`ErgodicTheory.Livsic.BoundedRigidity`). `u` merely measurable but
   **bounded**; the everywhere upgrade is unavailable, and one instead runs a periodic-orbit
   shadowing argument on cylinders of the full shift, using that the endpoint difference
   `u (T^[N] x) − u x` is controlled *uniformly in `N`* precisely because `u` is bounded.
3. **Unbounded-measurable tier** (`ErgodicTheory.Livsic.MeasurableRigidityFull`, issue #34). For a
   genuinely unbounded measurable `u` the uniform endpoint control breaks, and the theorem is the
   classical Livšic *regularity* theorem (Katok–Hasselblatt, Theorem 19.2.4). It is discharged by a
   Lusin-continuity argument on the two-sided natural extension (stable/unstable
   essential-oscillation bounds + reverse Fatou + clamp): `livsic_measurable_rigidity`.

The substantive content of the harder tiers is precisely the *promotion of a merely measurable `u`
to a controllable one*; once that promotion is available, the present lemma finishes.

## Main definitions

* `ErgodicTheory.IsAeCoboundaryOf μ T φ u` — witnessed a.e. coboundary of the given `u` (generic,
  parallel to `IsCoboundary`).
* `ErgodicTheory.IsAeCoboundary μ T φ` — `φ` is an a.e. coboundary of a *measurable* `u`.

(The obstruction class `HasVanishingPeriodicSums` and the coboundary vocabulary `IsCoboundary`
live in `ErgodicTheory.Livsic.Defs` and are reused here unchanged.)

## Main results

* `ErgodicTheory.Livsic.hasVanishingPeriodicSums_of_continuous_coboundary` — the continuous-tier
  Livšic rigidity theorem.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.4.
* A. Wilkinson, *The cohomological equation for partially hyperbolic diffeomorphisms*, Astérisque
  (2013), §2.
-/

open MeasureTheory Filter Function
open scoped Topology

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

/-- **Witnessed a.e. coboundary.** `φ` equals `u ∘ T − u` on a set of full `μ`-measure. Fully
generic (no dynamical hypotheses), the a.e. analogue of `IsCoboundary`. -/
def IsAeCoboundaryOf (μ : Measure X) (T : X → X) (φ u : X → ℝ) : Prop :=
  φ =ᵐ[μ] fun x => u (T x) - u x

/-- **Measurable a.e. coboundary.** `φ` is the a.e. coboundary of *some* measurable transfer
function `u`. This is the hypothesis of the measurable-Livšic rigidity theorem. -/
def IsAeCoboundary (μ : Measure X) (T : X → X) (φ : X → ℝ) : Prop :=
  ∃ u : X → ℝ, Measurable u ∧ IsAeCoboundaryOf μ T φ u

namespace Livsic

/-! ### Continuous-tier Livšic rigidity -/

variable [TopologicalSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]

/-- **Continuous-tier Livšic rigidity.** If `φ` is continuous and equals the coboundary of a
**continuous** `u` only `μ`-a.e., then — because `μ` is fully supported, so a.e.-equal continuous
functions are equal — `φ` is an *everywhere* coboundary, hence (via the trivial telescoping
direction `IsCoboundary.hasVanishingPeriodicSums`) has vanishing periodic sums.

This is the rigidity theorem in the regularity class in which it is elementary. The substantive
content of measurable Livšic is precisely the *promotion of a merely measurable `u` to a continuous
one*; once that promotion is available, this lemma finishes. -/
theorem hasVanishingPeriodicSums_of_continuous_coboundary {T : X → X} {φ u : X → ℝ}
    (hT : Continuous T) (hu : Continuous u) (hφ : Continuous φ)
    (hcob : IsAeCoboundaryOf μ T φ u) :
    HasVanishingPeriodicSums T φ := by
  -- Upgrade the a.e. equation to a pointwise (everywhere) equation, then use the trivial direction.
  have hpt : ∀ x, φ x = u (T x) - u x :=
    fun x => congrFun ((Continuous.ae_eq_iff_eq μ hφ ((hu.comp hT).sub hu)).1 hcob) x
  exact IsCoboundary.hasVanishingPeriodicSums ⟨u, hpt⟩

end Livsic

end ErgodicTheory
