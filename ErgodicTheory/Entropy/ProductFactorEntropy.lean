/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.FactorEntropy
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# The base entropy is below the entropy of the product with an identity factor

For a measure-preserving system `(X, T, μ)` and a probability space `(Y, ν)`, the product
transformation `T × id` on `(X × Y, μ ⊗ ν)` has the base system `(X, T, μ)` as a *factor*, via the
first projection `fst : X × Y → X`. Since a factor's Kolmogorov–Sinai entropy never exceeds that of
the total system, this gives the free inequality

`h(T) ≤ h(T × id)`  (`ErgodicTheory.Entropy.ksEntropy_le_prod`).

This is the easy half of Walters' product-entropy theorem (Walters, *An Introduction to Ergodic
Theory*, Theorem 4.23). Combined with the reverse bound `h(T × id) ≤ h(T)` it yields the equality
`h(T × id) = h(T)`.

The proof pulls each finite partition `R` of the base back along the factor map `fst`. By the
factor-relative entropy invariance (`ErgodicTheory.Entropy.factor_relative_eq`) the partition-relative
entropy `h(R, T)` equals `h(fst⁻¹ R, T × id)`, and the latter is bounded above by the entropy of the
product system (`ErgodicTheory.Entropy.le_ksEntropy`). Taking the supremum over all base partitions `R`
gives `h(T) ≤ h(T × id)`.

## Main results

* `ErgodicTheory.Entropy.ksEntropy_le_prod`: `h(T) ≤ h(T × id)`.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Theorem 4.23.
-/

open MeasureTheory Function

namespace ErgodicTheory.Entropy

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **The base entropy is below the entropy of the product with an identity factor:**
`h(T) ≤ h(T × id)`.

For a measure-preserving system `(X, T, μ)` and a probability space `(Y, ν)`, the first projection
`fst : X × Y → X` is a factor map from the product system `(X × Y, T × id, μ ⊗ ν)` onto the base
`(X, T, μ)` (it intertwines the dynamics, `fst ∘ (T × id) = T ∘ fst`, and is measure-preserving by
`measurePreserving_fst`). Each finite measurable partition `R` of the base pulls back to a partition
`fst⁻¹ R` of the product whose relative entropy agrees with that of `R` by the factor-relative
invariance `factor_relative_eq`; that pulled-back relative entropy is in turn `≤ h(T × id)` by
`le_ksEntropy`. Taking the supremum over all base partitions gives the claim.

This is the free `≥`-direction of Walters' product-entropy theorem (Theorem 4.23). -/
theorem ksEntropy_le_prod {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : X → X} (hT : MeasurePreserving T μ μ) :
    ksEntropy hT ≤ ksEntropy (hT.prod (MeasurePreserving.id ν)) := by
  refine iSup_le fun n => iSup_le fun R => ?_
  -- The first projection is a measure-preserving factor map intertwining the dynamics.
  have hπ : MeasurePreserving (Prod.fst : X × Y → X) (μ.prod ν) μ := measurePreserving_fst
  have hπS : (Prod.fst : X × Y → X) ∘ Prod.map T id = T ∘ Prod.fst := rfl
  -- Replace the base relative entropy by that of the pulled-back partition on the product.
  rw [← factor_relative_eq (hT.prod (MeasurePreserving.id ν)) hT hπ hπS R]
  -- The pulled-back partition's relative entropy is dominated by the product system's entropy.
  exact le_ksEntropy (hT.prod (MeasurePreserving.id ν)) (R.pulledBack hπ)

end ErgodicTheory.Entropy
