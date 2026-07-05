/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.GeneratorTheoremTwoSided
import ErgodicTheory.Multifractal.BernoulliTwoSidedGenerating

/-!
# The Kolmogorov–Sinai entropy of the two-sided Bernoulli shift equals `Hnu ν`

This is the headline "unlock" of the two-sided Bernoulli development: the **system**
(Kolmogorov–Sinai) entropy of the invertible left shift `biShiftEquiv` on the two-sided full shift
`BiShift α₀ := ℤ → α₀`, equipped with the two-sided i.i.d. measure `bernZ ν`, equals the
per-symbol Shannon entropy `Hnu ν`:
`ksEntropy (measurePreserving_biShiftEquiv_bernZ ν) = Hnu ν` (as an `EReal`).

It is a clean three-step composition of finished results:

1. **Two-sided generator theorem** (`ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided`,
   `ErgodicTheory.Entropy`): for a measure-preserving automorphism of a standard Borel probability
   space and a *two-sided generating* finite partition `P`, the system entropy is already attained
   on `P`, `h(e) = h(e, P)`. Applied with `e := biShiftEquiv`, `P := coordPartitionZFin (bernZ ν)`,
   and the two-sided generating discharge `coordPartitionZFin_isGeneratingTwoSided`, this gives
   `ksEntropy … = (ksEntropyPartition … (coordPartitionZFin (bernZ ν)) : EReal)`.
2. **The base entropy datum** (`ksEntropyPartition_coordPartitionZFin_bernZ_eq`): the
   partition-relative entropy of the time-`0` coordinate partition is the single-symbol entropy
   `Hnu ν`.
3. **Combine** by rewriting.

The only typeclass friction is the `StandardBorelSpace (BiShift α₀)` requirement of the generator
theorem. It is supplied entirely by instance resolution from the ambient `[Fintype α₀]
[MeasurableSpace α₀] [MeasurableSingletonClass α₀]`: a finite type is `Countable`, a countable
`MeasurableSingletonClass` is a `DiscreteMeasurableSpace`, a countable discrete measurable space is
standard Borel (`StandardBorelSpace.standardBorelSpace_of_discreteMeasurableSpace`), and a countable
(`ℤ`) product of standard Borel spaces is standard Borel (`StandardBorelSpace.pi_countable`). No
extra hypothesis on `α₀` is needed.

## Main result

* `ErgodicTheory.Multifractal.ksEntropy_biShiftEquiv_bernZ_eq`
-/

open MeasureTheory
open ErgodicTheory.Entropy

namespace ErgodicTheory.Multifractal

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- **System entropy of the two-sided Bernoulli shift.** The Kolmogorov–Sinai entropy of the
invertible left shift `biShiftEquiv` on the two-sided full shift `BiShift α₀ := ℤ → α₀` with the
two-sided i.i.d. measure `bernZ ν` equals the per-symbol Shannon entropy `Hnu ν`.

This composes the two-sided Kolmogorov–Sinai generator theorem
(`ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided`) — discharged with the two-sided
generating property of the time-`0` coordinate partition
(`coordPartitionZFin_isGeneratingTwoSided`) — with the base entropy datum
`ksEntropyPartition_coordPartitionZFin_bernZ_eq`. The required `StandardBorelSpace (BiShift α₀)`
is inferred from the finite-alphabet typeclass context (countable discrete product). -/
theorem ksEntropy_biShiftEquiv_bernZ_eq (ν : Measure α₀) [IsProbabilityMeasure ν] :
    ksEntropy (measurePreserving_biShiftEquiv_bernZ ν) = ((Hnu ν : ℝ) : EReal) := by
  rw [ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided
        (biShiftEquiv (α₀ := α₀)) (measurePreserving_biShiftEquiv_bernZ ν)
        (coordPartitionZFin (bernZ ν)) (coordPartitionZFin_isGeneratingTwoSided ν),
    ksEntropyPartition_coordPartitionZFin_bernZ_eq ν]

end ErgodicTheory.Multifractal
