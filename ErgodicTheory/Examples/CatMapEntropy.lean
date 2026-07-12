/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapEntropyLower
import ErgodicTheory.Examples.CatMapAdlerWeissGenerator
import ErgodicTheory.Examples.CatMapAdlerWeissCount
import ErgodicTheory.Entropy.GeneratorTheoremTwoSided

/-!
# The sharp Kolmogorov–Sinai entropy of the Arnold cat map

This is the **assembly module** for the entropy half of issue #52.  It closes the two-sided
computation of the Kolmogorov–Sinai entropy of the Arnold cat map `catTorus` (the hyperbolic toral
automorphism induced by `[[2,1],[1,1]]`), pinning it to the logarithm of the expanding eigenvalue:

`h(catTorus) = log λ₊ = log((3 + √5)/2)`,   `λ₊ = φ² = (3 + √5)/2`.

This is the entropy statement of the **Adler–Weiss** classification of ergodic toral automorphisms
(R. L. Adler and B. Weiss, *Entropy, a complete metric invariant for automorphisms of the torus*,
Proc. Nat. Acad. Sci. USA **57** (1967) 1573–1576) together with Sinai's identification of the
metric entropy of a hyperbolic automorphism with the sum of its positive Lyapunov exponents.

## Route

The two inequalities are proved by structurally different geometric mechanisms, then glued by
`le_antisymm`:

* **Lower bound** `log λ₊ ≤ h(catTorus)` (`catTorus_ksEntropy_ge`, in
  `ErgodicTheory.Examples.CatMapEntropyLower`): the `5 × 5` grid partition, the eigencoordinate
  telescoping slab, and the wall lemma bound every atom of the forward grid join by `(9√5/25)·λ·μⁿ`,
  forcing the atom count — and hence the entropy — to grow at least like `λ₊ⁿ`.
* **Upper bound** `h(catTorus) ≤ log λ₊` (`catTorus_ksEntropy_le`, here): the explicit golden
  **two-box Markov partition** `catAWPartition` is a *two-sided generator*
  (`isGeneratingTwoSided_catAWPartition`), so the two-sided Kolmogorov–Sinai generator theorem
  `Entropy.ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided` reduces `h(catTorus)` to the
  partition-relative entropy `h(catTorus, catAWPartition)`, which the transfer-matrix count of
  admissible golden itineraries bounds by `log λ₊` (`catAW_ksEntropyPartition_le`).

## Main results

* `ErgodicTheory.CatMapToral.catTorus_ksEntropy_le` — `h(catTorus) ≤ log((3 + √5)/2)`.
* `ErgodicTheory.CatMapToral.catTorus_ksEntropy_eq` — **the crown**:
  `h(catTorus) = log((3 + √5)/2)`.
-/

open MeasureTheory Matrix Function Filter

noncomputable section

/-- Normalise the circle measure to total mass `1`, matching the imported cat-map measure modules so
that `volume : Measure T2` lines up with `catAWPartition` and `measurePreserving_catTorus`. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catEnt :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catEnt :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catEnt :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- **Upper bound on the cat-map Kolmogorov–Sinai entropy** (unconditional):
`h(catTorus) ≤ log((3 + √5)/2)`.

The Adler–Weiss golden partition `catAWPartition` is a two-sided generator
(`isGeneratingTwoSided_catAWPartition`), so the two-sided Kolmogorov–Sinai generator theorem
collapses the system entropy `h(catTorus)` to the partition-relative entropy
`h(catTorus, catAWPartition)`, which the admissible-itinerary transfer-matrix count bounds by
`log λ₊` (`catAW_ksEntropyPartition_le`).  The measurable-equivalence packaging `catTorusEquiv`
coerces definitionally to `catTorus`, so the generator theorem (stated for `α ≃ᵐ α`) applies. -/
theorem catTorus_ksEntropy_le :
    Entropy.ksEntropy measurePreserving_catTorus ≤
      ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal) := by
  have hgen := Entropy.ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided
    catTorusEquiv measurePreserving_catTorusEquiv catAWPartition
    isGeneratingTwoSided_catAWPartition
  calc Entropy.ksEntropy measurePreserving_catTorus
      = Entropy.ksEntropy measurePreserving_catTorusEquiv := rfl
    _ = ((Entropy.ksEntropyPartition measurePreserving_catTorusEquiv catAWPartition : ℝ) : EReal) :=
        hgen
    _ ≤ ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr catAW_ksEntropyPartition_le

/-- **THE CROWN — the sharp Kolmogorov–Sinai entropy of the Arnold cat map** (unconditional):
`h(catTorus) = log((3 + √5)/2) = log λ₊`.

`le_antisymm` of the Adler–Weiss generator upper bound `catTorus_ksEntropy_le` and the grid-slab
lower bound `catTorus_ksEntropy_ge`.  This is the entropy statement of the Adler–Weiss
classification of ergodic toral automorphisms and Sinai's sum-of-positive-Lyapunov-exponents
formula in the `2 × 2` hyperbolic case. -/
theorem catTorus_ksEntropy_eq :
    Entropy.ksEntropy measurePreserving_catTorus =
      ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal) :=
  le_antisymm catTorus_ksEntropy_le catTorus_ksEntropy_ge

end ErgodicTheory.CatMapToral

end
