/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.BernoulliEntropy
import Oseledets.Multifractal.BernoulliErgodic

/-!
# The unconditional Bernoulli witness of the symbolic entropy–dimension identity (A7)

The headline `dimH_eq_ksEntropy_div_log_two` (`Oseledets/Multifractal/SymbolicDimension.lean`,
node A6) states, for an *abstract* ergodic shift-invariant probability measure `μ` on the one-sided
full shift `Shift α₀` with **positive** coordinate-partition Kolmogorov–Sinai entropy, that some
full-measure set has Hausdorff dimension `h_μ(σ) / log 2`. Its two standing conditionals —
ergodicity and positive entropy — are exactly what the concrete **biased Bernoulli** measure
supplies:

* ergodicity is `ergodic_shiftMap_bern` (Kolmogorov's 0–1 law, `BernoulliErgodic.lean`);
* the system entropy is the single-symbol Shannon entropy `Hnu ν`
  (`ksEntropy_bern_eq` / `ksEntropyPartition_coordPartition_bern_eq`, `BernoulliEntropy.lean`),
  which is strictly positive once `ν` charges two distinct symbols (`Hnu_pos`).

Discharging both, this file assembles the **unconditional** Bernoulli witness (node A7): for any
biased Bernoulli measure `bern ν` there is a `bern ν`-conull set whose Hausdorff dimension is
exactly `Hnu ν / log 2`. No ergodicity or positive-entropy hypothesis is assumed — only that the
single-symbol law `ν` charges two distinct symbols `i ≠ j` with positive mass, which is what makes
the shift genuinely chaotic. This is the concrete, non-vacuous instance the abstract A5/A6 headlines
pointed
at, and it makes the symbolic entropy = Hausdorff-dimension identity a theorem with **no** standing
conditional for the Bernoulli case.

## Main result

* `Oseledets.Multifractal.dimH_bern_eq_Hnu_div_log_two`: for a biased Bernoulli measure `bern ν`
  (two distinct symbols of positive mass), a `bern ν`-conull set has Hausdorff dimension
  `Hnu ν / log 2` — the unconditional symbolic entropy = dimension identity.
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

namespace Oseledets.Multifractal

open Oseledets.Entropy

variable {α₀ : Type*} [Fintype α₀] [Nonempty α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

-- The `PiNat` ultrametric on the shift (needed to speak of `dimH`) is a *local* instance, exactly
-- as registered in `SymbolicDimension.lean`.
attribute [local instance] PiNat.metricSpace

/-- **A7 (the unconditional Bernoulli entropy = Hausdorff-dimension identity).** For a biased
Bernoulli measure `bern ν` on the one-sided full shift — the i.i.d. product of a single-symbol law
`ν` that charges two *distinct* symbols `i ≠ j` with positive mass — there is a `bern ν`-conull set
`s` whose Hausdorff dimension equals `Hnu ν / log 2`, with `Hnu ν = ∑ a, negMulLog (ν {a}).toReal`
the single-symbol Shannon entropy (which is the system's Kolmogorov–Sinai entropy).

This is the headline `dimH_eq_ksEntropy_div_log_two` (node A6) with **both** of its standing
conditionals discharged for the Bernoulli case: ergodicity of the shift is `ergodic_shiftMap_bern`
(Kolmogorov's 0–1 law) and positivity of the entropy is `Hnu_pos` (the two charged symbols force
`0 < Hnu ν`). The system entropy `ksEntropy` is identified with `Hnu ν` by `ksEntropy_bern_eq`. The
base `log 2` is fixed by the `PiNat` ultrametric. Hence the symbolic entropy = dimension identity
holds for the Bernoulli witness with **no** remaining hypothesis beyond the honest genuine-bias
condition. -/
theorem dimH_bern_eq_Hnu_div_log_two (ν : Measure α₀) [IsProbabilityMeasure ν] {i j : α₀}
    (hij : i ≠ j) (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal) :
    ∃ s : Set (Shift α₀), bern ν sᶜ = 0 ∧
      dimH s = ENNReal.ofReal (Hnu ν / Real.log 2) := by
  -- Ergodicity (Kolmogorov 0–1) discharges the first conditional.
  have hσ := ergodic_shiftMap_bern ν
  -- Positive entropy discharges the second: `ksEntropyPartition (coordPartition) = Hnu ν > 0`.
  have hpos : 0 < ksEntropyPartition hσ.toMeasurePreserving (coordPartition (bern ν)) := by
    have hE : ksEntropyPartition hσ.toMeasurePreserving (coordPartition (bern ν)) = Hnu ν :=
      ksEntropyPartition_coordPartition_bern_eq ν
    rw [hE]
    exact Hnu_pos ν hij hi hj
  -- The abstract A6 headline now applies unconditionally.
  obtain ⟨s, hconull, hdim⟩ := dimH_eq_ksEntropy_div_log_two hσ hpos
  refine ⟨s, hconull, ?_⟩
  -- The system entropy `ksEntropy` is the single-symbol Shannon entropy `Hnu ν`.
  have hkse : (Oseledets.Entropy.ksEntropy hσ.toMeasurePreserving).toReal = Hnu ν :=
    ksEntropy_bern_eq ν
  rw [hdim, hkse]

end Oseledets.Multifractal
