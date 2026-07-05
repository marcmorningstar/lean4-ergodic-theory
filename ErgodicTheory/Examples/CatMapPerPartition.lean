/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapToral
import ErgodicTheory.Entropy.Ruelle.Crude

/-!
# The per-partition Ruelle bound for the genuine Arnold cat map

This module instantiates the unconditional arithmetic backbone of the Margulis–Ruelle inequality
`ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth` on the **genuine** Arnold cat map
`catTorus : 𝕋² → 𝕋²` (`ErgodicTheory/Examples/CatMapToral.lean`, the hyperbolic toral automorphism with
matrix `M = !![2,1;1,1]`), at the exact rate `log λ₊ = log((3 + √5)/2)`.

It is the cat-map analogue of the already-shipped doubling-map per-partition theorem
`ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp`
(`ErgodicTheory/Examples/RuelleDoubling.lean`): same base-space-polymorphic backbone, same honest
status for the single genuinely-geometric input (the Ruelle atom-count growth), here over the
genuine toral dynamics instead of the doubling map.

## What is the rate, and why it is the genuine top exponent

The rate `log((3 + √5)/2)` is **the genuine top Lyapunov exponent `λ₊` of the cat map**:
`(3 + √5)/2` is the larger eigenvalue of `M = !![2,1;1,1]`, and the sibling module
`ErgodicTheory/Examples/CatMapDerivativeCocycle.lean` proves — fully sorry-free — that the top Lyapunov
exponent of the **genuine Fréchet-derivative cocycle** of the cat map's ℝ²-linear lift `catLift`,
realized over the genuine ergodic base `catTorus`, is exactly `log((3 + √5)/2) > 0`
(`ErgodicTheory.CatMapToral.catLift_derivativeCocycle_topExponent_pos`). So the rate appearing here is
not an abstract constant: it is the actual Lyapunov datum of the cat map, with an independent honest
proof in the repo.

## What is discharged here, and what stays an honest input

`catTorus_ksEntropyPartition_le_logLambda` is a **thin specialization** of the unconditional
backbone `ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth` at the rate
`R = log((3 + √5)/2)`,
over the genuine ergodic toral base via `ErgodicTheory.CatMapToral.measurePreserving_catTorus`. There is
**no** hidden geometric content beyond the two explicit, named hypotheses:

* `hC : 1 ≤ C` — the constant in the atom-count bound;
* `hgrow` — the genuinely geometric **Ruelle atom-count growth bound**: the `n`-fold refinement
  `⋁ₖ₌₀ⁿ⁻¹ catTorus⁻ᵏ P` has eventually at most `C · exp(n · log λ₊)` non-empty atoms. This is the
  exact honest status the geometric input carries in `ErgodicTheory.Entropy.Ruelle.Crude` and in the
  doubling-map theorem `ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp` (whose binary
  instance makes `hgrow` automatic; here, as there, the bound is supplied as the named datum).

The conclusion is the **per-partition** bound `h(α, catTorus) ≤ log λ₊` for a *single* partition
`α`, **not** the system Margulis–Ruelle inequality `h(catTorus) ≤ λ₊`.

## The system-level sharp equality is a documented wall

The sharp system equality `h_μ(catTorus) = log λ₊` (the cat-map Pesin/Ledrappier–Young formula) is
**not** proved here and is a genuine wall:

* **Upper-bound, system level.** The bridge from the per-partition bound to the *system* entropy is
  the Kolmogorov–Sinai generator identity `h(T) = h(α, T)` for a generating partition `α`, which is
  fully proved in the repo as `ErgodicTheory.Entropy.ksEntropy_eq_ksEntropyPartition_of_generating`
  (`ErgodicTheory/Entropy/GeneratorTheorem.lean`). So a system-level upper bound `h(catTorus) ≤ log λ₊`
  is *one* `IsGenerating volume catTorus P` hypothesis away — and *that* hypothesis is exactly the
  deferred Adler–Weiss Markov-partition / SFT construction (a finite generating partition for the
  cat map), which Mathlib lacks.

* **Lower bound.** The matching lower bound `h_μ ≥ log λ₊` needs the Margulis–Ruelle/Pesin machinery
  in the differentiable setting; the repo's Margulis–Ruelle infrastructure is
  `EuclideanSpace`-typed, and `derivativeCocycle catTorus` is ill-typed on the torus manifold (no
  `mfderiv` API for `AddCircle` endomorphisms — see `CatMapDerivativeCocycle`'s Grade-2b note), so
  the sharp lower bound additionally requires the general singular Ledrappier–Young theorem (the #10
  Pesin/SRB wall). None of this is attempted here.

## Main results

* `ErgodicTheory.CatMapToral.log_lambda_cat_pos` — positivity of the rate: `0 < log((3 + √5)/2)`
  (hyperbolicity, `(3 + √5)/2 > 1`).
* `ErgodicTheory.CatMapToral.catTorus_ksEntropyPartition_le_logLambda` — the **per-partition** Ruelle
  bound `h(α, catTorus) ≤ log((3 + √5)/2) = log λ₊` for the genuine cat map, from the genuine
  Ruelle atom-count growth `hgrow` at rate `log λ₊`.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Filter Topology

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `ErgodicTheory/Examples/CatMapToral.lean` so that the ambient
`volume : Measure T2` here is *the same* product Haar probability measure for which
`measurePreserving_catTorus` is stated.  (Importing `ErgodicTheory/Examples/Elementary.lean`, which uses
the default `AddCircle.measureSpace 1`, would make `volume : Measure T2` ambiguous — hence we
re-establish exactly these instances and route everything through `measurePreserving_catTorus`.) -/
noncomputable local instance instMeasureSpaceUnitAddCircleCatPerPartition :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureUnitAddCircleCatPerPartition :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureUnitAddCircleCatPerPartition :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- **The cat-map rate is positive: `0 < log((3 + √5)/2)`.**  This is the hyperbolicity of the
Arnold cat map: the larger eigenvalue `(3 + √5)/2` of `M = !![2,1;1,1]` exceeds `1` (since
`√5 ≥ 0`), so its logarithm is positive.  It is `log λ₊`, the genuine top Lyapunov exponent
(`catLift_derivativeCocycle_topExponent_pos`). -/
theorem log_lambda_cat_pos : 0 < Real.log ((3 + Real.sqrt 5) / 2) := by
  apply Real.log_pos
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  linarith

/-- **The per-partition Ruelle bound for the genuine Arnold cat map.**

For any finite measurable partition `P` of the 2-torus `𝕋²` whose `n`-fold refinement
`⋁ₖ₌₀ⁿ⁻¹ catTorus⁻ᵏ P` under the genuine cat map has eventually at most `C · exp(n · log λ₊)`
non-empty atoms (`hgrow`, with `C ≥ 1`), the Kolmogorov–Sinai entropy *relative to that single
partition* is bounded by the top Lyapunov exponent `log λ₊ = log((3 + √5)/2)`:

`h(α, catTorus) ≤ log((3 + √5)/2)`.

This is the **per-partition** Ruelle bound, **not** the system inequality `h(catTorus) ≤ log λ₊`
(the bridge to the system entropy is the generator identity
`ErgodicTheory.Entropy.ksEntropy_eq_ksEntropyPartition_of_generating`, fully proved in the repo, applied
under an `IsGenerating volume catTorus P` hypothesis — the deferred Adler–Weiss Markov-partition
datum). The rate `log((3 + √5)/2)` is the *genuine top Lyapunov exponent* of the cat map
(`ErgodicTheory.CatMapToral.catLift_derivativeCocycle_topExponent_pos`), not an abstract constant.

The atom-count growth `hgrow` is the genuinely geometric Ruelle input, left as an honest named
hypothesis exactly as in `ErgodicTheory.Entropy.Ruelle.Crude` and in the doubling-map theorem
`ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp`. The reduction itself is the unconditional
arithmetic backbone `ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth`; this theorem adds
no hidden content beyond `hC` and `hgrow`. -/
theorem catTorus_ksEntropyPartition_le_logLambda {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : Entropy.MeasurePartition (volume : Measure T2) ι) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ᶠ n : ℕ in atTop,
      (Entropy.atomCount measurePreserving_catTorus P n : ℝ)
        ≤ C * Real.exp (n * Real.log ((3 + Real.sqrt 5) / 2))) :
    Entropy.ksEntropyPartition measurePreserving_catTorus P
      ≤ Real.log ((3 + Real.sqrt 5) / 2) :=
  Entropy.ksEntropyPartition_le_of_atomCount_growth measurePreserving_catTorus P hC hgrow

end ErgodicTheory.CatMapToral
