/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Oseledets.Entropy.Partition

/-!
# Foundation for Rokhlin's formula for an expanding map

This module freezes the **interface** on which the proof of Rokhlin's entropy formula
`h_μ(T, ξ) = ∫ log |det Dₓ T| dμ` for an absolutely continuous, uniformly expanding self-map
`T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)` rests. It contains two small,
near-trivial pieces that later (harder) nodes consume verbatim, so the signatures here are
chosen to match exactly the hypotheses those nodes need.

## The absolutely-continuous density layer

When `μ ≪ volume` (and `μ` is finite, hence has a Lebesgue decomposition w.r.t. `volume`), the
Radon–Nikodym density `ρ := μ.rnDeriv volume` recovers `μ` as `volume.withDensity ρ`, and `ρ` is
strictly positive `μ`-almost everywhere. These are thin wrappers over
`MeasureTheory.Measure.withDensity_rnDeriv_eq` and `MeasureTheory.Measure.rnDeriv_pos`.

We deliberately do **not** record any `log ρ ∈ L¹` integrability statement here: the `C¹`
absolutely continuous case can fail it, so log-density integrability is carried as a separate
hypothesis by the later nodes.

## The injectivity-partition predicate

`IsInjectivityPartition μ T ξ` packages the three hypotheses Coudène's conditional-expectation
proof of Rokhlin's formula needs from a finite measurable partition `ξ`:

* `T` is injective on each cell (`Set.InjOn`),
* each cell is measurable (`MeasurableSet`),
* the union of the cell frontiers is `μ`-null.

The first two fields are **literally** the hypotheses `hf` and `hs` of Mathlib's change-of-
variables lemma `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`, which the next
node feeds them into. We deliberately do **not** include a Markov condition (`T '' ξᵢ` a union of
cells) — the conditional-expectation argument needs only injectivity — and we do **not** bake in
`IsGenerating`, which is a separate hypothesis of the final formula.

## Main definitions

* `Oseledets.IsInjectivityPartition` — the injectivity/measurability/null-boundary predicate on a
  finite measurable partition.

## Main results

* `Oseledets.withDensity_rnDeriv_volume_eq` — `volume.withDensity (μ.rnDeriv volume) = μ` for an
  absolutely continuous finite measure.
* `Oseledets.rnDeriv_volume_pos` — the Radon–Nikodym density is `μ`-a.e. strictly positive.
-/

open MeasureTheory Function

namespace Oseledets

/-! ### N5.1 — the absolutely-continuous density layer -/

section Density

variable {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ]

/-- For a finite measure `μ` absolutely continuous w.r.t. Lebesgue `volume`, the
Radon–Nikodym density `ρ := μ.rnDeriv volume` recovers `μ`:
`volume.withDensity (μ.rnDeriv volume) = μ`. A thin wrapper over
`MeasureTheory.Measure.withDensity_rnDeriv_eq` (`μ` is finite, hence has a Lebesgue
decomposition w.r.t. `volume`). -/
lemma withDensity_rnDeriv_volume_eq (hac : μ ≪ volume) :
    volume.withDensity (μ.rnDeriv volume) = μ :=
  Measure.withDensity_rnDeriv_eq μ volume hac

/-- The Radon–Nikodym density `μ.rnDeriv volume` of an absolutely continuous finite measure is
strictly positive `μ`-almost everywhere. A thin wrapper over
`MeasureTheory.Measure.rnDeriv_pos`. -/
lemma rnDeriv_volume_pos (hac : μ ≪ volume) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv volume x :=
  Measure.rnDeriv_pos hac

end Density

/-! ### N5.2 — the injectivity-partition predicate -/

/-- An **injectivity partition** for a self-map `T` and a finite measurable partition `ξ`:
the three hypotheses Coudène's conditional-expectation proof of Rokhlin's formula needs.

* `inj` : `T` is injective on each cell `ξ.cells i`;
* `meas` : each cell is measurable;
* `boundaryNull` : the union of the cell frontiers is `μ`-null.

The `inj` and `meas` fields are exactly the hypotheses (`hf`, `hs`) consumed by Mathlib's
change-of-variables lemma `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`. No
Markov condition and no `IsGenerating` hypothesis are included here. -/
structure IsInjectivityPartition {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {ι : Type*} [Fintype ι] (ξ : Oseledets.Entropy.MeasurePartition μ ι) : Prop where
  /-- `T` is injective on each cell of the partition. -/
  inj : ∀ i, Set.InjOn T (ξ.cells i)
  /-- Each cell of the partition is measurable. -/
  meas : ∀ i, MeasurableSet (ξ.cells i)
  /-- The union of the cell frontiers is `μ`-null. -/
  boundaryNull : μ (⋃ i, frontier (ξ.cells i)) = 0

namespace IsInjectivityPartition

variable {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {ι : Type*} [Fintype ι] {ξ : Oseledets.Entropy.MeasurePartition μ ι}

/-- Each individual cell frontier is `μ`-null, extracted from `boundaryNull` via monotonicity. -/
lemma frontier_null (h : IsInjectivityPartition μ T ξ) (i : ι) :
    μ (frontier (ξ.cells i)) = 0 :=
  measure_mono_null (Set.subset_iUnion (fun j => frontier (ξ.cells j)) i) h.boundaryNull

end IsInjectivityPartition

end Oseledets
