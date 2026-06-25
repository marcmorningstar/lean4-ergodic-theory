/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.Jacobian
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
open scoped ENNReal

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

/-! ### N5.3 — the per-cell Jacobian–measure identity -/

section Jacobian

variable {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {ι : Type*} [Fintype ι]

/-- **The change-of-variables crux of Rokhlin's formula (per-cell version).**

For an absolutely continuous finite measure `μ ≪ volume` with density `ρ := μ.rnDeriv volume`, a
differentiable self-map `T` with non-vanishing Jacobian on the cell `ξ.cells i`, and an
injectivity partition `ξ`, the measure `μ (ξᵢ ∩ T⁻¹' B)` is recovered as the integral over the
image `T '' ξᵢ ∩ B` of the **per-branch transfer density**
`ρ (g⁻¹ y) / |det Dₓ T|ₓ₌g⁻¹ y`, where `g⁻¹ = Function.invFunOn T (ξ.cells i)` is the branch of the
inverse of `T` on the cell.

The orientation of the density ratio is pinned by the change-of-variables identity itself: writing
`S := ξᵢ ∩ T⁻¹' B`, we have `μ S = ∫_S ρ ∂volume` and, by
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` applied to `T` on `S` with the
transfer density as the integrand, `∫_{T '' S} (transfer) = ∫_S |det DT_x| · (transfer ∘ T)`. On
`S ⊆ ξᵢ` the inverse branch collapses (`invFunOn T ξᵢ (T x) = x`), so the integrand becomes
`|det DT_x| · ρ x / |det DT_x| = ρ x`, recovering `μ S`. The non-vanishing Jacobian hypothesis
`hdet` is exactly what makes this cancellation hold: where `det DT_x = 0` the ratio would undercount
`ρ`, so it cannot be dropped. -/
theorem measure_cell_inter_preimage_eq_setLIntegral_transfer
    (hac : μ ≪ volume) (hdiff : Differentiable ℝ T)
    (ξ : Oseledets.Entropy.MeasurePartition μ ι)
    (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x ∈ ξ.cells i, (fderiv ℝ T x).det ≠ 0)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    μ (ξ.cells i ∩ T ⁻¹' B)
      = ∫⁻ y in T '' ξ.cells i ∩ B,
          (μ.rnDeriv volume) (Function.invFunOn T (ξ.cells i) y)
            / ENNReal.ofReal |(fderiv ℝ T (Function.invFunOn T (ξ.cells i) y)).det| ∂volume := by
  set ρ := μ.rnDeriv volume with hρ
  set f' : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ]
    EuclideanSpace ℝ (Fin d)) := fun x => fderiv ℝ T x with hf'
  -- The branch of the inverse of `T` on the cell `ξ.cells i`.
  set j : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    Function.invFunOn T (ξ.cells i) with hj
  -- The transfer density `g y = ρ (j y) / ofReal |det (f' (j y))|`.
  set g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun y => ρ (j y) / ENNReal.ofReal |(f' (j y)).det| with hg
  -- `S := ξᵢ ∩ T⁻¹' B`, a measurable set.
  have hTmeas : Measurable T := hdiff.continuous.measurable
  have hSmeas : MeasurableSet (ξ.cells i ∩ T ⁻¹' B) := (hξ.meas i).inter (hTmeas hB)
  set S := ξ.cells i ∩ T ⁻¹' B with hS
  -- `HasFDerivWithinAt` of `T` on `S` from differentiability.
  have hHasFD : ∀ x ∈ S, HasFDerivWithinAt T (f' x) S x := fun x _ =>
    (hdiff x).hasFDerivAt.hasFDerivWithinAt
  -- `InjOn T S`, inherited from the cell.
  have hInjS : Set.InjOn T S := (hξ.inj i).mono Set.inter_subset_left
  -- Step 1: `μ S = ∫_S ρ ∂volume`.
  have hstep1 : μ S = ∫⁻ x in S, ρ x ∂volume := by
    conv_lhs => rw [← withDensity_rnDeriv_volume_eq hac]
    rw [withDensity_apply ρ hSmeas]
  -- Step 2: the image of `S` under `T` is `T '' ξᵢ ∩ B`.
  have hstep2 : T '' S = T '' ξ.cells i ∩ B := by
    rw [hS, Set.image_inter_preimage]
  -- Step 3: the change-of-variables formula applied to `T` on `S` with integrand `g`.
  have hcov : ∫⁻ y in T '' S, g y ∂volume
      = ∫⁻ x in S, ENNReal.ofReal |(f' x).det| * g (T x) ∂volume :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hHasFD hInjS g
  -- Step 4: on `S ⊆ ξᵢ` the integrand `ofReal|det DT_x| * g (T x)` collapses to `ρ x`.
  have hcollapse : ∫⁻ x in S, ENNReal.ofReal |(f' x).det| * g (T x) ∂volume
      = ∫⁻ x in S, ρ x ∂volume := by
    refine setLIntegral_congr_fun hSmeas (fun x hx => ?_)
    have hxcell : x ∈ ξ.cells i := Set.inter_subset_left hx
    -- `invFunOn T ξᵢ (T x) = x` by the left-inverse property of `invFunOn` on `ξᵢ`.
    have hjx : j (T x) = x := (hξ.inj i).leftInvOn_invFunOn hxcell
    -- The nonzero, finite ENNReal `ofReal |det DT_x|`.
    have hposR : 0 < |(f' x).det| := abs_pos.mpr (hdet x hxcell)
    have hne0 : ENNReal.ofReal |(f' x).det| ≠ 0 := (ENNReal.ofReal_ne_zero_iff.mpr hposR)
    have hnetop : ENNReal.ofReal |(f' x).det| ≠ ∞ := ENNReal.ofReal_ne_top
    rw [hg]
    simp only [hjx]
    exact ENNReal.mul_div_cancel hne0 hnetop
  -- Assemble: `μ S = ∫_S ρ = ∫_S |det|·(g∘T) = ∫_{T''S} g = ∫_{T''ξᵢ ∩ B} g`.
  rw [hstep1, ← hcollapse, ← hcov, hstep2]

end Jacobian

end Oseledets
