/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.Jacobian
import ErgodicTheory.Entropy.Partition
import ErgodicTheory.Entropy.CondPartition
import ErgodicTheory.Entropy.GeneratorTheorem
import ErgodicTheory.Entropy.JoinSigmaAlgebra
import ErgodicTheory.Krieger.SMBSharp
import ErgodicTheory.Smooth.Expanding

/-!
# Rokhlin's and Pesin's entropy formula for an expanding map

This module proves **Rokhlin's entropy formula**
`h_μ(T, ξ) = ∫ log |det Dₓ T| dμ` for an absolutely continuous, uniformly expanding self-map
`T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)`, and — chaining it with the
Kolmogorov–Sinai generator theorem and the exponent-sum identity — the corresponding **Pesin
entropy formula** `h_μ(T) = ∑ λ⁺`. It builds up through the nodes N5.1–N5.5: an
absolutely-continuous density layer (N5.1), the injectivity-partition predicate (N5.2), the per-cell
Jacobian–measure identity (N5.3), the conditional-entropy = Jacobian-integral identity (N5.4), and
their assembly into the per-partition formula (N5.5) and the unconditional Pesin formula.

The two lowest layers (N5.1/N5.2) are small, near-trivial pieces whose signatures are chosen to
match exactly the hypotheses the harder nodes consume; they are documented in the two subsections
below.

## The absolutely-continuous density layer

When `μ ≪ volume` (and `μ` is finite, hence has a Lebesgue decomposition w.r.t. `volume`), the
Radon–Nikodym density `ρ := μ.rnDeriv volume` recovers `μ` as `volume.withDensity ρ`, and `ρ` is
strictly positive `μ`-almost everywhere. These are thin wrappers over
`MeasureTheory.Measure.withDensity_rnDeriv_eq` and `MeasureTheory.Measure.rnDeriv_pos`.

We deliberately do **not** record any `log ρ ∈ L¹` integrability statement here: the `C¹`
absolutely continuous case can fail it, so log-density integrability is carried as a separate
hypothesis by the later nodes.

## The injectivity-partition predicate

`IsInjectivityPartition μ T ξ` packages the two hypotheses Coudène's conditional-expectation
proof of Rokhlin's formula needs from a finite measurable partition `ξ`:

* `T` is injective on each cell (`Set.InjOn`),
* each cell is measurable (`MeasurableSet`).

The two fields are **literally** the hypotheses `hf` and `hs` of Mathlib's change-of-
variables lemma `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`, which the next
node feeds them into. We deliberately do **not** include a Markov condition (`T '' ξᵢ` a union of
cells) — the conditional-expectation argument needs only injectivity — and we do **not** bake in
`IsGenerating`, which is a separate hypothesis of the final formula.

## Main definitions

* `ErgodicTheory.IsInjectivityPartition` — the injectivity/measurability predicate on a
  finite measurable partition.

## Main results

* `ErgodicTheory.withDensity_rnDeriv_volume_eq` — `volume.withDensity (μ.rnDeriv volume) = μ` for an
  absolutely continuous finite measure (N5.1).
* `ErgodicTheory.rnDeriv_volume_pos` — the Radon–Nikodym density is `μ`-a.e. strictly positive (N5.1).
* `ErgodicTheory.measure_cell_inter_preimage_eq_setLIntegral_transfer` (N5.3) — the per-cell
  change-of-variables identity recovering `μ (ξᵢ ∩ T⁻¹' B)` from the branch transfer density.
* `ErgodicTheory.condEntropy_comap_eq_integral_log_abs_det` (N5.4) — the partition-independent
  identity `H(ξ | comap T mα) = ∫ log|det DT| dμ` (Coudène Prop 12.1).
* `ErgodicTheory.ksEntropyPartition_eq_integral_log_abs_det` (N5.5) — the per-partition Rokhlin formula
  `h(T, ξ) = ∫ log|det DT| dμ` for a generating injectivity partition.
* `ErgodicTheory.pesin_formula_expanding` — the unconditional expanding-map Pesin formula
  `h_μ(T) = ∑ λ⁺ = ∫ log|det DT| dμ`. A correct implication that is **vacuous on `EuclideanSpace`**
  (see its docstring); the instantiated equality lives on the compact circle.
-/

open MeasureTheory Function
open scoped ENNReal

namespace ErgodicTheory

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
the two hypotheses Coudène's conditional-expectation proof of Rokhlin's formula needs.

* `inj` : `T` is injective on each cell `ξ.cells i`;
* `meas` : each cell is measurable.

The `inj` and `meas` fields are exactly the hypotheses (`hf`, `hs`) consumed by Mathlib's
change-of-variables lemma `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`. No
Markov condition and no `IsGenerating` hypothesis are included here. -/
structure IsInjectivityPartition {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {ι : Type*} [Fintype ι] (ξ : ErgodicTheory.Entropy.MeasurePartition μ ι) : Prop where
  /-- `T` is injective on each cell of the partition. -/
  inj : ∀ i, Set.InjOn T (ξ.cells i)
  /-- Each cell of the partition is measurable. -/
  meas : ∀ i, MeasurableSet (ξ.cells i)

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
    (ξ : ErgodicTheory.Entropy.MeasurePartition μ ι)
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

/-! ### N5.4 — the conditional-entropy = Jacobian-integral identity (Coudène Prop 12.1) -/

section CondEntropyJacobian

open ErgodicTheory.Entropy ProbabilityTheory MeasurableSpace

variable {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {ι : Type*} [Fintype ι] {ξ : ErgodicTheory.Entropy.MeasurePartition μ ι}

/-- The **per-branch transfer density** on the cell `ξ.cells i`:
`transferDensity ξ i T y = ρ(branchᵢ y) / ofReal|det DT(branchᵢ y)|`, where `branchᵢ = invFunOn T
(ξ.cells i)` is the inverse branch of `T` on the cell. This is the integrand of N5.3. -/
noncomputable def transferDensity (ξ : ErgodicTheory.Entropy.MeasurePartition μ ι)
    (i : ι) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  (μ.rnDeriv volume) (Function.invFunOn T (ξ.cells i) y)
    / ENNReal.ofReal |(fderiv ℝ T (Function.invFunOn T (ξ.cells i) y)).det|

/-- The **per-image branch weight** `wᵢ y = (T''ξᵢ).indicator (transferDensity / ρ) y`. On the
image `T''ξᵢ` it is the relative weight of the `i`-th preimage branch; off it, `0`. Postcomposed
with `T` this is the candidate for the conditional probability `E(1_{ξᵢ}|comap T mα)`. -/
noncomputable def branchWeight (ξ : ErgodicTheory.Entropy.MeasurePartition μ ι)
    (i : ι) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  (T '' ξ.cells i).indicator (fun y => transferDensity ξ i T y / (μ.rnDeriv volume) y) y

omit [IsProbabilityMeasure μ] in
/-- The inner density `a ↦ ρ a / ofReal|det DT a|` is measurable: a quotient of the measurable
Radon–Nikodym density by the measurable determinant data. -/
lemma measurable_innerDensity :
    Measurable (fun a : EuclideanSpace ℝ (Fin d) =>
      (μ.rnDeriv volume) a / ENNReal.ofReal |(fderiv ℝ T a).det|) := by
  refine (Measure.measurable_rnDeriv μ volume).div (ENNReal.measurable_ofReal.comp ?_)
  exact (continuous_abs.measurable).comp
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ T))

omit [IsProbabilityMeasure μ] in
/-- The image cell `T '' ξ.cells i` is measurable: `T` is continuous and injective on the
measurable cell `ξ.cells i`, so the image is Borel by the Lusin–Souslin theorem
(`MeasurableSet.image_of_continuousOn_injOn`). -/
lemma measurableSet_image_cell (hdiff : Differentiable ℝ T)
    (hξ : IsInjectivityPartition μ T ξ) (i : ι) :
    MeasurableSet (T '' ξ.cells i) :=
  (hξ.meas i).image_of_continuousOn_injOn hdiff.continuous.continuousOn (hξ.inj i)

omit [IsProbabilityMeasure μ] in
/-- On the image cell `T '' ξ.cells i`, the `transferDensity` agrees with the measurable extension
`Function.extend (ξᵢ.restrict T) (a ↦ ρ a / ofReal|det DT a|) 0`: the embedding
`e = ξᵢ.restrict T` is injective and hits `y` at the subtype point `⟨invFunOn T ξᵢ y, _⟩`, so
`extend` evaluates the inner density at that preimage — exactly the transfer integrand. -/
lemma transferDensity_eq_extend
    (hξ : IsInjectivityPartition μ T ξ) (i : ι) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ T '' ξ.cells i) :
    transferDensity ξ i T y
      = Function.extend ((ξ.cells i).restrict T)
          (fun a => (μ.rnDeriv volume) (a : EuclideanSpace ℝ (Fin d))
            / ENNReal.ofReal |(fderiv ℝ T (a : EuclideanSpace ℝ (Fin d))).det|) 0 y := by
  -- The preimage branch lands back in the cell, with `T (branch y) = y`.
  have hmem : Function.invFunOn T (ξ.cells i) y ∈ ξ.cells i := Function.invFunOn_mem hy
  have hTbranch : T (Function.invFunOn T (ξ.cells i) y) = y := Function.invFunOn_eq hy
  have hinj : Function.Injective ((ξ.cells i).restrict T) := (Set.injOn_iff_injective.1 (hξ.inj i))
  -- `y = e ⟨branch y, hmem⟩`, so `extend e g 0 y = g ⟨branch y, hmem⟩` (defeq to transferDensity).
  have hye : ((ξ.cells i).restrict T) ⟨Function.invFunOn T (ξ.cells i) y, hmem⟩ = y := by
    rw [Set.restrict_apply]; exact hTbranch
  conv_rhs => rw [← hye, hinj.extend_apply]
  rfl

omit [IsProbabilityMeasure μ] in
/-- `branchWeight` is measurable: it is the indicator on the (measurable) image cell of the
quotient of the measurable extension of the transfer integrand by the density `ρ`. -/
lemma measurable_branchWeight (hdiff : Differentiable ℝ T)
    (hξ : IsInjectivityPartition μ T ξ) (i : ι) :
    Measurable (branchWeight ξ i T) := by
  -- The measurable embedding `e = ξᵢ.restrict T` and the measurable extension of the integrand.
  have hemb : MeasurableEmbedding ((ξ.cells i).restrict T) :=
    ContinuousOn.measurableEmbedding (hξ.meas i) hdiff.continuous.continuousOn (hξ.inj i)
  have hext : Measurable
      (Function.extend ((ξ.cells i).restrict T)
        (fun a => (μ.rnDeriv volume) (a : EuclideanSpace ℝ (Fin d))
          / ENNReal.ofReal |(fderiv ℝ T (a : EuclideanSpace ℝ (Fin d))).det|) 0) :=
    hemb.measurable_extend (measurable_innerDensity.comp measurable_subtype_coe)
      measurable_zero
  -- Rewrite `branchWeight` as the indicator of the measurable `hext / ρ`: on `T''ξᵢ` the numerator
  -- `transferDensity` equals `hext`, and the indicator zeroes everything off `T''ξᵢ`.
  have heq : branchWeight ξ i T
      = (T '' ξ.cells i).indicator
          (fun y => Function.extend ((ξ.cells i).restrict T)
            (fun a => (μ.rnDeriv volume) (a : EuclideanSpace ℝ (Fin d))
              / ENNReal.ofReal |(fderiv ℝ T (a : EuclideanSpace ℝ (Fin d))).det|) 0 y
            / (μ.rnDeriv volume) y) := by
    funext y
    rw [branchWeight]
    by_cases hy : y ∈ T '' ξ.cells i
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
        transferDensity_eq_extend hξ i hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  rw [heq]
  exact Measurable.indicator (hext.div (Measure.measurable_rnDeriv μ volume))
    (measurableSet_image_cell hdiff hξ i)

/-- The set `{ρ = 0}` carries no `μ`-mass: `μ {ρ = 0} = ∫⁻_{ρ=0} ρ ∂volume = 0`, since `ρ = 0`
on that set and `μ = volume.withDensity ρ`. -/
lemma measure_rnDeriv_eq_zero (hac : μ ≪ volume) :
    μ {y | (μ.rnDeriv volume) y = 0} = 0 := by
  set ρ := μ.rnDeriv volume with hρ
  have hms : MeasurableSet {y | ρ y = 0} :=
    (Measure.measurable_rnDeriv μ volume) (measurableSet_singleton 0)
  have hμwd : μ = volume.withDensity ρ := (withDensity_rnDeriv_volume_eq hac).symm
  rw [hμwd, withDensity_apply ρ hms]
  exact setLIntegral_eq_zero hms (fun y hy => hy)

/-- **The heart sub-lemma (N5.4 core change of variables).** For a measurable set `B`, the
`μ`-integral of the per-image branch weight over `B` recovers the measure of the slice of the
`i`-th cell that maps into `B`:
`∫⁻ y in B, branchWeight ξ i T y ∂μ = μ (ξ.cells i ∩ T⁻¹' B)`.

Route: rewrite the `μ`-integral as a `volume`-integral of `ρ · branchWeight`
(`setLIntegral_rnDeriv_mul`); on the image cell `ρ · branchWeight = transferDensity` `volume`-a.e.
(the density ratio `ρ · (transfer / ρ)` collapses where `0 < ρ < ∞`, and the discarded `{ρ = 0}`
part carries no transfer mass by N5.3 applied to `{ρ = 0}`, while `{ρ = ∞}` is `volume`-null);
finally `∫⁻_{T''ξᵢ ∩ B} transferDensity = μ (ξᵢ ∩ T⁻¹B)` is exactly N5.3. -/
lemma branchWeight_setLIntegral_eq (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    ∫⁻ y in B, branchWeight ξ i T y ∂μ = μ (ξ.cells i ∩ T ⁻¹' B) := by
  set ρ := μ.rnDeriv volume with hρ
  have hcellMeas : MeasurableSet (T '' ξ.cells i) := measurableSet_image_cell hdiff hξ i
  have hrho0Meas : MeasurableSet {y | ρ y = 0} :=
    (Measure.measurable_rnDeriv μ volume) (measurableSet_singleton 0)
  -- Step A: `∫⁻_B branchWeight dμ = ∫⁻_B ρ · branchWeight dvolume`.
  rw [← setLIntegral_rnDeriv_mul hac (measurable_branchWeight hdiff hξ i).aemeasurable hB]
  -- `transferDensity` is `volume`-a.e. `0` on `T''ξᵢ ∩ {ρ = 0}` (N5.3 with `B := {ρ = 0}`).
  have hzeroInt :
      ∫⁻ y in T '' ξ.cells i ∩ {y | ρ y = 0}, transferDensity ξ i T y ∂volume = 0 := by
    have h53 := measure_cell_inter_preimage_eq_setLIntegral_transfer hac hdiff ξ hξ i
      (fun x _ => hdet x) hrho0Meas
    have hle : μ (ξ.cells i ∩ T ⁻¹' {y | ρ y = 0}) = 0 := by
      refine measure_mono_null Set.inter_subset_right ?_
      rw [hT.measure_preimage hrho0Meas.nullMeasurableSet]
      exact measure_rnDeriv_eq_zero hac
    rw [hle] at h53; exact h53.symm
  -- `transferDensity` is `AEMeasurable` on `T''ξᵢ` (equals the measurable extension there).
  have htransAEmeas : AEMeasurable (transferDensity ξ i T) (volume.restrict (T '' ξ.cells i)) := by
    have hemb : MeasurableEmbedding ((ξ.cells i).restrict T) :=
      ContinuousOn.measurableEmbedding (hξ.meas i) hdiff.continuous.continuousOn (hξ.inj i)
    have hext : Measurable
        (Function.extend ((ξ.cells i).restrict T)
          (fun a => (μ.rnDeriv volume) (a : EuclideanSpace ℝ (Fin d))
            / ENNReal.ofReal |(fderiv ℝ T (a : EuclideanSpace ℝ (Fin d))).det|) 0) :=
      hemb.measurable_extend (measurable_innerDensity.comp measurable_subtype_coe)
        measurable_zero
    refine ⟨_, hext, ?_⟩
    rw [Filter.EventuallyEq, ae_restrict_iff' hcellMeas]
    exact Filter.Eventually.of_forall fun y hy => transferDensity_eq_extend hξ i hy
  -- Hence `transferDensity =ᵐ 0` on `T''ξᵢ ∩ {ρ = 0}`.
  have htransAEzero :
      ∀ᵐ y ∂volume, y ∈ T '' ξ.cells i → ρ y = 0 → transferDensity ξ i T y = 0 := by
    have hsub : AEMeasurable (transferDensity ξ i T)
        (volume.restrict (T '' ξ.cells i ∩ {y | ρ y = 0})) :=
      htransAEmeas.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hz := (setLIntegral_eq_zero_iff' (hcellMeas.inter hrho0Meas) hsub).mp hzeroInt
    filter_upwards [hz] with y hy hyc hyr
    exact hy ⟨hyc, hyr⟩
  -- Step B: `ρ · branchWeight =ᵐ[volume] (T''ξᵢ).indicator transferDensity`.
  have hfin : ∀ᵐ y ∂volume, ρ y ≠ ∞ := Measure.rnDeriv_ne_top μ volume
  have hae : (fun y => ρ y * branchWeight ξ i T y)
      =ᵐ[volume] (T '' ξ.cells i).indicator (transferDensity ξ i T) := by
    filter_upwards [hfin, htransAEzero] with y hyfin hyzero
    by_cases hy : y ∈ T '' ξ.cells i
    · rw [branchWeight, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      exact ENNReal.mul_div_cancel' (fun h0 => hyzero hy h0) (fun htop => absurd htop hyfin)
    · rw [branchWeight, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  -- Assemble: a.e. rewrite, indicator restriction, then N5.3.
  rw [lintegral_congr_ae (ae_restrict_of_ae hae), setLIntegral_indicator hcellMeas]
  -- `∫⁻_{T''ξᵢ ∩ B} transferDensity = μ (ξᵢ ∩ T⁻¹B)` is exactly N5.3 (defeq integrand).
  exact (measure_cell_inter_preimage_eq_setLIntegral_transfer
    hac hdiff ξ hξ i (fun x _ => hdet x) hB).symm

/-- The **conditional probability candidate** `condProb ξ i T x`, the real value
`(branchWeight ξ i T (T x)).toReal` of the per-image branch weight at the image point. By the heart
sub-lemma this is the conditional probability of `ξᵢ` given the comap-of-`T` σ-algebra. -/
noncomputable def condProb (ξ : ErgodicTheory.Entropy.MeasurePartition μ ι)
    (i : ι) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (branchWeight ξ i T (T x)).toReal

/-- The branch weight is `μ`-a.e. finite (its `μ`-integral over the whole space is `μ ξᵢ ≤ 1`). -/
lemma branchWeight_lt_top_ae (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0) :
    ∀ᵐ y ∂μ, branchWeight ξ i T y ≠ ∞ := by
  have hint : ∫⁻ y, branchWeight ξ i T y ∂μ ≠ ∞ := by
    rw [← setLIntegral_univ]
    rw [branchWeight_setLIntegral_eq hT hac hdiff hξ i hdet MeasurableSet.univ]
    exact measure_ne_top μ _
  exact ae_lt_top (measurable_branchWeight hdiff hξ i) hint |>.mono fun y hy => hy.ne

/-- The set-integral of `condProb` over a generator `T⁻¹' B` recovers `μ.real (ξᵢ ∩ T⁻¹B)`:
push the `μ`-integral of `(branchWeight ∘ T).toReal` through `integral_toReal` to the lintegral
`∫⁻_{T⁻¹B} branchWeight (T ·) ∂μ`, change variables by measure-preservation (`setLIntegral_map`,
`map T μ = μ`) to `∫⁻_B branchWeight ∂μ = μ (ξᵢ ∩ T⁻¹B)` (the heart sub-lemma). -/
lemma condProb_setIntegral_eq (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    ∫ x in T ⁻¹' B, condProb ξ i T x ∂μ
      = ∫ x in T ⁻¹' B, (ξ.cells i).indicator (fun _ => (1 : ℝ)) x ∂μ := by
  have hTmeas : Measurable T := hdiff.continuous.measurable
  -- The lintegral of `branchWeight ∘ T` over `T⁻¹B` equals `μ (ξᵢ ∩ T⁻¹B)`.
  have hmap : ∫⁻ x in T ⁻¹' B, branchWeight ξ i T (T x) ∂μ
      = ∫⁻ y in B, branchWeight ξ i T y ∂μ := by
    have h := setLIntegral_map hB (measurable_branchWeight hdiff hξ i) hTmeas (μ := μ)
    rw [hT.map_eq] at h; exact h.symm
  have hlint : ∫⁻ x in T ⁻¹' B, branchWeight ξ i T (T x) ∂μ = μ (ξ.cells i ∩ T ⁻¹' B) := by
    rw [hmap, branchWeight_setLIntegral_eq hT hac hdiff hξ i hdet hB]
  -- The integrand `branchWeight ∘ T` is a.e.-finite on `T⁻¹B` (its lintegral there is `≤ 1`).
  have hfin : ∀ᵐ x ∂(μ.restrict (T ⁻¹' B)), branchWeight ξ i T (T x) < ∞ := by
    refine ae_lt_top ((measurable_branchWeight hdiff hξ i).comp hTmeas) ?_
    rw [hlint]; exact measure_ne_top μ _
  -- LHS via `integral_toReal`; RHS is the indicator set-integral.
  have hamb : AEMeasurable (fun x => branchWeight ξ i T (T x)) (μ.restrict (T ⁻¹' B)) :=
    ((measurable_branchWeight hdiff hξ i).comp hTmeas).aemeasurable
  -- RHS: `∫_{T⁻¹B} 1_{ξᵢ} = μ.real (ξᵢ ∩ T⁻¹B)`.
  have hrhs : ∫ x in T ⁻¹' B, (ξ.cells i).indicator (fun _ => (1 : ℝ)) x ∂μ
      = (μ (ξ.cells i ∩ T ⁻¹' B)).toReal := by
    rw [integral_indicator (hξ.meas i), setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def, Measure.restrict_apply (hξ.meas i)]
  rw [hrhs]
  unfold condProb
  rw [integral_toReal hamb hfin, hlint]

/-- `condProb` is integrable on any `μ`-finite measurable set (it is nonnegative and bounded in
`L¹` by the kernel mass; here we use that it is a bounded-by-`(branchWeight∘T).toReal`, finite-
integral function — its global `μ`-integral is `μ ξᵢ ≤ 1`). -/
lemma condProb_integrableOn (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0) (s : Set (EuclideanSpace ℝ (Fin d)))
    (_hs : MeasurableSet s) :
    IntegrableOn (condProb ξ i T) s μ := by
  have hTmeas : Measurable T := hdiff.continuous.measurable
  refine Integrable.integrableOn ?_
  -- `condProb` is measurable, nonnegative, and has finite `μ`-lintegral `μ ξᵢ`.
  refine ⟨(((measurable_branchWeight hdiff hξ i).comp hTmeas).ennreal_toReal).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound : ∀ x, ‖condProb ξ i T x‖ₑ ≤ branchWeight ξ i T (T x) := by
    intro x
    rw [show condProb ξ i T x = (branchWeight ξ i T (T x)).toReal from rfl,
      Real.enorm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hmapU : ∫⁻ x, branchWeight ξ i T (T x) ∂μ = ∫⁻ y, branchWeight ξ i T y ∂μ := by
    have h := lintegral_map (measurable_branchWeight hdiff hξ i) hTmeas (μ := μ)
    rw [hT.map_eq] at h; exact h.symm
  calc ∫⁻ x, ‖condProb ξ i T x‖ₑ ∂μ
      ≤ ∫⁻ x, branchWeight ξ i T (T x) ∂μ := lintegral_mono hbound
    _ = ∫⁻ y, branchWeight ξ i T y ∂μ := hmapU
    _ = μ (ξ.cells i ∩ T ⁻¹' Set.univ) := by
          rw [← setLIntegral_univ, branchWeight_setLIntegral_eq hT hac hdiff hξ i hdet
            MeasurableSet.univ]
    _ < ∞ := measure_lt_top μ _

/-- **N5.4 — conditional probability identification.** The regular-conditional kernel mass of the
cell `ξᵢ` given the comap-of-`T` σ-algebra equals, `μ`-a.e., the branch-weight candidate
`condProb`. The candidate is `comap T mα`-measurable (a measurable function of `T x`) and, on every
generator `T⁻¹' B`, has the right set-integral `μ (ξᵢ ∩ T⁻¹B)` by the heart sub-lemma; uniqueness of
the conditional expectation (`ae_eq_condExp_of_forall_setIntegral_eq`) and
`condExpKernel_ae_eq_condExp` then pin the kernel mass to `condProb`. -/
lemma condExpKernel_cell_ae_eq_condProb (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0) :
    (fun ω => (condExpKernel μ (MeasurableSpace.comap T inferInstance) ω (ξ.cells i)).toReal)
      =ᵐ[μ] condProb ξ i T := by
  have hTmeas : Measurable T := hdiff.continuous.measurable
  have h𝒜le : MeasurableSpace.comap T (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d)))
      ≤ (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))) := hTmeas.comap_le
  have hσf : SigmaFinite (μ.trim h𝒜le) := by
    have : IsFiniteMeasure (μ.trim h𝒜le) := isFiniteMeasure_trim h𝒜le
    infer_instance
  -- `condProb` is `comap T mα`-measurable (a measurable function precomposed with `T`).
  have hcpMeas : Measurable[MeasurableSpace.comap T inferInstance] (condProb ξ i T) :=
    ((measurable_branchWeight hdiff hξ i).ennreal_toReal).comp (Measurable.of_comap_le le_rfl)
  -- The kernel mass equals `μ⟦ξᵢ | comap T mα⟧` a.e.
  have hkernel : (fun ω => ((condExpKernel μ (MeasurableSpace.comap T inferInstance) ω)
      (ξ.cells i)).toReal) =ᵐ[μ] μ⟦ξ.cells i | MeasurableSpace.comap T inferInstance⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp h𝒜le (hξ.meas i)
  -- `condProb = μ⟦ξᵢ | comap T mα⟧` a.e. by uniqueness of conditional expectation.
  have hcp : condProb ξ i T =ᵐ[μ] μ⟦ξ.cells i | MeasurableSpace.comap T inferInstance⟧ := by
    refine ae_eq_condExp_of_forall_setIntegral_eq h𝒜le
      ((integrable_const (1 : ℝ)).indicator (hξ.meas i)) ?_ ?_
      hcpMeas.aestronglyMeasurable
    · intro s hs _
      exact condProb_integrableOn hT hac hdiff hξ i hdet s (h𝒜le s hs)
    · intro s hs _
      obtain ⟨B, hB, rfl⟩ := hs
      exact condProb_setIntegral_eq hT hac hdiff hξ i hdet hB
  exact hkernel.trans hcp.symm

omit [IsProbabilityMeasure μ] in
/-- **The density-ratio orientation, pinned on the cell `ξᵢ`.** For `x ∈ ξ.cells i`, the branch
weight evaluated at the image collapses (the inverse branch returns `x`):
`branchWeight ξ i T (T x) = (ρ x / ofReal|det DT x|) / ρ (T x)`. The numerator density `ρ` sits at
`x`, the denominator `ρ` at `T x` — the orientation that makes `∫ (log ρ∘T − log ρ)` telescope to
`0` under `T`-invariance. -/
lemma branchWeight_comp_eq_on_cell
    (hξ : IsInjectivityPartition μ T ξ) (i : ι) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ ξ.cells i) :
    branchWeight ξ i T (T x)
      = (μ.rnDeriv volume) x / ENNReal.ofReal |(fderiv ℝ T x).det| / (μ.rnDeriv volume) (T x) := by
  have hmem : T x ∈ T '' ξ.cells i := ⟨x, hx, rfl⟩
  have hbranch : Function.invFunOn T (ξ.cells i) (T x) = x :=
    (hξ.inj i).leftInvOn_invFunOn hx
  simp only [branchWeight, Set.indicator_of_mem hmem, transferDensity, hbranch]

omit [IsProbabilityMeasure μ] in
/-- **The log density-ratio identity on `ξᵢ`.** For `x ∈ ξ.cells i` with `ρ x, ρ (T x) > 0`,
`log (condProb ξ i T x) = log (ρ x).toReal − log |det DT x| − log (ρ (T x)).toReal`. -/
lemma log_condProb_eq_on_cell
    (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ ξ.cells i) (hρx : (μ.rnDeriv volume) x ≠ 0) (hρxtop : (μ.rnDeriv volume) x ≠ ∞)
    (hρTx : (μ.rnDeriv volume) (T x) ≠ 0) (hρTxtop : (μ.rnDeriv volume) (T x) ≠ ∞) :
    Real.log (condProb ξ i T x)
      = Real.log ((μ.rnDeriv volume) x).toReal - Real.log |(fderiv ℝ T x).det|
        - Real.log ((μ.rnDeriv volume) (T x)).toReal := by
  have hdetpos : 0 < |(fderiv ℝ T x).det| := abs_pos.mpr (hdet x)
  have hρxpos : 0 < ((μ.rnDeriv volume) x).toReal := ENNReal.toReal_pos hρx hρxtop
  have hρTxpos : 0 < ((μ.rnDeriv volume) (T x)).toReal := ENNReal.toReal_pos hρTx hρTxtop
  have hval : condProb ξ i T x = ((μ.rnDeriv volume) x).toReal / |(fderiv ℝ T x).det|
        / ((μ.rnDeriv volume) (T x)).toReal := by
    rw [condProb, branchWeight_comp_eq_on_cell hξ i hx, ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hdetpos.le]
  rw [hval, Real.log_div (ne_of_gt (div_pos hρxpos hdetpos)) hρTxpos.ne',
    Real.log_div hρxpos.ne' (ne_of_gt hdetpos)]

/-- The **Jacobian log-cocycle** `jacLog T x = log |det DT x| + log ρ(Tx) − log ρ(x)`. Its `μ`-mean
is `∫ log|det DT| dμ`, because the bracket `∫ (log ρ∘T − log ρ)` telescopes to `0` under
`T`-invariance (the orientation pinned by `log_condProb_eq_on_cell`). -/
noncomputable def jacLog (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log |(fderiv ℝ T x).det| + Real.log ((μ.rnDeriv volume) (T x)).toReal
    - Real.log ((μ.rnDeriv volume) x).toReal

omit [IsProbabilityMeasure μ] in
@[simp] lemma jacLog_apply (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    jacLog T ν x = Real.log |(fderiv ℝ T x).det| + Real.log ((ν.rnDeriv volume) (T x)).toReal
      - Real.log ((ν.rnDeriv volume) x).toReal := rfl

omit [IsProbabilityMeasure μ] in
/-- The `μ`-integral of the Jacobian log-cocycle is the integral of `log|det DT|`: the
`log ρ∘T − log ρ` bracket telescopes to `0` by `T`-invariance (`integral_map` with `map T μ = μ`),
using `hlogρ : log ρ ∈ L¹(μ)` (load-bearing — without it the bracket is `∞ − ∞`) and
`hlogdet : log|det DT| ∈ L¹(μ)`. -/
lemma integral_jacLog_eq (hT : MeasurePreserving T μ μ) (hdiff : Differentiable ℝ T)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    ∫ x, jacLog T μ x ∂μ = ∫ x, Real.log |(fderiv ℝ T x).det| ∂μ := by
  have hTmeas : Measurable T := hdiff.continuous.measurable
  -- `∫ logρ∘T = ∫ logρ` by `T`-invariance.
  have hfm : AEStronglyMeasurable (fun x => Real.log ((μ.rnDeriv volume) x).toReal)
      (Measure.map T μ) := by rw [hT.map_eq]; exact hlogρ.aestronglyMeasurable
  have hcomp : ∫ x, Real.log ((μ.rnDeriv volume) (T x)).toReal ∂μ
      = ∫ x, Real.log ((μ.rnDeriv volume) x).toReal ∂μ := by
    rw [← integral_map hTmeas.aemeasurable hfm, hT.map_eq]
  have hlogρcomp : Integrable (fun x => Real.log ((μ.rnDeriv volume) (T x)).toReal) μ :=
    hT.integrable_comp_of_integrable hlogρ
  -- Split the integral and telescope, with the minuend `F` as an explicit lambda.
  have hFint : Integrable (fun x => Real.log |(fderiv ℝ T x).det|
      + Real.log ((μ.rnDeriv volume) (T x)).toReal) μ := hlogdet.add hlogρcomp
  calc ∫ x, jacLog T μ x ∂μ
      = ∫ x, ((Real.log |(fderiv ℝ T x).det| + Real.log ((μ.rnDeriv volume) (T x)).toReal)
          - Real.log ((μ.rnDeriv volume) x).toReal) ∂μ := by simp only [jacLog_apply]
    _ = (∫ x, (Real.log |(fderiv ℝ T x).det| + Real.log ((μ.rnDeriv volume) (T x)).toReal) ∂μ)
          - ∫ x, Real.log ((μ.rnDeriv volume) x).toReal ∂μ := integral_sub hFint hlogρ
    _ = ((∫ x, Real.log |(fderiv ℝ T x).det| ∂μ)
          + ∫ x, Real.log ((μ.rnDeriv volume) (T x)).toReal ∂μ)
          - ∫ x, Real.log ((μ.rnDeriv volume) x).toReal ∂μ := by
          rw [integral_add hlogdet hlogρcomp]
    _ = ∫ x, Real.log |(fderiv ℝ T x).det| ∂μ := by rw [hcomp]; ring

omit [IsProbabilityMeasure μ] in
/-- `jacLog` is `μ`-integrable (sum of `log|det DT|`, `log ρ∘T`, `log ρ`, each in `L¹`). -/
lemma integrable_jacLog (hT : MeasurePreserving T μ μ)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    Integrable (jacLog T μ) μ := by
  have hlogρcomp : Integrable (fun x => Real.log ((μ.rnDeriv volume) (T x)).toReal) μ :=
    hT.integrable_comp_of_integrable hlogρ
  exact (hlogdet.add hlogρcomp).sub hlogρ

/-- **The per-cell pull-out identity.** For each cell `i`, the `μ`-mean of `negMulLog (condProb i)`
equals the set-integral of the Jacobian log-cocycle over the cell:
`∫ negMulLog (condProb ξ i T x) ∂μ = ∫_{ξᵢ} jacLog T μ x ∂μ`.

Pull-out: `condProb i = E(1_{ξᵢ} | comap T mα)` a.e., and `log (condProb i)` is
`comap T mα`-measurable, so `∫ condProb i · log (condProb i) = ∫ 1_{ξᵢ} · log (condProb i)`
(`condExp_mul_of_stronglyMeasurable_left` + `integral_condExp`). On `ξᵢ`,
`log (condProb i) = −jacLog` (`log_condProb_eq_on_cell`, the pinned orientation), and
`negMulLog t = −t · log t`, so the term becomes `∫_{ξᵢ} jacLog`. -/
lemma integral_negMulLog_condProb_eq (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) (hξ : IsInjectivityPartition μ T ξ) (i : ι)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    ∫ x, Real.negMulLog (condProb ξ i T x) ∂μ = ∫ x in ξ.cells i, jacLog T μ x ∂μ := by
  classical
  have hTmeas : Measurable T := hdiff.continuous.measurable
  have h𝒜le : MeasurableSpace.comap T (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d)))
      ≤ (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))) := hTmeas.comap_le
  have hσf : SigmaFinite (μ.trim h𝒜le) := by
    have : IsFiniteMeasure (μ.trim h𝒜le) := isFiniteMeasure_trim h𝒜le
    infer_instance
  have hcondProb_eq :
      condProb ξ i T =ᵐ[μ] μ⟦ξ.cells i | MeasurableSpace.comap T inferInstance⟧ :=
    (condExpKernel_cell_ae_eq_condProb hT hac hdiff hξ i hdet).symm.trans
      (condExpKernel_ae_eq_condExp h𝒜le (hξ.meas i))
  -- `log (condProb i)` is `comap T mα`-measurable.
  have hcpMeas𝒜 : Measurable[MeasurableSpace.comap T inferInstance] (condProb ξ i T) :=
    ((measurable_branchWeight hdiff hξ i).ennreal_toReal).comp (Measurable.of_comap_le le_rfl)
  have hlogMeas : Measurable[MeasurableSpace.comap T inferInstance]
      (fun x => Real.log (condProb ξ i T x)) := Real.measurable_log.comp hcpMeas𝒜
  -- `jacLog` is `μ`-integrable and `log (condProb i) = −jacLog` on `ξᵢ` a.e.
  have hjacInt : Integrable (jacLog T μ) μ := integrable_jacLog hT hlogρ hlogdet
  have hlogcp_cell : (fun x => Real.log (condProb ξ i T x)) =ᵐ[μ.restrict (ξ.cells i)]
      (fun x => -jacLog T μ x) := by
    have hρtop : ∀ᵐ x ∂μ, (μ.rnDeriv volume) x ≠ ∞ :=
      (Measure.rnDeriv_ne_top μ volume).filter_mono
        (Measure.ae_le_iff_absolutelyContinuous.mpr hac)
    rw [Filter.EventuallyEq, ae_restrict_iff' (hξ.meas i)]
    filter_upwards [rnDeriv_volume_pos hac, hρtop,
      hT.quasiMeasurePreserving.tendsto_ae.eventually (rnDeriv_volume_pos hac),
      hT.quasiMeasurePreserving.tendsto_ae.eventually hρtop] with x hx hxt hTx hTxt
    intro hxcell
    rw [log_condProb_eq_on_cell hξ i hdet hxcell hx.ne' hxt hTx.ne' hTxt, jacLog]
    ring
  -- `log (condProb i)` is `IntegrableOn ξᵢ` (it equals `−jacLog` there).
  have hlogcpOn : IntegrableOn (fun x => Real.log (condProb ξ i T x)) (ξ.cells i) μ :=
    (hjacInt.neg.integrableOn).congr hlogcp_cell.symm
  -- The product `log (condProb i) · 1_{ξᵢ}` is `μ`-integrable.
  have hprodInt : Integrable
      (fun x => Real.log (condProb ξ i T x) * (ξ.cells i).indicator (fun _ => (1 : ℝ)) x) μ := by
    have hrw : (fun x => Real.log (condProb ξ i T x) * (ξ.cells i).indicator (fun _ => (1 : ℝ)) x)
        = (ξ.cells i).indicator (fun x => Real.log (condProb ξ i T x)) := by
      funext x; by_cases hx : x ∈ ξ.cells i
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    rw [hrw, integrable_indicator_iff (hξ.meas i)]; exact hlogcpOn
  -- Pull-out: `∫ log(condProb)·condProb = ∫_{ξᵢ} log(condProb)`.
  have hpull : ∫ x, Real.log (condProb ξ i T x) * condProb ξ i T x ∂μ
      = ∫ x in ξ.cells i, Real.log (condProb ξ i T x) ∂μ := by
    have hg : Integrable ((ξ.cells i).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator (hξ.meas i)
    -- `μ[(log condProb)·1_{ξᵢ} | comap T mα] =ᵐ (log condProb) · μ[1_{ξᵢ} | comap T mα]`.
    have hmul := condExp_mul_of_stronglyMeasurable_left
      (m := MeasurableSpace.comap T inferInstance) (μ := μ)
      hlogMeas.stronglyMeasurable hprodInt hg
    -- `μ[1_{ξᵢ} | ·] = μ⟦ξᵢ | ·⟧ =ᵐ condProb`, so the RHS is `(log condProb)·condProb`.
    have hmul' : μ[(fun x => Real.log (condProb ξ i T x)) *
          (ξ.cells i).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap T inferInstance]
        =ᵐ[μ] (fun x => Real.log (condProb ξ i T x) * condProb ξ i T x) := by
      filter_upwards [hmul, hcondProb_eq] with x hx hxc
      rw [hx]; simp only [Pi.mul_apply]; rw [← hxc]
    -- `∫ log·condProb = ∫ E(log·1_{ξᵢ}|·) = ∫ log·1_{ξᵢ} = ∫_{ξᵢ} log`.
    rw [← integral_congr_ae hmul', integral_condExp h𝒜le]
    have hind : (fun x => Real.log (condProb ξ i T x))
        * (ξ.cells i).indicator (fun _ => (1 : ℝ))
        = (ξ.cells i).indicator (fun x => Real.log (condProb ξ i T x)) := by
      funext x; simp only [Pi.mul_apply]; by_cases hx : x ∈ ξ.cells i
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    rw [hind, integral_indicator (hξ.meas i)]
  -- Assemble: `negMulLog t = -(t·log t)`; rewrite, pull out, and use `log = −jacLog` on `ξᵢ`.
  simp only [Real.negMulLog_eq_neg]
  rw [integral_neg]
  have hcomm : (fun x => condProb ξ i T x * Real.log (condProb ξ i T x))
      = (fun x => Real.log (condProb ξ i T x) * condProb ξ i T x) := by funext x; ring
  rw [hcomm, hpull, setIntegral_congr_ae (hξ.meas i)
    ((ae_restrict_iff' (hξ.meas i)).1 hlogcp_cell), integral_neg]
  ring

/-- **N5.4 — the conditional-entropy = Jacobian-integral identity (Coudène Prop 12.1).**
For an absolutely continuous, differentiable, injectivity-partitioned self-map `T` with
everywhere-nonsingular derivative and `μ`-integrable `log ρ` and `log|det DT|`, the conditional
Shannon entropy of `ξ` given the comap-of-`T` σ-algebra equals the integral of `log|det DT|`:
`H(ξ | comap T mα) = ∫ log|det DT| dμ`.

This is **partition-independent** (no `IsGenerating`). The proof: the condEntropy integrand
`∑ᵢ negMulLog (κ ω ξᵢ).toReal` has each kernel mass identified with the branch-weight candidate
`condProb i` (`condExpKernel_cell_ae_eq_condProb`); the per-cell pull-out
(`integral_negMulLog_condProb_eq`) turns each summand into `∫_{ξᵢ} jacLog`; the cells partition the
space a.e. so the sum is `∫ jacLog`; and `∫ jacLog = ∫ log|det DT|` (`integral_jacLog_eq`, the
`log ρ∘T − log ρ` bracket telescoping to `0` by `T`-invariance — the pinned orientation). -/
theorem condEntropy_comap_eq_integral_log_abs_det (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) (hξ : IsInjectivityPartition μ T ξ)
    (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    ErgodicTheory.Entropy.condEntropy μ (MeasurableSpace.comap T inferInstance) ξ.cells
      = ∫ x, Real.log |(fderiv ℝ T x).det| ∂μ := by
  classical
  have hTmeas : Measurable T := hdiff.continuous.measurable
  -- Replace each kernel mass by `condProb i` a.e.
  have hintegrand : (fun ω => ∑ i, Real.negMulLog
        ((condExpKernel μ (MeasurableSpace.comap T inferInstance) ω) (ξ.cells i)).toReal)
      =ᵐ[μ] fun ω => ∑ i, Real.negMulLog (condProb ξ i T ω) := by
    have hall : ∀ i, (fun ω => ((condExpKernel μ (MeasurableSpace.comap T inferInstance) ω)
        (ξ.cells i)).toReal) =ᵐ[μ] condProb ξ i T :=
      fun i => condExpKernel_cell_ae_eq_condProb hT hac hdiff hξ i hdet
    filter_upwards [ae_all_iff.2 hall] with ω hω
    exact Finset.sum_congr rfl fun i _ => by rw [hω i]
  rw [condEntropy_def, integral_congr_ae hintegrand]
  -- Move the integral inside the finite sum.
  have hintegrableTerm : ∀ i, Integrable (fun ω => Real.negMulLog (condProb ξ i T ω)) μ := by
    intro i
    refine ((integrable_negMulLog_condExpKernel
      (𝒜 := MeasurableSpace.comap T inferInstance) hTmeas.comap_le (hξ.meas i)).congr ?_)
    filter_upwards [condExpKernel_cell_ae_eq_condProb hT hac hdiff hξ i hdet] with ω hω
    rw [hω]
  rw [integral_finsetSum _ (fun i _ => hintegrableTerm i)]
  -- Each summand is `∫_{ξᵢ} jacLog`; sum over the a.e.-partition is `∫ jacLog`.
  have hterm : ∀ i, ∫ ω, Real.negMulLog (condProb ξ i T ω) ∂μ
      = ∫ x in ξ.cells i, jacLog T μ x ∂μ :=
    fun i => integral_negMulLog_condProb_eq hT hac hdiff hξ i hdet hlogρ hlogdet
  simp_rw [hterm]
  -- `∑ᵢ ∫_{ξᵢ} jacLog = ∫_{⋃ ξᵢ} jacLog = ∫ jacLog` (a.e.-partition, `jacLog` integrable).
  have hjacInt : Integrable (jacLog T μ) μ := integrable_jacLog hT hlogρ hlogdet
  have hsum : ∑ i, ∫ x in ξ.cells i, jacLog T μ x ∂μ = ∫ x, jacLog T μ x ∂μ := by
    rw [← setIntegral_univ (μ := μ), ← ξ.cover,
      integral_iUnion_ae (fun i => (hξ.meas i).nullMeasurableSet) ξ.aedisjoint
        (by rw [ξ.cover]; exact hjacInt.integrableOn)]
    exact (tsum_fintype _).symm
  rw [hsum, integral_jacLog_eq hT hdiff hlogρ hlogdet]

end CondEntropyJacobian

/-! ### N5.3.5 — the σ-algebra glue identifying the strict-future filtration -/

section SigmaGlue

open ErgodicTheory.Entropy MeasurableSpace

variable {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {m : ℕ}

omit [IsProbabilityMeasure μ] in
/-- **The strict-future filtration is the `T`-comap of the ambient σ-algebra (for a generator).**
For a measure-preserving system with a one-sided generating finite partition `ξ`, the supremum of
the increasing filtration `k ↦ σ((⋁₀ᵏ⁻¹ T⁻ʲξ) pulled back by T)` — the σ-algebra of the strict
future `σ(⋁_{j≥1} T⁻ʲξ)` — equals the comap of the ambient σ-algebra under `T`:
`⨆ k, σ((ksJoin ξ k).pullback) = comap T mα`.

The σ-algebra chain: `σ((ksJoin ξ k).pullback) = comap T (σ(ksJoin ξ k))`
(`generatedSigmaAlgebra_pullback_eq_pulledBack` then `comap_generatedSigmaAlgebra_pulledBack`);
commute `comap T` out of the supremum (`comap_iSup`); collapse the inner supremum
`⨆ k, σ(ksJoin ξ k) = ⨆ k, comap (T^[k]) σ(ξ)` (`iSup_generatedSigmaAlgebra_ksJoin_eq`); and
apply the generator hypothesis `⨆ k, comap (T^[k]) σ(ξ) = mα`. -/
lemma strictFuture_eq_comap_of_generating (hT : MeasurePreserving T μ μ)
    (ξ : ErgodicTheory.Entropy.MeasurePartition μ (Fin m))
    (hgen : ErgodicTheory.Entropy.IsGenerating μ T ξ) :
    (⨆ k, ErgodicTheory.Entropy.generatedSigmaAlgebra μ
        ((ErgodicTheory.Entropy.ksJoin hT ξ k).pullback hT))
      = MeasurableSpace.comap T inferInstance := by
  -- Rewrite each `σ((ksJoin ξ k).pullback) = comap T (σ(ksJoin ξ k))`.
  have hterm : ∀ k : ℕ, generatedSigmaAlgebra μ ((ksJoin hT ξ k).pullback hT)
      = MeasurableSpace.comap T (generatedSigmaAlgebra μ (ksJoin hT ξ k)) := by
    intro k
    rw [ErgodicTheory.Krieger.generatedSigmaAlgebra_pullback_eq_pulledBack hT (ksJoin hT ξ k),
      comap_generatedSigmaAlgebra_pulledBack hT (ksJoin hT ξ k)]
  -- Commute `comap T` out of the supremum and collapse the inner supremum, then apply `hgen`.
  simp_rw [hterm, ← MeasurableSpace.comap_iSup, iSup_generatedSigmaAlgebra_ksJoin_eq hT ξ]
  rw [hgen]

omit [IsProbabilityMeasure μ] in
/-- The `ContinuousLinearMap` determinant of `fderiv ℝ T x` equals the matrix determinant of the
derivative cocycle generator `derivativeCocycle T x`: the generator is the matrix representing
`Dₓ T` through `toEuclideanCLM`, whose `LinearMap`-coercion is `toEuclideanLin`, whose determinant
(`LinearMap.det_toLin` against the standard basis) is the matrix determinant. -/
lemma det_fderiv_eq_det_derivativeCocycle
    {d : ℕ} {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (x : EuclideanSpace ℝ (Fin d)) :
    (fderiv ℝ T x).det = (ErgodicTheory.derivativeCocycle T x).det := by
  have hdet0 : (fderiv ℝ T x).det
      = LinearMap.det ((fderiv ℝ T x).toLinearMap) := rfl
  have h1 : (fderiv ℝ T x).det
      = LinearMap.det (Matrix.toEuclideanLin (ErgodicTheory.derivativeCocycle T x)) := by
    rw [hdet0, ← ErgodicTheory.toEuclideanCLM_derivativeCocycle T x,
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  rw [h1, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

end SigmaGlue

/-! ### N5.5 — the per-partition Rokhlin formula -/

section Assembly

open ErgodicTheory.Entropy MeasurableSpace

/-- **N5.5 — the per-partition Rokhlin formula.** For an absolutely continuous, differentiable,
uniformly injectivity-partitioned self-map `T` with a one-sided generating partition `ξ`,
everywhere-nonsingular derivative, and `μ`-integrable `log ρ` and `log|det DT|`, the
Kolmogorov–Sinai entropy of `T` relative to `ξ` equals the integrated volume distortion:
`h(T, ξ) = ∫ log |det (derivativeCocycle T x)| dμ`.

Assembled from the sharp-rate identity
`ksEntropyPartition hT ξ = condEntropy μ (⨆ k, σ((ksJoin ξ k).pullback)) ξ.cells`
(`ksEntropyPartition_eq_condEntropy_iSup`), the σ-algebra glue
`⨆ k, σ((ksJoin ξ k).pullback) = comap T mα` (`strictFuture_eq_comap_of_generating`, using `hgen`),
and N5.4 (`condEntropy_comap_eq_integral_log_abs_det`). The integrand bridge
`|det (fderiv ℝ T x)| = |det (derivativeCocycle T x)|` (`det_fderiv_eq_det_derivativeCocycle`) puts
the right-hand side in the verbatim shape of `sumPosExp_eq_integral_log_abs_det_of_expanding`.

Note: no instance of this hypothesis bundle (m.p. + a.c. + everywhere-nonsingular derivative +
finite *generating* injectivity partition) is exhibited here on `EuclideanSpace ℝ (Fin d)`. Unlike
`pesin_formula_expanding`, N5.5 carries **no** expansion hypothesis, so the escaping-mass
obstruction of the Pesin caveat does not apply and **no `no-model` claim is made** — only that no
instance is exhibited here. The genuine instantiated equality is `rokhlin_equality_doublingMap`
(`ErgodicTheory/Examples/Rokhlin/DoublingEquality.lean`) on the compact circle. -/
theorem ksEntropyPartition_eq_integral_log_abs_det {d : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    [StandardBorelSpace (EuclideanSpace ℝ (Fin d))]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {m : ℕ} {ξ : ErgodicTheory.Entropy.MeasurePartition μ (Fin m)} [Nonempty (Fin m)]
    (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume) (hdiff : Differentiable ℝ T)
    (hξ : IsInjectivityPartition μ T ξ) (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0)
    (hgen : ErgodicTheory.Entropy.IsGenerating μ T ξ)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    ErgodicTheory.Entropy.ksEntropyPartition hT ξ
      = ∫ x, Real.log |(ErgodicTheory.derivativeCocycle T x).det| ∂μ := by
  rw [ErgodicTheory.Krieger.ksEntropyPartition_eq_condEntropy_iSup hT ξ,
    strictFuture_eq_comap_of_generating hT ξ hgen,
    condEntropy_comap_eq_integral_log_abs_det hT hac hdiff hξ hdet hlogρ hlogdet]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [det_fderiv_eq_det_derivativeCocycle (T := T) x]

end Assembly

/-! ### Pesin — the unconditional expanding-map entropy formula -/

section Pesin

open ErgodicTheory.Entropy

/-- **Pesin's entropy formula for an absolutely-continuous uniformly-expanding map** — a correct
implication that is **vacuously true on `EuclideanSpace ℝ (Fin d)`**: its hypothesis bundle has no
model there (full vacuity caveat below; the instantiated equality lives on the compact circle).

For an ergodic, absolutely-continuous (`μ ≪ volume`), differentiable, uniformly expanding map `T` of
`EuclideanSpace ℝ (Fin d)` with everywhere-nonsingular derivative and `μ`-integrable log-norm data,
together with a one-sided generating injectivity partition `ξ` and `μ`-integrable `log ρ` and
`log|det DT|`, the Kolmogorov–Sinai entropy equals the sum of the (all positive) Lyapunov exponents:
`h_μ(T) = ∑ λ⁺ = ∫ log |det Df| dμ`.

This is the **placeholder-free assembly of the implication**: the SRB property is supplied by the
genuine absolute-continuity hypothesis `μ ≪ volume`, not an opaque SRB axiom. The proof composes
three on-branch theorems: `ksEntropy_eq_ksEntropyPartition_of_generating` (the Kolmogorov–Sinai
generator theorem), `ksEntropyPartition_eq_integral_log_abs_det` (Rokhlin's per-partition formula,
N5.5), and `sumPosExp_eq_integral_log_abs_det_of_expanding` (the Pesin = Rokhlin right-hand-side
identity); the two `det` hypotheses are aligned by `det_fderiv_eq_det_derivativeCocycle`. The
`StandardBorelSpace (EuclideanSpace ℝ (Fin d))` instance is the derived `standardBorel_of_polish`
instance — not assumed.

**Vacuity caveat (honest disclosure).** This is a correct *implication*, but its hypothesis bundle
has **no model on the non-compact space `EuclideanSpace ℝ (Fin d) = ℝ^d`**, so the theorem is
**vacuously true** — the EuclideanSpace assembly of the implication, not an exhibited instance.
A globally uniformly expanding (`K > 1`) self-map of `ℝ^d` admits no ergodic absolutely-continuous
invariant *probability* measure: e.g. for `T = c • id` (`c > 1`) the nested preimages
`T⁻ⁿ(closedBall 0 R)` have constant `μ`-mass, forcing an atom at the fixed point `0`, contradicting
`μ ≪ volume`; in general uniform expansion on a non-compact space forces mass to escape to infinity
(every existence theorem for a.c. invariant measures of uniformly expanding maps is on a *compact*
manifold). The intended models live on a torus. A genuinely *instantiated* Pesin/Rokhlin equality
`h_μ(T) = ∫ log|det DT| dμ = log 2` is `ErgodicTheory.Examples.Rokhlin.rokhlin_equality_doublingMap`, on
the compact circle `UnitAddCircle`. A non-vacuous EuclideanSpace-style statement would require
porting the derivative-cocycle / expanding / Lyapunov-exponent layer to the torus (currently
`EuclideanSpace`-only). -/
theorem pesin_formula_expanding {d : ℕ} [NeZero d]
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hErg : Ergodic T μ) (hac : μ ≪ volume) (hdiff : Differentiable ℝ T)
    {K : ℝ} (hK : 1 < K) (hexp : ∀ x v, K * ‖v‖ ≤ ‖fderiv ℝ T x v‖)
    (hdet : ∀ x, (ErgodicTheory.derivativeCocycle T x).det ≠ 0)
    (hint : ErgodicTheory.IntegrableLogNorm (ErgodicTheory.derivativeCocycle T) μ)
    (hint' : ErgodicTheory.IntegrableLogNorm (fun x => (ErgodicTheory.derivativeCocycle T x)⁻¹) μ)
    {m : ℕ} [Nonempty (Fin m)] {ξ : ErgodicTheory.Entropy.MeasurePartition μ (Fin m)}
    (hξ : ErgodicTheory.IsInjectivityPartition μ T ξ) (hgen : ErgodicTheory.Entropy.IsGenerating μ T ξ)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    ErgodicTheory.Entropy.ksEntropy hErg.toMeasurePreserving
      = ((ErgodicTheory.sumPosExp hErg hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint'
          : ℝ) : EReal) := by
  -- The `fderiv` form of the nonsingularity hypothesis, aligned via the determinant bridge.
  have hdet' : ∀ x, (fderiv ℝ T x).det ≠ 0 := fun x => by
    rw [det_fderiv_eq_det_derivativeCocycle]; exact hdet x
  -- Generator theorem: `h(T) = h(T, ξ)`; reduce to the `ℝ`-level equality.
  rw [ksEntropy_eq_ksEntropyPartition_of_generating hErg.toMeasurePreserving ξ hgen,
    EReal.coe_eq_coe_iff]
  -- Chain Rokhlin's per-partition formula (N5.5) with the Pesin = Rokhlin RHS identity.
  rw [ksEntropyPartition_eq_integral_log_abs_det hErg.toMeasurePreserving hac hdiff hξ hdet' hgen
      hlogρ hlogdet,
    sumPosExp_eq_integral_log_abs_det_of_expanding hErg hdet hint hint' hdiff hK hexp]

end Pesin

end ErgodicTheory
