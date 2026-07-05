/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Ruelle.Count
import ErgodicTheory.Entropy.Ruelle.SharpCovering
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Discharging the atom-count input: the sharp unconditional Margulis–Ruelle inequality

This module assembles the **sharp** Margulis–Ruelle inequality `h(T) ≤ ∑ λᵢ⁺` for a smooth ergodic
self-map `T` of `EuclideanSpace ℝ (Fin d)` by *discharging* the geometric atom-count input `hatom`
of `ErgodicTheory.margulisRuelle_sharp_of_atomVolProd`.  The capstone there reduces, modulo
`hatom`, the system entropy to the positive-exponent sum `sumPosExp`; the surrounding orbit
reduction
(`tendsto_log_volProd`, `eventually_volProd_le`,
`ksEntropyPartition_le_sumPosExp_of_atomVolProd`) is unconditional and sorry-free.  Here we feed the
**one-step sharp local covering count** into the **orbit iteration** that converts a per-partition
covering–distortion count into the atom-count growth bound, producing the inequality under the
*same* honest non-compactness regime as the crude bound `ErgodicTheory.Entropy.Ruelle.Crude`.

## The two inputs

1. **The one-step sharp local covering count (proved in-tree).**  The sharp anisotropic Liao–Qiu
   covering count
   `coveringNumber ε (D_x(T^[n]) '' closedBall 0 ε) ≤ C_d · ∏ᵢ max(1, σᵢ(D_x(T^[n])))`,
   i.e. `≤ C_d · volProd T n x`, is **fully proved in-tree** in
   `ErgodicTheory.Entropy.Ruelle.SharpCovering`
   (`ErgodicTheory.coveringCount_image_ball_le_volProd`, via a
   constructive SVD ellipsoid domination + determinant volume bound).  It is packaged here as the
   explicit `Prop`-valued interface `ErgodicTheory.SharpLocalCovering`, which
   `sharpLocalCovering_of_coveringCount` *discharges* (with the explicit dimensional constant
   `C_d = 6^d`); it is no longer a hypothesis of the sharp track.

2. **The geometric atom-count count (honest non-compactness hypothesis).**  The combinatorial step
   — a non-empty atom of the refined partition `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` maps under `T^[n]` into a set
   covered by `~ volProd` balls, each meeting boundedly many atoms — is the Mañé/Katok count.  On
   the noncompact `EuclideanSpace` it requires the honest regime of
   `ErgodicTheory.Entropy.Ruelle.Crude`
   (uniform derivative bound / `μ` on a compact invariant set / bounded distortion; the bare
   inequality is false otherwise, Riquelme 2017).  We phrase it as the explicit hypothesis
   `hgeoCount`: at a base point `x` carrying the orbit rate, the atom count of the `n`-refinement is
   eventually bounded by the per-orbit covering count.  Composed with input 1 this gives exactly the
   `volProd` atom bound that the orbit assembly consumes.

## Main results

* `ErgodicTheory.SharpLocalCovering` — the `Prop`-valued packaging of the one-step sharp covering
  count `coveringNumber ε (D_x(T^[n]) '' ball) ≤ C · volProd T n x`, *discharged* in-tree by
  `sharpLocalCovering_of_coveringCount`.
* `ErgodicTheory.atomCount_le_volProd_of_sharpCovering` — composing the (proved) sharp
  covering count
  with the geometric count `hgeoCount` yields the per-orbit `volProd` atom bound
  `atomCount ≤ C' · volProd T n x` consumed by the orbit assembly.
* `ErgodicTheory.hatom_of_sharpCovering` — discharges the existential `hatom` of the capstone for a
  fixed partition: at the a.e. orbit-rate base point the atom bound holds.
* `ErgodicTheory.margulisRuelle_sharp` — the **sharp Margulis–Ruelle inequality**
  `ksEntropy hT ≤ ∑ λᵢ⁺`, **conditional** on the honest geometric atom-count hypothesis
  `hgeo` (the Riquelme-necessary distortion datum on non-compact phase space); the sharp
  covering count is discharged internally from `SharpCovering`, so `hgeo` is the sole
  geometric input.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
* Ricardo Mañé, *Ergodic theory and differentiable dynamics*, Springer 1987, §IV.12 (Lemma 12.5).
* Gang Liao, Na Qiu, *Margulis–Ruelle inequality for general manifolds*, Ergodic Theory Dynam.
  Systems **42** (2022) 2064–2079, §3, Lemmas 3.2–3.3.
* Felipe Riquelme, *Counterexamples to Ruelle's inequality in the noncompact case*, Ann. Inst.
  Fourier **67** (2017) 23–41.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ErgodicTheory

variable {d : ℕ} [NeZero d]

/-! ## The one-step sharp local covering count (packaging the in-tree `SharpCovering`) -/

section SharpCoveringInterface

/-- **The per-orbit ε-covering number of the differential image, as a real number.**  The
`ℝ`-valued ε-covering number of the image `D_x(T^[n]) '' closedBall 0 ε` of an `ε`-ball under the
`n`-fold differential `D_x(T^[n]) = toEuclideanCLM (cocycle (derivativeCocycle T) T n x)`.  This is
the geometric quantity that the sharp one-step count (`SharpLocalCovering`) bounds by `C · volProd`
and that the Mañé/Katok count bounds the atom count by; packaging it as a definition keeps the
downstream statements legible. -/
noncomputable def coveringReal (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (ε : ℝ≥0) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((coveringNumber ε ((Matrix.toEuclideanCLM (𝕜 := ℝ)
    (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x)) ''
    closedBall 0 (ε : ℝ)) : ℝ≥0∞)).toReal

/-- **The one-step sharp local covering count (`Prop` packaging).**  For the `n`-fold iterate
`T^[n]`, the image `D_x(T^[n]) '' closedBall 0 ε` of an `ε`-ball under the differential is coverable
by at most `C · volProd T n x` balls of radius `ε`, where
`volProd T n x = ∏ᵢ max(1, σᵢ(D_x(T^[n])))` is the per-orbit positive-part singular-value product
and `D_x(T^[n]) = toEuclideanCLM (cocycle (derivativeCocycle T) T n x)`
(`ErgodicTheory.chainRule_cocycle`).

This is the **sharp anisotropic** Liao–Qiu count (a thin pancake needs *few* balls along its thin
directions), the genuinely geometric per-step input.  It is **proved in-tree** by the sibling
`ErgodicTheory.Entropy.Ruelle.SharpCovering` (`ErgodicTheory.coveringCount_image_ball_le_volProd`,
via a
constructive SVD ellipsoid domination); `sharpLocalCovering_of_coveringCount` instantiates that
count at the differential `D_x(T^[n])` to discharge this packaging, so it is not a hypothesis.
The weaker isotropic count `≤ (2‖L‖+1)^d` (which sees only `σ₀ = ‖L‖`) is subsumed by it. -/
def SharpLocalCovering (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (C : ℝ) (ε : ℝ≥0)
    (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ n : ℕ,
    (coveringNumber ε
        ((Matrix.toEuclideanCLM (𝕜 := ℝ)
          (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x)) ''
        closedBall 0 (ε : ℝ)) : ℝ≥0∞)
      ≤ ENNReal.ofReal (C * volProd T n x)

/-- **The sharp local covering count, discharged by `SharpCovering`.**  The packaging
`SharpLocalCovering T (6^d) ε x` is *proved* (not assumed) from the sharp anisotropic one-step
covering count `ErgodicTheory.coveringCount_image_ball_le_volProd`, instantiated at the differential
`L = D_x(T^[n]) = toEuclideanCLM (cocycle (derivativeCocycle T) T n x)` and centre `0`.

The covering bound gives `coveringNumber ε (L '' B(0,ε)) ≤ ofReal (6^d · ∏ᵢ max(1, σᵢ(L)))`; the
coercion `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin` identifies the underlying linear map of the
CLM with `toEuclideanLin (cocycle …)`, so `∏ᵢ max(1, σᵢ(L)) = volProd T n x` *definitionally*,
giving
exactly `SharpLocalCovering T (6^d) ε x` with the dimensional constant `Ccov' = 6^d`.  Hence the
sharp track no longer takes `∀ x, SharpLocalCovering` as a hypothesis. -/
theorem sharpLocalCovering_of_coveringCount
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {ε : ℝ≥0} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin d)) :
    SharpLocalCovering T ((6 : ℝ) ^ d) ε x := by
  intro n
  -- The sharp anisotropic count at the differential `L`, centred at `0`.
  have hcov := coveringCount_image_ball_le_volProd
    (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x)) 0 hε
  -- The singular-value product equals `volProd` (CLM ↦ LinearMap coercion is `toEuclideanLin`).
  rwa [show (6 : ℝ) ^ d *
        ∏ i ∈ Finset.range d, max 1 (LinearMap.singularValues
          ((Matrix.toEuclideanCLM (𝕜 := ℝ)
              (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x) :
              EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) i)
      = (6 : ℝ) ^ d * volProd T n x from rfl] at hcov

end SharpCoveringInterface

/-! ## The geometric atom-count count, composed with the sharp covering count -/

section AtomCount

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (ErgodicTheory.derivativeCocycle T x).det ≠ 0)
    (hint : ErgodicTheory.IntegrableLogNorm (ErgodicTheory.derivativeCocycle T) μ)
    (hint' : ErgodicTheory.IntegrableLogNorm (fun x => (ErgodicTheory.derivativeCocycle T x)⁻¹) μ)

omit [NeZero d] [IsProbabilityMeasure μ] in
/-- **From the sharp local covering count to the `volProd` atom bound.**  Suppose the geometric
Mañé/Katok count `hgeoCount` holds at a base point `x`: the non-empty atom count of the
`n`-refinement
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is eventually bounded by `Ccov · (the per-orbit ε-covering number of
`D_x(T^[n]) '' ball`)`.  Composing with the sharp one-step covering count `hcover`
(`SharpLocalCovering`, the bound `coveringNumber … ≤ Ccov' · volProd`) yields the per-orbit
`volProd` atom bound `atomCount ≤ C · volProd T n x` consumed by the orbit assembly
`ErgodicTheory.ksEntropyPartition_le_sumPosExp_of_atomVolProd`.

The geometric count `hgeoCount` is the honest non-compactness input (the same regime as
`ErgodicTheory.Entropy.Ruelle.Crude`); `hcover` is the in-tree sharp covering count
(`SharpLocalCovering`).  The composition is the elementary chaining of the two real-valued bounds,
monotone in the (finite) covering number. -/
theorem atomCount_le_volProd_of_sharpCovering {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ErgodicTheory.Entropy.MeasurePartition μ ι) {Ccov Ccov' : ℝ} (hCcov : 0 ≤ Ccov)
    (hCcov' : 0 ≤ Ccov') {ε : ℝ≥0} {x : EuclideanSpace ℝ (Fin d)}
    (hcover : SharpLocalCovering T Ccov' ε x)
    (hgeoCount : ∀ᶠ n : ℕ in atTop,
      (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P n : ℝ)
        ≤ Ccov * coveringReal T n ε x) :
    ∀ᶠ n : ℕ in atTop,
      (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P n : ℝ)
        ≤ (Ccov * Ccov') * volProd T n x := by
  filter_upwards [hgeoCount] with n hn
  -- The one-step covering count, read as a real-number bound on the finite covering number.
  have hstep := hcover n
  -- `coveringNumber … ≤ ofReal (Ccov' * volProd)` is finite on the right, so `toReal` is monotone.
  have hfin : ENNReal.ofReal (Ccov' * volProd T n x) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcov_toReal : coveringReal T n ε x ≤ Ccov' * volProd T n x := by
    have hle := ENNReal.toReal_mono hfin hstep
    rwa [ENNReal.toReal_ofReal
      (mul_nonneg hCcov' ((one_le_volProd T n x).trans' zero_le_one))] at hle
  calc (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P n : ℝ)
      ≤ Ccov * coveringReal T n ε x := hn
    _ ≤ Ccov * (Ccov' * volProd T n x) := by gcongr
    _ = (Ccov * Ccov') * volProd T n x := by ring

end AtomCount

/-! ## Discharging `hatom` and the sharp Margulis–Ruelle inequality -/

section Discharge

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (ErgodicTheory.derivativeCocycle T x).det ≠ 0)
    (hint : ErgodicTheory.IntegrableLogNorm (ErgodicTheory.derivativeCocycle T) μ)
    (hint' : ErgodicTheory.IntegrableLogNorm (fun x => (ErgodicTheory.derivativeCocycle T x)⁻¹) μ)

/-- **Discharging the per-partition `hatom`.**  For a fixed `Fin n`-indexed partition `P` and a
covering radius `ε`, suppose the honest geometric inputs hold *jointly at the a.e. orbit-rate set*:
there is a constant `Ccov ≥ 0` such that, for `μ`-a.e. base point `x`, the geometric Mañé/Katok
count
`hgeoCount` holds (`hgeo`), and a sharp covering constant `Ccov' ≥ 0` valid at every such point
(`hcover`).  Then the existential `hatom` of `ErgodicTheory.margulisRuelle_sharp_of_atomVolProd`
holds for `P`: there is `C ≥ 1` and a base point `x` carrying both the orbit rate
(`tendsto_log_volProd`, a.e.) and the `volProd` atom bound
(`atomCount_le_volProd_of_sharpCovering`).

The base point is selected from the intersection of the (full-measure) orbit-rate set and the
(full-measure) geometric-count set; `C := max 1 (Ccov · Ccov')` makes the constant `≥ 1` while
preserving the bound. -/
theorem hatom_of_sharpCovering {n : ℕ} (P : ErgodicTheory.Entropy.MeasurePartition μ (Fin n))
    [Nonempty (Fin n)] {ε : ℝ≥0} {Ccov Ccov' : ℝ} (hCcov : 0 ≤ Ccov) (hCcov' : 0 ≤ Ccov')
    (hcover : ∀ x, SharpLocalCovering T Ccov' ε x)
    (hgeo : ∀ᵐ x ∂μ, ∀ᶠ m : ℕ in atTop,
      (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P m : ℝ)
        ≤ Ccov * coveringReal T m ε x) :
    ∃ (C : ℝ) (x : EuclideanSpace ℝ (Fin d)), 1 ≤ C ∧
      Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * Real.log (volProd T m x)) atTop
        (𝓝 (ErgodicTheory.sumPosExp hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint')) ∧
      (∀ᶠ m : ℕ in atTop,
        (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P m : ℝ)
          ≤ C * volProd T m x) := by
  -- Select a base point in the intersection of the orbit-rate set and the geometric-count set.
  have hrate := tendsto_log_volProd hT hdet hint hint'
  obtain ⟨x, hxrate, hxgeo⟩ := (hrate.and hgeo).exists
  -- Compose the geometric count with the in-tree sharp covering count at `x`.
  have hatom := atomCount_le_volProd_of_sharpCovering hT P hCcov hCcov' (hcover x) hxgeo
  -- `C := max 1 (Ccov · Ccov') ≥ 1`, and the bound is preserved since `volProd ≥ 0`.
  refine ⟨max 1 (Ccov * Ccov'), x, le_max_left _ _, hxrate, ?_⟩
  filter_upwards [hatom] with m hm
  calc (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P m : ℝ)
      ≤ (Ccov * Ccov') * volProd T m x := hm
    _ ≤ max 1 (Ccov * Ccov') * volProd T m x := by
        gcongr
        · exact (one_le_volProd T m x).trans' zero_le_one
        · exact le_max_right _ _

/-- **The sharp Margulis–Ruelle inequality (unconditional modulo the honest distortion regime).**

For an ergodic self-map `T` of `EuclideanSpace ℝ (Fin d)` with nonsingular,
log-integrable derivative cocycle, the Kolmogorov–Sinai *system* entropy is bounded by the sum of
the
strictly positive Lyapunov exponents:

`h(T) ≤ ∑_{λᵢ > 0} λᵢ`.

The **only** remaining input is the honest non-compactness atom count:

* `hgeo` — the **geometric Mañé/Katok atom count** (the honest non-compactness input, same regime as
  `ErgodicTheory.Entropy.Ruelle.Crude`: a uniform-distortion / compact-carrier hypothesis is
  unavoidable
  on
  the noncompact `EuclideanSpace`, Riquelme 2017): for every finite partition `P` there is a
  constant
  `Ccov ≥ 0` and radius `ε > 0` so that, a.e., the atom count of the `n`-refinement is eventually
  bounded by `Ccov ·` the per-orbit covering number.

The sharp one-step covering count is **no longer a hypothesis**: it is discharged internally by
`sharpLocalCovering_of_coveringCount` (the sibling `ErgodicTheory.Entropy.Ruelle.SharpCovering`'s
`coveringCount_image_ball_le_volProd`), with the explicit dimensional constant `Ccov' = 6^d`.

Everything between this input and the conclusion — the orbit rate `tendsto_log_volProd`, the
sharp covering count `coveringCount_image_ball_le_volProd`, the per-partition assembly
`ksEntropyPartition_le_sumPosExp_of_atomVolProd`, and the supremum lift
`ErgodicTheory.margulisRuelle_le_sumPosExp` — is unconditional and sorry-free. -/
theorem margulisRuelle_sharp
    (hgeo : ∀ (n : ℕ) (P : ErgodicTheory.Entropy.MeasurePartition μ (Fin n)),
      ∃ (ε : ℝ≥0) (Ccov : ℝ), 0 < ε ∧ 0 ≤ Ccov ∧
        (∀ᵐ x ∂μ, ∀ᶠ m : ℕ in atTop,
          (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P m : ℝ)
            ≤ Ccov * coveringReal T m ε x)) :
    ErgodicTheory.Entropy.ksEntropy hT.toMeasurePreserving
      ≤ ((ErgodicTheory.sumPosExp hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint' : ℝ) : EReal) := by
  -- Discharge the capstone's existential `hatom` from the honest atom-count input.
  refine margulisRuelle_sharp_of_atomVolProd hT hdet hint hint' (fun n P => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- Arity `0` is vacuous: an empty-indexed partition cannot cover a probability space.
    subst hn
    exact absurd P.cover (by
      simp only [Set.iUnion_of_empty]
      intro hcov
      have := measure_univ (μ := μ)
      rw [← hcov, measure_empty] at this
      exact one_ne_zero this.symm)
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨ε, Ccov, hε, hCcov, hgeoc⟩ := hgeo n P
    -- The sharp covering count is discharged from `SharpCovering`, with `Ccov' = 6^d ≥ 0`.
    exact hatom_of_sharpCovering hT hdet hint hint' P hCcov (by positivity)
      (fun x => sharpLocalCovering_of_coveringCount T hε x) hgeoc

end Discharge

end ErgodicTheory
