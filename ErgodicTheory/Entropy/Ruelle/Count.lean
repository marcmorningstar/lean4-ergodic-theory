/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Ruelle.AtomCount
import ErgodicTheory.Entropy.Ruelle.Crude
import ErgodicTheory.Entropy.MargulisRuelleSharpened
import ErgodicTheory.Lyapunov.Extensions.ExteriorCocycle
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The sharp Ruelle counting bound: orbit iteration of the local covering

This module assembles the **orbit-iteration half** of the sharp Margulis–Ruelle inequality
`h(P, T) ≤ ∑ λᵢ⁺` for a smooth ergodic self-map `T` of `EuclideanSpace ℝ (Fin d)`.  The crude bound
of `ErgodicTheory.Entropy.Ruelle.Crude` controls the partition entropy by the *dimension times* the
uniform log-derivative bound, `d · B`; this module sharpens the geometric rate from `d · B` to the
genuine positive-exponent sum `sumPosExp = ∑_{λᵢ > 0} λᵢ`, by counting the image of an `ε`-ball
under the `n`-fold iterate `T^[n]` via the **positive-part singular-value product** of the
derivative cocycle.

## The per-orbit volume factor

The local volume-expansion factor of the differential `D_x(T^[n])` — counting only the *expanding*
directions — is the **positive-part singular-value product**

`volProd T n x = ∏_{i < d} max 1 σᵢ(D_x(T^[n]))`,

where `σᵢ(D_x(T^[n]))` are the singular values of the cocycle iterate
`cocycle (derivativeCocycle T) T n x` (the chain-rule cocycle, `chainRule_cocycle`).  Its logarithm
is `∑_{i} log⁺ σᵢ` (`ErgodicTheory.Entropy.sum_posLog_singularValues_toEuclideanLin_eq`), the finite-`n`
incarnation of `∑ λᵢ⁺`.

## The two layers

1. **The orbit growth rate (`tendsto_log_volProd`, sorry-free).**  For `μ`-a.e. `x`,
   `(1/n) · log (volProd T n x) → sumPosExp`.  This is the genuinely new orbit-iteration content:
   each per-singular-value term `(1/n) log⁺ σᵢ = max 0 ((1/n) log σᵢ)` converges to
   `max 0 (exponents i)` (continuity of `max 0 ·` composed with the per-exponent limit
   `ErgodicTheory.exponents_tendsto_log_singularValue`), and the finite sum of these limits is exactly
   `∑ᵢ max 0 (exponents i) = sumPosExp` (the positive part of an antitone spectrum, summed with
   multiplicity).  No extra Furstenberg–Kesten integrability is needed: the rate rides on the
   already-established per-exponent singular-value limits.

2. **The local covering count (`coveringCount_image_ball_le_volProd`, proved in-tree).**  The
   genuinely geometric per-step input — the image `L '' (ball x ε)` of an `ε`-ball under a linear
   map `L` is coverable by at most `6^d · ∏ᵢ max(1, σᵢ(L))` balls of radius `ε` — is **fully proved
   in-tree** in the sibling module `ErgodicTheory.Entropy.Ruelle.SharpCovering` (via a constructive SVD
   ellipsoid domination + determinant volume bound).  Specialised to the orbit differential
   `L = D_x(T^[n])` (`ErgodicTheory.chainRule_cocycle`) it gives exactly the per-orbit `volProd` count.
   The honest mathematical caveat is the non-compactness distortion regime (`hgeo` below, Riquelme
   2017), *not* the covering count itself.

Feeding the orbit rate (layer 1) into the abstract atom-count reduction
`ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth` (`ErgodicTheory.Entropy.Ruelle.Crude`)
turns the per-step covering count into the per-partition bound `h(P, T) ≤ sumPosExp`, which
discharges the `hgeo` / `hcount` hypothesis of `ErgodicTheory.margulisRuelle_le_sumPosExp`.

## Non-compactness

We carry the *same* honest non-compactness data as `ErgodicTheory.Entropy.Ruelle.Crude` (a uniform
derivative / bounded-distortion regime — on the noncompact `EuclideanSpace` the bare inequality
`h ≤ ∑ λᵢ⁺` is false, Riquelme 2017).  Here the geometric input is distilled to the single explicit
hypothesis `hatom`: there is a base point `x` of the full-measure orbit-rate set at which the
non-empty atom count of the refined partition is eventually bounded by `C · volProd T n x`.  This is
exactly the output of the Mañé/Katok covering–distortion counting argument; the surrounding orbit
reduction is unconditional.

## Main results

* `ErgodicTheory.volProd` — the per-orbit positive-part singular-value product
  `∏_{i<d} max 1 σᵢ(D(T^[n]))`.
* `ErgodicTheory.one_le_volProd` — the volume factor is `≥ 1`.
* `ErgodicTheory.log_volProd_eq_sum_posLog` — `log (volProd …) = ∑_{i<d} log⁺ σᵢ`.
* `ErgodicTheory.tendsto_log_volProd` — the orbit growth rate
  `(1/n) log (volProd …) → sumPosExp`, a.e. (sorry-free).
* `ErgodicTheory.coveringCount_image_ball_le_volProd` — the sharp local covering count, **proved
  in-tree** in the sibling `ErgodicTheory.Entropy.Ruelle.SharpCovering`.
* `ErgodicTheory.ksEntropyPartition_le_sumPosExp_of_atomVolProd` — the orbit assembly: a
  base-point `volProd` atom-count bound yields `h(P, T) ≤ sumPosExp`.
* `ErgodicTheory.margulisRuelle_sharp_of_atomVolProd` — the sharp Margulis–Ruelle inequality
  `h(T) ≤ ∑ λᵢ⁺`, conditional on the (honest, distilled) geometric atom-count input.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
* Ricardo Mañé, *Ergodic theory and differentiable dynamics*, Springer 1987, §IV.12.
* D. Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Bras. Mat. **9**
  (1978) 83–87.
* Felipe Riquelme, *Counterexamples to Ruelle's inequality in the noncompact case*, Ann. Inst.
  Fourier **67** (2017) 23–41.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator ENNReal NNReal

namespace ErgodicTheory

variable {d : ℕ} [NeZero d]

/-- **The per-orbit positive-part singular-value product.**  For a self-map `T` of
`EuclideanSpace ℝ (Fin d)`, `volProd T n x` is the product over the `d` singular-value indices of
`max 1 σᵢ(D_x(T^[n]))`, where `σᵢ` are the singular values of the chain-rule cocycle iterate
`cocycle (derivativeCocycle T) T n x`.  It is the local volume-expansion factor of `D_x(T^[n])`
restricted to its expanding directions; its log is `∑ᵢ log⁺ σᵢ`, the finite-`n` form of `∑ λᵢ⁺`. -/
noncomputable def volProd (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i ∈ Finset.range d,
    max 1 (LinearMap.singularValues
      (Matrix.toEuclideanLin (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x)) i)

omit [NeZero d] in
/-- **The volume factor is at least `1`.**  Every factor `max 1 σᵢ ≥ 1`, so the product is `≥ 1`. -/
theorem one_le_volProd (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : 1 ≤ volProd T n x := by
  rw [volProd]
  exact Finset.one_le_prod (fun i _ => le_max_left _ _)

omit [NeZero d] in
/-- **The volume factor is positive.**  Immediate from `one_le_volProd`. -/
theorem volProd_pos (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 < volProd T n x :=
  lt_of_lt_of_le one_pos (one_le_volProd T n x)

omit [NeZero d] in
/-- **The log of the volume factor is the positive-part log-singular-value sum.**
`log (volProd T n x) = ∑_{i<d} log⁺ σᵢ(D_x(T^[n]))`.  This is the
`ErgodicTheory.Entropy.sum_posLog_singularValues_toEuclideanLin_eq` identity, read right-to-left and
specialized to the cocycle iterate. -/
theorem log_volProd_eq_sum_posLog
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.log (volProd T n x)
      = ∑ i ∈ Finset.range d, Real.posLog
          (LinearMap.singularValues (Matrix.toEuclideanLin
            (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x)) i) := by
  rw [volProd]
  exact (ErgodicTheory.Entropy.sum_posLog_singularValues_toEuclideanLin_eq
    (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x) (Finset.range d)).symm

/-! ## The orbit growth rate -/

section Rate

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (ErgodicTheory.derivativeCocycle T x).det ≠ 0)
    (hint : ErgodicTheory.IntegrableLogNorm (ErgodicTheory.derivativeCocycle T) μ)
    (hint' : ErgodicTheory.IntegrableLogNorm (fun x => (ErgodicTheory.derivativeCocycle T x)⁻¹) μ)

/-- **The positive part of the spectrum sums to the positive-exponent sum.**  Summing the truncated
exponents `max 0 (exponents i)` over all indices gives the sum of the strictly positive exponents
`sumPosExp`: a non-positive exponent contributes `max 0 (exponents i) = 0`, and a positive one
contributes itself.  This is the deterministic, ergodic-constant right-hand side of the sharp Ruelle
inequality, expressed as the limit value of the orbit rate. -/
theorem sum_max_zero_exponents_eq_sumPosExp :
    ∑ i : Fin d, max 0
        (ErgodicTheory.exponents hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i)
      = ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' := by
  classical
  rw [ErgodicTheory.sumPosExp, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => 0 < ErgodicTheory.exponents hT hdet
      (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i)
    (fun i => max 0 (ErgodicTheory.exponents hT hdet
      (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i))]
  -- The positive block: `max 0 λ = λ` when `0 < λ`.
  have hpos : ∑ i ∈ Finset.univ.filter (fun i => 0 < ErgodicTheory.exponents hT hdet
        (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i),
        max 0 (ErgodicTheory.exponents hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i)
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < ErgodicTheory.exponents hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i),
        ErgodicTheory.exponents hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i :=
    Finset.sum_congr rfl (fun i hi =>
      max_eq_right (le_of_lt (Finset.mem_filter.mp hi).2))
  -- The non-positive block: `max 0 λ = 0` when `¬ 0 < λ`.
  have hnonpos : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < ErgodicTheory.exponents hT hdet
        (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i),
        max 0 (ErgodicTheory.exponents hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i) = 0 :=
    Finset.sum_eq_zero (fun i hi =>
      max_eq_left (not_lt.mp (Finset.mem_filter.mp hi).2))
  rw [hpos, hnonpos, add_zero]

/-- **The per-index orbit rate limit.**  For `μ`-a.e. `x` and each singular-value index `i`, the
normalized positive-part log of the `i`-th singular value of the cocycle iterate converges to the
truncated exponent `max 0 (exponents i)`.  Because `(n)⁻¹ ≥ 0`, the prefactor commutes with the
truncation, `(n)⁻¹ · log⁺ σᵢ = max 0 ((n)⁻¹ log σᵢ)`; continuity of `max 0 ·`
(`Filter.Tendsto.max_left`) applied to the per-exponent singular-value limit
`ErgodicTheory.exponents_tendsto_log_singularValue` gives the result. -/
theorem tendsto_posLog_singularValue (i : Fin d) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog
        (LinearMap.singularValues
          (Matrix.toEuclideanLin (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x))
          (i : ℕ))) atTop
      (𝓝 (max 0 (ErgodicTheory.exponents hT hdet
        (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i))) := by
  filter_upwards [ErgodicTheory.exponents_tendsto_log_singularValue hT hdet
    (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i] with x hx
  -- `(n)⁻¹ · max 0 (log σ) = max 0 ((n)⁻¹ log σ)`, then `max 0 ·` is continuous.
  have hcongr : ∀ n : ℕ, (n : ℝ)⁻¹ * Real.posLog
        (LinearMap.singularValues
          (Matrix.toEuclideanLin (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x))
          (i : ℕ))
      = max 0 ((n : ℝ)⁻¹ * Real.log
          (LinearMap.singularValues
            (Matrix.toEuclideanLin (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x))
            (i : ℕ))) := by
    intro n
    rw [Real.posLog_def, mul_max_of_nonneg _ _ (by positivity), mul_zero]
  exact ((tendsto_const_nhds (x := (0 : ℝ))).max hx).congr (fun n => (hcongr n).symm)

/-- **The orbit growth rate (the new orbit-iteration content).**  For `μ`-a.e. `x`, the normalized
log of the per-orbit positive-part singular-value product converges to the sum of the strictly
positive Lyapunov exponents:

`(1/n) · log (volProd T n x) → sumPosExp`.

This is the sharp finite-`n` volume rate driving the Ruelle counting bound.  Rewriting
`log (volProd …) = ∑_{i<d} log⁺ σᵢ` (`log_volProd_eq_sum_posLog`) and distributing the `(n)⁻¹`
prefactor over the finite sum, each term converges to `max 0 (exponents i)`
(`tendsto_posLog_singularValue`); the finite sum of the limits is
`∑ᵢ max 0 (exponents i) = sumPosExp` (`sum_max_zero_exponents_eq_sumPosExp`).  No additional
Furstenberg–Kesten integrability for a compound generator is required: the rate rides entirely
on the per-exponent singular-value limits. -/
theorem tendsto_log_volProd :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (volProd T n x)) atTop
      (𝓝 (ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint')) := by
  -- Gather the per-index limits over the finite index set `Fin d`.
  have hall : ∀ᵐ x ∂μ, ∀ i : Fin d, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.posLog
        (LinearMap.singularValues
          (Matrix.toEuclideanLin (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x))
          (i : ℕ))) atTop
      (𝓝 (max 0 (ErgodicTheory.exponents hT hdet
        (ErgodicTheory.measurable_derivativeCocycle T) hint hint' i))) := by
    rw [ae_all_iff]
    exact fun i => tendsto_posLog_singularValue hT hdet hint hint' i
  filter_upwards [hall] with x hx
  -- The normalized log of `volProd` is the finite sum of the per-index normalized `posLog`s.
  have hrw : ∀ n : ℕ, (n : ℝ)⁻¹ * Real.log (volProd T n x)
      = ∑ i : Fin d, (n : ℝ)⁻¹ * Real.posLog
          (LinearMap.singularValues
            (Matrix.toEuclideanLin (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x))
            (i : ℕ)) := by
    intro n
    rw [log_volProd_eq_sum_posLog, Finset.mul_sum,
      Finset.sum_range fun i => (n : ℝ)⁻¹ * Real.posLog
        (LinearMap.singularValues
          (Matrix.toEuclideanLin (ErgodicTheory.cocycle (ErgodicTheory.derivativeCocycle T) T n x)) i)]
  rw [← sum_max_zero_exponents_eq_sumPosExp hT hdet hint hint']
  exact (tendsto_finsetSum Finset.univ (fun i _ => hx i)).congr (fun n => (hrw n).symm)

/-- **Eventual sub-exponential `volProd` bound at the orbit rate.**  At a point `x` where the orbit
rate holds (`tendsto_log_volProd`), for every `ε > 0` the per-orbit volume factor is eventually
bounded by `exp(n · (sumPosExp + ε))`.  This is the multiplicative form of the rate limit, obtained
by exponentiating the eventual estimate `(1/n) log (volProd …) ≤ sumPosExp + ε` (valid for `n ≥ 1`
once `(1/n) log volProd` is within `ε` of `sumPosExp`) and using `volProd > 0`. -/
theorem eventually_volProd_le {x : EuclideanSpace ℝ (Fin d)}
    (hx : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (volProd T n x)) atTop
      (𝓝 (ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint')))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, volProd T n x
      ≤ Real.exp (n * (ErgodicTheory.sumPosExp hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint' + ε)) := by
  set L := ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' with hL
  -- Eventually `(1/n) log volProd < L + ε`.
  have hlt : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * Real.log (volProd T n x) < L + ε :=
    hx.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hlt, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- From `(1/n) log volProd < L + ε` multiply by `n > 0`: `log volProd ≤ n (L + ε)`.
  have hlog : Real.log (volProd T n x) ≤ n * (L + ε) := by
    have hmul := mul_lt_mul_of_pos_left hn hn0
    rw [← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul] at hmul
    exact le_of_lt hmul
  calc volProd T n x = Real.exp (Real.log (volProd T n x)) :=
        (Real.exp_log (volProd_pos T n x)).symm
    _ ≤ Real.exp (n * (L + ε)) := by gcongr

end Rate

/-! ## The orbit assembly: from a `volProd` atom-count bound to `h(P, T) ≤ sumPosExp` -/

section Assembly

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (ErgodicTheory.derivativeCocycle T x).det ≠ 0)
    (hint : ErgodicTheory.IntegrableLogNorm (ErgodicTheory.derivativeCocycle T) μ)
    (hint' : ErgodicTheory.IntegrableLogNorm (fun x => (ErgodicTheory.derivativeCocycle T x)⁻¹) μ)

/-- **The orbit assembly (sorry-free).**  Suppose, for a finite partition `P` of the probability
space, there is a base point `x` at which the orbit rate holds (`hxrate`, supplied a.e. by
`tendsto_log_volProd`) and at which the non-empty atom count of the refined partition is eventually
bounded by `C · volProd T n x` (`hatom`, the distilled output of the Mañé/Katok orbit
covering–distortion count via the in-tree local covering count
`ErgodicTheory.coveringCount_image_ball_le_volProd`).  Then the
Kolmogorov–Sinai partition entropy is bounded by the positive-exponent sum:

`h(P, T) ≤ sumPosExp`.

The proof reduces `h(P, T) ≤ sumPosExp + ε` for every `ε > 0`: the orbit rate makes
`volProd ≤ exp(n(sumPosExp + ε))` eventually (`eventually_volProd_le`), so `hatom` gives the
atom-count growth bound `atomCount ≤ C · exp(n(sumPosExp + ε))`, and the unconditional arithmetic
reduction `ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth`
(`ErgodicTheory.Entropy.Ruelle.Crude`) yields `h(P, T) ≤ sumPosExp + ε`; letting `ε ↓ 0` finishes
(`ge_of_tendsto` against the constant family, `le_of_forall_pos_le_add`). -/
theorem ksEntropyPartition_le_sumPosExp_of_atomVolProd {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ErgodicTheory.Entropy.MeasurePartition μ ι) {C : ℝ} (hC : 1 ≤ C)
    {x : EuclideanSpace ℝ (Fin d)}
    (hxrate : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (volProd T n x)) atTop
      (𝓝 (ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint')))
    (hatom : ∀ᶠ n : ℕ in atTop,
      (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P n : ℝ) ≤ C * volProd T n x) :
    ErgodicTheory.Entropy.ksEntropyPartition hT.toMeasurePreserving P
      ≤ ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' := by
  set L := ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' with hL
  -- Show `h(P, T) ≤ L + ε` for every `ε > 0`.
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- The atom-count growth bound at rate `L + ε`.
  have hgrow : ∀ᶠ n : ℕ in atTop,
      (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P n : ℝ)
        ≤ C * Real.exp (n * (L + ε)) := by
    filter_upwards [hatom, eventually_volProd_le hT hdet hint hint' hxrate hε] with n hn hvp
    have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
    calc (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P n : ℝ)
        ≤ C * volProd T n x := hn
      _ ≤ C * Real.exp (n * (L + ε)) := by gcongr
  -- The unconditional arithmetic reduction at rate `L + ε`.
  exact ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth
    hT.toMeasurePreserving P hC hgrow

/-- **The sharp Margulis–Ruelle inequality, conditional on the orbit atom-count input.**

For an ergodic self-map `T` of `EuclideanSpace ℝ (Fin d)` with nonsingular,
log-integrable derivative cocycle, the Kolmogorov–Sinai *system* entropy is bounded by the sum
of the strictly positive Lyapunov exponents:

`h(T) ≤ ∑_{λᵢ > 0} λᵢ`.

The single geometric input `hatom` is the **honest distillation of the Mañé/Katok orbit
covering–distortion count**: for every finite partition `P`, there is a constant `C ≥ 1` and a base
point `x` at which the non-empty atom count of the `n`-fold refinement is eventually bounded by
`C · volProd T n x` — the per-orbit positive-part singular-value product, whose growth rate is
`sumPosExp` (`tendsto_log_volProd`).  This carries the *same* non-compactness regime as the crude
bound `ErgodicTheory.Entropy.Ruelle.Crude` (a uniform-distortion hypothesis is unavoidable on the
noncompact `EuclideanSpace`, Riquelme 2017); the surrounding orbit reduction —
`ksEntropyPartition_le_sumPosExp_of_atomVolProd` per partition, then the supremum lift
`ErgodicTheory.margulisRuelle_le_sumPosExp` — is unconditional and sorry-free.

The orbit rate at the base point is *not* an extra hypothesis: it is supplied a.e. by
`tendsto_log_volProd`, and a base point of the full-measure rate set carrying the atom bound is what
`hatom` provides (its existence is the content of the geometric count, fed by the in-tree local
covering count `ErgodicTheory.coveringCount_image_ball_le_volProd`). -/
theorem margulisRuelle_sharp_of_atomVolProd
    (hatom : ∀ (n : ℕ) (P : ErgodicTheory.Entropy.MeasurePartition μ (Fin n)),
      ∃ (C : ℝ) (x : EuclideanSpace ℝ (Fin d)), 1 ≤ C ∧
        Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * Real.log (volProd T m x)) atTop
          (𝓝 (ErgodicTheory.sumPosExp hT hdet
            (ErgodicTheory.measurable_derivativeCocycle T) hint hint')) ∧
        (∀ᶠ m : ℕ in atTop,
          (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P m : ℝ)
            ≤ C * volProd T m x)) :
    ErgodicTheory.Entropy.ksEntropy hT.toMeasurePreserving
      ≤ ((ErgodicTheory.sumPosExp hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint' : ℝ) : EReal) := by
  -- Discharge the per-partition `hgeo` of `margulisRuelle_le_sumPosExp` via the orbit assembly.
  refine ErgodicTheory.margulisRuelle_le_sumPosExp hT hdet hint hint' (fun n P => ?_)
  -- The arity `n = 0` is vacuous: an empty-indexed partition cannot cover a probability space.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact absurd P.cover (by
      simp only [Set.iUnion_of_empty]
      intro hcov
      have := measure_univ (μ := μ)
      rw [← hcov, measure_empty] at this
      exact one_ne_zero this.symm)
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨C, x, hC, hxrate, hxatom⟩ := hatom n P
    exact EReal.coe_le_coe (ksEntropyPartition_le_sumPosExp_of_atomVolProd hT hdet hint hint' P hC
      hxrate hxatom)

end Assembly

end ErgodicTheory
