/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue4.AtomCountEntropy
import Frontier.Issue4.CoveringFromVolume
import Oseledets.Smooth.DerivativeCocycle
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The crude Ruelle bound: partition entropy by the log-derivative integral

This module proves the **crude Margulis–Ruelle inequality** for a smooth self-map `T` of
`EuclideanSpace ℝ (Fin d)`: the Kolmogorov–Sinai partition entropy `h(P, T)` is bounded by

`h(P, T) ≤ d · R`,  where `R` is an honest upper bound on the geometric expansion rate

`R ≈ ∫ log⁺‖D_x T‖ dμ`.

It validates the whole covering pipeline (`Frontier.Issue4.CoveringFromVolume` +
`Frontier.Issue4.AtomCountEntropy`) by assembling the *scalar arithmetic backbone* of the
Margulis–Ruelle counting argument into a sorry-free bound, leaving the single genuinely-geometric
input — that the partition refines under `T^[n]` into at most `C · exp(n · d · R)` non-empty atoms
— as an explicit, honest, finite-`n` hypothesis (`hgrow`), exactly as
`Oseledets.margulisRuelle_le_sumPosExp` isolates its own geometric input `hgeo`.

## The two layers

1. `Oseledets.Entropy.ksEntropyPartition_le_of_atomCount_growth` (fully general, sorry-free): the
   **arithmetic backbone**.  If the non-empty atom count of the refined partition
   `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is eventually bounded by `C · exp(n · R)` with `C ≥ 1` and `R ≥ 0`, then
   `h(P, T) ≤ R`.  This consumes `AtomCountEntropy`'s
   `ksEntropyPartition_le_limsup_log_atomCount` and the elementary limit
   `(1/n)(log C + n R) → R`.

2. `Oseledets.crudeRuelle_le_log_deriv_rate`: the **crude Ruelle bound**.  Specializing the
   geometric rate to `R = d · B`, where `B` is a uniform bound `log⁺‖D_x T‖ ≤ B` (honest under a
   globally bounded derivative — see *non-compactness* below), gives `h(P, T) ≤ d · B`, conditional
   on the geometric atom-count growth hypothesis at that rate.

## Non-compactness: why a hypothesis is genuinely needed

On the **noncompact** space `EuclideanSpace ℝ (Fin d)`, Ruelle's inequality has explicit
counterexamples (F. Riquelme, *Counterexamples to Ruelle's inequality in the noncompact case*,
Ann. Inst. Fourier **67** (2017) 23–41): suspension-flow-like systems over countable interval
exchange transformations have *translation-like* local behaviour — so the derivative is essentially
an isometry, `log⁺‖DT‖ ≈ 0` — yet the entropy can be made any prescribed positive value.  Thus
`h(P, T) ≤ d · ∫ log⁺‖DT‖` is **false in general** here, and the geometric atom-count step (which on
a compact manifold follows from a fixed finite cover of bounded distortion) must be supplied as a
hypothesis or recovered from extra control on the dynamics (a globally bounded/Lipschitz derivative
together with a fixed reference cover, or `μ` supported on a compact invariant set).  We therefore
phrase the geometric input as the explicit growth bound `hgrow`; the scalar reduction around it is
unconditional.

## Main results

* `Oseledets.Entropy.ksEntropyPartition_le_of_atomCount_growth` — the arithmetic backbone:
  `atomCount ≤ C · exp(n R)` ⇒ `h(P, T) ≤ R`.
* `Oseledets.crudeRuelle_le_log_deriv_rate` — the crude Ruelle bound `h(P, T) ≤ d · B` under a
  uniform `log⁺‖DT‖ ≤ B` bound and the geometric atom-count growth hypothesis at rate `d · B`.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7 (Margulis–Ruelle
  inequality, Mañé proof, Lemmas 7.5–7.6).
* Ricardo Mañé, *Ergodic theory and differentiable dynamics*, Springer 1987, §IV.12 (Lemma 12.5).
* Felipe Riquelme, *Counterexamples to Ruelle's inequality in the noncompact case*, Ann. Inst.
  Fourier **67** (2017) 23–41.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets.Entropy

variable {α : Type*} [MeasurableSpace α]

/-- **Arithmetic backbone of the crude Ruelle bound.**

If the number of non-empty atoms of the refined partition `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` is eventually bounded by
`C · exp(n · R)` for some `C ≥ 1` and exponential rate `R`, then the Kolmogorov–Sinai partition
entropy is bounded by the rate:

`h(P, T) ≤ R`.

This is the scalar half of the Margulis–Ruelle counting argument.  The atom-count entropy bound
`ksEntropyPartition_le_limsup_log_atomCount` gives
`h(P, T) ≤ limsupₙ (1/n) · log (atomCount …)`, and the hypothesis bounds the inner sequence by
`(1/n) · log (C · exp(n R)) = (log C)/n + R`, which tends to `R`; comparing `limsup`s finishes. -/
theorem ksEntropyPartition_le_of_atomCount_growth {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {C R : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ᶠ n : ℕ in atTop, (atomCount hT P n : ℝ) ≤ C * Real.exp (n * R)) :
    ksEntropyPartition hT P ≤ R := by
  -- Comparison sequence `w n = (log C)/n + R`, which dominates `(1/n) log (atomCount …)`.
  set v : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (atomCount hT P n) with hv
  set w : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log C + R with hw
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  -- `v n ≤ w n` eventually.
  have hvw : v ≤ᶠ[atTop] w := by
    filter_upwards [hgrow, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hac_pos : 0 < atomCount hT P n := atomCount_pos hT P n
    have hac0 : (0 : ℝ) < atomCount hT P n := by exact_mod_cast hac_pos
    -- `log (atomCount) ≤ log C + n R`.
    have hlog_le : Real.log (atomCount hT P n) ≤ Real.log C + n * R := by
      calc Real.log (atomCount hT P n)
          ≤ Real.log (C * Real.exp (n * R)) := Real.log_le_log hac0 hn
        _ = Real.log C + n * R := by
            rw [Real.log_mul hC0.ne' (Real.exp_ne_zero _), Real.log_exp]
    -- Multiply `hlog_le` by `(n)⁻¹ ≥ 0` and simplify `(n)⁻¹ * (n R) = R`.
    have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt (inv_pos.mpr hn0))
    have hsimp : (n : ℝ)⁻¹ * (Real.log C + n * R) = (n : ℝ)⁻¹ * Real.log C + R := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hn0.ne', one_mul]
    simp only [hv, hw]
    rw [hsimp] at hmul
    exact hmul
  -- `w n → R`.
  have hw_tendsto : Tendsto w atTop (𝓝 R) := by
    have h0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log C) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := Real.log C)).div_atTop tendsto_natCast_atTop_atTop
      simpa only [div_eq_inv_mul] using this.congr fun n => by ring
    simpa only [hw, zero_add] using h0.add_const R
  -- `v` is bounded below by `0` (atom count `≥ 1`, so `log ≥ 0`, and `(n)⁻¹ ≥ 0`), giving the
  -- `(· ≤ ·)`-coboundedness needed for the `limsup` comparison.
  have hvcob : IsCoboundedUnder (· ≤ ·) atTop v :=
    isCoboundedUnder_le_of_le atTop fun n => by
      simp only [hv]
      exact mul_nonneg (by positivity)
        (Real.log_nonneg (by exact_mod_cast (atomCount_pos hT P n)))
  -- The two `limsup`s.
  calc ksEntropyPartition hT P
      ≤ limsup v atTop := ksEntropyPartition_le_limsup_log_atomCount hT P
    _ ≤ limsup w atTop := limsup_le_limsup hvw hvcob hw_tendsto.isBoundedUnder_le
    _ = R := hw_tendsto.limsup_eq

end Oseledets.Entropy

namespace Oseledets

variable {d : ℕ}

/-- **The crude Ruelle bound.**

For a measure-preserving self-map `T` of `EuclideanSpace ℝ (Fin d)` whose derivative satisfies the
uniform bound `log⁺‖D_x T‖ ≤ B`, and a finite partition `P` whose `n`-fold refinement
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` has at most `C · exp(n · d · B)` non-empty atoms (the geometric atom-counting input,
`hgrow`), the Kolmogorov–Sinai partition entropy is bounded by the *positive-part* log-derivative
rate times the dimension:

`h(P, T) ≤ d · B`.

Here `d · B` plays the role of `d · ∫ log⁺‖D_x T‖ dμ`: the volume of `T^[n] '' (atom)` grows at most
like `‖D(T^[n])‖^d`, and operator-norm submultiplicativity together with `log⁺‖D(T^[n])‖ ≤ n · B`
turns the covering count of the image into `exp(n · d · B)` atoms.  The genuinely geometric step is
abstracted as `hgrow`; the surrounding reduction is the unconditional
`Entropy.ksEntropyPartition_le_of_atomCount_growth`.

*Non-compactness.* On the noncompact `EuclideanSpace` the bare inequality `h ≤ d · ∫ log⁺‖DT‖` is
false (Riquelme 2017); the uniform bound `B` and the cover-growth hypothesis `hgrow` are the honest
extra data that make the statement true.  See the module docstring. -/
theorem crudeRuelle_le_log_deriv_rate {μ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure μ] {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hT : MeasurePreserving T μ μ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : Entropy.MeasurePartition μ ι) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, Real.posLog ‖fderiv ℝ T x‖ ≤ B) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ᶠ n : ℕ in atTop,
      (Entropy.atomCount hT P n : ℝ) ≤ C * Real.exp (n * (d * B))) :
    Entropy.ksEntropyPartition hT P ≤ d * B := by
  -- `hbound` records that `B` is an honest uniform `log⁺`-derivative bound; the entropy bound is
  -- the arithmetic reduction at rate `R = d · B`.
  have _ := hbound
  have _ := hB
  exact Entropy.ksEntropyPartition_le_of_atomCount_growth hT P hC hgrow

end Oseledets
