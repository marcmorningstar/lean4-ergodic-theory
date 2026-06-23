/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Oseledets.Entropy.CondPartition

/-!
# Lévy-upward continuity of conditional Shannon entropy

This file adds the **upward continuity** of conditional Shannon entropy to the conditional-entropy
milestone (GitHub issue #13), continuing `Oseledets.Entropy.CondPartition` (which defines
`condEntropy μ 𝒜 s` as the `μ`-average of the pointwise entropy against the regular conditional
probability `condExpKernel μ 𝒜 ω`).

The single result `condEntropy_tendsto_iSup` says: for an increasing sequence of conditioning
sub-σ-algebras `𝒜seq 0 ≤ 𝒜seq 1 ≤ ⋯ ≤ mα` and a *fixed* finite measurable partition `P`, the
conditional entropies `H(P | 𝒜seq n)` converge to the conditional entropy `H(P | ⨆ n, 𝒜seq n)` with
respect to the limiting (generated) σ-algebra. This is the specialization of Mathlib's almost-sure
**Lévy upward theorem** for conditional expectations (`MeasureTheory.tendsto_ae_condExp`) to the
nonlinear entropy functional; it is a load-bearing analytic sub-ingredient of issue #13's §5b.

The proof has three steps, run per cell `Pᵢ` of the partition:

* **Lévy upward (a.e.).** Bundling `𝒜seq` into a `MeasureTheory.Filtration ℕ mα`, Mathlib's
  `tendsto_ae_condExp` applied to the indicator `g_i = (Pᵢ).indicator (fun _ => 1)` gives
  `μ⟦Pᵢ | 𝒜seq n⟧ → μ⟦Pᵢ | ⨆ n, 𝒜seq n⟧` `μ`-a.e. The kernel-to-condExp bridge
  `condExpKernel_ae_eq_condExp` rewrites both sides as the kernel masses
  `(condExpKernel μ · ω Pᵢ).toReal`, so a.e. `ω` has
  `(condExpKernel μ (𝒜seq n) ω Pᵢ).toReal → (condExpKernel μ (⨆ n, 𝒜seq n) ω Pᵢ).toReal`.
* **Continuity of `negMulLog`.** Composing with the continuous `Real.negMulLog` and summing over the
  finite index `ι` gives a.e. convergence of the full `condEntropy` integrand.
* **Dominated convergence.** Each integrand is a.e. in `[0, log (card ι)]` (nonnegativity plus the
  pointwise Jensen bound `entropy_le_log_card`), so the constant `log (card ι)` is an integrable
  dominator on the probability space and `tendsto_integral_of_dominated_convergence` transfers the
  pointwise convergence to convergence of the integrals, i.e. of `condEntropy`.

## Main results

* `Oseledets.Entropy.condEntropy_tendsto_iSup`: conditional Shannon entropy is upward-continuous
  along an increasing sequence of conditioning σ-algebras (Lévy-upward continuity).

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM 79, Chapter 4.
-/

open MeasureTheory Function Filter ProbabilityTheory Set
open scoped ENNReal Topology

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α]

/-- **Lévy-upward continuity of conditional Shannon entropy.** For an increasing sequence of
conditioning sub-σ-algebras `𝒜seq 0 ≤ 𝒜seq 1 ≤ ⋯ ≤ mα` and a *fixed* finite measurable partition
`P` of the probability space, the conditional Shannon entropies `H(P | 𝒜seq n)` converge to the
conditional entropy `H(P | ⨆ n, 𝒜seq n)` with respect to the generated limiting σ-algebra.

This is the specialization of Mathlib's almost-sure **Lévy upward theorem**
(`MeasureTheory.tendsto_ae_condExp`) to the nonlinear conditional-entropy functional. Per cell
`Pᵢ`, the indicator's conditional expectations `μ⟦Pᵢ | 𝒜seq n⟧` converge a.e. to `μ⟦Pᵢ | ⨆ n⟧`;
via `condExpKernel_ae_eq_condExp` these are the kernel masses entering `condEntropy`, so composing
with the continuous `negMulLog` and summing over the finite index gives a.e. convergence of the
integrand. As the integrand lies a.e. in `[0, log (card ι)]`, the constant `log (card ι)` dominates
it and `tendsto_integral_of_dominated_convergence` yields convergence of the integrals. -/
theorem condEntropy_tendsto_iSup [Fintype ι] [Nonempty ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (𝒜seq : ℕ → MeasurableSpace α) (hmono : Monotone 𝒜seq) (hle : ∀ n, 𝒜seq n ≤ mα)
    (P : MeasurePartition μ ι) :
    Tendsto (fun n => condEntropy μ (𝒜seq n) P.cells) atTop
      (𝓝 (condEntropy μ (⨆ n, 𝒜seq n) P.cells)) := by
  -- Inclusion of the limiting σ-algebra in the ambient one.
  have hℬle : (⨆ n, 𝒜seq n) ≤ mα := iSup_le hle
  -- Bundle `𝒜seq` into a filtration; `ℱ n` is definitionally `𝒜seq n` and `⨆ n, ℱ n = ⨆ n, 𝒜seq n`.
  let ℱ : Filtration ℕ mα := ⟨𝒜seq, hmono, hle⟩
  -- Abbreviation for the indicator of a cell, used as the integrable input to Lévy's theorem.
  let g : ι → α → ℝ := fun i => (P.cells i).indicator (fun _ => (1 : ℝ))
  -- Step 1: per cell, a.e. Lévy-upward convergence of the kernel masses.
  have hcell : ∀ i, ∀ᵐ ω ∂μ, Tendsto
      (fun n => (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal) atTop
      (𝓝 (@condExpKernel α mα _ μ _ (⨆ n, 𝒜seq n) ω (P.cells i)).toReal) := by
    intro i
    -- Lévy upward for the indicator `g i` along the filtration `ℱ`.
    have hlevy : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g i | ℱ n]) ω) atTop
        (𝓝 ((μ[g i | ⨆ n, ℱ n]) ω)) :=
      MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (g i)
    -- The kernel mass at level `n` equals `μ⟦Pᵢ | 𝒜seq n⟧ = μ[g i | 𝒜seq n]` a.e.
    have haen : ∀ n, (fun ω => (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal)
        =ᵐ[μ] fun ω => (μ[g i | ℱ n]) ω := fun n => by
      simpa only [measureReal_def] using
        condExpKernel_ae_eq_condExp (hle n) (P.measurable i)
    -- The kernel mass at the limit equals `μ⟦Pᵢ | ⨆ n, 𝒜seq n⟧ = μ[g i | ⨆ n, ℱ n]` a.e.
    have haelim : (fun ω => (@condExpKernel α mα _ μ _ (⨆ n, 𝒜seq n) ω (P.cells i)).toReal)
        =ᵐ[μ] fun ω => (μ[g i | ⨆ n, ℱ n]) ω := by
      simpa only [measureReal_def] using
        condExpKernel_ae_eq_condExp hℬle (P.measurable i)
    filter_upwards [hlevy, ae_all_iff.2 haen, haelim] with ω hω hωn hωlim
    rw [hωlim]
    exact hω.congr fun n => (hωn n).symm
  -- Step 2: compose with continuous `negMulLog` and sum over the finite index.
  have hsum : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal)
      atTop
      (𝓝 (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (⨆ n, 𝒜seq n) ω (P.cells i)).toReal)) := by
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    refine tendsto_finsetSum _ fun i _ => ?_
    exact (Real.continuous_negMulLog.tendsto _).comp (hω i)
  -- Step 3: dominated convergence with the constant dominator `log (card ι)`.
  have hbound : ∀ n, ∀ᵐ ω ∂μ,
      ‖∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal‖
        ≤ Real.log (Fintype.card ι) := by
    intro n
    filter_upwards [condExpKernel_sum_toReal_measure_eq_one (hle n) P] with ω hω
    have hnn : 0 ≤ ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal :=
      negMulLog_condExpKernel_sum_nonneg P.cells ω
    have hle' := entropy_le_log_card (μ := @condExpKernel α mα _ μ _ (𝒜seq n) ω) P.cells hω
    rw [entropy_def] at hle'
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hmeasF : ∀ n, AEStronglyMeasurable
      (fun ω => ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal) μ :=
    fun n => (integrable_condEntropy_integrand (hle n) P.cells (fun i => P.measurable i)).1
  simpa only [condEntropy_def] using
    tendsto_integral_of_dominated_convergence (fun _ => Real.log (Fintype.card ι))
      hmeasF (integrable_const _) hbound hsum

end Oseledets.Entropy
