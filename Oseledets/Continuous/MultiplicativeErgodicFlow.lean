/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.Flow
import Oseledets.Continuous.Reduction
import Oseledets.Continuous.BetweenTimes
import Oseledets.Continuous.Equivariance
import Oseledets.Lyapunov.Corollaries

/-!
# The continuous-flow Oseledets multiplicative ergodic theorem

This file contains the continuous-flow Oseledets multiplicative ergodic theorem (MET):
`Oseledets.oseledets_flow`. It is the continuous-time analogue of the discrete-time target
`Oseledets.oseledets_filtration`, stated over a measure-preserving one-parameter flow `φ`
(`Oseledets.MeasurePreservingFlow`) and a continuous-time linear cocycle `A`
(`Oseledets.FlowCocycle`).

The proof combines four continuous-flow ingredients:

* **Reduction** (`Oseledets.exists_isOseledetsFiltration_timeOne`): the discrete MET applied to
  the generator `A 1` over the ergodic time-`1` dynamics `φ 1` produces an Oseledets filtration
  for the time-`1` cocycle map. This yields the dimension `k`, the exponents `lam`, the
  measurable subspace family `V`, the strictly decreasing flag, and the integer-time growth
  rates.
* **Equivariance** (`Oseledets.ae_flow_equivariant`): for every fixed time `t₀`, the time-`t₀`
  cocycle map sends each level of the filtration at `x` onto the corresponding level at
  `φ t₀ x`, almost everywhere. This upgrades the discrete (time-`1`) equivariance to the full
  continuous flow.
* **Error sublinearity** (`Oseledets.ae_tendsto_flowError_zero`): the integrable controls
  fluctuate sublinearly along the integer orbit of the flow, almost everywhere.
* **Between-times limit** (`Oseledets.tendsto_log_norm_atTop_of_discrete`): the integer-time
  growth rate of a vector forces the *continuous-time* growth rate `t⁻¹ log ‖A t x v‖` to the
  same limit as `t → ∞`.

## Main statements

* `Oseledets.oseledets_flow`: the continuous-flow Oseledets MET. For an ergodic
  (at time `1`) measure-preserving flow `φ` on a probability space and a continuous-time linear
  cocycle `A` whose one-step log-norms are dominated uniformly on `[0,1]` by integrable
  functions, almost every point carries a strictly decreasing, fully flow-equivariant Oseledets
  flag whose strata realise the exponents `lam i` as continuous-time growth rates.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} {μ : Measure X}

/-- **The continuous-flow Oseledets multiplicative ergodic theorem.**

Let `μ` be a probability measure on `X`, let `φ` be a measure-preserving one-parameter flow
whose time-`1` map is `μ`-ergodic, and let `A` be a continuous-time linear cocycle over `φ`
valued in invertible `d × d` real matrices. Assume the one-step log-norms are controlled
uniformly on `[0,1]` by integrable functions: `log⁺ ‖A s x‖ ≤ g x` and
`log⁺ ‖(A s x)⁻¹‖ ≤ g' x` for all `s ∈ [0,1]` and `x`, with `g, g' ∈ L¹(μ)`.

Then there is a finite Oseledets spectrum: a number `k` of distinct Lyapunov exponents
`lam : Fin k → ℝ` (strictly decreasing) and a measurable family of nested subspaces
`V : Fin (k+1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))` such that:

* the exponents are strictly decreasing;
* each level `V i` is a measurable family of subspaces;
* **(full flow equivariance)** for every time `t`, almost every `x` has each level mapped by
  the time-`t` cocycle onto the level at the flowed point: `A t x · V i x = V i (φ t x)`;
* almost every `x` carries the strictly decreasing flag `⊤ = V 0 x ⊋ ⋯ ⊋ V k x = ⊥`, and on
  each stratum `V i \ V (i+1)` the **continuous-time** growth rate is exactly `lam i`:
  `t⁻¹ log ‖A t x v‖ → lam i` as `t → ∞`. -/
theorem oseledets_flow [IsProbabilityMeasure μ]
    (φ : MeasurePreservingFlow μ) (herg : Ergodic (φ 1) μ)
    (A : FlowCocycle φ d)
    (g g' : X → ℝ) (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, Real.posLog ‖A s x‖ ≤ g x)
    (hg'b : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, Real.posLog ‖(A s x)⁻¹‖ ≤ g' x) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => V i x) ∧
      (∀ t : ℝ, ∀ᵐ x ∂μ, ∀ i : Fin (k + 1),
        Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)).toLinearMap (V i x) = V i (φ t x)) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
          v ∉ V i.succ x →
          Tendsto (fun t : ℝ => t⁻¹ *
            Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x) v‖) atTop (𝓝 (lam i))) := by
  obtain ⟨k, lam, V, hV⟩ :=
    exists_isOseledetsFiltration_timeOne φ herg A hg hg' hgb hg'b
  refine ⟨k, lam, V, hV.1, hV.2.1,
    fun t => ae_flow_equivariant φ A hg hg' hgb hg'b hV t, ?_⟩
  filter_upwards [hV.2.2, ae_tendsto_flowError_zero φ hg hg'] with x hx herr
  obtain ⟨htop, hbot, hstrict, _hequiv, hgrow⟩ := hx
  refine ⟨htop, hbot, hstrict, fun i v hvmem hvnot => ?_⟩
  have hv : v ≠ 0 := fun h => hvnot (h ▸ Submodule.zero_mem _)
  have hdisc : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A (n : ℝ) x) v‖) atTop (𝓝 (lam i)) := by
    simp_rw [A.toCocycle_eq]
    exact hgrow i v hvmem hvnot
  exact tendsto_log_norm_atTop_of_discrete φ A hgb hg'b hv herr hdisc

end Oseledets
