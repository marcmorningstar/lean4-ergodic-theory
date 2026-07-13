/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Joint continuity of the pushforward of probability measures on compact spaces

Mathlib already knows that, for a *fixed* continuous map `f : X → Y`, the pushforward
`f_* : ProbabilityMeasure X → ProbabilityMeasure Y` is continuous for the topologies of weak
convergence (`MeasureTheory.ProbabilityMeasure.continuous_map`). This module upgrades that to
**joint** continuity in the pair `(f, ν)`: with `X` a compact metric space, `C(X, Y)` carrying the
uniform (sup) metric and `ProbabilityMeasure X` the topology of convergence in distribution, the map
`(f, ν) ↦ f_* ν` is continuous.

## Main statements

* `MeasureTheory.tendsto_probabilityMeasure_map_of_tendsto`: the sequential/filter form.  If
  `σs → σ` uniformly in `C(X, Y)` and `νs → ν` weakly, then `(σs)_* νs → σ_* ν` weakly.
* `MeasureTheory.continuous_probabilityMeasure_map_compact`: the joint pushforward
  `C(X, Y) × ProbabilityMeasure X → ProbabilityMeasure Y` is continuous.
* `MeasureTheory.isClosed_setOf_map_eq`: a worked closed-set corollary — the set of pairs `(f, ν)`
  whose pushforward equals a fixed target measure `μ₀` is closed.

## Implementation notes

The pushforward is `MeasureTheory.ProbabilityMeasure.map`, which takes an `AEMeasurable` witness;
for `τ : C(X, Y)` the witness is `τ.continuous.measurable.aemeasurable`.

The proof is the standard weak-convergence + uniform-convergence argument (Billingsley,
*Convergence of Probability Measures*, mapping-theorem circle of ideas).  Testing against
`g : Y →ᵇ ℝ` and using `∫ g d((σs i)_* νs i) = ∫ (g ∘ σs i) d(νs i)`, we split

`∫ (g ∘ σs i) dνs i − ∫ (g ∘ σ) dν
   = (∫ (g ∘ σs i) dνs i − ∫ (g ∘ σ) dνs i) + (∫ (g ∘ σ) dνs i − ∫ (g ∘ σ) dν).`

The second bracket → 0 by weak convergence `νs → ν` tested against the bounded continuous function
`g ∘ σ`.  The first is bounded by `‖g ∘ σs i − g ∘ σ‖∞` (probability measure), which → 0 because
`τ ↦ g ∘ τ` is continuous `C(X, Y) → (X →ᵇ ℝ)` (postcomposition,
`ContinuousMap.continuous_postcomp`, transported along the compact-domain isometry
`ContinuousMap.equivBoundedOfCompact`).

The postcomposition-continuity fact repackaged here has a self-contained Mathlib analogue in
`ContinuousMap.continuous_postcomp`; no `C(X, Y)`-composition lemmas are duplicated.

This fills a genuine gap: Mathlib currently only provides the fixed-map continuity
`ProbabilityMeasure.continuous_map`; the joint statement is a candidate for upstreaming.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace MeasureTheory

variable {X Y : Type*}
variable [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The pushforward of probability measures is jointly continuous in `(map, measure)` (sequential
form).  If `σs → σ` uniformly in `C(X, Y)` and `νs → ν` in distribution, then the pushforwards
`(σs i)_* (νs i)` converge in distribution to `σ_* ν`. -/
theorem tendsto_probabilityMeasure_map_of_tendsto {ι : Type*} {L : Filter ι}
    {σs : ι → C(X, Y)} {σ : C(X, Y)} (hσ : Tendsto σs L (𝓝 σ))
    {νs : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} (hν : Tendsto νs L (𝓝 ν)) :
    Tendsto (fun i ↦ (νs i).map (σs i).continuous.measurable.aemeasurable) L
      (𝓝 (ν.map σ.continuous.measurable.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  -- Pushforward integral: `∫ y, g y d(τ_* ρ) = ∫ x, g (τ x) dρ`.
  have hmap : ∀ (τ : C(X, Y)) (ρ : ProbabilityMeasure X),
      ∫ y, g y ∂(ρ.map τ.continuous.measurable.aemeasurable : Measure Y)
        = ∫ x, g (τ x) ∂(ρ : Measure X) := by
    intro τ ρ
    rw [ProbabilityMeasure.toMeasure_map,
      integral_map τ.continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  simp only [hmap]
  -- Rephrase the integrands as the bounded continuous functions `g ∘ τ`.
  change Tendsto (fun i ↦ ∫ x, (g.compContinuous (σs i)) x ∂(νs i : Measure X)) L
    (𝓝 (∫ x, (g.compContinuous σ) x ∂(ν : Measure X)))
  -- `τ ↦ g ∘ τ` is continuous `C(X, Y) → (X →ᵇ ℝ)`.
  have hΦ : Continuous fun τ : C(X, Y) ↦ g.compContinuous τ := by
    have hpost : Continuous fun τ : C(X, Y) ↦ g.toContinuousMap.comp τ :=
      ContinuousMap.continuous_postcomp _
    have hequiv : Continuous (ContinuousMap.isometryEquivBoundedOfCompact X ℝ) :=
      (ContinuousMap.isometryEquivBoundedOfCompact X ℝ).continuous
    have hcomp : (fun τ : C(X, Y) ↦ g.compContinuous τ)
        = (fun h ↦ ContinuousMap.isometryEquivBoundedOfCompact X ℝ h)
            ∘ fun τ : C(X, Y) ↦ g.toContinuousMap.comp τ := by
      ext τ x
      simp [BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.isometryEquivBoundedOfCompact_apply]
    rw [hcomp]
    exact hequiv.comp hpost
  -- `g ∘ σs i → g ∘ σ` uniformly, hence in norm.
  have hlim_u : Tendsto (fun i ↦ g.compContinuous (σs i)) L (𝓝 (g.compContinuous σ)) :=
    (hΦ.tendsto σ).comp hσ
  have hnorm : Tendsto (fun i ↦ ‖g.compContinuous (σs i) - g.compContinuous σ‖) L (𝓝 0) := by
    have hd : Tendsto (fun i ↦ g.compContinuous (σs i) - g.compContinuous σ) L
        (𝓝 (0 : X →ᵇ ℝ)) := by
      have h0 : (0 : X →ᵇ ℝ) = g.compContinuous σ - g.compContinuous σ := (sub_self _).symm
      rw [h0]
      exact hlim_u.sub tendsto_const_nhds
    simpa using hd.norm
  -- Second bracket → 0 by weak convergence against `g ∘ σ`.
  have hB : Tendsto (fun i ↦ ∫ x, (g.compContinuous σ) x ∂(νs i : Measure X)) L
      (𝓝 (∫ x, (g.compContinuous σ) x ∂(ν : Measure X))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) (g.compContinuous σ)
  -- First bracket → 0 by the sup bound on a probability measure.
  have hA : Tendsto (fun i ↦ (∫ x, (g.compContinuous (σs i)) x ∂(νs i : Measure X))
      - ∫ x, (g.compContinuous σ) x ∂(νs i : Measure X)) L (𝓝 0) := by
    refine squeeze_zero_norm (fun i ↦ ?_) hnorm
    have hsub : (∫ x, (g.compContinuous (σs i)) x ∂(νs i : Measure X))
        - ∫ x, (g.compContinuous σ) x ∂(νs i : Measure X)
        = ∫ x, (g.compContinuous (σs i) - g.compContinuous σ) x ∂(νs i : Measure X) := by
      simp only [BoundedContinuousFunction.sub_apply]
      exact (integral_sub ((g.compContinuous (σs i)).integrable _)
        ((g.compContinuous σ).integrable _)).symm
    rw [hsub]
    exact (g.compContinuous (σs i) - g.compContinuous σ).norm_integral_le_norm _
  -- Combine.
  have hcombine := hA.add hB
  simpa using hcombine

/-- The joint pushforward `C(X, Y) × ProbabilityMeasure X → ProbabilityMeasure Y`,
`(f, ν) ↦ f_* ν`, is continuous for the uniform metric on `C(X, Y)` and the topologies of weak
convergence.  This is the joint upgrade of `ProbabilityMeasure.continuous_map`. -/
theorem continuous_probabilityMeasure_map_compact :
    Continuous (fun p : C(X, Y) × ProbabilityMeasure X ↦
      p.2.map p.1.continuous.measurable.aemeasurable) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_probabilityMeasure_map_of_tendsto continuous_fst.continuousAt
    continuous_snd.continuousAt

/-- A worked closed-set corollary: for a fixed target `μ₀ : ProbabilityMeasure Y`, the set of
pairs `(f, ν)` whose pushforward `f_* ν` equals `μ₀` is closed.  This is the preimage of the closed
singleton `{μ₀}` (`ProbabilityMeasure Y` is Hausdorff) under the continuous joint pushforward. -/
theorem isClosed_setOf_map_eq (μ₀ : ProbabilityMeasure Y) :
    IsClosed {p : C(X, Y) × ProbabilityMeasure X |
      p.2.map p.1.continuous.measurable.aemeasurable = μ₀} :=
  isClosed_eq continuous_probabilityMeasure_map_compact continuous_const

/-- Non-vacuity of `isClosed_setOf_map_eq`: the identity map pushes any measure to itself, so the
fixed-target set is inhabited whenever the target is realised as a pushforward. -/
example (ν : ProbabilityMeasure X) :
    (ContinuousMap.id X, ν) ∈ {p : C(X, X) × ProbabilityMeasure X |
      p.2.map p.1.continuous.measurable.aemeasurable
        = ν.map (continuous_id.measurable.aemeasurable)} := rfl

end MeasureTheory
