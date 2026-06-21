/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue6.JointMeasurableLambdaBar
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.Extensions.Corollaries
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Graph measurability and a.e.-constant dimension of the Lyapunov sublevel filtration

This module assembles two facts about the forward Lyapunov sublevel filtration
`Oseledets.lambdaSublevel A T x c` (the limsup flag of `Oseledets.Lyapunov.Filtration`):
its **graph is measurable** in the pair `(x, v)`, and its **level dimension is `μ`-a.e.
constant** under an ergodic base dynamics. Both are prerequisites of the measurable selection
of the slow flag `{v | lambdaBar A T x v ≤ c}` that drives the (singular) measurable forward
Oseledets filtration of issue #6.

## The membership criterion and the `IsUltrametricGrowth` gate

`Oseledets.lambdaSublevel` is defined **totally**, with the junk value `⊥` off the set where
`v ↦ lambdaBar A T x v` is an `IsUltrametricGrowth` function. On the good set the membership
criterion is the expected
`v ∈ lambdaSublevel A T x c ↔ v = 0 ∨ lambdaBar A T x v ≤ c` (`Oseledets.mem_lambdaSublevel`);
off it, only `v = 0` lies in the level. Accordingly the graph theorem carries the everywhere
hypothesis `hUM : ∀ x, IsUltrametricGrowth (lambdaBar A T x)` — the pointwise form of the a.e.
fact `Oseledets.isUltrametricGrowth_lambdaBar` (it holds a.e. for an invertible cocycle, and
everywhere whenever the Furstenberg–Kesten sandwich converges everywhere, e.g. for a bounded
generator). Under it the graph is literally
`{p | p.2 = 0} ∪ {p | lambdaBar A T p.1 p.2 ≤ c}`, measurable from
`Oseledets.jointMeasurable_lambdaBar` plus the measurability of `{v = 0}`.

## Main results

* `Oseledets.measurableSet_graph_lambdaSublevel`: the graph
  `{p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ lambdaSublevel A T p.1 c}` is measurable (given the
  everywhere `IsUltrametricGrowth` gate `hUM`).
* `Oseledets.ae_dim_lambdaSublevel_eq_const`: for ergodic measure-preserving `T` and an
  invertible measurable generator, there is a single `k : ℕ` with
  `Module.finrank ℝ (lambdaSublevel A T x c) = k` for `μ`-a.e. `x`.

## Proof outline of the a.e.-constant dimension

The action `A x` maps the level-`c` space at `x` onto the level-`c` space at `T x`, a.e.
(`Oseledets.vflag_equivariant`). As `A x` is injective (`det A ≠ 0`), `Submodule.map`
preserves `finrank` (`Submodule.equivMapOfInjective`), so the integer-valued
`x ↦ finrank ℝ (lambdaSublevel A T x c)` is a.e. `T`-invariant. It is also measurable
(`Oseledets.MeasurableSubspace.measurable_finrank` applied to a threaded
`MeasurableSubspace` witness), so ergodicity forces it a.e. constant
(`Ergodic.ae_eq_const_of_ae_eq_comp₀`; `ℕ` is a countably-separated measurable space).

## References

* D. Ruelle, *Ergodic theory of differentiable dynamical systems*, Publ. Math. IHÉS **50**
  (1979), 27–58.
* A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

/-! ## Graph measurability of the sublevel filtration -/

section Graph

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- **The graph of the Lyapunov sublevel filtration is measurable.** Given the everywhere
`IsUltrametricGrowth` gate `hUM` (the pointwise form of `Oseledets.isUltrametricGrowth_lambdaBar`,
which holds a.e.), the set
`{p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ lambdaSublevel A T p.1 c}` is measurable.

Under `hUM` the membership criterion `Oseledets.mem_lambdaSublevel` turns the graph into the
union `{p | p.2 = 0} ∪ {p | lambdaBar A T p.1 p.2 ≤ c}`. The first set is the preimage of the
closed singleton `{0}` under the continuous `p ↦ p.2`; the second is measurable from the joint
measurability `Oseledets.jointMeasurable_lambdaBar` and the measurable constant `c`. -/
theorem measurableSet_graph_lambdaSublevel [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    (hA : Measurable A) (hT : Measurable T)
    (hUM : ∀ x, IsUltrametricGrowth (lambdaBar A T x)) (c : ℝ) :
    MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ lambdaSublevel A T p.1 c} := by
  -- Rewrite the graph via the membership criterion (valid everywhere under `hUM`).
  have hset : {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ lambdaSublevel A T p.1 c}
      = {p : X × EuclideanSpace ℝ (Fin d) | p.2 = 0}
        ∪ {p : X × EuclideanSpace ℝ (Fin d) | lambdaBar A T p.1 p.2 ≤ c} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union]
    exact mem_lambdaSublevel (hUM p.1) c p.2
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · -- `{p | p.2 = 0}` is the preimage of the measurable singleton `{0}` under `p ↦ p.2`.
    have : {p : X × EuclideanSpace ℝ (Fin d) | p.2 = 0}
        = (fun p : X × EuclideanSpace ℝ (Fin d) => p.2) ⁻¹' {0} := by
      ext p; simp [Set.mem_preimage]
    rw [this]
    exact measurable_snd (measurableSet_singleton 0)
  · -- `{p | lambdaBar A T p.1 p.2 ≤ c}` is measurable from joint measurability of `lambdaBar`.
    exact measurableSet_le (jointMeasurable_lambdaBar hA hT) measurable_const

end Graph

/-! ## A.e.-constant dimension of the sublevel filtration -/

section Dimension

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ} {μ : Measure X}

/-- **The level dimension of the Lyapunov sublevel filtration is `μ`-a.e. constant.** For an
ergodic measure-preserving `T` and an invertible (`det A ≠ 0`) measurable generator with the
forward and inverse log-norm integrability of the invertible MET, the function
`x ↦ Module.finrank ℝ (lambdaSublevel A T x c)` equals a single `k : ℕ` for `μ`-a.e. `x`.

The map `A x` carries the level-`c` space at `x` onto that at `T x` a.e.
(`Oseledets.vflag_equivariant`), and is injective by `det A ≠ 0`, so `Submodule.map` preserves
`finrank` (`Submodule.equivMapOfInjective`); hence the dimension is a.e. `T`-invariant. With a
`MeasurableSubspace` witness `hVmeas` for the level family the dimension is measurable
(`Oseledets.MeasurableSubspace.measurable_finrank`), and ergodicity makes an a.e.-invariant
measurable `ℕ`-valued function a.e. constant (`Ergodic.ae_eq_const_of_ae_eq_comp₀`). -/
theorem ae_dim_lambdaSublevel_eq_const [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (c : ℝ) (hVmeas : MeasurableSubspace fun x => lambdaSublevel A T x c) :
    ∃ k : ℕ, ∀ᵐ x ∂μ, Module.finrank ℝ (lambdaSublevel A T x c) = k := by
  -- The dimension of the level is a.e. `T`-invariant, by equivariance + injectivity of `A x`.
  have hinv : (fun x => Module.finrank ℝ (lambdaSublevel A T x c)) ∘ T
      =ᵐ[μ] fun x => Module.finrank ℝ (lambdaSublevel A T x c) := by
    filter_upwards [vflag_equivariant hT hA hAmeas hint hint'] with x hx
    have hmap := hx c
    -- injectivity of `A x` (via `toEuclideanLin`, since `det A x ≠ 0`)
    have hinj : Function.Injective
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
      have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
          = Matrix.toEuclideanLin (A x) :=
        Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (A x)
      rw [h1]
      exact injective_toEuclideanLin (hA x)
    -- `finrank (map (A x) (level x)) = finrank (level x)`, and `map = level (T x)` by `hmap`.
    have heq := (Submodule.equivMapOfInjective _ hinj (lambdaSublevel A T x c)).finrank_eq
    rw [Function.comp_apply, ← hmap]
    exact heq.symm
  -- Ergodic constancy of the measurable, a.e.-invariant `ℕ`-valued dimension.
  exact hT.ae_eq_const_of_ae_eq_comp₀ hVmeas.measurable_finrank.nullMeasurable hinv

end Dimension

end Oseledets
