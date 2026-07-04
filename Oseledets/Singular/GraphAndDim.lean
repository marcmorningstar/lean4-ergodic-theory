/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Singular.JointMeasurableLambdaBar
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
theorem measurableSet_graph_lambdaSublevel
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

end Oseledets
