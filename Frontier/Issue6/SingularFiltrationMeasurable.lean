/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue6.MeasurableProjection
import Frontier.Issue6.GraphAndDim

/-!
# The singular (issue #6) measurable forward Lyapunov filtration

This module assembles the **a.e.-measurable orthogonal projector** of the singular ("issue #6")
multiplicative ergodic theorem from the two pieces built upstream:

* the **measurable graph** of the Lyapunov sublevel filtration
  `Oseledets.measurableSet_graph_lambdaSublevel` (under the everywhere `IsUltrametricGrowth` gate);
* the projection of the graph being **universally measurable**, hence the distance maps
  `x ↦ infDist c (V x)` being `AEMeasurable` (`Frontier.aemeasurable_infDist_of_measurableGraph`),
  modulo the single classical residual `MeasureTheory.AnalyticSet.nullMeasurableSet`.

## From a.e. weak measurability to an a.e. projector via polarisation

Each entry of the orthogonal-projection matrix is a coordinate of a projected standard basis
vector:
`Oseledets.orthProjMatrix K a b = (K.starProjection (EuclideanSpace.single b 1)) a`
(`Frontier.orthProjMatrix_apply_eq_starProjection_coord`). The polarisation identity
`Frontier.starProjection_apply_coord` expands that coordinate as a fixed real-arithmetic
combination of the three scalar distance maps `x ↦ infDist c (V x)` (for
`c ∈ {single b, single a (the projected vector), single b − single a}` after specialisation —
concretely `c ∈ {single b, single a 1, single a 1 − single b}` with the projected vector `single
a 1`). Each of those is `AEMeasurable` by the weak-measurability deliverable, and `AEMeasurable`
is closed under the finite arithmetic, so every matrix entry — hence the matrix
(`aemeasurable_pi_iff`) — is `AEMeasurable`.

This is the natural **a.e.** analogue of `Oseledets.MeasurableSubspace`
(`= Measurable fun x => orthProjMatrix (V x)`): the singular MET only ever needs the projector a.e.

## Main results

* `Frontier.orthProjMatrix_apply_eq_starProjection_coord`: the projector entry as a projected
  basis coordinate (`sorry`-free).
* `Frontier.aemeasurable_orthProjMatrix_of_measurableGraph`: **the general a.e. converter** — a
  measurable graph at a standard Borel base yields `AEMeasurable (fun x => orthProjMatrix (V x)) μ`
  (modulo the isolated `AnalyticSet.nullMeasurableSet`).
* `Oseledets.aemeasurable_orthProjMatrix_lambdaSublevel`: **the #6 headline** — for the Lyapunov
  sublevel filtration over a standard Borel ergodic base (everywhere `IsUltrametricGrowth` gate),
  the orthogonal projector `x ↦ orthProjMatrix (lambdaSublevel A T x c)` is `AEMeasurable`.

## Hypotheses and the residual

The forward filtration's measurable graph requires the everywhere `IsUltrametricGrowth` gate
`hUM : ∀ x, IsUltrametricGrowth (lambdaBar A T x)` — the pointwise form of the a.e.
`Oseledets.isUltrametricGrowth_lambdaBar`, automatic e.g. for a bounded generator (everywhere-
convergent Furstenberg–Kesten). With it the headline is `sorry`-free *except* for the single
classical measure-theory residual `MeasureTheory.AnalyticSet.nullMeasurableSet` (analytic sets are
universally measurable — Lusin/Choquet), threaded through `Frontier.Issue6.MeasurableProjection`.

Literature: C. González-Tokman, A. Quas, *A semi-invertible operator Oseledets theorem*
(ETDS 2014), Appendix B; D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
Publ. Math. IHÉS **50** (1979).
-/

open scoped Matrix
open Metric MeasureTheory Submodule Set

namespace Frontier

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-! ### The projector entry as a projected-basis coordinate -/

section Entry

/-- **The orthogonal-projector entry is a projected-basis coordinate.** For any subspace `K`,
`orthProjMatrix K a b = (K.starProjection (EuclideanSpace.single b 1)) a`. Unfolding
`orthProjMatrix` to `(toEuclideanCLM).symm K.starProjection`, the entry is the inner product
`⟪single a, K.starProjection (single b)⟫` (`Matrix.inner_toEuclideanCLM`), and
`⟪single a, w⟫ = w a` extracts the `a`-coordinate. -/
theorem orthProjMatrix_apply_eq_starProjection_coord
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (a b : Fin d) :
    Oseledets.orthProjMatrix K a b
      = (K.starProjection (EuclideanSpace.single b (1 : ℝ))) a := by
  -- `toEuclideanCLM (orthProjMatrix K) = starProjection K`, so the entry is an inner product.
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℝ) (Oseledets.orthProjMatrix K) = K.starProjection := by
    rw [Oseledets.orthProjMatrix, StarAlgEquiv.apply_symm_apply]
  have hentry : Oseledets.orthProjMatrix K a b
      = inner ℝ (EuclideanSpace.single a (1 : ℝ))
          (K.starProjection (EuclideanSpace.single b (1 : ℝ))) := by
    rw [← hclm, Matrix.inner_toEuclideanCLM]
    -- `single a 1 ⬝ᵥ M *ᵥ single b 1 = M a b`.
    simp [EuclideanSpace.single, dotProduct, Matrix.mulVec, PiLp.single_apply,
      Finset.sum_ite_eq, eq_comm]
  rw [hentry, EuclideanSpace.inner_single_left, map_one, one_mul]

end Entry

/-! ### From a measurable graph to an a.e.-measurable projector -/

section AEMeasurableProjector

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

/-- **The general a.e. converter: a measurable graph yields an a.e.-measurable projector.** Over a
standard Borel base `X` and for every measure `μ`, a measurable graph `{(x, v) | v ∈ V x}` makes
the orthogonal-projection matrix `x ↦ orthProjMatrix (V x)` `AEMeasurable`.

Each entry is a projected-basis coordinate (`orthProjMatrix_apply_eq_starProjection_coord`), which
the polarisation identity `starProjection_apply_coord` writes as a fixed real combination of the
`AEMeasurable` distance maps `x ↦ infDist c (V x)` (`aemeasurable_infDist_of_measurableGraph`);
`AEMeasurable` arithmetic and `aemeasurable_pi_iff` (Matrix carries the Pi structure) conclude.
This is the a.e. analogue of `Oseledets.MeasurableSubspace`. -/
theorem aemeasurable_orthProjMatrix_of_measurableGraph (μ : Measure X)
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}) :
    AEMeasurable (fun x => Oseledets.orthProjMatrix (V x)) μ := by
  -- Reduce to entrywise `AEMeasurable` (Matrix carries the Pi structure, defeq to `m → n → ℝ`).
  refine aemeasurable_pi_lambda _ fun a => aemeasurable_pi_lambda _ fun b => ?_
  -- Rewrite the entry via the projected-basis coordinate and the polarisation identity.
  have hcoord : (fun x => Oseledets.orthProjMatrix (V x) a b)
      = fun x => ((‖(EuclideanSpace.single a (1 : ℝ))‖ ^ 2
            - infDist (EuclideanSpace.single a (1 : ℝ)) (V x : Set _) ^ 2)
          + (‖(EuclideanSpace.single b (1 : ℝ))‖ ^ 2
            - infDist (EuclideanSpace.single b (1 : ℝ)) (V x : Set _) ^ 2)
          - (‖(EuclideanSpace.single a (1 : ℝ)) - (EuclideanSpace.single b (1 : ℝ))‖ ^ 2
            - infDist ((EuclideanSpace.single a (1 : ℝ)) - (EuclideanSpace.single b (1 : ℝ)))
              (V x : Set _) ^ 2)) / 2 := by
    funext x
    rw [orthProjMatrix_apply_eq_starProjection_coord]
    exact starProjection_apply_coord (V x) (EuclideanSpace.single b (1 : ℝ)) a
  rw [hcoord]
  -- Each `infDist c (V ·)` is `AEMeasurable`; constants and arithmetic preserve it.
  have ha : AEMeasurable (fun x => infDist (EuclideanSpace.single a (1 : ℝ)) (V x : Set _)) μ :=
    aemeasurable_infDist_of_measurableGraph μ hgraph _
  have hb : AEMeasurable (fun x => infDist (EuclideanSpace.single b (1 : ℝ)) (V x : Set _)) μ :=
    aemeasurable_infDist_of_measurableGraph μ hgraph _
  have hab : AEMeasurable (fun x => infDist
      ((EuclideanSpace.single a (1 : ℝ)) - (EuclideanSpace.single b (1 : ℝ))) (V x : Set _)) μ :=
    aemeasurable_infDist_of_measurableGraph μ hgraph _
  exact ((((aemeasurable_const.sub (ha.pow_const 2)).add
    (aemeasurable_const.sub (hb.pow_const 2))).sub
      (aemeasurable_const.sub (hab.pow_const 2))).div_const 2)

end AEMeasurableProjector

/-! ### The issue #6 headline: a.e.-measurable projector of the Lyapunov sublevel filtration -/

section Headline

open scoped Matrix.Norms.L2Operator

variable {μ : Measure X} {T : X → X}

/-- **The singular issue #6 headline: an a.e.-measurable forward Lyapunov projector.** Over a
standard Borel ergodic base `X` with an invertible measurable generator `A` (forward/inverse
log-norm integrability of the invertible MET), and the everywhere `IsUltrametricGrowth` gate
`hUM` (the pointwise form of the a.e. `Oseledets.isUltrametricGrowth_lambdaBar`, automatic e.g. for
a bounded generator), the orthogonal-projection matrix
`x ↦ orthProjMatrix (lambdaSublevel A T x c)` of the forward Lyapunov sublevel filtration is
`AEMeasurable`.

The sublevel filtration has a measurable graph (`Oseledets.measurableSet_graph_lambdaSublevel`),
which the general a.e. converter `aemeasurable_orthProjMatrix_of_measurableGraph` turns into the
a.e.-measurable projector. The only residual is the classical universal measurability of analytic
sets `MeasureTheory.AnalyticSet.nullMeasurableSet`, threaded through the converter. -/
theorem _root_.Oseledets.aemeasurable_orthProjMatrix_lambdaSublevel
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X] [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) (hT : Measurable T)
    (hUM : ∀ x, Oseledets.IsUltrametricGrowth (Oseledets.lambdaBar A T x)) (c : ℝ) :
    AEMeasurable (fun x => Oseledets.orthProjMatrix (Oseledets.lambdaSublevel A T x c)) μ :=
  aemeasurable_orthProjMatrix_of_measurableGraph μ
    (Oseledets.measurableSet_graph_lambdaSublevel hA hT hUM c)

end Headline

end Frontier
