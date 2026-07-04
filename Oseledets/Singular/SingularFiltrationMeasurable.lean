/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Singular.MeasurableProjection
import Oseledets.Singular.GraphAndDim
import Oseledets.Singular.StarProjectionPolar

/-!
# The singular (issue #6) measurable forward Lyapunov filtration

This module assembles the **a.e.-measurable orthogonal projector** of the singular ("issue #6")
multiplicative ergodic theorem from the two pieces built upstream:

* the **measurable graph** of the Lyapunov sublevel filtration
  `Oseledets.measurableSet_graph_lambdaSublevel` (under the everywhere `IsUltrametricGrowth` gate);
* the projection of the graph being **universally measurable**, hence the distance maps
  `x ↦ infDist c (V x)` being `AEMeasurable` (`Oseledets.aemeasurable_infDist_of_measurableGraph`),
  using the now-proved universal measurability `MeasureTheory.AnalyticSet.nullMeasurableSet`
  (`Oseledets.MeasureTheory.AnalyticUniversallyMeasurable`).

## From a.e. weak measurability to an a.e. projector via polarisation

Each entry of the orthogonal-projection matrix is a coordinate of a projected standard basis
vector:
`Oseledets.orthProjMatrix K a b = (K.starProjection (EuclideanSpace.single b 1)) a`
(`Oseledets.orthProjMatrix_apply`). The polarisation identity
`Oseledets.starProjection_apply_coord` expands that coordinate as a fixed real-arithmetic
combination of the three scalar distance maps `x ↦ infDist c (V x)` (for
`c ∈ {single b, single a (the projected vector), single b − single a}` after specialisation —
concretely `c ∈ {single b, single a 1, single a 1 − single b}` with the projected vector `single
a 1`). Each of those is `AEMeasurable` by the weak-measurability deliverable, and `AEMeasurable`
is closed under the finite arithmetic, so every matrix entry — hence the matrix
(`aemeasurable_pi_iff`) — is `AEMeasurable`.

This is the natural **a.e.** analogue of `Oseledets.MeasurableSubspace`
(`= Measurable fun x => orthProjMatrix (V x)`): the singular MET only ever needs the projector a.e.

## Main results

* `Oseledets.aemeasurable_orthProjMatrix_of_measurableGraph`: **the general a.e. converter** — a
  measurable graph at a standard Borel base yields `AEMeasurable (fun x => orthProjMatrix (V x)) μ`
  for every s-finite `μ` (using the now-proved `AnalyticSet.nullMeasurableSet`).
* `Oseledets.aemeasurable_orthProjMatrix_lambdaSublevel`: **the #6 headline** — for the Lyapunov
  sublevel filtration over a standard Borel base with measurable `A`, `T` and any s-finite `μ`
  (everywhere `IsUltrametricGrowth` gate), the orthogonal projector
  `x ↦ orthProjMatrix (lambdaSublevel A T x c)` is `AEMeasurable`.

## Hypotheses and the residual

The forward filtration's measurable graph requires the everywhere `IsUltrametricGrowth` gate
`hUM : ∀ x, IsUltrametricGrowth (lambdaBar A T x)` — the pointwise form of the a.e.
`Oseledets.isUltrametricGrowth_lambdaBar`, automatic e.g. for a bounded generator (everywhere-
convergent Furstenberg–Kesten). With it, and for any s-finite `μ` (in particular the probability
measure of the MET), the headline is `sorry`-free: the universal measurability
`MeasureTheory.AnalyticSet.nullMeasurableSet` (analytic sets are universally measurable —
Lusin/Choquet) is now proved in `Oseledets.MeasureTheory.AnalyticUniversallyMeasurable` and threaded
through `Oseledets.Singular.MeasurableProjection`.

Literature: C. González-Tokman, A. Quas, *A semi-invertible operator Oseledets theorem*
(ETDS 2014), Appendix B; D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
Publ. Math. IHÉS **50** (1979).
-/

open Metric MeasureTheory Submodule Set

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-! ### From a measurable graph to an a.e.-measurable projector -/

section AEMeasurableProjector

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

/-- **The general a.e. converter: a measurable graph yields an a.e.-measurable projector.** Over a
standard Borel base `X` and for every measure `μ`, a measurable graph `{(x, v) | v ∈ V x}` makes
the orthogonal-projection matrix `x ↦ orthProjMatrix (V x)` `AEMeasurable`.

Each entry is a projected-basis coordinate (`Oseledets.orthProjMatrix_apply`), which
the polarisation identity `starProjection_apply_coord` writes as a fixed real combination of the
`AEMeasurable` distance maps `x ↦ infDist c (V x)` (`aemeasurable_infDist_of_measurableGraph`);
`AEMeasurable` arithmetic and `aemeasurable_pi_iff` (Matrix carries the Pi structure) conclude.
This is the a.e. analogue of `Oseledets.MeasurableSubspace`. -/
theorem aemeasurable_orthProjMatrix_of_measurableGraph (μ : Measure X) [SFinite μ]
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}) :
    AEMeasurable (fun x => orthProjMatrix (V x)) μ := by
  -- Reduce to entrywise `AEMeasurable` (Matrix carries the Pi structure, defeq to `m → n → ℝ`).
  refine aemeasurable_pi_lambda _ fun a => aemeasurable_pi_lambda _ fun b => ?_
  -- Rewrite the entry via the projected-basis coordinate and the polarisation identity.
  have hcoord : (fun x => orthProjMatrix (V x) a b)
      = fun x => ((‖(EuclideanSpace.single a (1 : ℝ))‖ ^ 2
            - infDist (EuclideanSpace.single a (1 : ℝ)) (V x : Set _) ^ 2)
          + (‖(EuclideanSpace.single b (1 : ℝ))‖ ^ 2
            - infDist (EuclideanSpace.single b (1 : ℝ)) (V x : Set _) ^ 2)
          - (‖(EuclideanSpace.single a (1 : ℝ)) - (EuclideanSpace.single b (1 : ℝ))‖ ^ 2
            - infDist ((EuclideanSpace.single a (1 : ℝ)) - (EuclideanSpace.single b (1 : ℝ)))
              (V x : Set _) ^ 2)) / 2 := by
    funext x
    rw [orthProjMatrix_apply]
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

variable {μ : Measure X} [SFinite μ] {T : X → X}

/-- **The singular issue #6 headline: an a.e.-measurable forward Lyapunov projector.** For a
measurable generator `A` (`hA`) and a measurable `T` (`hT`) over a standard Borel base `X`, an
arbitrary s-finite measure `μ`, and the everywhere `IsUltrametricGrowth` gate `hUM` (the pointwise
form of the a.e. `Oseledets.isUltrametricGrowth_lambdaBar`, automatic e.g. for a bounded
generator), the orthogonal-projection matrix `x ↦ orthProjMatrix (lambdaSublevel A T x c)` of the
forward Lyapunov sublevel filtration is `AEMeasurable`. **No invertibility (`det ≠ 0`), ergodicity,
measure-preservation, or log-norm integrability is assumed** — `A`, `T`, and `μ` are unrelated, so
the result is strictly more general than the invertible MET setting.

The sublevel filtration has a measurable graph (`Oseledets.measurableSet_graph_lambdaSublevel`),
which the general a.e. converter `aemeasurable_orthProjMatrix_of_measurableGraph` turns into the
a.e.-measurable projector (for any s-finite `μ`). The classical universal measurability of analytic
sets `MeasureTheory.AnalyticSet.nullMeasurableSet` it relies on is proved in
`Oseledets.MeasureTheory.AnalyticUniversallyMeasurable` and threaded through the converter. -/
theorem aemeasurable_orthProjMatrix_lambdaSublevel
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) (hT : Measurable T)
    (hUM : ∀ x, IsUltrametricGrowth (lambdaBar A T x)) (c : ℝ) :
    AEMeasurable (fun x => orthProjMatrix (lambdaSublevel A T x c)) μ :=
  aemeasurable_orthProjMatrix_of_measurableGraph μ
    (measurableSet_graph_lambdaSublevel hA hT hUM c)

end Headline

end Oseledets
