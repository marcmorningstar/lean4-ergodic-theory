/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MeasureTheory.CompactSectionProjection
import ErgodicTheory.Singular.GraphAndDim
import ErgodicTheory.Singular.StarProjectionPolar
import ErgodicTheory.Lyapunov.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# The everywhere-Borel singular forward Lyapunov filtration (issue #11)

This module upgrades the singular ("issue #6") forward Lyapunov projector from *a.e.* measurability
to **everywhere Borel measurability**, discharging the payoff of issue #11. Where
`ErgodicTheory.Singular.SingularFiltrationMeasurable` produces `AEMeasurable` projectors from a
measurable graph via the universal measurability of analytic sets, here we obtain honest
`Measurable` projectors via the **Novikov compact-section projection theorem**
`ErgodicTheory.measurableSet_image_fst_of_isCompact_sections`
(`ErgodicTheory.MeasureTheory.CompactSectionProjection`).

## The route: closed balls make the sections compact

For a subspace-valued family `V` with a measurable graph `{(x, v) | v ∈ V x}` over a standard Borel
base, each sublevel set `{x | infDist c (V x) ≤ r}` is the projection of the graph sliced with the
**closed** ball `closedBall c r`. The section `V x ∩ closedBall c r` is a closed subspace
intersected with a compact ball in the proper Euclidean space, hence **compact**, so Novikov 4.7.11
applies directly and `x ↦ infDist c (V x)` is `Measurable` (via `measurable_of_Iic`). No σ-compact
Saint-Raymond (5.12.2) machinery is needed.

**Scope.** The fully general σ-compact-section projection theorem (Arsenin–Kunugui, Saint-Raymond
5.12.2 — Effros Borel hyperspace, Π¹₁-boundedness, transfinite ranks) is a documented research wall
and is deliberately *not* formalized in this development. Only the compact-section case (Novikov
4.7.11) is, and it suffices for the subspace-valued Oseledets filtration precisely because
closed-ball slices of the subspace fibres are compact.

## From measurable distances to a measurable projector via polarisation

Each entry of the orthogonal-projection matrix is a projected-basis coordinate
(`ErgodicTheory.orthProjMatrix_apply`), which the polarisation identity
`ErgodicTheory.starProjection_apply_coord` writes as a fixed real combination of the three scalar
distance maps `x ↦ infDist c (V x)`. `Measurable` arithmetic and `measurable_pi_lambda` (Matrix
carries the Pi structure) then give the full projector. This is the everywhere analogue of
`ErgodicTheory.aemeasurable_orthProjMatrix_of_measurableGraph`.

## Main results

* `ErgodicTheory.measurable_infDist_of_measurableGraph`: a measurable graph yields
  `Measurable fun x => infDist c (V x)` for every `c` (closed-ball route, only Novikov 4.7.11).
* `ErgodicTheory.measurable_orthProjMatrix_of_measurableGraph`: the general converter — a measurable
  graph yields `Measurable fun x => orthProjMatrix (V x)`.
* `ErgodicTheory.measurable_orthProjMatrix_lambdaSublevel`: **the issue #11 headline** — the forward
  Lyapunov sublevel projector `x ↦ orthProjMatrix (lambdaSublevel A T x c)` is *everywhere*
  `Measurable` (everywhere `IsUltrametricGrowth` gate; no invertibility, ergodicity, or
  measure-preservation assumed).

Literature: S. M. Srivastava, *A Course on Borel Sets*, Springer GTM 180, §4.7; A. S. Kechris,
*Classical Descriptive Set Theory*, §28 (Arsenin–Kunugui); C. González-Tokman, A. Quas, *A
semi-invertible operator Oseledets theorem* (ETDS 2014), Appendix B.
-/

open Metric MeasureTheory Submodule Set

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-! ### The everywhere-Borel distance map via closed balls (Novikov 4.7.11 only) -/

section Consumer

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

/-- **A measurable graph yields everywhere-Borel `infDist`-measurability, via closed balls (only
Novikov 4.7.11 is consumed).** A measurable subspace graph gives *everywhere* Borel measurability of
`x ↦ infDist c (V x)` for every `c`: the `Iic`-sublevels are projections of the graph sliced with
**closed** balls, whose sections `V x ∩ closedBall c r` are **compact** (closed subspace ∩ compact
ball in the proper Euclidean space), so Novikov 4.7.11
(`measurableSet_image_fst_of_isCompact_sections`) applies directly. -/
theorem measurable_infDist_of_measurableGraph
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}) :
    ∀ c : EuclideanSpace ℝ (Fin d), Measurable fun x => infDist c (V x) := by
  intro c
  refine measurable_of_Iic fun r => ?_
  have hpre : (fun x => infDist c (V x)) ⁻¹' Iic r
      = Prod.fst '' ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
          ∩ ((univ : Set X) ×ˢ Metric.closedBall c r)) := by
    ext x
    constructor
    · intro hx
      rw [mem_preimage, mem_Iic] at hx
      obtain ⟨v, hvV, hvd⟩ := ((V x).closed_of_finiteDimensional).exists_infDist_eq_dist
        ⟨0, (V x).zero_mem⟩ c
      refine ⟨(x, v), ⟨hvV, ⟨mem_univ _, ?_⟩⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_comm, ← hvd]
      exact hx
    · rintro ⟨⟨x', v⟩, ⟨hvV, ⟨-, hvball⟩⟩, rfl⟩
      rw [mem_preimage, mem_Iic]
      calc infDist c ↑(V x') ≤ dist c v := infDist_le_dist_of_mem hvV
        _ ≤ r := by rw [dist_comm]; exact Metric.mem_closedBall.1 hvball
  rw [hpre]
  have hslab : MeasurableSet ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
      ∩ ((univ : Set X) ×ˢ Metric.closedBall c r)) :=
    hgraph.inter (MeasurableSet.univ.prod measurableSet_closedBall)
  refine measurableSet_image_fst_of_isCompact_sections hslab fun x => ?_
  have hsec : {v : EuclideanSpace ℝ (Fin d) | (x, v) ∈
      ({p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}
        ∩ ((univ : Set X) ×ˢ Metric.closedBall c r))}
      = (V x : Set (EuclideanSpace ℝ (Fin d))) ∩ Metric.closedBall c r := by
    ext v
    simp only [mem_setOf_eq, mem_inter_iff, mem_prod, mem_univ, true_and, SetLike.mem_coe]
  rw [hsec]
  exact Metric.isCompact_of_isClosed_isBounded
    ((V x).closed_of_finiteDimensional.inter Metric.isClosed_closedBall)
    (Metric.isBounded_closedBall.subset inter_subset_right)

/-- **The general converter: a measurable graph yields an everywhere-measurable projector.** Over a
standard Borel base `X`, a measurable graph `{(x, v) | v ∈ V x}` makes the orthogonal-projection
matrix `x ↦ orthProjMatrix (V x)` `Measurable`.

Each entry is a projected-basis coordinate (`ErgodicTheory.orthProjMatrix_apply`), which the
polarisation identity `starProjection_apply_coord` writes as a fixed real combination of the
`Measurable` distance maps `x ↦ infDist c (V x)` (`measurable_infDist_of_measurableGraph`);
`Measurable` arithmetic and `measurable_pi_lambda` (Matrix carries the Pi structure) conclude. This
is the everywhere analogue of `ErgodicTheory.aemeasurable_orthProjMatrix_of_measurableGraph`. -/
theorem measurable_orthProjMatrix_of_measurableGraph
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}) :
    Measurable fun x => orthProjMatrix (V x) := by
  -- Reduce to entrywise `Measurable` (Matrix carries the Pi structure, defeq to `m → n → ℝ`).
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
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
  -- Each `infDist c (V ·)` is `Measurable`; constants and arithmetic preserve it.
  have ha : Measurable (fun x => infDist (EuclideanSpace.single a (1 : ℝ)) (V x : Set _)) :=
    measurable_infDist_of_measurableGraph hgraph _
  have hb : Measurable (fun x => infDist (EuclideanSpace.single b (1 : ℝ)) (V x : Set _)) :=
    measurable_infDist_of_measurableGraph hgraph _
  have hab : Measurable (fun x => infDist
      ((EuclideanSpace.single a (1 : ℝ)) - (EuclideanSpace.single b (1 : ℝ))) (V x : Set _)) :=
    measurable_infDist_of_measurableGraph hgraph _
  exact ((((measurable_const.sub (ha.pow_const 2)).add
    (measurable_const.sub (hb.pow_const 2))).sub
      (measurable_const.sub (hab.pow_const 2))).div_const 2)

end Consumer

/-! ### The issue #11 headline: everywhere-Borel projector of the Lyapunov sublevel filtration -/

section Headline

variable {T : X → X}

/-- **The issue #11 headline: an everywhere-Borel forward Lyapunov projector.** For a measurable
generator `A` (`hA`) and a measurable `T` (`hT`) over a standard Borel base `X`, and the everywhere
`IsUltrametricGrowth` gate `hUM` (the pointwise form of the a.e.
`ErgodicTheory.isUltrametricGrowth_lambdaBar`, which itself needs invertibility, ergodicity, and
integrable log-norms; the everywhere form is satisfiable — e.g. `A ≡ 1` gives `lambdaBar ≡ 0` — but
it is *not* automatic for a merely bounded singular generator: boundedness yields only the floored
`ErgodicTheory.isUltrametricGrowth_max_lambdaBar` for `max (lambdaBar A T x ·) 0`, and the
unfloored gate can fail on a singular kernel), the orthogonal-projection matrix
`x ↦ orthProjMatrix (lambdaSublevel A T x c)` of the forward Lyapunov sublevel filtration is
*everywhere* `Measurable`. **No invertibility (`det ≠ 0`), ergodicity, measure-preservation, or
log-norm integrability is assumed** — `A` and `T` are unrelated, the invertible-MET hypotheses
being traded for the everywhere gate `hUM` — and the result is strictly stronger than the a.e.
`ErgodicTheory.aemeasurable_orthProjMatrix_lambdaSublevel`.

The sublevel filtration has a measurable graph (`ErgodicTheory.measurableSet_graph_lambdaSublevel`),
which the general converter `measurable_orthProjMatrix_of_measurableGraph` turns into the
everywhere-measurable projector via the Novikov compact-section projection theorem. -/
theorem measurable_orthProjMatrix_lambdaSublevel
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) (hT : Measurable T)
    (hUM : ∀ x, IsUltrametricGrowth (lambdaBar A T x)) (c : ℝ) :
    Measurable fun x => orthProjMatrix (lambdaSublevel A T x c) :=
  measurable_orthProjMatrix_of_measurableGraph
    (measurableSet_graph_lambdaSublevel hA hT hUM c)

end Headline

end ErgodicTheory
