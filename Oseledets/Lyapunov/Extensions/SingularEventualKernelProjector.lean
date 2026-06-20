/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Oseledets.Lyapunov.Extensions.SingularKernelProjector
import Oseledets.Lyapunov.Extensions.SingularEventualKernel

/-!
# Measurability of the orthogonal projector onto the eventual kernel

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem degenerates
from a direct-sum decomposition to a measurable **filtration**
`ℝ^d = V₁(ω) ⊃ ⋯ ⊃ V_{k+1}(ω) = {0}` (Quas, *Multiplicative Ergodic Theorems and Applications*,
Universidade de São Paulo lecture notes, 2013, **Theorem 2**; after Oseledec and Raghunathan),
whose bottom flag space `V_{k+1}(ω)` is the *eventual kernel* `⨆ n, cocycleKer A T n x`: the
directions the matrix products ultimately collapse. Quas' Theorem 2 demands a *measurable* choice
of every flag space. This module closes the bottom of that flag: it makes the **eventual-kernel
subspace map measurable**, i.e. it proves `MeasurableSubspace (fun x => eventualKerEuclid A T x)`,
equivalently `Measurable (fun x => orthProjMatrix (eventualKerEuclid A T x))` — a measurable map
`x ↦ eventualKer A T x` into the (orthogonal-projection-matrix-encoded) Grassmannian.

## Strategy

The eventual kernel transported to the Euclidean space `EuclideanSpace ℝ (Fin d)`,
`eventualKerEuclid A T x := ⨆ n, cocycleKerEuclid A T n x`, is a **monotone** supremum of the
finite-step kernels (`cocycleKer_mono` transported through the linear iso). For a monotone family
`U` of submodules with `HasOrthogonalProjection`, the per-vector orthogonal projection converges,
`(U n).starProjection x₀ → (⨆ U).topologicalClosure.starProjection x₀` along `atTop`
(`Submodule.starProjection_tendsto_closure_iSup`). In the finite-dimensional `EuclideanSpace`
every submodule is closed, so `(⨆ U).topologicalClosure = ⨆ U = eventualKerEuclid A T x`
(`Submodule.topologicalClosure_eq_self`). Hence for each standard basis column `j`,
`x ↦ (eventualKerEuclid A T x).starProjection (single j 1)` is the **pointwise limit** (in `x`) of
`x ↦ (cocycleKerEuclid A T n x).starProjection (single j 1)`, each of which is column `j` of
`orthProjMatrix (cocycleKerEuclid A T n x)` — measurable by the per-step
`measurable_orthProjMatrix_cocycleKer` (via the column reduction `measurable_orthProjMatrix_iff`).
A pointwise limit of measurable `EuclideanSpace`-valued maps is measurable
(`measurable_of_tendsto_metrizable`, the metric pi-limit). Reassembling the columns through the
`⟸` direction of `measurable_orthProjMatrix_iff` gives the headline.

This route **sidesteps Kuratowski–Ryll-Nardzewski measurable selection** entirely (no such generic
theorem exists in Mathlib; cf. the directed-union graph context of
`SingularKernelMeasurableGraph.lean`): the explicit continuous-functional-calculus spectral
projector of the previous module plus this monotone-limit argument produce the measurable
projection directly, which is why it builds green where a generic measurable-selection theorem
would not.

## Main definitions

* `Oseledets.eventualKerEuclid`: the eventual kernel transported to `EuclideanSpace ℝ (Fin d)`,
  `⨆ n, cocycleKerEuclid A T n x`.

## Main results

* `Oseledets.cocycleKerEuclid_mono`: the step-kernel family `n ↦ cocycleKerEuclid A T n x` is
  monotone (transported `cocycleKer_mono`).
* `Oseledets.tendsto_starProjection_cocycleKerEuclid`: for each vector `v`, the finite-step
  star-projections `(cocycleKerEuclid A T n x).starProjection v` converge to
  `(eventualKerEuclid A T x).starProjection v` along `atTop`.
* `Oseledets.measurable_orthProjMatrix_eventualKer`:
  `x ↦ orthProjMatrix (eventualKerEuclid A T x)` is measurable.
* `Oseledets.measurableSubspace_eventualKer`:
  `MeasurableSubspace (fun x => eventualKerEuclid A T x)` — the measurable eventual-kernel subspace
  map, the bottom of the singular Oseledets flag.

## gap

This module delivers the measurable *bottom* flag space `x ↦ eventualKerEuclid A T x` of the
singular filtration. The intermediate slow spaces `V_j(ω)` (`1 ≤ j ≤ k`) and their EReal exponents
from the Kingman/exterior-power machinery are not assembled here; only the eventual-kernel stratum
is made measurable. The transported `eventualKerEuclid` is also not here shown equivariant in the
Euclidean picture (the algebraic equivariance lives at the `Fin d → ℝ` level in
`SingularKernelEquivariant.lean`).
-/

open MeasureTheory Filter Topology

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- **Congruence for `starProjection` under submodule equality.** If two submodules `K₁ = K₂` are
equal then their orthogonal projections agree pointwise. The two `HasOrthogonalProjection`
instances may differ syntactically, but the class is a `Prop`, so after substituting the equality
they coincide by proof irrelevance. (Used to identify the closure of the supremum with the
eventual kernel, whose
`HasOrthogonalProjection` instances are derived along different paths.) -/
private theorem starProjection_congr_left {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K₁ K₂ : Submodule ℝ E} [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] (h : K₁ = K₂) (v : E) :
    K₁.starProjection v = K₂.starProjection v := by
  subst h
  rfl

/-- The **eventual kernel** of the cocycle transported to `EuclideanSpace ℝ (Fin d)`: the supremum
(union) over all step counts `n` of the finite-step Euclidean kernels `cocycleKerEuclid A T n x`.
This is the Euclidean-space avatar of `Oseledets.eventualKer`, packaged so that `orthProjMatrix`
(the orthogonal-projection matrix encoding of `Oseledets.MeasurableSubspace`) applies to it; it is
the bottom flag space `V_{k+1}(ω) = {0}`-analogue of the singular Oseledets filtration (Quas,
*Multiplicative Ergodic Theorems and Applications*, 2013, Theorem 2). -/
noncomputable def eventualKerEuclid (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  ⨆ n, cocycleKerEuclid A T n x

/-- **Monotonicity of the transported step kernels.** The family `n ↦ cocycleKerEuclid A T n x` is
monotone in the step count: the finite-step kernel grows as the cocycle composes along the orbit
(`cocycleKer_le_add`), and this inclusion transports through the linear map `toEuclideanCLM`. -/
theorem cocycleKerEuclid_mono (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Monotone (fun n => cocycleKerEuclid A T n x) := by
  refine monotone_nat_of_le_succ fun n => ?_
  intro v hv
  simp only [cocycleKerEuclid, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
  -- `cocycle A T (n+1) x = cocycle A T 1 (T^[n] x) * cocycle A T n x` (kernel grows).
  have hadd : cocycle A T (n + 1) x = cocycle A T 1 (T^[n] x) * cocycle A T n x := by
    rw [show n + 1 = 1 + n from by ring, cocycle_add]
  rw [hadd, map_mul, ContinuousLinearMap.mul_apply, hv, map_zero]

/-- **Each finite-step Euclidean kernel sits inside the eventual one.** -/
theorem cocycleKerEuclid_le_eventualKerEuclid (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) :
    cocycleKerEuclid A T n x ≤ eventualKerEuclid A T x :=
  le_iSup (fun k => cocycleKerEuclid A T k x) n

/-- **The per-vector monotone-limit of the kernel projector.** For each fixed vector `v`, the
finite-step orthogonal projections `(cocycleKerEuclid A T n x).starProjection v` converge to
`(eventualKerEuclid A T x).starProjection v` along `atTop`. This is
`Submodule.starProjection_tendsto_closure_iSup` (Mathlib) for the monotone family
`n ↦ cocycleKerEuclid A T n x`, combined with the fact that in the finite-dimensional
`EuclideanSpace ℝ (Fin d)` the topological closure of `⨆ n, cocycleKerEuclid A T n x` is itself
(`Submodule.topologicalClosure_eq_self`). -/
theorem tendsto_starProjection_cocycleKerEuclid (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => (cocycleKerEuclid A T n x).starProjection v) atTop
      (𝓝 ((eventualKerEuclid A T x).starProjection v)) := by
  have hmono : Monotone (fun n => cocycleKerEuclid A T n x) := cocycleKerEuclid_mono A T x
  have hlim := Submodule.starProjection_tendsto_closure_iSup
    (fun n => cocycleKerEuclid A T n x) hmono v
  -- In finite dimension the closure of the supremum is the supremum itself, which is
  -- `eventualKerEuclid A T x`; the two limit points agree (`starProjection_congr_left`).
  have hpt : (eventualKerEuclid A T x).starProjection v
      = (⨆ n, cocycleKerEuclid A T n x).topologicalClosure.starProjection v :=
    starProjection_congr_left (Submodule.topologicalClosure_eq_self _).symm v
  rw [hpt]
  exact hlim

/-- **Measurability of the eventual-kernel projector.** The orthogonal-projection matrix onto the
eventual kernel `eventualKerEuclid A T x` is measurable in `x`. Each standard-basis column `j` of
this matrix is the pointwise limit (in `x`) of the corresponding column of the measurable
finite-step kernel projectors `orthProjMatrix (cocycleKerEuclid A T n x)`
(`measurable_orthProjMatrix_cocycleKer`); a pointwise limit of measurable `EuclideanSpace`-valued
maps is measurable (`measurable_of_tendsto_metrizable`), and the columns reassemble to a measurable
matrix through `measurable_orthProjMatrix_iff`.

This makes the bottom flag space of the singular (non-invertible) Oseledets filtration measurable
(Quas, *Multiplicative Ergodic Theorems and Applications*, 2013, Theorem 2). -/
theorem measurable_orthProjMatrix_eventualKer [MeasurableSpace X] [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T) :
    Measurable (fun x => orthProjMatrix (eventualKerEuclid A T x)) := by
  -- It suffices, by the column reduction, to make each column `j` measurable.
  rw [measurable_orthProjMatrix_iff]
  intro j
  -- Column `j` is the pointwise limit of the finite-step columns.
  have hstep : ∀ n, Measurable fun x =>
      (cocycleKerEuclid A T n x).starProjection (EuclideanSpace.single j (1 : ℝ)) :=
    fun n => (measurable_orthProjMatrix_iff.mp
      (measurable_orthProjMatrix_cocycleKer hA hT n)) j
  have hpt : Tendsto (fun n x =>
      (cocycleKerEuclid A T n x).starProjection (EuclideanSpace.single j (1 : ℝ))) atTop
      (𝓝 fun x => (eventualKerEuclid A T x).starProjection (EuclideanSpace.single j (1 : ℝ))) := by
    rw [tendsto_pi_nhds]
    intro x
    exact tendsto_starProjection_cocycleKerEuclid A T x (EuclideanSpace.single j (1 : ℝ))
  exact measurable_of_tendsto_metrizable hstep hpt

/-- **The campaign goal: the eventual-kernel subspace map is measurable.** The eventual kernel
`x ↦ eventualKerEuclid A T x` is a `MeasurableSubspace`, i.e. its orthogonal-projection matrix is
measurable in `x`. This closes the missing piece of the *full measurable equivariant singular
Oseledets filtration* (Quas, *Multiplicative Ergodic Theorems and Applications*, 2013, Theorem 2):
the bottom flag space `V_{k+1}(ω) = {0}` — the eventual kernel, the directions ultimately collapsed
— varies measurably in the base point. The proof routes through the explicit spectral
(continuous-functional-calculus) finite-step projectors and a monotone-limit, sidestepping the
Kuratowski–Ryll-Nardzewski measurable-selection theorem absent from Mathlib. -/
theorem measurableSubspace_eventualKer [MeasurableSpace X] [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T) :
    MeasurableSubspace (fun x => eventualKerEuclid A T x) :=
  measurable_orthProjMatrix_eventualKer hA hT

end Oseledets
