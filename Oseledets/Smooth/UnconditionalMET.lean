/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Topology.Compactness.SigmaCompact
import Oseledets.Smooth.Framing
import Oseledets.Smooth.UnconditionalFraming
import Oseledets.Smooth.FrameAlg
import Oseledets.Cocycle.Norm
import Oseledets.MultiplicativeErgodic

/-!
# Unconditional Oseledets MET for the framed tangent cocycle (issue #9, no chart regularity)

The earlier canonical-frame headline `oseledets_filtration_derivativeCocycleManifold` (a staging
route, now superseded) fed the *canonical* manifold derivative
`x ↦ mfderiv I I T x` — framed by the **globally constant** `frameAlg` — into the matrix MET
`Oseledets.oseledets_filtration`, and **takes its measurability `hAmeas` as a hypothesis**. That
hypothesis is only dischargeable under the chart-regularity assumption
`[LocallyConstantChartAt H M]` (the canonical `chartAt x` is a pathological selector, so
`x ↦ mfderiv I I T x` need not be measurable for an arbitrary `ChartedSpace`).

This file removes that hypothesis entirely. We feed the matrix MET the **framed** cocycle attached
to a `MeasurableFraming I T` (`Oseledets.Smooth.Framing`): the *piecewise* tangent frame
produced by `Oseledets.Smooth.UnconditionalFraming`, whose conjugated generator
`framedGenerator` is measurable **with no chart regularity** (the moving native charts cancel inside
the conjugated composite, leaving the `fderivWithin` of a fixed-chart-written `C¹` map — see
`UnconditionalFraming.continuousOn_conjGen_block2`). Pushing that generator through the constant
framing algebra `frameAlg` gives a measurable matrix cocycle, so the measurability of the matrix
generator is discharged **unconditionally**:
`A x := frameAlg E (fr.framedGenerator x)` and
`measurable A = (measurable_frameAlg).comp fr.measurable_framedGenerator'`.

## Main results

* `framedMatrixCocycle_eq` — the matrix cocycle `Oseledets.cocycle A T n x` equals
  `frameAlg E (fr.framedCocycle n x)` (multiplicativity of `frameAlg`, by induction along the
  orbit).
* `oseledets_filtration_framedTangentCocycle` — **framing-parametrised unconditional headline**:
  given any `fr : MeasurableFraming I T`, the matrix cocycle
  `A x := frameAlg E (fr.framedGenerator x)` is measurable **unconditionally**, and under the
  genuine dynamical hypotheses (ergodicity, nonsingularity, log-integrability) admits an Oseledets
  filtration — **no `LocallyConstantChartAt`**.
* `exists_oseledets_filtration_framedTangentCocycle` — **fully unconditional existence form**: on
  a σ-compact boundaryless `C¹` manifold there *exists* a measurable framing whose framed tangent
  cocycle has an Oseledets filtration — **no `LocallyConstantChartAt`**.

## References

* S. Filip, *Notes on the Multiplicative Ergodic Theorem*, arXiv:1710.10694, §2.2.2.
* L. Arnold, *Random Dynamical Systems*, Springer (1998), Ch. 4 (MET on bundles and manifolds).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator Manifold

namespace Oseledets

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M]

/-! ### `frameAlg` is multiplicative along the framed cocycle -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] in
/-- **Right-telescoping recursion of the framed cocycle.** Reassociating the orbit, the `(n+1)`-fold
framed cocycle factors as `framedCocycle n (T x)` post-composed with the single generator
`framedGenerator x`. (The native recursion `framedCocycle_succ` peels the *outermost* factor; this
peels the *innermost* one — the two agree by the chain-rule telescoping `framedCocycle_eq`.) -/
theorem framedCocycle_succ_right {T : M → M} (hT : MDifferentiable I I T)
    (fr : MeasurableFraming I T) (n : ℕ) (x : M) :
    fr.framedCocycle (n + 1) x =
      (fr.framedCocycle n (T x)).comp (fr.framedGenerator x) := by
  -- **Inner** chain rule: `D(T^{n+1})_x = D(T^n)_{Tx} ∘ DT_x` (peel the innermost factor), from
  -- `T^[n+1] = T^[n] ∘ T` and `mfderiv_comp`.
  have hinner : mfderiv I I (T^[n + 1]) x =
      (mfderiv I I (T^[n]) (T x)).comp (mfderiv I I T x) := by
    have hcomp : T^[n + 1] = T^[n] ∘ T := by rw [Function.iterate_succ]
    rw [hcomp, mfderiv_comp x (MDifferentiable.iterate hT n (T x)) (hT x)]
  rw [fr.framedCocycle_eq hT (n + 1) x, fr.framedCocycle_eq hT n (T x),
    MeasurableFraming.framedGenerator, hinner]
  -- LHS: e_{T^{n+1}x} ∘ D(T^n)_{Tx} ∘ DT_x ∘ e_x⁻¹.
  -- RHS: [e_{T^n(Tx)} ∘ D(T^n)_{Tx} ∘ e_{Tx}⁻¹] ∘ [e_{Tx} ∘ DT_x ∘ e_x⁻¹].
  -- Align the index `T^[n] (T x) = T^[n+1] x` and cancel the inner `e_{Tx}⁻¹ ∘ e_{Tx} = id`.
  ext v
  rw [show (T^[n]) (T x) = (T^[n + 1]) x from (Function.iterate_succ_apply T n x).symm]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] in
/-- **The matrix cocycle represents the framed tangent cocycle.** Pushing the framed cocycle through
the (constant) framing algebra `frameAlg E` turns it into the matrix cocycle of
`A x := frameAlg E (fr.framedGenerator x)`:
`Oseledets.cocycle A T n x = frameAlg E (fr.framedCocycle n x)`.

Proved by induction, peeling the innermost generator from both the cocycle recursion
(`cocycle_succ`) and the right-telescoping framed recursion (`framedCocycle_succ_right`), using that
`frameAlg E` is an algebra equivalence (`map_one`, `map_mul`; multiplication in `E →L[ℝ] E` is
composition). -/
theorem framedMatrixCocycle_eq {T : M → M} (hT : MDifferentiable I I T)
    (fr : MeasurableFraming I T) (n : ℕ) (x : M) :
    Oseledets.cocycle (fun y => frameAlg E (fr.framedGenerator y)) T n x
      = frameAlg E (fr.framedCocycle n x) := by
  induction n generalizing x with
  | zero =>
    rw [Oseledets.cocycle_zero, MeasurableFraming.framedCocycle_zero]
    -- `ContinuousLinearMap.id ℝ E = (1 : E →L[ℝ] E)`, and `frameAlg E` is an algebra map.
    exact (map_one (frameAlg E)).symm
  | succ n ih =>
    rw [Oseledets.cocycle_succ, ih (T x), framedCocycle_succ_right hT fr n x, ← map_mul]
    -- the remaining goal `frameAlg E (a * b) = frameAlg E (a ∘L b)` is `rfl`:
    -- multiplication in `E →L[ℝ] E` is composition.
    rfl

/-! ### The framing-parametrised unconditional headline -/

set_option linter.unusedSectionVars false in
/-- **Oseledets MET for the framed tangent cocycle (framing-parametrised, unconditional).**

Given **any** measurable framing `fr : MeasurableFraming I T` of the tangent bundle adapted to a
`C¹` self-map `T`, set the matrix cocycle `A x := frameAlg E (fr.framedGenerator x)`. Then:

* `A` is **measurable unconditionally** — discharged as
  `(measurable_frameAlg).comp fr.measurable_framedGenerator'`, with **NO `LocallyConstantChartAt`**
  and **NO `hAmeas` hypothesis** (the chart pathology is dodged: `fr.framedGenerator` is measurable
  by the piecewise-fixed-chart construction of `UnconditionalFraming`);
* under the genuine dynamical hypotheses — `T` ergodic measure-preserving, every generator
  nonsingular (`hdet`), and `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹(μ)` (`hint`, `hint'`) — `A` admits the full
  Oseledets filtration `Oseledets.oseledets_filtration`.

The first conjunct certifies that the matrix cocycle is the genuine framed tangent cocycle:
`Oseledets.cocycle A T n x = frameAlg E (fr.framedCocycle n x)` (`framedMatrixCocycle_eq`), and by
`fr.framedCocycle_eq` the right-hand side is `frameAlg E` of the conjugated iterate derivative
`fr.frame (T^[n] x) ∘L mfderiv I I (T^[n]) x ∘L (fr.frame x).symm`. -/
theorem oseledets_filtration_framedTangentCocycle
    {μ : Measure M} [IsProbabilityMeasure μ] {T : M → M}
    (hTerg : Ergodic T μ) (hdiff : MDifferentiable I I T)
    (fr : MeasurableFraming I T)
    (hdet : ∀ x, (frameAlg E (fr.framedGenerator x)).det ≠ 0)
    (hint : Oseledets.IntegrableLogNorm (fun x => frameAlg E (fr.framedGenerator x)) μ)
    (hint' : Oseledets.IntegrableLogNorm
      (fun x => (frameAlg E (fr.framedGenerator x))⁻¹) μ) :
    (∀ (n : ℕ) (x : M),
        Oseledets.cocycle (fun y => frameAlg E (fr.framedGenerator y)) T n x
          = frameAlg E (fr.framedCocycle n x)) ∧
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) →
        M → Submodule ℝ (EuclideanSpace ℝ (Fin (modelDim E)))),
      StrictAnti lam ∧
      (∀ i, Oseledets.MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (frameAlg E (fr.framedGenerator x))).toLinearMap
            (V i x) = V i (T x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin (modelDim E)))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log
                  ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (Oseledets.cocycle (fun y => frameAlg E (fr.framedGenerator y)) T n x) v‖)
              atTop (𝓝 (lam i))) :=
  -- `hAmeas` is discharged UNCONDITIONALLY: `frameAlg E` is measurable, `fr.framedGenerator` is
  -- measurable (no chart regularity), so the composite is measurable.
  ⟨fun n x => framedMatrixCocycle_eq hdiff fr n x,
    Oseledets.oseledets_filtration hTerg (fun y => frameAlg E (fr.framedGenerator y)) hdet
      ((measurable_frameAlg (E := E)).comp (fr.measurable_framedGenerator')) hint hint'⟩

/-! ### The fully unconditional existence form -/

variable [I.Boundaryless] [SigmaCompactSpace M] [SecondCountableTopology H]
  [BorelSpace M]

set_option linter.unusedSectionVars false in
/-- **Fully unconditional Oseledets MET for the framed tangent cocycle (existence form).**

On a σ-compact, boundaryless, finite-dimensional `C¹` manifold with its Borel σ-algebra, for any
ergodic measure-preserving `C¹` self-map `T`, **there exists** a measurable framing `fr` of the
tangent bundle whose framed matrix cocycle `A x := frameAlg E (fr.framedGenerator x)` admits the
full Oseledets filtration — provided the genuine per-framing dynamical hypotheses (nonsingularity,
log-integrability) hold for *that* framing.

The framing is produced **unconditionally** by
`UnconditionalFraming.exists_measurableFraming_of_sigmaCompact` (piecewise fixed reference charts;
**no `LocallyConstantChartAt`**), and its framed generator is measurable by construction, so the
MET's measurability obligation never reappears. The conclusion is stated as: *there exists a framing
such that, granting its dynamical hypotheses, the filtration holds* — keeping the per-framing
det/log data as honest hypotheses (exactly as in the matrix MET), while the **measurability win** is
fully discharged. -/
theorem exists_oseledets_filtration_framedTangentCocycle
    {μ : Measure M} [IsProbabilityMeasure μ] {T : M → M}
    (hTerg : Ergodic T μ) (hTsmooth : ContMDiff I I 1 T) :
    ∃ fr : MeasurableFraming I T,
      (∀ x, (frameAlg E (fr.framedGenerator x)).det ≠ 0) →
      Oseledets.IntegrableLogNorm (fun x => frameAlg E (fr.framedGenerator x)) μ →
      Oseledets.IntegrableLogNorm (fun x => (frameAlg E (fr.framedGenerator x))⁻¹) μ →
      (∀ (n : ℕ) (x : M),
          Oseledets.cocycle (fun y => frameAlg E (fr.framedGenerator y)) T n x
            = frameAlg E (fr.framedCocycle n x)) ∧
      ∃ (k : ℕ) (lam : Fin k → ℝ)
        (V : Fin (k + 1) →
          M → Submodule ℝ (EuclideanSpace ℝ (Fin (modelDim E)))),
        StrictAnti lam ∧
        (∀ i, Oseledets.MeasurableSubspace fun x => V i x) ∧
        ∀ᵐ x ∂μ,
          V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
          (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
          (∀ i : Fin (k + 1),
            Submodule.map
              (Matrix.toEuclideanCLM (𝕜 := ℝ) (frameAlg E (fr.framedGenerator x))).toLinearMap
              (V i x) = V i (T x)) ∧
          (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin (modelDim E)))),
              v ∉ V i.succ x →
              Tendsto
                (fun n : ℕ => (n : ℝ)⁻¹ *
                  Real.log
                    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                      (Oseledets.cocycle (fun y => frameAlg E (fr.framedGenerator y)) T n x) v‖)
                atTop (𝓝 (lam i))) := by
  -- Produce a measurable framing UNCONDITIONALLY (no chart regularity).
  obtain ⟨fr⟩ := exists_measurableFraming_of_sigmaCompact hTsmooth
  refine ⟨fr, fun hdet hint hint' => ?_⟩
  exact oseledets_filtration_framedTangentCocycle hTerg
    (hTsmooth.mdifferentiable one_ne_zero) fr hdet hint hint'

end

end Oseledets
