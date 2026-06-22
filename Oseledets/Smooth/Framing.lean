/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Measurable framing of the tangent bundle and the framed derivative cocycle

Let `M` be a `C¹` finite-dimensional real manifold modelled on `(E, H)` and let `T : M → M`
be `MDifferentiable`. The family of manifold derivatives `x ↦ mfderiv I I T x :
TangentSpace I x →L[ℝ] TangentSpace I (T x)` is a *linear cocycle on the tangent bundle*: by the
chain rule (`mfderiv_comp`) the derivative of the `n`-th iterate `T^[n]` factors as a composite
of derivatives along the orbit (`mfderiv_iterate_succ` below).

To feed this into the matrix Oseledets multiplicative ergodic theorem
(`Oseledets.oseledets_filtration`, which lives over `EuclideanSpace ℝ (Fin d)`), one must pick,
**measurably in `x`**, a linear frame of each tangent space `TangentSpace I x`. Such a choice — a
*measurable framing* — turns the abstract tangent cocycle into a genuine measurable matrix-valued
cocycle. The frame conjugates the abstract derivative `mfderiv I I T x` into a single fixed model
space `E`:
`framedGenerator T fr x := fr (T x) ∘L mfderiv I I T x ∘L (fr x).symm : E →L[ℝ] E`.

This file packages the *output* of a measurable trivialization (the structure
`MeasurableFraming`) and proves, **sorry-free**, that GIVEN such a framing the tangent cocycle
becomes a measurable cocycle of continuous linear self-maps of the model space `E` satisfying the
genuine cocycle identity. The companion file `Oseledets.Smooth.UnconditionalFraming` addresses
the construction of a measurable framing on a smooth second-countable manifold — the genuine wall
of this issue.

## Main definitions

* `MeasurableFraming I T` — a measurable choice of linear frame `TangentSpace I x ≃L[ℝ] E` at
  each point of `M`, such that the conjugated derivative `framedGenerator` is measurable.
* `MeasurableFraming.framedGenerator` — the model-space generator
  `x ↦ fr (T x) ∘L mfderiv I I T x ∘L (fr x).symm`.
* `MeasurableFraming.framedCocycle` — the iterated model-space cocycle.

## Main results

* `MDifferentiable.iterate` — iterates of an `MDifferentiable` self-map are `MDifferentiable`.
* `mfderiv_iterate_succ` — the **chain-rule cocycle identity** on the tangent bundle.
* `MeasurableFraming.framedCocycle_eq` — the iterated framed cocycle conjugates the iterate
  derivative `mfderiv I I (T^[n]) x` (the inner frames telescope away).
* `MeasurableFraming.measurable_framedGenerator'` — measurability of the model-space generator.

## References

* S. Filip, *Notes on the Multiplicative Ergodic Theorem*, arXiv:1710.10694, §2.2.2
  ("any vector bundle can be measurably trivialized").
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014), §4.
-/

open Filter Topology Function
open scoped Manifold

namespace Oseledets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M]

/-! ### The tangent cocycle: chain rule on the tangent bundle -/

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] [MeasurableSpace M] in
/-- Iterates of an `MDifferentiable` self-map are `MDifferentiable`. -/
protected theorem MDifferentiable.iterate {T : M → M} (hT : MDifferentiable I I T) :
    ∀ n : ℕ, MDifferentiable I I (T^[n])
  | 0 => by simpa using (mdifferentiable_id (I := I))
  | (n + 1) => by
    rw [Function.iterate_succ']
    exact hT.comp (MDifferentiable.iterate hT n)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [IsManifold I 1 M] in
/-- **Chain-rule cocycle identity on the tangent bundle (composition form).** For an
`MDifferentiable` self-map `T`, the derivative of `T^[n+1]` is the derivative of `T` at the
endpoint `T^[n] x` post-composed with the derivative of `T^[n]` at `x`. Iterating this is exactly
the tangent cocycle recursion (the manifold analogue of `Oseledets.chainRule_cocycle`). -/
theorem mfderiv_iterate_succ {T : M → M} (hT : MDifferentiable I I T) (n : ℕ) (x : M) :
    mfderiv I I (T^[n + 1]) x =
      (mfderiv I I T (T^[n] x)).comp (mfderiv I I (T^[n]) x) := by
  have hcomp : (T^[n + 1]) = T ∘ T^[n] := by
    rw [Function.iterate_succ']
  rw [hcomp]
  exact mfderiv_comp x (hT (T^[n] x)) (MDifferentiable.iterate hT n x)

/-! ### Measurable framing -/

/-- A **measurable framing** of the tangent bundle adapted to a self-map `T : M → M`: a pointwise
choice of linear frame `frame x : TangentSpace I x ≃L[ℝ] E` of each tangent space, identifying it
with the model space `E`, such that the conjugated derivative
`x ↦ frame (T x) ∘L mfderiv I I T x ∘L (frame x).symm` is a measurable map into `E →L[ℝ] E`.

This is the *output* of a measurable trivialization of the tangent bundle: by Filip's notes
(§2.2.2) any vector bundle over a (standard Borel) base can be measurably trivialized, so on a
smooth second-countable manifold such a framing exists. The *existence* is the genuine wall of
issue #2 (the framing-existence wall); this structure isolates exactly the data the
matrix MET consumes. -/
structure MeasurableFraming (I : ModelWithCorners ℝ E H) (T : M → M) where
  /-- The linear frame at each point: an isomorphism of the tangent space with the model space. -/
  frame : (x : M) → TangentSpace I x ≃L[ℝ] E
  /-- The conjugated (frame-coordinate) derivative is measurable in the base point. -/
  measurable_framedGenerator :
    Measurable fun x : M =>
      (frame (T x) : TangentSpace I (T x) →L[ℝ] E).comp
        ((mfderiv I I T x).comp ((frame x).symm : E →L[ℝ] TangentSpace I x))

namespace MeasurableFraming

variable {T : M → M}

/-- The **framed derivative cocycle generator**: the manifold derivative `mfderiv I I T x`
conjugated by the chosen frames into a continuous linear self-map of the model space `E`. -/
noncomputable def framedGenerator (fr : MeasurableFraming I T) (x : M) : E →L[ℝ] E :=
  (fr.frame (T x) : TangentSpace I (T x) →L[ℝ] E).comp
    ((mfderiv I I T x).comp ((fr.frame x).symm : E →L[ℝ] TangentSpace I x))

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] in
/-- The measurability field, restated for the named generator. -/
theorem measurable_framedGenerator' (fr : MeasurableFraming I T) :
    Measurable (framedGenerator fr) :=
  fr.measurable_framedGenerator

/-- The `n`-fold composite of `framedGenerator` along the orbit, the model-space cocycle. -/
noncomputable def framedCocycle (fr : MeasurableFraming I T) : ℕ → M → (E →L[ℝ] E)
  | 0, _ => ContinuousLinearMap.id ℝ E
  | (n + 1), x => (fr.framedGenerator (T^[n] x)).comp (fr.framedCocycle n x)

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] in
@[simp] theorem framedCocycle_zero (fr : MeasurableFraming I T) (x : M) :
    fr.framedCocycle 0 x = ContinuousLinearMap.id ℝ E := rfl

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] in
theorem framedCocycle_succ (fr : MeasurableFraming I T) (n : ℕ) (x : M) :
    fr.framedCocycle (n + 1) x =
      (fr.framedGenerator (T^[n] x)).comp (fr.framedCocycle n x) := rfl

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] in
/-- **The framed cocycle conjugates the iterate derivative.** The `n`-fold model-space cocycle
`framedCocycle fr n x` equals the manifold derivative of `T^[n]` at `x`, conjugated by the frame
at the start point `x` and the frame at the end point `T^[n] x`:
`framedCocycle fr n x = fr.frame (T^[n] x) ∘L mfderiv I I (T^[n]) x ∘L (fr.frame x).symm`.
The inner frames telescope away — exactly the statement that the framed product is a genuine
representation of the tangent cocycle in the chosen trivialization. -/
theorem framedCocycle_eq (fr : MeasurableFraming I T) (hT : MDifferentiable I I T)
    (n : ℕ) (x : M) :
    fr.framedCocycle n x =
      (fr.frame (T^[n] x) : TangentSpace I (T^[n] x) →L[ℝ] E).comp
        ((mfderiv I I (T^[n]) x).comp
          ((fr.frame x).symm : E →L[ℝ] TangentSpace I x)) := by
  induction n with
  | zero =>
    simp only [framedCocycle_zero, Function.iterate_zero, id_eq]
    rw [mfderiv_id]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe]
    exact ((fr.frame x).apply_symm_apply v).symm
  | succ n ih =>
    rw [framedCocycle_succ, ih, framedGenerator, mfderiv_iterate_succ hT n x]
    -- Telescope: (e_{T^{n+1}x} ∘ DT_{T^n x} ∘ e_{T^n x}⁻¹) ∘ (e_{T^n x} ∘ D(T^n)_x ∘ e_x⁻¹)
    --          = e_{T^{n+1}x} ∘ DT_{T^n x} ∘ D(T^n)_x ∘ e_x⁻¹.
    -- Align the endpoint frame index `T^[n+1] x = T (T^[n] x)`, then cancel the inner pair
    -- `e_{T^n x}.symm (e_{T^n x} w) = w` (`symm_apply_apply`), flattening with `comp_apply`.
    ext v
    rw [show T^[n + 1] x = T (T^[n] x) from Function.iterate_succ_apply' T n x]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] in
/-- **Norm of the framed generator** equals the norm of the conjugated derivative — the bridge
that lets one phrase the integrability hypotheses of the matrix MET in terms of the framing.
(Definitional: `framedGenerator` *is* that conjugated map.) -/
theorem norm_framedGenerator (fr : MeasurableFraming I T) (x : M) :
    ‖fr.framedGenerator x‖ =
      ‖(fr.frame (T x) : TangentSpace I (T x) →L[ℝ] E).comp
        ((mfderiv I I T x).comp ((fr.frame x).symm : E →L[ℝ] TangentSpace I x))‖ := rfl

end MeasurableFraming

end Oseledets
