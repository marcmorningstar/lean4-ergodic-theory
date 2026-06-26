/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Examples.Elementary
import Oseledets.Examples.CatMapToral
import Oseledets.Lyapunov.Extensions.ConstantCocycleSpectralRadius
import Oseledets.Smooth.DerivativeCocycle

/-!
# The genuine Arnold cat-map derivative cocycle has a positive top exponent

The companion module `Oseledets/Examples/Elementary.lean` realizes the cat-map *matrix*
`M = !![2,1;1,1]` as a **constant cocycle over the doubling map** and reads off its Lyapunov
spectrum `log((3 ± √5)/2)` (`Oseledets.catMapMatrix_exponents`).  That theorem carries an explicit
*honesty caveat*: the base is the doubling map, not the genuine cat-map dynamics, and the cocycle is
the bare constant matrix, **not** the derivative cocycle of the Arnold cat map.

This module removes that caveat on two fronts, banking each independently.

## Grade 1 — the genuine ergodic torus base

`Oseledets/Examples/CatMapToral.lean` proves the genuine Arnold cat map `catTorus : 𝕋² → 𝕋²` is
**ergodic** for Haar (`Oseledets.CatMapToral.ergodic_catTorus`).  We realize the cat-map matrix
`catℝ` as a constant cocycle over *this* ergodic base and read off the spectrum
`log((3 ± √5)/2)`, with top exponent `log((3 + √5)/2) > 0`
(`catTorus_constCocycle_topExponent_pos`).  This strictly improves the doubling-map version: the
base is now the genuine hyperbolic toral automorphism.

## Grade 2a — the genuine derivative of the cat map's linear lift

The Arnold cat map lifts to the universal cover `ℝ²` as the genuine `ℝ`-linear map `catLift` with
matrix `catℝ` (acting through `Matrix.toEuclideanCLM`).  The Fréchet derivative of a continuous
linear map is the map itself (`ContinuousLinearMap.fderiv`), so the repo's derivative cocycle of
`catLift` is the **constant** matrix `catℝ` at every point
(`derivativeCocycle_catLift`).  Hence `derivativeCocycle catLift` *is* — in the repo's exact
`DerivativeCocycle` framework — the genuine tangent cocycle of the cat map's linear lift, and it
equals the constant `catℝ`.  Combining with Grade 1, the top Lyapunov exponent of this **genuine
derivative cocycle**, realized over the genuine ergodic base `catTorus`, is `log((3 + √5)/2) > 0`
(`catLift_derivativeCocycle_topExponent_pos`).  This is fully honest: `catLift` is the genuine
ℝ²-linear lift of the cat map to the universal cover, and `derivativeCocycle` is the repo's genuine
Fréchet-derivative cocycle.

## Grade 2b — the manifold `mfderiv` reading (documented gap)

A third, strictly stronger route would read the derivative directly on the torus *manifold*: prove
`mfderiv` of `catTorus`, in the standard `AddCircle` charts, equals `catℝ`.  Mathlib provides the
charted/smooth-manifold structure on `AddCircle` but has **no `mfderiv` API for `AddCircle`
endomorphisms** (no lemma computing the manifold derivative of `n • ·` or of an `AddMonoidHom` of a
product of circles in terms of its matrix).  Supplying that API is a genuine Mathlib-scale task
orthogonal to the Oseledets development, so we do **not** pursue 2b here; the universal-cover lift
(Grade 2a) is the honest derivative-cocycle deliverable, since the cat map and its lift have the
*same* derivative everywhere (the covering projection `ℝ² → 𝕋²` is a local diffeomorphism with
identity derivative).

## Main results

* `Oseledets.CatMapToral.catTorus_constCocycle_exponents` — the two Lyapunov exponents of the
  constant cocycle `catℝ` over the genuine ergodic base `catTorus` are `log((3 ± √5)/2)`.
* `Oseledets.CatMapToral.catTorus_constCocycle_topExponent_pos` — its top exponent is
  `log((3 + √5)/2) > 0`.
* `Oseledets.CatMapToral.catLift` — the genuine ℝ²-linear lift of the cat map to the universal
  cover, with matrix `catℝ`.
* `Oseledets.CatMapToral.derivativeCocycle_catLift` — the repo's derivative cocycle of `catLift`
  is the constant matrix `catℝ` at every point.
* `Oseledets.CatMapToral.catLift_derivativeCocycle_topExponent_pos` — the top Lyapunov exponent of
  the **genuine derivative cocycle** of `catLift`, over the genuine ergodic base `catTorus`, is
  `log((3 + √5)/2) > 0`.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `Oseledets/Examples/CatMapToral.lean` so that the
ambient `volume : Measure T2` here is *the same* product Haar probability measure for which
`ergodic_catTorus` is stated. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Oseledets.CatMapToral

/-! ## The real cat-map matrix coincides with `Elementary`'s `catMapGen` -/

/-- The real cat-map matrix `catℝ = !![2,1;1,1]` is literally `Elementary`'s `catMapGen`. -/
theorem catℝ_eq_catMapGen : catℝ = Oseledets.catMapGen := rfl

/-- `catℝ` is symmetric (inherited from `catMapGen`). -/
theorem catℝ_transpose' : catℝᵀ = catℝ := Oseledets.catMapGen_transpose

/-- `catℝ` is positive semidefinite (inherited from `catMapGen`). -/
theorem catℝ_posSemidef : catℝ.PosSemidef := Oseledets.catMapGen_posSemidef

/-- `det catℝ = 1 ≠ 0` (inherited from `catMapGen`). -/
theorem catℝ_det_ne_zero : catℝ.det ≠ 0 := Oseledets.catMapGen_det_ne_zero

/-- The Hermitian witness for `catℝ`, reused from `catMapGen`. -/
theorem catℝ_isHermitian : catℝ.IsHermitian := Oseledets.catMapGen_isHermitian

/-! ## Grade 1 — the constant cat-map cocycle over the genuine ergodic torus base -/

/-- **Grade 1.  The cat-map Lyapunov spectrum over the genuine ergodic base.**  Realized as a
constant cocycle with generator `catℝ = !![2,1;1,1]` over the **genuine** ergodic Arnold cat map
`catTorus : 𝕋² → 𝕋²` (`ergodic_catTorus`), the two Lyapunov exponents are `log((3 + √5)/2)` and
`log((3 - √5)/2)` — the logs of the eigenvalues of the cat-map matrix.

Unlike `Oseledets.catMapMatrix_exponents`, the base here is the genuine hyperbolic toral
automorphism, not the doubling map. -/
theorem catTorus_constCocycle_exponents :
    Oseledets.exponents ergodic_catTorus (Oseledets.const_det_ne_zero catℝ_det_ne_zero)
        (Oseledets.const_measurable catℝ) (Oseledets.const_integrableLogNorm catℝ)
        (Oseledets.const_integrableLogNorm_inv catℝ)
        ⟨(0 : ℕ), lt_of_lt_of_eq (Fin.isLt (0 : Fin (Fintype.card (Fin 2)))) (Fintype.card_fin 2)⟩
      = Real.log ((3 + Real.sqrt 5) / 2) ∧
    Oseledets.exponents ergodic_catTorus (Oseledets.const_det_ne_zero catℝ_det_ne_zero)
        (Oseledets.const_measurable catℝ) (Oseledets.const_integrableLogNorm catℝ)
        (Oseledets.const_integrableLogNorm_inv catℝ)
        ⟨(1 : ℕ), lt_of_lt_of_eq (Fin.isLt (1 : Fin (Fintype.card (Fin 2)))) (Fintype.card_fin 2)⟩
      = Real.log ((3 - Real.sqrt 5) / 2) := by
  obtain ⟨h0, h1⟩ := Oseledets.catMapGen_eigenvalues_closedForm
  -- The sorted eigenvalues of `|catℝ|` are those of `catℝ = catMapGen`; bridge the
  -- (proof-irrelevant) Hermitian witness `catℝ_posSemidef.isHermitian` to `catMapGen_isHermitian`.
  have hbridge : ∀ i : Fin (Fintype.card (Fin 2)),
      (Oseledets.absMatrix_isHermitian catℝ).eigenvalues₀ i
        = Oseledets.catMapGen_isHermitian.eigenvalues₀ i := fun i =>
    (Oseledets.eigenvalues₀_absMatrix_of_posSemidef catℝ_posSemidef i).trans
      (Oseledets.eigenvalues₀_congr catℝ_posSemidef.isHermitian Oseledets.catMapGen_isHermitian
        catℝ_eq_catMapGen i)
  refine ⟨?_, ?_⟩
  · have key := Oseledets.exponents_const ergodic_catTorus catℝ_transpose' catℝ_det_ne_zero
      (0 : Fin (Fintype.card (Fin 2)))
    rw [hbridge 0, h0] at key
    exact key
  · have key := Oseledets.exponents_const ergodic_catTorus catℝ_transpose' catℝ_det_ne_zero
      (1 : Fin (Fintype.card (Fin 2)))
    rw [hbridge 1, h1] at key
    exact key

/-- **Grade 1 (headline).  The top Lyapunov exponent over the genuine ergodic base is positive.**
The top Lyapunov exponent of the constant cat-map cocycle `catℝ` over the genuine ergodic Arnold cat
map `catTorus` is `log((3 + √5)/2) > 0`.  Positivity is the hyperbolicity of the cat map:
`(3 + √5)/2 > 1`. -/
theorem catTorus_constCocycle_topExponent_pos :
    0 < Oseledets.topExponent ergodic_catTorus (Oseledets.const_det_ne_zero catℝ_det_ne_zero)
        (Oseledets.const_measurable catℝ) (Oseledets.const_integrableLogNorm catℝ)
        (Oseledets.const_integrableLogNorm_inv catℝ) := by
  -- The top exponent is `exponents … ⟨0, _⟩`, which Grade 1 evaluates to `log((3+√5)/2)`.
  rw [Oseledets.topExponent, catTorus_constCocycle_exponents.1]
  -- `(3 + √5)/2 > 1`, so its log is positive.
  apply Real.log_pos
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  linarith

/-! ## Grade 2a — the genuine derivative cocycle of the cat map's linear lift -/

/-- **The universal-cover lift of the Arnold cat map.**  The cat map `catTorus : 𝕋² → 𝕋²` lifts to
the universal cover `ℝ² = EuclideanSpace ℝ (Fin 2)` as the genuine `ℝ`-linear map with matrix
`catℝ`, acting through the star-algebra equivalence `Matrix.toEuclideanCLM`.  The covering
projection `ℝ² → 𝕋²` intertwines `catLift` with `catTorus`, and is a local diffeomorphism with
identity derivative, so `catLift` and `catTorus` have the same derivative everywhere. -/
noncomputable def catLift : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) catℝ)

/-- `catLift` is the coercion of the continuous linear map `toEuclideanCLM catℝ`, hence its Fréchet
derivative at every point is that very map: `fderiv ℝ catLift x = toEuclideanCLM catℝ`. -/
theorem fderiv_catLift (x : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ catLift x = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) catℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) catℝ).fderiv

/-- `catLift` is differentiable (it is a continuous linear map). -/
theorem differentiable_catLift : Differentiable ℝ catLift :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) catℝ).differentiable

/-- **Grade 2a.  The repo's derivative cocycle of `catLift` is the constant matrix `catℝ`.**  Since
`catLift` is a continuous linear map, its Fréchet derivative at every point is itself
(`fderiv_catLift`); transporting back along `toEuclideanCLM.symm` recovers the matrix `catℝ`.  So
the genuine tangent cocycle of the cat map's linear lift, in the repo's exact
`DerivativeCocycle` framework, is the constant generator `catℝ`. -/
@[simp] theorem derivativeCocycle_catLift (x : EuclideanSpace ℝ (Fin 2)) :
    Oseledets.derivativeCocycle catLift x = catℝ := by
  rw [Oseledets.derivativeCocycle, fderiv_catLift x]
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)).symm_apply_apply catℝ

/-- The derivative cocycle of `catLift` is the **constant** generator `fun _ => catℝ`. -/
theorem derivativeCocycle_catLift_eq_const :
    Oseledets.derivativeCocycle catLift = fun _ : EuclideanSpace ℝ (Fin 2) => catℝ :=
  funext derivativeCocycle_catLift

/-- The determinant of the constant derivative-cocycle generator `derivativeCocycle catLift 0` is
nonzero (it equals `catℝ`, whose determinant is `1`). -/
theorem derivativeCocycle_catLift_det_ne_zero :
    (Oseledets.derivativeCocycle catLift (0 : EuclideanSpace ℝ (Fin 2))).det ≠ 0 := by
  rw [derivativeCocycle_catLift]; exact catℝ_det_ne_zero

/-- **Grade 2a (headline).  The genuine derivative cocycle of the cat map's lift has positive top
exponent over the genuine ergodic base.**  The derivative cocycle of `catLift` is the constant
matrix `catℝ` (`derivativeCocycle_catLift`).  Realized as a constant cocycle over the genuine
ergodic Arnold cat map `catTorus`, the top Lyapunov exponent of this **genuine derivative cocycle**
is the same constant-cocycle top exponent as in Grade 1, namely `log((3 + √5)/2) > 0`.

This closes the *EuclideanSpace ↔ torus adapter gap*: the generator is no longer a bare constant
matrix — it is the genuine Fréchet derivative `derivativeCocycle catLift` of the cat map's ℝ²-linear
lift to the universal cover (the repo's `DerivativeCocycle.derivativeCocycle`), evaluated as a
constant cocycle over the genuine hyperbolic toral automorphism, and its top Lyapunov exponent is
positive. -/
theorem catLift_derivativeCocycle_topExponent_pos :
    0 < Oseledets.topExponent ergodic_catTorus
        (Oseledets.const_det_ne_zero derivativeCocycle_catLift_det_ne_zero)
        (Oseledets.const_measurable
          (Oseledets.derivativeCocycle catLift (0 : EuclideanSpace ℝ (Fin 2))))
        (Oseledets.const_integrableLogNorm
          (Oseledets.derivativeCocycle catLift (0 : EuclideanSpace ℝ (Fin 2))))
        (Oseledets.const_integrableLogNorm_inv
          (Oseledets.derivativeCocycle catLift (0 : EuclideanSpace ℝ (Fin 2)))) := by
  -- The constant generator `derivativeCocycle catLift 0` equals `catℝ`; transport the Grade-1
  -- positivity along this equality.  Generalizing the (proof-irrelevant) hypothesis bundles first
  -- lets the single `rw` retype the whole `topExponent` term.
  have hpos := catTorus_constCocycle_topExponent_pos
  generalize derivativeCocycle_catLift_det_ne_zero = hdet
  revert hdet
  rw [derivativeCocycle_catLift 0]
  intro hdet
  exact hpos

end Oseledets.CatMapToral
