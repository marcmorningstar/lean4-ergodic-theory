/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import ErgodicTheory.Cocycle.Norm
import ErgodicTheory.MultiplicativeErgodic

/-!
# The derivative (tangent) cocycle of a smooth self-map

For a differentiable self-map `T : E → E` of `E := EuclideanSpace ℝ (Fin d)`, the family of
derivatives `x ↦ Dₓ T = fderiv ℝ T x` is a linear cocycle over `T`: by the chain rule the
derivative of the `n`-th iterate `T^[n]` factors as a product of derivatives along the orbit.
Transporting `fderiv ℝ T x : E →L[ℝ] E` to a matrix through the star-algebra equivalence
`Matrix.toEuclideanCLM` turns this into the matrix cocycle `cocycle (derivativeCocycle T) T`,
which feeds directly into the Oseledets multiplicative ergodic theorem.

The matrix norm throughout is the (scoped) L2 operator norm `Matrix.Norms.L2Operator`; matrices
act on `EuclideanSpace ℝ (Fin d)` via `Matrix.toEuclideanCLM`.

## Main definitions

* `ErgodicTheory.derivativeCocycle` — the matrix-valued generator
  `x ↦ (toEuclideanCLM).symm (Dₓ T)`.

## Main results

* `ErgodicTheory.toEuclideanCLM_derivativeCocycle` —
  `toEuclideanCLM (derivativeCocycle T x) = Dₓ T`.
* `ErgodicTheory.norm_derivativeCocycle` — the generator has the same L2 operator norm as `Dₓ T`.
* `ErgodicTheory.chainRule_cocycle` — the **chain-rule cocycle identity**
  `toEuclideanCLM (cocycle (derivativeCocycle T) T n x) = fderiv ℝ (T^[n]) x`.
* `ErgodicTheory.measurable_derivativeCocycle` — measurability of the generator from continuity of
  the second derivative data (here: from `measurable_fderiv`).
* `ErgodicTheory.det_derivativeCocycle_ne_zero` — invertibility of each `Dₓ T` gives a nonvanishing
  matrix determinant for the generator.
* `ErgodicTheory.oseledets_filtration_derivativeCocycle` — the Oseledets filtration specialized
  to the
  derivative cocycle of an ergodic differentiable map with integrable log-derivative data.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {d : ℕ}

/-- The **derivative (tangent) cocycle generator** of a self-map
`T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)`: the matrix representing the Fréchet
derivative `fderiv ℝ T x`, obtained by transporting `Dₓ T : E →L[ℝ] E` along the inverse of the
star-algebra equivalence `Matrix.toEuclideanCLM`. -/
noncomputable def derivativeCocycle
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ :=
  fun x => (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm (fderiv ℝ T x)

/-- The matrix `derivativeCocycle T x` represents the derivative `fderiv ℝ T x`. -/
@[simp] theorem toEuclideanCLM_derivativeCocycle
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (derivativeCocycle T x) = fderiv ℝ T x :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).apply_symm_apply _

/-- The generator has the same L2 operator norm as the derivative: `‖derivativeCocycle T x‖`
equals `‖fderiv ℝ T x‖`. This is the bridge identifying the matrix integrability hypotheses with
the genuine `log⁺‖Dₓ T‖` ones. -/
theorem norm_derivativeCocycle
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖derivativeCocycle T x‖ = ‖fderiv ℝ T x‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM (derivativeCocycle T x), toEuclideanCLM_derivativeCocycle]

/-- **Chain-rule cocycle identity.** For a differentiable `T`, the matrix
`cocycle (derivativeCocycle T) T n x` represents the derivative of the `n`-th iterate `T^[n]`
at `x`. Proved by induction, peeling the innermost factor `T` from both the cocycle recursion
(`cocycle_succ`) and the iterate (`Function.iterate_succ`, so `T^[n+1] = T^[n] ∘ T`). -/
theorem chainRule_cocycle
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Differentiable ℝ T)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (derivativeCocycle T) T n x) = fderiv ℝ (T^[n]) x := by
  induction n generalizing x with
  | zero =>
    simp only [cocycle_zero, map_one, Function.iterate_zero]
    rw [fderiv_id, ContinuousLinearMap.one_def]
  | succ n ih =>
    rw [cocycle_succ, map_mul, toEuclideanCLM_derivativeCocycle, ih (T x),
      ContinuousLinearMap.mul_def]
    rw [Function.iterate_succ, fderiv_comp x (hT.iterate n (T x)) (hT x)]

/-- The matrix entry `(derivativeCocycle T x) i j` is the `i`-th coordinate of `Dₓ T` applied to
the `j`-th standard basis vector. -/
theorem derivativeCocycle_apply
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (i j : Fin d) :
    derivativeCocycle T x i j =
      WithLp.ofLp ((fderiv ℝ T x) (EuclideanSpace.single j (1 : ℝ))) i := by
  have hcol :
      WithLp.ofLp
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (derivativeCocycle T x)
            (EuclideanSpace.single j (1 : ℝ))) =
        (derivativeCocycle T x).col j := by
    rw [Matrix.ofLp_toEuclideanCLM]
    simp only [PiLp.ofLp_single, Matrix.mulVec_single_one]
  have := congrArg (fun w => w i) hcol
  simpa only [toEuclideanCLM_derivativeCocycle, Matrix.col_apply] using this.symm

/-- **Measurability of the derivative cocycle generator.** Each matrix entry is the
(continuous) coordinate projection of `x ↦ (fderiv ℝ T x) eⱼ`, which is measurable by
`measurable_fderiv_apply_const`. -/
theorem measurable_derivativeCocycle
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Measurable (derivativeCocycle T) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [derivativeCocycle_apply]
  have hfd : Measurable fun x => (fderiv ℝ T x) (EuclideanSpace.single j (1 : ℝ)) :=
    measurable_fderiv_apply_const ℝ T (EuclideanSpace.single j (1 : ℝ))
  have hcoord :
      Continuous fun w : EuclideanSpace ℝ (Fin d) => WithLp.ofLp w i :=
    PiLp.continuous_apply (β := fun _ : Fin d => ℝ) 2 i
  exact hcoord.measurable.comp hfd

/-- If every derivative `Dₓ T` is invertible (as a continuous linear map), then the generator's
determinant never vanishes. Invertibility transfers across the star-algebra equivalence
`toEuclideanCLM`, and a matrix is a unit iff its determinant is. -/
theorem det_derivativeCocycle_ne_zero
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hiso : ∀ x, IsUnit (fderiv ℝ T x)) (x : EuclideanSpace ℝ (Fin d)) :
    (derivativeCocycle T x).det ≠ 0 := by
  have hunit : IsUnit (derivativeCocycle T x) :=
    (hiso x).map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- **Oseledets multiplicative ergodic theorem for the derivative cocycle.** Let `T` be an
ergodic measure-preserving differentiable self-map of `EuclideanSpace ℝ (Fin d)` with everywhere
nonsingular derivative cocycle and integrable log-derivative data
`log⁺‖Dₓ T‖, log⁺‖(Dₓ T)⁻¹‖ ∈ L¹(μ)`. Then there is an `A`-equivariant Lyapunov filtration with
the convergence `(1/n) log‖D(T^[n]) v‖ → λᵢ` along each stratum, for `A := derivativeCocycle T`.

The integrability hypotheses are stated directly for the matrix generator; by
`norm_derivativeCocycle` these are exactly the genuine `log⁺‖fderiv‖` (and inverse) conditions.
The first conjunct records that the cocycle is the genuine tangent cocycle: each factor
`toEuclideanCLM (cocycle (derivativeCocycle T) T n x)` is the derivative `fderiv ℝ (T^[n]) x`. -/
theorem oseledets_filtration_derivativeCocycle
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hT : Ergodic T μ) (hdiff : Differentiable ℝ T)
    (hdet : ∀ x, (derivativeCocycle T x).det ≠ 0)
    (hint : IntegrableLogNorm (derivativeCocycle T) μ)
    (hint' : IntegrableLogNorm (fun x => (derivativeCocycle T x)⁻¹) μ) :
    (∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
        Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (derivativeCocycle T) T n x)
          = fderiv ℝ (T^[n]) x) ∧
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) →
        EuclideanSpace ℝ (Fin d) → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (derivativeCocycle T x)).toLinearMap
            (V i x) = V i (T x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log
                  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle (derivativeCocycle T) T n x) v‖)
              atTop (𝓝 (lam i))) :=
  ⟨fun n x => chainRule_cocycle hdiff n x,
    oseledets_filtration hT (derivativeCocycle T) hdet (measurable_derivativeCocycle T) hint hint'⟩

end ErgodicTheory
