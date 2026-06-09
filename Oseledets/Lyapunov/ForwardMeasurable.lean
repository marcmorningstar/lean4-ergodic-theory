import Oseledets.Lyapunov.Measurable

/-!
# The projector/range bridge for `MeasurableSubspace`

This module connects a **self-adjoint idempotent matrix** `P` to the
`MeasurableSubspace` notion of `Oseledets/Lyapunov/MeasurableSubspace.lean`.

The key observation is purely linear-algebraic: if `P` is self-adjoint (`Pᵀ = P`,
i.e. `IsSelfAdjoint P`) and idempotent (`P * P = P`), then the continuous linear map
`toEuclideanCLM P` is a *star projection* (self-adjoint idempotent operator), hence equals
the orthogonal projection `starProjection` onto its own range. Translating back through the
`toEuclideanCLM` star-algebra equivalence shows `orthProjMatrix (range (toEuclideanCLM P)) = P`.

Consequently a measurable family of self-adjoint idempotent matrices induces a
`MeasurableSubspace` family of range subspaces — the form consumed downstream by the spectral
(CFC) construction of the Oseledets flag projections.

## Main results

* `orthProjMatrix_range_toEuclideanCLM` — Deliverable A, the projector/range bridge.
* `measurableSubspace_range_of_measurable` — Deliverable B, measurability of the range family.

The crux uses the Mathlib lemma
`ContinuousLinearMap.isStarProjection_iff_eq_starProjection_range`
(a star projection equals the orthogonal projection onto its range).
-/

open scoped Matrix

namespace Oseledets

variable {d : ℕ}

/-- For a self-adjoint idempotent matrix `P` (`IsSelfAdjoint P`, `P * P = P`), the orthogonal
projection onto the range of `toEuclideanCLM P` is `toEuclideanCLM P` itself, so
`orthProjMatrix (range …) = P`. -/
theorem orthProjMatrix_range_toEuclideanCLM
    (P : Matrix (Fin d) (Fin d) ℝ) (hsa : IsSelfAdjoint P) (hidem : P * P = P) :
    orthProjMatrix (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) P).toLinearMap) = P := by
  set E := EuclideanSpace ℝ (Fin d)
  -- The continuous linear map associated to `P`.
  set L : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) P with hL
  -- `L` is a star projection: self-adjoint and idempotent, transported through the
  -- star-algebra equivalence `toEuclideanCLM`.
  have hLsa : IsSelfAdjoint L := hsa.map (Matrix.toEuclideanCLM (𝕜 := ℝ))
  have hLidem : IsIdempotentElem L := by
    have : L * L = L := by
      rw [hL, ← map_mul, hidem]
    exact this
  have hsp : IsStarProjection L := ⟨hLidem, hLsa⟩
  -- A star projection equals the orthogonal projection onto its own range.
  obtain ⟨_, hLeq⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp hsp
  -- `L.range` (as a `ContinuousLinearMap`) is the same submodule as
  -- `LinearMap.range L.toLinearMap`.
  have hrange : (L.range) = LinearMap.range L.toLinearMap := rfl
  -- Unfold `orthProjMatrix` and rewrite the projection as `L`.
  rw [orthProjMatrix, ← hrange, ← hLeq, hL, StarAlgEquiv.symm_apply_apply]

variable {X : Type*} [MeasurableSpace X]

/-- If `x ↦ P x` is a measurable family of self-adjoint idempotent matrices, the range subspaces
form a `MeasurableSubspace`. -/
theorem measurableSubspace_range_of_measurable
    (P : X → Matrix (Fin d) (Fin d) ℝ) (hP : Measurable P)
    (hsa : ∀ x, IsSelfAdjoint (P x)) (hidem : ∀ x, P x * P x = P x) :
    MeasurableSubspace
      (fun x => LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (P x)).toLinearMap) := by
  unfold MeasurableSubspace
  have heq : (fun x => orthProjMatrix
      (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (P x)).toLinearMap)) = P := by
    funext x
    exact orthProjMatrix_range_toEuclideanCLM (P x) (hsa x) (hidem x)
  rw [heq]
  exact hP

end Oseledets
