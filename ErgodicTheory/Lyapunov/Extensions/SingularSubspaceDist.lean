/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import ErgodicTheory.Lyapunov.OseledetsLimit.BandProjector

/-!
# Subspace convergence via orthogonal-projector distances

A measurably-varying family of subspaces of `EuclideanSpace ℝ (Fin d)` is encoded in this
formalization by the matrix of its orthogonal projection, `ErgodicTheory.orthProjMatrix`
(`ErgodicTheory.Lyapunov.MeasurableSubspace`). This module turns the abstract
finite-dimensional-completeness `CauchySeq` machinery of
`ErgodicTheory.cauchySeq_of_summable_norm_sub`
(`ErgodicTheory.Lyapunov.OseledetsLimit.BandProjector`)
into a **subspace-convergence tool** keyed on the differences of those orthogonal-projection
matrices.

The metric we attach to a pair of subspaces is the operator-norm distance between their
orthogonal projectors, `‖orthProjMatrix U - orthProjMatrix V‖`,
which is the standard gap (aperture) distance on the Grassmannian. A sequence of subspaces
whose consecutive projector gaps are summable then has a convergent projector sequence, and the
limit is again an orthogonal projector — self-adjoint and idempotent. This is exactly the soft
analysis needed to extract a limiting flag space from a Cauchy sequence of finite-step subspaces
(e.g. the eventual-kernel / Oseledets filtration constructions for singular cocycles).

## Main results

* `ErgodicTheory.cauchySeq_of_summable_subspaceDist`: summable consecutive projector gaps give a
  Cauchy projector sequence.
* `ErgodicTheory.exists_tendsto_orthProjMatrix_of_summable`: such a sequence converges
  to a matrix `P`
  that is self-adjoint and idempotent (`P * P = P`) — an orthogonal projector.
-/

open scoped Matrix.Norms.L2Operator

open Filter Topology

namespace ErgodicTheory

variable {d : ℕ}

/-- **Self-adjointness of the orthogonal-projection matrix.** `orthProjMatrix K` is the image of
the (self-adjoint) orthogonal projection `K.starProjection` under the star algebra equivalence
`(Matrix.toEuclideanCLM).symm`, hence self-adjoint. -/
theorem isSelfAdjoint_orthProjMatrix (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    [K.HasOrthogonalProjection] : IsSelfAdjoint (orthProjMatrix K) := by
  rw [orthProjMatrix]
  exact (isSelfAdjoint_starProjection K).map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm

/-- **Idempotence of the orthogonal-projection matrix.** `orthProjMatrix K` is the image of the
idempotent orthogonal projection `K.starProjection` under the (multiplicative) star algebra
equivalence `(Matrix.toEuclideanCLM).symm`, hence idempotent. -/
theorem isIdempotentElem_orthProjMatrix (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    [K.HasOrthogonalProjection] : orthProjMatrix K * orthProjMatrix K = orthProjMatrix K := by
  have hinj : Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).injective
  apply hinj
  rw [map_mul, orthProjMatrix, StarAlgEquiv.apply_symm_apply]
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.mul_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v)

/-- **Cauchy from summable gaps.** If the consecutive projector gaps
`‖orthProjMatrix (V (n+1)) - orthProjMatrix (V n)‖` of a sequence of subspaces are summable, then
the projector sequence `n ↦ orthProjMatrix (V n)` is Cauchy in the (L2 operator) matrix metric.
This is pure soft analysis: matrices over `ℝ` form a finite-dimensional, hence complete, normed
space. -/
theorem cauchySeq_of_summable_subspaceDist
    {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin d))} [∀ n, (V n).HasOrthogonalProjection]
    (hsum : Summable (fun n => ‖orthProjMatrix (V (n + 1)) - orthProjMatrix (V n)‖)) :
    CauchySeq (fun n => orthProjMatrix (V n)) :=
  cauchySeq_of_summable_norm_sub hsum

/-- **Convergence to an orthogonal projector.** If the consecutive projector gaps of a sequence of
subspaces are summable, then `n ↦ orthProjMatrix (V n)` converges to some matrix `P`, and the
limit is again an orthogonal projector: it is self-adjoint and idempotent (`P * P = P`).

Self-adjointness passes to the limit because the entrywise Hermitian relation
`orthProjMatrix (V n) j i = orthProjMatrix (V n) i j` is closed under the (finite-dimensional)
matrix limit; idempotence passes to the limit because matrix multiplication is continuous in the
L2 operator norm and each term satisfies `orthProjMatrix_idem`. -/
theorem exists_tendsto_orthProjMatrix_of_summable
    {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin d))} [∀ n, (V n).HasOrthogonalProjection]
    (hsum : Summable (fun n => ‖orthProjMatrix (V (n + 1)) - orthProjMatrix (V n)‖)) :
    ∃ P, Tendsto (fun n => orthProjMatrix (V n)) atTop (𝓝 P) ∧ IsSelfAdjoint P ∧ P * P = P := by
  obtain ⟨P, hP⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_summable_subspaceDist hsum)
  refine ⟨P, hP, ?_, ?_⟩
  · -- Self-adjointness as an entrywise (Hermitian) limit, mirroring `oseledetsLimit_isSelfAdjoint`.
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    refine Matrix.IsHermitian.ext fun i j => ?_
    have hcij : Tendsto (fun n : ℕ => orthProjMatrix (V n) i j) atTop (𝓝 (P i j)) :=
      ((continuous_matrix_entry i j).tendsto _).comp hP
    have hcji : Tendsto (fun n : ℕ => orthProjMatrix (V n) j i) atTop (𝓝 (P j i)) :=
      ((continuous_matrix_entry j i).tendsto _).comp hP
    have heq : ∀ n : ℕ, orthProjMatrix (V n) i j = orthProjMatrix (V n) j i := fun n => by
      have hH := isSelfAdjoint_orthProjMatrix (V n)
      rw [← Matrix.isHermitian_iff_isSelfAdjoint] at hH
      simpa using (hH.apply i j).symm
    have hval : P j i = P i j := tendsto_nhds_unique hcji (hcij.congr heq)
    simpa using hval
  · -- Idempotence by continuity of matrix multiplication and `orthProjMatrix_idem`.
    have hmul : Tendsto (fun n : ℕ => orthProjMatrix (V n) * orthProjMatrix (V n)) atTop
        (𝓝 (P * P)) := (hP.mul hP)
    have hself : Tendsto (fun n : ℕ => orthProjMatrix (V n) * orthProjMatrix (V n)) atTop
        (𝓝 P) := by
      refine hP.congr (fun n => ?_)
      exact (isIdempotentElem_orthProjMatrix (V n)).symm
    exact tendsto_nhds_unique hmul hself

end ErgodicTheory
