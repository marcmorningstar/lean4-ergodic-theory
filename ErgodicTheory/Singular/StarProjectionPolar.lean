/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Polarisation of the orthogonal projector onto a subspace

For a finite-dimensional real inner-product space `EuclideanSpace ℝ (Fin d)` and a subspace
`K`, this module records the **polarisation identity for the orthogonal projector**
`K.starProjection`, expressing every coordinate of a projected vector as a fixed real-arithmetic
combination of the scalar distance-to-subspace maps `c ↦ infDist c K`.

Writing `P := K.starProjection` for the orthogonal projection onto `K` (every subspace of a
finite-dimensional space is complete, hence has an orthogonal projection) and `e_a` for the
standard basis vector `EuclideanSpace.single a 1`, self-adjointness and idempotency of `P` give
`⟪e_b, P e_a⟫ = ⟪P e_b, P e_a⟫`, so every coordinate of `P e_a` is an inner product of two
projections. The polarisation identity expands such an inner product into a combination of the
squared norms `‖P c‖²`, and Pythagoras gives
`‖P c‖² = ‖c‖² − infDist c K²`
(`c = P c + (c − P c)` is an orthogonal decomposition and `infDist c K` realises `‖c − P c‖`).
Hence **every coordinate of every projected vector `P c` is a real-arithmetic combination of the
scalar distance maps `infDist · K`**.

This algebraic core is the `sorry`-free heart of the singular ("issue #6") measurable-projector
converter: composed with the measurability of the distance maps it makes the orthogonal projector
of a measurably-varying subspace family (a.e.) measurable.

## Main results

* `ErgodicTheory.infDist_eq_norm_sub_starProjection`: `infDist c K = ‖c − K.starProjection c‖`.
* `ErgodicTheory.norm_starProjection_sq`: Pythagoras, `‖K.starProjection c‖² = ‖c‖² − infDist c K²`.
* `ErgodicTheory.starProjection_apply_coord`: the projector-coordinate polarisation identity,
  writing `(K.starProjection u) b` as a real combination of three squared-norm–minus–`infDist²`
  terms.

Literature: Kuratowski–Ryll-Nardzewski, *A general theorem on selectors* (1965); Castaing–Valadier,
*Convex Analysis and Measurable Multifunctions*; C. González-Tokman, A. Quas, *A semi-invertible
operator Oseledets theorem* (ETDS 2014), Appendix B.
-/

open Metric Submodule

namespace ErgodicTheory

variable {d : ℕ} (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))

/-- **Distance to a subspace is the norm of the projection residual.** For a closed (here:
finite-dimensional, hence complete) subspace `K`, `infDist c K = ‖c − K.starProjection c‖`. The
orthogonal projection realises the infimum `⨅ x : K, ‖c − x‖` (`starProjection_minimal`), and
`infDist` is exactly that infimum (`infDist_eq_iInf`, with `dist = ‖· − ·‖`). -/
theorem infDist_eq_norm_sub_starProjection (c : EuclideanSpace ℝ (Fin d)) :
    infDist c (K : Set (EuclideanSpace ℝ (Fin d))) = ‖c - K.starProjection c‖ := by
  rw [starProjection_minimal, infDist_eq_iInf]
  simp_rw [dist_eq_norm]
  rfl

/-- **Pythagoras for the projector.** `‖K.starProjection c‖² = ‖c‖² − infDist c K ²`. The
orthogonal decomposition `c = K.starProjection c + (c − K.starProjection c)` has orthogonal
summands, so `‖c‖² = ‖K.starProjection c‖² + ‖c − K.starProjection c‖²`, and the residual norm
is `infDist c K` by `infDist_eq_norm_sub_starProjection`. -/
theorem norm_starProjection_sq (c : EuclideanSpace ℝ (Fin d)) :
    ‖K.starProjection c‖ ^ 2
      = ‖c‖ ^ 2 - infDist c (K : Set (EuclideanSpace ℝ (Fin d))) ^ 2 := by
  have horth : inner ℝ (K.starProjection c) (c - K.starProjection c) = (0 : ℝ) := by
    rw [real_inner_comm]
    exact K.starProjection_inner_eq_zero c (K.starProjection c) (K.starProjection_apply_mem c)
  have hsplit : c = K.starProjection c + (c - K.starProjection c) := by abel
  have hpyth : ‖c‖ ^ 2 = ‖K.starProjection c‖ ^ 2 + ‖c - K.starProjection c‖ ^ 2 := by
    have hcc : ‖c‖ ^ 2 = ‖K.starProjection c + (c - K.starProjection c)‖ ^ 2 := by
      rw [← hsplit]
    rw [hcc, ← real_inner_self_eq_norm_sq, inner_add_add_self, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, horth, real_inner_comm, horth]
    ring
  rw [infDist_eq_norm_sub_starProjection]; linarith

/-- **A projector coordinate is a distance combination.** The `b`-th coordinate of the projected
vector `K.starProjection u` equals
`½[(‖single b‖² − infDist (single b) K²) + (‖u‖² − infDist u K²) −
   (‖single b − u‖² − infDist (single b − u) K²)]`.
Self-adjointness and idempotency give `(K.starProjection u) b = ⟪K.starProjection (single b),
K.starProjection u⟫`; polarisation expands the inner product into squared norms of projections;
each squared norm is `‖·‖² − infDist · K²` by `norm_starProjection_sq` (with
`K.starProjection (single b) − K.starProjection u = K.starProjection (single b − u)`). -/
theorem starProjection_apply_coord (u : EuclideanSpace ℝ (Fin d)) (b : Fin d) :
    (K.starProjection u) b
      = ((‖(EuclideanSpace.single b (1 : ℝ))‖ ^ 2
            - infDist (EuclideanSpace.single b (1 : ℝ)) (K : Set _) ^ 2)
          + (‖u‖ ^ 2 - infDist u (K : Set _) ^ 2)
          - (‖(EuclideanSpace.single b (1 : ℝ)) - u‖ ^ 2
            - infDist ((EuclideanSpace.single b (1 : ℝ)) - u) (K : Set _) ^ 2)) / 2 := by
  set s : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single b (1 : ℝ) with hs
  -- Coordinate as an inner product of projections (self-adjoint + idempotent).
  have hcoord : (K.starProjection u) b
      = inner ℝ (K.starProjection s) (K.starProjection u) := by
    rw [inner_starProjection_left_eq_right,
      starProjection_eq_self_iff.mpr (K.starProjection_apply_mem u), hs,
      EuclideanSpace.inner_single_left]
    simp
  -- Polarisation of the real inner product.
  have hpolar : inner ℝ (K.starProjection s) (K.starProjection u)
      = (‖K.starProjection s‖ ^ 2 + ‖K.starProjection u‖ ^ 2
          - ‖K.starProjection s - K.starProjection u‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]; ring
  rw [hcoord, hpolar, ← map_sub, norm_starProjection_sq, norm_starProjection_sq,
    norm_starProjection_sq]

end ErgodicTheory
