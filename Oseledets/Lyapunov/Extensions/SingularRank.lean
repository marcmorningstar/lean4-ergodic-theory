/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Oseledets.Cocycle.Basic

/-!
# Rank of a linear cocycle and its drop along the dynamics

For a non-invertible cocycle the Oseledets decomposition degenerates to a
*filtration* whose strata can lose dimension as the cocycle composes: the matrix
products `cocycle A T n x` may have strictly decreasing rank in `n`. This file
records that rank as the function `Oseledets.cocycleRank`, together with the basic
dimension bounds and the headline **rank-drop monotonicity**: the rank of an
`(m + n)`-step cocycle is bounded by the rank of each of its two composing factors,
so it can only fall as the orbit advances. This is the dimension data underlying the
singular (non-invertible) multiplicative ergodic theorem.

Literature source: A. Quas, *Multiplicative Ergodic Theorems and Applications*
(lecture notes, Universidade de São Paulo, 2013), Theorem 2 (Oseledets theorem,
non-invertible form, after Oseledec [12] and Raghunathan [13]): in the
non-invertible case the conclusion is a filtration `ℝ^d = V₁ ⊃ V₂ ⊃ ⋯ ⊃ {0}` rather
than a direct-sum decomposition, and the `cocycle`-rank measures the number of
directions not yet collapsed by the matrix products.

## Main definitions

* `Oseledets.cocycleRank`: the rank `(cocycle A T n x).rank` of the `n`-step cocycle —
  the number of non-collapsed directions after `n` steps.

## Main results

* `Oseledets.cocycleRank_le`: `cocycleRank A T n x ≤ d` (rank is bounded by the
  ambient dimension).
* `Oseledets.cocycleRank_zero`: `cocycleRank A T 0 x = d` (the zero-step cocycle is the
  identity, of full rank).
* `Oseledets.cocycleRank_add_le_left` / `..._right` / `..._min`: the rank-drop
  monotonicity `cocycleRank A T (m + n) x ≤ cocycleRank A T m (T^[n] x)` and
  `≤ cocycleRank A T n x`, hence `≤ min` of the two — the rank is non-increasing as the
  cocycle composes along the orbit.
-/

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- The **rank of the `n`-step cocycle**: the dimension of the image of
`cocycle A T n x`, i.e. the number of directions in `ℝ^d` not yet collapsed after `n`
steps of the cocycle. In the non-invertible Oseledets theorem (Quas, *Multiplicative
Ergodic Theorems and Applications*, 2013, Theorem 2; after Oseledec and Raghunathan)
this rank can strictly drop along the dynamics, producing the singular filtration
rather than a direct-sum decomposition. -/
noncomputable def cocycleRank (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) : ℕ :=
  (cocycle A T n x).rank

/-- The cocycle rank is bounded by the ambient dimension `d`. -/
theorem cocycleRank_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    cocycleRank A T n x ≤ d :=
  Matrix.rank_le_width _

/-- The zero-step cocycle is the identity, so it has full rank `d`. -/
@[simp] theorem cocycleRank_zero (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    cocycleRank A T 0 x = d := by
  rw [cocycleRank, cocycle_zero, Matrix.rank_one, Fintype.card_fin]

/-- **Rank drop, future factor.** The rank of the `(m + n)`-step cocycle is bounded by
the rank of its left factor `cocycle A T m (T^[n] x)`: the rank cannot increase past the
later block. -/
theorem cocycleRank_add_le_left (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (m n : ℕ) (x : X) :
    cocycleRank A T (m + n) x ≤ cocycleRank A T m (T^[n] x) := by
  rw [cocycleRank, cocycleRank, cocycle_add]
  exact Matrix.rank_mul_le_left _ _

/-- **Rank drop, past factor.** The rank of the `(m + n)`-step cocycle is bounded by the
rank of its right factor `cocycle A T n x`: the rank cannot exceed that of the earlier
block, so it is non-increasing as the cocycle composes. -/
theorem cocycleRank_add_le_right (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (m n : ℕ) (x : X) :
    cocycleRank A T (m + n) x ≤ cocycleRank A T n x := by
  rw [cocycleRank, cocycleRank, cocycle_add]
  exact Matrix.rank_mul_le_right _ _

/-- **Rank-drop monotonicity (combined).** The rank of the `(m + n)`-step cocycle is at
most the minimum of the ranks of its two composing factors. This is the dimension drop
of the singular filtration: as the cocycle composes along the orbit its rank can only
fall. -/
theorem cocycleRank_add_le_min (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (m n : ℕ) (x : X) :
    cocycleRank A T (m + n) x ≤
      min (cocycleRank A T m (T^[n] x)) (cocycleRank A T n x) :=
  le_min (cocycleRank_add_le_left A T m n x) (cocycleRank_add_le_right A T m n x)

end Oseledets
