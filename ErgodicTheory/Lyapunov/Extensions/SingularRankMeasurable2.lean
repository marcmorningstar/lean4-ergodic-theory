/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import ErgodicTheory.Lyapunov.Extensions.SingularRankMeasurable

/-!
# Toward the measurable rank flag: the nonsingular-minor lower bound

For the singular (non-invertible) multiplicative ergodic theorem the Oseledets
decomposition degenerates to a **measurable filtration**
`ℝ^d = V₁(x) ⊃ V₂(x) ⊃ ⋯ ⊃ {0}`, whose strata carry the dimension data
(the multiplicities `m_j`) of the flag (A. Quas, *Multiplicative Ergodic Theorems
and Applications*, lecture notes, Universidade de São Paulo, December 2013,
Theorem 2 — the non-invertible Oseledets theorem after Oseledec [12] and
Raghunathan [13]: in the non-invertible case the conclusion is a **measurable**
filtration rather than a direct-sum decomposition). Assembling that measurable
flag requires the *dimension function* `x ↦ cocycleRank A T n x` to be measurable,
which in turn rests on the determinantal characterisation of rank via minors.

`ErgodicTheory.Lyapunov.Extensions.SingularRankMeasurable` supplies the **top stratum**
(full rank `= d ↔ det ≠ 0`) and the determinantal building blocks
(`measurable_minor_det`, `measurableSet_minor_det_ne_zero`). This file proves the
**easy half** of the minor characterisation of rank — the only half that is
elementary from the Mathlib API.

## The minor characterisation of rank

For `M : Matrix (Fin d) (Fin d) R` over a field and `r : ℕ`, classically
`r ≤ M.rank` **iff** some `r × r` minor of `M` is nonsingular, i.e. there exist
`s t : Fin r → Fin d` with `(M.submatrix s t).det ≠ 0`.

* The **easy direction** `(⇐)` — a nonsingular `r × r` minor forces `r ≤ M.rank` —
  is `Matrix.le_rank_of_submatrix_det_ne_zero` below: the `r × r` minor has full
  rank `r` by `Matrix.rank_eq_card_iff_det_ne_zero`, and `Matrix.rank_submatrix_le`
  says a submatrix's rank never exceeds the parent's, so `r ≤ M.rank`.
* The **hard direction** `(⇒)` — `r ≤ M.rank` produces a nonsingular `r × r` minor —
  is the classical theorem (choose `r` independent columns, then `r` independent
  rows among them); it is **not** elementary from the Mathlib API and is proved
  downstream in `ErgodicTheory.Lyapunov.Extensions.SingularRankMinor`
  (`Matrix.exists_submatrix_det_ne_zero_of_le_rank`), which consumes the easy
  direction proved here to complete the full characterisation
  (`Matrix.le_rank_iff_exists_submatrix_det_ne_zero`) and, from it, the
  measurability of the cocycle-rank dimension function
  (`ErgodicTheory.measurableSet_le_cocycleRank`, `ErgodicTheory.measurable_cocycleRank`).

## Main result

* `Matrix.le_rank_of_submatrix_det_ne_zero`: a nonsingular `r × r` minor forces
  `r ≤ M.rank` (the easy half of the minor characterisation of rank).
-/

namespace Matrix

variable {n R : Type*} [Fintype n] [Field R]

/-- **Nonsingular-minor lower bound on rank** (the easy half of the minor
characterisation of rank). If the `r × r` minor of `M` selected by `s, t` has
nonzero determinant, then `r ≤ M.rank`.

The minor `M.submatrix s t` is a square matrix over `Fin r`; a nonzero determinant
makes it full rank `r` (`rank_eq_card_iff_det_ne_zero`, with `Fintype.card_fin`),
and a submatrix never has larger rank than its parent (`rank_submatrix_le`), so
`r = (M.submatrix s t).rank ≤ M.rank`. (No injectivity of `s, t` is needed: a
repeated index would force a zero determinant, so the hypothesis already rules it
out.) The converse — `r ≤ M.rank` yields such a minor — is the classical hard
direction, not available in Mathlib. -/
theorem le_rank_of_submatrix_det_ne_zero {r : ℕ} (M : Matrix n n R)
    (s t : Fin r → n) (h : (M.submatrix s t).det ≠ 0) :
    r ≤ M.rank := by
  have hfull : (M.submatrix s t).rank = r := by
    have hc := (rank_eq_card_iff_det_ne_zero (M.submatrix s t)).2 h
    rwa [Fintype.card_fin] at hc
  calc r = (M.submatrix s t).rank := hfull.symm
    _ ≤ M.rank := rank_submatrix_le M s t

end Matrix
