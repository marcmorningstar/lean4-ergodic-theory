/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Oseledets.Lyapunov.Extensions.SingularRankMeasurable

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

`Oseledets.Lyapunov.Extensions.SingularRankMeasurable` supplies the **top stratum**
(full rank `= d ↔ det ≠ 0`) and the determinantal building blocks
(`measurable_minor_det`, `measurableSet_minor_det_ne_zero`). This file continues
toward the general dimension function by proving the **easy half** of the minor
characterisation of rank — the only half that is elementary from the Mathlib API —
and recording precisely the classical direction that is still missing.

## The minor characterisation of rank

For `M : Matrix (Fin d) (Fin d) R` over a field and `r : ℕ`, classically
`r ≤ M.rank` **iff** some `r × r` minor of `M` is nonsingular, i.e. there exist
`s t : Fin r → Fin d` with `(M.submatrix s t).det ≠ 0`.

* The **easy direction** `(⇐)` — a nonsingular `r × r` minor forces `r ≤ M.rank` —
  is `Matrix.le_rank_of_submatrix_det_ne_zero` below: the `r × r` minor has full
  rank `r` by `Matrix.rank_eq_card_iff_det_ne_zero`, and `Matrix.rank_submatrix_le`
  says a submatrix's rank never exceeds the parent's, so `r ≤ M.rank`.
* The **hard direction** `(⇒)` — `r ≤ M.rank` produces a nonsingular `r × r` minor
  — is the classical theorem (choose `r` independent columns, then `r` independent
  rows among them); it is **not** in Mathlib and is *not* proved here.

## Consequence for measurability

The easy direction gives one inclusion of the level set of the cocycle rank:
`Matrix.measurableSet_le_cocycleRank_superset` exhibits the finite union of the
nonsingular-`r`-minor sets (each measurable, by `measurableSet_minor_det_ne_zero`)
as a **subset** of `{x | r ≤ cocycleRank A T n x}`. Equality of these two sets —
which is what `MeasurableSet {x | r ≤ cocycleRank A T n x}` needs — requires the
hard direction above. See the closing **Remaining gap** note.

## Main results

* `Matrix.le_rank_of_submatrix_det_ne_zero`: a nonsingular `r × r` minor forces
  `r ≤ M.rank` (the easy half of the minor characterisation of rank).
* `Oseledets.le_cocycleRank_of_minor_det_ne_zero`: the cocycle version — a
  nonsingular `r × r` minor of `cocycle A T n x` forces `r ≤ cocycleRank A T n x`.
* `Oseledets.measurableSet_minors_subset_le_cocycleRank`: the union of the
  nonsingular-`r`-minor sets is a measurable subset of `{x | r ≤ cocycleRank …}`.

## Remaining gap

The reverse inclusion `{x | r ≤ cocycleRank A T n x} ⊆ ⋃ (s t), {minor s t ≠ 0}`
is exactly the classical "rank `≥ r ⇒` some nonsingular `r`-minor" statement, the
Matrix-infrastructure lemma still absent from Mathlib. Supplying it would upgrade
the subset above to a set **equality**, yielding `MeasurableSet {x | r ≤ rank}`,
then (by differencing successive level sets) `Measurable (cocycleRank A T n)`, and
finally measurability of the eventual-kernel dimension `d - ⨅ n, cocycleRank A T n x`
— the dimension datum of the projection-valued / Grassmannian measurable flag.
-/

open MeasureTheory

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

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- **Cocycle nonsingular-minor lower bound.** If some `r × r` minor of the
`n`-step cocycle `cocycle A T n x` has nonzero determinant, then the cocycle rank
at `x` is at least `r`. This is the cocycle instance of the easy half of the minor
characterisation of rank (`Matrix.le_rank_of_submatrix_det_ne_zero`); it provides
the lower-bound inclusion of the rank level set used below. -/
theorem le_cocycleRank_of_minor_det_ne_zero {r : ℕ}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    (s t : Fin r → Fin d) (h : ((cocycle A T n x).submatrix s t).det ≠ 0) :
    r ≤ cocycleRank A T n x :=
  Matrix.le_rank_of_submatrix_det_ne_zero (cocycle A T n x) s t h

/-- **The minor union is a measurable subset of the rank level set.** The finite
union over all minor selections `s, t : Fin r → Fin d` of the measurable sets
`{x | (cocycle A T n x).submatrix s t).det ≠ 0}` is contained in
`{x | r ≤ cocycleRank A T n x}`, and is itself measurable (a finite union of the
measurable nonsingular-minor sets, `measurableSet_minor_det_ne_zero`).

This is the **lower-bound (`⊇`) inclusion** of the rank level set supplied by the
easy direction of the minor characterisation of rank. Promoting it to an equality
— hence to `MeasurableSet {x | r ≤ cocycleRank …}` — needs the classical converse
"rank `≥ r ⇒` nonsingular `r`-minor", which Mathlib lacks; see the module's
*Remaining gap*. -/
theorem measurableSet_minors_subset_le_cocycleRank [MeasurableSpace X] {r : ℕ}
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X}
    (hT : Measurable T) (n : ℕ) :
    (⋃ s : Fin r → Fin d, ⋃ t : Fin r → Fin d,
        {x | ((cocycle A T n x).submatrix s t).det ≠ 0})
      ⊆ {x | r ≤ cocycleRank A T n x}
    ∧ MeasurableSet (⋃ s : Fin r → Fin d, ⋃ t : Fin r → Fin d,
        {x | ((cocycle A T n x).submatrix s t).det ≠ 0}) := by
  constructor
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨s, t, hst⟩ := hx
    exact le_cocycleRank_of_minor_det_ne_zero A T n x s t hst
  · have hcoc : Measurable (fun x => cocycle A T n x) := measurable_cocycle hA hT n
    refine MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun t => ?_
    exact measurableSet_minor_det_ne_zero hcoc s t

end Oseledets
