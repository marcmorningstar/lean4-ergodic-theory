/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finite
import ErgodicTheory.Lyapunov.Extensions.SingularRankMeasurable2

/-!
# The nonsingular-minor characterisation of rank, and the measurable rank flag

For the singular (non-invertible) multiplicative ergodic theorem the Oseledets
decomposition degenerates to a **measurable filtration**
`ℝ^d = V₁(x) ⊃ V₂(x) ⊃ ⋯ ⊃ {0}`, whose strata carry the dimension data (the
multiplicities `m_j`) of the flag (A. Quas, *Multiplicative Ergodic Theorems and
Applications*, lecture notes, Universidade de São Paulo, December 2013, Theorem 2 —
the non-invertible Oseledets theorem after Oseledec [12] and Raghunathan [13]: in
the non-invertible case the conclusion is a **measurable** filtration rather than a
direct-sum decomposition). Assembling that measurable flag requires the *dimension
function* `x ↦ cocycleRank A T n x` to be measurable, which rests on the
determinantal characterisation of rank via minors.

`ErgodicTheory.Lyapunov.Extensions.SingularRankMeasurable2` supplied the **easy half** of
that characterisation — a nonsingular `r × r` minor forces `r ≤ M.rank`
(`Matrix.le_rank_of_submatrix_det_ne_zero`) — and exhibited the union of the
nonsingular-minor sets as a measurable **subset** of `{x | r ≤ cocycleRank A T n x}`.

This file proves the **classical hard half**, absent from Mathlib:

> `r ≤ M.rank ⇒ ∃ s t : Fin r → n, (M.submatrix s t).det ≠ 0`,

i.e. a matrix of rank at least `r` has a nonsingular `r × r` minor. Combined with
the easy half it gives the full minor characterisation
`r ≤ M.rank ↔ ∃ s t, (M.submatrix s t).det ≠ 0`, which upgrades the subset above to a
set **equality**, yielding `MeasurableSet {x | r ≤ cocycleRank A T n x}`, then the
measurability of the dimension function `cocycleRank A T n` and of the
eventual-kernel dimension `x ↦ d - ⨅ n, cocycleRank A T n x` — the dimension datum of
the measurable flag.

## The classical proof of the hard half

The standard linear-algebra argument (chosen here because every step is supported by
the Mathlib API):

1. `M.rank` is the dimension of the **column span** (`rank_eq_finrank_span_cols`); from
   a finite family whose span has dimension `≥ r` one can select an injective family of
   `r` indices on which the family is linearly independent
   (`Matrix.exists_submatrix_id_rank_eq`, built from `exists_linearIndependent'` and
   `finrank_span_eq_card`). This produces `t : Fin r → n` with the tall `m × r`
   submatrix `M.submatrix id t` of rank `r`.
2. Applying the same column selection to the **transpose** of that tall submatrix
   selects `r` independent rows, giving `s : Fin r → m` so that the square
   `r × r` minor `M.submatrix s t` again has rank `r`.
3. A square matrix of full rank has nonzero determinant
   (`Matrix.rank_eq_card_iff_det_ne_zero`).

## Main results

* `Matrix.exists_submatrix_id_rank_eq`: rank `≥ r` selects `t : Fin r → n` with the
  tall column-submatrix `M.submatrix id t` of rank exactly `r`.
* `Matrix.exists_submatrix_det_ne_zero_of_le_rank`: **the missing lemma** — rank `≥ r`
  yields a nonsingular `r × r` minor.
* `Matrix.le_rank_iff_exists_submatrix_det_ne_zero`: the full minor characterisation
  of rank (both directions).
* `ErgodicTheory.measurableSet_le_cocycleRank`: `{x | r ≤ cocycleRank A T n x}` is
  measurable.
* `ErgodicTheory.measurable_cocycleRank`: the cocycle-rank dimension function is
  measurable.
-/

open MeasureTheory Module

namespace Matrix

variable {m n R : Type*} [Field R]

/-- **Column selection from a rank bound.** If `r ≤ M.rank` then there is an injective
selection `t : Fin r → n` of `r` columns of `M` whose tall `m × r` submatrix
`M.submatrix id t` has rank exactly `r`.

Proof: `M.rank` equals the dimension of the column span (`rank_eq_finrank_span_cols`).
From the column family `M.col : n → (m → R)`, `exists_linearIndependent'` selects an
injective `a : κ → n` indexing a linearly independent subfamily with the same span,
hence (`finrank_span_eq_card`) `Fintype.card κ = M.rank ≥ r`; choosing an injection
`Fin r ↪ κ` and composing gives `t`. The columns of `M.submatrix id t` are exactly
`M.col ∘ t`, a linearly independent `Fin r`-family, so the submatrix's rank is `r`. -/
theorem exists_submatrix_id_rank_eq [Finite m] [Fintype n] {r : ℕ}
    (M : Matrix m n R) (hr : r ≤ M.rank) :
    ∃ t : Fin r → n, (M.submatrix id t).rank = r := by
  classical
  letI := Fintype.ofFinite m
  obtain ⟨κ, a, ha_inj, hspan, hli⟩ := exists_linearIndependent' R M.col
  -- `κ` is finite: `a : κ → n` is injective into the finite `n`.
  have : Finite κ := Finite.of_injective a ha_inj
  cases nonempty_fintype κ
  -- The selected columns are independent, so their span has dimension `card κ`.
  have hcard : Fintype.card κ = M.rank := by
    have h1 : finrank R (Submodule.span R (Set.range (M.col ∘ a))) = Fintype.card κ :=
      finrank_span_eq_card hli
    rw [hspan, ← rank_eq_finrank_span_cols] at h1
    exact h1.symm
  have hrκ : r ≤ Fintype.card κ := hcard ▸ hr
  -- Pick an injective `Fin r → κ` from a `Fin r ↪ κ` embedding.
  obtain ⟨e⟩ : Nonempty (Fin r ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hrκ)
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent R (M.col ∘ (a ∘ ⇑e)) := by
    have : LinearIndependent R ((M.col ∘ a) ∘ ⇑e) := hli.comp e e.injective
    simpa [Function.comp_assoc] using this
  -- The columns of the tall submatrix are exactly `M.col ∘ (a ∘ e)`.
  have hcol : (M.submatrix id (a ∘ e)).col = M.col ∘ (a ∘ e) := by
    funext k; funext i; rfl
  rw [rank_eq_finrank_span_cols, hcol, finrank_span_eq_card hli', Fintype.card_fin]

/-- **The missing nonsingular-minor lemma** (classical hard half of the minor
characterisation of rank). If `r ≤ M.rank`, then some `r × r` minor of `M` is
nonsingular: there exist `s t : Fin r → n` with `(M.submatrix s t).det ≠ 0`.

Proof. First select `r` independent columns: `exists_submatrix_id_rank_eq` gives
`t : Fin r → n` with the tall submatrix `N := M.submatrix id t` of rank `r`. The
transpose `Nᵀ` has the same rank `r` (`rank_transpose`); selecting `r` independent
columns of `Nᵀ` (again `exists_submatrix_id_rank_eq`) gives `s : Fin r → m` with
`(Nᵀ.submatrix id s).rank = r`. That selection is the square minor `M.submatrix s t`
up to transpose, and a square matrix of full rank has nonzero determinant
(`rank_eq_card_iff_det_ne_zero`). The converse — a nonsingular minor forcing
`r ≤ M.rank` — is `Matrix.le_rank_of_submatrix_det_ne_zero`. -/
theorem exists_submatrix_det_ne_zero_of_le_rank [Finite m] [Fintype n] {r : ℕ}
    (M : Matrix m n R) (hr : r ≤ M.rank) :
    ∃ s : Fin r → m, ∃ t : Fin r → n, (M.submatrix s t).det ≠ 0 := by
  classical
  letI := Fintype.ofFinite m
  obtain ⟨t, ht⟩ := exists_submatrix_id_rank_eq M hr
  -- The tall submatrix `N` has rank `r`; pass to its transpose to pick rows.
  set N : Matrix m (Fin r) R := M.submatrix id t with hN
  have hNrank : Nᵀ.rank = r := by rw [rank_transpose, hN, ht]
  obtain ⟨s, hs⟩ := exists_submatrix_id_rank_eq Nᵀ hNrank.ge
  -- `Nᵀ.submatrix id s` is the square `r × r` minor `(M.submatrix s t)ᵀ`.
  have hsq : Nᵀ.submatrix id s = (M.submatrix s t)ᵀ := by
    rw [hN, transpose_submatrix, submatrix_submatrix, transpose_submatrix]
    rfl
  rw [hsq] at hs
  refine ⟨s, t, ?_⟩
  have hdet : (M.submatrix s t)ᵀ.det ≠ 0 := by
    have := (rank_eq_card_iff_det_ne_zero (M.submatrix s t)ᵀ).1 (by rw [hs, Fintype.card_fin])
    exact this
  rwa [det_transpose] at hdet

/-- **The minor characterisation of rank.** For a square matrix over a field,
`r ≤ M.rank` iff some `r × r` minor is nonsingular. The forward direction is the
hard `exists_submatrix_det_ne_zero_of_le_rank`; the reverse is the easy
`le_rank_of_submatrix_det_ne_zero`. -/
theorem le_rank_iff_exists_submatrix_det_ne_zero [Fintype n] {r : ℕ}
    (M : Matrix n n R) :
    r ≤ M.rank ↔ ∃ s : Fin r → n, ∃ t : Fin r → n, (M.submatrix s t).det ≠ 0 :=
  ⟨fun hr => exists_submatrix_det_ne_zero_of_le_rank M hr,
    fun ⟨s, t, h⟩ => le_rank_of_submatrix_det_ne_zero M s t h⟩

end Matrix

namespace ErgodicTheory

variable {X : Type*} {d : ℕ}

/-- **The rank level set is measurable.** For a measurable matrix family `A` and a
measurable base map `T`, the set `{x | r ≤ cocycleRank A T n x}` is measurable.

By the minor characterisation of rank
(`Matrix.le_rank_iff_exists_submatrix_det_ne_zero`) this set equals the finite union
over all minor selections of the measurable nonsingular-minor sets
`{x | ((cocycle A T n x).submatrix s t).det ≠ 0}`
(`measurableSet_minor_det_ne_zero`). This is the level set whose differences cut out
the strata of the singular measurable filtration. -/
theorem measurableSet_le_cocycleRank [MeasurableSpace X] {r : ℕ}
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X}
    (hT : Measurable T) (n : ℕ) :
    MeasurableSet {x | r ≤ cocycleRank A T n x} := by
  have hset : {x | r ≤ cocycleRank A T n x}
      = ⋃ s : Fin r → Fin d, ⋃ t : Fin r → Fin d,
          {x | ((cocycle A T n x).submatrix s t).det ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [cocycleRank, Matrix.le_rank_iff_exists_submatrix_det_ne_zero]
  rw [hset]
  have hcoc : Measurable (fun x => cocycle A T n x) := measurable_cocycle hA hT n
  refine MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun t => ?_
  exact measurableSet_minor_det_ne_zero hcoc s t

/-- **The cocycle-rank dimension function is measurable.** The dimension datum
`x ↦ cocycleRank A T n x` of the singular flag is measurable: a `ℕ`-valued function
is measurable once every fibre `{x | f x = k}` is measurable, and each fibre is the
difference `{x | k ≤ f x} \ {x | k + 1 ≤ f x}` of the (measurable) rank level sets
from `measurableSet_le_cocycleRank`. -/
theorem measurable_cocycleRank [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X}
    (hT : Measurable T) (n : ℕ) :
    Measurable (fun x => cocycleRank A T n x) := by
  refine measurable_to_countable' fun k => ?_
  have hfib : (fun x => cocycleRank A T n x) ⁻¹' {k}
      = {x | k ≤ cocycleRank A T n x} \ {x | k + 1 ≤ cocycleRank A T n x} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
    omega
  rw [hfib]
  exact (measurableSet_le_cocycleRank hA hT n).diff (measurableSet_le_cocycleRank hA hT n)

end ErgodicTheory
