/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ErgodicTheory.Cocycle.Norm
import ErgodicTheory.Lyapunov.Extensions.SingularRank

/-!
# Measurability of the singular rank data

For the singular (non-invertible) multiplicative ergodic theorem the Oseledets
decomposition degenerates to a **measurable filtration**
`ℝ^d = V₁(x) ⊃ V₂(x) ⊃ ⋯ ⊃ {0}` whose strata carry the dimension data of the
flag (Quas, *Multiplicative Ergodic Theorems and Applications*, lecture notes,
Universidade de São Paulo, 2013, Theorem 2 — the non-invertible Oseledets theorem
after Oseledec [12] and Raghunathan [13]: the filtration is **measurable** and its
dimensions are the multiplicities `m_j`). A prerequisite for assembling that
measurable flag is that the *dimension data* of the cocycle — the rank of each
matrix product, and the level sets of that rank — depend measurably on the base
point `x`.

This file supplies the determinantal building blocks of that measurability.

The crux for the **full** rank function `x ↦ (A x).rank` is the determinantal
characterisation of rank: `r ≤ (A x).rank` iff some `r × r` minor of `A x` has
nonzero determinant, which would express each level set as a finite union of the
measurable sets `{x | minor-det ≠ 0}`. That equivalence (rank ↔ nonzero minors) is
**not** in Mathlib, so the general `Measurable (fun x => (A x).rank)` cannot yet be
proved here; see the module note at the end.

What *is* available is the **top stratum** of the flag — the full-rank set — via the
square determinantal characterisation `A.rank = d ↔ A.det ≠ 0`, which this file
proves (`Matrix.rank_eq_card_iff_det_ne_zero`) and turns into measurability of the
top-rank level set of the cocycle.

## Main results

* `ErgodicTheory.measurable_minor_det`: for a measurable matrix family `A`, the
  determinant of any fixed `r × r` minor `x ↦ ((A x).submatrix s t).det` is
  measurable. (A single minor — the elementary piece of the determinantal-rank
  union.)
* `ErgodicTheory.measurableSet_minor_det_ne_zero`: the set where a fixed minor is
  nondegenerate, `{x | ((A x).submatrix s t).det ≠ 0}`, is measurable.
* `Matrix.rank_eq_card_iff_det_ne_zero`: for a square matrix over a field,
  `A.rank = Fintype.card n ↔ A.det ≠ 0` (the full-rank determinantal criterion).
* `ErgodicTheory.measurableSet_cocycleRank_eq_full`: the top stratum of the rank flag,
  `{x | cocycleRank A T n x = d}`, is measurable.

## Remaining gap

The full measurable dimension function `x ↦ cocycleRank A T n x` (hence the
eventual-kernel dimension `x ↦ d - iInf_n cocycleRank A T n x`) requires the
rank ↔ nonzero-minor equivalence that Mathlib still lacks; see the closing note.
-/

open MeasureTheory

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R]

/-- **Full-rank determinantal criterion.** A square matrix over a field has full
rank iff its determinant is nonzero. This is the top-stratum case of the
determinantal characterisation of rank (the general `r ≤ rank ↔ nonzero r-minor`
is not yet in Mathlib). -/
theorem rank_eq_card_iff_det_ne_zero (A : Matrix n n R) :
    A.rank = Fintype.card n ↔ A.det ≠ 0 := by
  constructor
  · intro hrank hdet
    -- full rank ⇒ `range A.mulVecLin = ⊤` ⇒ `A.mulVecLin` injective ⇒ `det ≠ 0`.
    have htop : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_pi (R := R)]
      exact hrank
    have hsurj : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.1 htop
    have hinj : Function.Injective A.mulVecLin :=
      LinearMap.injective_iff_surjective.2 hsurj
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    refine hv (hinj ?_)
    rw [A.mulVecLin.map_zero, Matrix.mulVecLin_apply, hAv]
  · intro hdet
    have : IsUnit A := A.isUnit_iff_isUnit_det.2 (isUnit_iff_ne_zero.2 hdet)
    exact A.rank_of_isUnit this

end Matrix

namespace ErgodicTheory

variable {X : Type*} {d : ℕ}

/-- **Measurability of a single minor's determinant.** For a measurable matrix
family `A`, the determinant of the fixed `r × r` minor selected by `s, t` depends
measurably on `x`. Each minor entry is `(A x) (s i) (t j)`, a measurable coordinate
of `A x`, and the determinant is a polynomial in those entries. This is the
elementary piece of the determinantal characterisation of rank. -/
theorem measurable_minor_det [MeasurableSpace X] {r : ℕ}
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A)
    (s t : Fin r → Fin d) :
    Measurable (fun x => ((A x).submatrix s t).det) := by
  have hsub : Measurable (fun x => (A x).submatrix s t) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simp only [Matrix.submatrix_apply]
    exact (measurable_matrix_entry (s i) (t j)).comp hA
  exact measurable_det.comp hsub

/-- **The nondegenerate-minor set is measurable.** The set of base points where a
fixed `r × r` minor of `A x` has nonzero determinant is measurable: it is the
preimage of the measurable set `{0}ᶜ` under the measurable minor-determinant. In
the determinantal characterisation of rank these are the sets whose finite unions
cut out the rank level sets. -/
theorem measurableSet_minor_det_ne_zero [MeasurableSpace X] {r : ℕ}
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A)
    (s t : Fin r → Fin d) :
    MeasurableSet {x | ((A x).submatrix s t).det ≠ 0} := by
  have : {x | ((A x).submatrix s t).det ≠ 0}
      = (fun x => ((A x).submatrix s t).det) ⁻¹' {0}ᶜ := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
  rw [this]
  exact (measurableSet_singleton 0).compl.preimage (measurable_minor_det hA s t)

/-- **The full-rank stratum of the cocycle is measurable.** The top stratum of the
singular rank flag — the set where the `n`-step cocycle still has full rank `d` —
is measurable. By the full-rank determinantal criterion
`Matrix.rank_eq_card_iff_det_ne_zero` it equals `{x | (cocycle A T n x).det ≠ 0}`,
the preimage of `{0}ᶜ` under the measurable determinant of the (measurable) cocycle.
This is the outermost, full-dimension layer of the measurable filtration. -/
theorem measurableSet_cocycleRank_eq_full [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X}
    (hT : Measurable T) (n : ℕ) :
    MeasurableSet {x | cocycleRank A T n x = d} := by
  have hset : {x | cocycleRank A T n x = d}
      = (fun x => (cocycle A T n x).det) ⁻¹' {0}ᶜ := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, cocycleRank]
    have h := Matrix.rank_eq_card_iff_det_ne_zero (cocycle A T n x)
    rw [Fintype.card_fin] at h
    exact h
  rw [hset]
  exact (measurableSet_singleton 0).compl.preimage
    (measurable_det.comp (measurable_cocycle hA hT n))

end ErgodicTheory
