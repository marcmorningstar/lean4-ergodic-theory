/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.KSEntropySystem
import Oseledets.Entropy.FactorMap

/-!
# Pulled-back partitions and factor-relative entropy invariance

Given a factor map `π : α → β` from a measure-preserving system `(α, T, μ)` to `(β, S, ν)`
(`Oseledets.Entropy.IsFactorMap`), every finite measurable partition `R` of the *target* `β`
pulls back to a finite measurable partition of the *source* `α`, whose cells are the preimages
`π⁻¹(R.cells)`. This file constructs that pulled-back partition `MeasurePartition.pulledBack` and
proves the **factor-relative entropy invariance**

`h(π⁻¹R, T) = h(R, S)`  (`Oseledets.Entropy.factor_relative_eq`),

the first reduction of the Abramov–Rokhlin addition formula (issue #13). It is a clean change of
variables: the intertwining `π ∘ T = S ∘ π` gives `T⁻ᵏ(π⁻¹Rⱼ) = π⁻¹(S⁻ᵏRⱼ)`, so the cells of the
iterated join of `π⁻¹R` are the `π`-preimages of the cells of the iterated join of `R`; and
`MeasurePreserving π` gives `μ(π⁻¹E) = ν(E)`, so the two iterated-join entropy *sequences*
coincide for every `n`, hence so do their Fekete limits.

## Main definitions

* `Oseledets.Entropy.MeasurePartition.pulledBack`: the partition of `α` with cells `π⁻¹(R.cells)`,
  for a measure-preserving `π : α → β` and a partition `R` of `β`.

## Main results

* `Oseledets.Entropy.factor_relative_eq`: `ksEntropyPartition hT (R.pulledBack hπ) =
  ksEntropyPartition hS R`, the factor-relative entropy invariance.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Ch. 4.
-/

open MeasureTheory Function

namespace Oseledets.Entropy

variable {α β : Type*} {ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Equal subadditive sequences have equal Fekete limits.** Since `Subadditive.lim u` is
`sInf ((fun n => u n / n) '' Ici 1)`, depending only on the underlying sequence `u` and not on the
subadditivity proof, two subadditive sequences that agree as functions have equal limits. -/
lemma Subadditive.lim_eq_of_eq {u v : ℕ → ℝ} (hu : Subadditive u) (hv : Subadditive v)
    (huv : u = v) : hu.lim = hv.lim := by
  subst huv; rfl

/-- The **pulled-back partition** `π⁻¹ R` of a finite measurable partition `R` of the target `β`
along a measure-preserving map `π : α → β`: the partition of the source `α` whose cell at index
`i` is the preimage `π⁻¹ (R.cells i)`. Each cell is measurable (preimage of a measurable set under
the measurable `π`); the family is pairwise almost-everywhere disjoint (the preimage of an
a.e.-disjoint pair is a.e. disjoint, since `π` pushes `μ` to `ν`); and the cells cover the source
(the preimage of the cover `⋃ i, R.cells i = univ` is `univ`). -/
noncomputable def MeasurePartition.pulledBack [Fintype ι] {μ : Measure α} {ν : Measure β}
    {π : α → β} (hπ : MeasurePreserving π μ ν) (R : MeasurePartition ν ι) :
    MeasurePartition μ ι where
  cells := fun i => π ⁻¹' R.cells i
  measurable := fun i => (R.measurable i).preimage hπ.measurable
  aedisjoint := by
    intro i j hij
    simp only [onFun, AEDisjoint, ← Set.preimage_inter]
    rw [hπ.measure_preimage ((R.measurable i).inter (R.measurable j)).nullMeasurableSet]
    exact R.aedisjoint hij
  cover := by rw [← Set.preimage_iUnion, R.cover, Set.preimage_univ]

@[simp]
lemma MeasurePartition.pulledBack_cells [Fintype ι] {μ : Measure α} {ν : Measure β}
    {π : α → β} (hπ : MeasurePreserving π μ ν) (R : MeasurePartition ν ι) :
    (R.pulledBack hπ).cells = fun i => π ⁻¹' R.cells i := rfl

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- **Intertwining of iterated-join cells.** If `π` intertwines the dynamics, `π ∘ T = S ∘ π`, then
the cell at index `f` of the iterated join of the pulled-back partition `π⁻¹R` is the `π`-preimage
of the cell at `f` of the iterated join of `R`:
`ksJoinCells (π⁻¹R) T n f = π⁻¹ (ksJoinCells R S n f)`. Coordinatewise this is
`T⁻ᵏ(π⁻¹Rⱼ) = π⁻¹(S⁻ᵏRⱼ)`, the iterate `π ∘ T^[k] = S^[k] ∘ π` of the intertwining via
`Function.Semiconj`. -/
lemma ksJoinCells_pulledBack {T : α → α} {S : β → β} {π : α → β}
    (hπS : π ∘ T = S ∘ π) (R : ι → Set β) (n : ℕ) (f : Fin n → ι) :
    ksJoinCells (fun i => π ⁻¹' R i) T n f = π ⁻¹' ksJoinCells R S n f := by
  -- `π ∘ T^[k] = S^[k] ∘ π` for all `k`, via `Semiconj.iterate_right`.
  have hsemi : Function.Semiconj π T S := Function.semiconj_iff_comp_eq.mpr hπS
  rw [ksJoinCells_apply, ksJoinCells_apply, Set.preimage_iInter]
  refine Set.iInter_congr fun k => ?_
  -- `T^[k] ⁻¹' (π ⁻¹' R (f k)) = π ⁻¹' (S^[k] ⁻¹' R (f k))`.
  rw [← Set.preimage_comp, ← Set.preimage_comp, (hsemi.iterate_right (k : ℕ)).comp_eq]

variable [Fintype ι]

/-- **Factor-relative entropy invariance.** Let `π : α → β` be a factor map from `(α, T, μ)` to
`(β, S, ν)` (a measure-preserving intertwining `π ∘ T = S ∘ π`), and let `R` be a finite measurable
partition of the target. Then the Kolmogorov–Sinai entropy of the pulled-back partition `π⁻¹R`
relative to `T` equals that of `R` relative to `S`:
`h(π⁻¹R, T) = h(R, S)`.

This is the first reduction of the Abramov–Rokhlin addition formula. The proof is a change of
variables: for each `n` the cells of the iterated join of `π⁻¹R` are the `π`-preimages of those of
the iterated join of `R` (`ksJoinCells_pulledBack`), and `μ(π⁻¹E) = ν(E)` by measure-preservation,
so the two iterated-join entropy *sequences* `ksEntropySeq` agree as functions of `n`; the
subadditive sequences are therefore equal and have equal Fekete limits (`Subadditive.lim_congr`). -/
theorem factor_relative_eq {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : α → α} {S : β → β} {π : α → β}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (hπ : MeasurePreserving π μ ν) (hπS : π ∘ T = S ∘ π) (R : MeasurePartition ν ι) :
    ksEntropyPartition hT (R.pulledBack hπ) = ksEntropyPartition hS R := by
  rw [ksEntropyPartition, ksEntropyPartition]
  refine Subadditive.lim_eq_of_eq _ _ (funext fun n => ?_)
  -- The two iterated-join entropy sequences coincide at `n`.
  rw [ksEntropySeq, ksEntropySeq, ksJoin_cells, ksJoin_cells, entropy_def, entropy_def]
  refine Finset.sum_congr rfl fun f _ => ?_
  -- Cells coincide under `π`-preimage, and `μ(π⁻¹E) = ν(E)`.
  rw [MeasurePartition.pulledBack_cells, ksJoinCells_pulledBack hπS R.cells n f]
  rw [hπ.measure_preimage]
  exact ((ksJoin hS R n).measurable f).nullMeasurableSet

end Oseledets.Entropy
