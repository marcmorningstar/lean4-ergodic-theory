/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Fekete
import Mathlib.Analysis.Subadditive
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Kolmogorov–Sinai entropy via the Fekete limit

This file completes the measure-theoretic foundation for Kolmogorov–Sinai entropy started in
`ErgodicTheory.Entropy.Partition`, `ErgodicTheory.Entropy.Join`, `ErgodicTheory.Entropy.Subadditive`,
`ErgodicTheory.Entropy.Subadditive2`, and `ErgodicTheory.Entropy.Fekete`. It defines the entropy
`h(α, T)` of a measure-preserving transformation `T` relative to a finite measurable partition
`α` as the **Fekete limit** of the iterated-join entropy sequence.

Following the Le Maître notes on the Kolmogorov–Sinai theorem, the iterated join
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` is realized here with a **`Fin`-indexed** cell family, where the cell at an
index `f : Fin n → ι` is the intersection `⋂ₖ T⁻ᵏ (α_{f k})`. This flat `Fin`-indexing is what
makes the `n + m` subadditivity close: splitting `Fin (n + m) ≃ Fin n ⊕ Fin m` exhibits the
`(n + m)`-fold join, up to a reindexing of cells by `Fin.appendEquiv`, as the ordinary join of
the `n`-fold join with the `Tⁿ`-pullback of the `m`-fold join. Combined with the join
subadditivity `entropy_join_le` and the pullback invariance `entropy_pullback`, this gives
`ksEntropySeq (n + m) ≤ ksEntropySeq n + ksEntropySeq m`, so the sequence is `Subadditive`, and
`Subadditive.tendsto_lim` (Fekete's lemma) produces the limit `h(α, T)`, with the boundedness
hypothesis discharged from nonnegativity.

## Main definitions

* `ErgodicTheory.Entropy.ksJoin`: the flat `Fin n`-indexed iterated join, a measurable partition.
* `ErgodicTheory.Entropy.ksEntropySeq`: the entropy sequence `n ↦ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)`.
* `ErgodicTheory.Entropy.ksEntropyPartition`: the Kolmogorov–Sinai entropy `h(α, T)`, the Fekete limit.

## Main results

* `ErgodicTheory.Entropy.ksEntropySeq_subadditive`: `ksEntropySeq (n + m) ≤ ksEntropySeq n +
  ksEntropySeq m`.
* `ErgodicTheory.Entropy.ksSubadditive`: the sequence is a `Subadditive` sequence.
* `ErgodicTheory.Entropy.tendsto_ksEntropySeq`: `n ↦ ksEntropySeq n / n` tends to `ksEntropyPartition`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- The cell family of the flat `Fin n`-indexed iterated join: the cell at `f : Fin n → ι` is the
intersection `⋂ₖ T⁻ᵏ (α_{f k})` of the pullbacks of the chosen `α`-cells along the first `n`
iterates of `T`. For `n = 0` the index type `Fin 0 → ι` has a single element and the empty
intersection is the whole space, so the join is the trivial one-cell partition. -/
def ksJoinCells (cells : ι → Set α) (T : α → α) (n : ℕ) (f : Fin n → ι) : Set α :=
  ⋂ k : Fin n, (T^[(k : ℕ)]) ⁻¹' cells (f k)

omit [MeasurableSpace α] in
@[simp]
lemma ksJoinCells_apply (cells : ι → Set α) (T : α → α) (n : ℕ) (f : Fin n → ι) :
    ksJoinCells cells T n f = ⋂ k : Fin n, (T^[(k : ℕ)]) ⁻¹' cells (f k) := rfl

/-- The **flat iterated join** `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α`, indexed by `Fin n → ι`: the finite measurable
partition whose cell at `f` is `⋂ₖ T⁻ᵏ (α_{f k})`. Each cell is a finite intersection of
preimages of measurable sets under the measurable iterates `Tᵏ`; two distinct indices differ at
some `k`, where the corresponding `α`-cells are almost-everywhere disjoint and `Tᵏ` preserves the
measure, so the cells are pairwise almost-everywhere disjoint; and the cells cover the space
because for each point one can choose, at every coordinate `k`, the `α`-cell that `Tᵏ x` lies in. -/
noncomputable def ksJoin [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    MeasurePartition μ (Fin n → ι) where
  cells := ksJoinCells P.cells T n
  measurable f := by
    refine MeasurableSet.iInter fun k => ?_
    exact (P.measurable (f k)).preimage (hT.iterate (k : ℕ)).measurable
  aedisjoint := by
    intro f g hfg
    simp only [onFun]
    obtain ⟨k, hk⟩ : ∃ k, f k ≠ g k := by
      by_contra h
      exact hfg (funext fun k => not_not.mp fun hk => h ⟨k, hk⟩)
    have hsub₁ : ksJoinCells P.cells T n f ⊆ (T^[(k : ℕ)]) ⁻¹' P.cells (f k) :=
      Set.iInter_subset _ k
    have hsub₂ : ksJoinCells P.cells T n g ⊆ (T^[(k : ℕ)]) ⁻¹' P.cells (g k) :=
      Set.iInter_subset _ k
    refine AEDisjoint.mono ?_ hsub₁ hsub₂
    simp only [AEDisjoint, ← Set.preimage_inter]
    rw [(hT.iterate (k : ℕ)).measure_preimage
      ((P.measurable (f k)).inter (P.measurable (g k))).nullMeasurableSet]
    exact P.aedisjoint hk
  cover := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hx : ∀ k : Fin n, ∃ i, (T^[(k : ℕ)]) x ∈ P.cells i := fun k => by
      have : (T^[(k : ℕ)]) x ∈ ⋃ i, P.cells i := P.cover ▸ Set.mem_univ _
      exact Set.mem_iUnion.mp this
    choose f hf using hx
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iInter.mpr fun k => hf k⟩

@[simp]
lemma ksJoin_cells [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    (ksJoin hT P n).cells = ksJoinCells P.cells T n := rfl

/-- The **iterated-join entropy sequence** `n ↦ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)` for the flat `Fin`-indexed
join. Its Fekete limit is the Kolmogorov–Sinai entropy `h(α, T)`. -/
noncomputable def ksEntropySeq [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) : ℝ :=
  entropy μ (ksJoin hT P n).cells

/-- The flat `n = 0` join is the trivial one-cell partition, of entropy `0`: its only cell (the
empty intersection) is the whole space, which has measure `1`, and `negMulLog 1 = 0`. -/
@[simp]
lemma ksEntropySeq_zero [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    ksEntropySeq hT P 0 = 0 := by
  rw [ksEntropySeq, ksJoin_cells, entropy_def]
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [ksJoinCells_apply, Set.iInter_of_empty, measure_univ, ENNReal.toReal_one,
    Real.negMulLog_one]

/-- The iterated-join entropy is nonnegative for a probability measure. -/
lemma ksEntropySeq_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    0 ≤ ksEntropySeq hT P n :=
  entropy_nonneg μ _

/-- **Reindexing invariance of Shannon entropy.** Precomposing the cell family with an equivalence
of index types leaves the entropy unchanged, since it merely permutes the summands. -/
lemma entropy_reindex [Fintype ι] {β : Type*} [Fintype β] (μ : Measure α) (e : ι ≃ β)
    (s : β → Set α) : entropy μ (fun i => s (e i)) = entropy μ s := by
  rw [entropy_def, entropy_def]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

omit [MeasurableSpace α] in
/-- **Structural cell identity for the flat iterated join.** Under the append equivalence
`Fin.appendEquiv n m : (Fin n → ι) × (Fin m → ι) ≃ (Fin (n + m) → ι)`, the cell of the
`(n + m)`-fold join at `Fin.append a b` is the intersection of the cell of the `n`-fold join at
`a` with the `Tⁿ`-pullback of the cell of the `m`-fold join at `b`. This is the join–pullback
factorization underlying the subadditivity. -/
lemma ksJoinCells_append (cells : ι → Set α) (T : α → α) (n m : ℕ)
    (a : Fin n → ι) (b : Fin m → ι) :
    ksJoinCells cells T (n + m) (Fin.append a b)
      = ksJoinCells cells T n a ∩ (T^[n]) ⁻¹' ksJoinCells cells T m b := by
  -- Reindex the `Fin (n + m)` intersection along `Fin n ⊕ Fin m ≃ Fin (n + m)`.
  rw [ksJoinCells_apply]
  rw [show (⋂ k : Fin (n + m), (T^[(k : ℕ)]) ⁻¹' cells (Fin.append a b k))
      = ⋂ s : Fin n ⊕ Fin m,
          (T^[((finSumFinEquiv s : Fin (n + m)) : ℕ)]) ⁻¹'
            cells (Fin.append a b (finSumFinEquiv s)) from
    Set.iInter_congr_of_surjective finSumFinEquiv.symm finSumFinEquiv.symm.surjective
      fun k => by rw [Equiv.apply_symm_apply]]
  rw [Set.iInter_sum]
  congr 1
  · -- Left (`Fin n`) block: recovers the `n`-fold join cell at `a`.
    rw [ksJoinCells_apply]
    refine Set.iInter_congr fun i => ?_
    rw [finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.append_left]
  · -- Right (`Fin m`) block: recovers the `Tⁿ`-pullback of the `m`-fold join cell at `b`.
    rw [ksJoinCells_apply, Set.preimage_iInter]
    refine Set.iInter_congr fun j => ?_
    rw [finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.append_right]
    -- `T^[n + j] ⁻¹' A = T^[n] ⁻¹' (T^[j] ⁻¹' A)`.
    rw [show (T^[n + (j : ℕ)]) = (T^[(j : ℕ)]) ∘ (T^[n]) by
      rw [← Function.iterate_add, Nat.add_comm], Set.preimage_comp]

/-- **Subadditivity of the iterated-join entropy** (the Fekete inequality):
`H(⋁ₖ₌₀ⁿ⁺ᵐ⁻¹ T⁻ᵏ α) ≤ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α) + H(⋁ₖ₌₀ᵐ⁻¹ T⁻ᵏ α)`. Reindexing the `(n + m)`-fold
join by `Fin.appendEquiv` exhibits it as the join of the `n`-fold join with the `Tⁿ`-pullback of
the `m`-fold join (`ksJoinCells_append`); the join subadditivity `entropy_join_le` then bounds it
by the sum of the two entropies, and the pullback invariance `entropy_pullback` identifies the
second summand as the `m`-fold join entropy (`Tⁿ` is measure-preserving by `hT.iterate n`). -/
lemma ksEntropySeq_subadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n m : ℕ) :
    ksEntropySeq hT P (n + m) ≤ ksEntropySeq hT P n + ksEntropySeq hT P m := by
  -- The `Tⁿ`-pullback of the `m`-fold join.
  set Q : MeasurePartition μ (Fin m → ι) := (ksJoin hT P m).pullback (hT.iterate n) with hQ
  -- Rewrite the `(n + m)`-entropy as a join entropy via the append reindexing.
  have hreindex : ksEntropySeq hT P (n + m)
      = entropy μ (joinCells (ksJoin hT P n).cells Q.cells) := by
    rw [ksEntropySeq, ← entropy_reindex μ (Fin.appendEquiv n m) (ksJoin hT P (n + m)).cells,
      entropy_def, entropy_def]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨a, b⟩ := p
    have hcell : (ksJoin hT P (n + m)).cells (Fin.appendEquiv n m (a, b))
        = joinCells (ksJoin hT P n).cells Q.cells (a, b) := by
      simp only [ksJoin_cells, joinCells_apply, hQ, MeasurePartition.pullback_cells]
      exact ksJoinCells_append P.cells T n m a b
    rw [hcell]
  rw [hreindex, ksEntropySeq, ksEntropySeq]
  calc entropy μ (joinCells (ksJoin hT P n).cells Q.cells)
      ≤ entropy μ (ksJoin hT P n).cells + entropy μ Q.cells :=
        entropy_join_le (ksJoin hT P n) Q
    _ = entropy μ (ksJoin hT P n).cells + entropy μ (ksJoin hT P m).cells := by
        rw [hQ, entropy_pullback]

/-- The iterated-join entropy sequence is a **`Subadditive` sequence** in the sense of Fekete's
lemma: `u (k + l) ≤ u k + u l`. This is `ksEntropySeq_subadditive` repackaged. -/
lemma ksSubadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    Subadditive (ksEntropySeq hT P) := fun k l => ksEntropySeq_subadditive hT P k l

/-- **Equal subadditive sequences have equal Fekete limits.** Since `Subadditive.lim u` is defined
as `sInf ((fun n => u n / n) '' Ici 1)`, depending only on the underlying sequence `u` and not on
the subadditivity proof, two subadditive sequences that agree as functions have equal limits. -/
lemma Subadditive.lim_eq_of_eq {u v : ℕ → ℝ} (hu : Subadditive u) (hv : Subadditive v)
    (huv : u = v) : hu.lim = hv.lim := by
  subst huv; rfl

/-- The **Kolmogorov–Sinai entropy** `h(α, T)` of a measure-preserving transformation `T` relative
to a finite measurable partition `α`, defined as the Fekete limit
`limₙ (1 / n) · H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)` of the subadditive iterated-join entropy sequence. -/
noncomputable def ksEntropyPartition [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) : ℝ :=
  (ksSubadditive hT P).lim

/-- **Fekete convergence to the Kolmogorov–Sinai entropy.** The averaged iterated-join entropies
`(1 / n) · H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α)` converge to `h(α, T)`. The boundedness-below hypothesis of Fekete's
lemma `Subadditive.tendsto_lim` is discharged from the nonnegativity of the entropies: each
`ksEntropySeq n / n` is at least `0`, so the range is bounded below by `0`. -/
lemma tendsto_ksEntropySeq [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    Tendsto (fun n => ksEntropySeq hT P n / n) atTop (𝓝 (ksEntropyPartition hT P)) := by
  refine (ksSubadditive hT P).tendsto_lim ?_
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (ksEntropySeq_nonneg hT P n) (Nat.cast_nonneg n)

end ErgodicTheory.Entropy
