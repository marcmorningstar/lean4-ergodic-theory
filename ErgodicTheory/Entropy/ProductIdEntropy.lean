/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropyCondBound
import ErgodicTheory.Entropy.ProductRectangleEntropy
import ErgodicTheory.Entropy.CondEntropyRefineZero
import ErgodicTheory.Entropy.ProductFactorEntropy
import ErgodicTheory.Entropy.KSEntropySystem
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Frozen-factor product entropy: `h(T × id) = h(T)`

For a measure-preserving system `(X, T, μ)` on a standard-Borel space and a standard-Borel
probability space `(Y, ν)`, the frozen product transformation `T × id` on `(X × Y, μ ⊗ ν)` has the
same Kolmogorov–Sinai entropy as the base system:

`h(T × id) = h(T)`  (`ErgodicTheory.Entropy.ksEntropy_prod_id_eq`).

This is Walters' product-entropy theorem (Walters, *An Introduction to Ergodic Theory*,
Theorem 4.23), the final assembly of GitHub issue #20. It is proved by `le_antisymm` from the two
inequalities, each supplied by an already-proved sub-lemma module:

* the free bound `h(T) ≤ h(T × id)` (`ksEntropy_le_prod`, the projection factor map);
* the reverse bound `h(T × id) ≤ h(T)`, the genuine content, assembled here from Le Maître's
  inequality (7) (`ksEntropyPartition_le_add_condEntropy`), the rectangle-entropy identity
  (`ksEntropyPartition_rectangle_eq`), and the conditional-entropy refinement-to-zero glue
  (`tendsto_condEntropy_genJoin_seq_zero`).

## The reverse bound

`ksEntropy (T × id)` is the supremum over finite partitions `P` of `X × Y` of the partition
entropies `h(P, T × id)`. For each `P` we squeeze with an *increasing rectangle sequence*
`rectₘ = ξₘ ⊠ ηₘ`, where `ξₘ` and `ηₘ` are the standard countably-generated atom partitions of
`X` and `Y` (`MeasurableSpace.countablePartition`). Le Maître's inequality gives
`h(P, T × id) ≤ h(rectₘ, T × id) + H(P | σ(rectₘ))`; the rectangle identity rewrites
`h(rectₘ, T × id) = h(ξₘ, T) ≤ h(T)`; and the rectangle σ-algebras saturate `m(X × Y)`, so the
static conditional entropies `H(P | σ(rectₘ))` tend to `0`. The limit is taken on `ℝ` (EReal
addition is not jointly continuous), handling `h(T) = ⊤` separately by `le_top`.

## Main results

* `ErgodicTheory.Entropy.ksEntropy_prod_id_eq`: `h(T × id) = h(T)`.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Theorem 4.23.
* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1–2.
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

noncomputable section

variable {α : Type*}

/-- **Fintype on a countably-generated finite partition.** Each `countablePartition α n` is a finite
set of sets (`finite_countablePartition`); we promote that `Finite`-ness to a `Fintype` so the set
can index a `MeasurePartition`. -/
noncomputable instance instFintypeCountablePartition [MeasurableSpace α]
    [MeasurableSpace.CountablyGenerated α] (n : ℕ) :
    Fintype (MeasurableSpace.countablePartition α n) :=
  (MeasurableSpace.finite_countablePartition α n).fintype

/-- **The countably-generated atom partition of a standard-Borel space**, packaged as a
`MeasurePartition` indexed by the (finite) set `countablePartition α n` itself. Its cells are the
atoms (`Subtype.val`); they are measurable, genuinely disjoint and cover the space. -/
def cgPart (α : Type*) [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α] (μ : Measure α)
    (n : ℕ) : MeasurePartition μ ↥(MeasurableSpace.countablePartition α n) where
  cells := Subtype.val
  measurable := fun s => MeasurableSpace.measurableSet_countablePartition n s.2
  aedisjoint := fun s t hst =>
    (MeasurableSpace.disjoint_countablePartition s.2 t.2 (Subtype.coe_injective.ne hst)).aedisjoint
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ ⋃₀ MeasurableSpace.countablePartition α n := by
      rw [MeasurableSpace.sUnion_countablePartition]; exact Set.mem_univ x
    obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hxs⟩

/-- `cgPart α μ n` generates the same σ-algebra as `countablePartition α n`. -/
lemma generatedSigmaAlgebra_cgPart (α : Type*) [MeasurableSpace α]
    [MeasurableSpace.CountablyGenerated α] (μ : Measure α) (n : ℕ) :
    generatedSigmaAlgebra μ (cgPart α μ n)
      = MeasurableSpace.generateFrom (MeasurableSpace.countablePartition α n) := by
  have hr : Set.range (cgPart α μ n).cells = MeasurableSpace.countablePartition α n :=
    Subtype.range_val
  unfold generatedSigmaAlgebra
  rw [hr]

/-- The same atom partition, reindexed to a `Fin`-indexed partition (so it can feed `le_ksEntropy`,
whose supremum ranges over `Fin`-indexed partitions). -/
def cgFin (α : Type*) [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α] (μ : Measure α)
    (n : ℕ) : MeasurePartition μ (Fin (Fintype.card ↥(MeasurableSpace.countablePartition α n))) :=
  (cgPart α μ n).reindex (Fintype.equivFin _).symm

/-- The `Fin`-reindexed atom partition generates the same σ-algebra as `countablePartition`. -/
lemma generatedSigmaAlgebra_cgFin (α : Type*) [MeasurableSpace α]
    [MeasurableSpace.CountablyGenerated α] (μ : Measure α) (n : ℕ) :
    generatedSigmaAlgebra μ (cgFin α μ n)
      = MeasurableSpace.generateFrom (MeasurableSpace.countablePartition α n) := by
  unfold cgFin
  rw [generatedSigmaAlgebra_reindex, generatedSigmaAlgebra_cgPart]

/-- The generated σ-algebras of `countablePartition` are increasing in refinement. -/
lemma generateFrom_countablePartition_monotone (α : Type*) [MeasurableSpace α]
    [MeasurableSpace.CountablyGenerated α] :
    Monotone (fun n => MeasurableSpace.generateFrom (MeasurableSpace.countablePartition α n)) :=
  monotone_nat_of_le_succ fun n => MeasurableSpace.generateFrom_countablePartition_le_succ α n

/-- **The countably-generated atom partitions saturate the ambient σ-algebra:**
`⨆ n, σ(countablePartition α n) = mα`. -/
lemma iSup_generateFrom_countablePartition (α : Type*) [m : MeasurableSpace α]
    [MeasurableSpace.CountablyGenerated α] :
    (⨆ n, MeasurableSpace.generateFrom (MeasurableSpace.countablePartition α n)) = m := by
  rw [MeasurableSpace.iSup_generateFrom, MeasurableSpace.generateFrom_iUnion_countablePartition]

/-- **Rectangle σ-algebra.** For partitions `ξ` of `(X, μ)` and `η` of `(Y, ν)`, the σ-algebra
generated by the rectangle partition `(fst⁻¹ ξ) ∨ (snd⁻¹ η)` of `X × Y` is the join of the pulled-
back coordinate σ-algebras `comap fst σ(ξ) ⊔ comap snd σ(η)`. The `≤` step writes each rectangle
`ξᵢ × ηⱼ = fst⁻¹ ξᵢ ∩ snd⁻¹ ηⱼ`; the `≥` direction writes each `fst⁻¹ ξᵢ = ⋃ⱼ ξᵢ × ηⱼ` using that
`η` covers `Y` (and symmetrically for `snd`). -/
lemma generatedSigmaAlgebra_rect {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ξ : MeasurePartition μ ι)
    (η : MeasurePartition ν κ) :
    generatedSigmaAlgebra (μ.prod ν)
        (joinPartition (ξ.pulledBack (measurePreserving_fst (μ := μ) (ν := ν)))
          (η.pulledBack (measurePreserving_snd (μ := μ) (ν := ν))))
      = MeasurableSpace.comap Prod.fst (generatedSigmaAlgebra μ ξ)
        ⊔ MeasurableSpace.comap Prod.snd (generatedSigmaAlgebra ν η) := by
  unfold generatedSigmaAlgebra
  rw [MeasurableSpace.comap_generateFrom, MeasurableSpace.comap_generateFrom,
    MeasurableSpace.generateFrom_sup_generateFrom]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨⟨i, j⟩, rfl⟩
    have h1 : Prod.fst ⁻¹' ξ.cells i ∈
        Set.preimage Prod.fst '' Set.range ξ.cells
          ∪ Set.preimage Prod.snd '' Set.range η.cells :=
      Or.inl ⟨ξ.cells i, ⟨i, rfl⟩, rfl⟩
    have h2 : Prod.snd ⁻¹' η.cells j ∈
        Set.preimage Prod.fst '' Set.range ξ.cells
          ∪ Set.preimage Prod.snd '' Set.range η.cells :=
      Or.inr ⟨η.cells j, ⟨j, rfl⟩, rfl⟩
    exact (MeasurableSpace.measurableSet_generateFrom h1).inter
      (MeasurableSpace.measurableSet_generateFrom h2)
  · apply MeasurableSpace.generateFrom_le
    rintro a (⟨s, ⟨i, rfl⟩, rfl⟩ | ⟨t, ⟨j, rfl⟩, rfl⟩)
    · have hU : Prod.fst ⁻¹' ξ.cells i = ⋃ j : κ, ξ.cells i ×ˢ η.cells j := by
        rw [← Set.prod_univ, ← η.cover, Set.prod_iUnion]
      rw [hU]
      exact MeasurableSet.iUnion fun j => MeasurableSpace.measurableSet_generateFrom ⟨(i, j), rfl⟩
    · have hU : Prod.snd ⁻¹' η.cells j = ⋃ i : ι, ξ.cells i ×ˢ η.cells j := by
        rw [← Set.univ_prod, ← ξ.cover, Set.iUnion_prod_const]
      rw [hU]
      exact MeasurableSet.iUnion fun i => MeasurableSpace.measurableSet_generateFrom ⟨(i, j), rfl⟩

section Assembly

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X]
  [StandardBorelSpace Y]

/-- **The `Fin`-indexed rectangle sequence** feeding the conditional-entropy glue: the rectangle
partition `ξₙ ⊠ ηₙ` (atom partitions of `X` and `Y`), reindexed to a `Fin`-indexed partition. -/
def prodBPart (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) :=
  (joinPartition ((cgFin X μ n).pulledBack (measurePreserving_fst (μ := μ) (ν := ν)))
    ((cgPart Y ν n).pulledBack (measurePreserving_snd (μ := μ) (ν := ν)))).reindex
      (Fintype.equivFin _).symm

variable (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The σ-algebra of the reindexed rectangle equals that of the (non-reindexed) rectangle join. -/
lemma generatedSigmaAlgebra_prodBPart (n : ℕ) :
    generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν n)
      = generatedSigmaAlgebra (μ.prod ν)
          (joinPartition ((cgFin X μ n).pulledBack (measurePreserving_fst (μ := μ) (ν := ν)))
            ((cgPart Y ν n).pulledBack (measurePreserving_snd (μ := μ) (ν := ν)))) := by
  unfold prodBPart
  exact generatedSigmaAlgebra_reindex _ _

/-- The rectangle σ-algebra in coordinate form: `comap fst σ(ξₙ) ⊔ comap snd σ(ηₙ)`. -/
lemma generatedSigmaAlgebra_prodBPart_eq (n : ℕ) :
    generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν n)
      = MeasurableSpace.comap Prod.fst
            (MeasurableSpace.generateFrom (MeasurableSpace.countablePartition X n))
        ⊔ MeasurableSpace.comap Prod.snd
            (MeasurableSpace.generateFrom (MeasurableSpace.countablePartition Y n)) := by
  rw [generatedSigmaAlgebra_prodBPart, generatedSigmaAlgebra_rect, generatedSigmaAlgebra_cgFin,
    generatedSigmaAlgebra_cgPart]

/-- The rectangle σ-algebras form an increasing chain. -/
lemma generatedSigmaAlgebra_prodBPart_mono :
    Monotone (fun n => generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν n)) := by
  simp only [generatedSigmaAlgebra_prodBPart_eq]
  intro a b hab
  exact sup_le_sup (MeasurableSpace.comap_mono (generateFrom_countablePartition_monotone X hab))
    (MeasurableSpace.comap_mono (generateFrom_countablePartition_monotone Y hab))

/-- The rectangle σ-algebras saturate the product σ-algebra `m(X × Y)`. -/
lemma generatedSigmaAlgebra_prodBPart_iSup :
    (⨆ n, generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν n))
      = (inferInstance : MeasurableSpace (X × Y)) := by
  simp only [generatedSigmaAlgebra_prodBPart_eq]
  rw [iSup_sup_eq, ← MeasurableSpace.comap_iSup, ← MeasurableSpace.comap_iSup,
    iSup_generateFrom_countablePartition, iSup_generateFrom_countablePartition]
  rfl

variable {T : X → X} (hT : MeasurePreserving T μ μ)

/-- **Per-partition reverse bound.** For each finite partition `P` of `X × Y` with nonempty index,
`h(P, T × id) ≤ h(T)`. The argument squeezes via the rectangle sequence: Le Maître's inequality
bounds `h(P, T × id)` by `h(ξₙ, T) + H(P | σ(rectₙ))`, the first term is `≤ h(T)`, and the second
tends to `0`. -/
lemma ksEntropyPartition_prod_le {n : ℕ} (P : MeasurePartition (μ.prod ν) (Fin n))
    [Nonempty (Fin n)] :
    ((ksEntropyPartition (hT.prod (MeasurePreserving.id ν)) P : ℝ) : EReal) ≤ ksEntropy hT := by
  rcases eq_or_ne (ksEntropy hT) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hpos : (0 : EReal) ≤ ksEntropy hT := ksEntropy_nonneg hT
  have hbot : ksEntropy hT ≠ ⊥ := (lt_of_lt_of_le EReal.bot_lt_zero hpos).ne'
  set hR : ℝ := (ksEntropy hT).toReal with hRdef
  have hRcoe : ((hR : ℝ) : EReal) = ksEntropy hT := EReal.coe_toReal htop hbot
  -- The conditional entropies along the rectangle sequence tend to `0` (SL3 + σ-algebra rewrite).
  have hc : Tendsto (fun m => condEntropy (μ.prod ν)
      (generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν m)) P.cells) atTop (𝓝 0) :=
    tendsto_condEntropy_genJoin_seq_zero P (fun m => ⟨_, prodBPart μ ν m⟩)
      (generatedSigmaAlgebra_prodBPart_mono μ ν) (generatedSigmaAlgebra_prodBPart_iSup μ ν)
  simp only [generatedSigmaAlgebra_prodBPart] at hc
  -- Per-`m` real bound: `h(P, T × id) ≤ hR + H(P | σ(rectₘ))`.
  have hbound : ∀ m, ksEntropyPartition (hT.prod (MeasurePreserving.id ν)) P ≤ hR
      + condEntropy (μ.prod ν) (generatedSigmaAlgebra (μ.prod ν)
          (joinPartition ((cgFin X μ m).pulledBack (measurePreserving_fst (μ := μ) (ν := ν)))
            ((cgPart Y ν m).pulledBack (measurePreserving_snd (μ := μ) (ν := ν))))) P.cells := by
    intro m
    have hsl1 := ksEntropyPartition_le_add_condEntropy (hT.prod (MeasurePreserving.id ν)) P
      (joinPartition ((cgFin X μ m).pulledBack (measurePreserving_fst (μ := μ) (ν := ν)))
        ((cgPart Y ν m).pulledBack (measurePreserving_snd (μ := μ) (ν := ν))))
    rw [ksEntropyPartition_rectangle_eq hT (cgFin X μ m) (cgPart Y ν m)] at hsl1
    have hξle : ksEntropyPartition hT (cgFin X μ m) ≤ hR := by
      have hle := le_ksEntropy hT (cgFin X μ m)
      rw [← hRcoe, EReal.coe_le_coe_iff] at hle
      exact hle
    exact hsl1.trans (by gcongr)
  -- Take the limit on `ℝ`, then lift the coercion.
  have hlim : Tendsto (fun m => hR + condEntropy (μ.prod ν)
      (generatedSigmaAlgebra (μ.prod ν)
        (joinPartition ((cgFin X μ m).pulledBack (measurePreserving_fst (μ := μ) (ν := ν)))
          ((cgPart Y ν m).pulledBack (measurePreserving_snd (μ := μ) (ν := ν))))) P.cells)
      atTop (𝓝 hR) := by
    have hconst : Tendsto (fun _ : ℕ => hR) atTop (𝓝 hR) := tendsto_const_nhds
    have htmp := hconst.add hc
    rwa [add_zero] at htmp
  have hreal : ksEntropyPartition (hT.prod (MeasurePreserving.id ν)) P ≤ hR :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  calc ((ksEntropyPartition (hT.prod (MeasurePreserving.id ν)) P : ℝ) : EReal)
      ≤ ((hR : ℝ) : EReal) := EReal.coe_le_coe hreal
    _ = ksEntropy hT := hRcoe

end Assembly

section Main

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X]
  [StandardBorelSpace Y] {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {T : X → X} (hT : MeasurePreserving T μ μ)

/-- **Walters' product-entropy theorem (frozen identity factor):** `h(T × id) = h(T)`.

The free bound `h(T) ≤ h(T × id)` is `ksEntropy_le_prod` (the base is a factor of the product). The
reverse bound `h(T × id) ≤ h(T)` is `ksEntropyPartition_prod_le` for each finite partition `P`
of `X × Y`: partitions over an empty index do not exist on the nonempty space `X × Y`, so the
supremum reduces to the per-partition bounds. -/
theorem ksEntropy_prod_id_eq :
    ksEntropy (hT.prod (MeasurePreserving.id ν)) = ksEntropy hT := by
  refine le_antisymm ?_ (ksEntropy_le_prod hT)
  have hexp : ksEntropy (hT.prod (MeasurePreserving.id ν))
      = ⨆ n : ℕ, ⨆ P : MeasurePartition (μ.prod ν) (Fin n),
          ((ksEntropyPartition (hT.prod (MeasurePreserving.id ν)) P : ℝ) : EReal) := rfl
  rw [hexp]
  refine iSup_le fun n => iSup_le fun P => ?_
  rcases isEmpty_or_nonempty (Fin n) with hemp | hne
  · haveI := hemp
    exfalso
    have huniv : (Set.univ : Set (X × Y)) = ∅ := by rw [← P.cover, Set.iUnion_of_empty]
    have h1 : (μ.prod ν) Set.univ = 0 := by rw [huniv, measure_empty]
    rw [measure_univ] at h1
    exact one_ne_zero h1
  · haveI := hne
    exact ksEntropyPartition_prod_le μ ν hT P

end Main

end

end ErgodicTheory.Entropy
