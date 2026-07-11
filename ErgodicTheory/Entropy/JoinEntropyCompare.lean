/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondGivenPartitionBridge
import ErgodicTheory.Entropy.CondPullback
import ErgodicTheory.Entropy.CondMono
import ErgodicTheory.Entropy.KSEntropyMono
import ErgodicTheory.Entropy.KSEntropyCondBound
import ErgodicTheory.Entropy.FinJoin

/-!
# A two-family join-entropy comparison (Ito's Lemma)

This file proves the **static (dynamics-free) Shannon comparison** underlying the Abramov
flow-homogeneity argument (Ito, *Nagoya Math. J.* **41** (1971)): for two finite families
`β = (β_k)` and `γ = (γ_k)` of finite measurable partitions indexed by `Fin N` over a common
cell-index type `ι`,
`H(⋁_k γ_k) ≤ H(⋁_k β_k) + ∑_k H(γ_k | β_k)`.

The proof is pure Shannon entropy in four steps:
`H(⋁γ) ≤ H(⋁β ∨ ⋁γ)` (refinement monotonicity) `= H(⋁β) + H(⋁γ | ⋁β)` (chain rule)
`≤ H(⋁β) + ∑_k H(γ_k | ⋁β)` (conditional subadditivity over the family)
`≤ H(⋁β) + ∑_k H(γ_k | β_k)` (conditioning on a refinement decreases conditional entropy).

The join of a `Fin N`-indexed family of cell families with a common cell-index type `ι` is the
cell family `finJoinCells`, whose cell at `f : Fin N → ι` is the intersection `⋂_k (β_k)_{f k}`.
This is the finite-family generalization of the iterated dynamical join `ksJoin` (the special case
`β_k = T^{-k} P`), and it is exactly the primitive the Abramov argument consumes, where a single
partition is pulled back at an arbitrary finite set of flow times (all sharing the cell-index type).

## Main definitions

* `ErgodicTheory.Entropy.famJoin`: the join of a finite family, packaged as a
  `MeasurePartition μ (Fin N → ι)`, when each `β_k` is a partition. Its cell family is the
  `finJoinCells` primitive of `ErgodicTheory.Entropy.FinJoin`.

## Main results

* `ErgodicTheory.Entropy.condEntropy_famJoin_le`: conditional subadditivity of the family join,
  `H(⋁_k G_k | 𝒜) ≤ ∑_k H(G_k | 𝒜)`.
* `ErgodicTheory.Entropy.entropy_finJoin_le_add_sum_condEntropy`: the headline comparison
  `H(⋁γ) ≤ H(⋁β) + ∑_k H(γ_k | β_k)` (Ito's Lemma).
* `ErgodicTheory.Entropy.entropy_finJoin_sub_le_sum_condEntropy`: the difference form
  `H(⋁γ) - H(⋁β) ≤ ∑_k H(γ_k | β_k)`.

## References

* Yuji Ito, *An elementary proof of Abramov's result on the entropy of a flow*,
  Nagoya Math. J. **41** (1971), 1–5.
* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace ErgodicTheory.Entropy

variable {X : Type*} {𝒜 : MeasurableSpace X} [mX : MeasurableSpace X]
  {ι : Type*} [Fintype ι] {μ : Measure X} {N : ℕ}

/-! ## The finite-family join primitive

The cell family `finJoinCells` and its `@[simp]` cell-description lemma `finJoinCells_apply` are
provided by `ErgodicTheory.Entropy.FinJoin` (imported above); here we package the same join as a
`MeasurePartition`. -/

/-- The **join** `⋁_{k < N} B_k` of a `Fin N`-family of finite measurable partitions all indexed by
the same cell type `ι`, packaged as a `MeasurePartition μ (Fin N → ι)`. A thin alias of
`ErgodicTheory.Entropy.finJoin` (`Entropy.FinJoin`); its cell family is
`finJoinCells (fun k => (B k).cells)`. -/
noncomputable abbrev famJoin (B : Fin N → MeasurePartition μ ι) : MeasurePartition μ (Fin N → ι) :=
  finJoin B

@[simp]
lemma famJoin_cells (B : Fin N → MeasurePartition μ ι) :
    (famJoin B).cells = finJoinCells (fun k => (B k).cells) := rfl

/-- **Cell recursion for the family join.** Splitting off the first coordinate exhibits the cell of
`⋁_{k < N+1} B_k` as the intersection of the first partition's cell with the cell of the join of the
tail family. -/
lemma famJoin_cells_succ (B : Fin (N + 1) → MeasurePartition μ ι) (f : Fin (N + 1) → ι) :
    (famJoin B).cells f
      = (B 0).cells (f 0) ∩ (famJoin (Fin.tail B)).cells (Fin.tail f) := by
  simp only [famJoin_cells, finJoinCells_apply]
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff, Fin.forall_fin_succ, Fin.tail]

/-! ## Reindexing invariance of conditional entropy -/

/-- **Reindexing leaves conditional entropy unchanged.** The cell family is merely permuted along
the equivalence `e`, so the (pointwise) sum defining `condEntropy` is unchanged. -/
lemma condEntropy_comp_equiv [StandardBorelSpace X] {ι' ι'' : Type*} [Fintype ι'] [Fintype ι'']
    [IsFiniteMeasure μ] (t : ι'' → Set X) (e : ι' ≃ ι'') :
    condEntropy μ 𝒜 (fun k => t (e k)) = condEntropy μ 𝒜 t := by
  rw [condEntropy_def, condEntropy_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact Fintype.sum_equiv e _ _ (fun k => rfl)

/-! ## Conditional subadditivity of the family join -/

/-- **Conditional subadditivity of the family join.** For a sub-σ-algebra `𝒜 ≤ mX` and a
`Fin N`-family `G` of partitions, `H(⋁_k G_k | 𝒜) ≤ ∑_k H(G_k | 𝒜)`. Proved by induction on `N`
using the pairwise conditional subadditivity `condEntropy_join_le` and the cell recursion. -/
lemma condEntropy_famJoin_le [StandardBorelSpace X] [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mX) :
    ∀ {N : ℕ} (G : Fin N → MeasurePartition μ ι),
      condEntropy μ 𝒜 (famJoin G).cells ≤ ∑ k, condEntropy μ 𝒜 (G k).cells := by
  intro N
  induction N with
  | zero =>
    intro G
    have h0 : condEntropy μ 𝒜 (famJoin G).cells = 0 := by
      rw [condEntropy_def]
      have hpt : (fun ω => ∑ f : Fin 0 → ι,
          Real.negMulLog (condExpKernel μ 𝒜 ω ((famJoin G).cells f)).toReal) =ᵐ[μ]
          fun _ => (0 : ℝ) := by
        filter_upwards with ω
        haveI : IsProbabilityMeasure (condExpKernel μ 𝒜 ω) :=
          IsMarkovKernel.isProbabilityMeasure ω
        rw [Fintype.sum_unique]
        have huniv : (famJoin G).cells (default : Fin 0 → ι) = Set.univ := by
          simp only [famJoin_cells, finJoinCells_apply]; exact Set.iInter_of_empty _
        rw [huniv, measure_univ, ENNReal.toReal_one, Real.negMulLog_one]
      rw [integral_congr_ae hpt, integral_zero]
    rw [h0]; simp
  | succ N ih =>
    intro G
    have hcell : (famJoin G).cells
        = fun f => joinCells (G 0).cells (famJoin (Fin.tail G)).cells
            ((Fin.consEquiv (fun _ : Fin (N + 1) => ι)).symm f) := by
      funext f
      rw [famJoin_cells_succ]
      rfl
    have hstep : condEntropy μ 𝒜 (famJoin G).cells
        = condEntropy μ 𝒜 (joinCells (G 0).cells (famJoin (Fin.tail G)).cells) := by
      rw [hcell]
      exact condEntropy_comp_equiv _ (Fin.consEquiv (fun _ : Fin (N + 1) => ι)).symm
    rw [hstep, Fin.sum_univ_succ]
    calc condEntropy μ 𝒜 (joinCells (G 0).cells (famJoin (Fin.tail G)).cells)
        ≤ condEntropy μ 𝒜 (G 0).cells + condEntropy μ 𝒜 (famJoin (Fin.tail G)).cells :=
          condEntropy_join_le h𝒜 (G 0) (famJoin (Fin.tail G))
      _ ≤ condEntropy μ 𝒜 (G 0).cells + ∑ k : Fin N, condEntropy μ 𝒜 ((Fin.tail G) k).cells := by
          gcongr; exact ih (Fin.tail G)

/-! ## The generated σ-algebra of a family member is coarser than that of the join -/

/-- Every cell of a family member is a union of family-join cells: precisely those whose `i`-th
coordinate equals the chosen index. -/
lemma memberCell_eq_iUnion_famJoin (B : Fin N → MeasurePartition μ ι) (i : Fin N) (j : ι) :
    (B i).cells j = ⋃ f : {f : Fin N → ι // f i = j}, (famJoin B).cells (f : Fin N → ι) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : ∀ l, ∃ jj, x ∈ (B l).cells jj := fun l =>
      Set.mem_iUnion.mp ((B l).cover ▸ Set.mem_univ x)
    choose g hg using hx'
    refine Set.mem_iUnion.mpr ⟨⟨Function.update g i j, by simp⟩, ?_⟩
    simp only [famJoin_cells, finJoinCells_apply]
    refine Set.mem_iInter.mpr fun l => ?_
    by_cases hli : l = i
    · subst hli; simpa using hx
    · simpa [Function.update_of_ne hli] using hg l
  · refine Set.iUnion_subset fun f => ?_
    simp only [famJoin_cells, finJoinCells_apply]
    refine (Set.iInter_subset _ i).trans ?_
    rw [f.2]

/-- The static observable σ-algebra of a family member is contained in that of the family join. -/
lemma generatedSigmaAlgebra_le_famJoin (B : Fin N → MeasurePartition μ ι) (i : Fin N) :
    generatedSigmaAlgebra μ (B i) ≤ generatedSigmaAlgebra μ (famJoin B) := by
  apply MeasurableSpace.generateFrom_le
  rintro t ⟨j, rfl⟩
  rw [memberCell_eq_iUnion_famJoin B i j]
  refine MeasurableSet.iUnion fun f => ?_
  exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)

/-! ## The headline comparison (Ito's Lemma) -/

/-- **Ito's Lemma (two-family join-entropy comparison).** For two `Fin N`-families `β = (β_k)` and
`γ = (γ_k)` of finite measurable partitions of a probability space over a common cell-index type,
`H(⋁_k γ_k) ≤ H(⋁_k β_k) + ∑_k H(γ_k | β_k)`.

The proof is pure Shannon entropy: refinement monotonicity bounds `H(⋁γ)` by `H(⋁β ∨ ⋁γ)`; the
chain rule splits this as `H(⋁β) + H(⋁γ | ⋁β)`; conditional subadditivity over the family bounds
`H(⋁γ | ⋁β)` by `∑_k H(γ_k | ⋁β)`; and anti-monotonicity of conditioning (`⋁β` refines each `β_k`)
bounds each term by `H(γ_k | β_k)`. -/
theorem entropy_finJoin_le_add_sum_condEntropy [StandardBorelSpace X] [IsProbabilityMeasure μ]
    (β γ : Fin N → MeasurePartition μ ι) :
    entropy μ (finJoinCells (fun k => (γ k).cells))
      ≤ entropy μ (finJoinCells (fun k => (β k).cells))
        + ∑ k, condEntropyGivenPartition μ (β k).cells (γ k).cells := by
  have h𝒞 : generatedSigmaAlgebra μ (famJoin β) ≤ mX := generatedSigmaAlgebra_le (famJoin β)
  change entropy μ (famJoin γ).cells
      ≤ entropy μ (famJoin β).cells
        + ∑ k, condEntropyGivenPartition μ (β k).cells (γ k).cells
  calc entropy μ (famJoin γ).cells
      ≤ entropy μ (joinCells (famJoin β).cells (famJoin γ).cells) := by
        have h := entropy_le_entropy_join (famJoin γ) (famJoin β)
        rwa [entropy_joinCells_comm] at h
    _ = entropy μ (famJoin β).cells
          + condEntropyGivenPartition μ (famJoin β).cells (famJoin γ).cells :=
        entropy_join_eq_add_condEntropyGivenPartition (famJoin β) (famJoin γ)
    _ = entropy μ (famJoin β).cells
          + condEntropy μ (generatedSigmaAlgebra μ (famJoin β)) (famJoin γ).cells := by
        rw [condEntropyGivenPartition_eq_condEntropy_generated (famJoin β) (famJoin γ).cells
          (famJoin γ).measurable]
    _ ≤ entropy μ (famJoin β).cells
          + ∑ k, condEntropy μ (generatedSigmaAlgebra μ (famJoin β)) (γ k).cells := by
        gcongr
        exact condEntropy_famJoin_le h𝒞 γ
    _ ≤ entropy μ (famJoin β).cells
          + ∑ k, condEntropy μ (generatedSigmaAlgebra μ (β k)) (γ k).cells := by
        gcongr with k
        exact condEntropy_mono_of_le (generatedSigmaAlgebra_le_famJoin β k) h𝒞 (γ k)
    _ = entropy μ (famJoin β).cells
          + ∑ k, condEntropyGivenPartition μ (β k).cells (γ k).cells := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact (condEntropyGivenPartition_eq_condEntropy_generated (β k) (γ k).cells
          (γ k).measurable).symm

/-- **Difference form of Ito's Lemma.** The join-entropy gap is controlled by the summed
conditional entropies: `H(⋁_k γ_k) - H(⋁_k β_k) ≤ ∑_k H(γ_k | β_k)`. Immediate from
`entropy_finJoin_le_add_sum_condEntropy`. -/
theorem entropy_finJoin_sub_le_sum_condEntropy [StandardBorelSpace X] [IsProbabilityMeasure μ]
    (β γ : Fin N → MeasurePartition μ ι) :
    entropy μ (finJoinCells (fun k => (γ k).cells))
        - entropy μ (finJoinCells (fun k => (β k).cells))
      ≤ ∑ k, condEntropyGivenPartition μ (β k).cells (γ k).cells := by
  have h := entropy_finJoin_le_add_sum_condEntropy β γ
  linarith

end ErgodicTheory.Entropy
