/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondKSEntropyCondBound
import ErgodicTheory.Entropy.ProductIdEntropy
import ErgodicTheory.Entropy.CondEntropyContinuous
import ErgodicTheory.Entropy.CondKSEntropySystem
import ErgodicTheory.Entropy.GeneratorTheorem
import ErgodicTheory.Entropy.GeneratorTheoremTwoSided
import ErgodicTheory.Entropy.FactorGeneratorSaturate
import ErgodicTheory.Entropy.CondGivenPartitionBridge

/-!
# Conditional frozen-factor product entropy: `h(T × id | base) = 0`

This module is the **conditional analog** of `ErgodicTheory.Entropy.ProductIdEntropy`
(`ksEntropy_prod_id_eq : h(T × id) = h(T)`). Conditioning on the base factor
`baseFactor = comap Prod.fst mX`, the relative Kolmogorov–Sinai entropy of the frozen product
`T × id` on `(X × Y, μ ⊗ ν)` vanishes:

`h(T × id | comap fst mX) = 0`  (`ErgodicTheory.Entropy.condKsEntropy_prod_id_eq_zero`).

The argument mirrors the absolute upper bound but with the conditional Le Maître inequality
(`condKsEntropyPartition_le_add_condEntropy`) in place of the absolute one:

* **B** (`condKsEntropyPartition_prodBPart_eq_zero`): for the rectangle partition
  `rectₘ = ξₘ ⊠ ηₘ`, `h(rectₘ, T × id | baseFactor) = 0`. The conditional Le Maître inequality with
  the *frozen* partition `snd⁻¹ ηₘ` as comparison splits `h(rectₘ, · | baseFactor)` into the frozen
  factor's relative entropy (zero, since `snd` is a factor onto the identity system and conditioning
  only decreases entropy) plus the defect `H(rectₘ | σ(snd⁻¹ ηₘ) ⊔ baseFactor)`, which vanishes
  because every cell of `rectₘ` is `σ(snd⁻¹ ηₘ) ⊔ baseFactor`-measurable.
* **C** (`tendsto_condEntropy_prodBPart_sup_zero`): the static conditional entropy of any finite
  partition `P` given the growing σ-algebra `σ(rectₘ) ⊔ baseFactor` tends to `0`, by Lévy-upward
  continuity (`condEntropy_tendsto_iSup`), since `σ(rectₘ)` saturates the product σ-algebra.
* **D** (`condKsEntropy_prod_id_eq_zero`): assembling B and C through the conditional Le Maître
  inequality squeezes each partition-relative conditional entropy to `0`; the `EReal` supremum over
  partitions is then `0`.

## Main results

* `ErgodicTheory.Entropy.condKsEntropyPartition_le_ksEntropyPartition`: conditioning does not increase
  the relative Kolmogorov–Sinai entropy.
* `ErgodicTheory.Entropy.condKsEntropyPartition_prodBPart_eq_zero`: the conditional rectangle entropy
  vanishes (B).
* `ErgodicTheory.Entropy.tendsto_condEntropy_prodBPart_sup_zero`: the conditional defect tends to `0`
  (C).
* `ErgodicTheory.Entropy.condKsEntropy_prod_id_eq_zero`: `h(T × id | comap fst mX) = 0` (D).

## References

* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Theorem 4.23.
* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1–2.
-/

open MeasureTheory Function Filter Topology ProbabilityTheory
open scoped ENNReal

namespace ErgodicTheory.Entropy

section CondLe

variable {α : Type*} {ιe : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α] [Fintype ιe]

/-- **Conditioning does not increase the relative Kolmogorov–Sinai entropy:**
`h(α, T | 𝒜) ≤ h(α, T)`. Termwise the conditional iterated-join entropy is bounded by the absolute
one (`condEntropy_le`, conditioning only decreases Shannon entropy); dividing by `n` and passing
both Fekete limits transfers the inequality. -/
lemma condKsEntropyPartition_le_ksEntropyPartition {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜) (P : MeasurePartition μ ιe) :
    condKsEntropyPartition hm hT hinv P ≤ ksEntropyPartition hT P := by
  refine le_of_tendsto_of_tendsto' (tendsto_condKsEntropySeq hm hT hinv P)
    (tendsto_ksEntropySeq hT P) (fun n => ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (condEntropy_le hm (ksJoin hT P n))
    (inv_nonneg.mpr (Nat.cast_nonneg n))

end CondLe

section CondProductId

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X]
  [StandardBorelSpace Y] {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {T : X → X}

/-- The base-factor σ-algebra on the product, `comap fst mX`. -/
abbrev baseFactor : MeasurableSpace (X × Y) :=
  MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace X)

/-- **B (frozen-rectangle vanishing).** For the `Fin`-indexed rectangle `prodBPart μ ν m`,
`h(rectₘ, T × id | comap fst mX) = 0`. The conditional Le Maître inequality with the frozen
partition `snd⁻¹ ηₘ` as comparison gives `h(rectₘ | baseFactor) ≤ h(snd⁻¹ ηₘ | baseFactor) +
H(rectₘ | σ(snd⁻¹ ηₘ) ⊔ baseFactor)`; the first summand is `0` (the frozen factor is a factor onto
the identity, conditioning only decreases entropy) and the defect is `0` (every cell of `rectₘ` is
`σ(snd⁻¹ ηₘ) ⊔ baseFactor`-measurable). -/
theorem condKsEntropyPartition_prodBPart_eq_zero
    (hT : MeasurePreserving T μ μ)
    (hm : (baseFactor (X := X) (Y := Y)) ≤ (inferInstance : MeasurableSpace (X × Y)))
    (hinv : MeasurableSpace.comap (Prod.map T (id : Y → Y)) (baseFactor (X := X) (Y := Y))
      ≤ baseFactor (X := X) (Y := Y))
    (m : ℕ) :
    condKsEntropyPartition hm (hT.prod (MeasurePreserving.id ν)) hinv (prodBPart μ ν m) = 0 := by
  set hsnd := measurePreserving_snd (μ := μ) (ν := ν) with hsnd_def
  set P' := (cgPart Y ν m).pulledBack hsnd with hP'_def
  refine le_antisymm ?_
    (condKsEntropyPartition_nonneg hm (hT.prod (MeasurePreserving.id ν)) hinv (prodBPart μ ν m))
  -- The frozen factor `snd⁻¹ ηₘ` has zero relative conditional entropy.
  have hfrozen : condKsEntropyPartition hm (hT.prod (MeasurePreserving.id ν)) hinv P' = 0 := by
    refine le_antisymm ?_
      (condKsEntropyPartition_nonneg hm (hT.prod (MeasurePreserving.id ν)) hinv P')
    calc condKsEntropyPartition hm (hT.prod (MeasurePreserving.id ν)) hinv P'
        ≤ ksEntropyPartition (hT.prod (MeasurePreserving.id ν)) P' :=
          condKsEntropyPartition_le_ksEntropyPartition hm (hT.prod (MeasurePreserving.id ν))
            hinv P'
      _ = ksEntropyPartition (MeasurePreserving.id ν) (cgPart Y ν m) := by
          rw [hP'_def]
          exact factor_relative_eq (hT.prod (MeasurePreserving.id ν)) (MeasurePreserving.id ν)
            hsnd (funext fun p => rfl) (cgPart Y ν m)
      _ = 0 := ksEntropyPartition_id_eq_zero (cgPart Y ν m)
  -- The defect `H(rectₘ | σ(snd⁻¹ ηₘ) ⊔ baseFactor)` vanishes by measurability.
  have hdefect : condEntropy (μ.prod ν)
      (generatedSigmaAlgebra (μ.prod ν) P' ⊔ baseFactor) (prodBPart μ ν m).cells = 0 := by
    have hσY : generatedSigmaAlgebra (μ.prod ν) P'
        = MeasurableSpace.comap Prod.snd
            (MeasurableSpace.generateFrom (MeasurableSpace.countablePartition Y m)) := by
      rw [hP'_def, comap_generatedSigmaAlgebra_pulledBack hsnd (cgPart Y ν m),
        generatedSigmaAlgebra_cgPart Y ν m]
    have hσX : MeasurableSpace.generateFrom (MeasurableSpace.countablePartition X m)
        ≤ (inferInstance : MeasurableSpace X) := by
      rw [← generatedSigmaAlgebra_cgPart X μ m]
      exact generatedSigmaAlgebra_le _
    have hfst_le : MeasurableSpace.comap Prod.fst
        (MeasurableSpace.generateFrom (MeasurableSpace.countablePartition X m))
        ≤ baseFactor (X := X) (Y := Y) := MeasurableSpace.comap_mono hσX
    have hle : generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν m)
        ≤ generatedSigmaAlgebra (μ.prod ν) P' ⊔ baseFactor := by
      rw [generatedSigmaAlgebra_prodBPart_eq μ ν m, hσY]
      exact sup_le (le_sup_of_le_right hfst_le) le_sup_left
    refine condEntropy_eq_zero_of_measurable (sup_le (generatedSigmaAlgebra_le P') hm)
      (prodBPart μ ν m) (fun i => ?_)
    exact hle _ (measurableSet_generatedSigmaAlgebra_cell (prodBPart μ ν m) i)
  -- Assemble through the conditional Le Maître inequality.
  have hA2 := condKsEntropyPartition_le_add_condEntropy hm (hT.prod (MeasurePreserving.id ν)) hinv
    (prodBPart μ ν m) P'
  rwa [hfrozen, hdefect, zero_add] at hA2

/-- **C (defect → 0).** The static conditional Shannon entropy of any finite partition `P` given the
joined σ-algebra `σ(rectₘ) ⊔ comap fst mX` tends to `0`: `σ(rectₘ)` saturates the product σ-algebra
(`generatedSigmaAlgebra_prodBPart_iSup`), so the join saturates the full σ-algebra; Lévy-upward
continuity (`condEntropy_tendsto_iSup`) and `condEntropy_full_eq_zero` finish. -/
theorem tendsto_condEntropy_prodBPart_sup_zero {n : ℕ}
    (P : MeasurePartition (μ.prod ν) (Fin n)) [Nonempty (Fin n)] :
    Tendsto (fun m => condEntropy (μ.prod ν)
        (generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν m) ⊔ baseFactor) P.cells)
      atTop (𝓝 0) := by
  have hbase : (baseFactor (X := X) (Y := Y)) ≤ (inferInstance : MeasurableSpace (X × Y)) :=
    measurable_iff_comap_le.mp measurable_fst
  have hmono : Monotone fun m =>
      generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν m) ⊔ baseFactor :=
    fun a b hab => sup_le_sup_right (generatedSigmaAlgebra_prodBPart_mono μ ν hab) baseFactor
  have hle : ∀ m, (generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν m) ⊔ baseFactor)
      ≤ (inferInstance : MeasurableSpace (X × Y)) :=
    fun m => sup_le (generatedSigmaAlgebra_le _) hbase
  have hsup : (⨆ m, generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν m) ⊔ baseFactor)
      = (inferInstance : MeasurableSpace (X × Y)) := by
    rw [iSup_sup_eq, iSup_const, generatedSigmaAlgebra_prodBPart_iSup μ ν]
    exact sup_eq_left.mpr hbase
  have hlim := condEntropy_tendsto_iSup
    (fun m => generatedSigmaAlgebra (μ.prod ν) (prodBPart μ ν m) ⊔ baseFactor) hmono hle P
  rw [hsup, condEntropy_full_eq_zero] at hlim
  exact hlim

/-- **D (assembly).** `h(T × id | comap fst mX) = 0`. Each partition-relative conditional entropy is
squeezed to `0` by the conditional Le Maître inequality (`≤ h(rectₘ, · | baseFactor) + defectₘ`), B
(first term `= 0`) and C (defect → 0); the `EReal` supremum over partitions is then `0`. -/
theorem condKsEntropy_prod_id_eq_zero (hT : MeasurePreserving T μ μ)
    (hm : (baseFactor (X := X) (Y := Y)) ≤ (inferInstance : MeasurableSpace (X × Y)))
    (hinv : MeasurableSpace.comap (Prod.map T (id : Y → Y)) (baseFactor (X := X) (Y := Y))
      ≤ baseFactor (X := X) (Y := Y)) :
    condKsEntropy hm (hT.prod (MeasurePreserving.id ν)) hinv = 0 := by
  refine le_antisymm ?_ (condKsEntropy_nonneg hm (hT.prod (MeasurePreserving.id ν)) hinv)
  have hexp : condKsEntropy hm (hT.prod (MeasurePreserving.id ν)) hinv
      = ⨆ n : ℕ, ⨆ P : MeasurePartition (μ.prod ν) (Fin n),
          ((condKsEntropyPartition hm (hT.prod (MeasurePreserving.id ν)) hinv P : ℝ) : EReal) :=
    rfl
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
    have hreal : condKsEntropyPartition hm (hT.prod (MeasurePreserving.id ν)) hinv P ≤ 0 := by
      refine ge_of_tendsto' (tendsto_condEntropy_prodBPart_sup_zero P) (fun m => ?_)
      have hA2 := condKsEntropyPartition_le_add_condEntropy hm
        (hT.prod (MeasurePreserving.id ν)) hinv P (prodBPart μ ν m)
      rwa [condKsEntropyPartition_prodBPart_eq_zero hT hm hinv m, zero_add] at hA2
    calc ((condKsEntropyPartition hm (hT.prod (MeasurePreserving.id ν)) hinv P : ℝ) : EReal)
        ≤ ((0 : ℝ) : EReal) := EReal.coe_le_coe hreal
      _ = 0 := EReal.coe_zero

end CondProductId

end ErgodicTheory.Entropy
