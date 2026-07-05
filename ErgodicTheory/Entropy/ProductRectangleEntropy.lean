/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.FactorEntropy
import ErgodicTheory.Entropy.KSEntropyMono
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Frozen-factor product entropy: the rectangle partition

For a measure-preserving system `(X, T, μ)` and a probability space `(Y, ν)`, consider the
**frozen** product transformation `T × id` on `(X × Y, μ ⊗ ν)`. Given finite measurable partitions
`ξ` of `X` and `η` of `Y`, the *rectangle* partition `(fst⁻¹ ξ) ∨ (snd⁻¹ η)` of `X × Y` has cells
`ξᵢ × ηⱼ`. This file proves that the Kolmogorov–Sinai entropy of this rectangle partition relative
to `T × id` equals the base entropy of `ξ` relative to `T`:

`h((fst⁻¹ ξ) ∨ (snd⁻¹ η), T × id) = h(ξ, T)`  (`ksEntropyPartition_rectangle_eq`).

This is one component of the product-entropy upper bound `h(T × id) ≤ h(T)` (Walters, *An
Introduction to Ergodic Theory*, Theorem 4.23).

The proof is a sandwich.  The projection `fst : (X × Y, T × id) → (X, T)` is a factor map, so the
factor-relative invariance `factor_relative_eq` gives `h(fst⁻¹ ξ, T × id) = h(ξ, T)`.  Likewise
`snd : (X × Y, T × id) → (Y, id)` is a factor map, so `h(snd⁻¹ η, T × id) = h(η, id)`, and the
identity map has zero partition entropy (`ksEntropyPartition_id_eq_zero`).  Refinement monotonicity
`ksEntropyPartition_le_join` and join subadditivity `ksEntropyPartition_join_le` then squeeze:
`h(fst⁻¹ ξ) ≤ h(rect) ≤ h(fst⁻¹ ξ) + h(snd⁻¹ η) = h(ξ, T) + 0`.

## Main results

* `ErgodicTheory.Entropy.ksEntropySeq_id_of_pos`: for `n ≥ 1`, the `n`-fold iterated-join
  entropy under
  the identity map equals the static entropy `H(η)`.
* `ErgodicTheory.Entropy.ksEntropyPartition_id_eq_zero`: the identity map has zero
  partition entropy.
* `ErgodicTheory.Entropy.ksEntropyPartition_rectangle_eq`: the frozen-factor rectangle
  entropy equals
  the base entropy.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Theorem 4.23.
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

variable {Y : Type*} {κ : Type*} [MeasurableSpace Y] [Fintype κ]

/-- **Identity-map iterated-join entropy.** For `n ≥ 1`, the `n`-fold iterated-join entropy of a
partition `η` under the identity transformation equals the static Shannon entropy `H(η)`.

Under the identity, `Tᵏ = id`, so the cell of the iterated join at `f : Fin n → κ` collapses to
`⋂ₖ η_{f k}`.  For a non-constant `f` two coordinates pick almost-everywhere disjoint cells, so the
intersection is null and contributes `0`; for a constant `f ≡ j` (with `n ≥ 1`) the intersection is
`η_j`.  Summing over the constant indices recovers `H(η)`. -/
lemma ksEntropySeq_id_of_pos {ν : Measure Y} [IsProbabilityMeasure ν]
    (η : MeasurePartition ν κ) {n : ℕ} (hn : 1 ≤ n) :
    ksEntropySeq (MeasurePreserving.id ν) η n = entropy ν η.cells := by
  classical
  have hpos : 0 < n := hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  -- The id-iterated-join cell at `f` is `⋂ₖ η_{f k}`.
  have hcell : ∀ f : Fin n → κ,
      ksJoinCells η.cells id n f = ⋂ k : Fin n, η.cells (f k) := by
    intro f
    rw [ksJoinCells_apply]
    refine Set.iInter_congr fun k => ?_
    rw [Function.iterate_id, Set.preimage_id]
  rw [ksEntropySeq, ksJoin_cells, entropy_def, entropy_def]
  simp only [hcell]
  -- `c j` is the constant index `≡ j`.
  set c : κ → (Fin n → κ) := fun j _ => j with hc
  -- Non-constant indices contribute zero.
  have hvanish : ∀ f ∈ (Finset.univ : Finset (Fin n → κ)),
      f ∉ Finset.image c Finset.univ →
      Real.negMulLog (ν (⋂ k : Fin n, η.cells (f k))).toReal = 0 := by
    intro f _ hfS
    have hne : ∃ k₁ k₂ : Fin n, f k₁ ≠ f k₂ := by
      by_contra hcon
      simp only [not_exists, ne_eq, not_not] at hcon
      refine hfS (Finset.mem_image.mpr ⟨f ⟨0, hpos⟩, Finset.mem_univ _, ?_⟩)
      funext k
      simp only [hc]
      exact hcon ⟨0, hpos⟩ k
    obtain ⟨k₁, k₂, hk⟩ := hne
    have hsub : (⋂ k : Fin n, η.cells (f k)) ⊆ η.cells (f k₁) ∩ η.cells (f k₂) :=
      Set.subset_inter (Set.iInter_subset _ k₁) (Set.iInter_subset _ k₂)
    have hzero : ν (η.cells (f k₁) ∩ η.cells (f k₂)) = 0 := η.aedisjoint hk
    rw [measure_mono_null hsub hzero]
    simp
  -- Injectivity of the constant-index embedding (using `n ≥ 1`).
  have hinj : Set.InjOn c (↑(Finset.univ : Finset κ)) := by
    intro x _ y _ hxy
    simpa [hc] using congrFun hxy ⟨0, hpos⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.image c Finset.univ)) hvanish,
    Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcj : (⋂ k : Fin n, η.cells (c j k)) = η.cells j := by
    simp only [hc, Set.iInter_const]
  rw [hcj]

/-- **The identity map has zero partition entropy.** The iterated-join entropy sequence is
eventually the constant `H(η)` (`ksEntropySeq_id_of_pos`), so dividing by `n` and passing to the
Fekete limit gives `0`. -/
lemma ksEntropyPartition_id_eq_zero {ν : Measure Y} [IsProbabilityMeasure ν]
    (η : MeasurePartition ν κ) :
    ksEntropyPartition (MeasurePreserving.id ν) η = 0 := by
  have hlim : Tendsto (fun n : ℕ => entropy ν η.cells / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (entropy ν η.cells)
  have hev : (fun n : ℕ => ksEntropySeq (MeasurePreserving.id ν) η n / (n : ℝ))
      =ᶠ[atTop] (fun n : ℕ => entropy ν η.cells / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [ksEntropySeq_id_of_pos η hn]
  exact tendsto_nhds_unique (tendsto_ksEntropySeq (MeasurePreserving.id ν) η)
    (Filter.Tendsto.congr' hev.symm hlim)

/-- **Frozen-factor rectangle entropy.** Let `(X, T, μ)` be a measure-preserving system and `(Y, ν)`
a probability space.  For finite measurable partitions `ξ` of `X` and `η` of `Y`, the
Kolmogorov–Sinai entropy of the rectangle partition `(fst⁻¹ ξ) ∨ (snd⁻¹ η)` relative to the frozen
product `T × id` equals the base entropy of `ξ` relative to `T`:
`h((fst⁻¹ ξ) ∨ (snd⁻¹ η), T × id) = h(ξ, T)`.

The two projections `fst` and `snd` are factor maps of the frozen system, so by
`factor_relative_eq` the pulled-back partitions have entropies `h(ξ, T)` and `h(η, id) = 0`
(`ksEntropyPartition_id_eq_zero`); refinement monotonicity and join subadditivity then sandwich the
rectangle entropy between `h(ξ, T)` and `h(ξ, T) + 0`. -/
theorem ksEntropyPartition_rectangle_eq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : X → X} (hT : MeasurePreserving T μ μ) {ι : Type*} [Fintype ι]
    (ξ : MeasurePartition μ ι) (η : MeasurePartition ν κ) :
    ksEntropyPartition (hT.prod (MeasurePreserving.id ν))
        (joinPartition (ξ.pulledBack (measurePreserving_fst (μ := μ) (ν := ν)))
          (η.pulledBack (measurePreserving_snd (μ := μ) (ν := ν))))
      = ksEntropyPartition hT ξ := by
  set hfst := measurePreserving_fst (μ := μ) (ν := ν) with hfst_def
  set hsnd := measurePreserving_snd (μ := μ) (ν := ν) with hsnd_def
  set hidν := MeasurePreserving.id ν with hidν_def
  set hTν := hT.prod hidν with hTν_def
  set ξpb := ξ.pulledBack hfst with hξpb
  set ηpb := η.pulledBack hsnd with hηpb
  -- `fst` is a factor map `(T × id) → T`, giving `h(fst⁻¹ ξ, T × id) = h(ξ, T)`.
  have hξ : ksEntropyPartition hTν ξpb = ksEntropyPartition hT ξ := by
    rw [hξpb]
    exact factor_relative_eq hTν hT hfst (funext fun p => rfl) ξ
  -- `snd` is a factor map `(T × id) → id`, giving `h(snd⁻¹ η, T × id) = h(η, id) = 0`.
  have hη : ksEntropyPartition hTν ηpb = 0 := by
    rw [hηpb, factor_relative_eq hTν hidν hsnd (funext fun p => rfl) η, hidν_def]
    exact ksEntropyPartition_id_eq_zero η
  -- Sandwich: refinement ≥, subadditivity ≤.
  have hlow : ksEntropyPartition hTν ξpb
      ≤ ksEntropyPartition hTν (joinPartition ξpb ηpb) :=
    ksEntropyPartition_le_join hTν ξpb ηpb
  have hup : ksEntropyPartition hTν (joinPartition ξpb ηpb)
      ≤ ksEntropyPartition hTν ξpb + ksEntropyPartition hTν ηpb :=
    ksEntropyPartition_join_le hTν ξpb ηpb
  rw [hη, add_zero] at hup
  have heq : ksEntropyPartition hTν (joinPartition ξpb ηpb) = ksEntropyPartition hTν ξpb :=
    le_antisymm hup hlow
  rw [heq, hξ]

end ErgodicTheory.Entropy
