/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.SymbolicDimensionBernoulli

/-!
# The two-sided Bernoulli foundation: an invertible shift base

The suspension/flow construction (`ErgodicTheory/Continuous/Suspension*.lean`) requires an
**invertible** base automorphism `T : X ≃ᵐ X`. The on-`main` one-sided Bernoulli shift
(`ErgodicTheory/Multifractal/SymbolicDimensionBernoulli.lean`) is *non*-invertible. This file
builds the
two-sided analogue: the full shift over the index type `ℤ`, equipped with the i.i.d. (Bernoulli)
product measure, with the left shift packaged as a `MeasurableEquiv`.

The construction mirrors the one-sided foundation node for node, over `ℤ` instead of `ℕ`.

* **The bi-infinite shift space** `BiShift α₀ := ∀ _ : ℤ, α₀` with its product `MeasurableSpace`.
* **The shift map** `biShiftMap x n = x (n + 1)` and its measurability.
* **The invertible shift** `biShiftEquiv : BiShift α₀ ≃ᵐ BiShift α₀`, built as an explicit
  `MeasurableEquiv.mk`: the forward map `n ↦ x (n + 1)`, the inverse `n ↦ x (n - 1)`, with the two
  round-trip identities closing by `(n + 1) - 1 = n` and `(n - 1) + 1 = n` on `ℤ`.
* **The Bernoulli measure** `bernZ ν := Measure.infinitePi (fun _ : ℤ => ν)`, a probability measure.
* **Measure preservation** `measurePreserving_biShiftEquiv_bernZ`: the shift preserves `bernZ ν`,
  proved exactly as in the one-sided case (`preimage_biShiftMap_pi` re-indexes a box by `n ↦ n + 1`,
  then both sides evaluate by `infinitePi_pi` to the same finite product of `ν`-masses).
* **Cylinder mass** `bernZ_pi_eq_prod`: the cylinder-mass factorization
  `bernZ ν (Set.pi ↑s t) = ∏ i ∈ s, ν (t i)`, the key handle for the entropy identification.
* **The coordinate-`0` partition** `coordPartitionZ`.

The single-symbol Shannon entropy `Hnu` (alphabet-only) is reused unchanged from the one-sided
file; there is deliberately no two-sided `HnuZ`.
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

namespace ErgodicTheory.Multifractal

open ErgodicTheory.Entropy

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-! ### The bi-infinite shift space and the shift map -/

/-- The **two-sided full shift space** over the alphabet `α₀`: bi-infinite sequences `ℤ → α₀`. It
carries the product `MeasurableSpace`. -/
abbrev BiShift (α₀ : Type*) : Type _ := ∀ _ : ℤ, α₀

/-- The **left shift map** on the two-sided full shift: `(biShiftMap x) n = x (n + 1)`. -/
def biShiftMap : BiShift α₀ → BiShift α₀ := fun x n => x (n + 1)

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The two-sided shift map is measurable: each output coordinate is a measurable coordinate
projection of the input. -/
theorem measurable_biShiftMap : Measurable (biShiftMap (α₀ := α₀)) :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

/-! ### The invertible shift -/

/-- The **invertible left shift** on the two-sided full shift, as a `MeasurableEquiv`. The forward
map is `n ↦ x (n + 1)` and the inverse is `n ↦ x (n - 1)`; on `ℤ` the round trips close by
`(n + 1) - 1 = n` and `(n - 1) + 1 = n`. -/
def biShiftEquiv : BiShift α₀ ≃ᵐ BiShift α₀ where
  toEquiv :=
    { toFun := fun x n => x (n + 1)
      invFun := fun x n => x (n - 1)
      left_inv := fun x => funext fun n => by simp
      right_inv := fun x => funext fun n => by simp }
  measurable_toFun := measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)
  measurable_invFun := measurable_pi_lambda _ fun n => measurable_pi_apply (n - 1)

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
@[simp]
theorem biShiftEquiv_apply (x : BiShift α₀) : biShiftEquiv x = biShiftMap x := rfl

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The coercion of `biShiftEquiv` is definitionally the shift map `biShiftMap`. -/
theorem coe_biShiftEquiv : ⇑(biShiftEquiv (α₀ := α₀)) = biShiftMap := rfl

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
@[simp]
theorem biShiftEquiv_symm_apply (x : BiShift α₀) (n : ℤ) :
    (biShiftEquiv (α₀ := α₀)).symm x n = x (n - 1) := rfl

/-! ### The two-sided Bernoulli measure -/

/-- The **two-sided Bernoulli (i.i.d.) measure** on the full shift `BiShift α₀`: the infinite
product of the single-symbol law `ν` over all integer coordinates. -/
noncomputable def bernZ (ν : Measure α₀) : Measure (BiShift α₀) :=
  Measure.infinitePi (fun _ : ℤ => ν)

/-- The two-sided Bernoulli measure is a probability measure. (The global instance on `infinitePi`
does not fire through the `bernZ` definition, so it is provided explicitly.) -/
instance instIsProbabilityMeasureBernZ (ν : Measure α₀) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (bernZ ν) := by
  unfold bernZ; infer_instance

/-! ### Measure preservation -/

/-- The coordinate-shift embedding `n ↦ n + 1` of `ℤ` into itself. Used to re-index a measurable box
under the shift preimage. -/
def shiftEmbZ : ℤ ↪ ℤ := ⟨fun n => n + 1, fun a b h => by simpa using h⟩

omit [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀] in
/-- **Box preimage.** The `biShiftMap`-preimage of a measurable box `Set.pi ↑s t` is the box over
the re-indexed support `s.map shiftEmbZ` with the symbol sets shifted by one:
`biShiftMap ⁻¹' (Set.pi ↑s t) = Set.pi ↑(s.map shiftEmbZ) (fun n => t (n - 1))`. -/
theorem preimage_biShiftMap_pi (s : Finset ℤ) (t : ℤ → Set α₀) :
    biShiftMap (α₀ := α₀) ⁻¹' (Set.pi (↑s) t)
      = Set.pi (↑(s.map shiftEmbZ)) (fun n => t (n - 1)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Set.mem_image, Finset.mem_coe,
    shiftEmbZ, Function.Embedding.coeFn_mk, biShiftMap]
  constructor
  · rintro hx _ ⟨n, hn, rfl⟩
    rw [add_sub_cancel_right]
    exact hx n hn
  · intro hx n hn
    have h := hx (n + 1) ⟨n, hn, rfl⟩
    rwa [add_sub_cancel_right] at h

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **Measure preservation.** The invertible left shift preserves the two-sided Bernoulli measure
`bernZ ν`. The preimage of a box re-indexes by `n ↦ n + 1` (`preimage_biShiftMap_pi`); both sides
evaluate by `infinitePi_pi` to the same finite product of `ν`-masses, since every marginal is the
same `ν` and `Finset.prod_map` absorbs the injective reindex. -/
theorem measurePreserving_biShiftEquiv_bernZ (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (biShiftEquiv (α₀ := α₀)) (bernZ ν) (bernZ ν) where
  measurable := biShiftEquiv.measurable
  map_eq := by
    rw [coe_biShiftEquiv]
    change Measure.map biShiftMap (bernZ ν) = Measure.infinitePi (fun _ : ℤ => ν)
    refine Measure.eq_infinitePi (μ := fun _ : ℤ => ν) ?_
    intro s t ht
    have hbox : MeasurableSet (Set.pi (↑s) t) :=
      MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
    rw [Measure.map_apply measurable_biShiftMap hbox, preimage_biShiftMap_pi, bernZ,
      Measure.infinitePi_pi (μ := fun _ : ℤ => ν) (fun i _ => ht (i - 1)),
      Finset.prod_map s shiftEmbZ (fun i => ν (t (i - 1)))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [shiftEmbZ, Function.Embedding.coeFn_mk]
    congr 2
    omega

/-! ### Cylinder mass -/

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **Cylinder-mass factorization.** The two-sided Bernoulli mass of a measurable box `Set.pi ↑s t`
is the finite product of the single-symbol masses `ν (t i)` over the support `s`. This is the key
handle the entropy identification consumes. -/
theorem bernZ_pi_eq_prod (ν : Measure α₀) [IsProbabilityMeasure ν] (s : Finset ℤ)
    (t : ℤ → Set α₀) (ht : ∀ i, MeasurableSet (t i)) :
    bernZ ν (Set.pi (↑s) t) = ∏ i ∈ s, ν (t i) := by
  rw [bernZ, Measure.infinitePi_pi (μ := fun _ : ℤ => ν) (fun i _ => ht i)]

/-! ### The coordinate-`0` partition -/

/-- The **time-`0` coordinate partition** of the two-sided full shift: the cell at `i` is the set
`{x | x 0 = i}` of bi-infinite sequences whose `0`-th symbol is `i`. The cells are pairwise disjoint
and cover the whole space, so they form a genuine measurable partition. -/
def coordPartitionZ (ν : Measure (BiShift α₀)) : MeasurePartition ν α₀ where
  cells := fun i => {x | x 0 = i}
  measurable := fun i => by
    have : {x : BiShift α₀ | x 0 = i} = (fun x : BiShift α₀ => x 0) ⁻¹' {i} := by
      ext x; simp [Set.mem_preimage]
    rw [this]
    exact (measurable_pi_apply 0) (measurableSet_singleton i)
  aedisjoint := by
    intro i j hij
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_left]
    rintro x hx hx'
    rw [Set.mem_setOf_eq] at hx hx'
    exact hij (hx.symm.trans hx')
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact Set.mem_iUnion.mpr ⟨x 0, rfl⟩

end ErgodicTheory.Multifractal
