/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.BernoulliTwoSided
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The past ⊗ future product structure of the two-sided Bernoulli measure

The exact local product structure of the two-sided Bernoulli measure: `bernZ ν = past ⊗ future`.
This is the reason the Katok–Hasselblatt 19.2.4 absolutely-continuous-holonomy hypothesis is
*free* for the Bernoulli measure — its conditional measures on the local stable/unstable sets are
literally product marginals, so the holonomy maps preserve the conditional class by construction
(GitHub issue #34, step W2).

Concretely, splitting the index set `ℤ = {j < 0} ⊔ {0 ≤ j}` into the *past* and the *future*
identifies the bi-infinite shift space with a product `BiShift α₀ ≃ᵐ Past α₀ × Future α₀`
(`prodSplit`, via `MeasurableEquiv.piEquivPiSubtypeProd`), and under this identification the
i.i.d. measure factorizes:

* `map_joinPF_bernZ`: the joining map `joinPF : Past α₀ × Future α₀ → BiShift α₀` pushes the
  product `bernPast ν ⊗ bernFuture ν` forward to `bernZ ν`;
* `measurePreserving_joinPF`: the corresponding `MeasurePreserving` package.

For the stable-oscillation glue of the unbounded measurable Livšic tier we also record the
*pair-space* marginals: over `stablePairMeasure ν = (bernPast ν ⊗ bernPast ν) ⊗ bernFuture ν`,
each of the two joined coordinate maps `stableFst`, `stableSnd` — pairing one of the two pasts
with the shared future — is measure preserving onto `bernZ ν`
(`measurePreserving_stableFst`, `measurePreserving_stableSnd`), and the two agree on the
non-negative (future) coordinates (`stableFst_stableSnd_eq_on_nonneg`).

Finally we transplant the *complement form of reverse Fatou* `measure_not_frequently_le`: in any
measure space, if each event `A n` misses at most mass `c`, then the set of points that visit the
`A n` only finitely often has mass at most `c`. This is the finite-measure replacement for the
Birkhoff density of returns in the stable-oscillation argument (no ENNReal subtraction needed).
-/

open MeasureTheory Function Set Filter
open scoped ENNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- The past index set: the strictly negative integers. -/
abbrev NegZ : Type := {j : ℤ // j < 0}
/-- The future index set: the non-negative integers. -/
abbrev NonnegZ : Type := {j : ℤ // ¬ j < 0}

/-- Past component space (coordinates `j < 0`). -/
abbrev Past (α₀ : Type*) : Type _ := ∀ _ : NegZ, α₀
/-- Future component space (coordinates `0 ≤ j`). -/
abbrev Future (α₀ : Type*) : Type _ := ∀ _ : NonnegZ, α₀

/-- The Bernoulli (i.i.d.) measure on the past. -/
noncomputable def bernPast (ν : Measure α₀) : Measure (Past α₀) :=
  Measure.infinitePi (fun _ : NegZ => ν)

/-- The Bernoulli (i.i.d.) measure on the future. -/
noncomputable def bernFuture (ν : Measure α₀) : Measure (Future α₀) :=
  Measure.infinitePi (fun _ : NonnegZ => ν)

instance (ν : Measure α₀) [IsProbabilityMeasure ν] : IsProbabilityMeasure (bernPast ν) := by
  unfold bernPast; infer_instance

instance (ν : Measure α₀) [IsProbabilityMeasure ν] : IsProbabilityMeasure (bernFuture ν) := by
  unfold bernFuture; infer_instance

/-- The splitting measurable equivalence `BiShift α₀ ≃ᵐ Past α₀ × Future α₀`, obtained by
partitioning the index set `ℤ` into the negative (past) and non-negative (future) coordinates. -/
noncomputable def prodSplit : BiShift α₀ ≃ᵐ (Past α₀ × Future α₀) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℤ => α₀) (fun j => j < 0)

/-- The joining map `joinPF : Past α₀ × Future α₀ → BiShift α₀`, the inverse of `prodSplit`. -/
noncomputable def joinPF : Past α₀ × Future α₀ → BiShift α₀ :=
  (prodSplit (α₀ := α₀)).symm

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
theorem joinPF_apply (f : Past α₀) (g : Future α₀) (j : ℤ) :
    joinPF (f, g) j = if h : j < 0 then f ⟨j, h⟩ else g ⟨j, h⟩ := rfl

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **Product structure of the two-sided Bernoulli measure**: the joining map pushes
`bernPast ν ⊗ bernFuture ν` forward to `bernZ ν`. -/
theorem map_joinPF_bernZ (ν : Measure α₀) [IsProbabilityMeasure ν] :
    Measure.map (joinPF (α₀ := α₀)) ((bernPast ν).prod (bernFuture ν)) = bernZ ν := by
  classical
  rw [bernZ]
  refine Measure.eq_infinitePi (μ := fun _ : ℤ => ν) ?_
  intro s t ht
  have hbox : MeasurableSet (Set.pi (↑s) t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  -- the preimage of a box splits into a rectangle of sub-boxes
  have hpre : joinPF (α₀ := α₀) ⁻¹' (Set.pi (↑s) t)
      = (Set.pi (↑(s.subtype (fun j => j < 0))) (fun j => t j.val)) ×ˢ
        (Set.pi (↑(s.subtype (fun j => ¬ j < 0))) (fun j => t j.val)) := by
    ext ⟨f, g⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_subtype, joinPF_apply]
    constructor
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · have := h j.val hj
        rwa [dif_pos j.prop] at this
      · have := h j.val hj
        rwa [dif_neg j.prop] at this
    · rintro ⟨h1, h2⟩ j hj
      by_cases hneg : j < 0
      · rw [dif_pos hneg]
        exact h1 ⟨j, hneg⟩ hj
      · rw [dif_neg hneg]
        exact h2 ⟨j, hneg⟩ hj
  have hmeas : Measurable (joinPF (α₀ := α₀)) := (prodSplit (α₀ := α₀)).symm.measurable
  rw [Measure.map_apply hmeas hbox, hpre, Measure.prod_prod, bernPast, bernFuture,
    Measure.infinitePi_pi (μ := fun _ : NegZ => ν) (fun j _ => ht j.val),
    Measure.infinitePi_pi (μ := fun _ : NonnegZ => ν) (fun j _ => ht j.val)]
  -- recombine the two subtype products into the product over `s`
  have h1 : (∏ x ∈ s.subtype (fun j : ℤ => j < 0), ν (t ↑x))
      = ∏ j ∈ s.filter (fun j : ℤ => j < 0), ν (t j) := by
    rw [← Finset.subtype_map, Finset.prod_map]
    simp
  have h2 : (∏ x ∈ s.subtype (fun j : ℤ => ¬ j < 0), ν (t ↑x))
      = ∏ j ∈ s.filter (fun j : ℤ => ¬ j < 0), ν (t j) := by
    rw [← Finset.subtype_map, Finset.prod_map]
    simp
  rw [h1, h2]
  simpa using Finset.prod_filter_mul_prod_filter_not s (fun j => j < 0) (fun j => ν (t j))

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The `MeasurePreserving` package for the joining map: `joinPF` sends the past ⊗ future product
measure to `bernZ ν`. -/
theorem measurePreserving_joinPF (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (joinPF (α₀ := α₀)) ((bernPast ν).prod (bernFuture ν)) (bernZ ν) :=
  ⟨(prodSplit (α₀ := α₀)).symm.measurable, map_joinPF_bernZ ν⟩

/-! ### Pair-space marginals -/

/-- The stable-pair space: two independent pasts sharing one common future. -/
abbrev StablePairs (α₀ : Type*) : Type _ := (Past α₀ × Past α₀) × Future α₀

/-- The stable-pair measure `(bernPast ν ⊗ bernPast ν) ⊗ bernFuture ν`. -/
noncomputable def stablePairMeasure (ν : Measure α₀) : Measure (StablePairs α₀) :=
  ((bernPast ν).prod (bernPast ν)).prod (bernFuture ν)

instance (ν : Measure α₀) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (stablePairMeasure ν) := by
  unfold stablePairMeasure; infer_instance

/-- First marginal of a stable pair: join the first past with the shared future. -/
noncomputable def stableFst : StablePairs α₀ → BiShift α₀ := fun w => joinPF (w.1.1, w.2)

/-- Second marginal of a stable pair: join the second past with the shared future. -/
noncomputable def stableSnd : StablePairs α₀ → BiShift α₀ := fun w => joinPF (w.1.2, w.2)

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The first stable-pair marginal map is measure preserving onto `bernZ ν`. -/
theorem measurePreserving_stableFst (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (stableFst (α₀ := α₀)) (stablePairMeasure ν) (bernZ ν) := by
  have h1 : MeasurePreserving (Prod.map (Prod.fst : Past α₀ × Past α₀ → Past α₀)
      (id : Future α₀ → Future α₀))
      (((bernPast ν).prod (bernPast ν)).prod (bernFuture ν))
      ((bernPast ν).prod (bernFuture ν)) :=
    (measurePreserving_fst (μ := bernPast ν) (ν := bernPast ν)).prod
      (MeasurePreserving.id (bernFuture ν))
  exact (measurePreserving_joinPF ν).comp h1

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The second stable-pair marginal map is measure preserving onto `bernZ ν`. -/
theorem measurePreserving_stableSnd (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (stableSnd (α₀ := α₀)) (stablePairMeasure ν) (bernZ ν) := by
  have h1 : MeasurePreserving (Prod.map (Prod.snd : Past α₀ × Past α₀ → Past α₀)
      (id : Future α₀ → Future α₀))
      (((bernPast ν).prod (bernPast ν)).prod (bernFuture ν))
      ((bernPast ν).prod (bernFuture ν)) :=
    (measurePreserving_snd (μ := bernPast ν) (ν := bernPast ν)).prod
      (MeasurePreserving.id (bernFuture ν))
  exact (measurePreserving_joinPF ν).comp h1

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The two marginals of a stable pair share their non-negative (future) coordinates. -/
theorem stableFst_stableSnd_eq_on_nonneg (w : StablePairs α₀) (j : ℤ) (hj : 0 ≤ j) :
    stableFst w j = stableSnd w j := by
  simp only [stableFst, stableSnd, joinPF_apply, dif_neg (not_lt.mpr hj)]

/-! ### Reverse Fatou for sets (complement form) -/

/-- **Reverse Fatou, complement form.** If each event `A n` misses at most mass `c`, then the set
of points that visit the `A n` only finitely often (equivalently, that fail to be in some `A N`
for arbitrarily large `N`) has mass at most `c`. This is the finite-measure replacement for the
Birkhoff density of returns; it needs no `ENNReal` subtraction. -/
theorem measure_not_frequently_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Set Ω} {c : ℝ≥0∞} (hc : ∀ n, μ (A n)ᶜ ≤ c) :
    μ {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N} ≤ c := by
  have hset : {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N}
      = ⋃ N₀ : ℕ, ⋂ N, ⋂ (_ : N₀ ≤ N), (A N)ᶜ := by
    ext w
    simp only [Set.mem_setOf_eq, not_forall, not_exists, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_compl_iff, not_and]
  rw [hset]
  have hmono : Monotone (fun N₀ : ℕ => ⋂ N, ⋂ (_ : N₀ ≤ N), (A N)ᶜ) := by
    intro a b hab
    exact Set.iInter₂_mono' fun N hN => ⟨N, le_trans hab hN, subset_refl _⟩
  have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
  refine le_of_tendsto htend ?_
  filter_upwards with N₀
  have hsub : (⋂ N, ⋂ (_ : N₀ ≤ N), (A N)ᶜ) ⊆ (A N₀)ᶜ := fun w hw => by
    have := Set.mem_iInter.1 hw N₀
    exact Set.mem_iInter.1 this le_rfl
  exact le_trans (measure_mono hsub) (hc N₀)

end ErgodicTheory
