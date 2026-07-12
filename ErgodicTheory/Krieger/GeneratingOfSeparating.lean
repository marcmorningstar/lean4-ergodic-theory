/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.ZIterate
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Separating itineraries generate: a Blackwell-type bridge

This file records the generic measure-theoretic bridge from a **point-separating** itinerary to the
two-sided generating condition `ErgodicTheory.Krieger.IsGeneratingTwoSided` of Krieger's finite
generator theorem. It is entirely partition-independent: the only geometric input is that the
countable family of cell-preimages `{(T^n)⁻¹(P_i)}_{n : ℤ, i}` separates the points of the space.

## The statement

For a measurable automorphism `e : α ≃ᵐ α` of a **standard Borel** space and a finite measurable
partition `P`, if for every pair of distinct points `x ≠ y` some two-sided iterate `ziter e n`
sends `x` into a cell `P.cells i` that misses `ziter e n y`, then `P` is two-sided generating:
`⨆ n : ℤ, comap (ziter e n) σ(P) = mα`.

## Proof

The inclusion `⨆ n, comap (ziter e n) σ(P) ≤ mα` is automatic (each `ziter e n` is measurable and
each cell is measurable). For the reverse inclusion `mα ≤ m` we invoke **Blackwell's theorem** in
the form `Measurable.measurableEmbedding`: the identity map `id : (α, mα) → (α, m)` from the
ambient standard Borel structure to the coarser saturated structure `m` is measurable (`m ≤ mα`)
and injective, and its codomain `(α, m)` is countably separated — precisely by the separating
family of cell-preimages, each of which is `m`-measurable as a term of the `iSup`. Hence `id` is a
measurable embedding, so it carries `mα`-measurable sets to `m`-measurable sets, i.e. `mα ≤ m`.

The two σ-algebras `mα` and `m` on the *same* carrier `α` are kept apart by supplying the
countably-separated instance explicitly as an `@`-application to the Blackwell lemma, avoiding any
global instance clash.

## Main results

* `ErgodicTheory.Krieger.isGeneratingTwoSided_of_separating`: separating ⇒ two-sided generating.

## References

* David Blackwell, *On a class of probability spaces*, Proc. 3rd Berkeley Symp. (1956).
* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*, Trans. Amer.
  Math. Soc. **149** (1970), 453–464.
-/

open MeasureTheory Function MeasurableSpace

namespace ErgodicTheory.Krieger

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α]
  {μ : Measure α} [Fintype ι]

/-- **Separating ⇒ two-sided generating.** If the two-sided iterates of `e` sweep the cells of a
finite partition `P` into a family that separates points, then `P` is two-sided generating for `e`.
This is the partition-independent bridge underlying the finite-generator half of a two-sided
Kolmogorov–Sinai computation: it converts the *dynamical separation* of points (a pointwise, purely
combinatorial statement about itineraries) into the *σ-algebraic* generating hypothesis
`IsGeneratingTwoSided`. -/
theorem isGeneratingTwoSided_of_separating (e : α ≃ᵐ α) (P : Entropy.MeasurePartition μ ι)
    (hsep : ∀ x y : α, x ≠ y →
      ∃ (n : ℤ) (i : ι), ziter e n x ∈ P.cells i ∧ ziter e n y ∉ P.cells i) :
    IsGeneratingTwoSided e P := by
  -- Each generating cell is `mα`-measurable, hence `σ(P) ≤ mα`.
  have hgen_le : Entropy.generatedSigmaAlgebra μ P ≤ mα :=
    generateFrom_le (by rintro _ ⟨i, rfl⟩; exact P.measurable i)
  -- The saturated σ-algebra `m` is written out inline everywhere below: naming it via `set`/`let`
  -- would register it as a *local instance* of `MeasurableSpace α`, shadowing the ambient `mα`.
  change (⨆ n : ℤ, MeasurableSpace.comap (ziter e n) (Entropy.generatedSigmaAlgebra μ P)) = mα
  -- Direction 1: `m ≤ mα`.
  have hle : (⨆ n : ℤ, MeasurableSpace.comap (ziter e n) (Entropy.generatedSigmaAlgebra μ P))
      ≤ mα := by
    refine iSup_le fun n => ?_
    calc MeasurableSpace.comap (ziter e n) (Entropy.generatedSigmaAlgebra μ P)
        ≤ MeasurableSpace.comap (ziter e n) mα := comap_mono hgen_le
      _ ≤ mα := measurable_iff_comap_le.mp (measurable_ziter e n)
  -- Each `(n, i)`-preimage of a cell is `m`-measurable (it is one term of the `iSup`).
  have hcell_m : ∀ (n : ℤ) (i : ι),
      MeasurableSet[⨆ k : ℤ, MeasurableSpace.comap (ziter e k)
        (Entropy.generatedSigmaAlgebra μ P)] ((ziter e n) ⁻¹' (P.cells i)) := by
    intro n i
    have hcell_gen : MeasurableSet[Entropy.generatedSigmaAlgebra μ P] (P.cells i) :=
      measurableSet_generateFrom ⟨i, rfl⟩
    have hcomap : MeasurableSet[MeasurableSpace.comap (ziter e n)
        (Entropy.generatedSigmaAlgebra μ P)] ((ziter e n) ⁻¹' (P.cells i)) :=
      ⟨P.cells i, hcell_gen, rfl⟩
    exact le_def.1 (le_iSup (fun k : ℤ => MeasurableSpace.comap (ziter e k)
      (Entropy.generatedSigmaAlgebra μ P)) n) _ hcomap
  -- The countable family of cell-preimages separates points under the `m`-structure.
  have hCS : @CountablySeparated α
      (⨆ k : ℤ, MeasurableSpace.comap (ziter e k) (Entropy.generatedSigmaAlgebra μ P)) := by
    rw [@countablySeparated_def α
      (⨆ k : ℤ, MeasurableSpace.comap (ziter e k) (Entropy.generatedSigmaAlgebra μ P))]
    refine ⟨Set.range (fun p : ℤ × ι => (ziter e p.1) ⁻¹' (P.cells p.2)), Set.countable_range _,
      ?_, ?_⟩
    · rintro _ ⟨p, rfl⟩; exact hcell_m p.1 p.2
    · intro x _ y _ hxy
      by_contra hne
      obtain ⟨n, i, hxin, hynotin⟩ := hsep x y hne
      have hiff := hxy ((ziter e n) ⁻¹' (P.cells i)) ⟨(n, i), rfl⟩
      rw [Set.mem_preimage, Set.mem_preimage] at hiff
      exact hynotin (hiff.mp hxin)
  -- Blackwell: `id : (α, mα) → (α, m)` is a measurable embedding, giving `mα ≤ m`.
  have hemb : @MeasurableEmbedding α α mα
      (⨆ k : ℤ, MeasurableSpace.comap (ziter e k) (Entropy.generatedSigmaAlgebra μ P)) id :=
    @Measurable.measurableEmbedding α α
      (⨆ k : ℤ, MeasurableSpace.comap (ziter e k) (Entropy.generatedSigmaAlgebra μ P)) id hCS mα _
      ((@measurable_id α mα).mono le_rfl hle) injective_id
  have hge : mα ≤ ⨆ k : ℤ, MeasurableSpace.comap (ziter e k)
      (Entropy.generatedSigmaAlgebra μ P) := by
    refine le_def.2 fun s hs => ?_
    have himg : MeasurableSet[⨆ k : ℤ, MeasurableSpace.comap (ziter e k)
        (Entropy.generatedSigmaAlgebra μ P)] (id '' s) :=
      @MeasurableEmbedding.measurableSet_image' α α mα
        (⨆ k : ℤ, MeasurableSpace.comap (ziter e k) (Entropy.generatedSigmaAlgebra μ P)) id hemb
        s hs
    rwa [Set.image_id] at himg
  exact le_antisymm hle hge

end ErgodicTheory.Krieger
