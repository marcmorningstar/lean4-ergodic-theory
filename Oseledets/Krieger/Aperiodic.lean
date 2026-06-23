/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Measure-theoretic aperiodicity from ergodicity

For an ergodic, invertible, measure-preserving transformation `e` of a standard Borel
probability space with no atoms, the set of `n`-periodic points has measure zero for every
`n ≥ 1`.  Equivalently, almost every point has an infinite forward orbit: the transformation is
*aperiodic* in the measure-theoretic sense.

This fact is the structural input to the **Rokhlin tower lemma** (issue #15): aperiodicity is
precisely what lets one build, for any `n` and `ε`, a measurable base set `B` whose first `n`
images `B, eB, …, e^{n-1}B` are disjoint and exhaust all but `ε` of the space.  Measure-theoretic
aperiodicity is **absent from Mathlib**, so we develop it here.

## Main results

* `Oseledets.Krieger.ae_periodic_measure_zero` — the level-`n` fixed-point set
  `{x | eⁿ x = x}` is `μ`-null for `1 ≤ n`.
* `Oseledets.Krieger.aperiodic_of_ergodic` — the same statement quantified over all `n ≥ 1`.

## Proof outline

The fixed-point set `F = {x | Tⁿ x = x}` (with `T = e`) is measurable (a standard Borel space
has a measurable diagonal) and `T`-invariant, so by the zero–one law `μ F ∈ {0, 1}`.  Suppose
`μ F = 1`.  Embed the space measurably into `ℝ` via `embeddingReal` and consider
`g x = ⨅ j < n, f (Tʲ x)`, the minimum of the embedding over the length-`n` forward orbit.  On `F`
the orbit is cyclically permuted by `T`, so `g` is `T`-invariant a.e.; ergodicity forces `g` to be
a.e. constant `c`.  The infimum over a finite family is attained, so a.e. point lands —at some
time `j < n`— in the singleton `f⁻¹{c}`.  But each `(Tʲ)⁻¹{x₀}` is null (measure preservation plus
`NoAtoms`), so the full-measure set sits inside a finite union of null sets — contradiction.
Hence `μ F = 0`.
-/

open MeasureTheory Function Set
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]

/-- If `x` is an `n`-periodic point of `T` (i.e. `T^[n] x = x`), then the forward trajectory
`k ↦ T^[k] x` is periodic with period `n`: only the residue `k % n` matters. -/
private theorem iterate_mod_of_periodic {β : Type*} {T : β → β} {x : β} {n : ℕ}
    (hx : T^[n] x = x) (k : ℕ) : T^[k % n] x = T^[k] x := by
  conv_rhs => rw [← Nat.mod_add_div k n]
  rw [Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed hx]

/-- On the level-`n` periodic set, the minimum of a real-valued observable over the length-`n`
forward orbit is `T`-invariant: applying `T` cyclically permutes the orbit, so the infimum is
unchanged. -/
private theorem iInf_orbit_comp_eq {β : Type*} {T : β → β} {f : β → ℝ} {x : β} {n : ℕ}
    (hn : 1 ≤ n) (hx : T^[n] x = x) :
    ⨅ j : Fin n, f (T^[(j : ℕ)] (T x)) = ⨅ j : Fin n, f (T^[(j : ℕ)] x) := by
  have : NeZero n := ⟨Nat.one_le_iff_ne_zero.1 hn⟩
  -- rewrite both sides as an infimum of `j ↦ f (T^[k] x)` over shifted indices
  have key : ∀ j : Fin n, f (T^[(j : ℕ)] (T x)) = f (T^[((finRotate n j : Fin n) : ℕ)] x) := by
    intro j
    congr 1
    rw [← Function.iterate_succ_apply, ← iterate_mod_of_periodic hx ((j : ℕ) + 1)]
    congr 1
    -- (finRotate n j : ℕ) = (j + 1) % n
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp_rw [key]
  exact (finRotate n).iInf_comp (g := fun i : Fin n => f (T^[(i : ℕ)] x))

/-- **Aperiodicity from ergodicity.** For an ergodic, invertible, measure-preserving
transformation `e` of a standard Borel probability space with no atoms, the set of `n`-periodic
points `{x | eⁿ x = x}` has measure zero for every `n ≥ 1`.

This is the measure-theoretic *aperiodicity* of an ergodic automorphism; it is the structural
input to the Rokhlin tower lemma (issue #15) and is absent from Mathlib. -/
theorem ae_periodic_measure_zero [NoAtoms μ] (e : α ≃ᵐ α)
    (herg : Ergodic (e : α → α) μ) {n : ℕ} (hn : 1 ≤ n) :
    μ {x | (e : α → α)^[n] x = x} = 0 := by
  set T : α → α := (e : α → α) with hT
  have hTmeas : Measurable T := e.measurable
  have he : MeasurePreserving T μ μ := herg.toMeasurePreserving
  -- The level-`n` fixed-point set.
  set F : Set α := {x | T^[n] x = x} with hF
  have hFmeas : MeasurableSet F := measurableSet_eq_fun (hTmeas.iterate n) measurable_id
  -- `F` is `T`-invariant.
  have hFinv : T ⁻¹' F = F := by
    ext x
    simp only [hF, Set.mem_preimage, Set.mem_setOf_eq]
    have hcomm : T^[n] (T x) = T (T^[n] x) :=
      (Function.iterate_succ_apply T n x).symm.trans (Function.iterate_succ_apply' T n x)
    rw [hcomm]
    exact ⟨fun h => e.injective h, fun h => congrArg T h⟩
  -- Zero–one law.
  rcases herg.toPreErgodic.prob_eq_zero_or_one hFmeas hFinv with hzero | hone
  · exact hzero
  -- Suppose for contradiction `μ F = 1`; we will derive `μ univ = 0`.
  exfalso
  haveI : NeZero n := ⟨Nat.one_le_iff_ne_zero.1 hn⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  -- Measurable embedding of the space into the reals.
  set f : α → ℝ := embeddingReal α with hf
  have hfemb : MeasurableEmbedding f := measurableEmbedding_embeddingReal α
  have hfmeas : Measurable f := hfemb.measurable
  -- The orbit-minimum observable.
  set g : α → ℝ := fun x => ⨅ j : Fin n, f (T^[(j : ℕ)] x) with hg
  have hgmeas : Measurable g :=
    Measurable.iInf (fun j => hfmeas.comp (hTmeas.iterate (j : ℕ)))
  -- `g` is a.e. invariant under `T`: on the full-measure periodic set `F`, the orbit is permuted.
  have h_ae : g ∘ T =ᵐ[μ] g := by
    have hFcompl : μ Fᶜ = 0 := by
      rw [measure_compl hFmeas (measure_ne_top μ F), measure_univ, hone, tsub_self]
    have hFae : ∀ᵐ x ∂μ, x ∈ F := by
      rw [Filter.eventually_iff, mem_ae_iff]
      simpa using hFcompl
    filter_upwards [hFae] with x hx
    simp only [hg, Function.comp_apply]
    exact iInf_orbit_comp_eq hn hx
  -- Ergodicity forces `g` to be a.e. constant.
  obtain ⟨c, hc⟩ := herg.ae_eq_const_of_ae_eq_comp₀ hgmeas.nullMeasurable h_ae
  -- The full-measure set `{g = c}` sits inside a finite union of null preimages of the
  -- singleton `f⁻¹{c}`.
  have hsub : {x | g x = c} ⊆ ⋃ j : Fin n, T^[(j : ℕ)] ⁻¹' (f ⁻¹' {c}) := by
    intro x hx
    simp only [Set.mem_setOf_eq, hg] at hx
    obtain ⟨j, hj⟩ : ∃ j : Fin n, f (T^[(j : ℕ)] x) = ⨅ j : Fin n, f (T^[(j : ℕ)] x) :=
      exists_eq_ciInf_of_finite
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hj, hx]
  -- Each piece is null, hence the union is null.
  have hsing : (f ⁻¹' {c}).Subsingleton := Set.subsingleton_singleton.preimage hfemb.injective
  have hsingnull : μ (f ⁻¹' {c}) = 0 := hsing.measure_zero μ
  have hunull : μ (⋃ j : Fin n, T^[(j : ℕ)] ⁻¹' (f ⁻¹' {c})) = 0 := by
    refine measure_iUnion_null fun j => ?_
    rw [(he.iterate (j : ℕ)).measure_preimage (NullMeasurableSet.of_null hsingnull)]
    exact hsingnull
  -- `{g = c}` is contained in a null set, while its complement is null by ergodic constancy.
  have hgcnull : μ {x | g x = c} = 0 := measure_mono_null hsub hunull
  have hcomplnull : μ {x | g x = c}ᶜ = 0 := by
    have : ∀ᵐ x ∂μ, x ∈ {x | g x = c} := by
      filter_upwards [hc] with x hx using hx
    rwa [Filter.eventually_iff, mem_ae_iff] at this
  -- Hence the whole space is null, contradicting that `μ` is a probability measure.
  have : μ (Set.univ : Set α) = 0 := by
    have hunion : (Set.univ : Set α) = {x | g x = c} ∪ {x | g x = c}ᶜ := by
      rw [Set.union_compl_self]
    rw [hunion]
    exact measure_union_null hgcnull hcomplnull
  rw [measure_univ] at this
  exact one_ne_zero this

/-- The transformation `e` is **aperiodic**: for every period `n ≥ 1`, the set of `n`-periodic
points is `μ`-null.  Packaging of `ae_periodic_measure_zero` quantified over all `n`. -/
theorem aperiodic_of_ergodic [NoAtoms μ] (e : α ≃ᵐ α)
    (herg : Ergodic (e : α → α) μ) :
    ∀ n : ℕ, 1 ≤ n → μ {x | (e : α → α)^[n] x = x} = 0 :=
  fun _ hn => ae_periodic_measure_zero e herg hn

end Oseledets.Krieger
