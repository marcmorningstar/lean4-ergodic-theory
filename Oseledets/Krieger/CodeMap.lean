/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.Coding

/-!
# The symbolic code map for Krieger's finite generator theorem (C3)

This file builds the **structural / measurable backbone** of the symbolic-coding step (C3) of
Krieger's finite generator theorem (issue #15): the code partition of a measurable code symbol and
the two-sided itinerary map, together with the one measurability fact that lets a product-measurable
decoder of the itinerary pull back to a `twoSidedSat`-measurable set. This is exactly what the
cross-layer mod-0 coding reduction `Oseledets.Krieger.codesTwoSidedMod0c_of_aeRecovery`
(`Generator.lean`) — which feeds the headline `Oseledets.Krieger.krieger_finite_generator` through
`Oseledets.Krieger.ColumnCodeData` (`Recovery.lean`) — consumes. Everything here is proved
sorry-free and **unconditionally**; the genuinely dynamical/combinatorial inputs (the code symbol
`c : α → Fin k` and the a.e.-recovering decoder) live downstream.

## The construction (Downarowicz §4.2 Lemma 4.2.5; Einsiedler–Lindenstrauss–Ward §3; Krieger 1970)

Given a fixed (countable or finite) generator `Q`, the classical construction codes the columns of a
Rokhlin tower: on each tower column one reads the `Q`-`N`-name, maps it through the **sentinel
prefix-code** (`Oseledets.Krieger.exists_sentinelEncoding`) to a length-`O(N)` block over `Fin k`,
and *defines* the code symbol `c : α → Fin k` so that `c (eⁱ x)` is the `i`-th block symbol. The
sentinel marks the column boundaries, so a decoder reading the two-sided `P`-itinerary
`n ↦ c (eⁿ x)` can re-find the boundaries (`Oseledets.Krieger.sentinelEncodeList_injective`) and
reconstruct the `Q`-name of a.e. point. The number of distinct `N`-names is `≤ kᴺ` up to `ε`
(the name-count layer C2, where `log k > h` and the Shannon–McMillan–Breiman theorem enter), which
is exactly the cardinality bound `exists_sentinelEncoding` needs.

This file does **not** build `c` or `D` (that is the dynamical heart, C1/C2 + recurrence); it proves
that **once** a measurable code symbol `c : α → Fin k` is given, the code partition's two-sided
itinerary map is `twoSidedSat`-measurable, so a product-measurable decoder recovering each `Q`-cell
a.e. produces a `twoSidedSat`-measurable approximant of every cell.

## The itinerary map and the central measurability transfer

The bridge to the saturation σ-algebra is the **itinerary map**
`itin e c : α → (ℤ → Fin k)`, `x ↦ (n ↦ c (eⁿ x))`. Its single structural property —
`measurable_itin` — is that it is measurable from `(α, twoSidedSat e P)` to the product space
`(ℤ → Fin k)`: each coordinate `x ↦ c (eⁿ x)` is `comap (eⁿ) σ(P)`-measurable (its singleton
preimages are `(eⁿ)⁻¹(P.cells j)`), and the `n`-th term `comap (eⁿ) σ(P)` sits below
`twoSidedSat e P`. This is exactly what lets a product-measurable decoder pull back to a
`twoSidedSat e P`-measurable set, with **no new symbolic-dynamics infrastructure** — `Pi`
measurability (`measurable_pi_iff`), `measurable_to_countable'` (`Fin k` is discrete), and the
existing `comap`/`iSup` API suffice.

## The code partition

* `codePartition c hc` is the `Fin k`-partition with cells `c ⁻¹' {j}` — the partition `P` itself.
* `measurable_itin` is the central transfer: the itinerary map is `twoSidedSat e (codePartition …)`-
  measurable, so composing any product-measurable decoder `D` with it yields a `twoSidedSat`-
  measurable set. The downstream reduction `codesTwoSidedMod0c_of_aeRecovery` (`Generator.lean`)
  then turns an a.e.-recovering `D` into the cross-layer mod-0 code consumed by the headline.

`measurable_itin` shows the harder-looking half — measurability of the decoder set in the saturation
σ-algebra — is automatic from product-measurability of `D`; the residual is the *existence* of the
code symbol `c` and the a.e.-recovering decoder, the genuine dynamical content of C1/C2.

## References

* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*,
  Trans. Amer. Math. Soc. **149** (1970), 453–464.
* Manfred Einsiedler, Elon Lindenstrauss and Thomas Ward, *Entropy in Ergodic Theory and
  Homogeneous Dynamics*, §3 (the Krieger generator theorem).
* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5).
-/

open MeasureTheory Function MeasurableSpace Filter

namespace Oseledets.Krieger

variable {α : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

open Oseledets.Entropy

/-! ### The code partition from a measurable code symbol -/

/-- **The code partition** of a measurable code symbol `c : α → Fin k`: the `Fin k`-valued partition
whose `j`-th cell is the level set `c ⁻¹' {j} = {x | c x = j}`. Each cell is measurable (preimage of
a singleton under the measurable `c`); the cells are pairwise disjoint (distinct singletons are
disjoint) and cover `α` (every point has a code symbol). This is the partition `P` that the symbolic
code reads off; the `Fin k` index is the alphabet of the code. -/
noncomputable def codePartition (c : α → Fin k) (hc : Measurable c) :
    MeasurePartition μ (Fin k) where
  cells := fun j => c ⁻¹' {j}
  measurable := fun j => hc (measurableSet_singleton j)
  aedisjoint := by
    intro i j hij
    simp only [onFun, AEDisjoint]
    have : (c ⁻¹' {i}) ∩ (c ⁻¹' {j}) = ∅ := by
      rw [← Set.preimage_inter,
        show ({i} : Set (Fin k)) ∩ {j} = ∅ from Set.singleton_inter_eq_empty.mpr hij]
      exact Set.preimage_empty
    rw [this]; simp
  cover := by ext x; simp

@[simp] lemma codePartition_cells (c : α → Fin k) (hc : Measurable c) (j : Fin k) :
    (codePartition (μ := μ) c hc).cells j = c ⁻¹' {j} := rfl

/-! ### The itinerary map and its measurability in the two-sided saturation -/

/-- **The two-sided `P`-itinerary map** `itin e c : α → (ℤ → Fin k)`, sending a point `x` to its
two-sided code itinerary `n ↦ c (eⁿ x)`. A decoder of the symbolic code is a (product-)measurable
function of this itinerary; `measurable_itin` shows that composing such a decoder with `itin`
produces a set measurable in the two-sided saturation σ-algebra. -/
noncomputable def itin (e : α ≃ᵐ α) (c : α → Fin k) : α → (ℤ → Fin k) :=
  fun x n => c (ziter e n x)

@[simp] lemma itin_apply (e : α ≃ᵐ α) (c : α → Fin k) (x : α) (n : ℤ) :
    itin e c x n = c (ziter e n x) := rfl

/-- **The itinerary coordinate is measurable for the `n`-th saturation term.** The map
`x ↦ c (eⁿ x)` is measurable from `(α, comap (eⁿ) σ(P))` to the discrete `Fin k`: since `Fin k` is
countable it suffices to check that each singleton preimage `{x | c (eⁿ x) = j}` is
`comap (eⁿ) σ(P)`-measurable, and that set is `(eⁿ)⁻¹(P.cells j)` with `P.cells j ∈ σ(P)`. -/
theorem measurable_itin_coord (e : α ≃ᵐ α) (c : α → Fin k) (hc : Measurable c) (n : ℤ) :
    @Measurable α (Fin k)
      (MeasurableSpace.comap (ziter e n) (generatedSigmaAlgebra μ (codePartition (μ := μ) c hc))) _
      (fun x => itin e c x n) := by
  refine @measurable_to_countable' (Fin k) α _ _
    (MeasurableSpace.comap (ziter e n) (generatedSigmaAlgebra μ (codePartition (μ := μ) c hc)))
    (fun x => itin e c x n) ?_
  intro j
  have hset : (fun x => itin e c x n) ⁻¹' {j}
      = (ziter e n) ⁻¹' ((codePartition (μ := μ) c hc).cells j) := by
    ext x; simp [codePartition_cells, itin, Set.mem_preimage]
  rw [hset]
  exact ⟨(codePartition (μ := μ) c hc).cells j,
    MeasurableSpace.measurableSet_generateFrom ⟨j, rfl⟩, rfl⟩

/-- **The central measurability transfer (the structural crux of C3).** The two-sided itinerary map
`itin e c` is measurable from `(α, twoSidedSat e P)` to the product space `(ℤ → Fin k)`. Each
coordinate is measurable for the `n`-th saturation term `comap (eⁿ) σ(P)`
(`measurable_itin_coord`), which sits below `twoSidedSat e P` (`le_iSup`); `measurable_pi_iff`
assembles the coordinates. This is what lets a product-measurable decoder of the itinerary pull
back to a `twoSidedSat e P`-measurable set — the property the mod-0 coding reduction
`Oseledets.Krieger.codesTwoSidedMod0c_of_aeRecovery` (`Generator.lean`) consumes. No new
symbolic-dynamics infrastructure is needed: only `Pi`/countable measurability and the existing
`comap`/`iSup` saturation API. -/
theorem measurable_itin (e : α ≃ᵐ α) (c : α → Fin k) (hc : Measurable c) :
    @Measurable α (ℤ → Fin k) (twoSidedSat e (codePartition (μ := μ) c hc)) _ (itin e c) := by
  refine (@measurable_pi_iff α ℤ (fun _ => Fin k)
    (twoSidedSat e (codePartition (μ := μ) c hc)) _ (itin e c)).mpr ?_
  intro n
  exact (measurable_itin_coord e c hc n).mono
    (le_iSup (fun m : ℤ => MeasurableSpace.comap (ziter e m)
      (generatedSigmaAlgebra μ (codePartition (μ := μ) c hc))) n) le_rfl

end Oseledets.Krieger
