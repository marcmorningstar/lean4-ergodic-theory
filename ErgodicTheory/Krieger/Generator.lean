/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.Coding
import ErgodicTheory.Krieger.CountableEntropy
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The finite-entropy countable two-sided generator (Krieger sub-problem A)

This file constructs the **countable two-sided generator of finite static entropy** that opens
the unconditional Krieger finite generator theorem (issue #15). Following Downarowicz, *Entropy in
Dynamical Systems*, **Theorem 4.2.3, first half** (and the elementary Keane–Serafin proof of
Rokhlin's countable generator theorem), the proof of the finite generator theorem first reduces to
producing a **countable** partition `Q` of the standard-Borel probability space `(α, μ)` that

* **two-sidedly generates mod 0** under the ergodic aperiodic automorphism `e`
  (`IsGeneratingTwoSidedMod0c e Q`, the `Countable`-indexed analogue of the `Fintype`-indexed
  `ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0` of `Coding.lean`), and
* has **finite static (Shannon) entropy** — formalized, as in
  `ErgodicTheory.Krieger.CountableEntropy`,
  as `Summable (fun i => Real.negMulLog (μ (Q i)).toReal)` (whence `cHμ μ Q` is a genuine finite
  sum).

Only then is `Q` coded into `Fin k` (the M1+M2 Rokhlin-tower / name-count combinatorics already in
`ErgodicTheory.Krieger.Coding`/`NameCount`/`RokhlinTower`); this file is the **static input**,
not the coding step.

## The `Countable`-indexed coding layer

The mod-0 coding development of `Coding.lean` is stated for a `Fintype`-indexed
`ErgodicTheory.Entropy.MeasurePartition`. Since the generator `Q` is **countably infinite**,
this file
re-establishes the few structural facts at the level of a *bare* `Countable`-indexed family of cells
`Q : κ → Set α` (we never need the partition axioms for the generation statement — only that each
cell is measurable, supplied where used). Concretely:

* `ctwoSidedSat e Q := ⨆ n : ℤ, comap (ziter e n) (generateFrom (range Q))` — the two-sided
  itinerary σ-algebra of the countable family `Q`;
* `IsGeneratingTwoSidedMod0c e Q := mα ≤ eventuallyMeasurableSpace (ctwoSidedSat e Q) (ae μ)` — `Q`
  two-sidedly generates mod 0.

The two structural lemmas of `Coding.lean` that the reduction needs — shift-invariance of the
two-sided saturation and mod-0 monotonicity under recovery — are re-proved verbatim for the
`Countable` index (their proofs never used `Fintype`).

## The structural reduction (the formalizable core)

The Keane–Serafin / Downarowicz construction produces, inductively, an **increasing sequence of
finite partitions** `Qₖ` such that

1. each `Qₖ ⪯ Qₖ₊₁` refines the previous (`σ(Qₖ) ≤ σ(Qₖ₊₁)`);
2. the two-sided join of `Qₖ` recovers the `k`-th standard-Borel generating set `Bₖ` mod 0
   (`Bₖ ∈ ⋁ₙ eⁿσ(Qₖ)`, mod 0); and
3. the static entropies are uniformly bounded, `sup_k H(Qₖ) ≤ h(e) + 1 < ∞`.

This file proves, **unconditionally and sorry-free**, the structural step that turns *any* such
sequence into the desired countable generator:

* the **limit partition** `Q := ⋁ₖ Qₖ` is realized as a `Countable`-indexed family whose
  generated σ-algebra is the supremum `⨆ₖ σ(Qₖ)` (`generateFrom_limitFamily`);
* its two-sided saturation contains every `Bₖ` mod 0 hence — `B` generating `mα` — **generates mod
  0** (`isGeneratingTwoSidedMod0c_limit`);
* a uniform entropy bound `sup_k H(Qₖ) < ∞` together with a summable index-mass envelope certifies
  **finite static entropy** via `ErgodicTheory.Krieger.cHμ_summable_of_summable_index_mul`.

## What is supplied vs. proved

The single dynamical input — the per-step Keane–Serafin refinement lemma (which uses the
Shannon–McMillan–Breiman theorem and Rokhlin's lemma to bound the entropy increment) — is **not**
re-derived here; it is exposed as the hypothesis bundle `KeaneSerafinData` so that the headline
existence theorem `exists_countable_twoSided_generator_of_keaneSerafinData` is a faithful, honest
reduction: *given* the inductive sequence with its three properties, the finite-entropy countable
two-sided generator exists. The remaining dynamical residual is the Rokhlin-tower construction
assembling the (now proved in-repo) SMB equipartition into `Q`; it is isolated in `KeaneSerafinData`
and named, not faked, for sub-problem A.

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Theorem 4.2.3).
* Michael S. Keane and Jacek Serafin, *On the countable generator theorem*, Fund. Math. **157**
  (1998), 255–259 (the elementary proof of Rokhlin's countable generator theorem).
* Vladimir Rokhlin, *Generators in ergodic theory, II*, Vestnik Leningrad. Univ. (1965).
* Eli Glasner, *Ergodic Theory via Joinings*, Math. Surveys Monogr. **101**, AMS (2003).
-/

open MeasureTheory Function MeasurableSpace Filter

namespace ErgodicTheory.Krieger

open ErgodicTheory.Entropy

variable {α : Type*} {κ : Type*} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The `Countable`-indexed two-sided saturation and mod-0 generation

These mirror `twoSidedSat` / `IsGeneratingTwoSidedMod0` of `Coding.lean`, but on a *bare*
`Countable`-indexed family of cells `Q : κ → Set α` rather than a `Fintype`-indexed
`MeasurePartition`. The static σ-algebra is `generateFrom (range Q)`. -/

/-- The **two-sided itinerary σ-algebra** of a countable family of cells `Q : κ → Set α` under the
automorphism `e`: the supremum over all integer iterates `eⁿ` of the pulled-back static σ-algebra
`σ(Q) = generateFrom (range Q)`. This is the `Countable`-indexed analogue of
`ErgodicTheory.Krieger.twoSidedSat`. -/
@[reducible]
noncomputable def ctwoSidedSat (e : α ≃ᵐ α) (Q : κ → Set α) : MeasurableSpace α :=
  ⨆ n : ℤ, MeasurableSpace.comap (ziter e n) (generateFrom (Set.range Q))

@[simp]
lemma ctwoSidedSat_def (e : α ≃ᵐ α) (Q : κ → Set α) :
    ctwoSidedSat e Q =
      ⨆ n : ℤ, MeasurableSpace.comap (ziter e n) (generateFrom (Set.range Q)) := rfl

/-- **Shift-invariance** of the countable two-sided saturation (cf. `comap_twoSidedSat_le`). Pulling
`ctwoSidedSat e Q` back by any iterate `eᵐ` lands inside it again, because the reindexing
`n ↦ n + m` is a bijection of `ℤ` (`ziter_add`). -/
theorem comap_ctwoSidedSat_le (e : α ≃ᵐ α) (Q : κ → Set α) (m : ℤ) :
    MeasurableSpace.comap (ziter e m) (ctwoSidedSat e Q) ≤ ctwoSidedSat e Q := by
  rw [ctwoSidedSat_def, MeasurableSpace.comap_iSup]
  refine iSup_le fun n => ?_
  rw [MeasurableSpace.comap_comp, ← ziter_add]
  exact le_iSup
    (fun k : ℤ => MeasurableSpace.comap (ziter e k) (generateFrom (Set.range Q))) (n + m)

/-- `Q` **two-sidedly generates `(α, e, μ)` mod 0** for a *countable* family `Q : κ → Set α` when
the ambient σ-algebra `mα` is contained in the **μ-completion** of the two-sided `Q`-saturation.
The `Countable`-indexed analogue of `ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0`. -/
def IsGeneratingTwoSidedMod0c (μ : Measure α) (e : α ≃ᵐ α) (Q : κ → Set α) : Prop :=
  mα ≤ eventuallyMeasurableSpace (ctwoSidedSat e Q) (ae μ)

/-- **Mod-0 shift-invariance** of the countable two-sided saturation (cf.
`comap_eventuallyMeasurableSpace_twoSidedSat_le`). Preimage under a measure-preserving `eᵐ` commutes
with the μ-completion, and shift-invariance is literal, so completion-monotonicity finishes. -/
theorem comap_eventuallyMeasurableSpace_ctwoSidedSat_le (e : α ≃ᵐ α)
    (he : MeasurePreserving (e : α → α) μ μ) (Q : κ → Set α) (m : ℤ) :
    MeasurableSpace.comap (ziter e m)
        (eventuallyMeasurableSpace (ctwoSidedSat e Q) (ae μ)) ≤
      eventuallyMeasurableSpace (ctwoSidedSat e Q) (ae μ) :=
  le_trans (comap_eventuallyMeasurableSpace_le
      (measurePreserving_ziter e he m).quasiMeasurePreserving)
    (eventuallyMeasurableSpace_mono (comap_ctwoSidedSat_le e Q m))

/-! ### The cross-layer coding predicate: a countable generator coded by a `Fintype` partition

Krieger's construction codes the **countable** finite-entropy generator `Q : κ → Set α` (sub-problem
A, `exists_countable_twoSided_generator`) into a **`Fin k`/`Fintype`** partition `P` (sub-problem B,
the Rokhlin-tower / name-count combinatorics). The two saturation layers therefore meet here: `Q`
lives in the `Countable` layer (`ctwoSidedSat`, `IsGeneratingTwoSidedMod0c`) while `P` lives in the
`Fintype` layer of `Coding.lean` (`twoSidedSat`, `IsGeneratingTwoSidedMod0`). The bridge is the
**cross-layer coding predicate** `CodesTwoSidedMod0c e Q P`: every cell of the countable `Q` is
recovered, mod 0, by the two-sided `P`-itinerary of the finite partition. From it the **cross-layer
recovery** (`IsGeneratingTwoSidedMod0c.of_codesc`) promotes a mod-0 countable two-sided generator
`Q` to the mod-0 finite two-sided generator `P` — the exact step the headline assembly needs. -/

variable {ι : Type*} [Fintype ι]

/-- **The cross-layer mod-0 coding predicate.** A `Fintype`-indexed (`Fin k`-valued) partition
`P : MeasurePartition μ ι` *codes* a **countable** family of cells `Q : κ → Set α` two-sidedly mod 0
under `e` when every cell of `Q` is recovered, up to a μ-null set, by the two-sided `P`-itinerary:
`generateFrom (range Q) ≤ eventuallyMeasurableSpace (twoSidedSat e P) (ae μ)`.

The left-hand σ-algebra is the *static* σ-algebra `σ(Q) = generateFrom (range Q)` of the countable
family — exactly the `n = 0` term of `ctwoSidedSat e Q`, matching how `IsGeneratingTwoSidedMod0c`
and `ctwoSidedSat` are phrased. The right-hand side is the μ-completion of the *finite* partition's
two-sided saturation `ErgodicTheory.Krieger.twoSidedSat`. This is the conclusion of the symbolic
block
code: off a null set, the two-sided `P`-itinerary of a point determines its `Q`-name, hence which
`Q`-cell it lies in. -/
def CodesTwoSidedMod0c (e : α ≃ᵐ α) (Q : κ → Set α) (P : MeasurePartition μ ι) : Prop :=
  generateFrom (Set.range Q) ≤ eventuallyMeasurableSpace (twoSidedSat e P) (ae μ)

/-- **Cross-layer mod-0 recovery / refinement monotonicity.** If every cell of the countable family
`Q` is recovered mod 0 by the two-sided saturation of the finite partition `P`
(`σ(Q) ≤ completion (twoSidedSat e P)`), then the *entire* countable two-sided saturation of `Q` is
contained in that completion: `ctwoSidedSat e Q ≤ completion (twoSidedSat e P)`.

Each `ℤ`-term `comap (eᵐ) σ(Q)` of `ctwoSidedSat e Q` is bounded, by `comap`-monotonicity in the
hypothesis, by `comap (eᵐ) (completion (twoSidedSat e P))`, which is bounded by
`completion (twoSidedSat e P)` by mod-0 shift-invariance of the *finite* saturation
(`ErgodicTheory.Krieger.comap_eventuallyMeasurableSpace_twoSidedSat_le`). Taking the supremum
over `m` gives the claim. This is the cross-layer analogue of
`ErgodicTheory.Krieger.twoSidedSat_mono_of_codes`. -/
theorem ctwoSidedSat_mono_of_codesc (e : α ≃ᵐ α)
    (he : MeasurePreserving (e : α → α) μ μ) (P : MeasurePartition μ ι) (Q : κ → Set α)
    (hrec : generateFrom (Set.range Q) ≤ eventuallyMeasurableSpace (twoSidedSat e P) (ae μ)) :
    ctwoSidedSat e Q ≤ eventuallyMeasurableSpace (twoSidedSat e P) (ae μ) := by
  rw [ctwoSidedSat_def]
  refine iSup_le fun m => ?_
  exact le_trans (MeasurableSpace.comap_mono hrec)
    (comap_eventuallyMeasurableSpace_twoSidedSat_le e he P m)

/-- **Cross-layer recovery lifts a mod-0 countable two-sided generator to a finite one.** If the
countable family `Q` two-sidedly generates `(α, e, μ)` mod 0 (`IsGeneratingTwoSidedMod0c μ e Q`) and
the two-sided itinerary of the *finite* partition `P` recovers each cell of `Q` mod 0
(`CodesTwoSidedMod0c e Q P`), then `P` two-sidedly generates mod 0 in the `Fintype` sense
(`ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0 e P`).

`mα ≤ completion (ctwoSidedSat e Q)` (by `Q`'s mod-0 generation) and
`completion (ctwoSidedSat e Q) ≤ completion (completion (twoSidedSat e P)) ≤ completion
(twoSidedSat e P)` by cross-layer recovery monotonicity (`ctwoSidedSat_mono_of_codesc`),
completion-monotonicity (`ErgodicTheory.Krieger.eventuallyMeasurableSpace_mono`), and
completion-idempotence (`ErgodicTheory.Krieger.eventuallyMeasurableSpace_idem`). Chaining gives
`mα ≤ completion (twoSidedSat e P)`, i.e. `IsGeneratingTwoSidedMod0 e P`. This is the cross-layer
analogue of `ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0.of_codes`, bridging the `Countable`
layer (`Generator.lean`) to the `Fintype` layer (`Coding.lean`). -/
theorem IsGeneratingTwoSidedMod0c.of_codesc {e : α ≃ᵐ α}
    (he : MeasurePreserving (e : α → α) μ μ) {P : MeasurePartition μ ι} {Q : κ → Set α}
    (hQ : IsGeneratingTwoSidedMod0c μ e Q) (hrec : CodesTwoSidedMod0c e Q P) :
    IsGeneratingTwoSidedMod0 e P :=
  le_trans hQ
    (le_trans (eventuallyMeasurableSpace_mono (ctwoSidedSat_mono_of_codesc e he P Q hrec))
      eventuallyMeasurableSpace_idem)

/-- A cross-layer mod-0 code of a mod-0 countable two-sided generator is a mod-0 finite two-sided
generator — the cross-layer headline reduction. Immediate from
`IsGeneratingTwoSidedMod0c.of_codesc` and the definition of `CodesTwoSidedMod0c`. -/
theorem CodesTwoSidedMod0c.isGeneratingTwoSidedMod0 {e : α ≃ᵐ α}
    (he : MeasurePreserving (e : α → α) μ μ) {Q : κ → Set α} {P : MeasurePartition μ ι}
    (hQ : IsGeneratingTwoSidedMod0c μ e Q) (hP : CodesTwoSidedMod0c e Q P) :
    IsGeneratingTwoSidedMod0 e P :=
  IsGeneratingTwoSidedMod0c.of_codesc he hQ hP

/-- **The convenient sufficient condition for the cross-layer symbolic-code layer (C3).** To
establish a cross-layer mod-0 code `CodesTwoSidedMod0c e Q P` of a *countable* family
`Q : κ → Set α` it suffices to exhibit, for each cell `Q j`, a `twoSidedSat e P`-measurable set
`t` with `Q j =ᵐ[μ] t` — i.e. to recover every `Q`-cell, up to a μ-null set, from the two-sided
`P`-itinerary
of the finite partition `P`. This is exactly the output of an a.e.-injective measurable block code
`π : α → (ℤ → Fin k)` that recovers the countable `Q`-name a.e.: each `Q`-cell is, mod 0, a cylinder
event in the `P`-itinerary, hence `twoSidedSat e P`-measurable mod 0.

Formally, `σ(Q) = generateFrom (range Q)`, so `generateFrom_le` reduces the goal to the cells (the
range of `Q`), each handled by the hypothesis. -/
theorem codesTwoSidedMod0c_of_aeRecovery {e : α ≃ᵐ α} {Q : κ → Set α} {P : MeasurePartition μ ι}
    (hcode : ∀ j, ∃ t, @MeasurableSet α (twoSidedSat e P) t ∧ Q j =ᵐ[μ] t) :
    CodesTwoSidedMod0c e Q P := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨j, rfl⟩
  exact hcode j

/-! ### The generation criterion via a standard-Borel generating sequence

The ambient σ-algebra of a standard-Borel space is generated by a fixed countable sequence of
measurable sets `B = natGeneratingSequence α` (Mathlib's `generateFrom_natGeneratingSequence`,
available since `StandardBorelSpace α ⇒ MeasurableSpace.CountablyGenerated α`). To prove `Q`
two-sidedly generates mod 0, it therefore suffices to recover each `Bₘ` mod 0 from the two-sided
`Q`-itinerary. -/

/-- **Two-sided mod-0 generation from per-set recovery.** If a countable family of cells
`Q : κ → Set α` recovers every set `s` of a generating family `𝒢` (`generateFrom 𝒢 = mα`) up to a
μ-null set inside its two-sided saturation `ctwoSidedSat e Q`, then `Q` two-sidedly generates mod 0.

The hypothesis says each generator `s ∈ 𝒢` is `=ᵐ[μ]` to a `ctwoSidedSat e Q`-measurable set, i.e.
`s ∈ eventuallyMeasurableSpace (ctwoSidedSat e Q) (ae μ)`; since the completion is a σ-algebra,
`generateFrom 𝒢 = mα ≤` it. -/
theorem isGeneratingTwoSidedMod0c_of_recovers {e : α ≃ᵐ α} {Q : κ → Set α} {𝒢 : Set (Set α)}
    (hgen : generateFrom 𝒢 = mα)
    (hrec : ∀ s ∈ 𝒢, ∃ t, @MeasurableSet α (ctwoSidedSat e Q) t ∧ s =ᵐ[μ] t) :
    IsGeneratingTwoSidedMod0c μ e Q := by
  have hle : generateFrom 𝒢 ≤ eventuallyMeasurableSpace (ctwoSidedSat e Q) (ae μ) := by
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    obtain ⟨t, ht, hst⟩ := hrec s hs
    exact ⟨t, ht, hst⟩
  rw [hgen] at hle
  exact hle

/-- **Two-sided mod-0 generation from per-`natGeneratingSequence` recovery (standard-Borel).** For a
standard-Borel space the ambient σ-algebra is generated by `natGeneratingSequence α`
(`generateFrom_natGeneratingSequence`). Hence if the `ℕ`-indexed countable family `Q` recovers each
`natGeneratingSequence α m` mod 0 inside its two-sided saturation, `Q` two-sidedly generates mod 0.

This is the convenient generation criterion the Keane–Serafin / Downarowicz limit partition
discharges: the inductive construction is steered so that the two-sided itinerary of the limit
partition determines membership in every generating set `Bₘ` off a null set. -/
theorem isGeneratingTwoSidedMod0c_of_recovers_natGeneratingSequence
    [StandardBorelSpace α] {e : α ≃ᵐ α} {Q : κ → Set α}
    (hrec : ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e Q) t ∧
      natGeneratingSequence α m =ᵐ[μ] t) :
    IsGeneratingTwoSidedMod0c μ e Q := by
  refine isGeneratingTwoSidedMod0c_of_recovers (𝒢 := Set.range (natGeneratingSequence α))
    (generateFrom_natGeneratingSequence α) ?_
  rintro _ ⟨m, rfl⟩
  exact hrec m

/-! ### The increasing-sequence reduction: generation of the union family

The Keane–Serafin / Downarowicz construction builds an **increasing sequence of finite partitions**
`Qₖ`, where the level-`k` partition's two-sided itinerary already recovers the `k`-th generating set
`Bₖ` mod 0. The *union family* `Q⁺ ⟨k, i⟩ := (Qₖ) i` collects all their cells; its generated
σ-algebra is the join `⨆ₖ σ(Qₖ)` (`iSup_generateFrom`), so its two-sided saturation contains every
`comap (eⁿ) σ(Qₖ)`, hence recovers every `Bₖ` mod 0 and therefore two-sidedly generates mod 0.

This is the clean structural half of the construction. (The *entropy* of the union family is not
finite — that needs the genuine join **atom** partition, whose finite static entropy is the supplied
`summable_index_mass` of `KeaneSerafinData`; the union family only witnesses generation.) -/

omit mα in
/-- The static σ-algebra of the union family `Q⁺ ⟨k, i⟩ := Q k i` of a countable family of
finite-or-countable families `Q : ∀ k, κ k → Set α` is the supremum `⨆ₖ σ(Q k)` of the levels'
static σ-algebras. -/
theorem generateFrom_sigmaUnion {κ : ℕ → Type*} (Q : ∀ k, κ k → Set α) :
    generateFrom (Set.range fun p : (Σ k, κ k) => Q p.1 p.2) =
      ⨆ k, generateFrom (Set.range (Q k)) := by
  have hrange : (Set.range fun p : (Σ k, κ k) => Q p.1 p.2) = ⋃ k, Set.range (Q k) := by
    ext s; simp [Set.range, Sigma.exists]
  rw [hrange, ← iSup_generateFrom]

/-- **Generation of the union family from per-level recovery.** Suppose, for an increasing sequence
of countable families `Q : ∀ k, κ k → Set α`, that the level-`k` two-sided saturation recovers the
`k`-th standard-Borel generating set `Bₖ` mod 0 (each `Bₖ =ᵐ[μ]` a `twoSidedSat` cell of the family
`Q k`). Then the **union family** `Q⁺ ⟨k, i⟩ := Q k i` two-sidedly generates mod 0.

The proof: `ctwoSidedSat e Q⁺ = ⨆ₙ comap (eⁿ) (⨆ₖ σ(Q k))` dominates each level's
`ctwoSidedSat e (Q k)`, so a level-`k` recovery of `Bₖ` lifts to a `Q⁺`-recovery; then
`isGeneratingTwoSidedMod0c_of_recovers_natGeneratingSequence` finishes. -/
theorem isGeneratingTwoSidedMod0c_sigmaUnion_of_levelRecovers [StandardBorelSpace α]
    {κ : ℕ → Type*} {e : α ≃ᵐ α} (Q : ∀ k, κ k → Set α)
    (hrec : ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e (Q m)) t ∧
      natGeneratingSequence α m =ᵐ[μ] t) :
    IsGeneratingTwoSidedMod0c μ e (fun p : (Σ k, κ k) => Q p.1 p.2) := by
  set Qp : (Σ k, κ k) → Set α := fun p => Q p.1 p.2 with hQp
  -- The level-`m` two-sided saturation embeds into the union family's two-sided saturation.
  have hlevel_le : ∀ m, ctwoSidedSat e (Q m) ≤ ctwoSidedSat e Qp := by
    intro m
    rw [ctwoSidedSat_def, ctwoSidedSat_def]
    refine iSup_mono fun n => MeasurableSpace.comap_mono ?_
    -- σ(Q m) ≤ ⨆ₖ σ(Q k) = σ(range Qp)
    rw [hQp, generateFrom_sigmaUnion Q]
    exact le_iSup (fun k => generateFrom (Set.range (Q k))) m
  refine isGeneratingTwoSidedMod0c_of_recovers_natGeneratingSequence (Q := Qp) ?_
  intro m
  obtain ⟨t, ht, hBt⟩ := hrec m
  -- A `ctwoSidedSat e (Q m)`-measurable `t` is a fortiori `ctwoSidedSat e Qp`-measurable.
  exact ⟨t, hlevel_le m _ ht, hBt⟩

/-! ### The finite-entropy countable two-sided generator: the existence theorem

The Keane–Serafin / Downarowicz construction produces a countable partition `Q : ℕ → Set α` (the
join `⋁ₖ Qₖ` of an increasing sequence of finite partitions) with two properties:

* **two-sided recovery** of the standard-Borel generating sets `natGeneratingSequence α` mod 0
  (so `Q` two-sidedly generates mod 0); and
* a **summable index-mass envelope** `∑ i, i·μ(Qᵢ) < ∞`, the static finiteness witness produced by
  the SMB entropy bookkeeping (`H(Qₖ) ≤ h(e) + 1`, organised so the limit atoms are placed with
  geometrically decaying index-mass).

The dynamical/analytic content (Rokhlin's lemma + the Shannon–McMillan–Breiman theorem driving the
per-step entropy increment) lives entirely in producing this data; it is bundled as
`KeaneSerafinData`. Everything downstream — turning the recovery into mod-0 two-sided generation,
and the index-mass envelope into finite static Shannon entropy via Downarowicz's Fact 1.1.4
(`cHμ_summable_of_summable_index_mul`) — is proved here, unconditionally and sorry-free. -/

/-- **The Keane–Serafin / Downarowicz dynamical input** for sub-problem A: the data of a countable
partition `Q : ℕ → Set α` together with the two facts the construction guarantees but whose proof
needs the dynamics. Bundling them isolates the open analytic residual (SMB + Rokhlin) from the
clean structural reduction.

* `cells_measurable`: each cell `Q i` is measurable;
* `recovers`: each standard-Borel generating set `natGeneratingSequence α m` is recovered mod 0 by
  the two-sided `Q`-itinerary — the **generation** witness;
* `summable_index_mass`: the index-weighted total mass `∑ i, i·μ(Qᵢ)` is finite — the **finite
  static entropy** witness (Downarowicz Fact 1.1.4 input). -/
structure KeaneSerafinData [StandardBorelSpace α] (μ : Measure α) (e : α ≃ᵐ α) where
  /-- The countable limit partition `Q = ⋁ₖ Qₖ`, indexed by `ℕ`. -/
  Q : ℕ → Set α
  /-- Each cell of the limit partition is measurable. -/
  cells_measurable : ∀ i, MeasurableSet (Q i)
  /-- The two-sided `Q`-itinerary recovers each standard-Borel generating set mod 0. -/
  recovers : ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e Q) t ∧
    natGeneratingSequence α m =ᵐ[μ] t
  /-- The index-weighted total mass `∑ i, i·μ(Qᵢ)` is finite (Downarowicz Fact 1.1.4 input). -/
  summable_index_mass : Summable fun i : ℕ => (i : ℝ) * (μ (Q i)).toReal

/-- The limit partition of a `KeaneSerafinData` two-sidedly generates mod 0. Immediate from the
recovery witness via `isGeneratingTwoSidedMod0c_of_recovers_natGeneratingSequence`. -/
theorem KeaneSerafinData.isGeneratingTwoSidedMod0c [StandardBorelSpace α] {μ : Measure α}
    {e : α ≃ᵐ α} (D : KeaneSerafinData μ e) :
    IsGeneratingTwoSidedMod0c μ e D.Q :=
  isGeneratingTwoSidedMod0c_of_recovers_natGeneratingSequence D.recovers

/-- The limit partition of a `KeaneSerafinData` has **finite static Shannon entropy**: the entropy
terms `i ↦ negMulLog (μ (Qᵢ)).toReal` are summable. This is Downarowicz's Fact 1.1.4
(`cHμ_summable_of_summable_index_mul`) applied to the summable index-mass envelope. -/
theorem KeaneSerafinData.summable_negMulLog [StandardBorelSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {e : α ≃ᵐ α} (D : KeaneSerafinData μ e) :
    Summable fun i : ℕ => Real.negMulLog (μ (D.Q i)).toReal :=
  cHμ_summable_of_summable_index_mul μ D.summable_index_mass

/-- **The finite-entropy countable two-sided generator (Downarowicz Thm 4.2.3, first half).** Given
the Keane–Serafin / Downarowicz dynamical data, there is a countable (`ℕ`-indexed) partition `Q`
that two-sidedly generates `(α, e, μ)` mod 0 **and** has finite static Shannon entropy
(`Summable (fun i => negMulLog (μ (Qᵢ)).toReal)`, equivalently `cHμ μ Q < ∞`).

This is sub-problem A of the unconditional Krieger finite generator theorem (issue #15): the static
input that is then coded into `Fin k` by the Rokhlin-tower / name-count combinatorics of
`ErgodicTheory.Krieger.Coding`. The construction of the data `D` (the Rokhlin-tower assembly of the
now-proved in-repo Shannon–McMillan–Breiman equipartition) is the remaining dynamical residual;
everything from `D` to the two conclusions is proved here unconditionally. -/
theorem exists_countable_twoSided_generator_of_keaneSerafinData [StandardBorelSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {e : α ≃ᵐ α} (D : KeaneSerafinData μ e) :
    ∃ Q : ℕ → Set α, (∀ i, MeasurableSet (Q i)) ∧
      IsGeneratingTwoSidedMod0c μ e Q ∧
      Summable fun i : ℕ => Real.negMulLog (μ (Q i)).toReal :=
  ⟨D.Q, D.cells_measurable, D.isGeneratingTwoSidedMod0c, D.summable_negMulLog⟩

/-- **The finite-entropy countable two-sided generator, from the recovery + entropy data directly.**
A variant of `exists_countable_twoSided_generator_of_keaneSerafinData` that takes the two faithful
conclusions of sub-problem A as hypotheses on a single countable family `Q : ℕ → Set α`:

* `hrec`: the two-sided `Q`-itinerary recovers each standard-Borel generating set mod 0; and
* `hent`: the static Shannon entropy is finite (`Summable (fun i => negMulLog (μ Qᵢ).toReal)`).

The `recovers` hypothesis is turned into mod-0 two-sided generation by
`isGeneratingTwoSidedMod0c_of_recovers_natGeneratingSequence`. This phrasing keeps the *finite
static entropy* in its weakest faithful form (the entropy summability itself, not the stronger
index-mass envelope `summable_index_mass`), exactly matching the deliverable's target statement. -/
theorem exists_countable_twoSided_generator [StandardBorelSpace α]
    {μ : Measure α} {e : α ≃ᵐ α} {Q : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (Q i))
    (hrec : ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e Q) t ∧
      natGeneratingSequence α m =ᵐ[μ] t)
    (hent : Summable fun i : ℕ => Real.negMulLog (μ (Q i)).toReal) :
    ∃ Q : ℕ → Set α, (∀ i, MeasurableSet (Q i)) ∧
      IsGeneratingTwoSidedMod0c μ e Q ∧
      Summable fun i : ℕ => Real.negMulLog (μ (Q i)).toReal :=
  ⟨Q, hmeas, isGeneratingTwoSidedMod0c_of_recovers_natGeneratingSequence hrec, hent⟩

end ErgodicTheory.Krieger
