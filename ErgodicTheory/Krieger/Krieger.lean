/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.Generator
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Krieger's finite generator theorem — headline assembly (Krieger M3)

This file states and proves the **headline assembly** of Krieger's finite generator theorem
(issue #15), reducing it to the upstream Rokhlin-tower / name-count coding construction through the
recovery core of `ErgodicTheory.Krieger.Coding`.

## The theorem

Let `e : α ≃ᵐ α` be an **ergodic, aperiodic, measure-preserving automorphism** of a standard-Borel
probability space `(α, μ)`. If `k : ℕ` satisfies `(ksEntropy he).toReal < Real.log k` — the
Kolmogorov–Sinai entropy of the system is below `log k` — then `e` admits a **finite two-sided
generator of size `≤ k`**: a partition `P : MeasurePartition μ (Fin k)` that is
`IsGeneratingTwoSidedMod0` (generates mod 0).

The proof has three layers, of which this file is the top:

* **M1 (Rokhlin tower).** A tower of height `N` over a base `B` covers all but `ε`.
* **M2 (name count).** `(1 / N) · info ≤ h` a.e., so the number of distinct `N`-names of a fixed
  generator `Q` along the tower columns is `≤ kᴺ` up to `ε` whenever `log k > h`.
* **M3 (coding + recovery, this development).** The combinatorics of M1+M2 build a `Fin k`-valued
  partition `P` that **codes** a (two-sided) generator `Q` **mod 0** — i.e. the two-sided
  `P`-itinerary recovers each `Q`-cell up to a μ-null set (`ErgodicTheory.Krieger.CodesTwoSidedMod0c`).
  The recovery core (`ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0c.of_codesc`) then promotes `P` to a
  two-sided generator mod 0.

## Why *mod 0*

Generators in ergodic theory always generate the σ-algebra **up to null sets** (mod 0): the Krieger
construction produces an a.e.-defined, a.e.-invertible code, which recovers each generator cell
only modulo a μ-null set. Against an honest standard-Borel (non-`μ`-complete) `mα` this *cannot*
establish a literal σ-algebra equality, so the headline is — faithfully — phrased with the mod-0
conditions `IsGeneratingTwoSidedMod0` / `CodesTwoSidedMod0c` (the μ-completion of the two-sided
saturation is the full ambient). See `ErgodicTheory.Krieger.Coding` for the mod-0 development and
`ErgodicTheory.Krieger.isGeneratingTwoSidedMod0_of_literal` for faithfulness (literal ⟹ mod 0).

## What is proved here, and what is supplied

The **recovery half** — that a mod-0 code of a mod-0 two-sided generator is a mod-0 two-sided
generator — is proved *unconditionally* in `ErgodicTheory.Krieger.Coding` and is wired in here. The
**coding-existence half** — that `log k > h` (plus ergodicity, aperiodicity, the Rokhlin tower and
the name count) yields a `Fin k`-valued mod-0 code of a two-sided generator — is the genuine
combinatorial crux of Krieger's theorem; it is consumed here through the named hypothesis
`KriegerCodingData` (the existence of the coded partition), exactly the object the M1+M2 layers
produce. Both packaged forms are provided:

* `krieger_finite_generator_of_coding`: the clean assembly — given a `KriegerCodingData`, exhibit
  the finite mod-0 two-sided generator. **Fully proved, unconditionally.**
* `krieger_finite_generator`: the faithful headline carrying all of Krieger's hypotheses
  (ergodicity, aperiodicity, measure preservation, and the entropy threshold
  `(ksEntropy he).toReal < Real.log k`, pinned to the genuine system entropy — not a free real)
  together with the coding-existence hypothesis; it specializes the assembly. Its proof consumes
  *only* the coding hypothesis; the entropy threshold and dynamical hypotheses are the inputs the
  upstream coding construction consumes to *produce* the `KriegerCodingData`, carried here so the
  statement matches Krieger's theorem and so the orchestrator can discharge the coding hypothesis by
  wiring M1+M2.

## Main definitions

* `ErgodicTheory.Krieger.Aperiodic`: a.e.-aperiodicity of `e` (no nontrivial periodic points up to a
  null set) — the form the Rokhlin lemma consumes.
* `ErgodicTheory.Krieger.KriegerCodingData`: the existence of a `Fin k`-valued mod-0 code of a mod-0
  two-sided generator — the conclusion of the M1+M2 coding combinatorics.

## Main results

* `ErgodicTheory.Krieger.krieger_finite_generator_of_coding`: the recovery assembly.
* `ErgodicTheory.Krieger.krieger_finite_generator`: the headline Krieger finite generator theorem,
  modulo the supplied coding-existence hypothesis.

## References

* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*,
  Trans. Amer. Math. Soc. **149** (1970), 453–464.
* Manfred Einsiedler, Elon Lindenstrauss and Thomas Ward, *Entropy in Ergodic Theory and
  Homogeneous Dynamics*, §3 (the Krieger generator theorem).
* Eli Glasner, *Ergodic Theory via Joinings*, AMS (2003) — Krieger chapter.
* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011).
-/

open MeasureTheory Function MeasurableSpace

namespace ErgodicTheory.Krieger

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α}

open ErgodicTheory.Entropy

/-- **A.e.-aperiodicity of the automorphism `e`.** For every nonzero integer `n`, the set of
`n`-periodic points `{x | eⁿ x = x}` is `μ`-null. Equivalently: `μ`-a.e. point has trivial
stabiliser under the `ℤ`-action `n ↦ eⁿ`. This is the standard measure-theoretic aperiodicity
hypothesis under which Rokhlin's lemma (the M1 tower) holds; for an ergodic automorphism of a
non-atomic probability space it is automatic, but it is kept explicit here as the hypothesis the
tower construction consumes. -/
def Aperiodic (e : α ≃ᵐ α) (μ : Measure α) : Prop :=
  ∀ n : ℤ, n ≠ 0 → μ {x | ziter e n x = x} = 0

/-- **The coding data produced by the Krieger combinatorics (M1 + M2).** Bundles the
measure-preservation of `e`, a **countable** index type `κ` with a family of cells `Q` that
two-sidedly generates `(α, e, μ)` **mod 0** (`ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0c`, the
`Countable`-layer condition), together with a `Fin k`-valued partition `P` that *codes* the
countable `Q` two-sidedly **mod 0** across the two layers (the two-sided `P`-itinerary recovers each
`Q`-cell up to a μ-null set, `ErgodicTheory.Krieger.CodesTwoSidedMod0c`).

This is exactly the object the unconditional Krieger construction yields when `Real.log k > h`: `Q`
is the **countable finite-entropy two-sided generator** produced by the Keane–Serafin / Downarowicz
half (`ErgodicTheory.Krieger.exists_countable_twoSided_generator`, sub-problem A), and `P` is the
column-coding `Fin k` partition built from the `≤ kᴺ` name bound (sub-problem B), which recovers the
countable `Q`-name only a.e. The two saturation layers — the `Countable` layer of `Generator.lean`
for `Q` and the `Fintype` layer of `Coding.lean` for `P` — are bridged by `CodesTwoSidedMod0c`. The
headline turns a `KriegerCodingData` into a finite mod-0 two-sided generator by the cross-layer
recovery `ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0c.of_codesc`. The measure-preservation `mp` is
carried because that recovery needs it: preimage under the iterates `eⁿ` must commute with the
μ-completion. -/
structure KriegerCodingData (e : α ≃ᵐ α) (μ : Measure α) (k : ℕ) where
  /-- `e` is measure preserving (needed for mod-0 shift-invariance of the saturation). -/
  mp : MeasurePreserving (e : α → α) μ μ
  /-- The (countable) index type of the auxiliary generator `Q`. -/
  κ : Type*
  /-- `κ` is countable — `Q` is a countable (finite-entropy) generator. -/
  countableκ : Countable κ
  /-- A countable family of cells that two-sidedly generates the dynamics mod 0. -/
  gen : κ → Set α
  /-- Each cell of the countable generator is measurable. -/
  gen_measurable : ∀ i, MeasurableSet (gen i)
  /-- The candidate `Fin k`-valued coding partition. -/
  code : MeasurePartition μ (Fin k)
  /-- The countable generator `Q = gen` two-sidedly generates `(α, e, μ)` mod 0. -/
  gen_generating : IsGeneratingTwoSidedMod0c μ e gen
  /-- The coding partition `P = code` codes the countable `Q` two-sidedly mod 0 (cross-layer): its
  two-sided itinerary recovers each cell of `Q` up to a μ-null set. -/
  code_codes : CodesTwoSidedMod0c e gen code

attribute [instance] KriegerCodingData.countableκ

/-- **The recovery assembly of Krieger's theorem.** Given coding data `D` — a `Fin k`-valued
partition `D.code` that two-sidedly codes, mod 0, the **countable** mod-0 two-sided generator
`D.gen` — the coding partition itself is a finite **mod-0** two-sided generator. This is the
unconditional top layer: it is exactly the cross-layer recovery
`ErgodicTheory.Krieger.CodesTwoSidedMod0c.isGeneratingTwoSidedMod0` applied to `D`, repackaged as an
existence statement (bridging the `Countable` generator layer to the `Fintype` coding layer).

No entropy, ergodicity, or aperiodicity hypotheses enter here: those are consumed *upstream*, in
producing the coding data `D`. This lemma is the pure recovery content of Krieger's theorem. -/
theorem krieger_finite_generator_of_coding {e : α ≃ᵐ α} {k : ℕ}
    (D : KriegerCodingData e μ k) :
    ∃ P : MeasurePartition μ (Fin k), IsGeneratingTwoSidedMod0 e P :=
  ⟨D.code, D.code_codes.isGeneratingTwoSidedMod0 D.mp D.gen_generating⟩

/-- **Krieger's finite generator theorem (headline assembly).**

Let `e : α ≃ᵐ α` be an ergodic, aperiodic, measure-preserving automorphism of a standard-Borel
probability space `(α, μ)`. If `k : ℕ` satisfies `(ksEntropy he).toReal < Real.log k` — the
**actual** Kolmogorov–Sinai entropy of the system is below `log k` — and the Krieger coding
construction supplies a `Fin k`-valued mod-0 code of a mod-0 two-sided generator
(`KriegerCodingData e μ k`), then `e` admits a **finite two-sided generator of size `≤ k`, mod 0**:
a partition `P : MeasurePartition μ (Fin k)` with `IsGeneratingTwoSidedMod0 e P` (the μ-completion
of its two-sided saturation is the full ambient σ-algebra). The mod-0 conclusion is the standard,
faithful form of Krieger's theorem: ergodic-theory generators generate up to null sets (see
`ErgodicTheory.Krieger.Coding`).

The entropy threshold is stated as `(ksEntropy he).toReal < Real.log k`, so `he` names the actual
measure-preservation and the threshold is pinned to the genuine Kolmogorov–Sinai entropy
`ksEntropy he` of the system — it is *not* a free real, so the hypothesis is a real entropy
constraint (not vacuously satisfiable).

**What the proof consumes.** The proof term is `krieger_finite_generator_of_coding hcode`: it uses
*only* the coding hypothesis `hcode`, which already carries the measure-preservation it needs. The
dynamical hypotheses (`he`, `_herg`, `_hap`) and the entropy threshold `_hk` are carried so that the
statement is the faithful specialization of Krieger's theorem — they are precisely the inputs the
upstream M1 (Rokhlin tower) and M2 (name count) layers consume to *produce* the coding data `hcode`.
When M1+M2 are wired in, `hcode` is discharged from `he`, `_herg`, `_hap`, and `_hk`, yielding the
unconditional theorem with no change to this interface; until then this file proves the honest
conditional form, whose only nontrivial input is `hcode`. -/
theorem krieger_finite_generator [IsProbabilityMeasure μ] {e : α ≃ᵐ α}
    (he : MeasurePreserving (e : α → α) μ μ) (_herg : Ergodic (e : α → α) μ)
    (_hap : Aperiodic e μ) {k : ℕ} (_hk : (ksEntropy he).toReal < Real.log k)
    (hcode : KriegerCodingData e μ k) :
    ∃ P : MeasurePartition μ (Fin k), IsGeneratingTwoSidedMod0 e P :=
  krieger_finite_generator_of_coding hcode

end ErgodicTheory.Krieger
