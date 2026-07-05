/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.Generator
import ErgodicTheory.Krieger.RokhlinTower
import ErgodicTheory.Krieger.SMBSharp

/-!
# The Keane–Serafin inductive assembly (Krieger sub-problem A, dynamical core)

This file develops the **inductive assembly** of the Keane–Serafin / Downarowicz construction
(Keane–Serafin, *On the countable generator theorem*, Fund. Math. **157** (1998), 255–259;
Downarowicz, *Entropy in Dynamical Systems*, Thm 4.2.3, first half): the construction that turns
the per-step Keane–Serafin refinement lemma into the `KeaneSerafinData` of
`ErgodicTheory.Krieger.Generator`, whence the finite-entropy countable two-sided generator
(`exists_countable_twoSided_generator`) becomes unconditional.

## The construction (Keane–Serafin 1998)

Keane–Serafin produce, **inductively**, an increasing sequence `Q₀ ⪯ Q₁ ⪯ ⋯` of finite partitions
with `Q₀ = {X}`, where at step `k` one applies the Keane–Serafin **Lemma** with `ε = 2^{-(k+1)}`,
`P = Qₖ`, `A = Bₖ := natGeneratingSequence α k` to get `Q_{k+1}`. The Lemma guarantees:

1. `Qₖ ⪯ Q_{k+1}` (refinement);
2. `Bₖ ∈ ⋁ₙ eⁿ σ(Q_{k+1})` mod 0 (the two-sided itinerary of `Q_{k+1}` recovers `Bₖ`); and
3. `H(Q_{k+1}) ≤ H(Qₖ) + gₖ + 2^{-(k+1)}` where `gₖ = h(e, Q̄ₖ) − h(e, Qₖ)` is the **dynamical
   entropy gap** (`Q̄ₖ := Qₖ ∨ {Bₖ, Bₖᶜ}`).

Telescoping (3) with the Pinsker bound `h(e, Q̄ₖ) − h(e, Qₖ) ≤ H(Q_{k+1}) − H(Qₖ)`(*) and the finite
KS entropy `h := h(e) < ∞` (the load-bearing finiteness shortcut) gives the **uniform** static
bound `sup_k H(Qₖ) ≤ h + 1 < ∞`. The limit countable partition `Q := ⋁ₖ Qₖ` then has finite static
entropy, and its two-sided itinerary recovers every `Bₖ`, hence two-sidedly generates mod 0.

(*) In the elementary Keane–Serafin write-up the entropy increment of step `k` is controlled
directly by the count bound `Jₖ ≤ e^{(gₖ+2δ)m}` on the number of surviving sub-atoms per row, which
comes from the **Shannon–McMillan–Breiman convergence in probability** ("most atoms of the `m`-block
join have measure `≈ e^{−hm}`"). This is the one genuinely analytic ingredient.

## The single dynamical residual: the per-step Keane–Serafin Lemma

The per-step Lemma (3) is **not** re-derived here: its proof combines the *in-probability*
Shannon–McMillan–Breiman theorem (the equipartition `μ(atom) ∈ [e^{−(h+δ)m}, e^{−(h−δ)m}]` for most
`m`-block atoms) with a row-organized Rokhlin-tower marker-painting. The SMB ingredient is now
**proved** in the repository (`ErgodicTheory.Krieger.UpperSMB`, `SMBLeaves`): the pointwise a.e. SMB
`ae_tendsto_div_infoFun_self`, its in-measure upper bound `upperSMBInMeasure_of_ergodic`, and the
underlying Chung/Maker leaves `chungTail`, `lintegral_condInfoMaxFun_lt_top`, `makerTail`.
What is left un-formalized is only the Rokhlin-tower construction producing `Q`. The
in-probability equipartition is genuinely load-bearing for the count bound `Jₖ ≤ e^{(gₖ+2δ)m}`,
hence for the entropy economy of the step, hence for `summable_index_mass`.

We therefore expose the per-step output as the **honest hypothesis bundle** `KeaneSerafinStep`,
capturing exactly what the SMB-driven Lemma produces for the *whole* enumerated limit family:

* a countable family `Q : ℕ → Set α` of measurable cells (the join `⋁ₖ Qₖ`, atoms enumerated);
* `recovers`: the two-sided `Q`-itinerary recovers each `Bₘ` mod 0 (the *generation* witness — the
  faithful form of (1)+(2) for the union/join family); and
* an **enumerated geometric mass envelope** `mass_envelope`: `μ(Qᵢ) ≤ Cᵢ` with `∑ i·Cᵢ < ∞` — the
  faithful, directly-`summable_index_mass`-feeding form of the entropy economy (3).

The **inductive assembly** `keaneSerafinData_of_step` then produces `KeaneSerafinData` from a
`KeaneSerafinStep` **unconditionally and sorry-free**. The remaining dynamical residual is the
Rokhlin-tower construction producing the geometric mass envelope from the (now proved in-repo) SMB
equipartition, isolated in `KeaneSerafinStep`, exactly mirroring how `ErgodicTheory.Krieger.Krieger`
isolates the M1+M2 combinatorics in `KriegerCodingData`.

## Why a hypothesis bundle and not an outright construction

The outright construction of `KeaneSerafinData` (no hypotheses beyond ergodic/aperiodic
measure-preserving `e` of finite entropy) needs, on top of the in-probability SMB — now **proved**
in-repo (`upperSMBInMeasure_of_ergodic`, `ae_tendsto_div_infoFun_self`) — the Rokhlin-tower
marker-painting that turns the SMB output into `Q`, which is not formalized. Bundling that output is
the faithful reduction: it keeps the *structural* content — turning two-sided recovery into mod-0
generation, and the geometric mass envelope into finite static Shannon entropy (Downarowicz Fact
1.1.4, `cHμ_summable_of_summable_index_mul`) — proved here, while the open dynamical residual is
named, not faked. See the module note at the end for the precise residual.

## References

* Michael S. Keane and Jacek Serafin, *On the countable generator theorem*, Fund. Math. **157**
  (1998), 255–259.
* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Theorem 4.2.3) and
  §1.1 (Fact 1.1.4).
* Vladimir Rokhlin, *Generators in ergodic theory, II*, Vestnik Leningrad. Univ. (1965).
-/

open MeasureTheory Function MeasurableSpace Filter

namespace ErgodicTheory.Krieger

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The per-step Keane–Serafin output bundle

`KeaneSerafinStep` captures, in faithful form, the output of the (SMB-driven) Keane–Serafin
inductive construction for the *whole enumerated limit family* `Q := ⋁ₖ Qₖ`: a countable family of
measurable cells whose two-sided itinerary recovers every standard-Borel generating set mod 0, and
whose cell measures obey an enumerated geometric mass envelope `μ(Qᵢ) ≤ Cᵢ` with `∑ i·Cᵢ < ∞`. -/

/-- **The Keane–Serafin step output** (the faithful SMB-residual hypothesis bundle for sub-problem
A). It bundles the enumerated limit partition `Q : ℕ → Set α` of the Keane–Serafin construction
together with the two facts the SMB-driven per-step Lemma + Rokhlin tower guarantee:

* `cells_measurable`: each cell is measurable;
* `recovers`: the two-sided `Q`-itinerary recovers each standard-Borel generating set
  `natGeneratingSequence α m` mod 0 — the **generation** witness;
* a **summable index-mass envelope** `mass_envelope`/`mass_le`: there is `C : ℕ → ℝ` with
  `μ(Qᵢ).toReal ≤ Cᵢ` and `∑ i, i·Cᵢ < ∞` — the **finite static entropy** witness in the directly
  `summable_index_mass`-feeding form (Downarowicz Fact 1.1.4 input). The geometric envelope is what
  the row-by-row organization of the Keane–Serafin construction (per-step measure `≤ 2^{−k}`,
  geometric decay) produces; it is strictly the SMB content, isolated here. -/
structure KeaneSerafinStep [StandardBorelSpace α] (μ : Measure α) (e : α ≃ᵐ α) where
  /-- The enumerated limit partition `Q = ⋁ₖ Qₖ`. -/
  Q : ℕ → Set α
  /-- Each cell of the limit partition is measurable. -/
  cells_measurable : ∀ i, MeasurableSet (Q i)
  /-- The two-sided `Q`-itinerary recovers each standard-Borel generating set mod 0. -/
  recovers : ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e Q) t ∧
    natGeneratingSequence α m =ᵐ[μ] t
  /-- The geometric mass envelope `Cᵢ ≥ μ(Qᵢ)` (the SMB-produced per-row geometric decay). -/
  C : ℕ → ℝ
  /-- Each cell measure is bounded by its envelope value. -/
  mass_le : ∀ i, (μ (Q i)).toReal ≤ C i
  /-- The envelope is index-summable: `∑ i, i·Cᵢ < ∞`. -/
  envelope_summable : Summable fun i : ℕ => (i : ℝ) * C i

/-! ### The inductive assembly: `KeaneSerafinStep ⟹ KeaneSerafinData`

The assembly is the unconditional structural step: the enumerated geometric mass envelope
`μ(Qᵢ) ≤ Cᵢ` with `∑ i·Cᵢ < ∞` yields the `summable_index_mass` field
`Summable (fun i => i·μ(Qᵢ).toReal)` by termwise comparison (each `i·μ(Qᵢ) ≤ i·Cᵢ` for `i ≥ 0`),
and `recovers`/`cells_measurable` carry over verbatim. -/

/-- **The Keane–Serafin index-mass comparison.** A geometric mass envelope `μ(Qᵢ).toReal ≤ Cᵢ`
with `∑ i·Cᵢ < ∞` certifies the `summable_index_mass` field directly: the index-weighted measure
sequence `i ↦ i·μ(Qᵢ).toReal` is dominated termwise by the summable `i ↦ i·Cᵢ` (and is nonnegative),
so it is summable. This is the directly-`KeaneSerafinData`-feeding form of the entropy economy. -/
theorem summable_index_mass_of_envelope [StandardBorelSpace α] {e : α ≃ᵐ α}
    (S : KeaneSerafinStep μ e) :
    Summable fun i : ℕ => (i : ℝ) * (μ (S.Q i)).toReal := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) S.envelope_summable
  exact mul_le_mul_of_nonneg_left (S.mass_le i) (by positivity)

/-- **The Keane–Serafin data from a step.** The enumerated limit partition of a `KeaneSerafinStep`,
together with its recovery witness and the index-mass comparison `summable_index_mass_of_envelope`,
assembles into the `KeaneSerafinData` of `ErgodicTheory.Krieger.Generator` — the dynamical input to the
finite-entropy countable two-sided generator. **Unconditional and sorry-free.** -/
noncomputable def KeaneSerafinStep.toData [StandardBorelSpace α] {e : α ≃ᵐ α}
    (S : KeaneSerafinStep μ e) : KeaneSerafinData μ e where
  Q := S.Q
  cells_measurable := S.cells_measurable
  recovers := S.recovers
  summable_index_mass := summable_index_mass_of_envelope S

/-- **The finite-entropy countable two-sided generator from a Keane–Serafin step.** A
`KeaneSerafinStep` produces a countable (`ℕ`-indexed) partition `Q` that two-sidedly generates
`(α, e, μ)` mod 0 **and** has finite static Shannon entropy. This is
`exists_countable_twoSided_generator_of_keaneSerafinData` fed the assembled data — the headline of
sub-problem A, conditional only on the (faithful, SMB-residual) `KeaneSerafinStep`. -/
theorem exists_countable_twoSided_generator_of_step [StandardBorelSpace α]
    [IsProbabilityMeasure μ] {e : α ≃ᵐ α} (S : KeaneSerafinStep μ e) :
    ∃ Q : ℕ → Set α, (∀ i, MeasurableSet (Q i)) ∧
      IsGeneratingTwoSidedMod0c μ e Q ∧
      Summable fun i : ℕ => Real.negMulLog (μ (Q i)).toReal :=
  exists_countable_twoSided_generator_of_keaneSerafinData S.toData

/-! ### The multi-level structural assembly

The Keane–Serafin construction is *inductive*: it produces an increasing sequence of finite
partitions `Qₖ`, with the level-`k` two-sided itinerary recovering the `k`-th generating set `Bₖ`
mod 0, and the level cells placed (after the row-organization) with geometrically decaying measure.
This subsection assembles such per-level data into a single `KeaneSerafinStep` (hence a
`KeaneSerafinData`), **unconditionally**:

* the per-level cells are collected into the union family `Q⁺ ⟨k, i⟩ := Q k i` (a `ℕ × ℕ`-indexed
  family, re-indexed to `ℕ`), whose two-sided saturation contains every level's saturation
  (`ctwoSidedSat_mono_of_range_subset`), so per-level recovery lifts to `recovers`
  (`recovers_union_of_levelRecovers`); and
* the per-cell geometric envelope is carried verbatim under the re-indexing.

The level cells `Q k i` are the *enumerated* cells of the Keane–Serafin construction (e.g. the
genuine join atoms placed in rows); the only SMB-dependent input is the geometric envelope
`mass_le`/`envelope_summable`, which the row-organization supplies. -/

/-- **Range-monotonicity of the countable two-sided saturation.** If `range Q ⊆ range Q'` then the
two-sided itinerary σ-algebra grows: `ctwoSidedSat e Q ≤ ctwoSidedSat e Q'`. Indeed
`generateFrom (range Q) ≤ generateFrom (range Q')` by `generateFrom_mono`, and `comap` and the
`ℤ`-supremum are monotone. This is the engine of recovery-lifting: a recovery witness measurable in
a sub-family's saturation is a fortiori measurable in the larger family's saturation. -/
theorem ctwoSidedSat_mono_of_range_subset {κ κ' : Type*} (e : α ≃ᵐ α)
    {Q : κ → Set α} {Q' : κ' → Set α} (hsub : Set.range Q ⊆ Set.range Q') :
    ctwoSidedSat e Q ≤ ctwoSidedSat e Q' := by
  rw [ctwoSidedSat_def, ctwoSidedSat_def]
  exact iSup_mono fun n => MeasurableSpace.comap_mono (MeasurableSpace.generateFrom_mono hsub)

/-- **Recovery of the union family from per-level recovery.** If, for each `m`, the level-`m`
two-sided saturation recovers `natGeneratingSequence α m` mod 0, then the **union family**
`Q⁺ p := Q p.1 p.2` (over `ℕ × ℕ`) also recovers each generating set mod 0: each level-`m`
saturation embeds into the union family's saturation (the union family's range contains the
level-`m` range), so a level-`m` witness lifts. This is the `recovers`-field form of the reduction
`isGeneratingTwoSidedMod0c_sigmaUnion_of_levelRecovers` (which states the *generation* conclusion;
here we keep the per-`m` witnesses, as `KeaneSerafinStep.recovers` requires). -/
theorem recovers_union_of_levelRecovers [StandardBorelSpace α] {e : α ≃ᵐ α} (Q : ℕ → ℕ → Set α)
    (hrec : ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e (Q m)) t ∧
      natGeneratingSequence α m =ᵐ[μ] t) :
    ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e (fun p : ℕ × ℕ => Q p.1 p.2)) t ∧
      natGeneratingSequence α m =ᵐ[μ] t := by
  intro m
  obtain ⟨t, ht, hBt⟩ := hrec m
  -- `range (Q m) ⊆ range (union family)`: the cell `Q m i` is `Q⁺ (m, i)`.
  have hsub : Set.range (Q m) ⊆ Set.range (fun p : ℕ × ℕ => Q p.1 p.2) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(m, i), rfl⟩
  exact ⟨t, ctwoSidedSat_mono_of_range_subset e hsub _ ht, hBt⟩

/-- **The per-level Keane–Serafin data** (the inductive form of `KeaneSerafinStep`). It bundles an
increasing sequence of finite partitions, presented as a `ℕ × ℕ`-indexed family `Q : ℕ → ℕ → Set α`
(level `k`, cell `i`), with:

* `cells_measurable`: each cell `Q k i` is measurable;
* `levelRecovers`: the level-`k` two-sided itinerary recovers `natGeneratingSequence α k` mod 0; and
* a **per-cell geometric envelope** `C : ℕ → ℕ → ℝ`, `μ(Q k i).toReal ≤ C k i`, whose `ℕ × ℕ`-sum
  `∑_{k,i} (enumeration index)·C k i` is summable.

The assembly `KeaneSerafinLevels.toStep` re-indexes `ℕ × ℕ → ℕ` to produce a `KeaneSerafinStep`. -/
structure KeaneSerafinLevels [StandardBorelSpace α] (μ : Measure α) (e : α ≃ᵐ α) where
  /-- The level-`k`, cell-`i` partition cell. -/
  Q : ℕ → ℕ → Set α
  /-- Each cell is measurable. -/
  cells_measurable : ∀ k i, MeasurableSet (Q k i)
  /-- The level-`k` two-sided itinerary recovers `natGeneratingSequence α k` mod 0. -/
  levelRecovers : ∀ m, ∃ t, @MeasurableSet α (ctwoSidedSat e (Q m)) t ∧
    natGeneratingSequence α m =ᵐ[μ] t
  /-- The per-cell geometric envelope. -/
  C : ℕ → ℕ → ℝ
  /-- Each cell measure is bounded by its envelope value. -/
  mass_le : ∀ k i, (μ (Q k i)).toReal ≤ C k i
  /-- The envelope, transported to the `ℕ`-enumeration, is index-summable. -/
  envelope_summable : Summable fun n : ℕ =>
    (n : ℝ) * C (Nat.unpair n).1 (Nat.unpair n).2

/-- **The Keane–Serafin step from per-level data.** Re-indexing the union family `Q⁺ p := Q p.1 p.2`
through the pairing equivalence `ℕ ≃ ℕ × ℕ` (`Nat.unpair`), the per-level recovery lifts to the
enumerated family (`recovers_union_of_levelRecovers`), and measurability and the geometric envelope
carry over verbatim, producing a `KeaneSerafinStep`. **Unconditional and sorry-free.** -/
noncomputable def KeaneSerafinLevels.toStep [StandardBorelSpace α] {e : α ≃ᵐ α}
    (L : KeaneSerafinLevels μ e) : KeaneSerafinStep μ e where
  Q := fun n => L.Q (Nat.unpair n).1 (Nat.unpair n).2
  cells_measurable := fun n => L.cells_measurable _ _
  recovers := by
    intro m
    -- Lift the level-`m` recovery to the union family, then transport along `Nat.unpair`.
    obtain ⟨t, ht, hBt⟩ := recovers_union_of_levelRecovers L.Q L.levelRecovers m
    refine ⟨t, ?_, hBt⟩
    -- `range (n ↦ Q⁺ (unpair n)) = range Q⁺`, so the saturations coincide.
    have hrange : Set.range (fun n => L.Q (Nat.unpair n).1 (Nat.unpair n).2) =
        Set.range (fun p : ℕ × ℕ => L.Q p.1 p.2) := by
      ext s
      constructor
      · rintro ⟨n, rfl⟩; exact ⟨Nat.unpair n, rfl⟩
      · rintro ⟨p, rfl⟩; exact ⟨Nat.pair p.1 p.2, by simp only [Nat.unpair_pair]⟩
    have hle : ctwoSidedSat e (fun p : ℕ × ℕ => L.Q p.1 p.2)
        ≤ ctwoSidedSat e (fun n => L.Q (Nat.unpair n).1 (Nat.unpair n).2) :=
      ctwoSidedSat_mono_of_range_subset e (hrange ▸ subset_refl _)
    exact hle _ ht
  C := fun n => L.C (Nat.unpair n).1 (Nat.unpair n).2
  mass_le := fun n => L.mass_le _ _
  envelope_summable := L.envelope_summable

/-- **The finite-entropy countable two-sided generator from per-level Keane–Serafin data.** The
inductive `KeaneSerafinLevels` (an increasing sequence of finite partitions with per-level recovery
and a per-cell geometric envelope) produces a countable partition `Q` two-sidedly generating
`(α, e, μ)` mod 0 with finite static Shannon entropy — sub-problem A, conditional only on the
SMB-residual per-level data. -/
theorem exists_countable_twoSided_generator_of_levels [StandardBorelSpace α]
    [IsProbabilityMeasure μ] {e : α ≃ᵐ α} (L : KeaneSerafinLevels μ e) :
    ∃ Q : ℕ → Set α, (∀ i, MeasurableSet (Q i)) ∧
      IsGeneratingTwoSidedMod0c μ e Q ∧
      Summable fun i : ℕ => Real.negMulLog (μ (Q i)).toReal :=
  exists_countable_twoSided_generator_of_step L.toStep

/-! ### The remaining dynamical residual (precise)

Everything above is **unconditional and sorry-free**. The single open residual for sub-problem A is
the construction of a `KeaneSerafinStep` (equivalently `KeaneSerafinLevels`) from the raw dynamical
hypotheses — an ergodic, aperiodic, measure-preserving `e` of a standard-Borel probability space
with **finite Kolmogorov–Sinai entropy** `h := (ksEntropy he).toReal < ∞`. Concretely, the residual
is the per-step **Keane–Serafin Lemma**:

> Given a finite partition `P`, a measurable set `A`, and `c > 0`, set `P̄ := P ∨ {A, Aᶜ}` and
> `g := h(e, P̄) − h(e, P)`. Then there is a finite partition `Q` with `P ⪯ Q`,
> `A ∈ ⋁ₙ eⁿ σ(Q)` mod 0, and `H(Q) ≤ H(P) + g + c`.

Its proof is the row-organized Rokhlin-tower marker-painting of Keane–Serafin §2. The
`rokhlin_tower` lemma (`ErgodicTheory.Krieger.RokhlinTower`) supplies the tower, and the
**in-probability Shannon–McMillan–Breiman theorem** it feeds on — for `δ > 0` and `m` large,
*most* atoms of the `m`-block join `⋁₀^{m−1} eⁿ P̄` have measure in `[e^{−(h̄+δ)m}, e^{−(h̄−δ)m}]`
(and likewise for `P`), which yields the per-row count bound `Jᵢ ≤ e^{(g+2δ)m}` driving the entropy
increment `H(Q') ≲ g` — is now **proved** in the repository: beyond the integral-level rate identity
`ksEntropyPartition_eq_condEntropy_iSup` (`ErgodicTheory.Krieger.SMBSharp`), the SMB development gives
the full pointwise a.e. SMB `ae_tendsto_div_infoFun_self` and the in-measure equipartition
`upperSMBInMeasure_of_ergodic` (`ErgodicTheory.Krieger.UpperSMB`), via the Chung/Maker leaves
`chungTail`, `lintegral_condInfoMaxFun_lt_top`, `makerTail` (`ErgodicTheory.Krieger.SMBLeaves`).
What is **not** yet formalized is only the marker-painting that turns this equipartition into the
refinement partition `Q` — the genuine, non-fakeable dynamical residual. Pending it,
`KeaneSerafinStep` / `KeaneSerafinLevels` is the faithful hypothesis boundary, and
`exists_countable_twoSided_generator_of_levels` is the unconditional reduction of sub-problem A
to it.

The `summable_index_mass` strengthening (vs. the weaker `H(Q) < ∞`) is *not* an extra obstacle: the
row-organized construction places the `Jᵢ ≈ e^{gm}` cells of row `i` (measures `≈ e^{−h̄m}`) at
consecutive enumeration indices, so the per-index envelope `Cᵢ` decays geometrically and
`∑ i·Cᵢ < ∞` is the natural output, fed directly into `KeaneSerafinStep.envelope_summable`. -/

end ErgodicTheory.Krieger
