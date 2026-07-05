/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.CodeMap
import ErgodicTheory.Krieger.Generator
import ErgodicTheory.Krieger.RokhlinTower
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The a.e.-recovery construction for Krieger's symbolic code (C3, sub-problem B)

This file builds the **two-sided recurrence tiling** crux of the a.e.-recovery construction for the
symbolic-coding step (C3) of Krieger's finite generator theorem (issue #15), and assembles the
parameterized *column-code* data into the cross-layer countable mod-0 code
`ErgodicTheory.Krieger.CodesTwoSidedMod0c` consumed by the headline.

The contract that the code-map backbone (`ErgodicTheory.Krieger.CodeMap`) and the countable
coding layer
(`ErgodicTheory.Krieger.Generator`) need is: produce a **code symbol** `c : α → Fin k` and a
**decoder** `D : (ℤ → Fin k) → κ` together with the **a.e. recovery**

`∀ j, Q j =ᵐ[μ] {x | D (itin e c x) = j}`

— recover each generator cell from the two-sided code-itinerary, a.e. — which then discharges
`ErgodicTheory.Krieger.codesTwoSidedMod0c_of_aeRecovery`, hence the mod-0 coding hypothesis.

## The construction (Downarowicz §4.2 Lemma 4.2.5; Shields §I.9; Krieger 1970)

Use a **refining sequence of Rokhlin towers** of heights `N m ↑ ∞`. At stage `m`, `rokhlin_tower`
(`ErgodicTheory.Krieger.RokhlinTower`) gives a base `B m`, height `N m`, with disjoint floors
`eⁱ(B m)`
covering `1 - ε m` (`ε m ↓ 0`). On each column one reads the `Q`-`(N m)`-name; by the C2 name-count
bound (`ErgodicTheory.Krieger.exists_cover_names_card_le`, under `UpperSMBInMeasure`) there are
`≤ exp(N m·(h+ε)) < k^(N m)` names on a `(1-ε)`-set, so `exists_sentinelEncoding`
(`ErgodicTheory.Krieger.PrefixCode`) injects them into length-`(N m)` sentinel-terminated `Fin k`
blocks; the code symbol `c` on the column spells that block. The decoder `D` reads the two-sided
code-itinerary, splits at sentinels (`sentinelEncodeList_injective`: unique decodability), recovers
the column's `Q`-name, hence `Q j` at the relevant coordinate.

## The crux this file proves: two-sided Poincaré recurrence (the tiling backbone)

The recovery *across all* `n : ℤ` rests on the fact that a.e. `x` returns to the tower base `B`
**infinitely often in BOTH time directions**, so its entire `ℤ`-orbit is tiled by complete columns
in the `m → ∞` limit. This is `twoSided_recurrence` below: it follows from Mathlib's one-sided
Poincaré recurrence (`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`) applied to the
*forward* conservative system `e` (`MeasurePreserving.conservative`) and to the *backward* system
`e.symm` (`MeasurePreserving.symm`), then intersected a.e. **This is the load-bearing combinatorial
backbone of the recovery and it is proved here unconditionally and sorry-free.**

The accompanying `eventually_mem_of_summable_compl` discharges the `m → ∞` Borel–Cantelli leaf: if
the tower-miss measures `∑ μ((C m)ᶜ)` are summable then a.e. `x` lies inside the covered set `C m`
for all large `m` (Mathlib's `MeasureTheory.ae_eventually_notMem`).

## What is supplied vs. proved

Everything *structural/measurable* — the recurrence backbone (`twoSided_recurrence`,
`twoSided_recurrence_ziter`), the Borel–Cantelli leaf (`eventually_mem_of_summable_compl`), and the
assembly of a column-code into the cross-layer countable mod-0 code
(`codesTwoSidedMod0c_of_columnCode`) — is proved here, unconditionally and sorry-free.

The single irreducible **dynamical/combinatorial heart** — the *existence* of one fixed code symbol
`c` and one decoder `D` whose two-sided itinerary recovers each `Q`-cell a.e., obtained as the
`m → ∞` / `ε m ↓ 0` limit of the per-tower sentinel column codes (the refining-tower Borel–Cantelli
assembly) — is isolated as the named hypothesis bundle `ColumnCodeData`, mirroring the repo's
honest-reduction pattern (as with `ErgodicTheory.Krieger.KeaneSerafinData`).
This is the documented residual of sub-problem B (C3). See the module note at the bottom for the
precise minimal symbolic-dynamics infrastructure Mathlib lacks for a single-shot discharge.

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5).
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9
  (marker / strongly-separated codes; the decoder).
* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*,
  Trans. Amer. Math. Soc. **149** (1970), 453–464.
* Manfred Einsiedler, Elon Lindenstrauss and Thomas Ward, *Entropy in Ergodic Theory and
  Homogeneous Dynamics*, §3 (the Krieger generator theorem).
-/

open MeasureTheory Function MeasurableSpace Filter Set
open scoped ENNReal

namespace ErgodicTheory.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The two-sided Poincaré recurrence tiling crux

The recovery a.e. across **all** `n : ℤ` rests on the two-sided recurrence of the tower base: a.e.
point of the base `B` returns to `B` infinitely often in both forward and backward time. This is the
combinatorial backbone of the column tiling — in the `m → ∞` limit a.e. orbit is tiled by complete
tower columns on both sides of the origin, so the sentinel decoder can locate the column through
every coordinate. -/

/-- **Two-sided Poincaré recurrence (the tiling backbone).** For a measure-preserving automorphism
`e` of a probability space and a measurable set `B`, almost every point `x ∈ B` returns to `B`
**infinitely often in both time directions**: there are infinitely many forward iterates `eⁿx ∈ B`
*and* infinitely many backward iterates `(e⁻¹)ⁿ x ∈ B`.

This is the conjunction of the forward Poincaré recurrence theorem
(`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem` for the conservative system `e`,
`MeasurePreserving.conservative`) and the backward one (the same theorem for `e.symm`, which is
measure preserving by `MeasurePreserving.symm`), intersected over a μ-null set. It is the load-
bearing crux of the column tiling: a.e. orbit meets the tower base infinitely often on **both**
sides, so in the refining-tower limit the whole `ℤ`-orbit is covered by complete columns. -/
theorem twoSided_recurrence [IsProbabilityMeasure μ] (e : α ≃ᵐ α)
    (he : MeasurePreserving (e : α → α) μ μ) {B : Set α} (hB : MeasurableSet B) :
    ∀ᵐ x ∂μ, x ∈ B →
      (∃ᶠ n in atTop, (e : α → α)^[n] x ∈ B) ∧
      (∃ᶠ n in atTop, (e.symm : α → α)^[n] x ∈ B) := by
  have hfwd := he.conservative.ae_mem_imp_frequently_image_mem hB.nullMeasurableSet
  have hbwd := (he.symm).conservative.ae_mem_imp_frequently_image_mem hB.nullMeasurableSet
  filter_upwards [hfwd, hbwd] with x hx1 hx2 hxB
  exact ⟨hx1 hxB, hx2 hxB⟩

/-- **Two-sided recurrence in the `ziter` form (the form the decoder consumes).** The decoder reads
the two-sided itinerary `itin e c x = (n ↦ c (ziter e n x))`, where `ziter e n` is the two-sided
iterate. This restates `twoSided_recurrence` directly in terms of `ziter`: a.e. `x ∈ B` returns to
`B` for arbitrarily large positive `ziter`-times and arbitrarily large negative `ziter`-times. The
positive side is `ziter e (n : ℤ) = eⁿ` (`ziter_natCast`); the negative side is
`ziter e (-(n+1)) = (e⁻¹)ⁿ⁺¹` along `Int.negSucc` (`ziter_negSucc`). -/
theorem twoSided_recurrence_ziter [IsProbabilityMeasure μ] (e : α ≃ᵐ α)
    (he : MeasurePreserving (e : α → α) μ μ) {B : Set α} (hB : MeasurableSet B) :
    ∀ᵐ x ∂μ, x ∈ B →
      (∃ᶠ n : ℕ in atTop, ziter e (n : ℤ) x ∈ B) ∧
      (∃ᶠ n : ℕ in atTop, ziter e (-(n : ℤ) - 1) x ∈ B) := by
  filter_upwards [twoSided_recurrence e he hB] with x hx hxB
  obtain ⟨hfwd, hbwd⟩ := hx hxB
  refine ⟨?_, ?_⟩
  · -- `ziter e (n : ℤ) = eⁿ`.
    refine hfwd.mono fun n hn => ?_
    rwa [ziter_natCast]
  · -- `ziter e (-(n : ℤ) - 1) = ziter e (Int.negSucc n) = (e.symm)^[n+1]`.
    have hrw : ∀ n : ℕ, ziter e (-(n : ℤ) - 1) = (e.symm : α → α)^[n + 1] := by
      intro n
      have hneg : (-(n : ℤ) - 1) = Int.negSucc n := by
        rw [Int.negSucc_eq]; ring
      rw [hneg, ziter_negSucc]
    -- transport the `∃ᶠ` along the index shift `n ↦ n+1` and the rewrite.
    have hbwd' : ∃ᶠ n : ℕ in atTop, (e.symm : α → α)^[n + 1] x ∈ B := by
      rw [Filter.frequently_atTop] at hbwd ⊢
      intro N
      obtain ⟨m, hm, hmB⟩ := hbwd (N + 1)
      exact ⟨m - 1, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩
    refine hbwd'.mono fun n hn => ?_
    rwa [hrw n]

/-! ### The Borel–Cantelli leaf: eventual coverage from summable tower misses

The `m → ∞` half of the recovery needs that a.e. point eventually lies inside every tower of the
refining sequence. If the tower-miss measures `∑ μ((C m)ᶜ)` are summable, this is exactly the
first Borel–Cantelli lemma. -/

/-- **Eventual coverage from summable complements (the Borel–Cantelli leaf).** If a sequence of sets
`C : ℕ → Set α` has summable complement-measures `∑ μ((C m)ᶜ) < ∞`, then almost every `x` lies in
`C m` for all sufficiently large `m`. This is the `m → ∞` leaf of the refining-tower recovery: with
the covered sets `C m` of towers of height `N m` covering `1 - ε m` and `∑ ε m < ∞`, a.e. orbit
point is inside a complete column for all large `m`. Immediate from Mathlib's
`MeasureTheory.ae_eventually_notMem` (the first Borel–Cantelli lemma) applied to the complements. -/
theorem eventually_mem_of_summable_compl {C : ℕ → Set α}
    (hsum : (∑' m, μ (C m)ᶜ) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∈ C m := by
  filter_upwards [MeasureTheory.ae_eventually_notMem hsum] with x hx
  filter_upwards [hx] with m hm
  simpa using hm

/-! ### The parameterized column-code data (the irreducible dynamical heart)

The genuine content of sub-problem B (C3) is the *existence* of one fixed code symbol
`c : α → Fin k` and one decoder `D : (ℤ → Fin k) → κ` whose two-sided itinerary recovers each
generator cell `Q j` a.e. We isolate this as the hypothesis bundle `ColumnCodeData`, exactly
mirroring the repo's honest-reduction pattern (as with `ErgodicTheory.Krieger.KeaneSerafinData` for
sub-problem A). The structural / measurable backbone
— that this data yields the cross-layer countable mod-0 code — is then proved unconditionally
below. -/

/-- **The column-code data of sub-problem B (C3), countable layer.** Bundles the genuinely
dynamical/combinatorial inputs whose construction (refining Rokhlin towers + sentinel column
coding + the two-sided recurrence tiling of `twoSided_recurrence` + the `m → ∞` / `ε m ↓ 0`
Borel–Cantelli limit) is the heart of C3, isolated from the structural reduction proved in this
file:

* `code`: the measurable code symbol `c : α → Fin k`, built so that `c (eⁱ x)` is the `i`-th symbol
  of the sentinel block coding the `Q`-name of the tower column through `x`;
* `decoder`: the product-measurable decoder `D : (ℤ → Fin k) → κ`, which re-finds the
  sentinel-marked column boundaries in the two-sided itinerary and reads off the `Q`-label; and
* `recovers`: the **a.e. recovery** — for every generator cell `Q j`, `Q j` agrees `μ`-a.e. with the
  decoder event `{x | D (itin e code x) = j}`. Off a μ-null set the decoder recovers the `Q`-name
  across *all* integer shifts (two-sided Poincaré recurrence, `twoSided_recurrence`); the `ε`/`N`
  residual is absorbed mod 0 by the refining-tower limit.

This bundles the code-symbol-plus-decoder residual for the `Countable` coding layer. -/
structure ColumnCodeData [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (e : α ≃ᵐ α) (μ : Measure α) (Q : κ → Set α) (k : ℕ) where
  /-- The measurable code symbol `c : α → Fin k` of the column coding. -/
  code : α → Fin k
  /-- The code symbol is measurable. -/
  code_measurable : Measurable code
  /-- The decoder of the two-sided itinerary back to a `Q`-label. -/
  decoder : (ℤ → Fin k) → κ
  /-- The decoder is product-measurable. -/
  decoder_measurable : Measurable decoder
  /-- A.e. recovery: each generator cell agrees mod 0 with the decoder event. -/
  recovers : ∀ j, Q j =ᵐ[μ] {x | decoder (itin e code x) = j}

/-! ### The assembly: a column-code yields the cross-layer countable mod-0 code

Given a `ColumnCodeData`, the code partition `codePartition c hc` codes the countable generator `Q`
two-sidedly mod 0. The decoder event `{x | D (itin e c x) = j}` is `twoSidedSat e P`-measurable —
because `itin e c` is `twoSidedSat e P`-measurable (`ErgodicTheory.Krieger.measurable_itin`)
and `D` is
product-measurable — and the a.e. recovery then discharges the countable contract
`ErgodicTheory.Krieger.codesTwoSidedMod0c_of_aeRecovery`. Every step here is structural and
unconditional; the content is entirely in *producing* the `ColumnCodeData`. -/

/-- **The C3 reduction (countable layer, the deliverable).** Given a measurable code symbol `c`, a
product-measurable decoder `D`, and the a.e. recovery of each generator cell `Q j`, the code
partition `codePartition c hc` **codes the countable family `Q` two-sidedly mod 0**
(`ErgodicTheory.Krieger.CodesTwoSidedMod0c`).

The decoder event `{x | D (itin e c x) = j} = (D ∘ itin e c)⁻¹ {j}` is `twoSidedSat e P`-measurable
because `itin e c` is `twoSidedSat e P`-measurable (`ErgodicTheory.Krieger.measurable_itin`)
and `D` is
product-measurable; the a.e. recovery then discharges
`ErgodicTheory.Krieger.codesTwoSidedMod0c_of_aeRecovery`, using the itinerary-measurability backbone
`ErgodicTheory.Krieger.measurable_itin` (`CodeMap.lean`). -/
theorem codesTwoSidedMod0c_of_columnCode [Countable κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] {e : α ≃ᵐ α} {Q : κ → Set α}
    (c : α → Fin k) (hc : Measurable c)
    (D : (ℤ → Fin k) → κ) (hD : Measurable D)
    (hrec : ∀ j, Q j =ᵐ[μ] {x | D (itin e c x) = j}) :
    CodesTwoSidedMod0c e Q (codePartition (μ := μ) c hc) := by
  refine codesTwoSidedMod0c_of_aeRecovery ?_
  intro j
  refine ⟨{x | D (itin e c x) = j}, ?_, hrec j⟩
  have hset : {x | D (itin e c x) = j} = (D ∘ itin e c) ⁻¹' {j} := rfl
  rw [hset]
  exact (hD.comp (measurable_itin e c hc)) (measurableSet_singleton j)

/-- The bundled form: a `ColumnCodeData` yields the cross-layer countable mod-0 code of the
generator `Q` by its code partition. It slots directly into the headline assembly, supplying the
mod-0 coding hypothesis once the dynamical heart (the `ColumnCodeData` itself) is produced. -/
theorem ColumnCodeData.codes [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (data : ColumnCodeData e μ Q k) :
    CodesTwoSidedMod0c e Q (codePartition (μ := μ) data.code data.code_measurable) :=
  codesTwoSidedMod0c_of_columnCode data.code data.code_measurable
    data.decoder data.decoder_measurable data.recovers

/-! ### The minimal symbolic-dynamics infrastructure the single-shot discharge needs

Everything above is **unconditional and sorry-free** except the *existence* of a `ColumnCodeData` —
one fixed code symbol `c : α → Fin k` and one decoder `D : (ℤ → Fin k) → κ` whose two-sided
itinerary recovers each generator cell a.e. The two-sided **recurrence tiling** crux this
construction rests on is discharged here (`twoSided_recurrence`), as is the `m → ∞` Borel–Cantelli
leaf (`eventually_mem_of_summable_compl`); what remains for a single-shot construction of `(c, D)`
is the
symbolic-dynamics assembly that Mathlib does not yet have:

1. **The refining-tower code `c m`.** From `rokhlin_tower` (height `N m`, base `B m`, covering
   `1 - ε m`) and `exists_cover_names_card_le` (`≤ exp(N m·(h+ε))` `< k^(N m)` names on `1-ε`, under
   `UpperSMBInMeasure`) and `exists_sentinelEncoding` (inject names into length-`(N m)` sentinel
   blocks), define `c m` on each complete column to spell the encoded `Q`-`(N m)`-name and a fixed
   junk symbol off the tower. *Mathlib-absent piece:* the measurable "which-column / which-floor"
   function of a Rokhlin tower (the position of `x` within its column) — needs the first-return /
   tower address map as a measurable function, which the repo has in
   `FirstReturn`/`Skyscraper`/`TowerBase` but not yet packaged as a `Fin (N m)`-valued floor address
   feeding a per-column block read.

2. **The single fixed `c`.** The construction must produce **one** `c`, not a sequence `c m`: the
   classical device interleaves the towers (nested bases `B (m+1) ⊆ B m` with a reserved escape
   symbol), so the itinerary of `c` carries, at recurrence times, the finest available column's
   name. *Mathlib-absent piece:* none in principle, but this is a genuine inductive symbolic
   construction (`≈ several hundred lines`).

3. **The decoder `D` as a total product-measurable map.** `D` parses the bi-infinite stream
   `n ↦ c (ziter e n x)`: locate the sentinels (`sentinelEncodeList_injective` gives unique
   decodability of *finite* concatenations), find the column containing coordinate `0`, read its
   `Q`-name, output the relevant cell label. *Mathlib-absent piece:* a measurable bi-infinite
   sentinel parser — Mathlib has `List.takeWhile`/`dropWhile` (used in `PrefixCode`) for *finite*
   streams, but no API for measurably locating the marker structure of a `ℤ`-indexed stream and
   extracting the local block. This is the single largest infrastructure gap.

4. **The `m → ∞` a.e. recovery (Borel–Cantelli).** With `∑ ε m < ∞`, a.e. `x` lies in a complete
   column of tower `m` for all large `m` (`eventually_mem_of_summable_compl` on the tower-miss
   events), and by `twoSided_recurrence` its whole orbit is tiled, so `D` parses correctly off a
   μ-null set. *Mathlib-present:* both the Borel–Cantelli leaf (`eventually_mem_of_summable_compl`,
   proved here) and the recurrence backbone (`twoSided_recurrence`, proved here). *Mathlib-absent
   piece:* none — this is the cleanest leaf, but it depends on (1)–(3).

The **honest residual** is therefore the symbolic construction of `(c, D)`: the floor-address map of
a Rokhlin tower (1), the nested-tower interleaving giving a single `c` (2), and — the hardest, with
no Mathlib analogue — the **measurable bi-infinite sentinel parser** `D` (3). The recurrence tiling
(the crux flagged as the hardest leaf) is *not* the bottleneck: `twoSided_recurrence` discharges it
in a dozen lines, and the Borel–Cantelli `m → ∞` leaf is likewise a one-liner over Mathlib. The
genuine multi-week residual is the symbolic-parse infrastructure (3), which Mathlib lacks
entirely. -/

end ErgodicTheory.Krieger
