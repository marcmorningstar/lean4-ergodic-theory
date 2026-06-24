/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.Interleave
import Mathlib.Data.List.GetD

/-!
# The escape-symbol single-stage column code and the refining-tower assembly (C3, sub-problem B)

This file builds the **escape-symbol single-stage column alignment** — the genuine repair of the
two-sided bracketing defect (W7) flagged for `Oseledets.Krieger.sentinelParseAt_itin_eq` — and the
refining-tower assembly that bundles a sequence of single-stage codes into a
`Oseledets.Krieger.RefiningTowerCode`, hence sub-problem B's `CodesTwoSidedMod0c`.

## The W7 defect this repairs

`Oseledets.Krieger.sentinelParseAt_itin_of_encode` needs the previous column's terminating sentinel
one coordinate below floor `0` of the current column (`hprev`). With a *single skyscraper* this
FAILS on the bottom-most complete block of each first-return column: there, coordinate `-1` is the
top of the **incomplete residual stub** of the previous first-return column, which carries no
sentinel. This is a positive-measure obstruction (the bottom blocks are a fixed positive fraction of
the covered set, not a vanishing one).

## The escape-symbol repair (Keane–Serafin 1998 §; Downarowicz §4.2.5; Shields §I.9)

A reserved sentinel `s : Fin k` is placed so that **every first-return column terminates in `s`**
(at its top floor — whether that top is the top of a complete `N`-block or the top of the residual
stub). Then for *every* column base `b`, the coordinate `e⁻¹ b` (the top of the previous column)
carries `s`, so `hprev` holds for the bottom block of every column too. This is exactly the device
that makes every used column **two-sided sentinel-bracketed**.

This file isolates that repair as a clean, reusable abstract interface: a `StageCode` whose code
spells `sentinelEncode` blocks on each column and places `s` at every column-bottom predecessor.
On the well-tiled stage event the parser then recovers the cell index, via
`Oseledets.Krieger.sentinelParseAt_itin_of_encode` with `hprev` discharged from the bracketing.

## What is proved sorry-free here

* `StageCode` — the abstract single-stage interface (one code, one tower height/base, a bracketed
  encoding on every column) and `StageCode.tiled` — its per-stage alignment: on the well-tiled stage
  event the parser recovers the cell index. **This is the escape-symbol W7 repair, sorry-free.**
* `RefiningTowerCode.ofStages` — bundles a sequence of `StageCode`s sharing one fixed `code` and one
  `cellIndex`, with summable stage misses, into a `RefiningTowerCode`, hence `CodesTwoSidedMod0c`.

## The honest residual (the adversarial verdict)

What `StageCode` *carries* as hypotheses (`spells`, `brackets`) is precisely the
genuinely-dynamical content the construction of one fixed measurable interleaving `code` must
establish: that a single `code : α → Fin k`, on the refining sequence of Rokhlin towers, spells the
`sentinelEncode` of each column's `Q`-name AND places `s` at every column terminator,
*simultaneously for all stages*. Producing that one `code` (nested bases `Bₘ₊₁ ⊆ Bₘ`, the escape
symbol carrying the finest column's name) and verifying `spells`/`brackets` measurably is the
`≈ several-hundred-line` inductive symbolic-dynamics residual. The structural reduction —
escape-symbol bracketing ⟹ `hprev`
⟹ per-stage alignment ⟹ `RefiningTowerCode` — is proved here, unconditionally and sorry-free.

## References

* Michael S. Keane and Jacek Serafin, *On the countable generator theorem*, Fund. Math. **157**
  (1998), 255–259 (the per-step Rokhlin construction, `εₖ = 2^{−(k+1)}`, and the marker symbol).
* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5): the
  refining-tower column-coding limit with a reserved marker.
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9 (marker
  codes; two-sided bracketing).
-/

open MeasureTheory Function Set Filter
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The escape-symbol single-stage column code

We isolate, as a clean abstract interface, exactly the data the refining-tower interleaving must
supply at one stage so that on the well-tiled stage event the position-aware parser recovers the
cell index. The two genuinely-dynamical hypotheses are:

* `spells` — the code spells the `sentinelEncode` block of the column's `(N)`-name on each column,
  and the block decodes back to the cell index at every floor; and
* `brackets` — **the escape-symbol bracketing**: at every column base in the stage event, the
  predecessor coordinate `e⁻¹ b` carries the sentinel (`code (e⁻¹ b) = s`). This is the W7 repair —
  every used column is two-sided sentinel-bracketed.

`StageCode.tiled` then discharges the per-stage alignment via
`Oseledets.Krieger.sentinelParseAt_itin_of_encode`. -/

/-- **The escape-symbol single-stage column code interface.** Bundles, for one fixed stage, the data
the refining-tower interleaving construction supplies, isolated from the structural alignment:

* `N` (`≥ 1`): the stage tower height; `s`: the reserved sentinel; `emb`: the data embedding;
* `base x` / `floor x`: the column base point and within-column floor of `x`
  (`x = e^{floor x} base x`, `floor x < N`), valid on the stage event;
* `name x`: the `(N - 1)`-length data word coding the column's `Q`-name;
* `spells`: on the stage event, the code spells the `sentinelEncode` of `name x` along the column
  (`hblk`), and reading that block at the offset recovers the cell index;
* `brackets`: the **escape-symbol bracketing** — the predecessor of the column base carries `s`.

This is precisely the per-stage residual of the refining-tower interleaving: the structural
alignment `sentinelParseAt_itin_of_encode` is discharged from it without any further hypotheses. -/
structure StageCode (e : α ≃ᵐ α) (code : α → Fin k) (decode : List (Fin k) → ℕ → κ)
    (cellIndex : α → κ) (s : Fin k) (T : Set α) where
  /-- The stage tower height. -/
  N : ℕ
  /-- The height is positive. -/
  hN : 1 ≤ N
  /-- The data embedding placing data symbols into the non-sentinel letters. -/
  emb : Fin (k - 1) ↪ NonSentinel s
  /-- The column base point of `x` (valid on `T`). -/
  base : α → α
  /-- The within-column floor of `x` (valid on `T`). -/
  floor : α → ℕ
  /-- The `(N - 1)`-length data word coding the column's `Q`-name (valid on `T`). -/
  name : α → List (Fin (k - 1))
  /-- On `T`, `x` sits at floor `floor x < N` of the column over `base x`. -/
  at_floor : ∀ x ∈ T, floor x < N ∧ x = (e : α → α)^[floor x] (base x)
  /-- On `T`, the data word has length `N - 1`. -/
  name_length : ∀ x ∈ T, (name x).length = N - 1
  /-- On `T`, the code spells the `sentinelEncode` block of the column's name along the column. The
  block is indexed with the junk-safe `getD … s` (no proof in the type); on `T` the index `i < N`
  is in range, so `getD` agrees with the genuine `get` used by `sentinelParseAt_itin_of_encode`. -/
  spells : ∀ x ∈ T, ∀ i : ℕ, i < N →
    code ((e : α → α)^[i] (base x)) = (sentinelEncode s emb (name x)).getD i s
  /-- On `T`, decoding the column block at the floor offset recovers the cell index. -/
  decodes : ∀ x ∈ T, decode (sentinelEncode s emb (name x)) (floor x) = cellIndex x
  /-- **The escape-symbol bracketing.** The predecessor of the column base carries the sentinel. -/
  brackets : ∀ x ∈ T, code ((e.symm : α → α) (base x)) = s

/-- **The per-stage alignment from a `StageCode` (the W7 escape-symbol repair).** On the well-tiled
stage event `T` the position-aware parser of the fixed `code` recovers the cell index:
`sentinelParseAt s decode (itin e code x) = cellIndex x` for every `x ∈ T`.

The proof reads off `x = e^{floor x} (base x)` (`at_floor`), discharges the sentinel-placement
hypotheses `htop`/`hdata` from the `sentinelEncode` structure via
`Oseledets.Krieger.sentinelParseAt_itin_of_encode`, and discharges `hprev` from the escape-symbol
bracketing `brackets` (`code (e⁻¹ base) = s`): the previous column's terminator sits exactly one
coordinate below floor `0`. The decode then recovers the cell index by `decodes`. -/
theorem StageCode.tiled {e : α ≃ᵐ α} {code : α → Fin k} {decode : List (Fin k) → ℕ → κ}
    {cellIndex : α → κ} {s : Fin k} {T : Set α} (sc : StageCode e code decode cellIndex s T) :
    ∀ x ∈ T, sentinelParseAt s decode (itin e code x) = cellIndex x := by
  intro x hx
  obtain ⟨hfloor, hxeq⟩ := sc.at_floor x hx
  -- The block length is `N` (length `N - 1` data word plus the trailing sentinel).
  have hlen : (sentinelEncode s sc.emb (sc.name x)).length = sc.N := by
    rw [sentinelEncode_length, sc.name_length x hx]; omega
  -- Bridge the junk-safe `getD` spelling (`spells`) to the genuine `get (Fin.cast …)` form `hblk`.
  have hblk : ∀ j : Fin sc.N, code ((e : α → α)^[(j : ℕ)] (sc.base x))
      = (sentinelEncode s sc.emb (sc.name x)).get (Fin.cast hlen.symm j) := by
    intro j
    have hjlen : (j : ℕ) < (sentinelEncode s sc.emb (sc.name x)).length := by
      rw [hlen]; exact j.isLt
    rw [sc.spells x hx j j.isLt, List.get_eq_getElem, List.getD_eq_getElem _ _ hjlen]
    congr 1
  -- The per-column alignment from the encoding, anchored at the column base of `x`.
  have hkey := sentinelParseAt_itin_of_encode s sc.emb decode e code (sc.base x) sc.N (sc.floor x)
    hfloor (sc.name x) (sc.name_length x hx) sc.hN hblk ?_
  · -- `sentinelParseAt … (itin e code x) = decode (block) (floor x) = cellIndex x`.
    calc sentinelParseAt s decode (itin e code x)
        = sentinelParseAt s decode (itin e code ((e : α → α)^[sc.floor x] (sc.base x))) := by
          rw [← hxeq]
      _ = decode (sentinelEncode s sc.emb (sc.name x)) (sc.floor x) := hkey
      _ = cellIndex x := sc.decodes x hx
  · -- `hprev`: the previous column's terminator sits one coordinate below floor `0`. Concretely
    -- `itin e code (e^{floor} base) (-1-floor) = code (ziter e (-1) base) = code (e.symm base)`.
    rw [itin_apply]
    have hz : ziter e (-1 - (sc.floor x : ℤ)) ((e : α → α)^[sc.floor x] (sc.base x))
        = (e.symm : α → α) (sc.base x) := by
      have h1 : (e : α → α)^[sc.floor x] (sc.base x) = ziter e (sc.floor x : ℤ) (sc.base x) := by
        rw [ziter_natCast]
      rw [h1, ← Function.comp_apply (f := ziter e (-1 - (sc.floor x : ℤ))), ← ziter_add,
        show (-1 - (sc.floor x : ℤ)) + (sc.floor x : ℤ) = -1 by ring, ziter_neg_one]
    rw [hz]
    exact sc.brackets x hx

/-! ### The refining-tower assembly from a sequence of single-stage codes

A `RefiningTowerCode` is one fixed `code`, one `cellIndex` recovering `Q` mod 0, stage events `T m`
with summable misses, and per-stage alignment. Given a sequence of `StageCode`s **all sharing one
fixed `code`, `decode`, `cellIndex` and sentinel `s`** — the output of the interleaving — the
per-stage alignment is `StageCode.tiled` at each `m`. The summable-misses field is supplied
directly (`∑ εₘ < ∞`, `εₘ = 2^{−(m+1)}` in the Keane–Serafin construction). -/

/-- **The refining-tower code from a sequence of single-stage codes.** Bundles one fixed measurable
`code`, one fixed `cellIndex` (recovering `Q` mod 0), stage events `T m` with summable misses, and —
the genuinely-dynamical content — a `StageCode` at each stage `m` (all sharing the same
`code`/`decode`/`cellIndex`/`s`), into a `RefiningTowerCode`. The per-stage alignment field
`stage_tiled` is `StageCode.tiled` at each `m`; everything else is supplied verbatim.

This is the clean exit the refining-tower interleaving plugs into: once one fixed `code` is built
that, on each stage, spells `sentinelEncode` blocks and brackets every column with `s`
(`StageCode.spells`/`brackets`), and the stage misses are summable, the full
`RefiningTowerCode` — hence sub-problem B's `CodesTwoSidedMod0c` — is assembled. -/
noncomputable def RefiningTowerCode.ofStages
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (s : Fin k) (code : α → Fin k) (hcode : Measurable code)
    (decode : List (Fin k) → ℕ → κ) (cellIndex : α → κ)
    (hQ : ∀ j, Q j =ᵐ[μ] {x | cellIndex x = j})
    (T : ℕ → Set α) (hsum : (∑' m, μ (T m)ᶜ) ≠ ∞)
    (stages : ∀ m, StageCode e code decode cellIndex s (T m)) :
    RefiningTowerCode e μ Q k where
  sentinel := s
  code := code
  code_measurable := hcode
  decode := decode
  cellIndex := cellIndex
  cellIndex_recovers := hQ
  stage := T
  misses_summable := hsum
  stage_tiled := fun m => (stages m).tiled

/-- **A refining-tower code from a sequence of stages yields `CodesTwoSidedMod0c`.** Composing
`RefiningTowerCode.ofStages` with `Oseledets.Krieger.RefiningTowerCode.codes` closes sub-problem B's
symbolic side: the cross-layer countable mod-0 code of `Q` by the code partition. The entire
residual is concentrated in producing the single fixed interleaving `code` and its per-stage
`StageCode`s. -/
theorem RefiningTowerCode.codes_ofStages
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (s : Fin k) (code : α → Fin k) (hcode : Measurable code)
    (decode : List (Fin k) → ℕ → κ) (cellIndex : α → κ)
    (hQ : ∀ j, Q j =ᵐ[μ] {x | cellIndex x = j})
    (T : ℕ → Set α) (hsum : (∑' m, μ (T m)ᶜ) ≠ ∞)
    (stages : ∀ m, StageCode e code decode cellIndex s (T m)) :
    letI data := RefiningTowerCode.ofStages s code hcode decode cellIndex hQ T hsum stages
    CodesTwoSidedMod0c e Q
      (codePartition (μ := μ) data.toColumnLayoutData.code
        data.toColumnLayoutData.code_measurable) :=
  (RefiningTowerCode.ofStages s code hcode decode cellIndex hQ T hsum stages).codes

end Oseledets.Krieger
