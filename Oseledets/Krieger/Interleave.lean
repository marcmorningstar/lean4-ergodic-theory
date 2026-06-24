/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.CodeTerm

/-!
# The refining-tower a.e. tiling core of Krieger's column code (C3, sub-problem B)

This file builds the **a.e.-recovery core** that turns the column-tiling alignment
`Oseledets.Krieger.sentinelParseAt_itin_eq` (the dynamical headline of
`Oseledets.Krieger.CodeTerm`) into the `recovers_tiled` field of
`Oseledets.Krieger.ColumnLayoutData`, hence sub-problem B's `CodesTwoSidedMod0c`.

The alignment recovers the `Q`-cell of `x` **on the set where `x`'s itinerary is column-tiled around
coordinate `0`**. A single Rokhlin tower tiles only a `1 − ε` set
(`Oseledets.Krieger.rokhlin_tower`), so a single tower gives recovery only mod-`ε`. The mod-0
discharge needs the **refining-tower / Borel–Cantelli limit**: towers of heights `Nₘ ↑ ∞`, bases
`Bₘ`, tolerances `εₘ` with `∑ εₘ < ∞`, combined into ONE fixed code symbol `c`. By Borel–Cantelli
(`Oseledets.Krieger.eventually_mem_of_summable_compl`) a.e. `x` is eventually inside the
well-covered part of stage `m` for all large `m`, so its itinerary is a.e. column-tiled in the
limit; on the tiled event `sentinelParseAt_itin_eq` makes the parser read off the `Q`-cell.

## The two layers, and what is unconditional vs. carried

This file proves, **unconditionally and sorry-free**, the two *structural* layers that bracket the
genuinely-dynamical interleaving:

* **The bridge to `recovers_tiled` (`columnLayoutData_of_aeParse`).** If the position-aware parser
  of one fixed measurable code symbol `c` agrees `μ`-a.e. with a measurable `κ`-valued "cell index"
  `q : α → κ` whose level sets are mod-0 the cells of `Q` (`Q j =ᵐ[μ] {x | q x = j}`), then the
  full `ColumnLayoutData` is assembled. This is the clean exit any concrete construction
  (refining-tower interleaving, or sub-problem A's Keane–Serafin levels) plugs into: it reduces the
  entire term to the single a.e. statement *"the parser recovers the cell index of `x`"*.

* **The Borel–Cantelli a.e.-tiling reduction (`aeParse_of_aeStageTiled`).** If, for a sequence of
  *stage events* `T m` (the well-covered part of stage `m`, on which the alignment fires and the
  parser reads the `q`-cell), the misses `∑ₘ μ (T m)ᶜ` are summable, then the parser agrees with
  `q` a.e. This is the `m → ∞` / `∑ εₘ < ∞` Borel–Cantelli limit, packaged once over
  `eventually_mem_of_summable_compl`. It is exactly the leaf flagged in `Oseledets.Krieger.Recovery`
  as the cleanest part — discharged here generically over the abstract stage events.

## The honest residual (the adversarial verdict)

What is **not** built here is the genuinely-dynamical interleaving itself: the construction of one
fixed measurable `c : α → Fin k` and the stage events `T m` *together with the per-stage
alignment* `∀ x ∈ T m, sentinelParseAt sentinel decode (itin e c x) = q x` and the summability
`∑ₘ μ (T m)ᶜ < ∞`. This is the `≈ several-hundred-line` inductive symbolic-dynamics construction
(nested refining towers `Bₘ`, an escape/sentinel delimiting stages, the per-column `Q`-`Nₘ`-name
read via `Oseledets.Krieger.floorAddr` + `Oseledets.Krieger.exists_sentinelEncoding`) whose
hardest content is establishing the **two-sided alignment hypotheses** (`htop`/`hdata`/`hprev` of
`sentinelParseAt_itin_eq`) on a positive-coverage stage event. It is isolated, sorry-free, as the
parameterized bundle `RefiningTowerCode` below, exactly mirroring the repo's honest-reduction
pattern (`Oseledets.Krieger.KeaneSerafinStep`, `Oseledets.Krieger.ColumnCodeData`). The structural
assembly `RefiningTowerCode → ColumnLayoutData` is proved here, unconditionally and sorry-free.

## Main results

* `columnLayoutData_of_aeParse` — the bridge: a.e. parser-recovers-cell-index ⟹ the layout data.
* `aeParse_of_aeStageTiled` — the Borel–Cantelli reduction: summable stage-misses + per-stage
  alignment ⟹ a.e. parser-recovers-cell-index. **The reusable refining-tower core.**
* `RefiningTowerCode` / `RefiningTowerCode.toColumnLayoutData` / `.codes` — the honest residual
  bundle (one fixed code + stage events + per-stage alignment + summable misses) and its sorry-free
  assembly into `ColumnLayoutData`, hence `CodesTwoSidedMod0c`.

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5): the
  refining-tower column-coding limit.
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9.
* Michael S. Keane and Jacek Serafin, *On the countable generator theorem*, Fund. Math. **157**
  (1998), 255–259 (the inductive refining construction with `εₖ = 2^{−(k+1)}`).
* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*, Trans. Amer.
  Math. Soc. **149** (1970), 453–464.
-/

open MeasureTheory Function Set Filter
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The bridge: a.e. parser-recovers-cell-index ⟹ `ColumnLayoutData`

The exit any concrete column-coding construction plugs into. Suppose `c : α → Fin k` is a
measurable code symbol, `decode` a position-aware decoder, and `q : α → κ` a "cell index" whose
level sets are, mod 0, the cells of the countable family `Q` (`Q j =ᵐ[μ] {x | q x = j}`). If the
position-aware parser of `c`'s itinerary agrees with `q` a.e.
(`sentinelParseAt sentinel decode (itin e c x) = q x` for a.e. `x`), then for each cell `j` the
parser event equals `Q j` mod 0, which is exactly the `recovers_tiled` field of
`ColumnLayoutData`. -/

/-- **The a.e.-recovery bridge (the reusable exit).** Given a measurable code `c`, a position-aware
decoder `decode`, a sentinel, and a "cell index" `q : α → κ` with `Q j =ᵐ[μ] {x | q x = j}` for
every `j`, if the position-aware parser of `c`'s two-sided itinerary equals `q` almost everywhere,
then for each `j` the parser event `{x | sentinelParseAt … = j}` agrees with `Q j` mod 0.

This is the single a.e. statement the entire column term reduces to: the structural alignment
(`sentinelParseAt_itin_eq`) and the bundling (`ColumnLayoutData`) are all discharged once the parser
recovers the cell index a.e. -/
theorem aeEq_parseEvent_of_aeParse [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (sentinel : Fin k) (code : α → Fin k)
    (decode : List (Fin k) → ℕ → κ) (q : α → κ)
    (hQq : ∀ j, Q j =ᵐ[μ] {x | q x = j})
    (hparse : ∀ᵐ x ∂μ, sentinelParseAt sentinel decode (itin e code x) = q x) (j : κ) :
    Q j =ᵐ[μ] {x | sentinelParseAt sentinel decode (itin e code x) = j} := by
  -- `{q = j}` agrees a.e. with the parser event, since the parser agrees a.e. with `q`.
  have hqEvent : {x | q x = j} =ᵐ[μ]
      {x | sentinelParseAt sentinel decode (itin e code x) = j} := by
    apply Filter.eventuallyEq_set.mpr
    filter_upwards [hparse] with x hx
    exact ⟨fun h => hx ▸ h, fun h => hx.symm ▸ h⟩
  exact (hQq j).trans hqEvent

/-- **The `ColumnLayoutData` from an a.e.-recovering parser.** Assembles the full residual bundle
from: a measurable code symbol, a position-aware decoder, a sentinel, and a measurable cell index
`q` whose level sets are mod-0 the cells of `Q`, plus the a.e. statement that the parser recovers
`q`.
The only non-structural field, `recovers_tiled`, is `aeEq_parseEvent_of_aeParse`. -/
noncomputable def columnLayoutData_of_aeParse
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (sentinel : Fin k) (code : α → Fin k)
    (hcode : Measurable code) (decode : List (Fin k) → ℕ → κ) (q : α → κ)
    (hQq : ∀ j, Q j =ᵐ[μ] {x | q x = j})
    (hparse : ∀ᵐ x ∂μ, sentinelParseAt sentinel decode (itin e code x) = q x) :
    ColumnLayoutData e μ Q k where
  sentinel := sentinel
  code := code
  code_measurable := hcode
  decode := decode
  recovers_tiled := aeEq_parseEvent_of_aeParse sentinel code decode q hQq hparse

/-! ### The Borel–Cantelli a.e.-tiling reduction (the reusable refining-tower core)

The `m → ∞` half. The interleaving supplies a sequence of **stage events** `T m` — the
well-covered part of stage `m`, on which the column-tiling alignment fires and the parser reads off
the `q`-cell of `x`. If the stage misses `∑ₘ μ (T m)ᶜ` are summable (`∑ εₘ < ∞`), then by
Borel–Cantelli a.e. `x` lies in `T m` for all large `m`; picking any such `m` gives
`sentinelParseAt … (itin e c x) = q x`. This packages the `m → ∞` / `∑ εₘ < ∞` limit once,
generically over the abstract stage events. -/

/-- **The Borel–Cantelli a.e.-tiling reduction.** Let `T : ℕ → Set α` be stage events with
summable misses `∑ₘ μ (T m)ᶜ < ∞`, and suppose on each stage the parser already recovers the cell
index: `∀ x ∈ T m, sentinelParseAt sentinel decode (itin e code x) = q x`. Then the parser recovers
the cell index **almost everywhere**.

By `eventually_mem_of_summable_compl` a.e. `x` lies in `T m` for all large `m` (the first
Borel–Cantelli lemma); evaluating the per-stage alignment at any such `m` gives the a.e. parse.
This is the reusable refining-tower core: it reduces the whole a.e. recovery to *one stage's* tiling
plus the summable tolerance `∑ εₘ < ∞`, exactly the `m → ∞` leaf of the construction. -/
theorem aeParse_of_aeStageTiled {e : α ≃ᵐ α} (sentinel : Fin k) (code : α → Fin k)
    (decode : List (Fin k) → ℕ → κ) (q : α → κ) (T : ℕ → Set α)
    (hsum : (∑' m, μ (T m)ᶜ) ≠ ∞)
    (htile : ∀ m, ∀ x ∈ T m,
      sentinelParseAt sentinel decode (itin e code x) = q x) :
    ∀ᵐ x ∂μ, sentinelParseAt sentinel decode (itin e code x) = q x := by
  filter_upwards [eventually_mem_of_summable_compl (μ := μ) hsum] with x hx
  -- `hx : ∀ᶠ m, x ∈ T m`; extract one witness `m₀` and apply the per-stage alignment.
  obtain ⟨m₀, hm₀⟩ := hx.exists
  exact htile m₀ x hm₀

/-! ### The honest residual: the refining-tower interleaving bundle

What remains for a fully unconditional term is the genuinely-dynamical interleaving: one fixed
measurable code `c : α → Fin k`, a measurable cell index `q : α → κ` recovering the countable
family `Q` mod 0, and a sequence of stage events `T m` with summable misses on which the
column-tiling alignment fires. We isolate exactly this as `RefiningTowerCode`. Its construction
(nested refining Rokhlin towers `Bₘ`, an escape/sentinel delimiting stages, the per-column
`Q`-`Nₘ`-name read via `floorAddr` + `exists_sentinelEncoding`, with the two-sided alignment
hypotheses of `sentinelParseAt_itin_eq` discharged on each `T m`) is the `≈ several-hundred-line`
symbolic-dynamics residual; the structural assembly into `ColumnLayoutData` is proved here,
sorry-free. -/

/-- **The refining-tower column-code residual bundle.** Bundles the genuinely-dynamical inputs of
the refining-tower interleaving that the structural alignment and the Borel–Cantelli core cannot
supply:

* `sentinel`, `code` (+ `code_measurable`): the reserved letter and the one fixed measurable code
  symbol of the interleaving (built from `floorAddr` + `exists_sentinelEncoding`);
* `decode`: the position-aware per-block decoder;
* `cellIndex` (+ `cellIndex_recovers`): a measurable `κ`-valued cell index whose level sets are
  mod-0 the cells of `Q` (so `Q` is, mod 0, the partition of a measurable index);
* `stage`: the stage events `T m` (the well-covered part of stage `m`);
* `misses_summable`: the summable stage tolerances `∑ₘ μ (T m)ᶜ < ∞` (`∑ εₘ < ∞`); and
* `stage_tiled`: the per-stage column-tiling alignment — on `T m` the parser recovers the index.

`stage_tiled` is the irreducible content: it asserts the two-sided alignment hypotheses
(`htop`/`hdata`/`hprev` of `sentinelParseAt_itin_eq`) hold for `c` on the positive-coverage event
`T m`, which is what the refining-tower interleaving construction must establish. -/
structure RefiningTowerCode [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (e : α ≃ᵐ α) (μ : Measure α) (Q : κ → Set α) (k : ℕ) where
  /-- The reserved sentinel letter of the `Fin k` alphabet. -/
  sentinel : Fin k
  /-- The single fixed measurable code symbol `c : α → Fin k` of the interleaving. -/
  code : α → Fin k
  /-- The code symbol is measurable. -/
  code_measurable : Measurable code
  /-- The position-aware per-block decoder. -/
  decode : List (Fin k) → ℕ → κ
  /-- The measurable cell index whose level sets are mod-0 the cells of `Q`. -/
  cellIndex : α → κ
  /-- The cell index recovers each cell of `Q` mod 0. -/
  cellIndex_recovers : ∀ j, Q j =ᵐ[μ] {x | cellIndex x = j}
  /-- The stage events `T m` (the well-covered part of stage `m`). -/
  stage : ℕ → Set α
  /-- The stage misses are summable: `∑ₘ μ (T m)ᶜ < ∞` (`∑ εₘ < ∞`). -/
  misses_summable : (∑' m, μ (stage m)ᶜ) ≠ ∞
  /-- Per-stage column-tiling alignment: on `T m` the parser recovers the cell index. -/
  stage_tiled : ∀ m, ∀ x ∈ stage m,
    sentinelParseAt sentinel decode (itin e code x) = cellIndex x

/-- **A `RefiningTowerCode` assembles into a `ColumnLayoutData`** (the residual reduction). The
Borel–Cantelli core `aeParse_of_aeStageTiled` turns the summable stage misses and the per-stage
alignment into the a.e. parse `sentinelParseAt … = cellIndex`, and the bridge
`columnLayoutData_of_aeParse` turns that (with the mod-0 cell-index recovery of `Q`) into the full
`ColumnLayoutData`. Both steps are unconditional and sorry-free; the entire residual is concentrated
in the `RefiningTowerCode` fields, i.e. in the genuinely-dynamical interleaving. -/
noncomputable def RefiningTowerCode.toColumnLayoutData
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (data : RefiningTowerCode e μ Q k) :
    ColumnLayoutData e μ Q k :=
  columnLayoutData_of_aeParse data.sentinel data.code data.code_measurable data.decode
    data.cellIndex data.cellIndex_recovers
    (aeParse_of_aeStageTiled data.sentinel data.code data.decode data.cellIndex data.stage
      data.misses_summable data.stage_tiled)

/-- **A `RefiningTowerCode` yields the cross-layer countable mod-0 code.** Composing
`RefiningTowerCode.toColumnLayoutData` with `Oseledets.Krieger.ColumnLayoutData.codes` gives
`CodesTwoSidedMod0c` for the code partition — the deliverable that slots into
`Oseledets.Krieger.KriegerCodingData.code_codes`. The entire symbolic side of sub-problem B thus
reduces, sorry-free, to producing a `RefiningTowerCode`: one fixed code symbol whose refining-tower
stage events tile a.e. (with summable tolerances) and whose per-column blocks recover the `Q`-cell
index. -/
theorem RefiningTowerCode.codes
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (data : RefiningTowerCode e μ Q k) :
    CodesTwoSidedMod0c e Q
      (codePartition (μ := μ) data.toColumnLayoutData.code
        data.toColumnLayoutData.code_measurable) :=
  data.toColumnLayoutData.codes

/-! ### The concrete per-column alignment from a sentinel encoding (reusable for A and B)

The structural `Oseledets.Krieger.sentinelParseAt_itin_eq` takes the column block `blk` as an
abstract list with the sentinel-placement hypotheses `htop`/`hdata` as side conditions. When `blk`
is an actual `Oseledets.Krieger.sentinelEncode` block (`d.map emb ++ [s]`, the code C3 reads off),
those two hypotheses are **automatic** from the encoding structure: the sentinel is the trailing
letter (`htop`) and the data part `d.map emb` contains no sentinel (`hdata`, `notMem_sentinelData`).
This corollary discharges them, so a concrete construction needs only to supply

* `hblk`: the code spells the encoded block on the column (`c (eʲ b) = (sentinelEncode …)[j]`), and
* `hprev`: the previous column's terminating sentinel sits one coordinate below floor `0`.

This is the bridge `Oseledets.Krieger.PrefixCode` → `Oseledets.Krieger.sentinelParseAt_itin_eq`
that both the refining-tower interleaving (sub-problem B) and the Keane–Serafin levels (sub-problem
A) reuse when they build their stage codes. -/

/-- **Per-column alignment from a `sentinelEncode` block.** If `x = eⁱ b` is at floor `i` (`i < N`)
of a height-`N` column whose code block is the sentinel encoding `blk = sentinelEncode s emb d` of a
data word `d` of length `N - 1` (`hN`), the code spells that block on the column
(`hblk : c (eʲ b) = blk.get …`), and the previous column's terminator sits one coordinate below
floor `0` (`hprev`), then the position-aware parser reads off `dec blk i`.

The sentinel-placement hypotheses `htop`/`hdata` of `sentinelParseAt_itin_eq` are discharged from
the `sentinelEncode` structure: the block's last letter is the sentinel and its data prefix
`d.map emb` is sentinel-free (`notMem_sentinelData`). -/
theorem sentinelParseAt_itin_of_encode {l : ℕ} (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (dec : List (Fin l) → ℕ → κ) (e : α ≃ᵐ α) (c : α → Fin l) (b : α) (N i : ℕ) (hi : i < N)
    (d : List (Fin (l - 1))) (hd : d.length = N - 1) (hN : 1 ≤ N)
    (hblk : ∀ j : Fin N, c ((e : α → α)^[(j : ℕ)] b)
      = (sentinelEncode s emb d).get (Fin.cast (by simp [sentinelEncode, hd]; omega) j))
    (hprev : itin e c ((e : α → α)^[i] b) (-1 - (i : ℤ)) = s) :
    sentinelParseAt s dec (itin e c ((e : α → α)^[i] b)) = dec (sentinelEncode s emb d) i := by
  classical
  have hlen : (sentinelEncode s emb d).length = N := by simp [sentinelEncode, hd]; omega
  -- The data prefix `d.map emb` has length `N - 1`.
  have hmaplen : (d.map (fun j => (emb j : Fin l))).length = N - 1 := by simp [hd]
  refine sentinelParseAt_itin_eq s dec e c b N i hi (sentinelEncode s emb d) hlen hblk ?_ ?_ hprev
  · -- htop: the last letter of the block is the sentinel.
    rw [List.get_eq_getElem]
    simp only [sentinelEncode]
    rw [List.getElem_append, dif_neg (by simp; omega)]
    simp
  · -- hdata: every earlier letter lies in the sentinel-free data prefix.
    intro j hj
    have hjlt : (j : ℕ) < N - 1 := hj
    rw [List.get_eq_getElem]
    simp only [sentinelEncode]
    rw [List.getElem_append]
    have hjmap : (j : ℕ) < (d.map (fun j => (emb j : Fin l))).length := by rw [hmaplen]; exact hjlt
    rw [dif_pos (by simpa using hjmap), List.getElem_map]
    -- the data prefix's letters are non-sentinel by construction of `emb`
    exact (emb _).2

end Oseledets.Krieger
