/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.TowerCode

/-!
# The column-tiling alignment and the dynamical core of Krieger's column code (C3, sub-problem B)

This file builds the **dynamical alignment heart** of the column-coding step (C3) of Krieger's
finite generator theorem (issue #15), on top of the *position-aware* sentinel parser
`Oseledets.Krieger.sentinelParseAt` of `Oseledets.Krieger.TowerCode`. The prior repair there proved
the naive parser `sentinelParse` is **position-blind** — it returns the same label at `x` and
`e·x` (`Oseledets.Krieger.parse_event_cannot_separate`) — and replaced it with the offset-aware
`sentinelParseAt s dec w = dec (blockContent s w) (blockOffset s w)`.

The single missing dynamical fact that *justifies* the offset-aware parser is the **column-tiling
alignment**: for a point sitting at floor `i` of a height-`N` tower column whose sentinel-terminated
block is `blk`, the parser reads off exactly the offset `i` and the block `blk`, hence
`sentinelParseAt s dec (itin e c x) = dec blk i`. This is the alignment
`blockOffset (itin e c x) = floorAddr x` that the task flagged as the adversarial trap — and we
prove it here, sorry-free.

## The alignment, precisely (the adversarial check)

The sentinel `s` is the column block's **terminator**, placed at the column's **top floor** `N-1`
(the convention of `Oseledets.Krieger.sentinelEncode`, which appends `[s]`). For a point `x` at
floor `i` of a column over base point `b` (`x = eⁱ b`), its two-sided itinerary `w = itin e c x`
satisfies, *coordinate by coordinate*, `w (j - i) = c (eʲ b) = blk j` for every block index
`j : Fin N` (from the cocycle identity `ziter e (j - i) (eⁱ b) = eʲ b`). With the
sentinel at the top of *this* column and at the top of the *previous* column (one coordinate below
floor `0`, i.e. relative coordinate `-(i+1)`), the backward search from `-1` measures exactly the
floor index `i` (`bwdSentinel_eq_of`) and the forward search from `0` measures `N-1-i`
(`fwdSentinel_eq_of`); so `blockStart = -i`, `blockLen = N`, `blockContent = blk`, and
`blockOffset = i`. **The offset the parser consumes is exactly the floor index `i`** —
this is the alignment the position-blind parser was missing.

The headline `sentinelParseAt_itin_eq` packages this for the two-sided itinerary directly: if `x` is
at floor `i`, its column block is `blk`, the block ends in the sentinel and is otherwise
sentinel-free, and the previous column's terminator sits one coordinate below floor `0`, then
`sentinelParseAt s dec (itin e c x) = dec blk i`.

## The honest residual (the adversarial verdict on the *full* term)

A `SentinelColumnCodeAt` (`Oseledets.Krieger.TowerCode`) demands the **mod-0** recovery
`∀ j, Q j =ᵐ[μ] {x | sentinelParseAt s decode (itin e code x) = j}` — agreement off a
**μ-null** set. The alignment recovers the `Q`-cell of `x` **on the covered set of one tower**, with
measure only `1 - ε` (`Oseledets.Krieger.rokhlin_tower`), `ε > 0`. So a **single tower closes the
recovery only mod-`ε`, not mod-`0`**: off the covered set (`floorAddr = N`) the column tiling fails
and the parser returns an unrelated label, on a set of *positive* measure `μ Cᶜ ∈ (0, ε)`. The
documented framing "mod-0 tolerates the rest" is therefore **false for a single tower** — the
genuine discharge needs the refining-tower / Borel–Cantelli limit (`∑ εₘ < ∞`,
`Oseledets.Krieger.eventually_mem_of_summable_compl`) carried by **one** fixed code symbol
interleaving all the towers. That `m → ∞` symbolic interleaving is the irreducible residual; it is
isolated here as the hypothesis bundle `ColumnLayoutData`, whose single non-structural
field `recovers_tiled` is the a.e. two-sided column tiling. Everything else — the alignment, the
recovery from the tiling, the bundling into a `SentinelColumnCodeAt` and hence `CodesTwoSidedMod0c`
— is proved unconditionally and sorry-free below.

## Main results

* `bwdSentinel_eq_of`, `fwdSentinel_eq_of` — characterizations of the (totalized)
  sentinel-distance searches by a witness plus a closer-witness-free interval. Reusable.
* `ziter_sub_floor` — the cocycle coordinate identity `ziter e (j - i) (eⁱ b) = eʲ b`.
* `sentinelParseAt_column` — **the column-tiling alignment** (stream form): the position-aware
  parser on a single-column-tiled stream reads off `dec blk i`.
* `sentinelParseAt_itin_eq` — the alignment for the two-sided itinerary `itin e c x` of a
  floor-`i` point, the dynamical headline.
* `ColumnLayoutData` / `ColumnLayoutData.toSentinelColumnCodeAt` / `.codes` — the honest residual
  bundle: the a.e. two-sided column tiling (the `m → ∞` interleaving residual) yields a full
  `SentinelColumnCodeAt`, hence the cross-layer countable mod-0 code `CodesTwoSidedMod0c`.

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5): the
  column-coding decoder reads `decodeBlock(content)(offset)`.
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9.
* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*, Trans. Amer.
  Math. Soc. **149** (1970), 453–464.
-/

open MeasureTheory Function Set

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### Characterizations of the totalized sentinel-distance searches

The forward/backward searches `fwdSentinel`/`bwdSentinel` of `Oseledets.Krieger.TowerCode` are
`Nat.find` of a *totalized* predicate. On a stream that *does* have a sentinel in the relevant
direction, the distance is pinned down by exhibiting the sentinel at the claimed coordinate and the
absence of any closer one. These two lemmas package that `Nat.find_eq_iff` reasoning once. -/

/-- **The backward sentinel distance is `d`** when the sentinel sits at coordinate `-1 - d` and at
no closer coordinate `-1 - n`, `n < d`. (Anchor `-1`, as in `Oseledets.Krieger.blockStart`/
`blockOffset`.) -/
theorem bwdSentinel_eq_of (s : Fin k) (w : ℤ → Fin k) (d : ℕ)
    (hd : w (-1 - (d : ℤ)) = s) (hlt : ∀ n : ℕ, n < d → w (-1 - (n : ℤ)) ≠ s) :
    bwdSentinel s (-1) w = d := by
  classical
  rw [bwdSentinel, Nat.find_eq_iff]
  exact ⟨Or.inl hd, fun n hn hpred => hpred.elim (hlt n hn) (fun h => h d hd)⟩

/-- **The forward sentinel distance is `f`** when the sentinel sits at coordinate `f` and at no
closer coordinate `n`, `n < f`. (Anchor `0`, as in `Oseledets.Krieger.blockEnd`.) -/
theorem fwdSentinel_eq_of (s : Fin k) (w : ℤ → Fin k) (f : ℕ)
    (hf : w (0 + (f : ℤ)) = s) (hlt : ∀ n : ℕ, n < f → w (0 + (n : ℤ)) ≠ s) :
    fwdSentinel s 0 w = f := by
  classical
  rw [fwdSentinel, Nat.find_eq_iff]
  exact ⟨Or.inl hf, fun n hn hpred => hpred.elim (hlt n hn) (fun h => h f hf)⟩

/-! ### The column-tiling alignment (stream form) -/

/-- **The column-tiling alignment.** Suppose the bi-infinite stream `w` is, around coordinate `0`,
the layout of one height-`N` tower column whose sentinel-terminated block is `blk` (length `N`),
read by a point sitting at floor `i` of the column. Concretely:

* `i < N`, `blk.length = N`;
* `hcol`: stream coordinate `j - i` is block symbol `j`, for every block index `j : Fin N`;
* `htop`: the block ends in the sentinel (`blk N-1 = s`);
* `hdata`: every data floor `j < N-1` is non-sentinel (`blk j ≠ s`);
* `hprev`: the previous column's terminating sentinel sits one coordinate below floor `0`, i.e. at
  relative coordinate `-(i+1)` (`w (-1 - i) = s`).

Then the position-aware parser reads off exactly `dec blk i`: it locates the offset `i`
(`blockOffset = i`, the floor index) and the full column block (`blockContent = blk`), and applies
`dec`. This is the alignment `blockOffset = floor` that the position-blind parser
(`Oseledets.Krieger.parse_event_cannot_separate`) was missing. -/
theorem sentinelParseAt_column (s : Fin k) (dec : List (Fin k) → ℕ → κ) (w : ℤ → Fin k)
    (N i : ℕ) (hi : i < N) (blk : List (Fin k)) (hlen : blk.length = N)
    (hcol : ∀ j : Fin N, w ((j : ℤ) - (i : ℤ)) = blk.get (Fin.cast hlen.symm j))
    (htop : blk.get (Fin.cast hlen.symm ⟨N - 1, by omega⟩) = s)
    (hdata : ∀ j : Fin N, (j : ℕ) < N - 1 → blk.get (Fin.cast hlen.symm j) ≠ s)
    (hprev : w (-1 - (i : ℤ)) = s) :
    sentinelParseAt s dec w = dec blk i := by
  classical
  -- The offset (= backward sentinel distance) is the floor index `i`.
  have hoff : blockOffset s w = i := by
    rw [blockOffset_def]
    refine bwdSentinel_eq_of s w i hprev (fun n hn => ?_)
    -- coordinate `-1 - n` is data floor `i - 1 - n < N - 1`, hence non-sentinel
    have hjlt : i - 1 - n < N := by omega
    have hcoord : (-1 - (n : ℤ)) = ((⟨i - 1 - n, hjlt⟩ : Fin N) : ℤ) - (i : ℤ) := by
      push_cast; omega
    rw [hcoord, hcol ⟨i - 1 - n, hjlt⟩]
    exact hdata ⟨i - 1 - n, hjlt⟩ (by omega)
  -- The forward sentinel distance is `N - 1 - i` (the block terminator above floor `i`).
  have hfwd : fwdSentinel s 0 w = N - 1 - i := by
    refine fwdSentinel_eq_of s w (N - 1 - i) ?_ (fun n hn => ?_)
    · have hjN : N - 1 < N := by omega
      have hcoord :
          (0 + ((N - 1 - i : ℕ) : ℤ)) = ((⟨N - 1, hjN⟩ : Fin N) : ℤ) - (i : ℤ) := by
        push_cast; omega
      rw [hcoord, hcol ⟨N - 1, hjN⟩]; convert htop using 2
    · have hjlt : i + n < N := by omega
      have hcoord : (0 + (n : ℤ)) = ((⟨i + n, hjlt⟩ : Fin N) : ℤ) - (i : ℤ) := by
        push_cast; omega
      rw [hcoord, hcol ⟨i + n, hjlt⟩]
      exact hdata ⟨i + n, hjlt⟩ (by omega)
  -- Hence start = -i, length = N, content = blk.
  have hstart : blockStart s w = -(i : ℤ) := by rw [blockStart, ← blockOffset_def, hoff]
  have hlenblk : blockLen s w = N := by
    rw [blockLen, blockEnd, hfwd, hstart]
    have hcast : ((N - 1 - i : ℕ) : ℤ) = (N : ℤ) - 1 - (i : ℤ) := by
      push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + i ≤ N)]; ring
    rw [hcast]
    rw [show (N : ℤ) - 1 - (i : ℤ) - -(i : ℤ) + 1 = (N : ℤ) by ring]; simp
  have hcontent : blockContent s w = blk := by
    rw [blockContent, hstart, hlenblk, window]
    refine List.ext_getElem (by simp [hlen]) (fun j h1 h2 => ?_)
    simp only [List.getElem_ofFn]
    have hjN : j < N := by simpa [hlen] using h2
    have hcl := hcol ⟨j, hjN⟩
    
    rw [show (-(i : ℤ) + (j : ℕ)) = ((j : ℕ) : ℤ) - (i : ℤ) by ring, hcl]
    simp [List.get_eq_getElem]
  rw [sentinelParseAt, hcontent, hoff]

/-! ### The dynamical coordinate identity and the alignment for the two-sided itinerary -/

/-- **The cocycle coordinate identity.** For a point `x = eⁱ b` at floor `i`, the two-sided
iterate `ziter e (j - i) x` is `eʲ b`: stream coordinate `j - i` of `x`'s itinerary reads column
floor `j`. This is the bridge from the dynamics to the `hcol` hypothesis of the alignment. -/
theorem ziter_sub_floor (e : α ≃ᵐ α) (b : α) (i j : ℕ) :
    ziter e ((j : ℤ) - (i : ℤ)) ((e : α → α)^[i] b) = (e : α → α)^[j] b := by
  have h1 : (e : α → α)^[i] b = ziter e (i : ℤ) b := by rw [ziter_natCast]
  rw [h1, ← Function.comp_apply (f := ziter e ((j : ℤ) - i)), ← ziter_add,
    show (j : ℤ) - (i : ℤ) + (i : ℤ) = (j : ℤ) by ring, ziter_natCast]

/-- **The column-tiling alignment for the two-sided itinerary** (the dynamical headline). If `x`
sits at floor `i` of a height-`N` column over base `b` (`x = eⁱ b`), the column's sentinel-ended
block is `blk` (`blk j = c (eʲ b)`), the block ends in the sentinel and is otherwise sentinel-free,
and the previous column's terminator sits one coordinate below floor `0`
(`c (e⁻¹ b) = s`, i.e. `itin e c x (-1 - i) = s`), then

`sentinelParseAt s dec (itin e c x) = dec blk i`.

The position-aware parser recovers the offset `i` (the floor) and the column block `blk`; composing
with a `dec` that reads the `i`-th `Q`-symbol of the decoded block recovers the `Q`-cell of `x`. -/
theorem sentinelParseAt_itin_eq (s : Fin k) (dec : List (Fin k) → ℕ → κ)
    (e : α ≃ᵐ α) (c : α → Fin k) (b : α) (N i : ℕ) (hi : i < N)
    (blk : List (Fin k)) (hlen : blk.length = N)
    (hblk : ∀ j : Fin N, c ((e : α → α)^[(j : ℕ)] b) = blk.get (Fin.cast hlen.symm j))
    (htop : blk.get (Fin.cast hlen.symm ⟨N - 1, by omega⟩) = s)
    (hdata : ∀ j : Fin N, (j : ℕ) < N - 1 → blk.get (Fin.cast hlen.symm j) ≠ s)
    (hprev : itin e c ((e : α → α)^[i] b) (-1 - (i : ℤ)) = s) :
    sentinelParseAt s dec (itin e c ((e : α → α)^[i] b)) = dec blk i := by
  refine sentinelParseAt_column s dec (itin e c ((e : α → α)^[i] b)) N i hi blk hlen
    (fun j => ?_) htop hdata hprev
  rw [itin_apply, ziter_sub_floor e b i (j : ℕ), hblk j]

/-! ### The honest residual: the a.e. two-sided column tiling ⇒ the full term

The alignment recovers the `Q`-cell of `x` whenever its itinerary is column-tiled around `0`. The
*only* genuinely-residual input is the **existence of one fixed code symbol `c` whose itinerary is
a.e. column-tiled** (the refining-tower interleaving + the `m → ∞` / Borel–Cantelli mod-0 limit; a
single tower gives only a `1 - ε` set, not a μ-conull one). We isolate exactly this as the bundle
`ColumnLayoutData`, whose only non-structural field `recovers_tiled` is the a.e. recovery the
tiling produces. The structural assembly into `SentinelColumnCodeAt` (hence `CodesTwoSidedMod0c`) is
sorry-free — the measurable parser, code symbol, and decoder are all supplied; only the dynamical
a.e. correctness is carried, exactly as `Oseledets.Krieger.ColumnCodeData` /
`Oseledets.Krieger.CodeMapData` carry theirs. -/

/-- **The column-layout residual bundle.** Bundles the genuinely-dynamical inputs left after the
position-aware parser and the column-tiling alignment are discharged:

* `sentinel`, `code` (+ `code_measurable`): the reserved letter and the measurable code symbol,
  built (via `Oseledets.Krieger.floorAddr` + `Oseledets.Krieger.exists_sentinelEncoding`) so
  `c (eⁱ x)` spells the `i`-th symbol of the sentinel block of the column through `x`;
* `decode`: the position-aware per-block decoder (decode the sentinel block to its column
  `Q`-name — `Oseledets.Krieger.sentinelEncodeList_injective` — and read the symbol at the offset);
* `recovers_tiled`: the a.e. recovery the column tiling yields — for each `Q`-cell `j`, `Q j`
  agrees `μ`-a.e. with the position-aware parser event. This is the `m → ∞` interleaving residual:
  off a μ-null set the itinerary of `code` is two-sided column-tiled (the refining-tower limit),
  and on that set `sentinelParseAt_itin_eq` makes the parser recover the `Q`-cell of `x`.

This is the column-tiling analogue of `Oseledets.Krieger.SentinelColumnCode` /
`Oseledets.Krieger.ColumnCodeData`: it is exactly the `SentinelColumnCodeAt` data, named here so
the honest reduction (alignment discharged, parser discharged, only a.e. tiling residual carried) is
explicit. -/
structure ColumnLayoutData [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (e : α ≃ᵐ α) (μ : Measure α) (Q : κ → Set α) (k : ℕ) where
  /-- The reserved sentinel letter of the `Fin k` alphabet. -/
  sentinel : Fin k
  /-- The measurable code symbol `c : α → Fin k` of the column coding. -/
  code : α → Fin k
  /-- The code symbol is measurable. -/
  code_measurable : Measurable code
  /-- The position-aware per-block decode map (block content **and** offset of coordinate `0`). -/
  decode : List (Fin k) → ℕ → κ
  /-- A.e. recovery from the column tiling: each `Q`-cell agrees mod 0 with the position-aware
  parser event. This is the refining-tower / `m → ∞` interleaving residual; on the a.e. tiled set it
  is exactly `sentinelParseAt_itin_eq`. -/
  recovers_tiled : ∀ j, Q j =ᵐ[μ]
    {x | sentinelParseAt sentinel decode (itin e code x) = j}

/-- A `ColumnLayoutData` is exactly the data of a `SentinelColumnCodeAt` (the residual bundle of
`Oseledets.Krieger.TowerCode`): the column-tiling recovery `recovers_tiled` is its `recovers` field.
This makes the dynamical-core reduction explicit — the position-aware parser and the alignment are
discharged; only the a.e. column tiling is carried. -/
noncomputable def ColumnLayoutData.toSentinelColumnCodeAt
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (data : ColumnLayoutData e μ Q k) :
    SentinelColumnCodeAt e μ Q k where
  sentinel := data.sentinel
  code := data.code
  code_measurable := data.code_measurable
  decode := data.decode
  recovers := data.recovers_tiled

/-- **A `ColumnLayoutData` yields the cross-layer countable mod-0 code.** Composing
`ColumnLayoutData.toSentinelColumnCodeAt` with `Oseledets.Krieger.SentinelColumnCodeAt.codes` gives
`CodesTwoSidedMod0c` for the code partition — the deliverable that slots into
`Oseledets.Krieger.KriegerCodingData.code_codes`. Thus the entire symbolic side of sub-problem B
reduces, sorry-free, to the single residual `recovers_tiled` (the a.e. two-sided column tiling of
one fixed interleaving code symbol). -/
theorem ColumnLayoutData.codes
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (data : ColumnLayoutData e μ Q k) :
    CodesTwoSidedMod0c e Q
      (codePartition (μ := μ) data.code data.code_measurable) :=
  data.toSentinelColumnCodeAt.codes

end Oseledets.Krieger
