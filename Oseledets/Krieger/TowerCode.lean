/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.ColumnCode
import Oseledets.Krieger.RokhlinTower

/-!
# The position-aware sentinel parser for Krieger's column code (C3, sub-problem B)

This file repairs and sharpens the bi-infinite sentinel parser of
`Oseledets.Krieger.ColumnCode`. The parser there, `sentinelParse s dec w = dec (blockContent s w)`,
decodes the **content** of the sentinel block containing coordinate `0`. The dynamical-recovery
field that `SentinelColumnCode` then demands is

`recovers : ∀ j, Q j =ᵐ[μ] {x | sentinelParse s decode (itin e code x) = j}`,

i.e. the parser, fed the two-sided itinerary of a point `x`, must recover **which `Q`-cell `x`
itself lies in**. We show this is **impossible** for a generic countable generator `Q`:
`sentinelParse` is *position-blind*. The block content is the same list of symbols for every point
on the same tower column, while distinct floors of one column lie in genuinely different `Q`-cells
(a generator's cells cut across the floors). Formally, the two-sided itinerary intertwines the
dynamics with the one-step shift `shift w n = w (n+1)` (`itin_apply_e`), and `sentinelParse` is
**invariant under that shift inside a block** (`sentinelParse_shift_eq`): so the parser returns the
same label at `x` and at `e x` whenever both sit in one column, and no `decode` can make the parser
event coincide with the non-`e`-invariant cell `Q j`.

## The fix: carry the within-block offset

The classical Krieger/Downarowicz decoder reads off the `Q`-name at coordinate `0` by (i) locating
the sentinel-marked column boundaries, (ii) determining the **offset** of coordinate `0` inside the
column, and (iii) reading the symbol at that offset. Step (ii) — the offset — is available from the
stream (`blockOffset s w = bwdSentinel s (-1) w`, the distance back to the column's lower sentinel),
but `sentinelParse` discards it. The corrected parser

`sentinelParseAt s dec w = dec (blockContent s w) (blockOffset s w)`,

with `dec : List (Fin k) → ℕ → κ` taking the block content **and** the offset, keeps the offset
channel. It is still measurable (the offset is `measurable_bwdSentinel`, the content is the
`ColumnCode` decomposition), and — crucially — it is **not** shift-invariant: the offset increases
by one under the one-step shift (`blockOffset_shift`), so `sentinelParseAt` does distinguish `x`
from `e x` (`sentinelParseAt_can_separate`). The repaired residual bundle `SentinelColumnCodeAt`
uses it, and `SentinelColumnCodeAt.toColumnCodeData` shows it yields a full
`Oseledets.Krieger.ColumnCodeData` exactly as before, but now with a recovery field that is
*satisfiable* by the floor-address column code.

## Main definitions

* `shift` — the one-step shift `w ↦ (n ↦ w (n+1))` of a bi-infinite stream.
* `blockOffset s w` — the offset of coordinate `0` inside its sentinel block (`= bwdSentinel s
  (-1)`).
* `sentinelParseAt s dec w` — the **position-aware** parser, `dec (blockContent s w) (blockOffset)`.
* `SentinelColumnCodeAt` — the repaired residual bundle (code symbol + position-aware decode +
  satisfiable a.e. recovery).

## Main results

* `sentinelParse_shift_eq` — **the obstruction**: the old parser is shift-invariant inside a block.
* `parse_event_cannot_separate` — the old parser returns the same label at `x` and `e x` (the reason
  `SentinelColumnCode.recovers` is unsatisfiable for a generic generator).
* `blockOffset_shift` — the offset increases by one under the shift (the repaired position channel).
* `measurable_sentinelParseAt` — the position-aware parser is measurable.
* `sentinelParseAt_can_separate` — the position-aware parser *can* distinguish `x` from `e x`.
* `SentinelColumnCodeAt.toColumnCodeData` / `.codes` — the repaired bundle yields a full
  `ColumnCodeData`, hence the cross-layer mod-0 code.
* `floorAddr` / `measurable_floorAddr` — the measurable floor-address map of a Rokhlin tower (the
  within-column floor index), the first dynamical field of the code symbol (point (1) of the
  `Recovery` note).

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5).
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9.
* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*, Trans. Amer.
  Math. Soc. **149** (1970), 453–464.
-/

open MeasureTheory Function Set

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The one-step shift of a bi-infinite stream and its window/sentinel calculus -/

/-- The **one-step shift** of a bi-infinite stream: `shift w n = w (n + 1)`. The two-sided
itinerary intertwines the dynamics `e` with this shift (`itin_apply_e`): `itin e c (e x) =
shift (itin e c x)`. -/
def shift (w : ℤ → Fin k) : ℤ → Fin k := fun n => w (n + 1)

/-- `window` commutes with the shift: `window (shift w) b L = window w (b + 1) L`. -/
lemma window_shift (w : ℤ → Fin k) (b : ℤ) (L : ℕ) :
    window (shift w) b L = window w (b + 1) L := by
  unfold window shift
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_ofFn]
    congr 1
    ring

/-- Under `w 0 ≠ s` and a backward sentinel, the backward sentinel distance increases by one under
the shift. -/
lemma bwdSentinel_shift (s : Fin k) (w : ℤ → Fin k) (h0 : w 0 ≠ s)
    (hbwd : ∃ m : ℕ, w (-1 - (m : ℤ)) = s) :
    bwdSentinel s (-1) (shift w) = bwdSentinel s (-1) w + 1 := by
  classical
  set d := bwdSentinel s (-1) w with hd
  have hspec : bwdPred s (-1) w d := Nat.find_spec (exists_bwd s (-1) w)
  have hnofalse : ¬ (∀ m : ℕ, w (-1 - (m : ℤ)) ≠ s) := by push Not; exact hbwd
  have hwd : w (-1 - (d : ℤ)) = s := by
    rcases hspec with h | h
    · exact h
    · exact absurd h hnofalse
  have hmin : ∀ n < d, ¬ bwdPred s (-1) w n := fun n hn => Nat.find_min (exists_bwd s (-1) w) hn
  rw [bwdSentinel, Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · left
    change (shift w) (-1 - ((d : ℤ) + 1)) = s
    unfold shift
    rw [show -1 - ((d : ℤ) + 1) + 1 = -1 - (d : ℤ) by ring]
    exact hwd
  · intro n hn hpred
    rcases hpred with h | h
    · unfold shift at h
      rw [show -1 - (n : ℤ) + 1 = -(n : ℤ) by ring] at h
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0; simp only [Nat.cast_zero, neg_zero] at h; exact h0 h
      · have hkey : w (-1 - ((n - 1 : ℕ) : ℤ)) = s := by
          rw [show -1 - ((n - 1 : ℕ) : ℤ) = -(n : ℤ) by
            rw [Nat.cast_sub hnpos]; push_cast; ring]
          exact h
        exact hmin (n - 1) (by omega) (Or.inl hkey)
    · obtain ⟨m₀, hm₀⟩ := hbwd
      have hcontra := h (m₀ + 1)
      unfold shift at hcontra
      rw [show -1 - ((m₀ + 1 : ℕ) : ℤ) + 1 = -1 - (m₀ : ℤ) by push_cast; ring] at hcontra
      exact hcontra hm₀

/-- Under `w 0 ≠ s` and a forward sentinel, the forward sentinel distance decreases by one under the
shift. -/
lemma fwdSentinel_shift (s : Fin k) (w : ℤ → Fin k) (h0 : w 0 ≠ s)
    (hfwd : ∃ m : ℕ, w (0 + (m : ℤ)) = s) :
    fwdSentinel s 0 (shift w) + 1 = fwdSentinel s 0 w := by
  classical
  set f := fwdSentinel s 0 w with hf
  have hspec : fwdPred s 0 w f := Nat.find_spec (exists_fwd s 0 w)
  have hnofalse : ¬ (∀ m : ℕ, w (0 + (m : ℤ)) ≠ s) := by push Not; exact hfwd
  have hwf : w (0 + (f : ℤ)) = s := by
    rcases hspec with h | h
    · exact h
    · exact absurd h hnofalse
  have hmin : ∀ n < f, ¬ fwdPred s 0 w n := fun n hn => Nat.find_min (exists_fwd s 0 w) hn
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0' | h; swap; · exact h
    exfalso; apply h0; have := hwf; rw [h0'] at this; simpa using this
  have hval : fwdSentinel s 0 (shift w) = f - 1 := by
    rw [fwdSentinel, Nat.find_eq_iff]
    refine ⟨?_, ?_⟩
    · left
      change (shift w) (0 + ((f - 1 : ℕ) : ℤ)) = s
      unfold shift
      rw [show (0 : ℤ) + ((f - 1 : ℕ) : ℤ) + 1 = 0 + (f : ℤ) by
        rw [Nat.cast_sub hf1]; push_cast; ring]
      exact hwf
    · intro n hn hpred
      rcases hpred with h | h
      · unfold shift at h
        rw [show (0 : ℤ) + (n : ℤ) + 1 = 0 + ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
        exact hmin (n + 1) (by omega) (Or.inl h)
      · obtain ⟨m₀, hm₀⟩ := hfwd
        rcases Nat.eq_zero_or_pos m₀ with hm0 | hm0pos
        · subst hm0; exfalso; apply h0; simpa using hm₀
        · have := h (m₀ - 1)
          unfold shift at this
          rw [show (0 : ℤ) + ((m₀ - 1 : ℕ) : ℤ) + 1 = 0 + (m₀ : ℤ) by
            rw [Nat.cast_sub hm0pos]; push_cast; ring] at this
          exact this hm₀
  omega

/-! ### The obstruction: the position-blind parser cannot recover coordinate `0`'s cell -/

/-- **The block content is shift-invariant inside a block.** If coordinate `0` of the stream `w` is
not a sentinel and there are sentinels in both directions (the generic tiled case), then the
sentinel block around coordinate `0` of `w` and that of the one-step shift `shift w` are the **same
list** of symbols. The block re-anchors by one coordinate, but its content is identical: this is the
position-blindness of `blockContent`. -/
lemma blockContent_shift_eq (s : Fin k) (w : ℤ → Fin k) (h0 : w 0 ≠ s)
    (hbwd : ∃ m : ℕ, w (-1 - (m : ℤ)) = s) (hfwd : ∃ m : ℕ, w (0 + (m : ℤ)) = s) :
    blockContent s (shift w) = blockContent s w := by
  unfold blockContent
  have hbs : blockStart s (shift w) = blockStart s w - 1 := by
    unfold blockStart
    rw [bwdSentinel_shift s w h0 hbwd]; push_cast; ring
  have hlen : blockLen s (shift w) = blockLen s w := by
    unfold blockLen blockEnd blockStart
    rw [bwdSentinel_shift s w h0 hbwd]
    have hfs : (fwdSentinel s 0 (shift w) : ℤ) = (fwdSentinel s 0 w : ℤ) - 1 := by
      have := fwdSentinel_shift s w h0 hfwd; push_cast at this ⊢; omega
    rw [hfs]; congr 1; push_cast; ring
  rw [hbs, hlen, window_shift]
  congr 1
  ring

/-- **The old parser is shift-invariant inside a block.** Consequently `sentinelParse s dec`
returns the same `κ`-label at `w` and at its one-step shift `shift w` whenever coordinate `0` is not
a sentinel and the stream is tiled in both directions. -/
lemma sentinelParse_shift_eq (s : Fin k) (dec : List (Fin k) → κ) (w : ℤ → Fin k)
    (h0 : w 0 ≠ s)
    (hbwd : ∃ m : ℕ, w (-1 - (m : ℤ)) = s) (hfwd : ∃ m : ℕ, w (0 + (m : ℤ)) = s) :
    sentinelParse s dec (shift w) = sentinelParse s dec w := by
  unfold sentinelParse
  rw [blockContent_shift_eq s w h0 hbwd hfwd]

/-- The two-sided itinerary intertwines `e` with the one-step shift:
`itin e c (e x) = shift (itin e c x)`. -/
lemma itin_apply_e (e : α ≃ᵐ α) (c : α → Fin k) (x : α) :
    itin e c (e x) = shift (itin e c x) := by
  funext n
  simp only [itin_apply, shift]
  have hstep : ziter e n (e x) = ziter e (n + 1) x := by
    have hadd : ziter e (n + 1) = ziter e n ∘ ziter e 1 := ziter_add e n 1
    rw [hadd]; simp only [Function.comp_apply, ziter_one]
  rw [hstep]

/-- **The obstruction at the dynamical level.** For a point `x` whose itinerary stream is tiled (a
forward and backward sentinel exist) and whose coordinate `0` is not a sentinel, the
*position-blind* parser returns the **same** label at `x` and at `e x`:
`sentinelParse s dec (itin e c (e x)) = sentinelParse s dec (itin e c x)`. Since the floors `x` and
`e x` of one tower column lie in genuinely different cells of a generator `Q`, the parser event
`{x | sentinelParse s dec (itin e c x) = j}` cannot equal `Q j` a.e. for a generic generator — the
`recovers` field of `Oseledets.Krieger.SentinelColumnCode` is **unsatisfiable**. -/
theorem parse_event_cannot_separate (s : Fin k) (dec : List (Fin k) → κ) (e : α ≃ᵐ α)
    (c : α → Fin k) (x : α)
    (h0 : itin e c x 0 ≠ s)
    (hbwd : ∃ m : ℕ, itin e c x (-1 - (m : ℤ)) = s)
    (hfwd : ∃ m : ℕ, itin e c x (0 + (m : ℤ)) = s) :
    sentinelParse s dec (itin e c (e x)) = sentinelParse s dec (itin e c x) := by
  rw [itin_apply_e]
  exact sentinelParse_shift_eq s dec (itin e c x) h0 hbwd hfwd

/-! ### The fix: the position-aware parser -/

/-- **The within-block offset of coordinate `0`.** The distance from coordinate `0` back to the
lower sentinel of its block, `bwdSentinel s (-1) w`. Equivalently `-blockStart s w`. In the tiled
case it is exactly the floor index of `x` within its tower column, the piece of information the
position-blind `blockContent` discards. -/
noncomputable def blockOffset (s : Fin k) (w : ℤ → Fin k) : ℕ := bwdSentinel s (-1) w

@[simp] lemma blockOffset_def (s : Fin k) (w : ℤ → Fin k) :
    blockOffset s w = bwdSentinel s (-1) w := rfl

/-- **The offset increases by one under the shift** (the repaired position channel). If coordinate
`0` is not a sentinel and a backward sentinel exists, then
`blockOffset s (shift w) = blockOffset s w + 1` — matching the fact that `e x` sits one floor higher
in its column than `x`. This is exactly the information that distinguishes `x` from `e x`, lost by
the position-blind parser and restored here. -/
lemma blockOffset_shift (s : Fin k) (w : ℤ → Fin k) (h0 : w 0 ≠ s)
    (hbwd : ∃ m : ℕ, w (-1 - (m : ℤ)) = s) :
    blockOffset s (shift w) = blockOffset s w + 1 := by
  simp only [blockOffset_def]
  exact bwdSentinel_shift s w h0 hbwd

/-- The block-offset level set is measurable (it is a level set of the measurable backward sentinel
distance). -/
theorem measurableSet_blockOffset_eq (s : Fin k) (o : ℕ) :
    MeasurableSet {w : ℤ → Fin k | blockOffset s w = o} := by
  simp only [blockOffset_def]
  exact measurable_bwdSentinel s (-1) (measurableSet_singleton o)

/-- **The position-aware bi-infinite sentinel parser.** Given a block-decode map
`dec : List (Fin k) → ℕ → κ` taking the block content **and** the within-block offset of coordinate
`0`, the parser reads off both `blockContent s w` and `blockOffset s w`, and decodes:
`sentinelParseAt s dec w = dec (blockContent s w) (blockOffset s w)`. Unlike `sentinelParse`, it has
access to where coordinate `0` sits inside its column, so it can recover the `Q`-cell of `x` itself
(not merely the column name). -/
noncomputable def sentinelParseAt (s : Fin k) (dec : List (Fin k) → ℕ → κ)
    (w : ℤ → Fin k) : κ :=
  dec (blockContent s w) (blockOffset s w)

/-- **Each position-aware parser preimage is measurable.** For a target label `j : κ`, the set
`{w | dec (blockContent s w) (blockOffset s w) = j}` is the countable union, over block starts
`b : ℤ`, lengths `L : ℕ`, contents `l : List (Fin k)`, and offsets `o : ℕ` with `dec l o = j`, of
the cylinder `{blockStart = b} ∩ {blockLen = L} ∩ {window b L = l} ∩ {blockOffset = o}`. Each factor
is measurable (`measurableSet_blockStart_eq`, `measurableSet_blockLen_eq`,
`measurableSet_window_eq`, `measurableSet_blockOffset_eq`) and the index types are countable. -/
theorem measurableSet_parseAt_eq [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (s : Fin k) (dec : List (Fin k) → ℕ → κ) (j : κ) :
    MeasurableSet {w : ℤ → Fin k | dec (blockContent s w) (blockOffset s w) = j} := by
  have hdecomp : {w : ℤ → Fin k | dec (blockContent s w) (blockOffset s w) = j} =
      ⋃ b : ℤ, ⋃ L : ℕ, ⋃ o : ℕ, ⋃ l ∈ {l : List (Fin k) | dec l o = j},
        ({w | blockStart s w = b} ∩ {w | blockLen s w = L} ∩ {w | window w b L = l}
          ∩ {w | blockOffset s w = o}) := by
    ext w
    simp only [blockContent, mem_setOf_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro h
      exact ⟨blockStart s w, blockLen s w, blockOffset s w,
        window w (blockStart s w) (blockLen s w), h, ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨b, L, o, l, hgl, ⟨⟨hb, hL⟩, hwin⟩, ho⟩
      rw [hb, hL, hwin, ho]; exact hgl
  rw [hdecomp]
  refine MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun L =>
    MeasurableSet.iUnion (fun o => ?_)))
  refine MeasurableSet.biUnion (Set.to_countable _) (fun l _ => ?_)
  refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter ?_ ?_)
    (measurableSet_window_eq b L l)) (measurableSet_blockOffset_eq s o)
  · exact measurableSet_blockStart_eq s b
  · exact measurableSet_blockLen_eq s L

/-- **The position-aware sentinel parser is measurable.** The codomain `κ` is `Countable` with
`MeasurableSingletonClass`, so `measurable_to_countable'` reduces to measurability of each preimage,
supplied by `measurableSet_parseAt_eq`. -/
theorem measurable_sentinelParseAt [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (s : Fin k) (dec : List (Fin k) → ℕ → κ) :
    Measurable (sentinelParseAt s dec) := by
  refine measurable_to_countable' (fun j => ?_)
  exact measurableSet_parseAt_eq s dec j

/-- **The position-aware parser *can* separate `x` from `e x`** — it is not shift-invariant. Whereas
`sentinelParse` returns the same label at `x` and `e x` (`parse_event_cannot_separate`),
`sentinelParseAt` reads the offset, which increases by one under the shift (`blockOffset_shift`), so
it evaluates `dec` at offsets `blockOffset s w` and `blockOffset s w + 1` on the *same* block
content. A decoder that reads off the symbol at the offset position therefore recovers the distinct
`Q`-cells of the two floors. This is the capability the repaired `recovers` field relies on. -/
theorem sentinelParseAt_can_separate (s : Fin k) (dec : List (Fin k) → ℕ → κ)
    (w : ℤ → Fin k)
    (h0 : w 0 ≠ s) (hbwd : ∃ m : ℕ, w (-1 - (m : ℤ)) = s)
    (hfwd : ∃ m : ℕ, w (0 + (m : ℤ)) = s) :
    sentinelParseAt s dec (shift w) = dec (blockContent s w) (blockOffset s w + 1) := by
  unfold sentinelParseAt
  rw [blockContent_shift_eq s w h0 hbwd hfwd, blockOffset_shift s w h0 hbwd]

/-! ### The repaired residual bundle -/

/-- **The repaired column-code residual.** Identical to `Oseledets.Krieger.SentinelColumnCode`
except that the decoder is **position-aware** — `decode : List (Fin k) → ℕ → κ` reads both the block
content and the within-block offset of coordinate `0`. The recovery field uses the position-aware
parser `sentinelParseAt`, and is *satisfiable* by the floor-address column code (the floors of a
column carry distinct offsets, so `decode block offset` can return the genuine `Q`-cell of `x`),
unlike `SentinelColumnCode.recovers`. -/
structure SentinelColumnCodeAt [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (e : α ≃ᵐ α) (μ : Measure α) (Q : κ → Set α) (k : ℕ) where
  /-- The reserved sentinel letter of the `Fin k` alphabet. -/
  sentinel : Fin k
  /-- The measurable code symbol `c : α → Fin k` of the column coding. -/
  code : α → Fin k
  /-- The code symbol is measurable. -/
  code_measurable : Measurable code
  /-- The position-aware per-block decode map (block content **and** offset of coordinate `0`). -/
  decode : List (Fin k) → ℕ → κ
  /-- A.e. correctness of the position-aware sentinel parse. -/
  recovers : ∀ j, Q j =ᵐ[μ]
    {x | sentinelParseAt sentinel decode (itin e code x) = j}

/-- **The repaired residual yields a full `ColumnCodeData`.** The decoder field is filled by the
measurable position-aware parser `sentinelParseAt sentinel decode` (`measurable_sentinelParseAt`),
and the recovery field is the supplied a.e. correctness. -/
noncomputable def SentinelColumnCodeAt.toColumnCodeData
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (data : SentinelColumnCodeAt e μ Q k) :
    ColumnCodeData e μ Q k where
  code := data.code
  code_measurable := data.code_measurable
  decoder := sentinelParseAt data.sentinel data.decode
  decoder_measurable := measurable_sentinelParseAt data.sentinel data.decode
  recovers := data.recovers

/-- A `SentinelColumnCodeAt` yields the cross-layer countable mod-0 code of `Q` by its code
partition — the deliverable that slots into `Oseledets.Krieger.KriegerCodingData.code_codes`. -/
theorem SentinelColumnCodeAt.codes
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (data : SentinelColumnCodeAt e μ Q k) :
    CodesTwoSidedMod0c e Q
      (codePartition (μ := μ) data.code data.code_measurable) :=
  (data.toColumnCodeData).codes

/-! ### The measurable floor-address map of a Rokhlin tower

The first dynamical field of a `SentinelColumnCodeAt` — the code symbol `c : α → Fin k` — is built
from the **floor-address map** of a Rokhlin tower (`Oseledets.Krieger.rokhlin_tower`): the index of
the floor a point sits on within its column. We construct it here as a measurable `ℕ`-valued map
(junk value `N` off the tower), which is exactly the within-column offset the position-aware parser
(`blockOffset`) consumes. This is the self-contained, reusable piece point (1) of the `Recovery`
module note asked for (and is reused by `KeaneSerafinLevels` for sub-problem A). -/

/-- The floor levels of the tower: `level e A N i = eⁱ '' (towerBase e A N)`. -/
def level (e : α ≃ᵐ α) (A : Set α) (N : ℕ) (i : ℕ) : Set α :=
  (e : α → α)^[i] '' towerBase e A N

theorem measurableSet_level (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) (N i : ℕ) :
    MeasurableSet (level e A N i) :=
  measurableSet_iterate_image e i (measurableSet_towerBase e hA N)

open Classical in
/-- **The floor-address map** of a Rokhlin tower: the least `i < N` with `x ∈ eⁱ '' B`, or `N` if
`x` is off the tower. By level disjointness (`pairwise_disjoint_levels`) this least index is the
unique one, so the map is the genuine floor address. It feeds the per-column block read of the code
symbol `c` (point (1) of the `Recovery` note), and its value is the within-block offset of the
position-aware parser on the corresponding itinerary. -/
noncomputable def floorAddr (e : α ≃ᵐ α) (A : Set α) (N : ℕ) (x : α) : ℕ :=
  if h : ∃ i : ℕ, i < N ∧ x ∈ level e A N i then Nat.find h else N

/-- On the tower, `floorAddr` picks an index `< N` and `x` lies in that level. -/
lemma floorAddr_spec (e : α ≃ᵐ α) (A : Set α) (N : ℕ) {x : α}
    (h : ∃ i : ℕ, i < N ∧ x ∈ level e A N i) :
    floorAddr e A N x < N ∧ x ∈ level e A N (floorAddr e A N x) := by
  classical
  rw [floorAddr, dif_pos h]
  exact Nat.find_spec h

/-- The floor-address level set, for `i < N`, is exactly the `i`-th level (using disjointness:
the least admissible index is the unique one). -/
lemma floorAddr_eq_level (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N) {i : ℕ}
    (hi : i < N) :
    {x | floorAddr e A N x = i} = level e A N i := by
  classical
  ext x
  simp only [mem_setOf_eq]
  constructor
  · intro h
    have hex : ∃ j : ℕ, j < N ∧ x ∈ level e A N j := by
      by_contra hcon
      rw [floorAddr, dif_neg hcon] at h
      omega
    obtain ⟨_, hmem⟩ := floorAddr_spec e A N hex
    rwa [h] at hmem
  · intro hx
    have hex : ∃ j : ℕ, j < N ∧ x ∈ level e A N j := ⟨i, hi, hx⟩
    obtain ⟨hlt, hmem⟩ := floorAddr_spec e A N hex
    by_contra hne
    have hdisj := pairwise_disjoint_levels e A hN
      (i := ⟨floorAddr e A N x, hlt⟩) (j := ⟨i, hi⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; exact fun h => hne h)
    simp only [Function.onFun] at hdisj
    exact (Set.disjoint_left.mp hdisj) hmem hx

/-- The off-tower level set is the complement of the covered set. -/
lemma floorAddr_eq_N (e : α ≃ᵐ α) (A : Set α) (N : ℕ) :
    {x | floorAddr e A N x = N} = (coveredSet e A N)ᶜ := by
  classical
  ext x
  simp only [mem_setOf_eq, mem_compl_iff, coveredSet, mem_iUnion, not_exists]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := hcon
    have hex : ∃ j : ℕ, j < N ∧ x ∈ level e A N j := ⟨i, i.isLt, hi⟩
    obtain ⟨hlt, _⟩ := floorAddr_spec e A N hex
    omega
  · intro h
    have hnex : ¬ ∃ j : ℕ, j < N ∧ x ∈ level e A N j := by
      rintro ⟨j, hj, hmem⟩
      exact h ⟨j, hj⟩ hmem
    rw [floorAddr, dif_neg hnex]

/-- **The floor-address map is measurable.** A `ℕ`-valued map whose level sets are the tower levels
(for `i < N`, `floorAddr_eq_level`), the covered-set complement (for `i = N`, `floorAddr_eq_N`), or
empty (for `i > N`); each is measurable, and `ℕ` is countable. -/
theorem measurable_floorAddr (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) {N : ℕ}
    (hN : 1 ≤ N) :
    Measurable (floorAddr e A N) := by
  classical
  refine measurable_to_countable' (fun i => ?_)
  have hpre : (floorAddr e A N) ⁻¹' {i} = {x | floorAddr e A N x = i} := by
    ext x; simp [Set.mem_preimage, Set.mem_singleton_iff]
  rw [hpre]
  rcases lt_trichotomy i N with hlt | heq | hgt
  · rw [floorAddr_eq_level e A hN hlt]; exact measurableSet_level e hA N i
  · rw [heq, floorAddr_eq_N e A N]
    refine MeasurableSet.compl ?_
    rw [coveredSet]
    exact MeasurableSet.iUnion (fun i => measurableSet_iterate_image e (i : ℕ)
      (measurableSet_towerBase e hA N))
  · have hempty : {x | floorAddr e A N x = i} = (∅ : Set α) := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      by_cases hex : ∃ j : ℕ, j < N ∧ x ∈ level e A N j
      · obtain ⟨hlt, _⟩ := floorAddr_spec e A N hex; omega
      · rw [floorAddr, dif_neg hex] at h; omega
    rw [hempty]; exact MeasurableSet.empty

end Oseledets.Krieger
