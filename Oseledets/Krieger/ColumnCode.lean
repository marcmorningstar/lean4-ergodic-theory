/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.Recovery
import Oseledets.Krieger.PrefixCode
import Mathlib.Data.List.OfFn

/-!
# The measurable bi-infinite sentinel parser for Krieger's symbolic code (C3, sub-problem B)

This file builds the **single largest infrastructure gap** that the column-code residual of
sub-problem B (C3) of Krieger's finite generator theorem (issue #15) was reduced to in
`Oseledets.Krieger.Recovery`: the **measurable bi-infinite sentinel parser**

`D : (ℤ → Fin k) → κ`

that locates the marker/sentinel structure of a `ℤ`-indexed code stream around coordinate `0`,
extracts the local block, and decodes it — *as a measurable function of the stream*. The module note
at the bottom of `Recovery.lean` flagged this — point (3) — as the part with **no Mathlib analogue**
and the "genuine multi-week residual". **This file discharges it, unconditionally and sorry-free.**

## The verdict: the measurable bi-infinite parser is constructible on current Mathlib

The construction needs **no new symbolic-dynamics infrastructure** — only three standard pieces of
Mathlib measurability, assembled:

* `measurable_pi_apply` — each coordinate projection `w ↦ w n` of the product space `ℤ → Fin k` is
  measurable;
* `measurable_find` (`Nat.find` of a totalized forward search is measurable) — gives a **measurable
  sentinel-position function** in each direction (the backward search is a forward search in the
  reflected stream); and
* `measurable_to_countable'` — the codomain `κ` is `Countable` with `MeasurableSingletonClass`, so
  the parser is measurable as soon as each preimage `D⁻¹{j}` is measurable.

The preimage `D⁻¹{j}` decomposes as a **countable union over block shapes** `(b, L, l)` (start
`b : ℤ`, length `L : ℕ`, content `l : List (Fin k)`) of cylinder sets
`{blockStart = b} ∩ {blockLen = L} ∩ {window b L = l}` — each measurable. The window-content
cylinder `{w | window w b L = l}` is a **finite intersection of coordinate-singleton constraints**
(`measurableSet_window_eq`). This is the whole of the "measurable bi-infinite parse".

So the residual flagged as multi-week is, in fact, a few hundred lines of routine measurability.
What genuinely remains for an *unconditional* `ColumnCodeData` is the **dynamical** content — the
construction of one fixed code symbol `c : α → Fin k` whose per-column blocks spell the sentinel
encodings of the `Q`-names, and the a.e. recovery that the parser then reads off (points (1), (2),
(4) of the `Recovery` note). Note that a decoder must be **position-aware** to satisfy the recovery
field: the bare `sentinelParse` of this file is position-blind, so a naive sentinel-column recovery
bundle built on it is unsatisfiable (see the trap note at the end of this file, and the repaired
position-aware `SentinelColumnCodeAt` in `Oseledets.Krieger.TowerCode`).

## Main definitions

* `window w b L` — the length-`L` block of the stream `w` starting at integer coordinate `b`.
* `fwdSentinel s b w` / `bwdSentinel s b w` — the forward / backward distance to the nearest
  sentinel `s` from anchor `b` (totalized: `0` if the search direction has no sentinel).
* `blockStart s w` / `blockLen s w` / `blockContent s w` — the start, length and `List (Fin k)`
  content of the sentinel block containing coordinate `0`.
* `sentinelParse s dec w` — the parser: decode `blockContent s w` via `dec : List (Fin k) → κ`.

## Main results (all sorry-free)

* `measurableSet_window_eq` — `{w | window w b L = l}` is measurable.
* `measurable_fwdSentinel`, `measurable_bwdSentinel` — the sentinel-distance functions are
  measurable; hence the block-boundary level sets `measurableSet_blockStart_eq`,
  `measurableSet_blockLen_eq`.
* `measurableSet_blockContent_decode_eq` — each preimage `{w | dec (blockContent s w) = j}` is
  measurable (the countable-block-shape decomposition).
* `measurable_sentinelParse` — **the headline: the bi-infinite sentinel parser is measurable.**

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5).
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9 (marker
  codes and the decoder).
* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*, Trans. Amer.
  Math. Soc. **149** (1970), 453–464.
-/

open MeasureTheory Function Set

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### Coordinate cylinders of the bi-infinite stream

The product space `ℤ → Fin k` carries the product σ-algebra; each coordinate projection
`w ↦ w c` is measurable (`measurable_pi_apply`), so the singleton-value cylinder `{w | w c = s}` is
measurable. This is the only atom every measurability proof in this file is built from. -/

/-- **The single-coordinate cylinder is measurable.** `{w | w c = s}` is the preimage of the
singleton `{s}` under the measurable coordinate projection `w ↦ w c` (`measurable_pi_apply`). Every
measurability statement below — the window cylinders, the sentinel-position level sets, the parser
preimages — is assembled from this atom by countable Boolean operations. -/
theorem measurableSet_coord_eq (c : ℤ) (s : Fin k) :
    MeasurableSet {w : ℤ → Fin k | w c = s} := by
  have hset : {w : ℤ → Fin k | w c = s} = (fun w : ℤ → Fin k => w c) ⁻¹' {s} := by
    ext w; simp
  rw [hset]
  exact (measurable_pi_apply c) (measurableSet_singleton s)

/-! ### The window extractor and the window cylinder

`window w b L` reads the length-`L` block of the stream starting at integer coordinate `b`. The
parser will read off the content of the sentinel block containing coordinate `0` through this map.
Its key measurability fact, `measurableSet_window_eq`, is that fixing the start `b`, length `L`, and
target content `l` carves out a measurable cylinder — a *finite* intersection of coordinate
constraints. -/

/-- **The length-`L` window of a bi-infinite stream starting at coordinate `b`.** The block
`[w b, w (b+1), …, w (b+L-1)] : List (Fin k)`. A decoder reads off the sentinel block containing
coordinate `0` as `window w (blockStart …) (blockLen …)`. -/
def window (w : ℤ → Fin k) (b : ℤ) (L : ℕ) : List (Fin k) :=
  List.ofFn (fun i : Fin L => w (b + (i : ℕ)))

@[simp] lemma window_length (w : ℤ → Fin k) (b : ℤ) (L : ℕ) : (window w b L).length = L := by
  simp [window]

/-- **The window cylinder is measurable.** Fixing the start `b : ℤ`, length `L : ℕ`, and target
block `l : List (Fin k)`, the set `{w | window w b L = l}` of streams whose length-`L` block at `b`
equals `l` is measurable: if `|l| = L`, it is the **finite** intersection
`⋂ i : Fin L, {w | w (b + i) = l i}` of coordinate-singleton cylinders (`measurableSet_coord_eq`,
via `List.ofFn_inj`); if `|l| ≠ L` it is empty (the window always has length `L`). This is the
content-extraction half of the parser; combined with measurable block boundaries it gives the parser
preimage decomposition. -/
theorem measurableSet_window_eq (b : ℤ) (L : ℕ) (l : List (Fin k)) :
    MeasurableSet {w : ℤ → Fin k | window w b L = l} := by
  by_cases hlen : l.length = L
  · -- `l = List.ofFn g` for `g i := l.get (Fin.cast hlen.symm i)`; compare via `List.ofFn_inj`.
    set g : Fin L → Fin k := fun i => l.get (Fin.cast hlen.symm i) with hg
    have hl : l = List.ofFn g := by
      apply List.ext_get
      · simp [hlen]
      · intro n h1 h2; simp only [hg, List.get_ofFn]; congr 1
    have key : ∀ w : ℤ → Fin k, (window w b L = l) ↔
        (∀ i : Fin L, w (b + (i : ℕ)) = g i) := by
      intro w; rw [window, hl, List.ofFn_inj]; exact funext_iff
    have hrw : {w : ℤ → Fin k | window w b L = l} =
        ⋂ i : Fin L, {w : ℤ → Fin k | w (b + (i : ℕ)) = g i} := by
      ext w; simp only [mem_setOf_eq, mem_iInter]; exact key w
    rw [hrw]
    exact MeasurableSet.iInter (fun i => measurableSet_coord_eq _ _)
  · have hempty : {w : ℤ → Fin k | window w b L = l} = ∅ := by
      ext w; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h; apply hlen; rw [← h]; simp [window]
    rw [hempty]; exact MeasurableSet.empty

/-! ### The measurable sentinel-position search

The block boundaries are located by searching for the nearest sentinel. The forward search from an
anchor `b` looks for the least `n : ℕ` with `w (b + n) = s`; the backward search looks for the least
`n : ℕ` with `w (b - n) = s` — a forward search in the reflected stream, equally measurable. Both
are **totalized** (return `0` if that direction has no sentinel) so they are total functions of the
stream; on the a.e. set where the orbit is tiled by complete columns (the two-sided recurrence
backbone `twoSided_recurrence`) the search always succeeds and the totalization is irrelevant. -/

/-- The totalized forward-search predicate: a sentinel `s` sits at coordinate `b + n`, **or** the
forward ray from `b` contains no sentinel at all. The disjunction guarantees a witness for every
stream (`exists_fwd`), so `Nat.find` is total and `measurable_find` applies. -/
def fwdPred (s : Fin k) (b : ℤ) (w : ℤ → Fin k) (n : ℕ) : Prop :=
  w (b + (n : ℤ)) = s ∨ (∀ m : ℕ, w (b + (m : ℤ)) ≠ s)

/-- The totalized backward-search predicate (forward search in the reflected stream): a sentinel
sits at coordinate `b - n`, or the backward ray from `b` contains no sentinel. -/
def bwdPred (s : Fin k) (b : ℤ) (w : ℤ → Fin k) (n : ℕ) : Prop :=
  w (b - (n : ℤ)) = s ∨ (∀ m : ℕ, w (b - (m : ℤ)) ≠ s)

theorem exists_fwd (s : Fin k) (b : ℤ) (w : ℤ → Fin k) : ∃ n, fwdPred s b w n := by
  by_cases h : ∃ n : ℕ, w (b + (n : ℤ)) = s
  · obtain ⟨n, hn⟩ := h; exact ⟨n, Or.inl hn⟩
  · push Not at h; exact ⟨0, Or.inr h⟩

theorem exists_bwd (s : Fin k) (b : ℤ) (w : ℤ → Fin k) : ∃ n, bwdPred s b w n := by
  by_cases h : ∃ n : ℕ, w (b - (n : ℤ)) = s
  · obtain ⟨n, hn⟩ := h; exact ⟨n, Or.inl hn⟩
  · push Not at h; exact ⟨0, Or.inr h⟩

theorem measurableSet_fwdPred (s : Fin k) (b : ℤ) (n : ℕ) :
    MeasurableSet {w : ℤ → Fin k | fwdPred s b w n} := by
  have h2 : MeasurableSet {w : ℤ → Fin k | ∀ m : ℕ, w (b + (m : ℤ)) ≠ s} := by
    rw [show {w : ℤ → Fin k | ∀ m : ℕ, w (b + (m : ℤ)) ≠ s}
        = ⋂ m : ℕ, {w | w (b + (m : ℤ)) ≠ s} by ext w; simp]
    exact MeasurableSet.iInter (fun m => (measurableSet_coord_eq _ s).compl)
  have hrw : {w : ℤ → Fin k | fwdPred s b w n}
      = {w | w (b + (n : ℤ)) = s} ∪ {w | ∀ m : ℕ, w (b + (m : ℤ)) ≠ s} := by
    ext w; simp [fwdPred]
  rw [hrw]; exact (measurableSet_coord_eq _ s).union h2

theorem measurableSet_bwdPred (s : Fin k) (b : ℤ) (n : ℕ) :
    MeasurableSet {w : ℤ → Fin k | bwdPred s b w n} := by
  have h2 : MeasurableSet {w : ℤ → Fin k | ∀ m : ℕ, w (b - (m : ℤ)) ≠ s} := by
    rw [show {w : ℤ → Fin k | ∀ m : ℕ, w (b - (m : ℤ)) ≠ s}
        = ⋂ m : ℕ, {w | w (b - (m : ℤ)) ≠ s} by ext w; simp]
    exact MeasurableSet.iInter (fun m => (measurableSet_coord_eq _ s).compl)
  have hrw : {w : ℤ → Fin k | bwdPred s b w n}
      = {w | w (b - (n : ℤ)) = s} ∪ {w | ∀ m : ℕ, w (b - (m : ℤ)) ≠ s} := by
    ext w; simp [bwdPred]
  rw [hrw]; exact (measurableSet_coord_eq _ s).union h2

open Classical in
/-- **The forward sentinel distance.** The least `n : ℕ` such that `w (b + n) = s`, or `0` if the
forward ray from `b` has no sentinel. Measurable in `w` (`measurable_fwdSentinel`). -/
noncomputable def fwdSentinel (s : Fin k) (b : ℤ) (w : ℤ → Fin k) : ℕ :=
  Nat.find (exists_fwd s b w)

open Classical in
/-- **The backward sentinel distance.** The least `n : ℕ` such that `w (b - n) = s`, or `0` if the
backward ray from `b` has no sentinel. Measurable in `w` (`measurable_bwdSentinel`). -/
noncomputable def bwdSentinel (s : Fin k) (b : ℤ) (w : ℤ → Fin k) : ℕ :=
  Nat.find (exists_bwd s b w)

/-- **The forward sentinel distance is measurable.** This is the crux that the `Recovery` note
flagged as having "no Mathlib analogue": a measurable locator of the marker structure of a
`ℤ`-stream. It is `Nat.find` of a totalized forward search — `measurable_find` applies because the
totalization makes the search succeed for *every* stream (`exists_fwd`) and each predicate level set
is measurable (`measurableSet_fwdPred`). -/
theorem measurable_fwdSentinel (s : Fin k) (b : ℤ) : Measurable (fwdSentinel s b) := by
  classical
  exact measurable_find (exists_fwd s b) (fun n => measurableSet_fwdPred s b n)

/-- **The backward sentinel distance is measurable** (the reflected-stream form of
`measurable_fwdSentinel`). -/
theorem measurable_bwdSentinel (s : Fin k) (b : ℤ) : Measurable (bwdSentinel s b) := by
  classical
  exact measurable_find (exists_bwd s b) (fun n => measurableSet_bwdPred s b n)

/-! ### The block around coordinate `0`: start, length, content

The sentinel block containing coordinate `0` is delimited by the nearest sentinels on either side.
We take the **block start** to be one past the nearest sentinel strictly before coordinate `0`
(found by the backward search anchored at `-1`), and the **block end** to be the nearest sentinel at
coordinate `≥ 0` (the forward search anchored at `0`). The **content** is the window from start to
end inclusive — exactly one sentinel-terminated block in the well-tiled (a.e.) case. Each of
`blockStart`, `blockLen` is a measurable integer/nat function of the stream, built from the
measurable sentinel distances. -/

/-- **The start of the sentinel block containing coordinate `0`.** One past the nearest sentinel
strictly before `0`: anchoring the backward search at `-1` finds the distance `d` to that sentinel
(`w (-1 - d) = s`), and the block starts at `-1 - d + 1 = -d`. (In the no-sentinel-below case the
totalized search returns `d = 0`, giving start `0`; this only happens off the a.e. tiled set.) -/
noncomputable def blockStart (s : Fin k) (w : ℤ → Fin k) : ℤ :=
  -(bwdSentinel s (-1) w : ℤ)

/-- **The end coordinate of the sentinel block containing coordinate `0`.** The nearest sentinel at
coordinate `≥ 0`: the forward search anchored at `0` gives the distance, and the end is at that
coordinate (inclusive, the terminating sentinel of the block). -/
noncomputable def blockEnd (s : Fin k) (w : ℤ → Fin k) : ℤ :=
  (fwdSentinel s 0 w : ℤ)

/-- **The length of the sentinel block containing coordinate `0`** (inclusive of the terminating
sentinel): `blockEnd − blockStart + 1`, clamped to `ℕ`. -/
noncomputable def blockLen (s : Fin k) (w : ℤ → Fin k) : ℕ :=
  (blockEnd s w - blockStart s w + 1).toNat

/-- **The content of the sentinel block containing coordinate `0`** as a `List (Fin k)`: the window
of length `blockLen` starting at `blockStart`. A decoder applies `dec : List (Fin k) → κ` to this to
read off the `Q`-label. -/
noncomputable def blockContent (s : Fin k) (w : ℤ → Fin k) : List (Fin k) :=
  window w (blockStart s w) (blockLen s w)

/-- **Each block-start level set is measurable.** `{w | blockStart s w = b}` is the level set of
the measurable backward sentinel distance: `blockStart s w = b ⇔ bwdSentinel s (-1) w = (-b).toNat`
when `b ≤ 0` (and is empty when `b > 0`, since a distance is non-negative). This is all the parser
preimage decomposition uses; we avoid an honest `Measurable (blockStart s)` (whose `ℤ`-arithmetic
plumbing is irrelevant) in favour of the level sets directly. -/
theorem measurableSet_blockStart_eq (s : Fin k) (b : ℤ) :
    MeasurableSet {w : ℤ → Fin k | blockStart s w = b} := by
  by_cases hb : 0 ≤ b
  · -- a block start `-(distance)` is `≤ 0`; if `b > 0` it is unattainable, if `b = 0` it forces
    -- distance `0`.
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · -- `b = 0`: `blockStart = 0 ⇔ bwdSentinel = 0`.
      have hrw : {w : ℤ → Fin k | blockStart s w = b}
          = {w | bwdSentinel s (-1) w = 0} := by
        ext w; simp only [blockStart, mem_setOf_eq, ← hb0, neg_eq_zero, Nat.cast_eq_zero]
      rw [hrw]; exact measurable_bwdSentinel s (-1) (measurableSet_singleton 0)
    · -- `b > 0`: empty, `-(n:ℤ) = b > 0` impossible (`-(n:ℤ) ≤ 0`).
      have hrw : {w : ℤ → Fin k | blockStart s w = b} = ∅ := by
        ext w; simp only [blockStart, mem_setOf_eq, mem_empty_iff_false, iff_false]
        intro h
        have hle : -(bwdSentinel s (-1) w : ℤ) ≤ 0 :=
          neg_nonpos_of_nonneg (Int.natCast_nonneg _)
        rw [h] at hle; omega
      rw [hrw]; exact MeasurableSet.empty
  · -- `b < 0`: `blockStart = b ⇔ bwdSentinel = (-b).toNat`.
    push Not at hb
    have hrw : {w : ℤ → Fin k | blockStart s w = b}
        = {w | bwdSentinel s (-1) w = (-b).toNat} := by
      ext w
      simp only [blockStart, mem_setOf_eq]
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h, Int.toNat_of_nonneg (by linarith), neg_neg]
    rw [hrw]
    exact measurable_bwdSentinel s (-1) (measurableSet_singleton _)

/-- **Each block-length level set is measurable.** `{w | blockLen s w = L}` is a measurable set: it
decomposes over the (countably many) pairs of forward/backward sentinel distances `(f, d)` that
produce length `L`, and each `{fwdSentinel = f} ∩ {bwdSentinel = d}` is measurable. Again we expose
only the level sets, which is what the parser preimage decomposition consumes. -/
theorem measurableSet_blockLen_eq (s : Fin k) (L : ℕ) :
    MeasurableSet {w : ℤ → Fin k | blockLen s w = L} := by
  -- `blockLen s w = ((fwdSentinel s 0 w : ℤ) - blockStart s w + 1).toNat`, and
  -- `blockStart s w = -(bwdSentinel s (-1) w)`, so `blockLen` is a function of the pair
  -- `(fwdSentinel s 0 w, bwdSentinel s (-1) w)`. Decompose the level set over that pair.
  have hrw : {w : ℤ → Fin k | blockLen s w = L}
      = ⋃ f : ℕ, ⋃ d : ℕ, ⋃ (_ : ((f : ℤ) - (-(d : ℤ)) + 1).toNat = L),
          ({w | fwdSentinel s 0 w = f} ∩ {w | bwdSentinel s (-1) w = d}) := by
    ext w
    simp only [blockLen, blockEnd, blockStart, mem_setOf_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro h
      exact ⟨fwdSentinel s 0 w, bwdSentinel s (-1) w, h, rfl, rfl⟩
    · rintro ⟨f, d, hfd, hf, hd⟩
      rw [hf, hd]; exact hfd
  rw [hrw]
  refine MeasurableSet.iUnion (fun f => MeasurableSet.iUnion (fun d => ?_))
  by_cases hcond : ((f : ℤ) - (-(d : ℤ)) + 1).toNat = L
  · simp only [hcond, iUnion_true]
    exact (measurable_fwdSentinel s 0 (measurableSet_singleton f)).inter
      (measurable_bwdSentinel s (-1) (measurableSet_singleton d))
  · simp only [hcond, iUnion_false]; exact MeasurableSet.empty

/-! ### The parser and its measurability — the headline of this file

The parser applies a decode map `dec : List (Fin k) → κ` to the block content. Its measurability is
proved by the countable-codomain route (`measurable_to_countable'`): each preimage
`{w | dec (blockContent s w) = j}` decomposes over the countably many block shapes `(b, L, l)` as a
union of cylinders `{blockStart = b} ∩ {blockLen = L} ∩ {window b L = l}`. This is the measurable
bi-infinite sentinel parser that `Recovery` isolated as the residual with no Mathlib analogue. -/

/-- **The bi-infinite sentinel parser.** Given a block-decode map `dec : List (Fin k) → κ`, the
parser `sentinelParse s dec w` reads off the sentinel block of the bi-infinite stream `w` containing
coordinate `0` (`blockContent s w`) and decodes it. This is the decoder `D` of
`Oseledets.Krieger.ColumnCodeData`, now an *honest* total function rather than a hypothesis. -/
noncomputable def sentinelParse (s : Fin k) (dec : List (Fin k) → κ) (w : ℤ → Fin k) : κ :=
  dec (blockContent s w)

/-- **Each parser preimage is measurable (the countable block-shape decomposition).** For a fixed
target label `j : κ`, the set `{w | dec (blockContent s w) = j}` is the countable union, over all
block starts `b : ℤ`, lengths `L : ℕ`, and contents `l : List (Fin k)` with `dec l = j`, of the
cylinder `{blockStart = b} ∩ {blockLen = L} ∩ {window b L = l}`. Each factor is measurable
(`measurable_blockStart`, `measurable_blockLen`, `measurableSet_window_eq`), `List (Fin k)` is
countable, and `ℤ`, `ℕ` are countable, so the union is measurable. This is the entire content of the
"measurable bi-infinite parse". -/
theorem measurableSet_blockContent_decode_eq [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (s : Fin k) (dec : List (Fin k) → κ) (j : κ) :
    MeasurableSet {w : ℤ → Fin k | dec (blockContent s w) = j} := by
  have hdecomp : {w : ℤ → Fin k | dec (blockContent s w) = j} =
      ⋃ b : ℤ, ⋃ L : ℕ, ⋃ l ∈ {l : List (Fin k) | dec l = j},
        ({w | blockStart s w = b} ∩ {w | blockLen s w = L} ∩ {w | window w b L = l}) := by
    ext w
    simp only [blockContent, mem_setOf_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro h
      exact ⟨blockStart s w, blockLen s w, window w (blockStart s w) (blockLen s w),
        h, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨b, L, l, hgl, ⟨hb, hL⟩, hwin⟩
      rw [hb, hL, hwin]; exact hgl
  rw [hdecomp]
  refine MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun L => ?_))
  refine MeasurableSet.biUnion (Set.to_countable _) (fun l _ => ?_)
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) (measurableSet_window_eq b L l)
  · exact measurableSet_blockStart_eq s b
  · exact measurableSet_blockLen_eq s L

/-- **The bi-infinite sentinel parser is measurable.** This is the headline of the file and the
discharge of point (3) of the `Recovery` module note (the residual with "no Mathlib analogue"). The
codomain `κ` is `Countable` with `MeasurableSingletonClass`, so `measurable_to_countable'` reduces
measurability to the measurability of each preimage `{w | sentinelParse s dec w = j}` — supplied by
`measurableSet_blockContent_decode_eq`. **No new symbolic-dynamics infrastructure is needed.** -/
theorem measurable_sentinelParse [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (s : Fin k) (dec : List (Fin k) → κ) :
    Measurable (sentinelParse s dec) := by
  refine measurable_to_countable' (fun j => ?_)
  exact measurableSet_blockContent_decode_eq s dec j

/-! ### Why a naive sentinel-column coding scheme is unsatisfiable (a documented trap)

A tempting "sharpened residual" would bundle a measurable code symbol `c : α → Fin k` with an a.e.
recovery field of the form `Q j =ᵐ[μ] {x | sentinelParse s decode (itin e code x) = j}`, reusing
the constructed measurable parser `sentinelParse` as the decoder. **This scheme is unsatisfiable
for a generic countable generator `Q`.** The parser `sentinelParse s dec w` decodes only the
*content* of the sentinel block around coordinate `0`, hence is *position-blind*. The two-sided
itinerary intertwines `e` with the one-step shift (`itin_apply_e`), and `sentinelParse` is
invariant under that shift inside a block, so it returns the **same** label at `x` and at `e x`
whenever both sit in one tower column — while distinct floors of a column lie in genuinely
different `Q`-cells. Hence no `decode` makes the parser event agree a.e. with `Q j`. This
obstruction is formalized in `Oseledets.Krieger.parse_event_cannot_separate` (`TowerCode.lean`).
The honest column-code residual instead carries the within-block offset: the position-aware
parser `sentinelParseAt` and bundle `SentinelColumnCodeAt` (`TowerCode.lean`), whose recovery
field *is* satisfiable. -/

end Oseledets.Krieger
