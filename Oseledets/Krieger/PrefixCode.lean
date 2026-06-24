/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Infix
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The sentinel prefix-code counting lemma for Krieger's finite generator theorem (M2→C3)

This file proves the **self-contained combinatorial heart** of the symbolic-coding step (C3) of
Krieger's finite generator theorem (issue #15): the *sentinel code*. The classical Krieger
construction (Downarowicz, *Entropy in Dynamical Systems*, §4.2 Lemma 4.2.5 / Exercise 3.8; Shields,
*The Ergodic Theory of Discrete Sample Paths*, on strongly-separated codes; Lind–Marcus, *Symbolic
Dynamics and Coding*, on prefix codes) needs to inject the (`≤ kᴺ`) `N`-names of a generator into
short blocks over a small `Fin l` alphabet, **so that a decoder reading the raw code stream can
re-find the cutting points between successive blocks**. The standard device is a *sentinel*: a fixed
symbol `s : Fin l` reserved as a terminator and used **nowhere else** inside a block. Then in any
concatenation of such blocks the sentinel marks exactly the block boundaries, so the stream is
uniquely decodable.

We formalize the construction in its sharpest, most reusable form, decoupled from any dynamics:

* **The code map** `sentinelEncode emb s` sends a data word `d : List (Fin (l - 1))` (the "name"
  digits) to the block `d.map emb ++ [s]`, where `emb : Fin (l - 1) ↪ {a : Fin l // a ≠ s}` is any
  embedding of the data alphabet into the *non-sentinel* letters. The block has length `|d| + 1` and
  ends in the sentinel.

* **Counting / injection.** `sentinelEncode` is injective (`sentinelEncode_injective`), and its
  fixed-length variant `sentinelEncodeFn` (`sentinelEncodeFn_injective`) embeds the length-`m` data
  words `Fin m → Fin (l-1)` into the length-`(m+1)` sentinel blocks; there are `(l-1)ᵐ` of them
  (`card_dataWord`, `card_nonSentinel`). Hence any name set of size `≤ (l-1)ᵐ` injects into the
  blocks (`exists_sentinelEncoding`), with a **log-count bound** `kᴺ ≤ (l-1)ᵐ ⇔
  N·log k ≤ m·log(l-1)` (`pow_le_pow_iff_log`) — i.e. blocks of length `m + 1 = O(N)` suffice
  whenever `log k < log(l-1)`.

* **Decodability (prefix-free / comma-free).** The defining structural property: a `sentinelEncode`
  block contains the sentinel **only at its last position** (`sentinel_count_eq_one`,
  `notMem_sentinelData`). Hence in a concatenation of blocks (`sentinelEncodeList`) the sentinels
  are exactly the block ends, and the decoder recovers the block decomposition by splitting at the
  sentinels (`sentinelEncodeList_injective`, the unique-decodability statement C3 consumes).

## The interface C3 consumes

The deliverable for the next wave is `exists_sentinelEncoding`: for an alphabet `Fin l` with a
reserved sentinel `s` and any finite name set `Name`, if `Fintype.card Name` fits
in `(l-1)ᵐ` (in particular whenever `Name = Fin k`-names of length `N`, `card Name ≤ kᴺ`, and
`N · log k ≤ m · log(l-1)`, the `pow_le_pow_iff_log` regime that needs two free symbols plus a
sentinel, `2 ≤ l - 1`), there is an injection `enc : Name ↪ List (Fin l)` whose images are
length-`(m+1)` sentinel blocks (each with `count s = 1`) and whose *concatenations* are uniquely
decodable (`sentinelEncodeList_injective`): distinct name-streams give distinct code-streams. This
is exactly the symbolic code the column-coding partition is read off from.

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5) and
  Exercise 3.8 (the sentinel/marker coding of names).
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9
  (strongly-separated / marker codes).
* Douglas Lind and Brian Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge
  (1995), §8 (prefix codes, unique decodability).
-/

open Function

namespace Oseledets.Krieger

variable {l : ℕ}

/-! ### The data alphabet: non-sentinel letters of `Fin l` -/

/-- The **non-sentinel sub-alphabet**: the letters of `Fin l` other than the reserved sentinel `s`.
A `sentinelEncode` block uses only these for its data symbols, so the sentinel `s` can mark block
boundaries unambiguously. -/
abbrev NonSentinel (s : Fin l) : Type := {a : Fin l // a ≠ s}

/-- A data symbol (a non-sentinel letter) is, as a letter of `Fin l`, different from the
sentinel. -/
@[simp] lemma NonSentinel.ne_sentinel {s : Fin l} (a : NonSentinel s) : (a : Fin l) ≠ s := a.2

/-! ### The sentinel encoding of a single data word -/

/-- **The sentinel encoding of one data word.** Given an embedding `emb` of the data alphabet
`Fin (l - 1)` into the non-sentinel letters and the sentinel `s`, a data word
`d : List (Fin (l - 1))` is coded as `d.map (fun i => emb i) ++ [s]`: its letters mapped into the
non-sentinel alphabet, then terminated by the sentinel. The block has length `|d| + 1` and ends in
`s`, which occurs **nowhere else** in the block (`sentinel_count_eq_one`) — the prefix-free /
comma-free property that makes a concatenation of blocks uniquely decodable. -/
def sentinelEncode (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (d : List (Fin (l - 1))) : List (Fin l) :=
  d.map (fun i => (emb i : Fin l)) ++ [s]

@[simp] lemma sentinelEncode_length (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (d : List (Fin (l - 1))) : (sentinelEncode s emb d).length = d.length + 1 := by
  simp [sentinelEncode]

/-- The data part `d.map emb` of a `sentinelEncode` block contains **no** sentinel: every mapped
letter is a non-sentinel letter, hence `≠ s`. This is the structural core of decodability. -/
lemma notMem_sentinelData (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (d : List (Fin (l - 1))) : s ∉ d.map (fun i => (emb i : Fin l)) := by
  simp only [List.mem_map, not_exists, not_and]
  rintro i _ hi
  exact (emb i).2 hi

/-- **The sentinel occurs exactly once in a block: at the very end.** The data part contributes no
sentinel (`notMem_sentinelData`) and the trailing `[s]` contributes exactly one. Counting the
sentinel therefore yields `1` — the marker that a decoder uses to find the block boundary. -/
@[simp] lemma sentinel_count_eq_one (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (d : List (Fin (l - 1))) : (sentinelEncode s emb d).count s = 1 := by
  rw [sentinelEncode, List.count_append, List.count_singleton]
  simp [List.count_eq_zero.mpr (notMem_sentinelData s emb d)]

/-- **Injectivity of the single-word sentinel encoding.** The block `d.map emb ++ [s]` determines
the data word `d`: stripping the trailing sentinel recovers `d.map emb`, and `emb` is injective.
Hence distinct names map to distinct blocks — the injection C3 needs to faithfully receive names. -/
theorem sentinelEncode_injective (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s) :
    Function.Injective (sentinelEncode s emb) := by
  intro d₁ d₂ h
  rw [sentinelEncode, sentinelEncode] at h
  have hmap : d₁.map (fun i => (emb i : Fin l)) = d₂.map (fun i => (emb i : Fin l)) :=
    List.append_cancel_right h
  have hemb : Function.Injective (fun i => (emb i : Fin l)) := by
    intro a b hab
    exact emb.injective (Subtype.ext hab)
  exact List.map_injective_iff.mpr hemb hmap

/-! ### Unique decodability of a concatenation of sentinel blocks -/

/-- **The sentinel encoding of a stream of data words.** A list of data words
`ds : List (List (Fin (l - 1)))` (a sequence of `N`-names) is coded by concatenating the individual
sentinel blocks: `(ds.map (sentinelEncode s emb)).flatten`. The decoder re-finds the cutting points
because the sentinel `s` occurs **only at the end of each block** (`sentinel_count_eq_one`), so the
code stream is uniquely decodable (`sentinelEncodeList_injective`). -/
def sentinelEncodeList (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (ds : List (List (Fin (l - 1)))) : List (Fin l) :=
  (ds.map (sentinelEncode s emb)).flatten

@[simp] lemma sentinelEncodeList_nil (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s) :
    sentinelEncodeList s emb [] = [] := rfl

@[simp] lemma sentinelEncodeList_cons (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (b : List (Fin (l - 1))) (ds : List (List (Fin (l - 1)))) :
    sentinelEncodeList s emb (b :: ds) =
      sentinelEncode s emb b ++ sentinelEncodeList s emb ds := by
  simp [sentinelEncodeList]

/-- **The decoder splits a block-prefixed stream at the first sentinel: the data part.** Reading a
stream `sentinelEncode b ++ tail` and taking the maximal prefix of non-sentinel letters recovers
exactly the data part `b.map emb` of the first block — because the data part has no sentinel and is
immediately followed by the terminating sentinel. -/
lemma takeWhile_sentinelEncode_append (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    (b : List (Fin (l - 1))) (tail : List (Fin l)) :
    (sentinelEncode s emb b ++ tail).takeWhile (fun a => decide (a ≠ s)) =
      b.map (fun i => (emb i : Fin l)) := by
  rw [sentinelEncode, List.append_assoc]
  rw [List.takeWhile_append_of_pos]
  · -- the trailing `[s] ++ tail` starts with the sentinel, so `takeWhile` stops immediately
    have : ([s] ++ tail).takeWhile (fun a => decide (a ≠ s)) = [] := by
      simp
    rw [this, List.append_nil]
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp [(emb i).2]

/-- **The decoder splits a block-prefixed stream at the first sentinel: the remaining stream.**
After the maximal non-sentinel prefix, dropping the terminating sentinel returns exactly the rest of
the stream `tail` — so the decoder can recurse on the remaining blocks. -/
lemma drop_sentinel_dropWhile_sentinelEncode_append (s : Fin l)
    (emb : Fin (l - 1) ↪ NonSentinel s) (b : List (Fin (l - 1))) (tail : List (Fin l)) :
    ((sentinelEncode s emb b ++ tail).dropWhile (fun a => decide (a ≠ s))).tail = tail := by
  rw [sentinelEncode, List.append_assoc]
  rw [List.dropWhile_append]
  have hdrop : (b.map (fun i => (emb i : Fin l))).dropWhile (fun a => decide (a ≠ s)) = [] := by
    rw [List.dropWhile_eq_nil_iff]
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp [(emb i).2]
  rw [if_pos (by rw [hdrop, List.isEmpty_nil])]
  -- `dropWhile` over `[s] ++ tail` drops the leading sentinel, leaving `s :: tail`, then `.tail`
  have : ([s] ++ tail).dropWhile (fun a => decide (a ≠ s)) = s :: tail := by
    simp
  rw [this, List.tail_cons]

/-- **Unique decodability of the sentinel code (the C3 deliverable).** The stream encoding
`sentinelEncodeList s emb` is **injective**: distinct sequences of names produce distinct code
streams. This is the prefix-free / comma-free property that lets a decoder reconstruct the sequence
of blocks — hence the sequence of names — from the raw `Fin l`-stream alone. The proof recurses: the
maximal non-sentinel prefix recovers the first block's data (`takeWhile_sentinelEncode_append`,
giving the first name by `sentinelEncode_injective`), and dropping it leaves the rest of the stream
(`drop_sentinel_dropWhile_sentinelEncode_append`) to recurse on. -/
theorem sentinelEncodeList_injective (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s) :
    Function.Injective (sentinelEncodeList s emb) := by
  intro ds₁
  induction ds₁ with
  | nil =>
    intro ds₂ h
    cases ds₂ with
    | nil => rfl
    | cons b₂ rest₂ =>
      rw [sentinelEncodeList_nil, sentinelEncodeList_cons] at h
      exfalso
      have : (sentinelEncode s emb b₂ ++ sentinelEncodeList s emb rest₂).length = 0 := by
        rw [← h]; rfl
      simp only [List.length_append, sentinelEncode_length] at this
      omega
  | cons b₁ rest₁ ih =>
    intro ds₂ h
    cases ds₂ with
    | nil =>
      rw [sentinelEncodeList_nil, sentinelEncodeList_cons] at h
      exfalso
      have : (sentinelEncode s emb b₁ ++ sentinelEncodeList s emb rest₁).length = 0 := by
        rw [h]; rfl
      simp only [List.length_append, sentinelEncode_length] at this
      omega
    | cons b₂ rest₂ =>
      rw [sentinelEncodeList_cons, sentinelEncodeList_cons] at h
      -- recover the first block via `takeWhile`
      have hb : b₁.map (fun i => (emb i : Fin l)) = b₂.map (fun i => (emb i : Fin l)) := by
        have h₁ := takeWhile_sentinelEncode_append s emb b₁ (sentinelEncodeList s emb rest₁)
        have h₂ := takeWhile_sentinelEncode_append s emb b₂ (sentinelEncodeList s emb rest₂)
        rw [h] at h₁
        rw [h₁] at h₂
        exact h₂
      have hb' : b₁ = b₂ := by
        have hemb : Function.Injective (fun i => (emb i : Fin l)) := fun a b hab =>
          emb.injective (Subtype.ext hab)
        exact List.map_injective_iff.mpr hemb hb
      -- recover the rest via `dropWhile`
      have hrest : sentinelEncodeList s emb rest₁ = sentinelEncodeList s emb rest₂ := by
        have h₁ := drop_sentinel_dropWhile_sentinelEncode_append s emb b₁
          (sentinelEncodeList s emb rest₁)
        have h₂ := drop_sentinel_dropWhile_sentinelEncode_append s emb b₂
          (sentinelEncodeList s emb rest₂)
        rw [h] at h₁
        rw [h₁] at h₂
        exact h₂
      rw [hb', ih hrest]

/-! ### Fixed-length names: the counting / injection layer

For the symbolic code C3 the names are fixed-length words `Fin m → Fin (l - 1)` (e.g. the `N`-name
of a generator as a function of the `N` coordinates). Each such name is encoded as one sentinel
block via `sentinelEncodeFn`. The crux is a *counting* statement: there are exactly `(l - 1)ᵐ`
fixed-length data words, so any name set of cardinality `≤ (l - 1)ᵐ` injects into the sentinel
blocks. -/

/-- **The non-sentinel sub-alphabet has `l - 1` letters.** Removing the single reserved sentinel `s`
from `Fin l` leaves `l - 1` data letters. This is the per-symbol capacity of the code; the available
length-`m` data words number `(l - 1)ᵐ` (`card_dataWord`). -/
@[simp] theorem card_nonSentinel (s : Fin l) : Fintype.card (NonSentinel s) = l - 1 := by
  have : Fintype.card (NonSentinel s) = Fintype.card (Fin l) - Fintype.card {a : Fin l // a = s} :=
    Fintype.card_subtype_compl (· = s)
  rw [this, Fintype.card_fin, Fintype.card_subtype_eq]

/-- **There are `(l - 1)ᵐ` fixed-length data words.** The length-`m` words over the non-sentinel
alphabet are the functions `Fin m → Fin (l - 1)`, of which there are `(l - 1)ᵐ`. This is the number
of distinct sentinel blocks of length `m + 1` available to the encoder — the supply of code words
that must injectively receive all names. -/
@[simp] theorem card_dataWord (m : ℕ) :
    Fintype.card (Fin m → Fin (l - 1)) = (l - 1) ^ m := by
  rw [Fintype.card_fun]
  simp

/-- **The fixed-length sentinel encoder.** A length-`m` name `f : Fin m → Fin (l - 1)` (a word over
the non-sentinel data alphabet) is coded as the single sentinel block `sentinelEncode s emb
(List.ofFn f)`: its `m` data letters mapped into the non-sentinel alphabet, then the terminating
sentinel. The resulting block has length `m + 1`. -/
def sentinelEncodeFn (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s) {m : ℕ}
    (f : Fin m → Fin (l - 1)) : List (Fin l) :=
  sentinelEncode s emb (List.ofFn f)

@[simp] lemma sentinelEncodeFn_length (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s) {m : ℕ}
    (f : Fin m → Fin (l - 1)) : (sentinelEncodeFn s emb f).length = m + 1 := by
  simp [sentinelEncodeFn]

/-- **Injectivity of the fixed-length encoder.** Distinct length-`m` names map to distinct blocks:
`sentinelEncode` is injective (`sentinelEncode_injective`) and `List.ofFn` is injective, so the
composite is. -/
theorem sentinelEncodeFn_injective (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s) {m : ℕ} :
    Function.Injective (sentinelEncodeFn s emb (m := m)) := by
  intro f g h
  have := sentinelEncode_injective s emb h
  exact List.ofFn_injective this

/-- **A canonical embedding of the data alphabet into the non-sentinel letters.** Since
`NonSentinel s` has exactly `l - 1` letters (`card_nonSentinel`), it is in bijection with
`Fin (l - 1)`; the inverse bijection is the embedding the encoder uses to place data symbols. (Any
embedding works for the structural results; this fixes a concrete one so the code is computable from
the data.) -/
noncomputable def dataEmbedding (s : Fin l) : Fin (l - 1) ↪ NonSentinel s :=
  (Fintype.equivFinOfCardEq (card_nonSentinel s)).symm.toEmbedding

/-- **The headline counting injection (the C3 deliverable).** For an alphabet `Fin l` with a
reserved sentinel `s` and any finite name set `Name` whose cardinality fits in the supply of
length-`m` data words, `Fintype.card Name ≤ (l - 1) ^ m`, there is an injection
`enc : Name ↪ List (Fin l)` of names into **sentinel blocks of length `m + 1`** — each block ends
in the sentinel and contains it nowhere else, so the family is prefix-free and concatenated blocks
are uniquely decodable (`sentinelEncodeList_injective`).

Concretely `enc` is the composite `Name ↪ (Fin m → Fin (l - 1))` (which exists because
`card Name ≤ (l - 1) ^ m = card (Fin m → Fin (l - 1))`, `card_dataWord`) followed by the injective
fixed-length encoder `sentinelEncodeFn` (`sentinelEncodeFn_injective`). This is exactly the symbolic
code the column-coding partition is read off from: when `Real.log k < Real.log (l - 1)` and
`m · Real.log (l - 1) ≥ N · Real.log k`, the `≤ kᴺ`-many `N`-names inject into blocks of length
`m + 1 = O(N)`. -/
theorem exists_sentinelEncoding {l : ℕ} {Name : Type*} [Fintype Name] {m : ℕ}
    (s : Fin l) (hcard : Fintype.card Name ≤ (l - 1) ^ m) :
    ∃ enc : Name ↪ List (Fin l),
      (∀ x, (enc x).length = m + 1) ∧
      (∀ x, (enc x).count s = 1) ∧
      Function.Injective enc := by
  -- choose any embedding of the data alphabet into the non-sentinel letters
  let emb : Fin (l - 1) ↪ NonSentinel s := dataEmbedding s
  -- the name set embeds into the fixed-length data words by the cardinality bound
  have hcard' : Fintype.card Name ≤ Fintype.card (Fin m → Fin (l - 1)) := by
    rw [card_dataWord]; exact hcard
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard'
  -- compose with the injective fixed-length encoder
  refine ⟨⟨fun x => sentinelEncodeFn s emb (g x),
      fun x y h => g.injective (sentinelEncodeFn_injective s emb h)⟩, ?_, ?_, ?_⟩
  · intro x; simp [sentinelEncodeFn_length]
  · intro x; simp [sentinelEncodeFn, sentinel_count_eq_one]
  · intro x y h
    exact g.injective (sentinelEncodeFn_injective s emb h)

/-! ### The logarithmic length bound: blocks of length `O(N)` suffice -/

/-- **The log-count bridge.** Over a non-sentinel alphabet of size `b := l - 1 ≥ 2`, a name set of
size `≤ kᴺ` fits in the length-`m` data words `(l - 1)ᵐ` **iff** `N · log k ≤ m · log (l - 1)` — the
information-theoretic length bound. In particular, picking `m ≥ N · log k / log (l - 1)` gives
blocks of length `m + 1 = O(N)` whenever `log k < log (l - 1)`; this is the regime
`Real.log k < Real.log (l - 1)` the Krieger threshold `log (alphabet) > h` supplies. The statement
is the clean real-logarithm reformulation of the integer inequality `kᴺ ≤ (l - 1)ᵐ`. -/
theorem pow_le_pow_iff_log {k N l m : ℕ} (hk : 0 < k) (hl : 1 < l - 1) :
    k ^ N ≤ (l - 1) ^ m ↔
      (N : ℝ) * Real.log (k : ℝ) ≤ (m : ℝ) * Real.log ((l - 1 : ℕ) : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbR : (0 : ℝ) < ((l - 1 : ℕ) : ℝ) := by positivity
  -- transport the integer inequality to the reals and back through `log` (strictly monotone on ℝ>0)
  have hcast : (k ^ N ≤ (l - 1) ^ m) ↔ ((k : ℝ) ^ N ≤ ((l - 1 : ℕ) : ℝ) ^ m) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_le]
  rw [hcast, ← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]

end Oseledets.Krieger
