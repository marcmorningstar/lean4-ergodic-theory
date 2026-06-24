/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.StageBuild

/-!
# The cross-stage interleaving of one fixed measurable code (C3, sub-problem B, closure)

`Oseledets.Krieger.StageBuild` reduced sub-problem B of the unconditional Krieger theorem to
producing a single `StageInput e μ Q k`: one fixed measurable `code : α → Fin k` that, on each
refining tower stage `m`'s event `T m`, agrees with that stage's concrete
`stageCode e (A m) (N m) (nm m) s (emb m)` — the hard fields being `code_floor` and `code_pred`.

This file performs the **cross-stage interleaving**: it builds a `StageInput` from one master code
`code`, discharging `code_floor`/`code_pred`/`decodes` by a coherence device that makes the
per-stage agreement **definitional**.

## The coherence device (Keane–Serafin nested refinement, made definitional)

The genuine crux (cf. `Oseledets.Krieger.RefTower`): summable misses `∑ₘ μ (T m)ᶜ < ∞`
force the `T m` to overlap heavily, and on `T m ∩ T m'` the fixed `code` equals both `stageCode_m`
and `stageCode_{m'}`, so the per-stage codes must be **consistent**. Keane–Serafin (*On the
countable generator theorem*, Fund. Math. **157** (1998), 255–259) resolve this by nesting the
towers so each stage's column code refines the previous one's; the one fixed `code` is the
coherent limit.

We package the **output** of that nesting as the hypothesis bundle `BracketedTowerSystem`: one
master `code` and a refining sequence of towers on which `code` is *self-bracketed* — interior
column floors carry non-sentinel symbols, every column top and every column-base predecessor carries
the escape symbol `s`. Then, crucially, defining each stage's name map `nm m` as the **read-off of
the master code along the column** (`weaveName`) makes `stageCode_m` agree with `code` on `T m`
**by construction**:

* `stageCode_m (eⁱ b) = (sentinelEncode s (emb m) (weaveName … b)).getD i s`, and for a
  self-bracketed column this `getD` is, at interior `i`, `emb (decode (code (eⁱ b)))`
  `= code (eⁱ b)`, the embedding `emb` being a *bijection* onto the non-sentinel letters, so it
  inverts the read-off; at the top `i = N m − 1` it is the terminator `s = code (e^{N m−1} b)`.

So `code_floor`/`code_pred` hold **definitionally** from self-bracketing — the cross-stage
consistency is absorbed into the single statement "`code` is self-bracketed on every stage", which
is exactly what the nested Keane–Serafin construction delivers (one code, bracketing every
refining column with `s`). This is the honest reduction: it turns the *several* per-stage
agreements into *one* self-bracketing property of *one* code.

## What is built here, sorry-free

* `embLetter` / `embLetterInv` — the data-letter map of the embedding and its `Function.invFun`
  inverse (a left inverse on the range), used to read off and re-encode the master code.
* `weaveName` / `weaveName_length` — the per-stage name map (the master code read off the column,
  inverted through `emb`) and its length.
* `getD_sentinelEncode_weaveName_interior` — the interior block read of the read-off name.
* `stageCode_weaveName_eq` — **the coherence lemma**: on a self-bracketed column, `stageCode` with
  `weaveName` equals the master `code`. This is what makes `code_floor` definitional.
* `BracketedTowerSystem` — the bundle: one master code, refining towers, the self-bracketing of
  `code` on every stage, summable misses, and the cell-index recovery.
* `BracketedTowerSystem.toStageInput` / `BracketedTowerSystem.codes` — assemble a full
  `StageInput` from a `BracketedTowerSystem`, discharging every field; hence
  `CodesTwoSidedMod0c` via `StageInput.codes`.

## The honest residual

`BracketedTowerSystem` isolates exactly the genuinely-dynamical content the nested construction must
deliver: one measurable code, self-bracketed on a refining sequence of towers with summable misses.
Its *existence* is the inductive symbolic-dynamics construction (nested bases `A (m+1) ⊆ A m`,
heights `N m ↑ ∞`, the escape symbol carrying the finest column's `Q`-name) — the
`≈ several-hundred-line` heart of Keane–Serafin. The reduction proved here is the
structural exit:
**self-bracketed master code ⟹ `StageInput` ⟹ `CodesTwoSidedMod0c`**, unconditionally and
sorry-free.

## References

* Michael S. Keane and Jacek Serafin, *On the countable generator theorem*, Fund. Math. **157**
  (1998), 255–259 (the inductive refining construction `εₖ = 2^{−(k+1)}`, marker symbol).
* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5): the
  refining-tower column-coding limit with a reserved marker.
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9.
-/

open MeasureTheory Function Set Filter
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The letter map of a data embedding and its inverse

For a data embedding `emb : Fin (k - 1) ↪ NonSentinel s`, write `embLetter emb j : Fin k` for the
non-sentinel letter `emb j` viewed in the full alphabet. The stage's name word reads the master
`code` off the column and inverts it through `embLetter`: the `i`-th data letter is
`Function.invFun (embLetter emb) (code (eⁱ b))`. On a self-bracketed column the interior
letters are non-sentinels in the range of `emb`, so `embLetter` inverts them exactly. -/

/-- The letter map of a data embedding: `emb j` viewed as a letter of the full alphabet `Fin k`. It
is injective (`emb` is, and the subtype coercion is). -/
def embLetter {s : Fin k} (emb : Fin (k - 1) ↪ NonSentinel s) (j : Fin (k - 1)) : Fin k :=
  (emb j : Fin k)

lemma embLetter_injective {s : Fin k} (emb : Fin (k - 1) ↪ NonSentinel s) :
    Function.Injective (embLetter emb) := by
  intro a b hab
  exact emb.injective (Subtype.ext hab)

lemma embLetter_ne_sentinel {s : Fin k} (emb : Fin (k - 1) ↪ NonSentinel s) (j : Fin (k - 1)) :
    embLetter emb j ≠ s := (emb j).2

/-- The inverse of the letter map (`Function.invFun`). On the range of `embLetter` it recovers the
data symbol; this is a left/right inverse where applicable
(`embLetter_embLetterInv_of_mem_range`). Needs `Nonempty (Fin (k - 1))` (i.e. `2 ≤ k`, a genuine
requirement: the alphabet must carry a sentinel plus at least one data letter) for the junk default
of `Function.invFun`. -/
noncomputable def embLetterInv [Nonempty (Fin (k - 1))] {s : Fin k}
    (emb : Fin (k - 1) ↪ NonSentinel s) (a : Fin k) : Fin (k - 1) :=
  Function.invFun (embLetter emb) a

/-- On the range of `embLetter`, `embLetter ∘ embLetterInv` is the identity: if
`a = embLetter emb j`
for some `j`, then `embLetter emb (embLetterInv emb a) = a`. -/
lemma embLetter_embLetterInv_of_mem_range [Nonempty (Fin (k - 1))] {s : Fin k}
    (emb : Fin (k - 1) ↪ NonSentinel s) {a : Fin k} (ha : a ∈ Set.range (embLetter emb)) :
    embLetter emb (embLetterInv emb a) = a :=
  Function.invFun_eq ha

/-! ### The read-off name map of the master code -/

/-- **The read-off name map.** For tower `(A, N)` and master code `code`, the name word of a base
point `b` reads `code` off the first `N - 1` interior floors of the column over `b`, inverting each
letter through `embLetter`: `weaveName … b = List.ofFn (fun i : Fin (N - 1) ↦ embLetterInv emb
(code (eⁱ b)))`. On a self-bracketed column (interior letters non-sentinel and in the range of
`emb`), encoding this word reproduces `code` along the column — the definitional coherence. -/
noncomputable def weaveName [Nonempty (Fin (k - 1))] (e : α ≃ᵐ α) (_A : Set α) (N : ℕ)
    (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s) (code : α → Fin k) (b : α) :
    List (Fin (k - 1)) :=
  List.ofFn (fun i : Fin (N - 1) => embLetterInv emb (code ((e : α → α)^[(i : ℕ)] b)))

@[simp] lemma weaveName_length [Nonempty (Fin (k - 1))] (e : α ≃ᵐ α) (A : Set α) (N : ℕ)
    (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s) (code : α → Fin k) (b : α) :
    (weaveName e A N s emb code b).length = N - 1 := by
  simp [weaveName]

/-- **The interior block read of a read-off name.** For `i < N - 1`, the `i`-th letter of the
sentinel encoding of `weaveName … b` is `embLetter emb (embLetterInv emb (code (eⁱ b)))` —
the master
code at floor `i`, inverted then re-embedded. On a self-bracketed column this round-trips to
`code (eⁱ b)` (`embLetter_embLetterInv_of_mem_range`); the round-trip is isolated here. -/
lemma getD_sentinelEncode_weaveName_interior [Nonempty (Fin (k - 1))]
    (e : α ≃ᵐ α) (A : Set α) (N : ℕ) (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s)
    (code : α → Fin k) (b : α) {i : ℕ} (hi : i < N - 1) :
    (sentinelEncode s emb (weaveName e A N s emb code b)).getD i s
      = embLetter emb (embLetterInv emb (code ((e : α → α)^[i] b))) := by
  classical
  have hdlen : (weaveName e A N s emb code b).length = N - 1 := weaveName_length _ _ _ _ _ _ _
  have hmaplen :
      ((weaveName e A N s emb code b).map (fun j => (emb j : Fin k))).length = N - 1 := by
    simp [hdlen]
  have hidx : i < (sentinelEncode s emb (weaveName e A N s emb code b)).length := by
    rw [sentinelEncode_length, hdlen]; omega
  rw [List.getD_eq_getElem _ _ hidx]
  simp only [sentinelEncode]
  rw [List.getElem_append, dif_pos (by rw [hmaplen]; exact hi)]
  -- read the `i`-th letter of the mapped read-off word: `embLetter` of the `ofFn` entry
  simp only [weaveName, List.getElem_map, List.getElem_ofFn, embLetter]

/-! ### The coherence lemma: `stageCode` of the read-off name equals the master code

The heart of the file. On a *self-bracketed* column over `b` — interior floors carry non-sentinel
letters in the range of `emb`, and the top floor `N - 1` carries the sentinel `s` — the stage code
`stageCode … (weaveName …)` evaluated at any column floor `i < N` equals the master `code` at
that floor. The interior floors invert through `embLetter` (range membership ⟹
`embLetter ∘ embLetterInv = id`); the top floor reads the terminating sentinel `s`, which the
self-bracketing equates to `code`. This makes `StageInput.code_floor` definitional. -/

/-- **The coherence lemma.** Let `b ∈ towerBase e A N`, and suppose `code` is *self-bracketed* on
the column over `b`: every interior floor letter `code (eⁱ b)` (`i < N - 1`) lies in the range of
`embLetter emb`, and the top floor satisfies `code (e^{N-1} b) = s`. Then for every floor `i < N`,
`stageCode e A N (weaveName e A N s emb code) s emb (eⁱ b) = code (eⁱ b)`. -/
lemma stageCode_weaveName_eq [Nonempty (Fin (k - 1))]
    (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N) (s : Fin k)
    (emb : Fin (k - 1) ↪ NonSentinel s) (code : α → Fin k) {b : α}
    (hb : b ∈ towerBase e A N)
    (hinterior : ∀ i : ℕ, i < N - 1 →
      code ((e : α → α)^[i] b) ∈ Set.range (embLetter emb))
    (htop : code ((e : α → α)^[N - 1] b) = s)
    {i : ℕ} (hi : i < N) :
    stageCode e A N (weaveName e A N s emb code) s emb ((e : α → α)^[i] b)
      = code ((e : α → α)^[i] b) := by
  classical
  -- reduce the stage code at floor `i` to the block read of the read-off name
  rw [stageCode_iterate_base e A hN (weaveName e A N s emb code) s emb hi hb]
  have hdlen : (weaveName e A N s emb code b).length = N - 1 := weaveName_length _ _ _ _ _ _ _
  rcases lt_or_ge i (N - 1) with hint | htopge
  · -- interior floor: the block letter round-trips `code (eⁱ b)` through `embLetter`
    rw [getD_sentinelEncode_weaveName_interior e A N s emb code b hint]
    -- `embLetter emb (embLetterInv emb (code (eⁱ b))) = code (eⁱ b)` by range membership
    exact embLetter_embLetterInv_of_mem_range emb (hinterior i hint)
  · -- top floor `i = N - 1`: the block read is the terminating sentinel, equal to `code` by `htop`
    have hiN1 : i = N - 1 := by omega
    rw [hiN1, getD_sentinelEncode_terminator s emb hdlen, htop]

/-! ### The bracketed refining-tower system and the `StageInput` it produces

The genuinely-dynamical output of the Keane–Serafin nested construction, isolated as a hypothesis
bundle: one master measurable `code`, a refining sequence of towers `(A m, N m)` on whose columns
`code` is *self-bracketed*, with summable misses and a cell-index recovery. Self-bracketing —
interior floors non-sentinel/in range, every column top and base predecessor carrying `s` — is
exactly the property the escape symbol of the nested construction guarantees. From it the
`StageInput` fields `code_floor`/`code_pred` are **definitional**
(`stageCode_weaveName_eq` / `stageCode_predecessor`). -/

/-- **The bracketed refining-tower system** (the Keane–Serafin nested-construction output). One
master code self-bracketed on a refining sequence of towers. The shared embedding `emb` is fixed
across stages (the cross-stage coherence is carried by self-bracketing of the single `code`, not by
varying `emb`). -/
structure BracketedTowerSystem (e : α ≃ᵐ α) (μ : Measure α) (Q : κ → Set α) (k : ℕ)
    [Nonempty (Fin (k - 1))] where
  /-- The shared reserved sentinel. -/
  s : Fin k
  /-- The one fixed measurable master code. -/
  code : α → Fin k
  /-- The master code is measurable. -/
  code_measurable : Measurable code
  /-- The shared data embedding (fixed across stages). -/
  emb : Fin (k - 1) ↪ NonSentinel s
  /-- The shared position-aware decoder. -/
  decode : List (Fin k) → ℕ → κ
  /-- The shared measurable cell index. -/
  cellIndex : α → κ
  /-- The cell index recovers each cell of `Q` mod 0. -/
  cellIndex_recovers : ∀ j, Q j =ᵐ[μ] {x | cellIndex x = j}
  /-- The per-stage tower base sets, with each base measurable. -/
  A : ℕ → Set α
  /-- Each base is measurable. -/
  A_measurable : ∀ m, MeasurableSet (A m)
  /-- The per-stage tower heights. -/
  N : ℕ → ℕ
  /-- Each tower height is positive. -/
  hN : ∀ m, 1 ≤ N m
  /-- The stage events `T m`. -/
  T : ℕ → Set α
  /-- Each stage event lies in its tower's covered set. -/
  cover : ∀ m, T m ⊆ coveredSet e (A m) (N m)
  /-- **Self-bracketing, interior.** On `T m`, every interior column floor carries a non-sentinel
  letter in the range of `emb` (so the read-off name inverts to the master code). -/
  interior : ∀ m, ∀ x ∈ T m, ∀ i : ℕ, i < N m - 1 →
    code ((e : α → α)^[i] (columnBase e (A m) (N m) x)) ∈ Set.range (embLetter emb)
  /-- **Self-bracketing, top.** On `T m`, every column top floor `N m − 1` carries the
  sentinel. -/
  top : ∀ m, ∀ x ∈ T m,
    code ((e : α → α)^[N m - 1] (columnBase e (A m) (N m) x)) = s
  /-- **Self-bracketing, predecessor.** On `T m`, every column-base predecessor carries the
  sentinel. -/
  pred : ∀ m, ∀ x ∈ T m,
    code ((e.symm : α → α) (columnBase e (A m) (N m) x)) = s
  /-- Decoding stage `m`'s read-off block at the floor offset recovers the cell index. -/
  decodes : ∀ m, ∀ x ∈ T m,
    decode (sentinelEncode s emb (weaveName e (A m) (N m) s emb code (columnBase e (A m) (N m) x)))
      (floorAddr e (A m) (N m) x) = cellIndex x
  /-- The stage misses are summable. -/
  misses_summable : (∑' m, μ (T m)ᶜ) ≠ ∞

/-- **The `StageInput` from a `BracketedTowerSystem`.** Every field is discharged: the name maps are
the read-off `weaveName`, `code_floor` is the coherence lemma `stageCode_weaveName_eq` (using the
self-bracketing `interior`/`top`), and `code_pred` is `stageCode_predecessor` reconciled with the
master code via the self-bracketing `pred`. This is the cross-stage interleaving, made definitional:
one master code, self-bracketed on every refining tower, serves all stages. -/
noncomputable def BracketedTowerSystem.toStageInput [Nonempty (Fin (k - 1))] {e : α ≃ᵐ α}
    {Q : κ → Set α} (B : BracketedTowerSystem e μ Q k) : StageInput e μ Q k where
  s := B.s
  code := B.code
  code_measurable := B.code_measurable
  decode := B.decode
  cellIndex := B.cellIndex
  cellIndex_recovers := B.cellIndex_recovers
  A := B.A
  N := B.N
  hN := B.hN
  nm := fun m => weaveName e (B.A m) (B.N m) B.s B.emb B.code
  nm_len := fun m y => weaveName_length _ _ _ _ _ _ _
  emb := fun _ => B.emb
  T := B.T
  cover := B.cover
  code_floor := by
    intro m x hx i hi
    -- `columnBase x ∈ towerBase`, then apply the coherence lemma at this floor
    have hbase : columnBase e (B.A m) (B.N m) x ∈ towerBase e (B.A m) (B.N m) := by
      have hcov := B.cover m hx
      rw [coveredSet, Set.mem_iUnion] at hcov
      obtain ⟨j, hj⟩ := hcov
      have hxl : x ∈ level e (B.A m) (B.N m) (j : ℕ) := hj
      have hfa : floorAddr e (B.A m) (B.N m) x = (j : ℕ) := by
        have : x ∈ {y | floorAddr e (B.A m) (B.N m) y = (j : ℕ)} := by
          rw [floorAddr_eq_level e (B.A m) (B.hN m) j.isLt]; exact hxl
        simpa using this
      obtain ⟨b, hb, hbx⟩ := hxl
      have hcbeq : columnBase e (B.A m) (B.N m) x = b := by
        rw [columnBase, hfa, ← hbx, Function.LeftInverse.iterate e.symm_apply_apply]
      rw [hcbeq]; exact hb
    rw [stageCode_weaveName_eq e (B.A m) (B.hN m) B.s B.emb B.code hbase
      (fun i hi => B.interior m x hx i hi) (B.top m x hx) hi]
  code_pred := by
    intro m x hx
    -- `stageCode_predecessor` gives `stageCode (e.symm cb) = s`; `pred` gives
    -- `code (e.symm cb) = s`
    have hbase : columnBase e (B.A m) (B.N m) x ∈ towerBase e (B.A m) (B.N m) := by
      have hcov := B.cover m hx
      rw [coveredSet, Set.mem_iUnion] at hcov
      obtain ⟨j, hj⟩ := hcov
      have hxl : x ∈ level e (B.A m) (B.N m) (j : ℕ) := hj
      have hfa : floorAddr e (B.A m) (B.N m) x = (j : ℕ) := by
        have : x ∈ {y | floorAddr e (B.A m) (B.N m) y = (j : ℕ)} := by
          rw [floorAddr_eq_level e (B.A m) (B.hN m) j.isLt]; exact hxl
        simpa using this
      obtain ⟨b, hb, hbx⟩ := hxl
      have hcbeq : columnBase e (B.A m) (B.N m) x = b := by
        rw [columnBase, hfa, ← hbx, Function.LeftInverse.iterate e.symm_apply_apply]
      rw [hcbeq]; exact hb
    rw [B.pred m x hx, stageCode_predecessor e (B.A m) (B.hN m)
      (weaveName e (B.A m) (B.N m) B.s B.emb B.code)
      (fun y => weaveName_length _ _ _ _ _ _ _) B.s B.emb hbase]
  decodes := B.decodes
  misses_summable := B.misses_summable

/-- **Sub-problem B closed from a bracketed refining-tower system.** A
`BracketedTowerSystem` — one
master measurable `code`, self-bracketed on a refining sequence of towers with summable misses —
yields, via `StageInput.codes`, the cross-layer countable mod-0 code `CodesTwoSidedMod0c e Q (…)`,
the deliverable that slots into `Oseledets.Krieger.KriegerCodingData.code_codes`. The
entire residual
is now the *existence* of a `BracketedTowerSystem`, i.e. the Keane–Serafin nested
construction of one
self-bracketed code. -/
theorem BracketedTowerSystem.codes [Nonempty (Fin (k - 1))]
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (B : BracketedTowerSystem e μ Q k) :
    letI D := B.toStageInput
    letI data := RefiningTowerCode.ofStages D.s D.code D.code_measurable D.decode D.cellIndex
      D.cellIndex_recovers D.T D.misses_summable (fun m => D.toStageCode e m)
    CodesTwoSidedMod0c e Q
      (codePartition (μ := μ) data.toColumnLayoutData.code
        data.toColumnLayoutData.code_measurable) :=
  B.toStageInput.codes

end Oseledets.Krieger
