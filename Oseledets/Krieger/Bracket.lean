/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.Weave

/-!
# The aligned-marker construction of a `BracketedTowerSystem` (C3, sub-problem B, closure)

`Oseledets.Krieger.Weave` reduced sub-problem B of the unconditional Krieger theorem to producing a
single `BracketedTowerSystem e μ Q k`: one fixed measurable master `code : α → Fin k`,
*self-bracketed* on a refining sequence of Rokhlin towers with summable misses. The three genuinely
hard fields are the self-bracketing conditions on the **single** `code`, simultaneously across the
nested stages:

* `interior m`: every interior column floor of stage `m` carries a non-sentinel data letter;
* `top m`: every column top of stage `m` carries the sentinel `s`;
* `pred m`: every column-base predecessor of stage `m` carries `s`.

The crux (Keane–Serafin's nested alignment): a single point can be an *interior* floor of one stage
and a *marker* (top / predecessor) of another, and then `interior` and `top`/`pred` would demand
both `code ≠ s` and `code = s` at that point — a contradiction. The nesting eliminates this by
**aligning the markers**: there is a single *marker set* `M ⊆ α` such that, for every stage `m`,
the column tops and base-predecessors of stage `m` all lie in `M`, while every interior floor of
every stage lies outside `M`. With such a coherent `M` the conflict is structurally excluded, and
the master code is the **piecewise** map

`code x = if x ∈ M then s else embLetter emb (dataLetter x)` ,

placing the sentinel exactly on the marker set and a data letter off it.

## What is built here, sorry-free

This file isolates that coherent marker set as a clean hypothesis bundle — the **aligned-tower
castle** `AlignedTowerCastle` — and discharges, *unconditionally and sorry-free*, the entire
symbolic/measurable machinery that turns it into a `BracketedTowerSystem` (hence
`CodesTwoSidedMod0c`):

* `markerCode` — the piecewise master code (`s` on `M`, a data letter off `M`) and
  `measurable_markerCode` — its measurability (`Measurable.piecewise` over the measurable `M`).
* `markerCode_mem` / `markerCode_notMem` — the two definitional reads of the piecewise code.
* `AlignedTowerCastle` — the hypothesis bundle: a refining tower sequence `(A m, N m, T m)`, one
  measurable marker set `M` with the alignment facts (`marker_top`, `marker_pred`,
  `interior_notMarker`), summable misses, and the cell-index recovery / decode fields.
* `AlignedTowerCastle.toBracketedTowerSystem` — assembles the `BracketedTowerSystem`, discharging
  `interior`/`top`/`pred` from the alignment via the piecewise reads.
* `AlignedTowerCastle.codes` — sub-problem B's `CodesTwoSidedMod0c`, via
  `BracketedTowerSystem.codes`.

## The honest residual (the adversarial verdict)

The reduction proved here is the **structural exit**: a coherent aligned marker set ⟹ a self-
bracketed master code ⟹ `BracketedTowerSystem` ⟹ `CodesTwoSidedMod0c`. What `AlignedTowerCastle`
*carries* as the field `marker_top` ∧ `marker_pred` ∧ `interior_notMarker` is **exactly** the
genuinely-dynamical content the construction must deliver and which the repository's
`Oseledets.Krieger.rokhlin_tower` API does **not** supply: a single measurable set `M` that is the
top/predecessor marker for *every* refining stage while avoiding *every* stage's interior — i.e. the
**Kakutani–Rokhlin castle** in which each column of tower `m+1` is a concatenation of whole
tower-`m` columns plus a marked remainder, so that the tower tops nest (`N_{m+1}` a multiple-plus of
`N_m`).

`rokhlin_tower` produces, for each height `N`, an **independent** complete-block tower `towerBase
e A N` over a fresh small base `A`; its column tops sit at arbitrary positions inside the orbit and
are **not** aligned across distinct heights `N`. Consequently the marker set "column tops of tower
`m`" is, in general, an interior floor of tower `m'`, exactly the conflict the alignment is meant to
exclude. Building `M` therefore needs a genuine **nested castle refinement** (stack whole tower-`m`
columns to form tower `m+1`), for which Mathlib has **no analogue** and the repository has no lemma
(verified: no `nest`/`castle`/`stack`/aligned-tower construction exists in `Oseledets/Krieger/`).
This is the precise, non-fakeable dynamical residual of sub-problem B; `AlignedTowerCastle` is the
faithful hypothesis boundary, sharper than `BracketedTowerSystem` in that the *single* carried datum
is the coherent geometric marker set `M`, with all symbolic coding discharged here.

## References

* Michael S. Keane and Jacek Serafin, *On the countable generator theorem*, Fund. Math. **157**
  (1998), 255–259 (the inductive refining construction `εₖ = 2^{−(k+1)}`, the reserved marker
  symbol, and the nesting that aligns the markers across stages).
* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5): the
  refining-tower column-coding limit with a reserved marker.
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9.
-/

open MeasureTheory Function Set Filter
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The piecewise master code on a marker set

Given a measurable **marker set** `M ⊆ α` (the coherent column-top / predecessor set of the nested
castle), a sentinel `s : Fin k`, a data embedding `emb`, and a measurable **data-letter map**
`dataLetter : α → Fin (k - 1)`, the master code places the sentinel `s` exactly on `M` and the
embedded data letter off `M`. The two reads `markerCode_mem` / `markerCode_notMem` are the only
facts the self-bracketing proofs consume. -/

open Classical in
/-- **The piecewise master code.** On the marker set `M` it is the reserved sentinel `s`; off `M` it
is the embedded data letter `embLetter emb (dataLetter x)` (a non-sentinel letter, in the range of
`embLetter emb`). This is the `code = s` ⇔ marker placement that makes the column tops and base
predecessors carry `s` while interior floors carry data.

Decidability of membership in `M` is supplied *classically* (`Classical.propDecidable`) so the code
needs no `DecidablePred` instance to be carried alongside `M`; the piecewise *value* is independent
of the decidability instance, so this is harmless. The classical instance is supplied by
`open Classical in` on this definition. -/
noncomputable def markerCode {s : Fin k}
    (M : Set α) (emb : Fin (k - 1) ↪ NonSentinel s)
    (dataLetter : α → Fin (k - 1)) (x : α) :
    Fin k :=
  M.piecewise (fun _ => s) (fun x => embLetter emb (dataLetter x)) x

omit mα in
/-- On the marker set the master code is the sentinel `s`. -/
lemma markerCode_mem {s : Fin k} {M : Set α}
    {emb : Fin (k - 1) ↪ NonSentinel s} {dataLetter : α → Fin (k - 1)} {x : α} (hx : x ∈ M) :
    markerCode M emb dataLetter x = s := by
  classical
  exact Set.piecewise_eq_of_mem M (fun _ => s) (fun x => embLetter emb (dataLetter x)) hx

omit mα in
/-- Off the marker set the master code is the embedded data letter, hence in the range of
`embLetter emb` (a non-sentinel letter). -/
lemma markerCode_notMem {s : Fin k} {M : Set α}
    {emb : Fin (k - 1) ↪ NonSentinel s} {dataLetter : α → Fin (k - 1)} {x : α} (hx : x ∉ M) :
    markerCode M emb dataLetter x = embLetter emb (dataLetter x) := by
  classical
  exact Set.piecewise_eq_of_notMem M (fun _ => s) (fun x => embLetter emb (dataLetter x)) hx

omit mα in
/-- Off the marker set the master code lies in the range of `embLetter emb`. -/
lemma markerCode_mem_range_of_notMem {s : Fin k} {M : Set α}
    {emb : Fin (k - 1) ↪ NonSentinel s} {dataLetter : α → Fin (k - 1)} {x : α} (hx : x ∉ M) :
    markerCode M emb dataLetter x ∈ Set.range (embLetter emb) := by
  rw [markerCode_notMem hx]; exact ⟨dataLetter x, rfl⟩

/-- **The piecewise master code is measurable.** It is `Measurable.piecewise` over the measurable
marker set `M`, gluing the constant `s` (on `M`) with the measurable `embLetter emb ∘ dataLetter`
(off `M`). -/
theorem measurable_markerCode {s : Fin k} {M : Set α}
    (hM : MeasurableSet M) (emb : Fin (k - 1) ↪ NonSentinel s) {dataLetter : α → Fin (k - 1)}
    (hdata : Measurable dataLetter) :
    Measurable (markerCode M emb dataLetter) := by
  classical
  have hemb : Measurable (embLetter emb) := measurable_from_top
  exact Measurable.piecewise hM measurable_const (hemb.comp hdata)

/-! ### The aligned-tower castle

The genuinely-dynamical output of the Keane–Serafin nested construction, isolated as a hypothesis
bundle that is *sharper* than `BracketedTowerSystem`: a refining sequence of Rokhlin towers
`(A m, N m, T m)` together with **one measurable marker set `M`** whose alignment facts force every
column top and every column-base predecessor of every stage into `M`, and every interior floor of
every stage out of `M`. From these three alignment facts the self-bracketing of the piecewise master
code `markerCode M emb dataLetter` is purely definitional (`markerCode_mem` / `markerCode_notMem`).
The remaining fields (`decodes`, cell-index recovery, summable misses) are carried verbatim. -/

/-- **The aligned-tower castle** (the Keane–Serafin nested-construction output, marker-set form).
The single carried geometric datum is the coherent measurable marker set `M`; everything else is
bookkeeping shared with `BracketedTowerSystem`. -/
structure AlignedTowerCastle (e : α ≃ᵐ α) (μ : Measure α) (Q : κ → Set α) (k : ℕ)
    [Nonempty (Fin (k - 1))] where
  /-- The shared reserved sentinel. -/
  s : Fin k
  /-- The shared data embedding (fixed across stages). -/
  emb : Fin (k - 1) ↪ NonSentinel s
  /-- The measurable data-letter map (read off `Q` along the column). -/
  dataLetter : α → Fin (k - 1)
  /-- The data-letter map is measurable. -/
  dataLetter_measurable : Measurable dataLetter
  /-- **The coherent marker set** — the aligned column-top / predecessor set of the nested castle.
  This is the single genuinely-dynamical datum the construction must deliver. -/
  M : Set α
  /-- The marker set is measurable. -/
  M_measurable : MeasurableSet M
  /-- The shared position-aware decoder. -/
  decode : List (Fin k) → ℕ → κ
  /-- The shared measurable cell index. -/
  cellIndex : α → κ
  /-- The cell index recovers each cell of `Q` mod 0. -/
  cellIndex_recovers : ∀ j, Q j =ᵐ[μ] {x | cellIndex x = j}
  /-- The per-stage tower base sets. -/
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
  /-- **Alignment, interior.** On `T m`, every interior column floor lies *outside* the marker set
  (so the master code reads a data letter there). -/
  interior_notMarker : ∀ m, ∀ x ∈ T m, ∀ i : ℕ, i < N m - 1 →
    (e : α → α)^[i] (columnBase e (A m) (N m) x) ∉ M
  /-- **Alignment, top.** On `T m`, every column top lies *in* the marker set. -/
  marker_top : ∀ m, ∀ x ∈ T m,
    (e : α → α)^[N m - 1] (columnBase e (A m) (N m) x) ∈ M
  /-- **Alignment, predecessor.** On `T m`, every column-base predecessor lies *in* the marker
  set. -/
  marker_pred : ∀ m, ∀ x ∈ T m,
    (e.symm : α → α) (columnBase e (A m) (N m) x) ∈ M
  /-- Decoding stage `m`'s read-off block at the floor offset recovers the cell index. -/
  decodes : ∀ m, ∀ x ∈ T m,
    decode (sentinelEncode s emb
        (weaveName e (A m) (N m) s emb (markerCode M emb dataLetter)
          (columnBase e (A m) (N m) x)))
      (floorAddr e (A m) (N m) x) = cellIndex x
  /-- The stage misses are summable. -/
  misses_summable : (∑' m, μ (T m)ᶜ) ≠ ∞

/-- **The `BracketedTowerSystem` from an `AlignedTowerCastle`.** The master code is the piecewise
`markerCode M emb dataLetter`; measurability is `measurable_markerCode`. The three self-bracketing
fields are discharged from the alignment facts via the piecewise reads:

* `interior` is `markerCode_mem_range_of_notMem` applied to `interior_notMarker`;
* `top` is `markerCode_mem` applied to `marker_top`;
* `pred` is `markerCode_mem` applied to `marker_pred`.

`decodes`, cell-index recovery and summable misses carry over verbatim. This is the cross-stage
interleaving made definitional through one coherent marker set. -/
noncomputable def AlignedTowerCastle.toBracketedTowerSystem [Nonempty (Fin (k - 1))] {e : α ≃ᵐ α}
    {Q : κ → Set α} (C : AlignedTowerCastle e μ Q k) : BracketedTowerSystem e μ Q k where
  s := C.s
  code := markerCode C.M C.emb C.dataLetter
  code_measurable := measurable_markerCode C.M_measurable C.emb C.dataLetter_measurable
  emb := C.emb
  decode := C.decode
  cellIndex := C.cellIndex
  cellIndex_recovers := C.cellIndex_recovers
  A := C.A
  A_measurable := C.A_measurable
  N := C.N
  hN := C.hN
  T := C.T
  cover := C.cover
  interior := by
    intro m x hx i hi
    exact markerCode_mem_range_of_notMem (C.interior_notMarker m x hx i hi)
  top := by
    intro m x hx
    exact markerCode_mem (C.marker_top m x hx)
  pred := by
    intro m x hx
    exact markerCode_mem (C.marker_pred m x hx)
  decodes := C.decodes
  misses_summable := C.misses_summable

/-- **Sub-problem B closed from an aligned-tower castle.** An `AlignedTowerCastle` — a refining
sequence of Rokhlin towers with one coherent measurable marker set aligning every column top and
base-predecessor across stages while avoiding every interior floor, with summable misses — yields,
via `BracketedTowerSystem.codes`, the cross-layer countable mod-0 code `CodesTwoSidedMod0c e Q (…)`,
the deliverable that slots into `Oseledets.Krieger.KriegerCodingData.code_codes`. The entire
residual is now the *existence* of the aligned marker set `M`, i.e. the Kakutani–Rokhlin nested
castle. -/
theorem AlignedTowerCastle.codes [Nonempty (Fin (k - 1))]
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (C : AlignedTowerCastle e μ Q k) :
    letI B := C.toBracketedTowerSystem
    letI D := B.toStageInput
    letI data := RefiningTowerCode.ofStages D.s D.code D.code_measurable D.decode D.cellIndex
      D.cellIndex_recovers D.T D.misses_summable (fun m => D.toStageCode e m)
    CodesTwoSidedMod0c e Q
      (codePartition (μ := μ) data.toColumnLayoutData.code
        data.toColumnLayoutData.code_measurable) :=
  C.toBracketedTowerSystem.codes

end Oseledets.Krieger
