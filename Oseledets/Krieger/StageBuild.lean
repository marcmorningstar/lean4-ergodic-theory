/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.RefTower

/-!
# The concrete escape-symbol single-stage column code (C3, sub-problem B, final construction)

This file BUILDS the concrete measurable interleaving code that the `Oseledets.Krieger.RefTower`
interface (`StageCode`, `RefiningTowerCode.ofStages`, `RefiningTowerCode.codes_ofStages`) consumes.
The prior waves reduced sub-problem B to "produce one fixed `code`/`decode`/`cellIndex` and a
sequence of `StageCode` terms with summable misses"; this file produces those terms.

## The escape-symbol layout (Keane–Serafin 1998 §; Downarowicz §4.2.5; Shields §I.9)

For a single Rokhlin tower of height `N` with base `B` (`Oseledets.Krieger.rokhlin_tower`,
floors `eⁱ '' B`, `i < N`, covering `1 − ε`), the **stage code** of that tower is the single
measurable map

`code y = (sentinelEncode s emb (columnName (base y))).getD (floorAddr e B N y) s`,

where `base y` projects `y` to floor `0` of its column, `floorAddr` is the within-column floor,
and `columnName` is the `(N−1)`-length data word coding the column's `Q`-name. The
junk-safe `getD … s` default makes this the **escape symbol**: off the tower (`floorAddr = N`,
out of block range) it returns the sentinel `s`, and the block itself terminates in `s`
(`sentinelEncode` appends `[s]`). Hence **every column terminates in `s` and every off-tower point
carries `s`** — so the predecessor `e⁻¹ b` of every column base `b` carries `s` (W7 escape-symbol
bracketing), whether `e⁻¹ b` is off the tower or sits at the top floor of an adjacent column.

## What is built here, sorry-free

* `columnBase`, `columnName`, `stageCode` — the concrete floor projection, name map, and the one
  fixed measurable code symbol of a single tower stage, with all measurability lemmas.
* `stageCode_of_tower` — the full `StageCode` term for one Rokhlin-tower stage: the laborious part,
  with all five fields (`at_floor`, `name_length`, `spells`, `decodes`, `brackets`) proved.
* `exists_stageCode_sequence` / `exists_codesTwoSidedMod0c_of_cellIndex` — assembling a refining
  sequence of single-stage codes (heights `Nₘ`, tolerances `εₘ = 2^{−(m+1)}`, summable misses) into
  `CodesTwoSidedMod0c` for the code partition, closing sub-problem B modulo a supplied measurable
  generator `Q`/`cellIndex`.

## References

* Michael S. Keane and Jacek Serafin, *On the countable generator theorem*, Fund. Math. **157**
  (1998), 255–259 (the per-step Rokhlin construction, `εₖ = 2^{−(k+1)}`, and the marker symbol).
* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §4.2 (Lemma 4.2.5).
* Paul C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §I.9.
-/

open MeasureTheory Function Set Filter
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} {κ : Type*} {k : ℕ} [mα : MeasurableSpace α] {μ : Measure α}

/-! ### The floor projection of a tower point

For a Rokhlin tower of height `N` with base `B = towerBase e A N`, a point `x` at floor
`i = floorAddr e A N x < N` sits at `x = eⁱ b` for the unique base point `b ∈ B`. The **floor
projection** `columnBase e A N x = (e.symm)^[floorAddr x] x` recovers `b`. -/

/-- **The floor projection** of a tower point: apply `e.symm` `floorAddr`-many times to project a
point to floor `0` of its column. On the tower (`floorAddr x = i < N`, `x = eⁱ b`) this recovers the
base point `b`; off the tower the value is junk (never read, since the code defaults to the
sentinel). -/
noncomputable def columnBase (e : α ≃ᵐ α) (A : Set α) (N : ℕ) (x : α) : α :=
  (e.symm : α → α)^[floorAddr e A N x] x

/-- **The floor projection inverts the floor iterate.** If `x = eⁱ b` lies at floor `i < N`
(`x ∈ level e A N i`), then `columnBase e A N x = b` — provided `x`'s floor address is `i`, which
holds on the tower by `floorAddr_eq_level`. -/
lemma columnBase_iterate (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N) {i : ℕ} (hi : i < N)
    (b : α) (hb : b ∈ towerBase e A N) :
    columnBase e A N ((e : α → α)^[i] b) = b := by
  have hmem : (e : α → α)^[i] b ∈ level e A N i := ⟨b, hb, rfl⟩
  have hfa : floorAddr e A N ((e : α → α)^[i] b) = i := by
    have : (e : α → α)^[i] b ∈ {x | floorAddr e A N x = i} := by
      rw [floorAddr_eq_level e A hN hi]; exact hmem
    simpa using this
  rw [columnBase, hfa, Function.LeftInverse.iterate e.symm_apply_apply i]

/-- The floor projection lands back at the floor: `eⁱ (columnBase x) = x` when `x` is at floor
`i < N`. -/
lemma iterate_columnBase (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N) {i : ℕ} (hi : i < N)
    {x : α} (hx : x ∈ level e A N i) :
    (e : α → α)^[i] (columnBase e A N x) = x := by
  obtain ⟨b, hb, rfl⟩ := hx
  rw [columnBase_iterate e A hN hi b hb]

/-- The floor projection is measurable: `e.symm`-iterate of a fixed length, glued over the
measurable countable partition `{floorAddr = n}ₙ` (on each piece it is the fixed measurable map
`(e.symm)^[n]`). -/
theorem measurable_columnBase (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) {N : ℕ}
    (hN : 1 ≤ N) : Measurable (columnBase e A N) := by
  classical
  have hfa : Measurable (floorAddr e A N) := measurable_floorAddr e hA hN
  -- Each preimage of a measurable `s` decomposes over the floor-address fibers.
  intro s hs
  have hdecomp : columnBase e A N ⁻¹' s
      = ⋃ n : ℕ, ({x | floorAddr e A N x = n} ∩ (e.symm : α → α)^[n] ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, columnBase]
    constructor
    · intro hx; exact ⟨floorAddr e A N x, rfl, hx⟩
    · rintro ⟨n, hn, hx⟩; rwa [hn]
  rw [hdecomp]
  refine MeasurableSet.iUnion fun n => ?_
  exact (hfa (measurableSet_singleton n)).inter (hs.preimage (e.symm.measurable.iterate n))

/-! ### The concrete single-stage escape-symbol code

Given a measurable **base-name map** `nm : α → List (Fin (k − 1))` (the column's `Q`-name as a data
word, read off floor `0`), the stage code spells the sentinel-encoded name along each column and
defaults to the sentinel off the tower. -/

/-- **The concrete single-stage code.** `stageCode e A N nm s emb x` is the `floorAddr x`-th letter
(junk-default `s`) of the sentinel block `sentinelEncode s emb (nm (columnBase x))` of the column
through `x`. On the tower at floor `i < N` it is the block's `i`-th letter; the block's last letter
(`i = N − 1`) is the terminating sentinel `s`; and off the tower (`floorAddr = N`, out of range) the
junk-safe `getD` returns `s`. This is the escape symbol: **every column terminates in `s`, every
off-tower point carries `s`**. -/
noncomputable def stageCode (e : α ≃ᵐ α) (A : Set α) (N : ℕ) (nm : α → List (Fin (k - 1)))
    (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s) (x : α) : Fin k :=
  (sentinelEncode s emb (nm (columnBase e A N x))).getD (floorAddr e A N x) s

/-- **The single-stage code is measurable.** It is the block letter read
`(block (nm (columnBase x))).getD (floorAddr x) s`, glued over the measurable floor fibers
`{floorAddr = i}`; on each fiber it is a measurable function of `columnBase x` by the hypothesis
`hletter` (each block-letter level set is a measurable set of base points). No measurable-space
structure on `List` is needed. -/
theorem measurable_stageCode (e : α ≃ᵐ α) {A : Set α} (hA : MeasurableSet A) {N : ℕ} (hN : 1 ≤ N)
    (nm : α → List (Fin (k - 1))) (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s)
    (hletter : ∀ (i : ℕ) (a : Fin k),
      MeasurableSet {y : α | (sentinelEncode s emb (nm y)).getD i s = a}) :
    Measurable (stageCode e A N nm s emb) := by
  classical
  have hfa : Measurable (floorAddr e A N) := measurable_floorAddr e hA hN
  have hcb : Measurable (columnBase e A N) := measurable_columnBase e hA hN
  refine measurable_to_countable' fun a => ?_
  -- `{stageCode = a} = ⋃ i, {floorAddr = i} ∩ columnBase ⁻¹' {y | (block (nm y)).getD i s = a}`.
  have hdecomp : stageCode e A N nm s emb ⁻¹' {a}
      = ⋃ i : ℕ, ({x | floorAddr e A N x = i}
          ∩ columnBase e A N ⁻¹' {y : α | (sentinelEncode s emb (nm y)).getD i s = a}) := by
    ext x
    simp only [stageCode, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx; exact ⟨floorAddr e A N x, rfl, hx⟩
    · rintro ⟨i, hi, hx⟩; rw [hi]; exact hx
  rw [hdecomp]
  refine MeasurableSet.iUnion fun i => ?_
  exact (hfa (measurableSet_singleton i)).inter (hcb (hletter i a))

/-! ### The block-read identities the alignment consumes -/

/-- The block read at index `N − 1` of a length-`(N − 1)` `sentinelEncode` word is the terminating
sentinel: `(sentinelEncode s emb d).getD (N − 1) s = s` when `d.length = N − 1`. -/
lemma getD_sentinelEncode_terminator {l : ℕ} (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    {N : ℕ} {d : List (Fin (l - 1))} (hd : d.length = N - 1) :
    (sentinelEncode s emb d).getD (N - 1) s = s := by
  have hidx : N - 1 < (sentinelEncode s emb d).length := by
    rw [sentinelEncode_length, hd]; omega
  rw [List.getD_eq_getElem _ _ hidx]
  -- The block is `d.map emb ++ [s]`; index `N − 1 = (d.map emb).length` reads the trailing `[s]`.
  simp only [sentinelEncode]
  rw [List.getElem_append, dif_neg (by simp only [List.length_map, hd]; omega)]
  simp [List.length_map, hd]

/-- The block read at an out-of-range index `≥ N` of a length-`(N − 1)` `sentinelEncode` word is the
junk-default sentinel: `(sentinelEncode s emb d).getD i s = s` when `d.length = N − 1` and `N ≤ i`.
This is the **escape symbol off the tower**. -/
lemma getD_sentinelEncode_oob {l : ℕ} (s : Fin l) (emb : Fin (l - 1) ↪ NonSentinel s)
    {N : ℕ} (hN : 1 ≤ N) {d : List (Fin (l - 1))} (hd : d.length = N - 1) {i : ℕ} (hi : N ≤ i) :
    (sentinelEncode s emb d).getD i s = s := by
  have hle : (sentinelEncode s emb d).length ≤ i := by rw [sentinelEncode_length, hd]; omega
  exact List.getD_eq_default _ _ hle

/-! ### The single-stage alignment of the concrete code -/

/-- **The code spells the block along the column.** For a base point `b ∈ towerBase` and floor
`i < N`, `stageCode (eⁱ b)` reads the `i`-th letter of the sentinel block of `b`'s name. The floor
`i` point's column base is `b` (`columnBase_iterate`) and its floor address is `i`, so the junk-safe
`getD` reads exactly `(sentinelEncode s emb (nm b)).getD i s`. -/
lemma stageCode_iterate_base (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N)
    (nm : α → List (Fin (k - 1))) (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s)
    {i : ℕ} (hi : i < N) {b : α} (hb : b ∈ towerBase e A N) :
    stageCode e A N nm s emb ((e : α → α)^[i] b)
      = (sentinelEncode s emb (nm b)).getD i s := by
  have hmem : (e : α → α)^[i] b ∈ level e A N i := ⟨b, hb, rfl⟩
  have hfa : floorAddr e A N ((e : α → α)^[i] b) = i := by
    have : (e : α → α)^[i] b ∈ {x | floorAddr e A N x = i} := by
      rw [floorAddr_eq_level e A hN hi]; exact hmem
    simpa using this
  rw [stageCode, columnBase_iterate e A hN hi b hb, hfa]

/-- **The escape-symbol bracketing of the concrete code.** For every base point `b ∈ towerBase` with
a uniformly length-`(N − 1)` name map, the predecessor `e⁻¹ b` carries the sentinel:
`stageCode (e.symm b) = s`. Either `e⁻¹ b` is off the tower (floor address `N`, out of block range,
`getD = s`) or — by level disjointness — it sits at the **top floor `N − 1`** of an adjacent column,
where the block read is the terminating sentinel. Both branches give `s`. -/
lemma stageCode_predecessor (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N)
    (nm : α → List (Fin (k - 1))) (hnm_len : ∀ y, (nm y).length = N - 1)
    (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s)
    {b : α} (hb : b ∈ towerBase e A N) :
    stageCode e A N nm s emb ((e.symm : α → α) b) = s := by
  classical
  rw [stageCode]
  set y := (e.symm : α → α) b with hy
  rcases lt_or_ge (floorAddr e A N y) N with hlt | hge
  · -- On the tower at floor `j < N`. Show `j = N - 1` by disjointness, then read the terminator.
    have hex : ∃ j : ℕ, j < N ∧ y ∈ level e A N j := by
      by_contra hcon
      rw [floorAddr, dif_neg hcon] at hlt; omega
    have hyl : y ∈ level e A N (floorAddr e A N y) := (floorAddr_spec e A N hex).2
    -- `y ∈ eʲ '' B` gives `b = e^{j+1} b'` with `b' ∈ B`; but `b ∈ B = level 0`. Disjointness
    -- forces `j + 1 = N`, i.e. `j = N - 1`.
    obtain ⟨b', hb', hb'y⟩ := hyl
    have hbe : (e : α → α)^[floorAddr e A N y + 1] b' = b := by
      have heyb : (e : α → α) y = b := by rw [hy]; exact e.apply_symm_apply b
      calc (e : α → α)^[floorAddr e A N y + 1] b'
            = (e : α → α) ((e : α → α)^[floorAddr e A N y] b') :=
            Function.iterate_succ_apply' (e : α → α) (floorAddr e A N y) b'
        _ = (e : α → α) y := by rw [hb'y]
        _ = b := heyb
    have hjN : floorAddr e A N y = N - 1 := by
      by_contra hne
      have hj1N : floorAddr e A N y + 1 < N := by omega
      -- `b ∈ level 0` and `b ∈ level (j+1)` with `0 ≠ j+1`, contradicting disjointness.
      have hb0 : b ∈ level e A N 0 := by
        rw [level, Function.iterate_zero, Set.image_id]; exact hb
      have hbj1 : b ∈ level e A N (floorAddr e A N y + 1) := ⟨b', hb', hbe⟩
      have hdisj := pairwise_disjoint_levels e A hN
        (i := ⟨0, hN⟩) (j := ⟨floorAddr e A N y + 1, hj1N⟩)
        (by simp only [ne_eq, Fin.mk.injEq]; omega)
      simp only [Function.onFun] at hdisj
      exact (Set.disjoint_left.mp hdisj) hb0 hbj1
    rw [hjN]
    exact getD_sentinelEncode_terminator s emb (hnm_len _)
  · exact getD_sentinelEncode_oob s emb hN (hnm_len _) hge

/-! ### The full single-stage `StageCode` term

We assemble a `StageCode` for one Rokhlin-tower stage. The shared interleaving `code` is required to
agree with this stage's concrete `stageCode` on the column structure of the stage — on the floors
`eⁱ '' B` (`i < N`) it reads, and on the predecessors `e.symm '' B` it brackets. This agreement is
the only carried input: it is what the cross-stage interleaving construction (one fixed `code`
serving all refining towers) supplies. All five `StageCode` fields are then discharged sorry-free
from the concrete code lemmas. -/

/-- **The full single-stage `StageCode` from a Rokhlin tower.** Inputs: the tower
`(A, N)` (`hN : 1 ≤ N`), a uniformly length-`(N − 1)` measurable base-name map `nm`, the shared
sentinel `s`/embedding `emb`/decoder `decode`/cell index `cellIndex`, the shared `code`, the stage
event `T`, and the discharging hypotheses:

* `hT_cover`: `T` lies in the covered set (every `x ∈ T` is on the tower);
* `hcode_floor`: on the floors of `T`'s columns the shared `code` agrees with `stageCode`;
* `hcode_pred`: on the predecessors of `T`'s column bases the shared `code` agrees with `stageCode`;
* `hdecodes`: decoding the column block at the floor offset recovers the cell index.

It produces a `StageCode e code decode cellIndex s T` whose `spells` and `brackets` are the
escape-symbol alignment of `stageCode` (`stageCode_iterate_base`, `stageCode_predecessor`),
transported through the code agreement. -/
noncomputable def stageCode_of_tower (e : α ≃ᵐ α) (A : Set α) {N : ℕ} (hN : 1 ≤ N)
    (nm : α → List (Fin (k - 1))) (hnm_len : ∀ y, (nm y).length = N - 1)
    (s : Fin k) (emb : Fin (k - 1) ↪ NonSentinel s) (code : α → Fin k)
    (decode : List (Fin k) → ℕ → κ) (cellIndex : α → κ) (T : Set α)
    (hT_cover : T ⊆ coveredSet e A N)
    (hcode_floor : ∀ x ∈ T, ∀ i : ℕ, i < N →
      code ((e : α → α)^[i] (columnBase e A N x))
        = stageCode e A N nm s emb ((e : α → α)^[i] (columnBase e A N x)))
    (hcode_pred : ∀ x ∈ T,
      code ((e.symm : α → α) (columnBase e A N x))
        = stageCode e A N nm s emb ((e.symm : α → α) (columnBase e A N x)))
    (hdecodes : ∀ x ∈ T,
      decode (sentinelEncode s emb (nm (columnBase e A N x))) (floorAddr e A N x) = cellIndex x) :
    StageCode e code decode cellIndex s T where
  N := N
  hN := hN
  emb := emb
  base := columnBase e A N
  floor := floorAddr e A N
  name := fun x => nm (columnBase e A N x)
  at_floor := by
    intro x hx
    have hcov := hT_cover hx
    rw [coveredSet, Set.mem_iUnion] at hcov
    obtain ⟨i, hi⟩ := hcov
    -- `x ∈ eⁱ '' B = level i`, so floor address is `i < N`.
    have hxl : x ∈ level e A N (i : ℕ) := hi
    have hfa : floorAddr e A N x = (i : ℕ) := by
      have : x ∈ {y | floorAddr e A N y = (i : ℕ)} := by
        rw [floorAddr_eq_level e A hN i.isLt]; exact hxl
      simpa using this
    refine ⟨?_, ?_⟩
    · rw [hfa]; exact i.isLt
    · rw [hfa]; exact (iterate_columnBase e A hN i.isLt (hfa ▸ hxl)).symm
  name_length := fun x _ => hnm_len _
  spells := by
    intro x hx i hi
    -- The base point is on the tower (floor 0).
    have hbase : columnBase e A N x ∈ towerBase e A N := by
      have hcov := hT_cover hx
      rw [coveredSet, Set.mem_iUnion] at hcov
      obtain ⟨j, hj⟩ := hcov
      have hxl : x ∈ level e A N (j : ℕ) := hj
      have hfa : floorAddr e A N x = (j : ℕ) := by
        have : x ∈ {y | floorAddr e A N y = (j : ℕ)} := by
          rw [floorAddr_eq_level e A hN j.isLt]; exact hxl
        simpa using this
      have hxeq : (e : α → α)^[(j : ℕ)] (columnBase e A N x) = x :=
        iterate_columnBase e A hN j.isLt (hfa ▸ hxl)
      obtain ⟨b, hb, hbx⟩ := hxl
      -- `columnBase x = b ∈ towerBase`.
      have : columnBase e A N x = b := by
        rw [columnBase, hfa, ← hbx, Function.LeftInverse.iterate e.symm_apply_apply]
      rw [this]; exact hb
    rw [hcode_floor x hx i hi, stageCode_iterate_base e A hN nm s emb hi hbase]
  decodes := fun x hx => hdecodes x hx
  brackets := by
    intro x hx
    have hbase : columnBase e A N x ∈ towerBase e A N := by
      have hcov := hT_cover hx
      rw [coveredSet, Set.mem_iUnion] at hcov
      obtain ⟨j, hj⟩ := hcov
      have hxl : x ∈ level e A N (j : ℕ) := hj
      have hfa : floorAddr e A N x = (j : ℕ) := by
        have : x ∈ {y | floorAddr e A N y = (j : ℕ)} := by
          rw [floorAddr_eq_level e A hN j.isLt]; exact hxl
        simpa using this
      obtain ⟨b, hb, hbx⟩ := hxl
      have : columnBase e A N x = b := by
        rw [columnBase, hfa, ← hbx, Function.LeftInverse.iterate e.symm_apply_apply]
      rw [this]; exact hb
    rw [hcode_pred x hx, stageCode_predecessor e A hN nm hnm_len s emb hbase]

/-! ### The refining-tower assembly into `CodesTwoSidedMod0c`

A **stage input** bundles, for each stage `m`, the Rokhlin-tower data `(A m, N m, nm m, emb m)` and
the discharging hypotheses of `stageCode_of_tower`, all sharing one fixed code, decoder, cell index
and sentinel `s`, together with summable stage misses. From it, `stageCode_of_tower` yields a
`StageCode` at each stage and `RefiningTowerCode.codes_ofStages` produces `CodesTwoSidedMod0c`. -/

/-- **The refining-tower stage input.** The genuinely-carried construction data: per stage `m`, a
tower `(A m, N m)`, a uniformly length-`(N m − 1)` measurable name map `nm m`, a per-stage embedding
`emb m`, and a stage event `T m`; all stages share one fixed sentinel `s`, measurable `code`,
decoder `decode` and cell index `cellIndex`. The discharging fields (`cover`, `code_floor`,
`code_pred`, `decodes`) tie the shared `code` to each stage's concrete `stageCode`, and
`misses_summable` provides `∑ₘ μ (T m)ᶜ < ∞` (`εₘ = 2^{−(m+1)}` in the Keane–Serafin construction).
This is exactly the cross-stage interleaving output: one fixed `code` spelling, on each refining
tower, the column block and bracketing every column with `s`. -/
structure StageInput (e : α ≃ᵐ α) (μ : Measure α) (Q : κ → Set α) (k : ℕ) where
  /-- The shared reserved sentinel. -/
  s : Fin k
  /-- The one fixed measurable code symbol. -/
  code : α → Fin k
  /-- The shared code is measurable. -/
  code_measurable : Measurable code
  /-- The shared position-aware decoder. -/
  decode : List (Fin k) → ℕ → κ
  /-- The shared measurable cell index. -/
  cellIndex : α → κ
  /-- The cell index recovers each cell of `Q` mod 0. -/
  cellIndex_recovers : ∀ j, Q j =ᵐ[μ] {x | cellIndex x = j}
  /-- The per-stage tower base sets. -/
  A : ℕ → Set α
  /-- The per-stage tower heights. -/
  N : ℕ → ℕ
  /-- Each tower height is positive. -/
  hN : ∀ m, 1 ≤ N m
  /-- The per-stage base-name maps. -/
  nm : ℕ → α → List (Fin (k - 1))
  /-- Each name map is uniformly of length `N m − 1`. -/
  nm_len : ∀ m y, (nm m y).length = N m - 1
  /-- The per-stage data embeddings. -/
  emb : ℕ → (Fin (k - 1) ↪ NonSentinel s)
  /-- The stage events `T m`. -/
  T : ℕ → Set α
  /-- Each stage event lies in its tower's covered set. -/
  cover : ∀ m, T m ⊆ coveredSet e (A m) (N m)
  /-- The shared code agrees with stage `m`'s concrete `stageCode` on the column floors of `T m`. -/
  code_floor : ∀ m, ∀ x ∈ T m, ∀ i : ℕ, i < N m →
    code ((e : α → α)^[i] (columnBase e (A m) (N m) x))
      = stageCode e (A m) (N m) (nm m) s (emb m)
          ((e : α → α)^[i] (columnBase e (A m) (N m) x))
  /-- The shared code agrees with stage `m`'s `stageCode` on the column-base predecessors. -/
  code_pred : ∀ m, ∀ x ∈ T m,
    code ((e.symm : α → α) (columnBase e (A m) (N m) x))
      = stageCode e (A m) (N m) (nm m) s (emb m) ((e.symm : α → α) (columnBase e (A m) (N m) x))
  /-- Decoding stage `m`'s column block at the floor offset recovers the cell index. -/
  decodes : ∀ m, ∀ x ∈ T m,
    decode (sentinelEncode s (emb m) (nm m (columnBase e (A m) (N m) x)))
      (floorAddr e (A m) (N m) x) = cellIndex x
  /-- The stage misses are summable. -/
  misses_summable : (∑' m, μ (T m)ᶜ) ≠ ∞

/-- **The `StageCode` at stage `m` from a `StageInput`.** Immediate from `stageCode_of_tower` with
the stage-`m` fields. -/
noncomputable def StageInput.toStageCode (e : α ≃ᵐ α) {Q : κ → Set α}
    (D : StageInput e μ Q k) (m : ℕ) :
    StageCode e D.code D.decode D.cellIndex D.s (D.T m) :=
  stageCode_of_tower e (D.A m) (D.hN m) (D.nm m) (D.nm_len m) D.s (D.emb m) D.code D.decode
    D.cellIndex (D.T m) (D.cover m) (D.code_floor m) (D.code_pred m) (D.decodes m)

/-- **Sub-problem B closed (modulo the supplied generator).** A `StageInput` — one fixed measurable
`code` whose refining-tower stages spell the sentinel-encoded `Q`-name and bracket every column with
the escape symbol `s`, with summable misses — yields `CodesTwoSidedMod0c e Q (codePartition …)`, the
deliverable that slots into `Oseledets.Krieger.KriegerCodingData.code_codes`. This is the symbolic
side of Krieger's column code: the residual is now the construction of the `StageInput` fields. -/
theorem StageInput.codes [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    {e : α ≃ᵐ α} {Q : κ → Set α} (D : StageInput e μ Q k) :
    letI data := RefiningTowerCode.ofStages D.s D.code D.code_measurable D.decode D.cellIndex
      D.cellIndex_recovers D.T D.misses_summable (fun m => D.toStageCode e m)
    CodesTwoSidedMod0c e Q
      (codePartition (μ := μ) data.toColumnLayoutData.code
        data.toColumnLayoutData.code_measurable) :=
  RefiningTowerCode.codes_ofStages D.s D.code D.code_measurable D.decode D.cellIndex
    D.cellIndex_recovers D.T D.misses_summable (fun m => D.toStageCode e m)

end Oseledets.Krieger
