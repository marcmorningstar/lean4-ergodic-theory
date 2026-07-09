/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.SubshiftFiniteType
import Mathlib.Logic.Equiv.List
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Topology.MetricSpace.Holder

/-!
# Dense forward orbits for subshifts of finite type, and the golden-mean Livšic theorem

This file supplies the second, dynamical ingredient of the one-sided subshift-of-finite-type (SFT)
Livšic theorem `ErgodicTheory.livsic_sft` (`ErgodicTheory.Livsic.SubshiftFiniteType`): a **dense
forward orbit** for the SFT shift `sftShiftMap M`. Together with the unconditional exponential
closing property proved there, it produces the fully **unconditional** Livšic cohomology theorem for
concrete SFTs, of which the **golden-mean shift** (forbid the block `11`) is the headline instance.

## The safe-symbol interface

The closing property of `SubshiftFiniteType` needs *no* irreducibility of the transition matrix
`M`: the `δ = 1/2` radius makes the periodization admissible for any `M`. Irreducibility is used
only to produce a dense orbit. Here we isolate exactly the combinatorial input the dense-orbit
construction needs — a **safe symbol** `s` that can follow and precede every symbol:

* `ErgodicTheory.SafeSymbol` — the class packaging `s : Fin k` with `M a s = true` and
  `M s a = true` for all `a`.

A safe symbol is a symbol allowed adjacent to every symbol (as the golden-mean `0`). This is
*strictly stronger* than irreducibility of `M`: a general irreducible SFT need not have one, and
dense orbits for such SFTs are **not** delivered here. The golden-mean shift has `s = 0`.

## The construction

Mirroring the full-shift dense orbit `ErgodicTheory.Livsic.exists_denseRange_shiftMap_orbit`, we
concatenate *all* finite words (`Encodable.decode`), but first **sanitize** each word to its nearest
admissible version (keep it if `M`-admissible, drop it otherwise) and pad every block with one
trailing safe symbol. The trailing `s` makes every inter-block transition legal (`safe_from` at the
end of a block, `safe_to` at the start of the next), and sanitizing keeps every retained word
`M`-admissible, so the whole sequence lands in the SFT carrier
(`ErgodicTheory.sftRichPoint_mem`). Every admissible target word — in particular every prefix of a
point of the SFT — is retained verbatim and therefore appears as a block, giving density.

## Main results

* `ErgodicTheory.sftRichPoint` / `ErgodicTheory.sftRichPoint_mem` — the base point of the orbit.
* `ErgodicTheory.exists_denseRange_sftShiftMap_orbit` — its forward orbit is dense (for any
  `[SafeSymbol M]`).
* `ErgodicTheory.goldenMeanM` / the `SafeSymbol` instance / `ErgodicTheory.goldenMean_proper` — the
  golden-mean shift, and a certificate that it is a *proper* subshift (the all-ones sequence is
  inadmissible).
* `ErgodicTheory.livsic_goldenMean` — the unconditional Livšic equivalence for the golden-mean SFT.

## References

* D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, CUP (1995), §1.2
  (the golden-mean shift) and §2.2 (irreducible subshifts of finite type).
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  §19.2.
-/

open Function Filter Topology Set
open scoped NNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

attribute [local instance] PiNat.metricSpace

variable {k : ℕ}

/-- A **safe symbol** for the transition matrix `M : Fin k → Fin k → Bool`: a symbol `s` allowed
adjacent to every symbol — it may follow every symbol (`safe_from`) and precede every symbol
(`safe_to`) (as the golden-mean `0`). This is *strictly stronger* than irreducibility of `M`: a
general irreducible SFT need not have a safe symbol (dense orbits for such SFTs are **not**
delivered here). It is exactly the combinatorial input that the dense-orbit construction needs
(the closing property of `SubshiftFiniteType` needs no irreducibility at all). -/
class SafeSymbol (M : Fin k → Fin k → Bool) where
  /-- The distinguished safe symbol. -/
  s : Fin k
  /-- Every symbol may be followed by `s`. -/
  safe_from : ∀ a, M a s = true
  /-- Every symbol may be preceded by `s`, i.e. `s` may be followed by anything. -/
  safe_to : ∀ a, M s a = true

variable {M : Fin k → Fin k → Bool}

/-- The distinguished safe symbol of `M`. -/
def safe (M : Fin k → Fin k → Bool) [SafeSymbol M] : Fin k := SafeSymbol.s (M := M)

/-- Every symbol may be followed by the safe symbol. -/
theorem safe_from [SafeSymbol M] (a : Fin k) : M a (safe M) = true :=
  SafeSymbol.safe_from (M := M) a

/-- The safe symbol may be followed by every symbol. -/
theorem safe_to [SafeSymbol M] (a : Fin k) : M (safe M) a = true := SafeSymbol.safe_to (M := M) a

/-- The safe symbol may follow itself: the block `s s` is admissible. -/
theorem safe_safe [SafeSymbol M] : M (safe M) (safe M) = true := safe_to (safe M)

noncomputable section

open Classical in
/-- `sanitize M w` is `w` itself when `w` is `M`-admissible (adjacent symbols allowed by `M`,
`List.IsChain`), and the empty word otherwise. In either case the result is admissible. -/
def sanitize (M : Fin k → Fin k → Bool) (w : List (Fin k)) : List (Fin k) :=
  if w.IsChain (fun a b => M a b = true) then w else []

/-- The sanitized word is always `M`-admissible. -/
theorem sanitize_isChain (w : List (Fin k)) :
    (sanitize M w).IsChain (fun a b => M a b = true) := by
  unfold sanitize
  split
  · assumption
  · exact List.isChain_nil

/-- Sanitizing fixes an already-admissible word. -/
theorem sanitize_of_isChain {w : List (Fin k)}
    (h : w.IsChain (fun a b => M a b = true)) : sanitize M w = w := by
  unfold sanitize
  exact if_pos h

variable [SafeSymbol M]

/-- The `j`-th building block: the sanitized `j`-th decoded word (over the countable encoding of
`List (Fin k)`), padded with one trailing safe symbol. The pad makes (i) every block nonempty and
(ii) every inter-block transition admissible. -/
def sftWord (M : Fin k → Fin k → Bool) [SafeSymbol M] (j : ℕ) : List (Fin k) :=
  sanitize M ((Encodable.decode (α := List (Fin k)) j).getD []) ++ [safe M]

/-- Definitional unfolding of `sftWord`. -/
theorem sftWord_eq (j : ℕ) :
    sftWord M j = sanitize M ((Encodable.decode (α := List (Fin k)) j).getD []) ++ [safe M] := rfl

/-- Every block is nonempty, thanks to the trailing safe symbol. -/
theorem sftWord_length_pos (j : ℕ) : 1 ≤ (sftWord M j).length := by
  simp only [sftWord, List.length_append, List.length_singleton]; omega

/-- Every block is `M`-admissible: the sanitized part is admissible, the trailing `s` is admissible,
and the junction (`last-of-word → s`) is legal by `safe_from`. -/
theorem sftWord_isChain (j : ℕ) : (sftWord M j).IsChain (fun a b => M a b = true) := by
  rw [sftWord_eq]
  refine (sanitize_isChain _).append (List.isChain_singleton _) ?_
  intro x _hx y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst hy
  exact safe_from x

/-- The prefix obtained by concatenating the first `j` blocks. -/
def sftPrefixList (M : Fin k → Fin k → Bool) [SafeSymbol M] : ℕ → List (Fin k)
  | 0 => []
  | j + 1 => sftPrefixList M j ++ sftWord M j

/-- Unfolding lemma for the successor step of `sftPrefixList`. -/
theorem sftPrefixList_succ (j : ℕ) :
    sftPrefixList M (j + 1) = sftPrefixList M j ++ sftWord M j := rfl

/-- The `j`-th prefix has length at least `j`. -/
theorem sftPrefixList_length_ge (j : ℕ) : j ≤ (sftPrefixList M j).length := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hpos := sftWord_length_pos (M := M) j
    rw [sftPrefixList_succ, List.length_append]
    omega

/-- The prefixes are nested. -/
theorem sftPrefixList_prefix {a b : ℕ} (h : a ≤ b) :
    sftPrefixList M a <+: sftPrefixList M b := by
  induction b, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m _ ih => exact ih.trans ⟨sftWord M m, rfl⟩

/-- `getD` is stable along the prefix chain. -/
theorem getD_sftPrefixList_of_le {a b n : ℕ} (hab : a ≤ b)
    (hn : n < (sftPrefixList M a).length) :
    (sftPrefixList M b).getD n (safe M) = (sftPrefixList M a).getD n (safe M) := by
  obtain ⟨t, ht⟩ := sftPrefixList_prefix (M := M) hab
  rw [← ht, List.getD_append _ _ _ _ hn]

/-- The base point of the dense orbit: the concatenation of all sanitized, `s`-padded words, read
coordinatewise via the prefixes. -/
def sftRichPointFun (M : Fin k → Fin k → Bool) [SafeSymbol M] : Shift (Fin k) :=
  fun n => (sftPrefixList M (n + 1)).getD n (safe M)

/-- `sftRichPointFun M n` may be read off any prefix long enough to contain position `n`. -/
theorem sftRichPointFun_eq {j n : ℕ} (hn : n < (sftPrefixList M j).length) :
    sftRichPointFun M n = (sftPrefixList M j).getD n (safe M) := by
  have h1 : n < (sftPrefixList M (n + 1)).length :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (sftPrefixList_length_ge (M := M) (n + 1))
  have e1 : (sftPrefixList M (max (n + 1) j)).getD n (safe M)
      = (sftPrefixList M (n + 1)).getD n (safe M) :=
    getD_sftPrefixList_of_le (M := M) (le_max_left _ _) h1
  have e2 : (sftPrefixList M (max (n + 1) j)).getD n (safe M)
      = (sftPrefixList M j).getD n (safe M) :=
    getD_sftPrefixList_of_le (M := M) (le_max_right _ _) hn
  have hdef : sftRichPointFun M n = (sftPrefixList M (n + 1)).getD n (safe M) := rfl
  rw [hdef, ← e1, e2]

/-- **Block appearance.** Block `j` sits verbatim in `sftRichPointFun M` starting at position
`|sftPrefixList M j|`. -/
theorem sftRichPointFun_block (j i : ℕ) (hi : i < (sftWord M j).length) :
    sftRichPointFun M ((sftPrefixList M j).length + i) = (sftWord M j).getD i (safe M) := by
  have hlt : (sftPrefixList M j).length + i < (sftPrefixList M (j + 1)).length := by
    rw [sftPrefixList_succ, List.length_append]; omega
  rw [sftRichPointFun_eq (M := M) hlt, sftPrefixList_succ,
    List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The last symbol of any nonempty prefix is the safe symbol (each block ends with `s`). -/
theorem sftPrefixList_getLast?_mem {j : ℕ} :
    ∀ x ∈ (sftPrefixList M j).getLast?, x = safe M := by
  cases j with
  | zero =>
    intro x hx
    exact absurd hx (Option.not_mem_none x)
  | succ m =>
    intro x hx
    rw [sftPrefixList_succ, sftWord_eq, ← List.append_assoc, List.getLast?_concat,
      Option.mem_some_iff] at hx
    exact hx.symm

/-- **Admissibility of the prefixes.** Every prefix is `M`-admissible: blocks are admissible, and
the inter-block junction `last-of-prefix (= s) → head-of-next-block` is legal by `safe_to`. -/
theorem sftPrefixList_isChain (j : ℕ) :
    (sftPrefixList M j).IsChain (fun a b => M a b = true) := by
  induction j with
  | zero => exact List.isChain_nil
  | succ m ih =>
    rw [sftPrefixList_succ]
    refine ih.append (sftWord_isChain (M := M) m) ?_
    intro x hx y _hy
    have hxs := sftPrefixList_getLast?_mem (M := M) x hx
    subst hxs
    exact safe_to y

/-- **The base point lands in the SFT.** Every adjacent pair of `sftRichPointFun M` is admissible,
so it is a genuine point of the subshift. -/
theorem sftRichPoint_mem : sftRichPointFun M ∈ SFTCarrier M := by
  intro n
  have hlen : n + 2 ≤ (sftPrefixList M (n + 2)).length := sftPrefixList_length_ge (M := M) (n + 2)
  have hn : n < (sftPrefixList M (n + 2)).length := by omega
  have hn1 : n + 1 < (sftPrefixList M (n + 2)).length := by omega
  have hchain := sftPrefixList_isChain (M := M) (n + 2)
  rw [sftRichPointFun_eq (M := M) hn, sftRichPointFun_eq (M := M) hn1,
    List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hn1]
  exact List.isChain_iff_getElem.mp hchain n hn1

/-- The base point of the dense orbit, as a point of the SFT. -/
def sftRichPoint (M : Fin k → Fin k → Bool) [SafeSymbol M] : SFT M :=
  ⟨sftRichPointFun M, sftRichPoint_mem⟩

/-- **Orbit agreement.** For every target point `z` of the SFT and every precision `N`, some forward
iterate of `sftRichPointFun M` agrees with `z` on its first `N` coordinates: the admissible prefix
`z₀ … z_{N-1}` is retained by `sanitize` and appears verbatim as its own decode-block. -/
theorem exists_shiftMap_agree (z : SFT M) (N : ℕ) :
    ∃ n : ℕ, ∀ i < N, shiftMap^[n] (sftRichPointFun M) i = (z : Shift (Fin k)) i := by
  set w : List (Fin k) := List.ofFn (fun i : Fin N => (z : Shift (Fin k)) (i : ℕ)) with hw
  have hwlen : w.length = N := by rw [hw]; simp
  have hchainw : w.IsChain (fun a b => M a b = true) := by
    rw [hw, List.isChain_ofFn]
    intro i _hi
    exact z.2 i
  have hsan : sanitize M w = w := sanitize_of_isChain (M := M) hchainw
  obtain ⟨j, hj⟩ : ∃ j, (Encodable.decode (α := List (Fin k)) j).getD [] = w :=
    ⟨Encodable.encode w, by rw [Encodable.encodek]; rfl⟩
  refine ⟨(sftPrefixList M j).length, ?_⟩
  intro i hi
  rw [shiftMap_iterate_apply, Nat.add_comm i (sftPrefixList M j).length]
  have hi_word : i < (sftWord M j).length := by
    rw [sftWord_eq, List.length_append, hj, hsan, hwlen, List.length_singleton]; omega
  rw [sftRichPointFun_block (M := M) j i hi_word, sftWord_eq, hj, hsan]
  have hiw : i < w.length := by rw [hwlen]; exact hi
  rw [List.getD_append _ _ _ _ hiw, List.getD_eq_getElem _ _ hiw]
  simp only [hw, List.getElem_ofFn]

/-- **Dense forward orbit for the SFT.** For any transition matrix `M` equipped with a safe symbol,
the SFT shift `sftShiftMap M` has a point with dense forward orbit for the `PiNat` ultrametric. This
is the dense-orbit hypothesis consumed by `livsic_sft`; the safe-symbol hypothesis is the only place
any irreducibility-type assumption enters. -/
theorem exists_denseRange_sftShiftMap_orbit :
    ∃ x₀ : SFT M, DenseRange fun n : ℕ => (sftShiftMap M)^[n] x₀ := by
  refine ⟨sftRichPoint M, ?_⟩
  rw [Metric.denseRange_iff]
  intro z r hr
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < r := exists_pow_lt_of_lt_one hr (by norm_num)
  obtain ⟨n, hn⟩ := exists_shiftMap_agree (M := M) z N
  refine ⟨n, ?_⟩
  change dist z ((sftShiftMap M)^[n] (sftRichPoint M)) < r
  rw [Subtype.dist_eq, coe_sftShiftMap_iterate]
  change dist (z : Shift (Fin k)) (shiftMap^[n] (sftRichPointFun M)) < r
  have hd : dist (z : Shift (Fin k)) (shiftMap^[n] (sftRichPointFun M)) ≤ (1 / 2 : ℝ) ^ N := by
    rw [← agree_iff_dist_le]
    intro i hi
    exact (hn i hi).symm
  exact lt_of_le_of_lt hd hN

end

/-! ### The golden-mean shift -/

/-- The **golden-mean shift** transition matrix on `Fin 2`: forbid the block `11`, allow everything
else. (Lind–Marcus, §1.2.) -/
def goldenMeanM : Fin 2 → Fin 2 → Bool := fun a b => !(decide (a = 1) && decide (b = 1))

/-- `0` is a safe symbol of the golden-mean shift: it forbids nothing, so it may both follow and
precede every symbol. -/
instance : SafeSymbol goldenMeanM where
  s := 0
  safe_from := by decide
  safe_to := by decide

/-- The golden-mean shift is a **proper** subshift: the all-ones sequence contains the forbidden
block `11` at index `0`, so it is not admissible. -/
theorem goldenMean_proper : (fun _ => (1 : Fin 2)) ∉ SFTCarrier goldenMeanM := by
  intro h
  exact absurd (h 0) (by decide)

/-- **Livšic for the golden-mean shift (unconditional).** A Hölder observable `φ` (exponent
`0 < r ≤ 1`) on the golden-mean SFT is a Hölder coboundary iff all of its periodic Birkhoff sums
vanish. The closing property needed no irreducibility (`SubshiftFiniteType`, the `δ = 1/2` trick);
the safe symbol `0` pays only for the dense orbit `exists_denseRange_sftShiftMap_orbit`. -/
theorem livsic_goldenMean {C r : ℝ≥0} {φ : SFT goldenMeanM → ℝ}
    (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsHolderCoboundary (sftShiftMap goldenMeanM) φ ↔
      HasVanishingPeriodicSums (sftShiftMap goldenMeanM) φ := by
  obtain ⟨x₀, hx₀⟩ := exists_denseRange_sftShiftMap_orbit (M := goldenMeanM)
  exact livsic_sft hφ hr0 hr1 hx₀

end ErgodicTheory
