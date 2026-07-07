/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.SymbolicDimension
import Mathlib.Logic.Equiv.List
import Mathlib.Data.List.GetD
import Mathlib.Topology.MetricSpace.Holder

/-!
# A dense shift orbit and non-vacuity witnesses for the full-shift Livšic instance

This file supplies two structural ingredients for the full-shift instance of the Livšic
cohomology theorem (issue #29), both phrased on the one-sided full shift
`Shift α₀ := ∀ _ : ℕ, α₀` with Mathlib's `PiNat` ultrametric
(`dist x y = (1/2) ^ firstDiff x y`), following
`ErgodicTheory.Multifractal.SymbolicDimension`.

## Part A — a dense forward orbit

Over any **nonempty, encodable** alphabet `α₀` (in particular `Fin m` with `NeZero m`), there is a
point whose forward `shiftMap`-orbit is dense:

* `ErgodicTheory.Livsic.exists_denseRange_shiftMap_orbit_alphabet` (general alphabet),
* `ErgodicTheory.Livsic.exists_denseRange_shiftMap_orbit` (the `Fin m` instance).

The witness `richPoint α₀` is the concatenation of *all* finite words (enumerated via
`Encodable.decode`), each padded with one dummy symbol so that every block is nonempty. Every
target word of length `N` appears as the length-`N` prefix of its own block, so the orbit visits
every `PiNat` cylinder; the ultrametric cylinder ↔ closed-ball dictionary then upgrades
cylinder-visiting to metric density.

## Part B — non-vacuity witnesses on `Shift (Fin 2)`

* `holder_phi` : the locally constant `φ x = if x 0 = 0 then 0 else 1` is `HolderWith 1 1`
  (indeed `1`-Lipschitz for the `PiNat` distance) — an *obstruction* witness: it has a nonzero
  periodic sum at the fixed point `fun _ => 1` (`phi_apply_const_one`), so via the trivial
  direction of Livšic it is **not** a coboundary.
* `psi_eq_coboundary` / `psi_periodicSum_zero` : `ψ := φ ∘ shiftMap − φ` is, by construction, a
  coboundary with Hölder transfer function — a *positive* witness.

## References

* A. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972).
* T. Downarowicz, *Entropy in Dynamical Systems*, Cambridge Univ. Press (2011).
-/

open ErgodicTheory.Multifractal Function Set

attribute [local instance] PiNat.metricSpace

namespace ErgodicTheory.Livsic

noncomputable section

/-! ### Part A — a dense forward orbit -/

variable (α₀ : Type*) [Nonempty α₀] [Encodable α₀]

/-- A fixed dummy symbol of the (nonempty) alphabet, used to pad every enumerated word. -/
def dummy : α₀ := Classical.arbitrary α₀

/-- The `k`-th building block: the `k`-th list under the (countable) encoding of `List α₀`
(`decode`, defaulting to `[]` off-range), padded with one dummy symbol so the block is nonempty. -/
def word (k : ℕ) : List α₀ := (Encodable.decode (α := List α₀) k).getD [] ++ [dummy α₀]

/-- Every block is nonempty (length `≥ 1`), thanks to the appended dummy symbol. -/
theorem word_length_pos (k : ℕ) : 1 ≤ (word α₀ k).length := by
  simp only [word, List.length_append, List.length_singleton]; omega

/-- The prefix obtained by concatenating the first `k` blocks. -/
def prefixList : ℕ → List α₀
  | 0 => []
  | k + 1 => prefixList k ++ word α₀ k

/-- Unfolding lemma for the successor step of `prefixList`. -/
theorem prefixList_succ (k : ℕ) : prefixList α₀ (k + 1) = prefixList α₀ k ++ word α₀ k := rfl

/-- The `k`-th prefix has length at least `k` (each of the `k` blocks contributes `≥ 1`). -/
theorem prefixList_length_ge (k : ℕ) : k ≤ (prefixList α₀ k).length := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hpos := word_length_pos α₀ k
    rw [prefixList_succ, List.length_append]
    omega

/-- The prefixes are nested: `prefixList α₀ a` is a list-prefix of `prefixList α₀ b` for `a ≤ b`. -/
theorem prefixList_prefix {a b : ℕ} (h : a ≤ b) :
    prefixList α₀ a <+: prefixList α₀ b := by
  induction b, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m _ ih => exact ih.trans ⟨word α₀ m, rfl⟩

/-- `getD` is stable along the prefix chain: reading position `n < |prefixList α₀ a|` gives the
same value in every later prefix. -/
theorem getD_prefixList_of_le {a b n : ℕ} (hab : a ≤ b)
    (hn : n < (prefixList α₀ a).length) :
    (prefixList α₀ b).getD n (dummy α₀) = (prefixList α₀ a).getD n (dummy α₀) := by
  obtain ⟨t, ht⟩ := prefixList_prefix α₀ hab
  rw [← ht, List.getD_append _ _ _ _ hn]

/-- The base point of the dense orbit: the concatenation of *all* padded words, read coordinatewise
via the prefixes. Position `n` is read from `prefixList α₀ (n+1)`, which is long enough since
prefixes grow by at least one per block. -/
def richPoint : Shift α₀ := fun n => (prefixList α₀ (n + 1)).getD n (dummy α₀)

/-- Canonical form: `richPoint α₀ n` may be read off *any* prefix long enough to contain
position `n`. -/
theorem richPoint_eq {k n : ℕ} (hn : n < (prefixList α₀ k).length) :
    richPoint α₀ n = (prefixList α₀ k).getD n (dummy α₀) := by
  have h1 : n < (prefixList α₀ (n + 1)).length :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (prefixList_length_ge α₀ (n + 1))
  have e1 : (prefixList α₀ (max (n + 1) k)).getD n (dummy α₀)
      = (prefixList α₀ (n + 1)).getD n (dummy α₀) :=
    getD_prefixList_of_le α₀ (le_max_left _ _) h1
  have e2 : (prefixList α₀ (max (n + 1) k)).getD n (dummy α₀)
      = (prefixList α₀ k).getD n (dummy α₀) :=
    getD_prefixList_of_le α₀ (le_max_right _ _) hn
  have hdef : richPoint α₀ n = (prefixList α₀ (n + 1)).getD n (dummy α₀) := rfl
  rw [hdef, ← e1, e2]

/-- **Block appearance.** Block `k` sits verbatim in `richPoint α₀` starting at position
`|prefixList α₀ k|`: reading offset `i` there returns the `i`-th symbol of `word α₀ k`. -/
theorem richPoint_block (k i : ℕ) (hi : i < (word α₀ k).length) :
    richPoint α₀ ((prefixList α₀ k).length + i) = (word α₀ k).getD i (dummy α₀) := by
  have hlt : (prefixList α₀ k).length + i < (prefixList α₀ (k + 1)).length := by
    rw [prefixList_succ, List.length_append]; omega
  rw [richPoint_eq α₀ hlt, prefixList_succ,
    List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- **Cylinder visiting.** For every target sequence `z` and every length `N`, some forward iterate
of `richPoint α₀` lies in the length-`N` `PiNat` cylinder around `z`: the word `z₀ … z_{N-1}`
appears in `richPoint α₀` (as the prefix of its own block). -/
theorem exists_orbit_mem_cylinder (z : Shift α₀) (N : ℕ) :
    ∃ n, shiftMap^[n] (richPoint α₀) ∈ PiNat.cylinder z N := by
  set w : List α₀ := List.ofFn (fun i : Fin N => z (i : ℕ)) with hw
  have hwlen : w.length = N := by rw [hw]; simp
  obtain ⟨k, hk⟩ : ∃ k, (Encodable.decode (α := List α₀) k).getD [] = w :=
    ⟨Encodable.encode w, by rw [Encodable.encodek]; rfl⟩
  refine ⟨(prefixList α₀ k).length, ?_⟩
  rw [PiNat.mem_cylinder_iff]
  intro i hi
  rw [shiftMap_iterate_apply, Nat.add_comm i (prefixList α₀ k).length]
  have hi_word : i < (word α₀ k).length := by
    simp only [word, hk, List.length_append, hwlen, List.length_singleton]; omega
  rw [richPoint_block α₀ k i hi_word]
  simp only [word, hk]
  have hiw : i < w.length := by rw [hwlen]; exact hi
  rw [List.getD_append _ _ _ _ hiw, List.getD_eq_getElem _ _ hiw]
  simp only [hw, List.getElem_ofFn]

variable [TopologicalSpace α₀] [DiscreteTopology α₀]

/-- **Dense orbit (general alphabet).** Over any nonempty encodable alphabet, the full shift has a
point with dense forward orbit for the `PiNat` ultrametric. -/
theorem exists_denseRange_shiftMap_orbit_alphabet :
    ∃ x : Shift α₀, DenseRange (fun n => shiftMap^[n] x) := by
  refine ⟨richPoint α₀, ?_⟩
  rw [Metric.denseRange_iff]
  intro z r hr
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < r := exists_pow_lt_of_lt_one hr (by norm_num)
  obtain ⟨n, hn⟩ := exists_orbit_mem_cylinder α₀ z N
  refine ⟨n, ?_⟩
  have hd : dist (shiftMap^[n] (richPoint α₀)) z ≤ (1 / 2) ^ N :=
    PiNat.mem_cylinder_iff_dist_le.mp hn
  rw [dist_comm] at hd
  exact lt_of_le_of_lt hd hN

/-- **Dense orbit (`Fin m`).** The full shift on `m` symbols (`m ≠ 0`) has a point whose forward
`shiftMap`-orbit is dense. This is the full-shift dense-orbit hypothesis needed by the Livšic
instance. -/
theorem exists_denseRange_shiftMap_orbit (m : ℕ) [NeZero m] :
    ∃ x : Shift (Fin m), DenseRange (fun n => shiftMap^[n] x) :=
  exists_denseRange_shiftMap_orbit_alphabet (Fin m)

/-! ### Part B — non-vacuity witnesses on `Shift (Fin 2)` -/

/-- A locally constant (time-`0`) potential on the binary full shift. -/
def phi : Shift (Fin 2) → ℝ := fun x => if x 0 = 0 then 0 else 1

/-- `φ` is `HolderWith 1 1` — indeed `1`-Lipschitz for the `PiNat` distance. A locally constant
function is Hölder because points sharing coordinate `0` have equal `φ`, while points differing at
coordinate `0` are at distance exactly `1`. -/
theorem holder_phi : HolderWith 1 1 phi := by
  rw [holderWith_one]
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [NNReal.coe_one, one_mul]
  have hb : ∀ z : Shift (Fin 2), phi z = 0 ∨ phi z = 1 := fun z => by
    unfold phi; split <;> simp
  rcases eq_or_ne (x 0) (y 0) with h | h
  · have hpe : phi x = phi y := by unfold phi; rw [h]
    rw [hpe, dist_self]
    exact dist_nonneg
  · have hxy : x ≠ y := fun hh => h (by rw [hh])
    have hfd : PiNat.firstDiff x y = 0 := by
      by_contra hne
      exact h (PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hne))
    have hdist : dist x y = 1 := by
      rw [PiNat.dist_eq_of_ne hxy, hfd]; norm_num
    rw [hdist, Real.dist_eq]
    rcases hb x with hx | hx <;> rcases hb y with hy | hy <;> rw [hx, hy] <;> norm_num

/-- The constant-`1` sequence is a fixed point of the shift (a period-`1` periodic point). -/
theorem shift_const_fixed : shiftMap (fun _ => (1 : Fin 2)) = (fun _ => (1 : Fin 2)) := rfl

/-- The value of `φ` at the shift fixed point `fun _ => 1` is `1`. Since this is the period-`1`
Birkhoff sum of `φ` there, and it is `≠ 0`, the trivial direction of Livšic (a coboundary has zero
periodic sums) exhibits `φ` as a **non-coboundary** — the obstruction witness. -/
theorem phi_apply_const_one : phi (fun _ => (1 : Fin 2)) = 1 := by
  simp only [phi]
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

/-- The coboundary built from the Hölder transfer function `φ`: `ψ := φ ∘ shiftMap − φ`. -/
def psi : Shift (Fin 2) → ℝ := fun x => phi (shiftMap x) - phi x

/-- `ψ` is, by construction, a coboundary with `φ` (`HolderWith 1 1`, `holder_phi`) as transfer
function — the positive (non-vacuity) witness. -/
theorem psi_eq_coboundary (x : Shift (Fin 2)) : psi x = phi (shiftMap x) - phi x := rfl

/-- Consistency check: the coboundary `ψ` has vanishing periodic sum at the fixed point, as Livšic
demands of any coboundary. -/
theorem psi_periodicSum_zero : psi (fun _ => (1 : Fin 2)) = 0 := by
  rw [psi_eq_coboundary, shift_const_fixed, sub_self]

end

end ErgodicTheory.Livsic
