/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.MeanInequalitiesPow
import ErgodicTheory.Multifractal.Defs

/-!
# Rényi entropy of a finite weight family: the static data-processing inequality

For a finite weight family `p : ι → ℝ` (`0 ≤ p i`), the **Rényi entropy of order `q`** is
`H_q(p) = (1 - q)⁻¹ · log Z_q(p)`, where `Z_q(p) = ∑_{p i > 0} (p i) ^ q` is the generalized
partition function already introduced in `ErgodicTheory/Multifractal/Defs.lean`
(`partitionFunction`; the guard `0 < p i` is load-bearing at `q = 0`, where `Z_0` counts the
occupied cells). We reuse `partitionFunction` verbatim — it *is* the power sum `∑ p_i^q` — rather
than redefine it.

This file proves the **static data-processing inequality (DPI)** for Rényi entropy: coarse-graining
a weight family by a merge map `f : ι → κ` — pushing the family forward to the sums over the fibers
of `f` — can only *decrease* the Rényi entropy, for every order `q ∈ [0, 1) ∪ (1, ∞)`. The engine is
the per-fiber super/subadditivity of `x ↦ x^q`:

* for `q ≥ 1`: `∑_{a ∈ fiber} (p a)^q ≤ (∑_{a ∈ fiber} p a)^q` (superadditivity), so `Z_q` *grows*
  under merge, and the negative prefactor `(1-q)⁻¹ < 0` flips this to a *drop* in `H_q`;
* for `0 ≤ q ≤ 1`: `(∑_{a ∈ fiber} p a)^q ≤ ∑_{a ∈ fiber} (p a)^q` (subadditivity), so `Z_q`
  *shrinks*, and the positive prefactor `(1-q)⁻¹ > 0` again gives a drop in `H_q`.

The two-element super/subadditivity is `Real.add_rpow_le_rpow_add` (for `q ≥ 1`) and
`Real.rpow_add_le_add_rpow` (for `0 ≤ q ≤ 1`) from Mathlib; the finite-fiber versions are proved
here by `Finset.induction`. The strict two-point inequalities (`x, y > 0`) are proved elementarily
from the strict monotonicity of `rpow` in the base, giving a strict entropy drop whenever the merge
glues two atoms of the support.

## Main definitions

* `ErgodicTheory.Multifractal.mergedWeights`: the pushforward `κ → ℝ` of `p : ι → ℝ` along a merge
  `f : ι → κ`, summing each fiber.
* `ErgodicTheory.Multifractal.renyiEntropy`: the Rényi entropy `H_q(p) = (1-q)⁻¹ · log Z_q(p)`.

## Main results

* `ErgodicTheory.Multifractal.partitionFunction_merge_ge` / `partitionFunction_merge_le`: the
  power-sum super/subadditivity under merge, for `q ≥ 1` and `0 ≤ q ≤ 1` respectively.
* `ErgodicTheory.Multifractal.renyiEntropy_merge_le`: the **static DPI** — `H_q` is non-increasing
  under a merge, for every `0 ≤ q`, `q ≠ 1`.
* `ErgodicTheory.Multifractal.renyiEntropy_merge_lt`: the strict version — a merge that glues two
  support atoms strictly decreases `H_q`, for `q ∈ (0,1) ∪ (1,∞)`.

## References

* A. Rényi, *On measures of entropy and information*, Proc. 4th Berkeley Symp. (1961).
* T. van Erven and P. Harremoës, *Rényi divergence and Kullback–Leibler divergence*, IEEE Trans.
  Inform. Theory 60 (2014), no. 7.
-/

open Real

namespace ErgodicTheory.Multifractal

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-! ### Finite super/subadditivity of `x ↦ x ^ q` -/

/-- **Finite superadditivity** of `x ↦ x^q` for `q ≥ 1`: over a finite index set, the sum of the
`q`-powers is at most the `q`-power of the sum. Proved by induction from the two-term case
`Real.add_rpow_le_rpow_add`. -/
private lemma sum_rpow_le_rpow_sum {ι' : Type*} (s : Finset ι') {f : ι' → ℝ}
    (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq : 1 ≤ q) :
    ∑ a ∈ s, f a ^ q ≤ (∑ a ∈ s, f a) ^ q := by
  classical
  induction s using Finset.induction with
  | empty => simp [Real.zero_rpow (by linarith : q ≠ 0)]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hsum_nonneg : 0 ≤ ∑ b ∈ s, f b := Finset.sum_nonneg (fun b _ => hf b)
    calc f a ^ q + ∑ b ∈ s, f b ^ q
        ≤ f a ^ q + (∑ b ∈ s, f b) ^ q := by linarith [ih]
      _ ≤ (f a + ∑ b ∈ s, f b) ^ q := Real.add_rpow_le_rpow_add (hf a) hsum_nonneg hq

/-- **Finite subadditivity** of `x ↦ x^q` for `0 < q ≤ 1`: over a finite index set, the `q`-power of
the sum is at most the sum of the `q`-powers. Proved by induction from the two-term case
`Real.rpow_add_le_add_rpow`. -/
private lemma rpow_sum_le_sum_rpow {ι' : Type*} (s : Finset ι') {f : ι' → ℝ}
    (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ a ∈ s, f a) ^ q ≤ ∑ a ∈ s, f a ^ q := by
  classical
  induction s using Finset.induction with
  | empty => simp [Real.zero_rpow (ne_of_gt hq0)]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hsum_nonneg : 0 ≤ ∑ b ∈ s, f b := Finset.sum_nonneg (fun b _ => hf b)
    calc (f a + ∑ b ∈ s, f b) ^ q
        ≤ f a ^ q + (∑ b ∈ s, f b) ^ q :=
          Real.rpow_add_le_add_rpow (hf a) hsum_nonneg (le_of_lt hq0) hq1
      _ ≤ f a ^ q + ∑ b ∈ s, f b ^ q := by linarith [ih]

/-- The guard `if 0 < f a then (f a)^q else 0` is removable for `q ≠ 0`, since empty cells give
`(0)^q = 0` anyway: `∑ a ∈ s, (if 0 < f a then (f a)^q else 0) = ∑ a ∈ s, (f a)^q`. -/
private lemma sum_guard_eq_sum_rpow {ι' : Type*} (s : Finset ι') {f : ι' → ℝ}
    (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq : q ≠ 0) :
    (∑ a ∈ s, if 0 < f a then f a ^ q else 0) = ∑ a ∈ s, f a ^ q := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split
  · rfl
  · rename_i hlt
    rw [le_antisymm (not_lt.1 hlt) (hf a), Real.zero_rpow hq]

/-- The guarded summand `if 0 < f a then (f a)^q else 0` is nonnegative. -/
private lemma guard_nonneg {ι' : Type*} {f : ι' → ℝ} (hf : ∀ a, 0 ≤ f a) (q : ℝ) (a : ι') :
    0 ≤ if 0 < f a then f a ^ q else 0 := by
  split
  · exact Real.rpow_nonneg (hf a) q
  · exact le_refl 0

/-- **Strict two-term superadditivity** for `q > 1`: for `x, y > 0`, `x^q + y^q < (x+y)^q`.
Writing `x^q = x^{q-1}·x` and using `x^{q-1} < (x+y)^{q-1}` (strict monotonicity of `rpow` in the
base at the positive exponent `q-1`), each term is strictly dominated. -/
private lemma add_rpow_lt_rpow_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {q : ℝ} (hq : 1 < q) :
    x ^ q + y ^ q < (x + y) ^ q := by
  have hxy : 0 < x + y := by linarith
  have hqn : (0 : ℝ) < q - 1 := by linarith
  have hltx : x ^ (q - 1) < (x + y) ^ (q - 1) :=
    Real.rpow_lt_rpow (le_of_lt hx) (by linarith) hqn
  have hlty : y ^ (q - 1) < (x + y) ^ (q - 1) :=
    Real.rpow_lt_rpow (le_of_lt hy) (by linarith) hqn
  have ex : x ^ q = x ^ (q - 1) * x := by rw [← Real.rpow_add_one hx.ne']; congr 1; ring
  have ey : y ^ q = y ^ (q - 1) * y := by rw [← Real.rpow_add_one hy.ne']; congr 1; ring
  have exy : (x + y) ^ q = (x + y) ^ (q - 1) * (x + y) := by
    rw [← Real.rpow_add_one hxy.ne']; congr 1; ring
  rw [ex, ey, exy, mul_add]
  have h1 : x ^ (q - 1) * x < (x + y) ^ (q - 1) * x := mul_lt_mul_of_pos_right hltx hx
  have h2 : y ^ (q - 1) * y < (x + y) ^ (q - 1) * y := mul_lt_mul_of_pos_right hlty hy
  linarith

/-- **Strict two-term subadditivity** for `0 < q < 1`: for `x, y > 0`, `(x+y)^q < x^q + y^q`. Same
route as `add_rpow_lt_rpow_add`, now with the *negative* exponent `q-1`, where the base monotonicity
of `rpow` reverses (`Real.rpow_lt_rpow_of_neg`). -/
private lemma rpow_add_lt_add_rpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {q : ℝ}
    (hq1 : q < 1) : (x + y) ^ q < x ^ q + y ^ q := by
  have hxy : 0 < x + y := by linarith
  have hqn : q - 1 < 0 := by linarith
  have hltx : (x + y) ^ (q - 1) < x ^ (q - 1) :=
    Real.rpow_lt_rpow_of_neg hx (by linarith) hqn
  have hlty : (x + y) ^ (q - 1) < y ^ (q - 1) :=
    Real.rpow_lt_rpow_of_neg hy (by linarith) hqn
  have ex : x ^ q = x ^ (q - 1) * x := by rw [← Real.rpow_add_one hx.ne']; congr 1; ring
  have ey : y ^ q = y ^ (q - 1) * y := by rw [← Real.rpow_add_one hy.ne']; congr 1; ring
  have exy : (x + y) ^ q = (x + y) ^ (q - 1) * (x + y) := by
    rw [← Real.rpow_add_one hxy.ne']; congr 1; ring
  rw [ex, ey, exy, mul_add]
  have h1 : (x + y) ^ (q - 1) * x < x ^ (q - 1) * x := mul_lt_mul_of_pos_right hltx hx
  have h2 : (x + y) ^ (q - 1) * y < y ^ (q - 1) * y := mul_lt_mul_of_pos_right hlty hy
  linarith

/-- **Strict finite superadditivity** (`q > 1`): if `s` contains two distinct indices `i ≠ j` with
`f i, f j > 0`, then `∑_{a ∈ s} (f a)^q < (∑_{a ∈ s} f a)^q`. Split off `i`; the tail sum is
positive (it contains `j`), so the two-term strict inequality applies. -/
private lemma sum_rpow_lt_rpow_sum {ι' : Type*} (s : Finset ι') {f : ι' → ℝ} (hf : ∀ a, 0 ≤ f a)
    {q : ℝ} (hq : 1 < q) {i j : ι'} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hfi : 0 < f i) (hfj : 0 < f j) :
    ∑ a ∈ s, f a ^ q < (∑ a ∈ s, f a) ^ q := by
  classical
  have hjd : j ∈ s.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hrest_pos : 0 < ∑ a ∈ s.erase i, f a := Finset.sum_pos' (fun a _ => hf a) ⟨j, hjd, hfj⟩
  have hsplit_q : ∑ a ∈ s, f a ^ q = f i ^ q + ∑ a ∈ s.erase i, f a ^ q := by
    rw [← Finset.add_sum_erase s _ hi]
  have hsplit : ∑ a ∈ s, f a = f i + ∑ a ∈ s.erase i, f a := by rw [← Finset.add_sum_erase s _ hi]
  rw [hsplit_q, hsplit]
  have hle : ∑ a ∈ s.erase i, f a ^ q ≤ (∑ a ∈ s.erase i, f a) ^ q :=
    sum_rpow_le_rpow_sum (s.erase i) hf hq.le
  have hlt : f i ^ q + (∑ a ∈ s.erase i, f a) ^ q < (f i + ∑ a ∈ s.erase i, f a) ^ q :=
    add_rpow_lt_rpow_add hfi hrest_pos hq
  linarith

/-- **Strict finite subadditivity** (`0 < q < 1`): if `s` contains two distinct indices `i ≠ j` with
`f i, f j > 0`, then `(∑_{a ∈ s} f a)^q < ∑_{a ∈ s} (f a)^q`. -/
private lemma rpow_sum_lt_sum_rpow {ι' : Type*} (s : Finset ι') {f : ι' → ℝ} (hf : ∀ a, 0 ≤ f a)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {i j : ι'} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hfi : 0 < f i) (hfj : 0 < f j) :
    (∑ a ∈ s, f a) ^ q < ∑ a ∈ s, f a ^ q := by
  classical
  have hjd : j ∈ s.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hrest_pos : 0 < ∑ a ∈ s.erase i, f a := Finset.sum_pos' (fun a _ => hf a) ⟨j, hjd, hfj⟩
  have hsplit_q : ∑ a ∈ s, f a ^ q = f i ^ q + ∑ a ∈ s.erase i, f a ^ q := by
    rw [← Finset.add_sum_erase s _ hi]
  have hsplit : ∑ a ∈ s, f a = f i + ∑ a ∈ s.erase i, f a := by rw [← Finset.add_sum_erase s _ hi]
  rw [hsplit_q, hsplit]
  have hge : (∑ a ∈ s.erase i, f a) ^ q ≤ ∑ a ∈ s.erase i, f a ^ q :=
    rpow_sum_le_sum_rpow (s.erase i) hf hq0 hq1.le
  have hlt : (f i + ∑ a ∈ s.erase i, f a) ^ q < f i ^ q + (∑ a ∈ s.erase i, f a) ^ q :=
    rpow_add_lt_add_rpow hfi hrest_pos hq1
  linarith

/-! ### The merged weight family -/

/-- The **merged weight family** `mergedWeights f p : κ → ℝ` obtained by pushing `p : ι → ℝ` forward
along a merge map `f : ι → κ`: each `b : κ` receives the total mass of its fiber,
`mergedWeights f p b = ∑_{a : f a = b} p a`. -/
noncomputable def mergedWeights (f : ι → κ) (p : ι → ℝ) : κ → ℝ :=
  fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), p a

omit [Fintype κ] in
/-- The merged family inherits nonnegativity. -/
lemma mergedWeights_nonneg (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a) (b : κ) :
    0 ≤ mergedWeights f p b :=
  Finset.sum_nonneg (fun a _ => hp a)

/-- The merge preserves the total mass: `∑_b mergedWeights f p b = ∑_a p a`. -/
lemma sum_mergedWeights (f : ι → κ) (p : ι → ℝ) :
    ∑ b, mergedWeights f p b = ∑ a, p a := by
  rw [← Finset.sum_fiberwise Finset.univ f p]
  rfl

omit [Fintype κ] in
/-- If some atom `i` has `p i > 0`, then its image fiber has positive merged mass. -/
lemma mergedWeights_pos_of_pos (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a) {i : ι}
    (hi : 0 < p i) : 0 < mergedWeights f p (f i) := by
  simp only [mergedWeights]
  exact Finset.sum_pos' (fun a _ => hp a) ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩, hi⟩

/-! ### Per-fiber comparisons -/

/-- Per-fiber superadditivity (`q ≥ 1`): the guarded power sum over a fiber is at most the guarded
`q`-power of the fiber total. -/
private lemma partitionFunction_fiber_ge {ι' : Type*} (s : Finset ι') {f : ι' → ℝ}
    (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq : 1 ≤ q) :
    (∑ a ∈ s, if 0 < f a then f a ^ q else 0)
      ≤ (if 0 < ∑ a ∈ s, f a then (∑ a ∈ s, f a) ^ q else 0) := by
  by_cases h : 0 < ∑ a ∈ s, f a
  · rw [if_pos h, sum_guard_eq_sum_rpow s hf (by linarith : q ≠ 0)]
    exact sum_rpow_le_rpow_sum s hf hq
  · rw [if_neg h]
    have hS : ∑ a ∈ s, f a = 0 :=
      le_antisymm (not_lt.1 h) (Finset.sum_nonneg (fun a _ => hf a))
    refine le_of_eq (Finset.sum_eq_zero (fun a ha => ?_))
    have hfa : f a = 0 := by
      have hle : f a ≤ ∑ b ∈ s, f b := Finset.single_le_sum (fun b _ => hf b) ha
      linarith [hf a]
    simp [hfa]

/-- Per-fiber subadditivity (`0 ≤ q ≤ 1`): the guarded `q`-power of the fiber total is at most the
guarded power sum over the fiber. The `q = 0` corner is handled by counting the occupied cells. -/
private lemma partitionFunction_fiber_le {ι' : Type*} (s : Finset ι') {f : ι' → ℝ}
    (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (if 0 < ∑ a ∈ s, f a then (∑ a ∈ s, f a) ^ q else 0)
      ≤ (∑ a ∈ s, if 0 < f a then f a ^ q else 0) := by
  by_cases h : 0 < ∑ a ∈ s, f a
  · rw [if_pos h]
    rcases eq_or_lt_of_le hq0 with hq0' | hq0'
    · -- q = 0 : both sides count occupied cells
      obtain rfl := hq0'
      rw [Real.rpow_zero]
      obtain ⟨a₀, ha₀s, ha₀⟩ : ∃ a ∈ s, 0 < f a := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        have hz : ∑ a ∈ s, f a = 0 :=
          Finset.sum_eq_zero (fun a ha => le_antisymm (hcon a ha) (hf a))
        rw [hz] at h; exact lt_irrefl 0 h
      have hone : (if 0 < f a₀ then f a₀ ^ (0 : ℝ) else 0) = 1 := by
        rw [if_pos ha₀, Real.rpow_zero]
      calc (1 : ℝ) = (if 0 < f a₀ then f a₀ ^ (0 : ℝ) else 0) := hone.symm
        _ ≤ ∑ a ∈ s, if 0 < f a then f a ^ (0 : ℝ) else 0 :=
            Finset.single_le_sum (fun a _ => guard_nonneg hf 0 a) ha₀s
    · -- 0 < q ≤ 1
      rw [sum_guard_eq_sum_rpow s hf (ne_of_gt hq0')]
      exact rpow_sum_le_sum_rpow s hf hq0' hq1
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun a _ => guard_nonneg hf q a)

/-- Per-fiber strict superadditivity (`q > 1`) when the fiber has two distinct positive atoms. -/
private lemma partitionFunction_fiber_gt {ι' : Type*} (s : Finset ι') {f : ι' → ℝ}
    (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq : 1 < q) {i j : ι'} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hfi : 0 < f i) (hfj : 0 < f j) :
    (∑ a ∈ s, if 0 < f a then f a ^ q else 0)
      < (if 0 < ∑ a ∈ s, f a then (∑ a ∈ s, f a) ^ q else 0) := by
  have hSpos : 0 < ∑ a ∈ s, f a := Finset.sum_pos' (fun a _ => hf a) ⟨i, hi, hfi⟩
  rw [if_pos hSpos, sum_guard_eq_sum_rpow s hf (by linarith : q ≠ 0)]
  exact sum_rpow_lt_rpow_sum s hf hq hi hj hij hfi hfj

/-- Per-fiber strict subadditivity (`0 < q < 1`) when the fiber carries two distinct positive
atoms. -/
private lemma partitionFunction_fiber_lt {ι' : Type*} (s : Finset ι') {f : ι' → ℝ}
    (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {i j : ι'} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) (hfi : 0 < f i) (hfj : 0 < f j) :
    (if 0 < ∑ a ∈ s, f a then (∑ a ∈ s, f a) ^ q else 0)
      < (∑ a ∈ s, if 0 < f a then f a ^ q else 0) := by
  have hSpos : 0 < ∑ a ∈ s, f a := Finset.sum_pos' (fun a _ => hf a) ⟨i, hi, hfi⟩
  rw [if_pos hSpos, sum_guard_eq_sum_rpow s hf (ne_of_gt hq0)]
  exact rpow_sum_lt_sum_rpow s hf hq0 hq1 hi hj hij hfi hfj

/-! ### The power-sum inequalities under merge -/

/-- **Power-sum superadditivity under merge** (`q ≥ 1`): merging cells can only increase the
partition function `Z_q`. Regroup `Z_q(p)` by the fibers of `f` (`Finset.sum_fiberwise`) and apply
the per-fiber superadditivity. -/
theorem partitionFunction_merge_ge (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a) {q : ℝ}
    (hq : 1 ≤ q) : partitionFunction p q ≤ partitionFunction (mergedWeights f p) q := by
  rw [partitionFunction, partitionFunction,
    ← Finset.sum_fiberwise Finset.univ f (fun a => if 0 < p a then p a ^ q else 0)]
  refine Finset.sum_le_sum (fun b _ => ?_)
  simp only [mergedWeights]
  exact partitionFunction_fiber_ge _ hp hq

/-- **Power-sum subadditivity under merge** (`0 ≤ q ≤ 1`): merging cells can only decrease the
partition function `Z_q`. -/
theorem partitionFunction_merge_le (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    partitionFunction (mergedWeights f p) q ≤ partitionFunction p q := by
  rw [partitionFunction, partitionFunction,
    ← Finset.sum_fiberwise Finset.univ f (fun a => if 0 < p a then p a ^ q else 0)]
  refine Finset.sum_le_sum (fun b _ => ?_)
  simp only [mergedWeights]
  exact partitionFunction_fiber_le _ hp hq0 hq1

/-- **Strict power-sum superadditivity under merge** (`q > 1`): if the merge `f` glues two distinct
support atoms `i ≠ j` (`p i, p j > 0`, `f i = f j`), then `Z_q` strictly increases. -/
theorem partitionFunction_merge_gt (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a) {q : ℝ}
    (hq : 1 < q) {i j : ι} (hij : i ≠ j) (hfi : 0 < p i) (hfj : 0 < p j) (hf : f i = f j) :
    partitionFunction p q < partitionFunction (mergedWeights f p) q := by
  rw [partitionFunction, partitionFunction,
    ← Finset.sum_fiberwise Finset.univ f (fun a => if 0 < p a then p a ^ q else 0)]
  refine Finset.sum_lt_sum (fun b _ => ?_) ⟨f i, Finset.mem_univ _, ?_⟩
  · simp only [mergedWeights]
    exact partitionFunction_fiber_ge _ hp hq.le
  · simp only [mergedWeights]
    exact partitionFunction_fiber_gt _ hp hq
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hf.symm⟩) hij hfi hfj

/-- **Strict power-sum subadditivity under merge** (`0 < q < 1`): if the merge `f` glues two
distinct support atoms, then `Z_q` strictly decreases. -/
theorem partitionFunction_merge_lt (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) {i j : ι} (hij : i ≠ j) (hfi : 0 < p i) (hfj : 0 < p j)
    (hf : f i = f j) :
    partitionFunction (mergedWeights f p) q < partitionFunction p q := by
  rw [partitionFunction, partitionFunction,
    ← Finset.sum_fiberwise Finset.univ f (fun a => if 0 < p a then p a ^ q else 0)]
  refine Finset.sum_lt_sum (fun b _ => ?_) ⟨f i, Finset.mem_univ _, ?_⟩
  · simp only [mergedWeights]
    exact partitionFunction_fiber_le _ hp hq0.le hq1.le
  · simp only [mergedWeights]
    exact partitionFunction_fiber_lt _ hp hq0 hq1
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hf.symm⟩) hij hfi hfj

/-! ### The Rényi entropy and its data-processing inequality -/

/-- The **Rényi entropy of order `q`** of a finite weight family `p : ι → ℝ`:
`H_q(p) = (1 - q)⁻¹ · log Z_q(p)`, with `Z_q = partitionFunction p q` the generalized partition
function. This is a total function; at `q = 1` it evaluates to the junk value `0` (division by
zero returns `0` in Mathlib), the `q = 1` information-theoretic content being the
Shannon entropy `∑ i, negMulLog (p i)` supplied separately. -/
noncomputable def renyiEntropy (p : ι → ℝ) (q : ℝ) : ℝ :=
  (1 - q)⁻¹ * Real.log (partitionFunction p q)

/-- **Static data-processing inequality for Rényi entropy.** For every order `0 ≤ q`, `q ≠ 1`, a
merge `f : ι → κ` does not increase the Rényi entropy: `H_q(mergedWeights f p) ≤ H_q(p)`.

The sign dance: for `q > 1` the prefactor `(1-q)⁻¹ < 0` and `Z_q` increases under merge, so `H_q`
decreases; for `0 ≤ q < 1` the prefactor `(1-q)⁻¹ > 0` and `Z_q` decreases, so `H_q` again
decreases. The nondegeneracy `∃ i, 0 < p i` guarantees both partition functions are positive, so
`log` is monotone. -/
theorem renyiEntropy_merge_le (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpos : ∃ i, 0 < p i) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≠ 1) :
    renyiEntropy (mergedWeights f p) q ≤ renyiEntropy p q := by
  obtain ⟨i₀, hi₀⟩ := hpos
  have hZp : 0 < partitionFunction p q := partitionFunction_pos ⟨i₀, hi₀⟩ q
  have hZm : 0 < partitionFunction (mergedWeights f p) q :=
    partitionFunction_pos ⟨f i₀, mergedWeights_pos_of_pos f hp hi₀⟩ q
  rw [renyiEntropy, renyiEntropy]
  rcases lt_or_gt_of_ne hq1 with hlt | hgt
  · have hZle : partitionFunction (mergedWeights f p) q ≤ partitionFunction p q :=
      partitionFunction_merge_le f hp hq0 (le_of_lt hlt)
    have hlog := Real.log_le_log hZm hZle
    have hcpos : 0 < (1 - q)⁻¹ := inv_pos.mpr (by linarith)
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt hcpos)
  · have hZle : partitionFunction p q ≤ partitionFunction (mergedWeights f p) q :=
      partitionFunction_merge_ge f hp (le_of_lt hgt)
    have hlog := Real.log_le_log hZp hZle
    have hcneg : (1 - q)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
    exact mul_le_mul_of_nonpos_left hlog (le_of_lt hcneg)

/-- **Strict data-processing inequality for Rényi entropy.** For every order `q ∈ (0,1) ∪ (1,∞)`, if
the merge `f` glues two distinct support atoms `i ≠ j` (`p i, p j > 0`, `f i = f j`), then the Rényi
entropy strictly decreases: `H_q(mergedWeights f p) < H_q(p)`. This is the strictness half of the
equality characterization: for these orders, equality in the DPI holds iff `f` is injective on the
support. -/
theorem renyiEntropy_merge_lt (f : ι → κ) {p : ι → ℝ} (hp : ∀ a, 0 ≤ p a)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {i j : ι} (hij : i ≠ j) (hfi : 0 < p i) (hfj : 0 < p j)
    (hf : f i = f j) :
    renyiEntropy (mergedWeights f p) q < renyiEntropy p q := by
  have hZp : 0 < partitionFunction p q := partitionFunction_pos ⟨i, hfi⟩ q
  have hZm : 0 < partitionFunction (mergedWeights f p) q :=
    partitionFunction_pos ⟨f i, mergedWeights_pos_of_pos f hp hfi⟩ q
  rw [renyiEntropy, renyiEntropy]
  rcases lt_or_gt_of_ne hq1 with hlt | hgt
  · have hZlt := partitionFunction_merge_lt f hp hq0 hlt hij hfi hfj hf
    have hlog := Real.log_lt_log hZm hZlt
    have hcpos : 0 < (1 - q)⁻¹ := inv_pos.mpr (by linarith)
    exact mul_lt_mul_of_pos_left hlog hcpos
  · have hZgt := partitionFunction_merge_gt f hp hgt hij hfi hfj hf
    have hlog := Real.log_lt_log hZp hZgt
    have hcneg : (1 - q)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
    exact mul_lt_mul_of_neg_left hlog hcneg

/-! ### Bounds on the Rényi entropy of a probability weight family

The following bounds are the analytic input to the dynamical rate theorems
(`ErgodicTheory/Multifractal/RenyiRate.lean`): they make the per-length rate sequence bounded, so
its `limsup`/`liminf` are monotone under the per-length data-processing inequality. -/

/-- Each weight of a probability family is at most `1`. -/
private lemma le_one_of_sum_eq_one {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (i : ι) : p i ≤ 1 := by
  have := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  rwa [hsum] at this

/-- **Nonnegativity of the Rényi entropy** for a probability weight family, at every order
`0 ≤ q`, `q ≠ 1`. For `q < 1` the partition function satisfies `Z_q ≥ 1` (each `p_i^q ≥ p_i`) and
the prefactor `(1-q)⁻¹` is positive; for `q > 1` we have `Z_q ≤ 1` and the prefactor is negative, so
the product is nonnegative either way. -/
lemma renyiEntropy_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hpos : ∃ i, 0 < p i) {q : ℝ} (hq1 : q ≠ 1) : 0 ≤ renyiEntropy p q := by
  have hZpos : 0 < partitionFunction p q := partitionFunction_pos hpos q
  rw [renyiEntropy]
  rcases lt_or_gt_of_ne hq1 with hlt | hgt
  · have hZ1 : 1 ≤ partitionFunction p q := by
      rw [partitionFunction]
      calc (1 : ℝ) = ∑ i, p i := hsum.symm
        _ ≤ ∑ i, if 0 < p i then p i ^ q else 0 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            split
            · rename_i hpi
              calc p i = p i ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ p i ^ q := Real.rpow_le_rpow_of_exponent_ge hpi
                    (le_one_of_sum_eq_one hp hsum i) (le_of_lt hlt)
            · rename_i hpi
              rw [le_antisymm (not_lt.1 hpi) (hp i)]
    exact mul_nonneg (le_of_lt (inv_pos.mpr (by linarith))) (Real.log_nonneg hZ1)
  · have hZ1 : partitionFunction p q ≤ 1 := by
      rw [partitionFunction]
      calc ∑ i, (if 0 < p i then p i ^ q else 0) ≤ ∑ i, p i := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            split
            · rename_i hpi
              calc p i ^ q ≤ p i ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hpi
                    (le_one_of_sum_eq_one hp hsum i) (le_of_lt hgt)
                _ = p i := Real.rpow_one _
            · exact hp i
        _ = 1 := hsum
    have hc : (1 - q)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
    have hlogp : Real.log (partitionFunction p q) ≤ 0 := Real.log_nonpos (le_of_lt hZpos) hZ1
    have hprod := mul_nonneg (neg_nonneg.mpr (le_of_lt hc)) (neg_nonneg.mpr hlogp)
    rwa [neg_mul_neg] at hprod

/-- **Upper bound for `0 ≤ q < 1`.** Here `Z_q = ∑ p_i^q ≤ card ι` (each term is `≤ 1`), so
`H_q = (1-q)⁻¹ log Z_q ≤ (1-q)⁻¹ log (card ι)`. -/
lemma renyiEntropy_le_of_lt {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hpos : ∃ i, 0 < p i) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    renyiEntropy p q ≤ (1 - q)⁻¹ * Real.log (Fintype.card ι) := by
  have hZpos : 0 < partitionFunction p q := partitionFunction_pos hpos q
  have hZN : partitionFunction p q ≤ (Fintype.card ι : ℝ) := by
    rw [partitionFunction]
    calc ∑ i, (if 0 < p i then p i ^ q else 0) ≤ ∑ _i : ι, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          split
          · rename_i hpi
            exact Real.rpow_le_one (le_of_lt hpi) (le_one_of_sum_eq_one hp hsum i) hq0
          · exact zero_le_one
      _ = (Fintype.card ι : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [renyiEntropy]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hZpos hZN)
    (le_of_lt (inv_pos.mpr (by linarith)))

/-- **Upper bound for `q > 1`.** By pigeonhole some weight is at least `1 / card ι`, so
`Z_q ≥ (card ι)⁻¹ ^ q` and `log Z_q ≥ -q log (card ι)`; the negative prefactor `(1-q)⁻¹` then gives
`H_q ≤ (q / (q-1)) · log (card ι)`. -/
lemma renyiEntropy_le_of_gt {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hpos : ∃ i, 0 < p i) {q : ℝ} (hq : 1 < q) :
    renyiEntropy p q ≤ (q / (q - 1)) * Real.log (Fintype.card ι) := by
  obtain ⟨i₁, hi₁⟩ := hpos
  haveI : Nonempty ι := ⟨i₁⟩
  have hNpos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hZpos : 0 < partitionFunction p q := partitionFunction_pos ⟨i₁, hi₁⟩ q
  -- pigeonhole: some weight `≥ 1/card ι`
  obtain ⟨i₀, _, hi₀le⟩ : ∃ i ∈ Finset.univ, (Fintype.card ι : ℝ)⁻¹ ≤ p i := by
    refine Finset.exists_le_of_sum_le Finset.univ_nonempty ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum, mul_inv_cancel₀ (ne_of_gt hNpos)]
  have hpi0pos : 0 < p i₀ := lt_of_lt_of_le (inv_pos.mpr hNpos) hi₀le
  have hZge : (Fintype.card ι : ℝ)⁻¹ ^ q ≤ partitionFunction p q := by
    rw [partitionFunction]
    calc (Fintype.card ι : ℝ)⁻¹ ^ q
        ≤ p i₀ ^ q := Real.rpow_le_rpow (le_of_lt (inv_pos.mpr hNpos)) hi₀le (by linarith)
      _ = (if 0 < p i₀ then p i₀ ^ q else 0) := by rw [if_pos hpi0pos]
      _ ≤ ∑ i, (if 0 < p i then p i ^ q else 0) :=
          Finset.single_le_sum (fun i _ => guard_nonneg hp q i) (Finset.mem_univ i₀)
  have hlogge : -(q * Real.log (Fintype.card ι)) ≤ Real.log (partitionFunction p q) := by
    have h1 : Real.log ((Fintype.card ι : ℝ)⁻¹ ^ q) ≤ Real.log (partitionFunction p q) :=
      Real.log_le_log (Real.rpow_pos_of_pos (inv_pos.mpr hNpos) q) hZge
    rw [Real.log_rpow (inv_pos.mpr hNpos), Real.log_inv] at h1
    linarith
  rw [renyiEntropy]
  have hc : (1 - q)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
  have hstep : (1 - q)⁻¹ * Real.log (partitionFunction p q)
      ≤ (1 - q)⁻¹ * (-(q * Real.log (Fintype.card ι))) :=
    mul_le_mul_of_nonpos_left hlogge (le_of_lt hc)
  have hne1 : (1 : ℝ) - q ≠ 0 := by linarith
  have hne2 : q - 1 ≠ 0 := by linarith
  have heq : (1 - q)⁻¹ * (-(q * Real.log (Fintype.card ι)))
      = (q / (q - 1)) * Real.log (Fintype.card ι) := by
    field_simp
    ring
  rw [heq] at hstep
  exact hstep

end ErgodicTheory.Multifractal
