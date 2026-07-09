/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Abstract
import ErgodicTheory.Livsic.ShiftMetric

/-!
# The Livšic theorem for a one-sided subshift of finite type

This file extends the full-shift Livšic instance (`ErgodicTheory.Livsic.FullShift`) to a **general
one-sided subshift of finite type (SFT)** cut out of the full shift `Shift (Fin k)` by a `0/1`
transition matrix `M : Fin k → Fin k → Bool`. The SFT is the closed shift-invariant set

`SFTCarrier M = {x | ∀ i, M (x i) (x (i + 1)) = true}`

of admissible sequences; as a subtype it inherits the `PiNat` ultrametric and, being a closed subset
of the (Tychonoff-)compact full shift, is compact.

## The `δ = 1/2` design finding

The substantive geometric input to the abstract Livšic theorem
(`ErgodicTheory.isHolderCoboundary_iff`, Katok–Hasselblatt §19.2, Thm 19.2.1) is the summed
exponential closing property `ExpClosing`. For the full shift this holds with the *vacuous* closing
radius `δ = 1` (every finite word is legal, so the periodization `p i := x (i % n)` of an
almost-`n`-returning point is automatically admissible). For a genuine SFT this is false — the
periodization has a *wrap transition* `M (x (n-1)) (x 0)` that need not be legal.

The key observation is that at the **smaller closing radius `δ = 1/2`** the periodization is
admissible with **no connecting word and no irreducibility hypothesis on `M`**:
`dist x (σ^n x) ≤ 1/2` forces `x 0 = x n` (they agree on coordinate `0`), so the wrap transition
`M (x (n-1)) (x 0) = M (x (n-1)) (x n)` coincides with the interior transition
`M (x (n-1)) (x ((n-1)+1))`, which is legal because `x` itself is admissible. Hence the closing
property `ExpClosing (sftShiftMap M) α (1/2) K` holds **unconditionally in `M`** (with the same
explicit constant `K = (1/2)^α / (1 - (1/2)^α)` as the full shift). A *dense orbit* is what needs a
combinatorial hypothesis on `M`; it is taken as a hypothesis here (a sibling module supplies it
under a **safe-symbol** class — a symbol allowed adjacent to every symbol, strictly stronger than
irreducibility, so general irreducible-SFT dense orbits are not delivered here).

## Main results

* `ErgodicTheory.SFTCarrier` / `ErgodicTheory.isClosed_sftCarrier` — the admissible set and its
  closedness.
* `ErgodicTheory.SFT` — the SFT as a (compact metric) subtype.
* `ErgodicTheory.sftShiftMap` / `ErgodicTheory.lipschitzWith_two_sftShiftMap` — the restricted shift
  and its `2`-Lipschitz continuity.
* `ErgodicTheory.sft_head_eq_of_dist_le_half` — the `δ = 1/2` crux: an almost-`n`-return within
  `1/2` forces `x 0 = x n`.
* `ErgodicTheory.expClosing_sftShiftMap` — the headline: the SFT shift satisfies
  `ExpClosing (sftShiftMap M) α (1/2) ((1/2)^α / (1 - (1/2)^α))`, **unconditionally in `M`**.
* `ErgodicTheory.livsic_sft` — the conditional Livšic equivalence for the SFT, given a dense forward
  orbit.

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  §19.2 (Theorem 19.2.1).
* W. Parry, M. Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic dynamics*,
  Astérisque **187–188** (1990), Ch. 3.
-/

open Function Filter Topology Set
open scoped NNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

attribute [local instance] PiNat.metricSpace

/-! ### The subshift of finite type -/

section SFT

variable {k : ℕ} {M : Fin k → Fin k → Bool}

/-- The **carrier of the subshift of finite type** cut out of the full shift `Shift (Fin k)` by the
transition matrix `M`: the set of sequences whose consecutive symbols are `M`-admissible. -/
def SFTCarrier (M : Fin k → Fin k → Bool) : Set (Shift (Fin k)) :=
  {x | ∀ i, M (x i) (x (i + 1)) = true}

/-- The SFT carrier is **closed** (its complement is open): if `x` is inadmissible at some index `i`
(`M (x i) (x (i+1)) ≠ true`), then every `y` within `(1/2)^(i+2)` of `x` agrees with `x` on
coordinates `< i+2` (`agree_iff_dist_le`), hence is inadmissible at `i` too. -/
theorem isClosed_sftCarrier : IsClosed (SFTCarrier M) := by
  rw [← isOpen_compl_iff]
  refine Metric.isOpen_iff.mpr (fun x hx => ?_)
  rw [Set.mem_compl_iff] at hx
  replace hx : ¬ ∀ i, M (x i) (x (i + 1)) = true := hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  refine ⟨(1 / 2 : ℝ) ^ (i + 2), by positivity, fun y hy => ?_⟩
  rw [Metric.mem_ball] at hy
  have hagree : ∀ j < i + 2, y j = x j := (agree_iff_dist_le (i + 2) y x).mpr hy.le
  rw [Set.mem_compl_iff]
  intro hmem
  exact hi (by rw [← hagree i (by omega), ← hagree (i + 1) (by omega)]; exact hmem i)

/-- The **subshift of finite type** as a subtype of the full shift. It inherits the `PiNat`
ultrametric (`Subtype.metricSpace`) and, below, compactness. -/
abbrev SFT (M : Fin k → Fin k → Bool) : Type _ := ↥(SFTCarrier M)

/-- The SFT is **compact**: a closed subset of the Tychonoff-compact full shift `Shift (Fin k)`
(finite discrete alphabet). -/
instance instCompactSpaceSFT : CompactSpace (SFT M) :=
  isCompact_iff_compactSpace.mp isClosed_sftCarrier.isCompact

/-- The **left shift on the SFT**: the restriction of the full shift `shiftMap`. Admissibility is
preserved because dropping the first symbol shifts every transition index down by one. -/
def sftShiftMap (M : Fin k → Fin k → Bool) : SFT M → SFT M :=
  fun x => ⟨shiftMap x.1, by
    intro i
    simpa only [shiftMap] using x.2 (i + 1)⟩

/-- The coercion commutes with iteration of the SFT shift: `↑((sftShiftMap M)^[n] x) = σ^n ↑x`. -/
theorem coe_sftShiftMap_iterate (n : ℕ) (x : SFT M) :
    (((sftShiftMap M)^[n] x : SFT M) : Shift (Fin k)) = shiftMap^[n] (x : Shift (Fin k)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change shiftMap (((sftShiftMap M)^[m] x : SFT M) : Shift (Fin k))
      = shiftMap (shiftMap^[m] (x : Shift (Fin k)))
    rw [ih]

/-- The SFT shift is `2`-Lipschitz for the `PiNat` ultrametric — the restriction of the ambient
`2`-Lipschitz `shiftMap`, transported through `Subtype.dist_eq`. -/
theorem lipschitzWith_two_sftShiftMap : LipschitzWith 2 (sftShiftMap M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Subtype.dist_eq, Subtype.dist_eq]
  exact lipschitzWith_two_shiftMap.dist_le_mul (x : Shift (Fin k)) (y : Shift (Fin k))

/-- The SFT shift is continuous. -/
theorem continuous_sftShiftMap : Continuous (sftShiftMap M) :=
  lipschitzWith_two_sftShiftMap.continuous

/-- **The `δ = 1/2` crux.** If `x` almost `n`-returns within `1/2`
(`dist x ((sftShiftMap M)^[n] x) ≤ 1/2`), then `x` and `σ^n x` agree on coordinate `0`, i.e.
`x 0 = x n`. This is what makes the periodization's wrap transition legal without a connecting
word. -/
theorem sft_head_eq_of_dist_le_half (x : SFT M) (n : ℕ)
    (h : dist x ((sftShiftMap M)^[n] x) ≤ 1 / 2) :
    (x : Shift (Fin k)) 0 = (x : Shift (Fin k)) n := by
  rw [Subtype.dist_eq, coe_sftShiftMap_iterate] at h
  have hagree := (agree_iff_dist_le 1 (x : Shift (Fin k)) (shiftMap^[n] (x : Shift (Fin k)))).mpr
    (by rw [pow_one]; exact h)
  have h0 := hagree 0 Nat.one_pos
  rw [shiftMap_iterate_apply] at h0
  simpa using h0

/-- **Periodization admissibility.** Given `x` in the SFT with `x 0 = x n` (from the `δ = 1/2`
crux), the periodization `p i := x (i % n)` is again admissible: interior transitions inherit from
`x`, and
the wrap transition `M (x (n-1)) (x 0) = M (x (n-1)) (x n)` coincides with the legal interior
transition `M (x (n-1)) (x ((n-1)+1))`. **No connecting word / irreducibility is used.** -/
theorem periodize_mem_sftCarrier (x : SFT M) {n : ℕ} (hn : 0 < n)
    (hhead : (x : Shift (Fin k)) 0 = (x : Shift (Fin k)) n) :
    (fun i => (x : Shift (Fin k)) (i % n)) ∈ SFTCarrier M := by
  intro i
  change M ((x : Shift (Fin k)) (i % n)) ((x : Shift (Fin k)) ((i + 1) % n)) = true
  have hr : i % n < n := Nat.mod_lt i hn
  have key : (i + 1) % n = (i % n + 1) % n := ((Nat.mod_modEq i n).add_right 1).symm
  rw [key]
  rcases Nat.lt_or_ge (i % n + 1) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    exact x.2 (i % n)
  · have heq : i % n + 1 = n := by omega
    rw [heq, Nat.mod_self, hhead]
    have hn' : (x : Shift (Fin k)) n = (x : Shift (Fin k)) (i % n + 1) := by rw [heq]
    rw [hn']
    exact x.2 (i % n)

/-- **Headline: exponential closing for the SFT, unconditional in `M`.** For every Hölder exponent
`α > 0`, the SFT shift `sftShiftMap M` satisfies the summed-cost closing property
`ExpClosing (sftShiftMap M) α (1/2) ((1/2)^α / (1 - (1/2)^α))` with **closing radius `δ = 1/2`** and
the same explicit constant as the full shift — for **any** transition matrix `M`, with no
irreducibility hypothesis.

The `δ = 1/2` radius (versus the full shift's vacuous `δ = 1`) is exactly what is consumed: it
guarantees (`sft_head_eq_of_dist_le_half`) that the periodization `⟨fun i => x (i % n), …⟩` lands in
the SFT (`periodize_mem_sftCarrier`), and the shadow bound then follows from the ambient estimate
`sum_shadow_le` transported through `Subtype.dist_eq`. -/
theorem expClosing_sftShiftMap {α : ℝ} (hα : 0 < α) :
    ExpClosing (sftShiftMap M) α (1 / 2) ((1 / 2) ^ α / (1 - (1 / 2) ^ α)) := by
  intro n x hx
  rcases eq_or_ne x ((sftShiftMap M)^[n] x) with hxeq | hne_x
  · -- `x` is already `n`-periodic: it shadows itself with zero cost.
    refine ⟨x, hxeq.symm, ?_⟩
    have hz : ∀ i ∈ Finset.range n,
        dist ((sftShiftMap M)^[i] x) ((sftShiftMap M)^[i] x) ^ α = 0 :=
      fun i _ => by rw [dist_self, Real.zero_rpow (ne_of_gt hα)]
    refine le_of_eq ?_
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, ← hxeq, dist_self,
      Real.zero_rpow (ne_of_gt hα), mul_zero]
  · -- Main case: `x ≠ σ^n x`, so `n ≥ 1` and the periodization is the periodic shadow.
    have hn : 0 < n :=
      Nat.pos_of_ne_zero (by rintro rfl; exact hne_x (Function.iterate_zero_apply _ _).symm)
    have hhead : (x : Shift (Fin k)) 0 = (x : Shift (Fin k)) n :=
      sft_head_eq_of_dist_le_half x n hx
    have hp_mem : (fun i => (x : Shift (Fin k)) (i % n)) ∈ SFTCarrier M :=
      periodize_mem_sftCarrier x hn hhead
    have hne_y : (x : Shift (Fin k)) ≠ shiftMap^[n] (x : Shift (Fin k)) := by
      intro h
      apply hne_x
      apply Subtype.ext
      rw [coe_sftShiftMap_iterate]
      exact h
    refine ⟨⟨fun i => (x : Shift (Fin k)) (i % n), hp_mem⟩, ?_, ?_⟩
    · -- The periodization is genuinely `n`-periodic.
      apply Subtype.ext
      rw [coe_sftShiftMap_iterate]
      funext i
      rw [shiftMap_iterate_apply]
      change (x : Shift (Fin k)) ((i + n) % n) = (x : Shift (Fin k)) (i % n)
      rw [Nat.add_mod_right]
    · -- The shadow bound: transport `sum_shadow_le` through `Subtype.dist_eq`.
      have hbound := sum_shadow_le hα n hn (x : Shift (Fin k)) hne_y
      have hterm_eq : ∀ i, dist ((sftShiftMap M)^[i] x)
          ((sftShiftMap M)^[i] ⟨fun j => (x : Shift (Fin k)) (j % n), hp_mem⟩)
          = dist (shiftMap^[i] (x : Shift (Fin k)))
              (shiftMap^[i] (fun j => (x : Shift (Fin k)) (j % n))) := by
        intro i
        rw [Subtype.dist_eq, coe_sftShiftMap_iterate, coe_sftShiftMap_iterate]
      have hsum_eq : ∑ i ∈ Finset.range n,
            dist ((sftShiftMap M)^[i] x)
              ((sftShiftMap M)^[i] ⟨fun j => (x : Shift (Fin k)) (j % n), hp_mem⟩) ^ α
          = ∑ i ∈ Finset.range n,
            dist (shiftMap^[i] (x : Shift (Fin k)))
              (shiftMap^[i] (fun j => (x : Shift (Fin k)) (j % n))) ^ α :=
        Finset.sum_congr rfl (fun i _ => by rw [hterm_eq i])
      have hRHS_eq : dist x ((sftShiftMap M)^[n] x)
          = dist (x : Shift (Fin k)) (shiftMap^[n] (x : Shift (Fin k))) := by
        rw [Subtype.dist_eq, coe_sftShiftMap_iterate]
      rw [hsum_eq, hRHS_eq]
      exact hbound

/-- **Livšic for a one-sided subshift of finite type.** Given a Hölder observable `φ`
(exponent `0 < r ≤ 1`) on the SFT and a **dense forward orbit** under the SFT shift, `φ` is a Hölder
coboundary iff all of its periodic Birkhoff sums vanish.

This instantiates the abstract `isHolderCoboundary_iff` (Katok–Hasselblatt §19.2): continuity is
`lipschitzWith_two_sftShiftMap`, compactness is `instCompactSpaceSFT`, and the summed exponential
closing property is `expClosing_sftShiftMap` (closing radius `δ = 1/2`, unconditional in `M`). The
dense orbit — the only place a combinatorial hypothesis on `M` enters — is a hypothesis; a sibling
module supplies it under a **safe-symbol** class (a symbol allowed adjacent to every symbol,
strictly stronger than irreducibility, so general irreducible-SFT dense orbits are not delivered
here). -/
theorem livsic_sft {C r : ℝ≥0} {φ : SFT M → ℝ} (hφ : HolderWith C r φ)
    (hr0 : 0 < r) (hr1 : r ≤ 1) {x₀ : SFT M}
    (hdense : DenseRange fun n : ℕ => (sftShiftMap M)^[n] x₀) :
    IsHolderCoboundary (sftShiftMap M) φ ↔ HasVanishingPeriodicSums (sftShiftMap M) φ := by
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr0
  have hnum : (0 : ℝ) < (1 / 2 : ℝ) ^ (r : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt1 : (1 / 2 : ℝ) ^ (r : ℝ) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hrpos
  have hden : (0 : ℝ) < 1 - (1 / 2 : ℝ) ^ (r : ℝ) := by linarith
  have hK : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := (div_pos hnum hden).le
  exact isHolderCoboundary_iff lipschitzWith_two_sftShiftMap.continuous hr0 hr1 hφ
    (by norm_num : (0 : ℝ) < 1 / 2) hK (expClosing_sftShiftMap hrpos) hdense

end SFT

end ErgodicTheory
