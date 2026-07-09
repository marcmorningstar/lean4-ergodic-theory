/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.ErgodicDenseOrbit
import ErgodicTheory.Livsic.DoublingClosing
import ErgodicTheory.Livsic.Abstract

/-!
# The Livšic theorem for the doubling map

This is the smooth expanding instance of the abstract Livšic cohomological rigidity theorem
(issue #33) for the **doubling map** `doublingMap : y ↦ 2 • y` on the unit circle `UnitAddCircle`.
The doubling map is the canonical expanding endomorphism of the circle; it is ergodic for the Haar
(Lebesgue) measure, so it has a dense forward orbit
(`ErgodicTheory.ergodic_exists_denseRange_iterate` applied to `ergodic_doublingMap`), and the
rounding closing construction (`ErgodicTheory.expClosing_doublingMap`) supplies the summed
exponential closing property. Together with continuity and compactness of the circle these assemble
into the clean equivalence

`IsHolderCoboundary doublingMap φ ↔ HasVanishingPeriodicSums doublingMap φ`

for every Hölder observable `φ` (exponent `0 < r ≤ 1`).

## Main results

* `ErgodicTheory.livsic_doublingMap` — the headline equivalence for the doubling map.
* `ErgodicTheory.exists_denseRange_doublingMap_orbit` — the doubling map has a dense forward orbit.
* `ErgodicTheory.doublingMap_periodic_iff` — `n`-periodic points of the doubling map are the
  solutions of `2 ^ n • p = p`.
* `ErgodicTheory.const_one_not_isCoboundary_doublingMap` — an obstruction witness: the constant `1`
  is **not** a coboundary (its Birkhoff sum at the fixed point `0` is `1 ≠ 0`).
* `ErgodicTheory.norm_coboundary_isHolderCoboundary` — a positive witness: `‖·∘doublingMap‖ − ‖·‖`
  is a Hölder coboundary, with the `1`-Lipschitz transfer function `‖·‖`.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.1 (Livšic existence) and Ch. 19 (the doubling map as an expanding example).
-/

open Function
open scoped NNReal

namespace ErgodicTheory

/-- The doubling map is continuous: `2 • y = y + y` is a sum of two continuous maps. -/
theorem continuous_doublingMap : Continuous doublingMap := by
  have h : doublingMap = fun y : UnitAddCircle => y + y := by
    funext y; rw [doublingMap, two_nsmul]
  rw [h]
  exact continuous_id.add continuous_id

/-- **Periodic points of the doubling map.** A point `p` is `n`-periodic under `doublingMap` iff it
solves `2 ^ n • p = p`; immediate from `doublingMap^[n] = (2 ^ n) • ·`. -/
theorem doublingMap_periodic_iff (n : ℕ) (p : UnitAddCircle) :
    doublingMap^[n] p = p ↔ (2 ^ n : ℕ) • p = p := by
  rw [doublingMap_iterate]

/-- **The doubling map has a dense forward orbit.** The doubling map is ergodic for the Haar measure
on the circle (`ergodic_doublingMap`), an open-positive probability measure on a second-countable
space, so `ergodic_exists_denseRange_iterate` yields a point with dense forward orbit. -/
theorem exists_denseRange_doublingMap_orbit :
    ∃ x₀ : UnitAddCircle, DenseRange fun n : ℕ => doublingMap^[n] x₀ :=
  ergodic_exists_denseRange_iterate ergodic_doublingMap

/-- **Livšic for the doubling map** (Katok–Hasselblatt, Theorem 19.2.1). A Hölder observable `φ`
(exponent `0 < r ≤ 1`) on the circle is a **Hölder coboundary** for the doubling map **iff** all of
its periodic Birkhoff sums vanish.

This instantiates the abstract `isHolderCoboundary_iff`: continuity of the doubling map is
`continuous_doublingMap`, compactness of the circle is ambient, the summed exponential closing
property is `expClosing_doublingMap` (with `δ = 1`, closing constant `K = 2 ^ r / (2 ^ r − 1) ≥ 0`),
and the dense forward orbit is `exists_denseRange_doublingMap_orbit`. -/
theorem livsic_doublingMap {C r : ℝ≥0} {φ : UnitAddCircle → ℝ}
    (hφ : HolderWith C r φ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsHolderCoboundary doublingMap φ ↔ HasVanishingPeriodicSums doublingMap φ := by
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr0
  obtain ⟨x₀, hdense⟩ := exists_denseRange_doublingMap_orbit
  have hs0 : (0 : ℝ) < (2 : ℝ) ^ (r : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hs1 : (1 : ℝ) < (2 : ℝ) ^ (r : ℝ) := Real.one_lt_rpow (by norm_num) hrpos
  have hden : (0 : ℝ) < (2 : ℝ) ^ (r : ℝ) - 1 := by linarith
  have hK : (0 : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) / ((2 : ℝ) ^ (r : ℝ) - 1) := (div_pos hs0 hden).le
  exact isHolderCoboundary_iff continuous_doublingMap hr0 hr1 hφ one_pos hK
    (expClosing_doublingMap hrpos) hdense

/-! ### Non-vacuity witnesses -/

/-- **Obstruction witness.** The constant potential `1` is **not** a coboundary for the doubling
map: its period-`1` Birkhoff sum at the fixed point `0` (`doublingMap 0 = 0`) is `1 ≠ 0`, so the
bare obstruction certificate `not_isCoboundary_of_periodicSum_ne_zero` applies. -/
theorem const_one_not_isCoboundary_doublingMap :
    ¬ IsCoboundary doublingMap (fun _ => (1 : ℝ)) := by
  refine not_isCoboundary_of_periodicSum_ne_zero (n := 1) (p := (0 : UnitAddCircle)) ?_ ?_
  · rw [Function.iterate_one]; simp [doublingMap]
  · rw [birkhoffSum_one]; norm_num

/-- The circle norm `‖·‖ : UnitAddCircle → ℝ` is `1`-Lipschitz (reverse triangle inequality). -/
theorem lipschitzWith_one_norm_unitAddCircle :
    LipschitzWith 1 (fun y : UnitAddCircle => ‖y‖) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
  exact abs_norm_sub_norm_le x y

/-- **Positive witness.** `‖·∘doublingMap‖ − ‖·‖` is, by construction, a Hölder coboundary of the
doubling map, with the `1`-Lipschitz (hence `HolderWith 1 1`) transfer function `‖·‖`. -/
theorem norm_coboundary_isHolderCoboundary :
    IsHolderCoboundary doublingMap (fun y => ‖doublingMap y‖ - ‖y‖) :=
  ⟨1, 1, (fun y => ‖y‖), one_pos, lipschitzWith_one_norm_unitAddCircle.holderWith, fun _ => rfl⟩

end ErgodicTheory
