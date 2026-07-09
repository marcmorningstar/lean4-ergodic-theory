/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapCover
import ErgodicTheory.Examples.CatMapEigenShadow
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.Abstract
import ErgodicTheory.Livsic.ErgodicDenseOrbit

/-!
# The Anosov closing property and the Livšic theorem for the Arnold cat map

This module is the **tier-3 finale** of the Livšic campaign (GitHub issue #32): it discharges the
`ExpClosing` hypothesis of the abstract Livšic theorem (`ErgodicTheory.isHolderCoboundary_iff`) for
the genuine hyperbolic toral automorphism `catTorus : 𝕋² → 𝕋²`, and assembles the resulting
concrete **cohomological rigidity** statement.

## The exact-solve closing

For a *hyperbolic* toral automorphism the Anosov closing lemma admits an **exact** (non-iterative)
solution: because `catℝⁿ - 1` is invertible on `ℝ²` (`1` is not an eigenvalue of any power of the
hyperbolic matrix `catℝ = !![2,1;1,1]`), the shadowing periodic point is produced by *solving* the
cohomological equation `(catℝⁿ - 1) w = e` in closed form in the hyperbolic eigenbasis
(`ErgodicTheory.CatMapToral.catShadowSol`), rather than by a shadowing/contraction iteration.  Lift
the almost-return `x ↦ catTorusⁿ x` to a vector `d = catℝⁿ v - v` upstairs, take its nearest-integer
representative `e = roundReduce d`, solve for `w`, and project `p = catProj (v - w)` back to the
torus: `p` is an *exact* `n`-periodic point because `d - e` is an integer vector (invisible to the
covering projection), and its forward orbit two-sidedly geometrically shadows that of `x`.  Summing
the `α`-th powers of the shadow norms gives precisely the summed `ExpClosing` bound.

## Main results

* `ErgodicTheory.CatMapToral.expClosing_catTorus` — the summed exponential closing property
  `ExpClosing catTorus α 1 (2·Cshadow^α/(1-θ^α))` for every Hölder exponent `0 < α ≤ 1`.
* `ErgodicTheory.CatMapToral.catTorus_zero_fixed` — `0` is a fixed point of `catTorus`.
* `ErgodicTheory.CatMapToral.const_one_not_isCoboundary_catTorus` — the constant observable `1` is
  not a coboundary (a non-vacuity witness: its period-`1` Birkhoff sum at `0` is `1 ≠ 0`).
* `ErgodicTheory.CatMapToral.livsic_catTorus` — the **Livšic cohomological rigidity theorem** for
  the cat map: a Hölder observable is a Hölder coboundary iff all its periodic Birkhoff sums vanish.

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, Cambridge
  Univ. Press (1995), §6.4 (Anosov closing lemma, Cor. 6.4.17) and Theorem 19.2.1 (Livšic).
* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
-/

open Function Matrix MeasureTheory
open scoped NNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `ErgodicTheory/Examples/CatMapToral.lean` so that the
ambient `volume : Measure T2` here is *the same* product Haar probability measure for which
`ergodic_catTorus` is stated. -/
noncomputable local instance instMeasureSpaceUnitAddCircleClosing :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarUnitAddCircleClosing :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityUnitAddCircleClosing :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

open ErgodicTheory

/-- `catProj` is additive: `catProj (u + v) = catProj u + catProj v`.  (The companion module
`CatMapCover` records only the difference version `catProj_sub`; this is the `+` analogue.) -/
theorem catProj_add (u v : Fin 2 → ℝ) : catProj (u + v) = catProj u + catProj v := by
  funext i
  simp only [catProj, Pi.add_apply, AddCircle.coe_add]

/-! ## The exact-solve Anosov closing property -/

/-- **The Anosov closing property for the Arnold cat map** (Katok–Hasselblatt §6.4, Cor. 6.4.17
in the summed-cost form of `ErgodicTheory.Livsic.Defs`).  For every Hölder exponent `0 < α ≤ 1`,
`catTorus` satisfies the summed exponential closing property with closing radius `1` and the
explicit constant `K = 2·Cshadow^α/(1-θ^α)`.

The closing radius `δ = 1` is vacuous (the hypothesis is unused).  The shadowing periodic point is
obtained by the **exact solve** of the cohomological equation `(catℝⁿ - 1) w = e` (rather than a
shadowing iteration): lift the almost-return to `d = catℝⁿ v - v`, reduce it to its nearest-integer
representative `e = roundReduce d`, solve `w = catShadowSol n e`, and project `p = catProj (v - w)`.
The point `p` is *exactly* `n`-periodic because `d - e` is an integer vector, and the summed
`α`-power shadowing cost is controlled by `sum_rpow_norm_catShadow_le`. -/
theorem expClosing_catTorus {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ExpClosing catTorus α 1 (2 * Cshadow ^ α / (1 - θ ^ α)) := by
  -- The constant `K = 2·Cshadow^α/(1-θ^α)` is nonnegative.
  have hθα1 : θ ^ α < 1 := Real.rpow_lt_one θ_pos.le θ_lt_one hα0
  have h1mθα : (0 : ℝ) < 1 - θ ^ α := by linarith
  have hCshα : (0 : ℝ) ≤ Cshadow ^ α := Real.rpow_nonneg Cshadow_pos.le α
  have hKnonneg : (0 : ℝ) ≤ 2 * Cshadow ^ α / (1 - θ ^ α) :=
    div_nonneg (by linarith) h1mθα.le
  intro n x _hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `x` shadows itself with an empty sum.
    refine ⟨x, Function.iterate_zero_apply catTorus x, ?_⟩
    rw [Finset.range_zero, Finset.sum_empty]
    exact mul_nonneg hKnonneg (Real.rpow_nonneg dist_nonneg _)
  · -- Main case `1 ≤ n`: the exact-solve construction.
    obtain ⟨v, hv⟩ := catProj_surjective x
    set d : Fin 2 → ℝ := (catℝ ^ n) *ᵥ v - v with hd
    set e : Fin 2 → ℝ := roundReduce d with he
    set w : Fin 2 → ℝ := catShadowSol n e with hw_def
    -- `catProj d` is the toral almost-return `catTorusⁿ x - x`.
    have hcatProj_d : catProj d = catTorus^[n] x - x := by
      rw [hd, catProj_sub, ← catTorus_iterate_catProj, hv]
    -- `d - e` is an integer vector, so it is invisible to `catProj`.
    have hde : catProj (d - e) = (0 : T2) := by
      funext i
      have hcoord : (d - e) i = ((round (d i) : ℤ) : ℝ) := by
        rw [Pi.sub_apply, he]; simp only [roundReduce]; ring
      simp only [catProj, Pi.zero_apply, hcoord]
      exact coe_intCast_eq_zero (round (d i))
    -- `‖e‖` is exactly the toral return gap.
    have hnorm_e : ‖e‖ = dist x (catTorus^[n] x) := by
      rw [he, norm_roundReduce_eq_dist, hcatProj_d, dist_eq_norm, sub_zero, dist_eq_norm,
        norm_sub_rev]
    -- The shadow point `p := catProj (v - w)` is an *exact* `n`-periodic point.
    have hfix : catTorus^[n] (catProj (v - w)) = catProj (v - w) := by
      rw [catTorus_iterate_catProj]
      have hw' : (catℝ ^ n) *ᵥ w - w = e := by
        have h := sub_mulVec_catShadowSol n hn e
        rwa [← hw_def] at h
      have hd' : (catℝ ^ n) *ᵥ v - v = d := hd.symm
      have hvec : (catℝ ^ n) *ᵥ (v - w) = (v - w) + (d - e) := by
        rw [Matrix.mulVec_sub]
        have e1 : (catℝ ^ n) *ᵥ v = d + v := by rw [← hd']; abel
        have e2 : (catℝ ^ n) *ᵥ w = e + w := by rw [← hw']; abel
        rw [e1, e2]; abel
      rw [hvec, catProj_add, hde, add_zero]
    refine ⟨catProj (v - w), hfix, ?_⟩
    -- Per-step shadowing: `dist (catTorusⁱ x) (catTorusⁱ p) ≤ ‖catℝⁱ ·ᵥ w‖`.
    have hterm : ∀ i ∈ Finset.range n,
        dist (catTorus^[i] x) (catTorus^[i] (catProj (v - w))) ^ α
          ≤ ‖(catℝ ^ i) *ᵥ w‖ ^ α := by
      intro i _
      have h1 : catTorus^[i] x = catProj ((catℝ ^ i) *ᵥ v) := by
        rw [← hv, catTorus_iterate_catProj]
      have h2 : catTorus^[i] (catProj (v - w)) = catProj ((catℝ ^ i) *ᵥ (v - w)) :=
        catTorus_iterate_catProj i (v - w)
      have hvec : (catℝ ^ i) *ᵥ v - (catℝ ^ i) *ᵥ (v - w) = (catℝ ^ i) *ᵥ w := by
        rw [← Matrix.mulVec_sub, sub_sub_cancel]
      have hb : dist (catTorus^[i] x) (catTorus^[i] (catProj (v - w))) ≤ ‖(catℝ ^ i) *ᵥ w‖ := by
        rw [h1, h2]
        calc dist (catProj ((catℝ ^ i) *ᵥ v)) (catProj ((catℝ ^ i) *ᵥ (v - w)))
            ≤ ‖(catℝ ^ i) *ᵥ v - (catℝ ^ i) *ᵥ (v - w)‖ := dist_catProj_le _ _
          _ = ‖(catℝ ^ i) *ᵥ w‖ := by rw [hvec]
      exact Real.rpow_le_rpow dist_nonneg hb hα0.le
    calc ∑ i ∈ Finset.range n, dist (catTorus^[i] x) (catTorus^[i] (catProj (v - w))) ^ α
        ≤ ∑ i ∈ Finset.range n, ‖(catℝ ^ i) *ᵥ w‖ ^ α := Finset.sum_le_sum hterm
      _ ≤ 2 * Cshadow ^ α / (1 - θ ^ α) * ‖e‖ ^ α := by
          rw [hw_def]; exact sum_rpow_norm_catShadow_le hα0 hα1 n e
      _ = 2 * Cshadow ^ α / (1 - θ ^ α) * dist x (catTorus^[n] x) ^ α := by rw [hnorm_e]

/-! ## Non-vacuity witnesses -/

/-- `0` is a fixed point of the cat map (`catTorus` is a linear toral automorphism, so it fixes the
identity element). -/
theorem catTorus_zero_fixed : catTorus (0 : T2) = 0 := by
  funext i; simp [catTorus, torusMap]

/-- **A non-vacuity witness for the obstruction direction.**  The constant observable `1` is *not* a
coboundary of `catTorus`: its Birkhoff sum around the fixed point `0` (period `1`) equals `1 ≠ 0`,
so by `not_isCoboundary_of_periodicSum_ne_zero` no transfer function can cobound it. -/
theorem const_one_not_isCoboundary_catTorus :
    ¬ IsCoboundary catTorus (fun _ : T2 => (1 : ℝ)) := by
  refine not_isCoboundary_of_periodicSum_ne_zero (n := 1) (p := 0) ?_ ?_
  · rw [Function.iterate_one]; exact catTorus_zero_fixed
  · rw [birkhoffSum, Finset.sum_range_one]; norm_num

/-! ## The Livšic cohomological rigidity theorem for the cat map -/

/-- **The Livšic theorem for the Arnold cat map** (Katok–Hasselblatt Thm 19.2.1).  For any Hölder
observable `φ` (exponent `0 < r ≤ 1`), `φ` is a Hölder coboundary of the hyperbolic toral
automorphism `catTorus` **iff** all of its periodic Birkhoff sums vanish.

This instantiates the abstract equivalence `ErgodicTheory.isHolderCoboundary_iff`: `catTorus` is
continuous, the exponential closing property is `expClosing_catTorus`, and a dense forward orbit is
furnished by `ergodic_exists_denseRange_iterate` applied to the genuine ergodicity
`ergodic_catTorus` of the cat map for the Haar (`volume`) measure. -/
theorem livsic_catTorus {C r : ℝ≥0} {φ : T2 → ℝ} (hφ : HolderWith C r φ)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsHolderCoboundary catTorus φ ↔ HasVanishingPeriodicSums catTorus φ := by
  obtain ⟨x₀, hdense⟩ := ergodic_exists_denseRange_iterate ergodic_catTorus
  have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hcl : ExpClosing catTorus (r : ℝ) 1 (2 * Cshadow ^ (r : ℝ) / (1 - θ ^ (r : ℝ))) :=
    expClosing_catTorus hr0' hr1'
  have hθα1 : θ ^ (r : ℝ) < 1 := Real.rpow_lt_one θ_pos.le θ_lt_one hr0'
  have hK : (0 : ℝ) ≤ 2 * Cshadow ^ (r : ℝ) / (1 - θ ^ (r : ℝ)) :=
    div_nonneg (by nlinarith [Real.rpow_nonneg Cshadow_pos.le (r : ℝ)]) (by linarith)
  exact isHolderCoboundary_iff continuous_catTorus hr0 hr1 hφ one_pos hK hcl hdense

end ErgodicTheory.CatMapToral

end
