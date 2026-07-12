/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.HolderFlowCoboundary
import ErgodicTheory.Examples.CatMapClosing
import ErgodicTheory.Examples.CatMapSuspensionLivsic
import ErgodicTheory.Examples.CatMapFlowCoboundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.Int

/-!
# The classical (Hölder) Livšic theorem on the Arnold cat-map suspension flow

This module (issue #63, tier-2 instantiation) upgrades the regularity-free tier-III demarcation of
`ErgodicTheory/Examples/CatMapSuspensionLivsic.lean` (issue #55) to the **classical-strength Livšic
theorem** for the suspension (special) flow over the genuine Arnold cat map `catTorus : 𝕋² → 𝕋²`
with the unit roof `τ ≡ 1`: a *Hölder* flow observable admits a *Hölder* flow transfer function iff
its induced base observable has vanishing periodic sums.  The equivalence is measured for the
Bowen–Walters embedding metric `ErgodicTheory.embDist`, and it instantiates the abstract
`ErgodicTheory.livsic_holderFlow_constRoof` by discharging its base-system hypotheses for the cat
map (diameter bound, Lipschitz constant, continuity, the summed exponential closing property, and a
dense forward orbit from ergodicity).

## Hypothesis discharges

* `ErgodicTheory.CatMapToral.catTorus_dist_le_one` — the sup metric on `𝕋²` has diameter `≤ 1`
  (each `UnitAddCircle` factor has norm `≤ 1/2`).
* `ErgodicTheory.CatMapToral.lipschitzWith_catTorus` — `catTorus` is `3`-Lipschitz (the matrix
  `!![2,1;1,1]` has maximal absolute row sum `3`).

## Main results

* `ErgodicTheory.CatMapToral.livsic_catSuspensionHolderFlow` — **the headline**: the Hölder
  flow-Livšic equivalence for the cat-map suspension flow.
* `ErgodicTheory.CatMapToral.livsic_catSuspensionHolderFlow_orbitIntegral` — its flow-native
  (closed-orbit) form.
* `ErgodicTheory.CatMapToral.isHolderFlowCoboundary_sinFibreObservable` — **non-vacuity, coboundary
  side**: the `sin (2π·)` fibre observable is embedding-Hölder and *is* a Hölder flow coboundary.
* `ErgodicTheory.CatMapToral.const_one_not_isHolderFlowCoboundary_catSuspension` — **non-vacuity,
  obstruction side**: the constant observable `1` is embedding-Hölder yet *not* a Hölder flow
  coboundary.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972) 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §19.2.
* R. Bowen, P. Walters, *Expansive one-parameter flows*, J. Diff. Eq. **12** (1972) 180–193.
-/

open MeasureTheory Function Matrix
open scoped NNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of `ErgodicTheory/Examples/CatMapToral.lean` so that the
ambient `volume : Measure T2` here is *the same* product Haar probability measure for which
`ergodic_catTorus` is stated. (Uniquely named to avoid colliding with the identical local instances
of the sibling cat-map modules.) -/
noncomputable local instance instMeasureSpaceUnitAddCircleHolderLivsic :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarUnitAddCircleHolderLivsic :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityUnitAddCircleHolderLivsic :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

open ErgodicTheory

/-! ### Hypothesis discharges for the abstract theorem -/

/-- **Diameter bound for `𝕋²`.** The sup (`L∞`) metric on `𝕋² = Fin 2 → UnitAddCircle` has
diameter `≤ 1`: each coordinate distance is a `UnitAddCircle` norm, bounded by `|1| / 2 = 1/2`. -/
theorem catTorus_dist_le_one (a b : T2) : dist a b ≤ 1 := by
  rw [dist_pi_le_iff (by norm_num)]
  intro i
  rw [dist_eq_norm]
  calc ‖a i - b i‖ ≤ |(1 : ℝ)| / 2 := AddCircle.norm_le_half_period 1 one_ne_zero
    _ ≤ 1 := by norm_num

/-- **`catTorus` is `3`-Lipschitz.** In the sup metric, `dist (catTorus x) (catTorus y) ≤ 3 · dist
x y`: coordinatewise the difference is `∑ⱼ Mᵢⱼ • (xⱼ − yⱼ)`, and `∑ⱼ |Mᵢⱼ| ≤ 3` for the cat matrix
`M = !![2,1;1,1]` (maximal absolute row sum). -/
theorem lipschitzWith_catTorus : LipschitzWith 3 (⇑catTorusEquiv) := by
  have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
  rw [hcoe]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hsub : catTorus x i - catTorus y i = ∑ j, catℤ i j • (x j - y j) := by
    simp only [catTorus, torusMap]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_sub]
  rw [dist_eq_norm, hsub]
  have hbound : ∀ j : Fin 2, ‖catℤ i j • (x j - y j)‖ ≤ ‖catℤ i j‖ * dist x y := by
    intro j
    refine (norm_zsmul_le (catℤ i j) (x j - y j)).trans ?_
    gcongr
    rw [← dist_eq_norm]; exact dist_le_pi_dist x y j
  have hrow : (∑ j, ‖catℤ i j‖) ≤ 3 := by
    fin_cases i <;> norm_num [Fin.sum_univ_two, catℤ, Int.norm_eq_abs]
  calc ‖∑ j, catℤ i j • (x j - y j)‖ ≤ ∑ j, ‖catℤ i j • (x j - y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖catℤ i j‖ * dist x y := Finset.sum_le_sum fun j _ => hbound j
    _ = (∑ j, ‖catℤ i j‖) * dist x y := by rw [Finset.sum_mul]
    _ ≤ (3 : ℝ≥0) * dist x y := by
        push_cast
        exact mul_le_mul_of_nonneg_right hrow dist_nonneg

/-! ### The headline: the Hölder flow-Livšic equivalence for the cat-map suspension flow -/

/-- **The classical-strength Livšic theorem for the cat-map suspension flow** (Livšic 1972;
Katok–Hasselblatt §19.2).  For an embedding-`r`-Hölder, bounded flow observable `F` (with
interval-integrable fibre restrictions), `F` is a **Hölder** flow coboundary of the suspension flow
over the Arnold cat map (unit roof) **iff** every periodic Birkhoff sum of its induced base
observable vanishes.  The base-system hypotheses of `livsic_holderFlow_constRoof` are discharged by
`catTorus_dist_le_one`, `lipschitzWith_catTorus`, `continuous_catTorus`, the summed exponential
closing property `expClosing_catTorus`, and a dense forward orbit from `ergodic_catTorus`. -/
theorem livsic_catSuspensionHolderFlow {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (F : SuspensionSpace catTorusEquiv measurable_catRoof → ℝ)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) *
      embDist catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M)
    (hint : ∀ x a b, IntervalIntegrable
      (fun s => F (suspensionMk catTorusEquiv measurable_catRoof (x, s))) volume a b) :
    IsHolderFlowCoboundary catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one
        (suspensionFlowMap catTorusEquiv measurable_catRoof) F ↔
      HasVanishingPeriodicSums (⇑catTorusEquiv)
        (inducedBaseCocycle catTorusEquiv measurable_catRoof F) := by
  obtain ⟨x₀, hdense⟩ := ergodic_exists_denseRange_iterate ergodic_catTorus
  have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
  have hr0' : (0 : ℝ) < (rr : ℝ) := by exact_mod_cast hrr0
  have hθα1 : θ ^ (rr : ℝ) < 1 := Real.rpow_lt_one θ_pos.le θ_lt_one hr0'
  have hK : (0 : ℝ) ≤ 2 * Cshadow ^ (rr : ℝ) / (1 - θ ^ (rr : ℝ)) :=
    div_nonneg (by nlinarith [Real.rpow_nonneg Cshadow_pos.le (rr : ℝ)]) (by linarith)
  have hcl : ExpClosing catTorus (rr : ℝ) 1 (2 * Cshadow ^ (rr : ℝ) / (1 - θ ^ (rr : ℝ))) :=
    expClosing_catTorus hr0' (by exact_mod_cast hrr1)
  refine livsic_holderFlow_constRoof catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one
    ?_ lipschitzWith_catTorus F hrr0 hrr1 hF hM hint one_pos hK ?_ (x₀ := x₀) ?_
  · rw [hcoe]; exact continuous_catTorus
  · rw [hcoe]; exact hcl
  · rw [hcoe]; exact hdense

/-- **Flow-native form** of `livsic_catSuspensionHolderFlow`: the obstruction is phrased as the
vanishing of every closed-orbit integral of `F` (period `birkhoffSum catTorus catRoof n p = n` for
the unit roof).  Obtained from the abstract `livsic_holderFlow_constRoof_orbitIntegral`. -/
theorem livsic_catSuspensionHolderFlow_orbitIntegral {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (F : SuspensionSpace catTorusEquiv measurable_catRoof → ℝ)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) *
      embDist catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M)
    (hint : ∀ x a b, IntervalIntegrable
      (fun s => F (suspensionMk catTorusEquiv measurable_catRoof (x, s))) volume a b) :
    IsHolderFlowCoboundary catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one
        (suspensionFlowMap catTorusEquiv measurable_catRoof) F ↔
      ∀ (n : ℕ) (p : T2), (⇑catTorusEquiv)^[n] p = p →
        ∫ s in (0 : ℝ)..(birkhoffSum (⇑catTorusEquiv) catRoof n p),
          F (suspensionFlowMap catTorusEquiv measurable_catRoof s
            (suspensionSection' catTorusEquiv measurable_catRoof p)) = 0 := by
  obtain ⟨x₀, hdense⟩ := ergodic_exists_denseRange_iterate ergodic_catTorus
  have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
  have hr0' : (0 : ℝ) < (rr : ℝ) := by exact_mod_cast hrr0
  have hθα1 : θ ^ (rr : ℝ) < 1 := Real.rpow_lt_one θ_pos.le θ_lt_one hr0'
  have hK : (0 : ℝ) ≤ 2 * Cshadow ^ (rr : ℝ) / (1 - θ ^ (rr : ℝ)) :=
    div_nonneg (by nlinarith [Real.rpow_nonneg Cshadow_pos.le (rr : ℝ)]) (by linarith)
  have hcl : ExpClosing catTorus (rr : ℝ) 1 (2 * Cshadow ^ (rr : ℝ) / (1 - θ ^ (rr : ℝ))) :=
    expClosing_catTorus hr0' (by exact_mod_cast hrr1)
  refine livsic_holderFlow_constRoof_orbitIntegral catTorusEquiv measurable_catRoof rfl
    catTorus_dist_le_one ?_ lipschitzWith_catTorus F hrr0 hrr1 hF hM hint one_pos hK ?_
    (x₀ := x₀) ?_
  · rw [hcoe]; exact continuous_catTorus
  · rw [hcoe]; exact hcl
  · rw [hcoe]; exact hdense

/-! ### The circular Lipschitz modulus of `sin (2π·)` -/

/-- **`sin (2π·)` is `2π`-Lipschitz for the circle-height distance.** For fibre heights `a, b` with
`|a − b| ≤ 1`, `|sin (2π a) − sin (2π b)| ≤ 2π · hgt a b`, where `hgt a b = min |a−b| (1−|a−b|)` is
the circular distance.  Since `sin (2π·)` is `1`-periodic, both the no-wrap (`n = 0`) and the
wrap (`n = ±1`) integer shift give a `2π · |a − b − n|` bound; the two combine through
`mul_min_of_nonneg`. -/
theorem abs_sin_two_pi_sub_le_hgt {a b : ℝ} (hab : |a - b| ≤ 1) :
    |Real.sin (2 * Real.pi * a) - Real.sin (2 * Real.pi * b)| ≤ 2 * Real.pi * hgt a b := by
  have hper : ∀ n : ℤ, |Real.sin (2 * Real.pi * a) - Real.sin (2 * Real.pi * b)|
      ≤ 2 * Real.pi * |a - b - n| := by
    intro n
    have hb : Real.sin (2 * Real.pi * b) = Real.sin (2 * Real.pi * (b + n)) := by
      rw [show 2 * Real.pi * (b + n) = 2 * Real.pi * b + n * (2 * Real.pi) from by ring,
        Real.sin_add_int_mul_two_pi]
    rw [hb]
    refine (Real.abs_sin_sub_sin_le (2 * Real.pi * a) (2 * Real.pi * (b + n))).trans ?_
    rw [show 2 * Real.pi * a - 2 * Real.pi * (b + n) = 2 * Real.pi * (a - b - n) from by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have h1 : |Real.sin (2 * Real.pi * a) - Real.sin (2 * Real.pi * b)| ≤ 2 * Real.pi * |a - b| := by
    simpa using hper 0
  have h2 : |Real.sin (2 * Real.pi * a) - Real.sin (2 * Real.pi * b)|
      ≤ 2 * Real.pi * (1 - |a - b|) := by
    rcases le_or_gt 0 (a - b) with hpos | hneg
    · have h := hper 1
      have hle1 : a - b - 1 ≤ 0 := by linarith [abs_le.mp hab]
      have he : |a - b - ((1 : ℤ) : ℝ)| = 1 - |a - b| := by
        rw [Int.cast_one, abs_of_nonneg hpos, abs_of_nonpos hle1]
        ring
      rwa [he] at h
    · have h := hper (-1)
      have he : |a - b - ((-1 : ℤ) : ℝ)| = 1 - |a - b| := by
        rw [Int.cast_neg, Int.cast_one, abs_of_neg hneg,
          abs_of_nonneg (by linarith [abs_le.mp hab] : (0 : ℝ) ≤ a - b - -1)]
        ring
      rwa [he] at h
  rw [hgt, mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  exact le_min h1 h2

/-! ### Non-vacuity, coboundary side: the `sin (2π·)` fibre observable -/

/-- The `sin (2π·)` fibre observable evaluated at a point equals `sin (2π · h)` where `h` is the
canonical-representative fibre height. -/
theorem sinFibreObservable_eq_sin_rep (p : SuspensionSpace catTorusEquiv measurable_catRoof) :
    sinFibreObservable p = Real.sin (2 * Real.pi *
      (suspensionRep catTorusEquiv measurable_catRoof rfl p).2) := by
  conv_lhs => rw [← suspensionMk_suspensionRep catTorusEquiv measurable_catRoof rfl p]
  simp only [sinFibreObservable, fibreObservable_mk]

/-- **The `sin (2π·)` fibre observable is embedding-`1`-Hölder** with constant `2π`: it depends only
on the fibre height, controlled by the circular Lipschitz bound `abs_sin_two_pi_sub_le_hgt` and the
height lower bound `hgt_le_embDist`. -/
theorem holder_sinFibreObservable (p q : SuspensionSpace catTorusEquiv measurable_catRoof) :
    |sinFibreObservable p - sinFibreObservable q|
      ≤ ((Real.toNNReal (2 * Real.pi) : ℝ≥0) : ℝ) *
        embDist catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one p q
          ^ ((1 : ℝ≥0) : ℝ) := by
  rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 2 * Real.pi), NNReal.coe_one,
    Real.rpow_one, sinFibreObservable_eq_sin_rep p, sinFibreObservable_eq_sin_rep q]
  have ha := suspensionRep_mem_Ico catTorusEquiv measurable_catRoof rfl p
  have hb := suspensionRep_mem_Ico catTorusEquiv measurable_catRoof rfl q
  have hab : |(suspensionRep catTorusEquiv measurable_catRoof rfl p).2
      - (suspensionRep catTorusEquiv measurable_catRoof rfl q).2| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩
  refine (abs_sin_two_pi_sub_le_hgt hab).trans ?_
  gcongr
  exact hgt_le_embDist catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one p q

/-- **Non-vacuity of the coboundary side.** The `sin (2π·)` fibre observable is embedding-Hölder and
*is* a Hölder flow coboundary of the cat-map suspension flow: its induced base observable vanishes
identically (the full-period integral `∫₀¹ sin (2π s) ds = 0`), so the headline equivalence supplies
a *Hölder* flow transfer function.  This upgrades `isFlowCoboundary_sinFibreObservable` (issue #55)
to the classical (Hölder) regularity class.  Contrast with
`const_one_not_isHolderFlowCoboundary_catSuspension`, the obstruction-side witness. -/
theorem isHolderFlowCoboundary_sinFibreObservable :
    IsHolderFlowCoboundary catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one
      (suspensionFlowMap catTorusEquiv measurable_catRoof) sinFibreObservable := by
  refine (livsic_catSuspensionHolderFlow (CF := Real.toNNReal (2 * Real.pi)) (rr := 1) (M := 1)
    one_pos le_rfl sinFibreObservable holder_sinFibreObservable ?_ ?_).mpr
    hasVanishingPeriodicSums_sinFibreObservable
  · intro p
    rw [sinFibreObservable_eq_sin_rep p]; exact Real.abs_sin_le_one _
  · intro x a b
    have hcont : Continuous (fun s : ℝ => sinFibreObservable
        (suspensionMk catTorusEquiv measurable_catRoof (x, s))) := by
      simp only [sinFibreObservable, fibreObservable_mk]; fun_prop
    exact hcont.intervalIntegrable a b

/-! ### Non-vacuity, obstruction side: the constant observable `1` -/

/-- **Non-vacuity of the obstruction side.** The constant observable `1` is embedding-Hölder
(trivially, being constant) yet *not* a Hölder flow coboundary of the cat-map suspension flow: a
Hölder flow coboundary is in particular a flow coboundary
(`IsHolderFlowCoboundary.isFlowCoboundary`), and `const_one_not_isFlowCoboundary_catSuspension`
(issue #36) rules that out, since the induced base observable summed around the period-`1` fixed
point `0` equals `1 ≠ 0`.  Together with
`isHolderFlowCoboundary_sinFibreObservable` this certifies the classical Livšic equivalence has
content on both sides. -/
theorem const_one_not_isHolderFlowCoboundary_catSuspension :
    ¬ IsHolderFlowCoboundary catTorusEquiv measurable_catRoof rfl catTorus_dist_le_one
      (suspensionFlowMap catTorusEquiv measurable_catRoof) (fun _ => (1 : ℝ)) := by
  intro h
  exact const_one_not_isFlowCoboundary_catSuspension h.isFlowCoboundary

end ErgodicTheory.CatMapToral

end
