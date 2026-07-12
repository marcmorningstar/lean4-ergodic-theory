/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.HolderFlowCoboundaryVar
import ErgodicTheory.Examples.CatMapClosing
import ErgodicTheory.Examples.CatMapSuspensionHolderLivsic

/-!
# The classical (Hölder) Livšic theorem on a *variable-roof* Arnold cat-map suspension flow

This module (issue #63, tier-3 instantiation) provides the **variable-roof witness** for the
abstract `ErgodicTheory.livsic_holderFlow_varRoof`, which the constant-roof cat instantiation
(`ErgodicTheory/Examples/CatMapSuspensionHolderLivsic.lean`) left uninstantiated. Over the genuine
Arnold cat base `catTorus : 𝕋² → 𝕋²` we equip the suspension with a **genuinely non-constant,
Lipschitz roof**

`catVarRoof x = 2 + 4⁻¹ · ‖x 0‖`

(where `‖·‖` is the `UnitAddCircle` norm of the first coordinate, which ranges over `[0, 1/2]`): the
roof is `(1/4)`-Lipschitz, measurable, and takes values in `[2, 2 + 1/8] ⊆ [7/4, 9/4]` — in
particular value `2` at the origin (`x 0 = 0`) and `2 + 1/8` at a half-period coordinate, so it is
*not* constant. This discharges the classical Bowen–Walters roof hypotheses (`ρmin = 7/4`,
`ρmax = 9/4`, `Cρ = 1/4`) and, together with the cat base-system hypotheses (diameter, Lipschitz
constant, continuity, the summed exponential closing property, a dense forward orbit), instantiates
the variable-roof Hölder flow-Livšic equivalence.

## Main results

* `ErgodicTheory.CatMapToral.catVarRoof` — the non-constant Lipschitz roof, with
  `measurable_catVarRoof`, `catVarRoof_lb`/`catVarRoof_ub` (the `[7/4, 9/4]` bounds) and
  `lipschitzWith_catVarRoof`.
* `ErgodicTheory.CatMapToral.livsic_catVarRoofHolderFlow` — **the headline**: the variable-roof
  Hölder flow-Livšic equivalence for the cat-map suspension flow (general observable `F`).
* `ErgodicTheory.CatMapToral.livsic_catVarRoofHolderFlow_witness` — a concrete instantiation with
  the zero observable, certifying that the full hypothesis bundle of `livsic_holderFlow_varRoof`
  is simultaneously satisfiable together with the non-constant roof.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972) 1278–1301.
* R. Bowen, P. Walters, *Expansive one-parameter flows*, J. Diff. Eq. **12** (1972) 180–193.
* L. Barreira, C. Radu, C. Wolf, *Dimension of measures for suspension flows*, Dyn. Syst. **19**
  (2004) §2.1.
-/

open MeasureTheory Function Matrix
open scoped NNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
`MeasureSpace UnitAddCircle` convention of the sibling cat-map modules so that the ambient `volume`
here is *the same* product Haar probability measure for which `ergodic_catTorus` is stated.
(Uniquely named to avoid colliding with the identical local instances of the sibling modules.) -/
noncomputable local instance instMeasureSpaceUnitAddCircleVarRoofHolderLivsic :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarUnitAddCircleVarRoofHolderLivsic :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityUnitAddCircleVarRoofHolderLivsic :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

open ErgodicTheory

/-! ### The non-constant Lipschitz roof -/

/-- **A genuinely non-constant Lipschitz roof over `𝕋²`.** `catVarRoof x = 2 + 4⁻¹ · ‖x 0‖`, where
`‖x 0‖ ∈ [0, 1/2]` is the `UnitAddCircle` norm of the first coordinate. Its range is
`[2, 2 + 1/8] ⊆ [7/4, 9/4]`; it is `2` at the origin and `2 + 1/8` at a half-period coordinate. -/
def catVarRoof : T2 → ℝ := fun x => 2 + 4⁻¹ * ‖x 0‖

/-- `catVarRoof` is continuous (hence measurable): a constant plus a scalar multiple of the
continuous coordinate norm `x ↦ ‖x 0‖`. -/
theorem continuous_catVarRoof : Continuous catVarRoof :=
  continuous_const.add (continuous_const.mul ((continuous_apply 0).norm))

/-- `catVarRoof` is measurable. -/
theorem measurable_catVarRoof : Measurable catVarRoof := continuous_catVarRoof.measurable

/-- The roof lower bound `ρmin = 7/4` is positive (the `hρpos` hypothesis of the abstract
theorem). -/
theorem catVarRoof_pos : (0 : ℝ) < 7 / 4 := by norm_num

/-- **Roof lower bound.** `7/4 ≤ catVarRoof x`, since `catVarRoof x = 2 + 4⁻¹ · ‖x 0‖ ≥ 2`. -/
theorem catVarRoof_lb : ∀ x, (7 / 4 : ℝ) ≤ catVarRoof x := by
  intro x
  have h : (0 : ℝ) ≤ 4⁻¹ * ‖x 0‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  simp only [catVarRoof]; linarith

/-- **Roof upper bound.** `catVarRoof x ≤ 9/4`, since `‖x 0‖ ≤ 1/2` gives
`catVarRoof x ≤ 2 + 1/8 = 17/8 ≤ 9/4`. -/
theorem catVarRoof_ub : ∀ x, catVarRoof x ≤ (9 / 4 : ℝ) := by
  intro x
  have h : ‖x 0‖ ≤ (1 : ℝ) / 2 := by
    have := (AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero : ‖x 0‖ ≤ |(1 : ℝ)| / 2)
    simpa using this
  have hmul : (4 : ℝ)⁻¹ * ‖x 0‖ ≤ 4⁻¹ * (1 / 2) := mul_le_mul_of_nonneg_left h (by norm_num)
  simp only [catVarRoof]; linarith

/-- **The roof is `(1/4)`-Lipschitz.** `catVarRoof x − catVarRoof y = 4⁻¹ · (‖x 0‖ − ‖y 0‖)`, and
`|‖x 0‖ − ‖y 0‖| ≤ dist (x 0) (y 0) ≤ dist x y` (the coordinate projection is `1`-Lipschitz for the
sup metric, the norm is `1`-Lipschitz). -/
theorem lipschitzWith_catVarRoof : LipschitzWith 4⁻¹ catVarRoof := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  have hsub : catVarRoof x - catVarRoof y = 4⁻¹ * (‖x 0‖ - ‖y 0‖) := by
    simp only [catVarRoof]; ring
  rw [hsub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4⁻¹)]
  have hb : |‖x 0‖ - ‖y 0‖| ≤ dist x y := by
    refine (abs_norm_sub_norm_le (x 0) (y 0)).trans ?_
    rw [← dist_eq_norm]; exact dist_le_pi_dist x y 0
  have hcoe : ((4⁻¹ : ℝ≥0) : ℝ) = (4 : ℝ)⁻¹ := by rw [NNReal.coe_inv]; norm_num
  rw [hcoe]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

/-! ### The headline: the variable-roof Hölder flow-Livšic equivalence -/

/-- **The classical-strength Livšic theorem for the *variable-roof* cat-map suspension flow.**
For an `embDistVar`-`r`-Hölder, bounded flow observable `F` (with interval-integrable fibre
restrictions), `F` is a **variable-roof Hölder flow coboundary** of the suspension flow over the
Arnold cat map with the non-constant roof `catVarRoof` **iff** every periodic Birkhoff sum of its
induced base observable vanishes. The base-system hypotheses of `livsic_holderFlow_varRoof` are
discharged exactly as in the
constant-roof case (`catTorus_dist_le_one`, `lipschitzWith_catTorus`, `continuous_catTorus`,
`expClosing_catTorus`, a dense orbit from `ergodic_catTorus`); the roof hypotheses are discharged by
`catVarRoof_pos`, `catVarRoof_lb`, `catVarRoof_ub`, `lipschitzWith_catVarRoof`. -/
theorem livsic_catVarRoofHolderFlow {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (F : SuspensionSpace catTorusEquiv measurable_catVarRoof → ℝ)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) *
      embDistVar catTorusEquiv measurable_catVarRoof catVarRoof_pos catVarRoof_lb
        catTorus_dist_le_one p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M)
    (hint : ∀ x a b, IntervalIntegrable
      (fun s => F (suspensionMk catTorusEquiv measurable_catVarRoof (x, s))) volume a b) :
    IsHolderFlowCoboundaryVar catTorusEquiv measurable_catVarRoof catVarRoof_pos catVarRoof_lb
        catTorus_dist_le_one (suspensionFlowMap catTorusEquiv measurable_catVarRoof) F ↔
      HasVanishingPeriodicSums (⇑catTorusEquiv)
        (inducedBaseCocycle catTorusEquiv measurable_catVarRoof F) := by
  obtain ⟨x₀, hdense⟩ := ergodic_exists_denseRange_iterate ergodic_catTorus
  have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
  have hr0' : (0 : ℝ) < (rr : ℝ) := by exact_mod_cast hrr0
  have hθα1 : θ ^ (rr : ℝ) < 1 := Real.rpow_lt_one θ_pos.le θ_lt_one hr0'
  have hK : (0 : ℝ) ≤ 2 * Cshadow ^ (rr : ℝ) / (1 - θ ^ (rr : ℝ)) :=
    div_nonneg (by nlinarith [Real.rpow_nonneg Cshadow_pos.le (rr : ℝ)]) (by linarith)
  have hcl : ExpClosing catTorus (rr : ℝ) 1 (2 * Cshadow ^ (rr : ℝ) / (1 - θ ^ (rr : ℝ))) :=
    expClosing_catTorus hr0' (by exact_mod_cast hrr1)
  refine livsic_holderFlow_varRoof catTorusEquiv measurable_catVarRoof catVarRoof_pos catVarRoof_lb
    catTorus_dist_le_one ?_ lipschitzWith_catTorus F hrr0 hrr1 hF hM catVarRoof_ub
    lipschitzWith_catVarRoof hint one_pos hK ?_ (x₀ := x₀) ?_
  · rw [hcoe]; exact continuous_catTorus
  · rw [hcoe]; exact hcl
  · rw [hcoe]; exact hdense

/-! ### The witness: the full hypothesis bundle is satisfiable -/

/-- **Variable-roof witness.** The zero observable is a variable-roof Hölder flow coboundary of the
cat-map suspension flow with the non-constant roof `catVarRoof`.  This certifies that the entire
hypothesis bundle of `livsic_holderFlow_varRoof` — the `embDistVar`-Hölder and boundedness
conditions on `F`, the interval-integrability of the fibre restrictions, *and* the classical
Bowen–Walters roof conditions (`ρmin ≤ catVarRoof ≤ ρmax` with a Lipschitz, genuinely non-constant
roof) — is simultaneously satisfiable, so `livsic_catVarRoofHolderFlow` is non-vacuous.  The zero
observable has vanishing induced base observable (`∫ 0 = 0`), so the equivalence yields a Hölder
flow transfer function. -/
theorem livsic_catVarRoofHolderFlow_witness :
    IsHolderFlowCoboundaryVar catTorusEquiv measurable_catVarRoof catVarRoof_pos catVarRoof_lb
      catTorus_dist_le_one (suspensionFlowMap catTorusEquiv measurable_catVarRoof)
      (fun _ => (0 : ℝ)) := by
  refine (livsic_catVarRoofHolderFlow (CF := 0) (rr := 1) (M := 0) one_pos le_rfl
    (fun _ => (0 : ℝ)) ?_ ?_ ?_).mpr ?_
  · intro p q; simp
  · intro p; simp
  · intro x a b
    have hfun : (fun s => (fun _ => (0 : ℝ))
        (suspensionMk catTorusEquiv measurable_catVarRoof (x, s))) = fun _ => (0 : ℝ) := rfl
    rw [hfun]; exact intervalIntegrable_const
  · intro n p _
    have hzero : inducedBaseCocycle catTorusEquiv measurable_catVarRoof (fun _ => (0 : ℝ))
        = fun _ => (0 : ℝ) := by
      funext x; simp [inducedBaseCocycle]
    rw [hzero]; simp [birkhoffSum]

end ErgodicTheory.CatMapToral

end
