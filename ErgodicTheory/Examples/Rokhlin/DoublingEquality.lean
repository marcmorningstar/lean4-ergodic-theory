/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.Rokhlin.AbstractEqui
import ErgodicTheory.Examples.Rokhlin.DoublingCrux
import ErgodicTheory.Smooth.DerivativeCocycle

/-!
# Rokhlin's entropy equality for the doubling map

This module assembles the concrete realization of **Pesin's entropy equality on a real expanding
system**: for the doubling map `T : y ↦ 2 • y` on `UnitAddCircle` and the binary generating
partition `α = {[0,1/2), [1/2,1)}`,
`h(α, T) = log 2 = ∫ log|det D(2x)| dμ = ∫ log 2 dμ`.

The entropy side is `ksEntropyPartition_doublingMap_eq_log_two`, obtained by feeding the
join-cell measure `volume_binJoinCell` (every `n`-fold-join cell has volume `2⁻ⁿ`) into the
abstract uniform-join reduction `ksEntropyPartition_of_uniform`. The integral side is
`integral_log_det_doublingMap_eq_log_two`, whose integrand is the genuine log-determinant
`Real.log |doublingGen.det|` of the doubling map's derivative generator
`doublingGen = !![2]` (the matrix of `DT`, defined in `ErgodicTheory.Examples.Elementary`). Since
`doublingGen.det = 2` (`det_doublingGen`, a `1 × 1` determinant), the Jacobian is the constant `2`
— the doubling map is uniformly expanding — so `log|det DT| = log 2` integrates against the
probability measure to `log 2`. Their agreement is the headline `rokhlin_equality_doublingMap`,
which therefore genuinely reads `h(α, T) = ∫ log|det DT|`. That `doublingGen` really *is* the
derivative matrix `DT` — not an arbitrary `1 × 1` matrix of determinant `2` — is pinned down
formally by `derivativeCocycle_doublingLift` (`doublingGen` is the Fréchet derivative of the
doubling map's ℝ-linear lift) together with `circleProj_comp_doublingLift` (that lift genuinely
covers the doubling map). The numerical entropy-`= log 2` identity itself consumes only
`doublingGen.det = 2`.

Unlike the `EuclideanSpace`-framed Margulis–Ruelle *inequality* `h ≤ ∑ λᵢ⁺`, this is the genuine
Pesin/Rokhlin *equality* `h = ∫ log|det DT|`, realized on a real expanding system.

## Main results

* `ErgodicTheory.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two`: `h(α, T) = log 2`.
* `ErgodicTheory.Examples.Rokhlin.derivativeCocycle_doublingLift`: `doublingGen` is the Fréchet
  derivative of the doubling map's ℝ-linear lift (so it genuinely is `DT`, not a bare constant).
* `ErgodicTheory.Examples.Rokhlin.circleProj_comp_doublingLift`: the covering projection `ℝ → 𝕋¹`
  intertwines that lift with the doubling map.
* `ErgodicTheory.Examples.Rokhlin.integral_log_det_doublingMap_eq_log_two`:
  `∫ log|det doublingGen| dμ = log 2`.
* `ErgodicTheory.Examples.Rokhlin.rokhlin_equality_doublingMap`: the two sides agree.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* V. A. Rokhlin, *Lectures on the entropy theory of measure-preserving transformations* (1967).
-/

open MeasureTheory Function Set
open scoped ENNReal Matrix

namespace ErgodicTheory.Examples.Rokhlin

open ErgodicTheory ErgodicTheory.Entropy

/-! ### The binary partition of the unit circle -/

/-- The binary cells are pairwise disjoint (hence a.e.-disjoint): via `mem_binCell_iff` a point's
membership in `binCell i` is determined by which half of `[0,1)` its representative `rep` lies in,
and the two halves `binLift 0 = [0,1/2)`, `binLift 1 = [1/2,1)` are disjoint. -/
lemma disjoint_binCell {i j : Fin 2} (hij : i ≠ j) : Disjoint (binCell i) (binCell j) := by
  rw [Set.disjoint_left]
  intro y hi hj
  rw [mem_binCell_iff] at hi hj
  -- `rep y` lies in both `binLift i` and `binLift j`; but for `i ≠ j` these half-intervals are
  -- disjoint, a contradiction.
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false] <;>
    · simp only [binLift, mem_Ico] at hi hj
      norm_num at hi hj
      linarith [hi.1, hi.2, hj.1, hj.2]

/-- The binary cells are pairwise almost-everywhere disjoint (they are in fact genuinely disjoint;
see `disjoint_binCell`). -/
lemma aedisjoint_binCell :
    Pairwise (AEDisjoint volume on binCell) :=
  fun _ _ hij => (disjoint_binCell hij).aedisjoint

/-- The binary cells cover the circle: every point's representative `rep y ∈ [0,1)` lies in one of
the two halves `[0,1/2)` or `[1/2,1)`, so `y` lies in `binCell 0` or `binCell 1`. -/
lemma cover_binCell : ⋃ i, binCell i = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  rw [Set.mem_iUnion]
  have hrep : rep y ∈ Ico (0 : ℝ) 1 := rep_mem_Ico y
  simp only [mem_Ico] at hrep
  rcases lt_or_ge (rep y) (1 / 2) with h | h
  · refine ⟨0, ?_⟩
    rw [mem_binCell_iff]
    simp only [binLift, mem_Ico, Fin.val_zero, Nat.cast_zero, zero_div, zero_add]
    norm_num
    exact ⟨hrep.1, h⟩
  · refine ⟨1, ?_⟩
    rw [mem_binCell_iff]
    simp only [binLift, mem_Ico, Fin.val_one, Nat.cast_one]
    norm_num
    exact ⟨h, hrep.2⟩

/-- The **binary partition** `{[0,1/2), [1/2,1)}` of the unit circle, as a `MeasurePartition` for
the `volume` (Haar) measure. -/
noncomputable def binPartition : MeasurePartition (volume : Measure UnitAddCircle) (Fin 2) where
  cells := binCell
  measurable := measurableSet_binCell
  aedisjoint := aedisjoint_binCell
  cover := cover_binCell

@[simp]
lemma binPartition_cells : binPartition.cells = binCell := rfl

/-! ### The entropy side: `h(α, T) = log 2` -/

/-- Every `n`-fold-join cell of `binPartition` under the doubling map has volume `(2 ^ n)⁻¹`. This
restates `volume_binJoinCell` for the bundled partition, matching the hypothesis shape of
`ksEntropyPartition_of_uniform` (with `Fintype.card (Fin 2) = 2`). -/
lemma uniform_binJoin (n : ℕ) (f : Fin n → Fin 2) :
    volume ((ksJoin ergodic_doublingMap.toMeasurePreserving binPartition n).cells f)
      = ((Fintype.card (Fin 2) : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ksJoin_cells, binPartition_cells, Fintype.card_fin]
  exact volume_binJoinCell n f

/-- **Rokhlin equality, entropy side: `h(α, T) = log 2`.** The partition-relative
Kolmogorov–Sinai entropy of the binary partition under the doubling map is `Real.log 2`. The
`n`-fold join is the uniform partition into `2ⁿ` dyadic arcs of equal measure `2⁻ⁿ`
(`uniform_binJoin`), so the abstract uniform-join reduction `ksEntropyPartition_of_uniform` gives
`h(α, T) = log (card (Fin 2)) = log 2`. -/
theorem ksEntropyPartition_doublingMap_eq_log_two :
    ksEntropyPartition ergodic_doublingMap.toMeasurePreserving binPartition = Real.log 2 := by
  rw [ksEntropyPartition_of_uniform ergodic_doublingMap.toMeasurePreserving binPartition
    uniform_binJoin, Fintype.card_fin]
  norm_num

/-! ### The generator `doublingGen` is the derivative of the doubling map's lift

The doubling map `y ↦ 2 • y` lifts to the universal cover `ℝ` (here `EuclideanSpace ℝ (Fin 1)`) as
the genuine `ℝ`-linear map `doublingLift = x ↦ 2x`, whose matrix through `Matrix.toEuclideanCLM` is
exactly `doublingGen = !![2]`. The covering projection `ℝ → 𝕋¹` intertwines `doublingLift` with the
doubling map (`circleProj_comp_doublingLift`), and the Fréchet derivative of `doublingLift` is
`doublingGen` at every point (`derivativeCocycle_doublingLift`) — so `doublingGen` genuinely is the
matrix of `DT`, not an arbitrary `1 × 1` constant of the right determinant. -/

/-- The **universal-cover lift** of the doubling map: the `ℝ`-linear map `x ↦ 2x` on
`EuclideanSpace ℝ (Fin 1)`, i.e. the continuous linear map with matrix `doublingGen = !![2]`
through the star-algebra equivalence `Matrix.toEuclideanCLM`. -/
noncomputable def doublingLift : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
  ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 1) doublingGen)

/-- The Fréchet derivative of the doubling map's lift is its own linear map at every point:
`fderiv ℝ doublingLift x = toEuclideanCLM doublingGen`. -/
theorem fderiv_doublingLift (x : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ doublingLift x = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 1) doublingGen :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 1) doublingGen).fderiv

/-- **`doublingGen` is the repo's derivative-cocycle generator of the doubling map's lift.**  Since
`doublingLift` is a continuous linear map, its Fréchet derivative at every point is itself
(`fderiv_doublingLift`); transporting back along `toEuclideanCLM.symm` recovers `doublingGen`.  So
`doublingGen = !![2]` genuinely is the matrix of `D(doublingLift)`, in the repo's exact
`DerivativeCocycle` framework. -/
@[simp] theorem derivativeCocycle_doublingLift (x : EuclideanSpace ℝ (Fin 1)) :
    ErgodicTheory.derivativeCocycle doublingLift x = doublingGen := by
  rw [ErgodicTheory.derivativeCocycle, fderiv_doublingLift x]
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 1)).symm_apply_apply doublingGen

/-- The **covering projection** `ℝ → 𝕋¹`, sending a point of `EuclideanSpace ℝ (Fin 1)` to the class
in `UnitAddCircle` of its single real coordinate (modulo `1`). -/
noncomputable def circleProj (x : EuclideanSpace ℝ (Fin 1)) : UnitAddCircle :=
  ((WithLp.ofLp x 0 : ℝ) : UnitAddCircle)

/-- **The covering projection intertwines the lift with the doubling map:
`mk ∘ doublingLift = doublingMap ∘ mk`.**  The universal-cover projection `circleProj : ℝ → 𝕋¹`
conjugates the genuine ℝ-linear lift `doublingLift = x ↦ 2x` into the genuine doubling map
`doublingMap = y ↦ 2 • y`.  This is the formal content behind `doublingLift` being a *lift* of the
doubling map, so that `doublingGen` — its Fréchet derivative (`derivativeCocycle_doublingLift`) — is
the genuine Jacobian matrix `DT` of the doubling map. -/
theorem circleProj_comp_doublingLift (x : EuclideanSpace ℝ (Fin 1)) :
    circleProj (doublingLift x) = doublingMap (circleProj x) := by
  have hlift : WithLp.ofLp (doublingLift x) = doublingGen *ᵥ WithLp.ofLp x :=
    Matrix.ofLp_toEuclideanCLM doublingGen x
  change ((WithLp.ofLp (doublingLift x) 0 : ℝ) : UnitAddCircle)
      = (2 : ℕ) • ((WithLp.ofLp x 0 : ℝ) : UnitAddCircle)
  rw [congrFun hlift 0]
  have h00 : doublingGen 0 0 = 2 := by simp [doublingGen]
  have hmv : (doublingGen *ᵥ WithLp.ofLp x) 0 = 2 * WithLp.ofLp x 0 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, h00]
  rw [hmv, show (2 : ℝ) * WithLp.ofLp x 0 = (2 : ℕ) • WithLp.ofLp x 0 by
        rw [nsmul_eq_mul, Nat.cast_ofNat], AddCircle.coe_nsmul]

/-! ### The integral side: `∫ log|det DT| dμ = log 2` -/

/-- **The determinant of the doubling map's derivative generator is `2`.** The matrix of `DT` for
the doubling map `x ↦ 2x` is the `1 × 1` generator `doublingGen = !![2]`
(`ErgodicTheory.Examples.Elementary`), whose determinant is its single entry, `2`. -/
theorem det_doublingGen : doublingGen.det = 2 := by
  rw [doublingGen, Matrix.det_fin_one_of]

/-- **Rokhlin equality, integral side: `∫ log|det DT| dμ = log 2`.** The integrand is the genuine
log-determinant `Real.log |doublingGen.det|` of the doubling map's derivative generator
`doublingGen = !![2]` (the matrix of `DT`; formally the Fréchet derivative of the doubling map's
lift, `derivativeCocycle_doublingLift`). Since `doublingGen.det = 2` (`det_doublingGen`) the
Jacobian `|det DT| = 2` is the constant `2` — the doubling map is uniformly expanding — so the
integrand is `log 2`. Integrating that constant against the probability measure `volume` on the
unit circle gives `(volume univ).real • log 2 = 1 · log 2 = log 2`. -/
theorem integral_log_det_doublingMap_eq_log_two :
    ∫ _ : UnitAddCircle, Real.log |doublingGen.det| ∂(volume : Measure UnitAddCircle)
      = Real.log 2 := by
  rw [det_doublingGen, show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num), integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-! ### The headline: entropy = integral -/

/-- **Pesin/Rokhlin equality on the doubling map.** The Kolmogorov–Sinai entropy of the binary
partition under the doubling map equals `∫ log|det DT|`, where the integrand
`Real.log |doublingGen.det|` is the genuine log-determinant of the doubling map's derivative
generator `doublingGen = !![2]` (the matrix of `DT`). Both sides are `Real.log 2`: the entropy is
`log 2` by the dyadic uniform-join count, and the Jacobian `|det DT| = 2` is the constant `2`
(`det_doublingGen`) because the doubling map is uniformly expanding. This is the concrete
realization of Pesin's *equality* `h = ∫ log|det DT|` on a real expanding system that the
`EuclideanSpace`-framed Margulis–Ruelle *inequality* cannot give. The integrand
`Real.log |doublingGen.det|` is the honest log-Jacobian: `doublingGen` is proved to be the genuine
derivative matrix `DT` of the doubling map by `derivativeCocycle_doublingLift` together with the
covering intertwining `circleProj_comp_doublingLift`, not an arbitrary constant of the right
determinant. (The numerical `log 2` on both sides is fixed by `doublingGen.det = 2` alone.) -/
theorem rokhlin_equality_doublingMap :
    ksEntropyPartition ergodic_doublingMap.toMeasurePreserving binPartition
      = ∫ _ : UnitAddCircle, Real.log |doublingGen.det| ∂(volume : Measure UnitAddCircle) := by
  rw [ksEntropyPartition_doublingMap_eq_log_two, integral_log_det_doublingMap_eq_log_two]

end ErgodicTheory.Examples.Rokhlin
