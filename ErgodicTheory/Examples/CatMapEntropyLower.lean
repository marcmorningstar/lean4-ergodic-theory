/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapCoverMeasure
import ErgodicTheory.Examples.CatMapTelescope
import ErgodicTheory.Examples.CatMapGridPartition
import ErgodicTheory.Examples.CatMapEigenShadow
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-!
# The wall lemma and the sharp entropy lower bound for the Arnold cat map

This module proves **the wall lemma** — every atom of the `n`-fold forward join of the `5 × 5` grid
partition under `catTorus` has `volume` at most `(9√5/25) · λ · μⁿ` — and chains it through the two
conditional crowns of `ErgodicTheory.Examples.CatMapGridPartition` into the *unconditional* sharp
lower bound `log((3+√5)/2) ≤ h(catTorus)` and its strict positivity `0 < h(catTorus)`.

## Strategy

Fix an atom `A_f = ⋂_{k<n} catTorus⁻ᵏ (cell f_k)`.  If it is nonempty, pick `x₀ ∈ A_f`.  Any other
`y ∈ A_f` shares the grid cell of `x₀` at every step `k < n`, so their orbits stay `1/5`-close for
`n` steps; the telescoping export `exists_lift_slab_of_orbit_close` then produces a lift `e₀` of
`y − x₀` lying in the **eigencoordinate slab** `|eigCoordU| ≤ (3/10)·μⁿ⁻¹`, `|eigCoordS| ≤ 3/10`.
Hence `A_f ⊆ x₀ +ᵥ catProj '' eigSlab`.  Translation invariance on `𝕋²`, the projection
contraction `catProj_image_volume_le`, and the explicit `volume_eigSlab = √5·(2a)·(2b)` (an affine
image of a box, via `Measure.addHaar_image_linearMap`) give the geometric bound.

## Main results

* `ErgodicTheory.CatMapToral.eigSlab` — the eigencoordinate slab.
* `ErgodicTheory.CatMapToral.isCompact_eigSlab`, `volume_eigSlab` — its compactness and measure.
* `ErgodicTheory.CatMapToral.catTorus_gridJoinAtom_volume_le` — **the wall lemma**.
* `ErgodicTheory.CatMapToral.catTorus_ksEntropy_ge` — `log((3+√5)/2) ≤ h(catTorus)`.
* `ErgodicTheory.CatMapToral.catTorus_ksEntropy_pos` — `0 < h(catTorus)` (Tier 1 of issue #52).
-/

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
imported cat-map measure modules so that `volume : Measure T2` lines up. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_entLow :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_entLow :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_entLow :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## The eigencoordinate slab -/

/-- The **eigencoordinate slab**: vectors whose unstable coordinate is bounded by `a` and whose
stable coordinate is bounded by `b`. -/
def eigSlab (a b : ℝ) : Set (Fin 2 → ℝ) := {v | |eigCoordU v| ≤ a ∧ |eigCoordS v| ≤ b}

/-- The change-of-basis matrix whose columns are the eigenvectors `vU = ![1, λ-2]`,
`vS = ![1, μ-2]`. -/
def catSlabM : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; lam - 2, mu - 2]

/-- Explicit coordinate form of `catSlabM ·ᵥ p`. -/
lemma catSlabM_mulVec (p : Fin 2 → ℝ) :
    catSlabM *ᵥ p = ![p 0 + p 1, (lam - 2) * p 0 + (mu - 2) * p 1] := by
  funext i
  fin_cases i <;> simp [catSlabM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The unstable coordinate reads off the first entry of the preimage under `catSlabM`. -/
lemma eigCoordU_catSlabM (p : Fin 2 → ℝ) : eigCoordU (catSlabM *ᵥ p) = p 0 := by
  have hlm : lam - mu ≠ 0 := by rw [lam_sub_mu]; positivity
  rw [eigCoordU, catSlabM_mulVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_eq_iff hlm]; ring

/-- The stable coordinate reads off the second entry of the preimage under `catSlabM`. -/
lemma eigCoordS_catSlabM (p : Fin 2 → ℝ) : eigCoordS (catSlabM *ᵥ p) = p 1 := by
  have hlm : lam - mu ≠ 0 := by rw [lam_sub_mu]; positivity
  rw [eigCoordS, catSlabM_mulVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_eq_iff hlm]; ring

/-- **The slab as an affine image of a box.** `eigSlab a b` is the image, under the linear map
`toLin' catSlabM`, of the coordinate box `[-a,a] × [-b,b]`. -/
lemma eigSlab_eq_image (a b : ℝ) :
    eigSlab a b
      = (Matrix.toLin' catSlabM) '' (Set.univ.pi ![Set.Icc (-a) a, Set.Icc (-b) b]) := by
  ext v
  simp only [eigSlab, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hU, hS⟩
    refine ⟨![eigCoordU v, eigCoordS v], ?_, ?_⟩
    · rw [Set.mem_univ_pi]
      intro i
      fin_cases i
      · exact abs_le.mp hU
      · exact abs_le.mp hS
    · rw [Matrix.toLin'_apply, catSlabM_mulVec]
      have hd0 := congrFun (eig_decomp v) 0
      have hd1 := congrFun (eig_decomp v) 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vU, vS,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hd0 hd1
      funext i
      fin_cases i
      · simp only [Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination -hd0
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linear_combination -hd1
  · rintro ⟨p, hp, rfl⟩
    rw [Set.mem_univ_pi] at hp
    have hp0 := hp 0
    have hp1 := hp 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Icc] at hp0 hp1
    rw [Matrix.toLin'_apply, eigCoordU_catSlabM, eigCoordS_catSlabM]
    exact ⟨abs_le.mpr hp0, abs_le.mpr hp1⟩

/-- **The slab is compact** (a continuous linear image of a compact box). -/
lemma isCompact_eigSlab (a b : ℝ) : IsCompact (eigSlab a b) := by
  rw [eigSlab_eq_image]
  refine IsCompact.image ?_ (LinearMap.continuous_of_finiteDimensional _)
  refine isCompact_univ_pi ?_
  intro i
  fin_cases i <;> exact isCompact_Icc

/-- **The measure of the slab.** For `a ≥ 0`, `volume (eigSlab a b) = √5 · (2a) · (2b)`.  The
determinant of `catSlabM` is `μ - λ`, of absolute value `√5`, and the box has volume `(2a)(2b)`. -/
lemma volume_eigSlab (a b : ℝ) (ha : 0 ≤ a) :
    (volume : Measure (Fin 2 → ℝ)) (eigSlab a b)
      = ENNReal.ofReal (Real.sqrt 5 * (2 * a) * (2 * b)) := by
  have hdet : catSlabM.det = mu - lam := by
    simp only [catSlabM, Matrix.det_fin_two_of]; ring
  have habs : |catSlabM.det| = Real.sqrt 5 := by
    rw [hdet, show mu - lam = -(lam - mu) from by ring, abs_neg, lam_sub_mu,
      abs_of_nonneg (Real.sqrt_nonneg 5)]
  have hbox : (volume : Measure (Fin 2 → ℝ)) (Set.univ.pi ![Set.Icc (-a) a, Set.Icc (-b) b])
      = ENNReal.ofReal (2 * a) * ENNReal.ofReal (2 * b) := by
    rw [volume_pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.volume_Icc]
    rw [show a - -a = 2 * a from by ring, show b - -b = 2 * b from by ring]
  rw [eigSlab_eq_image, Measure.addHaar_image_linearMap, LinearMap.det_toLin', habs, hbox,
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * a),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg 5)]
  congr 1; ring

/-! ## The translation-invariance workhorse on the torus -/

/-- Translating a set of `𝕋²` by a constant preserves its `volume`. -/
theorem volume_addLeft_image_T2 (t : T2) (S : Set T2) :
    (volume : Measure T2) ((fun z => t + z) '' S) = volume S := by
  rw [Set.image_add_left, measure_preimage_add]

/-! ## The wall lemma -/

set_option maxHeartbeats 400000 in
-- The nested affine-slab image and measure calc exceed the default heartbeat budget.
/-- **The wall lemma.** Every atom of the `n`-fold forward join of the `5 × 5` grid partition under
`catTorus` has `volume` at most `(9√5/25) · λ · μⁿ` (with `λ = (3+√5)/2`, `μ = (3-√5)/2`).  This is
the geometric input consumed verbatim by the conditional crowns of `CatMapGridPartition`. -/
theorem catTorus_gridJoinAtom_volume_le (n : ℕ) (f : Fin n → Fin 5 × Fin 5) :
    (volume : Measure T2) (Entropy.ksJoinCells catGridPartition.cells catTorus n f)
      ≤ ENNReal.ofReal ((9 * Real.sqrt 5 / 25) * ((3 + Real.sqrt 5) / 2)
          * ((3 - Real.sqrt 5) / 2) ^ n) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [Entropy.ksJoinCells_apply, Set.iInter_of_empty, measure_univ, pow_zero, mul_one,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [two_lt_sqrt5, sqrt5_sq, Real.sqrt_nonneg 5]
  · by_cases hAempty : Entropy.ksJoinCells catGridPartition.cells catTorus n f = ∅
    · rw [hAempty, measure_empty]; exact bot_le
    · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hAempty
      -- The orbit of `x₀` visits the prescribed cells.
      have hmemx : ∀ k : Fin n, catTorus^[(k : ℕ)] x₀ ∈ gridCell (f k).1 (f k).2 := by
        intro k
        have h := hx₀
        rw [Entropy.ksJoinCells_apply, Set.mem_iInter] at h
        have hk := h k
        rw [Set.mem_preimage, catGridPartition_cells] at hk
        exact hk
      -- Every atom point lies in the translated projected slab.
      have hsub : Entropy.ksJoinCells catGridPartition.cells catTorus n f
          ⊆ (fun z => x₀ + z) '' (catProj '' eigSlab (3 / 10 * mu ^ (n - 1)) (3 / 10)) := by
        intro y hy
        have hmemy : ∀ k : Fin n, catTorus^[(k : ℕ)] y ∈ gridCell (f k).1 (f k).2 := by
          intro k
          have h := hy
          rw [Entropy.ksJoinCells_apply, Set.mem_iInter] at h
          have hk := h k
          rw [Set.mem_preimage, catGridPartition_cells] at hk
          exact hk
        have hclose : ∀ k, k < n → dist (catTorus^[k] y) (catTorus^[k] x₀) ≤ 1 / 5 := by
          intro k hk
          exact dist_le_of_mem_gridCell (hmemy ⟨k, hk⟩) (hmemx ⟨k, hk⟩)
        obtain ⟨e₀, he_proj, heU, heS⟩ := exists_lift_slab_of_orbit_close y x₀ n hn hclose
        refine ⟨catProj e₀, ⟨e₀, ⟨heU, heS⟩, rfl⟩, ?_⟩
        change x₀ + catProj e₀ = y
        rw [add_comm]
        exact eq_sub_iff_add_eq.mp he_proj
      -- Geometry: translation invariance, projection contraction, box measure.
      have hann : (0 : ℝ) ≤ 3 / 10 * mu ^ (n - 1) :=
        mul_nonneg (by norm_num) (pow_nonneg mu_pos.le _)
      calc (volume : Measure T2) (Entropy.ksJoinCells catGridPartition.cells catTorus n f)
          ≤ volume ((fun z => x₀ + z) ''
              (catProj '' eigSlab (3 / 10 * mu ^ (n - 1)) (3 / 10))) := measure_mono hsub
        _ = volume (catProj '' eigSlab (3 / 10 * mu ^ (n - 1)) (3 / 10)) :=
              volume_addLeft_image_T2 x₀ _
        _ ≤ volume (eigSlab (3 / 10 * mu ^ (n - 1)) (3 / 10)) :=
              catProj_image_volume_le _ (isCompact_eigSlab _ _)
        _ = ENNReal.ofReal (Real.sqrt 5 * (2 * (3 / 10 * mu ^ (n - 1))) * (2 * (3 / 10))) :=
              volume_eigSlab _ _ hann
        _ = ENNReal.ofReal ((9 * Real.sqrt 5 / 25) * ((3 + Real.sqrt 5) / 2)
              * ((3 - Real.sqrt 5) / 2) ^ n) := by
            rw [show ((3 + Real.sqrt 5) / 2) = lam from rfl,
              show ((3 - Real.sqrt 5) / 2) = mu from rfl]
            have hmupow : mu ^ n = mu ^ (n - 1) * mu := by
              conv_lhs => rw [show n = (n - 1) + 1 from by omega]
              rw [pow_succ]
            rw [hmupow]
            congr 1
            linear_combination (-(9 * Real.sqrt 5 / 25 * mu ^ (n - 1))) * lam_mul_mu

/-! ## The unconditional crowns -/

/-- **Sharp Kolmogorov–Sinai lower bound for the Arnold cat map** (unconditional):
`log((3+√5)/2) ≤ h(catTorus)`. -/
theorem catTorus_ksEntropy_ge :
    ((Real.log ((3 + Real.sqrt 5) / 2) : ℝ) : EReal)
      ≤ Entropy.ksEntropy measurePreserving_catTorus :=
  catTorus_ksEntropy_ge_of_gridAtom_bound catTorus_gridJoinAtom_volume_le

/-- **Strict positivity of the cat-map Kolmogorov–Sinai entropy** (unconditional):
`0 < h(catTorus)`.  This is Tier 1 of issue #52. -/
theorem catTorus_ksEntropy_pos :
    (0 : EReal) < Entropy.ksEntropy measurePreserving_catTorus :=
  catTorus_ksEntropy_pos_of_gridAtom_bound catTorus_gridJoinAtom_volume_le

end ErgodicTheory.CatMapToral
