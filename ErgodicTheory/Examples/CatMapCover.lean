/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapToral
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The universal-cover bridge for the cat map on the plain sup-metric torus

This module builds the **universal-cover bridge** for the Arnold cat map `catTorus` on the plain
function type `Fin 2 → ℝ` equipped with the **sup metric** (`Pi.norm_def` / `dist_pi_def`), matching
the product sup metric of the torus `T2 = Fin 2 → UnitAddCircle`.  It is the geometric input for the
Anosov closing lemma of `catTorus` (GitHub issue #32, tier 3, sub-lemmas L1–L3).

The covering projection `catProj : (Fin 2 → ℝ) → T2` reduces each real coordinate modulo `1`; it
intertwines the real linear action `catℝ *ᵥ ·` with the toral automorphism `catTorus`
(`catProj_mulVec`), lifts every toral point (`catProj_surjective`), and is a nonexpanding map for
the sup metrics (`dist_catProj_le`).  The nearest-integer reduction `roundReduce` picks, from a lift
of a toral point, the representative whose sup norm equals the toral distance
(`norm_roundReduce_eq_dist`, `exists_lift_norm_eq`).

This is **deliberately distinct** from `ErgodicTheory.CatMapToral.coverProj`
(`ErgodicTheory/Examples/CatMapDerivativeCocycle.lean`), which lives on `EuclideanSpace ℝ (Fin 2)`
with the **L2** metric and serves the derivative-cocycle layer.  Here everything is on the plain
`Fin 2 → ℝ` with the **sup (L∞)** metric, the metric compatible with the torus's product metric —
these two universal covers carry different metrics and must not be conflated.

## Main results

* `ErgodicTheory.CatMapToral.catProj` — the sup-metric covering projection `(Fin 2 → ℝ) → T2`.
* `ErgodicTheory.CatMapToral.catProj_mulVec` — `catProj` intertwines `catℝ *ᵥ ·` with `catTorus`.
* `ErgodicTheory.CatMapToral.catProj_surjective` — every toral point has a lift.
* `ErgodicTheory.CatMapToral.catTorus_iterate_catProj` — iterates of `catTorus` are matrix powers
  downstairs.
* `ErgodicTheory.CatMapToral.dist_catProj_le` — `catProj` is nonexpanding for the sup metrics.
* `ErgodicTheory.CatMapToral.roundReduce`, `norm_roundReduce_eq_dist`, `exists_lift_norm_eq` — the
  nearest-integer representative realizing the toral distance.
-/

open Matrix

noncomputable section

namespace ErgodicTheory.CatMapToral

/-! ## L1 — the covering projection and the intertwining identity -/

/-- The **universal-cover projection** on the plain sup-metric function type: send a point of
`Fin 2 → ℝ` to its class in `T2 = Fin 2 → UnitAddCircle`, reducing each coordinate modulo `1`.

This is the sup-metric analogue of `coverProj` (which lives on `EuclideanSpace ℝ (Fin 2)` with the
L2 metric); the two must not be conflated. -/
def catProj (v : Fin 2 → ℝ) : T2 := fun i => ((v i : ℝ) : UnitAddCircle)

/-- Coordinatewise intertwining identity: the class of `(catℝ *ᵥ v) i` in `UnitAddCircle` equals the
`i`-th coordinate of the integer toral action `torusMap catℤ` on the classes of `v`.  This turns the
*real* matrix action `catℝ` into the *integer* toral action `catℤ`, via `catℝ = catℤ.map Int.cast`
and additivity of the quotient map `ℝ → UnitAddCircle`. -/
theorem catProj_mulVec_coord (v : Fin 2 → ℝ) (i : Fin 2) :
    (((catℝ *ᵥ v) i : ℝ) : UnitAddCircle) = ∑ j, catℤ i j • ((v j : ℝ) : UnitAddCircle) := by
  have hsum : (catℝ *ᵥ v) i = ∑ j, (catℤ i j) • v j := by
    rw [catℝ_eq_map_catℤ]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, zsmul_eq_mul]
  rw [hsum, Fin.sum_univ_two, Fin.sum_univ_two, AddCircle.coe_add, AddCircle.coe_zsmul,
    AddCircle.coe_zsmul]

/-- **The covering projection intertwines the real linear action with the cat map:**
`catProj (catℝ *ᵥ v) = catTorus (catProj v)`.  The real matrix action upstairs projects to the toral
automorphism `catTorus` downstairs. -/
theorem catProj_mulVec (v : Fin 2 → ℝ) : catProj (catℝ *ᵥ v) = catTorus (catProj v) := by
  funext i
  simp only [catProj, catTorus, torusMap]
  exact catProj_mulVec_coord v i

/-- `catProj` is additive on differences: `catProj (u - v) = catProj u - catProj v`. -/
theorem catProj_sub (u v : Fin 2 → ℝ) : catProj (u - v) = catProj u - catProj v := by
  funext i
  simp only [catProj, Pi.sub_apply, AddCircle.coe_sub]

/-! ## L2 — lifts and iterates -/

/-- **Every toral point lifts.**  `catProj` is surjective, because the quotient map
`ℝ → UnitAddCircle` is surjective in each coordinate. -/
theorem catProj_surjective : Function.Surjective catProj := by
  intro y
  choose v hv using fun i : Fin 2 => QuotientAddGroup.mk_surjective (y i)
  exact ⟨v, funext hv⟩

/-- **Iterates of the cat map are matrix powers downstairs:**
`catTorus^[n] (catProj v) = catProj ((catℝ ^ n) *ᵥ v)`.  Induction from `catProj_mulVec`. -/
theorem catTorus_iterate_catProj (n : ℕ) (v : Fin 2 → ℝ) :
    catTorus^[n] (catProj v) = catProj ((catℝ ^ n) *ᵥ v) := by
  induction n with
  | zero => simp [Matrix.one_mulVec]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← catProj_mulVec, mulVec_mulVec, pow_succ']

/-! ## L3 — the sup-metric bridge

Both the torus `T2` and the plain lift `Fin 2 → ℝ` carry the sup (L∞) metric, so distances reduce to
suprema over the two coordinates of the per-coordinate `UnitAddCircle` norm `‖↑x‖ = |x - round x|`.
-/

/-- The `UnitAddCircle` norm of a class is bounded by the absolute value of a lift:
`‖(↑t : UnitAddCircle)‖ ≤ |t|`.  (The nearest integer `round t` is no farther from `t` than `0`.) -/
theorem norm_coe_le_abs (t : ℝ) : ‖(t : UnitAddCircle)‖ ≤ |t| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le t 0

/-- An integer projects to `0` on the unit circle: `((n : ℝ) : UnitAddCircle) = 0` for `n : ℤ`. -/
theorem coe_intCast_eq_zero (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by rw [zsmul_eq_mul, mul_one]⟩

/-- **`catProj` is nonexpanding for the sup metrics:**
`dist (catProj u) (catProj v) ≤ ‖u - v‖`.  Coordinatewise, `‖↑(u i - v i)‖ ≤ |u i - v i| ≤ ‖u - v‖`;
the torus's sup metric then bounds the whole distance. -/
theorem dist_catProj_le (u v : Fin 2 → ℝ) : dist (catProj u) (catProj v) ≤ ‖u - v‖ := by
  rw [dist_pi_le_iff (norm_nonneg _)]
  intro i
  calc dist (catProj u i) (catProj v i)
      = ‖(↑(u i - v i) : UnitAddCircle)‖ := by
        rw [dist_eq_norm]; simp only [catProj]; rw [← AddCircle.coe_sub]
    _ ≤ |u i - v i| := norm_coe_le_abs _
    _ = ‖(u - v) i‖ := by rw [Pi.sub_apply, Real.norm_eq_abs]
    _ ≤ ‖u - v‖ := norm_le_pi_norm _ i

/-- The **nearest-integer reduction** of a real vector: subtract the nearest integer in each
coordinate, `roundReduce d i = d i - round (d i)`.  It picks the representative of `catProj d` of
smallest sup norm. -/
def roundReduce (d : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => d i - round (d i)

/-- The nearest-integer shift is invisible to `catProj`: `catProj (roundReduce d) = catProj d`. -/
theorem catProj_roundReduce (d : Fin 2 → ℝ) : catProj (roundReduce d) = catProj d := by
  funext i
  simp only [catProj, roundReduce, AddCircle.coe_sub]
  rw [coe_intCast_eq_zero, sub_zero]

/-- **The reduced representative realizes the toral distance to `0`:**
`‖roundReduce d‖ = dist (catProj d) (0 : T2)`.  Coordinatewise both sides equal
`|d i - round (d i)|` (`UnitAddCircle.norm_eq`), and the sup metrics agree. -/
theorem norm_roundReduce_eq_dist (d : Fin 2 → ℝ) :
    ‖roundReduce d‖ = dist (catProj d) (0 : T2) := by
  have hcoord : ∀ i, ‖roundReduce d i‖ = ‖catProj d i‖ := by
    intro i
    simp only [roundReduce, catProj, Real.norm_eq_abs, UnitAddCircle.norm_eq]
  rw [dist_eq_norm, sub_zero]
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [hcoord i]
    exact norm_le_pi_norm _ i
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [← hcoord i]
    exact norm_le_pi_norm _ i

/-- **The distance-realizing lift.**  For any two toral points `x y`, there is a real vector `e`
with `catProj e = x - y` and `‖e‖ = dist x y`.  Lift `x, y` to `u, v`, reduce `u - v` to its
nearest-integer representative, and use `norm_roundReduce_eq_dist`. -/
theorem exists_lift_norm_eq (x y : T2) :
    ∃ e : Fin 2 → ℝ, catProj e = x - y ∧ ‖e‖ = dist x y := by
  obtain ⟨u, hu⟩ := catProj_surjective x
  obtain ⟨v, hv⟩ := catProj_surjective y
  have hcp : catProj (u - v) = x - y := by rw [catProj_sub, hu, hv]
  refine ⟨roundReduce (u - v), ?_, ?_⟩
  · rw [catProj_roundReduce, hcp]
  · rw [norm_roundReduce_eq_dist, hcp, dist_eq_norm, sub_zero, dist_eq_norm]

end ErgodicTheory.CatMapToral
