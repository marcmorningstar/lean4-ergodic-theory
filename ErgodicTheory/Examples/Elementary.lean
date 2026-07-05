/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.ConstantCocycle
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Matrix.Order

/-!
# Elementary worked examples of the multiplicative ergodic theorem

This module instantiates the constant-cocycle Lyapunov spectrum
(`ErgodicTheory.exponents_const`, `ErgodicTheory/Lyapunov/Extensions/ConstantCocycle.lean`) on three
classical dynamical systems. In each case the cocycle generator is a fixed real matrix `M`, so the
Lyapunov exponents are exactly `Real.log |λᵢ(M)|` — the log-moduli of the eigenvalues of `M`,
sorted in non-increasing order. These are documentation examples: they show how to discharge the
ergodicity and integrability hypotheses on a concrete base, and how to read off the spectrum of a
small matrix.

The three systems are:

* the **doubling map** `y ↦ 2 • y` on the circle, with generator `M = !![2]` (top exponent
  `log 2`);
* an **irrational rotation** `y ↦ √2 + y` on the circle, with generator `M = !![1]` (zero
  exponent: rotations are isometries);
* the **Arnold cat-map matrix** `M = !![2,1;1,1]`, whose exponents are `log((3 ± √5)/2)`.

A key linear-algebra helper, `ErgodicTheory.absMatrix_eq_self_of_posSemidef`, shows that
for a positive
semidefinite generator the absolute value `|M| = cfc |·| M` is `M` itself, so its sorted
eigenvalues are the eigenvalues of `M`. All three generators above are positive semidefinite, so
the headline spectra are stated directly in terms of the eigenvalues of `M`.

## Main results

* `ErgodicTheory.absMatrix_eq_self_of_posSemidef` — `|M| = M` for positive semidefinite `M`.
* `ErgodicTheory.doublingMap_topExponent_eq_log_two` — the top Lyapunov exponent of the doubling-map
  constant cocycle (`M = !![2]`) is `Real.log 2`.
* `ErgodicTheory.irrationalRotation_exponents_eq_zero` — the Lyapunov exponent of the irrational
  rotation by `√2` (constant cocycle `M = !![1]`) is `0`.
* `ErgodicTheory.catMapMatrix_exponents` — the two Lyapunov exponents of the cat-map matrix
  `M = !![2,1;1,1]` are `Real.log ((3 + √5) / 2)` and `Real.log ((3 - √5) / 2)`.

## Implementation notes

The genuine Arnold cat map is the toral automorphism of `𝕋²` induced by `!![2,1;1,1]`, and its
ergodicity **is** formalized in this repository: see `ErgodicTheory.CatMapToral.ergodic_catTorus`
(`ErgodicTheory/Examples/CatMapToral.lean`), built on Mathlib's `UnitAddTorus (Fin 2)` and the
multivariate Fourier basis `mFourier`/`mFourierBasis` of `Mathlib.Analysis.Fourier.AddCircleMulti`.
The examples in *this* file are deliberately elementary: we realize the cat-map *matrix* as a
constant cocycle over the (simpler) doubling-map base, since the Lyapunov exponents depend only on
`M` and so coincide with the cat-map exponents regardless of the base dynamics. The upgrade to the
genuine ergodic toral base — and to the genuine Fréchet-derivative cocycle of the cat map's
ℝ²-linear lift — is carried out in `ErgodicTheory/Examples/CatMapToral.lean` and
`ErgodicTheory/Examples/CatMapDerivativeCocycle.lean`. See the docstring of `catMapMatrix_exponents`
for the precise caveat attached to the constant-cocycle realization used here.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix

namespace ErgodicTheory

/-! ## The absolute value of a positive semidefinite matrix is itself -/

/-- **For a positive semidefinite matrix the absolute value is the matrix itself.** Since the
spectrum of `M` is contained in `[0, ∞)`, the function `|·|` agrees with the identity on
`spectrum ℝ M`, so the continuous functional calculus collapses: `|M| = cfc |·| M = cfc id M = M`.

Consequently, for a positive semidefinite generator the sorted eigenvalues of `|M|` (which control
the Lyapunov spectrum of the constant cocycle) are just the eigenvalues of `M`. -/
theorem absMatrix_eq_self_of_posSemidef {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) : absMatrix M = M := by
  -- The `ℝ`-spectrum of a positive semidefinite matrix is contained in `[0, ∞)`.
  have hspec : spectrum ℝ M ⊆ {a : ℝ | 0 ≤ a} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hM).2
  -- `|t| = t = id t` on the spectrum, so the calculus reduces to `cfc id M = M`.
  rw [absMatrix]
  have hcongr : cfc (fun t : ℝ => |t|) M = cfc (id : ℝ → ℝ) M :=
    cfc_congr (f := fun t : ℝ => |t|) (g := id) (fun t ht => abs_of_nonneg (hspec ht))
  rw [hcongr]
  exact cfc_id ℝ M hM.isHermitian.isSelfAdjoint

/-- The sorted-eigenvalue function depends only on the matrix, not on the chosen Hermitian witness:
equal matrices have equal `eigenvalues₀`. (`IsHermitian` is a `Prop`, hence proof-irrelevant once
the matrix is fixed.) -/
theorem eigenvalues₀_congr {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A = B) (i : Fin (Fintype.card (Fin d))) :
    hA.eigenvalues₀ i = hB.eigenvalues₀ i := by
  subst hAB
  rfl

/-- For a positive semidefinite `M`, the sorted eigenvalues of `|M|` are the sorted eigenvalues of
`M`: a direct consequence of `absMatrix_eq_self_of_posSemidef`. -/
theorem eigenvalues₀_absMatrix_of_posSemidef {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) (i : Fin (Fintype.card (Fin d))) :
    (absMatrix_isHermitian M).eigenvalues₀ i = hM.isHermitian.eigenvalues₀ i :=
  eigenvalues₀_congr (absMatrix_isHermitian M) hM.isHermitian
    (absMatrix_eq_self_of_posSemidef hM) i

/-! ## Sums and products of sorted eigenvalues, via trace and determinant

The trace and determinant of a Hermitian matrix are the sum and product of its eigenvalues. Both
Mathlib identities are phrased with `eigenvalues` (indexed by the matrix index type `Fin d`); we
reindex to `eigenvalues₀` (indexed by `Fin (Fintype.card (Fin d))`) so they can be combined with
the Oseledets spectrum, which uses `eigenvalues₀`. -/

/-- **The sum of the sorted eigenvalues is the trace.** A reindexing of
`Matrix.IsHermitian.trace_eq_sum_eigenvalues` from `eigenvalues` to `eigenvalues₀`. -/
theorem sum_eigenvalues₀_eq_trace {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian) :
    ∑ i, hM.eigenvalues₀ i = M.trace := by
  rw [hM.trace_eq_sum_eigenvalues]
  -- `eigenvalues i = eigenvalues₀ (e.symm i)`; reindex the sum over the bijection `e`.
  simp only [Matrix.IsHermitian.eigenvalues, RCLike.ofReal_real_eq_id, id_eq]
  exact (Equiv.sum_comp _ hM.eigenvalues₀).symm

/-- **The product of the sorted eigenvalues is the determinant.** A reindexing of
`Matrix.IsHermitian.det_eq_prod_eigenvalues` from `eigenvalues` to `eigenvalues₀`. -/
theorem prod_eigenvalues₀_eq_det {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian) :
    ∏ i, hM.eigenvalues₀ i = M.det := by
  rw [hM.det_eq_prod_eigenvalues]
  simp only [Matrix.IsHermitian.eigenvalues, RCLike.ofReal_real_eq_id, id_eq]
  exact (Equiv.prod_comp _ hM.eigenvalues₀).symm

/-! ## The measure setup on the unit circle

For the two circle examples the phase space is `UnitAddCircle = AddCircle (1 : ℝ)`, equipped with
its `volume` measure, which is a probability measure (`UnitAddCircle.measure_univ`). We record the
two instances needed by the constant-cocycle machinery. -/

/-- The `volume` on `UnitAddCircle` is a probability measure (total mass `1`,
`UnitAddCircle.measure_univ`).

**Measure convention.**  This uses Mathlib's *default* `AddCircle.measureSpace (1 : ℝ)`, whose
`volume` is `ENNReal.ofReal 1 • addHaarMeasure ⊤` — the convention the circle-ergodicity API
(`AddCircle.ergodic_nsmul`, `AddCircle.ergodic_add_left`) is stated for, hence the one used by the
doubling-map and rotation examples below. The `Fact ((0 : ℝ) < 1)` that this measure space needs is
already supplied globally by Mathlib (`ZeroLEOneClass.factZeroLtOne`), so no local `Fact` instance
is declared here. The companion cat-map modules (`ErgodicTheory/Examples/CatMapToral.lean`,
`CatMapDerivativeCocycle.lean`, `CatMapPerPartition.lean`) instead install a *local* mass-`1`
`MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩`, the convention the multivariate Fourier
API (`Mathlib.Analysis.Fourier.AddCircleMulti`) is stated for. Both are probability measures of
total mass `1` and agree (`volume = 1 • haarAddCircle`); they are distinct instance *terms*, but no
instance diamond arises because each module works under exactly one of them — the cat-map files'
local instance shadows this default within their own file scope. -/
instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-! ## Example 1 — the doubling map

The doubling map `T : y ↦ 2 • y` on the unit circle is ergodic (`AddCircle.ergodic_nsmul`). Its
derivative is multiplication by `2`, so the natural cocycle generator is `M = !![2]`, a `1 × 1`
matrix. Its single eigenvalue is `2`, and the top Lyapunov exponent is `Real.log 2`. -/

/-- The doubling map `y ↦ 2 • y` on the unit circle. -/
noncomputable def doublingMap : UnitAddCircle → UnitAddCircle := fun y => (2 : ℕ) • y

/-- The doubling map is ergodic for the `volume` (Haar) measure on the unit circle. -/
theorem ergodic_doublingMap : Ergodic doublingMap (volume : Measure UnitAddCircle) :=
  AddCircle.ergodic_nsmul (by norm_num)

/-- The constant cocycle generator of the doubling map: the `1 × 1` matrix `!![2]`. -/
def doublingGen : Matrix (Fin 1) (Fin 1) ℝ := !![(2 : ℝ)]

/-- `doublingGen = !![2]` is symmetric. -/
theorem doublingGen_transpose : doublingGenᵀ = doublingGen := by
  ext i j; fin_cases i; fin_cases j; rfl

/-- `doublingGen = !![2]` is Hermitian (over `ℝ`, the same as symmetric). -/
theorem doublingGen_isHermitian : doublingGen.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact doublingGen_transpose

/-- `det !![2] = 2 ≠ 0`, so the generator is invertible. -/
theorem doublingGen_det_ne_zero : doublingGen.det ≠ 0 := by
  rw [doublingGen, Matrix.det_fin_one_of]; norm_num

/-- `!![2]` is positive semidefinite: `xᵀ M x = 2 (x₀)² ≥ 0`. -/
theorem doublingGen_posSemidef : doublingGen.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg doublingGen_isHermitian fun x => ?_
  simp only [doublingGen, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply,
    star_trivial, Matrix.cons_val', Matrix.cons_val_zero, Matrix.of_apply]
  nlinarith [mul_self_nonneg (x 0)]

/-- The single eigenvalue of `!![2]` is `2`: the trace of a `1 × 1` matrix is its only entry, and
the trace equals the sum (here a single term) of the eigenvalues. -/
theorem doublingGen_eigenvalue (i : Fin (Fintype.card (Fin 1))) :
    doublingGen_isHermitian.eigenvalues₀ i = 2 := by
  haveI : Subsingleton (Fin (Fintype.card (Fin 1))) :=
    inferInstanceAs (Subsingleton (Fin 1))
  have hsum : ∑ j, doublingGen_isHermitian.eigenvalues₀ j = (2 : ℝ) := by
    rw [sum_eigenvalues₀_eq_trace, doublingGen, Matrix.trace_fin_one_of]
  rwa [Fintype.sum_subsingleton _ i] at hsum

/-- **Doubling map: the top Lyapunov exponent is `log 2`.** The constant cocycle with generator
`M = !![2]` over the (ergodic) doubling map has top Lyapunov exponent `Real.log 2`: the unique
exponent is `log` of the unique eigenvalue `2` of `M`. This is the priority worked example. -/
theorem doublingMap_topExponent_eq_log_two :
    topExponent ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
        (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
        (const_integrableLogNorm_inv doublingGen)
      = Real.log 2 := by
  -- The unique exponent (`exponents_const` at index `0`) is `log` of the eigenvalue `2`.
  have key := exponents_const ergodic_doublingMap doublingGen_transpose doublingGen_det_ne_zero
    (0 : Fin (Fintype.card (Fin 1)))
  rw [eigenvalues₀_absMatrix_of_posSemidef doublingGen_posSemidef, doublingGen_eigenvalue] at key
  -- `topExponent` is `exponents … ⟨0, _⟩`, definitionally the same index as `key`.
  rw [topExponent]
  exact key

/-! ## Example 2 — an irrational rotation

The rotation `T : y ↦ √2 + y` on the unit circle is ergodic because `√2` is irrational, hence has
infinite additive order (`AddCircle.ergodic_add_left`). A rotation is an isometry, so its
derivative is the identity; the natural cocycle generator is `M = !![1]`, with eigenvalue `1` and
Lyapunov exponent `log 1 = 0`. -/

/-- The constant cocycle generator of a circle rotation: the `1 × 1` identity `!![1]`. -/
def rotationGen : Matrix (Fin 1) (Fin 1) ℝ := !![(1 : ℝ)]

/-- `rotationGen = !![1]` is symmetric. -/
theorem rotationGen_transpose : rotationGenᵀ = rotationGen := by
  ext i j; fin_cases i; fin_cases j; rfl

/-- `rotationGen = !![1]` is Hermitian. -/
theorem rotationGen_isHermitian : rotationGen.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact rotationGen_transpose

/-- `det !![1] = 1 ≠ 0`. -/
theorem rotationGen_det_ne_zero : rotationGen.det ≠ 0 := by
  rw [rotationGen, Matrix.det_fin_one_of]; norm_num

/-- `!![1]` is positive semidefinite: `xᵀ M x = (x₀)² ≥ 0`. -/
theorem rotationGen_posSemidef : rotationGen.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg rotationGen_isHermitian fun x => ?_
  simp only [rotationGen, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply,
    star_trivial, Matrix.cons_val', Matrix.cons_val_zero, Matrix.of_apply]
  nlinarith [mul_self_nonneg (x 0)]

/-- The single eigenvalue of the identity generator `!![1]` is `1` (trace `= 1`). -/
theorem rotationGen_eigenvalue (i : Fin (Fintype.card (Fin 1))) :
    rotationGen_isHermitian.eigenvalues₀ i = 1 := by
  haveI : Subsingleton (Fin (Fintype.card (Fin 1))) :=
    inferInstanceAs (Subsingleton (Fin 1))
  have hsum : ∑ j, rotationGen_isHermitian.eigenvalues₀ j = (1 : ℝ) := by
    rw [sum_eigenvalues₀_eq_trace, rotationGen, Matrix.trace_fin_one_of]
  rwa [Fintype.sum_subsingleton _ i] at hsum

/-- **A rotation by an angle of infinite order is ergodic, parametric version.** For any
`a : UnitAddCircle` with `addOrderOf a = 0` (equivalently, `a` is not a rational point of the
circle), the rotation `y ↦ a + y` is ergodic. We use this with `a = √2`. -/
theorem ergodic_rotation_of_addOrderOf_eq_zero {a : UnitAddCircle} (ha : addOrderOf a = 0) :
    Ergodic (a + ·) (volume : Measure UnitAddCircle) :=
  AddCircle.ergodic_add_left.mpr ha

/-- The rotation angle `√2`, viewed as a point of the unit circle, has infinite additive order: a
point of `AddCircle (1 : ℝ)` has finite order iff its representative is rational, and `√2` is
irrational. -/
theorem addOrderOf_sqrtTwo_eq_zero :
    addOrderOf ((↑(Real.sqrt 2) : UnitAddCircle)) = 0 := by
  rw [addOrderOf_eq_zero_iff]
  -- Finite order would give a rational `q` with `(q : ℝ) = √2 / 1 = √2`, contradicting
  -- irrationality of `√2`.
  rw [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div]
  rintro ⟨q, hq⟩
  rw [div_one] at hq
  exact irrational_sqrt_two ⟨q, hq⟩

/-- The irrational rotation `y ↦ √2 + y` on the unit circle. -/
noncomputable def irrationalRotation : UnitAddCircle → UnitAddCircle :=
  fun y => (↑(Real.sqrt 2) : UnitAddCircle) + y

/-- The rotation by `√2` is ergodic. -/
theorem ergodic_irrationalRotation :
    Ergodic irrationalRotation (volume : Measure UnitAddCircle) :=
  ergodic_rotation_of_addOrderOf_eq_zero addOrderOf_sqrtTwo_eq_zero

/-- **Irrational rotation: the Lyapunov exponent is `0`.** The constant cocycle with the isometry
generator `M = !![1]` over the (ergodic) irrational rotation by `√2` has Lyapunov exponent `0`: the
unique eigenvalue of `M` is `1`, and `log 1 = 0`. Rotations preserve lengths, so they exhibit no
exponential growth. -/
theorem irrationalRotation_exponents_eq_zero (i : Fin (Fintype.card (Fin 1))) :
    exponents ergodic_irrationalRotation (const_det_ne_zero rotationGen_det_ne_zero)
        (const_measurable rotationGen) (const_integrableLogNorm rotationGen)
        (const_integrableLogNorm_inv rotationGen)
        ⟨(i : ℕ), lt_of_lt_of_eq i.isLt (Fintype.card_fin 1)⟩
      = 0 := by
  rw [exponents_const ergodic_irrationalRotation rotationGen_transpose rotationGen_det_ne_zero i,
    eigenvalues₀_absMatrix_of_posSemidef rotationGen_posSemidef, rotationGen_eigenvalue,
    Real.log_one]

/-! ## Example 3 — the Arnold cat-map matrix

The Arnold cat map is the toral automorphism of `𝕋²` induced by the matrix `!![2,1;1,1]`. Its
ergodicity is formalized separately as `ErgodicTheory.CatMapToral.ergodic_catTorus`
(`ErgodicTheory/Examples/CatMapToral.lean`); here we keep the example elementary and realize
the cat-map
*matrix* as a constant cocycle over the simpler doubling-map base. The Lyapunov exponents depend
only on the generator, so they are the genuine cat-map exponents.

The matrix is symmetric and positive definite with trace `3` and determinant `1`. If `a ≥ b` are
its (sorted) eigenvalues, then `a + b = 3` and `a b = 1`, hence `(a - b)² = (a+b)² - 4ab = 5`, so
`a - b = √5`, giving `a = (3 + √5)/2` and `b = (3 - √5)/2`. The Lyapunov exponents are `log a` and
`log b`. -/

/-- The Arnold cat-map matrix `!![2,1;1,1]`. -/
def catMapGen : Matrix (Fin 2) (Fin 2) ℝ := !![(2 : ℝ), 1; 1, 1]

/-- `catMapGen = !![2,1;1,1]` is symmetric. -/
theorem catMapGen_transpose : catMapGenᵀ = catMapGen := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `catMapGen = !![2,1;1,1]` is Hermitian. -/
theorem catMapGen_isHermitian : catMapGen.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact catMapGen_transpose

/-- The cat-map matrix is positive definite: `xᵀ M x = (x₀)² + (x₀ + x₁)² > 0` for `x ≠ 0`. -/
theorem catMapGen_posDef : catMapGen.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos catMapGen_isHermitian fun x hx => ?_
  simp only [catMapGen, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.empty_val']
  -- `x ≠ 0` forces one coordinate to be nonzero; then `x₀² + (x₀ + x₁)² > 0`.
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hx (funext fun j => by fin_cases j <;> simp [h.1, h.2])
  rcases hx' with h0 | h1
  · nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 + x 1), mul_self_pos.mpr h0]
  · nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 + x 1), mul_self_pos.mpr h1]

/-- The cat-map matrix is positive semidefinite. -/
theorem catMapGen_posSemidef : catMapGen.PosSemidef := catMapGen_posDef.posSemidef

/-- `det !![2,1;1,1] = 2·1 - 1·1 = 1 ≠ 0`. -/
theorem catMapGen_det_ne_zero : catMapGen.det ≠ 0 := by
  rw [catMapGen, Matrix.det_fin_two_of]; norm_num

/-- The sum of the two sorted eigenvalues of the cat-map matrix is the trace, `3`. -/
theorem catMapGen_eigenvalues_sum :
    catMapGen_isHermitian.eigenvalues₀ 0 + catMapGen_isHermitian.eigenvalues₀ 1 = 3 := by
  have hsum : ∑ j, catMapGen_isHermitian.eigenvalues₀ j = (3 : ℝ) := by
    rw [sum_eigenvalues₀_eq_trace, catMapGen, Matrix.trace_fin_two_of]; norm_num
  -- Expand the two-element sum; `Fin (Fintype.card (Fin 2))` is defeq to `Fin 2`.
  rwa [show (∑ j, catMapGen_isHermitian.eigenvalues₀ j)
    = catMapGen_isHermitian.eigenvalues₀ 0 + catMapGen_isHermitian.eigenvalues₀ 1 from
      Fin.sum_univ_two _] at hsum

/-- The product of the two sorted eigenvalues of the cat-map matrix is the determinant, `1`. -/
theorem catMapGen_eigenvalues_prod :
    catMapGen_isHermitian.eigenvalues₀ 0 * catMapGen_isHermitian.eigenvalues₀ 1 = 1 := by
  have hprod : ∏ j, catMapGen_isHermitian.eigenvalues₀ j = (1 : ℝ) := by
    rw [prod_eigenvalues₀_eq_det, catMapGen, Matrix.det_fin_two_of]; norm_num
  rwa [show (∏ j, catMapGen_isHermitian.eigenvalues₀ j)
    = catMapGen_isHermitian.eigenvalues₀ 0 * catMapGen_isHermitian.eigenvalues₀ 1 from
      Fin.prod_univ_two _] at hprod

/-- The larger sorted eigenvalue dominates the smaller: `eigenvalues₀ 1 ≤ eigenvalues₀ 0`
(`eigenvalues₀` is antitone). -/
theorem catMapGen_eigenvalues_le :
    catMapGen_isHermitian.eigenvalues₀ 1 ≤ catMapGen_isHermitian.eigenvalues₀ 0 :=
  catMapGen_isHermitian.eigenvalues₀_antitone (by decide)

/-- The two sorted eigenvalues of the cat-map matrix are `(3 + √5)/2` and `(3 - √5)/2`.

From `a + b = 3`, `a b = 1`, and `a ≥ b` we get `(a - b)² = (a+b)² - 4ab = 5`, hence `a - b = √5`,
and solving the linear system gives the closed forms. -/
theorem catMapGen_eigenvalues_closedForm :
    catMapGen_isHermitian.eigenvalues₀ 0 = (3 + Real.sqrt 5) / 2 ∧
      catMapGen_isHermitian.eigenvalues₀ 1 = (3 - Real.sqrt 5) / 2 := by
  set a := catMapGen_isHermitian.eigenvalues₀ 0 with ha
  set b := catMapGen_isHermitian.eigenvalues₀ 1 with hb
  have hsum : a + b = 3 := catMapGen_eigenvalues_sum
  have hprod : a * b = 1 := catMapGen_eigenvalues_prod
  have hle : b ≤ a := catMapGen_eigenvalues_le
  -- `(a - b)² = (a + b)² - 4 a b = 9 - 4 = 5`.
  have hsq : (a - b) ^ 2 = 5 := by nlinarith [hsum, hprod]
  -- `a - b ≥ 0`, so `a - b = √5`.
  have hdiff : a - b = Real.sqrt 5 := by
    rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by norm_num) (by linarith), hsq]
  -- Solve the linear system `a + b = 3`, `a - b = √5`.
  exact ⟨by linarith [hsum, hdiff], by linarith [hsum, hdiff]⟩

/-- The constant cocycle realization of the cat-map matrix uses the doubling map as its ergodic
base; only the (constant) generator `catMapGen` matters for the spectrum. -/
theorem ergodic_catMapBase : Ergodic doublingMap (volume : Measure UnitAddCircle) :=
  ergodic_doublingMap

/-- **The cat-map matrix: closed-form Lyapunov spectrum.** Realized as a constant cocycle with
generator `M = !![2,1;1,1]` over the (ergodic) doubling map, the two Lyapunov exponents are
`Real.log ((3 + √5)/2)` and `Real.log ((3 - √5)/2)` — the logs of the eigenvalues of the cat-map
matrix.

**Honesty caveat.** The cocycle here is the *constant* matrix `M = !![2,1;1,1]`, **not** the
derivative cocycle of the genuine Arnold cat map (the hyperbolic toral automorphism of `𝕋²`). The
exponents nonetheless coincide with the cat-map exponents, because they are determined by `M`. The
genuine toral-automorphism dynamics — ergodicity of the hyperbolic toral automorphism, and its
genuine Fréchet-derivative cocycle — *is* formalized elsewhere in this repository, on Mathlib's
`UnitAddTorus (Fin 2)` and multivariate `ℤ²` Fourier basis: see
`ErgodicTheory.CatMapToral.ergodic_catTorus`,
`ErgodicTheory.CatMapToral.catTorus_constCocycle_exponents`,
and `ErgodicTheory.CatMapToral.catLift_derivativeCocycle_topExponent_pos`
(`ErgodicTheory/Examples/CatMapToral.lean`, `ErgodicTheory/Examples/CatMapDerivativeCocycle.lean`).
This
elementary constant-cocycle version is retained as the simplest illustration. -/
theorem catMapMatrix_exponents :
    exponents ergodic_catMapBase (const_det_ne_zero catMapGen_det_ne_zero)
        (const_measurable catMapGen) (const_integrableLogNorm catMapGen)
        (const_integrableLogNorm_inv catMapGen)
        ⟨(0 : ℕ), lt_of_lt_of_eq (Fin.isLt (0 : Fin (Fintype.card (Fin 2)))) (Fintype.card_fin 2)⟩
      = Real.log ((3 + Real.sqrt 5) / 2) ∧
    exponents ergodic_catMapBase (const_det_ne_zero catMapGen_det_ne_zero)
        (const_measurable catMapGen) (const_integrableLogNorm catMapGen)
        (const_integrableLogNorm_inv catMapGen)
        ⟨(1 : ℕ), lt_of_lt_of_eq (Fin.isLt (1 : Fin (Fintype.card (Fin 2)))) (Fintype.card_fin 2)⟩
      = Real.log ((3 - Real.sqrt 5) / 2) := by
  obtain ⟨h0, h1⟩ := catMapGen_eigenvalues_closedForm
  refine ⟨?_, ?_⟩
  · have key := exponents_const ergodic_catMapBase catMapGen_transpose catMapGen_det_ne_zero
      (0 : Fin (Fintype.card (Fin 2)))
    rw [eigenvalues₀_absMatrix_of_posSemidef catMapGen_posSemidef, h0] at key
    exact key
  · have key := exponents_const ergodic_catMapBase catMapGen_transpose catMapGen_det_ne_zero
      (1 : Fin (Fintype.card (Fin 2)))
    rw [eigenvalues₀_absMatrix_of_posSemidef catMapGen_posSemidef, h1] at key
    exact key

/-- **The cat-map exponents sum to zero** (the cocycle is conservative: `det M = 1`). Equivalently,
`log a + log b = log (a b) = log 1 = 0`. -/
theorem catMapMatrix_exponents_sum_eq_zero :
    exponents ergodic_catMapBase (const_det_ne_zero catMapGen_det_ne_zero)
        (const_measurable catMapGen) (const_integrableLogNorm catMapGen)
        (const_integrableLogNorm_inv catMapGen)
        ⟨(0 : ℕ), lt_of_lt_of_eq (Fin.isLt (0 : Fin (Fintype.card (Fin 2)))) (Fintype.card_fin 2)⟩
      + exponents ergodic_catMapBase (const_det_ne_zero catMapGen_det_ne_zero)
        (const_measurable catMapGen) (const_integrableLogNorm catMapGen)
        (const_integrableLogNorm_inv catMapGen)
        ⟨(1 : ℕ), lt_of_lt_of_eq (Fin.isLt (1 : Fin (Fintype.card (Fin 2)))) (Fintype.card_fin 2)⟩
      = 0 := by
  obtain ⟨h0, h1⟩ := catMapMatrix_exponents
  -- `√5 < 3`, so both factors `(3 ± √5)/2` are positive (hence nonzero).
  have hlt : Real.sqrt 5 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  rw [h0, h1, ← Real.log_mul (by positivity) (by positivity),
    show (3 + Real.sqrt 5) / 2 * ((3 - Real.sqrt 5) / 2) = (9 - Real.sqrt 5 ^ 2) / 4 by ring,
    Real.sq_sqrt (by norm_num)]
  norm_num

end ErgodicTheory
