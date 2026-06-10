import Oseledets.Lyapunov.Fischer
import Oseledets.Lyapunov.ExteriorNorm
import Oseledets.Lyapunov.OseledetsLimit
import Mathlib.Analysis.Matrix.PosDef

/-!
# ForwardFrames — the determinant/Gram/angle factorization (`hfact`) and the
  fast-frame volume exponent bound (`hVF` upper half).

This file attacks the two open inputs of `SqueezeData` (committed in
`Oseledets/Lyapunov/ForwardSqueezeData.lean`):

* **hfact** — the EXACT (every `n`) determinant/Gram/angle factorization along the orbit, via the
  squared-determinant Gram identity and the (definitional) inter-block sine.
* **hVF (upper half)** — the fast-frame volume exponent is bounded by the top-`k` singular-value
  product, hence its `limsup` is bounded by the `Γ_k`-type exponent supplied by the committed
  exterior-Kingman layer.

## Main results

### Linear-algebra core (positivity + factorization)

* `Frames.det_gram_pos` — for a full-column-rank real frame `W`, `0 < det (Wᵀ W)`.
* `Frames.det_gram_nonneg` — `0 ≤ det (Wᵀ W)` always.
* `Frames.image_block_inl/inr` — `(M·Y).submatrix id Sum.inl = M · Y_F` (the image of a block).
* `Frames.thetaSq`, `Frames.thetaSq_nonneg`, `Frames.thetaSq_le_one` — the inter-block squared sine
  `θ² := det Gram(M Y) / (det Gram(M Y_F)·det Gram(M Y_S))`, with `0 ≤ θ² ≤ 1` (Fischer).
* `Frames.det_gram_eq_blocks_mul_thetaSq` — the EXACT identity
  `det Gram(M Y) = det Gram(M Y_F) · det Gram(M Y_S) · θ²`.
* `Frames.log_det_factorization` — the **exact log factorization** (`hfact`, route (c)):
  `½ log det Gram(M Y) = ½ log det Gram(M Y_F) + ½ log det Gram(M Y_S) + log √θ²`.

### `hVF` upper bound

* `Frames.det_gram_le_prod_singularValues_sq` — `det Gram(M Y_F) ≤ (∏_{i<k} σᵢ(M))²` for an
  orthonormal left frame block.
* `Frames.VF_le_logSprod` — the per-`n` exponent bound.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace

namespace Frames

open Matrix

/-! ## 1. Positivity of the Gram determinant for full-column-rank frames -/

/-- **`det Gram > 0` for full-column-rank real frames.** If a real frame matrix `W` has injective
column action (`W.mulVec` injective, i.e. linearly independent columns), then the Gram determinant
`det (Wᵀ W)` is strictly positive. Via `Matrix.PosDef.conjTranspose_mul_self` (real `ᴴ = ᵀ`) and
`Matrix.PosDef.det_pos`. -/
theorem det_gram_pos {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℝ) (hW : Function.Injective W.mulVec) : 0 < (Wᵀ * W).det := by
  have hpd : (Wᴴ * W).PosDef := Matrix.PosDef.conjTranspose_mul_self W hW
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpd
  exact hpd.det_pos

/-- The Gram determinant of any real matrix is nonnegative (`Wᵀ W` is positive semidefinite). -/
theorem det_gram_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℝ) : 0 ≤ (Wᵀ * W).det := by
  have hps : (Wᴴ * W).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self W
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hps
  exact hps.det_nonneg

/-! ## 2. Block image Gram determinants and the exact factorization

Fix a frame `Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ` whose columns split into a left (fast) block
`Y_F = Y.submatrix id Sum.inl` and a right (slow) block `Y_S = Y.submatrix id Sum.inr`. For any
`M : Matrix (Fin d) (Fin d) ℝ` we study the three Gram determinants `det Gram(M Y)`,
`det Gram(M Y_F)`, `det Gram(M Y_S)`. -/

section Factorization

variable {d p q : ℕ}

/-- The left image block of `M · Y` is `M · Y_F`. -/
theorem image_block_inl (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) :
    (M * Y).submatrix id Sum.inl = M * (Y.submatrix id Sum.inl) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

/-- The right image block of `M · Y` is `M · Y_S`. -/
theorem image_block_inr (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) :
    (M * Y).submatrix id Sum.inr = M * (Y.submatrix id Sum.inr) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

/-- The full image Gram determinant `det Gram(M Y)`. -/
noncomputable def gramFull (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) : ℝ :=
  ((M * Y)ᵀ * (M * Y)).det

/-- The fast block image Gram determinant `det Gram(M Y_F)`. -/
noncomputable def gramF (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) : ℝ :=
  ((M * (Y.submatrix id Sum.inl))ᵀ * (M * (Y.submatrix id Sum.inl))).det

/-- The slow block image Gram determinant `det Gram(M Y_S)`. -/
noncomputable def gramS (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) : ℝ :=
  ((M * (Y.submatrix id Sum.inr))ᵀ * (M * (Y.submatrix id Sum.inr))).det

/-- **The squared inter-block sine of the image** (the geometric splitting angle `θ²`):
`θ² := det Gram(M Y) / (det Gram(M Y_F) · det Gram(M Y_S))`. -/
noncomputable def thetaSq (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) : ℝ :=
  gramFull M Y / (gramF M Y * gramS M Y)

/-- The full image Gram determinant is nonnegative. -/
theorem gramFull_nonneg (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) : 0 ≤ gramFull M Y :=
  det_gram_nonneg _

/-- The fast block image Gram determinant is positive when `M · Y_F` has full column rank. -/
theorem gramF_pos (M : Matrix (Fin d) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ)
    (hinj : Function.Injective (M * (Y.submatrix id Sum.inl)).mulVec) :
    0 < gramF M Y :=
  det_gram_pos _ hinj

/-- The slow block image Gram determinant is positive when `M · Y_S` has full column rank. -/
theorem gramS_pos (M : Matrix (Fin d) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ)
    (hinj : Function.Injective (M * (Y.submatrix id Sum.inr)).mulVec) :
    0 < gramS M Y :=
  det_gram_pos _ hinj

/-- The full image Gram determinant is positive when `M · Y` (all columns) has full column rank. -/
theorem gramFull_pos (M : Matrix (Fin d) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ)
    (hinj : Function.Injective (M * Y).mulVec) :
    0 < gramFull M Y :=
  det_gram_pos _ hinj

/-- The block image Gram determinants relate to the submatrix Gram determinants Fischer uses. -/
theorem gramF_eq_submatrix (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) :
    gramF M Y = (((M * Y).submatrix id Sum.inl)ᵀ * (M * Y).submatrix id Sum.inl).det := by
  unfold gramF; rw [image_block_inl]

theorem gramS_eq_submatrix (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) :
    gramS M Y = (((M * Y).submatrix id Sum.inr)ᵀ * (M * Y).submatrix id Sum.inr).det := by
  unfold gramS; rw [image_block_inr]

/-- **`0 ≤ θ²`** — the inter-block squared sine is nonnegative. -/
theorem thetaSq_nonneg (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ) : 0 ≤ thetaSq M Y := by
  unfold thetaSq
  exact div_nonneg (gramFull_nonneg M Y)
    (mul_nonneg (det_gram_nonneg _) (det_gram_nonneg _))

/-- **Fischer: `θ² ≤ 1`** — the inter-block squared sine of the image is at most `1`, when both
block image Gram determinants are positive. -/
theorem thetaSq_le_one (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ)
    (hF : 0 < gramF M Y) (hS : 0 < gramS M Y) :
    thetaSq M Y ≤ 1 := by
  unfold thetaSq gramFull
  rw [gramF_eq_submatrix] at hF
  rw [gramS_eq_submatrix] at hS
  rw [gramF_eq_submatrix, gramS_eq_submatrix]
  have h := Fischer.sin_sq_le_one (M * Y)
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hF)
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- **The exact factorization.** `det Gram(M Y) = det Gram(M Y_F) · det Gram(M Y_S) · θ²`, an
identity holding for every `M` with both block image Gram determinants nonzero. Immediate from the
definition of `θ²` as the ratio (`field_simp`). -/
theorem det_gram_eq_blocks_mul_thetaSq (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ)
    (hF : gramF M Y ≠ 0) (hS : gramS M Y ≠ 0) :
    gramFull M Y = gramF M Y * gramS M Y * thetaSq M Y := by
  unfold thetaSq
  field_simp

end Factorization

/-! ## 3. The exact log factorization (`hfact`, route (c)) -/

section LogFactorization

variable {d p q : ℕ}

/-- **`θ² > 0`** when `M · Y` has full column rank (the full Gram det is positive) and both block
Gram dets are positive. -/
theorem thetaSq_pos (M : Matrix (Fin d) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ)
    (hFull : 0 < gramFull M Y) (hF : 0 < gramF M Y) (hS : 0 < gramS M Y) :
    0 < thetaSq M Y := by
  unfold thetaSq
  exact div_pos hFull (mul_pos hF hS)

/-- **The exact log factorization (`hfact`, route (c)).** For a square `M` and a frame `Y` whose
full image and two image blocks have full column rank (so all three Gram determinants are positive),
the following EXACT identity holds (for every such `M`, no asymptotics):

  `½ log det Gram(M Y) = ½ log det Gram(M Y_F) + ½ log det Gram(M Y_S) + log √θ²`,

where `√θ² = √(det Gram(M Y) / (det Gram(M Y_F)·det Gram(M Y_S)))` is the image splitting angle.

This is the splitting `D n = VF n + VS n + S n` of `SqueezeData.hfact`, with
`D n := ½ log det Gram(M Y)` (equal to `(1/n)·... ` after dividing by `n`, but here stated
per-step before normalization), `VF := ½ log det Gram(M Y_F)`, `VS := ½ log det Gram(M Y_S)`, and
`S := log √θ²`. The proof: take `log` of the factorization
`det Gram(M Y) = det Gram(M Y_F)·det Gram(M Y_S)·θ²`, split with `Real.log_mul`, and fold the `½`
into a `√` on the `θ²` term. -/
theorem log_det_factorization (M : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin p ⊕ Fin q) ℝ)
    (hFull : 0 < gramFull M Y) (hF : 0 < gramF M Y) (hS : 0 < gramS M Y) :
    (1 / 2) * Real.log (gramFull M Y)
      = (1 / 2) * Real.log (gramF M Y) + (1 / 2) * Real.log (gramS M Y)
        + Real.log (Real.sqrt (thetaSq M Y)) := by
  have hθ : 0 < thetaSq M Y := thetaSq_pos M Y hFull hF hS
  have hfact := det_gram_eq_blocks_mul_thetaSq M Y (ne_of_gt hF) (ne_of_gt hS)
  -- log of the product factorization.
  rw [hfact, Real.log_mul (by positivity) (ne_of_gt hθ),
    Real.log_mul (ne_of_gt hF) (ne_of_gt hS)]
  -- log √θ² = ½ log θ².
  rw [Real.log_sqrt hθ.le]
  ring

end LogFactorization

/-! ## 4. `hVF` upper bound: fast-frame Gram det ≤ (∏ top-k σ)²

For an ORTHONORMAL left frame block (`Y_Fᵀ Y_F = 1`, so the fast frame is an orthonormal basis of
the fast subspace), the image Gram determinant `det Gram(M Y_F)` is at most the squared product of
the top-`k` singular values of `M`: `det Gram(M Y_F) ≤ (∏_{i<k} σᵢ(M))²`. This is the exterior-norm
/ compound-matrix bound: `√det Gram(M Y_F) = ‖⋀^k M · (Y_F-wedge)‖ ≤ ‖⋀^k M‖ = ∏σ` for the unit
wedge of an orthonormal frame. -/

section VFUpper

open ExteriorNorm

variable {d : ℕ}

/-- The `j`-th column of `M · YF` is the image under `toEuclideanLin M` of the `j`-th column of
`YF`. -/
theorem colE_mul_eq {k : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (YF : Matrix (Fin d) (Fin k) ℝ)
    (j : Fin k) :
    colE (M * YF) j = Matrix.toEuclideanLin M (colE YF j) := by
  rw [Matrix.toEuclideanLin_apply]
  ext a
  simp only [colE, Matrix.mul_apply, Matrix.mulVec]
  rfl

/-- The Hodge-trivialized wedge of an orthonormal frame `YF` (i.e. `YFᵀ YF = 1`) has unit norm:
`‖hodge(ιMulti(colE YF))‖² = det(YFᵀ YF) = 1`. -/
theorem normSq_hodge_wedge_ortho {k : ℕ} (YF : Matrix (Fin d) (Fin k) ℝ)
    (hortho : YFᵀ * YF = 1) :
    ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k
        (exteriorPower.ιMulti ℝ k (fun j => colE YF j))‖ = 1 := by
  have hdet := det_transpose_mul_eq_inner_hodge YF YF
  rw [hortho, Matrix.det_one] at hdet
  have hnormsq : ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k
      (exteriorPower.ιMulti ℝ k (fun j => colE YF j))‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact hdet.symm
  nlinarith [norm_nonneg (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k
    (exteriorPower.ιMulti ℝ k (fun j => colE YF j))), hnormsq]

set_option maxHeartbeats 800000 in
/-- **`hVF` upper bound (Gram form).** For an orthonormal left frame block `YF` (`YFᵀ YF = 1`), the
image Gram determinant `det((M YF)ᵀ (M YF))` is at most the squared product of the top-`k` singular
values of `M`: `det Gram(M YF) ≤ (∏_{i<k} σᵢ(M))²`.

Route: `det Gram(M YF) = ‖hodge(ιMulti(colE(M YF)))‖²` (`det_transpose_mul_eq_inner_hodge` with
`U = V`); the wedge `ιMulti(colE(M YF)) = ⋀^k(toEuclideanLin M)(ιMulti(colE YF))` (`map_apply_ιMulti`
+ `colE_mul_eq`); the Hodge-trivialized image is `conjExteriorMap` applied to the trivialized source
wedge, so its norm is `≤ exteriorOpNorm·‖hodge(source wedge)‖ = (∏σ)·1` (the bridge
`exteriorOpNorm_hodge_eq_prod_singularValues` + orthonormality `‖hodge wedge‖ = 1`). -/
theorem det_gram_le_prod_singularValues_sq {k : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (YF : Matrix (Fin d) (Fin k) ℝ) (hortho : YFᵀ * YF = 1) :
    ((M * YF)ᵀ * (M * YF)).det
      ≤ (∏ i ∈ Finset.range k, (Matrix.toEuclideanLin M).singularValues i) ^ 2 := by
  classical
  set f := Matrix.toEuclideanLin M with hf
  set ηS : ⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)) :=
    exteriorPower.ιMulti ℝ k (fun j => colE YF j) with hηS
  set ηI : ⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)) :=
    exteriorPower.ιMulti ℝ k (fun j => colE (M * YF) j) with hηI
  -- Step 1: det Gram = ‖hodge ηI‖².
  have hdetGram : ((M * YF)ᵀ * (M * YF)).det
      = ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηI‖ ^ 2 := by
    have h := det_transpose_mul_eq_inner_hodge (M * YF) (M * YF)
    rw [← real_inner_self_eq_norm_sq]
    exact h
  -- Step 2: ηI = ⋀^k f (ηS).
  have hwedge : ηI = exteriorPower.map k f ηS := by
    have hcol : (fun j => colE (M * YF) j) = f ∘ (fun j => colE YF j) := by
      funext j; rw [Function.comp_apply, colE_mul_eq]
    rw [hηI, hηS, exteriorPower.map_apply_ιMulti, hcol]
  -- Step 3: hodge ηI = conjExteriorMap k hodge hodge f (hodge ηS).
  have hconj : hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηI
      = conjExteriorMap k (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k)
          (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k) f
          (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηS) := by
    rw [hwedge, conjExteriorMap]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  -- Step 4: the operator-norm bound.
  have hopbound : ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηI‖
      ≤ exteriorOpNorm k (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k)
          (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k) f
        * ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηS‖ := by
    rw [hconj, exteriorOpNorm]
    have := (LinearMap.toContinuousLinearMap
      (conjExteriorMap k (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k)
        (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k) f)).le_opNorm
      (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηS)
    rwa [LinearMap.coe_toContinuousLinearMap'] at this
  -- Step 5: the bridge + orthonormality.
  have hbridge : exteriorOpNorm k (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k)
      (hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k) f
      = ∏ i ∈ Finset.range k, f.singularValues i :=
    exteriorOpNorm_hodge_eq_prod_singularValues k f
  have hunit : ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηS‖ = 1 :=
    normSq_hodge_wedge_ortho YF hortho
  -- assemble.
  rw [hdetGram]
  have hprodnn : 0 ≤ ∏ i ∈ Finset.range k, f.singularValues i :=
    Finset.prod_nonneg (fun i _ => f.singularValues_nonneg i)
  have hnn : 0 ≤ ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηI‖ := norm_nonneg _
  have hle : ‖hodgeTrivialization (E := EuclideanSpace ℝ (Fin d)) k ηI‖
      ≤ ∏ i ∈ Finset.range k, f.singularValues i := by
    rw [hbridge, hunit, mul_one] at hopbound; exact hopbound
  exact pow_le_pow_left₀ hnn hle 2

end VFUpper

/-! ## 5. From the Gram bound to the volume exponent and its `limsup`

The fast-frame volume exponent `VF n := (1/n)·½·log det Gram(M_n W_F)` is bounded by
`(1/n)·log (∏_{i<k} σᵢ(M_n))`, and the latter converges (a.e.) to the ergodic `Γ_k`-type constant by
the committed `tendsto_GammaK_of_integrableLogNorm`. Hence `limsup VF ≤ Γ_k`. -/

section VFExponent

open Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- **The per-step volume/singular-value bound.** For an orthonormal fast frame `YF` (`YFᵀ YF = 1`)
with positive image Gram determinant, `½ log det Gram(M YF) ≤ log (∏_{i<k} σᵢ(M))`. From
`det Gram(M YF) ≤ (∏σ)²` (`det_gram_le_prod_singularValues_sq`) by taking `½ log` (monotone), using
`∏σ > 0`. -/
theorem half_log_det_gram_le_log_prod {k : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (YF : Matrix (Fin d) (Fin k) ℝ) (hortho : YFᵀ * YF = 1)
    (hgrampos : 0 < ((M * YF)ᵀ * (M * YF)).det)
    (hprodpos : 0 < ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin M).singularValues i) :
    (1 / 2) * Real.log (((M * YF)ᵀ * (M * YF)).det)
      ≤ Real.log (∏ i ∈ Finset.range k, (Matrix.toEuclideanLin M).singularValues i) := by
  have hbound := det_gram_le_prod_singularValues_sq M YF hortho
  have hlog : Real.log (((M * YF)ᵀ * (M * YF)).det)
      ≤ Real.log ((∏ i ∈ Finset.range k, (Matrix.toEuclideanLin M).singularValues i) ^ 2) :=
    Real.log_le_log hgrampos hbound
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **The per-step volume exponent bound (cocycle form).** With `M_n = cocycle A T n x` and an
orthonormal fast frame `YF`, the normalized fast-volume exponent
`(1/n)·½·log det Gram(M_n YF)` is `≤ (1/n)·log Sprod_k`, i.e. `≤` the normalized top-`k`
singular-value-product exponent. -/
theorem VF_le_logSprod {k : ℕ} {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hk : k ≤ d) (x : X) (n : ℕ)
    (YF : Matrix (Fin d) (Fin k) ℝ) (hortho : YFᵀ * YF = 1)
    (hgrampos : 0 < ((cocycle A T n x * YF)ᵀ * (cocycle A T n x * YF)).det) :
    (n : ℝ)⁻¹ * ((1 / 2) * Real.log (((cocycle A T n x * YF)ᵀ * (cocycle A T n x * YF)).det))
      ≤ (n : ℝ)⁻¹ * Real.log (Oseledets.Sprod A T k n x) := by
  have hprodpos : 0 < Oseledets.Sprod A T k n x := Oseledets.Sprod_pos hA hk n x
  have hSprod_eq : Oseledets.Sprod A T k n x
      = ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i := rfl
  have hbound := half_log_det_gram_le_log_prod (cocycle A T n x) YF hortho hgrampos
    (hSprod_eq ▸ hprodpos)
  rw [hSprod_eq]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- **`hVF` limsup upper bound.** If the fast-volume exponent `VF n` is eventually `≤` the
top-`k` singular-value-product exponent `Sexp n := (1/n) log Sprod_k`, and `Sexp → Γ_k` (the
committed ergodic limit), and `VF` is eventually bounded below (so its `limsup` is cobounded
above), then `limsup VF ≤ Γ_k`. -/
theorem limsup_VF_le_GammaK {VF Sexp : ℕ → ℝ} {Γk : ℝ}
    (hle : ∀ᶠ n in atTop, VF n ≤ Sexp n)
    (hS : Tendsto Sexp atTop (𝓝 Γk))
    (hVFlb : ∃ c : ℝ, ∀ᶠ n in atTop, c ≤ VF n) :
    limsup VF atTop ≤ Γk := by
  obtain ⟨c, hc⟩ := hVFlb
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop VF :=
    isCoboundedUnder_le_of_eventually_le atTop hc
  have hbdd : IsBoundedUnder (· ≤ ·) atTop Sexp := hS.isBoundedUnder_le
  calc limsup VF atTop ≤ limsup Sexp atTop := limsup_le_limsup hle hcobdd hbdd
    _ = Γk := hS.limsup_eq

end VFExponent

end Frames

-- Axiom audit for the main theorems.
#print axioms Frames.det_gram_pos
#print axioms Frames.log_det_factorization
#print axioms Frames.thetaSq_le_one
#print axioms Frames.det_gram_eq_blocks_mul_thetaSq
#print axioms Frames.det_gram_le_prod_singularValues_sq
#print axioms Frames.VF_le_logSprod
#print axioms Frames.limsup_VF_le_GammaK
