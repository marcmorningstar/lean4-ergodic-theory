/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MeasureTheory.CoveringFromVolume
import ErgodicTheory.Entropy.Ruelle.VolumeDistortion
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The sharp anisotropic one-step covering count

This module proves the **sharp, anisotropic** covering-count estimate that the *isotropic* volume
bound of `ErgodicTheory.Entropy.Ruelle.LocalCovering` left open (Liao–Qiu,
*Margulis–Ruelle inequality for general manifolds*, §3, Lemmas 3.2–3.3).

For a linear map `L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)` (the derivative of
one dynamical step) and `ε > 0`, the `ε`-covering number of the image `L '' closedBall x ε` of a
small ball is bounded by a dimensional constant times the **positive-part singular-value product**:

$$N_\varepsilon\big(L(B(x,\varepsilon))\big)\;\le\; C_d \cdot \prod_i \max(1,\sigma_i),$$

where `σ₀ ≥ σ₁ ≥ ⋯` are the singular values of `L`.  This is *sharp*: a thin pancake (some
`σᵢ ≪ 1`) is covered by *few* balls along its thin directions, which the isotropic bound
`(2‖L‖ + 1)^d` (seeing only `σ₀ = ‖L‖`) cannot detect.

## The route taken here: SVD ellipsoid domination + determinant volume

The lossy `‖L‖`-only volume bound is replaced by a genuine **singular-value decomposition**
(`svd_exists`): orthonormal bases `b` (eigenbasis of `Lᵀ L` in the domain) and `c` (an extension of
the normalised image frame `σᵢ⁻¹ • L bᵢ`) of `EuclideanSpace ℝ (Fin d)` such that `L bᵢ = σᵢ • cᵢ`
for all `i`.  In these coordinates `L '' closedBall 0 ε` is the axis-aligned **ellipsoid** with
semi-axes `ε σᵢ`.

The `δ`-thickening of this ellipsoid is contained in the dilated ellipsoid
`c.repr.symm '' (diagMap (2(ε σ + δ)) '' B(0,1))`
(`cthickening_image_closedBall_subset_ellipsoid`, a weighted-`L²` triangle inequality:
`‖·‖ₐ ≤ ‖signal‖ₐ + ‖noise‖ₐ ≤ ½ + ½` with `aᵢ = 2(ε σᵢ + δ)`).  Transporting the volume through the
measure-preserving frame isometry `c.repr.symm` and applying the diagonal determinant law
`MeasureTheory.Measure.addHaar_image_linearMap` gives the volume
`∏ᵢ 2(ε σᵢ + δ) · volume(B 0 1)` (`volume_cthickening_image_closedBall_le_volProd`).  With
`δ = ε/2`,
`ErgodicTheory.MeasureTheory.CoveringFromVolume`'s volume → covering bound divides by `(ε/2)^d ·
volume(B 0 1)`:
the dimensional constant cancels and `∏ᵢ 2(ε σᵢ + ε/2)/(ε/2)^d = ∏ᵢ (4 σᵢ + 2) ≤ 6^d ∏ᵢ max(1, σᵢ)`
(`prod_four_mul_add_two_le`).  The general centre `x` is reduced to the origin by the
covering-number isometry invariance under the translation `y ↦ L x + y`.

## Main results

* `ErgodicTheory.svd_exists` — the constructive **singular-value decomposition** `L bᵢ = σᵢ • cᵢ`
  with orthonormal bases `b, c`, identifying `σᵢ` with `LinearMap.singularValues`.
* `ErgodicTheory.cthickening_image_closedBall_subset_ellipsoid` — the **ellipsoid domination** of
  the thickened image (the geometric heart, the weighted-`L²` triangle inequality).
* `ErgodicTheory.volume_cthickening_image_closedBall_le_volProd` — the **anisotropic volume**
  `volume(cthickening δ (L '' B(0,ε))) ≤ ∏ᵢ 2(ε σᵢ + δ) · volume(B 0 1)`.
* `ErgodicTheory.coveringCount_image_ball_le_volProd` — the sharp anisotropic one-step covering
  count `coveringNumber ε (L '' B(x,ε)) ≤ 6^d · ∏ᵢ max(1, σᵢ(L))`.
-/

open Metric MeasureTheory Set Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace ErgodicTheory

variable {d : ℕ}

section SVD

variable (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))

/-- The Gram operator `Lᵀ L` is symmetric, its eigenbasis carries the right singular vectors. -/
private noncomputable abbrev gram : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.adjoint L ∘ₗ L

/-- **Singular value decomposition (existence form).**  For a linear self-map `L` of
`EuclideanSpace ℝ (Fin d)` there are an orthonormal basis `b` (the eigenbasis of the Gram operator
`Lᵀ L`, i.e. the right singular vectors), an orthonormal basis `c` (the left singular vectors), and
a nonnegative antitone sequence `σ` (the singular values) such that `L bᵢ = σᵢ • cᵢ` for every `i`,
and `σᵢ² = ⟪L bᵢ, L bᵢ⟫` so that `σᵢ = ‖L bᵢ‖`.

This is the constructive SVD that pinned Mathlib's `singularValues` API stops short of: it exposes
the **factorisation** `L = c.repr.symm ∘ Diag σ ∘ b.repr` the sharp covering count needs.
The left frame `c` is built by normalising the nonzero `L bᵢ` and extending to an orthonormal basis
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`). -/
theorem svd_exists (hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d) :
    ∃ (b c : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (σ : Fin d → ℝ),
      (∀ i, 0 ≤ σ i) ∧ (∀ i, L (b i) = σ i • c i) ∧ (∀ i, σ i ^ 2 = ⟪L (b i), L (b i)⟫) ∧
      (∀ i : Fin d, σ i = L.singularValues i) := by
  classical
  -- The right singular basis: eigenbasis of the symmetric Gram operator.
  set S := gram L with hS
  have hSsym : S.IsSymmetric := L.isSymmetric_adjoint_comp_self
  set b := hSsym.eigenvectorBasis hd with hb
  set μ : Fin d → ℝ := hSsym.eigenvalues hd with hμ
  -- Eigenvalues are nonnegative (Gram is positive) and `‖L bᵢ‖² = μ i`.
  have hμnonneg : ∀ i, 0 ≤ μ i := L.isPositive_adjoint_comp_self.nonneg_eigenvalues hd
  set σ : Fin d → ℝ := fun i => Real.sqrt (μ i) with hσ
  have hσnonneg : ∀ i, 0 ≤ σ i := fun i => Real.sqrt_nonneg _
  -- `⟪L bᵢ, L bⱼ⟫ = μ i • δᵢⱼ`.
  have hinner : ∀ i j, ⟪L (b i), L (b j)⟫ = μ i * (if i = j then (1 : ℝ) else 0) := by
    intro i j
    have h1 : ⟪L (b i), L (b j)⟫ = ⟪S (b i), b j⟫ := by
      rw [hS, gram]; simp [LinearMap.adjoint_inner_left]
    have h2 : S (b i) = (μ i : ℝ) • b i := by
      rw [hb, hμ]; exact hSsym.apply_eigenvectorBasis hd i
    rw [h1, h2, inner_smul_left]
    have hbon : ⟪b i, b j⟫ = (if i = j then (1 : ℝ) else 0) :=
      (orthonormal_iff_ite (v := b)).1 b.orthonormal i j
    rw [hbon]; simp
  -- `‖L bᵢ‖² = μ i = σ i ^ 2`.
  have hsq : ∀ i, σ i ^ 2 = ⟪L (b i), L (b i)⟫ := by
    intro i
    rw [hσ]; simp only
    rw [Real.sq_sqrt (hμnonneg i), hinner i i, if_pos rfl, mul_one]
  -- When `σ i = 0`, `L bᵢ = 0`.
  have hzero : ∀ i, σ i = 0 → L (b i) = 0 := by
    intro i hi
    have : ⟪L (b i), L (b i)⟫ = 0 := by rw [← hsq i, hi]; ring
    rwa [inner_self_eq_zero] at this
  -- The left frame: normalise the nonzero image vectors.
  set s : Set (Fin d) := {i | σ i ≠ 0} with hsdef
  set v : Fin d → EuclideanSpace ℝ (Fin d) := fun i => (σ i)⁻¹ • L (b i) with hv
  -- `s.restrict v` is orthonormal.
  have hvon : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.restrict_apply, hv]
    rw [inner_smul_left, inner_smul_right, hinner i j, conj_trivial]
    simp only [hsdef, Set.mem_setOf_eq] at hi hj
    by_cases hij : i = j
    · subst hij
      have hμi : μ i = σ i ^ 2 := by rw [hsq i, hinner i i, if_pos rfl, mul_one]
      simp only [hμi]
      field_simp
    · rw [if_neg hij, if_neg (show (⟨i, _⟩ : s) ≠ ⟨j, _⟩ by simp [hij])]; ring
  -- The geometric singular value equals Mathlib's `singularValues` (both `√(eigenvalues)`).
  have hsv : ∀ i : Fin d, σ i = L.singularValues i := by
    intro i
    rw [hσ]; simp only
    rw [L.singularValues_of_lt hd i.isLt, hμ]
  -- Extend to a full orthonormal basis.
  obtain ⟨c, hc⟩ := hvon.exists_orthonormalBasis_extension_of_card_eq (by rw [hd]; simp) (v := v)
  refine ⟨b, c, σ, hσnonneg, ?_, hsq, hsv⟩
  intro i
  by_cases hi : σ i = 0
  · rw [hi, zero_smul, hzero i hi]
  · have hci : c i = v i := hc i (by simp [hsdef, hi])
    rw [hci, hv]
    simp only
    rw [smul_inv_smul₀ hi]

end SVD

/-! ## The diagonal scaling map and its image of the unit ball -/

section Diag

variable {a : Fin d → ℝ}

/-- The diagonal scaling map on Euclidean space, `t ↦ (aᵢ tᵢ)ᵢ`. -/
private noncomputable def diagMap (a : Fin d → ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanLin (Matrix.diagonal a)

private theorem diagMap_apply (a : Fin d → ℝ) (t : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    diagMap a t i = a i * t i := by
  classical
  rw [diagMap, show (Matrix.toEuclideanLin (Matrix.diagonal a) t) i
        = (Matrix.diagonal a).mulVec (WithLp.ofLp t) i from rfl]
  simp [Matrix.mulVec_diagonal]

/-- The Haar volume of `diagMap a '' s` scales by `∏ᵢ |aᵢ|`. -/
private theorem addHaar_image_diagMap (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [μ.IsAddHaarMeasure] (a : Fin d → ℝ) (s : Set (EuclideanSpace ℝ (Fin d))) :
    μ (diagMap a '' s) = ENNReal.ofReal (∏ i, |a i|) * μ s := by
  rw [diagMap, μ.addHaar_image_linearMap]
  congr 2
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_diagonal,
    Finset.abs_prod]

end Diag

/-! ## The sharp anisotropic covering count -/

section Covering

open MeasureTheory

variable (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))

/-- **The ellipsoid containment (geometric heart).**  With singular data `b, c, σ` of `L`
(`svd_exists`) and `aᵢ := 2(ε σᵢ + δ)` (`ε, δ > 0`), the `δ`-thickening of the image of the unit
`ε`-ball (centred at origin) is contained in the ellipsoid `c.repr.symm '' (diagMap a '' B(0,1))`.

This is the weighted-`L²` triangle inequality: for `w` within `δ` of `z = L y`, `‖y‖ ≤ ε`, the
coordinates `tᵢ := ⟪cᵢ, w⟫ / aᵢ` satisfy `∑ tᵢ² ≤ 1` because `‖t‖ ≤ ‖t_z‖ + ‖t_{w-z}‖`, where the
"signal" part has `∑ σᵢ²(Ry)ᵢ²/aᵢ² ≤ ‖y‖²/(2ε)² ≤ ¼` (using `aᵢ ≥ 2ε σᵢ`) and the "noise" part has
`∑ ⟪cᵢ, w-z⟫²/aᵢ² ≤ ‖w-z‖²/(2δ)² ≤ ¼` (using `aᵢ ≥ 2δ`), giving `‖t‖ ≤ ½ + ½ = 1`. -/
theorem cthickening_image_closedBall_subset_ellipsoid {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (b c : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (σ : Fin d → ℝ)
    (hσnn : ∀ i, 0 ≤ σ i) (hLb : ∀ i, (L : _ →ₗ[ℝ] _) (b i) = σ i • c i) :
    cthickening δ (L '' closedBall 0 ε)
      ⊆ (c.repr.symm) '' (diagMap (fun i => 2 * (ε * σ i + δ)) '' closedBall 0 1) := by
  classical
  set a : Fin d → ℝ := fun i => 2 * (ε * σ i + δ) with ha
  have hapos : ∀ i, 0 < a i := fun i => by
    rw [ha]; have := hσnn i; positivity
  -- The image of the ε-ball is compact, so the thickening is a union of δ-balls.
  have hcompact : IsCompact (L '' closedBall (0 : EuclideanSpace ℝ (Fin d)) ε) :=
    (isCompact_closedBall 0 ε).image L.continuous
  rw [hcompact.cthickening_eq_biUnion_closedBall hδ.le]
  rintro w hw
  simp only [Set.mem_iUnion, mem_closedBall] at hw
  obtain ⟨z, ⟨y, hy, rfl⟩, hwz⟩ := hw
  rw [mem_closedBall] at hy
  -- The candidate point `t := diagMap (a⁻¹) (c.repr w)`, with coords `⟪cᵢ, w⟫ / aᵢ`.
  set t : EuclideanSpace ℝ (Fin d) := diagMap (fun i => (a i)⁻¹) (c.repr w) with ht
  have htval : ∀ i, t i = c.repr w i / a i := by
    intro i; rw [ht, diagMap_apply]; rw [div_eq_inv_mul]
  -- Provide the outer witness `c.repr w`, then the inner witness `t`.
  refine ⟨c.repr w, ⟨t, ?_, ?_⟩, by simp⟩
  · -- `‖t‖ ≤ 1` via the weighted-`L²` triangle inequality.
    rw [mem_closedBall, dist_zero_right]
    -- Signal coordinates: `c.repr (L y) i = ⟪cᵢ, L y⟫ = σ i * (b.repr y) i`.
    have hsig : ∀ i, c.repr (L y) i = σ i * b.repr y i := by
      intro i
      have hLyexp : (L : _ →ₗ[ℝ] _) y = ∑ j, b.repr y j • (σ j • c j) := by
        conv_lhs => rw [← b.sum_repr y]
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hLb j]
      rw [c.repr_apply_apply, show L y = (L : _ →ₗ[ℝ] _) y from rfl, hLyexp,
        inner_sum]
      rw [Finset.sum_eq_single i]
      · rw [inner_smul_right, inner_smul_right, (orthonormal_iff_ite (v := c)).1 c.orthonormal i i,
          if_pos rfl]
        ring
      · intro j _ hji
        rw [inner_smul_right, inner_smul_right,
          (orthonormal_iff_ite (v := c)).1 c.orthonormal i j, if_neg (Ne.symm hji)]
        ring
      · intro h; exact absurd (Finset.mem_univ i) h
    -- The split-vector witnesses: `p := signal/a`, `q := noise/a`, `t = p + q`.
    set p : EuclideanSpace ℝ (Fin d) := diagMap (fun i => (a i)⁻¹) (c.repr (L y)) with hp
    set q : EuclideanSpace ℝ (Fin d) := diagMap (fun i => (a i)⁻¹) (c.repr (w - L y)) with hq
    have htpq : t = p + q := by
      rw [ht, hp, hq, ← map_add, ← map_add]
      congr 2
      abel
    -- From a squared-norm bound to a norm bound.
    have hsqle : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ^ 2 ≤ (1 / 2) ^ 2 → ‖v‖ ≤ 1 / 2 := by
      intro v hv
      nlinarith [norm_nonneg v, hv]
    -- `‖p‖ ≤ 1/2`: the signal squared is `∑ σᵢ²(b.repr y)ᵢ²/aᵢ² ≤ ‖y‖²/(2ε)² ≤ ¼`.
    have hpbound : ‖p‖ ≤ 1 / 2 := by
      apply hsqle
      rw [EuclideanSpace.real_norm_sq_eq]
      have hpi : ∀ i, p i = σ i * b.repr y i / a i := by
        intro i; rw [hp, diagMap_apply, hsig i]; ring
      have hstep : ∀ i, p i ^ 2 ≤ (b.repr y i) ^ 2 / (2 * ε) ^ 2 := by
        intro i
        rw [hpi i, div_pow]
        rw [div_le_div_iff₀ (pow_pos (hapos i) 2) (pow_pos (by positivity) 2)]
        -- `(2εσᵢ) ≤ aᵢ`, both nonneg, so `(2εσᵢ)² ≤ aᵢ²`, multiply by `(b.repr y i)² ≥ 0`.
        have hai : 0 ≤ 2 * ε * σ i ∧ 2 * ε * σ i ≤ a i := by
          rw [ha]; constructor <;> nlinarith [hσnn i, hδ.le, hε.le]
        have hsq : (2 * ε * σ i) ^ 2 ≤ (a i) ^ 2 := by nlinarith [hai.1, hai.2]
        nlinarith [sq_nonneg (b.repr y i), mul_le_mul_of_nonneg_right hsq (sq_nonneg (b.repr y i))]
      calc ∑ i, p i ^ 2 ≤ ∑ i, (b.repr y i) ^ 2 / (2 * ε) ^ 2 :=
            Finset.sum_le_sum fun i _ => hstep i
        _ = (∑ i, (b.repr y i) ^ 2) / (2 * ε) ^ 2 := by rw [Finset.sum_div]
        _ = ‖y‖ ^ 2 / (2 * ε) ^ 2 := by
            rw [← EuclideanSpace.real_norm_sq_eq, LinearIsometryEquiv.norm_map]
        _ ≤ (1 / 2) ^ 2 := by
            rw [div_le_iff₀ (by positivity)]
            have hyε : ‖y‖ ≤ ε := by rwa [← dist_zero_right]
            nlinarith [norm_nonneg y, hε]
    -- `‖q‖ ≤ 1/2`: the noise squared is `∑ ⟪cᵢ,w-z⟫²/aᵢ² ≤ ‖w-z‖²/(2δ)² ≤ ¼`.
    have hqbound : ‖q‖ ≤ 1 / 2 := by
      apply hsqle
      rw [EuclideanSpace.real_norm_sq_eq]
      have hqi : ∀ i, q i = c.repr (w - L y) i / a i := by
        intro i; rw [hq, diagMap_apply]; ring
      have hstep : ∀ i, q i ^ 2 ≤ (c.repr (w - L y) i) ^ 2 / (2 * δ) ^ 2 := by
        intro i
        rw [hqi i, div_pow]
        rw [div_le_div_iff₀ (pow_pos (hapos i) 2) (pow_pos (by positivity) 2)]
        have hai : 2 * δ ≤ a i := by rw [ha]; nlinarith [hσnn i, hε.le]
        have hsq : (2 * δ) ^ 2 ≤ (a i) ^ 2 := by nlinarith [hδ.le, hai]
        nlinarith [sq_nonneg (c.repr (w - L y) i),
          mul_le_mul_of_nonneg_right hsq (sq_nonneg (c.repr (w - L y) i))]
      calc ∑ i, q i ^ 2 ≤ ∑ i, (c.repr (w - L y) i) ^ 2 / (2 * δ) ^ 2 :=
            Finset.sum_le_sum fun i _ => hstep i
        _ = (∑ i, (c.repr (w - L y) i) ^ 2) / (2 * δ) ^ 2 := by rw [Finset.sum_div]
        _ = ‖w - L y‖ ^ 2 / (2 * δ) ^ 2 := by
            rw [← EuclideanSpace.real_norm_sq_eq, LinearIsometryEquiv.norm_map]
        _ ≤ (1 / 2) ^ 2 := by
            rw [div_le_iff₀ (by positivity)]
            have hwz' : ‖w - L y‖ ≤ δ := by rw [← dist_eq_norm]; exact hwz
            nlinarith [norm_nonneg (w - L y), hδ]
    calc ‖t‖ = ‖p + q‖ := by rw [htpq]
      _ ≤ ‖p‖ + ‖q‖ := norm_add_le _ _
      _ ≤ 1 / 2 + 1 / 2 := by gcongr
      _ = 1 := by norm_num
  · -- `diagMap a t = c.repr w`.
    ext i
    rw [diagMap_apply, htval i]
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ (hapos i).ne'

/-- **Anisotropic thickened-image volume bound (at the origin).**  For `ε, δ > 0`, the volume of the
`δ`-thickening of the image `L '' closedBall 0 ε` of a small ball under a continuous linear self-map
`L` of `EuclideanSpace ℝ (Fin d)` is bounded by `∏ᵢ 2(ε σᵢ + δ) · volume(ball 0 1)`, where `σᵢ` are
the singular values of `L` (via the SVD `svd_exists`).

This is the **sharp anisotropic** replacement for the isotropic
`MeasureTheory.addHaar_cthickening_image_closedBall_le` (which sees only `‖L‖ = σ₀`): the thin
directions (`σᵢ ≪ 1`) genuinely shrink the product.  The proof dominates the thickened ellipsoid
`L '' closedBall 0 ε ⊕ ball δ` by the ellipsoid `c.repr.symm '' (diagMap (2(ε σ + δ)) '' ball 0 1)`
(`cthickening_image_closedBall_subset_ellipsoid`), transports the volume through the measure-
preserving frame isometry `c.repr.symm` (`measure_preimage` of the inverse isometry), and applies
the determinant volume law `addHaar_image_diagMap`. -/
theorem volume_cthickening_image_closedBall_le_volProd [NeZero d]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (b c : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (σ : Fin d → ℝ)
    (hσnn : ∀ i, 0 ≤ σ i) (hLb : ∀ i, (L : _ →ₗ[ℝ] _) (b i) = σ i • c i) :
    volume (cthickening δ (L '' closedBall (0 : EuclideanSpace ℝ (Fin d)) ε))
      ≤ ENNReal.ofReal (∏ i, 2 * (ε * σ i + δ)) *
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  classical
  set a : Fin d → ℝ := fun i => 2 * (ε * σ i + δ) with ha
  have hapos : ∀ i, 0 < a i := fun i => by rw [ha]; have := hσnn i; positivity
  -- Step 1: the containment from the geometric heart.
  have hsub := cthickening_image_closedBall_subset_ellipsoid L hε hδ b c σ hσnn hLb
  -- The frame isometry `c.repr.symm` preserves volume: `c.repr.symm '' T = c.repr ⁻¹' T`.
  have hpres : volume (c.repr.symm '' (diagMap a '' closedBall 0 1))
      = volume (diagMap a '' closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [show (c.repr.symm '' (diagMap a '' closedBall 0 1))
          = ⇑c.repr ⁻¹' (diagMap a '' closedBall 0 1) from by
      ext z; constructor
      · rintro ⟨u, hu, rfl⟩; simpa using hu
      · intro hz; exact ⟨c.repr z, hz, by simp⟩]
    have hmp : MeasurePreserving (c.repr.toMeasurableEquiv) volume volume := by
      simpa using c.repr.measurePreserving
    exact hmp.measure_preimage_equiv _
  calc volume (cthickening δ (L '' closedBall (0 : EuclideanSpace ℝ (Fin d)) ε))
      ≤ volume (c.repr.symm '' (diagMap a '' closedBall 0 1)) := measure_mono hsub
    _ = volume (diagMap a '' closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := hpres
    _ = ENNReal.ofReal (∏ i, |a i|) * volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
        addHaar_image_diagMap volume a _
    _ = ENNReal.ofReal (∏ i, 2 * (ε * σ i + δ)) *
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
        rw [show (∏ i, |a i|) = ∏ i, 2 * (ε * σ i + δ) from
          Finset.prod_congr rfl fun i _ => by rw [abs_of_pos (hapos i)]]
        rw [Measure.addHaar_closedBall_eq_addHaar_ball volume 0 1]

/-- The per-factor anisotropic bound `4σᵢ + 2 ≤ 6 · max(1, σᵢ)` packaged as a product:
`∏ᵢ (4σᵢ + 2) ≤ 6^d · ∏ᵢ max(1, σᵢ)`.  Each factor: if `σᵢ ≤ 1` then `4σᵢ + 2 ≤ 6 = 6 · 1`; if
`σᵢ ≥ 1` then `4σᵢ + 2 ≤ 6σᵢ`.  This converts the explicit covering count into the canonical
positive-part singular-value product `∏ᵢ max(1, σᵢ)` with the dimensional constant `6^d`. -/
theorem prod_four_mul_add_two_le {σ : Fin d → ℝ} (hσnn : ∀ i, 0 ≤ σ i) :
    ∏ i, (4 * σ i + 2) ≤ (6 : ℝ) ^ d * ∏ i, max 1 (σ i) := by
  rw [show (6 : ℝ) ^ d = ∏ _i : Fin d, (6 : ℝ) by rw [Finset.prod_const, Finset.card_univ,
    Fintype.card_fin], ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _; have := hσnn i; positivity
  · intro i _
    rcases le_or_gt (σ i) 1 with h | h
    · rw [max_eq_left h]; have := hσnn i; linarith
    · rw [max_eq_right h.le]; linarith

variable [NeZero d]

/-- **The sharp anisotropic one-step covering count.**  For a continuous linear self-map `L` of
`EuclideanSpace ℝ (Fin d)` and `ε > 0`, the `ε`-covering number of the image `L '' closedBall x ε`
of a small ball is bounded by `6^d · ∏ᵢ max(1, σᵢ(L))`, the dimensional constant times the
**positive-part singular-value product** of `L`.

This is the genuinely **sharp anisotropic** Liao–Qiu one-step count (§3, Lemmas 3.2–3.3): a thin
pancake (`σᵢ ≪ 1`) needs *few* balls along its thin directions, in contrast to the isotropic
`(2‖L‖ + 1)^d` count which sees only `σ₀ = ‖L‖`.

The proof: at origin, the SVD (`svd_exists`) + ellipsoid domination + determinant volume law give
`volume(cthickening (ε/2) (L '' B(0,ε))) ≤ ∏ᵢ 2(ε σᵢ + ε/2) · volume(B 0 1)`
(`volume_cthickening_image_closedBall_le_volProd`); the volume → covering bound
`Metric.coveringNumber_le_addHaar_div_of_addHaar_le` divides by `(ε/2)^d · volume(B 0 1)`, the
dimensional constant cancels and `∏ᵢ 2(ε σᵢ + ε/2)/(ε/2)^d = ∏ᵢ (4 σᵢ + 2) ≤ 6^d ∏ᵢ max(1, σᵢ)`
(`prod_four_mul_add_two_le`).  The general centre `x` is reduced to the origin by the
covering-number isometry invariance `Isometry.coveringNumber_image` under `y ↦ L x + y`. -/
theorem coveringCount_image_ball_le_volProd (x : EuclideanSpace ℝ (Fin d)) {ε : ℝ≥0} (hε : 0 < ε) :
    coveringNumber ε (L '' closedBall x (ε : ℝ))
      ≤ ENNReal.ofReal ((6 : ℝ) ^ d *
          ∏ i ∈ Finset.range d, max 1 (LinearMap.singularValues
            (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) i)) := by
  classical
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  -- Obtain the SVD data.
  obtain ⟨b, c, σ, hσnn, hLb, _hsq, hsv⟩ :=
    svd_exists (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
      (finrank_euclideanSpace_fin)
  -- Reduce to the origin via the translation isometry `y ↦ L x + y`.
  have hiso : Isometry (fun y : EuclideanSpace ℝ (Fin d) => L x + y) :=
    isometry_add_left (L x)
  have hball : closedBall x (ε : ℝ) = (fun y => x + y) '' closedBall 0 (ε : ℝ) := by
    ext w
    simp only [Set.mem_image, mem_closedBall, dist_zero_right]
    constructor
    · intro hw; exact ⟨w - x, by rw [← dist_eq_norm]; rwa [dist_comm] at hw ⊢, by abel⟩
    · rintro ⟨z, hz, rfl⟩; rw [dist_eq_norm]; simpa using hz
  have htrans : L '' closedBall x (ε : ℝ)
      = (fun y => L x + y) '' (L '' closedBall 0 (ε : ℝ)) := by
    rw [Set.image_image, hball, Set.image_image]
    exact Set.image_congr fun y _ => by rw [map_add]
  rw [htrans, hiso.coveringNumber_image]
  -- The volume bound at the origin with `δ = ε/2`.
  have hVbound : volume (cthickening ((ε : ℝ) / 2) (L '' closedBall 0 (ε : ℝ)))
      ≤ ENNReal.ofReal (∏ i, 2 * ((ε : ℝ) * σ i + (ε : ℝ) / 2)) *
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    volume_cthickening_image_closedBall_le_volProd L hεr (by positivity) b c σ hσnn hLb
  -- Apply the volume → covering bound.
  have hcov := Metric.coveringNumber_le_addHaar_div_of_addHaar_le
    (S := L '' closedBall 0 (ε : ℝ)) volume hε hVbound
  refine hcov.trans ?_
  -- Compute the division: `∏ 2(εσᵢ + ε/2) / (ε/2)^d = ∏ (4σᵢ + 2)`, then the algebraic bound.
  have hμpos : 0 < volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    measure_ball_pos volume 0 (by norm_num)
  have hμtop : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hpow : (0 : ℝ) < ((ε : ℝ) / 2) ^ d := pow_pos (by positivity) d
  rw [ENNReal.mul_div_mul_right _ _ hμpos.ne' hμtop, ← ENNReal.ofReal_div_of_pos hpow]
  apply ENNReal.ofReal_le_ofReal
  -- `∏ 2(εσᵢ + ε/2) / (ε/2)^d = ∏ (4σᵢ + 2) ≤ 6^d ∏ max 1 σᵢ`.
  have hdiv : (∏ i, 2 * ((ε : ℝ) * σ i + (ε : ℝ) / 2)) / ((ε : ℝ) / 2) ^ d
      = ∏ i, (4 * σ i + 2) := by
    rw [show ((ε : ℝ) / 2) ^ d = ∏ _i : Fin d, ((ε : ℝ) / 2) by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp
    ring
  rw [hdiv]
  -- Convert `∏ i ∈ range d, max 1 (singularValues L i)` to `∏ i : Fin d, max 1 (σ i)`.
  have hconv : (∏ i ∈ Finset.range d, max 1 (LinearMap.singularValues
            (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) i))
        = ∏ i : Fin d, max 1 (σ i) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => max 1 (LinearMap.singularValues
      (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) i)) d]
    exact Finset.prod_congr rfl fun i _ => by rw [hsv i]
  rw [hconv]
  exact prod_four_mul_add_two_le hσnn

end Covering

end ErgodicTheory
