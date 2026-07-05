/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.ConstantCocycle
import ErgodicTheory.Lyapunov.Extensions.SingularExponentTop
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# The top Lyapunov exponent of an arbitrary constant cocycle

The companion module `ErgodicTheory.Lyapunov.Extensions.ConstantCocycle` identifies the **full**
Lyapunov spectrum of a constant cocycle only in the **symmetric** case (`exponents_const`, for
`Mᵀ = M`). This module removes the symmetry hypothesis for the **top** exponent: for an
**arbitrary** real matrix `M`, the top Lyapunov exponent of the constant cocycle `x ↦ M` is the
logarithm of the **spectral radius** of `M`, i.e. the log of the maximal modulus of an eigenvalue
of `M` taken over `ℂ`.

The route is Gelfand's formula. The top exponent of the constant cocycle is
`lim_n (1/n) log ‖Mⁿ‖` (the operator-norm growth rate, recovered from the top singular value of
the cocycle iterate). By Gelfand's formula in the complex Banach algebra
`Matrix (Fin d) (Fin d) ℂ` (with its L2 operator norm), `‖(M_ℂ)ⁿ‖^{1/n}` converges to the
spectral radius of the complexification `M_ℂ = M.map (algebraMap ℝ ℂ)`. The L2 operator norm is
preserved by complexification (`ErgodicTheory.l2_opNorm_map_ofReal`), so the real growth rate is
exactly the log of `spectralRadius ℂ M_ℂ`.

## Main results

* `ErgodicTheory.l2_opNorm_map_ofReal` — the L2 operator norm of a real matrix equals the L2 operator
  norm of its complexification `M.map (algebraMap ℝ ℂ)`.
* `ErgodicTheory.tendsto_pow_norm_one_div_spectralRadius` —
  `‖Mⁿ‖^{1/n} → (spectralRadius ℂ M_ℂ).toReal`.
* `ErgodicTheory.tendsto_log_opNorm_pow_log_spectralRadius` —
  `(1/n) log ‖Mⁿ‖ → Real.log (spectralRadius ℂ M_ℂ).toReal`.
* `ErgodicTheory.topExponent_constantCocycle_eq_log_spectralRadius` — for ergodic `T` and an
  invertible (not necessarily symmetric) `M`, the top Lyapunov exponent of the constant cocycle
  equals `Real.log (spectralRadius ℂ M_ℂ).toReal`.

## References

* I. M. Gelfand, *Normierte Ringe*, Mat. Sb. **9** (1941), 3–24.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator ENNReal

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## Complexification preserves the L2 operator norm -/

/-- **Complexification preserves the L2 operator norm.** For a real square matrix `M`, the L2
operator norm of `M` equals the L2 operator norm of its complexification
`M_ℂ = M.map (algebraMap ℝ ℂ)`.

For `z : EuclideanSpace ℂ (Fin d)` with real/imaginary parts the real vectors `u, v`
(`u i = (z i).re`, `v i = (z i).im`), the `i`-th coordinate of `M_ℂ *ᵥ z` is
`(M *ᵥ u) i + (M *ᵥ v) i • I` (since `M` is real), so
`‖(M_ℂ *ᵥ z) i‖² = (M *ᵥ u) i² + (M *ᵥ v) i²` and summing gives
`‖M_ℂ z‖² = ‖M u‖² + ‖M v‖² ≤ ‖M‖²(‖u‖² + ‖v‖²) = ‖M‖² ‖z‖²`; the reverse inequality is the
restriction to real vectors. -/
theorem l2_opNorm_map_ofReal (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖M.map (algebraMap ℝ ℂ)‖ = ‖M‖ := by
  classical
  set Mℂ := M.map (algebraMap ℝ ℂ) with hMℂ
  set fℂ := Matrix.toEuclideanCLM (𝕜 := ℂ) Mℂ with hfℂ
  set fℝ := Matrix.toEuclideanCLM (𝕜 := ℝ) M with hfℝ
  -- real/imaginary parts of a complex Euclidean vector, as real Euclidean vectors.
  let re : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun z => WithLp.toLp 2 (fun j => (WithLp.ofLp z j).re)
  let im : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun z => WithLp.toLp 2 (fun j => (WithLp.ofLp z j).im)
  -- coordinatewise: `ofLp (fℂ z) i = (fℝ (re z)) i + (fℝ (im z)) i * I`.
  have hentry : ∀ (z : EuclideanSpace ℂ (Fin d)) (i : Fin d),
      WithLp.ofLp (fℂ z) i
        = ((WithLp.ofLp (fℝ (re z)) i : ℝ) : ℂ)
          + ((WithLp.ofLp (fℝ (im z)) i : ℝ) : ℂ) * Complex.I := by
    intro z i
    simp only [hfℂ, hfℝ, hMℂ, re, im, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec, Matrix.map_apply, dotProduct, Complex.coe_algebraMap]
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Complex.re_add_im (WithLp.ofLp z j)]
    push_cast
    ring
  -- `‖fℂ z‖² = ‖fℝ (re z)‖² + ‖fℝ (im z)‖²`.
  have hnormsq : ∀ z : EuclideanSpace ℂ (Fin d),
      ‖fℂ z‖ ^ 2 = ‖fℝ (re z)‖ ^ 2 + ‖fℝ (im z)‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ‖(fℂ z) i‖ = ‖WithLp.ofLp (fℂ z) i‖ from rfl, ← Complex.normSq_eq_norm_sq,
      hentry z i, Complex.normSq_add_mul_I]
    simp only [Real.norm_eq_abs, sq_abs]
  -- `‖z‖² = ‖re z‖² + ‖im z‖²`.
  have hznorm : ∀ z : EuclideanSpace ℂ (Fin d),
      ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ‖z i‖ = ‖WithLp.ofLp z i‖ from rfl, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [re, im, Real.norm_eq_abs, sq_abs]
    ring
  refine le_antisymm ?_ ?_
  · -- `‖Mℂ‖ ≤ ‖M‖`.
    rw [← Matrix.l2_opNorm_toEuclideanCLM, ← hfℂ]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have hsq : ‖fℂ z‖ ^ 2 ≤ (‖M‖ * ‖z‖) ^ 2 := by
      rw [hnormsq z, mul_pow, hznorm z, mul_add]
      have hu : ‖fℝ (re z)‖ ^ 2 ≤ ‖M‖ ^ 2 * ‖re z‖ ^ 2 := by
        have hle : ‖fℝ (re z)‖ ≤ ‖M‖ * ‖re z‖ := by
          calc ‖fℝ (re z)‖ ≤ ‖fℝ‖ * ‖re z‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖M‖ * ‖re z‖ := by rw [hfℝ, Matrix.l2_opNorm_toEuclideanCLM]
        nlinarith [norm_nonneg (fℝ (re z)), norm_nonneg (re z), norm_nonneg M, hle]
      have hv : ‖fℝ (im z)‖ ^ 2 ≤ ‖M‖ ^ 2 * ‖im z‖ ^ 2 := by
        have hle : ‖fℝ (im z)‖ ≤ ‖M‖ * ‖im z‖ := by
          calc ‖fℝ (im z)‖ ≤ ‖fℝ‖ * ‖im z‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖M‖ * ‖im z‖ := by rw [hfℝ, Matrix.l2_opNorm_toEuclideanCLM]
        nlinarith [norm_nonneg (fℝ (im z)), norm_nonneg (im z), norm_nonneg M, hle]
      linarith
    have h1 : (0 : ℝ) ≤ ‖M‖ * ‖z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg (fℂ z), hsq]
  · -- `‖M‖ ≤ ‖Mℂ‖`: restrict to the complexification of a real vector.
    rw [← Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ), ← hfℝ]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set z : EuclideanSpace ℂ (Fin d) :=
      WithLp.toLp 2 (fun j => ((WithLp.ofLp x j : ℝ) : ℂ)) with hzdef
    have hzre : re z = x := by
      simp only [re, hzdef, Complex.ofReal_re, WithLp.toLp_ofLp]
    have hzim : im z = 0 := by
      simp only [im, hzdef, Complex.ofReal_im]
      rfl
    have hzx : ‖z‖ = ‖x‖ := by
      have := hznorm z
      rw [hzre, hzim, norm_zero] at this
      nlinarith [norm_nonneg z, norm_nonneg x, this]
    have hMx : ‖fℝ x‖ = ‖fℂ z‖ := by
      have := hnormsq z
      rw [hzre, hzim] at this
      have hz0 : ‖fℝ (0 : EuclideanSpace ℝ (Fin d))‖ = 0 := by rw [map_zero, norm_zero]
      rw [hz0] at this
      nlinarith [norm_nonneg (fℝ x), norm_nonneg (fℂ z), this]
    rw [hMx, ← hzx]
    calc ‖fℂ z‖ ≤ ‖fℂ‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ z
      _ = ‖Mℂ‖ * ‖z‖ := by rw [hfℂ, Matrix.l2_opNorm_toEuclideanCLM]

/-! ## Finiteness and positivity of the spectral radius -/

/-- For a real matrix with `d ≠ 0`, the complex spectral radius of the complexification is
finite (bounded by the norm; the complex matrix algebra is a nontrivial `CStarRing`, hence a
`NormOneClass`). -/
theorem spectralRadius_map_ofReal_ne_top [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ) :
    spectralRadius ℂ (M.map (algebraMap ℝ ℂ)) ≠ ⊤ := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  haveI : Nontrivial (Matrix (Fin d) (Fin d) ℂ) := inferInstance
  exact ne_top_of_le_ne_top (by simp) (spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) _)

/-- For a real square matrix with `d ≠ 0`, the complexification has nonempty spectrum over `ℂ`. -/
theorem spectrum_map_ofReal_nonempty [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ) :
    (spectrum ℂ (M.map (algebraMap ℝ ℂ))).Nonempty := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ _

/-- For an **invertible** real matrix `M` (with `d ≠ 0`), the complex spectral radius of the
complexification is strictly positive: every spectral value is nonzero (`0 ∉ spectrum`, as `M_ℂ`
is a unit), and the spectral radius is attained at one such value. -/
theorem spectralRadius_map_ofReal_pos [NeZero d] {M : Matrix (Fin d) (Fin d) ℝ}
    (hdet : M.det ≠ 0) : 0 < (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal := by
  set Mℂ := M.map (algebraMap ℝ ℂ) with hMℂ
  -- `M_ℂ` is a unit: its determinant `(det M : ℂ)` is nonzero.
  have hdetℂ : Mℂ.det ≠ 0 := by
    have hmap : Mℂ.det = (algebraMap ℝ ℂ) M.det := by
      rw [hMℂ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [hmap]
    simpa [Complex.coe_algebraMap] using (Complex.ofReal_ne_zero).mpr hdet
  have hunit : IsUnit Mℂ := (Matrix.isUnit_iff_isUnit_det Mℂ).mpr (Ne.isUnit hdetℂ)
  -- `0 ∉ spectrum ℂ M_ℂ`.
  have hzero : (0 : ℂ) ∉ spectrum ℂ Mℂ := fun h => (spectrum.zero_mem_iff ℂ |>.mp h) hunit
  -- the spectral radius is the nnnorm of a spectral value, which is nonzero.
  obtain ⟨k, hk, hkr⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum_map_ofReal_nonempty M)
  have hkne : k ≠ 0 := fun h => hzero (h ▸ hk)
  have hknn : (0 : ℝ) < ‖k‖ := norm_pos_iff.mpr hkne
  have hne_top : spectralRadius ℂ Mℂ ≠ ⊤ := spectralRadius_map_ofReal_ne_top M
  rw [← hkr]
  simp only [ENNReal.coe_toReal, coe_nnnorm]
  exact hknn

/-! ## The Gelfand limit for the L2 operator norm of a real matrix -/

/-- **Gelfand's formula for a real matrix (L2 operator norm).** For any real square matrix `M`,
`‖Mⁿ‖^{1/n} → (spectralRadius ℂ M_ℂ).toReal`, where `M_ℂ = M.map (algebraMap ℝ ℂ)`. Obtained from
Gelfand's formula in the complex Banach algebra `Matrix (Fin d) (Fin d) ℂ`
(`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`), transported to the real norm via
`l2_opNorm_map_ofReal` (complexification preserves the L2 operator norm). -/
theorem tendsto_pow_norm_one_div_spectralRadius [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ) :
    Tendsto (fun n : ℕ => ‖M ^ n‖ ^ (1 / n : ℝ)) atTop
      (𝓝 (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal) := by
  set Mℂ := M.map (algebraMap ℝ ℂ) with hMℂ
  -- Gelfand in the complex algebra.
  have hg := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius Mℂ
  -- `‖M_ℂ^n‖ = ‖M^n‖`.
  have hnorm : ∀ n : ℕ, ‖Mℂ ^ n‖ = ‖M ^ n‖ := by
    intro n
    rw [hMℂ, ← Matrix.map_pow M (algebraMap ℝ ℂ) n, l2_opNorm_map_ofReal]
  have hg' : Tendsto (fun n : ℕ => ENNReal.ofReal (‖M ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ Mℂ)) := by
    refine hg.congr fun n => ?_
    rw [hnorm]
  -- push through `toReal` (the spectral radius is finite).
  have hfin : ∀ n : ℕ, ENNReal.ofReal (‖M ^ n‖ ^ (1 / n : ℝ)) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hconv := (ENNReal.tendsto_toReal_iff hfin (spectralRadius_map_ofReal_ne_top M)).mpr hg'
  refine hconv.congr fun n => ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- **The log-norm growth rate of a real matrix is the log spectral radius.** For an **invertible**
real matrix `M` (with `d ≠ 0`), `(1/n) log ‖Mⁿ‖ → Real.log (spectralRadius ℂ M_ℂ).toReal`. This is
the logarithm of `tendsto_pow_norm_one_div_spectralRadius`, valid because the spectral radius is
strictly positive (`spectralRadius_map_ofReal_pos`). -/
theorem tendsto_log_opNorm_pow_log_spectralRadius [NeZero d] {M : Matrix (Fin d) (Fin d) ℝ}
    (hdet : M.det ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖M ^ n‖) atTop
      (𝓝 (Real.log (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal)) := by
  set ρ := (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal
  have hρpos : 0 < ρ := spectralRadius_map_ofReal_pos hdet
  -- `log (‖Mⁿ‖^{1/n}) → log ρ` by continuity of `log` at `ρ > 0`.
  have hlog := (Real.continuousAt_log hρpos.ne').tendsto.comp
    (tendsto_pow_norm_one_div_spectralRadius M)
  simp only [Function.comp_def] at hlog
  -- `log (‖Mⁿ‖^{1/n}) = (1/n) log ‖Mⁿ‖` for `n ≥ 1`.
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n _
  have hpos : 0 < ‖M ^ n‖ := by
    have := norm_cocycle_pos (A := fun _ : Unit => M) (T := id) (fun _ => hdet) n ()
    rwa [cocycle_const] at this
  rw [Real.log_rpow hpos, one_div, mul_comm]

/-! ## The top Lyapunov exponent of a constant cocycle -/

section TopExponent

variable {μ : Measure X} {T : X → X}

/-- **The top Lyapunov exponent of an arbitrary constant cocycle is the log spectral radius.**
For an ergodic, probability-preserving `(X, μ, T)` and **any** real square matrix `M` with
`d ≠ 0` and `det M ≠ 0` (no symmetry assumption), the top Lyapunov exponent of the constant
cocycle `x ↦ M` equals `Real.log` of the spectral radius of `M`, i.e. the log of the maximal
modulus of an eigenvalue of `M` taken over `ℂ`.

The top exponent `exponents … 0` is the a.e. limit of `(1/n) log σ₀(toEuclideanLin Mⁿ)`
(`exponents_tendsto_log_singularValue` at index `0`), and `σ₀(toEuclideanLin Mⁿ) = ‖Mⁿ‖`
(`top_singularValue_eq_opNorm`), so a.e. `(1/n) log ‖Mⁿ‖ → topExponent`. This deterministic
sequence also tends to `log (spectralRadius ℂ M_ℂ).toReal` by Gelfand's formula
(`tendsto_log_opNorm_pow_log_spectralRadius`); uniqueness of limits closes the gap. -/
theorem topExponent_constantCocycle_eq_log_spectralRadius
    [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {M : Matrix (Fin d) (Fin d) ℝ} (hdet : M.det ≠ 0) :
    topExponent hT (const_det_ne_zero hdet) (const_measurable M) (const_integrableLogNorm M)
        (const_integrableLogNorm_inv M)
      = Real.log (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal := by
  set hA := const_det_ne_zero (X := X) hdet
  -- the deterministic Gelfand limit.
  have hgelfand : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖M ^ n‖) atTop
      (𝓝 (Real.log (spectralRadius ℂ (M.map (algebraMap ℝ ℂ))).toReal)) :=
    tendsto_log_opNorm_pow_log_spectralRadius hdet
  -- the singular-value σ-limit at index `0`, a.e.; extract a single point.
  obtain ⟨x, hx⟩ := (exponents_tendsto_log_singularValue hT hA (const_measurable M)
    (const_integrableLogNorm M) (const_integrableLogNorm_inv M)
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩).exists
  -- rewrite the σ-limit as `(1/n) log ‖Mⁿ‖`.
  have hx' : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖M ^ n‖) atTop
      (𝓝 (topExponent hT hA (const_measurable M) (const_integrableLogNorm M)
          (const_integrableLogNorm_inv M))) := by
    refine hx.congr fun n => ?_
    rw [cocycle_const, top_singularValue_eq_opNorm]
  exact tendsto_nhds_unique hx' hgelfand

end TopExponent

end ErgodicTheory
