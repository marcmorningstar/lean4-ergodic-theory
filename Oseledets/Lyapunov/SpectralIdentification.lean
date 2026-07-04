/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.StratumLogGrowthBounds
import Oseledets.Lyapunov.SlowFiltrationMeasurable
import Oseledets.Lyapunov.SpectrumResiduals

/-!
# Band-projector limit identification and the reverse slow-flag inclusion

Main results:

1. `tendsto_cfc_of_tendsto_of_lipschitz` — the continuous functional calculus of a (Lipschitz, hence
   continuous) function is continuous under matrix limits of Hermitian matrices.
2. `ae_tendsto_bandProjector_cfc_indicator` — a.e., the band projector limit at a non-eigenvalue
   threshold `c` is the Λ-spectral projector `cfc 𝟙_{(c,∞)} (lambdaHat …)`.
3. `ae_lambdaSublevel_le_vslow` — the reverse slow-flag inclusion `lambdaSublevel t ⊆ vslow (e^t)`.

The first result rests on a Frobenius / Hilbert–Schmidt Lipschitz estimate for the functional
calculus; the second uses a continuous Lipschitz clamp surrogate for the indicator of `(c, ∞)` to
transfer convergence through the calculus; the third combines the spectral identification with the
Furstenberg–Kesten growth bounds to obtain the inclusion of sublevel sets into slow spaces.
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]

/-! ## The functional calculus is matrix-limit continuous for Lipschitz functions

We prove the Frobenius / Hilbert–Schmidt Lipschitz bound: for Hermitian `A, B` and `K`-Lipschitz
`f`, `HS_B (cfc f A - cfc f B) ≤ K² HS_B (A - B)`, where `HS_B Y := ∑ⱼ ‖toEuclideanLin Y (vⱼ)‖²`
and `{vⱼ}` is the eigenbasis of `B`.  The per-`j` bound holds because `vⱼ` is an eigenvector of `B`:
expanding in the eigenbasis `{uᵢ}` of `A`, `⟪uᵢ, (cfc f A − cfc f B) vⱼ⟫ = (f αᵢ − f βⱼ)⟪uᵢ, vⱼ⟫`
and `⟪uᵢ, (A − B) vⱼ⟫ = (αᵢ − βⱼ)⟪uᵢ, vⱼ⟫`, so `|f αᵢ − f βⱼ| ≤ K |αᵢ − βⱼ|` gives it termwise.
The convergence then follows by an injective-linear-map (antilipschitz) sandwich. -/

/-- Per-eigenvector Frobenius bound: with `vⱼ` an eigenvector of `B`, the `cfc`-difference applied
to `vⱼ` is controlled (squared norm) by `K²` times the matrix-difference applied to `vⱼ`. -/
theorem norm_sq_toEuclideanLin_cfc_sub_eigenvectorBasis_le
    {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) (j : Fin d) :
    ‖Matrix.toEuclideanLin (cfc f A - cfc f B) (hB.eigenvectorBasis j)‖ ^ 2
      ≤ (K : ℝ) ^ 2 * ‖Matrix.toEuclideanLin (A - B) (hB.eigenvectorBasis j)‖ ^ 2 := by
  classical
  set u := hA.eigenvectorBasis with hu
  set vj := (hB.eigenvectorBasis j : EuclideanSpace ℝ (Fin d)) with hvj
  -- `A` and `cfc f A` are symmetric operators on `EuclideanSpace`.
  have hAsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hcfcAsym : (Matrix.toEuclideanLin (cfc f A)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (cfc_predicate f A : IsSelfAdjoint (cfc f A)).isHermitian
  -- Inner products with each `uᵢ`.
  have hcfc_inner : ∀ i, ⟪u i, Matrix.toEuclideanLin (cfc f A - cfc f B) vj⟫_ℝ
      = (f (hA.eigenvalues i) - f (hB.eigenvalues j)) * ⟪u i, vj⟫_ℝ := by
    intro i
    have hAv : ⟪u i, Matrix.toEuclideanLin (cfc f A) vj⟫_ℝ
        = f (hA.eigenvalues i) * ⟪u i, vj⟫_ℝ := by
      rw [← hcfcAsym (u i) vj, toEuclideanLin_cfc_eigenvectorBasis A hA f i, inner_smul_left,
        conj_trivial]
    have hBv : Matrix.toEuclideanLin (cfc f B) vj = f (hB.eigenvalues j) • vj := by
      rw [hvj]; exact toEuclideanLin_cfc_eigenvectorBasis B hB f j
    rw [map_sub, LinearMap.sub_apply, inner_sub_right, hAv, hBv, inner_smul_right]; ring
  have hmat_inner : ∀ i, ⟪u i, Matrix.toEuclideanLin (A - B) vj⟫_ℝ
      = (hA.eigenvalues i - hB.eigenvalues j) * ⟪u i, vj⟫_ℝ := by
    intro i
    have hAv : ⟪u i, Matrix.toEuclideanLin A vj⟫_ℝ = hA.eigenvalues i * ⟪u i, vj⟫_ℝ := by
      have hAui : Matrix.toEuclideanLin A (u i) = hA.eigenvalues i • u i := by
        rw [hu, Matrix.toLpLin_apply]
        rw [Matrix.IsHermitian.mulVec_eigenvectorBasis hA i]; rfl
      rw [← hAsym (u i) vj, hAui, inner_smul_left, conj_trivial]
    have hBv : Matrix.toEuclideanLin B vj = hB.eigenvalues j • vj := by
      rw [hvj, Matrix.toLpLin_apply, Matrix.IsHermitian.mulVec_eigenvectorBasis hB j]; rfl
    rw [map_sub, LinearMap.sub_apply, inner_sub_right, hAv, hBv, inner_smul_right]; ring
  -- Parseval in the `u`-basis for both sides.
  have hpars_cfc : ‖Matrix.toEuclideanLin (cfc f A - cfc f B) vj‖ ^ 2
      = ∑ i, ⟪u i, Matrix.toEuclideanLin (cfc f A - cfc f B) vj⟫_ℝ ^ 2 := by
    rw [← OrthonormalBasis.sum_sq_norm_inner_right u]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have hpars_mat : ‖Matrix.toEuclideanLin (A - B) vj‖ ^ 2
      = ∑ i, ⟪u i, Matrix.toEuclideanLin (A - B) vj⟫_ℝ ^ 2 := by
    rw [← OrthonormalBasis.sum_sq_norm_inner_right u]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  rw [hpars_cfc, hpars_mat, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hcfc_inner i, hmat_inner i, mul_pow, mul_pow, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  -- `(f αᵢ − f βⱼ)² ≤ K² (αᵢ − βⱼ)²` by Lipschitz.
  have hlip : |f (hA.eigenvalues i) - f (hB.eigenvalues j)|
      ≤ (K : ℝ) * |hA.eigenvalues i - hB.eigenvalues j| := by
    have := hf.dist_le_mul (hA.eigenvalues i) (hB.eigenvalues j)
    rwa [Real.dist_eq, Real.dist_eq] at this
  have h1 : (f (hA.eigenvalues i) - f (hB.eigenvalues j)) ^ 2
      ≤ ((K : ℝ) * |hA.eigenvalues i - hB.eigenvalues j|) ^ 2 := by
    rw [← sq_abs (f (hA.eigenvalues i) - f (hB.eigenvalues j))]
    exact pow_le_pow_left₀ (abs_nonneg _) hlip 2
  calc (f (hA.eigenvalues i) - f (hB.eigenvalues j)) ^ 2
      ≤ ((K : ℝ) * |hA.eigenvalues i - hB.eigenvalues j|) ^ 2 := h1
    _ = (K : ℝ) ^ 2 * (hA.eigenvalues i - hB.eigenvalues j) ^ 2 := by
        rw [mul_pow, sq_abs]

/-- The continuous functional calculus of a Lipschitz (hence continuous) function
is continuous under matrix limits of Hermitian matrices: if `M n → L` with all `M n` and `L`
Hermitian, then `cfc f (M n) → cfc f L`. -/
theorem tendsto_cfc_of_tendsto_of_lipschitz {M : ℕ → Matrix (Fin d) (Fin d) ℝ}
    {L : Matrix (Fin d) (Fin d) ℝ} (hM : ∀ n, (M n).IsHermitian) (hL : L.IsHermitian)
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (hlim : Filter.Tendsto M Filter.atTop (𝓝 L)) :
    Filter.Tendsto (fun n => cfc f (M n)) Filter.atTop (𝓝 (cfc f L)) := by
  classical
  -- The reference linear embedding `Φ Y = (j ↦ toEuclideanLin Y (vⱼ))` (vⱼ = eigenbasis of `L`).
  let Φ : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d → EuclideanSpace ℝ (Fin d)) :=
    { toFun := fun Y j => Matrix.toEuclideanLin Y (hL.eigenvectorBasis j)
      map_add' := fun Y Z => by funext j; simp [map_add]
      map_smul' := fun c Y => by funext j; simp [map_smul] }
  -- `Φ` is injective: `Φ Y = 0` kills `toEuclideanLin Y` on a basis, hence `Y = 0`.
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    have hzero : ∀ j, Matrix.toEuclideanLin Y (hL.eigenvectorBasis j) = 0 := fun j => congrFun hY j
    have hlin0 : Matrix.toEuclideanLin Y = 0 := by
      apply (hL.eigenvectorBasis).toBasis.ext
      intro j; simpa using hzero j
    have : Y = 0 := by
      apply Matrix.toEuclideanLin.injective
      rw [hlin0, map_zero]
    exact this
  -- `Φ` is antilipschitz (injective linear map on a finite-dimensional space).
  obtain ⟨c, _hc, hanti⟩ :=
    (Φ.injective_iff_antilipschitz (𝕜 := ℝ)).mp hΦinj
  -- It suffices to show `‖cfc f (M n) - cfc f L‖ → 0`.
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (g := fun n =>
    (c : ℝ) * ((K : ℝ) * ‖Φ (M n - L)‖)) ?_ ?_
  · intro n
    rw [dist_eq_norm]
    -- antilipschitz: `‖X‖ = dist X 0 ≤ c · dist (Φ X) 0 = c · ‖Φ X‖`.
    have hX : ‖cfc f (M n) - cfc f L‖ ≤ (c : ℝ) * ‖Φ (cfc f (M n) - cfc f L)‖ := by
      have := hanti.le_mul_dist (cfc f (M n) - cfc f L) 0
      rw [dist_zero_right, map_zero, dist_zero_right] at this
      exact this
    -- `‖Φ (cfc f (M n) - cfc f L)‖ ≤ K ‖Φ (M n - L)‖` via the per-`j` Frobenius bound (sup-norm).
    have hΦle : ‖Φ (cfc f (M n) - cfc f L)‖ ≤ (K : ℝ) * ‖Φ (M n - L)‖ := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro j
      have hbound := norm_sq_toEuclideanLin_cfc_sub_eigenvectorBasis_le (hM n) hL hf j
      have hcoord : ‖Φ (M n - L) j‖ ≤ ‖Φ (M n - L)‖ := norm_le_pi_norm _ j
      have hsqj : ‖Φ (cfc f (M n) - cfc f L) j‖ ^ 2 ≤ ((K : ℝ) * ‖Φ (M n - L)‖) ^ 2 := by
        calc ‖Φ (cfc f (M n) - cfc f L) j‖ ^ 2
            = ‖Matrix.toEuclideanLin (cfc f (M n) - cfc f L) (hL.eigenvectorBasis j)‖ ^ 2 := rfl
          _ ≤ (K : ℝ) ^ 2 * ‖Matrix.toEuclideanLin (M n - L) (hL.eigenvectorBasis j)‖ ^ 2 := hbound
          _ = (K : ℝ) ^ 2 * ‖Φ (M n - L) j‖ ^ 2 := rfl
          _ ≤ (K : ℝ) ^ 2 * ‖Φ (M n - L)‖ ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact pow_le_pow_left₀ (norm_nonneg _) hcoord 2
          _ = ((K : ℝ) * ‖Φ (M n - L)‖) ^ 2 := by ring
      have hsqrt := Real.sqrt_le_sqrt hsqj
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hsqrt
    calc ‖cfc f (M n) - cfc f L‖
        ≤ (c : ℝ) * ‖Φ (cfc f (M n) - cfc f L)‖ := hX
      _ ≤ (c : ℝ) * ((K : ℝ) * ‖Φ (M n - L)‖) := by
          apply mul_le_mul_of_nonneg_left hΦle (by positivity)
  · -- The bound `c · (K · ‖Φ(M n - L)‖) → 0` since `Φ(M n - L) → 0`.
    have hΦcont : Continuous Φ := Φ.continuous_of_finiteDimensional
    have hMtoL : Tendsto (fun n => M n - L) atTop (𝓝 0) := by
      simpa using hlim.sub (tendsto_const_nhds (x := L))
    have hΦ0 : Tendsto (fun n => Φ (M n - L)) atTop (𝓝 0) := by
      have h0 : Φ 0 = 0 := map_zero Φ
      have := (hΦcont.tendsto 0).comp hMtoL
      rw [h0] at this
      exact this
    have hnorm0 : Tendsto (fun n => ‖Φ (M n - L)‖) atTop (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : Fin d → EuclideanSpace ℝ (Fin d))).comp hΦ0
    have : Tendsto (fun n => (c : ℝ) * ((K : ℝ) * ‖Φ (M n - L)‖))
        atTop (𝓝 ((c : ℝ) * ((K : ℝ) * 0))) :=
      Tendsto.const_mul _ (Tendsto.const_mul _ hnorm0)
    simpa using this

/-! ## The band-projector limit is the Λ-spectral projector -/

/-- A continuous clamp surrogate `χ` for the indicator of `(c, ∞)`: `χ = 0` on `(-∞, c]`,
`χ = 1` on `[c + h, ∞)`, linear in between, Lipschitz with constant `h⁻¹` for `h > 0`. -/
noncomputable def clampSurrogate (c h : ℝ) : ℝ → ℝ :=
  fun t => max 0 (min 1 ((t - c) / h))

theorem clampSurrogate_continuous (c h : ℝ) : Continuous (clampSurrogate c h) := by
  unfold clampSurrogate
  fun_prop

theorem clampSurrogate_lipschitz {c h : ℝ} (hh : 0 < h) :
    ∃ K : NNReal, LipschitzWith K (clampSurrogate c h) := by
  unfold clampSurrogate
  -- `t ↦ (t - c)/h` is Lipschitz with constant `h⁻¹`; clamp by `max`/`min` preserves it.
  have hlin : LipschitzWith (Real.toNNReal h⁻¹) (fun t : ℝ => (t - c) / h) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hh))]
    rw [div_sub_div_same, abs_div, abs_of_pos hh]
    rw [show x - c - (y - c) = x - y by ring]
    rw [div_eq_inv_mul, mul_comm]
  exact ⟨_, (hlin.const_min 1).const_max 0⟩

/-- `clampSurrogate c h t = 0` for `t ≤ c`. -/
theorem clampSurrogate_eq_zero {c h : ℝ} (hh : 0 < h) {t : ℝ} (ht : t ≤ c) :
    clampSurrogate c h t = 0 := by
  unfold clampSurrogate
  have hle : (t - c) / h ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hh)
  rw [max_eq_left (min_le_of_right_le hle)]

/-- `clampSurrogate c h t = 1` for `t ≥ c + h`. -/
theorem clampSurrogate_eq_one {c h : ℝ} (hh : 0 < h) {t : ℝ} (ht : c + h ≤ t) :
    clampSurrogate c h t = 1 := by
  unfold clampSurrogate
  have h1 : 1 ≤ (t - c) / h := by
    rw [le_div_iff₀ hh]; linarith
  rw [min_eq_left h1, max_eq_right (by norm_num)]

omit [NeZero d] in
/-- Every real spectrum value of a Hermitian matrix is one of its sorted eigenvalues
`eigenvalues₀`. -/
theorem exists_eigenvalues₀_eq_of_mem_spectrum {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsHermitian) {s : ℝ} (hs : s ∈ _root_.spectrum ℝ M) :
    ∃ i : Fin (Fintype.card (Fin d)), hM.eigenvalues₀ i = s := by
  rw [hM.spectrum_real_eq_range_eigenvalues] at hs
  obtain ⟨i, rfl⟩ := hs
  exact ⟨_, rfl⟩

/-- A.e., for every threshold `c > 0` that is not one of the limiting eigenvalues
`e^{lamSing i}`, the band projector `cfc 𝟙_{(c,∞)} (qpow n)` converges to the Λ-spectral projector
`cfc 𝟙_{(c,∞)} (lambdaHat A T x)`. -/
theorem ae_tendsto_bandProjector_cfc_indicator
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X} (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, ∀ c : ℝ, 0 < c → (∀ i : Fin d, Real.exp (lamSing A T x (i : ℕ)) ≠ c) →
      Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
        Filter.atTop (𝓝 (cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) (lambdaHat A T x))) := by
  filter_upwards [tendsto_oseledetsLimit hT hA hAmeas hint hint',
    oseledetsLimit_isSelfAdjoint hT hA hAmeas hint hint',
    eigenvalues₀_qpow_tendsto_exp_lamSing hT hA hAmeas hint hint',
    oseledetsLimit_eigenvalues₀_eq hT hA hAmeas hint hint']
    with x hxlim hxsa hxeig hxeq c hc hcne0
  classical
  -- Restate the non-eigenvalue hypothesis indexed by `Fin (card (Fin d))`.
  have hcne : ∀ i : Fin (Fintype.card (Fin d)), Real.exp (lamSing A T x (i : ℕ)) ≠ c := by
    intro i
    have hi : (i : ℕ) < d := lt_of_lt_of_eq i.isLt (Fintype.card_fin d)
    have := hcne0 ⟨(i : ℕ), hi⟩
    simpa using this
  -- On the good set, `lambdaHat A T x = oseledetsLimit A T x` (since the latter is Hermitian).
  have hLeq : lambdaHat A T x = oseledetsLimit A T x := by
    rw [lambdaHat, if_pos ((Matrix.isHermitian_iff_isSelfAdjoint).mpr hxsa)]
  have hLH : (lambdaHat A T x).IsHermitian := by
    rw [hLeq]; exact (Matrix.isHermitian_iff_isSelfAdjoint).mpr hxsa
  have hLHosel : (oseledetsLimit A T x).IsHermitian :=
    (Matrix.isHermitian_iff_isSelfAdjoint).mpr hxsa
  -- The eigenvalues of `lambdaHat` are exactly `e^{lamSing i}`.
  have hLeig : ∀ i : Fin (Fintype.card (Fin d)),
      hLH.eigenvalues₀ i = Real.exp (lamSing A T x (i : ℕ)) := by
    intro i
    have hcongr : hLH.eigenvalues₀ i = hLHosel.eigenvalues₀ i := by
      congr 1
    rw [hcongr]; exact hxeq hLHosel i
  -- The gap `δ = min over `i` of `|e^{lamSing i} - c|` is positive (c not an eigenvalue).
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun i : Fin (Fintype.card (Fin d)) => |Real.exp (lamSing A T x (i : ℕ)) - c|) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro i _
    rw [abs_pos, sub_ne_zero]
    exact hcne _
  have hδle : ∀ i : Fin (Fintype.card (Fin d)),
      δ ≤ |Real.exp (lamSing A T x (i : ℕ)) - c| := by
    intro i; rw [hδ]; exact Finset.inf'_le _ (Finset.mem_univ i)
  -- The continuous Lipschitz surrogate `χ`.
  set χ : ℝ → ℝ := clampSurrogate c (δ / 2) with hχ
  have hχcont : Continuous χ := clampSurrogate_continuous c (δ / 2)
  obtain ⟨K, hχlip⟩ := clampSurrogate_lipschitz (c := c) (h := δ / 2) (by linarith)
  -- Eventually every sorted eigenvalue of `qpow n` is within `δ/2` of its limit.
  have heventually : ∀ᶠ n in atTop, ∀ i : Fin (Fintype.card (Fin d)),
      |(qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
        - Real.exp (lamSing A T x (i : ℕ))| < δ / 2 := by
    rw [eventually_all]
    intro i
    have := (hxeig i).eventually
      (eventually_abs_sub_lt (Real.exp (lamSing A T x (i : ℕ))) (by linarith : (0:ℝ) < δ / 2))
    simpa using this
  -- On the spectrum of `qpow n`, the indicator agrees with `χ` (eventually).
  have hEqOnQ : ∀ᶠ n in atTop, (_root_.spectrum ℝ (qpow A T n x)).EqOn
      (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) χ := by
    filter_upwards [heventually] with n hn s hs
    obtain ⟨i, rfl⟩ := exists_eigenvalues₀_eq_of_mem_spectrum
      (qpow_isSelfAdjoint A T n x).isHermitian hs
    set s := (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i with hsdef
    have hclose : |s - Real.exp (lamSing A T x (i : ℕ))| < δ / 2 := hn i
    -- `e^{lamSing i}` is `≥ c + δ` or `≤ c - δ`.
    rcases lt_or_gt_of_ne (hcne i) with hlt | hgt
    · -- `e^{lamSing i} < c`, hence `≤ c - δ`, hence `s ≤ c`.
      have hle : Real.exp (lamSing A T x (i : ℕ)) ≤ c - δ := by
        have := hδle i
        rw [abs_of_neg (by linarith : Real.exp (lamSing A T x (i:ℕ)) - c < 0)] at this
        linarith
      have hsle : s ≤ c := by
        rw [abs_sub_lt_iff] at hclose; linarith
      have hsnotmem : s ∉ Set.Ioi c := by simp [Set.mem_Ioi]; linarith
      rw [Set.indicator_of_notMem hsnotmem, hχ, clampSurrogate_eq_zero (by linarith) hsle]
    · -- `e^{lamSing i} > c`, hence `≥ c + δ`, hence `s ≥ c + δ/2`.
      have hge : c + δ ≤ Real.exp (lamSing A T x (i : ℕ)) := by
        have := hδle i
        rw [abs_of_pos (by linarith : (0:ℝ) < Real.exp (lamSing A T x (i:ℕ)) - c)] at this
        linarith
      have hsge : c + δ / 2 ≤ s := by
        rw [abs_sub_lt_iff] at hclose; linarith
      have hsmem : s ∈ Set.Ioi c := by simp only [Set.mem_Ioi]; linarith
      rw [Set.indicator_of_mem hsmem, Pi.one_apply, hχ, clampSurrogate_eq_one (by linarith) hsge]
  -- On the spectrum of `lambdaHat`, the indicator agrees with `χ`.
  have hEqOnL : (_root_.spectrum ℝ (lambdaHat A T x)).EqOn
      (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) χ := by
    intro s hs
    obtain ⟨i, rfl⟩ := exists_eigenvalues₀_eq_of_mem_spectrum hLH hs
    rw [hLeig i]
    rcases lt_or_gt_of_ne (hcne i) with hlt | hgt
    · have hsnotmem : Real.exp (lamSing A T x (i : ℕ)) ∉ Set.Ioi c := by
        simp only [Set.mem_Ioi]; linarith
      rw [Set.indicator_of_notMem hsnotmem, hχ, clampSurrogate_eq_zero (by linarith) (le_of_lt hlt)]
    · have hge : c + δ ≤ Real.exp (lamSing A T x (i : ℕ)) := by
        have := hδle i
        rw [abs_of_pos (by linarith : (0:ℝ) < Real.exp (lamSing A T x (i:ℕ)) - c)] at this
        linarith
      have hsmem : Real.exp (lamSing A T x (i : ℕ)) ∈ Set.Ioi c := by
        simp only [Set.mem_Ioi]; linarith
      rw [Set.indicator_of_mem hsmem, Pi.one_apply, hχ,
        clampSurrogate_eq_one (by linarith) (by linarith)]
  -- Functional-calculus continuity: `cfc χ (qpow n) → cfc χ (lambdaHat)`.
  have hcfctend : Tendsto (fun n => cfc χ (qpow A T n x)) atTop (𝓝 (cfc χ (lambdaHat A T x))) :=
    tendsto_cfc_of_tendsto_of_lipschitz (fun n => (qpow_isSelfAdjoint A T n x).isHermitian) hLH
      hχlip (by rw [hLeq]; exact hxlim)
  -- Rewrite the limit point: `cfc χ (lambdaHat) = cfc 𝟙_{(c,∞)} (lambdaHat)`.
  have hlimpt : cfc χ (lambdaHat A T x)
      = cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) (lambdaHat A T x) :=
    cfc_congr (fun s hs => (hEqOnL hs).symm)
  rw [hlimpt] at hcfctend
  -- Eventually `bandProjector ... = cfc χ (qpow n)`.
  refine hcfctend.congr' ?_
  filter_upwards [hEqOnQ] with n hn
  rw [bandProjector, cfc_congr (fun s hs => (hn hs).symm)]

/-! ## The reverse slow-flag inclusion -/

/-- A.e., for every `t`, the `lambdaBar`-sublevel at `t` is contained in the
Λ-slow space `vslow (e^t)`.  This is the inclusion consumed by
`Oseledets.oseledets_filtration_of_upper'`. -/
theorem ae_lambdaSublevel_le_vslow
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X} (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, ∀ t : ℝ, lambdaSublevel A T x t ≤ vslow A T (Real.exp t) x := by
  filter_upwards [isUltrametricGrowth_lambdaBar hT hA hAmeas hint hint',
    spectrum_lambdaHat_eq_ae hT hA hAmeas hint hint',
    ae_tendsto_bandProjector_cfc_indicator hT hA hAmeas hint hint',
    isBoundedUnder_log_norm_cocycle_apply hT A hA hAmeas hint hint']
    with x hx hspec hidentx hbddx t v hv
  classical
  -- `v = 0` is in every submodule.
  by_cases hv0 : v = 0
  · rw [hv0]; exact Submodule.zero_mem _
  -- Otherwise `lambdaBar v ≤ t`.
  have hbar : lambdaBar A T x v ≤ t := by
    rcases (mem_lambdaSublevel hx t v).mp hv with h | h
    · exact absurd h hv0
    · exact h
  -- Suppose for contradiction `v ∉ vslow (exp t)`.
  by_contra hvnot
  -- Some eigenvalue `exp (lamSing j) > exp t`, else `slowProjector (exp t) = 1` and
  -- `vslow = ⊤ ∋ v`.
  have hexists : ∃ j : Fin d, Real.exp t < Real.exp (lamSing A T x (j : ℕ)) := by
    by_contra hno
    push Not at hno
    -- every eigenvalue `≤ exp t`, so the `Iic (exp t)` indicator is `1` on the spectrum.
    apply hvnot
    have hQ1 : slowProjector A T (Real.exp t) x = 1 := by
      rw [slowProjector]
      rw [show (1 : Matrix (Fin d) (Fin d) ℝ)
          = cfc (1 : ℝ → ℝ) (lambdaHat A T x) from
        (cfc_one (R := ℝ) (a := lambdaHat A T x) (lambdaHat_isSelfAdjoint A T x)).symm]
      refine cfc_congr ?_
      rw [hspec]
      rintro _ ⟨j, rfl⟩
      have hle : Real.exp (lamSing A T x (j : ℕ)) ≤ Real.exp t := hno j
      rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle), Pi.one_apply]
    -- `vslow (exp t) = range (toEuclideanCLM 1) = ⊤ ∋ v`.
    rw [vslow, mem_range_toEuclideanCLM_iff (by rw [hQ1, one_mul] : _ * _ = _), hQ1]
    rw [show Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) v = v from by
      rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (𝕜 := ℝ)]; simp]
  -- `e* := min over the (finite, nonempty) set of eigenvalues `> exp t``.
  set S : Finset ℝ :=
    (Finset.univ.image (fun j : Fin d => Real.exp (lamSing A T x (j : ℕ)))).filter
      (fun e => Real.exp t < e) with hS
  have hSne : S.Nonempty := by
    obtain ⟨j, hj⟩ := hexists
    exact ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j), hj⟩⟩
  set estar : ℝ := S.min' hSne with hestar
  have hestar_mem : estar ∈ S := S.min'_mem hSne
  have hestar_gt : Real.exp t < estar := (Finset.mem_filter.mp hestar_mem).2
  have hestar_le : ∀ j : Fin d, Real.exp t < Real.exp (lamSing A T x (j : ℕ)) →
      estar ≤ Real.exp (lamSing A T x (j : ℕ)) := by
    intro j hj
    exact S.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j), hj⟩)
  -- `c := (exp t + e*)/2`, in the open gap `(exp t, e*)`.
  set c : ℝ := (Real.exp t + estar) / 2 with hc
  have hct : Real.exp t < c := by rw [hc]; linarith
  have hce : c < estar := by rw [hc]; linarith
  have hcpos : 0 < c := lt_trans (Real.exp_pos t) hct
  -- `c` is not an eigenvalue: each (in-range) eigenvalue is `≤ exp t < c` or `≥ e* > c`.
  have hcne : ∀ i : Fin d, Real.exp (lamSing A T x (i : ℕ)) ≠ c := by
    intro i
    by_cases hgt : Real.exp t < Real.exp (lamSing A T x (i : ℕ))
    · have : estar ≤ Real.exp (lamSing A T x (i : ℕ)) := hestar_le i hgt
      exact ne_of_gt (lt_of_lt_of_le hce this)
    · push Not at hgt; exact ne_of_lt (lt_of_le_of_lt hgt hct)
  -- The gap below `c` realizes `slowProjector c = slowProjector (exp t)` (no eigenvalue in
  -- `(t, c]`, equivalently in `(t, log c]`).
  have hQeq : slowProjector A T c x = slowProjector A T (Real.exp t) x := by
    have hgap : ∀ j : Fin d,
        lamSing A T x (j : ℕ) ≤ t ∨ Real.log c < lamSing A T x (j : ℕ) := by
      intro j
      by_cases hgt : Real.exp t < Real.exp (lamSing A T x (j : ℕ))
      · right
        have hge : estar ≤ Real.exp (lamSing A T x (j : ℕ)) := hestar_le j hgt
        rw [Real.log_lt_iff_lt_exp hcpos]
        exact lt_of_lt_of_le hce hge
      · left
        push Not at hgt
        exact (Real.exp_le_exp).mp hgt
    have hgapeq := slowProjector_eq_of_gap (A := A) (T := T) (x := x)
      (t₁ := t) (t₂ := Real.log c) hspec (le_of_lt ((Real.lt_log_iff_exp_lt hcpos).mpr hct)) hgap
    rw [Real.exp_log hcpos] at hgapeq
    exact hgapeq.symm
  -- The band-projector limit `P = cfc (Ioi c) lambdaHat = 1 - slowProjector (exp t)`.
  have htend := hidentx c hcpos hcne
  set P : Matrix (Fin d) (Fin d) ℝ :=
    cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) (lambdaHat A T x) with hP
  have hPeq : P = (1 : Matrix (Fin d) (Fin d) ℝ) - slowProjector A T (Real.exp t) x := by
    rw [hP, ← one_sub_slowProjector, hQeq]
  -- `toEuclideanLin P v ≠ 0` (else `v ∈ range (slowProjector (exp t)) = vslow (exp t)`).
  have hPv : Matrix.toEuclideanLin P v ≠ 0 := by
    intro h0
    apply hvnot
    rw [vslow, mem_range_toEuclideanCLM_iff (slowProjector_mul_self A T (Real.exp t) x)]
    have hmapsub : Matrix.toEuclideanLin
          ((1 : Matrix (Fin d) (Fin d) ℝ) - slowProjector A T (Real.exp t) x)
        = Matrix.toEuclideanLin 1 - Matrix.toEuclideanLin (slowProjector A T (Real.exp t) x) :=
      map_sub _ _ _
    have hone : Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) v = v := by
      rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (𝕜 := ℝ)]; simp
    have hsplit : Matrix.toEuclideanLin P v
        = v - Matrix.toEuclideanLin (slowProjector A T (Real.exp t) x) v := by
      rw [hPeq, hmapsub, LinearMap.sub_apply, hone]
    rw [hsplit, sub_eq_zero] at h0
    exact h0.symm
  -- cobounded-below from FK boundedness.
  obtain ⟨hba, hbb⟩ := hbddx v hv0
  have hcob : IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) :=
    hba.isCoboundedUnder_ge
  -- The liminf lower bound: `log c ≤ liminf …`.
  have hkey := log_le_liminf_log_cocycle_apply A T hA hcpos htend hPv hcob
  -- But `liminf ≤ limsup = lambdaBar v ≤ t < log c`.
  have hlimsupbar : limsup (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop = lambdaBar A T x v :=
    limsup_log_norm_cocycle_eq_lambdaBar A T x v
  have hliminf_le_limsup : liminf (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop
      ≤ limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop :=
    Filter.liminf_le_limsup hba hbb
  have hlogc : t < Real.log c := (Real.lt_log_iff_exp_lt hcpos).mpr hct
  -- Chain: `log c ≤ liminf ≤ limsup = lambdaBar v ≤ t < log c`, contradiction.
  rw [hlimsupbar] at hliminf_le_limsup
  exact absurd (le_trans hkey (le_trans hliminf_le_limsup hbar)) (not_le.mpr hlogc)

end Oseledets
