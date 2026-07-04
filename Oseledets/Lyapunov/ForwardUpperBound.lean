/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Forward
import Oseledets.Lyapunov.ForwardAngle
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.GrowthFunction

/-!
# The Lyapunov spectral upper bound via a two-term band split

This file proves the spectral upper bound of the multiplicative ergodic theorem along Viana's
one-sided route: a **two-term split** of the cocycle quadratic form against the band projector
`Pₙ = bandProjector A T 𝟙_{(c,∞)} n x` at threshold `c = e^{λᵢ}` (the fast singular-block
projector of `qpow A T n x`).

* The **slow band** contributes `≤ c^{2n}‖w‖²`: the slow Gram eigenvalues are `≤ c^{2n}`, so
  the slow quadratic form is bounded by `c^{2n}‖w‖²` with no angle or tilt estimate. This is the
  restricted-operator-norm bound `‖A⁽ⁿ⁾|_{slow}‖ ≤ cⁿ`, realized directly through the continuous
  functional calculus on the positive-semidefinite `qpow` rather than through Kingman's theorem
  on a skew-product.
* The **fast band** contributes `≤ ‖A⁽ⁿ⁾‖²·‖Pₙ w‖²`, since every spectral value `t` of `qpow`
  satisfies `t^{2n} ≤ ‖A⁽ⁿ⁾‖²`.

Adding the two halves yields the master inequality
`‖A⁽ⁿ⁾ v‖² ≤ ‖A⁽ⁿ⁾‖²·‖Pₙ v‖² + c^{2n}·‖v‖²`, from which the spectral upper bound
`limsup (1/n) log‖A⁽ⁿ⁾ v‖ ≤ λᵢ` follows, conditional on the single angle input
`limsup (1/n) log(‖A⁽ⁿ⁾‖·‖Pₙ v‖) ≤ λᵢ`. Via the Furstenberg–Kesten top exponent
`(1/n)log‖A⁽ⁿ⁾‖ → λ₁`, that angle input is in turn equivalent to the tilt-decay
residual `limsup (1/n) log‖Pₙ v‖ ≤ λᵢ − λ₁`.

## Main results

* `Oseledets.inner_slow_band_le`: the slow-band quadratic form is `≤ c^{2n}‖w‖²`.
* `Oseledets.rpow_mem_spectrum_qpow_le`: every `qpow` spectral value `t` has
  `t^{2n} ≤ ‖A⁽ⁿ⁾‖²`.
* `Oseledets.inner_fast_band_le`: the fast-band quadratic form is
  `≤ ‖A⁽ⁿ⁾‖²·‖Pₙ w‖²`.
* `Oseledets.norm_sq_cocycle_apply_le_split`: the master inequality
  `‖A⁽ⁿ⁾ v‖² ≤ ‖A⁽ⁿ⁾‖²·‖Pₙ v‖² + c^{2n}·‖v‖²`.
* `Oseledets.limsup_log_cocycle_apply_le_of_angle`: the spectral upper bound
  `limsup (1/n) log‖A⁽ⁿ⁾ v‖ ≤ λᵢ`, conditional on the angle input.

## Implementation notes

A naive per-overlap recursion is circular: slow growth `g ≤ λᵢ` and small overlaps
`oⱼ ≤ g − λⱼ` (Cauchy–Schwarz) compose vacuously to `g ≤ g`. The two-term split sidesteps
the per-overlap recursion entirely: the slow half (`inner_slow_band_le`) gives `λᵢ`
*unconditionally* — it never references an overlap, only the spectral ceiling `c` of the slow
Gram block. The growth is thereby reduced to a single scalar quantity, the fast-band projection
`‖Pₙ v‖`, whose decay (`htilt`) is a genuine slow–fast angle estimate about the projector
sequence, independent of `g`; there is no feedback loop.

The one non-elementary input is `htilt`: `limsup (1/n) log‖Pₙ v‖ ≤ λᵢ − λ₁` for the
limit-slow vector `v` (`P v = 0`, `P = limₙ Pₙ`), the slow–fast angle decay at the full
multi-gap rate `λᵢ − λ₁`. It is kept as an explicit hypothesis in this file. The summability
estimate `summable_norm_bandProjector_succ_sub` (in `Oseledets.Lyapunov.OseledetsLimit`)
supplies `‖Pₙ₊₁ − Pₙ‖` summability at the nearest-gap rate `λᵢ − λ_{i−1}`; upgrading it to the
full rate is a multi-gap telescope carried out elsewhere in the library.

## References

* Marcelo Viana, *Lectures on Lyapunov exponents*, Cambridge Studies in Advanced
  Mathematics 145, Cambridge University Press, 2014
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## The slow-band growth bound (the clean half of the split)

`A⁽ⁿ⁾` restricted to the SLOW Gram-eigenspace (singular values `≤ c`) has operator norm `≤ c`.
Concretely, for the complementary band projector `Q_n = I - P_n` (projection onto eigenvalues
`≤ c` of `qpow`), `‖A⁽ⁿ⁾ Q_n v‖² ≤ c^{2n} ‖Q_n v‖² ≤ c^{2n} ‖v‖²`.  This needs NO
angle/tilt estimate. -/

/-- **Slow-band upper bound.** For `c ≥ 0`, the SLOW quadratic form of the cocycle (the part of
`‖A⁽ⁿ⁾ w‖²` supported on `qpow`-eigenvalues `≤ c`) is `≤ c^{2n} ‖w‖²`.  Formally: applying the
gram quadratic form to the complementary band vector `w` with `P_n w = 0`. We package it via the
function `g(t) = t^{2n}·(1 - χ(t))` whose `cfc` is the slow part of `gram`. -/
theorem inner_slow_band_le [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {n : ℕ} (hn : 1 ≤ n) (x : X) {c : ℝ} (hc : 0 ≤ c) (w : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanLin
        (cfc (fun t : ℝ => t ^ (2 * (n : ℝ)) * (1 - Set.indicator (Set.Ioi c) 1 t))
          (qpow A T n x)) w, w⟫_ℝ
      ≤ c ^ (2 * (n : ℝ)) * ‖w‖ ^ 2 := by
  classical
  set Q := qpow A T n x with hQ
  set χ : ℝ → ℝ := Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) with hχ
  set g : ℝ → ℝ := fun t : ℝ => t ^ (2 * (n : ℝ)) * (1 - χ t) with hg
  have hQsa : IsSelfAdjoint Q := qpow_isSelfAdjoint A T n x
  have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hspec : _root_.spectrum ℝ Q ⊆ {a : ℝ | 0 ≤ a} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp (qpow_posSemidef A T n x)).2
  -- on the spectrum `g t ≤ c^{2n}` (for slow `t ≤ c`, `g t = t^{2n} ≤ c^{2n}`;
  -- for fast `t > c`, `χ t = 1` so `g t = 0 ≤ c^{2n}`), and `g t ≥ 0`.
  have hgnn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ g t := by
    intro t ht
    have ht0 : 0 ≤ t := hspec ht
    by_cases hct : t ∈ Set.Ioi c
    · simp only [hg, hχ, Set.indicator_of_mem hct]; norm_num
    · have h0 : χ t = 0 := by rw [hχ, Set.indicator_of_notMem hct]
      simp only [hg, h0, sub_zero, mul_one]; exact Real.rpow_nonneg ht0 _
  have hgle : ∀ t ∈ _root_.spectrum ℝ Q, g t ≤ c ^ (2 * (n : ℝ)) := by
    intro t ht
    have ht0 : 0 ≤ t := hspec ht
    have hcpow : 0 ≤ c ^ (2 * (n : ℝ)) := Real.rpow_nonneg hc _
    by_cases hct : t ∈ Set.Ioi c
    · simp only [hg, hχ, Set.indicator_of_mem hct]; simpa using hcpow
    · have h0 : χ t = 0 := by rw [hχ, Set.indicator_of_notMem hct]
      have htc : t ≤ c := not_lt.mp (by simpa [Set.mem_Ioi] using hct)
      simp only [hg, h0, sub_zero, mul_one]
      exact Real.rpow_le_rpow ht0 htc h2n
  -- `c^{2n} - g ≥ 0` on the spectrum, so `cfc (c^{2n} - g) Q` is PosSemidef, giving the bound.
  set h : ℝ → ℝ := fun t => c ^ (2 * (n : ℝ)) - g t with hh
  have hcontg : ContinuousOn g (_root_.spectrum ℝ Q) :=
    ((Real.continuous_rpow_const h2n).continuousOn).mul
      (continuousOn_const.sub
        ((Matrix.finite_real_spectrum (A := Q)).continuousOn _))
  have hconth : ContinuousOn h (_root_.spectrum ℝ Q) := continuousOn_const.sub hcontg
  have hhnn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ h t := by
    intro t ht; rw [hh]; linarith [hgle t ht]
  have hhPSD : (cfc h Q).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate h Q), ?_⟩
    rw [cfc_map_spectrum h Q hQsa hconth]
    rintro _ ⟨t, ht, rfl⟩; exact hhnn t ht
  -- `cfc h Q = algebraMap (c^{2n}) - cfc g Q`
  have hsplit : cfc h Q
      = (algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ)) (c ^ (2 * (n : ℝ))) - cfc g Q := by
    rw [hh, cfc_sub _ g Q continuousOn_const hcontg, cfc_const _ Q hQsa]
  -- quadratic form of `cfc h Q` is `≥ 0`, expand.
  have hdot : ⟪Matrix.toEuclideanLin (cfc h Q) w, w⟫_ℝ
      = star (w : Fin d → ℝ) ⬝ᵥ ((cfc h Q) *ᵥ (w : Fin d → ℝ)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]; simp only [star_trivial]
  have hPSDnn : (0 : ℝ) ≤ ⟪Matrix.toEuclideanLin (cfc h Q) w, w⟫_ℝ := by
    rw [hdot]; exact hhPSD.dotProduct_mulVec_nonneg _
  -- `algebraMap (c^{2n}) = c^{2n} • 1` as a matrix, and its quadratic form is `c^{2n} ‖w‖²`.
  have halg : (algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ)) (c ^ (2 * (n : ℝ)))
      = (c ^ (2 * (n : ℝ))) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [Algebra.algebraMap_eq_smul_one]
  have hexp : ⟪Matrix.toEuclideanLin (cfc h Q) w, w⟫_ℝ
      = c ^ (2 * (n : ℝ)) * ‖w‖ ^ 2 - ⟪Matrix.toEuclideanLin (cfc g Q) w, w⟫_ℝ := by
    rw [hsplit, halg, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_left,
      real_inner_smul_left]
    congr 2
    rw [Matrix.toLpLin_apply]
    simp only [Matrix.one_mulVec, real_inner_self_eq_norm_sq]
  rw [hexp] at hPSDnn
  -- goal is `⟪cfc g Q w, w⟫ ≤ c^{2n} ‖w‖²`
  change ⟪Matrix.toEuclideanLin (cfc g Q) w, w⟫_ℝ ≤ c ^ (2 * (n : ℝ)) * ‖w‖ ^ 2
  linarith

/-- **Spectral bound on `qpow`.** Every `t` in the spectrum of `qpow A T n x` satisfies
`t ^ (2n) ≤ ‖A⁽ⁿ⁾‖²`.  (`t^{2n}` is a gram eigenvalue, gram = `cocycleᵀ·cocycle`, and a
PSD eigenvalue is `≤ ‖gram‖ ≤ ‖cocycleᵀ‖·‖cocycle‖ = ‖cocycle‖²`.) -/
theorem rpow_mem_spectrum_qpow_le [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {n : ℕ} (hn : 1 ≤ n) (x : X) {t : ℝ} (ht : t ∈ _root_.spectrum ℝ (qpow A T n x)) :
    t ^ (2 * (n : ℝ)) ≤ ‖cocycle A T n x‖ ^ 2 := by
  classical
  set Q := qpow A T n x with hQ
  have hQsa : IsSelfAdjoint Q := qpow_isSelfAdjoint A T n x
  have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hcont : ContinuousOn (fun t : ℝ => t ^ (2 * (n : ℝ))) (_root_.spectrum ℝ Q) :=
    (Real.continuous_rpow_const h2n).continuousOn
  -- `t^{2n} ∈ spectrum(gram)`.
  have hmem : t ^ (2 * (n : ℝ)) ∈ _root_.spectrum ℝ (gram A T n x) := by
    have hmap := cfc_map_spectrum (fun t : ℝ => t ^ (2 * (n : ℝ))) Q hQsa hcont
    rw [gram_eq_cfc_qpow A T hn x] at hmap
    rw [hmap]
    exact ⟨t, ht, rfl⟩
  -- spectrum value `t^{2n} ≤ ‖gram‖` (it is `≥ 0`, so `‖t^{2n}‖ = t^{2n}`).
  have ht2n_nn : 0 ≤ t ^ (2 * (n : ℝ)) := by
    have hQpsd : Q.PosSemidef := qpow_posSemidef A T n x
    have hspec : _root_.spectrum ℝ Q ⊆ {a : ℝ | 0 ≤ a} :=
      (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hQpsd).2
    exact Real.rpow_nonneg (hspec ht) _
  have hμle : t ^ (2 * (n : ℝ)) ≤ ‖gram A T n x‖ := by
    have hb := spectrum.norm_le_norm_of_mem (𝕜 := ℝ) hmem
    rwa [Real.norm_eq_abs, abs_of_nonneg ht2n_nn] at hb
  -- `‖gram‖ = ‖cocycleᵀ * cocycle‖ = ‖cocycleᴴ * cocycle‖ = ‖cocycle‖²`.
  have hgramnorm : ‖gram A T n x‖ = ‖cocycle A T n x‖ ^ 2 := by
    rw [gram, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose_mul_self]
    ring
  rw [hgramnorm] at hμle
  linarith

/-! ## The fast-band bound (the angle term) -/

/-- **Fast-band upper bound.** The fast quadratic form of the cocycle (part of `‖A⁽ⁿ⁾ w‖²`
supported on `qpow`-eigenvalues `> c`) is `≤ ‖A⁽ⁿ⁾‖² · ‖P_n w‖²`, where
`P_n w = bandProjector` of the fast band applied to `w`.  The eigenvalues `t^{2n}` on the fast
band are `≤ ‖A⁽ⁿ⁾‖²` (`rpow_mem_spectrum_qpow_le`), so `cfc(t^{2n}χ) ⪯ ‖A⁽ⁿ⁾‖²·cfc(χ)` (PSD),
and `⟪cfc(χ)w,w⟫ = ‖P_n w‖²` (self-adjoint idempotent). -/
theorem inner_fast_band_le [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {n : ℕ} (hn : 1 ≤ n) (x : X) (c : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanLin
        (cfc (fun t : ℝ => t ^ (2 * (n : ℝ)) * Set.indicator (Set.Ioi c) 1 t)
          (qpow A T n x)) w, w⟫_ℝ
      ≤ ‖cocycle A T n x‖ ^ 2
        * ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) w‖ ^ 2
        := by
  classical
  set Q := qpow A T n x with hQ
  set χ : ℝ → ℝ := Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) with hχ
  set B := ‖cocycle A T n x‖ ^ 2 with hB
  set g : ℝ → ℝ := fun t : ℝ => t ^ (2 * (n : ℝ)) * χ t with hg
  have hQsa : IsSelfAdjoint Q := qpow_isSelfAdjoint A T n x
  have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hcontχ : ContinuousOn χ (_root_.spectrum ℝ Q) :=
    (Matrix.finite_real_spectrum (A := Q)).continuousOn _
  have hcontg : ContinuousOn g (_root_.spectrum ℝ Q) :=
    ((Real.continuous_rpow_const h2n).continuousOn).mul hcontχ
  -- `χ ≥ 0` and `B·χ - g ≥ 0` on the spectrum.
  have hχnn : ∀ t, 0 ≤ χ t := by
    intro t; rw [hχ]; by_cases ht : t ∈ Set.Ioi c
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  -- `‖P_n w‖² = ⟪cfc χ Q w, w⟫`.
  have hPsq : ‖Matrix.toEuclideanLin (cfc χ Q) w‖ ^ 2
      = ⟪Matrix.toEuclideanLin (cfc χ Q) w, w⟫_ℝ := by
    have hidem : (_root_.spectrum ℝ Q).EqOn (fun t => χ t * χ t) χ := by
      intro t _; by_cases ht : t ∈ Set.Ioi c
      · simp [hχ, Set.indicator_of_mem ht]
      · simp [hχ, Set.indicator_of_notMem ht]
    have hPidem : cfc χ Q * cfc χ Q = cfc χ Q := by
      rw [← cfc_mul χ χ Q hcontχ hcontχ, cfc_congr hidem]
    have hPtr : (cfc χ Q)ᵀ = cfc χ Q := by
      have h := Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate χ Q)
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [norm_sq_toEuclideanLin_eq_inner_gram, hPtr, hPidem]
  -- PSD gap: `cfc (B·χ - g) Q ⪰ 0`.
  set k : ℝ → ℝ := fun t => B * χ t - g t with hk
  have hcontk : ContinuousOn k (_root_.spectrum ℝ Q) :=
    (continuousOn_const.mul hcontχ).sub hcontg
  have hknn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ k t := by
    intro t ht
    rw [hk, hg]
    have hb : t ^ (2 * (n : ℝ)) ≤ B := rpow_mem_spectrum_qpow_le A T hn x ht
    have : t ^ (2 * (n : ℝ)) * χ t ≤ B * χ t :=
      mul_le_mul_of_nonneg_right hb (hχnn t)
    linarith
  have hkPSD : (cfc k Q).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate k Q), ?_⟩
    rw [cfc_map_spectrum k Q hQsa hcontk]
    rintro _ ⟨t, ht, rfl⟩; exact hknn t ht
  -- `cfc k Q = B • cfc χ Q - cfc g Q`.
  have hsplit : cfc k Q = B • cfc χ Q - cfc g Q := by
    have hk' : cfc k Q = cfc (fun t => B * χ t) Q - cfc g Q :=
      cfc_sub (fun t => B * χ t) g Q (continuousOn_const.mul hcontχ) hcontg
    rw [hk', cfc_const_mul B χ Q hcontχ]
  have hdot : ⟪Matrix.toEuclideanLin (cfc k Q) w, w⟫_ℝ
      = star (w : Fin d → ℝ) ⬝ᵥ ((cfc k Q) *ᵥ (w : Fin d → ℝ)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]; simp only [star_trivial]
  have hPSDnn : (0 : ℝ) ≤ ⟪Matrix.toEuclideanLin (cfc k Q) w, w⟫_ℝ := by
    rw [hdot]; exact hkPSD.dotProduct_mulVec_nonneg _
  have hexp : ⟪Matrix.toEuclideanLin (cfc k Q) w, w⟫_ℝ
      = B * ⟪Matrix.toEuclideanLin (cfc χ Q) w, w⟫_ℝ
        - ⟪Matrix.toEuclideanLin (cfc g Q) w, w⟫_ℝ := by
    rw [hsplit, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_left,
      real_inner_smul_left]
  rw [hexp] at hPSDnn
  -- conclude
  change ⟪Matrix.toEuclideanLin (cfc g Q) w, w⟫_ℝ
    ≤ B * ‖Matrix.toEuclideanLin (cfc χ Q) w‖ ^ 2
  rw [hPsq]
  -- goal: ⟪cfc g Q w,w⟫ ≤ B * ⟪cfc χ Q w, w⟫  (bandProjector = cfc χ Q by def)
  have hbp : bandProjector A T (Set.indicator (Set.Ioi c) 1) n x = cfc χ Q := rfl
  linarith

/-! ## The master inequality: Viana's two-term split

`‖A⁽ⁿ⁾ v‖² ≤ ‖A⁽ⁿ⁾‖² · ‖P_n v‖² + c^{2n} · ‖v‖²`. The first term is the FAST (angle) part;
the second is the SLOW part (clean). -/

/-- **Master inequality (Viana's split).** For `c ≥ 0`:
`‖A⁽ⁿ⁾ v‖² ≤ ‖A⁽ⁿ⁾‖² · ‖P_n v‖² + c^{2n} · ‖v‖²`, where `P_n` is the fast band projector
(`bandProjector` of `(c,∞)`). -/
theorem norm_sq_cocycle_apply_le_split [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ)
    (T : X → X) {n : ℕ} (hn : 1 ≤ n) (x : X) {c : ℝ} (hc : 0 ≤ c)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2
      ≤ ‖cocycle A T n x‖ ^ 2
          * ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ ^ 2
        + c ^ (2 * (n : ℝ)) * ‖v‖ ^ 2 := by
  classical
  have hQsa : IsSelfAdjoint (qpow A T n x) := qpow_isSelfAdjoint A T n x
  have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  set χ : ℝ → ℝ := Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) with hχ
  have hcontχ : ContinuousOn χ (_root_.spectrum ℝ (qpow A T n x)) :=
    (Matrix.finite_real_spectrum (A := qpow A T n x)).continuousOn _
  have hcontpow : ContinuousOn (fun t : ℝ => t ^ (2 * (n : ℝ)))
      (_root_.spectrum ℝ (qpow A T n x)) :=
    (Real.continuous_rpow_const h2n).continuousOn
  set f1 : ℝ → ℝ := fun t : ℝ => t ^ (2 * (n : ℝ)) * χ t with hf1
  set f2 : ℝ → ℝ := fun t : ℝ => t ^ (2 * (n : ℝ)) * (1 - χ t) with hf2
  have hcf1 : ContinuousOn f1 (_root_.spectrum ℝ (qpow A T n x)) := hcontpow.mul hcontχ
  have hcf2 : ContinuousOn f2 (_root_.spectrum ℝ (qpow A T n x)) :=
    hcontpow.mul (continuousOn_const.sub hcontχ)
  -- `gram = cfc (t^{2n}) = cfc f1 + cfc f2`.
  have hdecomp : ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2
      = ⟪Matrix.toEuclideanLin (cfc f1 (qpow A T n x)) v, v⟫_ℝ
        + ⟪Matrix.toEuclideanLin (cfc f2 (qpow A T n x)) v, v⟫_ℝ := by
    rw [norm_sq_cocycle_apply_eq_inner_gram, ← gram_eq_cfc_qpow A T hn x]
    have hcfc : cfc (fun t : ℝ => t ^ (2 * (n : ℝ))) (qpow A T n x)
        = cfc f1 (qpow A T n x) + cfc f2 (qpow A T n x) := by
      rw [← cfc_add (a := qpow A T n x) f1 f2 hcf1 hcf2]
      refine cfc_congr ?_
      intro t _; simp only [hf1, hf2]; ring
    rw [hcfc, map_add, LinearMap.add_apply, inner_add_left]
  rw [hdecomp]
  -- the fast and slow band bounds (rewritten into `f1`/`f2`/`χ` form).
  have hfast : ⟪Matrix.toEuclideanLin (cfc f1 (qpow A T n x)) v, v⟫_ℝ
      ≤ ‖cocycle A T n x‖ ^ 2
        * ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ ^ 2
        := by
    have := inner_fast_band_le A T hn x c v
    simpa only [hf1, hχ] using this
  have hslow : ⟪Matrix.toEuclideanLin (cfc f2 (qpow A T n x)) v, v⟫_ℝ
      ≤ c ^ (2 * (n : ℝ)) * ‖v‖ ^ 2 := by
    have := inner_slow_band_le A T hn x hc v
    simpa only [hf2, hχ] using this
  linarith

/-! ## The assembly: master inequality + angle input ⟹ spectral upper bound

The slow term contributes `λᵢ` for free. The fast term `‖A⁽ⁿ⁾‖·‖P_n v‖` is the irreducible
ANGLE/tilt input: its normalized-log `limsup` must be `≤ λᵢ`. Given that single hypothesis,
the spectral upper bound `limsup (1/n)log‖A⁽ⁿ⁾v‖ ≤ λᵢ` follows. -/

/-- **Spectral upper bound (assembled, conditional on the angle input).** For `v ≠ 0` and
threshold `c = exp λᵢ`, if the fast term satisfies the angle bound
`limsup (1/n) log (‖A⁽ⁿ⁾‖ · ‖P_n v‖) ≤ λᵢ`, then
`limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ`.

This is the two-term split: the slow band gives `λᵢ` unconditionally
(`norm_sq_cocycle_apply_le_split`, the `c^{2n}‖v‖²` term); the fast band is controlled by the
angle hypothesis `hangle`. The only genuinely non-elementary input is `hangle` (the slow–fast
tempering/angle decay of `‖P_n v‖`). -/
theorem limsup_log_cocycle_apply_le_of_angle [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ)
    (T : X → X) (x : X) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) {lamI : ℝ}
    (hangle : limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log (‖cocycle A T n x‖
          * ‖Matrix.toEuclideanLin (bandProjector A T
              (Set.indicator (Set.Ioi (Real.exp lamI)) 1) n x) v‖)) atTop ≤ lamI)
    (hanglebdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log (‖cocycle A T n x‖
          * ‖Matrix.toEuclideanLin (bandProjector A T
              (Set.indicator (Set.Ioi (Real.exp lamI)) 1) n x) v‖)))
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lamI := by
  classical
  set c := Real.exp lamI with hc
  have hcpos : 0 < c := Real.exp_pos _
  set P : ℕ → Matrix (Fin d) (Fin d) ℝ := fun n =>
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x with hP
  set fast : ℕ → ℝ := fun n => ‖cocycle A T n x‖ ^ 2
      * ‖Matrix.toEuclideanLin (P n) v‖ ^ 2 with hfast
  set slow : ℕ → ℝ := fun n => c ^ (2 * (n : ℝ)) * ‖v‖ ^ 2 with hslow
  set t : Fin 2 → ℕ → ℝ := fun m => if m = 0 then fast else slow with ht
  -- the master inequality: `‖A⁽ⁿ⁾v‖² ≤ fast n + slow n`.
  have hmaster : ∀ n : ℕ, 1 ≤ n →
      ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2 ≤ fast n + slow n := by
    intro n hn
    exact norm_sq_cocycle_apply_le_split A T hn x (le_of_lt hcpos) v
  -- envelope for `fast`: from `hangle`, eventually `‖cocycle‖·‖P v‖ ≤ exp(n(lamI+δ))`,
  -- square it.
  have hfast_env :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, fast n ≤ Real.exp ((n : ℝ) * (2 * lamI + ε)) := by
    intro ε hε
    have hgg := eventually_le_exp_of_limsup_le
      (a := fun n : ℕ => ‖cocycle A T n x‖ * ‖Matrix.toEuclideanLin (P n) v‖)
      (fun n => by positivity) hanglebdd hangle (ε/2) (by linarith)
    filter_upwards [hgg] with n hn
    have hfe : fast n = (‖cocycle A T n x‖ * ‖Matrix.toEuclideanLin (P n) v‖) ^ 2 := by
      rw [hfast]; ring
    rw [hfe]
    calc (‖cocycle A T n x‖ * ‖Matrix.toEuclideanLin (P n) v‖) ^ 2
        ≤ (Real.exp ((n : ℝ) * (lamI + ε/2))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hn 2
      _ = Real.exp ((n : ℝ) * (2 * lamI + ε)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- envelope for `slow`: `c^{2n}‖v‖² = exp(2n·lamI)·‖v‖²`, so `(1/n)log → 2lamI`.
  have hslow_env :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, slow n ≤ Real.exp ((n : ℝ) * (2 * lamI + ε)) := by
    intro ε hε
    -- `(1/n)log slow → 2lamI`; use `eventually_le_exp_of_limsup_le`.
    have hslow_pos : ∀ n, 0 ≤ slow n := fun n => by rw [hslow]; positivity
    have hslim :
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (slow n)) atTop (𝓝 (2 * lamI)) := by
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hlogeq : ∀ n : ℕ, 1 ≤ n → (n : ℝ)⁻¹ * Real.log (slow n)
          = 2 * lamI + (n : ℝ)⁻¹ * Real.log (‖v‖ ^ 2) := by
        intro n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        rw [hslow]
        rw [Real.log_mul (by positivity) (by positivity)]
        rw [hc, Real.log_rpow (Real.exp_pos _), Real.log_exp]
        field_simp
      have hcorr :
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (‖v‖ ^ 2)) atTop (𝓝 0) := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.mul_const
          (Real.log (‖v‖ ^ 2))
        simpa using this
      have : Tendsto (fun n : ℕ => 2 * lamI + (n : ℝ)⁻¹ * Real.log (‖v‖ ^ 2)) atTop
          (𝓝 (2 * lamI)) := by simpa using (tendsto_const_nhds.add hcorr)
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (hlogeq n hn).symm
    exact eventually_le_exp_of_limsup_le hslow_pos hslim.isBoundedUnder_le hslim.limsup_eq.le ε hε
  -- Direct: `‖A⁽ⁿ⁾v‖² ≤ 2·exp(n(2lamI+ε))` eventually, so
  -- `(1/n)log‖A⁽ⁿ⁾v‖ ≤ lamI+ε+(1/n)log√2`.
  set g : ℕ → ℝ :=
    fun n => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ with hg
  have hcorr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (2 : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.mul_const (Real.log 2)
    simpa using this
  have hgkey :
      ∀ ε > 0, ∀ᶠ n : ℕ in atTop, g n ≤ lamI + ε + (n : ℝ)⁻¹ * Real.log 2 := by
    intro ε hε
    filter_upwards [hfast_env (ε) hε, hslow_env (ε) hε, hpos, eventually_ge_atTop 1]
      with n hfe hse hpn hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hbound : ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2
        ≤ 2 * Real.exp ((n : ℝ) * (2 * lamI + ε)) := by
      have hm := hmaster n hn1
      have : fast n + slow n ≤ 2 * Real.exp ((n : ℝ) * (2 * lamI + ε)) := by linarith
      linarith
    -- take log: `2 log‖A⁽ⁿ⁾v‖ = log(‖..‖²) ≤ log 2 + n(2lamI+ε)`.
    have hlog2 : 2 * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
        ≤ Real.log 2 + (n : ℝ) * (2 * lamI + ε) := by
      have hl : Real.log (‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2)
          ≤ Real.log (2 * Real.exp ((n : ℝ) * (2 * lamI + ε))) :=
        Real.log_le_log (by positivity) hbound
      rw [Real.log_pow, Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hl
      push_cast at hl ⊢; linarith
    -- divide by `n`.
    have : g n ≤ (n : ℝ)⁻¹ * (2⁻¹ * (Real.log 2 + (n : ℝ) * (2 * lamI + ε))) := by
      rw [hg]
      have h2 : Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
          ≤ 2⁻¹ * (Real.log 2 + (n : ℝ) * (2 * lamI + ε)) := by linarith
      exact mul_le_mul_of_nonneg_left h2 hninv
    calc g n ≤ (n : ℝ)⁻¹ * (2⁻¹ * (Real.log 2 + (n : ℝ) * (2 * lamI + ε))) := this
      _ = 2⁻¹ * (lamI * 2 + ε) + (n : ℝ)⁻¹ * (2⁻¹ * Real.log 2) := by
          field_simp; ring
      _ ≤ lamI + ε + (n : ℝ)⁻¹ * Real.log 2 := by
          have : (0:ℝ) ≤ (n : ℝ)⁻¹ * (2⁻¹ * Real.log 2) := by positivity
          nlinarith [this, hninv]
  -- conclude `limsup g ≤ lamI`.
  have hgbdd : IsBoundedUnder (· ≤ ·) atTop g := by
    obtain ⟨M, hM⟩ := (eventually_atTop.mp ((hgkey 1 one_pos).and
      (hcorr.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num)))))
    refine ⟨lamI + 1 + 1, ?_⟩
    rw [eventually_map, eventually_atTop]
    refine ⟨M, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hM n hn
    have h2' : (n : ℝ)⁻¹ * Real.log 2 < 1 := by simpa using h2
    linarith
  rw [hg] at hcobdd
  rw [limsup_le_iff' hcobdd hgbdd]
  intro y hy
  set ε := y - lamI with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  filter_upwards [hgkey (ε/2) (by linarith),
    hcorr.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 from by linarith))] with n h1 h2
  have h2' : (n : ℝ)⁻¹ * Real.log 2 < ε/2 := by simpa using h2
  have : g n ≤ y := by
    calc g n ≤ lamI + ε/2 + (n : ℝ)⁻¹ * Real.log 2 := h1
      _ ≤ lamI + ε/2 + ε/2 := by linarith
      _ = y := by rw [hεdef]; ring
  exact this

end Oseledets
