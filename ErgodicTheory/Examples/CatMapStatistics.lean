/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapDecay
import ErgodicTheory.Examples.CatMapGreenKubo
import ErgodicTheory.Examples.CatMapSuspensionDecay
import ErgodicTheory.Continuous.ReturnTimeExponent

/-!
# Statistical laws for Arnold's cat map (issue #62)

This module assembles the quantitative-statistics package for the cat map
`catTorus : 𝕋² → 𝕋²` on the Fourier-decay class `𝒞_s = FourierDecay s` (`s > 2`), by composing the
five sibling modules of the campaign into a small number of self-contained headline theorems.

## Main results (namespace `ErgodicTheory.CatMapToral`)

* `catAutoCorr_decay` — **exponential decay of the autocovariance**.  For `f : C(𝕋², ℝ)` whose
  complexification lies in `FourierDecay s`, `|ρ(k)| = |cov[f, f∘Tᵏ]| ≤ C·θᵏ` with explicit rate
  `θ = λ^(-(s-2)/4) < 1`.  This is the *bridge* lemma: it identifies the probabilistic
  autocovariance `catAutoCorr` with the centred correlation bounded in `catCorr_decay_real`.
* `catGreenKubo_fourierDecay` — **Green–Kubo**: `Var(Sₙ)/n → σ²` for the Fourier-decay class.
* `catVariance_linear_fourierDecay` — the **linear variance bound** `Var(Sₙ) ≤ B·n`.
* `catConcentration_fourierDecay` — the **finite-sample Chebyshev concentration** law with explicit
  `1/(n·ε²)` rate (the tier-3 headline).
* `catSuspensionDecay_fourierDecay` — **suspension-flow transport** (tier-4 headline): correlation
  decay `θ^⌊t⌋` of fibre-product observables on the constant-roof cat suspension, with the base
  decay discharged from the Fourier-decay estimate.

## Scope notes (honest deferrals)

* A full **central limit theorem** is *not* proved: Mathlib currently has no martingale/Gordin CLT,
  so only the second-moment laws (Green–Kubo variance and Chebyshev concentration) are available at
  this rate.
* **Entropy-from-orbit estimation** is *not* covered: that would need a Shannon–McMillan–Breiman
  theorem *with rates*, which is out of scope here.
* The suspension-flow decay requires **base-centred** observables (`∫g = 0`): the fibre-rotation
  obstruction of the constant roof precludes an uncentred statement (see `CatMapSuspensionDecay`).
* **Witness quality.** Every observable given a *compile-time* `FourierDecay s` certificate in this
  file (the `catReCharObs` family) is a trigonometric polynomial, whose cat-map autocorrelations
  vanish *exactly* for large `k` (the dual index orbit escapes any finite frequency support). The
  geometric rate `θᵏ` is proved for the full class `FourierDecay s` — which does contain
  infinite-frequency members with genuinely `θᵏ`-tight decay — but is not *witnessed as binding* by
  these finitely-supported certificates.
-/

open MeasureTheory ProbabilityTheory Filter UnitAddTorus
open scoped Topology

noncomputable section

/-- The circle carries its Haar probability measure, so `volume` on `𝕋² = UnitAddTorus (Fin 2)` is
the product Haar probability measure used by the Fourier API.  Local instances do not cross files,
so the trio is repeated here with names unique to this module. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catStatistics :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catStatistics :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catStatistics :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## Boundedness and measurability bookkeeping for continuous observables -/

/-- A continuous observable on the compact torus is bounded by its sup-norm. -/
theorem abs_le_norm (f : C(T2, ℝ)) (x : T2) : |f x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x

/-! ## The autocovariance bridge -/

/-- **Bridge identity.**  The probabilistic autocovariance `cov[f, f∘Tᵏ]` equals the
variance-centred correlation `∫ f·(f∘Tᵏ) − (∫f)²`.  Measure preservation (`integral_comp_iterate`)
gives `∫ f∘Tᵏ = ∫ f`, collapsing the two mean terms to `(∫f)²`. -/
theorem catAutoCorr_eq (f : C(T2, ℝ)) (k : ℕ) :
    catAutoCorr (⇑f) k
      = (∫ t : T2, f t * f (catTorus^[k] t)) - (∫ t : T2, f t) ^ 2 := by
  have hfm : Measurable (⇑f) := f.continuous.measurable
  have hfb : ∀ x, |f x| ≤ ‖f‖ := abs_le_norm f
  have hL2g : MemLp (fun x => f (catTorus^[k] x)) 2 volume :=
    catMemLp_comp (⇑f) hfm hfb k
  have hL2f : MemLp (⇑f) 2 volume := by
    have h0 := catMemLp_comp (⇑f) hfm hfb 0
    simpa using h0
  unfold catAutoCorr
  rw [ProbabilityTheory.covariance_eq_sub hL2f hL2g]
  have hmean : (volume : Measure T2)[fun x => f (catTorus^[k] x)]
      = (volume : Measure T2)[⇑f] := integral_comp_iterate (⇑f) hfm k
  rw [hmean, sq]
  have hprod : (volume : Measure T2)[⇑f * fun x => f (catTorus^[k] x)]
      = ∫ t : T2, f t * f (catTorus^[k] t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
  rw [hprod]

/-- **Exponential decay of the autocovariance.**  For `f : C(𝕋², ℝ)` whose complexification lies in
`FourierDecay s` (`s > 2`), the autocovariance `ρ(k) = cov[f, f∘Tᵏ]` decays geometrically with the
explicit rate `θ = λ^(-(s-2)/4) < 1`.  This is the probabilistic input to the Green–Kubo and
concentration laws below. -/
theorem catAutoCorr_decay {s : ℝ} (hs : 2 < s) (f : C(T2, ℝ))
    (hf : FourierDecay s (fun t => (f t : ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |catAutoCorr (⇑f) k| ≤ C * (lam ^ (-(s - 2) / 4 : ℝ)) ^ k := by
  obtain ⟨C, hC, hbound⟩ := catCorr_decay_real hs f hf
  refine ⟨C, hC, fun k => ?_⟩
  rw [catAutoCorr_eq f k]
  exact hbound k

/-! ## Green–Kubo variance asymptotics -/

/-- **Green–Kubo for the Fourier-decay class.**  For `f : C(𝕋², ℝ)` with `FourierDecay s`
complexification (`s > 2`), the rescaled Birkhoff variance converges to the Green–Kubo variance
`σ² = ρ(0) + 2∑ₖ ρ(k+1)`. -/
theorem catGreenKubo_fourierDecay {s : ℝ} (hs : 2 < s) (f : C(T2, ℝ))
    (hf : FourierDecay s (fun t => (f t : ℂ))) :
    Tendsto (fun n => variance (birkhoffSum catTorus (⇑f) n) volume / (n : ℝ)) atTop
      (𝓝 (catSigmaSq (⇑f))) := by
  have hfm : Measurable (⇑f) := f.continuous.measurable
  have hfb : ∀ x, |f x| ≤ ‖f‖ := abs_le_norm f
  obtain ⟨C, _, hdecay⟩ := catAutoCorr_decay hs f hf
  have hlam0 : (0 : ℝ) ≤ lam := by linarith [one_lt_lam]
  have hθ0 : (0 : ℝ) ≤ lam ^ (-(s - 2) / 4 : ℝ) := Real.rpow_nonneg hlam0 _
  exact catGreenKubo_tendsto (⇑f) hfm hfb hθ0 (lam_rpow_lt_one hs) hdecay

/-- **Linear variance bound for the Fourier-decay class.**  `Var(Sₙ) ≤ B·n` with an explicit `B`
built from the decay constant. -/
theorem catVariance_linear_fourierDecay {s : ℝ} (hs : 2 < s) (f : C(T2, ℝ))
    (hf : FourierDecay s (fun t => (f t : ℂ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      variance (birkhoffSum catTorus (⇑f) n) volume ≤ B * (n : ℝ) := by
  have hfm : Measurable (⇑f) := f.continuous.measurable
  have hfb : ∀ x, |f x| ≤ ‖f‖ := abs_le_norm f
  obtain ⟨C, hC, hdecay⟩ := catAutoCorr_decay hs f hf
  have hlam0 : (0 : ℝ) ≤ lam := by linarith [one_lt_lam]
  have hθ0 : (0 : ℝ) ≤ lam ^ (-(s - 2) / 4 : ℝ) := Real.rpow_nonneg hlam0 _
  have hθ1 : lam ^ (-(s - 2) / 4 : ℝ) < 1 := lam_rpow_lt_one hs
  refine ⟨C * (2 / (1 - lam ^ (-(s - 2) / 4 : ℝ)) + 1), ?_,
    fun n => catVariance_le (⇑f) hfm hfb hθ0 hθ1 hdecay n⟩
  have h1θ : (0 : ℝ) < 1 - lam ^ (-(s - 2) / 4 : ℝ) := by linarith
  exact mul_nonneg hC (by positivity)

/-! ## Finite-sample concentration -/

/-- **Chebyshev concentration for the Fourier-decay class** (the tier-3 headline).  With an explicit
constant `B`, for every sample size `n ≥ 1` and threshold `ε > 0` the empirical average `Sₙ/n`
deviates from the space mean `∫f` by at least `ε` with probability at most `B/(n·ε²)`. -/
theorem catConcentration_fourierDecay {s : ℝ} (hs : 2 < s) (f : C(T2, ℝ))
    (hf : FourierDecay s (fun t => (f t : ℂ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (ε : ℝ), 1 ≤ n → 0 < ε →
      (volume : Measure T2).real
          {x : T2 | ε ≤ |birkhoffSum catTorus (⇑f) n x / (n : ℝ) - ∫ t : T2, f t|}
        ≤ B / ((n : ℝ) * ε ^ 2) := by
  have hfm : Measurable (⇑f) := f.continuous.measurable
  have hfb : ∀ x, |f x| ≤ ‖f‖ := abs_le_norm f
  obtain ⟨B, hB, hVar⟩ := catVariance_linear_fourierDecay hs f hf
  refine ⟨B, hB, fun n ε hn hε => ?_⟩
  exact catChebyshev_real (⇑f) hfm hfb hn (hVar n) hε

/-! ## Suspension-flow transport -/

/-- **Correlation decay for the cat-map suspension flow** (the tier-4 headline).  For base
observables `f, g : C(𝕋², ℝ)` with `FourierDecay s` complexifications (`s > 2`) and `g` centred
(`∫g = 0`), and bounded measurable fibre profiles `ψ, χ`, the centred flow correlation of the
fibre-product observables on the constant-roof cat suspension decays as `θ^⌊t⌋` with
`θ = λ^(-(s-2)/4)`.  The base-decay hypothesis of `catSuspension_fibreProduct_decay` is discharged
from `catCorr_decay_real₂` via the `baseIter ↔ catTorus^[k]` bridge. -/
theorem catSuspensionDecay_fourierDecay {s : ℝ} (hs : 2 < s) (f g : C(T2, ℝ))
    (hf : FourierDecay s (fun t => (f t : ℂ)))
    (hg : FourierDecay s (fun t => (g t : ℂ)))
    (hg0 : (∫ x, g x ∂(volume : Measure T2)) = 0)
    (ψ χ : ℝ → ℝ) (hψ : Measurable ψ) (hχ : Measurable χ)
    {Mψ Mχ : ℝ} (hMψ : ∀ u, |ψ u| ≤ Mψ) (hMχ : ∀ u, |χ u| ≤ Mχ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧
      |∫ q, fibreProduct catTorusEquiv measurable_catRoof (⇑f) ψ rfl q
          * fibreProduct catTorusEquiv measurable_catRoof (⇑g) χ rfl
              (suspensionFlowMap catTorusEquiv measurable_catRoof t q)
          ∂(suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2))|
        ≤ Mψ * Mχ * C * (lam ^ (-(s - 2) / 4 : ℝ)) ^ (⌊t⌋.toNat) := by
  obtain ⟨C, hC, hbound⟩ := catCorr_decay_real₂ hs f g hf hg
  have hlam0 : (0 : ℝ) ≤ lam := by linarith [one_lt_lam]
  have hθ0 : (0 : ℝ) ≤ lam ^ (-(s - 2) / 4 : ℝ) := Real.rpow_nonneg hlam0 _
  have hθ1 : lam ^ (-(s - 2) / 4 : ℝ) ≤ 1 := (lam_rpow_lt_one hs).le
  have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
  refine ⟨C, hC, ?_⟩
  refine catSuspension_fibreProduct_decay (⇑f) (⇑g) ψ χ f.continuous.measurable
    g.continuous.measurable hψ hχ (abs_le_norm f) (abs_le_norm g) hMψ hMχ hθ0 hθ1 hg0
    (fun k => ?_) t ht
  have key : (∫ x, (⇑f) x
        * (⇑g) (baseIter catTorusEquiv measurable_catRoof (k : ℤ) x) ∂(volume : Measure T2))
      = ∫ x, f x * g (catTorus^[k] x) ∂(volume : Measure T2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [baseIter_natCast, hcoe]
  rw [key]
  exact hbound k

/-! ## A concrete non-vacuity certificate -/

/-- The real character observable `x ↦ Re(mFourier m x) = cos(2π m·x)`, a genuine non-constant
element of the Fourier-decay class. -/
def catReCharObs (m : Fin 2 → ℤ) : C(T2, ℝ) :=
  ⟨fun t => (mFourier m t).re, Complex.continuous_re.comp (mFourier m).continuous⟩

/-- The complexification of `catReCharObs m` is the trigonometric polynomial
`½·mFourier m + ½·mFourier (-m)`, hence lies in every Fourier-decay class. -/
theorem fourierDecay_catReCharObs (m : Fin 2 → ℤ) :
    FourierDecay 3 (fun t => (catReCharObs m t : ℂ)) := by
  have hEq : (fun t => ((catReCharObs m t : ℝ) : ℂ))
      = ((2⁻¹ : ℂ) • (mFourier m : T2 → ℂ)) + ((2⁻¹ : ℂ) • (mFourier (-m) : T2 → ℂ)) := by
    funext t
    change ((mFourier m t).re : ℂ) = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mFourier_neg]
    have hc := Complex.add_conj (mFourier m t)
    rw [← mul_add, hc]; push_cast; ring
  rw [hEq]
  exact FourierDecay.add ((fourierDecay_mFourier 3 m).smul 2⁻¹)
    ((fourierDecay_mFourier 3 (-m)).smul 2⁻¹) ((integrable_mFourier m).smul 2⁻¹)
    ((integrable_mFourier (-m)).smul 2⁻¹)

/-- **Zero mean of a nontrivial real character.**  For `m ≠ 0` the observable `catReCharObs m`
integrates to `0`: its complexification `½·mFourier m + ½·mFourier (-m)` is supported on the
frequencies `{m, -m} ∌ 0`, and every character integrates to `0` off the trivial index
(`integral_mFourier`).  This is the space-mean that the concentration law centres against. -/
theorem integral_catReCharObs (m : Fin 2 → ℤ) (hm : m ≠ 0) :
    ∫ t : T2, catReCharObs m t = 0 := by
  have hint : ∫ t : T2, ((catReCharObs m t : ℝ) : ℂ) = 0 := by
    have hpt : ∀ t : T2, ((catReCharObs m t : ℝ) : ℂ)
        = (2⁻¹ : ℂ) * mFourier m t + (2⁻¹ : ℂ) * mFourier (-m) t := by
      intro t
      change ((mFourier m t).re : ℂ) = _
      simp only [mFourier_neg]
      have hc := Complex.add_conj (mFourier m t)
      rw [← mul_add, hc]; push_cast; ring
    simp_rw [hpt]
    rw [integral_add ((integrable_mFourier m).const_mul _)
      ((integrable_mFourier (-m)).const_mul _), integral_const_mul, integral_const_mul,
      integral_mFourier, integral_mFourier, if_neg hm, if_neg (fun h => hm (neg_eq_zero.mp h))]
    ring
  have hbridge := hint
  rw [integral_complex_ofReal] at hbridge
  exact_mod_cast hbridge

/-- **Compile-time non-vacuity.**  The Green–Kubo and concentration headlines apply to the concrete
non-constant observable `catReCharObs m`, certifying that the Fourier-decay hypotheses are
inhabited. -/
example (m : Fin 2 → ℤ) :
    Tendsto (fun n => variance (birkhoffSum catTorus (⇑(catReCharObs m)) n) volume / (n : ℝ))
        atTop (𝓝 (catSigmaSq (⇑(catReCharObs m))))
      ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (ε : ℝ), 1 ≤ n → 0 < ε →
          (volume : Measure T2).real
              {x : T2 | ε ≤ |birkhoffSum catTorus (⇑(catReCharObs m)) n x / (n : ℝ)
                - ∫ t : T2, catReCharObs m t|}
            ≤ B / ((n : ℝ) * ε ^ 2) :=
  ⟨catGreenKubo_fourierDecay (by norm_num) (catReCharObs m) (fourierDecay_catReCharObs m),
    catConcentration_fourierDecay (by norm_num) (catReCharObs m) (fourierDecay_catReCharObs m)⟩

/-- **Compile-time non-vacuity for the suspension-flow headline.**  The tier-4 decay law applies to
the concrete fibre-product observable built from `catReCharObs m₁` (base) and the centred
`catReCharObs m₂` (`m₂ ≠ 0`, whose zero mean is `integral_catReCharObs`) with constant fibre
profiles `ψ = χ = 1`, certifying that its hypotheses are inhabited. -/
example (m₁ m₂ : Fin 2 → ℤ) (hm₂ : m₂ ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      |∫ q, fibreProduct catTorusEquiv measurable_catRoof (⇑(catReCharObs m₁)) (fun _ => 1) rfl q
          * fibreProduct catTorusEquiv measurable_catRoof (⇑(catReCharObs m₂)) (fun _ => 1) rfl
              (suspensionFlowMap catTorusEquiv measurable_catRoof 1 q)
          ∂(suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2))|
        ≤ 1 * 1 * C * (lam ^ (-(3 - 2) / 4 : ℝ)) ^ (⌊(1 : ℝ)⌋.toNat) :=
  catSuspensionDecay_fourierDecay (by norm_num) (catReCharObs m₁) (catReCharObs m₂)
    (fourierDecay_catReCharObs m₁) (fourierDecay_catReCharObs m₂) (integral_catReCharObs m₂ hm₂)
    (fun _ => 1) (fun _ => 1) measurable_const measurable_const (fun _ => by norm_num)
    (fun _ => by norm_num) 1 (by norm_num)

end ErgodicTheory.CatMapToral

end
