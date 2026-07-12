/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapMixing
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The Fourier / character-pairing expansion of the cat-map correlation

This module records the **Parseval / character-pairing expansion** of the correlation
`∫ conj f · (g ∘ Tᵏ)` of two continuous observables `f g : 𝕋² → ℂ` under the `k`-fold iterate of
the Arnold cat map `catTorus`.  It is the standard first step of the Fourier proof of *quantitative*
mixing for hyperbolic toral automorphisms (Einsiedler–Ward, *Ergodic Theory with a View Towards
Number Theory*, Ch. 2): Parseval turns the correlation into a bilinear sum over the character
lattice, and the Koopman action `mFourier n ∘ Tᵏ = mFourier (Mᵏ ·ᵥ n)` shifts the index on one
factor, so the growth of `‖ĉ_f(Mᵏ b)‖` for `b ≠ 0` (hyperbolicity) controls the decay.

## Main results

* `ErgodicTheory.CatMapToral.mFourierCoeff_comp_iterate` — the Koopman coefficient shift:
  `mFourierCoeff (g ∘ Tᵏ) (Mᵏ ·ᵥ b) = mFourierCoeff g b` (the shifted index lands on the composed
  factor, equivalently on `f` after reindexing the sum).
* `ErgodicTheory.CatMapToral.mFourierCoeff_zero_eq_integral` — `mFourierCoeff g 0 = ∫ g`.
* `ErgodicTheory.CatMapToral.hasSum_correlation_fourier` — **the expansion**: for continuous
  `f g`, `HasSum (fun b => conj (ĉ_f (Mᵏ ·ᵥ b)) * ĉ_g b) (∫ conj f · (g ∘ Tᵏ))`.
* `ErgodicTheory.CatMapToral.hasSum_correlation_fourier_ne_zero` — the `b ≠ 0` restriction, whose
  sum is `∫ conj f · (g ∘ Tᵏ) − (∫ conj f) · (∫ g)` (correlation minus product of means).
* `ErgodicTheory.CatMapToral.norm_correlation_sub_le` — the resulting tail norm bound (given
  summability of the RHS).

## References

* M. Einsiedler, T. Ward, *Ergodic Theory with a View Towards Number Theory*, Ch. 2.
-/

open MeasureTheory UnitAddTorus Matrix Filter Topology
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching
`ErgodicTheory.Examples.CatMapToral`: with this `MeasureSpace` instance, `volume` on
`UnitAddTorus (Fin 2)` is the product Haar probability measure on `𝕋²`, the basis used by the
Fourier API. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catCorrExp :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catCorrExp :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catCorrExp :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## The reindexing bijection of the character lattice -/

/-- `M⁻ᵏ · Mᵏ = 1` (the two integer matrices `catℤ`, `catℤinv` are inverse, hence commute). -/
lemma catℤinv_pow_mul_catℤ_pow (k : ℕ) : catℤinv ^ k * catℤ ^ k = 1 := by
  have hc : Commute catℤinv catℤ := by
    unfold Commute SemiconjBy; rw [catℤinv_mul, catℤ_mul_inv]
  rw [← hc.mul_pow, catℤinv_mul, one_pow]

/-- `Mᵏ · M⁻ᵏ = 1`. -/
lemma catℤ_pow_mul_catℤinv_pow (k : ℕ) : catℤ ^ k * catℤinv ^ k = 1 := by
  have hc : Commute catℤ catℤinv := by
    unfold Commute SemiconjBy; rw [catℤ_mul_inv, catℤinv_mul]
  rw [← hc.mul_pow, catℤ_mul_inv, one_pow]

/-- The `k`-th matrix power `Mᵏ` acts on the character lattice `ℤ²` as a bijection
`b ↦ Mᵏ ·ᵥ b`, with inverse `c ↦ M⁻ᵏ ·ᵥ c`. -/
def mulVecEquiv (k : ℕ) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun b := catℤ ^ k *ᵥ b
  invFun c := catℤinv ^ k *ᵥ c
  left_inv b := by
    change catℤinv ^ k *ᵥ (catℤ ^ k *ᵥ b) = b
    rw [mulVec_mulVec, catℤinv_pow_mul_catℤ_pow, one_mulVec]
  right_inv c := by
    change catℤ ^ k *ᵥ (catℤinv ^ k *ᵥ c) = c
    rw [mulVec_mulVec, catℤ_pow_mul_catℤinv_pow, one_mulVec]

@[simp] lemma mulVecEquiv_apply (k : ℕ) (b : Fin 2 → ℤ) : mulVecEquiv k b = catℤ ^ k *ᵥ b := rfl

/-! ## The Koopman coefficient shift -/

/-- **Koopman coefficient shift.**  Composing an observable with the `k`-th iterate of the cat map
shifts its Fourier coefficients by the `k`-th matrix power of the index:
`mFourierCoeff (g ∘ Tᵏ) (Mᵏ ·ᵥ b) = mFourierCoeff g b`.

Since `mFourier (-b) ∘ Tᵏ = mFourier (-(Mᵏ ·ᵥ b))` (`mFourier_iterate_catTorus` + linearity of
`·ᵥ`), the defining integrand of `mFourierCoeff (g ∘ Tᵏ) (Mᵏ ·ᵥ b)` is
`(fun u => mFourier (-b) u • g u) ∘ Tᵏ`; measure preservation of `Tᵏ` removes the composition. -/
theorem mFourierCoeff_comp_iterate (g : T2 → ℂ) (k : ℕ) (b : Fin 2 → ℤ) :
    mFourierCoeff (fun t => g (catTorus^[k] t)) (catℤ ^ k *ᵥ b) = mFourierCoeff g b := by
  have hbij : Function.Bijective (catTorus^[k]) := catTorus_bijective.iterate k
  have hemb : MeasurableEmbedding (catTorus^[k]) :=
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (catTorus^[k]) hbij)
      (continuous_catTorus.iterate k)).measurableEmbedding
  have hmp := measurePreserving_catTorus.iterate k
  have hpt : ∀ t : T2, mFourier (-(catℤ ^ k *ᵥ b)) t • g (catTorus^[k] t)
      = mFourier (-b) (catTorus^[k] t) • g (catTorus^[k] t) := by
    intro t
    have h := mFourier_iterate_catTorus k (-b) t
    rw [mulVec_neg] at h
    rw [h]
  calc mFourierCoeff (fun t => g (catTorus^[k] t)) (catℤ ^ k *ᵥ b)
      = ∫ t : T2, mFourier (-(catℤ ^ k *ᵥ b)) t • g (catTorus^[k] t) := rfl
    _ = ∫ t : T2, mFourier (-b) (catTorus^[k] t) • g (catTorus^[k] t) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ u : T2, mFourier (-b) u • g u :=
        hmp.integral_comp hemb (fun u => mFourier (-b) u • g u)
    _ = mFourierCoeff g b := rfl

/-- The mean `mFourierCoeff g 0 = ∫ g` (the trivial character is constant `1`). -/
theorem mFourierCoeff_zero_eq_integral (g : T2 → ℂ) :
    mFourierCoeff g (0 : Fin 2 → ℤ) = ∫ t : T2, g t := by
  change ∫ t : T2, mFourier (-(0 : Fin 2 → ℤ)) t • g t = ∫ t : T2, g t
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [neg_zero, mFourier_zero_apply, one_smul]

/-! ## The expansion -/

set_option maxHeartbeats 800000 in
-- The Parseval application, the coefficient/integral `toLp` rewrites, and the lattice reindexing
-- assemble into a single elaboration that exceeds the default heartbeat budget.
/-- **Parseval / character-pairing expansion of the correlation.**  For continuous observables
`f g : 𝕋² → ℂ`,
`∑ b, conj (ĉ_f (Mᵏ ·ᵥ b)) · ĉ_g b = ∫ conj f · (g ∘ Tᵏ)`,
the standard first step of the Fourier proof of quantitative mixing.  Parseval
(`hasSum_prod_mFourierCoeff`) pairs the coefficients of `f` and `g ∘ Tᵏ`; reindexing the lattice by
`b ↦ Mᵏ ·ᵥ b` and the Koopman shift `mFourierCoeff_comp_iterate` move the shift onto the `f`
factor. -/
theorem hasSum_correlation_fourier (f g : C(T2, ℂ)) (k : ℕ) :
    HasSum (fun b : Fin 2 → ℤ =>
        (starRingEnd ℂ) (mFourierCoeff f (catℤ ^ k *ᵥ b)) * mFourierCoeff g b)
      (∫ t : T2, (starRingEnd ℂ) (f t) * g (catTorus^[k] t)) := by
  set Tk : C(T2, T2) := ⟨catTorus^[k], continuous_catTorus.iterate k⟩ with hTk
  set gTk : C(T2, ℂ) := g.comp Tk with hgTk
  have hbase : HasSum (fun i : Fin 2 → ℤ =>
      (starRingEnd ℂ) (mFourierCoeff (f.toLp 2 volume ℂ) i)
        * mFourierCoeff (gTk.toLp 2 volume ℂ) i)
      (∫ t : T2, (starRingEnd ℂ) ((f.toLp 2 volume ℂ) t) * (gTk.toLp 2 volume ℂ) t) :=
    hasSum_prod_mFourierCoeff _ _
  simp only [mFourierCoeff_toLp] at hbase
  -- The composed coefficient is the shifted coefficient of `g`.
  have hshift : ∀ b : Fin 2 → ℤ,
      mFourierCoeff gTk (catℤ ^ k *ᵥ b) = mFourierCoeff g b := by
    intro b
    have hcoe : (gTk : T2 → ℂ) = fun t => g (catTorus^[k] t) := by
      funext t; simp only [hgTk, ContinuousMap.comp_apply, hTk, ContinuousMap.coe_mk]
    rw [hcoe, mFourierCoeff_comp_iterate]
  -- The `L²` integral is the honest correlation integral.
  have hint : (∫ t : T2, (starRingEnd ℂ) ((f.toLp 2 volume ℂ) t) * (gTk.toLp 2 volume ℂ) t)
      = ∫ t : T2, (starRingEnd ℂ) (f t) * g (catTorus^[k] t) := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := (volume : Measure T2))
        (𝕜 := ℂ) f,
      ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := (volume : Measure T2)) (𝕜 := ℂ) gTk]
      with t hf hg
    rw [hf, hg]
    simp only [hgTk, ContinuousMap.comp_apply, hTk, ContinuousMap.coe_mk]
  rw [hint] at hbase
  -- Reindex the lattice by `b ↦ Mᵏ ·ᵥ b`; the Koopman shift moves the shift onto `f`.
  have key : (fun b : Fin 2 → ℤ =>
        (starRingEnd ℂ) (mFourierCoeff f (catℤ ^ k *ᵥ b)) * mFourierCoeff g b)
      = (fun i : Fin 2 → ℤ =>
          (starRingEnd ℂ) (mFourierCoeff f i) * mFourierCoeff gTk i) ∘ (mulVecEquiv k) := by
    funext b
    simp only [Function.comp_apply, mulVecEquiv_apply, hshift b]
  rw [key]
  exact (Equiv.hasSum_iff (f := fun i : Fin 2 → ℤ =>
    (starRingEnd ℂ) (mFourierCoeff f i) * mFourierCoeff gTk i) (mulVecEquiv k)).mpr hbase

/-! ## The `b ≠ 0` restriction and the tail bound -/

/-- **The `b ≠ 0` expansion.**  Removing the trivial character from `hasSum_correlation_fourier`
identifies the sum over `b ≠ 0` with the *centred* correlation
`∫ conj f · (g ∘ Tᵏ) − (∫ conj f) · (∫ g)` (correlation minus the product of the means). -/
theorem hasSum_correlation_fourier_ne_zero (f g : C(T2, ℂ)) (k : ℕ) :
    HasSum (fun b : {b : Fin 2 → ℤ // b ≠ 0} =>
        (starRingEnd ℂ) (mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ)))
          * mFourierCoeff g (b : Fin 2 → ℤ))
      ((∫ t : T2, (starRingEnd ℂ) (f t) * g (catTorus^[k] t))
        - (∫ t : T2, (starRingEnd ℂ) (f t)) * (∫ t : T2, g t)) := by
  have hfull := hasSum_correlation_fourier f g k
  -- The `b = 0` term is the product of the means.
  have hz : (starRingEnd ℂ) (mFourierCoeff f (catℤ ^ k *ᵥ (0 : Fin 2 → ℤ)))
        * mFourierCoeff g (0 : Fin 2 → ℤ)
      = (∫ t : T2, (starRingEnd ℂ) (f t)) * (∫ t : T2, g t) := by
    rw [mulVec_zero, mFourierCoeff_zero_eq_integral, mFourierCoeff_zero_eq_integral,
      ← integral_conj]
  -- Reindexing the removed `b = 0` term to the full sum recovers `hfull`.
  have hval : ((∫ t : T2, (starRingEnd ℂ) (f t) * g (catTorus^[k] t))
        - (∫ t : T2, (starRingEnd ℂ) (f t)) * (∫ t : T2, g t))
      + ∑ i ∈ ({0} : Finset (Fin 2 → ℤ)),
          ((starRingEnd ℂ) (mFourierCoeff f (catℤ ^ k *ᵥ i)) * mFourierCoeff g i)
      = ∫ t : T2, (starRingEnd ℂ) (f t) * g (catTorus^[k] t) := by
    rw [Finset.sum_singleton, hz, sub_add_cancel]
  -- Remove the singleton `{0}`.
  have hcompl := (Finset.hasSum_compl_iff (f := fun i : Fin 2 → ℤ =>
      (starRingEnd ℂ) (mFourierCoeff f (catℤ ^ k *ᵥ i)) * mFourierCoeff g i)
      ({0} : Finset (Fin 2 → ℤ))).mpr (hval.symm ▸ hfull)
  -- Reindex `{x ∉ {0}}` to `{b ≠ 0}` (`subtypeEquivRight` preserves the underlying value).
  exact (Equiv.hasSum_iff (Equiv.subtypeEquivRight (fun x : Fin 2 → ℤ => by
      simp only [Finset.mem_singleton]) :
      {b : Fin 2 → ℤ // b ≠ 0} ≃ {x : Fin 2 → ℤ // x ∉ ({0} : Finset (Fin 2 → ℤ))})).mpr hcompl

/-- **Tail norm bound for the centred correlation.**  Given summability of the `b ≠ 0` term-norms,
`‖∫ conj f · (g ∘ Tᵏ) − (∫ conj f) · (∫ g)‖ ≤ ∑'_{b ≠ 0} ‖ĉ_f (Mᵏ ·ᵥ b)‖ · ‖ĉ_g b‖`.  This is the
usable input to a quantitative decay estimate. -/
theorem norm_correlation_sub_le (f g : C(T2, ℂ)) (k : ℕ)
    (hsum : Summable (fun b : {b : Fin 2 → ℤ // b ≠ 0} =>
      ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖ * ‖mFourierCoeff g (b : Fin 2 → ℤ)‖)) :
    ‖(∫ t : T2, (starRingEnd ℂ) (f t) * g (catTorus^[k] t))
        - (∫ t : T2, (starRingEnd ℂ) (f t)) * (∫ t : T2, g t)‖
      ≤ ∑' b : {b : Fin 2 → ℤ // b ≠ 0},
          ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖
            * ‖mFourierCoeff g (b : Fin 2 → ℤ)‖ := by
  have hne := hasSum_correlation_fourier_ne_zero f g k
  have hnorm : ∀ b : {b : Fin 2 → ℤ // b ≠ 0},
      ‖(starRingEnd ℂ) (mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ)))
          * mFourierCoeff g (b : Fin 2 → ℤ)‖
        = ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖ * ‖mFourierCoeff g (b : Fin 2 → ℤ)‖ := by
    intro b; rw [norm_mul, RCLike.norm_conj]
  rw [← hne.tsum_eq]
  refine (norm_tsum_le_tsum_norm (hsum.congr fun b => (hnorm b).symm)).trans_eq ?_
  exact tsum_congr hnorm

end ErgodicTheory.CatMapToral
