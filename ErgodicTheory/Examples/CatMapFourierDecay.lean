/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapToral
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The Fourier-decay observable class on the 2-torus

This module introduces the coefficient-decay class `𝒞_s` used in the Fourier-analytic proof of
exponential mixing for hyperbolic toral automorphisms (the Arnold cat map, see
`ErgodicTheory/Examples/CatMapToral.lean`).  A function `f : 𝕋² → ℂ` lies in the class
`FourierDecay s` when its multivariate Fourier coefficients decay at least like `⟨n⟩^(-s)`, where
`⟨n⟩ = bracket n` is the Japanese bracket with respect to the sup norm on the frequency lattice
`ℤ²`.

## Main definitions and results

* `CatMapToral.bracket` — the Japanese bracket `⟨n⟩ = max 1 (max |n₀| |n₁|)`.
* `CatMapToral.FourierDecay` — the coefficient-decay class.
* `CatMapToral.fourierDecay_mFourier` — every character `mFourier m` is in every class
  `FourierDecay s` (non-vacuity); its coefficients are a Kronecker delta.
* `CatMapToral.FourierDecay.add`, `CatMapToral.FourierDecay.smul`,
  `CatMapToral.fourierDecay_finsetSum` — closure under (integrable) sums and scalar multiples, hence
  every trigonometric polynomial lies in the class.
* `CatMapToral.summable_bracket_rpow` — **the key lattice-sum estimate**: for `2 < s`, the family
  `n ↦ ⟨n⟩^(-s)` is summable over `ℤ²`.
* `CatMapToral.tsum_bracket_rpow_tail_le` — a clean tail bound: the sum of `⟨n⟩^(-s)` over any
  set of frequencies with `⟨n⟩ ≥ R` is `≤ C_s · R^(-(s-2)/2)`, with `C_s` the total sum of the
  faster-decaying family `⟨n⟩^(-(s+2)/2)`.  This is exactly the shape a downstream
  exponential-mixing argument consumes to bound a geometric tail
  `∑_{⟨b⟩ > λ^{k/2}} K·L·⟨b⟩^(-s) ≤ C·θ^k`.

## References

Standard lattice-sum comparison (splitting the exponent and dominating the sup norm by a product of
one-dimensional factors); the class is the coefficient-decay class `𝒞_s` from the Fourier proof of
exponential mixing for hyperbolic toral automorphisms, cf. M. Einsiedler and T. Ward, *Ergodic
Theory with a view towards Number Theory*, Chapter 2.
-/

open MeasureTheory UnitAddTorus Matrix
open scoped ComplexConjugate ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (matching `CatMapToral.lean` and the Fourier
API in `Mathlib.Analysis.Fourier.AddCircleMulti`).  Local instances do not cross files, so the trio
is repeated here. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catFourierDecay :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catFourierDecay :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catFourierDecay :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## The Japanese bracket -/

/-- The Japanese bracket `⟨n⟩` of a frequency `n : ℤ²`, with respect to the sup norm: it is spelled
with explicit maxima of the real casts (cheaper than going through the Pi norm instance). -/
def bracket (n : Fin 2 → ℤ) : ℝ := max 1 (max |(n 0 : ℝ)| |(n 1 : ℝ)|)

lemma one_le_bracket (n : Fin 2 → ℤ) : 1 ≤ bracket n := le_max_left _ _

lemma bracket_pos (n : Fin 2 → ℤ) : 0 < bracket n := lt_of_lt_of_le one_pos (one_le_bracket n)

lemma bracket_nonneg (n : Fin 2 → ℤ) : 0 ≤ bracket n := (bracket_pos n).le

@[simp] lemma bracket_zero : bracket (0 : Fin 2 → ℤ) = 1 := by simp [bracket]

/-! ## The decay class

This re-uses the `T2` abbreviation (`= UnitAddTorus (Fin 2)`) from `CatMapToral.lean`. -/

/-- The Fourier-decay class `𝒞_s`: functions whose `n`-th Fourier coefficient is `O(⟨n⟩^(-s))`
uniformly, with an explicit nonnegative constant. -/
def FourierDecay (s : ℝ) (f : T2 → ℂ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖mFourierCoeff f n‖ ≤ K * bracket n ^ (-s)

/-! ## Fourier coefficients of characters are a Kronecker delta -/

/-- The Fourier coefficients of a character `mFourier m` form a Kronecker delta at `m`.  This is the
orthonormality of the Fourier monomials, transported to the raw coefficient integral. -/
lemma mFourierCoeff_mFourier (m n : Fin 2 → ℤ) :
    mFourierCoeff (mFourier m : T2 → ℂ) n = if n = m then 1 else 0 := by
  have hbm : (mFourier m).toLp 2 volume ℂ = mFourierBasis (d := Fin 2) m := by
    rw [coe_mFourierBasis]
  rw [← mFourierCoeff_toLp (mFourier m) n, ← mFourierBasis_repr, hbm,
    HilbertBasis.repr_apply_apply, coe_mFourierBasis]
  exact orthonormal_iff_ite.mp orthonormal_mFourier n m

/-! ## Non-vacuity: characters lie in every class -/

/-- **Non-vacuity.**  Every character `mFourier m` lies in every class `FourierDecay s`: its
coefficients are a Kronecker delta, so a constant `⟨m⟩^s` dominates. -/
theorem fourierDecay_mFourier (s : ℝ) (m : Fin 2 → ℤ) :
    FourierDecay s (mFourier m : T2 → ℂ) := by
  refine ⟨bracket m ^ s, (Real.rpow_pos_of_pos (bracket_pos m) s).le, fun n => ?_⟩
  rw [mFourierCoeff_mFourier]
  by_cases h : n = m
  · rw [if_pos h, norm_one, h, ← Real.rpow_add (bracket_pos m)]
    simp
  · rw [if_neg h, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (bracket_nonneg m) s)
      (Real.rpow_nonneg (bracket_nonneg n) _)

/-! ## Closure of the class -/

/-- The Fourier coefficient is homogeneous of degree one in the function (no integrability needed:
`integral_smul` is unconditional). -/
lemma mFourierCoeff_smul (c : ℂ) (f : T2 → ℂ) (n : Fin 2 → ℤ) :
    mFourierCoeff (c • f) n = c • mFourierCoeff f n := by
  unfold mFourierCoeff
  simp only [Pi.smul_apply]
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  exact smul_comm (mFourier (-n) t) c (f t)

/-- **Closure under scalar multiplication.** -/
theorem FourierDecay.smul {s : ℝ} {f : T2 → ℂ} (hf : FourierDecay s f) (c : ℂ) :
    FourierDecay s (c • f) := by
  obtain ⟨K, hK, hbound⟩ := hf
  refine ⟨‖c‖ * K, mul_nonneg (norm_nonneg c) hK, fun n => ?_⟩
  rw [mFourierCoeff_smul, norm_smul]
  calc ‖c‖ * ‖mFourierCoeff f n‖
      ≤ ‖c‖ * (K * bracket n ^ (-s)) :=
        mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg c)
    _ = ‖c‖ * K * bracket n ^ (-s) := by ring

/-- A character times an integrable function is integrable (bounded times integrable). -/
lemma integrable_char_smul {f : T2 → ℂ} (hf : Integrable f volume) (n : Fin 2 → ℤ) :
    Integrable (fun t => mFourier (-n) t • f t) volume := by
  simp only [smul_eq_mul]
  refine hf.bdd_mul (c := 1) (mFourier (-n)).continuous.aestronglyMeasurable ?_
  filter_upwards with t
  calc ‖(mFourier (-n)) t‖ ≤ ‖mFourier (-n)‖ := (mFourier (-n)).norm_coe_le_norm t
    _ = 1 := mFourier_norm

/-- Characters are integrable (bounded continuous functions on a finite-measure space). -/
lemma integrable_mFourier (m : Fin 2 → ℤ) : Integrable (mFourier m : T2 → ℂ) volume := by
  have h := (BoundedContinuousFunction.mkOfCompact (mFourier m)).integrable
    (μ := (volume : Measure T2))
  refine h.congr ?_
  filter_upwards with t
  rfl

/-- The Fourier coefficient is additive on integrable functions (`integral_add`). -/
lemma mFourierCoeff_add {f g : T2 → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (n : Fin 2 → ℤ) :
    mFourierCoeff (f + g) n = mFourierCoeff f n + mFourierCoeff g n := by
  unfold mFourierCoeff
  simp only [Pi.add_apply, smul_add]
  exact integral_add (integrable_char_smul hf n) (integrable_char_smul hg n)

/-- **Closure under addition** of integrable representatives. -/
theorem FourierDecay.add {s : ℝ} {f g : T2 → ℂ} (hf : FourierDecay s f)
    (hg : FourierDecay s g) (hfi : Integrable f volume) (hgi : Integrable g volume) :
    FourierDecay s (f + g) := by
  obtain ⟨K₁, hK₁, hb₁⟩ := hf
  obtain ⟨K₂, hK₂, hb₂⟩ := hg
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun n => ?_⟩
  rw [mFourierCoeff_add hfi hgi]
  calc ‖mFourierCoeff f n + mFourierCoeff g n‖
      ≤ ‖mFourierCoeff f n‖ + ‖mFourierCoeff g n‖ := norm_add_le _ _
    _ ≤ K₁ * bracket n ^ (-s) + K₂ * bracket n ^ (-s) := add_le_add (hb₁ n) (hb₂ n)
    _ = (K₁ + K₂) * bracket n ^ (-s) := by ring

/-- A trigonometric polynomial is integrable. -/
lemma integrable_trigPoly {ι : Type*} (s : Finset ι) (c : ι → ℂ) (m : ι → Fin 2 → ℤ) :
    Integrable (fun x => ∑ i ∈ s, c i • mFourier (m i) x) volume := by
  apply integrable_finsetSum
  intro i _
  exact (integrable_mFourier (m i)).smul (c i)

/-- **Trigonometric polynomials lie in every class.**  A finite `ℂ`-linear combination of characters
is in `FourierDecay sExp` for every `sExp`.  Proved by induction on the index set, using closure
under scalar multiples and integrable sums. -/
theorem fourierDecay_finsetSum {ι : Type*} (sExp : ℝ) (s : Finset ι) (c : ι → ℂ)
    (m : ι → Fin 2 → ℤ) :
    FourierDecay sExp (fun x => ∑ i ∈ s, c i • mFourier (m i) x) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨0, le_refl 0, fun n => ?_⟩
      have h0 : mFourierCoeff (fun x => ∑ i ∈ (∅ : Finset ι), c i • mFourier (m i) x) n = 0 := by
        simp only [Finset.sum_empty]
        unfold mFourierCoeff
        simp only [smul_zero, integral_zero]
      rw [h0]
      simp
  | insert a s ha ih =>
      have hsplit : (fun x => ∑ i ∈ insert a s, c i • mFourier (m i) x)
          = (c a • (mFourier (m a) : T2 → ℂ))
            + (fun x => ∑ i ∈ s, c i • mFourier (m i) x) := by
        funext x
        simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply]
      rw [hsplit]
      exact FourierDecay.add ((fourierDecay_mFourier sExp (m a)).smul (c a)) ih
        ((integrable_mFourier (m a)).smul (c a)) (integrable_trigPoly s c m)

/-! ## The key summability estimate -/

/-- One-dimensional comparison: for `1 < t`, `p ↦ (max 1 |p|)^(-t)` is summable over `ℤ`.  It agrees
with the summable `p ↦ |p|^(-t)` off the single point `p = 0`. -/
lemma summable_max1 {t : ℝ} (ht : 1 < t) :
    Summable (fun p : ℤ => (max 1 |(p : ℝ)|) ^ (-t)) := by
  apply (Real.summable_abs_int_rpow ht).congr_cofinite
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{0}ᶜ, (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite, fun p hp => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hp
  have h1 : (1 : ℝ) ≤ |(p : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hp
  change |(p : ℝ)| ^ (-t) = max 1 |(p : ℝ)| ^ (-t)
  rw [max_eq_right h1]

/-- The pointwise sup-norm bound underlying the two-dimensional estimate: `⟨(p,q)⟩^(-s)` is
dominated by the product of the two one-dimensional factors at exponent `-s/2`.  (The `max 1` is
essential: a pure `|p|^(-s/2)·|q|^(-s/2)` bound fails on the coordinate axes.) -/
lemma sup_rpow_le {s : ℝ} (hs : 0 ≤ s) (p q : ℝ) :
    max 1 (max |p| |q|) ^ (-s)
      ≤ (max 1 |p|) ^ (-(s / 2)) * (max 1 |q|) ^ (-(s / 2)) := by
  have ha1 : (1 : ℝ) ≤ max 1 |p| := le_max_left _ _
  have hb1 : (1 : ℝ) ≤ max 1 |q| := le_max_left _ _
  have hc1 : (1 : ℝ) ≤ max 1 (max |p| |q|) := le_max_left _ _
  have hap : (0 : ℝ) < max 1 |p| := lt_of_lt_of_le one_pos ha1
  have hbp : (0 : ℝ) < max 1 |q| := lt_of_lt_of_le one_pos hb1
  have hcp : (0 : ℝ) < max 1 (max |p| |q|) := lt_of_lt_of_le one_pos hc1
  have hac : max 1 |p| ≤ max 1 (max |p| |q|) := max_le_max le_rfl (le_max_left _ _)
  have hbc : max 1 |q| ≤ max 1 (max |p| |q|) := max_le_max le_rfl (le_max_right _ _)
  have hab_le : max 1 |p| * max 1 |q| ≤ max 1 (max |p| |q|) ^ 2 := by
    have hmul := mul_le_mul hac hbc hbp.le hcp.le
    rwa [← pow_two] at hmul
  have hstep : (max 1 (max |p| |q|) ^ 2) ^ (-(s / 2))
      ≤ (max 1 |p| * max 1 |q|) ^ (-(s / 2)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hap hbp) hab_le (by linarith)
  have hLHS : (max 1 (max |p| |q|) ^ 2) ^ (-(s / 2)) = max 1 (max |p| |q|) ^ (-s) := by
    rw [← Real.rpow_natCast (max 1 (max |p| |q|)) 2, ← Real.rpow_mul hcp.le]
    congr 1
    push_cast
    ring
  rw [← hLHS]
  exact hstep.trans (le_of_eq (Real.mul_rpow hap.le hbp.le))

/-- **The key lattice-sum estimate.**  For `2 < s`, the Japanese-bracket family `n ↦ ⟨n⟩^(-s)` is
summable over the frequency lattice `ℤ²`.  We dominate `⟨n⟩^(-s)` by a product of one-dimensional
factors at exponent `-s/2 < -1` and transport the resulting product summability from `ℤ × ℤ` along
`finTwoArrowEquiv`. -/
theorem summable_bracket_rpow {s : ℝ} (hs : 2 < s) :
    Summable (fun n : Fin 2 → ℤ => bracket n ^ (-s)) := by
  have ht : (1 : ℝ) < s / 2 := by linarith
  have h1 := summable_max1 ht
  have hprod := h1.mul_of_nonneg h1
    (fun p => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    (fun p => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hH : Summable (fun n : Fin 2 → ℤ =>
      (max 1 |(n 0 : ℝ)|) ^ (-(s / 2)) * (max 1 |(n 1 : ℝ)|) ^ (-(s / 2))) := by
    refine ((finTwoArrowEquiv ℤ).summable_iff.mpr hprod).congr (fun n => ?_)
    rfl
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (bracket_nonneg n) _)
    (fun n => ?_) hH
  exact sup_rpow_le (by linarith) (n 0 : ℝ) (n 1 : ℝ)

/-! ## A geometric tail bound -/

/-- **Tail bound.**  Splitting the exponent `-s = -(s+2)/2 + -(s-2)/2` and dominating the second
factor by `R^(-(s-2)/2)` on the tail set, the sum of `⟨n⟩^(-s)` over *any* set of frequencies with
`⟨n⟩ ≥ R` (for `R ≥ 1`) is at most `C_s · R^(-(s-2)/2)`, where `C_s := ∑' n, ⟨n⟩^(-(s+2)/2)` is the
total sum of the faster-decaying family (summable since `(s+2)/2 > 2`).

Downstream use: a Fourier exponential-mixing argument bounds a sum
`∑_{⟨b⟩ > λ^{k/2}} K·L·⟨b⟩^(-s)` by factoring out `K·L`, applying this with `R = λ^{k/2}`, and
reading off the geometric decay `R^(-(s-2)/2) = θ^k` with `θ = λ^(-(s-2)/4)`. -/
theorem tsum_bracket_rpow_tail_le {s R : ℝ} (hs : 2 < s) (hR : 1 ≤ R)
    {S : Set (Fin 2 → ℤ)} (hS : ∀ n ∈ S, R ≤ bracket n) :
    ∑' n : ↥S, bracket (n : Fin 2 → ℤ) ^ (-s)
      ≤ (∑' n : Fin 2 → ℤ, bracket n ^ (-((s + 2) / 2))) * R ^ (-((s - 2) / 2)) := by
  have hp2 : (2 : ℝ) < (s + 2) / 2 := by linarith
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hqnp : (-((s - 2) / 2) : ℝ) ≤ 0 := by linarith
  have hsumS : Summable (fun n : ↥S => bracket (n : Fin 2 → ℤ) ^ (-s)) :=
    (summable_bracket_rpow hs).subtype (· ∈ S)
  have hgS : Summable (fun n : ↥S =>
      bracket (n : Fin 2 → ℤ) ^ (-((s + 2) / 2)) * R ^ (-((s - 2) / 2))) :=
    ((summable_bracket_rpow hp2).mul_right (R ^ (-((s - 2) / 2)))).subtype (· ∈ S)
  have hterm : ∀ n : ↥S, bracket (n : Fin 2 → ℤ) ^ (-s)
      ≤ bracket (n : Fin 2 → ℤ) ^ (-((s + 2) / 2)) * R ^ (-((s - 2) / 2)) := by
    intro n
    have hb := bracket_pos (n : Fin 2 → ℤ)
    have hsplit : (-s : ℝ) = -((s + 2) / 2) + -((s - 2) / 2) := by ring
    rw [hsplit, Real.rpow_add hb]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hR0 (hS _ n.2) hqnp)
      (Real.rpow_nonneg hb.le _)
  calc ∑' n : ↥S, bracket (n : Fin 2 → ℤ) ^ (-s)
      ≤ ∑' n : ↥S,
          bracket (n : Fin 2 → ℤ) ^ (-((s + 2) / 2)) * R ^ (-((s - 2) / 2)) :=
        hsumS.tsum_le_tsum hterm hgS
    _ = (∑' n : ↥S, bracket (n : Fin 2 → ℤ) ^ (-((s + 2) / 2)))
          * R ^ (-((s - 2) / 2)) :=
        ((summable_bracket_rpow hp2).subtype (· ∈ S)).tsum_mul_right _
    _ ≤ (∑' n : Fin 2 → ℤ, bracket n ^ (-((s + 2) / 2))) * R ^ (-((s - 2) / 2)) :=
        mul_le_mul_of_nonneg_right
          (Summable.tsum_subtype_le _ S (fun n => Real.rpow_nonneg (bracket_nonneg n) _)
            (summable_bracket_rpow hp2))
          (Real.rpow_nonneg hR0.le _)

end ErgodicTheory.CatMapToral
