/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Per-fibre Parseval bridge and the indicator dichotomy (issue #35)

This module isolates the harmonic-analysis ingredient used in the proof that the
time-`1` map of a constant-irrational-roof Bernoulli suspension is ergodic
(GitHub issue #35, STEP D finale).

Working on the lifted plane, the characteristic function of a `ζ₁`-invariant set
restricts, over each base point `x`, to a bounded measurable `1`-periodic
function `g : ℝ → ℝ` taking values in `{0, 1}`.  We provide:

* `ErgodicTheory.parseval_bridge` — the per-fibre Parseval identity relating the
  square-summed Fourier coefficients of a bounded measurable `1`-periodic
  `f : ℝ → ℂ` to `∫₀¹ ‖f‖²`, via the lift to `AddCircle (1 : ℝ)`;

* `ErgodicTheory.fibre_indicator_dichotomy` — if additionally `g` is
  `{0, 1}`-valued and all of its nonzero-mode Fourier coefficients vanish, then
  `g = 0` a.e. on `Ioc 0 1` or `g = 1` a.e. on `Ioc 0 1`;

* `ErgodicTheory.measure_periodic_ae_zero_spread` — a periodic null-set spread:
  a `1`-periodic function that vanishes a.e. on `Ioc 0 1` vanishes a.e. on
  `Ioc 0 r` for every `r`.

References: I. P. Cornfeld, S. V. Fomin and Ya. G. Sinai, *Ergodic Theory*
(CFS), Grundlehren der mathematischen Wissenschaften 245, Springer, 1982.
-/

open MeasureTheory Set Function AddCircle
open scoped Real ENNReal

noncomputable section

namespace ErgodicTheory

-- The `Fact ((0 : ℝ) < 1)` needed for the length-`1` circle `AddCircle (1 : ℝ)` is already
-- supplied globally by Mathlib (`ZeroLEOneClass.factZeroLtOne`); no local instance is added.

/-- The per-`x` Parseval bridge: for a bounded measurable `f : ℝ → ℂ`,
`∑' n, ‖(n-th Fourier coefficient)‖² = ∫ s in 0..1, ‖f s‖²`.  Only the values of
`f` on `Ioc 0 1` matter, so no periodicity hypothesis is required. -/
theorem parseval_bridge (f : ℝ → ℂ) (hf : Measurable f) (hbd : ∀ s, ‖f s‖ ≤ 1) :
    ∑' n : ℤ, ‖∫ s in (0 : ℝ)..1, fourier (-n) (s : AddCircle (1 : ℝ)) • f s‖ ^ 2
      = ∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 := by
  -- the lift to the circle
  set g : AddCircle (1 : ℝ) → ℂ := liftIoc (1 : ℝ) 0 f with hg
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  -- MemLp 2 for the lift
  have hmem : MemLp g 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
    rw [← hvol]
    refine MemLp.memLp_liftIoc ?_
    refine MemLp.of_bound (hf.aestronglyMeasurable.restrict) 1 ?_
    exact Filter.Eventually.of_forall hbd
  set gL : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))) := hmem.toLp g with hgL
  have hcoe : (gL : AddCircle (1 : ℝ) → ℂ) =ᵐ[haarAddCircle] g := MemLp.coeFn_toLp hmem
  -- coefficients agree with the interval integrals
  have hcoeff : ∀ n : ℤ, fourierCoeff (gL : AddCircle (1 : ℝ) → ℂ) n
      = ∫ s in (0 : ℝ)..1, fourier (-n) (s : AddCircle (1 : ℝ)) • f s := by
    intro n
    have e1 : fourierCoeff (gL : AddCircle (1 : ℝ) → ℂ) n = fourierCoeff g n := by
      rw [fourierCoeff, fourierCoeff]
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with θ hθ
      rw [hθ]
    rw [e1, fourierCoeff_eq_intervalIntegral g n 0]
    simp only [one_div, zero_add]
    rw [inv_one, one_smul]
    refine intervalIntegral.integral_congr_ae ?_
    have hIoc : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ uIoc (0 : ℝ) 1 → s ∈ Ioc (0 : ℝ) (0 + 1) := by
      refine Filter.Eventually.of_forall fun s hs => ?_
      rwa [uIoc_of_le zero_le_one, ← zero_add (1 : ℝ)] at hs
    filter_upwards [hIoc] with s hs hsmem
    rw [hg, liftIoc_coe_apply (hs hsmem)]
  -- Parseval on the circle
  have hpars := tsum_sq_fourierCoeff gL
  have hLHS : ∑' n : ℤ, ‖∫ s in (0 : ℝ)..1, fourier (-n) (s : AddCircle (1 : ℝ)) • f s‖ ^ 2
      = ∑' n : ℤ, ‖fourierCoeff (gL : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 := by
    refine tsum_congr fun n => ?_
    rw [hcoeff n]
  -- the L² norm integral transfers to the interval
  have hRHS : (∫ θ : AddCircle (1 : ℝ), ‖(gL : AddCircle (1 : ℝ) → ℂ) θ‖ ^ 2 ∂haarAddCircle)
      = ∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 := by
    have e1 : (∫ θ : AddCircle (1 : ℝ), ‖(gL : AddCircle (1 : ℝ) → ℂ) θ‖ ^ 2 ∂haarAddCircle)
        = ∫ θ : AddCircle (1 : ℝ), ‖g θ‖ ^ 2 ∂haarAddCircle := by
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with θ hθ
      rw [hθ]
    have e2 : (∫ θ : AddCircle (1 : ℝ), ‖g θ‖ ^ 2 ∂haarAddCircle)
        = ∫ θ : AddCircle (1 : ℝ), ‖g θ‖ ^ 2 := by
      rw [hvol]
    have e3 : (∫ θ : AddCircle (1 : ℝ), ‖g θ‖ ^ 2)
        = ∫ s in Ioc (0 : ℝ) (0 + 1), ‖g (s : AddCircle (1 : ℝ))‖ ^ 2 :=
      (AddCircle.integral_preimage (1 : ℝ) 0 fun θ => ‖g θ‖ ^ 2).symm
    have e4 : (∫ s in Ioc (0 : ℝ) (0 + 1), ‖g (s : AddCircle (1 : ℝ))‖ ^ 2)
        = ∫ s in Ioc (0 : ℝ) (0 + 1), ‖f s‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hg, liftIoc_coe_apply hs]
    have e5 : (∫ s in Ioc (0 : ℝ) (0 + 1), ‖f s‖ ^ 2) = ∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le zero_le_one, zero_add]
    rw [e1, e2, e3, e4, e5]
  rw [hLHS, hpars, hRHS]

/-- A nonnegative, bounded, measurable function on `Ioc 0 1` whose integral there
vanishes is a.e. zero. -/
private theorem ae_zero_of_integral_zero {k : ℝ → ℝ} (hk : Measurable k)
    (hbd : ∀ s, ‖k s‖ ≤ 1) (hnn : ∀ s, 0 ≤ k s)
    (hzero : ∫ s, k s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), k s = 0 := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  have hint : Integrable k (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (MemLp.of_bound (p := 1) hk.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)).integrable
      le_rfl
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint).mp hzero
  filter_upwards [hae] with s hs
  simpa using hs

/-- **Indicator dichotomy.**  Let `g : ℝ → ℝ` be a measurable `1`-periodic function
taking values in `{0, 1}`, all of whose nonzero-mode Fourier coefficients (over the
period `1`) vanish.  Then `g = 0` a.e. on `Ioc 0 1`, or `g = 1` a.e. on `Ioc 0 1`.

This is the STEP-D finale ingredient of the time-`1` ergodicity argument (issue #35):
a `{0,1}`-valued fibre indicator with no genuine oscillation is a.e. constant. -/
theorem fibre_indicator_dichotomy (g : ℝ → ℝ) (hg : Measurable g)
    (_hper : ∀ s, g (s + 1) = g s) (hval : ∀ s, g s = 0 ∨ g s = 1)
    (hmodes : ∀ n : ℤ, n ≠ 0 →
      (∫ s in (0 : ℝ)..1, Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑n * ↑s)) * (g s : ℂ)) = 0) :
    (∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), g s = 0) ∨
    (∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), g s = 1) := by
  -- elementary pointwise bounds coming from `g ∈ {0,1}`
  have gnn : ∀ s, 0 ≤ g s := fun s => by rcases hval s with h | h <;> norm_num [h]
  have onegnn : ∀ s, 0 ≤ 1 - g s := fun s => by rcases hval s with h | h <;> norm_num [h]
  have gbd : ∀ s, ‖g s‖ ≤ 1 := fun s => by
    rcases hval s with h | h <;> norm_num [h, Real.norm_eq_abs]
  have onegbd : ∀ s, ‖1 - g s‖ ≤ 1 := fun s => by
    rcases hval s with h | h <;> norm_num [h, Real.norm_eq_abs]
  -- the complexified fibre function
  set f : ℝ → ℂ := fun s => (g s : ℂ) with hfdef
  have hf : Measurable f := by rw [hfdef]; exact Complex.continuous_ofReal.measurable.comp hg
  have hbd : ∀ s, ‖f s‖ ≤ 1 := fun s => by
    simp only [hfdef]
    rcases hval s with h | h <;> norm_num [h, Complex.norm_real, Real.norm_eq_abs]
  -- character matching: the abstract Fourier symbol equals the concrete exponential
  have hfourier : ∀ (n : ℤ) (s : ℝ),
      fourier (-n) (↑s : AddCircle (1 : ℝ)) • f s
        = Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑n * ↑s)) * (g s : ℂ) := by
    intro n s
    simp only [hfdef]
    rw [fourier_coe_apply, smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  -- the squared-norm-of-`ℂ`-cast identity
  have hnormsq : ∀ x : ℝ, ‖(x : ℂ)‖ ^ 2 = x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- Parseval, applied to `f`
  have hpars := parseval_bridge f hf hbd
  -- the zero-mode coefficient equals the real interval integral of `g`
  have hc0 : (∫ s in (0 : ℝ)..1, fourier (-(0 : ℤ)) (↑s : AddCircle (1 : ℝ)) • f s)
      = ((∫ s in (0 : ℝ)..1, g s : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr (fun s _ => hfourier 0 s),
      ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  -- every nonzero mode contributes `0`
  have hzero_terms : ∀ n : ℤ, n ≠ 0 →
      ‖∫ s in (0 : ℝ)..1, fourier (-n) (↑s : AddCircle (1 : ℝ)) • f s‖ ^ 2 = 0 := by
    intro n hn
    rw [intervalIntegral.integral_congr (fun s _ => hfourier n s), hmodes n hn, norm_zero]
    norm_num
  -- collapse the Parseval sum to the zero mode
  have h1 : (∑' n : ℤ, ‖∫ s in (0 : ℝ)..1, fourier (-n) (↑s : AddCircle (1 : ℝ)) • f s‖ ^ 2)
      = (∫ s in (0 : ℝ)..1, g s) ^ 2 := by
    rw [tsum_eq_single 0 hzero_terms, hc0, hnormsq]
  -- the right-hand `L²` integral collapses too, because `‖g‖² = g` on `{0,1}`
  have hRHS : (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) = ∫ s in (0 : ℝ)..1, g s := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hfdef]
    rcases hval s with h | h <;> simp [h]
  -- hence `(∫₀¹ g)² = ∫₀¹ g`, so `∫₀¹ g ∈ {0, 1}`
  have hmain : (∫ s in (0 : ℝ)..1, g s) ^ 2 = ∫ s in (0 : ℝ)..1, g s :=
    h1.symm.trans (hpars.trans hRHS)
  have hfac : (∫ s in (0 : ℝ)..1, g s) * ((∫ s in (0 : ℝ)..1, g s) - 1) = 0 := by
    linear_combination hmain
  -- infrastructure to convert interval integrals to restricted integrals
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  have hgint : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (MemLp.of_bound (p := 1) hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall gbd)).integrable
      le_rfl
  have hJg : ∫ s, g s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = ∫ s in (0 : ℝ)..1, g s := by
    rw [intervalIntegral.integral_of_le zero_le_one]
  rcases mul_eq_zero.mp hfac with hI0 | hI1
  · -- `∫₀¹ g = 0`, so `g = 0` a.e.
    exact Or.inl (ae_zero_of_integral_zero hg gbd gnn (hJg.trans hI0))
  · -- `∫₀¹ g = 1`, so `1 - g = 0` a.e., i.e. `g = 1` a.e.
    have hI1' : (∫ s in (0 : ℝ)..1, g s) = 1 := sub_eq_zero.mp hI1
    have hconst : ∫ _s : ℝ, (1 : ℝ) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 1 := by
      rw [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le zero_le_one]
      simp
    have hsub : (∫ s, (1 - g s) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ _s, (1 : ℝ) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
          - ∫ s, g s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      integral_sub (integrable_const 1) hgint
    have h1g0 : ∫ s, (1 - g s) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0 := by
      rw [hsub, hconst, hJg, hI1']; norm_num
    have hae := ae_zero_of_integral_zero (k := fun s => 1 - g s) (measurable_const.sub hg)
      onegbd onegnn h1g0
    refine Or.inr ?_
    filter_upwards [hae] with s hs
    have hs' : 1 - g s = 0 := hs
    linarith

/-- **Periodic null-set spread.**  If `g : ℝ → ℝ` is `1`-periodic and vanishes
a.e. on `Ioc 0 1`, then it vanishes a.e. on `Ioc 0 r` for every `r`.  Boundary
integers form a null set, so `Ioc`/`Ico` are interchangeable up to null sets. -/
theorem measure_periodic_ae_zero_spread {g : ℝ → ℝ} (hper : ∀ s, g (s + 1) = g s)
    (hnull : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), g s = 0) (r : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) r)), g s = 0 := by
  rw [ae_iff, Measure.restrict_apply' measurableSet_Ioc]
  rw [ae_iff, Measure.restrict_apply' measurableSet_Ioc] at hnull
  -- `k`-fold periodicity of `g`
  have hkper : ∀ (k : ℕ) (s : ℝ), g (s + k) = g s := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        have hreassoc : s + ((n : ℝ) + 1) = (s + n) + 1 := by ring
        rw [Nat.cast_succ, hreassoc, hper (s + n), ih s]
  -- reduce the goal `volume (…) = 0` to `volume (…) ≤ 0`
  refine le_antisymm ?_ (zero_le' )
  -- every unit cell `Ioc k (k+1)` carries the same null mass as `Ioc 0 1`
  · have htrans : ∀ k : ℕ, volume ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1))
        = volume ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (0 : ℝ) 1) := by
      intro k
      have hpre : (fun x => x + (k : ℝ)) ⁻¹'
            ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1))
          = {s : ℝ | ¬ g s = 0} ∩ Set.Ioc (0 : ℝ) 1 := by
        ext x
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_setOf_eq, hkper k x]
        constructor
        · rintro ⟨hz, h1, h2⟩; exact ⟨hz, by linarith, by linarith⟩
        · rintro ⟨hz, h1, h2⟩; exact ⟨hz, by linarith, by linarith⟩
      calc volume ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1))
          = volume ((fun x => x + (k : ℝ)) ⁻¹'
              ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1))) :=
            (measure_preimage_add_right volume (k : ℝ) _).symm
        _ = volume ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (0 : ℝ) 1) := by rw [hpre]
    set N := ⌈r⌉₊ with hN
    -- the punctured strip `Ioc 0 r` is covered by the first `N` unit cells
    have hcover : {s : ℝ | ¬ g s = 0} ∩ Set.Ioc (0 : ℝ) r
        ⊆ ⋃ k ∈ Finset.range N, ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1)) := by
      rintro x ⟨hz, hx0, hxr⟩
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Ioc, Finset.mem_range,
        Set.mem_setOf_eq, exists_prop]
      have hm1 : 1 ≤ ⌈x⌉₊ := Nat.ceil_pos.mpr hx0
      have hcast : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
      have hmN : ⌈x⌉₊ ≤ N := Nat.ceil_mono hxr
      have hlt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
      have hle : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      refine ⟨⌈x⌉₊ - 1, by omega, hz, ?_, ?_⟩
      · rw [hcast]; linarith
      · rw [hcast]; linarith
    calc volume ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (0 : ℝ) r)
        ≤ volume (⋃ k ∈ Finset.range N,
            ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1))) := measure_mono hcover
      _ ≤ ∑ k ∈ Finset.range N,
            volume ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (k : ℝ) ((k : ℝ) + 1)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ _k ∈ Finset.range N, volume ({s : ℝ | ¬ g s = 0} ∩ Set.Ioc (0 : ℝ) 1) :=
          Finset.sum_congr rfl (fun k _ => htrans k)
      _ = 0 := by simp [hnull]

end ErgodicTheory
