/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionTimeOneCoeff
import ErgodicTheory.Continuous.SuspensionTimeOneParseval
import ErgodicTheory.Continuous.SuspensionFlowMP
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.NumberTheory.Real.Irrational

/-!
# Ergodicity of the time-`1` map of a constant-irrational-roof suspension

This module proves the tier-1 target of GitHub issue #35 in its **abstract, base-generic** form: the
time-`1` map of a constant-roof suspension flow over an ergodic base map with *no nontrivial
unimodular eigenvalues* is ergodic, provided the roof height `r` is a positive **irrational**.

## Statement

`ergodic_suspensionFlowMap_one_const_roof` shows that for an ergodic, measure-preserving base
`T : X ≃ᵐ X` on a probability space `(X, μ)` whose only measurable bounded eigenfunction with a
unimodular eigenvalue `≠ 1` is the zero function (`hspec`), the time-`1` map
`suspensionFlowMap T (τ ≡ r) 1` is ergodic for the invariant suspension probability measure.

## Method

Following Cornfeld–Fomin–Sinai (*Ergodic Theory*, Grundlehren 245, Ch. 11: special flows and their
spectral analysis), the proof is a **fibre-Fourier** argument on the lifted plane `X × ℝ`. Given a
time-`1`-invariant set `A`, its lifted indicator `F = 𝟙_{π⁻¹ A}` is `1`-periodic in the fibre and
satisfies the deck identity `F(Tx, s) = F(x, s + r)`. The transform window is the period of the
**invariance** (length `1`), *not* the roof `r`, so **no lap decomposition** is needed. Then:

* the fibre Fourier coefficients `cₙ(x) = ∫₀¹ e^{-2πi n s} F(x, s) ds` satisfy the twist
  `cₙ(Tx) = e^{2πi n r} cₙ(x)`; for `n ≠ 0` the eigenvalue `e^{2πi n r}` is unimodular and `≠ 1`
  (irrationality of `r`), so `hspec` forces `cₙ = 0` a.e.;
* the zero mode `c₀` is `T`-invariant, hence a.e. constant by base ergodicity;
* per fibre, a `{0,1}`-valued function with all nonzero modes vanishing is a.e. `0` or a.e. `1`
  (`fibre_indicator_dichotomy`), and the `1`-periodicity spreads the null fibre to the roof window
  `Ioc 0 r` (`measure_periodic_ae_zero_spread`);
* Fubini over the fundamental box `X × [0, r)` then yields `μ̂ A ∈ {0, 1}`.

The main content is packaged in the private key theorem `timeOne_measure_eq_zero_or_one` and the
Fubini descent lemma `suspensionMeasure_eq_zero_of_fibre_null`.
-/

open MeasureTheory Set Function Filter intervalIntegral
open scoped Real ENNReal

noncomputable section

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

/-- **Fubini descent: a fibrewise-null set descends to measure zero.** If for `μ`-a.e. base point
`x` the fibre `{s ∈ Ioc 0 r | (x, s) ∈ π⁻¹ A}` is Lebesgue-null, then the constant-roof suspension
measure of `A` vanishes. The `x`-fibre of the fundamental box `X × [0, r)` is `Ico 0 r`, which
differs from `Ioc 0 r` only on the null set `{0}`, so the Fubini integrand vanishes a.e. -/
private theorem suspensionMeasure_eq_zero_of_fibre_null
    (T : X ≃ᵐ X) (μ : Measure X) [SFinite μ] {r : ℝ}
    (hτ : Measurable (fun _ : X => r))
    (A : Set (SuspensionSpace T hτ)) (hA : MeasurableSet A)
    (hfib : ∀ᵐ x ∂μ, volume ((Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A))
        ∩ Set.Ioc (0 : ℝ) r) = 0) :
    suspensionMeasure T hτ μ A = 0 := by
  have hBmeas : MeasurableSet (suspensionMk T hτ ⁻¹' A) := (measurable_suspensionMk T hτ) hA
  have hbox : MeasurableSet (suspensionDomain (fun _ : X => r)) :=
    measurableSet_suspensionDomain hτ
  have hraw : suspensionMeasure₀ T hτ μ A
      = (μ.prod volume) ((suspensionMk T hτ ⁻¹' A) ∩ suspensionDomain (fun _ : X => r)) := by
    rw [suspensionMeasure₀, Measure.map_apply (measurable_suspensionMk T hτ) hA,
      Measure.restrict_apply hBmeas]
  have hzero : (μ.prod volume)
      ((suspensionMk T hτ ⁻¹' A) ∩ suspensionDomain (fun _ : X => r)) = 0 := by
    rw [Measure.prod_apply (hBmeas.inter hbox)]
    have haefun : (fun x => volume (Prod.mk x ⁻¹'
        ((suspensionMk T hτ ⁻¹' A) ∩ suspensionDomain (fun _ : X => r)))) =ᵐ[μ] 0 := by
      filter_upwards [hfib] with x hx
      have hfibre_eq : Prod.mk x ⁻¹'
          ((suspensionMk T hτ ⁻¹' A) ∩ suspensionDomain (fun _ : X => r))
          = (Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A)) ∩ Set.Ico (0 : ℝ) r := by
        rw [Set.preimage_inter, suspensionDomain_fiber]
      rw [Pi.zero_apply, hfibre_eq]
      have hsub : (Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A)) ∩ Set.Ico (0 : ℝ) r
          ⊆ ((Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A)) ∩ Set.Ioc (0 : ℝ) r) ∪ {(0 : ℝ)} := by
        rintro s ⟨hsB, hs0, hsr⟩
        rcases eq_or_lt_of_le hs0 with h | h
        · exact Or.inr (Set.mem_singleton_iff.mpr h.symm)
        · exact Or.inl ⟨hsB, h, hsr.le⟩
      refine le_antisymm ?_ (zero_le' )
      calc volume ((Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A)) ∩ Set.Ico (0 : ℝ) r)
          ≤ volume (((Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A)) ∩ Set.Ioc (0 : ℝ) r)
              ∪ {(0 : ℝ)}) := measure_mono hsub
        _ ≤ volume ((Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A)) ∩ Set.Ioc (0 : ℝ) r)
              + volume ({(0 : ℝ)}) := measure_union_le _ _
        _ = 0 := by rw [hx, Real.volume_singleton, add_zero]
    rw [lintegral_congr_ae haefun]; simp
  rw [suspensionMeasure, Measure.smul_apply, hraw, hzero, smul_zero]

/-- **Key zero–one law for the constant-irrational-roof time-`1` map.** For a `ζ₁`-invariant
measurable set `A`, the fibre-Fourier argument yields `μ̂ A ∈ {0, 1}`. This is the substantive core
of `ergodic_suspensionFlowMap_one_const_roof`. -/
private theorem timeOne_measure_eq_zero_or_one
    (T : X ≃ᵐ X) {r : ℝ} (hr0 : 0 < r) (hr : Irrational r)
    {μ : Measure X} [IsProbabilityMeasure μ]
    (hbase : Ergodic (⇑T) μ)
    (hspec : ∀ (g : X → ℂ) (l : ℂ), Measurable g →
      (∀ x, g (T x) = l * g x) → ‖l‖ = 1 → l ≠ 1 → g =ᵐ[μ] 0)
    (A : Set (SuspensionSpace T (measurable_const : Measurable (fun _ : X => r))))
    (hA : MeasurableSet A)
    (hinv : suspensionFlowMap T (measurable_const : Measurable (fun _ : X => r)) 1 ⁻¹' A = A) :
    suspensionMeasure T (measurable_const : Measurable (fun _ : X => r)) μ A = 0 ∨
    suspensionMeasure T (measurable_const : Measurable (fun _ : X => r)) μ A = 1 := by
  have hτ : Measurable (fun _ : X => r) := measurable_const
  -- The lifted indicator on the plane and its basic properties.
  set F : X × ℝ → ℂ := liftedIndicator T hτ A with hFdef
  have hFmeas : Measurable F := by
    simp only [hFdef]
    exact Measurable.indicator measurable_const ((measurable_suspensionMk T hτ) hA)
  have hper : ∀ (x : X) (s : ℝ), F (x, s + 1) = F (x, s) := by
    intro x s
    simp only [hFdef]
    exact lifted_indicator_periodic T hτ A hinv x s
  have htwist : ∀ (n : ℤ) (x : X),
      coeffFn F n (T x) = Complex.exp (2 * Real.pi * Complex.I * n * r) * coeffFn F n x := by
    intro n x
    simp only [hFdef]
    exact coeffFn_liftedIndicator_twist T hτ (fun _ => rfl) A hinv n x
  -- Pointwise `{0,1}`-value dictionary for the lifted indicator.
  have hF1 : ∀ (x : X) (s : ℝ), (x, s) ∈ suspensionMk T hτ ⁻¹' A → F (x, s) = 1 := by
    intro x s hin
    rw [hFdef]
    change (suspensionMk T hτ ⁻¹' A).indicator (1 : X × ℝ → ℂ) (x, s) = 1
    rw [Set.indicator_of_mem hin, Pi.one_apply]
  have hF0 : ∀ (x : X) (s : ℝ), (x, s) ∉ suspensionMk T hτ ⁻¹' A → F (x, s) = 0 := by
    intro x s hin
    rw [hFdef]
    change (suspensionMk T hτ ⁻¹' A).indicator (1 : X × ℝ → ℂ) (x, s) = 0
    rw [Set.indicator_of_notMem hin]
  have hreval : ∀ (x : X) (s : ℝ), (F (x, s)).re = 0 ∨ (F (x, s)).re = 1 := by
    intro x s
    by_cases hin : (x, s) ∈ suspensionMk T hτ ⁻¹' A
    · right; rw [hF1 x s hin]; norm_num
    · left; rw [hF0 x s hin]; norm_num
  have hgcast : ∀ (x : X) (s : ℝ), (((F (x, s)).re : ℝ) : ℂ) = F (x, s) := by
    intro x s
    by_cases hin : (x, s) ∈ suspensionMk T hτ ⁻¹' A
    · rw [hF1 x s hin]; norm_num
    · rw [hF0 x s hin]; norm_num
  have hmem1 : ∀ (x : X) (s : ℝ), (x, s) ∈ suspensionMk T hτ ⁻¹' A ↔ (F (x, s)).re = 1 := by
    intro x s
    by_cases hin : (x, s) ∈ suspensionMk T hτ ⁻¹' A
    · simp only [hin, true_iff]; rw [hF1 x s hin]; norm_num
    · simp only [hin, false_iff]; rw [hF0 x s hin]; norm_num
  have hmemA : ∀ (x : X) (s : ℝ),
      (x, s) ∈ suspensionMk T hτ ⁻¹' A ↔ ¬ ((F (x, s)).re = 0) := by
    intro x s
    rw [hmem1 x s]
    rcases hreval x s with h | h <;> rw [h] <;> norm_num
  have hmemAc : ∀ (x : X) (s : ℝ),
      (x, s) ∈ suspensionMk T hτ ⁻¹' Aᶜ ↔ ¬ ((1 - (F (x, s)).re) = 0) := by
    intro x s
    rw [Set.preimage_compl, Set.mem_compl_iff, hmem1 x s]
    rcases hreval x s with h | h <;> rw [h] <;> norm_num
  -- The nonzero Fourier modes vanish a.e. (twist eigenvalue is unimodular, `≠ 1` by irrationality).
  have hcn : ∀ n : ℤ, n ≠ 0 → coeffFn F n =ᵐ[μ] 0 := by
    intro n hn
    refine hspec (coeffFn F n) (Complex.exp (2 * Real.pi * Complex.I * n * r))
      (measurable_coeffFn hFmeas n) (fun x => htwist n x) ?_ ?_
    · rw [show (2 * Real.pi * Complex.I * (n : ℂ) * (r : ℂ) : ℂ)
          = ((2 * Real.pi * (n : ℝ) * r : ℝ) : ℂ) * Complex.I from by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    · intro hl
      rw [Complex.exp_eq_one_iff] at hl
      obtain ⟨k, hk⟩ := hl
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
      have heqc : (2 * Real.pi * Complex.I : ℂ) * ((n : ℂ) * (r : ℂ))
          = (2 * Real.pi * Complex.I : ℂ) * (k : ℂ) := by
        rw [show (2 * Real.pi * Complex.I : ℂ) * ((n : ℂ) * (r : ℂ))
              = 2 * Real.pi * Complex.I * (n : ℂ) * (r : ℂ) from by ring, hk]
        ring
      have hnrk : ((n : ℂ) * (r : ℂ)) = (k : ℂ) := mul_left_cancel₀ hne heqc
      have hnrk_real : (n : ℝ) * r = (k : ℝ) := by exact_mod_cast hnrk
      exact (Int.not_irrational k) (hnrk_real ▸ hr.intCast_mul hn)
  have hallzero : ∀ᵐ x ∂μ, ∀ n : ℤ, n ≠ 0 → coeffFn F n x = 0 := by
    rw [ae_all_iff]
    intro n
    by_cases hn : n = 0
    · exact Filter.Eventually.of_forall (fun _ hcontra => absurd hn hcontra)
    · filter_upwards [hcn n hn] with x hx
      intro _
      simpa using hx
  -- The zero mode is `∫₀¹` of the real fibre, and is `T`-invariant hence a.e. constant.
  have hc0 : ∀ x : X,
      coeffFn F 0 x = ((∫ s in (0 : ℝ)..1, (F (x, s)).re : ℝ) : ℂ) := by
    intro x
    rw [coeffFn, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [neg_zero, fourier_zero, one_smul]
    exact (hgcast x s).symm
  have hg_eq : coeffFn F 0 ∘ (⇑T) =ᵐ[μ] coeffFn F 0 :=
    Filter.Eventually.of_forall (fun x => by
      change coeffFn F 0 (T x) = coeffFn F 0 x
      have h := htwist 0 x
      simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul] at h
      exact h)
  obtain ⟨cval, hcval⟩ := hbase.ae_eq_const_of_ae_eq_comp_ae
    (measurable_coeffFn hFmeas 0).aestronglyMeasurable hg_eq
  have hcst : ∀ᵐ x ∂μ, (∫ s in (0 : ℝ)..1, (F (x, s)).re) = cval.re := by
    filter_upwards [hcval] with x hx
    have h2 : ((∫ s in (0 : ℝ)..1, (F (x, s)).re : ℝ) : ℂ) = cval := by
      rw [← hc0 x]; exact hx
    calc (∫ s in (0 : ℝ)..1, (F (x, s)).re)
        = (((∫ s in (0 : ℝ)..1, (F (x, s)).re : ℝ) : ℂ)).re := (Complex.ofReal_re _).symm
      _ = cval.re := by rw [h2]
  -- Per fibre: a `{0,1}`-valued function with vanishing nonzero modes is a.e. `0` or a.e. `1`.
  have hdich : ∀ᵐ x ∂μ,
      (∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (F (x, s)).re = 0) ∨
      (∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (F (x, s)).re = 1) := by
    filter_upwards [hallzero] with x hx
    refine fibre_indicator_dichotomy (fun s => (F (x, s)).re)
      (Complex.continuous_re.measurable.comp (hFmeas.comp measurable_prodMk_left)) ?_
      (fun s => hreval x s) ?_
    · intro s
      change (F (x, s + 1)).re = (F (x, s)).re
      rw [hper x s]
    · intro n hn
      have key : (∫ s in (0 : ℝ)..1,
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑n * ↑s)) * ((F (x, s)).re : ℂ))
          = coeffFn F n x := by
        rw [coeffFn]
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        rw [← hgcast x s, fourier_coe_apply, smul_eq_mul]
        congr 1
        congr 1
        push_cast; ring
      rw [key]; exact hx n hn
  -- The `∫₀¹` of the fibre is `0` (resp. `1`) on the a.e.-`0` (resp. a.e.-`1`) branch.
  have hint0 : ∀ x : X, (∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (F (x, s)).re = 0) →
      (∫ s in (0 : ℝ)..1, (F (x, s)).re) = 0 := by
    intro x hae
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact integral_eq_zero_of_ae hae
  have hint1 : ∀ x : X, (∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (F (x, s)).re = 1) →
      (∫ s in (0 : ℝ)..1, (F (x, s)).re) = 1 := by
    intro x hae
    have hae' : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc (0 : ℝ) 1 → (F (x, s)).re = 1 := by
      rw [Set.uIoc_of_le zero_le_one]
      exact (ae_restrict_iff' measurableSet_Ioc).mp hae
    rw [intervalIntegral.integral_congr_ae hae', intervalIntegral.integral_const]
    norm_num
  -- The a.e.-constant value `cval.re` is `0` or `1` (evaluate at any generic base point).
  obtain ⟨x0, hx0d, hx0c⟩ := (hdich.and hcst).exists
  have hkap : cval.re = 0 ∨ cval.re = 1 := by
    rcases hx0d with h | h
    · left; rw [← hx0c]; exact hint0 x0 h
    · right; rw [← hx0c]; exact hint1 x0 h
  haveI hprob : IsProbabilityMeasure (suspensionMeasure T hτ μ) :=
    isProbabilityMeasure_suspensionMeasure T hτ μ (fun _ => hr0.le) (integrable_const r) (by
      have hv : (∫ x, (fun _ : X => r) x ∂μ) = r := by simp
      rw [hv]; exact hr0)
  rcases hkap with hk0 | hk1
  · -- `cval.re = 0`: every fibre is a.e. `0`, so `A` is null.
    left
    refine suspensionMeasure_eq_zero_of_fibre_null T μ hτ A hA ?_
    filter_upwards [hdich, hcst] with x hxd hxc
    have hE0 : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (F (x, s)).re = 0 := by
      rcases hxd with h | h
      · exact h
      · exfalso
        have hcontra : (1 : ℝ) = 0 := by rw [← hint1 x h, hxc]; exact hk0
        exact one_ne_zero hcontra
    have hper_x : ∀ s : ℝ, (F (x, s + 1)).re = (F (x, s)).re := fun s => by rw [hper x s]
    have hspread := measure_periodic_ae_zero_spread (g := fun s => (F (x, s)).re) hper_x hE0 r
    rw [ae_iff, Measure.restrict_apply' measurableSet_Ioc] at hspread
    have hset : (Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' A)) ∩ Set.Ioc (0 : ℝ) r
        = {s | ¬ ((F (x, s)).re = 0)} ∩ Set.Ioc (0 : ℝ) r := by
      ext s
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(hmemA x s).mp h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨(hmemA x s).mpr h1, h2⟩
    rw [hset]; exact hspread
  · -- `cval.re = 1`: every fibre is a.e. `1`, so `Aᶜ` is null, hence `A` is conull.
    right
    have h0c : suspensionMeasure T hτ μ Aᶜ = 0 := by
      refine suspensionMeasure_eq_zero_of_fibre_null T μ hτ Aᶜ hA.compl ?_
      filter_upwards [hdich, hcst] with x hxd hxc
      have hE1 : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (F (x, s)).re = 1 := by
        rcases hxd with h | h
        · exfalso
          have hcontra : (0 : ℝ) = 1 := by rw [← hint0 x h, hxc]; exact hk1
          exact zero_ne_one hcontra
        · exact h
      have hE1' : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), 1 - (F (x, s)).re = 0 := by
        filter_upwards [hE1] with s hs; rw [hs]; ring
      have hper1 : ∀ s : ℝ, 1 - (F (x, s + 1)).re = 1 - (F (x, s)).re :=
        fun s => by rw [hper x s]
      have hspread :=
        measure_periodic_ae_zero_spread (g := fun s => 1 - (F (x, s)).re) hper1 hE1' r
      rw [ae_iff, Measure.restrict_apply' measurableSet_Ioc] at hspread
      have hset : (Prod.mk x ⁻¹' (suspensionMk T hτ ⁻¹' Aᶜ)) ∩ Set.Ioc (0 : ℝ) r
          = {s | ¬ (1 - (F (x, s)).re = 0)} ∩ Set.Ioc (0 : ℝ) r := by
        ext s
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨(hmemAc x s).mp h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨(hmemAc x s).mpr h1, h2⟩
      rw [hset]; exact hspread
    calc suspensionMeasure T hτ μ A
        = suspensionMeasure T hτ μ (Aᶜ)ᶜ := by rw [compl_compl]
      _ = suspensionMeasure T hτ μ univ - suspensionMeasure T hτ μ Aᶜ :=
          measure_compl hA.compl (measure_ne_top _ _)
      _ = 1 := by rw [measure_univ, h0c, tsub_zero]

/-- **Ergodicity of the time-`1` map of a constant-irrational-roof suspension flow** (issue #35,
tier 1, abstract base-generic form).

Let `T : X ≃ᵐ X` be an ergodic, measure-preserving map of a probability space `(X, μ)` whose only
measurable eigenfunction with a unimodular eigenvalue `≠ 1` is `0` (`hspec` — supplied in the
Bernoulli case by the mixing eigenfunction rigidity `eigenfunction_ae_zero_of_mixing`). For a
positive **irrational** roof height `r`, the time-`1` map of the constant-roof suspension flow is
ergodic for the invariant suspension probability measure.

The transform window in the fibre-Fourier proof is the invariance period `1`, not the roof `r`, so
no lap decomposition is needed (Cornfeld–Fomin–Sinai, special flows). -/
theorem ergodic_suspensionFlowMap_one_const_roof
    (T : X ≃ᵐ X) {r : ℝ} (hr0 : 0 < r) (hr : Irrational r)
    {μ : Measure X} [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hbase : Ergodic (⇑T) μ)
    (hspec : ∀ (g : X → ℂ) (l : ℂ), Measurable g →
      (∀ x, g (T x) = l * g x) → ‖l‖ = 1 → l ≠ 1 → g =ᵐ[μ] 0) :
    Ergodic (suspensionFlowMap T (measurable_const : Measurable (fun _ : X => r)) 1)
      (suspensionMeasure T (measurable_const : Measurable (fun _ : X => r)) μ) := by
  have hτ : Measurable (fun _ : X => r) := measurable_const
  change Ergodic (suspensionFlowMap T hτ 1) (suspensionMeasure T hτ μ)
  haveI hprob : IsProbabilityMeasure (suspensionMeasure T hτ μ) :=
    isProbabilityMeasure_suspensionMeasure T hτ μ (fun _ => hr0.le) (integrable_const r) (by
      have hv : (∫ x, (fun _ : X => r) x ∂μ) = r := by simp
      rw [hv]; exact hr0)
  exact {
    toMeasurePreserving :=
      measurePreserving_suspensionFlowMap T hτ hT (c := r) (fun _ => le_rfl) hr0 1
    aeconst_set := fun A hA hinv => by
      rw [eventuallyConst_set']
      rcases timeOne_measure_eq_zero_or_one T hr0 hr hbase hspec A hA hinv with h0 | h1
      · exact Or.inl (ae_eq_empty.mpr h0)
      · exact Or.inr (ae_eq_univ.mpr (by
          rw [measure_compl hA (measure_ne_top _ _), measure_univ, h1, tsub_self])) }

end ErgodicTheory
