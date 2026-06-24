/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.SMBSharp
import Oseledets.Ergodic.Birkhoff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Pointwise Shannon–McMillan–Breiman: the main (Birkhoff) term

This file carries the **pointwise** Shannon–McMillan–Breiman theorem past the integral-level
rate identity `ksEntropyPartition_eq_condEntropy_iSup` (proved in `SMBSharp`) towards the a.e.
limit `(1/n)·iₙ(x) → h(P,T)` for an ergodic measure-preserving `T`.

The Breiman split of the information function `iₙ(x) = ∑_{j<n} g_{n-j}(Tʲx)` is compared with the
Birkhoff sum of the **limit conditional information function**
`g∞(x) = ∑ᵢ 𝟙_{Pᵢ}(x) · (-log μ⟦Pᵢ | 𝒞∞⟧(x))`,
where `𝒞∞ = ⨆ₖ σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP))` is the strict-future σ-algebra (the conditioning σ-algebra of
the sharp rate identity).  This file establishes the **R3/R4 a.e. main term**:

* `condInfoFun` — the conditional information function `g𝒜(x) = ∑ᵢ 𝟙_{Pᵢ}(x)·(-log μ⟦Pᵢ|𝒜⟧(x))`,
  with its measurability (`measurable_condInfoFun`), nonnegativity (`condInfoFun_nonneg`), and the
  **keystone integral identity** `integral_condInfoFun_eq_condEntropy : ∫ g𝒜 = H(P | 𝒜)`.
* `integrable_condInfoFun` — `g𝒜 ∈ L¹(μ)` (its integral is the finite `H(P|𝒜)`, and it is `≥ 0`).
* `integral_condInfoFun_iSup_eq` — `∫ g∞ = h(P,T)`, identifying the Birkhoff target as the sharp KS
  rate (via `ksEntropyPartition_eq_condEntropy_iSup`).
* `ae_tendsto_birkhoffAverage_condInfoFun_iSup` — **R4**: for ergodic `T`, the Birkhoff averages of
  `g∞` converge a.e. to `∫ g∞ = h(P,T)`.

The keystone integral identity is the per-cell **pull-out** `∫ 𝟙_{Pᵢ}·(-log pᵢ) = ∫ negMulLog pᵢ`
where `pᵢ = μ⟦Pᵢ | 𝒜⟧`: since `-log pᵢ` is `𝒜`-measurable (a function of the conditional kernel),
replacing `𝟙_{Pᵢ}` by its `𝒜`-conditional expectation `pᵢ` leaves the integral unchanged
(`condExp_stronglyMeasurable_mul_of_bound`), and `negMulLog pᵢ = pᵢ·(-log pᵢ)`.  The unboundedness
of `-log` at `pᵢ = 0` is handled by a monotone truncation `hₘ = min(-log pᵢ, M)`:
`∫ 𝟙_{Pᵢ}·hₘ = ∫ pᵢ·hₘ` for each `M`, and both sides increase to the (finite, by
`negMulLog ≤ e⁻¹`) limit by monotone convergence in `lintegral`.

## References

* L. Breiman, *The individual ergodic theorem of information theory*, Ann. Math. Statist.
  **28** (1957), 809–811; correction **31** (1960), 809–810.
* K. L. Chung, *A note on the ergodic theorem of information theory*, Ann. Math. Statist.
  **32** (1961), 612–614.
* M. Einsiedler, E. Lindenstrauss, T. Ward, *Entropy in Ergodic Theory and Topological Dynamics*,
  Ch. 2 (SMB).
-/

open MeasureTheory Filter Topology Real Function ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Krieger

open Oseledets.Entropy

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α] [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

/-- The **conditional information function** of the finite partition `P` given the sub-σ-algebra
`𝒜`: `g𝒜(x) = ∑ᵢ 𝟙_{Pᵢ}(x)·(-log μ⟦Pᵢ | 𝒜⟧(x))`, the surprise of learning a point's `P`-cell once
the information in `𝒜` is known.  Here `μ⟦Pᵢ | 𝒜⟧(x)` is realized by the regular conditional
probability `(condExpKernel μ 𝒜 x) (Pᵢ)`.  Exactly one indicator survives at each `x` (the one for
its own cell), so `g𝒜` is the pointwise limit, as `𝒜 ↑ 𝒞∞`, of the per-step information functions
in the Breiman telescoping. -/
noncomputable def condInfoFun (P : MeasurePartition μ ι) (x : α) : ℝ :=
  ∑ i, (P.cells i).indicator
    (fun y => -Real.log (@condExpKernel α mα _ μ _ 𝒜 y (P.cells i)).toReal) x

section CondProb

/-- The conditional kernel mass `pᵢ(x) = (condExpKernel μ 𝒜 x (Pᵢ)).toReal` as a function of `x`. -/
private noncomputable def condProb (A : Set α) (x : α) : ℝ :=
  (@condExpKernel α mα _ μ _ 𝒜 x A).toReal

private lemma condProb_nonneg (A : Set α) (x : α) : 0 ≤ condProb (μ := μ) (𝒜 := 𝒜) A x :=
  ENNReal.toReal_nonneg

private lemma condProb_le_one (A : Set α) (x : α) : condProb (μ := μ) (𝒜 := 𝒜) A x ≤ 1 :=
  toReal_condExpKernel_le_one A x

private lemma measurable_condProb (h𝒜 : 𝒜 ≤ mα) {A : Set α} (hA : MeasurableSet A) :
    Measurable (condProb (μ := μ) (𝒜 := 𝒜) A) :=
  ((measurable_condExpKernel hA).mono h𝒜 le_rfl).ennreal_toReal

private lemma stronglyMeasurable_condProb {A : Set α} (hA : MeasurableSet A) :
    StronglyMeasurable[𝒜] (condProb (μ := μ) (𝒜 := 𝒜) A) :=
  (measurable_condExpKernel hA).ennreal_toReal.stronglyMeasurable

/-- The `𝒜`-conditional probability `pᵢ = (condExpKernel μ 𝒜 · Pᵢ).toReal` is a.e. equal to the
conditional expectation of the indicator `𝟙_{Pᵢ}`. -/
private lemma condProb_ae_eq_condExp_indicator (h𝒜 : 𝒜 ≤ mα) {A : Set α} (hA : MeasurableSet A) :
    condProb (μ := μ) (𝒜 := 𝒜) A =ᵐ[μ] μ[A.indicator (fun _ => (1 : ℝ)) | 𝒜] := by
  have h := condExpKernel_ae_eq_condExp (μ := μ) (m := 𝒜) h𝒜 hA
  simpa only [condProb, measureReal_def] using h

/-- **The per-cell pull-out identity (keystone).** For a cell `A` and conditional kernel mass
`pᵢ = (condExpKernel μ 𝒜 · A).toReal`, the `𝟙_A`-weighted information `∫ 𝟙_A·(-log pᵢ)` equals the
entropy integrand `∫ negMulLog pᵢ`.  Both equal `∫ pᵢ·(-log pᵢ)`: replacing `𝟙_A` by its
`𝒜`-conditional expectation `pᵢ` leaves the integral fixed (pull-out, as `-log pᵢ` is
`𝒜`-measurable), and `negMulLog pᵢ = pᵢ·(-log pᵢ)`.  Unboundedness of `-log` at `pᵢ = 0` is handled
by the truncation `hₘ = min(-log pᵢ, M)`: `∫ 𝟙_A·hₘ = ∫ pᵢ·hₘ` per `M`, and both sides increase
monotonically to the respective limits (finite, since `negMulLog pᵢ ≤ 1` on `[0,1]`).  The proof
yields the value identity together with the `lintegral` finiteness `hlint_fin` used for
integrability. -/
private lemma indicator_neg_log_lintegral_eq (h𝒜 : 𝒜 ≤ mα) {A : Set α} (hA : MeasurableSet A) :
    (∫ x, A.indicator (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) A y)) x ∂μ
        = ∫ x, Real.negMulLog (condProb (μ := μ) (𝒜 := 𝒜) A x) ∂μ)
      ∧ ∫⁻ x, ENNReal.ofReal
          (A.indicator (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) A y)) x) ∂μ
        = ENNReal.ofReal (∫ x, Real.negMulLog (condProb (μ := μ) (𝒜 := 𝒜) A x) ∂μ) := by
  set p : α → ℝ := condProb (μ := μ) (𝒜 := 𝒜) A with hp
  have hp_nonneg : ∀ x, 0 ≤ p x := condProb_nonneg A
  have hp_le_one : ∀ x, p x ≤ 1 := condProb_le_one A
  have hp_meas : StronglyMeasurable[𝒜] p := stronglyMeasurable_condProb hA
  have hp_meas' : Measurable p := measurable_condProb h𝒜 hA
  -- `ℓ x = -log (p x) ≥ 0`, `𝒜`-measurable. Truncations `hₘ = min ℓ M`.
  set ℓ : α → ℝ := fun x => -Real.log (p x) with hℓ
  have hℓ_nonneg : ∀ x, 0 ≤ ℓ x := fun x =>
    neg_nonneg.mpr (Real.log_nonpos (hp_nonneg x) (hp_le_one x))
  have hℓ_meas𝒜 : Measurable[𝒜] ℓ := (Real.measurable_log.comp hp_meas.measurable).neg
  have hℓ_meas' : Measurable ℓ := (Real.measurable_log.comp hp_meas').neg
  set trunc : ℕ → α → ℝ := fun M x => min (ℓ x) (M : ℝ) with htrunc
  have htrunc_meas : ∀ M, StronglyMeasurable[𝒜] (trunc M) := fun M =>
    (hℓ_meas𝒜.min measurable_const).stronglyMeasurable
  have htrunc_bound : ∀ M, ∀ x, ‖trunc M x‖ ≤ (M : ℝ) := fun M x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hℓ_nonneg x) (Nat.cast_nonneg M))]
    exact min_le_right _ _
  have htrunc_nonneg : ∀ M x, 0 ≤ trunc M x := fun M x =>
    le_min (hℓ_nonneg x) (Nat.cast_nonneg M)
  -- Indicator of `A` (integrable: bounded by 1 on a probability space).
  have hind_int : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  -- The pull-out at each truncation level `M`: `∫ 𝟙_A·(trunc M) = ∫ p·(trunc M)`.
  have hpullM : ∀ M, ∫ x, A.indicator (fun y => trunc M y) x ∂μ
      = ∫ x, p x * trunc M x ∂μ := by
    intro M
    have hindeq : (fun x => A.indicator (fun y => trunc M y) x)
        = fun x => trunc M x * A.indicator (fun _ => (1 : ℝ)) x := by
      funext x
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hindeq]
    have hpull : μ[(fun x => trunc M x * A.indicator (fun _ => (1 : ℝ)) x) | 𝒜]
        =ᵐ[μ] fun x => trunc M x * (μ[A.indicator (fun _ => (1 : ℝ)) | 𝒜]) x := by
      have := condExp_stronglyMeasurable_mul_of_bound h𝒜 (f := trunc M)
        (g := A.indicator (fun _ => (1 : ℝ))) (htrunc_meas M) hind_int (M : ℝ)
        (Eventually.of_forall (htrunc_bound M))
      simpa [Pi.mul_apply] using this
    have hpeq : (μ[A.indicator (fun _ => (1 : ℝ)) | 𝒜]) =ᵐ[μ] p :=
      (condProb_ae_eq_condExp_indicator h𝒜 hA).symm
    rw [← integral_condExp h𝒜, integral_congr_ae hpull]
    refine integral_congr_ae ?_
    filter_upwards [hpeq] with x hx
    rw [hx, mul_comm]
  -- `negMulLog p` is bounded (by `1`), measurable, hence integrable; `p·(trunc M) ↑ negMulLog p`.
  have hnegMulLog_eq : ∀ x, Real.negMulLog (p x) = p x * ℓ x := fun x => by
    rw [Real.negMulLog, hℓ]; ring
  have hRHS_int : Integrable (fun x => Real.negMulLog (p x)) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      (Real.continuous_negMulLog.comp_stronglyMeasurable
        (hp_meas.mono h𝒜)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg (hp_nonneg x) (hp_le_one x))]
    calc Real.negMulLog (p x) ≤ 1 - p x := Real.negMulLog_le_one_sub_self (hp_nonneg x)
      _ ≤ 1 := by linarith [hp_nonneg x]
  have hRHS_int' : ∀ M, Integrable (fun x => p x * trunc M x) μ := by
    intro M
    refine (integrable_const (1 : ℝ)).mono'
      (hp_meas'.aestronglyMeasurable.mul
        (hℓ_meas'.min measurable_const).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp_nonneg x) (htrunc_nonneg M x))]
    calc p x * trunc M x ≤ p x * ℓ x :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (hp_nonneg x)
      _ = Real.negMulLog (p x) := (hnegMulLog_eq x).symm
      _ ≤ 1 := by
          calc Real.negMulLog (p x) ≤ 1 - p x := Real.negMulLog_le_one_sub_self (hp_nonneg x)
            _ ≤ 1 := by linarith [hp_nonneg x]
  -- RHS limit: `∫ p·(trunc M) → ∫ negMulLog p` by monotone convergence.
  have hRHS_tendsto : Tendsto (fun M => ∫ x, p x * trunc M x ∂μ) atTop
      (𝓝 (∫ x, Real.negMulLog (p x) ∂μ)) := by
    refine integral_tendsto_of_tendsto_of_monotone hRHS_int' hRHS_int
      (Eventually.of_forall fun x M N hMN => ?_) (Eventually.of_forall fun x => ?_)
    · exact mul_le_mul_of_nonneg_left (min_le_min_left _ (by exact_mod_cast hMN)) (hp_nonneg x)
    · rw [hnegMulLog_eq x]
      refine Tendsto.const_mul (p x) ?_
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈ℓ x⌉₊) fun M hM => ?_
      change min (ℓ x) (M : ℝ) = ℓ x
      exact min_eq_left ((Nat.le_ceil (ℓ x)).trans (by exact_mod_cast hM))
  -- Therefore `∫ 𝟙_A·(trunc M) → ∫ negMulLog p` too (via the per-level pull-out).
  have hLHS_tendsto : Tendsto (fun M => ∫ x, A.indicator (fun y => trunc M y) x ∂μ) atTop
      (𝓝 (∫ x, Real.negMulLog (p x) ∂μ)) := by
    simp_rw [hpullM]; exact hRHS_tendsto
  have hLHS_indmeas : Measurable (fun x => A.indicator (fun y => ℓ y) x) := hℓ_meas'.indicator hA
  have hLHS_nonneg : ∀ x, 0 ≤ A.indicator (fun y => ℓ y) x := fun x =>
    Set.indicator_nonneg (fun y _ => hℓ_nonneg y) x
  -- ENNReal-valued truncated integrands `Fₘ = ofReal (𝟙_A·trunc M)`, monotone, → `ofReal (𝟙_A·ℓ)`.
  set F : ℕ → α → ℝ≥0∞ := fun M x => ENNReal.ofReal (A.indicator (fun y => trunc M y) x) with hF
  have hF_meas : ∀ M, Measurable (F M) :=
    fun M => ((hℓ_meas'.min measurable_const).indicator hA).ennreal_ofReal
  have hF_mono : ∀ x, Monotone fun M => F M x := by
    intro x M N hMN
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      exact min_le_min_left _ (by exact_mod_cast hMN)
    · simp [Set.indicator_of_notMem hx]
  have hF_tendsto : ∀ x, Tendsto (fun M => F M x) atTop
      (𝓝 (ENNReal.ofReal (A.indicator (fun y => ℓ y) x))) := by
    intro x
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈ℓ x⌉₊) fun M hM => ?_
      change min (ℓ x) (M : ℝ) = ℓ x
      exact min_eq_left ((Nat.le_ceil (ℓ x)).trans (by exact_mod_cast hM))
    · simp only [Set.indicator_of_notMem hx]; exact tendsto_const_nhds
  -- `∫⁻ Fₘ → ∫⁻ ofReal(𝟙_A·ℓ)` by ENNReal monotone convergence.
  have hlint_lim : Tendsto (fun M => ∫⁻ x, F M x ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (A.indicator (fun y => ℓ y) x) ∂μ)) :=
    lintegral_tendsto_of_tendsto_of_monotone (fun M => (hF_meas M).aemeasurable)
      (Eventually.of_forall hF_mono) (Eventually.of_forall hF_tendsto)
  -- Each `∫⁻ Fₘ = ofReal (∫ 𝟙_A·trunc M)`; and `∫ 𝟙_A·trunc M → ∫ negMulLog p` (`hLHS_tendsto`).
  have hlint_level : ∀ M, ∫⁻ x, F M x ∂μ
      = ENNReal.ofReal (∫ x, A.indicator (fun y => trunc M y) x ∂μ) := by
    intro M
    rw [hF, ← ofReal_integral_eq_lintegral_ofReal]
    · exact (Integrable.indicator ((integrable_const (M : ℝ)).mono'
        ((htrunc_meas M).mono h𝒜).aestronglyMeasurable (Eventually.of_forall (htrunc_bound M))) hA)
    · exact Eventually.of_forall fun x => Set.indicator_nonneg (fun y _ => htrunc_nonneg M y) x
  have hlint_lim2 : Tendsto (fun M => ∫⁻ x, F M x ∂μ) atTop
      (𝓝 (ENNReal.ofReal (∫ x, Real.negMulLog (p x) ∂μ))) := by
    simp_rw [hlint_level]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hLHS_tendsto
  have hlint_fin : ∫⁻ x, ENNReal.ofReal (A.indicator (fun y => ℓ y) x) ∂μ
      = ENNReal.ofReal (∫ x, Real.negMulLog (p x) ∂μ) :=
    tendsto_nhds_unique hlint_lim hlint_lim2
  have hLHS_val : ∫ x, A.indicator (fun y => ℓ y) x ∂μ = ∫ x, Real.negMulLog (p x) ∂μ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hLHS_nonneg)
      hLHS_indmeas.aestronglyMeasurable, hlint_fin,
      ENNReal.toReal_ofReal (integral_nonneg fun x =>
        Real.negMulLog_nonneg (hp_nonneg x) (hp_le_one x))]
  exact ⟨hLHS_val, hlint_fin⟩

/-- The per-cell `𝟙_A`-weighted information `𝟙_A·(-log pᵢ)` is `μ`-integrable: nonnegative,
measurable, and its `lintegral` is `ofReal (∫ negMulLog pᵢ) < ∞` (the `lintegral` half of the
keystone). -/
private lemma integrable_indicator_condInfo (h𝒜 : 𝒜 ≤ mα) {A : Set α} (hA : MeasurableSet A) :
    Integrable (A.indicator (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) A y))) μ := by
  have hmeas : Measurable (A.indicator (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) A y))) :=
    ((Real.measurable_log.comp (measurable_condProb h𝒜 hA)).neg).indicator hA
  have hnonneg : ∀ x, 0 ≤ A.indicator (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) A y)) x :=
    fun x => Set.indicator_nonneg
      (fun y _ => neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg (condProb_le_one A y))) x
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnonneg),
    (indicator_neg_log_lintegral_eq h𝒜 hA).2]
  exact ENNReal.ofReal_lt_top

/-- **Per-cell pull-out (value form).** `∫ 𝟙_A·(-log pᵢ) = ∫ negMulLog pᵢ`. -/
private lemma integral_indicator_neg_log_eq_integral_negMulLog (h𝒜 : 𝒜 ≤ mα) {A : Set α}
    (hA : MeasurableSet A) :
    ∫ x, A.indicator (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) A y)) x ∂μ
      = ∫ x, Real.negMulLog (condProb (μ := μ) (𝒜 := 𝒜) A x) ∂μ :=
  (indicator_neg_log_lintegral_eq h𝒜 hA).1

end CondProb

section Properties

/-- The conditional information function is measurable: a finite sum of indicators of measurable
cells, each weighted by the measurable function `x ↦ -log(condExpKernel μ 𝒜 x (Pᵢ)).toReal`. -/
lemma measurable_condInfoFun (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    Measurable (condInfoFun (𝒜 := 𝒜) P) := by
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  refine Measurable.indicator ?_ (P.measurable i)
  exact (Real.measurable_log.comp
    ((measurable_condExpKernel (P.measurable i)).mono h𝒜 le_rfl).ennreal_toReal).neg

/-- The conditional information function is nonnegative: each indicator term is `𝟙_{Pᵢ}·(-log pᵢ)`
with `pᵢ ∈ [0,1]`, so `-log pᵢ ≥ 0`. -/
lemma condInfoFun_nonneg (P : MeasurePartition μ ι) (x : α) : 0 ≤ condInfoFun (𝒜 := 𝒜) P x := by
  refine Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun y _ => ?_) x
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg (condProb_le_one (P.cells i) y))

/-- **The keystone integral identity.** The conditional information function of `P` given `𝒜`
integrates to the conditional Shannon entropy `H(P | 𝒜)`:
`∫ condInfoFun 𝒜 P = condEntropy μ 𝒜 P.cells`.

Summing the per-cell pull-out `integral_indicator_neg_log_eq_integral_negMulLog` over the finite
index recovers exactly the `condEntropy` integrand `∑ᵢ negMulLog(condExpKernel μ 𝒜 · Pᵢ).toReal`. -/
theorem integral_condInfoFun_eq_condEntropy (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    ∫ x, condInfoFun (𝒜 := 𝒜) P x ∂μ = condEntropy μ 𝒜 P.cells := by
  classical
  have hterm_int : ∀ i, Integrable
      ((P.cells i).indicator (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) (P.cells i) y))) μ :=
    fun i => integrable_indicator_condInfo h𝒜 (P.measurable i)
  have hcif : (fun x => condInfoFun (𝒜 := 𝒜) P x)
      = fun x => ∑ i, (P.cells i).indicator
          (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) (P.cells i) y)) x := rfl
  rw [hcif, integral_finsetSum _ (fun i _ => hterm_int i),
    condEntropy_def, integral_finsetSum _
      (fun i _ => integrable_negMulLog_condExpKernel h𝒜 (P.measurable i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_indicator_neg_log_eq_integral_negMulLog h𝒜 (P.measurable i)

/-- The conditional information function is `μ`-integrable: a finite sum of the integrable per-cell
weighted indicators. -/
lemma integrable_condInfoFun (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    Integrable (condInfoFun (𝒜 := 𝒜) P) μ := by
  have hcif : (condInfoFun (𝒜 := 𝒜) P)
      = fun x => ∑ i, (P.cells i).indicator
          (fun y => -Real.log (condProb (μ := μ) (𝒜 := 𝒜) (P.cells i) y)) x := rfl
  rw [hcif]
  exact integrable_finsetSum _ (fun i _ => integrable_indicator_condInfo h𝒜 (P.measurable i))

end Properties

section BirkhoffMainTerm

variable [Nonempty ι]

/-- The strict-future conditioning σ-algebra `𝒞∞ = ⨆ₖ σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP))` of the sharp SMB rate. -/
@[reducible]
noncomputable def futureSigma (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    MeasurableSpace α :=
  ⨆ k, generatedSigmaAlgebra μ ((ksJoin hT P k).pullback hT)

omit [StandardBorelSpace α] [IsProbabilityMeasure μ] [Nonempty ι] in
lemma futureSigma_le (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    futureSigma hT P ≤ mα :=
  iSup_le fun _ => generatedSigmaAlgebra_le _

/-- **The Birkhoff target equals the sharp KS rate.** The limit conditional information function
`g∞ = condInfoFun 𝒞∞ P` integrates to the Kolmogorov–Sinai entropy `h(P,T)`:
`∫ g∞ = condEntropy μ 𝒞∞ P.cells = ksEntropyPartition hT P`.
Combines the keystone identity with `ksEntropyPartition_eq_condEntropy_iSup`. -/
theorem integral_condInfoFun_futureSigma_eq (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) :
    ∫ x, condInfoFun (𝒜 := futureSigma hT P) P x ∂μ = ksEntropyPartition hT P := by
  rw [integral_condInfoFun_eq_condEntropy (futureSigma_le hT P) P, futureSigma,
    ← ksEntropyPartition_eq_condEntropy_iSup hT P]

/-- **R4: the Birkhoff main term converges a.e. to `h(P,T)`.** For an *ergodic* measure-preserving
`T`, the Birkhoff averages of the limit conditional information function `g∞ = condInfoFun 𝒞∞ P`
converge `μ`-a.e. to `∫ g∞ = ksEntropyPartition hT P`.  This is the pointwise ergodic theorem
(`tendsto_birkhoffAverage_ae_integral`) applied to the integrable `g∞`
(`integrable_condInfoFun`), with the integral value supplied by
`integral_condInfoFun_futureSigma_eq`. -/
theorem ae_tendsto_birkhoffAverage_condInfoFun_futureSigma (hT : Ergodic T μ)
    (P : MeasurePartition μ ι) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n => birkhoffAverage ℝ T
        (condInfoFun (𝒜 := futureSigma hT.toMeasurePreserving P) P) n x)
      atTop (𝓝 (ksEntropyPartition hT.toMeasurePreserving P)) := by
  have hmp := hT.toMeasurePreserving
  have hint : Integrable (condInfoFun (𝒜 := futureSigma hmp P) P) μ :=
    integrable_condInfoFun (futureSigma_le hmp P) P
  have hbirk := tendsto_birkhoffAverage_ae_integral hT hint
  filter_upwards [hbirk] with x hx
  rwa [integral_condInfoFun_futureSigma_eq hmp P] at hx

end BirkhoffMainTerm

section ChungDomination

/-! ### R5: Chung's `L¹` maximal domination

The Cesàro tail `(1/n)∑_{j<n}(g_{n-j} − g∞)(Tʲx) → 0` of the Breiman split is killed by the **Chung
maximal function** `g* = ⨆ₖ gₖ`, where `gₖ = condInfoFun (𝒞ₖ) P` and
`𝒞ₖ = σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP))` is the increasing conditioning family.  The genuinely analytic content
is `g* ∈ L¹(μ)`, which follows from the **per-cell stopping-time tail estimate**
`μ{x ∈ Pᵢ : g* x > λ} ≤ e^{−λ}` (Chung 1961) and the layer-cake formula, giving
`∫ g* ≤ H(P) + 1`.

This section delivers:
* `condLevelSigma`, `condInfoMaxFun` — the conditioning family and the (`ℝ≥0∞`-valued) maximal
  function, with measurability (`measurable_condInfoMaxFun`).
* `lintegral_min_meas_exp_le` — the per-cell layer-cake estimate
  `∫⁻_{(0,∞)} min(μ Pᵢ, e^{−t}) dt ≤ ofReal(negMulLog (μ Pᵢ).toReal) + μ Pᵢ`.
* `lintegral_condInfoMaxFun_le_of_layer` — **the R5 `L¹` bound**, sorry-free *given* the per-cell
  tail hypothesis `chungTail`: `∫⁻ g* ≤ ofReal (entropy μ P.cells) + 1`.

The two named residual leaves (the precise missing Mathlib pieces) are:
* `chungTail` — the Doob stopping-time tail `μ{x ∈ Pᵢ : λ < g* x} ≤ ofReal e^{−λ}` (a Markov bound
  on the conditional-probability martingale `pₖ = μ⟦Pᵢ | 𝒞ₖ⟧`, on the stopping time
  `τ = inf{k : pₖ < e^{−λ}}`); and
* the **Maker/Breiman dominated-Cesàro** step `(1/n)∑_{j<n}(g_{n-j} − g∞)(Tʲ·) → 0` a.e. from
  `g* ∈ L¹` and `gₖ → g∞` a.e. (not in Mathlib).
-/

/-- The `k`-th conditioning σ-algebra `𝒞ₖ = σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP))` of the Breiman telescoping. -/
@[reducible]
noncomputable def condLevelSigma (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (k : ℕ) : MeasurableSpace α :=
  generatedSigmaAlgebra μ ((ksJoin hT P k).pullback hT)

omit [StandardBorelSpace α] [IsProbabilityMeasure μ] in
lemma condLevelSigma_le (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (k : ℕ) :
    condLevelSigma hT P k ≤ mα :=
  generatedSigmaAlgebra_le _

/-- **The Chung maximal information function** `g* x = ⨆ₖ ofReal (gₖ x)` (in `ℝ≥0∞`), where
`gₖ = condInfoFun (𝒞ₖ) P`.  Working in `ℝ≥0∞` makes the supremum total (it may be `∞`) and feeds
the layer-cake formula directly. -/
noncomputable def condInfoMaxFun (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (x : α) : ℝ≥0∞ :=
  ⨆ k, ENNReal.ofReal (condInfoFun (𝒜 := condLevelSigma hT P k) P x)

/-- The maximal information function is measurable: a countable supremum of the measurable
`ofReal ∘ gₖ`. -/
lemma measurable_condInfoMaxFun (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    Measurable (condInfoMaxFun hT P) :=
  Measurable.iSup fun k =>
    (measurable_condInfoFun (condLevelSigma_le hT P k) P).ennreal_ofReal

/-- **Per-cell layer-cake estimate.** For a measure `a ∈ [0,1]`, the layer-cake integrand
`min(a, e^{−t})` over `(0,∞)` integrates to at most `negMulLog a + a` (equality for `a ∈ (0,1]`).
This is the `1`-D real-analysis core of the Chung bound `∫ g* ≤ H(P) + 1`: split `(0,∞)` at
`c = −log a`, where `min = a` below `c` (contributing `a·(−log a) = negMulLog a`) and `min = e^{−t}`
above (contributing `e^{−c} = a`). -/
lemma lintegral_min_meas_exp_le (a : ℝ≥0∞) (ha : a ≤ 1) :
    ∫⁻ t in Set.Ioi (0 : ℝ), min a (ENNReal.ofReal (Real.exp (-t)))
      ≤ ENNReal.ofReal (Real.negMulLog a.toReal) + a := by
  -- Abbreviate the real value `ar = a.toReal ∈ [0,1]` and the split point `c = -log ar`.
  set ar : ℝ := a.toReal with har
  have har_nonneg : 0 ≤ ar := ENNReal.toReal_nonneg
  have har_le_one : ar ≤ 1 := by
    rw [har]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ha)
  rcases eq_or_lt_of_le har_nonneg with haz | hapos
  · -- `a = 0`: the `min` is `0`, both sides `0` / `≥ 0`.
    have ha0 : a = 0 := by
      have hz : a.toReal = 0 := haz.symm
      rcases (ENNReal.toReal_eq_zero_iff a).mp hz with h | h
      · exact h
      · exact absurd h (by simpa using (lt_of_le_of_lt ha ENNReal.one_lt_top).ne)
    rw [ha0]
    have hz0 : ∫⁻ t in Set.Ioi (0:ℝ), min (0 : ℝ≥0∞) (ENNReal.ofReal (Real.exp (-t))) = 0 := by
      simp only [zero_min, lintegral_zero]
    rw [hz0]
    exact bot_le
  · -- `a ∈ (0,1]`: split `(0,∞) = (0,c] ∪ (c,∞)` at `c = -log ar`.
    set c : ℝ := -Real.log ar with hc
    have hc_nonneg : 0 ≤ c := by
      rw [hc]; exact neg_nonneg.mpr (Real.log_nonpos har_nonneg har_le_one)
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 c ∪ Set.Ioi c := by
      rw [Set.Ioc_union_Ioi_eq_Ioi hc_nonneg]
    rw [hsplit, lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
    refine add_le_add ?_ ?_
    · -- On `(0,c]`: `min a (e^{−t}) ≤ a`, volume `= c`, so integral `≤ a·c = ofReal(negMulLog ar)`.
      calc ∫⁻ t in Set.Ioc 0 c, min a (ENNReal.ofReal (Real.exp (-t)))
          ≤ ∫⁻ _t in Set.Ioc 0 c, a := lintegral_mono fun t => min_le_left _ _
        _ = a * volume (Set.Ioc (0:ℝ) c) := by rw [setLIntegral_const]
        _ = a * ENNReal.ofReal c := by rw [Real.volume_Ioc, sub_zero]
        _ ≤ ENNReal.ofReal (Real.negMulLog ar) := ?_
      -- `a·ofReal c = ofReal ar · ofReal(-log ar) = ofReal(ar·(-log ar)) = ofReal(negMulLog ar)`.
      rw [show a = ENNReal.ofReal ar from (ENNReal.ofReal_toReal
            (by simpa using (lt_of_le_of_lt ha ENNReal.one_lt_top).ne)).symm,
        ← ENNReal.ofReal_mul har_nonneg]
      apply le_of_eq; congr 1
      rw [Real.negMulLog, hc]; ring
    · -- On `(c,∞)`: `min ≤ e^{−t}`, integral `≤ ∫ e^{−t} = e^{−c} = ar = a`.
      calc ∫⁻ t in Set.Ioi c, min a (ENNReal.ofReal (Real.exp (-t)))
          ≤ ∫⁻ t in Set.Ioi c, ENNReal.ofReal (Real.exp (-t)) :=
            lintegral_mono fun t => min_le_right _ _
        _ = ENNReal.ofReal (∫ t in Set.Ioi c, Real.exp (-t)) := by
            rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi c)
              (Eventually.of_forall fun t => (Real.exp_pos _).le)]
        _ = ENNReal.ofReal (Real.exp (-c)) := by rw [integral_exp_neg_Ioi]
        _ = a := by
            rw [hc, neg_neg, Real.exp_log hapos, har,
              ENNReal.ofReal_toReal (by simpa using (lt_of_le_of_lt ha ENNReal.one_lt_top).ne)]

omit [StandardBorelSpace α] in
/-- **The Chung tail integral is `H(P) + 1`.** Summing the per-cell layer-cake estimate over the
finite partition, the layer-cake tail `∫⁻_{(0,∞)} ∑ᵢ min(μ Pᵢ, e^{−t}) dt` is at most
`ofReal(entropy μ P.cells) + 1`: each cell contributes `negMulLog(μ Pᵢ) + μ Pᵢ`, and the masses sum
to `μ(univ) = 1` while the `negMulLog` terms sum to the Shannon entropy of `P`. -/
lemma lintegral_tail_sum_le (P : MeasurePartition μ ι) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ∑ i, min (μ (P.cells i)) (ENNReal.ofReal (Real.exp (-t)))
      ≤ ENNReal.ofReal (entropy μ P.cells) + 1 := by
  classical
  -- Interchange the finite sum and the integral.
  rw [lintegral_finsetSum' (f := fun i t => min (μ (P.cells i)) (ENNReal.ofReal (Real.exp (-t))))
    _ (fun i _ => ((measurable_const.min
      ((Real.measurable_exp.comp measurable_neg).ennreal_ofReal))).aemeasurable.restrict)]
  -- Bound each cell by `ofReal(negMulLog (μ Pᵢ).toReal) + μ Pᵢ`.
  have hcell : ∀ i, ∫⁻ t in Set.Ioi (0:ℝ), min (μ (P.cells i)) (ENNReal.ofReal (Real.exp (-t)))
      ≤ ENNReal.ofReal (Real.negMulLog (μ (P.cells i)).toReal) + μ (P.cells i) :=
    fun i => lintegral_min_meas_exp_le _ prob_le_one
  refine le_trans (Finset.sum_le_sum fun i _ => hcell i) ?_
  rw [Finset.sum_add_distrib,
    ← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => Real.negMulLog_nonneg ENNReal.toReal_nonneg
        (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)))]
  have hentropy : ∑ i, Real.negMulLog (μ (P.cells i)).toReal = entropy μ P.cells := by
    rw [entropy_def]
  have hsum : ∑ i, μ (P.cells i) = 1 := by
    have heq := P.measure_eq_sum_inter (A := Set.univ) MeasurableSet.univ
    rw [measure_univ] at heq
    rw [heq]; exact Finset.sum_congr rfl fun i _ => by rw [Set.univ_inter]
  rw [hentropy, hsum]

/-- **R5: the Chung `L¹` maximal bound `∫ g* ≤ H(P) + 1`, reduced to the layer-cake tail leaf.**

Given the **layer-cake tail hypothesis** `hlayer`
`∫⁻ g* ≤ ∫⁻_{(0,∞)} ∑ᵢ min(μ Pᵢ, e^{−t}) dt`,
the maximal information function `g* = condInfoMaxFun hT P` has `∫⁻ g* ≤ ofReal(H(P)) + 1 < ∞`,
hence is in `L¹`.  The bound is closed sorry-free by `lintegral_tail_sum_le`.

The hypothesis `hlayer` is exactly what the **per-cell Chung stopping-time tail**
`μ{x ∈ Pᵢ : λ < g* x} ≤ e^{−λ}` delivers through the layer-cake formula
(`MeasureTheory.lintegral_eq_lintegral_meas_le`) and the union bound over the finitely many cells:
`μ{t ≤ g*} = ∑ᵢ μ{x ∈ Pᵢ : t ≤ g*} ≤ ∑ᵢ min(μ Pᵢ, e^{−t})` (each cell-tail is `≤ μ Pᵢ` trivially and
`≤ e^{−t}` by Chung).  Proving `hlayer` from the partition structure is the one genuinely missing
Mathlib piece (the Doob/Markov bound on the conditional-probability martingale `pₖ = μ⟦Pᵢ | 𝒞ₖ⟧`
along the stopping time `τ = inf{k : pₖ < e^{−λ}}`). -/
theorem lintegral_condInfoMaxFun_le_of_layer (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι)
    (hlayer : ∫⁻ x, condInfoMaxFun hT P x ∂μ
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ∑ i, min (μ (P.cells i)) (ENNReal.ofReal (Real.exp (-t)))) :
    ∫⁻ x, condInfoMaxFun hT P x ∂μ ≤ ENNReal.ofReal (entropy μ P.cells) + 1 :=
  hlayer.trans (lintegral_tail_sum_le P)

end ChungDomination

section SMBHeadline

variable [Nonempty ι]

/-! ### The pointwise Shannon–McMillan–Breiman theorem: full structure and remaining leaves

This is the assembly of the pointwise SMB theorem `(1/n)·iₙ(x) → h(P,T)` from the proved pieces and
the two precisely-isolated remaining leaves.  It records the dependency structure as an honest
`theorem` taking the two leaves as hypotheses, so the reduction is machine-checked even though the
leaves are not yet discharged.

The Breiman telescoping (`SMBSharp.infoWeight_succ_eq`) gives `iₙ(x) = ∑_{j<n} g_{n−j}(Tʲx)` a.e.,
so `(1/n)·iₙ(x) = A_n(g∞)(x) + (1/n)∑_{j<n}(g_{n−j} − g∞)(Tʲx)`, where:
* the **main term** `A_n(g∞)(x) → h(P,T)` a.e. is **R4**, proved:
  `ae_tendsto_birkhoffAverage_condInfoFun_futureSigma`;
* the **Cesàro tail** `→ 0` a.e. is the content of the two leaves below.
-/

/-- **Pointwise SMB, assembled from the single remaining (Maker/Chung) leaf.**  For ergodic `T`,
the information-function averages `(1/n)·iₙ(x)` converge `μ`-a.e. to
`h(P,T) = ksEntropyPartition hT P`, *given* the one residual leaf

* `hTail` — the **Maker/Breiman dominated-Cesàro** vanishing of the Cesàro tail
  `iₙ(x)/n − A_n(g∞)(x) → 0` a.e., whose `L¹` domination is the Chung bound
  `lintegral_condInfoMaxFun_le_of_layer`.

The proof adds the R4 main-term limit (`ae_tendsto_birkhoffAverage_condInfoFun_futureSigma`,
`A_n(g∞)(x) → ∫ g∞ = h(P,T)`) to the vanishing tail and rewrites `iₙ/n = A_n(g∞) + tail`.  Here
`infoFun_n n` plays the role of the information function `iₙ` (Breiman's `iₙ(x) = ∑_{j<n}
g_{n−j}(Tʲx)`, `SMBSharp.infoWeight_succ_eq`); the statement is `iₙ`-agnostic since the only
property used is the tail decomposition.  Everything but `hTail` (`condInfoFun`, its integral `= h`,
R4, the Chung `L¹` bound reduced to its tail leaf) is proved sorry-free above. -/
theorem ae_tendsto_div_infoFun_of_tail (hT : Ergodic T μ) (P : MeasurePartition μ ι)
    (infoFun_n : ℕ → α → ℝ)
    (hTail : ∀ᵐ x ∂μ, Tendsto
      (fun n => infoFun_n n x / n
        - birkhoffAverage ℝ T
            (condInfoFun (𝒜 := futureSigma hT.toMeasurePreserving P) P) n x) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => infoFun_n n x / n) atTop
      (𝓝 (ksEntropyPartition hT.toMeasurePreserving P)) := by
  filter_upwards [ae_tendsto_birkhoffAverage_condInfoFun_futureSigma hT P, hTail]
    with x hmain htail
  -- `iₙ/n = A_n(g∞) + (iₙ/n − A_n(g∞))`, the first term → h, the second → 0.
  have hsum := hmain.add htail
  rw [add_zero] at hsum
  exact hsum.congr fun n => by ring

end SMBHeadline

end Oseledets.Krieger
