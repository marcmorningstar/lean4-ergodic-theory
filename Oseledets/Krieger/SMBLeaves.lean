/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.SMBPointwise
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# The two analytic leaves of the pointwise Shannon–McMillan–Breiman theorem

This file discharges the two remaining analytic leaves of the pointwise SMB theorem set up in
`Oseledets.Krieger.SMBPointwise`, making the headline a.e. convergence
`(1/n)·iₙ(x) → h(P,T)` unconditional (given only the measure-algebra Breiman telescoping `R2`,
which is not an analytic leaf).

* **Leaf 1 (Chung stopping-time tail).** `chungTail`: for each cell `Pᵢ` and `λ > 0`,
  `μ {x ∈ Pᵢ | λ < g* x} ≤ ofReal e^{−λ}`, where `g* = ⨆ₖ gₖ` is the Chung maximal information
  function and `gₖ = condInfoFun 𝒞ₖ P` along the increasing past filtration `𝒞ₖ = condLevelSigma`.
  The argument is a Doob/Markov bound on the conditional-probability martingale
  `pₖ = μ⟦Pᵢ | 𝒞ₖ⟧` along the first-passage time `τ = inf{k : pₖ < e^{−λ}}`
  (`MeasureTheory.setIntegral_condExp` on each `{τ = k} ∈ 𝒞ₖ`).  This delivers, via the
  layer-cake formula, the hypothesis `hlayer` of `lintegral_condInfoMaxFun_le_of_layer`, hence
  `g* ∈ L¹` (`lintegral_condInfoMaxFun_lt_top`).

* **Leaf 2 (Maker/Breiman dominated-Cesàro).** `makerTail`: from `g* ∈ L¹` and the a.e. Lévy limit
  `gₖ → g∞`, the Cesàro tail `(1/n)∑_{j<n}(g_{n−j} − g∞)(Tʲx) → 0` a.e.  This is Maker's ergodic
  lemma, proved here by the standard ε/truncation split: a `sup`-tail `Gₙ = ⨆_{k≥n}|F_k| ↓ 0`
  dominated by `2g* ∈ L¹`, a Birkhoff average for the bounded part, and the orbital decay
  `m⁻¹·h(T^[m]x) → 0` (`Oseledets.ae_tendsto_orbit_div_atTop_zero`) for the small-lag part.

Assembling Leaf 2 into `ae_tendsto_div_infoFun_of_tail` yields the unconditional pointwise SMB
`ae_tendsto_div_infoFun` (parameterized by the abstract information function together with its
Breiman telescoping), and its in-measure / equipartition corollaries.

## References

* L. Breiman, *The individual ergodic theorem of information theory*, Ann. Math. Statist.
  **28** (1957), 809–811; correction **31** (1960), 809–810.
* K. L. Chung, *A note on the ergodic theorem of information theory*, Ann. Math. Statist.
  **32** (1961), 612–614.
* P. C. Shields, *The Ergodic Theory of Discrete Sample Paths*, GSM 13, AMS (1996), §3.1 (Maker).
* M. Einsiedler, E. Lindenstrauss, T. Ward, *Entropy in Ergodic Theory and Topological Dynamics*,
  Ch. 2 (SMB).
-/

open MeasureTheory Filter Topology Real Function ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Krieger

open Oseledets.Entropy

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α] [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

section Leaf1

/-! ### Leaf 1: the Chung stopping-time tail estimate

For a fixed cell `A = P.cells i₀` and `λ > 0`, the maximal information function `g*` exceeds `λ`
only on a set of measure `≤ e^{−λ}` inside `A`.  The proof tracks the conditional-probability
martingale `pₖ(x) = (condExpKernel μ 𝒞ₖ x A).toReal` (`=ᵐ μ⟦A | 𝒞ₖ⟧`), and the first-passage time
`τ(x) = inf{k : pₖ(x) < e^{−λ}}`.  Each first-passage stratum `{τ = k}` is `𝒞ₖ`-measurable, so
`μ(A ∩ {τ = k}) = ∫_{τ=k} 𝟙_A = ∫_{τ=k} pₖ ≤ e^{−λ}·μ{τ = k}` by `setIntegral_condExp`; summing the
disjoint strata gives `μ(A ∩ {g* > λ}) ≤ e^{−λ}·∑ₖ μ{τ=k} ≤ e^{−λ}`. -/

/-- On the "good" part of a cell `A = P.cells i₀` — points lying in *no other* cell — the
conditional information function is just `-log` of the conditional probability of `A`:
`condInfoFun 𝒜 P x = -log (condExpKernel μ 𝒜 x A).toReal`.  Only the `i₀`-indicator survives. -/
lemma condInfoFun_eq_neg_log_of_mem_unique (P : MeasurePartition μ ι) {i₀ : ι} {x : α}
    (hx : x ∈ P.cells i₀) (hxu : ∀ j, j ≠ i₀ → x ∉ P.cells j) :
    condInfoFun (𝒜 := 𝒜) P x
      = -Real.log (@condExpKernel α mα _ μ _ 𝒜 x (P.cells i₀)).toReal := by
  classical
  rw [condInfoFun, Finset.sum_eq_single i₀]
  · rw [Set.indicator_of_mem hx]
  · intro j _ hji
    exact Set.indicator_of_notMem (hxu j hji) _
  · intro hi₀; exact absurd (Finset.mem_univ i₀) hi₀

omit [StandardBorelSpace α] [IsProbabilityMeasure μ] in
/-- The a.e. set on which each point lies in **exactly one** cell of `P`: it is in its own cell and
no other.  Off a null set (the pairwise a.e.-overlaps), every point lies in a unique cell. -/
lemma ae_mem_unique_cell (P : MeasurePartition μ ι) :
    ∀ᵐ x ∂μ, ∀ i, x ∈ P.cells i → ∀ j, j ≠ i → x ∉ P.cells j := by
  classical
  have hpair : ∀ p : {q : ι × ι // q.1 ≠ q.2}, μ (P.cells p.1.1 ∩ P.cells p.1.2) = 0 :=
    fun p => P.aedisjoint p.2
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null (ι := {q : ι × ι // q.1 ≠ q.2}) hpair)
  intro x hx
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨i, hi, j, hji, hj⟩ := hx
  rw [not_not] at hj
  exact Set.mem_iUnion.2 ⟨⟨(i, j), Ne.symm hji⟩, ⟨hi, hj⟩⟩

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)

/-- The conditional-probability martingale value `pₖ(x) = (condExpKernel μ 𝒞ₖ x A).toReal`. -/
private noncomputable def cprob (A : Set α) (k : ℕ) (x : α) : ℝ :=
  (@condExpKernel α mα _ μ _ (condLevelSigma hT P k) x A).toReal

private lemma cprob_nonneg (A : Set α) (k : ℕ) (x : α) : 0 ≤ cprob hT P A k x :=
  ENNReal.toReal_nonneg

/-- `pₖ` is `𝒞ₖ`-measurable. -/
private lemma measurable_cprob {A : Set α} (hA : MeasurableSet A) (k : ℕ) :
    Measurable[condLevelSigma hT P k] (cprob hT P A k) :=
  (measurable_condExpKernel hA).ennreal_toReal

/-- `pₖ` is `𝒞ₘ`-measurable for `k ≤ m` (the filtration is increasing). -/
private lemma measurable_cprob_mono {A : Set α} (hA : MeasurableSet A) {k m : ℕ} (hkm : k ≤ m) :
    Measurable[condLevelSigma hT P m] (cprob hT P A k) :=
  (measurable_cprob hT P hA k).mono
    (generatedSigmaAlgebra_pullback_ksJoin_mono hT P hkm) le_rfl

/-- `pₖ` is `μ`-a.e. equal to the conditional expectation `μ⟦A | 𝒞ₖ⟧` of the indicator `𝟙_A`. -/
private lemma cprob_ae_eq_condExp {A : Set α} (hA : MeasurableSet A) (k : ℕ) :
    cprob hT P A k =ᵐ[μ] μ[A.indicator (fun _ => (1 : ℝ)) | condLevelSigma hT P k] := by
  have h := condExpKernel_ae_eq_condExp (μ := μ) (m := condLevelSigma hT P k)
    (condLevelSigma_le hT P k) hA
  simpa only [cprob, measureReal_def] using h

/-- The first-passage stratum `{τ = k}` of the first-passage time `τ = inf{k : pₖ < e^{−λ}}`:
the set of points whose conditional probability first drops below `e^{−λ}` exactly at step `k`. -/
private def firstPass (A : Set α) (lam : ℝ) (k : ℕ) : Set α :=
  {x | (∀ j < k, ¬ cprob hT P A j x < Real.exp (-lam)) ∧ cprob hT P A k x < Real.exp (-lam)}

/-- The first-passage strata are pairwise disjoint. -/
private lemma firstPass_disjoint (A : Set α) (lam : ℝ) :
    Pairwise (Disjoint on firstPass hT P A lam) := by
  intro k m hkm
  simp only [Function.onFun, Set.disjoint_left]
  rintro x ⟨hk1, hk2⟩ ⟨hm1, hm2⟩
  rcases lt_or_gt_of_ne hkm with h | h
  · exact hm1 k h hk2
  · exact hk1 m h hm2

/-- Each first-passage stratum `{τ = k}` is `𝒞ₖ`-measurable (all `pⱼ`, `j ≤ k`, are). -/
private lemma measurableSet_firstPass {A : Set α} (hA : MeasurableSet A) (lam : ℝ) (k : ℕ) :
    MeasurableSet[condLevelSigma hT P k] (firstPass hT P A lam k) := by
  have hbase : ∀ j ≤ k, MeasurableSet[condLevelSigma hT P k]
      {x | cprob hT P A j x < Real.exp (-lam)} := fun j hj =>
    measurableSet_lt (measurable_cprob_mono hT P hA hj) measurable_const
  have hrw : firstPass hT P A lam k
      = (⋂ j ∈ Finset.range k, {x | cprob hT P A j x < Real.exp (-lam)}ᶜ)
        ∩ {x | cprob hT P A k x < Real.exp (-lam)} := by
    ext x
    simp only [firstPass, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range, Set.mem_compl_iff]
  rw [hrw]
  refine MeasurableSet.inter ?_ (hbase k (le_refl k))
  refine MeasurableSet.biInter (Finset.range k).countable_toSet fun j hj => ?_
  exact (hbase j (le_of_lt (Finset.mem_range.1 hj))).compl

/-- **Per-stratum bound.** On the `k`-th first-passage stratum `{τ = k} ∈ 𝒞ₖ`,
`μ(A ∩ {τ = k}) = ∫_{τ=k} 𝟙_A = ∫_{τ=k} pₖ ≤ e^{−λ}·μ{τ = k}`, by `setIntegral_condExp` (the
indicator's `𝒞ₖ`-conditional expectation is `pₖ`) and `pₖ < e^{−λ}` on the stratum. -/
private lemma measure_inter_firstPass_le_real {A : Set α} (hA : MeasurableSet A) {lam : ℝ}
    (k : ℕ) :
    (μ (A ∩ firstPass hT P A lam k)).toReal
      ≤ Real.exp (-lam) * (μ (firstPass hT P A lam k)).toReal := by
  set S := firstPass hT P A lam k with hSdef
  have h𝒞le : condLevelSigma hT P k ≤ mα := condLevelSigma_le hT P k
  have hSmeas𝒞 : MeasurableSet[condLevelSigma hT P k] S := measurableSet_firstPass hT P hA lam k
  have hSmeas : MeasurableSet S := h𝒞le _ hSmeas𝒞
  have hind_int : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  -- Step 1: `μ.real(A ∩ S) = ∫_S 𝟙_A`.
  have hμAS : (μ (A ∩ S)).toReal = ∫ x in S, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    rw [setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one, ← measureReal_def,
      Set.inter_comm S A]
  -- Step 2: `∫_S 𝟙_A = ∫_S pₖ` (condExp on `S ∈ 𝒞ₖ`).
  have hμAS2 : ∫ x in S, A.indicator (fun _ => (1 : ℝ)) x ∂μ
      = ∫ x in S, cprob hT P A k x ∂μ := by
    rw [← setIntegral_condExp h𝒞le hind_int hSmeas𝒞]
    exact setIntegral_congr_ae (h𝒞le _ hSmeas𝒞)
      ((cprob_ae_eq_condExp hT P hA k).mono fun x hx _ => hx.symm)
  -- Step 3: `∫_S pₖ ≤ ∫_S exp(-lam) = exp(-lam)·μ.real(S)` (since `pₖ < exp(-lam)` on `S`).
  have hpint : IntegrableOn (cprob hT P A k) S μ := by
    refine Integrable.integrableOn ?_
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((measurable_cprob hT P hA k).mono h𝒞le le_rfl).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (cprob_nonneg hT P A k x)]
    simpa [cprob] using toReal_condExpKernel_le_one A x
  have hbound : ∫ x in S, cprob hT P A k x ∂μ ≤ Real.exp (-lam) * (μ S).toReal := by
    calc ∫ x in S, cprob hT P A k x ∂μ ≤ ∫ _x in S, Real.exp (-lam) ∂μ := by
          refine setIntegral_mono_on hpint
            (integrableOn_const (C := Real.exp (-lam)) (measure_ne_top μ S))
            hSmeas fun x hx => le_of_lt hx.2
      _ = Real.exp (-lam) * (μ S).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_comm, ← measureReal_def]
  rw [hμAS, hμAS2]; exact hbound

/-- ℝ≥0∞ form of the per-stratum bound: `μ(A ∩ {τ=k}) ≤ ofReal e^{−λ}·μ{τ=k}`. -/
private lemma measure_inter_firstPass_le {A : Set α} (hA : MeasurableSet A) {lam : ℝ}
    (k : ℕ) :
    μ (A ∩ firstPass hT P A lam k)
      ≤ ENNReal.ofReal (Real.exp (-lam)) * μ (firstPass hT P A lam k) := by
  have hreal := measure_inter_firstPass_le_real hT P hA (lam := lam) k
  have hAS_ne : μ (A ∩ firstPass hT P A lam k) ≠ ∞ := measure_ne_top μ _
  have hS_ne : μ (firstPass hT P A lam k) ≠ ∞ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hAS_ne, ← ENNReal.ofReal_toReal hS_ne,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **The first-passage union bound.** Summing the disjoint strata,
`μ(A ∩ {∃k, pₖ < e^{−λ}}) ≤ ofReal e^{−λ}`: the strata are pairwise disjoint and their measures
sum to at most `μ(univ) = 1`. -/
private lemma measure_inter_firstPass_iUnion_le {A : Set α} (hA : MeasurableSet A) (lam : ℝ) :
    μ (A ∩ ⋃ k, firstPass hT P A lam k) ≤ ENNReal.ofReal (Real.exp (-lam)) := by
  rw [Set.inter_iUnion]
  have hdisj : Pairwise (Function.onFun Disjoint fun k => A ∩ firstPass hT P A lam k) := by
    intro k m hkm
    exact (firstPass_disjoint hT P A lam hkm).mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ k, MeasurableSet (A ∩ firstPass hT P A lam k) := fun k =>
    hA.inter (condLevelSigma_le hT P k _ (measurableSet_firstPass hT P hA lam k))
  rw [measure_iUnion hdisj hmeas]
  calc ∑' k, μ (A ∩ firstPass hT P A lam k)
      ≤ ∑' k, ENNReal.ofReal (Real.exp (-lam)) * μ (firstPass hT P A lam k) :=
        ENNReal.tsum_le_tsum fun k => measure_inter_firstPass_le hT P hA k
    _ = ENNReal.ofReal (Real.exp (-lam)) * ∑' k, μ (firstPass hT P A lam k) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (Real.exp (-lam)) * 1 := by
        have hnm : ∀ k, NullMeasurableSet (firstPass hT P A lam k) μ := fun k =>
          (condLevelSigma_le hT P k _ (measurableSet_firstPass hT P hA lam k)).nullMeasurableSet
        have haed : Pairwise (AEDisjoint μ on firstPass hT P A lam) :=
          (firstPass_disjoint hT P A lam).aedisjoint
        gcongr
        exact (tsum_measure_le_measure_univ hnm haed).trans_eq (by rw [measure_univ])
    _ = ENNReal.ofReal (Real.exp (-lam)) := mul_one _

/-- **Leaf 1 (Chung's stopping-time tail).** For each cell `Pᵢ₀` and `λ > 0`, the Chung maximal
information function `g* = condInfoMaxFun` exceeds `λ` only on a subset of `Pᵢ₀` of measure
`≤ e^{−λ}`:
`μ {x ∈ Pᵢ₀ | ofReal λ < g* x} ≤ ofReal e^{−λ}`.

The point `x ∈ Pᵢ₀` (in no other cell, a.e.) with `g* x > λ` has some level `gₖ(x) > λ`, i.e.
`-log pₖ(x) > λ`, i.e. `pₖ(x) < e^{−λ}` (and `pₖ(x) > 0`, since `-log 0 = 0 ≯ λ`).  So the level set
sits inside `Pᵢ₀ ∩ ⋃ₖ {τ = k}`, whose measure is `≤ e^{−λ}` by the first-passage union bound. -/
theorem chungTail (i₀ : ι) {lam : ℝ} (hlam : 0 < lam) :
    μ {x | x ∈ P.cells i₀ ∧ ENNReal.ofReal lam < condInfoMaxFun hT P x}
      ≤ ENNReal.ofReal (Real.exp (-lam)) := by
  classical
  set A := P.cells i₀ with hA
  have hAmeas : MeasurableSet A := P.measurable i₀
  -- The level set sits (a.e.) inside `A ∩ ⋃ₖ {τ=k}`.
  refine le_trans (measure_mono_ae ?_) (measure_inter_firstPass_iUnion_le hT P hAmeas lam)
  filter_upwards [ae_mem_unique_cell P] with x hxu
  rintro ⟨hxA, hxgt⟩
  refine ⟨hxA, ?_⟩
  -- `g* x > ofReal λ` ⟹ `∃ k, gₖ x > λ`.
  rw [condInfoMaxFun, lt_iSup_iff] at hxgt
  obtain ⟨k, hk⟩ := hxgt
  -- On `A` (unique cell), `gₖ x = -log (pₖ x)`.
  have hcell : condInfoFun (𝒜 := condLevelSigma hT P k) P x
      = -Real.log (cprob hT P A k x) :=
    condInfoFun_eq_neg_log_of_mem_unique P hxA (hxu i₀ hxA)
  rw [hcell] at hk
  -- `ofReal λ < ofReal (-log pₖ)` ⟹ `λ < -log pₖ` (both nonneg).
  have hlt : lam < -Real.log (cprob hT P A k x) := by
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le).1 hk
    exact h
  -- Hence `log pₖ < -λ`, and `pₖ > 0` (else `-log 0 = 0 ≤ λ`), so `pₖ < e^{-λ}`.
  have hpk_nonneg : 0 ≤ cprob hT P A k x := cprob_nonneg hT P A k x
  have hpk_pos : 0 < cprob hT P A k x := by
    rcases eq_or_lt_of_le hpk_nonneg with h0 | hpos
    · exfalso; rw [← h0, Real.log_zero, neg_zero] at hlt; linarith
    · exact hpos
  have hlogpk : Real.log (cprob hT P A k x) < -lam := by linarith
  have hpk_lt : cprob hT P A k x < Real.exp (-lam) := by
    have := Real.exp_lt_exp.2 hlogpk
    rwa [Real.exp_log hpk_pos] at this
  -- Membership in `⋃ₖ {τ=k}` via `Nat.find` of the first passage.
  refine Set.mem_iUnion.2 ?_
  by_cases hex : ∃ m, cprob hT P A m x < Real.exp (-lam)
  · refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    intro j hj
    exact Nat.find_min hex hj
  · exact absurd ⟨k, hpk_lt⟩ hex

/-- **Per-`t` superlevel bound.** For `t > 0`, the superlevel set `{x | ofReal t < g* x}` has
measure at most `∑ᵢ min(μ Pᵢ, ofReal e^{−t})`: decomposing over the (a.e.-covering) cells, each
cell contributes `μ(Pᵢ ∩ {g* > t}) ≤ μ Pᵢ` (trivially) and `≤ ofReal e^{−t}` (Chung's tail). -/
private lemma measure_superlevel_le {t : ℝ} (ht : 0 < t) :
    μ {x | ENNReal.ofReal t < condInfoMaxFun hT P x}
      ≤ ∑ i, min (μ (P.cells i)) (ENNReal.ofReal (Real.exp (-t))) := by
  classical
  -- Decompose the superlevel set over the cells (which a.e.-cover the space).
  have hcover : {x | ENNReal.ofReal t < condInfoMaxFun hT P x}
      ⊆ ⋃ i, {x | x ∈ P.cells i ∧ ENNReal.ofReal t < condInfoMaxFun hT P x} := by
    intro x hx
    have hxu : x ∈ ⋃ i, P.cells i := by rw [P.cover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxu
    exact Set.mem_iUnion.2 ⟨i, hi, hx⟩
  refine le_trans (measure_mono hcover) ?_
  refine le_trans (measure_iUnion_fintype_le _ _) ?_
  refine Finset.sum_le_sum fun i _ => le_min ?_ (chungTail hT P i ht)
  exact measure_mono fun x hx => hx.1

/-- The `k`-th level information function `gₖ = condInfoFun 𝒞ₖ P` (abbreviation). -/
private noncomputable def gk (k : ℕ) (x : α) : ℝ :=
  condInfoFun (𝒜 := condLevelSigma hT P k) P x

private lemma gk_nonneg (k : ℕ) (x : α) : 0 ≤ gk hT P k x := condInfoFun_nonneg P x

private lemma measurable_gk (k : ℕ) : Measurable (gk hT P k) :=
  measurable_condInfoFun (condLevelSigma_le hT P k) P

/-- The real-valued partial maximum `Gₙ(x) = max_{k≤n} gₖ(x)`. -/
private noncomputable def Gpart (n : ℕ) : α → ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => gk hT P k

private lemma Gpart_apply (n : ℕ) (x : α) :
    Gpart hT P n x = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => gk hT P k x := by
  rw [Gpart, Finset.sup'_apply]

private lemma Gpart_nonneg (n : ℕ) (x : α) : 0 ≤ Gpart hT P n x := by
  rw [Gpart_apply]
  exact le_trans (gk_nonneg hT P 0 x)
    (Finset.le_sup' (fun k => gk hT P k x) (Finset.mem_range.2 (Nat.succ_pos n)))

private lemma measurable_Gpart (n : ℕ) : Measurable (Gpart hT P n) :=
  Finset.measurable_range_sup' fun k _ => measurable_gk hT P k

/-- `ofReal (Gₙ x) = ⨆_{k≤n} ofReal (gₖ x)`. -/
private lemma ofReal_Gpart (n : ℕ) (x : α) :
    ENNReal.ofReal (Gpart hT P n x)
      = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => ENNReal.ofReal (gk hT P k x) := by
  rw [Gpart_apply, Finset.comp_sup'_eq_sup'_comp Finset.nonempty_range_add_one
    (fun r => ENNReal.ofReal r) (fun a b => ENNReal.ofReal_max a b)]
  rfl

/-- `ofReal (Gₙ x) ↑ g* x` as `n → ∞`. -/
private lemma ofReal_Gpart_tendsto_condInfoMaxFun (x : α) :
    ⨆ n, ENNReal.ofReal (Gpart hT P n x) = condInfoMaxFun hT P x := by
  rw [condInfoMaxFun]
  simp_rw [ofReal_Gpart hT P _ x]
  apply le_antisymm
  · refine iSup_le fun n => Finset.sup'_le Finset.nonempty_range_add_one _ fun k _ => ?_
    exact le_iSup (fun k => ENNReal.ofReal (condInfoFun (𝒜 := condLevelSigma hT P k) P x)) k
  · refine iSup_le fun k => ?_
    refine le_iSup_of_le k ?_
    refine Finset.le_sup' (fun j => ENNReal.ofReal (gk hT P j x)) ?_
    exact Finset.mem_range.2 (Nat.lt_succ_self k)

/-- **The layer-cake bridge `hlayer`.** Summing the per-cell Chung tail through the layer-cake
formula bounds the maximal information `L¹`-norm by the per-cell tail integral:
`∫⁻ g* ≤ ∫⁻ t in Ioi 0, ∑ᵢ min(μ Pᵢ, e^{−t})`.

The supremum `g* = ⨆ₙ ofReal Gₙ` of the real partial maxima `Gₙ` is reached by monotone convergence;
each `∫⁻ ofReal Gₙ` equals `∫⁻ t in Ioi 0, μ{t < Gₙ}` (real layer cake), and the integrand is
bounded by `μ{ofReal t < g*} ≤ ∑ᵢ min(μ Pᵢ, e^{−t})` (`measure_superlevel_le`) uniformly in `n`. -/
theorem condInfoMaxFun_layer_le :
    ∫⁻ x, condInfoMaxFun hT P x ∂μ
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ∑ i, min (μ (P.cells i)) (ENNReal.ofReal (Real.exp (-t))) := by
  -- `∫⁻ g* = ⨆ₙ ∫⁻ ofReal Gₙ` by monotone convergence.
  have hmono : Monotone fun n => fun x => ENNReal.ofReal (Gpart hT P n x) := by
    intro m n hmn x
    simp only [Gpart_apply]
    refine ENNReal.ofReal_le_ofReal ?_
    exact Finset.sup'_le _ _ fun k hk =>
      Finset.le_sup' (fun k => gk hT P k x)
        (Finset.range_mono (Nat.add_le_add_right hmn 1) hk)
  have hlim : ∫⁻ x, condInfoMaxFun hT P x ∂μ
      = ⨆ n, ∫⁻ x, ENNReal.ofReal (Gpart hT P n x) ∂μ := by
    rw [← lintegral_iSup (fun n => (measurable_Gpart hT P n).ennreal_ofReal) hmono]
    refine lintegral_congr fun x => (ofReal_Gpart_tendsto_condInfoMaxFun hT P x).symm
  rw [hlim]
  refine iSup_le fun n => ?_
  -- Real layer cake for `Gₙ ≥ 0`.
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall (Gpart_nonneg hT P n))
    (measurable_Gpart hT P n).aemeasurable]
  -- Bound the integrand: `μ{t < Gₙ} ≤ ∑ᵢ min(...)` for `t > 0`.
  refine setLIntegral_mono_ae' measurableSet_Ioi (Eventually.of_forall fun t ht => ?_)
  -- `{x | t < Gₙ x} ⊆ {x | ofReal t < g* x}`.
  refine le_trans (measure_mono ?_) (measure_superlevel_le hT P (Set.mem_Ioi.1 ht))
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  calc ENNReal.ofReal t < ENNReal.ofReal (Gpart hT P n x) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Set.mem_Ioi.1 ht).le).2 hx
    _ ≤ condInfoMaxFun hT P x := by
        rw [← ofReal_Gpart_tendsto_condInfoMaxFun hT P x]
        exact le_iSup (fun n => ENNReal.ofReal (Gpart hT P n x)) n

/-- **`g* ∈ L¹`.** Combining the layer-cake bridge with the proved tail-integral bound
`lintegral_tail_sum_le` (≤ `H(P) + 1`), the Chung maximal information function is integrable. -/
theorem lintegral_condInfoMaxFun_lt_top :
    ∫⁻ x, condInfoMaxFun hT P x ∂μ < ∞ := by
  refine lt_of_le_of_lt
    (lintegral_condInfoMaxFun_le_of_layer hT P (condInfoMaxFun_layer_le hT P)) ?_
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.one_lt_top⟩

end Leaf1

section Leaf2

/-! ### Leaf 2: the Maker/Breiman dominated-Cesàro vanishing

From `g* ∈ L¹` (Leaf 1) and the a.e. Lévy limit `gₖ → g∞`, the Cesàro tail
`(1/n)∑_{j<n}(g_{n−j} − g∞)(Tʲx) → 0` a.e.  This is Maker's ergodic lemma.

The argument: with `Fk k = gk k − g∞` (so `Fk k → 0` a.e., dominated by `D = g*ℝ + g∞ ∈ L¹`), set
the antitone sup-tail `Ψ_N = ⨆_{k≥N}|Fk k|` (`Ψ_N ↓ 0` a.e., `Ψ_N ≤ D`, so `∫ Ψ_N → 0` by
dominated convergence).  Splitting `∑_{j<n}|Fk(n−j)(Tʲx)|` at lag `n−j ≷ N`:
the large-lag part is `≤ birkhoffAverage Ψ_N n x → ∫ Ψ_N` (Birkhoff); the small-lag part is the last
`N` terms `|Fk(m)(T^{n−m}x)|/n` with `m ≤ N`, each `→ 0` by the orbital decay
`ae_tendsto_orbit_div_atTop_zero`.  Hence `limsup ≤ ∫ Ψ_N → 0`. -/

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)

/-- The limit conditional information function `g∞ = condInfoFun (futureSigma) P`. -/
private noncomputable def ginf (x : α) : ℝ :=
  condInfoFun (𝒜 := futureSigma hT P) P x

private lemma ginf_nonneg (x : α) : 0 ≤ ginf hT P x := condInfoFun_nonneg P x

private lemma integrable_ginf : Integrable (ginf hT P) μ :=
  integrable_condInfoFun (futureSigma_le hT P) P

/-- The filtration `ℱ n = 𝒞ₙ = condLevelSigma hT P n`, with `⨆ n, ℱ n = futureSigma hT P`. -/
private noncomputable def condFiltration : Filtration ℕ mα :=
  ⟨fun n => condLevelSigma hT P n, generatedSigmaAlgebra_pullback_ksJoin_mono hT P,
    fun n => condLevelSigma_le hT P n⟩

/-- The conditional probability of one's *own* cell is `μ`-a.e. positive under the limit
σ-algebra `𝒞∞`: `μ(Pᵢ ∩ {μ⟦Pᵢ|𝒞∞⟧ = 0}) = ∫_{p∞ᵢ=0} p∞ᵢ = 0` (`setIntegral_condExp`). -/
private lemma ae_condExpKernel_futureSigma_pos :
    ∀ᵐ x ∂μ, ∀ i, x ∈ P.cells i →
      (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal ≠ 0 := by
  classical
  rw [ae_all_iff]
  intro i
  have h𝒞le : futureSigma hT P ≤ mα := futureSigma_le hT P
  -- `p∞ = (condExpKernel μ 𝒞∞ · Pᵢ).toReal`, `𝒞∞`-measurable.
  have hpinf_meas : Measurable[futureSigma hT P]
      (fun x => (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal) :=
    (measurable_condExpKernel (P.measurable i)).ennreal_toReal
  have hZmeas𝒞 : MeasurableSet[futureSigma hT P]
      {x | (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal = 0} :=
    hpinf_meas (measurableSet_singleton 0)
  set Z : Set α := {x | (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal = 0}
    with hZdef
  have hind_int : Integrable ((P.cells i).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (P.measurable i)
  -- The bad set `Pᵢ ∩ Z` is null.
  have hnull : μ (P.cells i ∩ Z) = 0 := by
    have hμreal : (μ (P.cells i ∩ Z)).toReal
        = ∫ x in Z, (P.cells i).indicator (fun _ => (1 : ℝ)) x ∂μ := by
      rw [setIntegral_indicator (P.measurable i), setIntegral_const, smul_eq_mul, mul_one,
        ← measureReal_def, Set.inter_comm]
    have hcondInt : ∫ x in Z, (P.cells i).indicator (fun _ => (1 : ℝ)) x ∂μ
        = ∫ x in Z, (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal ∂μ := by
      rw [← setIntegral_condExp h𝒞le hind_int hZmeas𝒞]
      refine setIntegral_congr_ae (h𝒞le _ hZmeas𝒞) ?_
      have hbridge := condExpKernel_ae_eq_condExp (μ := μ) (m := futureSigma hT P) h𝒞le
        (P.measurable i)
      filter_upwards [hbridge] with x hx _
      simp only [measureReal_def] at hx ⊢
      rw [hx]
    have hzero : ∫ x in Z, (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal ∂μ
        = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun x hx => hx
    have htoReal : (μ (P.cells i ∩ Z)).toReal = 0 := by rw [hμreal, hcondInt, hzero]
    exact ((ENNReal.toReal_eq_zero_iff _).1 htoReal).resolve_right (measure_ne_top μ _)
  have hae : ∀ᵐ x ∂μ, x ∉ P.cells i ∩ Z := by rw [ae_iff]; simpa using hnull
  filter_upwards [hae] with x hx hxi hzero
  exact hx ⟨hxi, hzero⟩

/-- **R3 (Lévy a.e. limit).** The level information functions converge a.e. to the limit:
`gₖ(x) → g∞(x)`.  Per cell, the kernel masses `μ⟦Pᵢ|𝒞ₖ⟧ → μ⟦Pᵢ|𝒞∞⟧` (Lévy upward); the surviving
own-cell `-log` is continuous since the limit mass is a.e. positive
(`ae_condExpKernel_futureSigma_pos`). -/
private lemma gk_tendsto_ginf :
    ∀ᵐ x ∂μ, Tendsto (fun k => gk hT P k x) atTop (𝓝 (ginf hT P x)) := by
  classical
  set ℱ : Filtration ℕ mα := condFiltration hT P with hℱ
  -- Per cell, the kernel masses converge a.e. (Lévy upward).
  have hcell : ∀ i, ∀ᵐ x ∂μ, Tendsto
      (fun k => (@condExpKernel α mα _ μ _ (condLevelSigma hT P k) x (P.cells i)).toReal) atTop
      (𝓝 (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal) := by
    intro i
    set g : α → ℝ := (P.cells i).indicator (fun _ => (1 : ℝ)) with hg
    have hlevy : ∀ᵐ x ∂μ, Tendsto (fun k => (μ[g | ℱ k]) x) atTop
        (𝓝 ((μ[g | ⨆ k, ℱ k]) x)) :=
      MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) g
    have haen : ∀ k, (fun x =>
          (@condExpKernel α mα _ μ _ (condLevelSigma hT P k) x (P.cells i)).toReal)
        =ᵐ[μ] fun x => (μ[g | ℱ k]) x := fun k => by
      simpa only [hg, measureReal_def] using
        condExpKernel_ae_eq_condExp (condLevelSigma_le hT P k) (P.measurable i)
    have haelim : (fun x => (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i)).toReal)
        =ᵐ[μ] fun x => (μ[g | ⨆ k, ℱ k]) x := by
      simpa only [hg, measureReal_def] using
        condExpKernel_ae_eq_condExp (futureSigma_le hT P) (P.measurable i)
    filter_upwards [hlevy, ae_all_iff.2 haen, haelim] with x hx hxk hxlim
    rw [hxlim]
    exact hx.congr fun k => (hxk k).symm
  -- Combine over cells: at a.e. `x` (in unique cell, with positive own-cell limit mass).
  have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ i, P.cells i :=
    Filter.Eventually.of_forall fun x => P.cover ▸ Set.mem_univ x
  filter_upwards [ae_all_iff.2 hcell, ae_mem_unique_cell P, ae_condExpKernel_futureSigma_pos hT P,
    hcov] with x hxc hxu hxpos hxcov
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hxcov
  have hxu' : ∀ j, j ≠ i₀ → x ∉ P.cells j := hxu i₀ hi₀
  -- `gₖ x = -log (pₖᵢ₀ x)`, `g∞ x = -log (p∞ᵢ₀ x)`, and `pₖᵢ₀ → p∞ᵢ₀` with `p∞ᵢ₀ > 0`.
  have hgkeq : ∀ k, gk hT P k x
      = -Real.log (@condExpKernel α mα _ μ _ (condLevelSigma hT P k) x (P.cells i₀)).toReal :=
    fun k => condInfoFun_eq_neg_log_of_mem_unique P hi₀ hxu'
  have hginfeq : ginf hT P x
      = -Real.log (@condExpKernel α mα _ μ _ (futureSigma hT P) x (P.cells i₀)).toReal :=
    condInfoFun_eq_neg_log_of_mem_unique P hi₀ hxu'
  rw [show (fun k => gk hT P k x) = fun k =>
        -Real.log (@condExpKernel α mα _ μ _ (condLevelSigma hT P k) x (P.cells i₀)).toReal from
      funext hgkeq, hginfeq]
  refine Tendsto.neg ?_
  refine (Real.continuousAt_log ?_).tendsto.comp (hxc i₀)
  exact hxpos i₀ hi₀

/-- The shifted difference `Fₖ = gₖ − g∞`. -/
private noncomputable def Fk (k : ℕ) (x : α) : ℝ := gk hT P k x - ginf hT P x

private lemma Fk_tendsto_zero :
    ∀ᵐ x ∂μ, Tendsto (fun k => Fk hT P k x) atTop (𝓝 0) := by
  filter_upwards [gk_tendsto_ginf hT P] with x hx
  have := hx.sub_const (ginf hT P x)
  simpa only [Fk, sub_self] using this

private lemma measurable_Fk (k : ℕ) : Measurable (Fk hT P k) :=
  (measurable_gk hT P k).sub (measurable_condInfoFun (futureSigma_le hT P) P)

/-- The real-valued Chung maximal function `g*ℝ = (condInfoMaxFun).toReal`. -/
private noncomputable def gstarR (x : α) : ℝ := (condInfoMaxFun hT P x).toReal

private lemma measurable_gstarR : Measurable (gstarR hT P) :=
  (measurable_condInfoMaxFun hT P).ennreal_toReal

private lemma integrable_gstarR : Integrable (gstarR hT P) μ :=
  integrable_toReal_of_lintegral_ne_top (measurable_condInfoMaxFun hT P).aemeasurable
    (lintegral_condInfoMaxFun_lt_top hT P).ne

/-- `gₖ(x) ≤ g*ℝ(x)` a.e.: `ofReal (gₖ x) ≤ g* x` and `g* x < ∞` a.e. (`g* ∈ L¹`). -/
private lemma gk_le_gstarR : ∀ᵐ x ∂μ, ∀ k, gk hT P k x ≤ gstarR hT P x := by
  have hfin : ∀ᵐ x ∂μ, condInfoMaxFun hT P x ≠ ∞ :=
    ae_lt_top (measurable_condInfoMaxFun hT P) (lintegral_condInfoMaxFun_lt_top hT P).ne
      |>.mono fun x hx => hx.ne
  filter_upwards [hfin] with x hx k
  have hle : ENNReal.ofReal (gk hT P k x) ≤ condInfoMaxFun hT P x := by
    rw [condInfoMaxFun]
    exact le_iSup (fun k => ENNReal.ofReal (gk hT P k x)) k
  have := (ENNReal.ofReal_le_iff_le_toReal hx).1 hle
  exact this

/-- The integrable dominator `D = g*ℝ + g∞` of every `|Fₖ|`. -/
private noncomputable def dom (x : α) : ℝ := gstarR hT P x + ginf hT P x

private lemma integrable_dom : Integrable (dom hT P) μ :=
  (integrable_gstarR hT P).add (integrable_ginf hT P)

private lemma measurable_dom : Measurable (dom hT P) :=
  (measurable_gstarR hT P).add (measurable_condInfoFun (futureSigma_le hT P) P)

private lemma dom_nonneg (x : α) : 0 ≤ dom hT P x :=
  add_nonneg ENNReal.toReal_nonneg (ginf_nonneg hT P x)

/-- `|Fₖ(x)| ≤ D(x)` a.e., uniformly in `k`. -/
private lemma abs_Fk_le_dom : ∀ᵐ x ∂μ, ∀ k, |Fk hT P k x| ≤ dom hT P x := by
  filter_upwards [gk_le_gstarR hT P] with x hx k
  rw [Fk, dom, abs_le]
  constructor
  · have hg0 : 0 ≤ gk hT P k x := gk_nonneg hT P k x
    have hgi0 : 0 ≤ ginf hT P x := ginf_nonneg hT P x
    have hgs0 : 0 ≤ gstarR hT P x := ENNReal.toReal_nonneg
    linarith [hx k]
  · have hgi0 : 0 ≤ ginf hT P x := ginf_nonneg hT P x
    linarith [hx k]

/-- The ℝ≥0∞ sup-tail `ΨEₙ(x) = ⨆_{i} ofReal |F_{n+i}(x)| = sup of `|Fₖ|` over `k ≥ n`. -/
private noncomputable def PsiE (n : ℕ) (x : α) : ℝ≥0∞ :=
  ⨆ i, ENNReal.ofReal |Fk hT P (n + i) x|

/-- The real-valued sup-tail `Ψₙ = (ΨEₙ).toReal`. -/
private noncomputable def Psi (n : ℕ) (x : α) : ℝ := (PsiE hT P n x).toReal

private lemma measurable_PsiE (n : ℕ) : Measurable (PsiE hT P n) :=
  Measurable.iSup fun i =>
    (_root_.continuous_abs.measurable.comp (measurable_Fk hT P (n + i))).ennreal_ofReal

private lemma measurable_Psi (n : ℕ) : Measurable (Psi hT P n) :=
  (measurable_PsiE hT P n).ennreal_toReal

/-- `ΨEₙ(x) ≤ ofReal (D x)` a.e.: each `|Fₖ| ≤ D`. -/
private lemma PsiE_le_dom : ∀ᵐ x ∂μ, ∀ n, PsiE hT P n x ≤ ENNReal.ofReal (dom hT P x) := by
  filter_upwards [abs_Fk_le_dom hT P] with x hx n
  refine iSup_le fun i => ENNReal.ofReal_le_ofReal (hx (n + i))

/-- `|Fₙ(x)| ≤ Ψₙ(x)` a.e. (the `n`-th term sits under its own tail sup). -/
private lemma abs_Fk_le_Psi : ∀ᵐ x ∂μ, ∀ n, |Fk hT P n x| ≤ Psi hT P n x := by
  filter_upwards [PsiE_le_dom hT P] with x hx n
  have hfin : PsiE hT P n x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hx n)
  rw [Psi, ← ENNReal.ofReal_le_iff_le_toReal hfin, PsiE]
  refine (le_iSup (fun i => ENNReal.ofReal |Fk hT P (n + i) x|) 0).trans_eq' ?_
  rw [Nat.add_zero]

/-- `|Fₘ(x)| ≤ Ψ_M(x)` a.e. whenever `M ≤ m` (the `m`-th term is in the `M`-tail sup). -/
private lemma abs_Fk_le_Psi_of_le : ∀ᵐ x ∂μ, ∀ M m, M ≤ m → |Fk hT P m x| ≤ Psi hT P M x := by
  filter_upwards [PsiE_le_dom hT P] with x hx M m hMm
  have hfin : PsiE hT P M x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hx M)
  rw [Psi, ← ENNReal.ofReal_le_iff_le_toReal hfin, PsiE]
  refine (le_iSup (fun i => ENNReal.ofReal |Fk hT P (M + i) x|) (m - M)).trans_eq' ?_
  rw [Nat.add_sub_cancel' hMm]

/-- The sup-tail is antitone: `Ψₙ₊₁ ≤ Ψₙ` (fewer indices in the sup). -/
private lemma PsiE_antitone (x : α) : Antitone (fun n => PsiE hT P n x) := by
  intro m n hmn
  refine iSup_le fun i => ?_
  refine le_iSup_of_le (i + (n - m)) ?_
  have heq : m + (i + (n - m)) = n + i := by omega
  rw [heq]

/-- The sup-tail vanishes a.e.: `ΨEₙ(x) → 0` (the indices `≥ n` of `Fₖ → 0` have shrinking sup). -/
private lemma tendsto_PsiE_zero :
    ∀ᵐ x ∂μ, Tendsto (fun n => PsiE hT P n x) atTop (𝓝 0) := by
  filter_upwards [Fk_tendsto_zero hT P] with x hx
  -- antitone, so converges to its infimum; show the infimum is `0`.
  have hanti := PsiE_antitone hT P x
  have hinf : ⨅ n, PsiE hT P n x = 0 := by
    rw [← bot_eq_zero]
    refine iInf_eq_bot.2 fun b hb => ?_
    rw [bot_eq_zero] at hb
    -- pick `N` with `|Fₖ x| < (b.toReal)/2` for `k ≥ N`, so `ΨE_N x ≤ ofReal(b.toReal/2) < b`.
    obtain ⟨c, hc0, hcb⟩ : ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c < b := by
      rcases eq_or_ne b ∞ with rfl | hbne
      · exact ⟨1, one_pos, ENNReal.ofReal_lt_top⟩
      · have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbne
        refine ⟨(b.toReal) / 2, by linarith, ?_⟩
        rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hbne]
        linarith
    have habs : Tendsto (fun k => |Fk hT P k x|) atTop (𝓝 0) := by
      simpa only [abs_zero] using hx.abs
    rw [Metric.tendsto_atTop] at habs
    obtain ⟨N, hN⟩ := habs c hc0
    refine ⟨N, lt_of_le_of_lt ?_ hcb⟩
    refine iSup_le fun i => ?_
    have hb' := hN (N + i) (Nat.le_add_right N i)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)] at hb'
    exact ENNReal.ofReal_le_ofReal hb'.le
  rw [← hinf]
  exact tendsto_atTop_iInf hanti

/-- The real sup-tail vanishes a.e.: `Ψₙ(x) → 0`. -/
private lemma tendsto_Psi_zero :
    ∀ᵐ x ∂μ, Tendsto (fun n => Psi hT P n x) atTop (𝓝 0) := by
  filter_upwards [tendsto_PsiE_zero hT P] with x hx
  have : Tendsto (fun n => (PsiE hT P n x).toReal) atTop (𝓝 (0 : ℝ≥0∞).toReal) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx
  simpa only [Psi, ENNReal.toReal_zero] using this

/-- `Ψₙ ≥ 0`. -/
private lemma Psi_nonneg (n : ℕ) (x : α) : 0 ≤ Psi hT P n x := ENNReal.toReal_nonneg

/-- The sup-tail integrals vanish: `∫ Ψₙ → 0` (dominated convergence, `Ψₙ ↓ 0`, `Ψₙ ≤ D ∈ L¹`). -/
private lemma tendsto_integral_Psi_zero :
    Tendsto (fun n => ∫ x, Psi hT P n x ∂μ) atTop (𝓝 0) := by
  have hdom : ∀ n, ∀ᵐ x ∂μ, ‖Psi hT P n x‖ ≤ dom hT P x := by
    intro n
    filter_upwards [PsiE_le_dom hT P] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Psi_nonneg hT P n x), Psi]
    calc (PsiE hT P n x).toReal ≤ (ENNReal.ofReal (dom hT P x)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hx n)
      _ = dom hT P x := ENNReal.toReal_ofReal (dom_nonneg hT P x)
  have hlim : Tendsto (fun n => ∫ x, Psi hT P n x ∂μ) atTop (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (dom hT P)
      (fun n => (measurable_Psi hT P n).aestronglyMeasurable) (integrable_dom hT P) hdom ?_
    filter_upwards [tendsto_Psi_zero hT P] with x hx using hx
  simpa using hlim

omit [StandardBorelSpace α] [IsProbabilityMeasure μ] in
/-- A measurable a.e.-true predicate holds, a.e., along the whole forward orbit. -/
private lemma ae_forall_orbit (hT : MeasurePreserving T μ μ) {p : α → Prop}
    (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, ∀ j : ℕ, p (T^[j] x) := by
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (T^[j]) μ μ := MeasurePreserving.iterate hT j
  exact hmp.quasiMeasurePreserving.tendsto_ae hp

/-! ### The Maker dominated-Cesàro core -/

/-- The Cesàro tail sum `Mₙ(x) = ∑_{j<n} F_{n−j}(Tʲx)` of the Breiman telescoping; we show
`(1/n)·Mₙ(x) → 0` a.e. (Maker's theorem). -/
private noncomputable def makerSum (n : ℕ) (x : α) : ℝ :=
  ∑ j ∈ Finset.range n, Fk hT P (n - j) (T^[j] x)

/-- Pointwise split of the absolute Cesàro tail at lag `N`: for `N ≤ n`,
`|Mₙ(x)| ≤ ∑_{j<n} Ψ_{N+1}(Tʲx) + ∑_{j ∈ [n−N, n)} D(Tʲx)`.  The large-lag terms (`n−j ≥ N+1`) are
bounded by the `(N+1)`-tail sup; the `≤ N` small-lag terms (the last `N`) by the dominator `D`.
The bounds are required *along the orbit* (`hΨ`, `hD`). -/
private lemma abs_makerSum_le {x : α}
    (hΨ : ∀ j : ℕ, ∀ M m, M ≤ m → |Fk hT P m (T^[j] x)| ≤ Psi hT P M (T^[j] x))
    (hD : ∀ j : ℕ, ∀ m, |Fk hT P m (T^[j] x)| ≤ dom hT P (T^[j] x)) (N n : ℕ) :
    |makerSum hT P n x|
      ≤ (∑ j ∈ Finset.range n, Psi hT P (N + 1) (T^[j] x))
        + ∑ j ∈ Finset.Ico (n - N) n, dom hT P (T^[j] x) := by
  classical
  -- Split the LHS sum `∑_{range n}|Fk| = ∑_{Ico 0 (n-N)}|Fk| + ∑_{Ico(n-N) n}|Fk|`.
  have hsplitLHS : ∑ j ∈ Finset.range n, |Fk hT P (n - j) (T^[j] x)|
      = (∑ j ∈ Finset.Ico 0 (n - N), |Fk hT P (n - j) (T^[j] x)|)
        + ∑ j ∈ Finset.Ico (n - N) n, |Fk hT P (n - j) (T^[j] x)| := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (n - N)) (Nat.sub_le n N)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [hsplitLHS]
  refine add_le_add ?_ ?_
  · -- Large lag `j < n - N` ⟹ `n - j ≥ N + 1`; bound by `Ψ_{N+1}(Tʲx)`, then extend to all `j < n`.
    calc ∑ j ∈ Finset.Ico 0 (n - N), |Fk hT P (n - j) (T^[j] x)|
        ≤ ∑ j ∈ Finset.Ico 0 (n - N), Psi hT P (N + 1) (T^[j] x) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjlt : j < n - N := (Finset.mem_Ico.1 hj).2
          exact hΨ j (N + 1) (n - j) (by omega)
      _ ≤ ∑ j ∈ Finset.range n, Psi hT P (N + 1) (T^[j] x) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => Psi_nonneg hT P (N + 1) _)
          rw [Finset.range_eq_Ico]
          exact Finset.Ico_subset_Ico (le_refl 0) (Nat.sub_le n N)
  · -- Small lag (last `N` terms): bound each `|F_{n-j}(Tʲx)| ≤ D(Tʲx)`.
    exact Finset.sum_le_sum fun j _ => hD j (n - j)

omit mα [StandardBorelSpace α] [IsProbabilityMeasure μ] in
/-- `∑_{j ∈ Ico(n−N) n} f(Tʲx) = Sₙ(f) − S_{n−N}(f)` (a `birkhoffSum` difference). -/
private lemma sum_Ico_eq_birkhoffSum_sub {f : α → ℝ} (N n : ℕ) (x : α) :
    ∑ j ∈ Finset.Ico (n - N) n, f (T^[j] x)
      = birkhoffSum T f n x - birkhoffSum T f (n - N) x := by
  rw [eq_sub_iff_add_eq, birkhoffSum, birkhoffSum, add_comm, ← Finset.sum_range_add_sum_Ico _
    (Nat.sub_le n N)]

omit mα [StandardBorelSpace α] in
/-- `(1/n)·S_{n−N}(f) x → ∫ f` (the shifted Birkhoff average has the same limit). -/
private lemma tendsto_birkhoffSum_shift_div {f : α → ℝ} (L : ℝ) (N : ℕ) (x : α)
    (hf : Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * birkhoffSum T f (n - N) x) atTop (𝓝 L) := by
  -- `(1/n)·S_{n-N} = ((n-N)/n)·A_{n-N}` and `A_{n-N} → L`, `(n-N)/n → 1`.
  have hAshift : Tendsto (fun n => birkhoffAverage ℝ T f (n - N) x) atTop (𝓝 L) :=
    hf.comp (tendsto_sub_atTop_nat N)
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) - N) / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - (N : ℝ) / n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  have hprod := hratio.mul hAshift
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (N + 1)] with n hNn
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hNn
  have hnN : N ≤ n := le_of_lt (Nat.lt_of_succ_le hNn)
  have hncast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
  have hsubcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := Nat.cast_sub hnN
  have hsubpos : (0 : ℝ) < (n : ℝ) - N := by
    have : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hNn
    linarith
  simp only [birkhoffAverage, smul_eq_mul]
  rw [show ((n : ℝ) - N) / n * (((n - N : ℕ) : ℝ)⁻¹ * birkhoffSum T f (n - N) x)
      = (n : ℝ)⁻¹ * birkhoffSum T f (n - N) x by
    rw [hsubcast]
    field_simp]

/-- **Leaf 2 (Maker/Breiman dominated-Cesàro).** For ergodic `T`, the Cesàro tail of the Breiman
telescoping vanishes a.e.:
`(1/n)·∑_{j<n}(g_{n−j} − g∞)(Tʲx) → 0`. -/
theorem makerTail (herg : Ergodic T μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * makerSum hT P n x) atTop (𝓝 0) := by
  classical
  -- The dominator's Birkhoff average and the per-`M` sup-tail Birkhoff averages converge a.e.
  have hbD : ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T (dom hT P) n x) atTop
      (𝓝 (∫ y, dom hT P y ∂μ)) :=
    tendsto_birkhoffAverage_ae_integral herg (integrable_dom hT P)
  have hbΨ : ∀ M, ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T (Psi hT P M) n x) atTop
      (𝓝 (∫ y, Psi hT P M y ∂μ)) := fun M =>
    tendsto_birkhoffAverage_ae_integral herg
      ((integrable_dom hT P).mono' (measurable_Psi hT P M).aestronglyMeasurable
        (by filter_upwards [PsiE_le_dom hT P] with x hx
            rw [Real.norm_eq_abs, abs_of_nonneg (Psi_nonneg hT P M x), Psi]
            calc (PsiE hT P M x).toReal ≤ (ENNReal.ofReal (dom hT P x)).toReal :=
                  ENNReal.toReal_mono ENNReal.ofReal_ne_top (hx M)
              _ = dom hT P x := ENNReal.toReal_ofReal (dom_nonneg hT P x)))
  -- Orbit-a.e. bounds.
  have hΨorb := ae_forall_orbit hT (abs_Fk_le_Psi_of_le hT P)
  have hDorb := ae_forall_orbit hT (abs_Fk_le_dom hT P)
  filter_upwards [hbD, ae_all_iff.2 hbΨ, hΨorb, hDorb] with x hbDx hbΨx hΨorbx hDorbx
  -- Tendsto to 0 via the `ε`-`N` characterization.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- pick `N` with `∫ Ψ_{N+1} < ε/2`.
  have hIΨ : Tendsto (fun M => ∫ y, Psi hT P M y ∂μ) atTop (𝓝 0) := tendsto_integral_Psi_zero hT P
  rw [Metric.tendsto_atTop] at hIΨ
  obtain ⟨N, hN⟩ := hIΨ (ε / 2) (by linarith)
  have hIΨN : ∫ y, Psi hT P (N + 1) y ∂μ < ε / 2 := by
    have := hN (N + 1) (Nat.le_succ N)
    rw [Real.dist_eq, sub_zero] at this
    have hnn : 0 ≤ ∫ y, Psi hT P (N + 1) y ∂μ := integral_nonneg fun y => Psi_nonneg hT P (N + 1) y
    rw [abs_of_nonneg hnn] at this
    exact this
  -- The bounding RHS `→ ∫ Ψ_{N+1} < ε/2`, hence eventually `< ε`.
  set L := ∫ y, Psi hT P (N + 1) y ∂μ with hL
  have hRHStend : Tendsto (fun n => birkhoffAverage ℝ T (Psi hT P (N + 1)) n x
      + (birkhoffAverage ℝ T (dom hT P) n x
        - (n : ℝ)⁻¹ * birkhoffSum T (dom hT P) (n - N) x)) atTop
      (𝓝 (L + (∫ y, dom hT P y ∂μ - ∫ y, dom hT P y ∂μ))) := by
    exact (hbΨx (N + 1)).add (hbDx.sub
      (tendsto_birkhoffSum_shift_div (∫ y, dom hT P y ∂μ) N x hbDx))
  rw [sub_self, add_zero] at hRHStend
  rw [Metric.tendsto_atTop] at hRHStend
  obtain ⟨N₂, hN₂⟩ := hRHStend (ε / 2) (by linarith)
  refine ⟨max (max N N₂) 1, fun n hn => ?_⟩
  have hNn : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN₂n : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hn)
  -- `|(1/n)·makerSum| ≤ RHS_N(n) < ε`.
  rw [Real.dist_eq, sub_zero]
  have hncast : (0 : ℝ) < n := by exact_mod_cast hn0
  have hRHS_lt : birkhoffAverage ℝ T (Psi hT P (N + 1)) n x
      + (birkhoffAverage ℝ T (dom hT P) n x
        - (n : ℝ)⁻¹ * birkhoffSum T (dom hT P) (n - N) x) < ε := by
    have hd := hN₂ n hN₂n
    rw [Real.dist_eq] at hd
    have := (abs_lt.1 hd).2
    linarith
  -- The pointwise bound.
  have hbound : |(n : ℝ)⁻¹ * makerSum hT P n x|
      ≤ birkhoffAverage ℝ T (Psi hT P (N + 1)) n x
        + (birkhoffAverage ℝ T (dom hT P) n x
          - (n : ℝ)⁻¹ * birkhoffSum T (dom hT P) (n - N) x) := by
    rw [abs_mul, abs_inv, abs_of_nonneg hncast.le]
    have hmaker := abs_makerSum_le hT P (x := x) hΨorbx hDorbx N n
    have hAΨ : ∑ j ∈ Finset.range n, Psi hT P (N + 1) (T^[j] x)
        = (n : ℝ) * birkhoffAverage ℝ T (Psi hT P (N + 1)) n x := by
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ hncast.ne', one_mul]
    have hBdom : ∑ j ∈ Finset.Ico (n - N) n, dom hT P (T^[j] x)
        = birkhoffSum T (dom hT P) n x - birkhoffSum T (dom hT P) (n - N) x :=
      sum_Ico_eq_birkhoffSum_sub (f := dom hT P) N n x
    rw [inv_mul_le_iff₀ hncast]
    calc |makerSum hT P n x|
        ≤ (∑ j ∈ Finset.range n, Psi hT P (N + 1) (T^[j] x))
          + ∑ j ∈ Finset.Ico (n - N) n, dom hT P (T^[j] x) := hmaker
      _ = (n : ℝ) * (birkhoffAverage ℝ T (Psi hT P (N + 1)) n x
          + (birkhoffAverage ℝ T (dom hT P) n x
            - (n : ℝ)⁻¹ * birkhoffSum T (dom hT P) (n - N) x)) := by
          rw [hAΨ, hBdom]
          simp only [birkhoffAverage, smul_eq_mul]
          field_simp
  exact lt_of_le_of_lt hbound hRHS_lt

end Leaf2

section Assembly

/-! ### Assembling the unconditional pointwise SMB

With both analytic leaves discharged — Leaf 1 gives `g* ∈ L¹` (`lintegral_condInfoMaxFun_lt_top`),
Leaf 2 gives the dominated-Cesàro vanishing (`makerTail`) — the Cesàro tail hypothesis of
`ae_tendsto_div_infoFun_of_tail` is now *proved*.  The Breiman tail decomposition
`(1/n)·iₙ(x) − A_n(g∞)(x) = (1/n)∑_{j<n}(g_{n−j} − g∞)(Tʲx)` (which holds a.e. via the
measure-algebra telescoping `infoWeight_succ_eq`, recorded here as the hypothesis `hbreiman`) then
yields the unconditional pointwise SMB `(1/n)·iₙ(x) → h(P,T)`. -/

variable [Nonempty ι]

omit [Nonempty ι] in
/-- **Leaf 2 in the form consumed by `ae_tendsto_div_infoFun_of_tail`.** The Cesàro tail of the
Breiman split — the difference between the information average `(1/n)∑_{j<n} g_{n−j}(Tʲx)` and the
limit Birkhoff average `A_n(g∞)` — vanishes a.e. -/
theorem ae_tendsto_breiman_tail (herg : Ergodic T μ) (P : MeasurePartition μ ι) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * (∑ j ∈ Finset.range n,
          condInfoFun (𝒜 := condLevelSigma herg.toMeasurePreserving P (n - j)) P (T^[j] x))
        - birkhoffAverage ℝ T
            (condInfoFun (𝒜 := futureSigma herg.toMeasurePreserving P) P) n x) atTop (𝓝 0) := by
  have hmp := herg.toMeasurePreserving
  filter_upwards [makerTail hmp P herg] with x hx
  refine hx.congr fun n => ?_
  -- `(1/n)·makerSum = (1/n)∑ g_{n-j}(Tʲx) − A_n(g∞)`.
  simp only [makerSum, Fk, gk, ginf, Finset.sum_sub_distrib, mul_sub, birkhoffAverage,
    birkhoffSum, smul_eq_mul]

/-- **Pointwise Shannon–McMillan–Breiman (unconditional, given the Breiman telescoping `R2`).**
For ergodic `T` and any sequence `iₙ` satisfying the a.e. Breiman telescoping
`iₙ(x) = ∑_{j<n} g_{n−j}(Tʲx)` (`hbreiman`), the information averages `(1/n)·iₙ(x)` converge
`μ`-a.e. to the Kolmogorov–Sinai entropy `h(P,T) = ksEntropyPartition hT P`.

Both analytic leaves are now proved: Leaf 1 (`lintegral_condInfoMaxFun_lt_top`, `g* ∈ L¹`) and
Leaf 2 (`ae_tendsto_breiman_tail`, the Maker dominated-Cesàro tail).  The only remaining input is
the measure-algebra telescoping `hbreiman` (Breiman's `R2`, not an analytic leaf). -/
theorem ae_tendsto_div_infoFun (herg : Ergodic T μ) (P : MeasurePartition μ ι)
    (infoFun_n : ℕ → α → ℝ)
    (hbreiman : ∀ᵐ x ∂μ, ∀ n, infoFun_n n x
      = ∑ j ∈ Finset.range n,
          condInfoFun (𝒜 := condLevelSigma herg.toMeasurePreserving P (n - j)) P (T^[j] x)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => infoFun_n n x / n) atTop
      (𝓝 (ksEntropyPartition herg.toMeasurePreserving P)) := by
  refine ae_tendsto_div_infoFun_of_tail herg P infoFun_n ?_
  filter_upwards [ae_tendsto_breiman_tail herg P, hbreiman] with x hx hbx
  refine hx.congr fun n => ?_
  rw [hbx n, div_eq_inv_mul]

/-- **In-measure / upper-equipartition corollary.** For ergodic `T` and the Breiman telescoping,
for every `δ > 0` the measure of `{x : (1/n)·iₙ(x) > h(P,T) + δ}` tends to `0`: a.e. convergence
(`ae_tendsto_div_infoFun`) implies convergence in measure of the deviation set. -/
theorem tendsto_measure_div_infoFun_gt (herg : Ergodic T μ) (P : MeasurePartition μ ι)
    (infoFun_n : ℕ → α → ℝ)
    (hbreiman : ∀ᵐ x ∂μ, ∀ n, infoFun_n n x
      = ∑ j ∈ Finset.range n,
          condInfoFun (𝒜 := condLevelSigma herg.toMeasurePreserving P (n - j)) P (T^[j] x))
    (hmeas : ∀ n, Measurable (infoFun_n n)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => μ {x | ksEntropyPartition herg.toMeasurePreserving P + δ < infoFun_n n x / n})
      atTop (𝓝 0) := by
  set h := ksEntropyPartition herg.toMeasurePreserving P with hh
  set A : ℕ → Set α := fun n => {x | h + δ < infoFun_n n x / n} with hA
  have hmeasSet : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_lt measurable_const ((hmeas n).div measurable_const)
  -- a.e. convergence ⟹ for a.e. `x`, eventually `x ∉ Aₙ` (the limit deviation set is empty).
  have hlim : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ (∅ : Set α)) := by
    filter_upwards [ae_tendsto_div_infoFun herg P infoFun_n hbreiman] with x hx
    rw [Metric.tendsto_atTop] at hx
    obtain ⟨N, hN⟩ := hx δ hδ
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [hA, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have hd := hN n hn
    rw [Real.dist_eq, abs_lt] at hd
    linarith [hd.2]
  have hconv := MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := μ) atTop (A := (∅ : Set α)) (As := A) MeasurableSet.empty hmeasSet hlim
  simpa only [measure_empty] using hconv

end Assembly

end Oseledets.Krieger
