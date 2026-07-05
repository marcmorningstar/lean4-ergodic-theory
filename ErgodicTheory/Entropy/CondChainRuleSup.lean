/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondChainRule
import ErgodicTheory.Entropy.CondGivenPartitionBridge
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The σ-algebra-form conditional chain rule (conditional analog of the W2 bridge)

This module proves the **conditional analog** of the absolute W2 bridge lemma
`condEntropyGivenPartition_eq_condEntropy_generated` (`CondGivenPartitionBridge`): the
additive-over-cells second summand of the *conditional* chain rule, conditioned on a fixed
sub-σ-algebra `𝒜`, equals conditioning on the joined σ-algebra `σ(P) ⊔ 𝒜`:

`condEntropyGivenPartitionCond μ 𝒜 P.cells Q.cells = condEntropy μ (σ(P) ⊔ 𝒜) Q.cells`   (A0)

together with the σ-algebra-form conditional chain rule

`H(P ∨ Q | 𝒜) = H(P | 𝒜) + H(Q | σ(P) ⊔ 𝒜)`.   (A0')

## Proof outline

The crux (A0) is a disintegration/tower identity for the regular conditional kernel of the join.
We introduce the **conditional candidate** `gⱼ(ω) = ∑ᵢ 𝟙_{Pᵢ}(ω) · r_{ij}(ω)`, where
`r_{ij}(ω) = condExpKernel μ 𝒜 ω (Pᵢ ∩ Qⱼ) / condExpKernel μ 𝒜 ω Pᵢ` is the cell-conditional
ratio (`condCellRatio`). This candidate is `(σ(P) ⊔ 𝒜)`-strongly measurable and is shown to be a
version of `μ⟦Qⱼ | σ(P) ⊔ 𝒜⟧` via `ae_eq_condExp_of_forall_setIntegral_eq`. Its set-integral
hypothesis — `∫ x in s, gⱼ x ∂μ = μ(s ∩ Qⱼ).toReal` for every `(σ(P) ⊔ 𝒜)`-measurable `s` — is
established by `MeasurableSpace.induction_on_inter` on the rectangle π-system
`{v ∩ w : v ∈ σ(P), w ∈ 𝒜}` (which generates `σ(P) ⊔ 𝒜`). The base case combines the atom
property of `σ(P)` (`generatedSigmaAlgebra_atom`) with the pull-out property of conditional
expectation (`condExp_mul_of_aestronglyMeasurable_right`) and the kernel/condExp bridge
(`condExpKernel_ae_eq_condExp`).

Identifying the join kernel with `gⱼ`, the `condEntropy` integrand becomes `∑ⱼ negMulLog (gⱼ ω)`,
which on each cell `Pᵢ` equals `condEntropyOnCell (condExpKernel μ 𝒜 ω) Pᵢ Q`; a final pull-out
recovers the `condExpKernel μ 𝒜`-weighted average `condEntropyGivenPartitionCond μ 𝒜 P Q`.

## Main results

* `ErgodicTheory.Entropy.condEntropyGivenPartitionCond_eq_condEntropy_sup` (A0).
* `ErgodicTheory.Entropy.condEntropy_join_eq_sup` (A0').
-/

open MeasureTheory Function Filter ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace ErgodicTheory.Entropy

noncomputable section

-- The conditioning σ-algebra `𝒜` is declared BEFORE `[mα]` so the ambient `mα` keeps higher
-- instance priority (CLAUDE-trap); we use this section `𝒜` throughout rather than a fresh
-- explicit `MeasurableSpace α` parameter (which would shadow `mα` as a local instance).
variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

/-- The cell-conditional ratio `condExpKernel μ 𝒜 ω (b ∩ t) / condExpKernel μ 𝒜 ω b`: the
conditional probability of `t` given the cell `b`, computed against the regular conditional
probability `condExpKernel μ 𝒜 ω`. -/
def condCellRatio (μ : Measure α) [IsFiniteMeasure μ] (b t : Set α) : α → ℝ :=
  fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (b ∩ t)).toReal / (@condExpKernel α mα _ μ _ 𝒜 ω b).toReal

/-- The conditional candidate for `μ⟦t | σ(P) ⊔ 𝒜⟧`: the function taking the cell-conditional ratio
`condCellRatio μ (P.cells i) t ω` on each cell `P.cells i`. -/
def condCandidateSup (μ : Measure α) [IsFiniteMeasure μ] [Fintype ι]
    (P : MeasurePartition μ ι) (t : Set α) : α → ℝ :=
  fun ω => ∑ i, (P.cells i).indicator (condCellRatio (𝒜 := 𝒜) μ (P.cells i) t) ω

/-- The per-cell conditional entropy of a family `u` against `condExpKernel μ 𝒜 ω`, expressed via
`condCellRatio`. Definitionally `condEntropyOnCell (condExpKernel μ 𝒜 ω) b u`. -/
def condCellEntropy (μ : Measure α) [IsFiniteMeasure μ] [Fintype κ] (b : Set α) (u : κ → Set α) :
    α → ℝ :=
  fun ω => ∑ j, Real.negMulLog (condCellRatio (𝒜 := 𝒜) μ b (u j) ω)

/-! ### Basic properties of the cell-conditional ratio. -/

lemma condCellRatio_nonneg (μ : Measure α) [IsFiniteMeasure μ] (b t : Set α) (ω : α) :
    0 ≤ condCellRatio (𝒜 := 𝒜) μ b t ω :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma condCellRatio_le_one (μ : Measure α) [IsFiniteMeasure μ] (b t : Set α) (ω : α) :
    condCellRatio (𝒜 := 𝒜) μ b t ω ≤ 1 := by
  simp only [condCellRatio]
  rcases eq_or_ne (@condExpKernel α mα _ μ _ 𝒜 ω b).toReal 0 with hY | hY
  · rw [hY, div_zero]; exact zero_le_one
  · rw [div_le_one (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hY))]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)

/-- The key cancellation: `condCellRatio · (κ b) = κ (b ∩ t)` pointwise. -/
lemma condCellRatio_mul_toReal (μ : Measure α) [IsFiniteMeasure μ] (b t : Set α) (ω : α) :
    condCellRatio (𝒜 := 𝒜) μ b t ω * (@condExpKernel α mα _ μ _ 𝒜 ω b).toReal
      = (@condExpKernel α mα _ μ _ 𝒜 ω (b ∩ t)).toReal := by
  simp only [condCellRatio]
  rcases eq_or_ne (@condExpKernel α mα _ μ _ 𝒜 ω b).toReal 0 with hY | hY
  · have hb0 : @condExpKernel α mα _ μ _ 𝒜 ω b = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 hY).resolve_right (measure_ne_top _ _)
    have hbt0 : @condExpKernel α mα _ μ _ 𝒜 ω (b ∩ t) = 0 := by
      have hle : @condExpKernel α mα _ μ _ 𝒜 ω (b ∩ t) ≤ @condExpKernel α mα _ μ _ 𝒜 ω b :=
        measure_mono Set.inter_subset_left
      rw [hb0, le_zero_iff] at hle; exact hle
    rw [hY, div_zero, mul_zero, hbt0, ENNReal.toReal_zero]
  · rw [div_mul_cancel₀ _ hY]

lemma stronglyMeasurable_condCellRatio (μ : Measure α) [IsFiniteMeasure μ] {b t : Set α}
    (hb : MeasurableSet b) (ht : MeasurableSet t) :
    StronglyMeasurable[𝒜] (condCellRatio (𝒜 := 𝒜) μ b t) := by
  unfold condCellRatio
  exact Measurable.stronglyMeasurable (Measurable.div
    (measurable_condExpKernel (μ := μ) (m := 𝒜) (hb.inter ht)).ennreal_toReal
    (measurable_condExpKernel (μ := μ) (m := 𝒜) hb).ennreal_toReal)

lemma integrable_condCellRatio (μ : Measure α) [IsFiniteMeasure μ] (h𝒜 : 𝒜 ≤ mα) {b t : Set α}
    (hb : MeasurableSet b) (ht : MeasurableSet t) :
    Integrable (condCellRatio (𝒜 := 𝒜) μ b t) μ := by
  refine Integrable.of_bound
    ((stronglyMeasurable_condCellRatio μ hb ht).mono h𝒜).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (condCellRatio_nonneg μ b t ω)]
  exact condCellRatio_le_one μ b t ω

/-! ### Properties of the per-cell conditional entropy. -/

lemma condCellEntropy_nonneg (μ : Measure α) [IsFiniteMeasure μ] [Fintype κ] (b : Set α)
    (u : κ → Set α) (ω : α) : 0 ≤ condCellEntropy (𝒜 := 𝒜) μ b u ω :=
  Finset.sum_nonneg fun j _ => Real.negMulLog_nonneg (condCellRatio_nonneg μ b (u j) ω)
    (condCellRatio_le_one μ b (u j) ω)

lemma condCellEntropy_le_card (μ : Measure α) [IsFiniteMeasure μ] [Fintype κ] (b : Set α)
    (u : κ → Set α) (ω : α) : condCellEntropy (𝒜 := 𝒜) μ b u ω ≤ Fintype.card κ := by
  simp only [condCellEntropy]
  calc ∑ j, Real.negMulLog (condCellRatio (𝒜 := 𝒜) μ b (u j) ω)
      ≤ ∑ _j : κ, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
        le_trans (Real.negMulLog_le_one_sub_self (condCellRatio_nonneg (𝒜 := 𝒜) μ b (u j) ω))
          (by linarith [condCellRatio_nonneg (𝒜 := 𝒜) μ b (u j) ω])
    _ = Fintype.card κ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma stronglyMeasurable_condCellEntropy (μ : Measure α) [IsFiniteMeasure μ] [Fintype κ]
    {b : Set α} (hb : MeasurableSet b) {u : κ → Set α} (hu : ∀ j, MeasurableSet (u j)) :
    StronglyMeasurable[𝒜] (condCellEntropy (𝒜 := 𝒜) μ b u) :=
  Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    Real.continuous_negMulLog.comp_stronglyMeasurable (stronglyMeasurable_condCellRatio μ hb (hu j))

lemma integrable_condCellEntropy (μ : Measure α) [IsFiniteMeasure μ] (h𝒜 : 𝒜 ≤ mα) [Fintype κ]
    {b : Set α} (hb : MeasurableSet b) {u : κ → Set α} (hu : ∀ j, MeasurableSet (u j)) :
    Integrable (condCellEntropy (𝒜 := 𝒜) μ b u) μ := by
  refine Integrable.of_bound
    ((stronglyMeasurable_condCellEntropy μ hb hu).mono h𝒜).aestronglyMeasurable
    (Fintype.card κ) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (condCellEntropy_nonneg μ b u ω)]
  exact condCellEntropy_le_card μ b u ω

/-! ### The "on cell" reduction of a sum of cell-indicators. -/

omit 𝒜 [StandardBorelSpace α] in
/-- On the cell `P.cells k`, a sum `∑ᵢ 𝟙_{Pᵢ} · F i` equals `F k` almost everywhere. -/
lemma sum_indicator_ae_eq_on_cell (μ : Measure α) [IsFiniteMeasure μ] [Fintype ι]
    (P : MeasurePartition μ ι) (F : ι → α → ℝ) (k : ι) :
    (fun ω => ∑ i, (P.cells i).indicator (F i) ω) =ᵐ[μ.restrict (P.cells k)] F k := by
  have hnull : ∀ i, i ≠ k → ∀ᵐ ω ∂μ.restrict (P.cells k), ω ∉ P.cells i := by
    intro i hik
    rw [ae_restrict_iff' (P.measurable k)]
    have hnk : μ (P.cells k ∩ P.cells i) = 0 := P.aedisjoint (Ne.symm hik)
    have hae : ∀ᵐ ω ∂μ, ω ∉ P.cells k ∩ P.cells i := by rw [ae_iff]; simpa using hnk
    filter_upwards [hae] with ω hω hωk
    simp only [Set.mem_inter_iff, not_and] at hω
    exact hω hωk
  have hnull' : ∀ᵐ ω ∂μ.restrict (P.cells k), ∀ i, i ≠ k → ω ∉ P.cells i := by
    rw [ae_all_iff]; intro i
    by_cases hik : i = k
    · subst hik; exact Eventually.of_forall fun ω h => absurd rfl h
    · filter_upwards [hnull i hik] with ω hω _ using hω
  have hself : ∀ᵐ ω ∂μ.restrict (P.cells k), ω ∈ P.cells k := by
    rw [ae_restrict_iff' (P.measurable k)]; exact Eventually.of_forall fun ω h => h
  filter_upwards [hnull', hself] with ω hω hωk
  rw [Finset.sum_eq_single k]
  · rw [Set.indicator_of_mem hωk]
  · intro i _ hik; rw [Set.indicator_of_notMem (hω i hik)]
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ### Measurability and integrability of the conditional candidate. -/

lemma stronglyMeasurable_condCandidateSup (μ : Measure α) [IsFiniteMeasure μ] [Fintype ι]
    (P : MeasurePartition μ ι) {t : Set α} (ht : MeasurableSet t) :
    StronglyMeasurable[generatedSigmaAlgebra μ P ⊔ 𝒜] (condCandidateSup (𝒜 := 𝒜) μ P t) := by
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  exact ((stronglyMeasurable_condCellRatio μ (P.measurable i) ht).mono
      (le_sup_right : 𝒜 ≤ generatedSigmaAlgebra μ P ⊔ 𝒜)).indicator
    ((le_sup_left : generatedSigmaAlgebra μ P ≤ generatedSigmaAlgebra μ P ⊔ 𝒜) _
      (measurableSet_generatedSigmaAlgebra_cell P i))

lemma integrable_condCandidateSup (μ : Measure α) [IsFiniteMeasure μ] (h𝒜 : 𝒜 ≤ mα) [Fintype ι]
    (P : MeasurePartition μ ι) {t : Set α} (ht : MeasurableSet t) :
    Integrable (condCandidateSup (𝒜 := 𝒜) μ P t) μ :=
  integrable_finsetSum _ fun i _ =>
    (integrable_condCellRatio μ h𝒜 (P.measurable i) ht).indicator (P.measurable i)

/-! ### The per-cell set-integral identity (clean pull-out building block). -/

/-- **Per-cell set-integral.** For `a ∈ 𝒜`, the set-integral of `condCellRatio μ b t` over
`a ∩ b` equals `μ(a ∩ b ∩ t)`. -/
lemma condCell_setIntegral (μ : Measure α) [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα) {a b t : Set α}
    (ha : MeasurableSet[𝒜] a) (hb : MeasurableSet b) (ht : MeasurableSet t) :
    ∫ x in a ∩ b, condCellRatio (𝒜 := 𝒜) μ b t x ∂μ = (μ (a ∩ b ∩ t)).toReal := by
  have hcrint : Integrable (condCellRatio (𝒜 := 𝒜) μ b t) μ := integrable_condCellRatio μ h𝒜 hb ht
  have hgint : Integrable (b.indicator (condCellRatio (𝒜 := 𝒜) μ b t)) μ := hcrint.indicator hb
  have hprod : b.indicator (condCellRatio (𝒜 := 𝒜) μ b t)
      = fun ω => b.indicator (fun _ => (1 : ℝ)) ω * condCellRatio (𝒜 := 𝒜) μ b t ω := by
    funext ω; by_cases h : ω ∈ b <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hpull : μ[b.indicator (condCellRatio (𝒜 := 𝒜) μ b t) | 𝒜]
      =ᵐ[μ] fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (b ∩ t)).toReal := by
    have h1 : μ[b.indicator (condCellRatio (𝒜 := 𝒜) μ b t) | 𝒜]
        =ᵐ[μ] fun ω => μ[b.indicator (fun _ => (1 : ℝ)) | 𝒜] ω
          * condCellRatio (𝒜 := 𝒜) μ b t ω := by
      have hfg : Integrable (fun ω => b.indicator (fun _ => (1 : ℝ)) ω
          * condCellRatio (𝒜 := 𝒜) μ b t ω) μ := by rw [← hprod]; exact hgint
      rw [hprod]
      exact condExp_mul_of_aestronglyMeasurable_right
        (stronglyMeasurable_condCellRatio μ hb ht).aestronglyMeasurable
        hfg ((integrable_const 1).indicator hb)
    have h2 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω b).toReal)
        =ᵐ[μ] μ[b.indicator (fun _ => (1 : ℝ)) | 𝒜] := by
      have := condExpKernel_ae_eq_condExp (μ := μ) (m := 𝒜) h𝒜 hb
      simpa only [measureReal_def] using this
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1, ← hω2, mul_comm, condCellRatio_mul_toReal]
  have h3 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (b ∩ t)).toReal) =ᵐ[μ] μ⟦b ∩ t | 𝒜⟧ := by
    have := condExpKernel_ae_eq_condExp (μ := μ) (m := 𝒜) h𝒜 (hb.inter ht)
    simpa only [measureReal_def] using this
  rw [← setIntegral_indicator hb, ← setIntegral_condExp h𝒜 hgint ha,
    setIntegral_congr_ae (h𝒜 a ha) (hpull.mono fun ω h _ => h),
    setIntegral_congr_ae (h𝒜 a ha) (h3.mono fun ω h _ => h),
    setIntegral_condExp h𝒜 ((integrable_const (1 : ℝ)).indicator (hb.inter ht)) ha,
    setIntegral_indicator (hb.inter ht), setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    Set.inter_assoc]

/-! ### The set-integral of the candidate. -/

/-- **Rectangle base case.** For `v ∈ σ(P)` and `w ∈ 𝒜`, the set-integral of the conditional
candidate over `v ∩ w` equals `μ(v ∩ w ∩ t)`. -/
lemma condCandidateSup_setIntegral_rect (μ : Measure α) [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    [Fintype ι] (P : MeasurePartition μ ι) {t : Set α} (ht : MeasurableSet t) {v w : Set α}
    (hv : MeasurableSet[generatedSigmaAlgebra μ P] v) (hw : MeasurableSet[𝒜] w) :
    ∫ x in v ∩ w, condCandidateSup (𝒜 := 𝒜) μ P t x ∂μ = (μ (v ∩ w ∩ t)).toReal := by
  have hvm : MeasurableSet v := generatedSigmaAlgebra_le P v hv
  have hwm : MeasurableSet w := h𝒜 w hw
  simp only [condCandidateSup]
  rw [integral_finsetSum]
  swap
  · intro i _
    exact ((integrable_condCellRatio μ h𝒜 (P.measurable i) ht).indicator (P.measurable i)).restrict
  have hterm : ∀ i, ∫ x in v ∩ w, (P.cells i).indicator (condCellRatio (𝒜 := 𝒜) μ (P.cells i) t) x
        ∂μ = (μ (v ∩ w ∩ P.cells i ∩ t)).toReal := by
    intro i
    rw [setIntegral_indicator (P.measurable i)]
    rcases generatedSigmaAlgebra_atom P hv i with hatom | hatom
    · have h0 : μ (v ∩ w ∩ P.cells i) = 0 :=
        measure_mono_null (show v ∩ w ∩ P.cells i ⊆ P.cells i ∩ v from
          fun x hx => ⟨hx.2, hx.1.1⟩) hatom
      have h0' : μ (v ∩ w ∩ P.cells i ∩ t) = 0 :=
        measure_mono_null (show v ∩ w ∩ P.cells i ∩ t ⊆ P.cells i ∩ v from
          fun x hx => ⟨hx.1.2, hx.1.1.1⟩) hatom
      rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure, h0', ENNReal.toReal_zero]
    · have hsubE : v ∩ w ∩ P.cells i ⊆ w ∩ P.cells i := fun x hx => ⟨hx.1.2, hx.2⟩
      have hsub1 : (w ∩ P.cells i) \ (v ∩ w ∩ P.cells i) ⊆ P.cells i \ v :=
        fun x hx => ⟨hx.1.2, fun hxv => hx.2 ⟨⟨hxv, hx.1.1⟩, hx.1.2⟩⟩
      have hae : (v ∩ w ∩ P.cells i : Set α) =ᵐ[μ] (w ∩ P.cells i : Set α) := by
        rw [ae_eq_set]
        exact ⟨by rw [Set.diff_eq_empty.2 hsubE]; exact measure_empty,
          measure_mono_null hsub1 hatom⟩
      rw [setIntegral_congr_set hae, condCell_setIntegral μ h𝒜 hw (P.measurable i) ht]
      have hsub2 : (w ∩ P.cells i ∩ t) \ (v ∩ w ∩ P.cells i ∩ t) ⊆ P.cells i \ v :=
        fun x hx => ⟨hx.1.1.2, fun hxv => hx.2 ⟨⟨⟨hxv, hx.1.1.1⟩, hx.1.1.2⟩, hx.1.2⟩⟩
      have hsubE2 : v ∩ w ∩ P.cells i ∩ t ⊆ w ∩ P.cells i ∩ t :=
        fun x hx => ⟨⟨hx.1.1.2, hx.1.2⟩, hx.2⟩
      refine congrArg ENNReal.toReal (measure_congr ?_)
      rw [ae_eq_set]
      exact ⟨measure_mono_null hsub2 hatom,
        by rw [Set.diff_eq_empty.2 hsubE2]; exact measure_empty⟩
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    ← ENNReal.toReal_sum fun i _ => measure_ne_top μ _]
  congr 1
  rw [P.measure_eq_sum_inter ((hvm.inter hwm).inter ht)]
  exact Finset.sum_congr rfl fun i _ => by rw [Set.inter_right_comm]

/-- **Set-integral of the candidate on all join sets.** For every `(σ(P) ⊔ 𝒜)`-measurable `s`,
`∫ x in s, condCandidateSup μ P t x ∂μ = μ(s ∩ t)`. -/
lemma condCandidateSup_setIntegral (μ : Measure α) [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    [Fintype ι] (P : MeasurePartition μ ι) {t : Set α} (ht : MeasurableSet t) {s : Set α}
    (hs : MeasurableSet[generatedSigmaAlgebra μ P ⊔ 𝒜] s) :
    ∫ x in s, condCandidateSup (𝒜 := 𝒜) μ P t x ∂μ = (μ (s ∩ t)).toReal := by
  have hm : generatedSigmaAlgebra μ P ⊔ 𝒜 ≤ mα := sup_le (generatedSigmaAlgebra_le P) h𝒜
  have hgint : Integrable (condCandidateSup (𝒜 := 𝒜) μ P t) μ :=
    integrable_condCandidateSup μ h𝒜 P ht
  set Rect : Set (Set α) :=
    {u | ∃ v w, MeasurableSet[generatedSigmaAlgebra μ P] v ∧ MeasurableSet[𝒜] w ∧ u = v ∩ w}
    with hRect
  have hgenC : generatedSigmaAlgebra μ P ⊔ 𝒜 = generateFrom Rect := by
    refine le_antisymm (sup_le ?_ ?_) (generateFrom_le ?_)
    · refine generateFrom_le fun u hu => ?_
      obtain ⟨i, rfl⟩ := hu
      exact measurableSet_generateFrom ⟨P.cells i, Set.univ,
        measurableSet_generatedSigmaAlgebra_cell P i, MeasurableSet.univ, by rw [Set.inter_univ]⟩
    · intro u hu
      have hu' : u = ⋃ i, P.cells i ∩ u := by rw [← Set.iUnion_inter, P.cover, Set.univ_inter]
      rw [hu']
      exact MeasurableSet.iUnion fun i => measurableSet_generateFrom
        ⟨P.cells i, u, measurableSet_generatedSigmaAlgebra_cell P i, hu, rfl⟩
    · rintro u ⟨v, w, hv, hw, rfl⟩
      exact ((le_sup_left : generatedSigmaAlgebra μ P ≤ generatedSigmaAlgebra μ P ⊔ 𝒜) _ hv).inter
        ((le_sup_right : 𝒜 ≤ generatedSigmaAlgebra μ P ⊔ 𝒜) _ hw)
  have hpi : IsPiSystem Rect := by
    rintro u ⟨a, b, ha, hb, rfl⟩ v ⟨c, d, hc, hd, rfl⟩ -
    exact ⟨a ∩ c, b ∩ d, ha.inter hc, hb.inter hd, by rw [Set.inter_inter_inter_comm]⟩
  have hUniv : ∫ x, condCandidateSup (𝒜 := 𝒜) μ P t x ∂μ = (μ t).toReal := by
    have := condCandidateSup_setIntegral_rect μ h𝒜 P ht (v := Set.univ) (w := Set.univ)
      MeasurableSet.univ MeasurableSet.univ
    simpa using this
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => ∫ x in s, condCandidateSup (𝒜 := 𝒜) μ P t x ∂μ = (μ (s ∩ t)).toReal)
    hgenC hpi ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro u ⟨v, w, hv, hw, rfl⟩
    exact condCandidateSup_setIntegral_rect μ h𝒜 P ht hv hw
  · intro u hu hCu
    have hum : MeasurableSet u := hm u hu
    have hsplit : ∫ x in uᶜ, condCandidateSup (𝒜 := 𝒜) μ P t x ∂μ
        = ∫ x, condCandidateSup (𝒜 := 𝒜) μ P t x ∂μ
          - ∫ x in u, condCandidateSup (𝒜 := 𝒜) μ P t x ∂μ := by
      rw [eq_sub_iff_add_eq, add_comm, integral_add_compl hum hgint]
    have hut : uᶜ ∩ t = t \ u := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]; tauto
    have hut' : u ∩ t = t ∩ u := Set.inter_comm u t
    have hmeas : μ (t ∩ u) + μ (t \ u) = μ t := measure_inter_add_diff t hum
    rw [hsplit, hUniv, hCu, hut, hut', eq_comm, ← hmeas,
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
    ring
  · intro f hfd hfm hCf
    have hfm' : ∀ i, MeasurableSet (f i) := fun i => hm _ (hfm i)
    rw [integral_iUnion hfm' hfd hgint.integrableOn, Set.iUnion_inter,
      measure_iUnion (fun i j hij => (hfd hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i => (hfm' i).inter ht),
      ENNReal.tsum_toReal_eq fun i => measure_ne_top μ _]
    exact tsum_congr hCf

/-- **The candidate is a version of the join conditional expectation.** -/
lemma condCandidateSup_ae_eq_condExp (μ : Measure α) [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    [Fintype ι] (P : MeasurePartition μ ι) {t : Set α} (ht : MeasurableSet t) :
    condCandidateSup (𝒜 := 𝒜) μ P t =ᵐ[μ] μ⟦t | generatedSigmaAlgebra μ P ⊔ 𝒜⟧ := by
  have hm : generatedSigmaAlgebra μ P ⊔ 𝒜 ≤ mα := sup_le (generatedSigmaAlgebra_le P) h𝒜
  refine ae_eq_condExp_of_forall_setIntegral_eq hm ((integrable_const (1 : ℝ)).indicator ht)
    (fun s _ _ => (integrable_condCandidateSup μ h𝒜 P ht).integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_condCandidateSup μ P ht).aestronglyMeasurable
  rw [condCandidateSup_setIntegral μ h𝒜 P ht hs, setIntegral_indicator ht, setIntegral_const,
    smul_eq_mul, mul_one, measureReal_def]

/-! ### The keystone (A0) and the σ-algebra-form chain rule (A0'). -/

/-- **A0 (conditional W2 bridge — KEYSTONE).** The additive-over-cells second summand of the
conditional chain rule, conditioned on `𝒜`, equals conditioning on the joined σ-algebra
`σ(P) ⊔ 𝒜`. -/
theorem condEntropyGivenPartitionCond_eq_condEntropy_sup [Fintype ι] [Fintype κ]
    {μ : Measure α} [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    condEntropyGivenPartitionCond μ 𝒜 P.cells Q.cells
      = condEntropy μ (generatedSigmaAlgebra μ P ⊔ 𝒜) Q.cells := by
  have hm : generatedSigmaAlgebra μ P ⊔ 𝒜 ≤ mα := sup_le (generatedSigmaAlgebra_le P) h𝒜
  have hcand : ∀ j, (fun ω => (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ P ⊔ 𝒜) ω
        (Q.cells j)).toReal) =ᵐ[μ] condCandidateSup (𝒜 := 𝒜) μ P (Q.cells j) := by
    intro j
    have h1 := condExpKernel_ae_eq_condExp (μ := μ) (m := generatedSigmaAlgebra μ P ⊔ 𝒜) hm
      (Q.measurable j)
    have h2 := (condCandidateSup_ae_eq_condExp μ h𝒜 P (Q.measurable j)).symm
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [measureReal_def] at hω1
    rw [hω1, hω2]
  have hRHS : condEntropy μ (generatedSigmaAlgebra μ P ⊔ 𝒜) Q.cells
      = ∫ ω, ∑ j, Real.negMulLog (condCandidateSup (𝒜 := 𝒜) μ P (Q.cells j) ω) ∂μ := by
    rw [condEntropy_def]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hcand] with ω hω
    exact Finset.sum_congr rfl fun j _ => by rw [hω j]
  have hcell : (fun ω => ∑ j, Real.negMulLog (condCandidateSup (𝒜 := 𝒜) μ P (Q.cells j) ω))
      =ᵐ[μ] fun ω => ∑ k, (P.cells k).indicator
        (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells) ω := by
    have hcombine : (fun ω => ∑ j, Real.negMulLog (condCandidateSup (𝒜 := 𝒜) μ P (Q.cells j) ω))
        =ᵐ[μ.restrict (⋃ i, P.cells i)] fun ω => ∑ k, (P.cells k).indicator
          (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells) ω := by
      rw [ae_eq_restrict_iUnion_iff]
      intro k
      have hL : (fun ω => ∑ j, Real.negMulLog (condCandidateSup (𝒜 := 𝒜) μ P (Q.cells j) ω))
          =ᵐ[μ.restrict (P.cells k)] condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells := by
        have hj : ∀ j, (fun ω => condCandidateSup (𝒜 := 𝒜) μ P (Q.cells j) ω)
            =ᵐ[μ.restrict (P.cells k)] condCellRatio (𝒜 := 𝒜) μ (P.cells k) (Q.cells j) :=
          fun j => sum_indicator_ae_eq_on_cell μ P
            (fun i => condCellRatio (𝒜 := 𝒜) μ (P.cells i) (Q.cells j)) k
        filter_upwards [ae_all_iff.2 hj] with ω hω
        simp only [condCellEntropy]
        exact Finset.sum_congr rfl fun j _ => by rw [hω j]
      have hR : (fun ω => ∑ i, (P.cells i).indicator
            (condCellEntropy (𝒜 := 𝒜) μ (P.cells i) Q.cells) ω)
          =ᵐ[μ.restrict (P.cells k)] condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells :=
        sum_indicator_ae_eq_on_cell μ P (fun i => condCellEntropy (𝒜 := 𝒜) μ (P.cells i) Q.cells) k
      exact hL.trans hR.symm
    rwa [P.cover, Measure.restrict_univ] at hcombine
  have hint_eq : ∀ ω, condEntropyGivenPartition (@condExpKernel α mα _ μ _ 𝒜 ω) P.cells Q.cells
      = ∑ k, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells k)).toReal
          * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω := by
    intro ω
    simp only [condEntropyGivenPartition, condEntropyOnCell, condCellEntropy, condCellRatio]
  have hint_indic : ∀ k, Integrable
      ((P.cells k).indicator (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells)) μ := fun k =>
    (integrable_condCellEntropy μ h𝒜 (P.measurable k) Q.measurable).indicator (P.measurable k)
  have hint_wCk : ∀ k, Integrable (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells k)).toReal
      * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω) μ := by
    intro k
    have hmeas : AEStronglyMeasurable (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells k)).toReal
        * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω) μ :=
      AEStronglyMeasurable.mul
        (((measurable_condExpKernel (μ := μ) (m := 𝒜) (P.measurable k)).ennreal_toReal.mono h𝒜
          le_rfl).aestronglyMeasurable)
        ((stronglyMeasurable_condCellEntropy μ (P.measurable k) Q.measurable).mono
          h𝒜).aestronglyMeasurable
    refine Integrable.of_bound hmeas (Fintype.card κ) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (condCellEntropy_nonneg μ (P.cells k) Q.cells ω)]
    calc (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells k)).toReal
          * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω
        ≤ 1 * Fintype.card κ :=
          mul_le_mul (toReal_condExpKernel_le_one _ _)
            (condCellEntropy_le_card μ (P.cells k) Q.cells ω)
            (condCellEntropy_nonneg μ (P.cells k) Q.cells ω) zero_le_one
      _ = Fintype.card κ := one_mul _
  have hpullk : ∀ k, ∫ ω, (P.cells k).indicator
        (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells) ω ∂μ
      = ∫ ω, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells k)).toReal
          * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω ∂μ := by
    intro k
    have hprod : (P.cells k).indicator (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells)
        = fun ω => (P.cells k).indicator (fun _ => (1 : ℝ)) ω
          * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω := by
      funext ω; by_cases h : ω ∈ P.cells k <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have hCkint : Integrable (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells) μ :=
      integrable_condCellEntropy μ h𝒜 (P.measurable k) Q.measurable
    have hpull : μ[(P.cells k).indicator (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells) | 𝒜]
        =ᵐ[μ] fun ω => μ[(P.cells k).indicator (fun _ => (1 : ℝ)) | 𝒜] ω
            * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω := by
      have hfgk : Integrable (fun ω => (P.cells k).indicator (fun _ => (1 : ℝ)) ω
          * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω) μ := by
        rw [← hprod]; exact hCkint.indicator (P.measurable k)
      rw [hprod]
      exact condExp_mul_of_aestronglyMeasurable_right
        (stronglyMeasurable_condCellEntropy μ (P.measurable k) Q.measurable).aestronglyMeasurable
        hfgk ((integrable_const 1).indicator (P.measurable k))
    calc ∫ ω, (P.cells k).indicator (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells) ω ∂μ
        = ∫ ω, μ[(P.cells k).indicator (condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells) | 𝒜] ω ∂μ :=
          (integral_condExp h𝒜).symm
      _ = ∫ ω, μ[(P.cells k).indicator (fun _ => (1 : ℝ)) | 𝒜] ω
            * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω ∂μ := integral_congr_ae hpull
      _ = ∫ ω, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells k)).toReal
            * condCellEntropy (𝒜 := 𝒜) μ (P.cells k) Q.cells ω ∂μ := by
          refine integral_congr_ae ?_
          have h2 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells k)).toReal)
              =ᵐ[μ] μ[(P.cells k).indicator (fun _ => (1 : ℝ)) | 𝒜] := by
            have := condExpKernel_ae_eq_condExp (μ := μ) (m := 𝒜) h𝒜 (P.measurable k)
            simpa only [measureReal_def] using this
          filter_upwards [h2] with ω hω; rw [hω]
  have hLHS : condEntropyGivenPartitionCond μ 𝒜 P.cells Q.cells
      = ∫ ω, ∑ j, Real.negMulLog (condCandidateSup (𝒜 := 𝒜) μ P (Q.cells j) ω) ∂μ := by
    rw [condEntropyGivenPartitionCond, integral_congr_ae hcell,
      integral_congr_ae (Eventually.of_forall hint_eq),
      integral_finsetSum _ fun k _ => hint_wCk k, integral_finsetSum _ fun k _ => hint_indic k]
    exact Finset.sum_congr rfl fun k _ => (hpullk k).symm
  rw [hLHS, hRHS]

/-- **A0' (σ-algebra-form conditional chain rule).** -/
theorem condEntropy_join_eq_sup [Fintype ι] [Fintype κ]
    {μ : Measure α} [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    condEntropy μ 𝒜 (joinCells P.cells Q.cells)
      = condEntropy μ 𝒜 P.cells + condEntropy μ (generatedSigmaAlgebra μ P ⊔ 𝒜) Q.cells := by
  rw [condEntropy_join_eq h𝒜 P Q, condEntropyGivenPartitionCond_eq_condEntropy_sup h𝒜 P Q]

end

end ErgodicTheory.Entropy
