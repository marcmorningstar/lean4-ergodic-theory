/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionEntropyDescent
import ErgodicTheory.Continuous.SuspensionMeasureContinuity
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Continuous.FlowCondEntropyShift
import ErgodicTheory.Continuous.FlowEntropyContinuity
import ErgodicTheory.Entropy.CondChainRule
import ErgodicTheory.Entropy.KSEntropyBounds
import ErgodicTheory.Entropy.FinJoin
import ErgodicTheory.Entropy.JoinEntropyCompare

/-!
# Abramov flow-entropy homogeneity via Ito's elementary proof (issue #48)

Ito, *An elementary proof of Abramov's result on the entropy of a flow*, Nagoya Math. J. 41
(1971), 1–5. The theorem `h(φ_t) = t·h(φ_1)` for a measure-continuous flow, whose only genuinely
new analytic input is the flow measure-continuity (D.4)/(2.2). Everything else reuses the repo's
conditional-entropy chain rule + the discrete power rule `nsmul_ksEntropy_flow`.

The four analytic/combinatorial inputs are supplied by dedicated modules:
* `MeasurePreservingFlow.MeasureContinuous` and the small-shift limit `L1`
  (`condEntropyGivenPartition_flow_tendsto_zero`) from `Continuous.FlowEntropyContinuity`;
* the common-pullback invariance `W_inv` (`condEntropyGivenPartition_comap_left`) and the flow-shift
  identity `W_shift` (`condEntropyGivenPartition_flow_shift`), both from
  `Continuous.FlowCondEntropyShift`;
* Ito's static join comparison `L2` (`entropy_finJoin_le_add_sum_condEntropy`) from
  `Entropy.JoinEntropyCompare`, over the finite-family join primitive of `Entropy.FinJoin`;
* the keystone measure-continuity of the Bernoulli suspension flow from
  `Continuous.SuspensionMeasureContinuity`.
-/

open MeasureTheory Function Filter Topology
open scoped ENNReal

namespace ErgodicTheory

open Entropy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-! ## Imported inputs

The finite-family join primitive `finJoinCells`, the measure-continuity predicate
`MeasurePreservingFlow.MeasureContinuous`, the common-pullback invariance
`condEntropyGivenPartition_comap_left` and flow-shift identity
`condEntropyGivenPartition_flow_shift` (`W_inv`/`W_shift`), the small-shift limit
`condEntropyGivenPartition_flow_tendsto_zero` (`L1`), and Ito's static join comparison
`entropy_finJoin_le_add_sum_condEntropy` (`L2`) are all imported from the modules listed in the
header. -/

/-! ## Fekete lower bound and small-shift comparison lemmas -/

/-- **Fekete infimum bound:** the partition-level Kolmogorov–Sinai entropy is below every
averaged join entropy `H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα)/n` (`n ≥ 1`), because the Fekete limit of a subadditive
sequence is the infimum of its averages. -/
lemma ksEntropyPartition_le_ksEntropySeq_div {ι : Type*} [Fintype ι] {T : X → X}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) {n : ℕ} (hn : n ≠ 0) :
    ksEntropyPartition hT P ≤ ksEntropySeq hT P n / n := by
  refine (ksSubadditive hT P).lim_le_div ⟨0, ?_⟩ hn
  rintro x ⟨m, rfl⟩
  exact div_nonneg (ksEntropySeq_nonneg hT P m) (Nat.cast_nonneg m)

omit [IsProbabilityMeasure μ] in
/-- **Symmetric small-shift identity:** `H(α | φ_τ α) = H(φ_{-τ} α | α)`. Apply the common
measure-preserving pullback `φ_τ` to both families (`condEntropyGivenPartition_comap_left`) and
collapse `φ_{-τ} ∘ φ_τ = id` by flow additivity. -/
lemma condEntropyGivenPartition_flow_symm (φ : MeasurePreservingFlow μ) {ι : Type*} [Fintype ι]
    (P : MeasurePartition μ ι) (τ : ℝ) :
    condEntropyGivenPartition μ (P.pulledBack (φ.measurePreserving τ)).cells P.cells
      = condEntropyGivenPartition μ P.cells
          (P.pulledBack (φ.measurePreserving (-τ))).cells := by
  have h := condEntropyGivenPartition_comap_left (φ.measurePreserving τ)
    P.cells (P.pulledBack (φ.measurePreserving (-τ))).cells
    P.measurable (P.pulledBack (φ.measurePreserving (-τ))).measurable
  have hfix : (fun j => φ τ ⁻¹' (P.pulledBack (φ.measurePreserving (-τ))).cells j)
      = P.cells := by
    funext j
    simp only [MeasurePartition.pulledBack_cells]
    rw [← Set.preimage_comp, ← φ.map_add, neg_add_cancel, φ.map_zero, Set.preimage_id]
  rw [hfix] at h
  simpa only [MeasurePartition.pulledBack_cells] using h

omit [IsProbabilityMeasure μ] in
/-- **Small-shift control for a pair of pullbacks** (Ito's (2.3)): if the `L1` small-shift bound
holds below `δ` and `|a - b| < δ`, then `H(φ_b α | φ_a α) < ε`. Normalize by the shift identity
to `H(α | φ_{a-b} α)` and flip with the symmetric identity to an `L1` instance at `-(a-b)`. -/
lemma condEntropyGivenPartition_flow_pair_lt (φ : MeasurePreservingFlow μ) {ι : Type*}
    [Fintype ι] (P : MeasurePartition μ ι) {ε δ : ℝ}
    (hδ : ∀ τ : ℝ, |τ| < δ → condEntropyGivenPartition μ P.cells
      (P.pulledBack (φ.measurePreserving τ)).cells < ε)
    {a b : ℝ} (hab : |a - b| < δ) :
    condEntropyGivenPartition μ (P.pulledBack (φ.measurePreserving a)).cells
      (P.pulledBack (φ.measurePreserving b)).cells < ε := by
  rw [condEntropyGivenPartition_flow_shift φ P a b,
    condEntropyGivenPartition_flow_symm φ P (a - b)]
  exact hδ (-(a - b)) (by rwa [abs_neg])

/-- **Ito's grid comparison** ((2.3)–(2.4)): if each time `b k` is `δ`-close to the grid point
`k·t'`, then the `n`-step join entropy of `φ_{t'}` is bounded by the join entropy of the family
pulled back at the times `b k`, plus `n·ε`. This is `L2` fed with the small-shift control. -/
lemma ksEntropySeq_le_finJoin_add [StandardBorelSpace X] (φ : MeasurePreservingFlow μ)
    {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι) {ε δ : ℝ}
    (hδ : ∀ τ : ℝ, |τ| < δ → condEntropyGivenPartition μ P.cells
      (P.pulledBack (φ.measurePreserving τ)).cells < ε)
    (t' : ℝ) {n : ℕ} (b : Fin n → ℝ) (hb : ∀ k : Fin n, |b k - (k : ℕ) * t'| < δ) :
    ksEntropySeq (φ.measurePreserving t') P n
      ≤ entropy μ (finJoinCells fun k => (P.pulledBack (φ.measurePreserving (b k))).cells)
        + n * ε := by
  have hseq : ksEntropySeq (φ.measurePreserving t') P n
      = entropy μ (finJoinCells fun k : Fin n =>
          (P.pulledBack (φ.measurePreserving ((k : ℕ) * t'))).cells) := by
    refine congrArg (entropy μ) (funext fun f => ?_)
    change (⋂ k : Fin n, (φ t')^[(k : ℕ)] ⁻¹' P.cells (f k))
        = ⋂ k : Fin n, φ ((k : ℕ) * t') ⁻¹' P.cells (f k)
    exact Set.iInter_congr fun k => by rw [flow_iterate φ t' (k : ℕ)]
  rw [hseq]
  have hL2 := entropy_finJoin_le_add_sum_condEntropy
    (fun k : Fin n => P.pulledBack (φ.measurePreserving (b k)))
    (fun k : Fin n => P.pulledBack (φ.measurePreserving ((k : ℕ) * t')))
  have hsum : ∑ k : Fin n, condEntropyGivenPartition μ
      (P.pulledBack (φ.measurePreserving (b k))).cells
      (P.pulledBack (φ.measurePreserving ((k : ℕ) * t'))).cells ≤ (n : ℝ) * ε := by
    have hcard := Finset.sum_le_card_nsmul Finset.univ _ ε fun k _ =>
      (condEntropyGivenPartition_flow_pair_lt φ P hδ (hb k)).le
    simpa [Finset.card_univ, nsmul_eq_mul] using hcard
  exact hL2.trans (add_le_add_right hsum _)

/-- **Subsequence refinement into the fine grid:** the join of the pullbacks of `P` at the times
`m k · t` (with every `m k < M`) is refined by the full `M`-step `φ_t`-join, so its entropy is
smaller. Duplicate values among the `m k` are harmless for the refinement. -/
lemma entropy_finJoin_le_ksEntropySeq (φ : MeasurePreservingFlow μ) {ι : Type*} [Fintype ι]
    (P : MeasurePartition μ ι) (t : ℝ) {n M : ℕ} (m : Fin n → ℕ) (hm : ∀ k, m k < M) :
    entropy μ (finJoinCells fun k : Fin n =>
        (P.pulledBack (φ.measurePreserving ((m k : ℝ) * t))).cells)
      ≤ ksEntropySeq (φ.measurePreserving t) P M := by
  have hrefine : ∀ f : Fin M → ι,
      (ksJoin (φ.measurePreserving t) P M).cells f ≤ᵐ[μ]
        (finJoin fun k : Fin n =>
          P.pulledBack (φ.measurePreserving ((m k : ℝ) * t))).cells fun k => f ⟨m k, hm k⟩ := by
    intro f
    have hsub : (ksJoin (φ.measurePreserving t) P M).cells f ⊆
        (finJoin fun k : Fin n =>
          P.pulledBack (φ.measurePreserving ((m k : ℝ) * t))).cells fun k => f ⟨m k, hm k⟩ := by
      intro x hx
      have hx' : ∀ j : Fin M, (φ t)^[(j : ℕ)] x ∈ P.cells (f j) := by
        simpa [ksJoin_cells, ksJoinCells_apply, Set.mem_iInter] using hx
      refine Set.mem_iInter.mpr fun k => ?_
      change x ∈ φ ((m k : ℝ) * t) ⁻¹' P.cells (f ⟨m k, hm k⟩)
      rw [← flow_iterate φ t (m k)]
      exact hx' ⟨m k, hm k⟩
    exact hsub.eventuallyLE
  exact entropy_le_of_refines _ (ksJoin (φ.measurePreserving t) P M)
    (fun f k => f ⟨m k, hm k⟩) hrefine

/-! ## Ito's alignment inequality (the quantitative form of (2.1)) -/

set_option maxHeartbeats 800000 in
-- the alignment chain elaborates many nested `Fin`-indexed joins and Fekete limits in one proof
/-- **Ito's alignment inequality** (the ε–δ heart of (2.1), his (2.4)–(2.5)): for every `t' > 0`
and `ε > 0` there is `δ > 0` such that for all `0 < t < δ`,
`h(α, φ_{t'})/t' ≤ h(α, φ_t)/t + ε/t'`. The `n`-step `t'`-grid join is compared, via the
half-`t`-close alignment `m_k = ⌊k·t'/t + 1/2⌋₊`, with the `M_n`-step fine `t`-grid join
(`M_n = m_{n-1} + 1`), and the Fekete limits are passed along `n → ∞`, where `M_n/n → t'/t`. -/
lemma ksEntropyPartition_flow_ratio_le [StandardBorelSpace X] (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous) {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι)
    {t' ε : ℝ} (ht' : 0 < t') (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ksEntropyPartition (φ.measurePreserving t') P / t'
        ≤ ksEntropyPartition (φ.measurePreserving t) P / t + ε / t' := by
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ τ : ℝ, |τ| < δ →
      condEntropyGivenPartition μ P.cells
        (P.pulledBack (φ.measurePreserving τ)).cells < ε := by
    have h := (condEntropyGivenPartition_flow_tendsto_zero φ hφ P).eventually_lt_const hε
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ0, h⟩ := h
    exact ⟨δ, hδ0, fun τ hτ => h (by simpa [Real.dist_eq] using hτ)⟩
  refine ⟨δ, hδ0, fun t ht0 htδ => ?_⟩
  have htne : t ≠ 0 := ht0.ne'
  have ht'ne : t' ≠ 0 := ht'.ne'
  -- the alignment sequence and its elementary properties
  have hmono : ∀ a b : ℕ, a ≤ b →
      ⌊(a : ℝ) * t' / t + 1 / 2⌋₊ ≤ ⌊(b : ℝ) * t' / t + 1 / 2⌋₊ := by
    intro a b hab
    apply Nat.floor_mono
    have h1 : (a : ℝ) * t' ≤ (b : ℝ) * t' :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) ht'.le
    have h2 : (a : ℝ) * t' / t ≤ (b : ℝ) * t' / t := (div_le_div_iff_of_pos_right ht0).mpr h1
    linarith
  have hm_le : ∀ k : ℕ, (⌊(k : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) ≤ (k : ℝ) * t' / t + 1 / 2 := by
    intro k
    have h0 : (0 : ℝ) ≤ (k : ℝ) * t' / t :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg k) ht'.le) ht0.le
    exact Nat.floor_le (by linarith)
  have hm_gt : ∀ k : ℕ, (k : ℝ) * t' / t - 1 / 2 < (⌊(k : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) := by
    intro k
    have h1 := Nat.sub_one_lt_floor ((k : ℝ) * t' / t + 1 / 2)
    linarith
  have hclose : ∀ k : ℕ, |(⌊(k : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) * t - (k : ℝ) * t'| < δ := by
    intro k
    have hxt : (k : ℝ) * t' / t * t = (k : ℝ) * t' := div_mul_cancel₀ _ htne
    have hub : (⌊(k : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) * t ≤ (k : ℝ) * t' + t / 2 := by
      have h1 := mul_le_mul_of_nonneg_right (hm_le k) ht0.le
      rw [add_mul, hxt] at h1
      linarith
    have hlb : (k : ℝ) * t' - t / 2 < (⌊(k : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) * t := by
      have h1 := mul_lt_mul_of_pos_right (hm_gt k) ht0
      rw [sub_mul, hxt] at h1
      linarith
    rw [abs_lt]
    constructor <;> linarith
  -- the fine-grid length
  set Mf : ℕ → ℕ := fun n => ⌊((n - 1 : ℕ) : ℝ) * t' / t + 1 / 2⌋₊ + 1 with hMf
  -- the per-`n` chain (Fekete bound, grid comparison, refinement)
  have key : ∀ n : ℕ, n ≠ 0 →
      ksEntropyPartition (φ.measurePreserving t') P
        ≤ ksEntropySeq (φ.measurePreserving t) P (Mf n) / n + ε := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 := ksEntropyPartition_le_ksEntropySeq_div (φ.measurePreserving t') P hn
    have h2 := ksEntropySeq_le_finJoin_add φ P hδ t'
      (fun k : Fin n => (⌊((k : ℕ) : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) * t)
      (fun k => hclose (k : ℕ))
    have hmlt : ∀ k : Fin n, ⌊((k : ℕ) : ℝ) * t' / t + 1 / 2⌋₊ < Mf n := by
      intro k
      have hk := hmono (k : ℕ) (n - 1) (Nat.le_pred_of_lt k.isLt)
      simp only [hMf]
      omega
    have h3 := entropy_finJoin_le_ksEntropySeq φ P t
      (fun k : Fin n => ⌊((k : ℕ) : ℝ) * t' / t + 1 / 2⌋₊) hmlt
    have h23 : ksEntropySeq (φ.measurePreserving t') P n
        ≤ ksEntropySeq (φ.measurePreserving t) P (Mf n) + n * ε :=
      h2.trans (add_le_add_left h3 _)
    calc ksEntropyPartition (φ.measurePreserving t') P
        ≤ ksEntropySeq (φ.measurePreserving t') P n / n := h1
      _ ≤ (ksEntropySeq (φ.measurePreserving t) P (Mf n) + n * ε) / n :=
          (div_le_div_iff_of_pos_right hn0).mpr h23
      _ = ksEntropySeq (φ.measurePreserving t) P (Mf n) / n + ε := by
          rw [add_div, mul_div_cancel_left₀ ε hn0.ne']
  -- limit bookkeeping: `Mf n / n → t'/t` and `Mf n → ∞`
  have hMf_gt : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) - 1) * t' / t + 1 / 2 < (Mf n : ℝ) := by
    intro n hn
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    have h1 := hm_gt (n - 1)
    rw [hcast] at h1
    have h2 : (Mf n : ℝ) = (⌊((n - 1 : ℕ) : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) + 1 := by
      simp [hMf]
    rw [h2, hcast]
    linarith
  have hMf_le : ∀ n : ℕ, 1 ≤ n → (Mf n : ℝ) ≤ ((n : ℝ) - 1) * t' / t + 3 / 2 := by
    intro n hn
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    have h1 := hm_le (n - 1)
    rw [hcast] at h1
    have h2 : (Mf n : ℝ) = (⌊((n - 1 : ℕ) : ℝ) * t' / t + 1 / 2⌋₊ : ℝ) + 1 := by
      simp [hMf]
    rw [h2, hcast]
    linarith
  have haux : ∀ a : ℝ, Tendsto (fun n : ℕ => (((n : ℝ) - 1) * t' / t + a) / n)
      atTop (𝓝 (t' / t)) := by
    intro a
    have h0 : Tendsto (fun n : ℕ => t' / t + (a - t' / t) / (n : ℝ)) atTop (𝓝 (t' / t + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [add_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  have hB : Tendsto (fun n : ℕ => (Mf n : ℝ) / n) atTop (𝓝 (t' / t)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (haux (1 / 2)) (haux (3 / 2)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      exact (div_le_div_iff_of_pos_right hn0).mpr (hMf_gt n hn).le
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      exact (div_le_div_iff_of_pos_right hn0).mpr (hMf_le n hn)
  have hMtop : Tendsto Mf atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    have hg : Tendsto (fun n : ℕ => ((n : ℝ) - 1) * (t' / t)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-1) tendsto_natCast_atTop_atTop).atTop_mul_const
        (div_pos ht' ht0)
    refine tendsto_atTop_mono' atTop ?_ hg
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 := hMf_gt n hn
    rw [mul_div_assoc] at h1
    linarith
  have hA : Tendsto (fun n : ℕ => ksEntropySeq (φ.measurePreserving t) P (Mf n) / (Mf n : ℝ))
      atTop (𝓝 (ksEntropyPartition (φ.measurePreserving t) P)) :=
    (tendsto_ksEntropySeq (φ.measurePreserving t) P).comp hMtop
  have hAB : Tendsto (fun n : ℕ => ksEntropySeq (φ.measurePreserving t) P (Mf n) / n + ε)
      atTop (𝓝 (ksEntropyPartition (φ.measurePreserving t) P * (t' / t) + ε)) := by
    refine Tendsto.add_const ε ((hA.mul hB).congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hMne : (Mf n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp only [hMf]; omega)
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hstar : ksEntropyPartition (φ.measurePreserving t') P
      ≤ ksEntropyPartition (φ.measurePreserving t) P * (t' / t) + ε := by
    refine ge_of_tendsto hAB ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact key n (by omega)
  have heq : ksEntropyPartition (φ.measurePreserving t) P * (t' / t) / t'
      = ksEntropyPartition (φ.measurePreserving t) P / t := by
    field_simp
  calc ksEntropyPartition (φ.measurePreserving t') P / t'
      ≤ (ksEntropyPartition (φ.measurePreserving t) P * (t' / t) + ε) / t' :=
        (div_le_div_iff_of_pos_right ht').mpr hstar
    _ = ksEntropyPartition (φ.measurePreserving t) P / t + ε / t' := by
        rw [add_div, heq]

/-! ## Proposition (Ito (2.1)): the per-partition slope is attained in the `t → 0⁺` limit

NOTE (statement corrected during implementation): the originally skeleton'd `∃ L : ℝ` packaging
is **false** in general — for the shift flow of a stationary telegraph process (rate-`λ` Markov
flips on `{0,1}`; a measure-continuous flow of infinite entropy) and the two-cell time-zero
partition `α`, one has `h(α, φ_t) = H₂(p(t))` with `p(t) ~ λt`, so
`h(α, φ_t)/t ~ λ·log(1/(λt)) → ∞`: the slope family has no real upper bound. Ito's (2.1) itself
is an extended-real statement, so the limit `L` lives in `EReal` (only the codomain of the
packaging changed; the `Tendsto`/`IsLUB` shape is untouched). -/

/-- **Proposition (Ito (2.1)).** For a measure-continuous flow and each finite partition `P`, the
averaged partition entropy `(1/t)·h(P, φ_t)` converges (in `EReal`) as `t → 0⁺` to the supremum
`L` of the same ratios over all `t' > 0`; `L` is that least upper bound. This is the analytic
heart: the ε–δ subsequence bookkeeping consumes L1 (small-shift control) and L2 (grid
comparison), with the discrete power rule entering through the integer alignment. -/
theorem exists_isLUB_ksEntropyPartition_flow_ratio [StandardBorelSpace X]
    (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous) {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι) :
    ∃ L : EReal,
      Tendsto (fun t : ℝ => ((ksEntropyPartition (φ.measurePreserving t) P / t : ℝ) : EReal))
        (𝓝[>] 0) (𝓝 L) ∧
      IsLUB (Set.range (fun t' : {t' : ℝ // 0 < t'} =>
        ((ksEntropyPartition (φ.measurePreserving t'.1) P / t'.1 : ℝ) : EReal))) L := by
  refine ⟨⨆ t' : {t' : ℝ // 0 < t'},
    ((ksEntropyPartition (φ.measurePreserving t'.1) P / t'.1 : ℝ) : EReal), ?_, isLUB_iSup⟩
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- eventually below: use the alignment inequality at a witness `u` with `b < slope(u)`
    obtain ⟨⟨u, hu⟩, hbu⟩ := lt_iSup_iff.mp hb
    obtain ⟨c, hbc, hcu⟩ := EReal.lt_iff_exists_real_btwn.mp hbu
    have hclt : c < ksEntropyPartition (φ.measurePreserving u) P / u :=
      EReal.coe_lt_coe_iff.mp hcu
    have hε0 : 0 < (ksEntropyPartition (φ.measurePreserving u) P / u - c) * u :=
      mul_pos (by linarith) hu
    obtain ⟨δ, hδ0, hδ⟩ := ksEntropyPartition_flow_ratio_le φ hφ P hu hε0
    filter_upwards [Ioo_mem_nhdsGT hδ0] with s hs
    have hle := hδ s hs.1 hs.2
    have hεu : (ksEntropyPartition (φ.measurePreserving u) P / u - c) * u / u
        = ksEntropyPartition (φ.measurePreserving u) P / u - c :=
      mul_div_cancel_right₀ _ hu.ne'
    rw [hεu] at hle
    exact lt_of_lt_of_le hbc (EReal.coe_le_coe_iff.mpr (by linarith))
  · -- eventually above: every slope is below the supremum
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact lt_of_le_of_lt
      (le_iSup (fun t' : {t' : ℝ // 0 < t'} =>
        ((ksEntropyPartition (φ.measurePreserving t'.1) P / t'.1 : ℝ) : EReal)) ⟨s, hs⟩) hb

/-! ## The abstract Abramov homogeneity theorem -/

/-- Commuting a positive real scalar through an `EReal` supremum (the real-scalar analogue of the
`nsmul` version in `KSEntropyPow`): `x ↦ ↑c * x` is monotone and continuous for a finite positive
`c`, and sends `⊥` to `⊥`, so it preserves arbitrary suprema. -/
private lemma coe_mul_iSup {J : Sort*} {c : ℝ} (hc : 0 < c) (f : J → EReal) :
    (c : EReal) * ⨆ j, f j = ⨆ j, (c : EReal) * f j := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · rw [iSup_of_empty, iSup_of_empty]
    exact EReal.coe_mul_bot_of_pos hc
  · have hmono : Monotone fun x : EReal => (c : EReal) * x := fun a b hab =>
      mul_le_mul_of_nonneg_left hab (by exact_mod_cast hc.le)
    have hne0 : ((c : ℝ) : EReal) ≠ 0 := by exact_mod_cast hc.ne'
    have hcont : ContinuousAt (fun x : EReal => (c : EReal) * x) (⨆ j, f j) := by
      have hpair : ContinuousAt (fun x : EReal => ((c : EReal), x)) (⨆ j, f j) := by fun_prop
      have hmul : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) ((c : EReal), ⨆ j, f j) :=
        EReal.continuousAt_mul (Or.inl hne0) (Or.inl hne0)
          (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
      exact hmul.comp hpair
    exact Monotone.map_ciSup_of_continuousAt hcont hmono ⟨⊤, fun _ _ => le_top⟩

/-- `ksEntropyPartition` depends only on the underlying map: two measure-preserving witnesses
with equal underlying maps give equal partition entropies (proof irrelevance). -/
private lemma ksEntropyPartition_congr {T S : X → X} (hT : MeasurePreserving T μ μ)
    (hS : MeasurePreserving S μ μ) {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι)
    (h : T = S) : ksEntropyPartition hT P = ksEntropyPartition hS P := by
  subst h
  rfl

set_option maxHeartbeats 400000 in
-- the two `iSup` directions elaborate `EReal` continuity/limit arguments in one proof
/-- **Ito's assembly identity** ((2.6)–(2.9)): for every `s > 0`, `h(φ_s) = s · h({φ})`, where
`h({φ}) = ⨆_α ⨆_{u>0} (1/u)·h(α, φ_u)` is the supremum of all partition slopes. The `≤`
direction writes `h(α, φ_s) = s·(h(α, φ_s)/s)` and feeds the slope into the supremum; the `≥`
direction passes the Proposition's limit along `u = s/n`, where the discrete power identity
turns `s·(h(α, φ_{s/n})/(s/n)) = n·h(α, φ_{s/n})` into the entropy of the `n`-fold join
partition under `φ_s` itself, hence below `h(φ_s)`. -/
private lemma ksEntropy_flow_eq_mul_slope [StandardBorelSpace X] (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous) {s : ℝ} (hs : 0 < s) :
    ksEntropy (φ.measurePreserving s)
      = (s : EReal) * ⨆ m : ℕ, ⨆ P : MeasurePartition μ (Fin m),
          ⨆ t' : {t' : ℝ // 0 < t'},
            ((ksEntropyPartition (φ.measurePreserving t'.1) P / t'.1 : ℝ) : EReal) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun m => iSup_le fun P => ?_
    have h1 : s * (ksEntropyPartition (φ.measurePreserving s) P / s)
        = ksEntropyPartition (φ.measurePreserving s) P := by
      field_simp
    calc ((ksEntropyPartition (φ.measurePreserving s) P : ℝ) : EReal)
        = (s : EReal) * ((ksEntropyPartition (φ.measurePreserving s) P / s : ℝ) : EReal) := by
          rw [← EReal.coe_mul, h1]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_iSup_of_le m (le_iSup_of_le P (le_iSup
            (fun t' : {t' : ℝ // 0 < t'} =>
              ((ksEntropyPartition (φ.measurePreserving t'.1) P / t'.1 : ℝ) : EReal))
            ⟨s, hs⟩)))
          (by exact_mod_cast hs.le)
  · rw [coe_mul_iSup hs]
    refine iSup_le fun m => ?_
    rw [coe_mul_iSup hs]
    refine iSup_le fun P => ?_
    obtain ⟨L, hlim, hlub⟩ := exists_isLUB_ksEntropyPartition_flow_ratio φ hφ P
    rw [hlub.iSup_eq]
    have hseq : Tendsto (fun n : ℕ => s / n) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_const_div_atTop_nhds_zero_nat s, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact div_pos hs (by exact_mod_cast (by omega : 0 < n))
    have hcont : ContinuousAt (fun x : EReal => (s : EReal) * x) L := by
      have hne0 : ((s : ℝ) : EReal) ≠ 0 := by exact_mod_cast hs.ne'
      have hpair : ContinuousAt (fun x : EReal => ((s : EReal), x)) L := by fun_prop
      have hmul : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) ((s : EReal), L) :=
        EReal.continuousAt_mul (Or.inl hne0) (Or.inl hne0)
          (Or.inl (EReal.coe_ne_bot s)) (Or.inl (EReal.coe_ne_top s))
      exact hmul.comp hpair
    have hmul : Tendsto (fun n : ℕ => (s : EReal) *
        ((ksEntropyPartition (φ.measurePreserving (s / n)) P / (s / n) : ℝ) : EReal))
        atTop (𝓝 ((s : EReal) * L)) :=
      hcont.tendsto.comp (hlim.comp hseq)
    refine le_of_tendsto hmul ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnne : (n : ℝ) ≠ 0 := hnR.ne'
    have hreal : s * (ksEntropyPartition (φ.measurePreserving (s / n)) P / (s / n))
        = (n : ℝ) * ksEntropyPartition (φ.measurePreserving (s / n)) P := by
      field_simp
    have hpow : (n : ℝ) * ksEntropyPartition (φ.measurePreserving (s / n)) P
        = ksEntropyPartition (φ.measurePreserving s)
            (ksJoin (φ.measurePreserving (s / n)) P n) := by
      rw [← ksEntropyPartition_iterate_ksJoin (φ.measurePreserving (s / n)) P hn0]
      refine ksEntropyPartition_congr _ _ _ ?_
      have hmap : (n : ℝ) * (s / n) = s := by field_simp
      rw [flow_iterate, hmap]
    rw [← EReal.coe_mul, hreal, hpow]
    exact ksEntropyPartition_coe_le_ksEntropy (φ.measurePreserving s) _

/-- **Abstract Abramov homogeneity.** For a measure-continuous measure-preserving flow and `t > 0`,
`h(φ_t) = t · h(φ_1)` in `EReal`. Assembles the Proposition over the `iSup`-over-partitions
definition of `ksEntropy` (`KSEntropySystem.lean`) and the discrete homogeneity entering through
`ksEntropyPartition_iterate_ksJoin`. -/
theorem ksEntropy_flow_eq_mul [StandardBorelSpace X] (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous)
    {t : ℝ} (ht : 0 < t) :
    ksEntropy (φ.measurePreserving t) = (t : EReal) * ksEntropy (φ.measurePreserving 1) := by
  rw [ksEntropy_flow_eq_mul_slope φ hφ ht, ksEntropy_flow_eq_mul_slope φ hφ one_pos,
    EReal.coe_one, one_mul]

/-- **Coe-valued corollary.** When `h(φ_1)` is the finite value `↑c`, `h(φ_t) = ↑(t · c)`. -/
theorem ksEntropy_flow_eq_coe_mul [StandardBorelSpace X] (φ : MeasurePreservingFlow μ)
    (hφ : φ.MeasureContinuous)
    {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : ksEntropy (φ.measurePreserving 1) = (c : EReal)) :
    ksEntropy (φ.measurePreserving t) = ((t * c : ℝ) : EReal) := by
  rw [ksEntropy_flow_eq_mul φ hφ ht, hc, ← EReal.coe_mul]

end ErgodicTheory

/-! ## Bernoulli instantiation and the final irrational-roof result -/

namespace ErgodicTheory

open Entropy Multifractal

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **Measure-continuity of the Bernoulli suspension flow** (the keystone, instantiated). This is
the unit-roof time-zero continuity-in-measure of the suspension flow, proved for an arbitrary
measure-preserving base in `Continuous.SuspensionMeasureContinuity`
(`tendsto_measureReal_symmDiff_suspensionFlowMap`, via fibre-translation continuity + dominated
convergence on the fundamental box); here it is instantiated at the two-sided Bernoulli shift. -/
theorem measureContinuous_bernSuspensionFlow (ν : Measure α₀) [IsProbabilityMeasure ν] :
    (bernSuspensionFlow ν).MeasureContinuous := by
  refine fun A hA => ?_
  have h := tendsto_measureReal_symmDiff_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
    (measurePreserving_biShiftEquiv_bernZ ν) hA
  simpa only [bernSuspensionFlow_apply, measureReal_def] using h

/-- **Unit-roof time-`s` entropy for ALL `s > 0`** (including irrational): `h(ζ^{(1)}_s) = s·Hnu ν`.
The general form the irrational-roof target reduces to. -/
theorem ksEntropy_bernSuspensionFlow_time_s_eq (ν : Measure α₀) [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    ksEntropy ((bernSuspensionFlow ν).measurePreserving s) = ((s * Hnu ν : ℝ) : EReal) :=
  ksEntropy_flow_eq_coe_mul (bernSuspensionFlow ν) (measureContinuous_bernSuspensionFlow ν) hs
    (ksEntropy_bernSuspensionFlow_one_eq_Hnu ν)

/-- **The issue #48 target (irrational roof allowed).** For EVERY roof `r > 0`, the time-`1` map of
the constant-roof Bernoulli suspension flow has entropy `Hnu ν / r`. Drops into the existing
`hbridge` of `ksEntropy_bernConstSuspension_time_one`, with the rational hypotheses removed. -/
theorem ksEntropy_bernConstSuspension_time_one_irrational (ν : Measure α₀) [IsProbabilityMeasure ν]
    (r : ℝ) [hr : Fact (0 < r)] :
    ksEntropy (measurePreserving_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
        (measurable_constFun r) (measurePreserving_biShiftEquiv_bernZ ν)
        (fun _ => le_refl r) hr.out 1)
      = ((Hnu ν / r : ℝ) : EReal) := by
  have hrne : r ≠ 0 := hr.out.ne'
  have hbridge :
      ksEntropy (measurePreserving_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
          (measurable_constFun r) (measurePreserving_biShiftEquiv_bernZ ν)
          (fun _ => le_refl r) hr.out 1)
        = ksEntropy ((bernSuspensionFlow ν).measurePreserving (1 / r)) := by
    rw [ksEntropy_suspensionFlowMap_const_eq_unit biShiftEquiv r 1
      (measurePreserving_biShiftEquiv_bernZ ν)]
    exact ksEntropy_unit_flow_eq ν (1 / r)
  rw [hbridge, ksEntropy_bernSuspensionFlow_time_s_eq ν (one_div_pos.mpr hr.out),
    EReal.coe_eq_coe_iff]
  field_simp

end ErgodicTheory
