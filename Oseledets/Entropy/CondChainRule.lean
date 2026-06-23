/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.Subadditive2
import Oseledets.Entropy.CondPartition
import Oseledets.Entropy.CondPullback

/-!
# The conditional chain rule (analytic heart of Abramov–Rokhlin, issue #13)

This module proves the entropy chain rule `H(P ∨ Q) = H(P) + H(Q | P)`, the EQUALITY refining
`entropy_join_le`, both in its absolute form and in the kernel-level conditional form
`H(P ∨ Q | 𝒜) = H(P | 𝒜) + H(Q | 𝒜 ⊔ σ(P))`.
-/

open MeasureTheory Function Filter ProbabilityTheory Finset
open scoped ENNReal

namespace Oseledets.Entropy

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]

/-! ## Step 1: the pure finite (scalar) chain rule.

For a "joint distribution" `p : ι × κ → ℝ` (nonneg, summing to 1) with `ι`-marginal
`a i = ∑ⱼ p (i,j)`, the joint entropy splits as the marginal entropy of `a` plus the average
over `i` of the conditional entropies of the rows `j ↦ p (i,j) / a i`. This is a pure
`negMulLog_mul` identity; no measure theory.
-/

/-- **Scalar chain rule, single-row form.** For a nonnegative row `r : κ → ℝ` with sum `a ≥ 0`,
`∑ⱼ negMulLog (r j) = negMulLog a + a · (∑ⱼ negMulLog (r j / a))`, provided `a ≠ 0`
(or trivially both sides are about `a = 0`). The identity is `negMulLog (a · (rⱼ/a))` expanded by
`negMulLog_mul`, summed over `j`, using `∑ⱼ rⱼ/a = 1`. -/
lemma sum_negMulLog_row [Fintype κ] (r : κ → ℝ) (a : ℝ) (ha : a ≠ 0)
    (hrow : ∑ j, r j = a) :
    ∑ j, Real.negMulLog (r j)
      = Real.negMulLog a + a * ∑ j, Real.negMulLog (r j / a) := by
  -- rewrite each `r j = a * (r j / a)` and expand by `negMulLog_mul`
  have hcsum : ∑ j, (r j / a) = 1 := by
    rw [← Finset.sum_div, hrow, div_self ha]
  have hstep : ∀ j, Real.negMulLog (r j)
      = (r j / a) * Real.negMulLog a + a * Real.negMulLog (r j / a) := by
    intro j
    have hrw : a * (r j / a) = r j := by field_simp
    calc Real.negMulLog (r j)
        = Real.negMulLog (a * (r j / a)) := by rw [hrw]
      _ = (r j / a) * Real.negMulLog a + a * Real.negMulLog (r j / a) := Real.negMulLog_mul _ _
  calc ∑ j, Real.negMulLog (r j)
      = ∑ j, ((r j / a) * Real.negMulLog a + a * Real.negMulLog (r j / a)) := by
        exact Finset.sum_congr rfl fun j _ => hstep j
    _ = (∑ j, (r j / a)) * Real.negMulLog a + a * ∑ j, Real.negMulLog (r j / a) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = Real.negMulLog a + a * ∑ j, Real.negMulLog (r j / a) := by
        rw [hcsum, one_mul]

/-- **Per-cell conditional entropy of a partition `Q` given the cell `s i` of `P`.**
This is the Shannon entropy of the *conditional distribution* `j ↦ μ(s i ∩ t j) / μ(s i)`
(the law of `Q` restricted to and renormalized on the cell `s i`). When `μ (s i) = 0` the
division-by-zero convention makes the conditional measures `0`, so the entropy is `0`. -/
noncomputable def condEntropyOnCell [Fintype κ] (μ : Measure α) (sᵢ : Set α)
    (t : κ → Set α) : ℝ :=
  ∑ j, Real.negMulLog ((μ (sᵢ ∩ t j)).toReal / (μ sᵢ).toReal)

/-- **Conditional entropy of `Q` given the finite partition `P`** (the additive-over-cells form
`H(Q | P) = ∑ᵢ μ(Pᵢ) · H(Q | Pᵢ)`). This is the second summand of the chain rule
`H(P ∨ Q) = H(P) + H(Q | P)`, and is exactly the `𝒜 = ⊥` instance of the conditional entropy
`H(Q | 𝒜 ⊔ σ(P))` written without reference to the refined kernel
`condExpKernel μ (𝒜 ⊔ σ(P))`. -/
noncomputable def condEntropyGivenPartition [Fintype ι] [Fintype κ] (μ : Measure α)
    (s : ι → Set α) (t : κ → Set α) : ℝ :=
  ∑ i, (μ (s i)).toReal * condEntropyOnCell μ (s i) t

/-! ## Step 2: the absolute chain rule `H(P ∨ Q) = H(P) + H(Q | P)`. -/

/-- **The absolute entropy chain rule.** For two finite measurable partitions `P` and `Q` of a
probability space, the entropy of the join equals the entropy of `P` plus the conditional entropy
of `Q` given `P`:
`H(P ∨ Q) = H(P) + H(Q | P)`.

This is the EQUALITY refining `entropy_join_le`. It is the pure finite identity obtained by
applying the single-row scalar chain rule `sum_negMulLog_row` to each row
`r j = μ(Pᵢ ∩ Qⱼ)` with marginal `a = μ(Pᵢ)`, then summing over `i`. The `a = 0` rows
contribute `0` on both sides (every `μ(Pᵢ ∩ Qⱼ) ≤ μ(Pᵢ) = 0`). -/
theorem entropy_join_eq_add_condEntropyGivenPartition [Fintype ι] [Fintype κ] {μ : Measure α}
    [IsProbabilityMeasure μ] (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    entropy μ (joinCells P.cells Q.cells)
      = entropy μ P.cells + condEntropyGivenPartition μ P.cells Q.cells := by
  rw [entropy_def, entropy_def, condEntropyGivenPartition]
  -- Group the join sum over `ι × κ` by the `ι`-coordinate.
  rw [show (∑ x, Real.negMulLog (μ (joinCells P.cells Q.cells x)).toReal)
      = ∑ i, ∑ j, Real.negMulLog (μ (P.cells i ∩ Q.cells j)).toReal from by
        rw [Fintype.sum_prod_type]; rfl]
  -- Combine the two `∑ i` sums on the RHS.
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Per-row identity. Two cases on whether `μ (Pᵢ) = 0`.
  set a : ℝ := (μ (P.cells i)).toReal with ha
  set r : κ → ℝ := fun j => (μ (P.cells i ∩ Q.cells j)).toReal with hr
  rcases eq_or_ne a 0 with ha0 | ha0
  · -- `μ (Pᵢ) = 0`: each `μ (Pᵢ ∩ Qⱼ) = 0`, both sides vanish.
    have ha0' : (μ (P.cells i)).toReal = 0 := by rw [← ha]; exact ha0
    have hμ0 : μ (P.cells i) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (μ (P.cells i))).mp ha0' with h | h
      · exact h
      · exact absurd h (measure_ne_top μ _)
    have hrow0 : ∀ j, r j = 0 := by
      intro j
      have hz : μ (P.cells i ∩ Q.cells j) = 0 := measure_mono_null Set.inter_subset_left hμ0
      simp only [hr, hz, ENNReal.toReal_zero]
    have hLHS : ∑ j, Real.negMulLog (r j) = 0 := by
      simp only [hrow0, Real.negMulLog_zero, Finset.sum_const_zero]
    rw [show (∑ j, Real.negMulLog (μ (P.cells i ∩ Q.cells j)).toReal)
        = ∑ j, Real.negMulLog (r j) from rfl, hLHS, ha0]
    simp only [Real.negMulLog_zero, zero_mul, add_zero]
  · -- `μ (Pᵢ) > 0`: the single-row scalar chain rule.
    have hrow : ∑ j, r j = a := by
      simp only [hr, ha]
      rw [Q.measure_eq_sum_inter (P.measurable i),
        ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
    have hchain := sum_negMulLog_row r a ha0 hrow
    have hcell : (∑ j, Real.negMulLog (r j / a))
        = condEntropyOnCell μ (P.cells i) Q.cells := by
      simp only [condEntropyOnCell, hr, ha]
    rw [show (∑ j, Real.negMulLog (μ (P.cells i ∩ Q.cells j)).toReal)
        = ∑ j, Real.negMulLog (r j) from rfl, hchain, hcell]

/-! ## Step 3: the kernel-level (general `𝒜`) conditional chain rule.

The absolute identity, applied *pointwise* against the Markov kernel `condExpKernel μ 𝒜 ω`
(which is a.e. a probability measure for which `P`, `Q` are still partitions) and integrated
over `μ`. This is the EQUALITY refining `condEntropy_join_le`. The refined-conditioning term
`H(Q | 𝒜 ⊔ σ(P))` is expressed in the additive-over-cells form, *avoiding* the refined kernel
`condExpKernel μ (𝒜 ⊔ σ(P))` entirely. -/

section Conditional

variable [StandardBorelSpace α]

-- NOTE: the variable ORDER `{𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]` (top of file,
-- mirroring `CondPullback`) is load-bearing: `mα` is declared AFTER `𝒜`, so it has higher
-- instance priority and `Measure α` / `StandardBorelSpace α` resolve to the ambient `mα`, not
-- the sub-σ-algebra `𝒜`.

/-- **Conditional version of `condEntropyGivenPartition`**, evaluated against the regular
conditional probability `condExpKernel μ 𝒜 ω` and averaged over `μ`. This is `H(Q | 𝒜 ⊔ σ(P))`
written in the additive-over-cells form, i.e. the second summand of the conditional chain rule.

Uses the ambient `mα` for the kernel (exactly as `condEntropy`/`condEntropy_join_le`); the
sub-σ-algebra `𝒜` is a plain explicit argument, never an instance. -/
noncomputable def condEntropyGivenPartitionCond [Fintype ι] [Fintype κ]
    (μ : Measure α) [IsFiniteMeasure μ] (𝒜 : MeasurableSpace α) (s : ι → Set α)
    (t : κ → Set α) : ℝ :=
  ∫ ω, @condEntropyGivenPartition α ι κ mα _ _ (@condExpKernel α mα _ μ _ 𝒜 ω) s t ∂μ

/-- **The conditional chain rule (kernel-level form).**
`H(P ∨ Q | 𝒜) = H(P | 𝒜) + H(Q | 𝒜 ⊔ σ(P))`, with the last term in additive-over-cells form
`∫ ω, ∑ᵢ κ(ω)(Pᵢ) · H_{κ(ω)|Pᵢ}(Q) ∂μ`. The EQUALITY refining `condEntropy_join_le`. -/
theorem condEntropy_join_eq [Fintype ι] [Fintype κ]
    {μ : Measure α} [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    condEntropy μ 𝒜 (joinCells P.cells Q.cells)
      = condEntropy μ 𝒜 P.cells + condEntropyGivenPartitionCond μ 𝒜 P.cells Q.cells := by
  -- Abbreviation for the conditional kernel measure at `ω`.
  set κω : α → Measure α := fun ω => @condExpKernel α mα _ μ _ 𝒜 ω with hκω
  -- The pointwise absolute chain rule: for a.e. `ω`, `κ ω` is a probability measure with `P`, `Q`
  -- genuine partitions, so the absolute equality holds against `κ ω`.
  have hpt : ∀ᵐ ω ∂μ,
      entropy (κω ω) (joinCells P.cells Q.cells)
        = entropy (κω ω) P.cells + condEntropyGivenPartition (κω ω) P.cells Q.cells := by
    filter_upwards [condExpKernel_pairwise_aedisjoint h𝒜 P,
      condExpKernel_pairwise_aedisjoint h𝒜 Q] with ω hPd hQd
    have : IsProbabilityMeasure (κω ω) := IsMarkovKernel.isProbabilityMeasure ω
    let Pω : MeasurePartition (κω ω) ι :=
      { cells := P.cells, measurable := P.measurable, aedisjoint := hPd, cover := P.cover }
    let Qω : MeasurePartition (κω ω) κ :=
      { cells := Q.cells, measurable := Q.measurable, aedisjoint := hQd, cover := Q.cover }
    exact entropy_join_eq_add_condEntropyGivenPartition Pω Qω
  -- Integrability of the per-cell conditional-entropy term: a.e. it is the difference of the two
  -- (integrable) `condEntropy` integrands.
  have hdiff : (fun ω => condEntropyGivenPartition (κω ω) P.cells Q.cells)
      =ᵐ[μ] fun ω =>
        entropy (κω ω) (joinCells P.cells Q.cells) - entropy (κω ω) P.cells := by
    filter_upwards [hpt] with ω hω; rw [hω]; ring
  have hintJ : Integrable (fun ω => entropy (κω ω) (joinCells P.cells Q.cells)) μ := by
    simp only [hκω, entropy_def]
    exact integrable_condEntropy_integrand h𝒜 (joinCells P.cells Q.cells)
      (fun x => (P.measurable x.1).inter (Q.measurable x.2))
  have hintP : Integrable (fun ω => entropy (κω ω) P.cells) μ := by
    simp only [hκω, entropy_def]
    exact integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i)
  have hintC : Integrable (fun ω => condEntropyGivenPartition (κω ω) P.cells Q.cells) μ :=
    (hintJ.sub hintP).congr hdiff.symm
  -- Now assemble. Rewrite the three quantities as integrals of pointwise `entropy` /
  -- `condEntropyGivenPartition`, combine the two RHS integrals, and integrate the a.e. equality.
  have eJ : condEntropy μ 𝒜 (joinCells P.cells Q.cells)
      = ∫ ω, entropy (κω ω) (joinCells P.cells Q.cells) ∂μ := by
    rw [condEntropy_def]
    simp only [hκω, entropy_def]
  have eP : condEntropy μ 𝒜 P.cells = ∫ ω, entropy (κω ω) P.cells ∂μ := by
    rw [condEntropy_def]
    simp only [hκω, entropy_def]
  have eC : condEntropyGivenPartitionCond μ 𝒜 P.cells Q.cells
      = ∫ ω, condEntropyGivenPartition (κω ω) P.cells Q.cells ∂μ := by
    rw [condEntropyGivenPartitionCond]
  rw [eJ, eP, eC, ← integral_add hintP hintC]
  exact integral_congr_ae hpt

end Conditional

end Oseledets.Entropy
