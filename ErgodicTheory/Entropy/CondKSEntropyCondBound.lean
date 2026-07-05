/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondKSEntropy
import ErgodicTheory.Entropy.CondChainRuleSup
import ErgodicTheory.Entropy.JoinSigmaAlgebra
import ErgodicTheory.Entropy.KSEntropyCondBound

/-!
# The conditional Le Maître inequality (7): the relative static-conditional-entropy correction

This module is the **conditional analog** of `ErgodicTheory.Entropy.KSEntropyCondBound`
(`ksEntropyPartition_le_add_condEntropy`), threading a fixed forward-invariant conditioning
σ-algebra `𝒜 ≤ mα` (with `comap T 𝒜 ≤ 𝒜`) through the whole argument. For a measure-preserving
transformation `T` and two finite measurable partitions `α = P` and `β = P'`, the **relative**
Kolmogorov–Sinai entropies obey the **conditional Le Maître inequality**
`h(α, T | 𝒜) ≤ h(β, T | 𝒜) + H(α | σ(β) ⊔ 𝒜)`,
where `H(α | σ(β) ⊔ 𝒜)` is the *static* conditional Shannon entropy of `α` given the σ-algebra
`σ(β) ⊔ 𝒜` (the join of the cells of `β` with the conditioning σ-algebra `𝒜`). This is the
relativized first half of the Kolmogorov–Sinai theorem, and the building block for the
*conditional* product-entropy upper bound used in issue #21.

The defect σ-algebra is `σ(β) ⊔ 𝒜` — not `σ(β)` — which is precisely why the σ-algebra-form
conditional chain rule `condEntropy_join_eq_sup` (A0', `CondChainRuleSup`) is needed in place of
the absolute bridge.

The dynamical statement reduces to a per-`n` bound. Writing `A_n = ⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` and
`B_n = ⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ β` for the flat `Fin n`-indexed iterated joins:

* **conditional refinement + σ-form chain rule** (`condEntropy_le_condEntropy_join`,
  `condEntropy_joinCells_comm`, `condEntropy_join_eq_sup`):
  `H(A_n | 𝒜) ≤ H(A_n ∨ B_n | 𝒜) = H(B_n | 𝒜) + H(A_n | σ(B_n) ⊔ 𝒜)`;
* **finite conditional subadditivity** (`condEntropy_ksJoin_le_sum`, applied with the *arbitrary*
  conditioning σ-algebra `σ(B_n) ⊔ 𝒜`):
  `H(A_n | σ(B_n) ⊔ 𝒜) ≤ ∑ₖ<ₙ H(T⁻ᵏα | σ(B_n) ⊔ 𝒜)`;
* **moving-conditioning collapse** (`condEntropy_mono_of_le`, `condEntropy_comap_pullback`): each
  summand is at most `H(α | σ(β) ⊔ 𝒜)`, because (distributing `comap` over `⊔` with
  `MeasurableSpace.comap_sup`) `comap (T^[k]) (σ(β) ⊔ 𝒜) ≤ σ(B_n) ⊔ 𝒜`. Here the
  `comap (T^[k]) σ(β) ≤ σ(B_n)` half is the absolute argument, while `comap (T^[k]) 𝒜 ≤ 𝒜`
  consumes the forward-invariance hypothesis `hinv` (iterated via `comap_iterate_le`).

Together these give `H(A_n | 𝒜) ≤ H(B_n | 𝒜) + n · H(α | σ(β) ⊔ 𝒜)`; dividing by `n` and passing
both Fekete limits (`tendsto_condKsEntropySeq`) yields the dynamical inequality.

## Main results

* `ErgodicTheory.Entropy.condEntropy_joinCells_comm`: symmetry `H(α ∨ β | 𝒜) = H(β ∨ α | 𝒜)` of the
  static conditional join entropy.
* `ErgodicTheory.Entropy.condEntropy_le_condEntropy_join`: conditional refinement monotonicity
  `H(α | 𝒜) ≤ H(α ∨ β | 𝒜)`.
* `ErgodicTheory.Entropy.condKsEntropySeq_le_add_condEntropy`: the per-`n` conditional bound
  `H(A_n | 𝒜) ≤ H(B_n | 𝒜) + n · H(α | σ(β) ⊔ 𝒜)`.
* `ErgodicTheory.Entropy.condKsEntropyPartition_le_add_condEntropy`: the conditional Le Maître
  inequality `h(α, T | 𝒜) ≤ h(β, T | 𝒜) + H(α | σ(β) ⊔ 𝒜)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1–2, inequality (7).
* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM 79, Chapter 4.
-/

open MeasureTheory Function Filter Topology ProbabilityTheory
open scoped ENNReal

namespace ErgodicTheory.Entropy

section CondLeMaitre

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

/-- **Symmetry of the static conditional join entropy:** `H(α ∨ β | 𝒜) = H(β ∨ α | 𝒜)`. The join
cell families `(i, j) ↦ sᵢ ∩ tⱼ` and `(j, i) ↦ tⱼ ∩ sᵢ` agree after swapping the product index and
using commutativity of intersection, so for every `ω` the pointwise conditional-entropy integrands
coincide; integrating gives equal conditional Shannon entropies. The conditional mirror of
`entropy_joinCells_comm`. -/
lemma condEntropy_joinCells_comm {β γ : Type*} [Fintype β] [Fintype γ] {μ : Measure α}
    [IsFiniteMeasure μ] (s : β → Set α) (t : γ → Set α) :
    condEntropy μ 𝒜 (joinCells s t) = condEntropy μ 𝒜 (joinCells t s) := by
  rw [condEntropy_def, condEntropy_def]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only []
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [joinCells_apply, joinCells_apply, Set.inter_comm]

/-- **Conditional refinement monotonicity:** `H(α | 𝒜) ≤ H(α ∨ β | 𝒜)`. By the σ-algebra-form
conditional chain rule `condEntropy_join_eq_sup`, the join conditional entropy splits as
`H(α | 𝒜) + H(β | σ(α) ⊔ 𝒜)`, and the second summand is nonnegative. -/
lemma condEntropy_le_condEntropy_join [Fintype ι] [Fintype κ] {μ : Measure α}
    [IsProbabilityMeasure μ] (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι)
    (Q : MeasurePartition μ κ) :
    condEntropy μ 𝒜 P.cells ≤ condEntropy μ 𝒜 (joinCells P.cells Q.cells) := by
  rw [condEntropy_join_eq_sup h𝒜 P Q]
  exact le_add_of_nonneg_right condEntropy_nonneg

/-- **Per-`n` conditional Le Maître bound.** For finite measurable partitions `α = P` and `β = P'`,
a fixed conditioning σ-algebra `𝒜 ≤ mα` with `comap T 𝒜 ≤ 𝒜`, and every `n`,
`H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α | 𝒜) ≤ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ β | 𝒜) + n · H(α | σ(β) ⊔ 𝒜)`.

Conditional refinement (`condEntropy_le_condEntropy_join`), join symmetry
(`condEntropy_joinCells_comm`) and the σ-algebra-form conditional chain rule
(`condEntropy_join_eq_sup`) give `H(A_n | 𝒜) ≤ H(B_n | 𝒜) + H(A_n | σ(B_n) ⊔ 𝒜)`; finite
conditional subadditivity (`condEntropy_ksJoin_le_sum` with `𝒞 = σ(B_n) ⊔ 𝒜`) splits the last
term into `n` single-coordinate conditional entropies, each of which collapses to
`H(α | σ(β) ⊔ 𝒜)` by conditioning monotonicity (`condEntropy_mono_of_le`) against
`comap (T^[k]) (σ(β) ⊔ 𝒜) ⊆ σ(B_n) ⊔ 𝒜` followed by the joint-pullback invariance
(`condEntropy_comap_pullback`). -/
theorem condKsEntropySeq_le_add_condEntropy [Fintype ι] [Fintype κ]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) (P' : MeasurePartition μ κ) (n : ℕ) :
    condKsEntropySeq 𝒜 hT P n
      ≤ condKsEntropySeq 𝒜 hT P' n
        + (n : ℝ) * condEntropy μ (generatedSigmaAlgebra μ P' ⊔ 𝒜) P.cells := by
  have hCnle : generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜 ≤ mα :=
    sup_le (generatedSigmaAlgebra_le _) hm
  have hm' : generatedSigmaAlgebra μ P' ⊔ 𝒜 ≤ mα := sup_le (generatedSigmaAlgebra_le P') hm
  set C : ℝ := condEntropy μ (generatedSigmaAlgebra μ P' ⊔ 𝒜) P.cells with hC
  -- Finite conditional subadditivity against the conditioning σ-algebra `σ(B_n) ⊔ 𝒜`.
  have hsub : condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜) (ksJoin hT P n).cells
      ≤ ∑ k : Fin n, condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜)
          (P.pullback (hT.iterate (k : ℕ))).cells :=
    condEntropy_ksJoin_le_sum hCnle hT P n
  -- Each single-coordinate conditional entropy collapses to `C = H(α | σ(β) ⊔ 𝒜)`.
  have hterm : ∀ k : Fin n,
      condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜)
        (P.pullback (hT.iterate (k : ℕ))).cells ≤ C := by
    intro k
    have hle : MeasurableSpace.comap (T^[(k : ℕ)]) (generatedSigmaAlgebra μ P' ⊔ 𝒜)
        ≤ generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜 := by
      rw [MeasurableSpace.comap_sup]
      refine sup_le_sup ?_ (comap_iterate_le hinv (k : ℕ))
      have hk1 := comap_iterate_generatedSigmaAlgebra_ksJoin_le hT P' (k : ℕ) 1
      rw [generatedSigmaAlgebra_ksJoin_one hT P'] at hk1
      refine hk1.trans (generatedSigmaAlgebra_ksJoin_mono hT P' ?_)
      have := k.isLt; omega
    calc condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜)
            (P.pullback (hT.iterate (k : ℕ))).cells
        ≤ condEntropy μ (MeasurableSpace.comap (T^[(k : ℕ)]) (generatedSigmaAlgebra μ P' ⊔ 𝒜))
            (P.pullback (hT.iterate (k : ℕ))).cells :=
          condEntropy_mono_of_le hle hCnle (P.pullback (hT.iterate (k : ℕ)))
      _ = C := by
          rw [hC, MeasurePartition.pullback_cells]
          exact condEntropy_comap_pullback hm' hT (k : ℕ) P
  -- Sum the per-coordinate bounds.
  have hsum : (∑ k : Fin n, condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜)
        (P.pullback (hT.iterate (k : ℕ))).cells) ≤ (n : ℝ) * C := by
    calc (∑ k : Fin n, condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜)
            (P.pullback (hT.iterate (k : ℕ))).cells)
        ≤ ∑ _k : Fin n, C := Finset.sum_le_sum fun k _ => hterm k
      _ = (n : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc condKsEntropySeq 𝒜 hT P n
      = condEntropy μ 𝒜 (ksJoin hT P n).cells := rfl
    _ ≤ condEntropy μ 𝒜 (joinCells (ksJoin hT P n).cells (ksJoin hT P' n).cells) :=
        condEntropy_le_condEntropy_join hm (ksJoin hT P n) (ksJoin hT P' n)
    _ = condEntropy μ 𝒜 (joinCells (ksJoin hT P' n).cells (ksJoin hT P n).cells) :=
        condEntropy_joinCells_comm (ksJoin hT P n).cells (ksJoin hT P' n).cells
    _ = condEntropy μ 𝒜 (ksJoin hT P' n).cells
          + condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜)
              (ksJoin hT P n).cells :=
        condEntropy_join_eq_sup hm (ksJoin hT P' n) (ksJoin hT P n)
    _ = condKsEntropySeq 𝒜 hT P' n
          + condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P' n) ⊔ 𝒜)
              (ksJoin hT P n).cells := rfl
    _ ≤ condKsEntropySeq 𝒜 hT P' n + (n : ℝ) * C := by
        gcongr
        exact hsub.trans hsum

/-- **The conditional Le Maître inequality (7).** For a measure-preserving transformation `T`, a
fixed conditioning σ-algebra `𝒜 ≤ mα` with `comap T 𝒜 ≤ 𝒜`, and finite measurable partitions
`α = P` and `β = P'`, the relative Kolmogorov–Sinai entropy of `α` is bounded by that of `β` plus
the *static* conditional Shannon entropy of `α` given the σ-algebra `σ(β) ⊔ 𝒜`:
`h(α, T | 𝒜) ≤ h(β, T | 𝒜) + H(α | σ(β) ⊔ 𝒜)`.

Divide the per-`n` bound `condKsEntropySeq_le_add_condEntropy` by `n`, reading
`H(A_n | 𝒜)/n ≤ H(B_n | 𝒜)/n + H(α | σ(β) ⊔ 𝒜)`, then pass both averaged conditional
iterated-join entropies to their Fekete limits (`tendsto_condKsEntropySeq`);
`le_of_tendsto_of_tendsto'` transfers the inequality to the limits. -/
theorem condKsEntropyPartition_le_add_condEntropy [Fintype ι] [Fintype κ]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) (P' : MeasurePartition μ κ) :
    condKsEntropyPartition hm hT hinv P
      ≤ condKsEntropyPartition hm hT hinv P'
        + condEntropy μ (generatedSigmaAlgebra μ P' ⊔ 𝒜) P.cells := by
  set C : ℝ := condEntropy μ (generatedSigmaAlgebra μ P' ⊔ 𝒜) P.cells with hC
  refine le_of_tendsto_of_tendsto' (tendsto_condKsEntropySeq hm hT hinv P)
    ((tendsto_condKsEntropySeq hm hT hinv P').add tendsto_const_nhds) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, div_zero, zero_add]
    rw [hC]
    exact condEntropy_nonneg
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hperN := condKsEntropySeq_le_add_condEntropy hm hT hinv P P' n
    rw [← hC] at hperN
    calc condKsEntropySeq 𝒜 hT P n / (n : ℝ)
        ≤ (condKsEntropySeq 𝒜 hT P' n + (n : ℝ) * C) / (n : ℝ) :=
          div_le_div_of_nonneg_right hperN hn0.le
      _ = condKsEntropySeq 𝒜 hT P' n / (n : ℝ) + C := by
          rw [add_div, mul_comm (n : ℝ) C, mul_div_assoc, div_self hn0.ne', mul_one]

end CondLeMaitre

end ErgodicTheory.Entropy
