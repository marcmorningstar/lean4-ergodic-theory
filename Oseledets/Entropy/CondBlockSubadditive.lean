/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.CondKSEntropy

/-!
# Block-subadditivity atoms for the conditional iterated join (issue #13)

This file isolates two reusable *atoms* about the conditional Shannon entropy
`condEntropy μ ℱ (ksJoin hT P n).cells` of the flat `Fin n`-indexed iterated join, for an
**arbitrary** fixed sub-σ-algebra `ℱ ≤ mα` — crucially **not** assumed `T`-invariant. They feed a
blocking argument for the Abramov–Rokhlin *moving-index* conditional Kolmogorov–Sinai limit
(GitHub issue #13), where the conditioning σ-algebra varies with the block and so cannot be assumed
forward-invariant.

The two atoms split off exactly the invariance-free portion of the subadditivity argument in
`Oseledets.Entropy.CondKSEntropy`:

* **Append block-subadditivity** (`condEntropy_ksJoin_append_le`): reindexing the `(a + b)`-fold
  join by `Fin.appendEquiv` exhibits it (via `ksJoinCells_append`) as the join of the `a`-fold join
  with the `Tᵃ`-pullback of the `b`-fold join, and the conditional join subadditivity
  `condEntropy_join_le` bounds it by the sum of the two conditional entropies. This is the
  `hcell`/`hreindex` reindexing step plus `condEntropy_join_le` of `condKsEntropySeq_subadditive`,
  *stopping before* the pullback-invariance fold; hence it holds for arbitrary `ℱ`, with the pulled
  back `Tᵃ`-block kept explicit on the right-hand side.

* **Uniform linear bound** (`condEntropy_ksJoin_le_nsmul_log_card`): since the `n`-fold join is a
  finite measurable partition indexed by `Fin n → ι`, the conditional `log card` bound
  `condEntropy_le_log_card` gives `condEntropy μ ℱ (ksJoin hT P n).cells ≤ log (card (Fin n → ι))`,
  and `Fintype.card_fun` together with `Real.log_pow` evaluates the right-hand side as
  `n * log (card ι)`. This is a *uniform* (in `ℱ`) ceiling on the block entropies.

## Main results

* `Oseledets.Entropy.condEntropy_ksJoin_append_le`: block-subadditivity of the conditional
  iterated-join entropy for an arbitrary sub-σ-algebra `ℱ`.
* `Oseledets.Entropy.condEntropy_ksJoin_le_nsmul_log_card`: the uniform linear bound
  `condEntropy μ ℱ (ksJoin hT P n).cells ≤ n * Real.log (Fintype.card ι)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM 79, Chapter 4.
-/

open MeasureTheory Function Filter Topology ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} {ℱ : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

/-- **Append block-subadditivity of the conditional iterated-join entropy** for an *arbitrary*
sub-σ-algebra `ℱ ≤ mα` (no invariance hypothesis):
`H(⋁ₖ₌₀ᵃ⁺ᵇ⁻¹ T⁻ᵏ α | ℱ) ≤ H(⋁ₖ₌₀ᵃ⁻¹ T⁻ᵏ α | ℱ) + H(T⁻ᵃ(⋁ₖ₌₀ᵇ⁻¹ T⁻ᵏ α) | ℱ)`.

Reindexing the `(a + b)`-fold join by `Fin.appendEquiv` exhibits its cell at `Fin.append p.1 p.2`
as the join cell of the `a`-fold join with the `Tᵃ`-pullback of the `b`-fold join
(`ksJoinCells_append`), so the conditional entropies agree after permuting the integrand's summands
(`Equiv.sum_comp`); the conditional join subadditivity `condEntropy_join_le` then bounds it by the
sum. This is the invariance-free half of `condKsEntropySeq_subadditive`: the second summand is kept
as the explicit `Tᵃ`-pullback `(ksJoin hT P b).pullback (hT.iterate a)`, *not* folded back to the
`b`-fold join (which would require a forward-invariance hypothesis on `ℱ`). This is the
block-subadditivity atom for the Abramov–Rokhlin moving-index conditional KS limit (issue #13). -/
lemma condEntropy_ksJoin_append_le [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hℱ : ℱ ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (a b : ℕ) :
    condEntropy μ ℱ (ksJoin hT P (a + b)).cells
      ≤ condEntropy μ ℱ (ksJoin hT P a).cells
        + condEntropy μ ℱ ((ksJoin hT P b).pullback (hT.iterate a)).cells := by
  -- The `Tᵃ`-pullback of the `b`-fold join.
  set Q : MeasurePartition μ (Fin b → ι) := (ksJoin hT P b).pullback (hT.iterate a) with hQ
  -- Cell identity: the `(a + b)`-join cell at `appendEquiv (x, y)` is the join cell at `(x, y)`.
  have hcell : ∀ p : (Fin a → ι) × (Fin b → ι),
      (ksJoin hT P (a + b)).cells (Fin.appendEquiv a b p)
        = joinCells (ksJoin hT P a).cells Q.cells p := by
    rintro ⟨x, y⟩
    simp only [ksJoin_cells, joinCells_apply, hQ, MeasurePartition.pullback_cells]
    exact ksJoinCells_append P.cells T a b x y
  -- Reindex the `(a + b)`-entropy as the conditional join entropy. Uses no invariance.
  have hreindex : condEntropy μ ℱ (ksJoin hT P (a + b)).cells
      = condEntropy μ ℱ (joinCells (ksJoin hT P a).cells Q.cells) := by
    rw [condEntropy_def, condEntropy_def]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    refine (Equiv.sum_comp (Fin.appendEquiv a b)
      (fun g => Real.negMulLog
        (@condExpKernel α mα _ μ _ ℱ ω ((ksJoin hT P (a + b)).cells g)).toReal)).symm.trans ?_
    exact Finset.sum_congr rfl fun p _ => by rw [hcell p]
  rw [hreindex]
  exact condEntropy_join_le hℱ (ksJoin hT P a) Q

/-- **Uniform linear bound on the conditional iterated-join entropy** for an *arbitrary*
sub-σ-algebra `ℱ ≤ mα`:
`H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α | ℱ) ≤ n · log (card ι)`.

The `n`-fold join `ksJoin hT P n` is a finite measurable partition indexed by `Fin n → ι`, so the
conditional `log card` ceiling `condEntropy_le_log_card` bounds its conditional entropy by
`log (card (Fin n → ι))`. Since `card (Fin n → ι) = (card ι)ⁿ` (`Fintype.card_fun`,
`Fintype.card_fin`), `Real.log_pow` evaluates this as `n · log (card ι)`. The constant
`log (card ι)` is independent of `ℱ`, the uniform ceiling needed to control the moving-index
blocks in the Abramov–Rokhlin conditional KS limit (issue #13). -/
lemma condEntropy_ksJoin_le_nsmul_log_card [Fintype ι] [Nonempty ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hℱ : ℱ ≤ mα)
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    condEntropy μ ℱ (ksJoin hT P n).cells ≤ n * Real.log (Fintype.card ι) := by
  calc condEntropy μ ℱ (ksJoin hT P n).cells
      ≤ Real.log (Fintype.card (Fin n → ι)) := condEntropy_le_log_card hℱ (ksJoin hT P n)
    _ = Real.log (((Fintype.card ι : ℝ)) ^ n) := by
        rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    _ = n * Real.log (Fintype.card ι) := by
        rw [Real.log_pow]

end Oseledets.Entropy
