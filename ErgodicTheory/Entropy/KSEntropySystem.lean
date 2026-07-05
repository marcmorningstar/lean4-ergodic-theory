/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropyBounds

/-!
# Kolmogorov–Sinai entropy of a measure-preserving system

Building on the partition-relative entropy `ksEntropyPartition hT P = h(α, T)` from
`ErgodicTheory.Entropy.KSEntropy` and `ErgodicTheory.Entropy.KSEntropyBounds`, this file defines the
**Kolmogorov–Sinai entropy of the system itself**,
`h(T) = sup_α h(α, T)`,
the supremum of the partition-relative entropies over all finite measurable partitions `α`.

Following the Le Maître notes on the Kolmogorov–Sinai theorem (and the standard
Kolmogorov–Sinai definition as recorded in Contractor's *The Pesin Entropy Formula*, §2,
Definition 2.10: "The entropy over all partitions `h(T)` is the supremum over the entropies
for each partition"), the supremum is genuinely over *all* finite partitions and may be
infinite. We therefore value it in `EReal`, taking the supremum in that complete lattice so the
definition is total even when the entropy is `+∞`.

Concretely the supremum ranges over `Fin n`-indexed partitions for every `n : ℕ`; since every
finite index type is in bijection with some `Fin n` and `ksEntropyPartition` is reindexing
invariant, this `Fin`-indexed family already realizes the full partition supremum, while keeping
the index of the `iSup` a small type.

## Main definitions

* `ErgodicTheory.Entropy.ksEntropy`: the Kolmogorov–Sinai entropy `h(T)` of a measure-preserving
  transformation `T`, the `EReal`-valued supremum of `h(α, T)` over all finite partitions `α`.

## Main results

* `ErgodicTheory.Entropy.le_ksEntropy`: every partition-relative entropy `h(α, T)` is below `h(T)`.
* `ErgodicTheory.Entropy.ksEntropy_nonneg`: `0 ≤ h(T)`, witnessed by the trivial one-cell partition.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Maryam Contractor, *The Pesin Entropy Formula* (2023), §2 (standard Kolmogorov–Sinai entropy).
-/

open MeasureTheory Function

namespace ErgodicTheory.Entropy

variable {α : Type*} [MeasurableSpace α]

/-- The **Kolmogorov–Sinai entropy of the system** `h(T)`: the supremum, taken in `EReal`, of the
partition-relative entropies `h(α, T) = ksEntropyPartition hT P` over all finite measurable
partitions `α`. The supremum ranges over `Fin n`-indexed partitions for every `n : ℕ`; valuing it
in the complete lattice `EReal` makes it total even when the entropy is unbounded (`+∞`). -/
noncomputable def ksEntropy {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) : EReal :=
  ⨆ n : ℕ, ⨆ P : MeasurePartition μ (Fin n), ((ksEntropyPartition hT P : ℝ) : EReal)

/-- Every partition-relative Kolmogorov–Sinai entropy `h(α, T)` is bounded above by the entropy of
the system `h(T)`: the defining supremum dominates each of its terms (`le_iSup` applied to the
outer `n`-indexed and the inner partition-indexed suprema). -/
lemma le_ksEntropy {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) {n : ℕ} (P : MeasurePartition μ (Fin n)) :
    ((ksEntropyPartition hT P : ℝ) : EReal) ≤ ksEntropy hT :=
  le_trans (le_iSup (fun P : MeasurePartition μ (Fin n) =>
      ((ksEntropyPartition hT P : ℝ) : EReal)) P)
    (le_iSup (fun n : ℕ =>
      ⨆ P : MeasurePartition μ (Fin n), ((ksEntropyPartition hT P : ℝ) : EReal)) n)

/-- The **trivial one-cell partition** of a probability space: the single cell is the whole space.
It is measurable (`MeasurableSet.univ`), pairwise almost-everywhere disjoint (vacuously, since the
index type `Fin 1` is a subsingleton), and covers the space (a constant `⋃` over a nonempty index
is that constant). It witnesses that the supremum defining `ksEntropy` ranges over a nonempty
family. -/
def trivialPartition (μ : Measure α) : MeasurePartition μ (Fin 1) where
  cells _ := Set.univ
  measurable _ := MeasurableSet.univ
  aedisjoint := Subsingleton.pairwise
  cover := Set.iUnion_const Set.univ

/-- **Nonnegativity of the Kolmogorov–Sinai entropy of the system:** `0 ≤ h(T)`. The trivial
one-cell partition `trivialPartition μ` has nonnegative partition-relative entropy
(`ksEntropyPartition_nonneg`), and that entropy is below `h(T)` by `le_ksEntropy`; chaining the two
`EReal` inequalities (and `EReal.coe_nonneg` to lift `0 ≤ h(α, T)` to `EReal`) gives the claim. -/
lemma ksEntropy_nonneg {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) :
    0 ≤ ksEntropy hT := by
  have h0 : (0 : EReal) ≤ ((ksEntropyPartition hT (trivialPartition μ) : ℝ) : EReal) :=
    EReal.coe_nonneg.mpr (ksEntropyPartition_nonneg hT (trivialPartition μ))
  exact h0.trans (le_ksEntropy hT (trivialPartition μ))

end ErgodicTheory.Entropy
