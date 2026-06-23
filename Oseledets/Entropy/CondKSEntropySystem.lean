/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.CondKSEntropy
import Oseledets.Entropy.KSEntropySystem

/-!
# Relative Kolmogorov–Sinai entropy of a measure-preserving system

Building on the partition-relative entropy `condKsEntropyPartition hm hT hinv P =
h(α, T | 𝒜)` from `Oseledets.Entropy.CondKSEntropy`, this file defines the **relative
Kolmogorov–Sinai entropy of the system itself**,
`h(T | 𝒜) = sup_α h(α, T | 𝒜)`,
the supremum of the partition-relative conditional entropies over all finite measurable
partitions `α`. This is the conditional mirror of `Oseledets.Entropy.KSEntropySystem`.

The one-sided forward-invariance hypothesis on `T` (`comap T 𝒜 ≤ 𝒜`) is a fixed parameter of the
definition; the supremum ranges over `Fin n`-indexed partitions for every `n : ℕ`. As in the
absolute case, the supremum may be infinite, so it is valued in `EReal`.

## Main definitions

* `Oseledets.Entropy.condKsEntropy`: the relative Kolmogorov–Sinai entropy `h(T | 𝒜)` of a
  measure-preserving transformation `T`, the `EReal`-valued supremum of `h(α, T | 𝒜)` over all
  finite partitions `α`.

## Main results

* `Oseledets.Entropy.le_condKsEntropy`: every partition-relative entropy `h(α, T | 𝒜)` is below
  `h(T | 𝒜)`.
* `Oseledets.Entropy.condKsEntropy_nonneg`: `0 ≤ h(T | 𝒜)`, witnessed by the trivial partition.
* `Oseledets.Entropy.condKsEntropy_bot`: conditioning on `⊥` recovers the absolute entropy `h(T)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Maryam Contractor, *The Pesin Entropy Formula* (2023), §2 (standard Kolmogorov–Sinai entropy).
-/

open MeasureTheory Function

namespace Oseledets.Entropy

variable {α : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α] [StandardBorelSpace α]

/-- The **relative Kolmogorov–Sinai entropy of the system** `h(T | 𝒜)`: the supremum, taken in
`EReal`, of the partition-relative conditional entropies `h(α, T | 𝒜) =
condKsEntropyPartition hm hT hinv P` over all finite measurable partitions `α`. The one-sided
forward-invariance hypothesis `comap T 𝒜 ≤ 𝒜` on `T` is a fixed parameter; the supremum ranges over
`Fin n`-indexed partitions for every `n : ℕ`. Valuing it in the complete lattice `EReal` makes it
total even when the entropy is unbounded (`+∞`). -/
noncomputable def condKsEntropy {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜) : EReal :=
  ⨆ n : ℕ, ⨆ P : MeasurePartition μ (Fin n),
    ((condKsEntropyPartition hm hT hinv P : ℝ) : EReal)

/-- Every partition-relative conditional Kolmogorov–Sinai entropy `h(α, T | 𝒜)` is bounded above by
the relative entropy of the system `h(T | 𝒜)`: the defining supremum dominates each of its terms
(`le_iSup` applied to the outer `n`-indexed and the inner partition-indexed suprema). -/
lemma le_condKsEntropy {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    {n : ℕ} (P : MeasurePartition μ (Fin n)) :
    ((condKsEntropyPartition hm hT hinv P : ℝ) : EReal) ≤ condKsEntropy hm hT hinv :=
  le_trans (le_iSup (fun P : MeasurePartition μ (Fin n) =>
      ((condKsEntropyPartition hm hT hinv P : ℝ) : EReal)) P)
    (le_iSup (fun n : ℕ =>
      ⨆ P : MeasurePartition μ (Fin n),
        ((condKsEntropyPartition hm hT hinv P : ℝ) : EReal)) n)

/-- **Nonnegativity of the relative Kolmogorov–Sinai entropy of the system:** `0 ≤ h(T | 𝒜)`. The
trivial one-cell partition `trivialPartition μ` has nonnegative partition-relative conditional
entropy (`condKsEntropyPartition_nonneg`), and that entropy is below `h(T | 𝒜)` by
`le_condKsEntropy`; chaining the two `EReal` inequalities (and `EReal.coe_nonneg` to lift the
nonnegativity to `EReal`) gives the claim. -/
lemma condKsEntropy_nonneg {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜) :
    0 ≤ condKsEntropy hm hT hinv := by
  have h0 : (0 : EReal) ≤
      ((condKsEntropyPartition hm hT hinv (trivialPartition μ) : ℝ) : EReal) :=
    EReal.coe_nonneg.mpr (condKsEntropyPartition_nonneg hm hT hinv (trivialPartition μ))
  exact h0.trans (le_condKsEntropy hm hT hinv (trivialPartition μ))

/-- **The relative entropy of the system at `⊥` recovers the absolute entropy:**
`h(T | ⊥) = h(T)`. Termwise inside the double supremum, each partition-relative conditional
entropy `h(α, T | ⊥)` equals the absolute `h(α, T)` by `condKsEntropyPartition_bot`; the two
`EReal`-valued suprema therefore coincide. The one-sided forward-invariance hypothesis is
discharged internally for `⊥` via `MeasurableSpace.comap_bot`. -/
lemma condKsEntropy_bot {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : @MeasurePreserving α α mα mα T μ μ) :
    condKsEntropy (𝒜 := ⊥) bot_le hT MeasurableSpace.comap_bot.le = ksEntropy hT := by
  rw [condKsEntropy, ksEntropy]
  refine iSup_congr fun n => iSup_congr fun P => ?_
  rw [condKsEntropyPartition_bot hT P]

end Oseledets.Entropy
