/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.AbramovRokhlinPartition
import ErgodicTheory.Entropy.CondGivenPartitionBridge

/-!
# Reducing the Abramov–Rokhlin residual to a single Cesàro entropy-defect (B6a, issue #13)

The partition-level Abramov–Rokhlin identity `abramovRokhlin_partition_of_W3`
(`ErgodicTheory.Entropy.AbramovRokhlinPartition`) rests on a named hypothesis `hW3`, which
identifies
the Cesàro limit of the conditional *cell-form* sequence
`condCellSeq hT Q P n = condEntropyGivenPartition μ B_n A_n` (with `A_n = ⋁_{k<n}T⁻ᵏP`,
`B_n = ⋁_{k<n}T⁻ᵏQ`) with the relative Kolmogorov–Sinai entropy `condKsEntropyPartition` — the
relative entropy of `P` against the *fixed* factor σ-algebra `𝒜`.

This file performs a **route-independent refactor**: it reduces that `hW3` hypothesis to a single,
sharper analytic residual `hdefect` — a "Cesàro defect vanishes" statement — discharging all the
surrounding plumbing sorry-free. The hard analytic core (that the defect's Cesàro average vanishes)
is carried as the named hypothesis `hdefect` and is *not* proved here.

## The defect

Pass through the W2 bridge `condEntropyGivenPartition_eq_condEntropy_generated`, which rewrites the
cell-form conditional entropy as the σ-algebra conditional entropy against the *moving* generated
σ-algebra `σ(B_n) = generatedSigmaAlgebra μ (ksJoin hT Q n)`:
`condCellSeq hT Q P n = condEntropy μ (σ(B_n)) A_n`.
The **entropy defect** at stage `n` is the gap between conditioning on this moving σ-algebra and on
the fixed factor σ-algebra `𝒜`:
`condEntropy μ (σ(B_n)) A_n − condKsEntropySeq 𝒜 hT P n = H(A_n | σ(B_n)) − H(A_n | 𝒜)`.
The single residual `hdefect` asserts that the Cesàro average `defect / n` of this gap vanishes.

## Main results

* `ErgodicTheory.Entropy.tendsto_condCellSeq_of_defect`: under `hdefect`, the Cesàro average of the
  conditional cell-form sequence `condCellSeq hT Q P n / n` converges to `condKsEntropyPartition`
  (i.e. `hdefect ⟹ hW3`). This is pure `Tendsto` algebra over the W2 bridge.
* `ErgodicTheory.Entropy.abramovRokhlin_partition_of_defect`: the partition-level Abramov–Rokhlin
  identity `h(P, T) = h(Q, T) + h(P, T | 𝒜)` holds under `hdefect` in place of `hW3` — the sharpest
  reduction of the identity to the single Cesàro entropy-defect residual.

## References

* Manfred Einsiedler, Elon Lindenstrauss, Thomas Ward, *Entropy in Ergodic Theory and Topological
  Dynamics*, Ch. 2 (cf. Prop. 2.19, the future formula).
* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM **79** (1982), §4.5.
* L. M. Abramov, V. A. Rokhlin, *The entropy of a skew product of measure-preserving
  transformations*, Vestnik Leningrad Univ. **17** (1962).
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

-- The variable ORDER `{𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]` (mirroring
-- `CondKSEntropy`/`AbramovRokhlinPartition`) is load-bearing: `mα` is declared AFTER `𝒜`, so it
-- has higher instance priority and `Measure α` / `StandardBorelSpace α` resolve to the ambient
-- `mα`, not the conditioning sub-σ-algebra `𝒜`.
variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α}

/-- **The conditional cell-form sequence converges, from the vanishing-defect residual** (i.e.
`hdefect ⟹ hW3`). Suppose the Cesàro average of the **entropy defect**
`H(A_n | σ(B_n)) − H(A_n | 𝒜) = condEntropy μ (σ(B_n)) A_n − condKsEntropySeq 𝒜 hT P n`
— the gap between conditioning the `P`-join `A_n = ⋁_{k<n}T⁻ᵏP` on the *moving* generated σ-algebra
`σ(B_n) = generatedSigmaAlgebra μ (ksJoin hT Q n)` versus the *fixed* factor σ-algebra `𝒜` —
vanishes (`hdefect`). Then the Cesàro average of the conditional cell-form sequence converges to the
relative
Kolmogorov–Sinai entropy:
`(1/n) condCellSeq hT Q P n → condKsEntropyPartition hm hT hinv P`.

The W2 bridge `condEntropyGivenPartition_eq_condEntropy_generated` identifies, for every `n`, the
cell-form conditional entropy `condCellSeq hT Q P n` with the σ-algebra conditional entropy
`condEntropy μ (σ(B_n)) A_n`. Splitting `a/n = b/n + (a − b)/n` writes `condCellSeq / n` as
`condKsEntropySeq / n` plus `defect / n`; the first summand converges to `condKsEntropyPartition`
by Fekete (`tendsto_condKsEntropySeq`), the second to `0` by `hdefect`. -/
theorem tendsto_condCellSeq_of_defect [Fintype ι] [Fintype κ]
    (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (hdefect : Tendsto (fun n => (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
        (ksJoin hT P n).cells - condKsEntropySeq 𝒜 hT P n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => condCellSeq hT Q P n / n) atTop
      (𝓝 (condKsEntropyPartition hm hT hinv P)) := by
  -- W2 bridge: the cell-form conditional entropy is the σ-algebra conditional entropy against the
  -- moving generated σ-algebra `σ(B_n)`.
  have hbridge : ∀ n, condCellSeq hT Q P n
      = condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells := fun n =>
    condEntropyGivenPartition_eq_condEntropy_generated (ksJoin hT Q n) (ksJoin hT P n).cells
      (ksJoin hT P n).measurable
  -- Split `condCellSeq / n = condKsEntropySeq / n + defect / n` pointwise.
  have hsplit : (fun n => condCellSeq hT Q P n / n)
      = fun n => condKsEntropySeq 𝒜 hT P n / n
        + (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells
            - condKsEntropySeq 𝒜 hT P n) / n := by
    funext n
    rw [hbridge n, ← add_div, add_sub_cancel]
  -- The first summand converges to `condKsEntropyPartition` (Fekete); the second to `0`.
  have hsum : Tendsto (fun n => condKsEntropySeq 𝒜 hT P n / n
        + (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells
            - condKsEntropySeq 𝒜 hT P n) / n) atTop
      (𝓝 (condKsEntropyPartition hm hT hinv P)) := by
    have := (tendsto_condKsEntropySeq hm hT hinv P).add hdefect
    rwa [add_zero] at this
  rwa [hsplit]

/-- **The Abramov–Rokhlin partition identity, modulo the single Cesàro entropy-defect residual.**
This is the **sharpest reduction** of the partition-level Abramov–Rokhlin identity. Given the
per-`n` refinement of `A_n = ⋁_{k<n}T⁻ᵏP` over `B_n = ⋁_{k<n}T⁻ᵏQ` (each `P`-join cell is `μ`-a.e.
inside a
single `Q`-join cell, witnessed by `g`), the whole identity
`h(P, T) = h(Q, T) + h(P, T | 𝒜)`
now rests on the *single* analytic residual `hdefect`: that the Cesàro average of the **entropy
defect**
`H(A_n | σ(B_n)) − H(A_n | 𝒜)`
vanishes — i.e. that the gap between conditioning on the *moving* generated σ-algebra
`σ(B_n) = generatedSigmaAlgebra μ (ksJoin hT Q n)` (the σ-algebra catching up as `n → ∞`) and the
*fixed* factor σ-algebra `𝒜` washes out in the Cesàro average. Everything else is discharged
sorry-free: `tendsto_condCellSeq_of_defect` turns `hdefect` into the `hW3` limit-identity through
the
W2 bridge, and `abramovRokhlin_partition_of_W3` then assembles the identity from the per-`n`
refinement and the two Fekete convergences.

See Einsiedler–Lindenstrauss–Ward, *Entropy in Ergodic Theory and Topological Dynamics*, Ch. 2
(cf. Prop. 2.19, the future formula), and Walters, GTM **79**, §4.5. -/
theorem abramovRokhlin_partition_of_defect [Fintype ι] [Fintype κ]
    (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (g : ∀ n, (Fin n → ι) → (Fin n → κ))
    (hrefine : ∀ n f, (ksJoin hT P n).cells f ≤ᵐ[μ] (ksJoin hT Q n).cells (g n f))
    (hdefect : Tendsto (fun n => (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
        (ksJoin hT P n).cells - condKsEntropySeq 𝒜 hT P n) / n) atTop (𝓝 0)) :
    ksEntropyPartition hT P
      = ksEntropyPartition hT Q + condKsEntropyPartition hm hT hinv P :=
  abramovRokhlin_partition_of_W3 hm hT hinv Q P g hrefine
    (tendsto_condCellSeq_of_defect hm hT hinv Q P hdefect)

end ErgodicTheory.Entropy
