/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.CondEntropyContinuous
import ErgodicTheory.Entropy.GeneratorTheorem
import ErgodicTheory.Entropy.CondGivenPartitionBridge

/-!
# Conditional entropy along a σ-saturating partition sequence tends to zero

This file proves the abstract glue lemma `SL3` for the product-entropy upper bound
`h(T × id) ≤ h(T)` (Walters, *An Introduction to Ergodic Theory*, Theorem 4.23) of GitHub
issue #20: for a *fixed* finite measurable partition `P` of a standard-Borel probability space and
an increasing sequence of finite partitions `B n` whose generated σ-algebras *saturate* the ambient
σ-algebra (`⨆ n σ(B n) = mα`), the conditional Shannon entropies `H(P | σ(B n))` converge to `0`.

The lemma is purely an analytic glue step: the actual "rectangle saturation" content
(`⨆ n σ(B n) = mα`) is supplied at assembly, where `B n` is a sequence of product rectangles on
`X × Y` built from coordinate cylinders on a two-sided shift and dyadic partitions of `[0, 1)`.
Crucially, that saturation is *static* (it is the standard generation of the product σ-algebra), so
this route side-steps the two-sided forward-generator wall entirely.

## Proof outline

Two ingredients suffice:

* **Lévy-upward continuity** (`condEntropy_tendsto_iSup`): along the increasing sequence of
  conditioning σ-algebras `𝒜 n := σ(B n)`, the conditional entropies `H(P | 𝒜 n)` converge to the
  conditional entropy `H(P | ⨆ n, 𝒜 n)` with respect to the limiting σ-algebra.
* **Vanishing at the full σ-algebra** (`condEntropy_full_eq_zero`): conditioning on the whole
  ambient σ-algebra `mα` makes every cell mass a.e. `{0, 1}`-valued, so `H(P | mα) = 0`.

Substituting the saturation hypothesis `⨆ n, σ(B n) = mα` into the Lévy limit and applying the
vanishing lemma identifies the limit value as `0`.

## Main results

* `ErgodicTheory.Entropy.tendsto_condEntropy_genJoin_seq_zero`: `H(P | σ(B n)) → 0` along a
  σ-saturating increasing partition sequence.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM **79**, Chapter 4 (Thm 4.23).
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory.Entropy

/-- **SL3 — conditional entropy along a σ-saturating partition sequence tends to zero.**

For a fixed finite measurable partition `P` of a standard-Borel probability space and a sequence
`B : ℕ → Σ k, MeasurePartition μ' (Fin k)` of finite partitions whose generated σ-algebras form an
increasing chain (`hmono`) saturating the ambient σ-algebra (`hsat : ⨆ n, σ(B n) = mα'`), the
conditional Shannon entropies `H(P | σ(B n))` converge to `0`.

This is the analytic glue step of the product-entropy upper bound `h(T × id) ≤ h(T)`
(Walters, Theorem 4.23): the rectangle-saturation content `⨆ n σ(B n) = mα'` is supplied at
assembly. The proof combines Lévy-upward continuity of conditional entropy
(`condEntropy_tendsto_iSup`, giving the limit `H(P | ⨆ n σ(B n))`) with the vanishing of
conditional entropy against the full σ-algebra (`condEntropy_full_eq_zero`), the saturation
hypothesis rewriting `⨆ n σ(B n)` to `mα'`. -/
theorem tendsto_condEntropy_genJoin_seq_zero {α' : Type*} [mα' : MeasurableSpace α']
    [StandardBorelSpace α'] {μ' : Measure α'} [IsProbabilityMeasure μ']
    {ι : Type*} [Fintype ι] [Nonempty ι] (P : MeasurePartition μ' ι)
    (B : ℕ → Σ k, MeasurePartition μ' (Fin k))
    (hmono : Monotone (fun n => generatedSigmaAlgebra μ' (B n).2))
    (hsat : (⨆ n, generatedSigmaAlgebra μ' (B n).2) = mα') :
    Tendsto (fun n => condEntropy μ' (generatedSigmaAlgebra μ' (B n).2) P.cells) atTop (𝓝 0) := by
  -- Each conditioning σ-algebra sits below the ambient one.
  have hle : ∀ n, generatedSigmaAlgebra μ' (B n).2 ≤ mα' :=
    fun n => generatedSigmaAlgebra_le (B n).2
  -- Lévy-upward continuity: the conditional entropies converge to `H(P | ⨆ n σ(B n))`.
  have key : Tendsto (fun n => condEntropy μ' (generatedSigmaAlgebra μ' (B n).2) P.cells) atTop
      (𝓝 (condEntropy μ' (⨆ n, generatedSigmaAlgebra μ' (B n).2) P.cells)) :=
    condEntropy_tendsto_iSup (fun n => generatedSigmaAlgebra μ' (B n).2) hmono hle P
  -- Saturate the limiting σ-algebra to the full one, where the conditional entropy vanishes.
  rwa [hsat, condEntropy_full_eq_zero P] at key

end ErgodicTheory.Entropy
