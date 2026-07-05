/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropy
import ErgodicTheory.Entropy.KSEntropyProps

/-!
# Partition-relative entropy of a uniform-join system

This is the **abstract, system-independent** half of the Rokhlin-equality computation for the
doubling map. It isolates the only fact about the dynamics that is needed: if, for a
measure-preserving transformation `T` and a finite partition `α` indexed by a type `ι` of
cardinality `b`, *every* cell of the `n`-fold join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` has the same measure `b⁻ⁿ`,
then the iterated-join entropy is exactly `n · log b` and the partition-relative
Kolmogorov–Sinai entropy is `h(α, T) = log b`.

For the doubling map with the binary partition (`b = 2`) this gives `h(α, T) = log 2`, the
concrete realization of Pesin's equality on a real expanding system; the dynamical input — that the
`n`-fold join cells are the `2ⁿ` dyadic arcs of length `2⁻ⁿ` — is supplied in
`ErgodicTheory.Examples.Rokhlin.DoublingCrux`.

## Main results

* `ErgodicTheory.Examples.Rokhlin.entropy_uniform_join`: if every join cell has measure `b⁻ⁿ` and there
  are `bⁿ` of them, then `ksEntropySeq hT P n = n · Real.log b`.
* `ErgodicTheory.Examples.Rokhlin.ksEntropyPartition_of_uniform`: under the same uniform-measure
  hypothesis for every `n`, `ksEntropyPartition hT P = Real.log b`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* V. A. Rokhlin, *Lectures on the entropy theory of measure-preserving transformations* (1967).
-/

open MeasureTheory Function Filter Topology
open scoped ENNReal

namespace ErgodicTheory.Examples.Rokhlin

open ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α] [Fintype ι] [Nonempty ι]

/-- **Exact iterated-join entropy of a uniform join.** Suppose every cell of the `n`-fold join
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` has the same measure `(b ^ n)⁻¹`, where `b = Fintype.card ι ≥ 1`. Since the join is
indexed by `Fin n → ι`, a type of cardinality `b ^ n`, the entropy is a sum of `b ^ n` equal terms
`negMulLog (b ^ n)⁻¹ = (b ^ n)⁻¹ · n · log b`, totalling `n · log b`. -/
theorem entropy_uniform_join {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)
    (huniform : ∀ f : Fin n → ι,
      μ ((ksJoin hT P n).cells f) = ((Fintype.card ι : ℝ≥0∞) ^ n)⁻¹) :
    ksEntropySeq hT P n = n * Real.log (Fintype.card ι) := by
  set b : ℕ := Fintype.card ι with hb
  -- The index type `Fin n → ι` has `b ^ n` elements.
  have hcard : Fintype.card (Fin n → ι) = b ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
  -- Each cell contributes the same value `negMulLog ((b : ℝ) ^ n)⁻¹`.
  have hterm : ∀ f : Fin n → ι,
      Real.negMulLog (μ ((ksJoin hT P n).cells f)).toReal
        = Real.negMulLog (((b : ℝ) ^ n)⁻¹) := by
    intro f
    rw [huniform f]
    congr 1
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow]
    norm_cast
  rw [ksEntropySeq, entropy_def, Finset.sum_congr rfl (fun f _ => hterm f),
    Finset.sum_const, Finset.card_univ, hcard]
  -- `(b ^ n) • negMulLog ((b ^ n)⁻¹) = (b ^ n) · ((b ^ n)⁻¹ · n · log b) = n · log b`.
  have hbpos : (0 : ℝ) < (b : ℝ) ^ n := by
    have : (0 : ℝ) < b := by
      rw [hb]; exact_mod_cast Fintype.card_pos
    positivity
  rw [nsmul_eq_mul, Real.negMulLog, Real.log_inv, Real.log_pow]
  push_cast
  field_simp

/-- **Partition-relative Kolmogorov–Sinai entropy of a uniform-join system.** If for *every* `n` the
`n`-fold join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` has all its cells of equal measure `(Fintype.card ι ^ n)⁻¹`, then the
partition-relative entropy is `h(α, T) = Real.log (Fintype.card ι)`. The averaged entropy sequence
`ksEntropySeq n / n` is the constant `log b` for `n ≥ 1` (`entropy_uniform_join`), hence tends to
`log b`; but it also tends to `ksEntropyPartition` (`tendsto_ksEntropySeq`), so the two limits
agree. -/
theorem ksEntropyPartition_of_uniform {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (huniform : ∀ n : ℕ, ∀ f : Fin n → ι,
      μ ((ksJoin hT P n).cells f) = ((Fintype.card ι : ℝ≥0∞) ^ n)⁻¹) :
    ksEntropyPartition hT P = Real.log (Fintype.card ι) := by
  -- The averaged sequence `ksEntropySeq n / n` is eventually the constant `log b`.
  have hconst : (fun _ : ℕ => Real.log (Fintype.card ι))
      =ᶠ[atTop] fun n => ksEntropySeq hT P n / n := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := hn
      positivity
    simp only []
    rw [entropy_uniform_join hT P n (huniform n), mul_comm, mul_div_assoc, div_self hn0, mul_one]
  -- This eventual-equality forces the limit of `ksEntropySeq n / n` to be `log b`.
  have htends_const : Tendsto (fun n => ksEntropySeq hT P n / n) atTop
      (𝓝 (Real.log (Fintype.card ι))) :=
    Tendsto.congr' hconst tendsto_const_nhds
  exact tendsto_nhds_unique (tendsto_ksEntropySeq hT P) htends_const

end ErgodicTheory.Examples.Rokhlin
