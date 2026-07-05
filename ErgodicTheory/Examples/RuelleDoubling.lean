/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.Elementary
import ErgodicTheory.Lyapunov.Extensions.ExponentSums
import ErgodicTheory.Entropy.Ruelle.Crude

/-!
# A non-vacuous instance of the per-partition Ruelle bound: the doubling map

The abstract per-partition Ruelle inequality `h(α, T) ≤ ∑ λᵢ⁺` — entropy relative to **one**
partition `α` — has as its unconditional arithmetic backbone
`ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth`, which isolates the genuinely
geometric content as an explicit atom-counting hypothesis and proves everything around it. This
module **instantiates that content concretely** on the classical worked example: the **doubling
map** `T : y ↦ 2 • y` on the unit circle (`ErgodicTheory.doublingMap`,
`ErgodicTheory/Examples/Elementary.lean`).

The headline `ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp` proves the **per-partition**
bound `ksEntropyPartition hT P ≤ sumPosExp`, i.e. `h(α, T) ≤ ∑ λᵢ⁺`, for a *single* partition `α` —
it is **not** the system Margulis–Ruelle inequality `h(T) ≤ ∑ λᵢ⁺`. The bridge from the
per-partition bound to the system entropy is the Kolmogorov–Sinai identity `h(T) = h(α, T)` for a
**generating** partition `α`, which is an un-formalized named input (see below).

For the doubling map the right-hand side equals `log 2`:

* the **right-hand side** — the sum of the strictly positive Lyapunov exponents of the (constant)
  derivative cocycle, generator `M = !![2]` — is `log 2` (the single exponent is `log 2 > 0`).

For the binary generating partition the left-hand side is also `log 2`, so the per-partition bound
`h(α, T) ≤ log 2` is *attained* — but that equality is **not** proved in this file; it is the
sibling theorem `ErgodicTheory.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two`
(`h(α, T) = log 2`). Cross-referencing that lemma is what backs the "attained" claim with a real
proof rather than prose.

## What is discharged here, and what stays an honest input

* **The right-hand side is computed unconditionally.** `ErgodicTheory.doublingMap_sumPosExp_eq_log_two`
  proves `sumPosExp = log 2` for the doubling-map constant cocycle, with *every* spectrum hypothesis
  (invertibility, measurability, the two log-integrability conditions) discharged from the
  constant-cocycle API (`const_det_ne_zero`, `const_measurable`, `const_integrableLogNorm`,
  `const_integrableLogNorm_inv`). It reuses the proven single exponent
  `ErgodicTheory.doublingMap_topExponent_eq_log_two` (`= log 2`). This is the genuine positive-exponent
  *sum* side, fully sorry-free.

* **The per-partition Ruelle inequality is instantiated at the rate `log 2`.**
  `ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp` specializes the unconditional arithmetic
  backbone `ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth` to the doubling map at the
  exponential rate `R = log 2`, and then *identifies that rate with the computed positive-exponent
  sum*: from the atom-count growth `atomCount ≤ C · 2ⁿ` of a partition's `n`-refinement, the
  partition entropy `h(α, T)` is bounded by `sumPosExp = log 2`. The rate here is not an assumed
  abstract constant — it is the actual Lyapunov datum `log 2`.

The atom-count hypothesis `hgrow` (`atomCount ≤ C · 2ⁿ`) is **automatic for the binary partition**:
the `n`-fold refinement of a 2-element partition has at most `card(ι)ⁿ = 2ⁿ` atoms by the generic
bound `atomCount ≤ card(ι)ⁿ` (the count of formal `n`-tuples of cells), with no use of any
doubling-map-specific geometry. So the natural binary instance exercises **no** sharp geometric
input. The geometric content of `hgrow` only *bites* for partitions of cardinality `> 2`, where
`card(ι)ⁿ` exceeds `2ⁿ` and the exact `2`-to-`1` structure of the doubling map (a partition into
intervals refines under `T^[n]` into `≈ 2ⁿ` atoms, not `card(ι)ⁿ`) is what pins the rate down. The
hypothesis has exactly the status the Mañé/Katok count carries in `ErgodicTheory.Entropy.Ruelle.Crude`,
here with the rate `log 2` matching the true exponent.

The remaining bridge to a fully unconditional `h(T) ≤ log 2` over the **system** entropy is the
Kolmogorov–Sinai theorem `h(T) = h(α, T)` for a generating partition `α` (Le Maître's notes, §1),
multi-month-scale ergodic infrastructure not present in Mathlib, hence deliberately left as the
named input.

## Main results

* `ErgodicTheory.doublingMap_sumPosExp_eq_log_two` — the positive-exponent sum of the doubling-map
  constant cocycle is `log 2` (unconditional, all hypotheses discharged).
* `ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp` — the **per-partition** Ruelle bound
  `h(α, T) ≤ ∑ λᵢ⁺ = log 2` for the doubling map, from the atom-count growth at rate `log 2`.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7.
* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory

/-! ## The positive-exponent sum of the doubling-map cocycle is `log 2` -/

/-- The single Lyapunov exponent of the doubling-map constant cocycle (generator `M = !![2]`,
indexed by `Fin (Fintype.card (Fin 1)) = Fin 1`) is `log 2`.

This is `ErgodicTheory.doublingMap_topExponent_eq_log_two` read off the only spectrum index: the top
exponent `exponents … ⟨0, _⟩` *is* the single exponent, and a subsingleton index forces every index
to that value. -/
theorem doublingMap_exponents_eq_log_two
    (i : Fin (Fintype.card (Fin 1))) :
    exponents ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
        (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
        (const_integrableLogNorm_inv doublingGen) i
      = Real.log 2 := by
  -- `exponents_const` evaluates the spectrum at the (only) sorted index to `log` of the eigenvalue.
  have key := exponents_const ergodic_doublingMap doublingGen_transpose doublingGen_det_ne_zero
    (i : Fin (Fintype.card (Fin 1)))
  rw [eigenvalues₀_absMatrix_of_posSemidef doublingGen_posSemidef, doublingGen_eigenvalue] at key
  -- The reindexing `⟨(i : ℕ), …⟩ : Fin 1` is the index `i` itself.
  rwa [show (⟨(i : ℕ), lt_of_lt_of_eq i.isLt (Fintype.card_fin 1)⟩ : Fin 1) = i from
    Fin.ext rfl] at key

/-- **Doubling map: the sum of the strictly positive Lyapunov exponents is `log 2`.**

The right-hand side of the Margulis–Ruelle inequality for the doubling-map constant cocycle
(generator `M = !![2]`) is `log 2`: the spectrum has a single exponent `log 2 > 0`, so the
positive-exponent sum is that one term. **Every** hypothesis (invertibility, measurability, and the
two log-integrability conditions) is discharged from the constant-cocycle API, so this
computation is unconditional. -/
theorem doublingMap_sumPosExp_eq_log_two :
    sumPosExp ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
        (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
        (const_integrableLogNorm_inv doublingGen)
      = Real.log 2 := by
  classical
  -- Abbreviate the exponent function; every entry is `log 2 > 0`, so the positive filter is all of
  -- `Finset.univ`, and the sum over the single index `Fin 1` is `log 2`.
  rw [sumPosExp]
  have hval : ∀ i, exponents ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
      (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
      (const_integrableLogNorm_inv doublingGen) i = Real.log 2 :=
    doublingMap_exponents_eq_log_two
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- The positive-exponent filter is the full `Finset.univ` (every exponent is `log 2 > 0`).
  have hfilter : (Finset.univ.filter fun i =>
      0 < exponents ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
        (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
        (const_integrableLogNorm_inv doublingGen) i) = (Finset.univ : Finset (Fin 1)) := by
    refine Finset.filter_true_of_mem (fun i _ => ?_)
    rw [hval i]; exact hpos
  rw [hfilter, Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, one_smul]

/-! ## The non-vacuous per-partition Ruelle inequality for the doubling map -/

/-- **The per-partition Ruelle bound for the doubling map.**

For any finite measurable partition `P` of the unit circle whose `n`-fold refinement
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ P` under the doubling map has eventually at most `C · 2ⁿ` non-empty atoms
(`hgrow`, with `C ≥ 1`), the Kolmogorov–Sinai entropy *relative to that single partition* is bounded
by the sum of the strictly positive Lyapunov exponents of the (constant) derivative cocycle:

`h(α, T) ≤ ∑ λᵢ⁺ = log 2`.

This is the **per-partition** Ruelle bound `h(α, T) ≤ ∑ λᵢ⁺`, **not** the system inequality
`h(T) ≤ ∑ λᵢ⁺` (which additionally needs the Kolmogorov–Sinai identity `h(T) = h(α, T)` for a
generating partition — an un-formalized named input; see the module docstring). The right-hand side
is the *computed* exponent sum `log 2` (`doublingMap_sumPosExp_eq_log_two`), not an abstract
constant.

The bound is **attained** for the binary generating partition, where `h(α, T) = log 2` — but that
equality is proved in the sibling theorem
`ErgodicTheory.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two`, not here.

The atom-count growth `hgrow` is **automatic for the binary partition** (its `n`-refinement has at
most `card(ι)ⁿ = 2ⁿ` atoms by the generic tuple bound, no doubling-map geometry); the geometric
content of `hgrow` only bites for partitions of cardinality `> 2`, where the exact `2`-to-`1`
structure of the doubling map (`≈ 2ⁿ` interval atoms, not `card(ι)ⁿ`) is what pins the rate `log 2`
down (note `2ⁿ = exp(n · log 2)`). The reduction itself is the unconditional arithmetic backbone
`ErgodicTheory.Entropy.ksEntropyPartition_le_of_atomCount_growth`. -/
theorem doublingMap_ksEntropyPartition_le_sumPosExp {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : Entropy.MeasurePartition (volume : Measure UnitAddCircle) ι) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ᶠ n : ℕ in atTop,
      (Entropy.atomCount ergodic_doublingMap.toMeasurePreserving P n : ℝ)
        ≤ C * Real.exp (n * Real.log 2)) :
    Entropy.ksEntropyPartition ergodic_doublingMap.toMeasurePreserving P
      ≤ sumPosExp ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
          (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
          (const_integrableLogNorm_inv doublingGen) := by
  rw [doublingMap_sumPosExp_eq_log_two]
  exact Entropy.ksEntropyPartition_le_of_atomCount_growth
    ergodic_doublingMap.toMeasurePreserving P hC hgrow

end ErgodicTheory
