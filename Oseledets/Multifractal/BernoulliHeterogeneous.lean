/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.SymbolicDimensionBernoulli
import Oseledets.Multifractal.Measure
import Oseledets.Multifractal.Source.FlowPartition

/-!
# Genuine `q`-dependence of the Rényi spectrum of a biased Bernoulli measure (issue #19)

The downstream WITNESS of issue #19 needs the `q`-dependence of the Rényi (generalized) dimension
spectrum to be *genuinely* non-vacuous — not a bare existential `∃ q₁ q₂, D q₁ ≠ D q₂` that could be
satisfied trivially by a degenerate (uniform / monofractal) measure whose whole spectrum is a single
point. This file supplies the pure measure-theoretic prerequisites that make the witness real, for
the load-bearing **biased 2-symbol Bernoulli measure**.

The chain is:

* **Item 1 — the strict entropy bound.** For a biased law on two symbols (masses `p`, `1 - p`,
  `p ≠ 1/2`) the single-symbol Shannon entropy is *strictly below* the uniform maximum:
  `Hnu ν < log 2`. This is the load-bearing strict inequality; it rests on the **strict concavity**
  of `Real.negMulLog` (`Real.strictConcaveOn_negMulLog`), evaluated at the two-point pair
  `(p, 1 - p)` against its midpoint `1/2`, where `2 · negMulLog (1/2) = log 2`.
* **Item 2 — base heterogeneity.** For a biased `ν` (`ν {i} ≠ ν {j}`) the coordinate-partition cell
  masses of `bern ν` differ, `IsHeterogeneous (bern ν) (coordPartition (bern ν))`. Immediate from
  the marginal identity `(bern ν) {x | x 0 = i} = ν {i}` (the `0`-th coordinate of an i.i.d. product
  is distributed as `ν`).
* **Item 3 — explicit `q`-dependence.** Combining the two, the Rényi dimension of `bern ν` for the
  coordinate partition takes *different* values at `q = 0` and `q = 1`: `D₀ = log 2 / (-log ε)`
  (both atoms have positive mass, so `Z₀` counts the two occupied cells) while
  `D₁ = -Hnu ν / log ε = Hnu ν / (-log ε)`; these differ exactly because `Hnu ν < log 2` (item 1).
  Hence `∃ q₁ q₂, renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε q₁ ≠ … q₂`, a *non-vacuous*
  witness of genuine multifractality.

## Main results

* `Oseledets.Multifractal.Hnu_lt_log_two`: the strict bound `Hnu ν < log 2` for a biased 2-symbol
  law.
* `Oseledets.Multifractal.measure_coordPartition_cell_bern`: the marginal identity
  `(bern ν) ((coordPartition (bern ν)).cells i) = ν {i}`.
* `Oseledets.Multifractal.isHeterogeneous_coordPartition_bern`: base heterogeneity of `bern ν`.
* `Oseledets.Multifractal.renyiDimMeasure_coordPartition_bern_zero` /
  `renyiDimMeasure_coordPartition_bern_one`: the explicit dimension values `log 2 / (-log ε)` and
  `Hnu ν / (-log ε)` at `q = 0, 1`.
* `Oseledets.Multifractal.renyiDimMeasure_zero_ne_one_bern`: the explicit non-vacuity witness
  `D₀ ≠ D₁` at the exhibited exponents `q = 0, 1`.
* `Oseledets.Multifractal.renyiDimMeasure_q_dependent_bern`: its `∃`-corollary.
-/

open MeasureTheory Real Function Set
open scoped ENNReal

namespace Oseledets.Multifractal

variable {α₀ : Type*} [Fintype α₀] [DecidableEq α₀] [MeasurableSpace α₀]
  [MeasurableSingletonClass α₀]

/-! ### Item 1 — the strict single-symbol entropy bound `Hnu ν < log 2` -/

/-- **Two-point Shannon entropy is strictly below `log 2`.** For a probability split `p + p' = 1`
with `p ≠ p'` and both `p, p' > 0`, the sum `negMulLog p + negMulLog p' < log 2`. This is the
strict-concavity bound on the binary entropy: applying the strict concavity of `Real.negMulLog`
(`Real.strictConcaveOn_negMulLog`) to the distinct points `p ≠ p'` at the midpoint weights
`1/2, 1/2` gives `(1/2) negMulLog p + (1/2) negMulLog p' < negMulLog ((1/2) p + (1/2) p')`, whose
right-hand argument is `1/2`; since `2 · negMulLog (1/2) = log 2`, doubling yields the claim. -/
theorem negMulLog_add_negMulLog_lt_log_two {p p' : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hsum : p + p' = 1) (hbias : p ≠ p') :
    Real.negMulLog p + Real.negMulLog p' < Real.log 2 := by
  have hpmem : p ∈ Set.Ici (0 : ℝ) := le_of_lt hp
  have hp'mem : p' ∈ Set.Ici (0 : ℝ) := le_of_lt hp'
  -- Strict concavity of `negMulLog` at the distinct points `p ≠ p'` with weights `1/2, 1/2`.
  have hstrict := Real.strictConcaveOn_negMulLog.2 hpmem hp'mem hbias
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  -- The midpoint argument is `1/2`.
  have hmid : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • p' = 1 / 2 := by
    simp only [smul_eq_mul]
    linarith
  rw [hmid] at hstrict
  -- `negMulLog (1/2) = (1/2) * log 2`, so `2 • negMulLog (1/2) = log 2`.
  have hhalf : Real.negMulLog (1 / 2 : ℝ) = (1 / 2) * Real.log 2 := by
    rw [Real.negMulLog, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    ring
  simp only [smul_eq_mul] at hstrict
  rw [hhalf] at hstrict
  linarith

/-- **The load-bearing strict bound (2-symbol case): `Hnu ν < log 2`.** For a probability law `ν`
on an alphabet with *exactly two* symbols `i ≠ j` (`Finset.univ = {i, j}`) that is **biased**
(`(ν {i}).toReal ≠ (ν {j}).toReal`) with both masses positive, the single-symbol Shannon entropy is
strictly below the uniform maximum `log 2 = log (Fintype.card α₀)`. The entropy unfolds (over the
two-element universe) to `negMulLog (ν {i}).toReal + negMulLog (ν {j}).toReal` with the masses
summing to `1` (disjoint singletons covering the universe), so the claim is the strict two-point
entropy bound `negMulLog_add_negMulLog_lt_log_two`. -/
theorem Hnu_lt_log_two {ν : Measure α₀} [IsProbabilityMeasure ν] {i j : α₀} (hij : i ≠ j)
    (huniv : (Finset.univ : Finset α₀) = {i, j})
    (hbias : (ν {i}).toReal ≠ (ν {j}).toReal)
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal) :
    Hnu ν < Real.log 2 := by
  -- The two masses sum to `1`: `{i} ∪ {j}` is the whole (two-symbol) universe.
  have hdisj : Disjoint ({i} : Set α₀) {j} := by simp [hij]
  have hcover : ({i} : Set α₀) ∪ {j} = Set.univ := by
    rw [← Set.univ_subset_iff]
    intro x _
    have hx : x ∈ (Finset.univ : Finset α₀) := Finset.mem_univ x
    rw [huniv, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  have hsum_one : ν {i} + ν {j} = 1 := by
    rw [← measure_union hdisj (measurableSet_singleton j), hcover, measure_univ]
  have hi_top : ν {i} ≠ ⊤ := measure_ne_top ν {i}
  have hj_top : ν {j} ≠ ⊤ := measure_ne_top ν {j}
  have hsum_one' : (ν {i}).toReal + (ν {j}).toReal = 1 := by
    rw [← ENNReal.toReal_add hi_top hj_top, hsum_one, ENNReal.toReal_one]
  -- `Hnu ν` is the two-term sum over `{i, j}`.
  have hHnu : Hnu ν = Real.negMulLog (ν {i}).toReal + Real.negMulLog (ν {j}).toReal := by
    rw [Hnu, huniv, Finset.sum_pair hij]
  rw [hHnu]
  exact negMulLog_add_negMulLog_lt_log_two hi hj hsum_one' hbias

/-! ### Item 2 — base heterogeneity of the biased Bernoulli measure -/

omit [DecidableEq α₀] in
/-- **Marginal identity for the coordinate partition of a Bernoulli measure.** The mass that the
i.i.d. product measure `bern ν` assigns to the `0`-th coordinate cell `{x | x 0 = i}` is the
single-symbol mass `ν {i}`: the cell is the preimage `(Function.eval 0) ⁻¹' {i}`, and the
coordinate evaluation `eval 0` is measure-preserving from `bern ν = Measure.infinitePi (fun _ => ν)`
to its `0`-th marginal `ν` (`measurePreserving_eval_infinitePi`). -/
theorem measure_coordPartition_cell_bern (ν : Measure α₀) [IsProbabilityMeasure ν] (i : α₀) :
    (bern ν) ((coordPartition (bern ν)).cells i) = ν {i} := by
  have hcell : (coordPartition (bern ν)).cells i = (fun x : Shift α₀ => x 0) ⁻¹' {i} := by
    ext x
    simp only [coordPartition, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hcell, bern]
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).measure_preimage
    (measurableSet_singleton i).nullMeasurableSet

omit [DecidableEq α₀] in
/-- **Base heterogeneity of a biased Bernoulli measure.** If the single-symbol law `ν` charges two
distinct symbols `i ≠ j` with *different* masses (`ν {i} ≠ ν {j}`), the coordinate-partition cell
masses of `bern ν` differ, so `IsHeterogeneous (bern ν) (coordPartition (bern ν))`. Immediate from
the marginal identity `measure_coordPartition_cell_bern`: the cell mass at `i` is `(ν {i}).toReal`,
so distinct atom masses give distinct cell masses. -/
theorem isHeterogeneous_coordPartition_bern (ν : Measure α₀) [IsProbabilityMeasure ν] {i j : α₀}
    (hbias : ν {i} ≠ ν {j}) :
    IsHeterogeneous (bern ν) (coordPartition (bern ν)) := by
  refine ⟨i, j, ?_⟩
  rw [measure_coordPartition_cell_bern ν i, measure_coordPartition_cell_bern ν j]
  intro hcontra
  exact hbias ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν {i})
    (measure_ne_top ν {j})).1 hcontra)

/-! ### Item 3 — explicit `q`-dependence of the Rényi spectrum -/

/-- The partition function of `bern ν` at `q = 0` (2-symbol case) counts the two occupied cells:
`Z₀ = 2`. Both atoms have positive mass, so each occupied guard contributes `(mass)^0 = 1`, and
there are exactly two cells. -/
theorem partitionFunctionMeasure_coordPartition_bern_zero {ν : Measure α₀} [IsProbabilityMeasure ν]
    {i j : α₀} (hij : i ≠ j) (huniv : (Finset.univ : Finset α₀) = {i, j})
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal) :
    partitionFunctionMeasure (bern ν) (coordPartition (bern ν)) 0 = 2 := by
  rw [partitionFunctionMeasure, partitionFunction]
  -- The cell mass at `k` is `(ν {k}).toReal`; both guards `0 < mass` hold for `k ∈ {i, j}`.
  have hmass : ∀ k : α₀, ((bern ν) ((coordPartition (bern ν)).cells k)).toReal = (ν {k}).toReal :=
    fun k => by rw [measure_coordPartition_cell_bern ν k]
  rw [huniv, Finset.sum_pair hij]
  rw [hmass i, hmass j, if_pos hi, if_pos hj, Real.rpow_zero, Real.rpow_zero]
  norm_num

/-- **The Rényi dimension of `bern ν` at `q = 0` (explicit value).** For a scale `0 < ε < 1` and a
biased 2-symbol law `ν` (exactly two symbols `i ≠ j`, both of positive mass), the `q = 0` Rényi
(generalized) dimension of `bern ν` for the coordinate partition is the box-counting value
`D₀ = log 2 / (-log ε)`: both atoms are occupied, so the partition function `Z₀` counts the two
cells (`partitionFunctionMeasure_coordPartition_bern_zero`). -/
theorem renyiDimMeasure_coordPartition_bern_zero {ν : Measure α₀} [IsProbabilityMeasure ν]
    {i j : α₀} (hij : i ≠ j) (huniv : (Finset.univ : Finset α₀) = {i, j})
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε 0 = Real.log 2 / (-Real.log ε) := by
  have hlogε_neg : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hlogε_ne : Real.log ε ≠ 0 := ne_of_lt hlogε_neg
  -- `D₀ = massExponent / (0 - 1) = - massExponent`; with `Z₀ = 2`, `massExponent = log 2 / log ε`.
  have hZ0 : partitionFunction
      (fun k => ((bern ν) ((coordPartition (bern ν)).cells k)).toReal) 0 = 2 :=
    partitionFunctionMeasure_coordPartition_bern_zero hij huniv hi hj
  rw [renyiDimMeasure, renyiDim, if_neg (by norm_num : (0 : ℝ) ≠ 1), massExponent, hZ0]
  field_simp
  ring

omit [DecidableEq α₀] in
/-- **The Rényi dimension of `bern ν` at `q = 1` (explicit value, information dimension).** The
`q = 1` Rényi (generalized) dimension of `bern ν` for the coordinate partition is
`D₁ = Hnu ν / (-log ε)`: the `q = 1` branch is the Shannon entropy of the partition divided by
`-log ε` (`renyiDimMeasure_one_eq`), and the coordinate partition's entropy is the single-symbol
entropy `Hnu ν` (the marginal identity `measure_coordPartition_cell_bern`). -/
theorem renyiDimMeasure_coordPartition_bern_one {ν : Measure α₀} [IsProbabilityMeasure ν] {ε : ℝ} :
    renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε 1 = Hnu ν / (-Real.log ε) := by
  have hentropy : Oseledets.Entropy.entropy (bern ν) (coordPartition (bern ν)).cells = Hnu ν := by
    rw [Oseledets.Entropy.entropy_def, Hnu]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [measure_coordPartition_cell_bern ν k]
  rw [renyiDimMeasure_one_eq, hentropy, neg_div, div_neg]

/-- **The non-vacuity core (explicit witnesses `q = 0, 1`): the Rényi dimension of a biased
Bernoulli measure differs at `q = 0` and `q = 1`.** For a scale `0 < ε < 1` and a biased 2-symbol
law `ν` (two symbols `i ≠ j`, both of positive mass, with `(ν {i}).toReal ≠ (ν {j}).toReal`),
the two *explicit* values `D₀ = log 2 / (-log ε)` (box counting,
`renyiDimMeasure_coordPartition_bern_zero`) and `D₁ = Hnu ν / (-log ε)` (information dimension,
`renyiDimMeasure_coordPartition_bern_one`) are **distinct**: they share the nonzero denominator
`-log ε`, and their numerators differ because `Hnu ν < log 2` (the strict bias bound
`Hnu_lt_log_two`, item 1). This is the honest, non-vacuous `q`-dependence — the exponents `q = 0, 1`
and the inequality are exhibited, not merely existentially asserted. -/
theorem renyiDimMeasure_zero_ne_one_bern {ν : Measure α₀} [IsProbabilityMeasure ν] {i j : α₀}
    (hij : i ≠ j) (huniv : (Finset.univ : Finset α₀) = {i, j})
    (hbias : (ν {i}).toReal ≠ (ν {j}).toReal)
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε 0
      ≠ renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε 1 := by
  rw [renyiDimMeasure_coordPartition_bern_zero hij huniv hi hj hε0 hε1,
    renyiDimMeasure_coordPartition_bern_one]
  -- The two values share the nonzero denominator `-log ε`, so they agree iff `log 2 = Hnu ν`.
  intro hcontra
  have hlogε_neg : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hnegε_ne : -Real.log ε ≠ 0 := neg_ne_zero.2 (ne_of_lt hlogε_neg)
  have hne : Real.log 2 = Hnu ν := (div_left_inj' hnegε_ne).1 hcontra
  exact absurd hne.symm (ne_of_lt (Hnu_lt_log_two hij huniv hbias hi hj))

/-- **The non-vacuity core (existential form).** The `∃`-corollary of the explicit
`renyiDimMeasure_zero_ne_one_bern`: for a scale `0 < ε < 1` and a biased 2-symbol law `ν`, the Rényi
(generalized) dimension of `bern ν` for the coordinate partition takes different values at the
*explicit* exponents `q₁ = 0` and `q₂ = 1` — the box-counting `D₀ = log 2 / (-log ε)` versus the
information dimension `D₁ = Hnu ν / (-log ε)`, which differ precisely because `Hnu ν < log 2`. This
is a **non-vacuous** witness: the exhibited exponents `0, 1` and the driving bias bound are recorded
in `renyiDimMeasure_zero_ne_one_bern`, not left implicit. -/
theorem renyiDimMeasure_q_dependent_bern {ν : Measure α₀} [IsProbabilityMeasure ν] {i j : α₀}
    (hij : i ≠ j) (huniv : (Finset.univ : Finset α₀) = {i, j})
    (hbias : (ν {i}).toReal ≠ (ν {j}).toReal)
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ q₁ q₂ : ℝ,
      renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε q₁
        ≠ renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε q₂ :=
  ⟨0, 1, renyiDimMeasure_zero_ne_one_bern hij huniv hbias hi hj hε0 hε1⟩

end Oseledets.Multifractal
