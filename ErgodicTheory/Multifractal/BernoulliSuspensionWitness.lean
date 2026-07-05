/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.BernoulliSuspensionFlow
import ErgodicTheory.Multifractal.BernoulliHeterogeneous

/-!
# The multifractal witness of the Bernoulli suspension flow (issue #19, deliverable (ii))

Issue #19 asks for two deliverables for the constant-roof (`τ ≡ 1`) suspension flow of the
two-sided asymmetric Bernoulli shift:

* **(i)** positive metric entropy `0 < h(Φ)` — supplied by
  `ErgodicTheory.Multifractal.suspensionFlow_bernZ_ksEntropy_pos`
  (`ErgodicTheory/Multifractal/BernoulliSuspensionFlow.lean`);
* **(ii) the WITNESS (this file):** an explicit finite measurable partition `P` of the flow's
  invariant probability measure `μ̂ := suspensionMeasure biShiftEquiv measurable_oneRoof (bernZ ν)`
  that is **heterogeneous** (`IsHeterogeneous μ̂ P`) and on which the Rényi (generalized) dimension
  `renyiDimFlow (bernSuspensionFlow ν) P` is **genuinely `q`-dependent** — a *non-vacuous* witness
  of multifractality (not a bare existential, but one driven by the genuine bias of `ν`).

## The witness partition

The witness is the base coordinate partition pulled back along the base projection (factor map)
`π := suspensionBaseProj`:

`P := (coordPartitionZFin (bernZ ν)).pulledBack (measurePreserving_suspensionBaseProj ν)`,

a `Fin (Fintype.card α₀)`-indexed measurable partition of the *flow* measure `μ̂`.

## The mass identity (the crux)

The load-bearing fact is that pulling the base coordinate partition back along the
measure-preserving `π` does not change the cell masses: for each `Fin`-index `j`,

`μ̂ (P.cells j) = bernZ ν ((coordPartitionZFin (bernZ ν)).cells j)
                = ν {(Fintype.equivFin α₀).symm j}`.

The first equality is `(measurePreserving_suspensionBaseProj ν).measure_preimage` on the
(measurable) cell; the second is the two-sided marginal identity
`measure_coordPartitionZ_cell_bernZ` (the `0`-th coordinate of an i.i.d. product is distributed as
`ν`), reindexed by `(Fintype.equivFin α₀).symm`.

## Main results

* `ErgodicTheory.Multifractal.measure_coordPartitionZ_cell_bernZ`: the two-sided marginal identity
  `bernZ ν ((coordPartitionZ (bernZ ν)).cells a) = ν {a}`.
* `ErgodicTheory.Multifractal.bernSuspensionWitness`: the witness partition `P`.
* `ErgodicTheory.Multifractal.measure_bernSuspensionWitness_cell`: the cell-mass identity
  `(μ̂ (P.cells j)).toReal = (ν {(Fintype.equivFin α₀).symm j}).toReal`.
* `ErgodicTheory.Multifractal.isHeterogeneous_bernSuspensionWitness`: heterogeneity of `P`.
* `ErgodicTheory.Multifractal.renyiDimFlow_bernSuspension_eq_base`: the flow Rényi spectrum equals the
  one-sided base spectrum at every `q` (the transfer).
* `ErgodicTheory.Multifractal.renyiDimFlow_bernSuspension_zero_ne_one`: the headline non-vacuous
  `q`-dependence at the *explicit* exponents `q = 0, 1`, reduced to the biased fact `Hnu ν < log 2`.
* `ErgodicTheory.Multifractal.renyiDimFlow_bernSuspension_q_dependent`: its `∃`-corollary.
-/

open MeasureTheory Real Function Set
open scoped ENNReal

namespace ErgodicTheory.Multifractal

open ErgodicTheory.Entropy

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀]
  [MeasurableSingletonClass α₀] (ν : Measure α₀) [IsProbabilityMeasure ν]

/-! ### The two-sided marginal identity -/

/-- **Marginal identity for the coordinate partition of the two-sided Bernoulli measure.** The mass
that the two-sided i.i.d. product measure `bernZ ν` assigns to the `0`-th coordinate cell
`(coordPartitionZ (bernZ ν)).cells a = {x | x 0 = a}` is the single-symbol mass `ν {a}`. The cell is
the measurable cylinder box `Set.pi ↑({0} : Finset ℤ) (fun _ => {a})`, whose `bernZ ν`-mass
factorizes (`bernZ_pi_eq_prod`) to the single-coordinate product `∏ i ∈ {0}, ν {a} = ν {a}`. This is
the two-sided mirror of the one-sided `measure_coordPartition_cell_bern`. -/
theorem measure_coordPartitionZ_cell_bernZ (a : α₀) :
    bernZ ν ((coordPartitionZ (bernZ ν)).cells a) = ν {a} := by
  -- The cell `{x | x 0 = a}` is the singleton cylinder box on the coordinate `0`.
  have hcell : (coordPartitionZ (bernZ ν)).cells a
      = Set.pi (↑({0} : Finset ℤ)) (fun _ : ℤ => ({a} : Set α₀)) := by
    ext x
    simp only [coordPartitionZ, Set.mem_setOf_eq, Set.mem_pi, Finset.coe_singleton,
      Set.mem_singleton_iff, forall_eq]
  rw [hcell, bernZ_pi_eq_prod ν _ _ (fun _ => measurableSet_singleton a),
    Finset.prod_singleton]

/-! ### The witness partition -/

/-- **The witness partition** of the constant-roof Bernoulli suspension flow's invariant measure
`μ̂ := suspensionMeasure biShiftEquiv measurable_oneRoof (bernZ ν)`: the base coordinate partition
`coordPartitionZFin (bernZ ν)` pulled back along the base projection (factor map)
`π := suspensionBaseProj`, which is measure-preserving onto `bernZ ν`
(`measurePreserving_suspensionBaseProj`). Its cell at `j : Fin (Fintype.card α₀)` is
`π ⁻¹' ((coordPartitionZFin (bernZ ν)).cells j)`. -/
noncomputable def bernSuspensionWitness :
    MeasurePartition (suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
      (Fin (Fintype.card α₀)) :=
  (coordPartitionZFin (bernZ ν)).pulledBack (measurePreserving_suspensionBaseProj ν)

/-- **The mass identity (the crux).** The `μ̂`-mass of the `j`-th witness cell equals the
single-symbol mass `ν {(Fintype.equivFin α₀).symm j}` of the corresponding base symbol. The cell is
the `π`-preimage of the base cell (`pulledBack_cells`); pulling it through the measure-preserving
`π` (`measure_preimage`) gives the base mass `bernZ ν ((coordPartitionZFin (bernZ ν)).cells j)`,
which is the reindexed two-sided marginal identity `measure_coordPartitionZ_cell_bernZ`. -/
theorem measure_bernSuspensionWitness_cell (j : Fin (Fintype.card α₀)) :
    (suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
        ((bernSuspensionWitness ν).cells j)
      = ν {(Fintype.equivFin α₀).symm j} := by
  rw [bernSuspensionWitness, MeasurePartition.pulledBack_cells,
    (measurePreserving_suspensionBaseProj ν).measure_preimage
      ((coordPartitionZFin (bernZ ν)).measurable j).nullMeasurableSet]
  -- The base cell of `coordPartitionZFin` is the `coordPartitionZ` cell at the reindexed symbol.
  change bernZ ν ((coordPartitionZ (bernZ ν)).cells ((Fintype.equivFin α₀).symm j)) = _
  rw [measure_coordPartitionZ_cell_bernZ]

/-- The **real-valued** mass identity, the form consumed by `IsHeterogeneous` and the Rényi
spectrum: `(μ̂ (P.cells j)).toReal = (ν {(Fintype.equivFin α₀).symm j}).toReal`. -/
theorem measure_bernSuspensionWitness_cell_toReal (j : Fin (Fintype.card α₀)) :
    ((suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
        ((bernSuspensionWitness ν).cells j)).toReal
      = (ν {(Fintype.equivFin α₀).symm j}).toReal := by
  rw [measure_bernSuspensionWitness_cell]

/-! ### Heterogeneity of the witness -/

/-- **The witness partition is heterogeneous.** For a biased single-symbol law `ν` charging two
distinct symbols `i ≠ j` with *different* masses (`ν {i} ≠ ν {j}`), the witness cells indexed by
`Fintype.equivFin α₀ i` and `Fintype.equivFin α₀ j` carry masses `ν {i}` and `ν {j}` (the mass
identity `measure_bernSuspensionWitness_cell`), which differ; hence
`IsHeterogeneous μ̂ (bernSuspensionWitness ν)`. -/
theorem isHeterogeneous_bernSuspensionWitness {i j : α₀} (_hij : i ≠ j) (hbias : ν {i} ≠ ν {j}) :
    IsHeterogeneous (suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
      (bernSuspensionWitness ν) := by
  refine ⟨Fintype.equivFin α₀ i, Fintype.equivFin α₀ j, ?_⟩
  rw [measure_bernSuspensionWitness_cell_toReal, measure_bernSuspensionWitness_cell_toReal,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  intro hcontra
  exact hbias ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν {i})
    (measure_ne_top ν {j})).1 hcontra)

/-! ### The headline `q`-dependence (transfer route) -/

/-- **The cell-mass families of the flow witness and the one-sided base witness agree up to the
`α₀ ≃ Fin` reindex.** Both Rényi spectra depend only on the cell-mass family, and these agree (each
cell carries a single-symbol mass `ν {·}`), so the flow's partition function at every `q` equals the
one-sided base partition function `partitionFunctionMeasure (bern ν) (coordPartition (bern ν))`.
The reindex `Fintype.equivFin α₀` is summed away by `Equiv.sum_comp`. -/
theorem partitionFunctionMeasure_bernSuspensionWitness_eq (q : ℝ) :
    partitionFunctionMeasure
        (suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
        (bernSuspensionWitness ν) q
      = partitionFunctionMeasure (bern ν) (coordPartition (bern ν)) q := by
  rw [partitionFunctionMeasure, partitionFunctionMeasure, partitionFunction, partitionFunction]
  -- Reindex the flow sum (over `Fin (card α₀)`) to a sum over `α₀` via `Fintype.equivFin α₀`.
  rw [← Equiv.sum_comp (Fintype.equivFin α₀) (fun k : Fin (Fintype.card α₀) =>
    if 0 < ((suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
        ((bernSuspensionWitness ν).cells k)).toReal
      then ((suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
        ((bernSuspensionWitness ν).cells k)).toReal ^ q else 0)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [measure_bernSuspensionWitness_cell_toReal, Equiv.symm_apply_apply,
    measure_coordPartition_cell_bern]

/-- **The flow witness's Rényi spectrum equals the one-sided base spectrum, at every `q`.** Since
`renyiDimFlow (bernSuspensionFlow ν) P ε q` unfolds to `renyiDimMeasure μ̂ P ε q`, and
`renyiDimMeasure` depends only on the cell masses — which agree with those of `bern ν` up to the
`α₀ ≃ Fin` reindex (`partitionFunctionMeasure_bernSuspensionWitness_eq` for the `q ≠ 1` mass
exponent, and the matching entropy-numerator reindex for `q = 1`) — the flow Rényi dimension equals
the one-sided base Rényi dimension `renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε q` at every
`q`. This is the transfer that carries every explicit base value/inequality to the flow. -/
theorem renyiDimFlow_bernSuspension_eq_base {ε : ℝ} (q : ℝ) :
    renyiDimFlow (bernSuspensionFlow ν) (bernSuspensionWitness ν) ε q
      = renyiDimMeasure (bern ν) (coordPartition (bern ν)) ε q := by
  rw [renyiDimFlow, renyiDimMeasure, renyiDimMeasure, renyiDim, renyiDim]
  -- The two `q = 1` numerators `∑ i, p i log p i` agree (reindex the masses by `equivFin`).
  have hnum : (∑ k, ((suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
        ((bernSuspensionWitness ν).cells k)).toReal
        * Real.log (((suspensionMeasure (biShiftEquiv (α₀ := α₀)) measurable_oneRoof (bernZ ν))
          ((bernSuspensionWitness ν).cells k)).toReal))
      = ∑ a, ((bern ν) ((coordPartition (bern ν)).cells a)).toReal
          * Real.log (((bern ν) ((coordPartition (bern ν)).cells a)).toReal) := by
    rw [← Equiv.sum_comp (Fintype.equivFin α₀)
        (fun k => ((suspensionMeasure (biShiftEquiv (α₀ := α₀))
          measurable_oneRoof (bernZ ν)) ((bernSuspensionWitness ν).cells k)).toReal
          * Real.log (((suspensionMeasure (biShiftEquiv (α₀ := α₀))
          measurable_oneRoof (bernZ ν)) ((bernSuspensionWitness ν).cells k)).toReal))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [measure_bernSuspensionWitness_cell_toReal, Equiv.symm_apply_apply,
      measure_coordPartition_cell_bern]
  -- The mass exponents agree (their partition functions agree, by the same reindex).
  have hmass : massExponent (fun k => ((suspensionMeasure (biShiftEquiv (α₀ := α₀))
        measurable_oneRoof (bernZ ν)) ((bernSuspensionWitness ν).cells k)).toReal) ε q
      = massExponent (fun a => ((bern ν) ((coordPartition (bern ν)).cells a)).toReal) ε q := by
    rw [massExponent, massExponent]
    congr 2
    exact partitionFunctionMeasure_bernSuspensionWitness_eq ν q
  by_cases hq : q = 1
  · rw [if_pos hq, if_pos hq, hnum]
  · rw [if_neg hq, if_neg hq, hmass]

/-- **THE HEADLINE (deliverable (ii)), explicit witnesses `q = 0, 1`.** For a scale `0 < ε < 1` and
a biased 2-symbol law `ν` (exactly two symbols `i ≠ j`, both of positive mass, with
`(ν {i}).toReal ≠ (ν {j}).toReal`), the Rényi (generalized) dimension of the **flow's invariant
measure** `μ̂` for the witness partition takes *different* values at the **explicit** exponents
`q = 0` and `q = 1`. Concretely `D₀ = log 2 / (-log ε)` (both atoms occupied) and
`D₁ = Hnu ν / (-log ε)` (the information dimension); they differ precisely because `Hnu ν < log 2`
— the strict bias bound `Hnu_lt_log_two`. This is the **non-vacuous** witness: the inequality at the
exhibited exponents is driven by the genuine bias of `ν`, not satisfied trivially.

The proof **transfers** the explicit one-sided base inequality `renyiDimMeasure_zero_ne_one_bern`
through `renyiDimFlow_bernSuspension_eq_base` (the flow and base Rényi dimensions coincide at every
`q`). -/
theorem renyiDimFlow_bernSuspension_zero_ne_one [DecidableEq α₀] {i j : α₀} (hij : i ≠ j)
    (huniv : (Finset.univ : Finset α₀) = {i, j})
    (hbias : (ν {i}).toReal ≠ (ν {j}).toReal)
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    renyiDimFlow (bernSuspensionFlow ν) (bernSuspensionWitness ν) ε 0
      ≠ renyiDimFlow (bernSuspensionFlow ν) (bernSuspensionWitness ν) ε 1 := by
  rw [renyiDimFlow_bernSuspension_eq_base ν 0, renyiDimFlow_bernSuspension_eq_base ν 1]
  exact renyiDimMeasure_zero_ne_one_bern hij huniv hbias hi hj hε0 hε1

/-- **The headline (deliverable (ii)), existential form.** The `∃`-corollary of the explicit
`renyiDimFlow_bernSuspension_zero_ne_one`: for a scale `0 < ε < 1` and a biased 2-symbol law `ν`,
the flow's Rényi dimension takes different values at the *explicit* exponents `q₁ = 0` and `q₂ = 1`
(the box-counting `D₀ = log 2 / (-log ε)` versus the information dimension `D₁ = Hnu ν / (-log ε)`),
which differ precisely because `Hnu ν < log 2`. Non-vacuous — the exhibited exponents `0, 1` and the
driving bias bound are recorded in `renyiDimFlow_bernSuspension_zero_ne_one`, not left implicit. -/
theorem renyiDimFlow_bernSuspension_q_dependent [DecidableEq α₀] {i j : α₀} (hij : i ≠ j)
    (huniv : (Finset.univ : Finset α₀) = {i, j})
    (hbias : (ν {i}).toReal ≠ (ν {j}).toReal)
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ q₁ q₂ : ℝ,
      renyiDimFlow (bernSuspensionFlow ν) (bernSuspensionWitness ν) ε q₁
        ≠ renyiDimFlow (bernSuspensionFlow ν) (bernSuspensionWitness ν) ε q₂ :=
  ⟨0, 1, renyiDimFlow_bernSuspension_zero_ne_one ν hij huniv hbias hi hj hε0 hε1⟩

end ErgodicTheory.Multifractal
