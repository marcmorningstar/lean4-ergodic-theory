/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.BernoulliTwoSidedErgodic

/-!
# Strong mixing of the two-sided Bernoulli shift

This file upgrades the *ergodicity* of the invertible two-sided Bernoulli shift `biShiftEquiv`
(proved in `ErgodicTheory/Multifractal/BernoulliTwoSidedErgodic.lean` by the cylinder-approximation
mixing squeeze) to full **strong mixing** (2-mixing): for arbitrary measurable sets `A B`,

`bernZ ν (A ∩ biShiftMap^[k] ⁻¹' B) → bernZ ν A · bernZ ν B` as `k → ∞`.

That Bernoulli shifts are strong mixing is classical (Cornfeld–Fomin–Sinai, *Ergodic Theory*, §10;
Walters, *An Introduction to Ergodic Theory*, Thm 1.30 and §4).

## The route

The `#19`-extension asymptotic-independence machinery already delivers *exact* decorrelation of
finite-block cylinders beyond a finite shift: if `A B` are block cylinders, then the blocks of `A`
and of the shifted set `biShiftMap^[k] ⁻¹' B` become disjoint for large `k`, and disjoint blocks are
independent under the i.i.d. product measure, so

`bernZ ν (A ∩ biShiftMap^[k] ⁻¹' B) = bernZ ν A · bernZ ν B` for all large `k`

(`measure_inter_preimage_iterate_eventually`). An `ε/3`-style approximation of arbitrary measurable
sets by block cylinders (`exists_blockAlg_symmDiff_lt`) then transports this to the limit statement:
the symmetric-difference bookkeeping bounds

`|real (A ∩ σ⁻ᵏB) − real (A' ∩ σ⁻ᵏB')| ≤ real (A ∆ A') + real (B ∆ B')`,

with the shifted symmetric difference keeping its mass because the iterate is measure preserving,
and the products differ by at most `real (A ∆ A') + real (B ∆ B')`.

## Main results

* `measure_inter_preimage_iterate_eventually` — exact block decorrelation beyond a finite shift.
* `tendsto_measureReal_inter_preimage_iterate` — **strong mixing** of the two-sided Bernoulli shift.

This is STEP A of issue `#35`; the strong-mixing statement is consumed by the eigenvalue-killing
argument for the ergodicity of the time-`1` map of the constant-roof Bernoulli suspension flow.
-/

open MeasureTheory Filter Topology Function Set MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal symmDiff

namespace ErgodicTheory.Multifractal

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-! ### Exact decorrelation of block cylinders beyond a finite shift -/

/-- Two-block version of the disjoint-shift lemma: for finite blocks `J K`, all large forward shifts
of `K` are disjoint from `J`. Derived from the single-block version applied to `J ∪ K`. -/
theorem exists_disjoint_shifted_block_two (J K : Finset ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → Disjoint J (K.map (blockShiftEmb k)) := by
  obtain ⟨N, hN⟩ := exists_disjoint_shifted_block (J ∪ K)
  refine ⟨N, fun k hk => ?_⟩
  have h := hN k hk
  refine Disjoint.mono ?_ ?_ h
  · exact Finset.subset_union_left
  · exact Finset.map_subset_map.mpr Finset.subset_union_right

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **Exact block decorrelation.** Two block cylinders decorrelate *exactly* beyond a finite shift:
for a block-`J` cylinder `C` and a block-`K` cylinder `D`,
`bernZ ν (C ∩ biShiftMap^[k] ⁻¹' D) = bernZ ν C · bernZ ν D` for all sufficiently large `k`. The
blocks `J` and `K + k` become disjoint (`exists_disjoint_shifted_block_two`), disjoint blocks are
independent (`measure_inter_of_disjoint_blocks`), and the iterate is measure preserving. -/
theorem measure_inter_preimage_iterate_eventually (ν : Measure α₀) [IsProbabilityMeasure ν]
    {J K : Finset ℤ} {C D : Set (BiShift α₀)}
    (hC : MeasurableSet[piBlock (α₀ := α₀) J] C) (hD : MeasurableSet[piBlock (α₀ := α₀) K] D) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      bernZ ν (C ∩ biShiftMap^[k] ⁻¹' D) = bernZ ν C * bernZ ν D := by
  obtain ⟨N, hN⟩ := exists_disjoint_shifted_block_two J K
  refine ⟨N, fun k hk => ?_⟩
  have hDk : MeasurableSet[piBlock (α₀ := α₀) (K.map (blockShiftEmb k))]
      (biShiftMap^[k] ⁻¹' D) := measurableSet_preimage_iterate_piBlock k hD
  have hmul := measure_inter_of_disjoint_blocks ν (hN k hk) hC hDk
  have hmp : MeasurePreserving ((biShiftMap (α₀ := α₀))^[k]) (bernZ ν) (bernZ ν) := by
    have h := (measurePreserving_biShiftEquiv_bernZ (α₀ := α₀) ν).iterate k
    rwa [coe_biShiftEquiv] at h
  have hDmeas : MeasurableSet D := piBlock_le K _ hD
  rw [hmul, hmp.measure_preimage hDmeas.nullMeasurableSet]

/-! ### Strong mixing of the two-sided Bernoulli shift -/

variable {A B : Set (BiShift α₀)}

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **Strong mixing (2-mixing) of the two-sided Bernoulli shift.** For arbitrary measurable sets
`A B`, the correlation `bernZ ν (A ∩ biShiftMap^[k] ⁻¹' B)` converges to the product
`bernZ ν A · bernZ ν B` as `k → ∞`.

The finite-block cylinders decorrelate *exactly* beyond a finite shift
(`measure_inter_preimage_iterate_eventually`); approximating `A` and `B` by block cylinders `A' B'`
in symmetric difference (`exists_blockAlg_symmDiff_lt`) and running the `ε/3`-bookkeeping — the
preimage of a symmetric difference under the measure-preserving iterate keeps its mass — pushes the
exact identity to the limit. Classical (Cornfeld–Fomin–Sinai §10; Walters Thm 1.30): Bernoulli
shifts are strong mixing. This is STEP A of `#35`, feeding the eigenvalue-killing argument for
time-`1` suspension ergodicity. -/
theorem tendsto_measureReal_inter_preimage_iterate (ν : Measure α₀) [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto (fun k => (bernZ ν).real (A ∩ biShiftMap^[k] ⁻¹' B))
      Filter.atTop (𝓝 ((bernZ ν).real A * (bernZ ν).real B)) := by
  set μ := bernZ ν with hμ
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / 5 with hε'def
  have hε' : 0 < ε' := by positivity
  -- Approximate `A` and `B` by finite-block cylinders in symmetric difference.
  obtain ⟨A', ⟨J, hA'J⟩, hA'A⟩ :=
    exists_blockAlg_symmDiff_lt ν hA (ε := ENNReal.ofReal ε') (by positivity)
  obtain ⟨B', ⟨K, hB'K⟩, hB'B⟩ :=
    exists_blockAlg_symmDiff_lt ν hB (ε := ENNReal.ofReal ε') (by positivity)
  have hA'meas : MeasurableSet A' := piBlock_le J _ hA'J
  have hB'meas : MeasurableSet B' := piBlock_le K _ hB'K
  -- Real symmetric-difference bounds (both orientations).
  have hA'Areal : μ.real (A' ∆ A) < ε' := by
    have hlt : (μ (A' ∆ A)).toReal < (ENNReal.ofReal ε').toReal :=
      (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hA'A
    rwa [ENNReal.toReal_ofReal hε'.le, ← Measure.real] at hlt
  have hB'Breal : μ.real (B' ∆ B) < ε' := by
    have hlt : (μ (B' ∆ B)).toReal < (ENNReal.ofReal ε').toReal :=
      (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hB'B
    rwa [ENNReal.toReal_ofReal hε'.le, ← Measure.real] at hlt
  have hAA'real : μ.real (A ∆ A') < ε' := by rw [symmDiff_comm]; exact hA'Areal
  have hBB'real : μ.real (B ∆ B') < ε' := by rw [symmDiff_comm]; exact hB'Breal
  -- Exact product for the block cylinders beyond a finite shift.
  obtain ⟨N, hNeq⟩ := measure_inter_preimage_iterate_eventually ν hA'J hB'K
  refine ⟨N, fun k hk => ?_⟩
  -- The iterate preserves `μ`.
  have hmp : MeasurePreserving ((biShiftMap (α₀ := α₀))^[k]) μ μ := by
    have h := (measurePreserving_biShiftEquiv_bernZ (α₀ := α₀) ν).iterate k
    rw [coe_biShiftEquiv, ← hμ] at h
    exact h
  have hσB : MeasurableSet (biShiftMap^[k] ⁻¹' B) := hB.preimage hmp.measurable
  have hσB' : MeasurableSet (biShiftMap^[k] ⁻¹' B') := hB'meas.preimage hmp.measurable
  -- Term 1: the two intersections differ by at most `2 ε'` in real measure.
  have hterm1 : |μ.real (A ∩ biShiftMap^[k] ⁻¹' B) - μ.real (A' ∩ biShiftMap^[k] ⁻¹' B')|
      ≤ 2 * ε' := by
    have htri := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
      (hA.inter hσB).nullMeasurableSet (hA'meas.inter hσB').nullMeasurableSet
    refine htri.trans ?_
    have hsub : μ.real ((A ∩ biShiftMap^[k] ⁻¹' B) ∆ (A' ∩ biShiftMap^[k] ⁻¹' B'))
        ≤ μ.real ((A ∆ A') ∪ ((biShiftMap^[k] ⁻¹' B) ∆ (biShiftMap^[k] ⁻¹' B'))) :=
      measureReal_mono (symmDiff_inter_subset _ _ _ _) (by finiteness)
    refine hsub.trans ?_
    refine (measureReal_union_le _ _).trans ?_
    have hpre : μ.real ((biShiftMap^[k] ⁻¹' B) ∆ (biShiftMap^[k] ⁻¹' B')) = μ.real (B ∆ B') := by
      rw [← Set.preimage_symmDiff]
      exact hmp.measureReal_preimage (hB.symmDiff hB'meas).nullMeasurableSet
    rw [hpre]
    have h1 := hAA'real.le
    have h2 := hBB'real.le
    linarith
  -- Term 2 (exact for `k ≥ N`): the block correlation is the block product.
  have hprodk : μ.real (A' ∩ biShiftMap^[k] ⁻¹' B') = μ.real A' * μ.real B' := by
    have he := hNeq k hk
    rw [← hμ] at he
    rw [Measure.real, he, ENNReal.toReal_mul, ← Measure.real, ← Measure.real]
  -- Term 3: the block product differs from the target product by at most `2 ε'`.
  have hterm3 : |μ.real A' * μ.real B' - μ.real A * μ.real B| ≤ 2 * ε' := by
    have h1 : |μ.real A' - μ.real A| ≤ ε' :=
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
        hA'meas.nullMeasurableSet hA.nullMeasurableSet).trans hA'Areal.le
    have h2 : |μ.real B' - μ.real B| ≤ ε' :=
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
        hB'meas.nullMeasurableSet hB.nullMeasurableSet).trans hB'Breal.le
    have hAabs : |μ.real A| ≤ 1 := by
      rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
    have hB'abs : |μ.real B'| ≤ 1 := by
      rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
    calc |μ.real A' * μ.real B' - μ.real A * μ.real B|
        = |(μ.real A' - μ.real A) * μ.real B' + μ.real A * (μ.real B' - μ.real B)| := by
          congr 1; ring
      _ ≤ |(μ.real A' - μ.real A) * μ.real B'| + |μ.real A * (μ.real B' - μ.real B)| :=
          abs_add_le _ _
      _ = |μ.real A' - μ.real A| * |μ.real B'| + |μ.real A| * |μ.real B' - μ.real B| := by
          rw [abs_mul, abs_mul]
      _ ≤ ε' * 1 + 1 * ε' :=
          add_le_add (mul_le_mul h1 hB'abs (abs_nonneg _) hε'.le)
            (mul_le_mul hAabs h2 (abs_nonneg _) zero_le_one)
      _ = 2 * ε' := by ring
  -- Assemble the three terms and conclude `dist < ε`.
  change dist (μ.real (A ∩ biShiftMap^[k] ⁻¹' B)) (μ.real A * μ.real B) < ε
  rw [Real.dist_eq]
  calc |μ.real (A ∩ biShiftMap^[k] ⁻¹' B) - μ.real A * μ.real B|
      ≤ |μ.real (A ∩ biShiftMap^[k] ⁻¹' B) - μ.real (A' ∩ biShiftMap^[k] ⁻¹' B')|
        + |μ.real (A' ∩ biShiftMap^[k] ⁻¹' B') - μ.real A * μ.real B| := abs_sub_le _ _ _
    _ ≤ 2 * ε' + |μ.real (A' ∩ biShiftMap^[k] ⁻¹' B') - μ.real A * μ.real B| := by linarith [hterm1]
    _ = 2 * ε' + |μ.real A' * μ.real B' - μ.real A * μ.real B| := by rw [hprodk]
    _ ≤ 2 * ε' + 2 * ε' := by linarith [hterm3]
    _ = 4 * ε' := by ring
    _ < ε := by rw [hε'def]; linarith

end ErgodicTheory.Multifractal
