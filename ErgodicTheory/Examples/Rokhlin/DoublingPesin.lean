/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.Rokhlin.DoublingEquality
import ErgodicTheory.Examples.RuelleDoubling
import ErgodicTheory.Entropy.GeneratorTheorem

/-!
# Pesin's entropy formula for the doubling map: a positive-entropy compact-carrier witness

This module upgrades the *per-partition* Rokhlin/Pesin equality of the doubling map
`T : y ↦ 2 • y` on `UnitAddCircle` (proved in `DoublingEquality`) to the genuine **full-system**
Pesin formula `h(T) = ∑ λᵢ⁺`, by showing that the binary partition
`α = {[0,1/2), [1/2,1)}` is a **one-sided generator** for `T`.  This is a concrete,
non-vacuous instance of Pesin's formula on a compact carrier with strictly positive entropy
(`log 2 > 0`): every input is honest — the entropy side is the Kolmogorov–Sinai entropy computed
through the generator theorem, and the exponent side is the genuine sum of positive Lyapunov
exponents of the derivative cocycle.

## The generator crux

The only substantive gap is that the binary partition generates the Borel σ-algebra of the circle,
i.e. its forward `T`-translates recover every measurable set.  It reduces to
`borel_le_generateFrom_dyadicArcs`: the countable family of **dyadic arcs**
`ksJoinCells binCell T n f = ⋂ₖ T⁻ᵏ(binCell (f k))` generates the Borel structure.

We prove this by the **binary-expansion measurability** route.  The canonical representative
`rep : UnitAddCircle → [0,1)` is the pointwise limit of its dyadic partial sums
`binPartialSum N = ∑ₙ₌₀ᴺ⁻¹ dₙ · 2⁻⁽ⁿ⁺¹⁾`, where the `n`-th binary digit
`dₙ(y) = binDigit n y ∈ {0,1}` records which half `Tⁿ y` lands in.  Each digit set
`T⁻ⁿ(binCell 1)` is a finite union of generation-`(n+1)` dyadic arcs (so it is
`generateFrom dyadicArcSet`-measurable), hence each `binPartialSum N` is; the pointwise limit `rep`
is therefore `generateFrom dyadicArcSet`-measurable (`measurable_of_tendsto_metrizable'`).  Since
`(↑) ∘ rep = id` intertwines `rep` with the (measurable) covering projection, `rep` is a Borel
embedding and the Borel σ-algebra pulls back through it into `generateFrom dyadicArcSet`.

The dynamical partial-sum recursion is `rep y = binPartialSum N y + rep (Tᴺ y) · 2⁻ᴺ`, driven by
the single step `rep (T y) = 2 · rep y − binDigit 0 y` (the doubling map is `x ↦ 2x mod 1` on each
half), with remainder `rep (Tᴺ y) · 2⁻ᴺ ≤ 2⁻ᴺ → 0`.

## Main results

* `pesin_identity_doublingMap_perPartition` — the per-partition Pesin equality `h(α, T) = ∑ λᵢ⁺`.
* `borel_le_generateFrom_dyadicArcs` — the dyadic arcs generate the Borel σ-algebra (the crux).
* `binPartition_isGenerating` — the binary partition is a one-sided generator for `T`.
* `ksEntropy_doublingMap_eq_log_two` — `h(T) = log 2`.
* `pesin_formula_doublingMap` — the full-system Pesin formula `h(T) = ∑ λᵢ⁺`.

## References

* V. A. Rokhlin, *Lectures on the entropy theory of measure-preserving transformations* (1967).
* Y. Coudène, *Ergodic Theory and Dynamical Systems* (2016), Ch. 12.
-/

open MeasureTheory Function Set Filter Topology
open scoped ENNReal

namespace ErgodicTheory.Examples.Rokhlin

open ErgodicTheory ErgodicTheory.Entropy

/-! ## W1 — the per-partition Pesin identity (PROVED outright). -/

/-- **W1 (per-partition Pesin identity witness).** For the doubling map with its binary partition,
the partition-relative Kolmogorov–Sinai entropy equals the sum of positive Lyapunov exponents:
both are `log 2`. Positive entropy on a compact carrier: the genuine per-partition Pesin equality
`h(α, T) = ∑ λᵢ⁺`. -/
theorem pesin_identity_doublingMap_perPartition :
    ksEntropyPartition ergodic_doublingMap.toMeasurePreserving binPartition
      = sumPosExp ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
          (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
          (const_integrableLogNorm_inv doublingGen) := by
  rw [ksEntropyPartition_doublingMap_eq_log_two]
  exact doublingMap_sumPosExp_eq_log_two.symm

/-! ## Binary-expansion machinery for the generator crux -/

/-- `mk (x + k) = mk x` for an integer `k`: integer translates are killed by the projection
`ℝ → 𝕋¹` (here `k ∈ ℤ ⊆ ℝ`, so `mk k = 0`). -/
lemma mk_add_intCast (x : ℝ) (k : ℤ) :
    (QuotientAddGroup.mk (x + (k : ℝ)) : UnitAddCircle) = QuotientAddGroup.mk x := by
  rw [QuotientAddGroup.mk_add]
  have hk : (QuotientAddGroup.mk ((k : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by simp⟩
  rw [hk, add_zero]

/-- A point not in the right half `binCell 1` lies in the left half `binCell 0` (the two binary
cells cover the circle). -/
lemma mem_binCell_zero_of_not_one {z : UnitAddCircle} (h : z ∉ binCell 1) : z ∈ binCell 0 := by
  have hz : z ∈ ⋃ j, binCell j := by rw [cover_binCell]; exact Set.mem_univ z
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
  fin_cases j
  · exact hj
  · exact absurd hj h

/-- The **`n`-th binary digit** of the doubling map: `1` if `Tⁿ y` lies in the right half
`binCell 1`, else `0`.  Realized as the indicator of the digit set `T⁻ⁿ(binCell 1)`. -/
noncomputable def binDigit (n : ℕ) (y : UnitAddCircle) : ℝ :=
  (doublingMap^[n] ⁻¹' binCell 1).indicator (fun _ => (1 : ℝ)) y

/-- The **`N`-th dyadic partial sum** `∑ₙ₌₀ᴺ⁻¹ binDigit n · 2⁻⁽ⁿ⁺¹⁾` of the binary expansion of the
canonical representative `rep`. -/
noncomputable def binPartialSum (N : ℕ) (y : UnitAddCircle) : ℝ :=
  ∑ n ∈ Finset.range N, binDigit n y / 2 ^ (n + 1)

/-- **One-step doubling recursion for the representative.**  On the left half the doubling map is
`x ↦ 2x`, on the right half `x ↦ 2x − 1`; in both cases `rep (T y) = 2 · rep y − binDigit 0 y`. -/
lemma rep_doublingMap (y : UnitAddCircle) :
    rep (doublingMap y) = 2 * rep y - binDigit 0 y := by
  have hty : doublingMap y = QuotientAddGroup.mk (2 * rep y) := by
    conv_lhs => rw [← mk_rep y]
    rw [doublingMap_mk]
  by_cases h : y ∈ binCell 1
  · have hd : binDigit 0 y = 1 := by
      simp only [binDigit, Function.iterate_zero, Set.preimage_id]
      exact Set.indicator_of_mem h _
    have ha := (mem_binCell_iff 1 y).mp h
    simp only [binLift, Fin.val_one, Nat.cast_one, mem_Ico] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have hmem : (2 * rep y - 1) ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have heq : (QuotientAddGroup.mk (2 * rep y) : UnitAddCircle)
        = QuotientAddGroup.mk (2 * rep y - 1) := by
      have h1 := mk_add_intCast (2 * rep y - 1) 1
      rw [show (2 * rep y - 1 + ((1 : ℤ) : ℝ)) = 2 * rep y by push_cast; ring] at h1
      exact h1
    rw [hd, hty, heq, rep_coe_of_mem hmem]
  · have hd : binDigit 0 y = 0 := by
      simp only [binDigit, Function.iterate_zero, Set.preimage_id]
      exact Set.indicator_of_notMem h _
    have hy0 : y ∈ binCell 0 := mem_binCell_zero_of_not_one h
    have ha := (mem_binCell_iff 0 y).mp hy0
    simp only [binLift, Fin.val_zero, Nat.cast_zero, zero_div, zero_add, mem_Ico] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have hmem : (2 * rep y) ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    rw [hd, sub_zero, hty, rep_coe_of_mem hmem]

/-- The `0`-th digit at `Tᴺ y` is the `N`-th digit at `y`: `binDigit 0 (Tᴺ y) = binDigit N y`
(both read whether `Tᴺ y ∈ binCell 1`). -/
lemma binDigit_zero_iterate (N : ℕ) (y : UnitAddCircle) :
    binDigit 0 (doublingMap^[N] y) = binDigit N y := by
  unfold binDigit
  simp only [Function.iterate_zero, Set.preimage_id]
  by_cases h : doublingMap^[N] y ∈ binCell 1
  · rw [Set.indicator_of_mem h (fun _ => (1 : ℝ)),
      Set.indicator_of_mem (Set.mem_preimage.mpr h) (fun _ => (1 : ℝ))]
  · rw [Set.indicator_of_notMem h (fun _ => (1 : ℝ)),
      Set.indicator_of_notMem (fun hc => h (Set.mem_preimage.mp hc)) (fun _ => (1 : ℝ))]

/-- **The dynamical partial-sum recursion.**  `rep y = binPartialSum N y + rep (Tᴺ y) · 2⁻ᴺ`: the
first `N` binary digits plus the rescaled tail.  By induction on `N`, feeding the one-step
recursion `rep_doublingMap` into the tail. -/
lemma rep_eq_binPartialSum_add (N : ℕ) (y : UnitAddCircle) :
    rep y = binPartialSum N y + rep (doublingMap^[N] y) / 2 ^ N := by
  induction N with
  | zero => simp [binPartialSum]
  | succ N ih =>
    have hstep : rep (doublingMap^[N + 1] y)
        = 2 * rep (doublingMap^[N] y) - binDigit N y := by
      rw [Function.iterate_succ_apply', rep_doublingMap, binDigit_zero_iterate]
    have h2 : (2 : ℝ) ^ N ≠ 0 := by positivity
    have h2' : (2 : ℝ) ^ (N + 1) ≠ 0 := by positivity
    simp only [binPartialSum, Finset.sum_range_succ] at ih ⊢
    rw [hstep, ih]
    field_simp
    ring

/-- **Convergence of the binary expansion.**  `binPartialSum N y → rep y` as `N → ∞`, because the
remainder `rep (Tᴺ y) · 2⁻ᴺ ≤ 2⁻ᴺ → 0`. -/
lemma tendsto_binPartialSum (y : UnitAddCircle) :
    Tendsto (fun N => binPartialSum N y) atTop (𝓝 (rep y)) := by
  have hrem : Tendsto (fun N => rep (doublingMap^[N] y) / 2 ^ N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => ?_) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : ((1 : ℝ) / 2) < 1))
    · exact div_nonneg (rep_mem_Ico _).1 (by positivity)
    · rw [div_pow, one_pow]
      gcongr
      exact (rep_mem_Ico _).2.le
  have hfun : (fun N => binPartialSum N y)
      = fun N => rep y - rep (doublingMap^[N] y) / 2 ^ N := by
    funext N; linarith [rep_eq_binPartialSum_add N y]
  rw [hfun]
  have hconst : Tendsto (fun _ : ℕ => rep y) atTop (𝓝 (rep y)) := tendsto_const_nhds
  simpa using hconst.sub hrem

/-! ## W2 — the binary partition is a generator (reduced to the Borel-generation crux). -/

/-- The countable family of dyadic arcs: the `n`-fold-join cells of the binary partition under the
doubling map, `ksJoinCells binCell doublingMap n f = ⋂ₖ T⁻ᵏ(binCell (f k))`, over all `n` and all
digit strings `f : Fin n → Fin 2`. Each is a dyadic arc of length `2⁻ⁿ`. -/
def dyadicArcSet : Set (Set UnitAddCircle) :=
  {A | ∃ (n : ℕ) (f : Fin n → Fin 2), A = ksJoinCells binCell doublingMap n f}

/-- **The `n`-th digit set is a dyadic-arc σ-algebra set.**  `T⁻ⁿ(binCell 1)` is the finite union
of the generation-`(n+1)` dyadic arcs whose last digit is `1`, so it is
`generateFrom dyadicArcSet`-measurable. -/
lemma preimage_iterate_binCell_one_mem (n : ℕ) :
    MeasurableSet[MeasurableSpace.generateFrom dyadicArcSet]
      (doublingMap^[n] ⁻¹' binCell 1) := by
  have hunion : doublingMap^[n] ⁻¹' binCell 1
      = ⋃ (g : {f : Fin (n + 1) → Fin 2 // f (Fin.last n) = 1}),
          ksJoinCells binCell doublingMap (n + 1) g.1 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, ksJoinCells_apply, Set.mem_iInter,
      Subtype.exists, exists_prop]
    constructor
    · intro hy
      classical
      refine ⟨fun k => if doublingMap^[(k : ℕ)] y ∈ binCell 1 then (1 : Fin 2) else 0, ?_, ?_⟩
      · simp only [Fin.val_last]; rw [if_pos hy]
      · intro k
        dsimp only
        split_ifs with hc
        · exact hc
        · exact mem_binCell_zero_of_not_one hc
    · rintro ⟨f, hf, hmem⟩
      have hk := hmem (Fin.last n)
      rwa [Fin.val_last, hf] at hk
  rw [hunion]
  exact MeasurableSet.iUnion fun g =>
    MeasurableSpace.measurableSet_generateFrom ⟨n + 1, g.1, rfl⟩

/-- Each binary digit function is `generateFrom dyadicArcSet`-measurable (indicator of a digit
set). -/
lemma measurable_binDigit (n : ℕ) :
    Measurable[MeasurableSpace.generateFrom dyadicArcSet] (binDigit n) := by
  letI : MeasurableSpace UnitAddCircle := MeasurableSpace.generateFrom dyadicArcSet
  unfold binDigit
  exact measurable_const.indicator (preimage_iterate_binCell_one_mem n)

/-- Each dyadic partial sum is `generateFrom dyadicArcSet`-measurable (finite sum of digits). -/
lemma measurable_binPartialSum (N : ℕ) :
    Measurable[MeasurableSpace.generateFrom dyadicArcSet] (binPartialSum N) := by
  letI : MeasurableSpace UnitAddCircle := MeasurableSpace.generateFrom dyadicArcSet
  unfold binPartialSum
  exact Finset.measurable_sum _ fun n _ => (measurable_binDigit n).div_const _

/-- The canonical representative `rep` is `generateFrom dyadicArcSet`-measurable: it is the
pointwise limit of the measurable dyadic partial sums (`measurable_of_tendsto_metrizable'`). -/
lemma measurable_rep_dyadic :
    Measurable[MeasurableSpace.generateFrom dyadicArcSet] rep := by
  letI : MeasurableSpace UnitAddCircle := MeasurableSpace.generateFrom dyadicArcSet
  exact measurable_of_tendsto_metrizable' atTop measurable_binPartialSum
    (tendsto_pi_nhds.mpr tendsto_binPartialSum)

/-- **CRUX (the single genuine gap, proved).** The dyadic arcs generate the Borel σ-algebra of the
unit circle.  Binary-expansion route: the representative `rep` is the pointwise limit of the
`generateFrom dyadicArcSet`-measurable partial sums `binPartialSum N` (`tendsto_binPartialSum`,
`measurable_binPartialSum`), hence `rep` is `generateFrom dyadicArcSet`-measurable
(`measurable_of_tendsto_metrizable'`).  As `(↑) ∘ rep = id` factors the identity through the
measurable covering projection, the Borel σ-algebra pulls back through `rep` into
`generateFrom dyadicArcSet`. -/
theorem borel_le_generateFrom_dyadicArcs :
    (inferInstance : MeasurableSpace UnitAddCircle)
      ≤ MeasurableSpace.generateFrom dyadicArcSet := by
  have hcomp : ((↑) : ℝ → UnitAddCircle) ∘ rep = id := funext mk_rep
  have hmk_le : MeasurableSpace.comap ((↑) : ℝ → UnitAddCircle)
      (inferInstance : MeasurableSpace UnitAddCircle) ≤ (inferInstance : MeasurableSpace ℝ) :=
    AddCircle.measurable_mk'.comap_le
  have hcircle_le : (inferInstance : MeasurableSpace UnitAddCircle)
      ≤ MeasurableSpace.comap rep (inferInstance : MeasurableSpace ℝ) := by
    calc (inferInstance : MeasurableSpace UnitAddCircle)
        = MeasurableSpace.comap rep (MeasurableSpace.comap ((↑) : ℝ → UnitAddCircle)
            (inferInstance : MeasurableSpace UnitAddCircle)) := by
          rw [MeasurableSpace.comap_comp, hcomp, MeasurableSpace.comap_id]
      _ ≤ MeasurableSpace.comap rep (inferInstance : MeasurableSpace ℝ) :=
          MeasurableSpace.comap_mono hmk_le
  exact le_trans hcircle_le measurable_rep_dyadic.comap_le

/-- **W2 (generator).** The binary partition is a one-sided generator for the doubling map:
`⨆ n, comap (Tⁿ) σ(binPartition) = Borel`. Reduces to `borel_le_generateFrom_dyadicArcs`; the easy
inclusion and the reduction of the crux to the dyadic-arc family are proved here. -/
theorem binPartition_isGenerating :
    IsGenerating (volume : Measure UnitAddCircle) doublingMap binPartition := by
  have hTmeas : Measurable doublingMap :=
    ergodic_doublingMap.toMeasurePreserving.measurable
  have hσle : generatedSigmaAlgebra (volume : Measure UnitAddCircle) binPartition
      ≤ (inferInstance : MeasurableSpace UnitAddCircle) := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨i, rfl⟩
    exact measurableSet_binCell i
  unfold IsGenerating
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · exact le_trans (MeasurableSpace.comap_mono hσle)
      (measurable_iff_comap_le.mp (hTmeas.iterate n))
  · -- Each digit set `Tⁿ⁻¹(binCell i)` is measurable for the saturated σ-algebra `G`.
    have hdigit : ∀ (n : ℕ) (i : Fin 2),
        MeasurableSet[⨆ m : ℕ, MeasurableSpace.comap (doublingMap^[m])
          (generatedSigmaAlgebra (volume : Measure UnitAddCircle) binPartition)]
          ((doublingMap^[n]) ⁻¹' binCell i) := by
      intro n i
      have h1 : MeasurableSet[MeasurableSpace.comap (doublingMap^[n])
          (generatedSigmaAlgebra (volume : Measure UnitAddCircle) binPartition)]
          ((doublingMap^[n]) ⁻¹' binCell i) :=
        ⟨binCell i, MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩, rfl⟩
      exact (le_iSup (fun m : ℕ => MeasurableSpace.comap (doublingMap^[m])
        (generatedSigmaAlgebra (volume : Measure UnitAddCircle) binPartition)) n) _ h1
    -- Each dyadic arc is a finite intersection of digit sets, hence `G`-measurable.
    have harc : ∀ (n : ℕ) (f : Fin n → Fin 2),
        MeasurableSet[⨆ m : ℕ, MeasurableSpace.comap (doublingMap^[m])
          (generatedSigmaAlgebra (volume : Measure UnitAddCircle) binPartition)]
          (ksJoinCells binCell doublingMap n f) := by
      intro n f
      rw [ksJoinCells_apply]
      exact MeasurableSet.iInter (fun k => hdigit (k : ℕ) (f k))
    -- Reduce Borel ≤ G to the crux via the dyadic-arc family.
    refine le_trans borel_le_generateFrom_dyadicArcs (MeasurableSpace.generateFrom_le ?_)
    rintro A ⟨n, f, rfl⟩
    exact harc n f

/-! ## W3 — the full-system Pesin formula (PROVED via W2). -/

/-- **W3a.** The Kolmogorov–Sinai entropy of the doubling map equals `log 2` (generator theorem +
Rokhlin equality). -/
theorem ksEntropy_doublingMap_eq_log_two :
    ksEntropy ergodic_doublingMap.toMeasurePreserving = ((Real.log 2 : ℝ) : EReal) := by
  rw [ksEntropy_eq_ksEntropyPartition_of_generating ergodic_doublingMap.toMeasurePreserving
      binPartition binPartition_isGenerating, ksEntropyPartition_doublingMap_eq_log_two]

/-- **W3b (full-system Pesin formula witness).** The Kolmogorov–Sinai entropy of the doubling map
equals the sum of its positive Lyapunov exponents: `h(T) = ∑ λᵢ⁺`, the genuine full-system Pesin
equality on a compact carrier with strictly positive entropy `log 2`. -/
theorem pesin_formula_doublingMap :
    ksEntropy ergodic_doublingMap.toMeasurePreserving
      = ((sumPosExp ergodic_doublingMap (const_det_ne_zero doublingGen_det_ne_zero)
          (const_measurable doublingGen) (const_integrableLogNorm doublingGen)
          (const_integrableLogNorm_inv doublingGen) : ℝ) : EReal) := by
  rw [ksEntropy_doublingMap_eq_log_two, doublingMap_sumPosExp_eq_log_two]

end ErgodicTheory.Examples.Rokhlin
