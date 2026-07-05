/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.SymbolicDimension
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The Bernoulli witness for the symbolic entropy–dimension identity

The conditional headline `dimH_eq_ksEntropy_div_log_two`
(`ErgodicTheory/Multifractal/SymbolicDimension.lean`) is stated for an *abstract* ergodic
shift-invariant probability measure on the one-sided full shift with positive coordinate-partition
entropy. This file lays the **foundation** of the concrete Bernoulli witness that discharges those
two conditionals: it equips the full shift `Shift α₀` over a finite alphabet with the i.i.d.
(Bernoulli) product measure of a single-symbol law `ν`, and supplies the easy structural facts.

The construction proceeds in (currently three) foundation nodes.

* **N1 (probability).** The Bernoulli measure `bern ν := Measure.infinitePi (fun _ => ν)` is a
  probability measure when `ν` is.
* **N2 (measure preservation).** The left shift `shiftMap` preserves `bern ν`: the preimage of a
  measurable box `Set.pi ↑s t` is the box re-indexed by `n ↦ n + 1`, and both sides evaluate by
  `infinitePi_pi` to the *same* finite product of `ν`-masses (every marginal is the same `ν`, and
  `Finset.prod_map` absorbs the injective reindex).
* **N4b (positive entropy).** The single-symbol Shannon entropy
  `Hnu ν := ∑ i, negMulLog (ν {i}).toReal` is strictly positive once `ν` charges two distinct
  symbols, because every summand is nonnegative and the two charged ones are strictly positive.

The ergodicity (N3) and the entropy identification (N4a, `Hnu ν = ksEntropy`) are separate later
nodes; they are not attempted here.
-/

open MeasureTheory Filter Topology Function Set
open scoped ENNReal NNReal

namespace ErgodicTheory.Multifractal

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-! ### Definitions -/

/-- The **Bernoulli (i.i.d.) measure** on the one-sided full shift `Shift α₀`: the infinite product
of the single-symbol law `ν` over all coordinates. -/
noncomputable def bern (ν : Measure α₀) : Measure (Shift α₀) :=
  Measure.infinitePi (fun _ : ℕ => ν)

/-- The **single-symbol Shannon entropy** of the law `ν`:
`Hnu ν = ∑ i, negMulLog (ν {i}).toReal`. For a Bernoulli measure this is the Kolmogorov–Sinai
entropy of the coordinate partition (proved in a later node). -/
noncomputable def Hnu (ν : Measure α₀) : ℝ := ∑ i : α₀, Real.negMulLog (ν {i}).toReal

/-! ### N1 — the Bernoulli measure is a probability measure -/

/-- **N1.** The Bernoulli measure is a probability measure. (The global instance on `infinitePi`
does not fire through the `bern` definition, so it is provided explicitly.) -/
instance instIsProbabilityMeasureBern (ν : Measure α₀) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (bern ν) := by
  unfold bern; infer_instance

/-! ### N2 — the shift preserves the Bernoulli measure -/

/-- The coordinate-shift embedding `n ↦ n + 1` of `ℕ` into itself. Used to re-index a measurable
box under the shift preimage. -/
def shiftEmb : ℕ ↪ ℕ := ⟨fun n => n + 1, fun a b h => by simpa using h⟩

omit [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀] in
/-- **N2 box preimage.** The `shiftMap`-preimage of a measurable box `Set.pi ↑s t` is the box over
the re-indexed support `s.map shiftEmb` with the symbol sets shifted by one:
`shiftMap ⁻¹' (Set.pi ↑s t) = Set.pi ↑(s.map shiftEmb) (fun n => t (n - 1))`. -/
theorem preimage_shiftMap_pi (s : Finset ℕ) (t : ℕ → Set α₀) :
    shiftMap (α₀ := α₀) ⁻¹' (Set.pi (↑s) t)
      = Set.pi (↑(s.map shiftEmb)) (fun n => t (n - 1)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Set.mem_image, Finset.mem_coe,
    shiftEmb, Function.Embedding.coeFn_mk, shiftMap]
  constructor
  · rintro hx _ ⟨n, hn, rfl⟩
    rw [Nat.add_sub_cancel]
    exact hx n hn
  · intro hx n hn
    have h := hx (n + 1) ⟨n, hn, rfl⟩
    rwa [Nat.add_sub_cancel] at h

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **N2.** The left shift map preserves the Bernoulli measure `bern ν`. The preimage of a box
re-indexes by `n ↦ n + 1` (`preimage_shiftMap_pi`); both sides evaluate by `infinitePi_pi` to the
same finite product of `ν`-masses, since every marginal is the same `ν` and `Finset.prod_map`
absorbs the injective reindex. -/
theorem measurePreserving_shiftMap_bern (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (shiftMap (α₀ := α₀)) (bern ν) (bern ν) where
  measurable := measurable_shiftMap
  map_eq := by
    change Measure.map shiftMap (bern ν) = Measure.infinitePi (fun _ : ℕ => ν)
    refine Measure.eq_infinitePi (μ := fun _ : ℕ => ν) ?_
    intro s t ht
    have hbox : MeasurableSet (Set.pi (↑s) t) :=
      MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
    rw [Measure.map_apply measurable_shiftMap hbox, preimage_shiftMap_pi, bern,
      Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (fun i _ => ht (i - 1)),
      Finset.prod_map s shiftEmb (fun i => ν (t (i - 1)))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [shiftEmb]

/-! ### N4b — the single-symbol entropy is positive -/

/-- `negMulLog x > 0` for `x ∈ (0, 1)`: writing `negMulLog x = -x * log x`, the factor `log x` is
negative on `(0, 1)` and `x > 0`, so the product is positive. -/
private theorem negMulLog_pos_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < Real.negMulLog x := by
  rw [Real.negMulLog, neg_mul]
  have hlog : Real.log x < 0 := Real.log_neg hx0 hx1
  have : 0 < x * -Real.log x := mul_pos hx0 (neg_pos.mpr hlog)
  linarith

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- The mass `(ν {a}).toReal` of any single symbol lies in `[0, 1]`. -/
theorem measureReal_singleton_le_one (ν : Measure α₀) [IsProbabilityMeasure ν] (a : α₀) :
    (ν {a}).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := {a}))
  rwa [ENNReal.toReal_one] at h

/-- **N4b.** The single-symbol Shannon entropy `Hnu ν` is strictly positive once `ν` charges two
distinct symbols `i ≠ j` with positive `toReal`-mass. Every summand `negMulLog (ν {a}).toReal` is
nonnegative (the mass lies in `[0, 1]`), and the `i`-summand is strictly positive because
`(ν {i}).toReal ∈ (0, 1)`: the upper bound `(ν {i}).toReal < 1` follows from
`ν {i} + ν {j} ≤ ν univ = 1` (disjoint singletons) together with `0 < (ν {j}).toReal`. -/
theorem Hnu_pos (ν : Measure α₀) [IsProbabilityMeasure ν] {i j : α₀} (hij : i ≠ j)
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal) : 0 < Hnu ν := by
  -- Upper bound `(ν {i}).toReal < 1` via the disjoint pair `{i} ∪ {j}`.
  have hdisj : Disjoint ({i} : Set α₀) {j} := by
    simp [hij]
  have hsum_le : ν {i} + ν {j} ≤ 1 := by
    rw [← measure_union hdisj (measurableSet_singleton j)]
    exact prob_le_one
  have hi_top : ν {i} ≠ ⊤ := measure_ne_top ν {i}
  have hj_top : ν {j} ≠ ⊤ := measure_ne_top ν {j}
  have hsum_le' : (ν {i}).toReal + (ν {j}).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hsum_le
    rwa [ENNReal.toReal_add hi_top hj_top, ENNReal.toReal_one] at this
  have hi_lt_one : (ν {i}).toReal < 1 := by linarith
  -- Each summand is nonnegative; the `i`-summand is strictly positive.
  refine Finset.sum_pos' (fun a _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · exact Real.negMulLog_nonneg ENNReal.toReal_nonneg (measureReal_singleton_le_one ν a)
  · exact negMulLog_pos_of_lt_one hi hi_lt_one

end ErgodicTheory.Multifractal

