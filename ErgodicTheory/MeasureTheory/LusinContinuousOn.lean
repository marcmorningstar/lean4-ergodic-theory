/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Lusin's theorem (continuous-on-a-compact form)

This module supplies the classical **Lusin theorem** — a real-valued Borel-measurable function on a
Polish (finite-measure) space agrees with a *continuous* function off an arbitrarily small set, and
in fact is *continuous on* a compact set of almost full measure:

> `lusin_continuousOn`: for a Borel-measurable `u : X → ℝ` on a Polish space `X` carrying a finite
> Borel measure `μ`, and any tolerance `ε ≠ 0`, there is a **compact** `K ⊆ X` with `μ Kᶜ < ε` on
> which `u` is continuous (`ContinuousOn u K`).

Mathlib (on the pinned toolchain) provides the ingredients — Egorov's theorem, `Lᵖ`-density of
bounded continuous functions, convergence in measure, and inner regularity for compact sets — but
**not** the assembled Lusin statement, which is what this file adds.

## The route (arctan compression)

The proof avoids any integrability hypothesis on `u` by compressing to a bounded range:

1. Replace `u` by the bounded measurable `v := arctan ∘ u` (values in the open interval
   `(-π/2, π/2)`), which lies in `L¹(μ)` because `μ` is finite.
2. Bounded continuous functions are dense in `L¹` (`MemLp.exists_boundedContinuous_eLpNorm_sub_le`,
   available because a finite measure on a metrizable Borel space is `WeaklyRegular`): pick
   continuous `gₙ` with `eLpNorm (v - gₙ) 1 μ → 0`.
3. `L¹` convergence implies convergence in measure (`tendstoInMeasure_of_tendsto_eLpNorm`), which
   yields an almost-everywhere convergent subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`).
4. Egorov's theorem (`tendstoUniformlyOn_of_ae_tendsto'`) upgrades the a.e. convergence to *uniform*
   convergence off a small measurable set, and inner regularity
   (`MeasurableSet.exists_isCompact_isClosed_diff_lt`) carves a compact `K` out of its complement.
5. On `K` the continuous `gₙ` converge uniformly to `v`, so `v` is continuous on `K`
   (`TendstoUniformlyOn.continuousOn`); composing with `tan` (continuous on `(-π/2, π/2)`, and
   `tan ∘ arctan = id`) recovers `ContinuousOn u K`.

## References

* W. Rudin, *Real and Complex Analysis*, McGraw–Hill (1987), Theorem 2.24.
* D. L. Cohn, *Measure Theory*, 2nd ed., Birkhäuser (2013), Theorem 7.4.4.

The statement is phrased for a general Polish Borel space with a finite measure and is intended to
be Mathlib-upstreamable; it is consumed by the measurable tier of Livšic rigidity (issue #34).
-/

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal Real

namespace ErgodicTheory

/-- **Lusin's theorem.** A Borel-measurable real function `u` on a Polish space carrying a finite
Borel measure `μ` is continuous on a compact set of almost full measure: for every tolerance
`ε ≠ 0` there is a compact `K` with `μ Kᶜ < ε` and `ContinuousOn u K`.

The transfer function is obtained by the arctan-compression route (see the module docstring): `u` is
compressed to the bounded `arctan ∘ u ∈ L¹`, approximated in `L¹` by continuous functions, and the
approximation is made uniform on a compact set by Egorov's theorem together with inner regularity;
`tan` then recovers `u`. -/
theorem lusin_continuousOn {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Measurable u) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn u K := by
  -- If `ε = ∞`, the empty compact already works (`μ univ < ∞ = ε`).
  rcases eq_or_ne ε ∞ with hεtop | hεtop
  · refine ⟨∅, isCompact_empty, ?_, continuousOn_empty _⟩
    rw [Set.compl_empty, hεtop]
    exact measure_lt_top μ Set.univ
  -- Compression `v := arctan ∘ u`, bounded (values in `(-π/2, π/2)`) hence in `L¹`.
  let v : X → ℝ := fun x => Real.arctan (u x)
  have hv_apply : ∀ x, v x = Real.arctan (u x) := fun _ => rfl
  have hv_meas : Measurable v := Real.measurable_arctan.comp hu
  have hv_bd : ∀ x, ‖v x‖ ≤ π / 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan (u x)).le, (Real.arctan_lt_pi_div_two (u x)).le⟩
  have hv_mem : MemLp v 1 μ :=
    MemLp.of_bound hv_meas.aestronglyMeasurable (π / 2) (ae_of_all _ hv_bd)
  -- `L¹`-approximation of `v` by bounded continuous `g n`, with `eLpNorm (v - g n) 1 μ ≤ (n)⁻¹`.
  have hp1 : (1 : ℝ≥0∞) ≠ ∞ := ENNReal.one_ne_top
  choose g hg_le _hg_mem using fun n : ℕ =>
    hv_mem.exists_boundedContinuous_eLpNorm_sub_le hp1
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))
  set F : ℕ → X → ℝ := fun n => (g n : X → ℝ) with hF
  -- `eLpNorm (F n - v) 1 μ → 0` by squeezing against `(n)⁻¹`.
  have htend : Tendsto (fun n => eLpNorm (F n - v) 1 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun n => zero_le') (fun n => ?_)
    rw [hF]
    rw [eLpNorm_sub_comm]
    exact hg_le n
  -- convergence in `L¹` ⇒ in measure ⇒ an a.e.-convergent subsequence `F ∘ ns`.
  have htim : TendstoInMeasure μ F atTop v :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n => ((g n).continuous).aestronglyMeasurable) hv_meas.aestronglyMeasurable htend
  obtain ⟨ns, _hns_mono, hns_ae⟩ := htim.exists_seq_tendsto_ae
  -- Split the tolerance: `η := ε / 2`, finite and nonzero.
  set η : ℝ≥0∞ := ε / 2 with hη_def
  have hη_ne_top : η ≠ ∞ := by
    rw [hη_def]; exact (ENNReal.div_lt_top hεtop (by norm_num)).ne
  have hη_ne_zero : η ≠ 0 := by
    rw [hη_def]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε, by norm_num⟩
  -- Egorov on the subsequence: uniform convergence off a set `t` with `μ t ≤ η`.
  have hδpos : 0 < η.toReal := ENNReal.toReal_pos hη_ne_zero hη_ne_top
  obtain ⟨t, ht_meas, ht_le, ht_unif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto' (μ := μ) (f := fun i => F (ns i)) (g := v)
      (fun i => ((g (ns i)).continuous).stronglyMeasurable)
      hv_meas.stronglyMeasurable hns_ae hδpos
  have ht_le' : μ t ≤ η := by rwa [ENNReal.ofReal_toReal hη_ne_top] at ht_le
  -- Inner regularity: a compact `K ⊆ tᶜ` with `μ (tᶜ \ K) < η`.
  obtain ⟨K, hK_sub, hK_co, _hK_cl, hK_diff⟩ :=
    ht_meas.compl.exists_isCompact_isClosed_diff_lt (measure_ne_top μ tᶜ) hη_ne_zero
  refine ⟨K, hK_co, ?_, ?_⟩
  · -- Mass bookkeeping: `μ Kᶜ ≤ μ t + μ (tᶜ \ K) < η + η = ε`.
    have hsub : Kᶜ ⊆ t ∪ (tᶜ \ K) := by
      intro x hx
      by_cases hxt : x ∈ t
      · exact Or.inl hxt
      · exact Or.inr ⟨hxt, hx⟩
    calc μ Kᶜ ≤ μ (t ∪ (tᶜ \ K)) := measure_mono hsub
      _ ≤ μ t + μ (tᶜ \ K) := measure_union_le _ _
      _ < η + η :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top hη_ne_top ht_le') ht_le' hK_diff
      _ = ε := by rw [hη_def, ENNReal.add_halves]
  · -- `v` is continuous on `K` (uniform limit of continuous functions), then `u = tan ∘ v`.
    have hvK : ContinuousOn v K :=
      (ht_unif.mono hK_sub).continuousOn
        ((Eventually.of_forall fun i => ((g (ns i)).continuous).continuousOn).frequently)
    have hmaps : MapsTo v K (Ioo (-(π / 2)) (π / 2)) := fun x _ => Real.arctan_mem_Ioo (u x)
    have htanv : ContinuousOn (fun x => Real.tan (v x)) K :=
      Real.continuousOn_tan_Ioo.comp hvK hmaps
    refine htanv.congr fun x _ => ?_
    rw [hv_apply x]
    exact (Real.tan_arctan (u x)).symm

/-- Sanity check that `lusin_continuousOn` applies with the stated typeclass row resolving from the
standard instances (here on `ℝ`, a Polish Borel space, with an arbitrary finite measure). The
one-sided full shift `Shift α₀` over a finite discrete alphabet is likewise a compact — hence
Polish — metric space with `MeasurableSpace.pi = borel` (`Pi.borelSpace`), so the theorem is
available to the Livšic measurable-rigidity tier for `bern ν`. -/
example {μ : Measure ℝ} [IsFiniteMeasure μ] {u : ℝ → ℝ} (hu : Measurable u) :
    ∃ K : Set ℝ, IsCompact K ∧ μ Kᶜ < 1 ∧ ContinuousOn u K :=
  lusin_continuousOn hu (by norm_num)

end ErgodicTheory
