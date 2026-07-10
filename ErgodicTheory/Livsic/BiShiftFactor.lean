/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.ShiftMetric
import ErgodicTheory.Livsic.BiShiftMetric
import ErgodicTheory.Livsic.ContinuousRigidity
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Map

/-!
# The one-sided factor of the two-sided full shift

This file records the **canonical factor map** `π : BiShift α₀ → Shift α₀` (the restriction of a
bi-infinite sequence to its `ℕ`-coordinates) and the transport properties that let the two-sided
Bernoulli shift serve as a *natural extension* of the one-sided Bernoulli shift. It is the `W1`
foundation of the unbounded-measurable Livšic rigidity programme (GitHub issue #34,
Katok–Hasselblatt §19.2.4 route).

The one-sided shift `(Shift α₀, shiftMap, bern ν)` is a **measure-theoretic factor** of the
invertible two-sided shift `(BiShift α₀, biShiftMap, bernZ ν)`:

* **`toShift`** — the factor map `x ↦ (n ↦ x n)`, restriction to the non-negative coordinates.
* **`toShift_biShiftMap`** — the intertwining `π ∘ σ̃ = σ ∘ π`.
* **`map_toShift_bernZ`** — the pushforward identity `Measure.map π (bernZ ν) = bern ν`, so `π`
  is measure preserving from the two-sided to the one-sided Bernoulli measure.
* **`holderWith_comp_toShift`** — Hölder data transports *up* the factor: `π` is `1`-Lipschitz for
  the respective θ-ultrametrics (two points close in `distZ` agree on a symmetric window, hence
  their `ℕ`-restrictions agree on a prefix of the same length), so `φ ∘ π` inherits any Hölder
  exponent/constant of `φ`.
* **`isAeCoboundaryOf_comp_toShift`** — an a.e. coboundary of `shiftMap` over `bern ν` transports to
  an a.e. coboundary of `biShiftMap` over `bernZ ν`, pulling the a.e. identity back along `π`
  (`ae_of_ae_map`) and rewriting through the intertwining.

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  §19.2.4.
* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
-/

open MeasureTheory Function Set
open scoped ENNReal NNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

/-! ### The factor map, its intertwining, and the pushforward -/

/-- The canonical embedding `ℕ ↪ ℤ`. -/
def natEmbZ : ℕ ↪ ℤ := ⟨fun n => (n : ℤ), Nat.cast_injective⟩

/-- The **factor map** `π : BiShift α₀ → Shift α₀`: the restriction of a bi-infinite sequence to its
non-negative coordinates, `π x n = x n`. -/
def toShift {α₀ : Type*} : BiShift α₀ → Shift α₀ := fun x n => x (n : ℤ)

variable {α₀ : Type*} [MeasurableSpace α₀]

/-- The factor map is measurable: each output coordinate is a measurable coordinate projection of
the input. -/
theorem measurable_toShift : Measurable (toShift (α₀ := α₀)) :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n : ℤ)

omit [MeasurableSpace α₀] in
/-- **Intertwining (pointwise).** The factor map conjugates the two shifts: `π (σ̃ x) = σ (π x)`. -/
theorem toShift_biShiftMap (x : BiShift α₀) :
    toShift (biShiftMap x) = shiftMap (toShift x) := by
  funext n
  simp only [toShift, biShiftMap, shiftMap]
  norm_cast

omit [MeasurableSpace α₀] in
/-- **Intertwining (composed).** The factor map conjugates the two shifts: `π ∘ σ̃ = σ ∘ π`. -/
theorem toShift_comp_biShiftMap :
    toShift ∘ biShiftMap = shiftMap ∘ (toShift (α₀ := α₀)) :=
  funext fun x => toShift_biShiftMap x

/-- **The pushforward identity.** The pushforward of the two-sided Bernoulli measure along the
factor map `π` is the one-sided Bernoulli measure. Checked on measurable boxes via
`Measure.eq_infinitePi`: the `π`-preimage of a box over a finite support `s ⊆ ℕ` is the box over the
image support `s.map natEmbZ ⊆ ℤ`, whose two-sided mass is the same finite product of `ν`-masses. -/
theorem map_toShift_bernZ (ν : Measure α₀) [IsProbabilityMeasure ν] :
    Measure.map (toShift (α₀ := α₀)) (bernZ ν) = bern ν := by
  rw [bern]
  refine Measure.eq_infinitePi (μ := fun _ : ℕ => ν) ?_
  intro s t ht
  have hbox : MeasurableSet (Set.pi (↑s) t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  have hpre : toShift (α₀ := α₀) ⁻¹' (Set.pi (↑s) t)
      = Set.pi (↑(s.map natEmbZ)) (fun j => t j.toNat) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.coeFn_mk, toShift, natEmbZ]
    constructor
    · rintro hx _ ⟨n, hn, rfl⟩
      simpa using hx n hn
    · intro hx n hn
      have := hx (n : ℤ) ⟨n, hn, rfl⟩
      simpa using this
  rw [Measure.map_apply measurable_toShift hbox, hpre, bernZ,
    Measure.infinitePi_pi (μ := fun _ : ℤ => ν) (fun j _ => ht j.toNat),
    Finset.prod_map s natEmbZ (fun j => ν (t j.toNat))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [natEmbZ]

/-- **Measure preservation.** The factor map is measure preserving from the two-sided Bernoulli
measure to the one-sided Bernoulli measure. -/
theorem measurePreserving_toShift (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (toShift (α₀ := α₀)) (bernZ ν) (bern ν) :=
  ⟨measurable_toShift, map_toShift_bernZ ν⟩

/-- **Measurability transport.** A measurable transfer function pulls back to a measurable one along
the factor map. -/
theorem measurable_comp_toShift {u : Shift α₀ → ℝ} (hu : Measurable u) :
    Measurable (u ∘ toShift) :=
  hu.comp measurable_toShift

/-- **A.e.-coboundary transport.** An a.e. coboundary of the one-sided shift over `bern ν` lifts to
an a.e. coboundary of the two-sided shift over `bernZ ν`, with transfer function pulled back along
the factor map. The a.e. identity is transported through the pushforward `map_toShift_bernZ` by
`ae_of_ae_map`, then the intertwining rewrites `u (σ (π x)) = u (π (σ̃ x))`. -/
theorem isAeCoboundaryOf_comp_toShift (ν : Measure α₀) [IsProbabilityMeasure ν]
    {φ u : Shift α₀ → ℝ} (h : IsAeCoboundaryOf (bern ν) shiftMap φ u) :
    IsAeCoboundaryOf (bernZ ν) biShiftMap (φ ∘ toShift) (u ∘ toShift) := by
  unfold IsAeCoboundaryOf at h ⊢
  rw [← map_toShift_bernZ ν] at h
  have h2 := ae_of_ae_map measurable_toShift.aemeasurable h
  filter_upwards [h2] with x hx
  simp only [Function.comp_apply] at hx ⊢
  rw [toShift_biShiftMap]
  exact hx

/-! ### Hölder transport up the factor -/

section Holder

variable {α₀ : Type*} [TopologicalSpace α₀] [DiscreteTopology α₀]

attribute [local instance] PiNat.metricSpace biShiftMetricSpace

/-- **The factor map is `1`-Lipschitz** from the two-sided θ-ultrametric to the one-sided `PiNat`
ultrametric. Two points at `distZ`-distance `(1/2)^N` agree on the symmetric window `|j| < N`, so
in particular their `ℕ`-restrictions agree on the first `N` coordinates, whence their `PiNat`
distance is at most `(1/2)^N`. -/
theorem lipschitzWith_one_toShift : LipschitzWith 1 (toShift (α₀ := α₀)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_distZ]
  by_cases hxy : x = y
  · rw [hxy, dist_self]
    exact distZ_nonneg y y
  · rw [distZ_of_ne hxy, ← agree_iff_dist_le]
    intro i hi
    change x (i : ℤ) = y (i : ℤ)
    exact apply_eq_of_natAbs_lt_firstDiffZ (by rw [Int.natAbs_natCast]; exact hi)

/-- **Hölder transport up the factor.** If `φ` is `(C, r)`-Hölder on the one-sided shift, then
`φ ∘ π` is `(C, r)`-Hölder on the two-sided shift, because `π` is `1`-Lipschitz. -/
theorem holderWith_comp_toShift {C r : ℝ≥0} {φ : Shift α₀ → ℝ} (hφ : HolderWith C r φ) :
    HolderWith C r (φ ∘ toShift) := by
  have h1 : HolderWith 1 1 (toShift (α₀ := α₀)) := holderWith_one.mpr lipschitzWith_one_toShift
  have h2 := hφ.comp h1
  simpa only [NNReal.one_rpow, mul_one] using h2

end Holder

end ErgodicTheory
