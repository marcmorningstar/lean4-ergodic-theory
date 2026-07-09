/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Bases

/-!
# A dense forward orbit from ergodicity

This file records a small, general topological-dynamics fact used by the concrete instances of the
Livšic cohomological rigidity theorem (issues #29, #33): an **ergodic** measure-preserving map on a
second-countable space carrying a fully supported (open-positive) probability measure has a point
whose forward orbit is **dense**.

The proof is the classical one. For each set `o` of a countable topological basis put
`U o := ⋃ n, T^[n] ⁻¹' o` — the points whose orbit visits `o`. This set is (almost) forward
invariant (`T ⁻¹' (U o) ⊆ U o`), so ergodicity forces it to be either null or conull; since
`o ⊆ U o` and `o` is a nonempty open set of positive measure, the null alternative is impossible and
`U o` is conull. Intersecting over the countable basis gives a conull set of points whose orbit
visits **every** basic open set, i.e. a dense orbit; probability of the measure makes that set
nonempty.

## Main results

* `ErgodicTheory.ergodic_exists_denseRange_iterate` — a generic ergodic map on a second-countable
  open-positive probability space has a point with dense forward orbit. Used to discharge the
  dense-orbit hypothesis of the abstract Livšic theorem for the doubling map (issue #33) and the
  cat map.

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.1 (Livšic) and the surrounding discussion of dense orbits of ergodic maps.
-/

open MeasureTheory Filter Set TopologicalSpace

namespace ErgodicTheory

/-- **A generic ergodic map has a point with dense forward orbit.** On a second-countable
topological space `X` equipped with an open-positive probability measure `μ`, if `T` is ergodic for
`μ`, then some `x₀ : X` has a dense forward orbit `n ↦ T^[n] x₀`.

This is the dense-orbit input feeding the concrete Livšic instances (the doubling map, the cat map):
the abstract theorem `ErgodicTheory.isHolderCoboundary_iff` requires exactly a dense forward orbit
under a continuous map. It is stated for a general such space and is Mathlib-upstreamable. -/
theorem ergodic_exists_denseRange_iterate
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {T : X → X} {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (hT : Ergodic T μ) :
    ∃ x₀ : X, DenseRange (fun n : ℕ => T^[n] x₀) := by
  classical
  set U : Set X → Set X := fun o => ⋃ n : ℕ, T^[n] ⁻¹' o with hU
  -- `U o` is forward invariant: `T ⁻¹' (U o) ⊆ U o` (tail reindexing of the union).
  have hUinv : ∀ o : Set X, T ⁻¹' (U o) ⊆ U o := by
    intro o x hx
    simp only [hU, mem_preimage, mem_iUnion] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  -- For measurable `o`, `U o` is measurable (a countable union of preimages).
  have hUmeas : ∀ o : Set X, MeasurableSet o → MeasurableSet (U o) := by
    intro o ho
    simp only [hU]
    exact MeasurableSet.iUnion fun n => (hT.measurable.iterate n) ho
  -- `o ⊆ U o` via the zeroth iterate.
  have hUsub : ∀ o : Set X, o ⊆ U o := by
    intro o x hx
    simp only [hU, mem_iUnion, mem_preimage]
    exact ⟨0, hx⟩
  -- Every basic open set `o` has a conull `U o`.
  have hUae : ∀ o ∈ countableBasis X, U o =ᵐ[μ] (univ : Set X) := by
    intro o ho
    have hoopen : IsOpen o := isOpen_of_mem_countableBasis ho
    have homeas : MeasurableSet (U o) := hUmeas o hoopen.measurableSet
    rcases hT.ae_empty_or_univ_of_preimage_ae_le homeas.nullMeasurableSet
        (hUinv o).eventuallyLE with hempty | huniv
    · exfalso
      have hopos : 0 < μ o := hoopen.measure_pos μ (nonempty_of_mem_countableBasis ho)
      have h1 : μ o ≤ μ (U o) := measure_mono (hUsub o)
      rw [measure_congr hempty, measure_empty] at h1
      exact absurd h1 (not_le.2 hopos)
    · exact huniv
  -- A single point visiting every basic open set.
  have hae : ∀ᵐ x ∂μ, ∀ o ∈ countableBasis X, x ∈ U o := by
    rw [ae_ball_iff (countable_countableBasis X)]
    intro o ho
    exact eventuallyEq_univ.1 (hUae o ho)
  obtain ⟨x₀, hx₀⟩ := hae.exists
  -- That point has dense forward orbit.
  refine ⟨x₀, (isBasis_countableBasis X).dense_iff.2 ?_⟩
  intro o ho _
  have hmem : x₀ ∈ U o := hx₀ o ho
  simp only [hU, mem_iUnion, mem_preimage] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨T^[n] x₀, hn, mem_range_self n⟩

end ErgodicTheory
