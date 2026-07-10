/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.BiShiftFull
import ErgodicTheory.Livsic.BiShiftProductStructure
import ErgodicTheory.Livsic.BiShiftStableOscillation
import ErgodicTheory.MeasureTheory.LusinContinuousOn
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Unstable (same-past) essential-oscillation bound for the two-sided Bernoulli shift

This is the `σ̃⁻¹` mirror of the stable oscillation core (Katok–Hasselblatt 19.2.4), the second
symmetric half of the unbounded measurable Livšic tier (GitHub issue #34, step W4). Where the
stable side controls the oscillation of a measurable transfer function `u` between two sequences
with the **same future** (contracting under the forward shift `σ̃`), this module controls the
oscillation between two sequences with the **same past** (contracting under the *inverse* shift
`σ̃⁻¹ = ⇑biShiftEquiv.symm`).

The design is scout-validated. It reuses — by import, not duplication — the *deterministic*
common-returns lemma (`abs_sub_le_of_common_returns`, generic in the map `T`, from
`BiShiftStableOscillation`) and the reverse-Fatou complement helper (`measure_not_frequently_le`,
from `BiShiftProductStructure`), and mirrors the geometry through the index reflection
`(σ̃⁻¹)^[N] x n = x (n − N)`.

## Strategy

Let `hae` witness that `u` is an a.e. transfer function for the *forward* cocycle `φ` over `bernZ ν`
(`φ = u∘σ̃ − u` a.e.). Composing this identity with `σ̃⁻¹` turns it into
`ψ = u∘σ̃⁻¹ − u` a.e. for the **reversed cocycle** `ψ := −φ∘σ̃⁻¹`, so `u` is an a.e. transfer for
`(σ̃⁻¹, ψ)`. Two sequences with a common past contract under `σ̃⁻¹`, and — expanding `ψ` back into
`φ` — the reversed Birkhoff differences inherit the same geometric Hölder bound as the stable core.
Reverse Fatou on the common-return events (no pointwise ergodic theorem) then forces, for a.e.
same-past pair, `|u y − u x| ≤ C·θ/(1−θ)`.

## Main results

* `birkhoffSum_unstable_bound` — the same-past Birkhoff shadowing bound for the reversed cocycle
  `ψ`, uniform in `N` (the `σ̃⁻¹` analogue of the stable core's shadowing bound).
* `unstable_pair_osc` — **the deliverable**: for a.e. unstable pair (two futures, one shared past)
  in the `Future × (Past × Future)` organization, `u (J (a, b₂))` and `u (J (a, b₁))` differ by at
  most `C·θ/(1−θ)`, with `θ = (1/2)^r`.

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  §19.2, Theorem 19.2.4 (stable-holonomy identity, mirrored here through `σ̃⁻¹`).
* A. Wilkinson, *The cohomological equation for partially hyperbolic diffeomorphisms*, Astérisque
  (2013), §2.
* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
-/

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal Real

-- This staging module duplicates a small generic measure/metric substrate under one uniform
-- instance context (`[Fintype] [TopologicalSpace] [DiscreteTopology] [MeasurableSpace]
-- [MeasurableSingletonClass]`); most declarations use only a subset, and none carry `Fintype` in
-- their statement type. The two purely stylistic linters below are disabled file-wide rather than
-- threading a bespoke `omit` list through every duplicated lemma (the integration worker dedups).
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

/-! ### Instance context

The product-splitting substrate — `NegZ`/`NonnegZ`/`Past`/`Future`/`bernPast`/`bernFuture`/`joinPF`/
`joinPF_apply`/`map_joinPF_bernZ`/`measurePreserving_joinPF` and the reverse-Fatou complement helper
`measure_not_frequently_le` — is the single public substrate in
`ErgodicTheory.Livsic.BiShiftProductStructure`, imported above and reused here (deduplicated at
integration; GitHub issue #34). -/

variable {α₀ : Type*} [Fintype α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-! ### The inverse shift and its reflected iterate -/

/-- The **inverse two-sided shift** `n ↦ x (n − 1)`, i.e. `⇑biShiftEquiv.symm`. It contracts
same-past pairs exactly as the forward shift contracts same-future pairs. -/
def biShiftMapInv (x : BiShift α₀) : BiShift α₀ := fun n => x (n - 1)

theorem biShiftMapInv_eq :
    (biShiftMapInv (α₀ := α₀)) = ⇑(biShiftEquiv (α₀ := α₀)).symm := by
  funext x n; rfl

/-- **Reflected iterate.** `(σ̃⁻¹)^[k] x` reads coordinate `n` from `x (n − k)`. -/
theorem biShiftMapInv_iterate_apply (k : ℕ) (x : BiShift α₀) (n : ℤ) :
    biShiftMapInv^[k] x n = x (n - (k : ℤ)) := by
  induction k generalizing x n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (biShiftMapInv^[k] x) (n - 1) = x (n - ((k + 1 : ℕ) : ℤ))
    rw [ih]
    congr 1
    push_cast
    ring

/-- The inverse shift preserves the two-sided Bernoulli measure. -/
theorem measurePreserving_biShiftMapInv (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (biShiftMapInv (α₀ := α₀)) (bernZ ν) (bernZ ν) := by
  rw [biShiftMapInv_eq]
  exact MeasurePreserving.symm biShiftEquiv (measurePreserving_biShiftEquiv_bernZ ν)

/-- `σ̃ ∘ σ̃⁻¹ = id`: the forward shift of the inverse shift recovers the point. -/
theorem biShiftMap_biShiftMapInv (z : BiShift α₀) : biShiftMap (biShiftMapInv z) = z := by
  funext n
  change z (n + 1 - 1) = z n
  congr 1
  ring

/-! ### Same-past geometry: the shadowing bound

The deterministic common-returns core `abs_sub_le_of_common_returns` (generic in the map `T`) is
imported from `BiShiftStableOscillation` and reused verbatim; only the same-past geometry
(`dist_iterate_le_of_eqOn_past`, `birkhoffSum_unstable_bound`) is `σ̃⁻¹`-specific. -/

section Geometry

attribute [local instance] biShiftMetricSpace

/-- Two sequences with the same past contract under inverse iteration:
`dist ((σ̃⁻¹)^N x) ((σ̃⁻¹)^N y) ≤ (1/2)^N`. -/
theorem dist_iterate_le_of_eqOn_past {x y : BiShift α₀}
    (hxy : ∀ j : ℤ, j < 0 → x j = y j) (N : ℕ) :
    dist (biShiftMapInv^[N] x) (biShiftMapInv^[N] y) ≤ (1 / 2 : ℝ) ^ N := by
  have hmem : biShiftMapInv^[N] x ∈ symCyl (biShiftMapInv^[N] y) N := by
    intro j hj
    rw [biShiftMapInv_iterate_apply, biShiftMapInv_iterate_apply]
    exact hxy (j - (N : ℤ)) (by omega)
  rw [dist_eq_distZ]
  exact (mem_symCyl_iff_distZ_le _ _ N).1 hmem

/-- **Same-past Birkhoff shadowing bound**, uniform in `N`. For a Hölder `φ`, its reversed cocycle
`ψ = −φ∘σ̃⁻¹` and two points with a common past, the reversed Birkhoff differences are bounded by
`C·θ/(1−θ)`, `θ = (1/2)^r` — the `σ̃⁻¹` mirror of the stable shadowing bound (the same constant,
obtained by expanding `ψ` back into `φ`, whose `(k+1)`-th inverse iterates still contract). -/
theorem birkhoffSum_unstable_bound {C r : ℝ≥0} {φ ψ : BiShift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr : 0 < r)
    (hψ : ∀ z, ψ z = -φ (biShiftMapInv z)) {x y : BiShift α₀}
    (hxy : ∀ j : ℤ, j < 0 → x j = y j) (N : ℕ) :
    |birkhoffSum biShiftMapInv ψ N y - birkhoffSum biShiftMapInv ψ N x|
      ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := by
  set θ : ℝ := (1 / 2 : ℝ) ^ (r : ℝ) with hθdef
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hθpos : 0 < θ := by rw [hθdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hθlt : θ < 1 := by rw [hθdef]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hrpos
  have h1θ : 0 < 1 - θ := by linarith
  have hterm : ∀ k ∈ Finset.range N,
      |φ (biShiftMapInv^[k + 1] x) - φ (biShiftMapInv^[k + 1] y)| ≤ (C : ℝ) * θ ^ (k + 1) := by
    intro k _
    have hmem : biShiftMapInv^[k + 1] x ∈ symCyl (biShiftMapInv^[k + 1] y) (k + 1) := by
      intro j hj
      rw [biShiftMapInv_iterate_apply, biShiftMapInv_iterate_apply]
      exact hxy (j - ((k + 1 : ℕ) : ℤ)) (by omega)
    have hdist : dist (biShiftMapInv^[k + 1] x) (biShiftMapInv^[k + 1] y)
        ≤ (1 / 2 : ℝ) ^ (k + 1) := by
      rw [dist_eq_distZ]
      exact (mem_symCyl_iff_distZ_le _ _ (k + 1)).1 hmem
    have hpow : ((1 / 2 : ℝ) ^ (k + 1)) ^ (r : ℝ) = θ ^ (k + 1) := by rw [half_pow_rpow, hθdef]
    have hH := hφ.dist_le_of_le hdist
    rw [Real.dist_eq, hpow] at hH
    exact hH
  have hbs : birkhoffSum biShiftMapInv ψ N y - birkhoffSum biShiftMapInv ψ N x
      = ∑ k ∈ Finset.range N, (φ (biShiftMapInv^[k + 1] x) - φ (biShiftMapInv^[k + 1] y)) := by
    simp only [birkhoffSum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hψ, hψ, ← Function.iterate_succ_apply' biShiftMapInv k y,
      ← Function.iterate_succ_apply' biShiftMapInv k x]
    ring
  have hfac : ∑ k ∈ Finset.range N, θ ^ (k + 1) = θ * ∑ k ∈ Finset.range N, θ ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_succ']
  have hgeom : ∑ k ∈ Finset.range N, θ ^ k ≤ (1 - θ)⁻¹ :=
    geomSum_range_le_inv_one_sub hθpos.le hθlt N
  rw [hbs]
  calc |∑ k ∈ Finset.range N, (φ (biShiftMapInv^[k + 1] x) - φ (biShiftMapInv^[k + 1] y))|
      ≤ ∑ k ∈ Finset.range N, |φ (biShiftMapInv^[k + 1] x) - φ (biShiftMapInv^[k + 1] y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (C : ℝ) * θ ^ (k + 1) := Finset.sum_le_sum hterm
    _ = (C : ℝ) * ∑ k ∈ Finset.range N, θ ^ (k + 1) := by rw [Finset.mul_sum]
    _ = (C : ℝ) * (θ * ∑ k ∈ Finset.range N, θ ^ k) := by rw [hfac]
    _ ≤ (C : ℝ) * (θ * (1 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgeom hθpos.le) (by positivity)
    _ = (C : ℝ) * θ / (1 - θ) := by ring

end Geometry

/-! ### The unstable pair space and its marginals -/

/-- Unstable pair space, organized as `Future × (Past × Future)` (two futures `b₁`, `b₂` and one
shared past `a`) so that the two marginals are plain `swap`/`fst`/`snd` compositions of the joining
map, needing no product-reassociation. -/
abbrev UnstablePairs (α₀ : Type*) : Type _ := Future α₀ × (Past α₀ × Future α₀)

/-- The unstable-pair measure. -/
noncomputable def unstablePairMeasure (ν : Measure α₀) : Measure (UnstablePairs α₀) :=
  (bernFuture ν).prod ((bernPast ν).prod (bernFuture ν))

instance (ν : Measure α₀) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (unstablePairMeasure ν) := by
  unfold unstablePairMeasure; infer_instance

/-- First marginal `J (a, b₁)`: the shared past `a = w.2.1` joined with the first future `b₁ = w.1`.
-/
noncomputable def unstableFst : UnstablePairs α₀ → BiShift α₀ := fun w => joinPF (w.2.1, w.1)

/-- Second marginal `J (a, b₂)`: the shared past `a = w.2.1` joined with the second future
`b₂ = w.2.2`. -/
noncomputable def unstableSnd : UnstablePairs α₀ → BiShift α₀ := fun w => joinPF (w.2.1, w.2.2)

theorem measurePreserving_unstableFst (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (unstableFst (α₀ := α₀)) (unstablePairMeasure ν) (bernZ ν) := by
  have h1 : MeasurePreserving
      (Prod.map (id : Future α₀ → Future α₀) (Prod.fst : Past α₀ × Future α₀ → Past α₀))
      ((bernFuture ν).prod ((bernPast ν).prod (bernFuture ν)))
      ((bernFuture ν).prod (bernPast ν)) :=
    (MeasurePreserving.id (bernFuture ν)).prod
      (measurePreserving_fst (μ := bernPast ν) (ν := bernFuture ν))
  have h2 : MeasurePreserving (Prod.swap : Future α₀ × Past α₀ → Past α₀ × Future α₀)
      ((bernFuture ν).prod (bernPast ν)) ((bernPast ν).prod (bernFuture ν)) :=
    Measure.measurePreserving_swap
  exact (measurePreserving_joinPF ν).comp (h2.comp h1)

theorem measurePreserving_unstableSnd (ν : Measure α₀) [IsProbabilityMeasure ν] :
    MeasurePreserving (unstableSnd (α₀ := α₀)) (unstablePairMeasure ν) (bernZ ν) := by
  have h1 : MeasurePreserving
      (Prod.snd : Future α₀ × (Past α₀ × Future α₀) → Past α₀ × Future α₀)
      ((bernFuture ν).prod ((bernPast ν).prod (bernFuture ν)))
      ((bernPast ν).prod (bernFuture ν)) :=
    measurePreserving_snd (μ := bernFuture ν) (ν := (bernPast ν).prod (bernFuture ν))
  exact (measurePreserving_joinPF ν).comp h1

/-- The two marginals of an unstable pair share their negative (past) coordinates (the mirror of
`stableFst_stableSnd_eq_on_nonneg`). -/
theorem unstableFst_unstableSnd_eq_on_neg (w : UnstablePairs α₀) (j : ℤ) (hj : j < 0) :
    unstableFst w j = unstableSnd w j := by
  simp only [unstableFst, unstableSnd, joinPF_apply, dif_pos hj]

/-! ### The measure-level unstable oscillation lemma -/

section UnstableOsc

attribute [local instance] biShiftMetricSpace

variable (ν : Measure α₀) [IsProbabilityMeasure ν]

/-- **Unstable (same-past) essential oscillation of the transfer function.** If `φ` is `r`-Hölder
and `u` is a measurable a.e. transfer function for the forward cocycle `φ` over `bernZ ν`, then for
a.e. unstable pair (two futures, one shared past) the values of `u` differ by at most `C·θ/(1−θ)`.
Reversing the cocycle to `ψ = −φ∘σ̃⁻¹` makes `u` a transfer function for `(σ̃⁻¹, ψ)`; Lusin plus
reverse Fatou plus the deterministic common-returns lemma then finish, using no ergodic theorem and
no boundedness of `u`. This is the `σ̃⁻¹` mirror of the stable core (Katok–Hasselblatt 19.2.4). -/
theorem unstable_pair_osc {C r : ℝ≥0} {φ u : BiShift α₀ → ℝ}
    (hφ : HolderWith C r φ) (hr : 0 < r) (hu : Measurable u)
    (hae : IsAeCoboundaryOf (bernZ ν) biShiftMap φ u) :
    ∀ᵐ w ∂(unstablePairMeasure ν),
      |u (unstableSnd w) - u (unstableFst w)|
        ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) := by
  classical
  set Cs : ℝ := (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) with hCs
  set lam : Measure (UnstablePairs α₀) := unstablePairMeasure ν with hlam
  set ψ : BiShift α₀ → ℝ := fun z => -φ (biShiftMapInv z) with hψdef
  have hψ : ∀ z, ψ z = -φ (biShiftMapInv z) := fun _ => rfl
  -- the inverse shift is measure preserving
  have hmpInv : MeasurePreserving (biShiftMapInv (α₀ := α₀)) (bernZ ν) (bernZ ν) :=
    measurePreserving_biShiftMapInv ν
  -- reverse the coboundary: `u` is an a.e. transfer for `(σ̃⁻¹, ψ)`
  have hae' : φ =ᵐ[bernZ ν] fun x => u (biShiftMap x) - u x := hae
  have hcob_inv : ψ =ᵐ[bernZ ν] fun z => u (biShiftMapInv z) - u z := by
    have hstep := hmpInv.quasiMeasurePreserving.ae_eq hae'
    filter_upwards [hstep] with z hz
    simp only [Function.comp_apply] at hz
    rw [biShiftMap_biShiftMapInv] at hz
    rw [hψ, hz]; ring
  have htel := ae_birkhoffSum_eq_endpoint hmpInv hcob_inv
  -- pull telescoping back along the two marginals
  have htel1 : ∀ᵐ w ∂lam, ∀ N,
      birkhoffSum biShiftMapInv ψ N (unstableFst w)
        = u (biShiftMapInv^[N] (unstableFst w)) - u (unstableFst w) := by
    have hmap := (measurePreserving_unstableFst ν).map_eq
    exact ae_of_ae_map (measurePreserving_unstableFst ν).measurable.aemeasurable
      (by rw [hmap]; exact htel)
  have htel2 : ∀ᵐ w ∂lam, ∀ N,
      birkhoffSum biShiftMapInv ψ N (unstableSnd w)
        = u (biShiftMapInv^[N] (unstableSnd w)) - u (unstableSnd w) := by
    have hmap := (measurePreserving_unstableSnd ν).map_eq
    exact ae_of_ae_map (measurePreserving_unstableSnd ν).measurable.aemeasurable
      (by rw [hmap]; exact htel)
  rw [ae_iff]
  set B : Set (UnstablePairs α₀) := {w | ¬ |u (unstableSnd w) - u (unstableFst w)| ≤ Cs} with hB
  have key : ∀ k : ℕ, lam B ≤ 2 * ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro k
    set ε : ℝ≥0∞ := ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ with hε
    have hεne : ε ≠ 0 := by
      rw [hε]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (k + 1))
    obtain ⟨K, hKco, hKmass, hKcont⟩ := lusin_continuousOn (μ := bernZ ν) hu hεne
    have hKmeas : MeasurableSet K := hKco.isClosed.measurableSet
    set A : ℕ → Set (UnstablePairs α₀) := fun N =>
      {w | biShiftMapInv^[N] (unstableFst w) ∈ K ∧ biShiftMapInv^[N] (unstableSnd w) ∈ K} with hA
    have hAcompl : ∀ N, lam (A N)ᶜ ≤ 2 * ε := by
      intro N
      have hATc : (A N)ᶜ ⊆
          (fun w => biShiftMapInv^[N] (unstableFst w)) ⁻¹' Kᶜ ∪
          (fun w => biShiftMapInv^[N] (unstableSnd w)) ⁻¹' Kᶜ := by
        intro w hw
        rw [Set.mem_compl_iff, hA, Set.mem_setOf_eq, not_and_or] at hw
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hiter : MeasurePreserving (biShiftMapInv^[N]) (bernZ ν) (bernZ ν) := hmpInv.iterate N
      have hm1 : lam ((fun w => biShiftMapInv^[N] (unstableFst w)) ⁻¹' Kᶜ) = bernZ ν Kᶜ := by
        have hcomp : MeasurePreserving (fun w => biShiftMapInv^[N] (unstableFst w)) lam (bernZ ν) :=
          hiter.comp (measurePreserving_unstableFst ν)
        exact hcomp.measure_preimage hKmeas.compl.nullMeasurableSet
      have hm2 : lam ((fun w => biShiftMapInv^[N] (unstableSnd w)) ⁻¹' Kᶜ) = bernZ ν Kᶜ := by
        have hcomp : MeasurePreserving (fun w => biShiftMapInv^[N] (unstableSnd w)) lam (bernZ ν) :=
          hiter.comp (measurePreserving_unstableSnd ν)
        exact hcomp.measure_preimage hKmeas.compl.nullMeasurableSet
      calc lam (A N)ᶜ ≤ lam ((fun w => biShiftMapInv^[N] (unstableFst w)) ⁻¹' Kᶜ)
            + lam ((fun w => biShiftMapInv^[N] (unstableSnd w)) ⁻¹' Kᶜ) :=
            le_trans (measure_mono hATc) (measure_union_le _ _)
        _ = bernZ ν Kᶜ + bernZ ν Kᶜ := by rw [hm1, hm2]
        _ ≤ ε + ε := add_le_add hKmass.le hKmass.le
        _ = 2 * ε := by rw [two_mul]
    have hnotfreq := measure_not_frequently_le lam (A := A) hAcompl
    have hdet : ∀ᵐ w ∂lam,
        (∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N) → |u (unstableSnd w) - u (unstableFst w)| ≤ Cs := by
      filter_upwards [htel1, htel2] with w hw1 hw2 hfreq
      have hpast : ∀ j : ℤ, j < 0 → (unstableFst w) j = (unstableSnd w) j :=
        fun j hj => unstableFst_unstableSnd_eq_on_neg w j hj
      refine abs_sub_le_of_common_returns hKco hKcont hw1 hw2
        (fun N => birkhoffSum_unstable_bound hφ hr hψ hpast N)
        (fun N => dist_iterate_le_of_eqOn_past hpast N)
        (fun N₀ => ?_)
      obtain ⟨N, hN, hw⟩ := hfreq N₀
      exact ⟨N, hN, hw.1, hw.2⟩
    have hBsub : lam B ≤ lam {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N} + 0 := by
      rw [add_zero]
      have hincl : B ⊆ {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N}
          ∪ {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
              → |u (unstableSnd w) - u (unstableFst w)| ≤ Cs)} := by
        intro w hwB
        by_cases hfr : ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N
        · exact Or.inr (fun himp => hwB (himp hfr))
        · exact Or.inl hfr
      have hz : lam {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
          → |u (unstableSnd w) - u (unstableFst w)| ≤ Cs)} = 0 := by
        rw [← ae_iff] at *
        exact hdet
      calc lam B ≤ lam ({w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N}
            ∪ {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
                → |u (unstableSnd w) - u (unstableFst w)| ≤ Cs)}) := measure_mono hincl
        _ ≤ lam {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N}
            + lam {w | ¬ ((∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N)
                → |u (unstableSnd w) - u (unstableFst w)| ≤ Cs)} := measure_union_le _ _
        _ = lam {w | ¬ ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ w ∈ A N} := by rw [hz, add_zero]
    rw [add_zero] at hBsub
    exact le_trans hBsub hnotfreq
  by_contra hne
  have hpos : 0 < lam B := pos_iff_ne_zero.mpr hne
  have hfin : lam B ≠ ∞ := measure_ne_top lam B
  have hhalf_pos : lam B / 2 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hne, by norm_num⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hhalf_pos
  have hmono : ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((n : ℕ) : ℝ≥0∞)⁻¹ := by
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)
  have hlt : 2 * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ < lam B := by
    calc 2 * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ 2 * ((n : ℕ) : ℝ≥0∞)⁻¹ := by
          gcongr
      _ < 2 * (lam B / 2) := by
          calc 2 * ((n : ℕ) : ℝ≥0∞)⁻¹ = ((n : ℕ) : ℝ≥0∞)⁻¹ * 2 := mul_comm _ _
            _ < (lam B / 2) * 2 := ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) hn
            _ = 2 * (lam B / 2) := mul_comm _ _
      _ = lam B := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
  exact absurd (key n) (not_le.mpr hlt)

end UnstableOsc

end ErgodicTheory
