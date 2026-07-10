/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.BiShiftStableOscillation
import ErgodicTheory.Livsic.BiShiftUnstableOscillation
import ErgodicTheory.Livsic.BiShiftFull

/-!
# Measurable Livšic rigidity on the two-sided Bernoulli shift (the Fubini glue)

This is step **W5** of the unbounded measurable Livšic rigidity programme (GitHub issue #34,
Katok–Hasselblatt §19.2.4): the *glue* that turns the two symmetric essential-oscillation bounds —
the **stable** bound (`stable_pair_osc`, same-future pairs, `BiShiftStableOscillation`) and the
**unstable** bound (`unstable_pair_osc`, same-past pairs, `BiShiftUnstableOscillation`) — into the
**two-sided measurable-tier rigidity theorem** for the invertible Bernoulli full shift.

The classical Hölder-version construction of the transfer function `u` and its Birkhoff density of
returns are *not* used. Instead:

* **Fubini glue** (`essBounded_of_measurable_aeCoboundary_biShift`): splitting the bilateral shift
  space into `past ⊗ future` (`joinPF`), a merely **measurable** a.e. solution `u` of the
  cohomological equation `φ = u ∘ σ̃ − u` over `bernZ ν` is `bernZ ν`-**essentially bounded**. One
  typical base point `(a₀, b₀)` connects to a.e. `(a, b)` in two holonomy moves —
  `(a, b) →unstable (a, b₀) →stable (a₀, b₀)` — so `|u|` is a.e. bounded by
  `|u (a₀, b₀)| + Cs + Cu` (iterated `Measure.ae_ae_of_ae_prod`, `Prod.swap`-transport, an a.e.
  base-point pick via `Filter.Eventually.exists`, and a `fst`-section lift, all abstract in the
  joining data).

* **Clamp + two-sided headline**
  (`hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift`): with the essential bound `M`, the
  clamp `v := max (−M) (min M u)` is a **bounded-everywhere** measurable function agreeing with `u`
  on a co-null set, hence itself an a.e. transfer function (the shift being measure preserving), so
  the already-shipped bounded tier `hasVanishingPeriodicSums_of_bounded_aeCoboundary_biShift`
  discharges vanishing periodic sums — with `u` allowed to be genuinely **unbounded**, and using no
  ergodic theorem (the oscillation bounds are proved by reverse Fatou).

The descent to the one-sided full shift and the full Katok–Hasselblatt 19.2.4 iff are assembled in
`ErgodicTheory.Livsic.MeasurableRigidityFull` (step W6).

## Main results

* `essBounded_of_measurable_aeCoboundary_biShift` — a measurable a.e. solution of the cohomological
  equation over `bernZ ν` is `bernZ ν`-essentially bounded.
* `hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift` — **the two-sided headline**: a
  Hölder observable that is the a.e. coboundary of a merely measurable transfer function over
  `bernZ ν` has vanishing periodic sums.

## References

* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, CUP (1995),
  Theorem 19.2.4.
* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.

Issue #34.
-/

open MeasureTheory Filter Set Function
open scoped ENNReal NNReal

namespace ErgodicTheory

open ErgodicTheory.Multifractal ErgodicTheory.Livsic

/-! ### The abstract Fubini glue

Stated abstractly in the joining data `(P = past, F = future, Ω = the shift space, J = the joining
map)`: from the stable oscillation bound (same future, two pasts) and the unstable oscillation bound
(same past, two futures), essential boundedness of the transfer function follows by iterated Fubini,
a `Prod.swap`-transport, an a.e. base-point pick, and a `fst`-section lift. -/

section Glue

variable {P F Ω : Type*} [MeasurableSpace P] [MeasurableSpace F] [MeasurableSpace Ω]
  {mP : Measure P} {mF : Measure F} {μ : Measure Ω}
  [IsProbabilityMeasure mP] [IsProbabilityMeasure mF] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **The Fubini glue.** Given the joining map `J : P × F → Ω` (measure preserving onto `μ`), a
measurable `u`, and the two a.e. oscillation bounds — stable (same future, two pasts) and unstable
(same past, two futures) — the function `u` is `μ`-essentially bounded. One typical base point
`(a₀, b₀)` connects to a.e. `(a, b)` in two moves: `(a, b) →unstable (a, b₀) →stable (a₀, b₀)`. -/
private theorem essBounded_of_stable_unstable_osc
    {J : P × F → Ω} (hJ : MeasurePreserving J (mP.prod mF) μ)
    {u : Ω → ℝ} (hu : Measurable u) {Cs Cu : ℝ}
    (hst : ∀ᵐ w ∂((mP.prod mP).prod mF),
      |u (J (w.1.2, w.2)) - u (J (w.1.1, w.2))| ≤ Cs)
    (hun : ∀ᵐ v ∂(mF.prod (mP.prod mF)),
      |u (J (v.2.1, v.2.2)) - u (J (v.2.1, v.1))| ≤ Cu) :
    ∃ M : ℝ, ∀ᵐ x ∂μ, |u x| ≤ M := by
  -- 1. swap-transport the stable bound to the F-outer organization
  have hswap : MeasurePreserving (Prod.swap : F × (P × P) → (P × P) × F)
      (mF.prod (mP.prod mP)) ((mP.prod mP).prod mF) := Measure.measurePreserving_swap
  have hst' : ∀ᵐ z ∂(mF.prod (mP.prod mP)),
      |u (J (z.2.2, z.1)) - u (J (z.2.1, z.1))| ≤ Cs := by
    have := ae_of_ae_map (f := (Prod.swap : F × (P × P) → (P × P) × F))
      hswap.measurable.aemeasurable (by rw [hswap.map_eq]; exact hst)
    exact this
  -- 2. Fubini both statements to F-outer a.e. form
  have hst'' : ∀ᵐ b ∂mF, ∀ᵐ y ∂(mP.prod mP),
      |u (J (y.2, b)) - u (J (y.1, b))| ≤ Cs := Measure.ae_ae_of_ae_prod hst'
  have hst''' : ∀ᵐ b ∂mF, ∀ᵐ a₁ ∂mP, ∀ᵐ a₂ ∂mP,
      |u (J (a₂, b)) - u (J (a₁, b))| ≤ Cs :=
    hst''.mono fun b hb => Measure.ae_ae_of_ae_prod hb
  have hun' : ∀ᵐ b₀ ∂mF, ∀ᵐ z ∂(mP.prod mF),
      |u (J (z.1, z.2)) - u (J (z.1, b₀))| ≤ Cu := Measure.ae_ae_of_ae_prod hun
  -- 3. pick a joint typical future b₀, then a typical past a₀
  obtain ⟨b₀, hb_st, hb_un⟩ := (hst'''.and hun').exists
  obtain ⟨a₀, ha₀⟩ := hb_st.exists
  -- 4. lift the stable section along `fst` to the product
  have hlift : ∀ᵐ z ∂(mP.prod mF), |u (J (z.1, b₀)) - u (J (a₀, b₀))| ≤ Cs := by
    have hfst : MeasurePreserving (Prod.fst : P × F → P) (mP.prod mF) mP :=
      measurePreserving_fst
    exact ae_of_ae_map hfst.measurable.aemeasurable (by rw [hfst.map_eq]; exact ha₀)
  -- 5. triangle inequality on the product
  set M : ℝ := Cu + Cs + |u (J (a₀, b₀))| with hM
  have hbound : ∀ᵐ z ∂(mP.prod mF), |u (J z)| ≤ M := by
    filter_upwards [hb_un, hlift] with z hz1 hz2
    have hzz : u (J (z.1, z.2)) = u (J z) := rfl
    rw [hzz] at hz1
    have e1 := abs_le.1 hz1
    have e2 := abs_le.1 hz2
    have e4 := le_abs_self (u (J (a₀, b₀)))
    have e5 := neg_abs_le (u (J (a₀, b₀)))
    rw [hM, abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e4, e5]
  -- 6. transport along J to μ
  refine ⟨M, ?_⟩
  have hbadmeas : MeasurableSet {x : Ω | ¬ |u x| ≤ M} := by
    have h1 : {x : Ω | |u x| ≤ M} = {x | u x ≤ M} ∩ {x | -M ≤ u x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
      tauto
    have h2 : MeasurableSet {x : Ω | |u x| ≤ M} := by
      rw [h1]
      exact (measurableSet_le hu measurable_const).inter
        (measurableSet_le measurable_const hu)
    have h3 : {x : Ω | ¬ |u x| ≤ M} = {x : Ω | |u x| ≤ M}ᶜ := rfl
    rw [h3]
    exact h2.compl
  rw [ae_iff, ← hJ.map_eq, Measure.map_apply hJ.measurable hbadmeas]
  have : J ⁻¹' {x | ¬ |u x| ≤ M} = {z | ¬ |u (J z)| ≤ M} := rfl
  rw [this, ← ae_iff]
  exact hbound

end Glue

/-! ### Essential boundedness and the two-sided headline -/

section BiShift

attribute [local instance] biShiftMetricSpace

variable {α₀ : Type*} [Finite α₀] [TopologicalSpace α₀] [DiscreteTopology α₀]
  [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
variable (ν : Measure α₀) [IsProbabilityMeasure ν]

/-- **Essential boundedness of the measurable Livšic transfer.** If `φ` is `r`-Hölder and `u` is a
merely **measurable** (possibly unbounded) a.e. solution of the cohomological equation
`φ = u ∘ σ̃ − u` over the two-sided Bernoulli measure `bernZ ν`, then `u` is `bernZ ν`-essentially
bounded. The two symmetric essential-oscillation bounds (`stable_pair_osc` over the same-future pair
space, `unstable_pair_osc` over the same-past pair space) feed the abstract Fubini glue applied to
the past ⊗ future product structure `joinPF`. -/
theorem essBounded_of_measurable_aeCoboundary_biShift
    {C r : ℝ≥0} {φ u : BiShift α₀ → ℝ} (hφ : HolderWith C r φ) (hr : 0 < r)
    (hu : Measurable u) (hae : IsAeCoboundaryOf (bernZ ν) biShiftMap φ u) :
    ∃ M : ℝ, ∀ᵐ x ∂(bernZ ν), |u x| ≤ M := by
  haveI : Fintype α₀ := Fintype.ofFinite α₀
  -- the stable bound, in the named public stable-pair marginals of `BiShiftProductStructure`
  -- (`stablePairMeasure`/`stableFst`/`stableSnd`); the abstract Fubini glue below unfolds these
  -- defs to the `joinPF` rectangle vocabulary it is stated in
  have hst : ∀ᵐ w ∂(stablePairMeasure ν),
      |u (stableSnd w) - u (stableFst w)|
        ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) :=
    stable_pair_osc ν hφ hr hu hae
  -- the unstable bound, in the named public unstable-pair marginals
  -- (`unstablePairMeasure`/`unstableFst`/`unstableSnd`)
  have hun : ∀ᵐ w ∂(unstablePairMeasure ν),
      |u (unstableSnd w) - u (unstableFst w)|
        ≤ (C : ℝ) * (1 / 2 : ℝ) ^ (r : ℝ) / (1 - (1 / 2 : ℝ) ^ (r : ℝ)) :=
    unstable_pair_osc ν hφ hr hu hae
  exact essBounded_of_stable_unstable_osc (measurePreserving_joinPF ν) hu hst hun

/-- **Two-sided measurable-tier Livšic rigidity (headline).** Let `ν` be a fully supported
probability law on the finite discrete alphabet `α₀` (`hν : ∀ a, ν {a} ≠ 0`). If `φ` is an
`r`-Hölder observable (`r > 0`) that is `bernZ ν`-a.e. the coboundary of a merely **measurable**
(possibly **unbounded**) transfer function `u`, then `φ` has **vanishing periodic sums** for the
two-sided full shift.

Route: the Fubini glue makes `u` `bernZ ν`-essentially bounded (bound `M`); the clamp
`v := max (−M') (min M' u)` (`M' = max M 0 ≥ 0`) is bounded everywhere by `M'` and agrees with `u`
on the co-null set `{|u| ≤ M'}`; since the shift is measure preserving, `v` is itself an a.e.
transfer function; the already-shipped bounded tier
`hasVanishingPeriodicSums_of_bounded_aeCoboundary_biShift` finishes. No Hölder-version construction
of `u`, no Birkhoff ergodic theorem. -/
theorem hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift
    (hν : ∀ a : α₀, ν {a} ≠ 0)
    {C r : ℝ≥0} {φ u : BiShift α₀ → ℝ} (hφ : HolderWith C r φ) (hr : 0 < r)
    (hu : Measurable u) (hae : IsAeCoboundaryOf (bernZ ν) biShiftMap φ u) :
    HasVanishingPeriodicSums biShiftMap φ := by
  obtain ⟨M, hM⟩ := essBounded_of_measurable_aeCoboundary_biShift ν hφ hr hu hae
  -- clamp to a bounded-everywhere transfer function `v` agreeing with `u` a.e.
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set v : BiShift α₀ → ℝ := fun x => max (-M') (min M' (u x)) with hvdef
  have hv_meas : Measurable v := measurable_const.max (measurable_const.min hu)
  have hv_bdd : ∀ x, |v x| ≤ M' := by
    intro x
    rw [abs_le]
    refine ⟨le_max_left _ _, ?_⟩
    refine max_le (by linarith) ?_
    exact min_le_left _ _
  have huv : v =ᵐ[bernZ ν] u := by
    filter_upwards [hM] with x hx
    have hxM' : |u x| ≤ M' := le_trans hx (le_max_left _ _)
    rw [abs_le] at hxM'
    simp only [hvdef, min_eq_right hxM'.2, max_eq_right hxM'.1]
  -- the shift is measure preserving, so `v ∘ σ̃ =ᵐ u ∘ σ̃`
  have hmp : MeasurePreserving biShiftMap (bernZ ν) (bernZ ν) := by
    rw [← coe_biShiftEquiv]
    exact measurePreserving_biShiftEquiv_bernZ ν
  have hvσ : v ∘ biShiftMap =ᵐ[bernZ ν] u ∘ biShiftMap :=
    hmp.quasiMeasurePreserving.ae_eq huv
  -- `v` is an a.e. transfer function for `φ`
  have hcob_v : IsAeCoboundaryOf (bernZ ν) biShiftMap φ v := by
    unfold IsAeCoboundaryOf at hae ⊢
    filter_upwards [hae, huv, hvσ] with x hx hxu hxσ
    simp only [Function.comp_apply] at hxσ
    rw [hxσ, hxu]
    exact hx
  exact hasVanishingPeriodicSums_of_bounded_aeCoboundary_biShift ν hν hφ hr hv_bdd hcob_v

end BiShift

end ErgodicTheory
