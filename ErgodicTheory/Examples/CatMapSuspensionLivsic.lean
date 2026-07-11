/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionLivsic
import ErgodicTheory.Examples.CatMapClosing
import ErgodicTheory.Examples.CatMapSuspensionFlow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The flow-Livšic demarcation on the Arnold cat-map suspension flow

This module (issue #55) instantiates the tier-III Livšic equivalence for constant-roof suspension
flows (`ErgodicTheory.livsic_suspensionFlow_constRoof`) on the special (suspension) flow over the
genuine Arnold cat map `catTorus : 𝕋² → 𝕋²` with the unit roof `τ ≡ 1`, plugging the Hölder Livšic
converse `livsic_catTorus` for the base direction.

## Main results

* `ErgodicTheory.CatMapToral.livsic_catSuspensionFlow` — the flow-Livšic equivalence: a flow
  observable `F` (with Hölder induced base observable and per-fibre interval-integrability) is a
  flow coboundary of the cat-map suspension flow **iff** every periodic Birkhoff sum of its induced
  base observable vanishes.
* `ErgodicTheory.CatMapToral.livsic_catSuspensionFlow_orbitIntegral` — the flow-native form of the
  equivalence, phrasing the obstruction as the vanishing of every closed-orbit integral of `F`.
* `ErgodicTheory.CatMapToral.fibreObservable` — a `1`-periodic fibre profile `h` descends to a flow
  observable `F [x, s] = h s` on the suspension space (its full `ℤ`-invariance discharged).
* `ErgodicTheory.CatMapToral.sinFibreObservable` — the concrete profile `h s = sin (2π s)`.
* `ErgodicTheory.CatMapToral.isFlowCoboundary_sinFibreObservable` — **non-vacuity of the coboundary
  side**: since `∫₀¹ sin (2π s) ds = 0`, the induced base observable vanishes identically, so
  `sinFibreObservable` *is* a flow coboundary of the cat-map suspension flow.

The obstruction-side contrast is
`ErgodicTheory.CatMapToral.const_one_not_isFlowCoboundary_catSuspension`
(issue #36, `ErgodicTheory/Examples/CatMapFlowCoboundary.lean`): the constant observable `1` is
*not* a flow coboundary, because its induced base observable summed around the period-`1` fixed
point `0` equals `1 ≠ 0`. Together these two witnesses certify the tier-III equivalence has content
on both sides — some observables cobound, others do not.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972) 1278–1301.
* J. Laureano, A. Mendes, M. J. Ferreira, *Livschitz Theorem in Suspension Flows and Markov
  Systems*, Symmetry **12**(3):338 (2020).
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §19.2.
-/

open MeasureTheory Function

open scoped NNReal

namespace ErgodicTheory.CatMapToral

open ErgodicTheory

/-- **Flow-Livšic equivalence for the cat-map suspension flow** (constant unit roof). A flow
observable `F` whose induced base observable is Hölder and whose fibre restrictions are
interval-integrable is a flow coboundary of the cat-map suspension flow **iff** every periodic
Birkhoff sum of `inducedBaseCocycle F` vanishes. The base direction is discharged by the Hölder
Livšic rigidity theorem `livsic_catTorus`. -/
theorem livsic_catSuspensionFlow {C r : ℝ≥0} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (F : SuspensionSpace catTorusEquiv measurable_catRoof → ℝ)
    (hFhol : HolderWith C r (inducedBaseCocycle catTorusEquiv measurable_catRoof F))
    (hint : ∀ x a b, IntervalIntegrable
      (fun s => F (suspensionMk catTorusEquiv measurable_catRoof (x, s))) volume a b) :
    IsFlowCoboundary (suspensionFlowMap catTorusEquiv measurable_catRoof) F ↔
      HasVanishingPeriodicSums (⇑catTorusEquiv)
        (inducedBaseCocycle catTorusEquiv measurable_catRoof F) := by
  refine livsic_suspensionFlow_constRoof catTorusEquiv measurable_catRoof F 1 rfl hint ?_
  intro hvps
  have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
  rw [hcoe] at hvps ⊢
  exact ((livsic_catTorus hFhol hr0 hr1).mpr hvps).isCoboundary

/-- **Flow-native flow-Livšic equivalence for the cat-map suspension flow** (constant unit roof).
Same hypotheses as `livsic_catSuspensionFlow`, with the coboundary obstruction phrased directly as
the vanishing of every closed-orbit integral of `F`: `F` is a flow coboundary of the cat-map
suspension flow **iff** for every `catTorus`-periodic point `p` the integral of `F` around the
corresponding closed flow orbit (of period `birkhoffSum catTorus catRoof n p`, which is `n` for the
unit roof) vanishes. The base direction is discharged by the Hölder Livšic rigidity theorem
`livsic_catTorus`; the flow-native phrasing comes from
`livsic_suspensionFlow_constRoof_orbitIntegral`. -/
theorem livsic_catSuspensionFlow_orbitIntegral {C r : ℝ≥0} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (F : SuspensionSpace catTorusEquiv measurable_catRoof → ℝ)
    (hFhol : HolderWith C r (inducedBaseCocycle catTorusEquiv measurable_catRoof F))
    (hint : ∀ x a b, IntervalIntegrable
      (fun s => F (suspensionMk catTorusEquiv measurable_catRoof (x, s))) volume a b) :
    IsFlowCoboundary (suspensionFlowMap catTorusEquiv measurable_catRoof) F ↔
      ∀ (n : ℕ) (p : T2), catTorus^[n] p = p →
        ∫ s in (0 : ℝ)..(birkhoffSum catTorus catRoof n p),
          F (suspensionFlowMap catTorusEquiv measurable_catRoof s
            (suspensionSection' catTorusEquiv measurable_catRoof p)) = 0 := by
  have hcoe : (⇑catTorusEquiv : T2 → T2) = catTorus := funext catTorusEquiv_apply
  simp only [← hcoe]
  refine livsic_suspensionFlow_constRoof_orbitIntegral catTorusEquiv measurable_catRoof F 1 rfl
    hint ?_
  intro hvps
  rw [hcoe] at hvps ⊢
  exact ((livsic_catTorus hFhol hr0 hr1).mpr hvps).isCoboundary

/-- A `1`-periodic fibre profile shifted by an integer is unchanged: `h (s − n) = h s` for `n : ℤ`,
by induction on `n` from the single-step periodicity `h (s − 1) = h s`. -/
theorem fibreProfile_sub_intCast {h : ℝ → ℝ} (hper : ∀ s, h (s - 1) = h s) :
    ∀ (n : ℤ) (s : ℝ), h (s - (n : ℝ)) = h s := by
  have hp : Function.Periodic h 1 := by
    intro x
    have h1 := hper (x + 1)
    rw [add_sub_cancel_right] at h1
    exact h1.symm
  intro n s
  simpa using hp.sub_int_mul_eq n

/-- **Non-vacuity witness (descent).** A `1`-periodic fibre profile `h` (well-definedness =
periodicity) descends through the suspension quotient to a flow observable `F [x, s] = h s` on the
cat-map suspension space. The full `ℤ`-invariance follows from `fibreProfile_sub_intCast` since the
suspension action shifts the fibre coordinate by the integer roof sum `roofSum n x = n`
(`roofSum_oneRoof`). -/
noncomputable def fibreObservable (h : ℝ → ℝ) (hper : ∀ s, h (s - 1) = h s) :
    SuspensionSpace catTorusEquiv measurable_catRoof → ℝ :=
  letI := suspensionAddAction catTorusEquiv measurable_catRoof
  Quotient.lift (fun p => h p.2) (fun p q hpq => by
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n +ᵥ q = p := hpq
    have hn' : suspensionAct catTorusEquiv measurable_catRoof n q = p := hn
    obtain ⟨qx, qs⟩ := q
    obtain ⟨px, ps⟩ := p
    have hact := suspensionAct_eq catTorusEquiv measurable_catRoof n qx qs
    rw [roofSum_oneRoof catTorusEquiv measurable_catRoof rfl] at hact
    rw [hact] at hn'
    have hps : qs - (n : ℝ) = ps := (Prod.ext_iff.mp hn').2
    change h ps = h qs
    rw [← hps]
    exact fibreProfile_sub_intCast hper n qs)

@[simp] theorem fibreObservable_mk (h : ℝ → ℝ) (hper : ∀ s, h (s - 1) = h s) (p : T2 × ℝ) :
    fibreObservable h hper (suspensionMk catTorusEquiv measurable_catRoof p) = h p.2 := rfl

/-- The concrete `sin (2π·)` fibre profile: `1`-periodic, so a valid witness input. -/
noncomputable def sinFibreObservable :
    SuspensionSpace catTorusEquiv measurable_catRoof → ℝ :=
  fibreObservable (fun s => Real.sin (2 * Real.pi * s)) (by
    intro s
    dsimp only
    rw [show 2 * Real.pi * (s - 1) = 2 * Real.pi * s - 2 * Real.pi from by ring,
      Real.sin_sub_two_pi])

/-- The induced base observable of the `sin (2π·)` fibre profile vanishes identically: over the
unit roof it is the full-period integral `∫₀¹ sin (2π s) ds = 0`. -/
theorem inducedBaseCocycle_sinFibreObservable :
    inducedBaseCocycle catTorusEquiv measurable_catRoof sinFibreObservable = 0 := by
  funext x
  rw [inducedBaseCocycle]
  simp only [sinFibreObservable, fibreObservable_mk, Pi.zero_apply]
  have hc : (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  change (∫ s in (0 : ℝ)..(1 : ℝ), Real.sin (2 * Real.pi * s)) = 0
  rw [intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (c := 2 * Real.pi) (f := Real.sin) hc,
    mul_zero, mul_one, integral_sin, Real.cos_zero, Real.cos_two_pi, sub_self, smul_zero]

/-- The `sin (2π·)` induced base observable has vanishing periodic sums (it is identically zero). -/
theorem hasVanishingPeriodicSums_sinFibreObservable :
    HasVanishingPeriodicSums (⇑catTorusEquiv)
      (inducedBaseCocycle catTorusEquiv measurable_catRoof sinFibreObservable) := by
  rw [inducedBaseCocycle_sinFibreObservable]
  intro n p _
  simp [birkhoffSum]

/-- **Non-vacuity of the coboundary side.** The `sin (2π·)` fibre observable *is* a flow coboundary
of the cat-map suspension flow: its induced base observable vanishes identically (the full-period
integral `∫₀¹ sin (2π s) ds = 0`), so all periodic Birkhoff sums vanish and the tier-III
equivalence `livsic_catSuspensionFlow` supplies a flow transfer function. Contrast with
`const_one_not_isFlowCoboundary_catSuspension`, the obstruction-side witness. -/
theorem isFlowCoboundary_sinFibreObservable :
    IsFlowCoboundary (suspensionFlowMap catTorusEquiv measurable_catRoof)
      sinFibreObservable := by
  refine (livsic_catSuspensionFlow (C := 0) (r := 1) one_pos le_rfl sinFibreObservable ?_ ?_).mpr
    hasVanishingPeriodicSums_sinFibreObservable
  · rw [inducedBaseCocycle_sinFibreObservable]
    exact HolderWith.zero
  · intro x a b
    have hcont : Continuous (fun s : ℝ => sinFibreObservable
        (suspensionMk catTorusEquiv measurable_catRoof (x, s))) := by
      simp only [sinFibreObservable, fibreObservable_mk]
      fun_prop
    exact hcont.intervalIntegrable a b

end ErgodicTheory.CatMapToral
