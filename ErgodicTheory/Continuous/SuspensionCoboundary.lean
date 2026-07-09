/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlow
import ErgodicTheory.Continuous.ReturnTimeExponent
import ErgodicTheory.Continuous.SuspensionFlowMP
import ErgodicTheory.Livsic.FlowCoboundary
import ErgodicTheory.Livsic.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Livšic flow tier: the periodic-orbit obstruction for suspension flows

This module (issue #36) lands the **flow Livšic** periodic-orbit obstruction on the concrete
suspension (mapping-torus) flow `ζ_t` of a base automorphism `T` under a roof `τ`, built in
`ErgodicTheory.Continuous.SuspensionFlow`. It connects the regularity-free flow coboundary
`ErgodicTheory.IsFlowCoboundary` of `ErgodicTheory.Livsic.FlowCoboundary` with the discrete
coboundary `ErgodicTheory.IsCoboundary` on the base, via the cross-section `x ↦ [x, 0]`.

The construction is the classical *induced observable* on the cross-section: the roof-height
integral

`inducedBaseCocycle F x = ∫₀^{τ x} F [x, s] ds`

of the flow observable `F` over one lap of the flow above the point `x`. Its base Birkhoff sum
around a periodic base orbit equals the flow integral of `F` around the corresponding closed flow
orbit; this is the *lap decomposition* bridge. Consequently a nonzero periodic sum of the induced
observable — equivalently, a nonzero closed-orbit integral of `F` — forbids `F` from being a flow
coboundary.

## Main definitions

* `ErgodicTheory.suspensionSection'` — the cross-section `x ↦ [x, 0]`.
* `ErgodicTheory.inducedBaseCocycle` — the induced base observable `∫₀^{τ x} F [x, s] ds`.

## Main results

* `ErgodicTheory.suspensionFlowMap_roof` — flowing for time `τ x` from the section carries `[x, 0]`
  to `[T x, 0]`.
* `ErgodicTheory.inducedBaseCocycle_isCoboundary` — a flow coboundary induces a discrete coboundary
  on the base (transfer function `u ∘ section`).
* `ErgodicTheory.not_isFlowCoboundary_of_inducedPeriodicSum_ne_zero` — **tier 1**: a nonzero
  periodic Birkhoff sum of the induced observable defeats every flow coboundary.
* `ErgodicTheory.suspensionFlow_orbit_periodic` — a base `n`-periodic point closes up into a
  flow-periodic point with period the roof Birkhoff sum `birkhoffSum T τ n p`.
* `ErgodicTheory.not_isFlowCoboundary_suspensionFlowMap_of_periodicOrbitIntegral_ne_zero` —
  **tier 2** (flow-native): a nonzero closed-orbit integral of `F` defeats every flow coboundary.
* `ErgodicTheory.suspensionCoboundary_lap_integral` — the per-lap identity: the flow integral of `F`
  over the `k`-th lap equals `inducedBaseCocycle F (T^[k] p)`.
* `ErgodicTheory.suspension_periodicOrbitIntegral_eq_birkhoffSum` — **the bridge**: the closed-orbit
  flow integral of `F` equals the base Birkhoff sum of the induced observable, identifying the two
  obstruction quantities.

## What is *not* in this file

Only the **trivial** (obstruction) direction of the flow Livšic theorem is proved. The **converse**
— vanishing of all closed-orbit integrals implies `F` is a *Hölder* flow coboundary (flow Livšic
proper) — is **not** delivered. Its genuine obstacle is the Hölder gluing of the reconstructed
transfer function across the fundamental-domain seam `s = τ`, which is beyond the scope of this
regularity-free layer.
-/

open MeasureTheory Function

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- Orbit-quotient collapse: applying any `ℤ`-power of the suspension generator before projecting to
the suspension space changes nothing, `[suspensionAct n p] = [p]`. Re-derived here (rather than
imported from the heavier `SuspensionStandardBorel`) directly from `Quotient.sound` and the identity
`suspension_vadd_eq_act`. -/
theorem suspensionMk_act' (n : ℤ) (p : X × ℝ) :
    suspensionMk T hτ (suspensionAct T hτ n p) = suspensionMk T hτ p := by
  letI := suspensionAddAction T hτ
  refine Quotient.sound ?_
  change ∃ m : ℤ, m +ᵥ p = suspensionAct T hτ n p
  exact ⟨n, suspension_vadd_eq_act T hτ n p⟩

/-- The **cross-section** of the suspension flow: the base point `x` at height `0`, `x ↦ [x, 0]`.
This re-derives the cross-section `suspensionSection` of `SuspensionMeasureTransfer` (the prime
avoids the name clash with that root-imported definition) to keep this module's imports light,
mirroring the `suspensionMk_act'` pattern above. -/
def suspensionSection' (x : X) : SuspensionSpace T hτ := suspensionMk T hτ (x, 0)

/-- The **induced base observable** of a flow observable `F`: the integral of `F` over one lap of
the suspension flow above `x`, `∫₀^{τ x} F [x, s] ds`. Its base Birkhoff sums are the closed-orbit
integrals of `F` (see `suspension_periodicOrbitIntegral_eq_birkhoffSum`). -/
noncomputable def inducedBaseCocycle (F : SuspensionSpace T hτ → ℝ) (x : X) : ℝ :=
  ∫ s in (0 : ℝ)..(τ x), F (suspensionMk T hτ (x, s))

/-- Flowing for time `τ x` from the cross-section carries `[x, 0]` to the next section point
`[T x, 0]`: the flow returns to the cross-section exactly after one roof-height. -/
theorem suspensionFlowMap_roof (x : X) :
    suspensionFlowMap T hτ (τ x) (suspensionSection' T hτ x) = suspensionSection' T hτ (T x) := by
  have hact : suspensionAct T hτ 1 (x, τ x) = (T x, 0) := by
    rw [suspensionAct_one, suspensionGen_apply]; simp
  simp only [suspensionSection', suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]
  rw [← hact, suspensionMk_act' T hτ 1 (x, τ x)]

/-- **A flow coboundary induces a discrete base coboundary.** If `F` is a flow coboundary for the
suspension flow, with transfer function `u`, then the induced base observable `inducedBaseCocycle F`
is a discrete coboundary for the base map `T`, with transfer function `u ∘ suspensionSection'`. The
identity is the flow-coboundary equation evaluated at the section point `[x, 0]` over one lap
`t = τ x`, using `suspensionFlowMap_roof` to collapse the left side and the descent identity
`ζ_s [x, 0] = [x, s]` to identify the lap integrand. -/
theorem inducedBaseCocycle_isCoboundary (F : SuspensionSpace T hτ → ℝ)
    (h : IsFlowCoboundary (suspensionFlowMap T hτ) F) :
    IsCoboundary (⇑T) (inducedBaseCocycle T hτ F) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨fun x => u (suspensionSection' T hτ x), fun x => ?_⟩
  change inducedBaseCocycle T hτ F x
    = u (suspensionSection' T hτ (T x)) - u (suspensionSection' T hτ x)
  have key := hu (suspensionSection' T hτ x) (τ x)
  rw [suspensionFlowMap_roof] at key
  have hfun : (fun s => F (suspensionFlowMap T hτ s (suspensionSection' T hτ x)))
      = fun s => F (suspensionMk T hτ (x, s)) := by
    funext s
    simp only [suspensionSection', suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]
  rw [inducedBaseCocycle, key, hfun]

/-- **Tier 1 obstruction.** If `p` is an `n`-periodic base point and the periodic Birkhoff sum of
the induced base observable `inducedBaseCocycle F` does not vanish, then `F` is not a flow
coboundary of the suspension flow. Combines `inducedBaseCocycle_isCoboundary` with the discrete
obstruction `ErgodicTheory.not_isCoboundary_of_periodicSum_ne_zero`. -/
theorem not_isFlowCoboundary_of_inducedPeriodicSum_ne_zero {n : ℕ} {p : X}
    (hp : (⇑T)^[n] p = p) (F : SuspensionSpace T hτ → ℝ)
    (hf : birkhoffSum (⇑T) (inducedBaseCocycle T hτ F) n p ≠ 0) :
    ¬ IsFlowCoboundary (suspensionFlowMap T hτ) F := fun h =>
  not_isCoboundary_of_periodicSum_ne_zero hp hf (inducedBaseCocycle_isCoboundary T hτ F h)

/-- **Tier 2a: base periodicity closes up into flow periodicity.** A base `n`-periodic point `p`
(`T^[n] p = p`) is a periodic point of the suspension flow with period the roof Birkhoff sum
`birkhoffSum T τ n p`: flowing the section point `[p, 0]` for that time returns to `[p, 0]`.
Under the descent `ζ_t [p, 0] = [p, t]`, the endpoint `[p, birkhoffSum T τ n p]` collapses through
the orbit relation (`suspensionAct n` lands it at `(p, 0)`). -/
theorem suspensionFlow_orbit_periodic {n : ℕ} {p : X} (hp : (⇑T)^[n] p = p) :
    suspensionFlowMap T hτ (birkhoffSum (⇑T) τ n p) (suspensionSection' T hτ p)
      = suspensionSection' T hτ p := by
  have hS : birkhoffSum (⇑T) τ n p = roofSum T hτ (n : ℤ) p :=
    (roofSum_natCast_eq_birkhoffSum T hτ n p).symm
  have hact : suspensionAct T hτ (n : ℤ) (p, roofSum T hτ (n : ℤ) p) = (p, 0) := by
    rw [suspensionAct_eq, sub_self, baseIter_natCast, hp]
  calc suspensionFlowMap T hτ (birkhoffSum (⇑T) τ n p) (suspensionSection' T hτ p)
      = suspensionMk T hτ (p, roofSum T hτ (n : ℤ) p) := by
        rw [hS]
        simp only [suspensionSection', suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]
    _ = suspensionMk T hτ (suspensionAct T hτ (n : ℤ) (p, roofSum T hτ (n : ℤ) p)) :=
        (suspensionMk_act' T hτ (n : ℤ) _).symm
    _ = suspensionSection' T hτ p := by rw [hact, suspensionSection']

/-- **Tier 2 obstruction (flow-native).** If `p` is an `n`-periodic base point and the integral of
`F` around the corresponding closed flow orbit (of period `birkhoffSum T τ n p`) does not vanish,
then `F` is not a flow coboundary of the suspension flow. Combines the flow-periodicity
`suspensionFlow_orbit_periodic` with the generic flow obstruction
`not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero`. -/
theorem not_isFlowCoboundary_suspensionFlowMap_of_periodicOrbitIntegral_ne_zero {n : ℕ} {p : X}
    (hp : (⇑T)^[n] p = p) (F : SuspensionSpace T hτ → ℝ)
    (hI : (∫ s in (0 : ℝ)..(birkhoffSum (⇑T) τ n p),
        F (suspensionFlowMap T hτ s (suspensionSection' T hτ p))) ≠ 0) :
    ¬ IsFlowCoboundary (suspensionFlowMap T hτ) F :=
  not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero
    (suspensionFlow_orbit_periodic T hτ hp) hI

/-- **Per-lap identity.** The flow integral of `F` over the `k`-th lap, i.e. over the time interval
`[birkhoffSum T τ k p, birkhoffSum T τ (k+1) p]` starting from the section point `[p, 0]`, equals
the induced base observable at the `k`-th base iterate, `inducedBaseCocycle F (T^[k] p)`. The proof
rewrites the flow integrand `F (ζ_s [p, 0]) = F [p, s]`, shifts the base point along the orbit
relation (`suspensionAct k`), and matches the lap window to `[0, τ (T^[k] p)]` via the change of
variables `intervalIntegral.integral_comp_add_left`. -/
theorem suspensionCoboundary_lap_integral (F : SuspensionSpace T hτ → ℝ) (p : X) (k : ℕ) :
    (∫ s in (birkhoffSum (⇑T) τ k p)..(birkhoffSum (⇑T) τ (k + 1) p),
        F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)))
      = inducedBaseCocycle T hτ F ((⇑T)^[k] p) := by
  have hdir : ∀ s : ℝ, F (suspensionFlowMap T hτ s (suspensionSection' T hτ p))
      = F (suspensionMk T hτ (p, s)) := by
    intro s
    simp only [suspensionSection', suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]
  have hshift : ∀ x : ℝ, F (suspensionMk T hτ ((⇑T)^[k] p, x))
      = F (suspensionMk T hτ (p, birkhoffSum (⇑T) τ k p + x)) := by
    intro x
    have hact : suspensionAct T hτ (k : ℤ) (p, birkhoffSum (⇑T) τ k p + x)
        = ((⇑T)^[k] p, x) := by
      rw [suspensionAct_eq, baseIter_natCast, roofSum_natCast_eq_birkhoffSum, Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      ring
    rw [← suspensionMk_act' T hτ (k : ℤ) (p, birkhoffSum (⇑T) τ k p + x), hact]
  have hsucc := birkhoffSum_succ (⇑T) τ k p
  simp_rw [hdir]
  rw [inducedBaseCocycle]
  simp_rw [hshift, intervalIntegral.integral_comp_add_left (fun s => F (suspensionMk T hτ (p, s)))]
  rw [hsucc, add_zero]

/-- **The bridge.** The integral of `F` around one full closed flow orbit above the base
`n`-periodic point `p`, i.e. from `0` to `birkhoffSum T τ n p`, equals the base Birkhoff sum of the
induced base observable `inducedBaseCocycle F`. This identifies the two obstruction quantities of
tier 1 and tier 2. It is the lap decomposition: the closed orbit is cut at the successive
cross-section returns `birkhoffSum T τ k p`, each lap contributing `inducedBaseCocycle F (T^[k] p)`
by `suspensionCoboundary_lap_integral`. The hypothesis `hint` is the per-lap interval integrability
required to add the lap integrals (`intervalIntegral.sum_integral_adjacent_intervals`). -/
theorem suspension_periodicOrbitIntegral_eq_birkhoffSum (F : SuspensionSpace T hτ → ℝ) (p : X)
    (n : ℕ)
    (hint : ∀ k < n, IntervalIntegrable
        (fun s => F (suspensionFlowMap T hτ s (suspensionSection' T hτ p))) volume
        (birkhoffSum (⇑T) τ k p) (birkhoffSum (⇑T) τ (k + 1) p)) :
    (∫ s in (0 : ℝ)..(birkhoffSum (⇑T) τ n p),
        F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)))
      = birkhoffSum (⇑T) (inducedBaseCocycle T hτ F) n p := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (n := n)
    (a := fun k => birkhoffSum (⇑T) τ k p) hint
  simp only [birkhoffSum_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ => suspensionCoboundary_lap_integral T hτ F p k

/-! ### Corollaries against the packaged measure-preserving suspension flow

The obstructions above are stated for the raw flow map `suspensionFlowMap`. When `T` preserves a
measure `μ` and the roof is bounded below by `c > 0`, the flow is packaged as a
`MeasurePreservingFlow` (`ErgodicTheory.suspensionFlow`); its coercion is definitionally
`suspensionFlowMap`, so the obstructions transfer verbatim to the packaged flow. -/

section Packaged

variable {μ : Measure X} [SFinite μ] (hT : MeasurePreserving T μ μ)
  {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)

/-- **Tier 1, packaged.** The tier-1 obstruction stated for the packaged measure-preserving
suspension flow `ErgodicTheory.suspensionFlow`. -/
theorem not_isFlowCoboundary_suspensionFlow_of_inducedPeriodicSum_ne_zero {n : ℕ} {p : X}
    (hp : (⇑T)^[n] p = p) (F : SuspensionSpace T hτ → ℝ)
    (hf : birkhoffSum (⇑T) (inducedBaseCocycle T hτ F) n p ≠ 0) :
    ¬ IsFlowCoboundary (⇑(suspensionFlow T hτ hT hc hcpos)) F :=
  not_isFlowCoboundary_of_inducedPeriodicSum_ne_zero T hτ hp F hf

/-- **Tier 2, packaged.** The tier-2 (flow-native) obstruction stated for the packaged
measure-preserving suspension flow `ErgodicTheory.suspensionFlow`. -/
theorem not_isFlowCoboundary_suspensionFlow_of_periodicOrbitIntegral_ne_zero {n : ℕ} {p : X}
    (hp : (⇑T)^[n] p = p) (F : SuspensionSpace T hτ → ℝ)
    (hI : (∫ s in (0 : ℝ)..(birkhoffSum (⇑T) τ n p),
        F (suspensionFlowMap T hτ s (suspensionSection' T hτ p))) ≠ 0) :
    ¬ IsFlowCoboundary (⇑(suspensionFlow T hτ hT hc hcpos)) F :=
  not_isFlowCoboundary_suspensionFlowMap_of_periodicOrbitIntegral_ne_zero T hτ hp F hI

end Packaged

end ErgodicTheory
