/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import ErgodicTheory.Continuous.SuspensionFlow

/-!
# Fibre Fourier coefficients on the lifted plane of a constant-roof suspension

This module builds the *fibre Fourier coefficient* used to prove the ergodicity of the time-one map
of a constant-roof suspension flow (GitHub issue #35, STEP-D infrastructure). It works on the
**lifted plane** `X × ℝ` — the total space of the suspension before quotienting — rather than on the
suspension space itself.

## The transform

For a function `F : X × ℝ → ℂ` on the lifted plane we integrate its `n`-th Fourier mode over the
*unit* window in the fibre coordinate:

`coeffFn F n x := ∫ s in 0..1, fourier (-n) (↑s) • F (x, s)`.

The key point (Cornfeld–Fomin–Sinai, *Ergodic Theory*, Ch. 11: special flows and their spectral
analysis) is that the transform window is the period of the **invariance** — the time-one map has
period `1` in the fibre — and *not* the roof `r`. Consequently no piecewise "lap" decomposition of
the roof is needed: everything is a clean global change of variables.

## Main results

* `ErgodicTheory.coeffFn` — the fibre Fourier coefficient.
* `ErgodicTheory.measurable_coeffFn` — measurability of `x ↦ coeffFn F n x`, by Fubini
  (`StronglyMeasurable.integral_prod_right'`).
* `ErgodicTheory.norm_coeffFn_le` — the trivial sup bound `‖coeffFn F n x‖ ≤ M` for `‖F‖ ≤ M`.
* `ErgodicTheory.coeffFn_twist` — **the twisted eigenfunction relation.** For `F` that is
  `1`-periodic in the fibre (`F (x, s + 1) = F (x, s)`) and satisfies the deck identity
  `F (T x, s) = F (x, s + r)`,
  `coeffFn F n (T x) = e^{2πinr} · coeffFn F n x`. Its proof is a three-step change of variables:
  character algebra, `intervalIntegral.integral_comp_add_right`, and
  `Function.Periodic.intervalIntegral_add_eq`.

## The lift dictionary

For a measurable set `A` in a constant-roof (`τ ≡ r`) suspension, its **lifted indicator**
`liftedIndicator A := 𝟙_{suspensionMk ⁻¹' A}` on the plane realises exactly the two hypotheses of
`coeffFn_twist`:

* `ErgodicTheory.lifted_indicator_periodic` — if `A` is invariant under the time-one flow map
  (`suspensionFlowMap 1 ⁻¹' A = A`) then the lifted indicator is `1`-periodic in the fibre.
* `ErgodicTheory.lifted_indicator_deck` — quotient saturation gives the deck identity
  `liftedIndicator A (T x, s) = liftedIndicator A (x, s + r)` unconditionally.
* `ErgodicTheory.coeffFn_liftedIndicator_twist` — assembling the two, the fibre Fourier coefficient
  of a `ζ₁`-invariant set's lifted indicator is a twisted eigenfunction.

The `Fact ((0 : ℝ) < 1)` needed for the length-`1` circle `AddCircle (1 : ℝ)` is already supplied
globally by Mathlib (`ZeroLEOneClass.factZeroLtOne`).
-/

open MeasureTheory Set Function intervalIntegral AddCircle
open scoped Real

noncomputable section

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X]

section Coeff

/-- The `n`-th **fibre Fourier coefficient** of `F : X × ℝ → ℂ` over the unit invariance window:
`coeffFn F n x = ∫ s in 0..1, fourier (-n) (↑s) • F (x, s)`. The window length `1` is the period of
the time-one flow map, not the roof. -/
def coeffFn (F : X × ℝ → ℂ) (n : ℤ) (x : X) : ℂ :=
  ∫ s in (0 : ℝ)..1, fourier (-n) (s : AddCircle (1 : ℝ)) • F (x, s)

/-- Fubini measurability of the fibre Fourier coefficient: if `F` is measurable then so is
`x ↦ coeffFn F n x`, via `StronglyMeasurable.integral_prod_right'`. -/
theorem measurable_coeffFn {F : X × ℝ → ℂ} (hF : Measurable F) (n : ℤ) :
    Measurable (coeffFn F n) := by
  have hint : StronglyMeasurable
      fun p : X × ℝ => fourier (-n) (p.2 : AddCircle (1 : ℝ)) • F p := by
    refine Measurable.stronglyMeasurable ?_
    have hchar : Measurable fun p : X × ℝ => (fourier (-n) (p.2 : AddCircle (1 : ℝ)) : ℂ) :=
      ((map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' (1 : ℝ))).measurable.comp
        measurable_snd
    exact hchar.smul hF
  have h := hint.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
  have heq : coeffFn F n = fun x => ∫ s, fourier (-n) (s : AddCircle (1 : ℝ)) • F (x, s)
      ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext x
    rw [coeffFn, intervalIntegral.integral_of_le zero_le_one]
  rw [heq]
  exact h.measurable

omit [MeasurableSpace X] in
/-- The trivial sup bound: if `‖F p‖ ≤ M` everywhere then `‖coeffFn F n x‖ ≤ M`, since the character
has unit modulus and the integration window has length `1`. -/
theorem norm_coeffFn_le {F : X × ℝ → ℂ} {M : ℝ} (hbd : ∀ p, ‖F p‖ ≤ M) (n : ℤ) (x : X) :
    ‖coeffFn F n x‖ ≤ M := by
  rw [coeffFn]
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖fourier (-n) (s : AddCircle (1 : ℝ)) • F (x, s)‖ ≤ M := by
    intro s _
    rw [norm_smul]
    have hf : ‖fourier (-n) (s : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
    rw [hf, one_mul]
    exact hbd (x, s)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa using h

omit [MeasurableSpace X] in
/-- **The twisted eigenfunction relation.** For `F : X × ℝ → ℂ` that is `1`-periodic in the fibre
coordinate and satisfies the deck identity `F (T x, s) = F (x, s + r)`,
`coeffFn F n (T x) = e^{2πinr} · coeffFn F n x`. The proof is a three-step change of variables:
character algebra, `intervalIntegral.integral_comp_add_right`, and
`Function.Periodic.intervalIntegral_add_eq` over the unit window. -/
theorem coeffFn_twist {F : X × ℝ → ℂ} (T : X → X) (r : ℝ)
    (hper : ∀ x s, F (x, s + 1) = F (x, s))
    (hdeck : ∀ x s, F (T x, s) = F (x, s + r)) (n : ℤ) (x : X) :
    coeffFn F n (T x) = Complex.exp (2 * Real.pi * Complex.I * n * r) * coeffFn F n x := by
  set G : ℝ → ℂ := fun u => fourier (-n) (u : AddCircle (1 : ℝ)) • F (x, u) with hG
  have hGper : Function.Periodic G 1 := by
    intro u
    have h1 : ((u + 1 : ℝ) : AddCircle (1 : ℝ)) = ((u : ℝ) : AddCircle (1 : ℝ)) :=
      coe_add_period (1 : ℝ) u
    simp only [hG, h1, hper]
  have hstep : ∀ s : ℝ, fourier (-n) (s : AddCircle (1 : ℝ)) • F (T x, s)
      = Complex.exp (2 * Real.pi * Complex.I * n * r) • G (s + r) := by
    intro s
    rw [hdeck x s, hG]
    simp only [smul_eq_mul, ← mul_assoc]
    congr 1
    rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h1 : coeffFn F n (T x)
      = Complex.exp (2 * Real.pi * Complex.I * n * r) • ∫ s in (0 : ℝ)..1, G (s + r) := by
    rw [coeffFn, ← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr fun s _ => hstep s
  have h2 : (∫ s in (0 : ℝ)..1, G (s + r)) = ∫ u in (0 + r : ℝ)..(1 + r : ℝ), G u :=
    intervalIntegral.integral_comp_add_right G r
  have h3 : (∫ u in (0 + r : ℝ)..(1 + r : ℝ), G u) = ∫ u in (0 : ℝ)..1, G u := by
    have := hGper.intervalIntegral_add_eq r 0
    simpa [zero_add, add_comm] using this
  rw [h1, h2, h3, smul_eq_mul, coeffFn]

end Coeff

section Lift

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The **lifted indicator** of a set `A` in the suspension space: the `ℂ`-valued indicator on the
plane `X × ℝ` of the preimage `suspensionMk ⁻¹' A`. It is `1` on points whose orbit class lies in
`A` and `0` elsewhere, and is the function fed to `coeffFn` in the time-one ergodicity argument. -/
def liftedIndicator (A : Set (SuspensionSpace T hτ)) : X × ℝ → ℂ :=
  Set.indicator (suspensionMk T hτ ⁻¹' A) 1

/-- **Deck identity for the lifted indicator** (constant roof `τ ≡ r`). Quotient saturation gives
`suspensionMk (T x, s) = suspensionMk (x, s + r)`, so the lifted indicator satisfies
`liftedIndicator A (T x, s) = liftedIndicator A (x, s + r)` unconditionally on `A`. This is the
`hdeck` hypothesis consumed by `coeffFn_twist`. -/
theorem lifted_indicator_deck {r : ℝ} (hconst : ∀ y, τ y = r) (A : Set (SuspensionSpace T hτ))
    (x : X) (s : ℝ) :
    liftedIndicator T hτ A (T x, s) = liftedIndicator T hτ A (x, s + r) := by
  have h1 : suspensionAct T hτ 1 (x, s + r) = (T x, s) := by
    rw [suspensionAct_one, suspensionGen_apply, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    change s + r - τ x = s
    rw [hconst]; ring
  have hmk : suspensionMk T hτ (T x, s) = suspensionMk T hτ (x, s + r) := by
    calc suspensionMk T hτ (T x, s)
        = suspensionMk T hτ (suspensionAct T hτ 1 (x, s + r)) := by rw [h1]
      _ = suspensionMk T hτ (x, s + r) := by
          letI := suspensionAddAction T hτ
          exact Quotient.sound ⟨1, suspension_vadd_eq_act T hτ 1 (x, s + r)⟩
  have hiff : (T x, s) ∈ suspensionMk T hτ ⁻¹' A ↔ (x, s + r) ∈ suspensionMk T hτ ⁻¹' A := by
    rw [Set.mem_preimage, Set.mem_preimage, hmk]
  unfold liftedIndicator
  by_cases hc : (x, s + r) ∈ suspensionMk T hτ ⁻¹' A
  · rw [Set.indicator_of_mem (hiff.mpr hc), Set.indicator_of_mem hc, Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem (fun h => hc (hiff.mp h)), Set.indicator_of_notMem hc]

/-- **Fibre `1`-periodicity of the lifted indicator.** If `A` is invariant under the time-one flow
map (`suspensionFlowMap T hτ 1 ⁻¹' A = A`) then, since `suspensionMk (x, s + 1) = ζ₁ (suspensionMk
(x, s))`, the lifted indicator satisfies `liftedIndicator A (x, s + 1) = liftedIndicator A (x, s)`.
This is the `hper` hypothesis consumed by `coeffFn_twist`. -/
theorem lifted_indicator_periodic (A : Set (SuspensionSpace T hτ))
    (hinv : suspensionFlowMap T hτ 1 ⁻¹' A = A) (x : X) (s : ℝ) :
    liftedIndicator T hτ A (x, s + 1) = liftedIndicator T hτ A (x, s) := by
  have key : suspensionMk T hτ (x, s + 1)
      = suspensionFlowMap T hτ 1 (suspensionMk T hτ (x, s)) := by
    simp only [suspensionFlowMap_mk, suspensionTranslate_apply]
  have hmem : suspensionMk T hτ (x, s + 1) ∈ A ↔ suspensionMk T hτ (x, s) ∈ A := by
    rw [key, ← Set.mem_preimage, hinv]
  have hiff : (x, s + 1) ∈ suspensionMk T hτ ⁻¹' A ↔ (x, s) ∈ suspensionMk T hτ ⁻¹' A := by
    rw [Set.mem_preimage, Set.mem_preimage]; exact hmem
  unfold liftedIndicator
  by_cases hc : (x, s) ∈ suspensionMk T hτ ⁻¹' A
  · rw [Set.indicator_of_mem (hiff.mpr hc), Set.indicator_of_mem hc, Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem (fun h => hc (hiff.mp h)), Set.indicator_of_notMem hc]

/-- **The dictionary assembled.** For a `ζ₁`-invariant set `A` in a constant-roof suspension, its
lifted indicator's fibre Fourier coefficient is a twisted eigenfunction:
`coeffFn (liftedIndicator A) n (T x) = e^{2πinr} · coeffFn (liftedIndicator A) n x`. This is
`coeffFn_twist` fed with `lifted_indicator_periodic` and `lifted_indicator_deck`. -/
theorem coeffFn_liftedIndicator_twist {r : ℝ} (hconst : ∀ y, τ y = r)
    (A : Set (SuspensionSpace T hτ)) (hinv : suspensionFlowMap T hτ 1 ⁻¹' A = A) (n : ℤ) (x : X) :
    coeffFn (liftedIndicator T hτ A) n (T x)
      = Complex.exp (2 * Real.pi * Complex.I * n * r) * coeffFn (liftedIndicator T hτ A) n x :=
  coeffFn_twist (⇑T) r (lifted_indicator_periodic T hτ A hinv)
    (lifted_indicator_deck T hτ hconst A) n x

end Lift

end ErgodicTheory
