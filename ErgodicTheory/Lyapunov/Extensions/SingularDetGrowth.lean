/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.SingularDet

/-!
# The top singular exponent `γ_d` and the genuine `log|det|` growth

This module completes the `k = d` (volume) end of the cumulative forward singular exponent
family `γ_k` (`ErgodicTheory.forwardSingularExponent`): it ties the top cumulative `EReal` exponent
`γ_d` — and the forward top-`d` value `Γ_d⁺` — to the **genuine** (not `log⁺`) determinant growth
`(1/n) log|det(A⁽ⁿ⁾ x)|`, staying entirely inside the **singular** (forward-only) track.

The crux is that, at the top index, the singular-value product collapses to the absolute
determinant, `sprod A T d n x = |det(A⁽ⁿ⁾ x)|` (`ErgodicTheory.sprod_d_eq_abs_det`). Rewriting the
top-`k` results of `ErgodicTheory/Lyapunov/Extensions/Singular.lean` through this identity converts
their `log sprod_d` statements into statements about `log|det(A⁽ⁿ⁾)|`:

* the a.e.-constant value: `γ_d(x) = (Γ_d⁺ : EReal)` `μ`-a.e. (`k = d` instance of
  `ErgodicTheory.ae_forwardSingularExponent_eq_coe`);
* the genuine growth, when `Γ_d⁺ > 0`: `limsup ((1/n) log|det(A⁽ⁿ⁾)| : EReal) = (Γ_d⁺ : EReal)`
  `μ`-a.e. (`k = d` instance of `ErgodicTheory.limsup_logSprod_eq_top_of_pos`, rewritten by
  `sprod_d_eq_abs_det`).

## Main results

* `ErgodicTheory.ae_forwardSingularExponent_full_eq_coe` — `γ_d = (Γ_d⁺ : EReal)` `μ`-a.e. (the
  top-index value, forward-only hypotheses).
* `ErgodicTheory.ae_forwardSingularExponent_full_eq_det_growth` — the headline: a single forward
  top-`d` constant `Γ_d⁺` is the `μ`-a.e. value of `γ_d`, and, **whenever `Γ_d⁺ > 0`**, also the
  exact `EReal`-`limsup` of the genuine normalized `log|det(A⁽ⁿ⁾)|`.

## Implementation notes

* Everything here uses **only** the forward hypotheses `[IsProbabilityMeasure μ]`, `[NeZero d]`,
  `Ergodic T μ`, `Measurable A`, `IntegrableLogNorm A μ` (`log⁺‖A‖ ∈ L¹`). There is **no** call
  to the invertible additive `ErgodicTheory/Lyapunov/Extensions/DetIdentity.lean` track: its genuine
  `(1/n) log|det(A⁽ⁿ⁾)| → ∑ exponents` requires `det A ≠ 0`, inverse integrability
  `log⁺‖A⁻¹‖ ∈ L¹`, and Oseledets filtration data, which the singular track does not assume. The
  `EReal`/`limsup` packaging here is the contraction-robust replacement.
* The positivity hypothesis `Γ_d⁺ > 0` (the expanding-volume regime) is essential for the genuine
  `log|det|` identification: only then does the convergent `log⁺` form agree eventually with the
  genuine `log`. When `Γ_d⁺ = 0` (volume contraction, `|det(A⁽ⁿ⁾)| → 0`, genuine growth `→ −∞`)
  the `EReal`-`limsup` of the genuine `log|det|` can fall strictly below `Γ_d⁺`, so only the `≤`
  form (`ErgodicTheory.limsup_logSprod_le_top` rewritten through `sprod_d_eq_abs_det`) survives
  there; it is not folded in here.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58.
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ} {μ : Measure X}

/-- **`γ_d` is `μ`-a.e. a real constant `Γ_d⁺`** (the top-index value). The `k = d` instance of
`ErgodicTheory.ae_forwardSingularExponent_eq_coe`: for an ergodic measure-preserving `T` and a
possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹`, there is a real `Γ_d⁺` with
`γ_d(x) = (Γ_d⁺ : EReal)` for `μ`-a.e. `x`. No invertibility, no inverse integrability. -/
theorem ae_forwardSingularExponent_full_eq_coe [IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) :
    ∃ gam : ℝ, ∀ᵐ x ∂μ, forwardSingularExponent A T d x = (gam : EReal) :=
  ae_forwardSingularExponent_eq_coe hT hAmeas hint d

/-- **`γ_d` and the genuine `log|det|` growth** (the headline). For an ergodic measure-preserving
`T` and a possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹` (no `det A ≠ 0`, no inverse
integrability), there is a single forward top-`d` constant `Γ_d⁺` such that:

* `γ_d(x) = (Γ_d⁺ : EReal)` for `μ`-a.e. `x` (the cumulative top singular exponent is a.e. this
  constant), and
* **whenever `Γ_d⁺ > 0`**, for `μ`-a.e. `x`
  `limsup (fun n => ((1/n) log|det(A⁽ⁿ⁾ x)| : EReal)) = (Γ_d⁺ : EReal)`,
  i.e. the *genuine* (not `log⁺`) normalized log absolute determinant has `EReal`-`limsup`
  exactly `Γ_d⁺`.

Proof: instantiate `ErgodicTheory.limsup_logSprod_eq_top_of_pos` at `k = d`, which provides the
constant `Γ_d⁺` together with the a.e. limit of `(1/n) log⁺ sprod_d` and the positive-regime
genuine `limsup` identity for `log sprod_d`. The value clause comes from that limit through
`forwardSingularExponent` (mirroring `ae_forwardSingularExponent_eq_coe`); the growth clause is
the genuine `limsup` rewritten by `sprod_d_eq_abs_det` (`sprod_d = |det|`). The positivity
hypothesis is essential — in the contracting case `Γ_d⁺ = 0` the genuine `log|det|` may tend to
`−∞`, so its `limsup` can be strictly below `Γ_d⁺`. -/
theorem ae_forwardSingularExponent_full_eq_det_growth [IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) :
    ∃ gam : ℝ,
      (∀ᵐ x ∂μ, forwardSingularExponent A T d x = (gam : EReal)) ∧
      (0 < gam → ∀ᵐ x ∂μ,
        Filter.limsup
          (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log |(cocycle A T n x).det| : ℝ) : EReal)) atTop
          = (gam : EReal)) := by
  obtain ⟨gam, hlim, hpos⟩ := limsup_logSprod_eq_top_of_pos hT hAmeas hint d
  refine ⟨gam, ?_, fun hg => ?_⟩
  · -- The value clause: `(1/n) log⁺ sprod_d → gam` lifts to `γ_d = (gam : EReal)` a.e.
    filter_upwards [hlim] with x hx
    have hxE : Tendsto
        (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog (sprod A T d n x) : ℝ) : EReal)) atTop
        (𝓝 (gam : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hx
    rw [forwardSingularExponent]
    exact hxE.limsup_eq
  · -- The growth clause: rewrite `sprod_d = |det|` in the genuine-`log` `limsup` identity.
    filter_upwards [hpos hg] with x hx
    have hrw : (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log |(cocycle A T n x).det| : ℝ) : EReal))
        = fun n : ℕ => (((n : ℝ)⁻¹ * Real.log (sprod A T d n x) : ℝ) : EReal) := by
      funext n
      rw [sprod_d_eq_abs_det n x]
    rw [hrw]
    exact hx

end ErgodicTheory
