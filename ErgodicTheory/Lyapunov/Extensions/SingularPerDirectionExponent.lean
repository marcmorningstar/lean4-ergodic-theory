/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.SingularExponent

/-!
# The per-direction forward singular exponent `λ_i = γ_{i+1} − γ_i` (`EReal`-valued)

For a **possibly-singular** matrix cocycle generator `A` — only the forward hypothesis
`IntegrableLogNorm A μ` (`log⁺‖A‖ ∈ L¹`), no invertibility — this module differences the cumulative
forward singular exponent `γ_k = ErgodicTheory.forwardSingularExponent A T k` of
`ErgodicTheory/Lyapunov/Extensions/SingularExponent.lean` into the **per-direction exponent**

`λ_i(x) = γ_{i+1}(x) − γ_i(x)`,

the `i`-th *individual* forward exponent built from the top-`(i+1)` minus the top-`i` singular-value
volume.  Because `γ_k` is the `log⁺` (`Real.posLog`) cumulative volume exponent, it is `μ`-a.e. a
**finite** real constant `Γ_k⁺` (`ErgodicTheory.ae_forwardSingularExponent_eq_coe`), so the `EReal`
subtraction `γ_{i+1} − γ_i` is `μ`-a.e. an honest finite difference `(Γ_{i+1}⁺ − Γ_i⁺ : EReal)` — it
never lands on the indeterminate `⊤ − ⊤` or `⊥ − ⊥` forms.

## Main definitions

* `ErgodicTheory.singularDirExponent` — the per-direction forward singular exponent `λ_i`,
  the `EReal`
  difference `γ_{i+1} − γ_i`, defined for every `x` with no invertibility hypothesis.

## Main results

* `ErgodicTheory.measurable_singularDirExponent` — `λ_i` is measurable (difference of measurable
  `EReal`-valued maps, via `MeasurableAdd₂ EReal` and the continuous `EReal` negation).
* `ErgodicTheory.ae_singularDirExponent_eq_coe` — under ergodicity and forward integrability,
  `λ_i = (Γ_{i+1}⁺ − Γ_i⁺ : EReal)` `μ`-a.e. for a real constant; in particular `λ_i` is `μ`-a.e. an
  a.e.-**constant** finite real.
* `ErgodicTheory.ae_singularDirExponent_lt_top`, `ErgodicTheory.ae_singularDirExponent_ne_bot`
  — `μ`-a.e.
  finiteness (`λ_i < ⊤` and `⊥ < λ_i`), since `λ_i` a.e. equals a real coercion.

## Implementation notes

* Everything here rests **only** on the forward `γ_k` packaging of `SingularExponent.lean`, which
  needs only forward integrability and ergodicity. No `det A ≠ 0`, no `log⁺‖A⁻¹‖ ∈ L¹`.
* **Antitonicity in `i` is deliberately NOT claimed**, because it is *false* for this `log⁺`
  cumulative exponent in the contracting/collapsing regime.  Indeed `μ`-a.e.
  `γ_k = (max 0 μ_k : EReal)` where `μ_k = Σ_{j<k} λ_j^{gen}` is the *genuine* cumulative volume
  exponent and the genuine per-`σ` exponents `λ_j^{gen}` are antitone
  (`ErgodicTheory.antitone_log_singularValue`).  The increments `Γ_{i+1}⁺ − Γ_i⁺ = max 0 μ_{i+1} −
  max 0 μ_i` are antitone *only while `μ` stays `≥ 0`*: once the cumulative volume turns
  non-positive the `log⁺` clamps to `0`, and the increment jumps back **up** from a negative value
  to `0`.  Concretely, antitone genuine exponents `λ^{gen} = (1, −½, −½, −½)` give the cumulative
  `μ = (0,1,½,0,−½)`, so `max 0 μ = (0,1,½,0,0)` with increments `(1, −½, −½, 0)` — and `−½ < 0`
  breaks antitonicity.  So the
  antitone ordering lives on the *genuine-log* exponent `ErgodicTheory.forwardSingularExponentLog`
  (whose per-direction increments are the genuine `λ_i^{gen}`), not on this `log⁺` one; this module
  records only the unconditional, true facts (measurability and a.e.-constancy/finiteness).

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ} {μ : Measure X}

/-- **The per-direction forward singular exponent `λ_i`** of a possibly-singular cocycle generator,
the `EReal` difference of consecutive cumulative forward singular exponents:

`λ_i(x) = γ_{i+1}(x) − γ_i(x)`,

where `γ_k = ErgodicTheory.forwardSingularExponent A T k` is the `log⁺` cumulative top-`k` volume
exponent.  Since each `γ_k` is `μ`-a.e. a finite real constant `Γ_k⁺`, the `EReal` subtraction is
`μ`-a.e. the honest finite difference `(Γ_{i+1}⁺ − Γ_i⁺ : EReal)`. -/
noncomputable def singularDirExponent (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (i : ℕ) (x : X) : EReal :=
  forwardSingularExponent A T (i + 1) x - forwardSingularExponent A T i x

/-- **`λ_i` is measurable.** It is the `EReal` difference `γ_{i+1} − γ_i` of two measurable
`EReal`-valued maps (`measurable_forwardSingularExponent`).  `EReal` subtraction is `f + (-g)`
(`sub_eq_add_neg` on the `SubNegZeroMonoid EReal`); `EReal` negation is continuous
(`continuous_neg`, from `ContinuousNeg EReal`) hence measurable, and `EReal` addition is measurable
(`MeasurableAdd₂ EReal`), so `Measurable.add` applies. -/
theorem measurable_singularDirExponent [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hAmeas : Measurable A) (hTmeas : Measurable T) (i : ℕ) :
    Measurable (singularDirExponent A T i) := by
  have hsucc : Measurable (forwardSingularExponent A T (i + 1)) :=
    measurable_forwardSingularExponent hAmeas hTmeas (i + 1)
  have hcur : Measurable (forwardSingularExponent A T i) :=
    measurable_forwardSingularExponent hAmeas hTmeas i
  have hneg : Measurable fun x => -forwardSingularExponent A T i x :=
    (continuous_neg.measurable).comp hcur
  have : Measurable fun x =>
      forwardSingularExponent A T (i + 1) x + -forwardSingularExponent A T i x :=
    hsucc.add hneg
  simpa only [singularDirExponent, sub_eq_add_neg] using this

/-- **`λ_i` is `μ`-a.e. a real constant `Γ_{i+1}⁺ − Γ_i⁺`.** For an ergodic measure-preserving `T`
and a possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹`, both cumulative exponents are
`μ`-a.e. real constants (`ae_forwardSingularExponent_eq_coe`); on their common a.e. set the
`EReal` difference is the coercion of the real difference (`EReal.coe_sub`).  In particular `λ_i`
is `μ`-a.e. an a.e.-**constant** finite real, with no `⊤ − ⊤`/`⊥ − ⊥` indeterminacy. -/
theorem ae_singularDirExponent_eq_coe [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (i : ℕ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ, singularDirExponent A T i x = (lam : EReal) := by
  obtain ⟨gsucc, hgsucc⟩ := ae_forwardSingularExponent_eq_coe hT hAmeas hint (i + 1)
  obtain ⟨gcur, hgcur⟩ := ae_forwardSingularExponent_eq_coe hT hAmeas hint i
  refine ⟨gsucc - gcur, ?_⟩
  filter_upwards [hgsucc, hgcur] with x hx hy
  rw [singularDirExponent, hx, hy, ← EReal.coe_sub]

/-- **`λ_i < ⊤` `μ`-a.e.** Since `λ_i` `μ`-a.e. equals a real coercion
(`ae_singularDirExponent_eq_coe`), it is `μ`-a.e. strictly below `⊤`. -/
theorem ae_singularDirExponent_lt_top [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (i : ℕ) :
    ∀ᵐ x ∂μ, singularDirExponent A T i x < ⊤ := by
  obtain ⟨lam, hlam⟩ := ae_singularDirExponent_eq_coe hT hAmeas hint i
  filter_upwards [hlam] with x hx
  rw [hx]; exact EReal.coe_lt_top lam

/-- **`⊥ < λ_i` `μ`-a.e.** Since `λ_i` `μ`-a.e. equals a real coercion
(`ae_singularDirExponent_eq_coe`), it is `μ`-a.e. strictly above `⊥`. -/
theorem ae_singularDirExponent_ne_bot [IsProbabilityMeasure μ] [NeZero d] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (i : ℕ) :
    ∀ᵐ x ∂μ, ⊥ < singularDirExponent A T i x := by
  obtain ⟨lam, hlam⟩ := ae_singularDirExponent_eq_coe hT hAmeas hint i
  filter_upwards [hlam] with x hx
  rw [hx]; exact EReal.bot_lt_coe lam

end ErgodicTheory
