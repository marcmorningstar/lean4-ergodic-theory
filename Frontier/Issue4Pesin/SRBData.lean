/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.Ruelle.MargulisRuelleSharp

/-!
# Pesin's entropy formula, part 1: the SRB / Pesin data interface

This is the first of three modules assembling **Pesin's entropy formula**
`h_μ(T) = ∫ (∑_i λ_i⁺) dμ` for a smooth ergodic self-map `T` preserving an SRB (e.g. volume /
Lebesgue) measure, as the natural completion of the Margulis–Ruelle *inequality*
`h_μ(T) ≤ ∫ ∑_i λ_i⁺ dμ` already proved sorry-free in `Oseledets.margulisRuelle_sharp`.

The equality `=` is `≤` (Ruelle, done) together with the **hard reverse inequality**
`∑_i λ_i⁺ ≤ h_μ(T)`, which holds **exactly for SRB measures** (Ledrappier–Strelcyn–Young: the
entropy formula holds iff `μ` has absolutely continuous conditional measures on unstable
manifolds — Contractor §8, Theorem 8.1). The reverse inequality is the genuinely research-scale
content: it requires Pesin theory (Lyapunov charts, the measurable `Eˢ ⊕ Eᵘ` splitting), the
absolute continuity of the unstable foliation / its holonomy, and the unstable-Jacobian volume
estimate. None of this exists in Mathlib. This module **names each missing piece as an explicit
`Prop`-valued interface** so the downstream statements are honestly typed; the geometric content
of each interface is a documented `BLOCKED` leaf (Mathlib-scale Pesin / Ledrappier–Young theory).

## The shape of the missing theory (Contractor §7, Mañé's proof of Theorem 7.15)

Following Mañé's proof of the reverse inequality (Contractor *The Pesin Entropy Formula*, §7,
Theorem 7.15), the geometric inputs split into:

* **The hyperbolic splitting `T_xM = Eˢ(x) ⊕ Eᵘ(x)`** of Pesin theory — a measurable, a.e.-defined,
  `Df`-invariant decomposition of the tangent space into the contracting (non-positive exponent)
  and expanding (positive exponent) subspaces, continuous on a positive-measure Pesin block `K`
  (Contractor §5, §7 around (7.9)). Here `PesinSplitting` packages the *data* of the unstable
  subspace assignment together with the unstable-Jacobian growth rate it must satisfy.

* **The unstable Jacobian = positive-exponent sum**, `log|det (D_xT)|Eᵘ(x)| → ∑ λ_i⁺` along the
  orbit (Contractor (7.9)(3): `log|det(D_xg^n)|Eᵘ| ≥ N(χ(x) − ε)n`). Here `χ(x) = ∑_i λ_i⁺(x)`,
  the integrand of Pesin's formula. Packaged as `UnstableJacobianRate`.

* **The SRB / absolute-continuity property** — `μ` has absolutely continuous conditional measures
  on unstable manifolds (Contractor §8, Definition 8.2). This is what links the reference
  (Lebesgue) volume on unstable leaves, whose growth rate is the unstable Jacobian, back to `μ`,
  closing Mañé's lower bound `h_μ(g) ≥ ∫ h_ν(g,ρ,x) dμ` (Proposition 7.7). Packaged as
  `SRBProperty`.

## Main definitions

* `Frontier.Issue4Pesin.UnstableJacobianRate` — the geometric integrand identity
  `χ(x) = ∑_i λ_i⁺` realized as the a.e. orbit growth rate of the unstable Jacobian.
* `Frontier.Issue4Pesin.SRBProperty` — the SRB property: absolute continuity of `μ` along
  unstable manifolds (the Ledrappier–Strelcyn–Young characterization).

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7 (Theorem 7.15), §8.
* F. Ledrappier, J.-M. Strelcyn, *A proof of the estimation from below in Pesin's entropy formula*,
  Ergodic Theory Dynam. Systems **2** (1982) 203–219.
* F. Ledrappier, L.-S. Young, *The metric entropy of diffeomorphisms I, II*, Ann. of Math. **122**
  (1985) 509–539, 540–574.
* Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math.
  Surveys **32** (1977) 55–114.
-/

open MeasureTheory Filter Topology

namespace Frontier.Issue4Pesin

variable {d : ℕ} [NeZero d]

/-- **The unstable-Jacobian growth rate, equal to the positive-exponent sum.**

For an ergodic differentiable self-map `T` of `EuclideanSpace ℝ (Fin d)` with nonsingular,
log-integrable derivative cocycle, this is the `Prop`-valued packaging of Contractor (7.9)(3): the
integrand `χ(x)` of Pesin's formula is the a.e. orbit growth rate of the **unstable Jacobian**
`log|det (D_x T^[n])|Eᵘ(x)|`, and equals the deterministic positive-exponent sum
`∑_i λ_i⁺ = sumPosExp`.

Concretely, `UnstableJacobianRate T χ` asserts that the candidate integrand `χ : … → ℝ` is
`μ`-a.e. equal to the constant `sumPosExp`. (Since the spectrum is ergodic, `∑ λ_i⁺` is
a.e.-constant — `Oseledets.sumPosExp` is exactly that constant — so the integrand is a.e. the
constant `sumPosExp`; the genuinely geometric content is that `χ` *is* the unstable-Jacobian rate,
which is recorded by whoever supplies this interface from Pesin theory.)

This is the bridge object: `∫ χ dμ = sumPosExp` (a probability measure integrates a constant to
itself), so the equality `h_μ(T) = ∫ χ dμ` reduces to `h_μ(T) = sumPosExp`.

`BLOCKED`: the identification of `χ` with the unstable-Jacobian rate requires the Pesin splitting
`Eᵘ(x)` and the multiplicative ergodic theorem applied to `det|Eᵘ` — Mathlib has neither the
measurable Pesin splitting nor the restricted-determinant cocycle. It is supplied here as an
interface, not proved. -/
def UnstableJacobianRate {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (Oseledets.derivativeCocycle T x).det ≠ 0)
    (hint : Oseledets.IntegrableLogNorm (Oseledets.derivativeCocycle T) μ)
    (hint' : Oseledets.IntegrableLogNorm (fun x => (Oseledets.derivativeCocycle T x)⁻¹) μ)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ᵐ x ∂μ, χ x = Oseledets.sumPosExp hT hdet
    (Oseledets.measurable_derivativeCocycle T) hint hint'

/-- **Absolutely continuous conditional measures on unstable manifolds — an opaque marker.**

This is the Ledrappier–Strelcyn–Young SRB condition (Contractor §8, Theorem 8.1, Definition 8.2):
`μ` has conditional measures on the unstable manifolds `Wᵘ(x)` that are absolutely continuous with
respect to the leaf (Lebesgue / Riemannian volume) measure. It is exposed here as an **`opaque`
constant** — neither provable nor refutable inside the current library — and that opacity is the
honest state of the art, for two reasons.

* A *faithful* statement needs three Mathlib-absent objects: the unstable foliation `Wᵘ`
  (integrating the measurable distribution `Eᵘ`, i.e. Pesin's stable/unstable manifold theorem),
  the disintegration of `μ` along *that specific* foliation, and the leaf Riemannian-volume measure.

* The condition cannot be salvaged by an *existential* over an arbitrary measurable factor
  `π : E → E` and reference kernel `η`. Such an existential self-trivialises: with `π` constant the
  conditional distribution is `μ` itself and one may take `η := μ`; with `π = id` the conditionals
  are Dirac measures, trivially absolutely continuous. So `∃ π η, …` would hold for *every* measure
  and carry no SRB content. The condition is genuine *only* for the actual geometric unstable
  foliation, which does not yet exist in Mathlib.

`BLOCKED`: replacing this opaque marker by the real absolute-continuity statement needs the Pesin
unstable manifold theorem, the leaf-volume measure, and the disintegration of `μ` along `Wᵘ`. -/
opaque ACConditionalsUnstable (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop

/-- **The SRB property**: `μ` has absolutely continuous conditional measures on the unstable
manifolds of `T` — the Ledrappier–Strelcyn–Young condition that *upgrades* the Margulis–Ruelle
inequality `h_μ(T) ≤ ∑ λ_i⁺` to Pesin's equality (the formula holds **iff** `μ` has this property).

A genuine, **non-vacuous** hypothesis: its sole field is the opaque, currently-undischargeable
`ACConditionalsUnstable T μ`, so `SRBProperty T μ` cannot be discharged by `trivial`/`⟨⟩`.

History (both prior versions were vacuous): the field was first `acConditionalUnstable : True`
(provable by `⟨trivial⟩`); a second attempt used `∃ π η, Kernel.singularPart (condDistrib id π μ)
η = 0`, which is *also* satisfied by every `μ` (take `η := condDistrib id π μ`, or `π` constant and
`η := μ`). The `opaque` marker is the honest fix. Do **not** confuse with `μ ≪ volume`: a genuine
SRB measure is typically *singular* w.r.t. ambient volume (it lives on a fractal attractor); the
content is absolute continuity of the conditionals *on leaves*. The expanding / volume-preserving
case (whole space a single unstable leaf) is the one special case where it reduces to `μ ≪ volume`,
and the expanding track states *that* directly and honestly, without this interface. -/
structure SRBProperty (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop where
  /-- **BLOCKED**: `μ` has absolutely continuous conditional measures on the unstable manifolds of
  `T`, held as the opaque `ACConditionalsUnstable T μ` (which the absent Pesin unstable foliation +
  leaf disintegration would discharge). Keeping it opaque makes this field — and hence
  `SRBProperty` — a genuine, non-trivially-dischargeable hypothesis. -/
  acConditionalUnstable : ACConditionalsUnstable T μ

end Frontier.Issue4Pesin
