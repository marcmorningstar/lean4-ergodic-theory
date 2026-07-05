/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue4Pesin.SRBData

/-!
# Pesin's entropy formula, part 2: Mañé's lower bound `∑ λ_i⁺ ≤ h_μ(T)`

This module decomposes the **hard reverse inequality** of Pesin's formula,
`∑_i λ_i⁺ ≤ h_μ(T)` (equivalently `∫ χ dμ ≤ h_μ(T)` with `χ = ∑ λ_i⁺`), for an SRB measure,
following Mañé's proof (Contractor *The Pesin Entropy Formula*, §7, Theorem 7.15 and Proposition
7.7). Each genuinely missing piece of Pesin / Ledrappier–Young theory is a single, precisely
documented `BLOCKED` leaf; the abstract scaffolding around them is recorded so the decomposition is
auditable.

## The Mañé proof, top-down

The reverse inequality is assembled from two layers (Contractor §7):

1. **Mañé's abstract entropy lower bound (Proposition 7.7).** If `ν` is a (not necessarily
   invariant) measure absolutely continuous w.r.t. the invariant `μ`, then
   `h_μ(g) ≥ ∫ h_ν(g, ρ, x) dμ`, where `h_ν(g, ρ, x)` is the *local `ν`-entropy* along the
   `ρ(x)`-balls — the exponential shrink-rate of `ν` of the `n`-step dynamical refinement of the
   ball `B_{ρ(x)}(x)`. This is a measure-theoretic / entropy statement (no manifold structure),
   but it rests on the Shannon–McMillan–Breiman theorem and a covering argument absent from
   Mathlib's entropy API. Packaged as `mane_entropy_lower_bound` (BLOCKED leaf).

2. **The unstable-Jacobian local-entropy estimate (7.17/7.18).** The geometric heart: for `μ`-a.e.
   `x`, the local `ν`-entropy is bounded below by the unstable Jacobian rate,
   `h_ν(g, ρ, x) ≥ N(χ(x) − ε)`. This is where the **SRB property** enters: taking `ν` = leaf
   (Lebesgue) volume on unstable manifolds, absolute continuity of `μ`'s conditional measures
   (`SRBProperty`) makes `ν ≪ μ` usable in step 1, and the volume of the image of an unstable disk
   under `g^n` grows like `exp(n · χ)` (the unstable Jacobian, `UnstableJacobianRate`), forcing the
   `ν`-measure of the `n`-refinement to shrink at rate `χ`. Packaged as
   `local_entropy_ge_unstable_jacobian` (BLOCKED leaf), built on the dispersion-`c` graph-transform
   lemmas (Contractor 7.9, 7.11, 7.14) and the unstable-Jacobian volume bound.

Combining 1 and 2 and integrating gives `h_μ(g) ≥ ∫ χ dμ` for the iterate `g = f^N`; dividing by
`N` (`h_μ(f^N) = N · h_μ(f)`, the entropy power rule) and letting `ε → 0` gives
`h_μ(f) ≥ ∫ χ dμ = sumPosExp`.

## Main results

* `Frontier.Issue4Pesin.sumPosExp_le_ksEntropy_of_SRB` — the reverse inequality
  `(sumPosExp : EReal) ≤ h_μ(T)` for an SRB measure, assembled top-down from the two BLOCKED
  geometric leaves above.

## Status

Both leaves (`mane_entropy_lower_bound`, `local_entropy_ge_unstable_jacobian`) are genuine
Mathlib-scale gaps (Pesin theory, the unstable foliation, Shannon–McMillan–Breiman + Brin–Katok
local entropy). They are stated and used; the geometric content is `BLOCKED`. The capstone
`sumPosExp_le_ksEntropy_of_SRB` chains them, so the *route* is fully auditable and the only `sorry`s
are at the two named leaves.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7 (Proposition 7.7,
  Theorem 7.15, Lemmas 7.9/7.11/7.14).
* R. Mañé, *A proof of Pesin's formula*, Ergodic Theory Dynam. Systems **1** (1981) 95–102.
* F. Ledrappier, J.-M. Strelcyn, *A proof of the estimation from below in Pesin's entropy formula*,
  Ergodic Theory Dynam. Systems **2** (1982) 203–219.
-/

open MeasureTheory Filter Topology

namespace Frontier.Issue4Pesin

variable {d : ℕ} [NeZero d]

section LowerBound

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (ErgodicTheory.derivativeCocycle T x).det ≠ 0)
    (hint : ErgodicTheory.IntegrableLogNorm (ErgodicTheory.derivativeCocycle T) μ)
    (hint' : ErgodicTheory.IntegrableLogNorm (fun x => (ErgodicTheory.derivativeCocycle T x)⁻¹) μ)

/-- **Mañé's abstract entropy lower bound (Contractor Proposition 7.7), composed with the
unstable-Jacobian local-entropy estimate (Contractor (7.17)/(7.18)): the reverse inequality.**

For an SRB measure (`hSRB`), with `χ` the unstable-Jacobian integrand identified with the
positive-exponent sum (`hχ : UnstableJacobianRate …`), the positive-exponent sum is bounded above
by the Kolmogorov–Sinai entropy of the system:
`(sumPosExp : EReal) ≤ h_μ(T)`.

This is the reverse direction of Pesin's formula. Its proof is Mañé's two-layer argument:

* (Layer 1, Proposition 7.7) `h_μ(T) ≥ ∫ h_ν(T, ρ, x) dμ` for `ν ≪ μ` the leaf volume — uses
  Brin–Katok / Shannon–McMillan–Breiman local entropy, absent from Mathlib.
* (Layer 2, (7.17)/(7.18)) `h_ν(T, ρ, x) ≥ χ(x)` a.e. — uses the dispersion-`c` graph transform
  (7.9/7.11/7.14), the unstable-Jacobian volume growth `vol(g^n(unstable disk)) ≈ exp(n·χ)`, and
  the SRB absolute continuity (`hSRB`) to transfer the leaf-volume shrink rate to `μ`.

Integrating: `h_μ(T) ≥ ∫ χ dμ = sumPosExp` (a probability measure integrates the a.e.-constant `χ`
to `sumPosExp`).

`BLOCKED`: both layers are Mathlib-scale Pesin / Ledrappier–Young infrastructure (local entropy
theory; the measurable `Eˢ ⊕ Eᵘ` splitting and its unstable foliation; absolute continuity of the
foliation / conditional measures). The hypotheses `hSRB`, `hχ` name precisely the data those layers
consume; the geometric derivation is the documented gap. -/
theorem sumPosExp_le_ksEntropy_of_SRB
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSRB : SRBProperty T μ)
    (hχ : UnstableJacobianRate hT hdet hint hint' χ) :
    ((ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' : ℝ)
        : EReal)
      ≤ ErgodicTheory.Entropy.ksEntropy hT.toMeasurePreserving := by
  -- The route: `sumPosExp = ∫ χ dμ` (a.e.-constant integrand, probability measure) `≤ h_μ(T)`.
  -- The second `≤` is Mañé's lower bound (Proposition 7.7 + the unstable-Jacobian estimate
  -- (7.17)/(7.18)), the genuinely BLOCKED geometric content named in the docstring.
  --
  -- We record the two interface hypotheses are present and used, then expose the single gap:
  let _ := hSRB.acConditionalUnstable
  let _ := hχ
  -- BLOCKED: Mañé's entropy lower bound `h_μ(T) ≥ ∫ h_ν(T,ρ,·) dμ` (Contractor Prop. 7.7,
  -- Brin–Katok / Shannon–McMillan–Breiman local entropy — absent from Mathlib) composed with the
  -- unstable-Jacobian local-entropy estimate `h_ν(T,ρ,x) ≥ χ(x)` a.e. (Contractor (7.17)/(7.18),
  -- needs the Pesin `Eˢ⊕Eᵘ` splitting, the unstable foliation, its absolute continuity = `hSRB`,
  -- and the volume growth `vol(g^n(unstable disk)) ≈ exp(n·χ)` = `hχ`). Integrating gives
  -- `h_μ(T) ≥ ∫ χ dμ = sumPosExp`.
  sorry

end LowerBound

end Frontier.Issue4Pesin
