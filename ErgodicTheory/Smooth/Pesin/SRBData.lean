/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.Ruelle.MargulisRuelleSharp

/-!
# Pesin's entropy formula, part 1: the SRB data interface (volume case)

This is the first of the three-module **Pesin-entropy-formula chain** — the migrated and
**discharged** issue-#10 reverse inequality — completing the Margulis–Ruelle inequality
`h_μ(T) ≤ ∑_i λ_i⁺` (already proved sorry-free in `ErgodicTheory.margulisRuelle_sharp`) to Pesin's
*equality* `h_μ(T) = ∑_i λ_i⁺`.

```
  SRBData          (this file)  — the SRB hypothesis + the unstable-Jacobian bridge object
  ManeLowerBound                — Rokhlin's inequality ⇒ the reverse leaf  ∑ λ⁺ ≤ h_μ(T)
  PesinFormula                  — le_antisymm capstone:  h_μ(T) = ∑ λ⁺ = ∫ ∑ λ⁺ dμ
```

## What "SRB, volume case" means here — the honest story

Pesin's formula holds **exactly for SRB measures**: those whose conditional measures on unstable
manifolds are absolutely continuous with respect to the leaf (Lebesgue / Riemannian) volume
(Ledrappier–Strelcyn–Young). In full generality that condition is **not stateable in Mathlib**: it
needs the Pesin unstable-manifold theorem (integrating the measurable distribution `Eᵘ` into the
foliation `Wᵘ`), the disintegration of `μ` along *that specific* foliation, and the leaf-volume
measure — none of which exist in the library.

This chain formalizes the **volume case**: the situation in which the *whole space is a single
unstable leaf*, so the Ledrappier–Strelcyn–Young condition collapses to the honest, first-order
statement `μ ≪ volume`. Accordingly `SRBProperty` here carries the single field
`absolutelyContinuous : μ ≪ volume`. This is the largest fragment of the SRB condition expressible
without the Mathlib-absent Pesin foliation machinery, and — crucially — it is *consumable*: the
downstream reverse inequality is proved from it, sorry-free, via Rokhlin's inequality.

### History of the SRB interface on issue #10 (why the volume case is the honest rescope)

Three earlier framings of `SRBProperty` were all defective, and are recorded here so the rescope is
auditable (see the issue-#10 record):

* `acConditionalUnstable : True` — vacuous; dischargeable by `⟨trivial⟩`, so it carried no content.
* `∃ π η, Kernel.singularPart (condDistrib id π μ) η = 0` — *also* vacuous; satisfied by **every**
  `μ` (take `η := condDistrib id π μ`, or `π` constant and `η := μ`), because an existential over an
  arbitrary measurable factor self-trivialises. The SRB content lives only in the *actual geometric*
  unstable foliation.
* `opaque ACConditionalsUnstable T μ` — honest (neither provable nor refutable) but *unconsumable*:
  an opaque marker cannot feed any proof, so the reverse inequality remained a documented `BLOCKED`
  leaf rather than a theorem.

The volume case `μ ≪ volume` is the honest fix that is *both* genuine (non-vacuously dischargeable —
`volume ≪ volume` is a witness, but a Dirac mass is **not** `≪ volume`) *and* consumable (the
reverse inequality is a real theorem, `ManeLowerBound.sumPosExp_le_ksEntropy_of_SRB`). A general
(fractal-attractor) SRB measure is typically *singular* w.r.t. ambient volume — its content is
absolute continuity of the conditionals *on leaves* — so `μ ≪ volume` is not the general SRB
condition; it is exactly its volume-case specialization, and that is disclosed throughout.

## Main definitions

* `ErgodicTheory.SRBProperty` — the volume-case SRB property `μ ≪ volume`.
* `ErgodicTheory.UnstableJacobianRate` — the bridge object: the Pesin integrand `χ` is `μ`-a.e.
  equal to the a.e.-constant positive-exponent sum `sumPosExp`, so `∫ χ dμ = sumPosExp`.

## References

* V. A. Rokhlin, *Lectures on the entropy theory of measure-preserving transformations*, Russian
  Math. Surveys **22** (1967), no. 5, 1–52, §9.
* Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math.
  Surveys **32** (1977) 55–114.
* F. Ledrappier, J.-M. Strelcyn, *A proof of the estimation from below in Pesin's entropy formula*,
  Ergodic Theory Dynam. Systems **2** (1982) 203–219.
* F. Ledrappier, L.-S. Young, *The metric entropy of diffeomorphisms I*, Ann. of Math. **122**
  (1985) 509–539.
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory

variable {d : ℕ}

/-! ## The SRB property (volume case) -/

/-- **The SRB property, volume case.** `μ` is absolutely continuous with respect to ambient
Lebesgue volume, `μ ≪ volume`.

This is the volume-case specialization of the Ledrappier–Strelcyn–Young SRB condition (absolute
continuity of `μ`'s conditional measures on unstable manifolds): when the whole space is a single
unstable leaf the leaf volume *is* ambient volume, and the condition collapses to `μ ≪ volume`.
See the module docstring for why this — rather than the vacuous `True`/existential framings or the
unconsumable opaque marker — is the honest, consumable interface. It is a genuine, non-vacuous
hypothesis: a Dirac mass is not `≪ volume`. -/
structure SRBProperty (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop where
  /-- The measure is absolutely continuous with respect to ambient Lebesgue volume. -/
  absolutelyContinuous : μ ≪ volume

/-- Satisfiability: `SRBProperty` is inhabited — here by the trivial `volume ≪ volume` witness — so
the structure is a genuine, non-vacuous, dischargeable hypothesis (unlike the historical `True` /
existential framings, which were satisfied by *every* measure). -/
example : SRBProperty (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) volume :=
  ⟨Measure.AbsolutelyContinuous.rfl⟩

/-! ## The unstable-Jacobian bridge object -/

section Bridge

variable [NeZero d]

/-- **The unstable-Jacobian growth rate, equal to the positive-exponent sum.**

For an ergodic differentiable self-map `T` of `EuclideanSpace ℝ (Fin d)` with nonsingular,
log-integrable derivative cocycle, this is the `Prop`-valued packaging of the Pesin integrand
identity: the integrand `χ(x)` of Pesin's formula is the a.e. orbit growth rate of the **unstable
Jacobian** `log|det (D_x T^[n])|Eᵘ(x)|`, and equals the deterministic positive-exponent sum
`∑_i λ_i⁺ = sumPosExp`.

Concretely, `UnstableJacobianRate hT hdet hint hint' χ` asserts that the candidate integrand
`χ : … → ℝ` is `μ`-a.e. equal to the constant `sumPosExp`. Since the spectrum is ergodic, `∑ λ_i⁺`
is a.e.-constant (`ErgodicTheory.sumPosExp` is exactly that constant), so the integrand is a.e. the
constant `sumPosExp`; the genuinely geometric content — that `χ` *is* the unstable-Jacobian rate —
is recorded by whoever supplies this interface from Pesin theory.

This is the bridge object powering the integral form of Pesin's formula: `∫ χ dμ = sumPosExp` (a
probability measure integrates the a.e.-constant `χ` to itself), so the equality `h_μ(T) = ∫ χ dμ`
reduces to the spectral `h_μ(T) = sumPosExp`. In the **volume case** of this chain the reverse
inequality is proved *without* this interface (it goes through Rokhlin's inequality directly); the
object is retained only to phrase the integral form `pesin_entropy_formula` as the literal
`h_μ(T) = ∫ ∑ λ_i⁺ dμ`. -/
def UnstableJacobianRate {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (derivativeCocycle T x).det ≠ 0)
    (hint : IntegrableLogNorm (derivativeCocycle T) μ)
    (hint' : IntegrableLogNorm (fun x => (derivativeCocycle T x)⁻¹) μ)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ᵐ x ∂μ, χ x = sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint'

end Bridge

end ErgodicTheory
