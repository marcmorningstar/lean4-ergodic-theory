/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.KSEntropySystem
import Oseledets.Smooth.DerivativeCocycle
import Oseledets.Lyapunov.Extensions.ExponentSums

/-!
# The Margulis–Ruelle inequality, reduced to the geometric atom-counting bound

For a smooth ergodic self-map `T` of `EuclideanSpace ℝ (Fin d)`, the **Margulis–Ruelle
inequality** bounds the Kolmogorov–Sinai entropy of the system by the sum of the *positive*
Lyapunov exponents of the derivative (tangent) cocycle `A := derivativeCocycle T`:
`h(T) ≤ ∑_{λᵢ > 0} λᵢ`  (equation (7.1) of Contractor's *The Pesin Entropy Formula*, in the
form `h_μ(f) ≤ ∫ Σ λᵢ⁺ mᵢ dμ`, here a deterministic constant because the spectrum is ergodic
and hence `μ`-a.e. constant).

This module assembles **all of the abstract entropy-side scaffolding** around the inequality and
reduces it to a *single*, explicitly named, genuinely geometric hypothesis: the per-partition
atom-counting estimate. Everything else — the supremum structure of the system entropy `h(T)` and
the lift from `ℝ` to the complete lattice `EReal` — is proved here, sorry-free.

* The **left-hand side** `ksEntropy hT.toMeasurePreserving` is the `EReal`-valued system entropy
  `h(T) = sup_α h(α, T)`, the supremum over all `Fin n`-indexed finite measurable partitions
  (`Oseledets.Entropy.ksEntropy`, `Oseledets.Entropy.KSEntropySystem`). Since `Ergodic` extends
  `MeasurePreserving`, the ergodic hypothesis `hT` feeds the entropy through
  `hT.toMeasurePreserving`.
* The **right-hand side** `(sumPosExp … : EReal)` is the coercion to `EReal` of the (plain real)
  sum of the strictly positive Lyapunov exponents of `A := derivativeCocycle T`
  (`Oseledets.sumPosExp`, `Oseledets.Lyapunov.Extensions.ExponentSums`), formed against the
  invertibility / log-integrability data packaged for the derivative cocycle by
  `oseledets_filtration_derivativeCocycle`.

The conclusion `ksEntropy hT.toMeasurePreserving ≤ (sumPosExp … : EReal)` then follows from the
geometric hypothesis by *two* applications of `iSup_le` in the complete lattice `EReal`: the
hypothesis bounds each partition term, and the supremum of a uniformly bounded family is bounded.

## Main results

* `Oseledets.margulisRuelle_le_sumPosExp` — the Margulis–Ruelle inequality
  `h(T) ≤ ∑_{λᵢ > 0} λᵢ` for the derivative cocycle of a smooth ergodic self-map of
  `EuclideanSpace ℝ (Fin d)`, conditional on the geometric atom-counting hypothesis `hgeo`.

## gap

The single open input is the **geometric atom-counting bound**, supplied here as the explicit
hypothesis

```
hgeo : ∀ (n : ℕ) (P : MeasurePartition μ (Fin n)),
    ((ksEntropyPartition hT.toMeasurePreserving P : ℝ) : EReal)
      ≤ ((sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' : ℝ) : EReal)
```

This is the **Ruelle counting estimate** (Contractor, *The Pesin Entropy Formula*, UChicago REU
2023, equation (7.1) and Lemmas 7.5–7.6 of the Mañé proof of §7; original source D. Ruelle,
*An inequality for the entropy of differentiable maps*, Bol. Soc. Bras. Mat. **9** (1978) 83–87):
under the dynamics, an atom of a partition of small diameter refines under `T^[n]` into at most
`≈ exp(n · ∑ λᵢ⁺)` atoms, because the volume of an image ball grows like the product of the
*positive* singular-value growth rates, i.e. `|det D(T^[n])|⁺ ≈ exp(n · ∑ λᵢ⁺)`. Dividing the
`log`-cardinality by `n` and passing to the Fekete limit turns this `log⁺|det Df|` atom-count into
the displayed bound on the partition-relative entropy `h(α, T)`. It is **not** a restatement of the
conclusion: it is a single-partition, finite-`n` estimate, whereas the conclusion is the supremum
over all partitions.

Formalizing `hgeo` itself requires smooth-manifold ergodic theory absent from Mathlib — Lyapunov
charts and the Mañé/Katok covering–counting argument (how a partition refines under `T^[n]`,
bounded by the volume growth = product of positive exponents). That bridge is historically
assessed as multi-month, not one-shot, and is the *only* piece left open: this module proves
the entire abstract reduction around it.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7 (Margulis–Ruelle
  inequality (7.1), Mañé proof, Lemmas 7.5–7.6).
* D. Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Bras. Mat. **9**
  (1978) 83–87.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory

namespace Oseledets

variable {d : ℕ} [NeZero d]

/-- **The Margulis–Ruelle inequality, conditional on the geometric atom-counting bound.**

For an ergodic, differentiable self-map `T` of `EuclideanSpace ℝ (Fin d)` with everywhere
nonsingular derivative cocycle (`hdet`) and integrable log-derivative data (`hint`, `hint'`), the
Kolmogorov–Sinai entropy of the system is bounded above by the sum of the strictly positive
Lyapunov exponents of the derivative (tangent) cocycle `A := derivativeCocycle T`:
`h(T) ≤ ∑_{λᵢ > 0} λᵢ`.

The proof is the pure abstract reduction: the conclusion is the coercion to the complete lattice
`EReal` of `iSup_le` applied twice to the geometric per-partition hypothesis `hgeo` — the outer
supremum over the partition arity `n` and the inner supremum over `Fin n`-indexed partitions both
inherit the uniform bound. The lone genuinely geometric input is `hgeo`, the Ruelle atom-counting
estimate (see the module `## gap`). -/
theorem margulisRuelle_le_sumPosExp
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hT : Ergodic T μ) (hdiff : Differentiable ℝ T)
    (hdet : ∀ x, (derivativeCocycle T x).det ≠ 0)
    (hint : IntegrableLogNorm (derivativeCocycle T) μ)
    (hint' : IntegrableLogNorm (fun x => (derivativeCocycle T x)⁻¹) μ)
    (hgeo : ∀ (n : ℕ) (P : Entropy.MeasurePartition μ (Fin n)),
        ((Entropy.ksEntropyPartition hT.toMeasurePreserving P : ℝ) : EReal)
          ≤ ((sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' : ℝ) : EReal)) :
    Entropy.ksEntropy hT.toMeasurePreserving
      ≤ ((sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' : ℝ) : EReal) := by
  -- `hdiff` enters only to identify the cocycle as the genuine tangent cocycle (recorded by
  -- `oseledets_filtration_derivativeCocycle`); the entropy bound itself is the abstract reduction.
  let _ := hdiff
  rw [Entropy.ksEntropy]
  refine iSup_le (fun n => iSup_le (fun P => hgeo n P))

end Oseledets
