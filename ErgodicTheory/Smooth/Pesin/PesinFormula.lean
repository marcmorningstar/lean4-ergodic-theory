/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Smooth.Pesin.ManeLowerBound

/-!
# Pesin's entropy formula `h_μ(T) = ∫ ∑ λ_i⁺ dμ` (capstone, volume case)

This is the capstone of the three-module Pesin-entropy-formula chain — the migrated and
**discharged** issue-#10 formula — for a smooth ergodic self-map `T` of `EuclideanSpace ℝ (Fin d)`
preserving an SRB (volume-case) measure `μ`:

`h_μ(T) = ∑_i λ_i⁺ = ∫ (∑_i λ_i⁺) dμ`

(the last equality because the spectrum is ergodic, so the integrand is a.e. the constant
`sumPosExp`, which a probability measure integrates to itself).

It assembles the two directions by `le_antisymm`:

* **`≤` (Margulis–Ruelle, DONE).** `h_μ(T) ≤ ∑_i λ_i⁺` is `ErgodicTheory.margulisRuelle_sharp`,
  proved sorry-free modulo the honest non-compactness atom-count input `hgeo`. This direction holds
  for *every* invariant measure — no SRB hypothesis.
* **`≥` (Rokhlin, volume case).** `∑_i λ_i⁺ ≤ h_μ(T)` is
  `ErgodicTheory.sumPosExp_le_ksEntropy_of_SRB`, the reverse inequality discharged in
  `ManeLowerBound` via **Rokhlin's inequality** in the volume case `μ ≪ volume` with nonnegative
  spectrum (`hspec`). The general mixed-spectrum reverse inequality remains the documented
  Ledrappier–Young wall.

The equality is stated in both the clean spectral form `h_μ(T) = (sumPosExp : EReal)`
(`pesin_entropy_formula_spectral`) and the genuine Pesin integral form `h_μ(T) = (∫ χ dμ : EReal)`
(`pesin_entropy_formula`), the two identified by the a.e.-constancy of the integrand `χ`
(`UnstableJacobianRate`).

## Vacuity disclosure (honest, mirroring `pesin_formula_expanding`)

Like `ErgodicTheory.pesin_formula_expanding`, these are correct *implications* whose **joint
hypothesis bundle has no known model on the non-compact space `EuclideanSpace ℝ (Fin d) = ℝ^d`**.
The bundle asks for an *ergodic*, *absolutely continuous probability* (`μ ≪ volume`),
*everywhere-nonsingular* map with *no negative Lyapunov exponents* (`hspec`). On `ℝ^d` these clash:
a map with all exponents `≥ 0` expands volume on average, which on a non-compact space forces
mass to escape to infinity, incompatible with an a.c. invariant *probability* measure — empty for
`d = 1`. So the EuclideanSpace statements are (as far as is known) vacuously true assemblies of the
implication, not exhibited instances.

The genuinely *witnessed* Pesin/Rokhlin equality lives on the **compact circle**: see
`ErgodicTheory.Examples.Rokhlin.rokhlin_equality_doublingMap`
(`h = ∫ log|det DT| dμ = log 2` for the doubling map) and the companion
`ErgodicTheory.Examples.Rokhlin.pesin_formula_doublingMap` (the spectral `h = ∑ λ⁺ = log 2`). A
non-vacuous EuclideanSpace-style instance would require porting the derivative-cocycle / Lyapunov
layer to the torus (currently `EuclideanSpace`-only).

## Main results

* `ErgodicTheory.pesin_entropy_formula_spectral` — Pesin's formula, spectral form
  `h_μ(T) = (∑_i λ_i⁺ : EReal)`.
* `ErgodicTheory.pesin_entropy_formula` — Pesin's formula, integral form
  `h_μ(T) = (∫ χ dμ : EReal)` = the literal `h_μ(T) = ∫ ∑ λ_i⁺ dμ`.

## Status of the chain

Both directions are sorry-free in the **volume case**. The `≤` half is
`ErgodicTheory.margulisRuelle_sharp` (modulo its honest atom-count hypothesis `hgeo`); the `≥` half
is `ErgodicTheory.sumPosExp_le_ksEntropy_of_SRB` (Rokhlin's inequality + nonnegative spectrum). No
`BLOCKED` leaf remains in the volume case. The general mixed-spectrum SRB reverse inequality
(absolute continuity of conditional measures on genuine unstable manifolds) is the remaining
Mathlib-scale wall, documented in `SRBData` and `ManeLowerBound`.

## References

* V. A. Rokhlin, *Lectures on the entropy theory of measure-preserving transformations*, Russian
  Math. Surveys **22** (1967), no. 5, 1–52, §9.
* Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math.
  Surveys **32** (1977) 55–114.
* R. Mañé, *A proof of Pesin's formula*, Ergodic Theory Dynam. Systems **1** (1981) 95–102.
* F. Ledrappier, L.-S. Young, *The metric entropy of diffeomorphisms I*, Ann. of Math. **122**
  (1985) 509–539.
* Y. Coudène, *Ergodic Theory and Dynamical Systems*, Universitext, Springer, 2016, Ch. 12,
  Cor. 12.1.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ErgodicTheory

open ErgodicTheory.Entropy

variable {d : ℕ} [NeZero d]

section Pesin

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {m : ℕ} (hT : Ergodic T μ)
    (hdet : ∀ x, (derivativeCocycle T x).det ≠ 0)
    (hint : IntegrableLogNorm (derivativeCocycle T) μ)
    (hint' : IntegrableLogNorm (fun x => (derivativeCocycle T x)⁻¹) μ)

/-- **Pesin's entropy formula, spectral form (volume case).** `h_μ(T) = ∑_i λ_i⁺`.

For an ergodic differentiable self-map `T` of `EuclideanSpace ℝ (Fin d)` preserving an SRB
(volume-case) measure `μ` (`hSRB : μ ≪ volume`) with nonsingular log-integrable derivative cocycle
and **nonnegative Lyapunov spectrum** (`hspec`), the Kolmogorov–Sinai system entropy equals the sum
of the strictly positive Lyapunov exponents, `h_μ(T) = (sumPosExp : EReal)`.

The proof is `le_antisymm` of the two directions:

* `≤` : `ErgodicTheory.margulisRuelle_sharp` — the Margulis–Ruelle inequality, sorry-free modulo the
  honest atom-count hypothesis `hgeo`; holds for every invariant measure. (Note:
  `margulisRuelle_sharp` takes `hT hdet hint hint' hgeo` and **no** `hdiff` — the earlier frontier
  draft passed a spurious `hdiff` here; that arity is corrected.)
* `≥` : `ErgodicTheory.sumPosExp_le_ksEntropy_of_SRB` — the volume-case reverse inequality via
  Rokhlin's inequality (`ManeLowerBound`).

The hypotheses are exactly the union of the two halves: `hgeo` is the Ruelle atom-count input
(carried verbatim from `margulisRuelle_sharp`), and `hdiff`, `hSRB`, `hξ`, `hspec`, `hlogρ`,
`hlogdet` are the inputs to the reverse leaf. See the module docstring for the vacuity caveat. -/
theorem pesin_entropy_formula_spectral (hdiff : Differentiable ℝ T) (hSRB : SRBProperty T μ)
    {ξ : Entropy.MeasurePartition μ (Fin m)} [Nonempty (Fin m)]
    (hξ : IsInjectivityPartition μ T ξ)
    (hspec : ∀ i, 0 ≤ exponents hT hdet (measurable_derivativeCocycle T) hint hint' i)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ)
    (hgeo : ∀ (n : ℕ) (P : Entropy.MeasurePartition μ (Fin n)),
      ∃ (ε : ℝ≥0) (Ccov : ℝ), 0 < ε ∧ 0 ≤ Ccov ∧
        (∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop,
          (Entropy.atomCount hT.toMeasurePreserving P k : ℝ)
            ≤ Ccov * coveringReal T k ε x)) :
    Entropy.ksEntropy hT.toMeasurePreserving
      = ((sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' : ℝ) : EReal) :=
  le_antisymm
    (margulisRuelle_sharp hT hdet hint hint' hgeo)
    (sumPosExp_le_ksEntropy_of_SRB hT hdet hint hint' hdiff hSRB hξ hspec hlogρ hlogdet)

/-- **Pesin's entropy formula, integral form (volume case)** — the genuine `h_μ(T) = ∫ ∑_i λ_i⁺ dμ`.

For an SRB (volume-case) measure, the system entropy equals the integral over `μ` of the
positive-exponent-sum integrand `χ` (the unstable Jacobian, `UnstableJacobianRate`):
`h_μ(T) = ∫ χ dμ`.

This is `pesin_entropy_formula_spectral` rewritten through the bridge `∫ χ dμ = sumPosExp`: since
`χ` is `μ`-a.e. equal to the constant `sumPosExp` (`hχ`) and `μ` is a probability measure,
`∫ χ dμ = sumPosExp · μ(univ) = sumPosExp`. No integrability hypothesis on `χ` is needed: the
`integral_congr_ae` bridge consumes only the a.e.-constancy `hχ`, and integrability of `χ` is in
any case automatic from `hχ` (being a.e. equal to a constant on a probability measure). The bridge
is sorry-free, so the integral form inherits the exact (volume-case, sorry-free) status of the
spectral form. -/
theorem pesin_entropy_formula (hdiff : Differentiable ℝ T)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSRB : SRBProperty T μ) (hχ : UnstableJacobianRate hT hdet hint hint' χ)
    {ξ : Entropy.MeasurePartition μ (Fin m)} [Nonempty (Fin m)]
    (hξ : IsInjectivityPartition μ T ξ)
    (hspec : ∀ i, 0 ≤ exponents hT hdet (measurable_derivativeCocycle T) hint hint' i)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ)
    (hgeo : ∀ (n : ℕ) (P : Entropy.MeasurePartition μ (Fin n)),
      ∃ (ε : ℝ≥0) (Ccov : ℝ), 0 < ε ∧ 0 ≤ Ccov ∧
        (∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop,
          (Entropy.atomCount hT.toMeasurePreserving P k : ℝ)
            ≤ Ccov * coveringReal T k ε x)) :
    Entropy.ksEntropy hT.toMeasurePreserving = ((∫ x, χ x ∂μ : ℝ) : EReal) := by
  -- The integral of the a.e.-constant `χ` over a probability measure is `sumPosExp`.
  have hbridge : (∫ x, χ x ∂μ)
      = sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' := by
    rw [integral_congr_ae hχ, integral_const, probReal_univ, one_smul]
  rw [hbridge]
  exact pesin_entropy_formula_spectral hT hdet hint hint' hdiff hSRB hξ hspec hlogρ hlogdet hgeo

end Pesin

end ErgodicTheory
