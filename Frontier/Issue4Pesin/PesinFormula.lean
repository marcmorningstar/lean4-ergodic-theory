/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue4Pesin.ManeLowerBound

/-!
# Pesin's entropy formula `h_μ(T) = ∫ ∑ λ_i⁺ dμ` (capstone)

This is the capstone of the three-module assembly of **Pesin's entropy formula** for a smooth
ergodic self-map `T` of `EuclideanSpace ℝ (Fin d)` preserving an SRB (e.g. volume) measure `μ`:

`h_μ(T) = ∫ (∑_i λ_i⁺) dμ = ∑_i λ_i⁺`

(the last equality because the spectrum is ergodic, so the integrand is a.e. the constant
`sumPosExp`, which a probability measure integrates to itself).

It assembles the two directions:

* **`≤` (Margulis–Ruelle, DONE).** `h_μ(T) ≤ ∑_i λ_i⁺` is `ErgodicTheory.margulisRuelle_sharp`, proved
  sorry-free modulo the honest non-compactness atom-count input `hgeo` (the Riquelme-necessary
  bounded-distortion regime). This direction holds for *every* invariant measure, no SRB hypothesis.

* **`≥` (Mañé / Ledrappier–Strelcyn–Young, SRB-only).** `∑_i λ_i⁺ ≤ h_μ(T)` is
  `Frontier.Issue4Pesin.sumPosExp_le_ksEntropy_of_SRB`, the reverse inequality that holds **exactly
  for SRB measures** (absolute continuity of conditional measures on unstable manifolds). Its proof
  is the BLOCKED Pesin / Ledrappier–Young geometric content decomposed in `ManeLowerBound`.

`le_antisymm` of the two gives the equality. The equality is stated both as
`h_μ(T) = (sumPosExp : EReal)` (the clean spectral form) and as
`h_μ(T) = (∫ χ dμ : EReal)` (the genuine Pesin integral form), the two being identified by the
a.e.-constancy of the integrand `χ` (`UnstableJacobianRate`).

## Main results

* `Frontier.Issue4Pesin.pesin_entropy_formula_spectral` — Pesin's formula in spectral form
  `h_μ(T) = (∑_i λ_i⁺ : EReal)`, the equality for an SRB measure.
* `Frontier.Issue4Pesin.pesin_entropy_formula` — Pesin's formula in integral form
  `h_μ(T) = (∫ χ dμ : EReal)`, the genuine `h_μ(T) = ∫ ∑ λ_i⁺ dμ`.

## Status of the chain

The `≤` half is sorry-free (modulo its honest atom-count hypothesis, identical to the
already-landed `ErgodicTheory.margulisRuelle_sharp`). The `≥` half rests on the single BLOCKED leaf
`sumPosExp_le_ksEntropy_of_SRB` (Mañé's lower bound + the unstable-Jacobian estimate; Pesin /
Ledrappier–Young theory, Mathlib-absent). The capstone equalities chain the two with `le_antisymm`
and the integral-vs-constant bridge — that chaining is sorry-free; only the `≥` leaf carries the
gap. This is the honest, research-scale shape of the result: a correct roadmap with one precisely
named geometric wall.

## References

* Maryam Contractor, *The Pesin Entropy Formula*, UChicago REU 2023, §7 (Theorem 7.15), §8.
* Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math.
  Surveys **32** (1977) 55–114.
* F. Ledrappier, L.-S. Young, *The metric entropy of diffeomorphisms I*, Ann. of Math. **122**
  (1985) 509–539.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Frontier.Issue4Pesin

variable {d : ℕ} [NeZero d]

section Pesin

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : Ergodic T μ)
    (hdet : ∀ x, (ErgodicTheory.derivativeCocycle T x).det ≠ 0)
    (hint : ErgodicTheory.IntegrableLogNorm (ErgodicTheory.derivativeCocycle T) μ)
    (hint' : ErgodicTheory.IntegrableLogNorm (fun x => (ErgodicTheory.derivativeCocycle T x)⁻¹) μ)

/-- **Pesin's entropy formula, spectral form.**

For an ergodic differentiable self-map `T` of `EuclideanSpace ℝ (Fin d)` preserving an SRB measure
`μ` (`hSRB`), with nonsingular log-integrable derivative cocycle, the Kolmogorov–Sinai system
entropy equals the sum of the strictly positive Lyapunov exponents:

`h_μ(T) = ∑_i λ_i⁺`  (`= (sumPosExp : EReal)`).

The proof is `le_antisymm` of the two directions:

* `≤` : `ErgodicTheory.margulisRuelle_sharp` (the Margulis–Ruelle inequality, proved sorry-free modulo
  the honest atom-count hypothesis `hgeo`; holds for every invariant measure).
* `≥` : `sumPosExp_le_ksEntropy_of_SRB` (the SRB-only reverse inequality; its proof is the BLOCKED
  Pesin / Ledrappier–Young content).

The hypotheses are exactly those of the two halves: `hgeo` is the Ruelle atom-count input (carried
verbatim from `margulisRuelle_sharp`), `hSRB` is the SRB property, and `hχ` identifies the
unstable-Jacobian integrand with the spectrum. The `EReal` coercion of `sumPosExp` is the
finite right-hand side, so `le_antisymm` lands the equality in `EReal`. -/
theorem pesin_entropy_formula_spectral (hdiff : Differentiable ℝ T)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSRB : SRBProperty T μ) (hχ : UnstableJacobianRate hT hdet hint hint' χ)
    (hgeo : ∀ (n : ℕ) (P : ErgodicTheory.Entropy.MeasurePartition μ (Fin n)),
      ∃ (ε : ℝ≥0) (Ccov : ℝ), 0 < ε ∧ 0 ≤ Ccov ∧
        (∀ᵐ x ∂μ, ∀ᶠ m : ℕ in atTop,
          (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P m : ℝ)
            ≤ Ccov * ErgodicTheory.coveringReal T m ε x)) :
    ErgodicTheory.Entropy.ksEntropy hT.toMeasurePreserving
      = ((ErgodicTheory.sumPosExp hT hdet
          (ErgodicTheory.measurable_derivativeCocycle T) hint hint' : ℝ) : EReal) :=
  le_antisymm
    (ErgodicTheory.margulisRuelle_sharp hT hdet hint hint' hdiff hgeo)
    (sumPosExp_le_ksEntropy_of_SRB hT hdet hint hint' hSRB hχ)

/-- **Pesin's entropy formula, integral form** — the genuine `h_μ(T) = ∫ ∑_i λ_i⁺ dμ`.

For an SRB measure, the system entropy equals the integral over `μ` of the positive-exponent sum
integrand `χ` (the unstable Jacobian, `UnstableJacobianRate`):

`h_μ(T) = ∫ χ dμ`.

This is `pesin_entropy_formula_spectral` rewritten through the bridge `∫ χ dμ = sumPosExp`: since
`χ` is `μ`-a.e. equal to the constant `sumPosExp` (`hχ`), and `μ` is a probability measure,
`∫ χ dμ = sumPosExp · μ(univ) = sumPosExp`. The integrability of `χ` (`hχint`) makes the integral
well-defined; with it the `setIntegral`/`integral_congr_ae` rewriting is sorry-free, so the integral
form inherits the exact gap structure of the spectral form (`≤` done, `≥` the single BLOCKED leaf).
-/
theorem pesin_entropy_formula (hdiff : Differentiable ℝ T)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχint : Integrable χ μ)
    (hSRB : SRBProperty T μ) (hχ : UnstableJacobianRate hT hdet hint hint' χ)
    (hgeo : ∀ (n : ℕ) (P : ErgodicTheory.Entropy.MeasurePartition μ (Fin n)),
      ∃ (ε : ℝ≥0) (Ccov : ℝ), 0 < ε ∧ 0 ≤ Ccov ∧
        (∀ᵐ x ∂μ, ∀ᶠ m : ℕ in atTop,
          (ErgodicTheory.Entropy.atomCount hT.toMeasurePreserving P m : ℝ)
            ≤ Ccov * ErgodicTheory.coveringReal T m ε x)) :
    ErgodicTheory.Entropy.ksEntropy hT.toMeasurePreserving = ((∫ x, χ x ∂μ : ℝ) : EReal) := by
  -- `hχint` records that the Pesin integrand `χ` is integrable, making `∫ χ dμ` genuinely the
  -- Lebesgue integral of the formula (not a vacuous zero); the a.e.-constancy bridge below does
  -- not consume it, but it is a load-bearing part of the *statement*.
  let _ := hχint
  -- The integral of the a.e.-constant `χ` over a probability measure is `sumPosExp`.
  have hbridge : (∫ x, χ x ∂μ)
      = ErgodicTheory.sumPosExp hT hdet (ErgodicTheory.measurable_derivativeCocycle T) hint hint' := by
    rw [integral_congr_ae hχ, integral_const, probReal_univ, one_smul]
  rw [hbridge]
  exact pesin_entropy_formula_spectral hT hdet hint hint' hdiff hSRB hχ hgeo

end Pesin

end Frontier.Issue4Pesin
