/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Smooth.Pesin.SRBData
import ErgodicTheory.Smooth.RokhlinExpanding
import ErgodicTheory.Smooth.Expanding
import ErgodicTheory.Entropy.CondMono
import ErgodicTheory.Krieger.SMBSharp
import ErgodicTheory.Lyapunov.Extensions.DetIdentity

/-!
# Pesin's entropy formula, part 2: the reverse inequality `∑ λ⁺ ≤ h_μ(T)` (volume case)

This is the second of the three-module Pesin-entropy-formula chain — the migrated and
**discharged** issue-#10 reverse inequality. Where the general Ledrappier–Young reverse inequality
is a documented Mathlib-scale wall (Pesin unstable-manifold theory + absolute continuity of the
unstable foliation), the **volume case** `μ ≪ volume` goes through instead by **Rokhlin's
inequality**, which is unconditional and already fully within reach of the on-branch entropy API.

## The route (volume case)

The reverse inequality is assembled from three on-branch steps (all sorry-free), together with the
imported spectral lemma `sumPosExp_eq_sumAllExp_of_nonneg` (now living in
`ErgodicTheory.Lyapunov.Extensions.ExponentSums`): under a **nonnegative Lyapunov spectrum**
(`hspec`) the positive-exponent sum equals the full exponent sum (the extra summands are exponents
`≤ 0`, which under the hypothesis are `= 0`).

1. `strictFuture_le_comap` — the generator-free half of `strictFuture_eq_comap_of_generating`: the
   strict-future σ-algebra sits below `comap T`.
2. `integral_log_abs_det_le_ksEntropy` — **Rokhlin's inequality** `∫ log|det DT| dμ ≤ h_μ(T)`,
   unconditional (no generator, no ergodicity, no expansion).
3. `sumPosExp_le_ksEntropy_of_SRB` — chaining them: `∑ λ⁺ =` (hspec) `∑ λ = ∫ log|det Df| dμ ≤ h`,
   using `sumPosExp_eq_sumAllExp_of_nonneg` and the trace–determinant identity
   `sumAllExp = ∫ log|det Df|`.

The **only** place the volume case shows up is `hspec` (nonnegative spectrum): in the volume case
`∫ log|det DT| = ∑ λ⁺` because there are no genuinely negative exponents; for a mixed-spectrum SRB
measure with real stable directions `∫ log|det| = ∑ λ⁺ + ∑ λ⁻ < ∑ λ⁺`, and the reverse inequality
then needs the Ledrappier–Young unstable-Jacobian machinery — the documented general wall.

## Main results

* `ErgodicTheory.strictFuture_le_comap` — strict-future σ-algebra `≤ comap T` (generator-free).
* `ErgodicTheory.integral_log_abs_det_le_ksEntropy` — **Rokhlin's inequality**, unconditional.
* `ErgodicTheory.sumPosExp_le_ksEntropy_of_SRB` — the discharged issue-#10 reverse leaf.

## Status

No `BLOCKED` leaf remains in the **volume case**: all four results are sorry-free. The general
mixed-spectrum SRB reverse inequality (absolute continuity of the conditional measures on genuine
unstable manifolds) remains the documented Mathlib-scale wall — see the discussion under
`sumPosExp_le_ksEntropy_of_SRB` and the `SRBData` module docstring.

## References

* V. A. Rokhlin, *Lectures on the entropy theory of measure-preserving transformations*, Russian
  Math. Surveys **22** (1967), no. 5, 1–52, §9.
* W. Parry, *Entropy and Generators in Ergodic Theory*, Benjamin, 1969.
* Y. Coudène, *Ergodic Theory and Dynamical Systems*, Universitext, Springer, 2016, Ch. 12,
  Cor. 12.1 (the inequality is unconditional; the one-sided generator is needed only for equality),
  and the Remark `|T'_μ| = |det DT|` a.e. for `μ ≪ Leb`.
* R. Mañé, *A proof of Pesin's formula*, Ergodic Theory Dynam. Systems **1** (1981) 95–102
  (Errata ETDS **3** (1983): misprint in ineq. (11), no consequence).
* F. Ledrappier, L.-S. Young, *The metric entropy of diffeomorphisms I*, Ann. of Math. **122**
  (1985) 509–539.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ErgodicTheory

open ErgodicTheory.Entropy

variable {d : ℕ}

/-! ## (1) The strict-future σ-algebra lies below `comap T` (generator-free) -/

section StrictFuture

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {m : ℕ}

omit [IsProbabilityMeasure μ] in
/-- **The strict-future σ-algebra lies below `comap T`.** The strict-future σ-algebra
`⨆ₖ σ((ksJoin ξ k).pullback)` is below `comap T mα`.

This is the **generator-free half** of `strictFuture_eq_comap_of_generating`: the equality there
needs a one-sided generating partition, but the `≤` direction is unconditional. It mimics that
lemma's per-term step, then closes with `iSup_le` and `comap_mono (generatedSigmaAlgebra_le _)`.
This `≤` is exactly what makes Rokhlin's inequality (below) unconditional — no generator. -/
theorem strictFuture_le_comap (hT : MeasurePreserving T μ μ)
    (ξ : Entropy.MeasurePartition μ (Fin m)) :
    (⨆ k, Entropy.generatedSigmaAlgebra μ ((Entropy.ksJoin hT ξ k).pullback hT))
      ≤ MeasurableSpace.comap T inferInstance := by
  refine iSup_le (fun k => ?_)
  rw [Krieger.generatedSigmaAlgebra_pullback_eq_pulledBack hT (Entropy.ksJoin hT ξ k),
    Entropy.comap_generatedSigmaAlgebra_pulledBack hT (Entropy.ksJoin hT ξ k)]
  exact MeasurableSpace.comap_mono (Entropy.generatedSigmaAlgebra_le _)

end StrictFuture

/-! ## (2) Rokhlin's inequality `∫ log|det DT| dμ ≤ h_μ(T)` (generator-free) -/

section Rokhlin

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {m : ℕ}

/-- **Rokhlin's inequality (Rokhlin §9; Parry 1969; Coudène Cor. 12.1), generator-free.**
`∫ log|det DT| dμ ≤ h_μ(T)`.

For an absolutely continuous (`μ ≪ volume`), differentiable, injectivity-partitioned self-map of
`EuclideanSpace ℝ (Fin d)` with nonsingular derivative and integrable log data, the integrated
volume distortion is bounded by the Kolmogorov–Sinai entropy.

**Unconditional**: this is Rokhlin's *inequality*, and it needs **no** one-sided generating
partition (`IsGenerating`), **no** ergodicity, and **no** expansion — those are needed only for
Rokhlin's *equality*. Here `μ ≪ volume` enters solely through the Coudène Remark
`|T'_μ| = |det DT|` a.e., identifying the Radon–Nikodym distortion with the Jacobian determinant.

Chain: `condEntropy_comap_eq_integral_log_abs_det` identifies the integral with the conditional
entropy `H(ξ | comap T mα)`; `condEntropy_mono_of_le` against the generator-free
`strictFuture_le_comap` bounds it by `H(ξ | 𝒮∞)`; `ksEntropyPartition_eq_condEntropy_iSup`
identifies that with `h(T, ξ)`; and `le_ksEntropy` lifts to the system entropy `h_μ(T)`.

**Non-vacuous on `EuclideanSpace`**: unlike the uniformly-expanding Pesin bundle (whose hypotheses
have no model on non-compact `ℝ^d`), this inequality's hypotheses *are* satisfiable — e.g. `T = id`
with any absolutely continuous probability `μ` gives `∫ log|det D(id)| dμ = 0 ≤ h_μ(id)`. -/
theorem integral_log_abs_det_le_ksEntropy (hT : MeasurePreserving T μ μ) (hac : μ ≪ volume)
    (hdiff : Differentiable ℝ T) {ξ : Entropy.MeasurePartition μ (Fin m)} [Nonempty (Fin m)]
    (hξ : IsInjectivityPartition μ T ξ) (hdet : ∀ x, (fderiv ℝ T x).det ≠ 0)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    ((∫ x, Real.log |(fderiv ℝ T x).det| ∂μ : ℝ) : EReal) ≤ Entropy.ksEntropy hT := by
  classical
  have hTmeas : Measurable T := hdiff.continuous.measurable
  have h1 : Entropy.condEntropy μ (MeasurableSpace.comap T inferInstance) ξ.cells
      = ∫ x, Real.log |(fderiv ℝ T x).det| ∂μ :=
    condEntropy_comap_eq_integral_log_abs_det hT hac hdiff hξ hdet hlogρ hlogdet
  have h2 : Entropy.condEntropy μ (MeasurableSpace.comap T inferInstance) ξ.cells
      ≤ Entropy.condEntropy μ (⨆ k, Entropy.generatedSigmaAlgebra μ
          ((Entropy.ksJoin hT ξ k).pullback hT)) ξ.cells :=
    Entropy.condEntropy_mono_of_le (strictFuture_le_comap hT ξ) hTmeas.comap_le ξ
  have h3 : Entropy.condEntropy μ (⨆ k, Entropy.generatedSigmaAlgebra μ
        ((Entropy.ksJoin hT ξ k).pullback hT)) ξ.cells = Entropy.ksEntropyPartition hT ξ :=
    (Krieger.ksEntropyPartition_eq_condEntropy_iSup hT ξ).symm
  have hR : ∫ x, Real.log |(fderiv ℝ T x).det| ∂μ ≤ Entropy.ksEntropyPartition hT ξ := by
    rw [← h1, ← h3]; exact h2
  calc ((∫ x, Real.log |(fderiv ℝ T x).det| ∂μ : ℝ) : EReal)
      ≤ ((Entropy.ksEntropyPartition hT ξ : ℝ) : EReal) := by exact_mod_cast hR
    _ ≤ Entropy.ksEntropy hT := Entropy.le_ksEntropy hT ξ

end Rokhlin

/-! ## (3) The discharged issue-#10 reverse leaf `∑ λ⁺ ≤ h_μ(T)` (volume case) -/

section ReverseLeaf

variable [NeZero d]
variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {m : ℕ}

/-- **The SRB reverse inequality, volume case — the discharged issue-#10 leaf.**
`(sumPosExp : EReal) ≤ h_μ(T)`.

For an ergodic, differentiable, injectivity-partitioned self-map preserving an SRB (volume-case)
measure (`hSRB : μ ≪ volume`) with **nonnegative Lyapunov spectrum** (`hspec`) and integrable log
data, the positive-exponent sum is bounded by the Kolmogorov–Sinai entropy.

**The chain** is `∑ λ⁺ =`(hspec)` ∑ λ = ∫ log|det Df| dμ ≤ h_μ(T)`:

* `=`(hspec): `sumPosExp_eq_sumAllExp_of_nonneg` — the nonnegative spectrum kills the negative part.
* `=`: the trace–determinant identity `sumAllExp_eq_integral_log_abs_det`, aligned to `fderiv` by
  `det_fderiv_eq_det_derivativeCocycle`.
* `≤`: **Rokhlin's inequality** `integral_log_abs_det_le_ksEntropy`.

**`hspec` is exactly the volume-case boundary.** In the volume case there are no genuinely negative
exponents, so `∫ log|det DT| = ∑ λ⁺` and the chain closes. For a mixed-spectrum SRB measure with
real stable directions, `∫ log|det DT| = ∑ λ⁺ + ∑ λ⁻ < ∑ λ⁺`, so Rokhlin's inequality gives only
`∑ λ⁺ + ∑ λ⁻ ≤ h`, which is *weaker*; recovering the reverse inequality then requires the
Ledrappier–Young unstable-Jacobian machinery (the documented Mathlib-scale wall). **Do not** attempt
to derive `hspec` from `μ ≪ volume`: it is false in general (volume-preserving hyperbolic maps have
`∫ log|det| = 0` with genuine negative exponents). `hspec` is a real, separate hypothesis marking
the volume-case fragment. -/
theorem sumPosExp_le_ksEntropy_of_SRB (hT : Ergodic T μ)
    (hdet : ∀ x, (derivativeCocycle T x).det ≠ 0)
    (hint : IntegrableLogNorm (derivativeCocycle T) μ)
    (hint' : IntegrableLogNorm (fun x => (derivativeCocycle T x)⁻¹) μ)
    (hdiff : Differentiable ℝ T) (hSRB : SRBProperty T μ)
    {ξ : Entropy.MeasurePartition μ (Fin m)} [Nonempty (Fin m)]
    (hξ : IsInjectivityPartition μ T ξ)
    (hspec : ∀ i, 0 ≤ exponents hT hdet (measurable_derivativeCocycle T) hint hint' i)
    (hlogρ : Integrable (fun x => Real.log ((μ.rnDeriv volume) x).toReal) μ)
    (hlogdet : Integrable (fun x => Real.log |(fderiv ℝ T x).det|) μ) :
    ((sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint' : ℝ) : EReal)
      ≤ Entropy.ksEntropy hT.toMeasurePreserving := by
  have hdet' : ∀ x, (fderiv ℝ T x).det ≠ 0 := fun x => by
    rw [det_fderiv_eq_det_derivativeCocycle]; exact hdet x
  have hspE : sumPosExp hT hdet (measurable_derivativeCocycle T) hint hint'
      = ∫ x, Real.log |(fderiv ℝ T x).det| ∂μ := by
    rw [sumPosExp_eq_sumAllExp_of_nonneg hT hdet (measurable_derivativeCocycle T) hint hint' hspec,
      sumAllExp_eq_integral_log_abs_det hT hdet (measurable_derivativeCocycle T) hint hint']
    exact integral_congr_ae
      (Filter.Eventually.of_forall (fun x => by
        simp only [det_fderiv_eq_det_derivativeCocycle (T := T) x]))
  rw [hspE]
  exact integral_log_abs_det_le_ksEntropy hT.toMeasurePreserving hSRB.absolutelyContinuous
    hdiff hξ hdet' hlogρ hlogdet

end ReverseLeaf

end ErgodicTheory
