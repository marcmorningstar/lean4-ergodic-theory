/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.ReturnTimeExponent
import ErgodicTheory.Lyapunov.Extensions.Corollaries

/-!
# The concrete top-exponent return-time transfer

`ErgodicTheory.returnTime_tendsto_exponent` (in `ErgodicTheory.Continuous.ReturnTimeExponent`)
transfers *any* base log-norm growth rate `lam` through the suspension roof to the
return-time exponent `lam / ∫ τ`, but it takes the base growth rate as a *hypothesis*
`hgrow`. This module discharges that hypothesis with the genuine top Lyapunov exponent
supplied by the multiplicative ergodic theorem.

The base growth rate is produced by
`ErgodicTheory.IsOseledetsFiltration.tendsto_log_opNorm_cocycle`
(`ErgodicTheory.Lyapunov.Extensions.Corollaries`), which states that, for an Oseledets
filtration datum `(k, lam, V)` of an invertible cocycle, the operator-norm growth rate
`n⁻¹ · log ‖A⁽ⁿ⁾(x)‖` converges `μ`-a.e. to the **top exponent** `lam ⟨0, hk⟩`. Feeding this
into `returnTime_tendsto_exponent` (with the roof average from
`ErgodicTheory.tendsto_roofAverage_ae` and `∫ τ ≠ 0` from `ErgodicTheory.integral_roof_pos`) yields
the concrete identity

`log ‖A⁽ⁿ⁾(x)‖ / roofSum n x → lam ⟨0, hk⟩ / ∫ τ`  (`μ`-a.e.).

## Main results

* `ErgodicTheory.IsOseledetsFiltration.returnTime_tendsto_topExponent`: the concrete top-exponent
  return-time transfer, with the base-growth hypothesis of `returnTime_tendsto_exponent`
  discharged by the MET top-exponent limit `tendsto_log_opNorm_cocycle`.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
  {A : X → Matrix (Fin d) (Fin d) ℝ}
  {k : ℕ} {lam : Fin k → ℝ}
  {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-- **Concrete top-exponent return-time transfer.** Let `T : X ≃ᵐ X` be ergodic for a
probability measure `μ`, let `A` be an invertible base cocycle generator (`(A x).det ≠ 0`)
carrying an Oseledets filtration datum `(k, lam, V)` with `0 < k`, and let `τ` be a measurable
integrable roof with a uniform positive lower bound `0 < c ≤ τ`. Then the base cocycle
log-norm, rescaled by the return time `roofSum n x` (the suspension time after `n` base
steps), converges `μ`-a.e. to `lam ⟨0, hk⟩ / ∫ τ`, the **top Lyapunov exponent divided by the
mean roof**.

The proof discharges the base-growth hypothesis of `returnTime_tendsto_exponent` with the MET
top-exponent limit `IsOseledetsFiltration.tendsto_log_opNorm_cocycle`, supplies the roof
average via `tendsto_roofAverage_ae`, and obtains `∫ τ ≠ 0` from `integral_roof_pos`. -/
theorem IsOseledetsFiltration.returnTime_tendsto_topExponent
    {μ : Measure X} [IsProbabilityMeasure μ] (T : X ≃ᵐ X) (hT : Ergodic (⇑T) μ)
    (hA : ∀ x, (A x).det ≠ 0)
    (hV : IsOseledetsFiltration μ (⇑T) A k lam V) (hk : 0 < k)
    {τ : X → ℝ} (hτ : Measurable τ) (hτint : Integrable τ μ)
    {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => Real.log ‖cocycle A (⇑T) n x‖ / roofSum T hτ (n : ℤ) x) atTop
      (𝓝 (lam ⟨0, hk⟩ / ∫ y, τ y ∂μ)) := by
  -- the MET top-exponent limit discharges the base-growth hypothesis (rate `lam ⟨0, hk⟩`)
  have hgrow := hV.tendsto_log_opNorm_cocycle hA hk
  have hroof := tendsto_roofAverage_ae T hτ hT hτint
  have hτne : (∫ y, τ y ∂μ) ≠ 0 :=
    ne_of_gt (integral_roof_pos hc hcpos hτint)
  exact returnTime_tendsto_exponent T hτ hgrow hroof hτne

end ErgodicTheory
