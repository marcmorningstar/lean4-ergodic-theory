/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionNlap
import ErgodicTheory.Continuous.SuspensionCocycle
import ErgodicTheory.Continuous.ReturnTimeTopExponent

/-!
# The special-flow Lyapunov exponent along return times

This module assembles the **special-flow Lyapunov exponent transfer sampled at return times**, the
headline `λ_flow = λ_base / ∫ τ` of Issue #5, *along the cross-section return subsequence*. It bolts
the cover-cocycle operator-norm bridge at return times (`coverCocycle_returnTime_norm_eq`, in
`ErgodicTheory.Continuous.SuspensionNlap`) onto the base return-time exponent
(`returnTime_tendsto_exponent`, in `ErgodicTheory.Continuous.ReturnTimeExponent`).

The cover flow cocycle `coverCocycle`, sampled on the base section exactly at the `n`-th return time
`returnTime n x`, has operator norm equal to the discrete base cocycle norm `‖cocycle A T n x‖` on
the nose (no bounded discrepancy to wash out at the section). The return time itself is the roof
Birkhoff sum, `returnTime n x = roofSum (n : ℤ) x` (definitionally). The headline below substitutes
both and reduces *exactly* to `returnTime_tendsto_exponent`: the flow cocycle norm, sampled at
return times, grows at rate `λ_base / ∫ τ`.

This is the special-flow / flow-under-a-roof construction of Cornfeld–Fomin–Sinai, *Ergodic Theory*
(Springer 1982), Ch. 11 (special/suspension flows; Ambrose–Kakutani), the first-return / ceiling
construction underlying Abramov's entropy formula `h(flow) = h(base)/∫τ` (L.M. Abramov, *On the
entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959) 873–875); the Lyapunov-exponent analogue is
the design reference of Bessa–Varandas (suspension Lyapunov exponents).

## Main results

* `ErgodicTheory.coverCocycle_returnTime_tendsto_exponent`: the
  **headline return-time flow exponent**.
  Given any base log-norm growth rate `lam` (a hypothesis, as in `returnTime_tendsto_exponent`),
  the roof average tendsto, and `∫ τ ≠ 0`, the *cover flow cocycle* log-norm rescaled by the return
  time converges `μ`-a.e. to `lam / ∫ τ`:
  `Real.log ‖coverCocycle (x,0) (returnTime n x)‖ / returnTime n x → lam / ∫ τ`.
* `ErgodicTheory.IsOseledetsFiltration.coverCocycle_returnTime_tendsto_topExponent`: the concrete
  **top-exponent** specialization, with the base-growth hypothesis discharged by the multiplicative
  ergodic theorem, giving the rate `lam ⟨0, hk⟩ / ∫ τ` (the top Lyapunov exponent over the mean
  roof).

## What is *not* in this file — the remaining gap toward the `MeasurePreservingFlow` exponent

The limits below are along the discrete return times `returnTime n x`, i.e. the flow exponent
sampled on the cross-section at base returns. Three pieces remain, all deferred (as documented in
`ErgodicTheory.Continuous.SuspensionNlap` / `SuspensionCocycle` / `SuspensionCoverFlow`):

1. **Between-returns interpolation.** Upgrading the return-subsequence limit to the full
   continuous-time limit `(1/t)·log‖coverCocycle p t‖` over arbitrary real `t → ∞` needs the
   residual control `coverCocycle_returnTime_opNorm_le` squeezed between consecutive returns (the
   bounded-residual sandwich) plus the additive flow law in the height coordinate.
2. **Quotient descent to `SuspensionSpace`.** Reading the rate as a class-invariant measurable
   function on the orbit quotient is the open keystone (the genuine space-level `FlowCocycle`).
3. **The `MeasurePreservingFlow` exponent.** Reading `λ_flow = λ_base / ∫τ` against the invariant
   suspension measure needs per-time measure-preservation of the suspension flow. The denominator
   `∫τ` is Abramov's; the numerator is the base Oseledets exponent.

The present file is self-contained and sorry-free.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

section FlowExponent

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **The return-time flow exponent (headline).** Suppose the base cocycle `A` has a `μ`-a.e.
log-norm growth rate `lam` (`n⁻¹ · log ‖cocycle A T n x‖ → lam` a.e.; the headline output of the
discrete Oseledets/Furstenberg–Kesten theorem, taken as a hypothesis so the lemma applies to the
top exponent, a `k`-th exponent, or any other rate), that the roof average converges a.e. to `∫ τ`,
and that `∫ τ ≠ 0`. Then the **cover flow cocycle** log-norm, sampled on the base section at the
`n`-th return time and rescaled by that return time, converges `μ`-a.e. to `lam / ∫ τ`.

The proof rewrites the cover-cocycle norm at the return time as the base cocycle norm
(`coverCocycle_returnTime_norm_eq`) and unfolds `returnTime n x = roofSum (n : ℤ) x`, reducing
the statement exactly to `returnTime_tendsto_exponent`. This is the special-flow exponent transfer
along the cross-section: at return times the flow cocycle grows at rate `λ_base / ∫ τ`. -/
theorem coverCocycle_returnTime_tendsto_exponent (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    {μ : Measure X} {lam : ℝ}
    (hgrow : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A (⇑T) n x‖) atTop (𝓝 lam))
    (hroof : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * roofSum T hτ (n : ℤ) x) atTop (𝓝 (∫ y, τ y ∂μ)))
    (hτne : (∫ y, τ y ∂μ) ≠ 0) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ =>
        Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) (returnTime T hτ n x)‖
          / returnTime T hτ n x)
      atTop (𝓝 (lam / ∫ y, τ y ∂μ)) := by
  have hbase := returnTime_tendsto_exponent T hτ hgrow hroof hτne
  refine hbase.mono fun x hx => ?_
  refine hx.congr (fun n => ?_)
  rw [coverCocycle_returnTime_norm_eq A T hτ hc hcpos n x]
  rfl

end FlowExponent

section TopExponent

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
  {A : X → Matrix (Fin d) (Fin d) ℝ}
  {k : ℕ} {lam : Fin k → ℝ}
  {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-- **The concrete top-exponent return-time flow exponent.** Let `T` be ergodic for a probability
measure `μ`, let `A` be an invertible base cocycle generator carrying an Oseledets filtration datum
`(k, lam, V)` with `0 < k`, and let `τ` be a measurable integrable roof with a uniform positive
lower bound `0 < c ≤ τ`. Then the **cover flow cocycle** log-norm, sampled on the base section at
the `n`-th return time and rescaled by that return time, converges `μ`-a.e. to `lam ⟨0, hk⟩ / ∫ τ`,
the **top Lyapunov exponent divided by the mean roof** — the special-flow top exponent along the
cross-section returns.

The proof discharges the base-growth hypothesis of `coverCocycle_returnTime_tendsto_exponent` with
the MET top-exponent limit, via `IsOseledetsFiltration.returnTime_tendsto_topExponent` rewritten
through the norm bridge `coverCocycle_returnTime_norm_eq`. -/
theorem IsOseledetsFiltration.coverCocycle_returnTime_tendsto_topExponent
    {μ : Measure X} [IsProbabilityMeasure μ] (T : X ≃ᵐ X) (hT : Ergodic (⇑T) μ)
    (hA : ∀ x, (A x).det ≠ 0)
    (hV : IsOseledetsFiltration μ (⇑T) A k lam V) (hk : 0 < k)
    {τ : X → ℝ} (hτ : Measurable τ) (hτint : Integrable τ μ)
    {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ =>
        Real.log ‖coverCocycle A T hτ hc hcpos (x, 0) (returnTime T hτ n x)‖
          / returnTime T hτ n x)
      atTop (𝓝 (lam ⟨0, hk⟩ / ∫ y, τ y ∂μ)) := by
  have hbase :=
    hV.returnTime_tendsto_topExponent T hT hA hk hτ hτint hc hcpos
  refine hbase.mono fun x hx => ?_
  refine hx.congr (fun n => ?_)
  rw [coverCocycle_returnTime_norm_eq A T hτ hc hcpos n x]
  rfl

end TopExponent

end ErgodicTheory
