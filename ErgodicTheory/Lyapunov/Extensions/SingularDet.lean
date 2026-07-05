/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.SingularExponent
import ErgodicTheory.Lyapunov.Extensions.DetIdentity

/-!
# The top (`k = d`) singular exponent `γ_d` as the `log⁺`-determinant `limsup`

This module records the **top** index `k = d` of the cumulative forward singular exponent family
`γ_k` (`ErgodicTheory.forwardSingularExponent`), dual to the bottom (`k = 1`) tie-in of
`ErgodicTheory/Lyapunov/Extensions/SingularExponentTop.lean`.

The full singular-value product is the absolute determinant,
`sprod A T d n x = |det(A⁽ⁿ⁾ x)|` — this is the pre-existing, invertibility-free identity
`ErgodicTheory.sprod_d_eq_abs_det` (`ErgodicTheory/Lyapunov/Extensions/DetIdentity.lean`),
obtained from
`(∏ σᵢ)² = ∏ eigenvalueᵢ(MᵀM) = det(MᵀM) = (det M)²` and a nonnegative square root. Rewriting the
defining `limsup` of `γ_d` through it shows the top cumulative forward singular exponent `γ_d` is
*exactly* the forward `log⁺`-determinant `limsup`, the volume-growth (full `d`-dimensional)
specialization of the singular-value layer in the `EReal` track.

## Main results

* `ErgodicTheory.forwardSingularExponent_full_eq` — `γ_d(x)` is the `limsup` of the `EReal`-coerced
  `(1/n) log⁺|det(A⁽ⁿ⁾ x)|` (deterministic, every `x`).

## Implementation notes

* The genuine-`log` determinant growth `(1/n) log|det(A⁽ⁿ⁾)| → ∑ i, exponents i` lives in the
  *invertible* additive track (`DetIdentity.lean`, hypotheses `det A ≠ 0`, `log⁺‖A⁻¹‖ ∈ L¹`). It is
  **not** folded into the `EReal`/`log⁺` packaging here: the `log⁺` form of `γ_d` agrees with the
  genuine `log` only in the expanding regime `Γ_d⁺ > 0` (the contracting volume case can fall to
  `−∞`). So `γ_d` is recorded only as the deterministic `log⁺`-determinant `limsup`.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58.
-/

open MeasureTheory Filter Topology

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

omit [MeasurableSpace X] in
/-- **`γ_d` is exactly the forward `log⁺`-determinant `limsup`** (deterministic, every `x`).
Rewriting the defining `limsup` of `γ_d` through `sprod_d_eq_abs_det` (`sprod_d = |det(A⁽ⁿ⁾)|`)
turns it into the `limsup` of the `EReal`-coerced `(1/n) log⁺|det(A⁽ⁿ⁾ x)|`. This is the full-`d`
(volume-growth) specialization of the cumulative forward singular exponent. -/
theorem forwardSingularExponent_full_eq [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) :
    forwardSingularExponent A T d x
      = Filter.limsup
          (fun n : ℕ =>
            (((n : ℝ)⁻¹ * Real.posLog |(cocycle A T n x).det| : ℝ) : EReal)) atTop := by
  rw [forwardSingularExponent]
  refine Filter.limsup_congr (Filter.Eventually.of_forall fun n => ?_)
  rw [sprod_d_eq_abs_det n x]

end ErgodicTheory
