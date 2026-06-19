/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Extensions.SingularExponent

/-!
# Full singular-value product = `|det|`, and the top (`k = d`) singular exponent

This module supplies the infrastructure lemma at the **top** index `k = d` of the cumulative
forward singular exponent family `γ_k` (`Oseledets.forwardSingularExponent`), dual to the bottom
(`k = 1`) tie-in of `Oseledets/Lyapunov/Extensions/SingularExponentTop.lean`: the **product of
all `d` singular values of a matrix equals the absolute value of its determinant**,

`∏ i, σᵢ(toEuclideanLin M) = |det M|`.

The singular values `LinearMap.singularValues` are the descending square roots of the eigenvalues
of `adjoint f ∘ₗ f` (the Gram operator). Squaring the full product and using the
eigenvalue-product = determinant identity for the symmetric Gram operator
(`LinearMap.IsSymmetric.det_eq_prod_eigenvalues`) gives

`(∏ σᵢ)² = ∏ σᵢ² = ∏ eigenvalueᵢ(MᵀM) = det(MᵀM) = det Mᵀ · det M = (det M)²`,

and since the left side is `≥ 0` the square root is `|det M|`. No invertibility is needed: the
identity holds for *every* matrix (both sides are nonnegative with equal squares).

With this in hand the top cumulative singular-value product collapses to the absolute determinant
(`sprod A T d n x = |det(A⁽ⁿ⁾ x)|`), so the cumulative forward singular exponent `γ_d` is *exactly*
the forward `log⁺`-determinant `limsup`. This is the volume-growth (full `d`-dimensional)
specialization of the singular-value layer, recorded invertibility-free in the `EReal` track.

## Main results

* `Oseledets.prod_singularValues_eq_abs_det` — `∏ i, σᵢ(toEuclideanLin M) = |det M|` (the crux
  infra lemma).
* `Oseledets.sprod_full_eq_abs_det` — `sprod A T d n x = |det(A⁽ⁿ⁾ x)|`.
* `Oseledets.forwardSingularExponent_full_eq` — `γ_d(x)` is the `limsup` of the `EReal`-coerced
  `(1/n) log⁺|det(A⁽ⁿ⁾ x)|` (deterministic, every `x`).

## Implementation notes

* The genuine-`log` determinant growth `(1/n) log|det(A⁽ⁿ⁾)| → ∑ i, exponents i` lives in the
  *invertible* additive track (`Oseledets/Lyapunov/Extensions/DetIdentity.lean`, hypotheses
  `det A ≠ 0`, `log⁺‖A⁻¹‖ ∈ L¹`). It is **not** folded into the `EReal`/`log⁺` packaging here: the
  `log⁺` form of `γ_d` agrees with the genuine `log` only in the expanding regime `Γ_d⁺ > 0`,
  exactly the obstruction recorded for the cumulative `γ_k` (the contracting volume case can fall
  to `−∞`). So `γ_d` is recorded only as the deterministic `log⁺`-determinant `limsup`.

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58.
-/

open Module InnerProductSpace MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- **Product of all singular values = `|det|`** (the crux infra lemma). For a square matrix
`M : Matrix (Fin d) (Fin d) ℝ`, the product of *all* `d` singular values of `toEuclideanLin M`
equals the absolute value of its determinant: `∏ i, σᵢ(toEuclideanLin M) = |det M|`. Proof: square
the product, use `σᵢ² = eigenvalueᵢ(MᵀM)` (`sq_singularValues_eq_gram_eigenvalue`) and
`det = ∏ eigenvalues` for the symmetric Gram operator
(`LinearMap.IsSymmetric.det_eq_prod_eigenvalues`), giving `(∏σ)² = det(MᵀM) = (det M)²`; then take
the (nonnegative) square root. No invertibility is required. -/
theorem prod_singularValues_eq_abs_det [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ) :
    ∏ i : Fin d, (Matrix.toEuclideanLin M).singularValues (i : ℕ) = |M.det| := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  -- The full product over `Fin d` is nonnegative.
  have hnn : 0 ≤ ∏ i : Fin d, (Matrix.toEuclideanLin M).singularValues (i : ℕ) :=
    Finset.prod_nonneg fun i _ => (Matrix.toEuclideanLin M).singularValues_nonneg i
  -- `(∏ σᵢ)² = ∏ σᵢ²`.
  have hsq : (∏ i : Fin d, (Matrix.toEuclideanLin M).singularValues (i : ℕ)) ^ 2
      = ∏ i : Fin d, (Matrix.toEuclideanLin M).singularValues (i : ℕ) ^ 2 := by
    rw [← Finset.prod_pow]
  -- Each squared singular value is the corresponding Gram eigenvalue.
  have heig : ∏ i : Fin d, (Matrix.toEuclideanLin M).singularValues (i : ℕ) ^ 2
      = ∏ i : Fin d,
          (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues hfin i :=
    Finset.prod_congr rfl fun i _ => sq_singularValues_eq_gram_eigenvalue M hfin i
  -- The product of eigenvalues of the symmetric Gram operator is its determinant.
  have hdet : ∏ i : Fin d,
        (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues hfin i
      = LinearMap.det ((Matrix.toEuclideanLin M).adjoint ∘ₗ (Matrix.toEuclideanLin M)) := by
    rw [(Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.det_eq_prod_eigenvalues hfin]
    norm_num
  -- The Gram operator is `toEuclideanLin (MᵀM)`, whose determinant is `(det M)²`.
  have hgram : LinearMap.det
        ((Matrix.toEuclideanLin M).adjoint ∘ₗ (Matrix.toEuclideanLin M)) = M.det ^ 2 := by
    rw [adjoint_comp_self_eq_gram, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
      Matrix.det_mul, Matrix.det_transpose, sq]
  -- Assemble `(∏ σᵢ)² = (det M)²` and take the nonnegative square root.
  have hkey : (∏ i : Fin d, (Matrix.toEuclideanLin M).singularValues (i : ℕ)) ^ 2
      = M.det ^ 2 := by
    rw [hsq, heig, hdet, hgram]
  have habs : |∏ i : Fin d, (Matrix.toEuclideanLin M).singularValues (i : ℕ)| = |M.det| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, hkey]
  rwa [abs_of_nonneg hnn] at habs

omit [MeasurableSpace X] in
/-- **`sprod` at the top index `k = d` is the absolute determinant** (deterministic, every `n`,
`x`). The full cumulative singular-value product over `Finset.range d` is the product over all of
`Fin d` (`Fin.prod_univ_eq_prod_range`), which equals `|det(A⁽ⁿ⁾ x)|`
(`prod_singularValues_eq_abs_det`): `sprod A T d n x = |det(A⁽ⁿ⁾ x)|`. -/
theorem sprod_full_eq_abs_det [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) :
    sprod A T d n x = |(cocycle A T n x).det| := by
  rw [sprod, ← Fin.prod_univ_eq_prod_range
      (fun i => (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i) d,
    prod_singularValues_eq_abs_det]

omit [MeasurableSpace X] in
/-- **`γ_d` is exactly the forward `log⁺`-determinant `limsup`** (deterministic, every `x`).
Rewriting the defining `limsup` of `γ_d` through `sprod_full_eq_abs_det`
(`sprod_d = |det(A⁽ⁿ⁾)|`) turns it into the `limsup` of the `EReal`-coerced
`(1/n) log⁺|det(A⁽ⁿ⁾ x)|`. This is the full-`d` (volume-growth) specialization of the cumulative
forward singular exponent. -/
theorem forwardSingularExponent_full_eq [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) :
    forwardSingularExponent A T d x
      = Filter.limsup
          (fun n : ℕ =>
            (((n : ℝ)⁻¹ * Real.posLog |(cocycle A T n x).det| : ℝ) : EReal)) atTop := by
  rw [forwardSingularExponent]
  refine Filter.limsup_congr (Filter.Eventually.of_forall fun n => ?_)
  rw [sprod_full_eq_abs_det A n x]

end Oseledets
