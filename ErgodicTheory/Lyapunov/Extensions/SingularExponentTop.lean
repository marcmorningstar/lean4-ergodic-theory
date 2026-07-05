/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.SingularExponentBounds

/-!
# Top singular value = operator norm, and the `k = 1` singular exponent tie-in

This module supplies the infrastructure lemma left open by
`ErgodicTheory/Lyapunov/Extensions/SingularExponentBounds.lean`: the **largest singular value of a
matrix equals its L2 operator norm**,

`σ₀(toEuclideanLin M) = ‖M‖`.

The singular values `LinearMap.singularValues` are the descending square roots of the eigenvalues
of `adjoint f ∘ₗ f`, so `σ₀` is the *largest* one. The bound `σ₀ ≤ ‖M‖` is already available
(`ErgodicTheory.sigma_le_opNorm`). The reverse `‖M‖ ≤ σ₀` is the new content: for every vector `x`,
`‖f x‖² = ⟪(adjoint f ∘ₗ f) x, x⟫ = Σᵢ eᵢ ⟪uᵢ, x⟫² ≤ e₀ Σᵢ ⟪uᵢ, x⟫² = σ₀² ‖x‖²`, where `u` is
the eigenvector basis of `adjoint f ∘ₗ f` and `e` its descending eigenvalues (`e₀ = σ₀²`). Hence
`‖f x‖ ≤ σ₀ ‖x‖`, giving `‖M‖ = ‖toEuclideanLin M‖ ≤ σ₀` via `ContinuousLinearMap.opNorm_le_bound`.

With `σ₀ = ‖M‖` in hand, the `k = 1` singular-value product collapses to the operator norm
(`sprod A T 1 n x = ‖A⁽ⁿ⁾(x)‖`), so the cumulative forward singular exponent `γ₁` is *exactly* the
forward `log⁺`-operator-norm `limsup` (`forwardPosLogNormLimsup`); this is the identity that
`SingularExponentBounds.lean` could only state as a one-sided ceiling. Under ergodicity it pins
`γ₁` to the a.e.-constant forward top value `λ₁⁺`.

## Main results

* `ErgodicTheory.top_singularValue_eq_opNorm` — `σ₀(toEuclideanLin M) = ‖M‖` (the crux infra lemma).
* `ErgodicTheory.sprod_one_eq_opNorm` — `sprod A T 1 n x = ‖A⁽ⁿ⁾(x)‖`.
* `ErgodicTheory.forwardSingularExponent_one_eq` — `γ₁(x) = forwardPosLogNormLimsup A T x`
  (deterministic, every `x`).
* `ErgodicTheory.ae_forwardSingularExponent_one_eq_topExponent` — under ergodicity, `γ₁ = (λ₁⁺ : EReal)`
  `μ`-a.e. for a real constant `λ₁⁺` (the headline tie-in).

## References

* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open Module InnerProductSpace MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

namespace LinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Top singular value bounds the image norm.** For every `x`, `‖f x‖ ≤ σ₀(f) · ‖x‖`. Expanding
`x` in the eigenvector basis `u` of `adjoint f ∘ₗ f` (with descending eigenvalues `e`, so
`e₀ = σ₀²` is the largest), `‖f x‖² = ⟪(adjoint f ∘ₗ f) x, x⟫ = Σᵢ eᵢ ⟪uᵢ, x⟫² ≤ e₀ Σᵢ ⟪uᵢ, x⟫²
= σ₀² ‖x‖²`. -/
theorem norm_apply_le_top_singularValue (f : E →ₗ[ℝ] F) [Nonempty (Fin (finrank ℝ E))] (x : E) :
    ‖f x‖ ≤ f.singularValues 0 * ‖x‖ := by
  set n := finrank ℝ E with hn
  set S := LinearMap.adjoint f ∘ₗ f with hS
  set hT := f.isSymmetric_adjoint_comp_self with hThT
  set u := hT.eigenvectorBasis hn.symm with hu
  set e := hT.eigenvalues hn.symm with he
  -- `σ₀² = e₀`, the largest eigenvalue.
  have hi0 : (0 : ℕ) < n := Fin.pos_iff_nonempty.mpr ‹_›
  have hsq0 : f.singularValues 0 ^ 2 = e ⟨0, hi0⟩ :=
    f.sq_singularValues_of_lt hn.symm hi0
  have hσ0_nonneg : 0 ≤ f.singularValues 0 := f.singularValues_nonneg 0
  -- `‖f x‖² = ⟪S x, x⟫`.
  have hnormsq : ‖f x‖ ^ 2 = (inner ℝ (S x) x : ℝ) := by
    rw [hS, LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  -- Expand `x` over the orthonormal eigenbasis and diagonalize `S`.
  have hSx : S x = ∑ i : Fin n, (e i * ⟪u i, x⟫) • u i := by
    conv_lhs => rw [← u.sum_repr' x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    have happ : S (u i) = (e i : ℝ) • u i := hT.apply_eigenvectorBasis _ i
    rw [happ, smul_smul, mul_comm]
  -- `⟪S x, x⟫ = Σ eᵢ ⟪uᵢ, x⟫²`.
  have hinner : (inner ℝ (S x) x : ℝ) = ∑ i : Fin n, e i * ⟪u i, x⟫ ^ 2 := by
    rw [hSx, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, sq]
    ring
  -- `Σ eᵢ ⟪uᵢ, x⟫² ≤ e₀ Σ ⟪uᵢ, x⟫² = σ₀² ‖x‖²`.
  have hbound : (inner ℝ (S x) x : ℝ) ≤ f.singularValues 0 ^ 2 * ‖x‖ ^ 2 := by
    rw [hinner, hsq0]
    have hsum : ∑ i : Fin n, e ⟨0, hi0⟩ * ⟪u i, x⟫ ^ 2 = e ⟨0, hi0⟩ * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      have := u.sum_sq_norm_inner_right x
      simpa [Real.norm_eq_abs, sq_abs] using this
    rw [← hsum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact hT.eigenvalues_antitone hn.symm (Fin.mk_le_mk.mpr (Nat.zero_le _))
  -- `‖f x‖² ≤ (σ₀ ‖x‖)²`, conclude `‖f x‖ ≤ σ₀ ‖x‖`.
  have hle_sq : ‖f x‖ ^ 2 ≤ (f.singularValues 0 * ‖x‖) ^ 2 := by
    rw [hnormsq, mul_pow]; exact hbound
  exact le_of_sq_le_sq hle_sq (mul_nonneg hσ0_nonneg (norm_nonneg _))

end LinearMap

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- **Top singular value = L2 operator norm.** For a square matrix `M : Matrix (Fin d) (Fin d) ℝ`
with `d ≠ 0`, the largest singular value of `toEuclideanLin M` equals the L2 operator norm `‖M‖`:
`σ₀(toEuclideanLin M) = ‖M‖`. The `≤` direction is `ErgodicTheory.sigma_le_opNorm`; the `≥` direction
is `ContinuousLinearMap.opNorm_le_bound` fed the per-vector bound
`LinearMap.norm_apply_le_top_singularValue` (`‖f x‖ ≤ σ₀ · ‖x‖`), using
`‖M‖ = ‖LinearMap.toContinuousLinearMap (toEuclideanLin M)‖`. -/
theorem top_singularValue_eq_opNorm [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ) :
    (Matrix.toEuclideanLin M).singularValues 0 = ‖M‖ := by
  set f := Matrix.toEuclideanLin M with hf
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hne : Nonempty (Fin (finrank ℝ (EuclideanSpace ℝ (Fin d)))) := by
    rw [hfin]; exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  refine le_antisymm (sigma_le_opNorm M 0) ?_
  -- `‖M‖ = ‖toContinuousLinearMap f‖ ≤ σ₀` from the per-vector bound.
  have hnorm : ‖M‖ = ‖LinearMap.toContinuousLinearMap f‖ := rfl
  rw [hnorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (f.singularValues_nonneg 0) (fun x => ?_)
  rw [LinearMap.coe_toContinuousLinearMap']
  exact f.norm_apply_le_top_singularValue x

omit [MeasurableSpace X] in
/-- **`sprod` at `k = 1` is the operator norm.** The top-`1` singular-value product is just the
largest singular value (`Finset.prod_range_one`), which equals `‖A⁽ⁿ⁾(x)‖`
(`top_singularValue_eq_opNorm`): `sprod A T 1 n x = ‖cocycle A T n x‖`. -/
theorem sprod_one_eq_opNorm [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ)
    (x : X) : sprod A T 1 n x = ‖cocycle A T n x‖ := by
  rw [sprod, Finset.prod_range_one, top_singularValue_eq_opNorm]

omit [MeasurableSpace X] in
/-- **`γ₁` is exactly the forward `log⁺`-operator-norm `limsup`** (deterministic, every `x`).
Rewriting the defining `limsup` of `γ₁` through `sprod_one_eq_opNorm` (`sprod_1 = ‖A⁽ⁿ⁾‖`) turns
it into the `limsup` of `(1/n) log⁺‖A⁽ⁿ⁾‖`, i.e. `forwardPosLogNormLimsup A T x`. This sharpens
the one-sided ceiling `forwardSingularExponent_le_natCast_mul` (at `k = 1`) to an equality. -/
theorem forwardSingularExponent_one_eq [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) : forwardSingularExponent A T 1 x = forwardPosLogNormLimsup A T x := by
  rw [forwardSingularExponent, forwardPosLogNormLimsup]
  refine Filter.limsup_congr (Filter.Eventually.of_forall fun n => ?_)
  rw [sprod_one_eq_opNorm]

/-- **The `k = 1` singular exponent tie-in (headline).** For an ergodic measure-preserving `T` and
a possibly-singular measurable generator with `log⁺‖A‖ ∈ L¹`, there is a real constant `λ₁⁺` (the
forward top value of `tendsto_top_posLogNorm`) such that the cumulative forward singular exponent
`γ₁` equals `(λ₁⁺ : EReal)` for `μ`-a.e. `x`. Via `forwardSingularExponent_one_eq`, `γ₁` is the
`limsup` of the `EReal`-coerced `(1/n) log⁺‖A⁽ⁿ⁾‖`; on the a.e. convergence set this sequence
tends to `(λ₁⁺ : EReal)` (`continuous_coe_real_ereal`), so its `limsup` is `(λ₁⁺ : EReal)`
(`Tendsto.limsup_eq`). -/
theorem ae_forwardSingularExponent_one_eq_topExponent {μ : Measure X} [IsProbabilityMeasure μ]
    [NeZero d] (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ, forwardSingularExponent A T 1 x = (lam : EReal) := by
  obtain ⟨lam, hlam⟩ := tendsto_top_posLogNorm hT hAmeas hint
  refine ⟨lam, ?_⟩
  filter_upwards [hlam] with x hx
  rw [forwardSingularExponent_one_eq, forwardPosLogNormLimsup]
  have hxE : Tendsto
      (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
      (𝓝 (lam : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hx
  exact hxE.limsup_eq

end ErgodicTheory

end
