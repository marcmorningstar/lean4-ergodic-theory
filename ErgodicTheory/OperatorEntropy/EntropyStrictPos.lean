import ErgodicTheory.OperatorEntropy.Basic

/-!
# Strict positivity of von Neumann entropy for non-idempotent states

A density matrix `ρ` has vanishing von Neumann entropy exactly when it is a *pure* state, i.e.
a rank-one projection, which is the same as saying `ρ` is idempotent: `ρ² = ρ`.  This module
records the strict-positivity half of that dichotomy: if `ρ` is **not** idempotent then its
entropy is strictly positive.

The proof is the spectral argument.  Entropy is a nonnegative sum, so it vanishes iff every
summand `negMulLog(λᵢ)` vanishes; on `[0,1]` this forces each eigenvalue into `{0,1}`.  A
diagonal matrix with `{0,1}` entries is idempotent, and idempotency is transported through the
spectral unitary (a `*`-algebra automorphism, hence multiplicative), yielding `ρ² = ρ` — the
contradiction.
-/

open Matrix Real
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Strict positivity of von Neumann entropy for a non-idempotent state.**  If the density
matrix `ρ` is not idempotent (`ρ² ≠ ρ`), then its von Neumann entropy is strictly positive.
Equivalently: a zero-entropy state is a pure state, hence a projection. -/
theorem vonNeumannEntropy_pos_of_sq_ne (ρ : DensityMatrix n) (h : ρ.val * ρ.val ≠ ρ.val) :
    0 < vonNeumannEntropy ρ := by
  rcases (vonNeumannEntropy_nonneg ρ).lt_or_eq with hlt | heq
  · exact hlt
  · refine absurd ?_ h
    have hA := ρ.posSemidef.1
    have hsum : ∑ i, Real.negMulLog (hA.eigenvalues i) = 0 := heq.symm
    have hterm : ∀ i ∈ Finset.univ, Real.negMulLog (hA.eigenvalues i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Real.negMulLog_nonneg (ρ.eigenvalues_nonneg i) (ρ.eigenvalues_le_one i)).mp hsum
    have key : ∀ i, hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
      intro i
      have hz := hterm i (Finset.mem_univ i)
      simp only [Real.negMulLog_eq_neg, neg_eq_zero, mul_eq_zero, Real.log_eq_zero] at hz
      rcases hz with h0 | h0 | h1 | hm1
      · exact Or.inl h0
      · exact Or.inl h0
      · exact Or.inr h1
      · exact absurd (hm1 ▸ ρ.eigenvalues_nonneg i) (by norm_num)
    have hDD : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℂ)
        * diagonal (RCLike.ofReal ∘ hA.eigenvalues)
          = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      refine congrArg diagonal (funext fun i => ?_)
      rcases key i with h0 | h1
      · simp [Function.comp_apply, h0]
      · simp [Function.comp_apply, h1]
    have hspec := hA.spectral_theorem
    rw [hspec, ← map_mul, hDD]

end ErgodicTheory.OperatorEntropy
