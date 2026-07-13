/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.RelativeEntropy
import ErgodicTheory.OperatorEntropy.DiagonalSpectrum

/-!
# Issue #59 (tiers T2a/T2b) — shared spectral lemmas for the quantum recovery seal

Three reusable facts about the von Neumann and Umegaki relative entropies, feeding the
`QuantumSeal` module:

* `vonNeumannEntropy_eq_zero_of_sq_eq` — the converse of `vonNeumannEntropy_pos_of_sq_ne`: an
  **idempotent** (pure / projection) state has zero von Neumann entropy.  Spectral argument:
  `ρ² = ρ` transports through the eigenbasis to `D² = D` for the diagonal of eigenvalues, forcing
  every eigenvalue into `{0,1}`, on which `negMulLog` vanishes.
* `vonNeumannEntropy_conj` — **unitary invariance** of the von Neumann entropy.  Conjugation by a
  unitary is a similarity, so the characteristic polynomial (hence the eigenvalue multiset, hence
  the spectral entropy sum) is preserved.  Proved via `Matrix.charpoly_mul_comm`.
* `relEntropy_maximallyMixed` — `D(ρ ‖ I/d) = log d − S(ρ)`.  The maximally mixed state has all
  eigenvalues `1/d`, so the cross term collapses through the doubly-stochastic row sum
  (`crossOverlap` row-sum-`1`, as in `relEntropy_nonneg`) to `−log d · Tr ρ = −log d`.
-/

open Matrix Real Polynomial
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## (1) Zero entropy for an idempotent (pure) state -/

/-- **Zero von Neumann entropy for an idempotent state.**  If the density matrix `ρ` is a
projection (`ρ² = ρ`), then its von Neumann entropy vanishes.  This is the converse of
`vonNeumannEntropy_pos_of_sq_ne`: a projection has eigenvalues in `{0,1}`, on which `negMulLog`
is zero. -/
theorem vonNeumannEntropy_eq_zero_of_sq_eq (ρ : DensityMatrix n) (h : ρ.val * ρ.val = ρ.val) :
    vonNeumannEntropy ρ = 0 := by
  have hρ : ρ.val
      = ρ.eigVec * diagonal (fun k => (ρ.eig k : ℂ)) * star ρ.eigVec := by
    have hs := ρ.posSemidef.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    have hRC : (RCLike.ofReal ∘ ρ.posSemidef.1.eigenvalues) = fun k => (ρ.eig k : ℂ) := rfl
    rw [hRC] at hs
    exact hs
  have hss : star ρ.eigVec * ρ.eigVec = 1 :=
    Unitary.coe_star_mul_self ρ.posSemidef.1.eigenvectorUnitary
  have hss' : ρ.eigVec * star ρ.eigVec = 1 :=
    Unitary.coe_mul_star_self ρ.posSemidef.1.eigenvectorUnitary
  have hD : star ρ.eigVec * ρ.val * ρ.eigVec = diagonal (fun k => (ρ.eig k : ℂ)) := by
    rw [hρ,
      show star ρ.eigVec * (ρ.eigVec * diagonal (fun k => (ρ.eig k : ℂ)) * star ρ.eigVec)
            * ρ.eigVec
          = star ρ.eigVec * ρ.eigVec * diagonal (fun k => (ρ.eig k : ℂ))
            * (star ρ.eigVec * ρ.eigVec) by simp only [mul_assoc],
      hss, one_mul, mul_one]
  have hDsq : diagonal (fun k => (ρ.eig k : ℂ)) * diagonal (fun k => (ρ.eig k : ℂ))
      = diagonal (fun k => (ρ.eig k : ℂ)) := by
    conv_lhs => rw [← hD]
    rw [show star ρ.eigVec * ρ.val * ρ.eigVec * (star ρ.eigVec * ρ.val * ρ.eigVec)
          = star ρ.eigVec * (ρ.val * (ρ.eigVec * star ρ.eigVec) * ρ.val) * ρ.eigVec
          by simp only [mul_assoc], hss', mul_one, h, hD]
  rw [Matrix.diagonal_mul_diagonal] at hDsq
  unfold vonNeumannEntropy
  apply Finset.sum_eq_zero
  intro k _
  have hpt : ρ.eig k * ρ.eig k = ρ.eig k := by
    have h2 := congrFun (Matrix.diagonal_injective hDsq) k
    exact_mod_cast h2
  have hz : ρ.eig k * (ρ.eig k - 1) = 0 := by rw [mul_sub, mul_one, hpt, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h1
  · change Real.negMulLog (ρ.eig k) = 0
    rw [h0, Real.negMulLog_zero]
  · change Real.negMulLog (ρ.eig k) = 0
    rw [show ρ.eig k = 1 by linarith, Real.negMulLog_one]

/-! ## (2) Unitary invariance of the von Neumann entropy -/

/-- **Unitary invariance of the von Neumann entropy.**  `S(U ρ Uᴴ) = S(ρ)`: conjugation by a
unitary is a similarity, so the characteristic polynomial and hence the eigenvalue multiset (the
spectral data of `S`) is preserved. -/
theorem vonNeumannEntropy_conj (ρ : DensityMatrix n) (U : Matrix.unitaryGroup n ℂ) :
    vonNeumannEntropy (ρ.conj U) = vonNeumannEntropy ρ := by
  have hcp : (ρ.conj U).val.charpoly = ρ.val.charpoly := by
    change ((U : Matrix n n ℂ) * ρ.val * star (U : Matrix n n ℂ)).charpoly = ρ.val.charpoly
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  have hmulti : Finset.univ.val.map (ρ.conj U).eig = Finset.univ.val.map ρ.eig := by
    apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
    simp only [DensityMatrix.eig]
    rw [Multiset.map_map, Multiset.map_map,
      ← (ρ.conj U).posSemidef.1.roots_charpoly_eq_eigenvalues,
      ← ρ.posSemidef.1.roots_charpoly_eq_eigenvalues, hcp]
  unfold vonNeumannEntropy
  have h := congrArg (fun m : Multiset ℝ => (m.map Real.negMulLog).sum) hmulti
  simpa only [DensityMatrix.eig, Multiset.map_map, Finset.sum_eq_multiset_sum,
    Function.comp_def] using h

/-! ## (3) Relative entropy against the maximally mixed state -/

/-- Every eigenvalue of the maximally mixed state `I/d` is `1/d`. -/
theorem DensityMatrix.maximallyMixed_eig [Nonempty n] (m : n) :
    (DensityMatrix.maximallyMixed : DensityMatrix n).eig m = (Fintype.card n : ℝ)⁻¹ := by
  set c : ℝ := (Fintype.card n : ℝ)⁻¹ with hc
  have hval : (DensityMatrix.maximallyMixed : DensityMatrix n).val
      = Matrix.diagonal (fun _ : n => (c : ℂ)) := by
    ext i j
    simp only [DensityMatrix.maximallyMixed, Matrix.smul_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp [hij, Complex.real_smul, hc]
    · simp [hij]
  have hmulti :
      Finset.univ.val.map (DensityMatrix.maximallyMixed : DensityMatrix n).eig
        = Finset.univ.val.map (fun _ : n => c) := by
    apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
    simp only [DensityMatrix.eig]
    rw [Multiset.map_map, Multiset.map_map,
      ← (DensityMatrix.maximallyMixed : DensityMatrix n).posSemidef.1.roots_charpoly_eq_eigenvalues,
      hval, charpoly_diagonal, roots_prod_X_sub_C_comp]
    refine Multiset.map_congr rfl fun i _ => ?_
    rfl
  have hmem : (DensityMatrix.maximallyMixed : DensityMatrix n).eig m
      ∈ Finset.univ.val.map (fun _ : n => c) :=
    hmulti ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ m)
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  exact hi.symm

/-- **Relative entropy against the maximally mixed state.**
`D(ρ ‖ I/d) = log d − S(ρ)`.  The maximally mixed state has all eigenvalues `1/d`, so the cross
term collapses via the doubly-stochastic row sum to `−log d · Tr ρ = −log d`; the diagonal term is
`−S(ρ)`. -/
theorem relEntropy_maximallyMixed [Nonempty n] (ρ : DensityMatrix n) :
    relEntropy ρ DensityMatrix.maximallyMixed
      = Real.log (Fintype.card n) - vonNeumannEntropy ρ := by
  set mm := (DensityMatrix.maximallyMixed : DensityMatrix n) with hmm
  -- row sums of the overlap matrix are 1 (doubly stochastic)
  set Q : Matrix n n ℂ := star ρ.eigVec * mm.eigVec with hQ_def
  have hρss : star ρ.eigVec * ρ.eigVec = 1 :=
    Unitary.coe_star_mul_self ρ.posSemidef.1.eigenvectorUnitary
  have hmss : star mm.eigVec * mm.eigVec = 1 :=
    Unitary.coe_star_mul_self mm.posSemidef.1.eigenvectorUnitary
  have hmss' : mm.eigVec * star mm.eigVec = 1 :=
    Unitary.coe_mul_star_self mm.posSemidef.1.eigenvectorUnitary
  have hsQ : star Q = star mm.eigVec * ρ.eigVec := by rw [hQ_def, star_mul, star_star]
  have hQss' : Q * star Q = 1 := by
    rw [hsQ, hQ_def, mul_assoc, ← mul_assoc mm.eigVec, hmss', one_mul, hρss]
  have hrow : ∀ k, (∑ m, crossOverlap ρ mm k m) = 1 := by
    intro k
    have hc : ((∑ m, crossOverlap ρ mm k m : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have he : (∑ m, ((crossOverlap ρ mm k m : ℝ) : ℂ)) = (Q * star Q) k k := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [crossOverlap, ← hQ_def]
        rw [Matrix.star_apply, Complex.star_def, Complex.mul_conj]
      rw [he, hQss', Matrix.one_apply_eq]
    exact_mod_cast hc
  -- log of every eigenvalue of mm is −log d
  have hlog : ∀ m, Real.log (mm.eig m) = - Real.log (Fintype.card n) := by
    intro m
    rw [hmm, DensityMatrix.maximallyMixed_eig m, Real.log_inv]
  -- assemble
  have hcross : (∑ k, ∑ m, crossOverlap ρ mm k m * ρ.eig k * Real.log (mm.eig m))
      = - Real.log (Fintype.card n) := by
    have hstep : ∀ k, (∑ m, crossOverlap ρ mm k m * ρ.eig k * Real.log (mm.eig m))
        = ρ.eig k * (- Real.log (Fintype.card n)) := by
      intro k
      calc (∑ m, crossOverlap ρ mm k m * ρ.eig k * Real.log (mm.eig m))
          = ∑ m, crossOverlap ρ mm k m * (ρ.eig k * (- Real.log (Fintype.card n))) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [hlog m]; ring
        _ = (∑ m, crossOverlap ρ mm k m) * (ρ.eig k * (- Real.log (Fintype.card n))) := by
            rw [Finset.sum_mul]
        _ = ρ.eig k * (- Real.log (Fintype.card n)) := by rw [hrow k, one_mul]
    calc (∑ k, ∑ m, crossOverlap ρ mm k m * ρ.eig k * Real.log (mm.eig m))
        = ∑ k, ρ.eig k * (- Real.log (Fintype.card n)) := Finset.sum_congr rfl fun k _ => hstep k
      _ = (∑ k, ρ.eig k) * (- Real.log (Fintype.card n)) := by rw [Finset.sum_mul]
      _ = - Real.log (Fintype.card n) := by
          rw [show (∑ k, ρ.eig k) = 1 from ρ.sum_eigenvalues_eq_one, one_mul]
  have hdiag : (∑ k, ρ.eig k * Real.log (ρ.eig k)) + vonNeumannEntropy ρ = 0 := by
    unfold vonNeumannEntropy
    simp only [DensityMatrix.eig]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k _
    rw [Real.negMulLog_eq_neg]
    ring
  simp only [relEntropy]
  rw [hcross]
  linarith [hdiag]

/-- **Von Neumann entropy of the maximally mixed state.**  `S(I/d) = log d`.  Immediate from
`relEntropy_maximallyMixed` evaluated at `ρ = I/d`, together with `D(I/d ‖ I/d) = 0`. -/
theorem vonNeumannEntropy_maximallyMixed [Nonempty n] :
    vonNeumannEntropy (DensityMatrix.maximallyMixed : DensityMatrix n)
      = Real.log (Fintype.card n) := by
  have h := relEntropy_maximallyMixed (DensityMatrix.maximallyMixed : DensityMatrix n)
  rw [relEntropy_self_eq_zero] at h
  linarith

end ErgodicTheory.OperatorEntropy
