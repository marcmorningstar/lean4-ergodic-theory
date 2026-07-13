import ErgodicTheory.OperatorEntropy.CNT.Refinement
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# A canonical-MASA incompatibility certificate for CNT dynamics and the seal

This module records a concrete, fully computational obstruction living inside the
Connes–Narnhofer–Thirring quantum dynamical entropy framework (CNT, *Comm. Math. Phys.* **112**
(1987)): the "seal" (a fixed maximal abelian subalgebra, or MASA — here the diagonal) and the
dynamics cannot share a *canonical* invariant MASA.

Two structural facts, each verified by hand on an explicit `2 × 2` example, package the
incompatibility:

* **The seal's MASA is not dynamics-invariant.** The dynamics `qDynamics = Ad(U)` does not
  preserve the diagonal subalgebra: `not_preservesDiag_qDynamics`. Concretely `U · diag(1,0) · Uᴴ`
  has a nonzero `(1,0)` entry.
* **The dynamics' MASA is not seal-invariant.** The unique `Ad(U)`-invariant MASA is the eigenbasis
  of `U`, i.e. the commutant of the eigenprojection `eigProj`. The seal's dephasing map
  `E(M) = diagonal (diag M)` moves `eigProj` out of that MASA: `E(eigProj)` fails to commute with
  `eigProj` (`dephase_eigProj_not_commute`).

The dynamics unitary is a **Pythagorean** `(3,4,5)` rotation of the eigenbasis composed with the
phase `diag(1, i)`; all entries lie in `ℚ(i)` (no square roots), so every claim reduces to
`norm_num` over the rationals.  Explicitly `U = V · diag(1, i) · Vᵀ` with the real orthogonal
`V = !![4/5, -3/5; 3/5, 4/5]`, and `eigProj = V · diag(1, 0) · Vᵀ = !![16/25, 12/25; 12/25, 9/25]`
is the eigenprojection onto the first eigenvector of `U`.

## Scope and honest disclosure

* The genuinely strong statement — that there is **no** common invariant MASA over *all* unitary
  conjugates of the diagonal — is *true* for this `U`, but its formalization over the full unitary
  group is deferred (it is large). It rests on: (i) the dephasing-invariant MASAs of `M₂` are
  exactly the diagonal MASA together with the mutually-unbiased ("circular") ones; (ii) the only
  `Ad(U)`-invariant MASA is `U`'s eigenbasis (because `U²` is non-scalar, ruling out the swap-type
  MASAs); and (iii) `U`'s eigenbasis is neither diagonal nor unbiased — indeed
  `|V₀₀|² = 16/25 ≠ 1/2`. What is formalized here is the concrete pairwise failure on the two
  canonical candidate MASAs (the seal's diagonal and the dynamics' eigenbasis), which is the honest
  operational core of the obstruction.
* **A documented landmine.** The natural Hadamard/rotation choices *fail* to witness this
  certificate: the "circular" (mutually unbiased) basis is simultaneously dephasing-invariant *and*
  swap-invariant, so it is a common MASA. The Pythagorean tilt above is chosen precisely to dodge
  that degeneracy.
* By Skolem–Noether every unital `*`-endomorphism of `Mₙ` is inner, hence conjugation by a unitary,
  and therefore *always* preserves some MASA (the eigenbasis of that unitary). The certificate is
  necessarily a statement about the **pair** (dynamics, seal), never about a single map.

References: Connes–Narnhofer–Thirring, *Dynamical entropy of C\*-algebras and von Neumann
algebras*, Comm. Math. Phys. **112** (1987) 691–719; and the mutually-unbiased-bases literature
(e.g. Durt–Englert–Bengtsson–Życzkowski, *On mutually unbiased bases*, Int. J. Quantum Inf. **8**
(2010)) for the characterization of dephasing-invariant MASAs.
-/

open Matrix

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

/-! ## 1. Conjugation by a unitary as a unital `*`-endomorphism -/

/-- Conjugation `x ↦ U x Uᴴ` by a unitary `U` (`Uᴴ U = 1` and `U Uᴴ = 1`), packaged as a unital
`*`-endomorphism of the matrix algebra.  This is the Skolem–Noether normal form of a unital
`*`-endomorphism of `Mₙ(ℂ)`. -/
def adUnitary {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hL : Uᴴ * U = 1) (hR : U * Uᴴ = 1) :
    UnitalStarEndo d where
  toFun x := U * x * Uᴴ
  map_zero := by rw [mul_zero, zero_mul]
  map_add x y := by rw [mul_add, add_mul]
  map_one := by rw [mul_one, hR]
  map_mul x y := by
    show U * (x * y) * Uᴴ = U * x * Uᴴ * (U * y * Uᴴ)
    simp only [mul_assoc]
    rw [← mul_assoc Uᴴ U, hL, one_mul]
  map_star x := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      mul_assoc]

@[simp] theorem adUnitary_toFun {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hL : Uᴴ * U = 1)
    (hR : U * Uᴴ = 1) (x : Matrix (Fin d) (Fin d) ℂ) :
    (adUnitary U hL hR).toFun x = U * x * Uᴴ := rfl

/-! ## 2. The concrete Pythagorean dynamics unitary -/

/-- The dynamics unitary `U = V · diag(1, i) · Vᵀ`, with `V = !![4/5, -3/5; 3/5, 4/5]` the
Pythagorean `(3,4,5)` rotation.  All entries lie in `ℚ(i)`. -/
def dynU : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 25 : ℂ) • !![16 + 9 * Complex.I, 12 - 12 * Complex.I;
                    12 - 12 * Complex.I, 9 + 16 * Complex.I]

theorem dynU_star : dynUᴴ * dynU = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Complex.normSq] <;> norm_num

theorem dynU_star' : dynU * dynUᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Complex.normSq] <;> norm_num

/-- The concrete CNT dynamics: conjugation by the Pythagorean unitary `dynU`. -/
def qDynamics : UnitalStarEndo 2 := adUnitary dynU dynU_star dynU_star'

/-! ## 3. The seal's diagonal MASA is not dynamics-invariant -/

/-- A `*`-endomorphism preserves the diagonal MASA (the seal) if it maps every diagonal matrix to a
diagonal matrix. -/
def PreservesDiag (Φ : UnitalStarEndo 2) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.IsDiag → (Φ.toFun A).IsDiag

/-- **Headline 1.** The dynamics does not preserve the seal's diagonal MASA: `qDynamics` maps the
diagonal projection `diag(1, 0)` to a matrix with a nonzero off-diagonal `(1,0)` entry, namely
`U₁₀ · conj U₀₀ = (12 - 12i)(16 - 9i)/625 = (84 - 300i)/625 ≠ 0`. -/
theorem not_preservesDiag_qDynamics : ¬ PreservesDiag qDynamics := by
  intro h
  have hd : (!![(1 : ℂ), 0; 0, 0]).IsDiag := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h10 := h _ hd (show (1 : Fin 2) ≠ 0 by decide)
  simp only [qDynamics, adUnitary_toFun] at h10
  norm_num [dynU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul, Complex.ext_iff] at h10

/-! ## 4. The dynamics' eigenbasis MASA is not seal-invariant -/

/-- The eigenprojection of `dynU` onto its first eigenvector, `eigProj = V · diag(1,0) · Vᵀ`; a real
rational symmetric idempotent.  Its commutant is the unique `Ad(dynU)`-invariant MASA. -/
def eigProj : Matrix (Fin 2) (Fin 2) ℂ :=
  !![16 / 25, 12 / 25; 12 / 25, 9 / 25]

/-- **Headline 2.** The seal's dephasing map `E(M) = diagonal (diag M)` sends the dynamics'
eigenprojection out of its own MASA: `E(eigProj)` does not commute with `eigProj`.  The commutator's
`(0,1)` entry is `eigProj₀₁ · (16/25 - 9/25) = (12/25)(7/25) ≠ 0`, so
`E(eigProj) = diag(16/25, 9/25)` is not in the commutant of `eigProj`; the dynamics' invariant MASA
is therefore not seal-invariant. -/
theorem dephase_eigProj_not_commute :
    ¬ (Matrix.diagonal (Matrix.diag eigProj) * eigProj
        = eigProj * Matrix.diagonal (Matrix.diag eigProj)) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp only [eigProj, Matrix.mul_apply, Matrix.diagonal, Matrix.diag, Matrix.of_apply] at h01
  norm_num [Fin.sum_univ_two, Complex.ext_iff] at h01

/-! ## 5. The packaged incompatibility certificate -/

/-- **Canonical-MASA incompatibility certificate** for the pair (`qDynamics`, seal).  Neither of the
two canonical candidate MASAs is invariant for both maps:

* the seal's diagonal MASA is not preserved by the dynamics (`not_preservesDiag_qDynamics`), and
* the dynamics' eigenbasis MASA (commutant of `eigProj`) is not preserved by the seal's dephasing
  map (`dephase_eigProj_not_commute`).

The seal fixes the diagonal MASA once and for all, while the dynamics' only invariant MASA is its
eigenbasis; the two disagree, and there is no canonical common invariant MASA.

Honest scope (see the module docstring): the *full* `∀`-MASA statement (no common invariant MASA
across all unitary conjugates of the diagonal) is true for this `U` — its eigenbasis is neither
diagonal nor unbiased, `|V₀₀|² = 16/25 ≠ 1/2` — but its formalization over the whole unitary group
is deferred as large.  Note the landmine: the natural Hadamard/rotation choices *fail* the
certificate, because the circular (mutually unbiased) basis is simultaneously dephasing-invariant
and swap-invariant; the Pythagorean tilt is chosen to avoid that degeneracy.  Finally, by
Skolem–Noether every unital `*`-endomorphism of `Mₙ` is inner and hence preserves *some* MASA, so
the certificate is necessarily about the pair, never a single map.  (CNT 1987.) -/
theorem qDynamics_seal_no_common_canonical_masa :
    ¬ PreservesDiag qDynamics ∧
      ¬ (Matrix.diagonal (Matrix.diag eigProj) * eigProj
          = eigProj * Matrix.diagonal (Matrix.diag eigProj)) :=
  ⟨not_preservesDiag_qDynamics, dephase_eigProj_not_commute⟩

end ErgodicTheory.OperatorEntropy.CNT
