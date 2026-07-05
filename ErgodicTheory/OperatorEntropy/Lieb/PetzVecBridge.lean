/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.PetzReconciliation
import ErgodicTheory.OperatorEntropy.Lieb.ModularOperator

/-!
# Petz equality — the vectorisation bridge (issue #28, STEP 1 → matrix form)

This module discharges the **vectorisation bridge** of the sufficiency (`⟹`) direction of the
Petz-equality theorem (issue #28): it turns the *operator-level* ρ-twisted Petz isometry
`petzW ω X = (X · ω_A^{-1/2} ⊗ 1_B) · ω^{1/2}` (with its three green identities `petzW_isometry`,
`petzW_cyclic`, `petzW_modular_compression` in `PetzReconciliation`) into a genuine **rectangular
matrix** `petzWvec ω` on the vectorised Hilbert–Schmidt spaces, and transports the three identities
to matrix facts about it.

## The vec functor

`vec X : m × m → ℂ`, `vec X (i, j) = X i j`, is the row-major vectorisation of a matrix.  Its two
structural facts are:

* `vec_mul_mul`: the **vec/Kronecker trick** `vec (A · X · C) = (A ⊗ₖ Cᵀ) *ᵥ vec X`.
* `amplMat` + `vec_kron_one` / `vec_partialTraceRight`: the **ampliation** `Y ↦ Y ⊗ₖ 1_B` and the
  **partial trace** `Tr_B` are matricised by a fixed `0/1` matrix `amplMat` and its conjugate
  transpose, `vec (Y ⊗ₖ 1_B) = amplMat *ᵥ vec Y`, `vec (Tr_B Z) = amplMatᴴ *ᵥ vec Z`.

`vec` is bijective (`vec_surjective`) so a matrix is pinned down by its action on all `vec X`
(`eq_of_mulVec_vec`).

## The vectorised Petz isometry and the three bridged identities

`petzWvec ω := (1 ⊗ₖ (ω^{1/2})ᵀ) · amplMat · (1 ⊗ₖ (ω_A^{-1/2})ᵀ)` matricises `petzW ω`
(`vec_petzW`), and its conjugate transpose matricises the adjoint `petzWadj ω`
(`vec_petzWadj`).  Consequently:

* `petzWvec_isometry` — identity **(i)**: `(petzWvec ω)ᴴ · petzWvec ω = 1`.
* `petzWvec_cyclic` — identity **(ii)**: `petzWvec ω *ᵥ vec (ω_A^{1/2}) = vec (ω^{1/2})`.
* `petzWvec_modular_compression` — identity **(iii)**:
  `(petzWvec ω)ᴴ · modArgVec τ ω · petzWvec ω = modArgVec τ_A ω_A`, where `modArgVec τ ω` is the
  vectorised relative modular map `Z ↦ τ Z ω⁻¹` (the Kronecker matrix `τ ⊗ₖ (ω⁻¹)ᵀ`).

These are the three matrix facts (isometry, cyclic-vector, modular-compression) that feed the
resolvent rigidity assembly in `PetzEqualitySufficiency` / `PetzEqualityGeneral`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

open ErgodicTheory.OperatorEntropy

/-! ## The vec functor and the vec/Kronecker trick -/

/-- Row-major **vectorisation** of a matrix: `vec X (i, j) = X i j`. -/
def vec {m : Type*} (X : Matrix m m ℂ) : m × m → ℂ := fun p => X p.1 p.2

@[simp] lemma vec_apply {m : Type*} (X : Matrix m m ℂ) (p : m × m) : vec X p = X p.1 p.2 := rfl

/-- The Hilbert–Schmidt inner product in vectorised form: `⟪vec A, vec B⟫ = tr(Aᴴ B)`. -/
lemma vec_dotProduct_eq_trace {m : Type*} [Fintype m] (A B : Matrix m m ℂ) :
    star (vec A) ⬝ᵥ vec B = (Aᴴ * B).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, vec_apply, RCLike.star_def]

/-- The inverse of `vec`: rebuild a matrix from its vectorisation. -/
def unvec {m : Type*} (v : m × m → ℂ) : Matrix m m ℂ := Matrix.of fun i j => v (i, j)

@[simp] lemma vec_unvec {m : Type*} (v : m × m → ℂ) : vec (unvec v) = v := by
  funext p; obtain ⟨i, j⟩ := p; rfl

lemma vec_surjective {m : Type*} : Function.Surjective (vec (m := m)) :=
  fun v => ⟨unvec v, vec_unvec v⟩

/-- A square matrix is pinned down by the `mulVec`-action on all vectorisations `vec X`. -/
lemma eq_of_mulVec_vec {m : Type*} [Fintype m]
    {M N : Matrix (m × m) (m × m) ℂ} (h : ∀ X : Matrix m m ℂ, M *ᵥ vec X = N *ᵥ vec X) :
    M = N := by
  classical
  refine Matrix.ext_of_mulVec_single fun q => ?_
  obtain ⟨v, hv⟩ := vec_surjective (Pi.single q (1 : ℂ))
  rw [← hv]; exact h v

/-- **The vec / Kronecker trick.** `vec (A · X · C) = (A ⊗ₖ Cᵀ) *ᵥ vec X`. -/
lemma vec_mul_mul {m : Type*} [Fintype m] (A X C : Matrix m m ℂ) :
    vec (A * X * C) = (A ⊗ₖ Cᵀ) *ᵥ vec X := by
  funext p
  obtain ⟨i, k⟩ := p
  rw [vec_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp only [Matrix.kronecker_apply, Matrix.transpose_apply, vec_apply]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Right multiplication.** `vec (X · C) = (1 ⊗ₖ Cᵀ) *ᵥ vec X`. -/
lemma vec_rightMul {m : Type*} [Fintype m] [DecidableEq m] (X C : Matrix m m ℂ) :
    vec (X * C) = ((1 : Matrix m m ℂ) ⊗ₖ Cᵀ) *ᵥ vec X := by
  have h := vec_mul_mul (1 : Matrix m m ℂ) X C
  rwa [Matrix.one_mul] at h

/-! ## The ampliation matrix and the partial trace -/

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- The **ampliation matrix** matricising `Y ↦ Y ⊗ₖ 1_B` under `vec`. -/
def amplMat (nA nB : Type*) [DecidableEq nA] [DecidableEq nB] :
    Matrix ((nA × nB) × (nA × nB)) (nA × nA) ℂ :=
  Matrix.of fun p q => if p.1.1 = q.1 ∧ p.2.1 = q.2 ∧ p.1.2 = p.2.2 then 1 else 0

omit [Fintype nB] in
/-- The `mulVec`-action of the ampliation matrix: it duplicates the entry across the diagonal of
the `B`-factor. -/
lemma amplMat_mulVec (v : nA × nA → ℂ) (a a' : nA) (b b' : nB) :
    (amplMat nA nB *ᵥ v) ((a, b), (a', b')) = if b = b' then v (a, a') else 0 := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (a, a')]
  · simp only [amplMat, Matrix.of_apply]
    by_cases hb : b = b' <;> simp [hb]
  · intro q _ hq
    have hcond : ¬ (a = q.1 ∧ a' = q.2 ∧ b = b') := by
      rintro ⟨h1, h2, _⟩; exact hq (Prod.ext h1.symm h2.symm)
    simp only [amplMat, Matrix.of_apply, if_neg hcond, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype nB] in
/-- **Ampliation transport.** `vec (Y ⊗ₖ 1_B) = amplMat *ᵥ vec Y`. -/
lemma vec_kron_one (Y : Matrix nA nA ℂ) :
    vec (Y ⊗ₖ (1 : Matrix nB nB ℂ)) = amplMat nA nB *ᵥ vec Y := by
  funext p
  obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := p
  rw [vec_apply, Matrix.kronecker_apply, Matrix.one_apply, amplMat_mulVec, vec_apply,
    mul_ite, mul_one, mul_zero]

/-- The `mulVec`-action of the adjoint ampliation matrix: it contracts the `B`-factor diagonal — the
partial trace. -/
lemma amplMatH_mulVec (v : (nA × nB) × (nA × nB) → ℂ) (a a' : nA) :
    ((amplMat nA nB)ᴴ *ᵥ v) (a, a') = ∑ d : nB, v ((a, d), (a', d)) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_apply, amplMat, Matrix.of_apply]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single a']
    · rw [Finset.sum_eq_single d]
      · rw [if_pos ⟨rfl, rfl, rfl⟩, star_one, one_mul]
      · intro d'' _ hd''
        rw [if_neg (fun h => hd'' h.2.2.symm), star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ d) h
    · intro c'' _ hc''
      refine Finset.sum_eq_zero fun d'' _ => ?_
      rw [if_neg (fun h => hc'' h.2.1), star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ a') h
  · intro c'' _ hc''
    refine Finset.sum_eq_zero fun d _ => ?_
    refine Finset.sum_eq_zero fun c''' _ => ?_
    refine Finset.sum_eq_zero fun d'' _ => ?_
    rw [if_neg (fun h => hc'' h.1), star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Partial-trace transport.** `vec (Tr_B Z) = amplMatᴴ *ᵥ vec Z`. -/
lemma vec_partialTraceRight (Z : Matrix (nA × nB) (nA × nB) ℂ) :
    vec (partialTraceRight Z) = (amplMat nA nB)ᴴ *ᵥ vec Z := by
  funext p
  obtain ⟨a, a'⟩ := p
  rw [vec_apply, partialTraceRight_apply, amplMatH_mulVec]
  simp only [vec_apply]

/-! ## The vectorised Petz isometry -/

/-- The **vectorised ρ-twisted Petz reconciliation isometry**: the rectangular matrix matricising
`petzW ω` under `vec`. -/
def petzWvec (ω : Matrix (nA × nB) (nA × nB) ℂ) :
    Matrix ((nA × nB) × (nA × nB)) (nA × nA) ℂ :=
  ((1 : Matrix (nA × nB) (nA × nB) ℂ) ⊗ₖ (ω ^ (1 / 2 : ℝ))ᵀ) * amplMat nA nB
    * ((1 : Matrix nA nA ℂ) ⊗ₖ ((partialTraceRight ω) ^ (-(1 / 2) : ℝ))ᵀ)

/-- The **vectorised relative modular map** `Z ↦ τ Z ω⁻¹`: the Kronecker matrix `τ ⊗ₖ (ω⁻¹)ᵀ`. -/
def modArgVec (τ ω : Matrix (nA × nB) (nA × nB) ℂ) :
    Matrix ((nA × nB) × (nA × nB)) ((nA × nB) × (nA × nB)) ℂ :=
  τ ⊗ₖ (ω ^ (-1 : ℝ))ᵀ

/-- `modArgVec` matricises `modularMap`: `modArgVec τ ω *ᵥ vec Z = vec (modularMap τ ω Z)`. -/
lemma modArgVec_mulVec (τ ω : Matrix (nA × nB) (nA × nB) ℂ)
    (Z : Matrix (nA × nB) (nA × nB) ℂ) :
    modArgVec τ ω *ᵥ vec Z = vec (modularMap τ ω Z) := by
  rw [modArgVec, modularMap, vec_mul_mul]

omit [DecidableEq nB] in
/-- `modArgVec` at the reduced (output) system, matricising `X ↦ τ_A X ω_A⁻¹`. -/
lemma modArgVecA_mulVec (τ ω : Matrix (nA × nB) (nA × nB) ℂ) (X : Matrix nA nA ℂ) :
    ((partialTraceRight τ) ⊗ₖ ((partialTraceRight ω) ^ (-1 : ℝ))ᵀ) *ᵥ vec X
      = vec (partialTraceRight τ * X * (partialTraceRight ω) ^ (-1 : ℝ)) := by
  rw [vec_mul_mul]

/-- The modular argument `modArgVec τ ω = τ ⊗ₖ (ω⁻¹)ᵀ` is positive definite (for faithful
`τ, ω`), the input data `Δ` for the abstract rigidity spine. -/
lemma modArgVec_posDef {τ ω : Matrix (nA × nB) (nA × nB) ℂ} (hτ : τ.PosDef) (hω : ω.PosDef) :
    (modArgVec τ ω).PosDef := by
  rw [modArgVec]
  exact hτ.kronecker (IsStrictlyPositive.rpow ω (-1) hω.isStrictlyPositive).posDef.transpose

/-- The spectrum of `modArgVec τ ω` is positive — the spectral hypothesis for the spine. -/
lemma modArgVec_spectrum {τ ω : Matrix (nA × nB) (nA × nB) ℂ} (hτ : τ.PosDef) (hω : ω.PosDef) :
    spectrum ℝ (modArgVec τ ω) ⊆ Set.Ioi 0 := by
  intro x hx
  have hpd := modArgVec_posDef hτ hω
  exact (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos _ hpd.1).mp hpd.isStrictlyPositive x hx

/-- **Vectorisation of `petzW`.** `vec (petzW ω X) = petzWvec ω *ᵥ vec X`. -/
lemma vec_petzW (ω : Matrix (nA × nB) (nA × nB) ℂ) (X : Matrix nA nA ℂ) :
    vec (petzW ω X) = petzWvec ω *ᵥ vec X := by
  rw [petzW, vec_rightMul, vec_kron_one, vec_rightMul, petzWvec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- Hermitian-ness of the `rpow` twist. -/
private lemma isHermitian_rpow {ω : Matrix (nA × nB) (nA × nB) ℂ} (hω : ω.PosDef) (y : ℝ) :
    (ω ^ (y : ℝ)).IsHermitian := by
  have : (CFC.rpow ω y).PosDef := (IsStrictlyPositive.rpow ω y hω.isStrictlyPositive).posDef
  exact this.1

omit [DecidableEq nB] in
private lemma isHermitian_rpowA {ω : Matrix (nA × nB) (nA × nB) ℂ}
    (hωA : (partialTraceRight ω).PosDef) (y : ℝ) :
    ((partialTraceRight ω) ^ (y : ℝ)).IsHermitian := by
  have : (CFC.rpow (partialTraceRight ω) y).PosDef :=
    (IsStrictlyPositive.rpow (partialTraceRight ω) y hωA.isStrictlyPositive).posDef
  exact this.1

/-- For a Hermitian `M`, `(Mᵀ)ᴴ = Mᵀ`. -/
private lemma conjTranspose_transpose_herm {m : Type*} {M : Matrix m m ℂ} (h : M.IsHermitian) :
    (Mᵀ)ᴴ = Mᵀ := by
  rw [transpose_conjTranspose, ← conjTranspose_transpose, h.eq]

/-- The conjugate transpose of `petzWvec` (the matricisation of `petzWadj ω`). -/
lemma petzWvec_conjTranspose (ω : Matrix (nA × nB) (nA × nB) ℂ) (hω : ω.PosDef)
    (hωA : (partialTraceRight ω).PosDef) :
    (petzWvec ω)ᴴ
      = ((1 : Matrix nA nA ℂ) ⊗ₖ ((partialTraceRight ω) ^ (-(1 / 2) : ℝ))ᵀ) * (amplMat nA nB)ᴴ
        * ((1 : Matrix (nA × nB) (nA × nB) ℂ) ⊗ₖ (ω ^ (1 / 2 : ℝ))ᵀ) := by
  rw [petzWvec]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    conjTranspose_transpose_herm (isHermitian_rpow hω (1 / 2)),
    conjTranspose_transpose_herm (isHermitian_rpowA hωA (-(1 / 2))), Matrix.mul_assoc]

/-- **Vectorisation of `petzWadj`.** `vec (petzWadj ω Z) = (petzWvec ω)ᴴ *ᵥ vec Z`. -/
lemma vec_petzWadj (ω : Matrix (nA × nB) (nA × nB) ℂ) (hω : ω.PosDef)
    (hωA : (partialTraceRight ω).PosDef) (Z : Matrix (nA × nB) (nA × nB) ℂ) :
    vec (petzWadj ω Z) = (petzWvec ω)ᴴ *ᵥ vec Z := by
  rw [petzWadj, vec_rightMul, vec_partialTraceRight, vec_rightMul,
    petzWvec_conjTranspose ω hω hωA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-! ## The three bridged identities -/

/-- **Bridged identity (i): `Wᵥᴴ Wᵥ = 1`.**  The vectorised Petz isometry is a genuine rectangular
isometry, transported from `petzW_isometry`. -/
theorem petzWvec_isometry (ω : Matrix (nA × nB) (nA × nB) ℂ) (hω : ω.PosDef)
    (hωA : (partialTraceRight ω).PosDef) :
    (petzWvec ω)ᴴ * petzWvec ω = 1 := by
  refine eq_of_mulVec_vec fun X => ?_
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← vec_petzW,
    ← vec_petzWadj ω hω hωA, petzW_isometry ω hω hωA]

/-- **Bridged identity (ii): `Wᵥ (vec ω_A^{1/2}) = vec ω^{1/2}`.**  The vectorised isometry carries
the output cyclic vector to the input one, transported from `petzW_cyclic`. -/
theorem petzWvec_cyclic (ω : Matrix (nA × nB) (nA × nB) ℂ)
    (hωA : (partialTraceRight ω).PosDef) :
    petzWvec ω *ᵥ vec ((partialTraceRight ω) ^ (1 / 2 : ℝ)) = vec (ω ^ (1 / 2 : ℝ)) := by
  rw [← vec_petzW, petzW_cyclic ω hωA]

/-- **Bridged identity (iii): `Wᵥᴴ (modArgVec τ ω) Wᵥ = modArgVec τ_A ω_A`.**  The vectorised
compression of the relative modular map is the output relative modular map, transported from
`petzW_modular_compression` (Carlen–Vershynina (2.3)). -/
theorem petzWvec_modular_compression (τ ω : Matrix (nA × nB) (nA × nB) ℂ) (hω : ω.PosDef)
    (hωA : (partialTraceRight ω).PosDef) :
    (petzWvec ω)ᴴ * modArgVec τ ω * petzWvec ω
      = (partialTraceRight τ) ⊗ₖ ((partialTraceRight ω) ^ (-1 : ℝ))ᵀ := by
  refine eq_of_mulVec_vec fun X => ?_
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← vec_petzW, modArgVec_mulVec, ← vec_petzWadj ω hω hωA,
    petzW_modular_compression τ ω hω hωA X, modArgVecA_mulVec]

end ErgodicTheory.OperatorEntropy.Lieb

end

