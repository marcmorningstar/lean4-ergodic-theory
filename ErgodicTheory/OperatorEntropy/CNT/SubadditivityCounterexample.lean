import Mathlib.Analysis.Subadditive
import ErgodicTheory.OperatorEntropy.CNT.Construction
import ErgodicTheory.OperatorEntropy.DiagonalSpectrum
import ErgodicTheory.OperatorEntropy.EntropyStrictPos

/-!
# Failure of subadditivity of the CNT/ALF entropy sequence

The Connes–Narnhofer–Thirring / Alicki–Fannes construction attaches to an operational partition
`X` the sequence `n ↦ S(ρ[X(n)]) = vonNeumannEntropy (corrMatrix Φ ρ X n)`.  Unlike the classical
Kolmogorov–Sinai construction, this sequence is **not** subadditive in general: `S(ρ[X(2)])` can
strictly exceed `2 · S(ρ[X(1)])`.  This is precisely why the CNT/ALF entropy of a partition is
defined as an infimum rate (here `cntEntropyPartition`, an `sInf`; Alicki–Fannes use a `limsup`
for the same reason) rather than a Fekete-style limit of a subadditive sequence.

This module records an explicit witness of the failure, even in the simplest possible dynamical
setting.  Take `Φ = id` on `Matrix (Fin 2) (Fin 2) ℂ`, the invariant pure state `ρ = |0⟩⟨0|`, and
the two-element operational partition

`x₀ = (1/√2) · !![1,0;1,0]`,  `x₁ = !![0,1;0,0]`  (with `x₀ᴴx₀ + x₁ᴴx₁ = 1`).

Then `S(ρ[X(1)]) = 0` while `S(ρ[X(2)]) > 0`, so `S(ρ[X(2)]) > 2 · S(ρ[X(1)])` and the sequence
`n ↦ S(ρ[X(n)])` is not subadditive (`not_subadditive_cnt_entropySeq`).

Reference: Alicki–Fannes, *Quantum Dynamical Systems*, Oxford University Press (2001), the
Alicki–Lindblad–Fannes (ALF) entropy chapter.
-/

open Matrix Real
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

/-- The counterexample dynamics: the identity `*`-endomorphism of `Matrix (Fin 2) (Fin 2) ℂ`. -/
def cexEndo : UnitalStarEndo 2 where
  toFun := id
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

@[simp] theorem cexEndo_toFun (x : Matrix (Fin 2) (Fin 2) ℂ) : cexEndo.toFun x = x := rfl

/-- The counterexample state: the pure state `|0⟩⟨0| = diagonal ![1,0]`. -/
def cexState : DensityMatrix (Fin 2) where
  val := Matrix.diagonal ![1, 0]
  posSemidef := Matrix.PosSemidef.diagonal (by
    rw [Pi.le_def]; intro i; fin_cases i <;> simp)
  trace_one := by simp

/-- `(√2)⁻¹ · (√2)⁻¹ = 1/2` in `ℂ`. -/
theorem cex_s_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [← mul_inv, h2]; norm_num

/-- The counterexample operational partition: `x₀ = (1/√2)!![1,0;1,0]` (written as the equal
literal `!![1/√2, 0; 1/√2, 0]`) and `x₁ = !![0,1;0,0]`. -/
def cexPartition : OperationalPartition 2 2 where
  op := ![!![(1 / Real.sqrt 2 : ℂ), 0; (1 / Real.sqrt 2 : ℂ), 0], !![0, 1; 0, 0]]
  partUnity := by
    rw [Fin.sum_univ_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
        Fin.sum_univ_two, cex_s_sq]

/-- The refinement of the counterexample partition at length `1` is just `x_{f 0}`
(since `Φ = id`). -/
theorem refine_cex_one (f : Fin 1 → Fin 2) :
    refine cexEndo cexPartition 1 f = cexPartition.op (f 0) := by
  rw [refine_succ, refine_zero, cexEndo_toFun, mul_one]

/-- The refinement of the counterexample partition at length `2` is `x_{f 0} · x_{f 1}`
(since `Φ = id`). -/
theorem refine_cex_two (f : Fin 2 → Fin 2) :
    refine cexEndo cexPartition 2 f = cexPartition.op (f 0) * cexPartition.op (f 1) := by
  rw [refine_succ, refine_cex_one, cexEndo_toFun]
  rfl

/-- The `ρ`-weighted Hilbert–Schmidt pairing for the pure state `ρ = diagonal ![1,0]`:
`Tr(ρ Xᴴ Y)` reads off column `0`, giving `⟨col₀ X, col₀ Y⟩`. -/
theorem cex_trace (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (cexState.val * Xᴴ * Y).trace = star (X 0 0) * Y 0 0 + star (X 1 0) * Y 1 0 := by
  simp only [cexState, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  norm_num

/-- Closed form for a length-`2` correlation-matrix entry: an inner product of the column-`0`
vectors of the two refinement words. -/
theorem corrVal_two_apply (g f : Fin 2 → Fin 2) :
    corrVal cexEndo cexState cexPartition 2 g f
      = star ((cexPartition.op (g 0) * cexPartition.op (g 1)) 0 0)
          * (cexPartition.op (f 0) * cexPartition.op (f 1)) 0 0
        + star ((cexPartition.op (g 0) * cexPartition.op (g 1)) 1 0)
          * (cexPartition.op (f 0) * cexPartition.op (f 1)) 1 0 := by
  rw [corrVal_apply, cex_trace]
  simp only [refine_cex_two]

/-- Von Neumann entropy of a density matrix whose value is a real diagonal is the classical
entropy of that diagonal. -/
theorem vonNeumannEntropy_of_val_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) (p : ι → ℝ)
    (hval : ρ.val = Matrix.diagonal (fun i => (p i : ℂ))) :
    vonNeumannEntropy ρ = ∑ i, Real.negMulLog (p i) := by
  have hpsd : (Matrix.diagonal (fun i => (p i : ℂ))).PosSemidef := hval ▸ ρ.posSemidef
  have htr : (Matrix.diagonal (fun i => (p i : ℂ))).trace = 1 := hval ▸ ρ.trace_one
  have hρ : ρ = ⟨Matrix.diagonal (fun i => (p i : ℂ)), hpsd, htr⟩ := DensityMatrix.ext hval
  rw [hρ]
  exact vonNeumannEntropy_diagonal p hpsd htr

/-- **Fact 1.** For the invariant pure state `ρ = |0⟩⟨0|`, the length-`1` correlation matrix is the
classical pure state `diagonal ![1,0]`, so `S(ρ[X(1)]) = 0`. -/
theorem entropy_corrMatrix_one_eq_zero :
    vonNeumannEntropy (corrMatrix cexEndo cexState cexPartition 1) = 0 := by
  have hval : (corrMatrix cexEndo cexState cexPartition 1).val
      = Matrix.diagonal
        (fun f : Fin 1 → Fin 2 => ((if f 0 = 0 then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
    rw [corrMatrix_val]
    ext g f
    rw [corrVal_apply, cex_trace]
    simp only [refine_cex_one, Matrix.diagonal_apply]
    have hgf : (g = f) ↔ (g 0 = f 0) := by rw [funext_iff, Fin.forall_fin_one]
    simp only [hgf]
    have two : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    rcases two (g 0) with hg | hg <;> rcases two (f 0) with hf | hf <;>
      rw [hg, hf] <;> norm_num [cexPartition, cex_s_sq]
  rw [vonNeumannEntropy_of_val_diagonal _ _ hval,
    ← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 2)).symm]
  simp [Real.negMulLog]

/-- **Fact 2.** For the same pure state, the length-`2` correlation matrix is *not* idempotent
(its `(w₀₀, w₀₀)` entry violates `M² = M`: `3/8 ≠ 1/2`), hence `S(ρ[X(2)]) > 0`. -/
theorem entropy_corrMatrix_two_pos :
    0 < vonNeumannEntropy (corrMatrix cexEndo cexState cexPartition 2) := by
  apply vonNeumannEntropy_pos_of_sq_ne
  rw [corrMatrix_val]
  intro hsq
  have hc := congrFun (congrFun hsq ![0, 0]) ![0, 0]
  rw [Matrix.mul_apply, ← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm] at hc
  simp only [finTwoArrowEquiv_symm_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    corrVal_two_apply] at hc
  simp only [cexPartition, one_div, Fin.isValue, cons_val_zero, cons_val_one, cons_val_fin_one,
    mul_apply, of_apply, cons_val', Fin.sum_univ_two, cex_s_sq, zero_mul, add_zero, star_inv₀,
    star_ofNat, mul_zero, star_zero, one_mul, zero_add, RCLike.star_def, Complex.conj_ofReal] at hc
  have h38 : (3 : ℂ) / 8 = 1 / 2 := by linear_combination hc - (1 / 4 : ℂ) * cex_s_sq
  norm_num at h38

/-- **The counterexample.**  The CNT/ALF entropy sequence `n ↦ S(ρ[X(n)])` of the operational
partition `cexPartition`, under the identity dynamics `cexEndo` and the invariant pure state
`cexState`, is **not subadditive**: `S(ρ[X(2)]) > 0 = 2·S(ρ[X(1)])` violates `u 2 ≤ u 1 + u 1`.
This is why the CNT/ALF entropy of a partition is defined as an infimum rate (`cntEntropyPartition`,
an `sInf`) rather than a Fekete limit of a subadditive sequence. -/
theorem not_subadditive_cnt_entropySeq :
    ¬ Subadditive (fun n => vonNeumannEntropy (corrMatrix cexEndo cexState cexPartition n)) := by
  intro h
  have h2 : vonNeumannEntropy (corrMatrix cexEndo cexState cexPartition 2)
      ≤ vonNeumannEntropy (corrMatrix cexEndo cexState cexPartition 1)
        + vonNeumannEntropy (corrMatrix cexEndo cexState cexPartition 1) := h 1 1
  rw [entropy_corrMatrix_one_eq_zero] at h2
  linarith [entropy_corrMatrix_two_pos]

end ErgodicTheory.OperatorEntropy.CNT
