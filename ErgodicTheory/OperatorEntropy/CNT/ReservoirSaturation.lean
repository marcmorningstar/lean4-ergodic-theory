import ErgodicTheory.OperatorEntropy.CNT.Construction
import ErgodicTheory.OperatorEntropy.EntropyPure

/-!
# Saturation of the finite CNT/ALF entropy reservoir at `d = 2`

The finite-dimensional degeneracy `cntDynamicalEntropy_eq_zero` (`CNT.FiniteDimZero`) rests on a
*uniform* cap: the von Neumann entropy of the correlation matrix is `≤ log(d²)` at **every**
resolution `n` (`vonNeumannEntropy_corrMatrix_le_log`), so the per-step rate `S/n` dies.  This
module shows the mechanism is genuine "saturation, not identically-zero" (issue #69): the cap is
attained.

At `d = 2` the **Pauli operational partition** `pauliPartition : OperationalPartition 2 4` — the
four Pauli operators `1, X, Y, Z` scaled by `1/2` — fills the reservoir completely at one step, for
*every* unital `*`-endomorphism `Φ`.  Feeding it the maximally mixed state `I/2`, the correlation
matrix at `n = 1` is *itself* maximally mixed on the `4`-element index set `Fin 1 → Fin 4`
(`corrMatrix_pauliPartition_one`), so its entropy is exactly `log 4 = log(2²)`
(`vonNeumannEntropy_corrMatrix_pauliPartition_eq`).  The rate still vanishes only because that
finite reservoir `log(d²)` is uniform in `n`, not because single steps carry no information.

The arithmetic behind saturation is Pauli trace-orthogonality `Tr(Pᵢᴴ Pⱼ) = 2 δᵢⱼ`, which makes
`(op a)ᴴ (op b)` contribute `(1/4) δ_{ab}` to the correlation trace against `I/2`.  Note honestly
that this also shows the naive `log d` cap is *false* for the correlation-matrix construction:
a `d²`-dimensional density matrix genuinely occurs.  Weyl/Pauli-operator saturation of the CNT
reservoir is folklore in this framework; see Connes–Narnhofer–Thirring, *Dynamical entropy of
`C*`-algebras and von Neumann algebras*, Comm. Math. Phys. **112** (1987), 691–719.
-/

open Matrix Real
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

/-- The **Pauli operational partition** of `Matrix (Fin 2) (Fin 2) ℂ`: the four operators
`(1/2)·Pᵢ`, where `P₀ = 1`, `P₁ = X`, `P₂ = Y`, `P₃ = Z` are the Pauli matrices.  Each `Pᵢ` is
Hermitian and unitary, so `∑ᵢ (op i)ᴴ (op i) = ∑ᵢ (1/4)·Pᵢ² = 4·(1/4)·1 = 1`. -/
def pauliPartition : OperationalPartition 2 4 where
  op := ![!![(1 / 2 : ℂ), 0; 0, 1 / 2],
          !![(0 : ℂ), 1 / 2; 1 / 2, 0],
          !![(0 : ℂ), -Complex.I / 2; Complex.I / 2, 0],
          !![(1 / 2 : ℂ), 0; 0, -1 / 2]]
  partUnity := by
    ext a b
    rw [Matrix.sum_apply, Fin.sum_univ_four]
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.tail_cons, Complex.ext_iff, Complex.normSq,
        Complex.div_re, Complex.div_im] <;> norm_num

/-- Each Pauli partition operator is Hermitian (self-adjoint). -/
theorem pauliPartition_op_herm (i : Fin 4) :
    (pauliPartition.op i)ᴴ = pauliPartition.op i := by
  fin_cases i <;>
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [pauliPartition, Matrix.conjTranspose_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.tail_cons, Complex.conj_I]

/-- The `n = 1` time-ordered refinement of any partition is just its selected operator:
`refine Φ X 1 f = X.op (f 0)`, since `refine Φ X 0 _ = 1` and `Φ 1 = 1`. -/
theorem refine_one {d k : ℕ} (Φ : UnitalStarEndo d) (X : OperationalPartition d k)
    (f : Fin 1 → Fin k) : refine Φ X 1 f = X.op (f 0) := by
  rw [refine_succ, refine_zero, Φ.map_one, mul_one]

/-- **Pauli trace-orthogonality against the maximally mixed state.**  For the Pauli partition,
`Tr(I/2 · (op a)ᴴ · (op b)) = (1/4)·δ_{ab}`.  This is `Tr(Pᵢᴴ Pⱼ) = 2 δᵢⱼ` scaled by the state
`I/2` and the `(1/2)²` normalisation. -/
theorem trace_maximallyMixed_pauli (a b : Fin 4) :
    ((DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)).val
        * (pauliPartition.op a)ᴴ * pauliPartition.op b).trace
      = if a = b then (1 / 4 : ℂ) else 0 := by
  have hmm : (DensityMatrix.maximallyMixed : DensityMatrix (Fin 2)).val
      = !![(1 / 2 : ℂ), 0; 0, 1 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [DensityMatrix.maximallyMixed, Matrix.smul_apply,
        Complex.real_smul, Fintype.card_fin]
  rw [pauliPartition_op_herm, hmm]
  fin_cases a <;> fin_cases b <;>
    simp [pauliPartition, Matrix.trace_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Complex.ext_iff, Complex.normSq] <;> norm_num

/-- **Saturation of the correlation matrix at `n = 1`.**  For every unital `*`-endomorphism `Φ`,
the CNT correlation matrix of the Pauli partition in the maximally mixed state `I/2` is, at a single
step, *itself* the maximally mixed state on the `4`-element index set `Fin 1 → Fin 4`.  This is the
Pauli trace-orthogonality `Tr(Pᵢᴴ Pⱼ) = 2 δᵢⱼ` read off as a diagonal `(1/4)·1` density matrix. -/
theorem corrMatrix_pauliPartition_one (Φ : UnitalStarEndo 2) :
    corrMatrix Φ DensityMatrix.maximallyMixed pauliPartition 1 = DensityMatrix.maximallyMixed := by
  apply DensityMatrix.ext
  rw [corrMatrix_val]
  ext g f
  have hcard : Fintype.card (Fin 1 → Fin 4) = 4 := by
    simp [Fintype.card_fin]
  have hcond : (g = f) ↔ (g 0 = f 0) := by rw [funext_iff, Fin.forall_fin_one]
  rw [corrVal_apply, refine_one, refine_one, trace_maximallyMixed_pauli]
  simp only [DensityMatrix.maximallyMixed, Matrix.smul_apply, Matrix.one_apply, hcard,
    Complex.real_smul]
  by_cases h : g 0 = f 0
  · rw [if_pos h, if_pos (hcond.mpr h)]; norm_num
  · rw [if_neg h, if_neg (fun he => h (hcond.mp he)), mul_zero]

/-- **The reservoir cap `log(d²)` is tight at `d = 2`.**  The Pauli operational partition in the
maximally mixed state attains the uniform bound `vonNeumannEntropy_corrMatrix_le_log` at a single
step, for *every* unital `*`-endomorphism `Φ`: its correlation matrix is maximally mixed on `4`
points, so its von Neumann entropy is exactly `log 4 = log(2²)`.  This realises issue #69's
"saturation, not identically-zero": the mechanism behind `cntDynamicalEntropy_eq_zero` is a finite
reservoir `log(d²)` that single steps can fill completely; the per-step *rate* dies only because the
cap is uniform in `n`, not because individual steps are trivial.  (It also shows the naive `log d`
cap is false for this construction.) -/
theorem vonNeumannEntropy_corrMatrix_pauliPartition_eq (Φ : UnitalStarEndo 2) :
    vonNeumannEntropy (corrMatrix Φ DensityMatrix.maximallyMixed pauliPartition 1)
      = Real.log ((2 : ℝ) ^ 2) := by
  rw [corrMatrix_pauliPartition_one, vonNeumannEntropy_maximallyMixed]
  norm_num [Fintype.card_fun, Fintype.card_fin]

end ErgodicTheory.OperatorEntropy.CNT
