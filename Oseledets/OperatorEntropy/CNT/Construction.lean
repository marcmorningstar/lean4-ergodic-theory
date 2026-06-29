import Oseledets.OperatorEntropy.CNT.Refinement

/-!
# The CNT/ALF correlation matrix and quantum dynamical entropy

Building on the time-ordered refinement of `Refinement`, this module constructs the
Connes–Narnhofer–Thirring / Alicki–Fannes correlation density matrix and the resulting
quantum dynamical entropy of a finite-dimensional quantum dynamics.

Given a unital `*`-endomorphism `Φ`, a state `ρ`, and an operational partition `X`, the
**correlation matrix** `corrMatrix Φ ρ X n` is the `(Fin n → Fin k)`-indexed matrix with entries
`⟨g, f⟩ ↦ Tr(ρ · (refine g)ᴴ · (refine f))`.  It is a genuine density matrix:

* `trace_one` is the telescoping identity `∑_f (refine f)ᴴ (refine f) = 1` together with
  `Tr ρ = 1`;
* positive semidefiniteness is the Gram/`Tr(ρ Tᴴ T) ≥ 0` argument: the quadratic form
  `x⋆ M x` equals `Tr(T ρ Tᴴ)` for `T = ∑_f x_f · refine f`, and `T ρ Tᴴ` is positive
  semidefinite with nonnegative trace.

The **CNT entropy of a partition** is the infimum rate `inf_n S(corrMatrix n)/n` of the von
Neumann entropy of the correlation matrix, and the **dynamical entropy** is the supremum over all
operational partitions. -/

open Matrix Real
open scoped ComplexOrder

noncomputable section

namespace Oseledets.OperatorEntropy.CNT

variable {d : ℕ}

/-- The (unnormalised) correlation matrix of the CNT construction, as a raw matrix:
`corrVal Φ ρ X n g f = Tr(ρ · (refine Φ X n g)ᴴ · (refine Φ X n f))`. -/
def corrVal (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    Matrix (Fin n → Fin k) (Fin n → Fin k) ℂ :=
  fun g f => (ρ.val * (refine Φ X n g)ᴴ * refine Φ X n f).trace

theorem corrVal_apply (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) (g f : Fin n → Fin k) :
    corrVal Φ ρ X n g f = (ρ.val * (refine Φ X n g)ᴴ * refine Φ X n f).trace := rfl

/-- The correlation matrix is Hermitian. -/
theorem corrVal_isHermitian (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    (corrVal Φ ρ X n).IsHermitian := by
  have hρH : ρ.valᴴ = ρ.val := ρ.posSemidef.1
  refine Matrix.IsHermitian.ext fun g f => ?_
  rw [corrVal_apply, corrVal_apply, ← Matrix.trace_conjTranspose, conjTranspose_mul,
    conjTranspose_mul, conjTranspose_conjTranspose, hρH, ← mul_assoc, trace_mul_cycle]

/-- The correlation matrix is positive semidefinite: the quadratic form `x⋆ M x` equals
`Tr(T ρ Tᴴ)` with `T = ∑_f x_f · refine f`, which is a trace of a positive semidefinite matrix. -/
theorem corrVal_posSemidef (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    (corrVal Φ ρ X n).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (corrVal_isHermitian Φ ρ X n) fun x => ?_
  set T := ∑ f : Fin n → Fin k, x f • refine Φ X n f with hT
  have hmat : T * ρ.val * Tᴴ
      = ∑ g, star (x g) • ∑ f, x f • (refine Φ X n f * ρ.val * (refine Φ X n g)ᴴ) := by
    rw [hT, conjTranspose_sum]
    simp only [conjTranspose_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  have hR : (T * ρ.val * Tᴴ).trace
      = ∑ g, ∑ f, star (x g) * (corrVal Φ ρ X n g f * x f) := by
    rw [hmat]
    simp only [trace_sum, trace_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun f _ => ?_
    rw [corrVal_apply, trace_mul_cycle, trace_mul_cycle]
    ring
  have hL : star x ⬝ᵥ (corrVal Φ ρ X n *ᵥ x)
      = ∑ g, ∑ f, star (x g) * (corrVal Φ ρ X n g f * x f) := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  have hkey : star x ⬝ᵥ (corrVal Φ ρ X n *ᵥ x) = (T * ρ.val * Tᴴ).trace := by
    rw [hL, hR]
  rw [hkey]
  exact (ρ.posSemidef.mul_mul_conjTranspose_same T).trace_nonneg

/-- The trace of the correlation matrix is `1`: telescoping plus `Tr ρ = 1`. -/
theorem corrVal_trace_one (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    (corrVal Φ ρ X n).trace = 1 := by
  have h1 : (corrVal Φ ρ X n).trace = ∑ g, corrVal Φ ρ X n g g := by
    simp only [Matrix.trace, Matrix.diag_apply]
  rw [h1]
  simp only [corrVal_apply]
  rw [← trace_sum]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, sum_refine_conjTranspose_mul_refine, mul_one]
  exact ρ.trace_one

/-- The **correlation density matrix** of the CNT construction: the density matrix on the
classical index set `Fin n → Fin k` with entries `Tr(ρ · (refine g)ᴴ · (refine f))`. -/
def corrMatrix (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) : DensityMatrix (Fin n → Fin k) where
  val := fun g f => (ρ.val * (refine Φ X n g)ᴴ * refine Φ X n f).trace
  posSemidef := corrVal_posSemidef Φ ρ X n
  trace_one := corrVal_trace_one Φ ρ X n

@[simp]
theorem corrMatrix_val (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    (corrMatrix Φ ρ X n).val = corrVal Φ ρ X n := rfl

/-- The CNT entropy of an operational partition: the infimum entropy rate
`inf_{n ≥ 1} S(corrMatrix Φ ρ X n) / n`. -/
def cntEntropyPartition (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) : ℝ :=
  sInf ((fun n => vonNeumannEntropy (corrMatrix Φ ρ X n) / n) '' Set.Ici 1)

theorem cntEntropyPartition_eq (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) :
    cntEntropyPartition Φ ρ X
      = sInf ((fun n => vonNeumannEntropy (corrMatrix Φ ρ X n) / n) '' Set.Ici 1) := rfl

/-- The **CNT/ALF quantum dynamical entropy** of `Φ` in the state `ρ`: the supremum of the
partition entropy rate over all finite operational partitions of unity. -/
def cntDynamicalEntropy (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d)) : EReal :=
  ⨆ k : ℕ, ⨆ X : OperationalPartition d k, ((cntEntropyPartition Φ ρ X : ℝ) : EReal)

end Oseledets.OperatorEntropy.CNT
