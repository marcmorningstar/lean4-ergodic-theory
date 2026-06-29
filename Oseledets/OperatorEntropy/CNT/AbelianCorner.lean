import Oseledets.OperatorEntropy.CNT.Construction
import Oseledets.OperatorEntropy.DiagonalSpectrum
import Oseledets.Entropy.KSEntropySystem

/-!
# The abelian corner: CNT dynamical entropy = Kolmogorov–Sinai entropy

This module discharges issue #24: on the abelian (diagonal-subalgebra) corner the
Connes–Narnhofer–Thirring / Alicki–Fannes quantum dynamical entropy collapses to the classical
Kolmogorov–Sinai entropy.

Concretely, fix a finite probability vector `μ : Fin d → ℝ≥0∞` and a permutation `σ` of `Fin d`
preserving `μ`. The associated classical system is the measure-preserving map `⇑σ` on
`(Fin d, probMeasure μ)`. On the quantum side we take the dynamics `Φ = adPerm σ` (conjugation by
the permutation matrix `P_σ`) acting on the state `ρ_μ = densityOfPMF μ` (the diagonal density
matrix with entries `μ`). A cell map `c : Fin d → Fin k` gives a **projection operational
partition** `projPartition c` (diagonal indicator projections) on the quantum side and the
**classical partition** `projMeasurePartition μ c` on the classical side.

The two key results are:

* `cntEntropyPartition_eq_ksEntropyPartition`: per partition, the CNT correlation matrix is
  diagonal with the join-cell masses on the diagonal, so its von Neumann entropy equals the
  classical Shannon entropy of the corresponding join — hence the entropy rates coincide.
* `cntDynamicalEntropyAbelian_eq_ksEntropy`: taking the supremum over all projection partitions
  recovers the full Kolmogorov–Sinai entropy `h(⇑σ)` of the classical system (using that, when
  every state has positive mass, an arbitrary measurable partition is realized by a cell map).

A consolation lower bound `ksEntropy_le_cntDynamicalEntropy` records that the *full* CNT dynamical
entropy (supremum over all operational partitions) dominates the classical entropy.
-/

open Matrix MeasureTheory Function Real
open scoped ComplexOrder ENNReal

noncomputable section

namespace Oseledets.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two density matrices with equal underlying matrix are equal (proof-irrelevant fields). -/
private theorem DensityMatrix.ext' {ρ τ : DensityMatrix n} (h : ρ.val = τ.val) : ρ = τ := by
  cases ρ; cases τ; subst h; rfl

namespace CNT

variable {d k : ℕ}

/-! ## 1. The classical system on `Fin d` -/

/-- The probability measure on `Fin d` attached to a probability vector `μ`. -/
def probMeasure (μ : Fin d → ℝ≥0∞) : Measure (Fin d) :=
  Measure.sum (fun i => μ i • Measure.dirac i)

instance probMeasure_isProb (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1) :
    IsProbabilityMeasure (probMeasure μ) := by
  constructor
  rw [probMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul, mul_one]
  rw [tsum_fintype]; exact hμ

theorem probMeasure_apply (μ : Fin d → ℝ≥0∞) (s : Set (Fin d)) :
    probMeasure μ s = ∑ i, μ i * s.indicator 1 i := by
  rw [probMeasure, Measure.sum_apply _ (by measurability), tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ (by measurability), smul_eq_mul]

theorem probMeasure_singleton (μ : Fin d → ℝ≥0∞) (j : Fin d) :
    (probMeasure μ) {j} = μ j := by
  rw [probMeasure_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      (fun i _ hij => by rw [Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr hij),
        mul_zero]),
    Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl), Pi.one_apply, mul_one]

theorem measurePreserving_perm (μ : Fin d → ℝ≥0∞) (σ : Equiv.Perm (Fin d))
    (hinv : ∀ i, μ (σ i) = μ i) :
    MeasurePreserving (⇑σ) (probMeasure μ) (probMeasure μ) := by
  refine ⟨measurable_of_finite _, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_finite _) hs, probMeasure_apply, probMeasure_apply,
    ← Equiv.sum_comp σ (fun a => μ a * s.indicator 1 a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hinv i]
  congr 1

/-! ## 2. The dynamics `Ad P_σ` and the diagonal state `ρ_μ` -/

/-- Conjugation by `P_σ = σ.permMatrix ℂ`, as a unital `*`-endomorphism. -/
def adPerm (σ : Equiv.Perm (Fin d)) : UnitalStarEndo d where
  toFun x := σ.permMatrix ℂ * x * (σ.permMatrix ℂ)ᴴ
  map_zero := by rw [mul_zero, zero_mul]
  map_add x y := by rw [mul_add, add_mul]
  map_one := by
    rw [mul_one, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]
  map_mul x y := by
    have hPP : (σ.permMatrix ℂ)ᴴ * σ.permMatrix ℂ = 1 := by
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
        Matrix.permMatrix_one]
    change σ.permMatrix ℂ * (x * y) * (σ.permMatrix ℂ)ᴴ =
      σ.permMatrix ℂ * x * (σ.permMatrix ℂ)ᴴ * (σ.permMatrix ℂ * y * (σ.permMatrix ℂ)ᴴ)
    simp only [mul_assoc]
    rw [← mul_assoc (σ.permMatrix ℂ)ᴴ (σ.permMatrix ℂ), hPP, one_mul]
  map_star x := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      mul_assoc]

theorem adPerm_diagonal (σ : Equiv.Perm (Fin d)) (v : Fin d → ℂ) :
    (adPerm σ).toFun (Matrix.diagonal v) = Matrix.diagonal (v ∘ σ) := by
  change σ.permMatrix ℂ * Matrix.diagonal v * (σ.permMatrix ℂ)ᴴ = Matrix.diagonal (v ∘ σ)
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  simp only [Function.comp_id, Function.id_comp, Equiv.Perm.inv_def, Equiv.symm_symm,
    Matrix.submatrix_diagonal_equiv]

def stateVec (μ : Fin d → ℝ≥0∞) : Fin d → ℝ := fun i => (μ i).toReal

theorem stateVec_nonneg (μ : Fin d → ℝ≥0∞) (i : Fin d) : 0 ≤ stateVec μ i :=
  ENNReal.toReal_nonneg

theorem stateVec_sum (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1) : ∑ i, stateVec μ i = 1 := by
  have hfin : ∀ i, μ i ≠ ∞ := by
    intro i
    have hle : μ i ≤ 1 := hμ ▸ Finset.single_le_sum (fun j _ => zero_le') (Finset.mem_univ i)
    exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
  simp only [stateVec]
  rw [← ENNReal.toReal_sum (fun i _ => hfin i), hμ, ENNReal.toReal_one]

def densityOfPMF (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1) : DensityMatrix (Fin d) where
  val := Matrix.diagonal (fun i => ((stateVec μ i : ℝ) : ℂ))
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast stateVec_nonneg μ i
  trace_one := by
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, stateVec_sum μ hμ, Complex.ofReal_one]

@[simp] theorem densityOfPMF_val (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1) :
    (densityOfPMF μ hμ).val = Matrix.diagonal (fun i => ((stateVec μ i : ℝ) : ℂ)) := rfl

/-! ## 3. The projection operational partition from a cell map `c : Fin d → Fin k` -/

def projPartition (c : Fin d → Fin k) : OperationalPartition d k where
  op i := Matrix.diagonal (fun j => if c j = i then (1 : ℂ) else 0)
  partUnity := by
    have hsq : ∀ i, (Matrix.diagonal (fun j => if c j = i then (1 : ℂ) else 0))ᴴ *
        Matrix.diagonal (fun j => if c j = i then (1 : ℂ) else 0)
        = Matrix.diagonal (fun j => if c j = i then (1 : ℂ) else 0) := by
      intro i
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1; funext j; by_cases h : c j = i <;> simp [h]
    rw [Finset.sum_congr rfl (fun i _ => hsq i)]
    ext a b
    simp only [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp [Finset.sum_ite_eq]
    · simp [hab]

@[simp] theorem projPartition_op (c : Fin d → Fin k) (i : Fin k) :
    (projPartition c).op i = Matrix.diagonal (fun j => if c j = i then (1 : ℂ) else 0) := rfl

def projMeasurePartition (μ : Fin d → ℝ≥0∞) (c : Fin d → Fin k) :
    Oseledets.Entropy.MeasurePartition (probMeasure μ) (Fin k) where
  cells i := c ⁻¹' {i}
  measurable _ := by measurability
  aedisjoint := by
    intro i i' hii'
    exact Disjoint.aedisjoint (Disjoint.preimage c (Set.disjoint_singleton.mpr hii'))
  cover := by rw [Set.eq_univ_iff_forall]; intro x; exact Set.mem_iUnion.mpr ⟨c x, rfl⟩

@[simp] theorem projMeasurePartition_cells (μ : Fin d → ℝ≥0∞) (c : Fin d → Fin k) (i : Fin k) :
    (projMeasurePartition μ c).cells i = c ⁻¹' {i} := rfl

/-! ## 4. THE DIAGONAL COLLAPSE -/

/-- The product of indicators = the indicator of the n-fold join cell. -/
def joinInd (σ : Equiv.Perm (Fin d)) (c : Fin d → Fin k) (n : ℕ) (f : Fin n → Fin k)
    (j : Fin d) : ℂ :=
  ∏ l : Fin n, (if c ((σ ^ (l : ℕ)) j) = f l then (1 : ℂ) else 0)

/-- The `n`-fold refinement product is the indicator of the corresponding classical join cell. -/
theorem joinInd_eq_indicator (μ : Fin d → ℝ≥0∞) (σ : Equiv.Perm (Fin d)) (c : Fin d → Fin k)
    (nn : ℕ) (f : Fin nn → Fin k) (j : Fin d) :
    joinInd σ c nn f j
      = (Oseledets.Entropy.ksJoinCells (projMeasurePartition μ c).cells (⇑σ) nn f).indicator
          (fun _ => (1 : ℂ)) j := by
  have hmem : ∀ l : Fin nn,
      (j ∈ (⇑σ)^[(l : ℕ)] ⁻¹' (projMeasurePartition μ c).cells (f l))
        ↔ c ((σ ^ (l : ℕ)) j) = f l := fun l => by
    simp only [projMeasurePartition_cells, Set.mem_preimage, Set.mem_singleton_iff,
      Equiv.Perm.coe_pow]
  rw [joinInd]
  by_cases hj : j ∈ Oseledets.Entropy.ksJoinCells (projMeasurePartition μ c).cells (⇑σ) nn f
  · rw [Set.indicator_of_mem hj]
    have hj' : ∀ l : Fin nn, j ∈ (⇑σ)^[(l : ℕ)] ⁻¹' (projMeasurePartition μ c).cells (f l) := by
      rw [Oseledets.Entropy.ksJoinCells_apply, Set.mem_iInter] at hj; exact hj
    refine Finset.prod_eq_one fun l _ => ?_
    rw [if_pos ((hmem l).mp (hj' l))]
  · rw [Set.indicator_of_notMem hj]
    have hj' : ¬ ∀ l : Fin nn, j ∈ (⇑σ)^[(l : ℕ)] ⁻¹' (projMeasurePartition μ c).cells (f l) := by
      rw [Oseledets.Entropy.ksJoinCells_apply, Set.mem_iInter] at hj; exact hj
    obtain ⟨l, hl⟩ := not_forall.mp hj'
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg fun hc => hl ((hmem l).mpr hc))

theorem adPerm_refine (σ : Equiv.Perm (Fin d)) (c : Fin d → Fin k) :
    ∀ (n : ℕ) (f : Fin n → Fin k),
      refine (adPerm σ) (projPartition c) n f = Matrix.diagonal (joinInd σ c n f)
  | 0, f => by
      rw [refine_zero,
        show (joinInd σ c 0 f) = (fun _ => (1 : ℂ)) from by funext j; simp [joinInd]]
      exact Matrix.diagonal_one.symm
  | n + 1, f => by
      have hfun : (fun j => (if c j = f 0 then (1 : ℂ) else 0) *
          ((joinInd σ c n (Fin.tail f)) ∘ ⇑σ) j) = joinInd σ c (n + 1) f := by
        funext j
        simp only [joinInd, Function.comp_apply, Fin.prod_univ_succ, Fin.val_zero, pow_zero,
          Equiv.Perm.one_apply, Fin.val_succ, Fin.tail, pow_succ, Equiv.Perm.mul_apply]
        rfl
      rw [refine_succ, adPerm_refine σ c n (Fin.tail f), projPartition_op, adPerm_diagonal,
        Matrix.diagonal_mul_diagonal, hfun]

/-- **Per-partition collapse (the deliverable core).** -/
theorem cntEntropyPartition_eq_ksEntropyPartition
    (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) (hinv : ∀ i, μ (σ i) = μ i)
    (c : Fin d → Fin k) :
    haveI := probMeasure_isProb μ hμ
    cntEntropyPartition (adPerm σ) (densityOfPMF μ hμ) (projPartition c)
      = Oseledets.Entropy.ksEntropyPartition (measurePreserving_perm μ σ hinv)
          (projMeasurePartition μ c) := by
  haveI := probMeasure_isProb μ hμ
  classical
  rw [cntEntropyPartition_eq]
  unfold Oseledets.Entropy.ksEntropyPartition
  rw [Subadditive.lim]
  congr 1
  refine Set.image_congr fun nn _ => ?_
  have hseq : vonNeumannEntropy (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) nn)
      = Oseledets.Entropy.ksEntropySeq (measurePreserving_perm μ σ hinv)
          (projMeasurePartition μ c) nn := by
    set mreal : (Fin nn → Fin k) → ℝ := fun f =>
      ((probMeasure μ) (Oseledets.Entropy.ksJoinCells
        (projMeasurePartition μ c).cells (⇑σ) nn f)).toReal with hmreal
    have hcorr : (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) nn).val
        = Matrix.diagonal (fun f => ((mreal f : ℝ) : ℂ)) := by
      ext g f
      rw [corrMatrix_val, corrVal_apply, adPerm_refine, adPerm_refine, densityOfPMF_val,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
        Matrix.trace_diagonal, Matrix.diagonal_apply]
      simp only [Pi.star_apply]
      have hfin : ∀ i, μ i ≠ ⊤ := by
        intro i
        have hle : μ i ≤ 1 := hμ ▸ Finset.single_le_sum (fun j _ => zero_le') (Finset.mem_univ i)
        exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
      by_cases hgf : g = f
      · subst hgf
        rw [if_pos rfl]
        have hmf0 : mreal g = ((probMeasure μ) (Oseledets.Entropy.ksJoinCells
            (projMeasurePartition μ c).cells (⇑σ) nn g)).toReal := by rw [hmreal]
        have hfin2 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
            μ i * (Oseledets.Entropy.ksJoinCells (projMeasurePartition μ c).cells (⇑σ) nn
              g).indicator (1 : Fin d → ℝ≥0∞) i ≠ ⊤ := by
          intro i _
          refine ENNReal.mul_ne_top (hfin i) ?_
          rw [Set.indicator_apply]; split <;> simp
        rw [hmf0, probMeasure_apply, ENNReal.toReal_sum hfin2, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [joinInd_eq_indicator μ]
        by_cases hi : i ∈ Oseledets.Entropy.ksJoinCells (projMeasurePartition μ c).cells (⇑σ) nn g
        · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
          simp only [stateVec, Pi.one_apply, star_one, mul_one]
        · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi]
          simp
      · rw [if_neg hgf]
        refine Finset.sum_eq_zero fun i _ => ?_
        obtain ⟨l, hl⟩ : ∃ l, g l ≠ f l := by
          by_contra h
          exact hgf (funext fun l => not_not.mp fun hh => h ⟨l, hh⟩)
        by_cases hcg : c ((σ ^ (l : ℕ)) i) = g l
        · have hzero : joinInd σ c nn f i = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ l) (if_neg fun hcf => hl (hcg ▸ hcf))
          rw [hzero, mul_zero]
        · have hzero : joinInd σ c nn g i = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hcg)
          rw [hzero, star_zero, mul_zero, zero_mul]
    have hpsd : (Matrix.diagonal (fun f => ((mreal f : ℝ) : ℂ))).PosSemidef :=
      hcorr ▸ (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) nn).posSemidef
    have htr : (Matrix.diagonal (fun f => ((mreal f : ℝ) : ℂ))).trace = 1 :=
      hcorr ▸ (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) nn).trace_one
    have hρτ : corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) nn
        = (⟨Matrix.diagonal (fun f => ((mreal f : ℝ) : ℂ)), hpsd, htr⟩ :
          DensityMatrix (Fin nn → Fin k)) := DensityMatrix.ext' hcorr
    rw [hρτ, vonNeumannEntropy_diagonal]
    rw [Oseledets.Entropy.ksEntropySeq, Oseledets.Entropy.ksJoin_cells,
      Oseledets.Entropy.entropy_def]
  rw [hseq]

/-! ## 5. System-level statement -/

/-- The abelian-corner CNT dynamical entropy: sup of the partition entropy rate over PROJECTION
(diagonal-subalgebra) operational partitions. -/
def cntDynamicalEntropyAbelian (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) : EReal :=
  ⨆ k : ℕ, ⨆ c : Fin d → Fin k,
    ((cntEntropyPartition (adPerm σ) (densityOfPMF μ hμ) (projPartition c) : ℝ) : EReal)

/-- **System-level abelian-corner equality.** Over projection operational partitions, the CNT
dynamical entropy of `adPerm σ` in the diagonal state `densityOfPMF μ` equals the classical
Kolmogorov–Sinai entropy of `⇑σ`, provided every state has positive mass. -/
theorem cntDynamicalEntropyAbelian_eq_ksEntropy
    (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) (hinv : ∀ i, μ (σ i) = μ i) (hpos : ∀ i, 0 < μ i) :
    haveI := probMeasure_isProb μ hμ
    cntDynamicalEntropyAbelian μ hμ σ
      = Oseledets.Entropy.ksEntropy (measurePreserving_perm μ σ hinv) := by
  haveI := probMeasure_isProb μ hμ
  refine le_antisymm ?_ ?_
  · unfold cntDynamicalEntropyAbelian
    refine iSup_le fun k => iSup_le fun c => ?_
    rw [cntEntropyPartition_eq_ksEntropyPartition μ hμ σ hinv c]
    exact Oseledets.Entropy.le_ksEntropy (measurePreserving_perm μ σ hinv)
      (projMeasurePartition μ c)
  · unfold Oseledets.Entropy.ksEntropy
    refine iSup_le fun nP => iSup_le fun P => ?_
    have hdisj : ∀ (j : Fin d) (i i' : Fin nP), j ∈ P.cells i → j ∈ P.cells i' → i = i' := by
      intro j i i' hi hi'
      by_contra hne
      have hmem : j ∈ P.cells i ∩ P.cells i' := ⟨hi, hi'⟩
      have hμj0 : (probMeasure μ) {j} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.mpr hmem) (P.aedisjoint hne)
      rw [probMeasure_singleton] at hμj0
      exact (hpos j).ne' hμj0
    have hcov : ∀ j : Fin d, ∃ i, j ∈ P.cells i := by
      intro j
      have hj : j ∈ ⋃ i, P.cells i := by rw [P.cover]; exact Set.mem_univ j
      exact Set.mem_iUnion.mp hj
    let c : Fin d → Fin nP := fun j => (hcov j).choose
    have hc : ∀ j, j ∈ P.cells (c j) := fun j => (hcov j).choose_spec
    have hcells : ∀ i, c ⁻¹' {i} = P.cells i := by
      intro i; ext j
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => h ▸ hc j, fun h => hdisj j (c j) i (hc j) h⟩
    have hcellfun : (projMeasurePartition μ c).cells = P.cells := by
      funext i; exact hcells i
    have hseqfun : Oseledets.Entropy.ksEntropySeq (measurePreserving_perm μ σ hinv)
        (projMeasurePartition μ c)
        = Oseledets.Entropy.ksEntropySeq (measurePreserving_perm μ σ hinv) P := by
      funext m
      unfold Oseledets.Entropy.ksEntropySeq
      rw [Oseledets.Entropy.ksJoin_cells, Oseledets.Entropy.ksJoin_cells, hcellfun]
    have hkspart : Oseledets.Entropy.ksEntropyPartition (measurePreserving_perm μ σ hinv)
        (projMeasurePartition μ c)
        = Oseledets.Entropy.ksEntropyPartition (measurePreserving_perm μ σ hinv) P := by
      unfold Oseledets.Entropy.ksEntropyPartition
      rw [Subadditive.lim, Subadditive.lim, hseqfun]
    rw [← hkspart, ← cntEntropyPartition_eq_ksEntropyPartition μ hμ σ hinv c]
    unfold cntDynamicalEntropyAbelian
    exact le_iSup_of_le nP (le_iSup_of_le c le_rfl)

/-- **System-level lower bound (consolation).** The full CNT dynamical entropy (supremum over ALL
operational partitions) dominates the classical Kolmogorov–Sinai entropy of `⇑σ`. -/
theorem ksEntropy_le_cntDynamicalEntropy
    (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) (hinv : ∀ i, μ (σ i) = μ i) (hpos : ∀ i, 0 < μ i) :
    haveI := probMeasure_isProb μ hμ
    Oseledets.Entropy.ksEntropy (measurePreserving_perm μ σ hinv)
      ≤ cntDynamicalEntropy (adPerm σ) (densityOfPMF μ hμ) := by
  haveI := probMeasure_isProb μ hμ
  have hle : cntDynamicalEntropyAbelian μ hμ σ
      ≤ cntDynamicalEntropy (adPerm σ) (densityOfPMF μ hμ) := by
    unfold cntDynamicalEntropyAbelian cntDynamicalEntropy
    refine iSup_le fun k => iSup_le fun c => ?_
    exact le_iSup_of_le k (le_iSup_of_le (projPartition c) le_rfl)
  rw [← cntDynamicalEntropyAbelian_eq_ksEntropy μ hμ σ hinv hpos]
  exact hle

end CNT
end Oseledets.OperatorEntropy
