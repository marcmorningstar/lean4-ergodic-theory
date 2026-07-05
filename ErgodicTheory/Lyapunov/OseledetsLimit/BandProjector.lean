/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.OseledetsLimit.SingularValues

/-!
# The band spectral projector

The band spectral projectors `bandProjector A T χ n x = cfc χ (qpow A T n x)` of the candidate
Oseledets matrices `qpow`, together with their self-adjoint / idempotent algebra, the sorted Gram
eigenbasis and top frame, and the Cauchy / summability and abstract sin-Θ machinery used to extract
limiting spectral projectors from the candidates.

## Main definitions

* `ErgodicTheory.bandProjector` — the band spectral projector of `qpow A T n x` cut at a threshold `χ`.
* `ErgodicTheory.sortedGramEigenbasis`, `ErgodicTheory.sortedTopFrame` — the sorted Gram eigenbasis and the
  orthonormal frame spanning the top eigenvalue-block.

## Main results

* `ErgodicTheory.bandProjector_isSelfAdjoint`, `ErgodicTheory.bandProjector_mul_self`,
  `ErgodicTheory.bandProjector_rank` — the band-projector algebra.
* `ErgodicTheory.norm_cfc_le_of_forall_eigenvalue_abs_le` — the spectral-block operator-norm bound.
* `ErgodicTheory.exists_tendsto_cfc_of_summable` — CFC convergence from summable increments.
* `ErgodicTheory.sin_sq_le_rayleigh_deficit_div_gap`, `ErgodicTheory.offdiag_sin_le_residual_div_gap` — the
  abstract Rayleigh-deficit / sin-Θ core.
-/

open Module InnerProductSpace MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator Matrix MatrixOrder RealInnerProductSpace

noncomputable section

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
variable [NeZero d]
variable {μ : Measure X} {T : X → X}

/-! ## The band spectral projector and its basic algebra

The spectral projectors of the Oseledets matrix limit are obtained as limits of *band spectral
projectors* of the candidate matrices `qpow A T n x = (Qₙ)^{1/(2n)}`: cut the spectrum at a
continuous threshold function `χ` via the continuous functional calculus. For a `χ` that equals the
`0/1` indicator of a spectral gap on the (finite) spectrum, `cfc χ (qpow)` is the orthogonal
projector onto the top eigenvalue-block. This subsection records the projector and its self-adjoint
/ idempotent algebra; the gap hypothesis discharging idempotence is supplied by the root-test layer
below. -/

/-- The band spectral projector of `qpow A T n x` cut at a continuous threshold function
`χ`: `bandProjector A T χ n x = cfc χ (qpow A T n x)`. For a `χ` that equals the `0/1` indicator of
a spectral gap on the (finite) spectrum it is the orthogonal projector onto the top
eigenvalue-block; the projector identity is provided conditionally below. -/
def bandProjector (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (χ : ℝ → ℝ) (n : ℕ) (x : X) :
    Matrix (Fin d) (Fin d) ℝ :=
  cfc χ (qpow A T n x)

set_option linter.unusedSectionVars false in
/-- The band spectral projector is self-adjoint (a CFC of a real-valued function is
always self-adjoint). -/
theorem bandProjector_isSelfAdjoint (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (χ : ℝ → ℝ)
    (n : ℕ) (x : X) : IsSelfAdjoint (bandProjector A T χ n x) :=
  cfc_predicate _ _

set_option linter.unusedSectionVars false in
/-- If the cutoff `χ` is idempotent on the spectrum of `qpow` (i.e. `χ = χ²` there — true
for a `0/1` indicator separated from the spectrum by a gap), the band projector is idempotent: a
genuine orthogonal projector. Conditional; the gap hypothesis that supplies `hidem` is discharged by
the root-test layer below. -/
theorem bandProjector_mul_self (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) {χ : ℝ → ℝ} (n : ℕ)
    (x : X) (hχ : ContinuousOn χ (_root_.spectrum ℝ (qpow A T n x)))
    (hidem : (_root_.spectrum ℝ (qpow A T n x)).EqOn (fun t => χ t * χ t) χ) :
    bandProjector A T χ n x * bandProjector A T χ n x = bandProjector A T χ n x := by
  rw [bandProjector, ← cfc_mul χ χ _, cfc_congr hidem]

/-! ## The band projector is the top-block eigenprojector

For a cutoff `χ` equal on the (finite) spectrum of `qpow A T n x` to the `0/1` indicator of
`(c, ∞)`, the band projector `bandProjector A T χ n x = cfc χ (qpow…)` is a genuine orthogonal
projector (self-adjoint idempotent) whose **rank** equals the number of eigenvalues of `qpow`
strictly above `c` — i.e. the dimension of the top eigenvalue-block. The explicit Hermitian-CFC
triple-product formula `cfc χ A = U · diag(χ ∘ eigenvalues) · Uᴴ` makes the projector concrete;
the rank is the count of nonzero diagonal entries, and a `{0,1}`-valued `χ` selects exactly the
eigenvalues above the cut. -/

set_option linter.unusedSectionVars false in
/-- When `χ` equals the `0/1` indicator of `(c, ∞)` on the spectrum of `qpow`, the band
projector is idempotent (a genuine orthogonal projector). Specialization of `bandProjector_mul_self`
to the indicator cutoff, whose continuity hypothesis is discharged because the spectrum is finite
and the indicator is `0/1`-valued (hence `χ² = χ` on it). -/
theorem bandProjector_indicator_mul_self (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) {c : ℝ}
    (n : ℕ) (x : X) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
        * bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
      = bandProjector A T (Set.indicator (Set.Ioi c) 1) n x := by
  -- On the spectrum, the `0/1`-valued indicator satisfies `χ² = χ`.
  have hidem : (_root_.spectrum ℝ (qpow A T n x)).EqOn
      (fun t => Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) t * Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) t)
      (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) := by
    intro t _
    by_cases ht : t ∈ Set.Ioi c
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  -- `ContinuousOn` of any function on the (finite) spectrum holds.
  have hcont : ContinuousOn (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ))
      (_root_.spectrum ℝ (qpow A T n x)) :=
    (Matrix.finite_real_spectrum (A := qpow A T n x)).continuousOn _
  rw [bandProjector, ← cfc_mul _ _ _ hcont hcont, cfc_congr hidem]

/-- The explicit Hermitian-CFC triple product: for a Hermitian matrix `M`, `cfc χ M` equals the
unitary conjugate of the diagonal matrix of `χ` applied to the eigenvalues,
`U · diag(RCLike.ofReal ∘ χ ∘ eigenvalues) · Uᴴ`. Matrix analogue of the spectral step
`hA.cfc χ = U · diag(ofReal ∘ χ ∘ eig) · star U`. -/
theorem cfc_eq_eigenvectorUnitary_conj {m : Type*} [Fintype m] [DecidableEq m] {𝕜 : Type*}
    [RCLike 𝕜] {M : Matrix m m 𝕜} (hM : M.IsHermitian) (χ : ℝ → ℝ) :
    cfc χ M
      = (hM.eigenvectorUnitary : Matrix m m 𝕜)
          * Matrix.diagonal (RCLike.ofReal ∘ χ ∘ hM.eigenvalues)
          * star (hM.eigenvectorUnitary : Matrix m m 𝕜) := by
  rw [hM.cfc_eq χ, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]

/-- **Rank of the band projector.** The rank of `bandProjector A T χ n x = cfc χ (qpow…)`
is the number of eigenvalues `i` of `qpow A T n x` with `χ (eigenvalues i) ≠ 0`. Computed from the
explicit Hermitian-CFC triple product `U · diag(χ ∘ eig) · Uᴴ`: conjugation by the (invertible)
eigenvector unitary preserves rank, and the rank of the diagonal is the count of nonzero entries. -/
theorem bandProjector_rank (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (χ : ℝ → ℝ)
    (n : ℕ) (x : X) :
    (bandProjector A T χ n x).rank
      = Fintype.card {i : Fin d //
          χ ((qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues i) ≠ 0} := by
  classical
  set hM := (qpow_isSelfAdjoint A T n x).isHermitian with hMdef
  set U : Matrix (Fin d) (Fin d) ℝ := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  -- The eigenvector unitary has unit determinant (both `U` and `star U`).
  have hUstar : U * star U = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hdetU : IsUnit U.det :=
    IsUnit.of_mul_eq_one (a := U.det) (star U).det
      (by rw [← Matrix.det_mul, hUstar, Matrix.det_one])
  have hdetUs : IsUnit (star U).det :=
    IsUnit.of_mul_eq_one (a := (star U).det) U.det
      (by rw [← Matrix.det_mul, Unitary.coe_star_mul_self hM.eigenvectorUnitary, Matrix.det_one])
  -- The band projector is the unitary conjugate of the diagonal of `χ ∘ eigenvalues`.
  rw [bandProjector, cfc_eq_eigenvectorUnitary_conj hM χ, ← hU]
  -- Strip the unitary factors (rank is invariant under multiplication by invertible matrices).
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetUs,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdetU, Matrix.rank_diagonal]
  -- The nonzero diagonal entries are exactly the indices with `χ (eigenvalues i) ≠ 0`.
  refine Fintype.card_congr (Equiv.subtypeEquivRight (fun i => ?_))
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, ne_eq]

/-! ## Frame form: the band projector is `U_top · U_topᵀ`

The Frobenius back-transport `ExteriorNorm.norm_proj_sub_le_wedge` consumes the band projector in
the
shape `P = U Uᵀ` with `Uᵀ U = 1` (orthonormal columns). The `0/1` indicator cutoff selects exactly
the eigenvectors of `qpow` with eigenvalue `> c`; through the explicit Hermitian-CFC triple product
`cfc χ M = U · diag(χ ∘ eig) · Uᴴ` (`cfc_eq_eigenvectorUnitary_conj`), the band projector equals
`U_top · U_topᵀ`, where `U_top` is the column-submatrix of the eigenvector unitary selecting the
columns above the cut. The selected columns are orthonormal (`U_topᵀ U_top = 1`). -/

set_option linter.unusedSectionVars false in
/-- **Diag-selection.** For a real matrix `U` and the `0/1` indicator of `(c, ∞)` precomposed with a
scalar `e : Fin d → ℝ`, conjugating the indicator diagonal by `U` selects the columns of `U` whose
`e`-value exceeds `c`: `U · diag(𝟙_{(c,∞)} ∘ e) · Uᵀ = U_S · U_Sᵀ`, where `U_S` is the
column-submatrix of `U` on `S = {i | c < e i}`. -/
theorem diag_indicator_conj_eq_submatrix (U : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (e : Fin d → ℝ) :
    U * Matrix.diagonal (fun i => Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) (e i)) * Uᵀ
      = (U.submatrix id (Subtype.val : {i // c < e i} → Fin d))
          * (U.submatrix id (Subtype.val : {i // c < e i} → Fin d))ᵀ := by
  classical
  ext a b
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [← Finset.sum_subtype (s := Finset.univ.filter (fun i => c < e i))
      (p := fun i => c < e i) (fun i => by simp) (fun i => U a i * U b i)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : c < e i
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hi), Pi.one_apply, if_pos hi, one_mul]
  · rw [Set.indicator_of_notMem (by simpa using hi), if_neg hi, zero_mul, mul_zero]

set_option linter.unusedSectionVars false in
/-- **Orthonormal columns of the selected submatrix.** If `U` has orthonormal columns
(`Uᵀ U = 1`, e.g. an eigenvector unitary), then any column-subselection of `U` still has orthonormal
columns: `U_Sᵀ U_S = 1`. (`U_S = U.submatrix id Subtype.val` over a subtype of column indices.) -/
theorem submatrix_transpose_mul_self_eq_one (U : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (e : Fin d → ℝ) (hU : Uᵀ * U = 1) :
    (U.submatrix id (Subtype.val : {i // c < e i} → Fin d))ᵀ
        * (U.submatrix id (Subtype.val : {i // c < e i} → Fin d)) = 1 := by
  classical
  ext s t
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  have hsum : ∑ a, U a (s : Fin d) * U a (t : Fin d) = (Uᵀ * U) (s : Fin d) (t : Fin d) := by
    rw [Matrix.mul_apply]; simp [Matrix.transpose_apply]
  rw [hsum, hU, Matrix.one_apply, Matrix.one_apply]
  by_cases hst : s = t
  · simp [hst]
  · rw [if_neg hst, if_neg (fun h => hst (Subtype.ext h))]

/-- **CFC indicator = `U_top · U_topᵀ`.** For a Hermitian real matrix `M` with eigenvector unitary
`U` and eigenvalues `eig`, the band projector cut by the `0/1` indicator of `(c, ∞)` is
`U_top · U_topᵀ`, where `U_top` is the column-submatrix of `U` selecting the eigenvectors with
eigenvalue `> c`. Combines `cfc_eq_eigenvectorUnitary_conj` (the triple product
`U · diag(χ ∘ eig) · Uᴴ`) with `diag_indicator_conj_eq_submatrix`. -/
theorem cfc_indicator_eq_submatrix_mul (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.IsHermitian) (c : ℝ) :
    cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) M
      = (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).submatrix id
            (Subtype.val : {i // c < hM.eigenvalues i} → Fin d)
          * ((hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).submatrix id
            (Subtype.val : {i // c < hM.eigenvalues i} → Fin d))ᵀ := by
  classical
  rw [cfc_eq_eigenvectorUnitary_conj hM (Set.indicator (Set.Ioi c) 1)]
  have hdiag : (Matrix.diagonal
        (RCLike.ofReal ∘ Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) ∘ hM.eigenvalues)
      : Matrix (Fin d) (Fin d) ℝ)
      = Matrix.diagonal (fun i => Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) (hM.eigenvalues i)) := by
    congr 1
  rw [hdiag, Matrix.star_eq_conjTranspose,
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial,
    diag_indicator_conj_eq_submatrix]

/-- **The band-projector frame extraction.** The band projector of `qpow` cut
by the `0/1` indicator of `(c, ∞)` is `U_top · U_topᵀ`, with `U_top` the column-submatrix of the
eigenvector unitary of `qpow A T n x` selecting the eigenvectors with eigenvalue `> c`, and the
selected columns are orthonormal (`U_topᵀ U_top = 1`). This is the `P = U Uᵀ` input consumed by the
Frobenius back-transport `ExteriorNorm.norm_proj_sub_le_wedge`. -/
theorem bandProjector_indicator_eq_frame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {c : ℝ} (n : ℕ) (x : X) :
    let hM := (qpow_isSelfAdjoint A T n x).isHermitian
    let Utop := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).submatrix id
      (Subtype.val : {i // c < hM.eigenvalues i} → Fin d)
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x = Utop * Utopᵀ
      ∧ Utopᵀ * Utop = 1 := by
  intro hM Utop
  refine ⟨?_, ?_⟩
  · exact cfc_indicator_eq_submatrix_mul (qpow A T n x) hM c
  · exact submatrix_transpose_mul_self_eq_one
      (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) c hM.eigenvalues
      (Unitary.coe_star_mul_self hM.eigenvectorUnitary)

/-! ## Sorted frame: the band projector is the SORTED top-`k` gram eigenframe projector

The Plücker eigenpair `ExteriorNorm.plucker_eigenpair_ceiling_standard'` and the det-Gram bridge
`ExteriorNorm.det_transpose_mul_eq_inner_onbTriv` both speak of the **sorted** gram eigenbasis: the
top eigenvector wedge is `onbTriv basisFun (⋀ {u₀, …, u_{k-1}})` of the orthonormal eigenframe `u`
with **antitone** eigenvalues `lam = σ²`. The `bandProjector_indicator_eq_frame` expresses
the band projector through `qpow`'s **unsorted** eigenvector unitary; this subsection reconciles the
two by showing the band projector equals `W Wᵀ`, where `W` is the `d×k` matrix whose columns are the
**sorted** top-`k` gram eigenvectors. Both are the orthogonal projector onto the same eigenvalue-`>
c`
subspace; the reconciliation is via the elementary "self-adjoint idempotent of trace `k` and range
fixing `W` is `W Wᵀ`" device (trace-zero symmetric idempotent vanishes). -/

set_option linter.unusedSectionVars false in
/-- **CFC acts diagonally on the matrix eigenbasis.** For a Hermitian real matrix `M` with
eigenvector basis `eigenvectorBasis` and eigenvalues `eigenvalues`, `cfc g M` sends the `j`-th
eigenvector to `g (eigenvalues j)` times itself: `cfc g M *ᵥ (eigenvectorBasis j) =
g (eigenvalues j) • eigenvectorBasis j`. The matrix-level spectral action, derived from the explicit
triple product `cfc g M = U · diag(g ∘ eig) · Uᴴ` (`cfc_eq_eigenvectorUnitary_conj`). -/
theorem cfc_mulVec_eigenvectorBasis (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian) (g : ℝ → ℝ)
    (j : Fin d) :
    cfc g M *ᵥ ⇑(hM.eigenvectorBasis j) = g (hM.eigenvalues j) • ⇑(hM.eigenvectorBasis j) := by
  rw [cfc_eq_eigenvectorUnitary_conj hM g, Matrix.star_eq_conjTranspose,
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hstar : (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ *ᵥ ⇑(hM.eigenvectorBasis j)
      = Pi.single j 1 := by
    have := Matrix.IsHermitian.star_eigenvectorUnitary_mulVec hM j
    rwa [Matrix.star_eq_conjTranspose,
      (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial]
      at this
  rw [hstar, Matrix.diagonal_mulVec_single]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, mul_one]
  rw [show Pi.single j (g (hM.eigenvalues j)) = g (hM.eigenvalues j) • Pi.single j (1:ℝ) from by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], Matrix.mulVec_smul,
    Matrix.IsHermitian.eigenvectorUnitary_mulVec]

/-- **CFC acts diagonally on the matrix eigenbasis (Euclidean-linear form).** The `EuclideanSpace`
analogue of `cfc_mulVec_eigenvectorBasis`: `toEuclideanLin (cfc g M)` sends the `j`-th eigenvector
to
`g (eigenvalues j)` times itself. -/
theorem toEuclideanLin_cfc_eigenvectorBasis (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (g : ℝ → ℝ) (j : Fin d) :
    Matrix.toEuclideanLin (cfc g M) (hM.eigenvectorBasis j)
      = g (hM.eigenvalues j) • (hM.eigenvectorBasis j) := by
  rw [Matrix.toLpLin_apply, cfc_mulVec_eigenvectorBasis M hM g j]; rfl

/-- **The spectral operator-norm bound.** For a Hermitian matrix `M` and a function
`g`, if `|g (eigenvalue i)| ≤ c` for every eigenvalue (and `0 ≤ c`), then the L2 operator norm of
`cfc g M` is at most `c`. This is the analytic core of the spectral-block approximation: applied
with
`g = (· − v ·)` (the deviation between the identity and the block-value step function), it bounds
the
distance between `qpow` and its block-approximant by the maximal eigenvalue deviation.

Proof: in the orthonormal eigenbasis `b` of `M`, `cfc g M` acts diagonally
(`toEuclideanLin_cfc_eigenvectorBasis`), so `⟪b i, (cfc g M) v⟫ = g (eig i) · ⟪b i, v⟫`; Parseval
(`OrthonormalBasis.sum_sq_norm_inner_right`) then gives
`‖(cfc g M) v‖² = ∑ |g(eig i)|² |⟪b i,v⟫|² ≤ c² ∑ |⟪b i,v⟫|² = c² ‖v‖²`. -/
theorem norm_cfc_le_of_forall_eigenvalue_abs_le (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (g : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ i, |g (hM.eigenvalues i)| ≤ c) :
    ‖cfc g M‖ ≤ c := by
  classical
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  change ‖Matrix.toEuclideanLin (cfc g M) v‖ ≤ c * ‖v‖
  set w := Matrix.toEuclideanLin (cfc g M) v with hw
  have hsa : (Matrix.toEuclideanLin (cfc g M)).IsSymmetric := by
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (cfc_predicate g M : IsSelfAdjoint (cfc g M)).isHermitian
  have hinner : ∀ i, ⟪hM.eigenvectorBasis i, w⟫_ℝ
      = g (hM.eigenvalues i) * ⟪hM.eigenvectorBasis i, v⟫_ℝ := by
    intro i
    rw [hw, ← hsa (hM.eigenvectorBasis i) v, toEuclideanLin_cfc_eigenvectorBasis M hM g i,
      inner_smul_left, conj_trivial]
  have hpars_w : ‖w‖ ^ 2 = ∑ i, ⟪hM.eigenvectorBasis i, w⟫_ℝ ^ 2 := by
    rw [← OrthonormalBasis.sum_sq_norm_inner_right hM.eigenvectorBasis w]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have hpars_v : ‖v‖ ^ 2 = ∑ i, ⟪hM.eigenvectorBasis i, v⟫_ℝ ^ 2 := by
    rw [← OrthonormalBasis.sum_sq_norm_inner_right hM.eigenvectorBasis v]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have hsqbound : ‖w‖ ^ 2 ≤ c ^ 2 * ‖v‖ ^ 2 := by
    rw [hpars_w, hpars_v, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hinner i, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [hbound i, abs_nonneg (g (hM.eigenvalues i)), sq_abs (g (hM.eigenvalues i)), hc]
  nlinarith [norm_nonneg w, norm_nonneg v, hsqbound, mul_nonneg hc (norm_nonneg v)]

set_option linter.unusedSectionVars false in
/-- **Trace of the indicator band projector = number of eigenvalues above the cut.** For a Hermitian
real matrix `M`, the trace of `cfc (𝟙_{(c,∞)}) M` is the count of eigenvalues `> c`. The
`0/1`-valued
cutoff makes the conjugated-diagonal trace a count. (For a self-adjoint idempotent this is its
rank.) -/
theorem trace_cfc_indicator_eq_count (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian) (c : ℝ) :
    (cfc (Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) M).trace
      = (Fintype.card {i : Fin d // c < hM.eigenvalues i} : ℝ) := by
  classical
  rw [cfc_eq_eigenvectorUnitary_conj hM, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.star_eq_conjTranspose,
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial]
  have hUU : (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ
      * (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 := by
    have := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose_eq_transpose_of_trivial]
      at this
  rw [hUU, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  rw [show (∑ i : Fin d, Set.indicator (Set.Ioi c) (1:ℝ→ℝ) (hM.eigenvalues i))
      = ∑ i : Fin d, (if c < hM.eigenvalues i then (1:ℝ) else 0) from by
    apply Finset.sum_congr rfl; intro i _
    by_cases hi : c < hM.eigenvalues i
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hi), Pi.one_apply, if_pos hi]
    · rw [Set.indicator_of_notMem (by simpa using hi), if_neg hi]]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    mul_one, Fintype.card_subtype]

/-- **A symmetric idempotent of trace `0` vanishes.** Over `ℝ`, a matrix `E` with `Eᵀ = E` and
`E * E = E` and `tr E = 0` is the zero matrix: `tr(Eᴴ E) = tr(E²) = tr E = 0`, and the squared
Frobenius norm `tr(Eᴴ E) = ∑ Eᵢⱼ²` is zero only for `E = 0`. The kernel that turns "same range,
same trace" into a projector identity. -/
theorem eq_zero_of_transpose_eq_of_mul_self_of_trace_zero {D : ℕ} (E : Matrix (Fin D) (Fin D) ℝ)
    (hsym : Eᵀ = E) (hidem : E * E = E) (htr : E.trace = 0) : E = 0 := by
  have hconj : Eᴴ = E := by rw [E.conjTranspose_eq_transpose_of_trivial, hsym]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hconj, hidem, htr])

/-- **The band projector via the `cfc` on the Gram matrix.** Since `qpow = cfc (·^{1/(2n)}) (gram)`
and `cfc` composes, `bandProjector A T 𝟙_{(c,∞)} n x = cfc (𝟙_{(c,∞)} ∘ (·^{1/(2n)})) (gram A T n
x)`.
This unfolds the band projector onto the **gram** spectral data, where the sorted eigenbasis lives.
-/
theorem bandProjector_eq_cfc_gram (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    (c : ℝ) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
      = cfc ((Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) ∘ (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹)))
          (gram A T n x) := by
  rw [bandProjector, qpow,
    cfc_comp (Set.indicator (Set.Ioi c) 1) (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹))
      (gram A T n x) (gram_isSelfAdjoint A T n x)
      ((Matrix.finite_real_spectrum (A := gram A T n x)).image _ |>.continuousOn _)
      ((Matrix.finite_real_spectrum (A := gram A T n x)).continuousOn _)]

/-- **The sorted Gram eigenbasis.** The orthonormal eigenbasis of `gram A T n x`, reindexed by
`Fin (card (Fin d))` so that `sortedGramEigenbasis i` has eigenvalue `eigenvalues₀ i = σᵢ²`
(**antitone**, descending). This is exactly the `u` consumed by
`ExteriorNorm.plucker_eigenpair_ceiling_standard'` (with `lam = σ²`). -/
noncomputable def sortedGramEigenbasis (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) : OrthonormalBasis (Fin (Fintype.card (Fin d))) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (gram_posSemidef A T n x).isHermitian.eigenvectorBasis.reindex
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm

/-- The sorted Gram eigenbasis diagonalizes `toEuclideanLin (gram)` with the **antitone**
eigenvalues
`eigenvalues₀`: `toEuclideanLin (gram) (sortedGramEigenbasis i) = eigenvalues₀ i •
sortedGramEigenbasis i`.
The eigenpair hypothesis `hf` of `ExteriorNorm.plucker_eigenpair_ceiling_standard'`. -/
theorem sortedGramEigenbasis_eigenpair (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) (i : Fin (Fintype.card (Fin d))) :
    Matrix.toEuclideanLin (gram A T n x) (sortedGramEigenbasis A T n x i)
      = (gram_posSemidef A T n x).isHermitian.eigenvalues₀ i • sortedGramEigenbasis A T n x i := by
  set hM := (gram_posSemidef A T n x).isHermitian
  set e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm with he
  have hbase : (sortedGramEigenbasis A T n x i) = (hM.eigenvectorBasis (e.symm i)) := by
    rw [sortedGramEigenbasis, OrthonormalBasis.reindex_apply]
  rw [hbase]
  have hval : hM.eigenvalues (e.symm i) = hM.eigenvalues₀ i := by
    rw [Matrix.IsHermitian.eigenvalues]
    congr 1
    change (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))) i) = i
    simp [Equiv.symm_apply_apply]
  rw [← hval, Matrix.toLpLin_apply, hM.mulVec_eigenvectorBasis (e.symm i)]; rfl

/-- The `1/(2n)`-power of the sorted Gram eigenvalue is the sorted `qpow` eigenvalue:
`(eigenvalues₀(gram) i)^{1/(2n)} = eigenvalues₀(qpow) i`. The monotone-CFC bridge identifying the
gram cut with the qpow cut. -/
theorem rpow_gram_eigenvalues₀_eq_qpow_eigenvalues₀ (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) (i : Fin (Fintype.card (Fin d))) :
    ((gram_posSemidef A T n x).isHermitian.eigenvalues₀ i) ^ ((2 * (n:ℝ))⁻¹)
      = (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i := by
  have hmono : MonotoneOn (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹)) (Set.Ici 0) :=
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by positivity)
  have hpos : ∀ j, 0 ≤ (gram_posSemidef A T n x).isHermitian.eigenvalues₀ j := by
    intro j; rw [gram_eigenvalues₀_eq_sq_singularValues]; positivity
  have hcfc := eigenvalues₀_cfc_of_monotoneOn (gram_posSemidef A T n x).isHermitian hmono hpos
  have hi : (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
      = (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹))
          ((gram_posSemidef A T n x).isHermitian.eigenvalues₀ i) := by
    rw [show (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ i
        = ((cfc_predicate (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹))
            (gram A T n x) : IsSelfAdjoint _).isHermitian).eigenvalues₀ i from rfl, hcfc]
    rfl
  rw [hi]

/-- **The sorted top-`k` Gram eigenframe.** The `d×k` matrix whose `j`-th column is the `j`-th
sorted
Gram eigenvector `sortedGramEigenbasis ⟨j, …⟩`. Its column wedge is the Plücker top eigenvector
`w₀ = onbTriv basisFun (⋀ {u₀, …, u_{k-1}})` of `ExteriorNorm.plucker_eigenpair_ceiling_standard'`,
and it is the `W` of the band-projector frame identity `bandProjector = W Wᵀ`. -/
noncomputable def sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    {k : ℕ} (hk : k ≤ Fintype.card (Fin d)) : Matrix (Fin d) (Fin k) ℝ :=
  Matrix.of (fun a (j : Fin k) => sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hk⟩ a)

/-- The `j`-th column of `sortedTopFrame` (as a Euclidean vector) is the `j`-th sorted Gram
eigenvector. This is the identification that makes `ExteriorNorm.det_transpose_mul_eq_inner_onbTriv`
and `ExteriorNorm.plucker_eigenpair_ceiling_standard'` share the same wedge. -/
theorem colE_sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X)
    {k : ℕ} (hk : k ≤ Fintype.card (Fin d)) (j : Fin k) :
    ExteriorNorm.colE (sortedTopFrame A T n x hk) j
      = sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hk⟩ := by
  rw [ExteriorNorm.colE, sortedTopFrame]
  ext a
  simp [EuclideanSpace.equiv]

/-- The sorted top-`k` Gram eigenframe has **orthonormal columns**: `Wᵀ W = 1`. -/
theorem sortedTopFrame_transpose_mul_self (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) {k : ℕ} (hk : k ≤ Fintype.card (Fin d)) :
    (sortedTopFrame A T n x hk)ᵀ * (sortedTopFrame A T n x hk) = 1 := by
  ext s t
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hinner : ∑ a, (sortedTopFrame A T n x hk)ᵀ s a * (sortedTopFrame A T n x hk) a t
      = (inner ℝ (sortedGramEigenbasis A T n x ⟨s, lt_of_lt_of_le s.2 hk⟩)
          (sortedGramEigenbasis A T n x ⟨t, lt_of_lt_of_le t.2 hk⟩) : ℝ) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl; intro a _
    simp only [sortedTopFrame, Matrix.transpose_apply, Matrix.of_apply, RCLike.inner_apply,
      conj_trivial]
    ring
  rw [hinner, (sortedGramEigenbasis A T n x).inner_eq_ite]
  by_cases hst : s = t
  · subst hst; simp
  · rw [if_neg (show (⟨(s:ℕ), _⟩ : Fin (Fintype.card (Fin d))) ≠ ⟨(t:ℕ), _⟩ from by
      simp only [ne_eq, Fin.mk.injEq]; exact fun h => hst (Fin.ext h)), if_neg hst]

/-- **The band projector fixes the sorted top-`k` Gram eigenframe.** If each of the top-`k` sorted
`qpow` eigenvalues exceeds the cut `c`, then `bandProjector * W = W`, i.e. the band projector acts
as
the identity on each top-`k` sorted Gram eigenvector. (Each column is a `qpow`-eigenvector with
eigenvalue `> c`, where the `0/1` cutoff is `1`.) -/
theorem bandProjector_mul_sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) (c : ℝ) {k : ℕ} (hk : k ≤ Fintype.card (Fin d))
    (htop : ∀ j : Fin k, c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hk⟩) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x * sortedTopFrame A T n x hk
      = sortedTopFrame A T n x hk := by
  set g := (Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) ∘ (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹)) with hg
  set hM := (gram_posSemidef A T n x).isHermitian with hMdef
  set e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm with he
  ext a j
  rw [bandProjector_eq_cfc_gram]
  have hcol : (cfc g (gram A T n x) * sortedTopFrame A T n x hk) a j
      = (cfc g (gram A T n x) *ᵥ (fun b => sortedTopFrame A T n x hk b j)) a := by
    rw [Matrix.mul_apply, Matrix.mulVec]; rfl
  rw [hcol]
  have hcolvec : (fun b => sortedTopFrame A T n x hk b j)
      = ⇑(hM.eigenvectorBasis (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)) := by
    funext b
    change sortedGramEigenbasis A T n x ⟨j, lt_of_lt_of_le j.2 hk⟩ b
      = (hM.eigenvectorBasis (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)) b
    rw [sortedGramEigenbasis, OrthonormalBasis.reindex_apply, he, hMdef, Equiv.symm_symm]
  rw [hcolvec, cfc_mulVec_eigenvectorBasis (gram A T n x) hM g (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)]
  have hval : hM.eigenvalues (e.symm ⟨j, lt_of_lt_of_le j.2 hk⟩)
      = hM.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩ := by
    rw [Matrix.IsHermitian.eigenvalues]
    congr 1
    change (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))))
        ⟨j, lt_of_lt_of_le j.2 hk⟩) = ⟨j, lt_of_lt_of_le j.2 hk⟩
    simp [Equiv.symm_apply_apply]
  rw [hval]
  have hg1 : g (hM.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩) = 1 := by
    have hbr : (hM.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩) ^ ((2 * (n:ℝ))⁻¹)
        = (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀ ⟨j, lt_of_lt_of_le j.2 hk⟩ := by
      rw [hMdef]; exact rpow_gram_eigenvalues₀_eq_qpow_eigenvalues₀ A T n x ⟨j, _⟩
    rw [hg, Function.comp_apply, hbr,
      Set.indicator_of_mem (Set.mem_Ioi.mpr (htop j)), Pi.one_apply]
  rw [hg1, one_smul]
  exact (congrFun hcolvec a).symm

/-- **The band projector is the SORTED top-`k` Gram eigenframe projector.** For a
cut
`c` such that exactly `k` of the `qpow` eigenvalues exceed `c` (`hcount`) and the top-`k` sorted
ones
all exceed it (`htop`), the band projector equals `W Wᵀ` with `Wᵀ W = 1`, where `W = sortedTopFrame`
has the sorted top-`k` Gram eigenvectors as columns. The unsorted↔sorted eigenframe reconciliation:
both `bandProjector` (the `cfc`-indicator eigenvalue-`> c` projector of `qpow`) and `W Wᵀ` (the
sorted
top-`k` Gram eigenspace projector) are the orthogonal projector onto the **same** subspace. Proof:
the
difference `E = bandProjector − W Wᵀ` is a symmetric idempotent (`bandProjector` fixes the columns
of
`W` — `bandProjector_mul_sortedTopFrame`) of trace `k − k = 0`, hence vanishes
(`eq_zero_of_transpose_eq_of_mul_self_of_trace_zero`). The frame `W` and its column wedge are
exactly
the data consumed by `ExteriorNorm.plucker_eigenpair_ceiling_standard'` and
`ExteriorNorm.det_transpose_mul_eq_inner_onbTriv`. -/
theorem bandProjector_indicator_eq_sortedTopFrame (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) (c : ℝ) {k : ℕ} (hk : k ≤ Fintype.card (Fin d))
    (htop : ∀ j : Fin k, c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hk⟩)
    (hcount : Fintype.card {i : Fin d // c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues i}
      = k) :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
        = sortedTopFrame A T n x hk * (sortedTopFrame A T n x hk)ᵀ
      ∧ (sortedTopFrame A T n x hk)ᵀ * sortedTopFrame A T n x hk = 1 := by
  set P := bandProjector A T (Set.indicator (Set.Ioi c) 1) n x with hP
  set W := sortedTopFrame A T n x hk with hW
  have hWW : Wᵀ * W = 1 := sortedTopFrame_transpose_mul_self A T n x hk
  refine ⟨?_, hWW⟩
  set E := P - W * Wᵀ with hE
  have hPsym : Pᵀ = P := by
    have hsa : Pᴴ = P := bandProjector_isSelfAdjoint A T (Set.indicator (Set.Ioi c) 1) n x
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hsa
  have hPWWsym : (W * Wᵀ)ᵀ = W * Wᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hEsym : Eᵀ = E := by rw [hE, Matrix.transpose_sub, hPsym, hPWWsym]
  have hPidem : P * P = P := bandProjector_indicator_mul_self A T n x
  have hPW : P * W = W := bandProjector_mul_sortedTopFrame A T n x c hk htop
  have hWWP : W * Wᵀ * P = W * Wᵀ := by
    have hWtP : Wᵀ * P = Wᵀ := by
      have : (P * W)ᵀ = Wᵀ := by rw [hPW]
      rwa [Matrix.transpose_mul, hPsym] at this
    rw [Matrix.mul_assoc, hWtP]
  have hPWW : P * (W * Wᵀ) = W * Wᵀ := by rw [← Matrix.mul_assoc, hPW]
  have hWWWW : W * Wᵀ * (W * Wᵀ) = W * Wᵀ := by
    rw [show W * Wᵀ * (W * Wᵀ) = W * (Wᵀ * W) * Wᵀ by simp only [Matrix.mul_assoc], hWW,
      Matrix.mul_one]
  have hEidem : E * E = E := by
    rw [hE, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPidem, hPWW, hWWP, hWWWW]
    abel
  have htrP : P.trace = (k : ℝ) := by
    rw [hP, bandProjector, qpow]
    rw [show cfc (Set.indicator (Set.Ioi c) (1:ℝ→ℝ))
          (cfc (fun t : ℝ => t ^ ((2 * (n:ℝ))⁻¹)) (gram A T n x))
        = cfc (Set.indicator (Set.Ioi c) (1:ℝ→ℝ)) (qpow A T n x) from by rw [qpow]]
    rw [trace_cfc_indicator_eq_count (qpow A T n x) (qpow_isSelfAdjoint A T n x).isHermitian c,
      hcount]
  have htrWW : (W * Wᵀ).trace = (k : ℝ) := by
    rw [Matrix.trace_mul_comm, hWW, Matrix.trace_one, Fintype.card_fin]
  have htrE : E.trace = 0 := by rw [hE, Matrix.trace_sub, htrP, htrWW, sub_self]
  have hE0 := eq_zero_of_transpose_eq_of_mul_self_of_trace_zero E hEsym hEidem htrE
  rw [hE] at hE0
  exact sub_eq_zero.mp hE0

/-! ## Cauchy packaging — summable increments give a convergent (band-projector) sequence

The hard mathematical content (the gapped band-projector-Cauchy estimate and its summability)
produces
the *summability* of the consecutive-norm increments of the band projectors. Once that is in hand,
convergence is pure soft analysis: matrices form a finite-dimensional, hence complete, normed space,
so a sequence with summable increments is Cauchy and converges. We package this abstractly (no
dynamics) so it is upstreamable and reusable for any matrix sequence — and keep a `cfc χ (H n)`
specialization that plugs directly into `bandProjector`. -/

/-- A matrix sequence whose consecutive-difference norms `‖f (n+1) - f n‖` are summable is Cauchy
(matrices over `ℝ` are a finite-dimensional, hence complete, normed space). General soft-analysis
fact, independent of the continuous functional calculus. -/
theorem cauchySeq_of_summable_norm_sub {d : ℕ} {f : ℕ → Matrix (Fin d) (Fin d) ℝ}
    (hsum : Summable (fun n => ‖f (n + 1) - f n‖)) : CauchySeq f := by
  refine cauchySeq_of_summable_dist ?_
  refine hsum.congr (fun n => ?_)
  rw [dist_eq_norm, norm_sub_rev]

/-- **Packaging.** A sequence of band-projector-shaped matrices `cfc χ (H n)` whose
consecutive-norm increments are summable is Cauchy. The mathematical content lives in supplying the
summability (the gapped-Cauchy estimate and root test); this is the soft-analysis packaging. -/
theorem cauchySeq_cfc_of_summable {d : ℕ} (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (χ : ℝ → ℝ)
    (hsum : Summable (fun n => ‖cfc χ (H (n + 1)) - cfc χ (H n)‖)) :
    CauchySeq (fun n => cfc χ (H n)) :=
  cauchySeq_of_summable_norm_sub hsum

/-- **Packaging.** A band-projector-shaped sequence `cfc χ (H n)` with summable
consecutive-norm increments converges (matrices are a complete space). The limit is the candidate
Oseledets spectral projector. -/
theorem exists_tendsto_cfc_of_summable {d : ℕ} (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (χ : ℝ → ℝ)
    (hsum : Summable (fun n => ‖cfc χ (H (n + 1)) - cfc χ (H n)‖)) :
    ∃ L, Tendsto (fun n => cfc χ (H n)) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_cfc_of_summable H χ hsum)

/-! ## The rank-1 Rayleigh-gap sin-Θ core

The irreducible analytic kernel of the gapped band-projector Cauchy estimate. It is an
elementary (Parseval + one scalar inequality) replacement for an abstract Davis–Kahan sin-Θ
theorem, which Mathlib lacks entirely. Stated abstractly for a symmetric operator on any real inner
product space (upstreamable, no dynamics): if a unit vector `v'` nearly maximizes the Rayleigh
quotient of `C`, it is close to the top eigenvector `v₀`, with the squared sine of the angle
controlled by the Rayleigh deficit divided by the spectral gap. The cocycle consumer takes
`C = ⋀^k Qₙ` and `v'` the top eigenvector of `⋀^k Qₙ₊₁`, where the deficit is the one-step
distortion. -/

/-- **The rank-1 Rayleigh-gap sin-Θ bound.** For a symmetric operator `C` with a top unit
eigenvector `v₀` of eigenvalue `μ₀`, whose `v₀`-orthogonal complement has Rayleigh quotient bounded
above by a strictly smaller `μ₁`, any unit vector `v'` whose Rayleigh quotient is within `ε` of `μ₀`
makes a small angle with `v₀`: the squared sine `‖v' - ⟪v', v₀⟫ v₀‖²` is at most `ε / (μ₀ - μ₁)`. -/
theorem sin_sq_le_rayleigh_deficit_div_gap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : E →ₗ[ℝ] E} (hC : C.IsSymmetric)
    {μ₀ μ₁ : ℝ} {v₀ : E} (hv₀ : ‖v₀‖ = 1) (hev : C v₀ = μ₀ • v₀) (hgap : μ₁ < μ₀)
    (hμ₁ : ∀ w : E, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ μ₁ * ‖w‖ ^ 2)
    {v' : E} (hv' : ‖v'‖ = 1) {ε : ℝ} (hRay : μ₀ - ε ≤ ⟪C v', v'⟫_ℝ) :
    ‖v' - (⟪v', v₀⟫_ℝ) • v₀‖ ^ 2 ≤ ε / (μ₀ - μ₁) := by
  set p : ℝ := ⟪v', v₀⟫_ℝ with hp
  set w : E := v' - p • v₀ with hw
  have hv₀v₀ : ⟪v₀, v₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  have hwv₀ : ⟪w, v₀⟫_ℝ = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, hv₀v₀, hp]; ring
  have hv₀w : ⟪v₀, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact hwv₀
  have hdecomp : v' = p • v₀ + w := by rw [hw]; abel
  -- Pythagoras: `1 = p² + ‖w‖²`.
  have hpv : ‖p • v₀‖ ^ 2 = p ^ 2 := by
    rw [norm_smul, hv₀, mul_one, Real.norm_eq_abs, sq_abs]
  have hpyth : (1 : ℝ) = p ^ 2 + ‖w‖ ^ 2 := by
    have h2 : ‖v'‖ ^ 2 = ‖p • v₀‖ ^ 2 + 2 * ⟪p • v₀, w⟫_ℝ + ‖w‖ ^ 2 := by
      rw [hdecomp]; exact norm_add_sq_real _ _
    rw [hv', hpv, real_inner_smul_left, hv₀w] at h2
    nlinarith [h2]
  -- Rayleigh decomposition: `⟪C v', v'⟫ = μ₀ p² + ⟪C w, w⟫`.
  have hCwv₀ : ⟪C w, v₀⟫_ℝ = 0 := by
    simp [hC w v₀, hev, real_inner_smul_right, hwv₀]
  have hray : ⟪C v', v'⟫_ℝ = μ₀ * p ^ 2 + ⟪C w, w⟫_ℝ := by
    have hCv' : C v' = (p * μ₀) • v₀ + C w := by
      rw [hdecomp, map_add, map_smul, hev, smul_smul]
    rw [hCv', hdecomp]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hv₀v₀, hv₀w, hCwv₀, mul_zero, add_zero, mul_one]
    ring
  have hb : ⟪C w, w⟫_ℝ ≤ μ₁ * ‖w‖ ^ 2 := hμ₁ w hwv₀
  -- the algebraic kernel: `c + s = 1`, `μ₀ - ε ≤ μ₀ c + b`, `b ≤ μ₁ s` force `s ≤ ε/(μ₀-μ₁)`.
  set s : ℝ := ‖w‖ ^ 2 with hs
  have hgap' : 0 < μ₀ - μ₁ := by linarith
  rw [le_div_iff₀ hgap']
  have hp2 : p ^ 2 = 1 - s := by rw [hs] at hpyth ⊢; linarith
  rw [hray, hp2] at hRay
  nlinarith [hRay, hb]

/-! ## The tempered one-step factor

The relative-gap projector-increment bound carries a one-step distortion factor
`‖A(Tⁿx)‖·‖A(Tⁿx)⁻¹‖`. For the increments to be summable a.e. this factor must be
*tempered*: its normalized logarithm vanishes a.e. This is the orbital-tail consequence of
Birkhoff's theorem (`ae_tendsto_orbit_div_atTop_zero`: `n⁻¹·g(Tⁿx) → 0` a.e. for integrable `g`)
applied to the integrable signed log-norms `log‖A·‖` and `log‖A·⁻¹‖` (`integrable_logNorm_cocycle`
at `n = 1`, where `cocycle A T 1 = A`). -/

/-- **The tempered one-step factor.** The normalized log-norm of the one-step generator
along the orbit vanishes a.e.: `(1/n)·log‖A(Tⁿx)‖ → 0`. -/
theorem tendsto_logNorm_orbit_div_atTop_zero {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ] (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖A (T^[n] x)‖) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_orbit_div_atTop_zero hT
    (integrable_logNorm_cocycle hT hA hAmeas hTmeas hint hint' 1)] with x hx
  simpa using hx

/-- **The tempered one-step factor (inverse).** The normalized log-norm of the inverse of
the one-step generator along the orbit vanishes a.e.: `(1/n)·log‖A(Tⁿx)⁻¹‖ → 0`. -/
theorem tendsto_logNorm_inv_orbit_div_atTop_zero {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ] (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖(A (T^[n] x))⁻¹‖) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_orbit_div_atTop_zero hT
    (integrable_logNorm_inv_cocycle hT hA hAmeas hTmeas hint hint' 1)] with x hx
  simpa using hx

set_option linter.unusedSectionVars false in
/-- **Compound operator-norm upper bound** `‖compound k B‖ ≤ ‖B‖^k`. From the singular-value
product `∏_{i<k} σᵢ = ‖compound k B‖` (`prod_singularValues_eq_l2_opNorm_compound`) and the
per-index
ceiling `σᵢ ≤ ‖B‖` (`sigma_le_opNorm`). -/
theorem norm_compound_le (k : ℕ) (B : Matrix (Fin d) (Fin d) ℝ) :
    ‖ExteriorNorm.compoundMatrix k B‖ ≤ ‖B‖ ^ k := by
  rw [← ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound k B]
  calc ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin B).singularValues i
      ≤ ∏ _i ∈ Finset.range k, ‖B‖ := by
        apply Finset.prod_le_prod
        · intro i _; exact (Matrix.toEuclideanLin B).singularValues_nonneg i
        · intro i _; exact sigma_le_opNorm B i
    _ = ‖B‖ ^ k := by rw [Finset.prod_const, Finset.card_range]

set_option linter.unusedSectionVars false in
/-- **Compound operator-norm lower bound** `(‖B⁻¹‖⁻¹)^k ≤ ‖compound k B‖`, for invertible `B` and
`k ≤ d`. From the singular-value product and the per-index floor `‖B⁻¹‖⁻¹ ≤ σᵢ`
(`inv_opNorm_inv_le_sigma`). -/
theorem norm_inv_pow_le_norm_compound (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.det ≠ 0) (hk : k ≤ d) :
    (‖B⁻¹‖⁻¹) ^ k ≤ ‖ExteriorNorm.compoundMatrix k B‖ := by
  rw [← ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound k B]
  calc (‖B⁻¹‖⁻¹) ^ k
      = ∏ _i ∈ Finset.range k, ‖B⁻¹‖⁻¹ := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin B).singularValues i := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i hi
          exact inv_opNorm_inv_le_sigma hB (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)

/-- **Compound operator norm is positive** for invertible `B`, `k ≤ d`, `0 < d`. -/
theorem norm_compound_pos (k : ℕ) {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.det ≠ 0) (hk : k ≤ d) (hd : 0 < d) :
    0 < ‖ExteriorNorm.compoundMatrix k B‖ := by
  have hBinvdet : (B⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hB
  have hBinv : (0:ℝ) < ‖B⁻¹‖ := by
    rw [norm_pos_iff]
    intro h
    rw [h, Matrix.det_zero (Fin.pos_iff_nonempty.mp hd)] at hBinvdet
    exact hBinvdet rfl
  have hBinvne : (0:ℝ) < ‖B⁻¹‖⁻¹ := by positivity
  calc (0:ℝ) < (‖B⁻¹‖⁻¹) ^ k := by positivity
    _ ≤ ‖ExteriorNorm.compoundMatrix k B‖ := norm_inv_pow_le_norm_compound k hB hk

/-- **The tempered compound factor.** The normalized log compound operator norm along the
orbit vanishes a.e.: `(1/n)·log‖compound k (A(Tⁿx))‖ → 0`. Squeezed between
`-k·(1/n)log‖A(Tⁿx)⁻¹‖ → 0` and `k·(1/n)log‖A(Tⁿx)‖ → 0` via the compound-norm sandwich
(`norm_compound_le`, `norm_inv_pow_le_norm_compound`) and the tempered one-step factors
(`tendsto_logNorm_orbit_div_atTop_zero` and its inverse). This makes `κ(⋀ᵏB) = ‖compound k B‖·
‖compound k B⁻¹‖` subexponential, so it contributes `0` to the root-test log-limit. -/
theorem tendsto_logNorm_compound_orbit_div_atTop_zero {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hT : MeasurePreserving T μ μ) [IsFiniteMeasure μ] (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A) (hTmeas : Measurable T)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (k : ℕ) (hk : k ≤ d) (hd : 0 < d) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k (A (T^[n] x))‖)
      atTop (𝓝 0) := by
  filter_upwards [tendsto_logNorm_orbit_div_atTop_zero hT hA hAmeas hTmeas hint hint',
    tendsto_logNorm_inv_orbit_div_atTop_zero hT hA hAmeas hTmeas hint hint'] with x hup hlow
  have hupper : Tendsto
      (fun n : ℕ => (k : ℝ) * ((n : ℝ)⁻¹ * Real.log ‖A (T^[n] x)‖)) atTop (𝓝 0) := by
    have := hup.const_mul (k : ℝ); simpa using this
  have hlower : Tendsto
      (fun n : ℕ => -((k : ℝ) * ((n : ℝ)⁻¹ * Real.log ‖(A (T^[n] x))⁻¹‖))) atTop (𝓝 0) := by
    have := (hlow.const_mul (k : ℝ)).neg; simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    set B := A (T^[n] x) with hBdef
    have hBdet : B.det ≠ 0 := hA _
    have hninv : (0:ℝ) ≤ (n:ℝ)⁻¹ := by positivity
    have hCpos : 0 < ‖ExteriorNorm.compoundMatrix k B‖ := norm_compound_pos k hBdet hk hd
    have hBinvdet : (B⁻¹).det ≠ 0 := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hBdet
    have hBinvpos : (0:ℝ) < ‖B⁻¹‖ := by
      rw [norm_pos_iff]; intro h
      rw [h, Matrix.det_zero (Fin.pos_iff_nonempty.mp hd)] at hBinvdet; exact hBinvdet rfl
    have hlogle : -((k:ℝ) * Real.log ‖B⁻¹‖) ≤ Real.log ‖ExteriorNorm.compoundMatrix k B‖ := by
      have h1 : (‖B⁻¹‖⁻¹) ^ k ≤ ‖ExteriorNorm.compoundMatrix k B‖ :=
        norm_inv_pow_le_norm_compound k hBdet hk
      have h2 : Real.log ((‖B⁻¹‖⁻¹) ^ k) ≤ Real.log ‖ExteriorNorm.compoundMatrix k B‖ :=
        Real.log_le_log (by positivity) h1
      rwa [Real.log_pow, Real.log_inv, mul_neg] at h2
    calc -((k:ℝ) * ((n:ℝ)⁻¹ * Real.log ‖B⁻¹‖))
        = (n:ℝ)⁻¹ * (-((k:ℝ) * Real.log ‖B⁻¹‖)) := by ring
      _ ≤ (n:ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k B‖ :=
          mul_le_mul_of_nonneg_left hlogle hninv
  · filter_upwards [eventually_ge_atTop 1] with n hn
    set B := A (T^[n] x) with hBdef
    have hBdet : B.det ≠ 0 := hA _
    have hninv : (0:ℝ) ≤ (n:ℝ)⁻¹ := by positivity
    have hCpos : 0 < ‖ExteriorNorm.compoundMatrix k B‖ := norm_compound_pos k hBdet hk hd
    have hlogle : Real.log ‖ExteriorNorm.compoundMatrix k B‖ ≤ (k:ℝ) * Real.log ‖B‖ := by
      have h1 : ‖ExteriorNorm.compoundMatrix k B‖ ≤ ‖B‖ ^ k := norm_compound_le k B
      have h2 : Real.log ‖ExteriorNorm.compoundMatrix k B‖ ≤ Real.log (‖B‖ ^ k) :=
        Real.log_le_log hCpos h1
      rwa [Real.log_pow] at h2
    calc (n:ℝ)⁻¹ * Real.log ‖ExteriorNorm.compoundMatrix k B‖
        ≤ (n:ℝ)⁻¹ * ((k:ℝ) * Real.log ‖B‖) :=
          mul_le_mul_of_nonneg_left hlogle hninv
      _ = (k:ℝ) * ((n:ℝ)⁻¹ * Real.log ‖B‖) := by ring

/-! ## Refined Davis–Kahan off-diagonal sin-Θ

The Rayleigh-DEFICIT bound `sin_sq_le_rayleigh_deficit_div_gap` is *true* but the WRONG tool for the
gapped band-projector summability: feeding it the only provable deficit `ε ≤ (1−1/κ²)μ₀` yields
`sin²θ ≤ (1−1/κ²)/(1−r²)`, which is NOT summable along the orbit (the one-step `κ` is tempered with
positive mean, so `1−1/κ²` does not decay), and the route is structurally circular (`ε ≈ μ₀ sin²θ`).
The summable estimate needs the refined Davis–Kahan sin-Θ in **off-diagonal/residual form**: the
numerator is the off-diagonal block `C v₀ − ⟪C v₀, v₀⟫ v₀`, which (for the cocycle compound) carries
the extra `σₖ/σₖ₋₁` factor the deficit route loses. -/

/-- **Refined off-diagonal rank-1 sin-Θ.** For a perturbed operator `C`
with top unit eigenvector `vt` (eigenvalue `μ₀`), an unperturbed top eigenline `v₀`, and a Rayleigh
ceiling `ν < μ₀` of `C` on `v₀^⊥`, the sine of the angle between `vt` and `v₀` is bounded by the
*off-diagonal residual* `‖C v₀ − ⟪C v₀, v₀⟫ v₀‖` over the gap `μ₀ − ν`. Elementary (Rayleigh +
Cauchy–Schwarz + `|⟪vt,v₀⟫| ≤ 1`); no symmetry, no functional calculus. This replaces the
deficit-form `sin_sq_le_rayleigh_deficit_div_gap` as the load-bearing sin-Θ core. -/
theorem offdiag_sin_le_residual_div_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : E →ₗ[ℝ] E} {μ₀ ν : ℝ} {v₀ vt : E} (hv₀ : ‖v₀‖ = 1) (hvtnorm : ‖vt‖ = 1)
    (hev : C vt = μ₀ • vt) (hgap : ν < μ₀)
    (hν : ∀ w : E, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ ν * ‖w‖ ^ 2) :
    ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ ≤ ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν) := by
  set p : ℝ := ⟪vt, v₀⟫_ℝ with hp
  set w : E := vt - p • v₀ with hw
  set res : E := C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀ with hres
  have hv₀v₀ : ⟪v₀, v₀⟫_ℝ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  have hwv₀ : ⟪w, v₀⟫_ℝ = (0 : ℝ) := by
    rw [hw, inner_sub_left, real_inner_smul_left, hv₀v₀, hp]; ring
  have hv₀w : ⟪v₀, w⟫_ℝ = (0 : ℝ) := by rw [real_inner_comm]; exact hwv₀
  have hdecomp : vt = p • v₀ + w := by rw [hw]; abel
  have hresw : ⟪res, w⟫_ℝ = ⟪C v₀, w⟫_ℝ := by
    rw [hres, inner_sub_left, real_inner_smul_left, hv₀w, mul_zero, sub_zero]
  have hvtw : ⟪vt, w⟫_ℝ = ‖w‖ ^ 2 := by
    rw [hdecomp, inner_add_left, real_inner_smul_left, hv₀w, mul_zero,
      zero_add, real_inner_self_eq_norm_sq]
  have hCvtw : ⟪C vt, w⟫_ℝ = μ₀ * ‖w‖ ^ 2 := by rw [hev, real_inner_smul_left, hvtw]
  have hexpand : ⟪C vt, w⟫_ℝ = p * ⟪C v₀, w⟫_ℝ + ⟪C w, w⟫_ℝ := by
    rw [hdecomp, map_add, map_smul, inner_add_left, real_inner_smul_left]
  have hpres : p * ⟪res, w⟫_ℝ = μ₀ * ‖w‖ ^ 2 - ⟪C w, w⟫_ℝ := by
    rw [hresw]; have h := hCvtw.symm.trans hexpand; linarith [h]
  have hCww : ⟪C w, w⟫_ℝ ≤ ν * ‖w‖ ^ 2 := hν w hwv₀
  have hpabs : |p| ≤ 1 := by
    have hcs := abs_real_inner_le_norm vt v₀
    rw [hv₀, hvtnorm, mul_one] at hcs
    exact hcs
  have hCS : ⟪res, w⟫_ℝ ≤ ‖res‖ * ‖w‖ := real_inner_le_norm res w
  have hCS' : -(‖res‖ * ‖w‖) ≤ ⟪res, w⟫_ℝ := by
    have := real_inner_le_norm (-res) w
    rw [inner_neg_left, norm_neg] at this; linarith
  have hp_res : p * ⟪res, w⟫_ℝ ≤ ‖res‖ * ‖w‖ := by
    rcases le_or_gt 0 (⟪res, w⟫_ℝ) with hge | hlt
    · calc p * ⟪res, w⟫_ℝ ≤ |p| * ⟪res, w⟫_ℝ := by
            apply mul_le_mul_of_nonneg_right (le_abs_self p) hge
        _ ≤ 1 * ⟪res, w⟫_ℝ := by apply mul_le_mul_of_nonneg_right hpabs hge
        _ = ⟪res, w⟫_ℝ := one_mul _
        _ ≤ ‖res‖ * ‖w‖ := hCS
    · calc p * ⟪res, w⟫_ℝ ≤ |p| * |⟪res, w⟫_ℝ| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ 1 * |⟪res, w⟫_ℝ| := by apply mul_le_mul_of_nonneg_right hpabs (abs_nonneg _)
        _ = |⟪res, w⟫_ℝ| := one_mul _
        _ ≤ ‖res‖ * ‖w‖ := by rw [abs_le]; exact ⟨hCS', hCS⟩
  have hkey : (μ₀ - ν) * ‖w‖ ^ 2 ≤ ‖res‖ * ‖w‖ := by
    calc (μ₀ - ν) * ‖w‖ ^ 2 ≤ μ₀ * ‖w‖ ^ 2 - ⟪C w, w⟫_ℝ := by nlinarith [hCww]
      _ = p * ⟪res, w⟫_ℝ := hpres.symm
      _ ≤ ‖res‖ * ‖w‖ := hp_res
  have hgap' : 0 < μ₀ - ν := by linarith
  rcases eq_or_lt_of_le (norm_nonneg w) with hw0 | hwpos
  · rw [hw, ← hw0]; positivity
  · rw [hw] at hwpos ⊢
    rw [le_div_iff₀ hgap']
    have h2 : (μ₀ - ν) * ‖vt - p • v₀‖ * ‖vt - p • v₀‖ ≤ ‖res‖ * ‖vt - p • v₀‖ := by
      have : (μ₀ - ν) * ‖vt - p • v₀‖ ^ 2 = (μ₀ - ν) * ‖vt - p • v₀‖ * ‖vt - p • v₀‖ := by ring
      rw [hw] at hkey; linarith [hkey, this]
    have hcancel := le_of_mul_le_mul_right h2 hwpos
    linarith [hcancel]

/-! ## Summability by the root test (engine)

The corrected per-step bound has the shape `‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·κ(⋀ᵏB)²·rₙ` with
`rₙ = σₖ(Mₙ)/σₖ₋₁(Mₙ)` geometric (`(1/n)log rₙ → λₖ−λₖ₋₁ < 0`) and `κ(⋀ᵏB)²` subexponential
(`(1/n)log → 0`). Their product is summable by the root test. These are the scalar engines. -/

/-- **Geometric tail ⟹ summable.** A nonnegative sequence eventually dominated by `ρⁿ`
(`0 ≤ ρ < 1`) is summable. -/
theorem summable_of_eventually_le_geometric (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hev : ∀ᶠ n in atTop, a n ≤ ρ ^ n) :
    Summable a := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  apply summable_of_sum_range_le (c := (∑ i ∈ Finset.range N, a i) + (1 - ρ)⁻¹)
  · intro n; exact ha n
  intro n
  have hgeo : (0:ℝ) ≤ (1 - ρ)⁻¹ := by positivity
  rcases le_or_gt n N with h | h
  · have hsub : ∑ i ∈ Finset.range n, a i ≤ ∑ i ∈ Finset.range N, a i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) (fun i _ _ => ha i)
    linarith [hsub]
  · have hsplit : ∑ i ∈ Finset.range n, a i
        = (∑ i ∈ Finset.range N, a i) + ∑ i ∈ Finset.Ico N n, a i := by
      rw [← Finset.sum_range_add_sum_Ico _ (le_of_lt h)]
    rw [hsplit]
    have htail : ∑ i ∈ Finset.Ico N n, a i ≤ (1 - ρ)⁻¹ := by
      calc ∑ i ∈ Finset.Ico N n, a i
          ≤ ∑ i ∈ Finset.Ico N n, ρ ^ i := by
            apply Finset.sum_le_sum; intro i hi
            exact hN i (Finset.mem_Ico.mp hi).1
        _ ≤ ∑' i, ρ ^ i :=
            Summable.sum_le_tsum _ (fun i _ => by positivity)
              (summable_geometric_of_lt_one hρ0 hρ1)
        _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ1
    linarith [htail]

/-- **Root test (log form).** For an eventually-positive `a` whose normalized log tends to a
negative limit `L`, `a` is summable. The engine that turns the geometric×subexponential per-step
projector bound into summability (take `L = λₖ − λₖ₋₁ < 0`). -/
theorem summable_of_logLimit_neg (a : ℕ → ℝ) (hnn : ∀ n, 0 ≤ a n) (hpos : ∀ᶠ n in atTop, 0 < a n)
    {L : ℝ} (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop (𝓝 L)) :
    Summable a := by
  set ρ : ℝ := Real.exp (L / 2) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hev : ∀ᶠ n in atTop, a n ≤ ρ ^ n := by
    have hlt : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * Real.log (a n) < L / 2 := by
      have := hlog.eventually (eventually_lt_nhds (show L < L/2 by linarith))
      exact this
    have hn1 : ∀ᶠ n in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    filter_upwards [hlt, hpos, hn1] with n hn hp hn1
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hloga : Real.log (a n) < (L/2) * n := by
      rw [inv_mul_eq_div, div_lt_iff₀ hnpos] at hn
      linarith [hn]
    have : a n < ρ ^ n := by
      rw [hρdef, ← Real.exp_nat_mul]
      calc a n = Real.exp (Real.log (a n)) := (Real.exp_log hp).symm
        _ < Real.exp ((L/2) * n) := by exact Real.exp_lt_exp.mpr hloga
        _ = Real.exp (↑n * (L/2)) := by rw [mul_comm]
    exact le_of_lt this
  exact summable_of_eventually_le_geometric a hnn (le_of_lt hρ0) hρ1 hev

end ErgodicTheory

end
