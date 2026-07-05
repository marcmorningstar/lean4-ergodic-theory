import ErgodicTheory.OperatorEntropy.Basic
import ErgodicTheory.OperatorEntropy.PartialTrace
import ErgodicTheory.OperatorEntropy.Klein

/-!
# Subadditivity of the von Neumann entropy

For a bipartite density matrix `ρ` on `nA ⊗ nB` with reduced density matrices
`ρ_A = Tr_B ρ` and `ρ_B = Tr_A ρ`, the von Neumann entropy is **subadditive**:
`S(ρ) ≤ S(ρ_A) + S(ρ_B)`.

The proof is the elementary route through the scalar **Klein / Peierls inequality**
(`klein_scalar`, Carlen, *Trace Inequalities and Quantum Entropy*, Thm 2.11; Nielsen–Chuang
§11.3) — no Lieb concavity and no matrix logarithm / continuous functional calculus.

Writing `M = G diag(p) Gᴴ`, `ρ_A = U diag(λ) Uᴴ`, `ρ_B = V diag(μ) Vᴴ` from the spectral
theorem and `W = U ⊗ V`, the doubly stochastic matrix `D k m = |‖(Gᴴ W)ₖₘ‖²` together with the
product eigenvalue vector `s (i,j) = λ i · μ j` feeds Klein's inequality.  The key linear-algebra
input is the conjugation identity `Tr_B(Wᴴ M W) = Uᴴ (Tr_B M) U` (and its left analogue), which
lets the marginals of `D` be read off as `λ` and `μ`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker

noncomputable section

namespace ErgodicTheory.OperatorEntropy

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]

/-- The reduced density matrix on the left (A) factor: `Tr_B ρ`. -/
def DensityMatrix.partialTraceRight (ρ : DensityMatrix (nA × nB)) : DensityMatrix nA where
  val := _root_.ErgodicTheory.OperatorEntropy.partialTraceRight ρ.val
  posSemidef := PosSemidef.partialTraceRight ρ.posSemidef
  trace_one := by rw [trace_partialTraceRight, ρ.trace_one]

/-- The reduced density matrix on the right (B) factor: `Tr_A ρ`. -/
def DensityMatrix.partialTraceLeft (ρ : DensityMatrix (nA × nB)) : DensityMatrix nB where
  val := _root_.ErgodicTheory.OperatorEntropy.partialTraceLeft ρ.val
  posSemidef := PosSemidef.partialTraceLeft ρ.posSemidef
  trace_one := by rw [trace_partialTraceLeft, ρ.trace_one]

/-- The diagonal entry of a conjugation `Qᴴ diag(d) Q`, written as the real quadratic form
`∑ₖ ‖Qₖₘ‖² dₖ`. -/
private lemma diag_quadratic {N : Type*} [Fintype N] [DecidableEq N]
    (Q : Matrix N N ℂ) (d : N → ℝ) (m : N) :
    (star Q * diagonal (fun k => ((d k : ℝ) : ℂ)) * Q) m m
      = ((∑ k, Complex.normSq (Q k m) * d k : ℝ) : ℂ) := by
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  simp only [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

omit [DecidableEq nA] in
/-- Conjugation–partial-trace identity on the right factor: for `V` an isometry,
`Tr_B((U ⊗ V)ᴴ M (U ⊗ V)) = Uᴴ (Tr_B M) U`. -/
private lemma ptr_right_conj (M : Matrix (nA × nB) (nA × nB) ℂ)
    (U : Matrix nA nA ℂ) (V : Matrix nB nB ℂ) (hV : V * Vᴴ = 1) :
    partialTraceRight ((U ⊗ₖ V)ᴴ * M * (U ⊗ₖ V)) = Uᴴ * partialTraceRight M * U := by
  ext i i'
  rw [partialTraceRight_apply]
  have hexp : ∀ j : nB, ((U ⊗ₖ V)ᴴ * M * (U ⊗ₖ V)) (i, j) (i', j)
      = ∑ c, ∑ d, ∑ a, ∑ b,
          star (U a i) * star (V b j) * M (a, b) (c, d) * (U c i' * V d j) := by
    intro j
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.kronecker_apply, star_mul']
  have hcollapse : ∀ b d : nB, (∑ j, star (V b j) * V d j) = (1 : Matrix nB nB ℂ) d b := by
    intro b d
    have h1 : (∑ j, star (V b j) * V d j) = (V * Vᴴ) d b := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.conjTranspose_apply, mul_comm]
    rw [h1, hV]
  calc ∑ j, ((U ⊗ₖ V)ᴴ * M * (U ⊗ₖ V)) (i, j) (i', j)
      = ∑ j, ∑ c, ∑ d, ∑ a, ∑ b,
          star (U a i) * star (V b j) * M (a, b) (c, d) * (U c i' * V d j) :=
        Finset.sum_congr rfl fun j _ => hexp j
    _ = ∑ c, ∑ d, ∑ a, ∑ b, ∑ j,
          star (U a i) * star (V b j) * M (a, b) (c, d) * (U c i' * V d j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b,
          (star (U a i) * M (a, b) (c, d) * U c i') * (∑ j, star (V b j) * V d j) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ c, ∑ d, ∑ a, ∑ b,
          (star (U a i) * M (a, b) (c, d) * U c i') * (1 : Matrix nB nB ℂ) d b := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hcollapse b d]
    _ = ∑ c, ∑ d, ∑ a, star (U a i) * M (a, d) (c, d) * U c i' := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun a _ => ?_
        simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
        rw [Fintype.sum_ite_eq]
    _ = (Uᴴ * partialTraceRight M * U) i i' := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Matrix.conjTranspose_apply, partialTraceRight_apply, Finset.mul_sum, Finset.sum_mul]

omit [DecidableEq nB] in
/-- Conjugation–partial-trace identity on the left factor: for `U` an isometry,
`Tr_A((U ⊗ V)ᴴ M (U ⊗ V)) = Vᴴ (Tr_A M) V`. -/
private lemma ptr_left_conj (M : Matrix (nA × nB) (nA × nB) ℂ)
    (U : Matrix nA nA ℂ) (V : Matrix nB nB ℂ) (hU : U * Uᴴ = 1) :
    partialTraceLeft ((U ⊗ₖ V)ᴴ * M * (U ⊗ₖ V)) = Vᴴ * partialTraceLeft M * V := by
  ext j j'
  rw [partialTraceLeft_apply]
  have hexp : ∀ i : nA, ((U ⊗ₖ V)ᴴ * M * (U ⊗ₖ V)) (i, j) (i, j')
      = ∑ c, ∑ d, ∑ a, ∑ b,
          star (U a i) * star (V b j) * M (a, b) (c, d) * (U c i * V d j') := by
    intro i
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.kronecker_apply, star_mul']
  have hcollapse : ∀ a c : nA, (∑ i, star (U a i) * U c i) = (1 : Matrix nA nA ℂ) c a := by
    intro a c
    have h1 : (∑ i, star (U a i) * U c i) = (U * Uᴴ) c a := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_apply, mul_comm]
    rw [h1, hU]
  calc ∑ i, ((U ⊗ₖ V)ᴴ * M * (U ⊗ₖ V)) (i, j) (i, j')
      = ∑ i, ∑ c, ∑ d, ∑ a, ∑ b,
          star (U a i) * star (V b j) * M (a, b) (c, d) * (U c i * V d j') :=
        Finset.sum_congr rfl fun i _ => hexp i
    _ = ∑ c, ∑ d, ∑ a, ∑ b, ∑ i,
          star (U a i) * star (V b j) * M (a, b) (c, d) * (U c i * V d j') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b,
          (star (V b j) * M (a, b) (c, d) * V d j') * (∑ i, star (U a i) * U c i) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ c, ∑ d, ∑ a, ∑ b,
          (star (V b j) * M (a, b) (c, d) * V d j') * (1 : Matrix nA nA ℂ) c a := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hcollapse a c]
    _ = ∑ c, ∑ d, ∑ b, star (V b j) * M (c, b) (c, d) * V d j' := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
        rw [Fintype.sum_ite_eq]
    _ = (Vᴴ * partialTraceLeft M * V) j j' := by
        rw [Matrix.mul_apply, Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.conjTranspose_apply, partialTraceLeft_apply, Finset.mul_sum, Finset.sum_mul]

/-- **Subadditivity of the von Neumann entropy.**
`S(ρ) ≤ S(Tr_B ρ) + S(Tr_A ρ)` for a bipartite density matrix `ρ`. -/
theorem vonNeumannEntropy_subadditive (ρ : DensityMatrix (nA × nB)) :
    vonNeumannEntropy ρ ≤ vonNeumannEntropy ρ.partialTraceRight
      + vonNeumannEntropy ρ.partialTraceLeft := by
  simp only [vonNeumannEntropy]
  set hM := ρ.posSemidef.1 with hM_def
  set hA := ρ.partialTraceRight.posSemidef.1 with hA_def
  set hB := ρ.partialTraceLeft.posSemidef.1 with hB_def
  have hMspec0 := hM.spectral_theorem
  have hAspec0 := hA.spectral_theorem
  have hBspec0 := hB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hMspec0 hAspec0 hBspec0
  set p := hM.eigenvalues with hp_def
  set lam := hA.eigenvalues with hlam_def
  set mu := hB.eigenvalues with hmu_def
  set G := (hM.eigenvectorUnitary : Matrix (nA × nB) (nA × nB) ℂ) with hG_def
  set U := (hA.eigenvectorUnitary : Matrix nA nA ℂ) with hU_def
  set V := (hB.eigenvectorUnitary : Matrix nB nB ℂ) with hV_def
  have hRCp : (RCLike.ofReal ∘ p) = fun k => ((p k : ℝ) : ℂ) := by funext k; rfl
  have hRClam : (RCLike.ofReal ∘ lam) = fun k => ((lam k : ℝ) : ℂ) := by funext k; rfl
  have hRCmu : (RCLike.ofReal ∘ mu) = fun k => ((mu k : ℝ) : ℂ) := by funext k; rfl
  rw [hRCp] at hMspec0
  rw [hRClam] at hAspec0
  rw [hRCmu] at hBspec0
  have hAspec : partialTraceRight ρ.val
      = U * diagonal (fun k => ((lam k : ℝ) : ℂ)) * star U := hAspec0
  have hBspec : partialTraceLeft ρ.val
      = V * diagonal (fun k => ((mu k : ℝ) : ℂ)) * star V := hBspec0
  -- Unitarity facts.
  have hGss : star G * G = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hGss' : G * star G = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hUss : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUss' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hVss : star V * V = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hVss' : V * star V = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hUct : U * Uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hUss'
  have hVct : V * Vᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hVss'
  have hUcs : Uᴴ * U = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hUss
  have hVcs : Vᴴ * V = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hVss
  have hWss' : (U ⊗ₖ V) * (U ⊗ₖ V)ᴴ = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hUct, hVct, one_kronecker_one]
  have hWss : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hUcs, hVcs, one_kronecker_one]
  set Q := star G * (U ⊗ₖ V) with hQ_def
  have hsQ : star Q = (U ⊗ₖ V)ᴴ * G := by
    rw [hQ_def, star_mul, star_star, Matrix.star_eq_conjTranspose]
  have hQss' : Q * star Q = 1 := by
    rw [hsQ, hQ_def, mul_assoc, ← mul_assoc (U ⊗ₖ V), hWss', one_mul, hGss]
  have hQss : star Q * Q = 1 := by
    rw [hsQ, hQ_def, mul_assoc, ← mul_assoc G, hGss', one_mul, hWss]
  set D : (nA × nB) → (nA × nB) → ℝ := fun k m => Complex.normSq (Q k m) with hD_def
  set s : (nA × nB) → ℝ := fun m => lam m.1 * mu m.2 with hs_def
  set aa : (nA × nB) → ℝ := fun m => ∑ k, D k m * p k with haa_def
  -- (L1) diagonal of the conjugation.
  have hWMW : (U ⊗ₖ V)ᴴ * ρ.val * (U ⊗ₖ V)
      = star Q * diagonal (fun k => ((p k : ℝ) : ℂ)) * Q := by
    rw [hMspec0, hsQ, hQ_def]
    simp only [mul_assoc]
  have hL1 : ∀ m, ((U ⊗ₖ V)ᴴ * ρ.val * (U ⊗ₖ V)) m m = ((aa m : ℝ) : ℂ) := by
    intro m
    rw [hWMW, diag_quadratic Q p m]
  -- (L4 / L5) marginals of the doubly stochastic matrix.
  have heqU : Uᴴ * (U * diagonal (fun k => ((lam k : ℝ) : ℂ)) * star U) * U
      = diagonal (fun k => ((lam k : ℝ) : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose U]
    have h1 : star U * (U * diagonal (fun k => ((lam k : ℝ) : ℂ)) * star U) * U
        = star U * U * diagonal (fun k => ((lam k : ℝ) : ℂ)) * (star U * U) := by
      simp only [mul_assoc]
    rw [h1]
    simp only [hUss, one_mul, mul_one]
  have heqV : Vᴴ * (V * diagonal (fun k => ((mu k : ℝ) : ℂ)) * star V) * V
      = diagonal (fun k => ((mu k : ℝ) : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose V]
    have h1 : star V * (V * diagonal (fun k => ((mu k : ℝ) : ℂ)) * star V) * V
        = star V * V * diagonal (fun k => ((mu k : ℝ) : ℂ)) * (star V * V) := by
      simp only [mul_assoc]
    rw [h1]
    simp only [hVss, one_mul, mul_one]
  have hL4 : ∀ i, (∑ j, aa (i, j)) = lam i := by
    intro i
    have hc : ((∑ j, aa (i, j) : ℝ) : ℂ) = ((lam i : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      simp only [← hL1]
      rw [← partialTraceRight_apply, ptr_right_conj ρ.val U V hVct, hAspec, heqU,
        Matrix.diagonal_apply_eq]
    exact_mod_cast hc
  have hL5 : ∀ j, (∑ i, aa (i, j)) = mu j := by
    intro j
    have hc : ((∑ i, aa (i, j) : ℝ) : ℂ) = ((mu j : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      simp only [← hL1]
      rw [← partialTraceLeft_apply, ptr_left_conj ρ.val U V hUct, hBspec, heqV,
        Matrix.diagonal_apply_eq]
    exact_mod_cast hc
  -- (L2 / L3) double stochasticity.
  have hrow : ∀ k, (∑ m, D k m) = 1 := by
    intro k
    have hc : ((∑ m, D k m : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have he : (∑ m, ((D k m : ℝ) : ℂ)) = (Q * star Q) k k := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hD_def, Matrix.star_apply, Complex.star_def, Complex.mul_conj]
      rw [he, hQss', Matrix.one_apply_eq]
    exact_mod_cast hc
  have hcol : ∀ m, (∑ k, D k m) = 1 := by
    intro m
    have hc : ((∑ k, D k m : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have he : (∑ k, ((D k m : ℝ) : ℂ)) = (star Q * Q) m m := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hD_def, Matrix.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]
      rw [he, hQss, Matrix.one_apply_eq]
    exact_mod_cast hc
  -- Nonnegativity and total mass.
  have hp_nn : ∀ k, 0 ≤ p k := fun k => ρ.eigenvalues_nonneg k
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i => ρ.partialTraceRight.eigenvalues_nonneg i
  have hmu_nn : ∀ j, 0 ≤ mu j := fun j => ρ.partialTraceLeft.eigenvalues_nonneg j
  have hD_nn : ∀ k m, 0 ≤ D k m := by intro k m; simp only [hD_def]; exact Complex.normSq_nonneg _
  have haa_nn : ∀ m, 0 ≤ aa m := by
    intro m; rw [haa_def]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hD_nn k m) (hp_nn k)
  have hs_nn : ∀ m, 0 ≤ s m := by
    intro m; simp only [hs_def]; exact mul_nonneg (hlam_nn m.1) (hmu_nn m.2)
  have hp1 : (∑ k, p k) = 1 := ρ.sum_eigenvalues_eq_one
  have hlam1 : (∑ i, lam i) = 1 := ρ.partialTraceRight.sum_eigenvalues_eq_one
  have hmu1 : (∑ j, mu j) = 1 := ρ.partialTraceLeft.sum_eigenvalues_eq_one
  have hs1 : (∑ m, s m) = 1 := by
    have h1 : (∑ m, s m) = ∑ i, ∑ j, lam i * mu j := by
      simp only [hs_def]
      exact Fintype.sum_prod_type' fun i j => lam i * mu j
    rw [h1, ← Fintype.sum_mul_sum, hlam1, hmu1, mul_one]
  have hsum : (∑ k, p k) = ∑ m, s m := by rw [hp1, hs1]
  -- Support condition.
  have haa_zero : ∀ m, lam m.1 = 0 ∨ mu m.2 = 0 → aa m = 0 := by
    intro m hm
    have hmm : aa m = aa (m.1, m.2) := by rw [Prod.mk.eta]
    rcases hm with h | h
    · have hsumj := hL4 m.1
      rw [h] at hsumj
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => haa_nn (m.1, j)).1 hsumj
      rw [hmm]; exact hz m.2 (Finset.mem_univ _)
    · have hsumi := hL5 m.2
      rw [h] at hsumi
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => haa_nn (i, m.2)).1 hsumi
      rw [hmm]; exact hz m.1 (Finset.mem_univ _)
  have hsupp : ∀ m k, s m = 0 → D k m * p k = 0 := by
    intro m k hsm
    have hz : lam m.1 = 0 ∨ mu m.2 = 0 := by
      rw [hs_def] at hsm; exact mul_eq_zero.1 hsm
    have haa0 : aa m = 0 := haa_zero m hz
    simp only [haa_def] at haa0
    exact (Finset.sum_eq_zero_iff_of_nonneg
      fun k' _ => mul_nonneg (hD_nn k' m) (hp_nn k')).1 haa0 k (Finset.mem_univ _)
  -- Klein's inequality and the entropy decomposition.
  have hklein := klein_scalar p s D hp_nn hs_nn hD_nn hrow hcol hsum hsupp
  have hterm : ∀ m, aa m * Real.log (s m)
      = aa m * Real.log (lam m.1) + aa m * Real.log (mu m.2) := by
    intro m
    rcases (hlam_nn m.1).eq_or_lt with h1 | h1
    · have hz : aa m = 0 := haa_zero m (Or.inl h1.symm)
      rw [hz]; ring
    · rcases (hmu_nn m.2).eq_or_lt with h2 | h2
      · have hz : aa m = 0 := haa_zero m (Or.inr h2.symm)
        rw [hz]; ring
      · simp only [hs_def]
        rw [Real.log_mul h1.ne' h2.ne']; ring
  have hL8 : (∑ m, aa m * Real.log (s m))
      = (∑ i, lam i * Real.log (lam i)) + (∑ j, mu j * Real.log (mu j)) := by
    have e1 : (∑ m, aa m * Real.log (s m))
        = (∑ m, aa m * Real.log (lam m.1)) + ∑ m, aa m * Real.log (mu m.2) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => hterm m
    rw [e1]
    congr 1
    · have hrw : (∑ m, aa m * Real.log (lam m.1))
          = ∑ m : nA × nB, aa (m.1, m.2) * Real.log (lam m.1) :=
        Finset.sum_congr rfl fun m _ => by rw [Prod.mk.eta]
      rw [hrw, Fintype.sum_prod_type' fun i j => aa (i, j) * Real.log (lam i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, hL4 i]
    · have hrw : (∑ m, aa m * Real.log (mu m.2))
          = ∑ m : nA × nB, aa (m.1, m.2) * Real.log (mu m.2) :=
        Finset.sum_congr rfl fun m _ => by rw [Prod.mk.eta]
      rw [hrw, Fintype.sum_prod_type' fun i j => aa (i, j) * Real.log (mu j)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, hL5 j]
  have hkey : (∑ i, lam i * Real.log (lam i)) + (∑ j, mu j * Real.log (mu j))
      ≤ ∑ k, p k * Real.log (p k) := by
    rw [← hL8]
    have hconv : (∑ m, aa m * Real.log (s m))
        = ∑ m, (∑ k, D k m * p k) * Real.log (s m) := by simp only [haa_def]
    rw [hconv]; exact hklein
  -- Assemble: negate to entropies.
  have hentP : (∑ k, Real.negMulLog (p k)) = -(∑ k, p k * Real.log (p k)) := by
    simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
  have hentA : (∑ i, Real.negMulLog (lam i)) = -(∑ i, lam i * Real.log (lam i)) := by
    simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
  have hentB : (∑ j, Real.negMulLog (mu j)) = -(∑ j, mu j * Real.log (mu j)) := by
    simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
  rw [hentP, hentA, hentB]
  linarith [hkey]

end ErgodicTheory.OperatorEntropy
