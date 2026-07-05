/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import ErgodicTheory.OperatorEntropy.PetzRecovery
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityIntertwine

/-!
# Analytic continuation of the modular `it`-intertwining towards Petz recovery

This module builds the complex-analysis machinery that turns the *imaginary-axis* modular
intertwining condition

`Λ†((Λρ)^{it} (Λσ)^{-it}) = ρ^{it} σ^{-it}` (for all real `t`)

into its **entire** counterpart

`Λ†((Λρ)^{z} (Λσ)^{-z}) = ρ^{z} σ^{-z}` (for all complex `z`).

The key object is `cpow hA z`, the entire complex power `A^{z}` of a positive-definite matrix
defined through its spectral decomposition `A = U diag(λ) U*` by
`A^{z} = U diag(exp(z·log λ)) U*`. Each matrix entry `z ↦ (A^z)_{ij}` is a finite sum of
`Complex.exp`-composites, hence **entire**.

## Main definitions

* `ErgodicTheory.OperatorEntropy.Lieb.cpow`: the entire complex power `A^{z}` via the spectral theorem.
* `ErgodicTheory.OperatorEntropy.Lieb.upow`: the modular unitary `A^{it} = cpow hA (t·i)`.
* `ErgodicTheory.OperatorEntropy.Lieb.IntertwinesIt`: the imaginary-axis intertwining condition.

## Main results

* `cpow_apply`: the explicit entrywise formula for `cpow`.
* `matrix_eq_zero_of_entriesDifferentiable_of_imagAxis`: a matrix-valued **identity theorem** —
  an entrywise-entire matrix function vanishing on the imaginary axis vanishes identically.
* `intertwinesIt_continued`: the entire continuation of the intertwining condition.
* `cpow_ofReal_eq_rpow`: the **spectral bridge** `cpow hA (r : ℂ) = A ^ r` (the CFC real power),
  and its corollaries `cpow_one`, `cpow_zero`.
-/

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

open ErgodicTheory.OperatorEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/- `cpow`, `upow` and `IntertwinesIt` are the (byte-identical) definitions from
`PetzEqualityIntertwine`; they are imported from there so that the sufficiency and recovery
chains share a single canonical set of modular-power definitions. -/

/-- The explicit entrywise formula for `cpow`:
`(A^z)_{ij} = ∑ₖ U_{ik} · exp(z·log λₖ) · (U*)_{kj}`. -/
lemma cpow_apply {A : Matrix n n ℂ} (hA : A.PosDef) (z : ℂ) (i j : n) :
    cpow hA z i j = ∑ k, (hA.1.eigenvectorUnitary : Matrix n n ℂ) i k *
      Complex.exp (z * (Real.log (hA.1.eigenvalues k) : ℂ)) *
      (star (hA.1.eigenvectorUnitary : Matrix n n ℂ)) k j := by
  unfold cpow
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_diagonal]

/-! ## Entrywise differentiability machinery -/

/-- A matrix-valued function of a complex variable has **entrywise `ℂ`-differentiable** entries. -/
def EntriesDifferentiable (M : ℂ → Matrix n n ℂ) : Prop :=
  ∀ i j, Differentiable ℂ (fun z => M z i j)

section
omit [Fintype n] [DecidableEq n]

/-- Constant matrix functions are entrywise differentiable. -/
lemma EntriesDifferentiable.const (C : Matrix n n ℂ) :
    EntriesDifferentiable (fun _ => C) :=
  fun _ _ => differentiable_const _

/-- Entrywise differentiability is preserved by pointwise subtraction. -/
lemma EntriesDifferentiable.sub {M N : ℂ → Matrix n n ℂ}
    (hM : EntriesDifferentiable M) (hN : EntriesDifferentiable N) :
    EntriesDifferentiable (fun z => M z - N z) := by
  intro i j
  have h : (fun z => (M z - N z) i j) = fun z => M z i j - N z i j := by
    funext z; rw [Matrix.sub_apply]
  rw [h]
  exact (hM i j).sub (hN i j)

/-- Entrywise differentiability is preserved by finite sums. -/
lemma EntriesDifferentiable.finsetSum {γ : Type*} (s : Finset γ)
    (F : γ → ℂ → Matrix n n ℂ) (h : ∀ p ∈ s, EntriesDifferentiable (F p)) :
    EntriesDifferentiable (fun z => ∑ p ∈ s, F p z) := by
  intro i j
  have hEq : (fun z => (∑ p ∈ s, F p z) i j) = fun z => ∑ p ∈ s, (F p z) i j := by
    funext z; rw [Matrix.sum_apply]
  rw [hEq]
  exact Differentiable.fun_sum (fun p hp => (h p hp) i j)

end

omit [DecidableEq n] in
/-- Entrywise differentiability is preserved by pointwise matrix multiplication. -/
lemma EntriesDifferentiable.mul {M N : ℂ → Matrix n n ℂ}
    (hM : EntriesDifferentiable M) (hN : EntriesDifferentiable N) :
    EntriesDifferentiable (fun z => M z * N z) := by
  intro i j
  have h : (fun z => (M z * N z) i j) = fun z => ∑ k, M z i k * N z k j := by
    funext z; rw [Matrix.mul_apply]
  rw [h]
  exact Differentiable.fun_sum (fun k _ => (hM i k).mul (hN k j))

/-- Entrywise differentiability is preserved by the Heisenberg adjoint `Λ†`. -/
lemma EntriesDifferentiable.adj (Λ : KrausChannel n) {M : ℂ → Matrix n n ℂ}
    (hM : EntriesDifferentiable M) : EntriesDifferentiable (fun z => Λ.adj (M z)) := by
  have hEq : (fun z => Λ.adj (M z))
      = fun z => ∑ p : Λ.ι, (Λ.K p)ᴴ * M z * Λ.K p := rfl
  rw [hEq]
  refine EntriesDifferentiable.finsetSum Finset.univ
    (fun p z => (Λ.K p)ᴴ * M z * Λ.K p) (fun p _ => ?_)
  exact ((EntriesDifferentiable.const ((Λ.K p)ᴴ)).mul hM).mul (EntriesDifferentiable.const (Λ.K p))

/-- The entries of `z ↦ cpow hA (φ z)` are `ℂ`-differentiable whenever `φ` is. -/
lemma cpow_comp_entriesDifferentiable {A : Matrix n n ℂ} (hA : A.PosDef)
    {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) :
    EntriesDifferentiable (fun z => cpow hA (φ z)) := by
  intro i j
  have hform : (fun z => cpow hA (φ z) i j)
      = fun z => ∑ k, (hA.1.eigenvectorUnitary : Matrix n n ℂ) i k *
          Complex.exp (φ z * (Real.log (hA.1.eigenvalues k) : ℂ)) *
          (star (hA.1.eigenvectorUnitary : Matrix n n ℂ)) k j := by
    funext z; exact cpow_apply hA (φ z) i j
  rw [hform]
  exact Differentiable.fun_sum (fun k _ =>
    (((differentiable_const ((hA.1.eigenvectorUnitary : Matrix n n ℂ) i k)).mul
        ((hφ.mul_const ((Real.log (hA.1.eigenvalues k) : ℂ))).cexp)).mul
      (differentiable_const ((star (hA.1.eigenvectorUnitary : Matrix n n ℂ)) k j))))

/-! ## The matrix identity theorem -/

section
omit [Fintype n] [DecidableEq n]

/-- If every real multiple of `i` maps to a zero of `h`, then `h` vanishes frequently near `0`
inside the punctured neighbourhood filter. -/
lemma frequently_zero_nhdsWithin_of_imagAxis {h : ℂ → ℂ}
    (hz : ∀ t : ℝ, h ((t : ℂ) * Complex.I) = 0) :
    ∃ᶠ w in 𝓝[≠] (0 : ℂ), h w = 0 := by
  set u : ℕ → ℂ := fun k => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hu
  have htend : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun k : ℕ => (((1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ))
          atTop (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp h0
      simp only [Complex.ofReal_zero] at h1
      have h2 := h1.mul_const Complex.I
      simpa [hu, zero_mul] using h2
    · refine Eventually.of_forall (fun k => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)) Complex.I_ne_zero
  exact htend.frequently ((Eventually.of_forall
    (fun k : ℕ => hz (1 / ((k : ℝ) + 1)))).frequently)

/-- **Matrix identity theorem.** A matrix-valued function whose entries are entire and which
vanishes on the imaginary axis vanishes identically. -/
theorem matrix_eq_zero_of_entriesDifferentiable_of_imagAxis
    {g : ℂ → Matrix n n ℂ} (hg : EntriesDifferentiable g)
    (hvan : ∀ t : ℝ, g ((t : ℂ) * Complex.I) = 0) (z : ℂ) : g z = 0 := by
  refine Matrix.ext (fun i j => ?_)
  rw [Matrix.zero_apply]
  have hAO : AnalyticOnNhd ℂ (fun w => g w i j) Set.univ :=
    (hg i j).differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), g w i j = 0 :=
    frequently_zero_nhdsWithin_of_imagAxis (fun t => by rw [hvan t]; rw [Matrix.zero_apply])
  have hEqOn := hAO.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ 0) hfreq
  simpa using hEqOn (Set.mem_univ z)

end

/-! ## Analytic continuation of the intertwining condition -/

variable {ρ σ : DensityMatrix n} {Λ : KrausChannel n}

/-- **Entire continuation of the intertwining condition.** From the imaginary-axis intertwining
`IntertwinesIt`, the identity `Λ†((Λρ)^{z}(Λσ)^{-z}) = ρ^{z}σ^{-z}` holds for *all* complex `z`. -/
theorem intertwinesIt_continued (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hInt : IntertwinesIt hρ hσ hΛρ hΛσ) (z : ℂ) :
    Λ.adj (cpow hΛρ z * cpow hΛσ (-z)) = cpow hρ z * cpow hσ (-z) := by
  set g : ℂ → Matrix n n ℂ := fun w =>
    Λ.adj (cpow hΛρ w * cpow hΛσ (-w)) - cpow hρ w * cpow hσ (-w) with hg
  have hdiff : EntriesDifferentiable g := by
    refine EntriesDifferentiable.sub ?_ ?_
    · exact EntriesDifferentiable.adj Λ
        ((cpow_comp_entriesDifferentiable hΛρ differentiable_id).mul
          (cpow_comp_entriesDifferentiable hΛσ (differentiable_id.neg)))
    · exact (cpow_comp_entriesDifferentiable hρ differentiable_id).mul
        (cpow_comp_entriesDifferentiable hσ (differentiable_id.neg))
  have hvan : ∀ t : ℝ, g ((t : ℂ) * Complex.I) = 0 := by
    intro t
    simp only [hg]
    have e : (-((t : ℂ) * Complex.I)) = ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, sub_eq_zero]
    have hI := hInt t
    simp only [upow] at hI
    exact hI
  have hzero := matrix_eq_zero_of_entriesDifferentiable_of_imagAxis hdiff hvan z
  rw [hg] at hzero
  rwa [sub_eq_zero] at hzero

/-! ## The spectral bridge to the CFC real power -/

/-- **Spectral bridge.** For a positive-definite matrix, the entire power at a real exponent agrees
with the continuous-functional-calculus real power: `cpow hA (r : ℂ) = A ^ r`. -/
lemma cpow_ofReal_eq_rpow {A : Matrix n n ℂ} (hA : A.PosDef) (r : ℝ) :
    cpow hA (r : ℂ) = A ^ r := by
  have step1 : (A ^ r : Matrix n n ℂ) = cfc (fun x : ℝ => x ^ r) A :=
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg
  rw [step1, hA.1.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  unfold cpow
  congr 2
  refine congrArg diagonal (funext fun i => ?_)
  have hpos : 0 < hA.1.eigenvalues i := hA.eigenvalues_pos i
  simp only [Function.comp_apply]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.rpow_def_of_pos hpos,
    mul_comm (Real.log (hA.1.eigenvalues i)) r]
  rfl

/-- `cpow hA 1 = A`. -/
lemma cpow_one {A : Matrix n n ℂ} (hA : A.PosDef) : cpow hA (1 : ℂ) = A := by
  have h := cpow_ofReal_eq_rpow hA 1
  rw [Complex.ofReal_one] at h
  rw [h, CFC.rpow_one A hA.posSemidef.nonneg]

/-! ## The KMS-point specialisation

The continued intertwining, evaluated at the KMS half-power `z = 1/2` and transported through the
spectral bridge, is the Connes-cocycle identity at the boundary. This is the furthest that the pure
analytic continuation reaches; the remaining step to full Petz recovery (turning the *product*
`(Λρ)^{1/2}(Λσ)^{-1/2}` under `Λ†` into the *sandwich* `√σ · Λ†((Λσ)^{-1/2}(Λρ)(Λσ)^{-1/2}) · √σ`)
is the Kadison–Schwarz multiplicative-domain equality, not an analytic-continuation fact. -/

/-- **KMS-point (half-power) intertwining.** The continued identity at `z = 1/2`, transported to the
CFC real power: `Λ†((Λρ)^{1/2}(Λσ)^{-1/2}) = ρ^{1/2}σ^{-1/2}`. -/
theorem intertwinesIt_rpow_half (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hInt : IntertwinesIt hρ hσ hΛρ hΛσ) :
    Λ.adj ((Λ.toDM ρ).val ^ (1 / 2 : ℝ) * (Λ.toDM σ).val ^ (-(1 / 2) : ℝ))
      = ρ.val ^ (1 / 2 : ℝ) * σ.val ^ (-(1 / 2) : ℝ) := by
  have e1 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  have e2 : ((-(1 / 2) : ℝ) : ℂ) = -(1 / 2 : ℂ) := by push_cast; ring
  rw [← cpow_ofReal_eq_rpow hΛρ (1 / 2), ← cpow_ofReal_eq_rpow hΛσ (-(1 / 2)),
    ← cpow_ofReal_eq_rpow hρ (1 / 2), ← cpow_ofReal_eq_rpow hσ (-(1 / 2)), e1, e2]
  exact intertwinesIt_continued hρ hσ hΛρ hΛσ hInt (1 / 2 : ℂ)

end ErgodicTheory.OperatorEntropy.Lieb

end
