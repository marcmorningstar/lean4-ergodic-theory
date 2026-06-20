/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.SpectralMeasurable
import Oseledets.Lyapunov.Measurable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Measurability of the orthogonal projector onto the finite-step cocycle kernel

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem degenerates
from a direct-sum decomposition to a measurable **filtration** `ℝ^d = V₁(ω) ⊃ ⋯ ⊃ V_{k+1}(ω) = {0}`
(Quas, *Multiplicative Ergodic Theorems and Applications*, Universidade de São Paulo lecture notes,
2013, **Theorem 2**; after Oseledec and Raghunathan), whose bottom space is the *eventual kernel*
`⨆ n, cocycleKer A T n x`. Quas' Theorem 2 demands a *measurable* choice of each flag space; a
robust way to make a subspace-valued map `x ↦ K x` measurable, used throughout this development, is
to show that its **orthogonal-projection matrix** `x ↦ orthProjMatrix (K x)` is measurable (the
`Oseledets.MeasurableSubspace` notion of `Oseledets.Lyapunov.MeasurableSubspace`).

This file delivers exactly that for each *fixed step* `n`: the orthogonal projector onto the
`n`-step cocycle kernel — viewed as a subspace `cocycleKerEuclid A T n x` of the Euclidean space
`EuclideanSpace ℝ (Fin d)` — depends measurably on `x`. The eventual kernel is the (monotone) union
of these finite-step kernels (`Oseledets.eventualKer`), so this per-step projector measurability is
the analytic engine for the measurability of the bottom flag space.

## Strategy

The kernel projector is realised *spectrally*, so its measurability reduces to the already-proven
`Oseledets.measurable_spectralProjector` (no new measurable-selection theorem is needed). Set
`S x := (cocycle A T n x)ᵀ * (cocycle A T n x)`. Then:

* `S x` is Hermitian and positive semidefinite (`Matrix.isHermitian_conjTranspose_mul_self`,
  `Matrix.posSemidef_conjTranspose_mul_self`; for real matrices `conjTranspose = transpose`), so its
  spectrum lies in `[0, ∞)`. It is measurable in `x` (a measurable cocycle composed with the
  entrywise transpose and the jointly-measurable matrix product, i.e.
  `Oseledets.instMeasurableMul₂Matrix`).
* `ker S = ker (cocycle A T n x)`: `S v = 0 ↔ ⟪v, S v⟫ = 0 ↔ ‖M v‖² = 0 ↔ M v = 0`
  (`Matrix.inner_toEuclideanCLM`, `inner_self_eq_zero`).
* The orthogonal projector onto `ker S` is the *spectral `≤ 0` projector*
  `cfc (Set.indicator (Set.Iic 0) 1) (S x)`: this continuous-functional-calculus element is a
  self-adjoint idempotent (because the `{0,1}`-valued indicator squares to itself on the spectrum),
  hence a `IsStarProjection`, and its range is exactly `ker S` (one inclusion from `S * P = 0`,
  since `id · indicator (Iic 0) 1 = 0` on `[0, ∞)`; the other from `(1 - P) v = (cfc h S) (S v) = 0`
  for `v ∈ ker S`, where `h` is any continuous extension with `id · h = indicator (Ioi 0) 1` on the
  finite spectrum). Identifying `orthProjMatrix` with `cfc` via the star-algebra equivalence
  `Matrix.toEuclideanCLM` gives the pointwise bridge.

## Main definitions

* `Oseledets.cocycleKerEuclid`: the `n`-step cocycle kernel transported to a subspace of
  `EuclideanSpace ℝ (Fin d)`, i.e. `LinearMap.ker (Matrix.toEuclideanCLM (cocycle A T n x))`.

## Main results

* `Oseledets.orthProjMatrix_cocycleKerEuclid_eq_spectralProjector`: the pointwise bridge
  `orthProjMatrix (cocycleKerEuclid A T n x) = cfc (Set.indicator (Set.Iic 0) 1) (Sᴴ S)`.
* `Oseledets.measurable_orthProjMatrix_cocycleKer`: `x ↦ orthProjMatrix (cocycleKerEuclid A T n x)`
  is measurable, obtained by rewriting with the bridge and applying
  `Oseledets.measurable_spectralProjector`.

## Remaining gap toward the measurable equivariant flag

This module makes the projector onto the *finite-step* kernel measurable. Assembling the full
measurable bottom flag space `x ↦ eventualKer A T x` from these finite-step projectors (the
projectors increase to the eventual-kernel projector as `n → ∞`, by kernel monotonicity), together
with the measurability of the *intermediate* slow spaces `V_j(ω)` and their exponents from the
Kingman/exterior-power machinery, is not carried out here; only the per-step kernel projector is
made measurable.
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- The kernel of the `n`-step cocycle, transported to a subspace of `EuclideanSpace ℝ (Fin d)`
via the star-algebra equivalence `Matrix.toEuclideanCLM`. This is the Euclidean-space avatar of
`Oseledets.cocycleKer`, packaged so that `orthProjMatrix` (the orthogonal-projection matrix used by
`Oseledets.MeasurableSubspace`) applies to it directly. -/
noncomputable def cocycleKerEuclid (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x)).toLinearMap

/-- The **Gram matrix** of the `n`-step cocycle, `(cocycle A T n x)ᵀ * (cocycle A T n x)`. It is
Hermitian and positive semidefinite, and its kernel coincides with the kernel of the cocycle; its
spectral `≤ 0` projector is the orthogonal projector onto that kernel. -/
noncomputable def cocycleGram (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) : Matrix (Fin d) (Fin d) ℝ :=
  (cocycle A T n x)ᵀ * (cocycle A T n x)

/-- The Gram matrix `(cocycle)ᵀ * cocycle` is Hermitian (= self-adjoint): for real matrices the
conjugate transpose is the transpose, so this is `Matrix.isHermitian_conjTranspose_mul_self`. -/
theorem cocycleGram_isHermitian (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    (cocycleGram A T n x).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_self (cocycle A T n x)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The Gram matrix `(cocycle)ᵀ * cocycle` is positive semidefinite, so its real spectrum lies in
`[0, ∞)`. (`Matrix.posSemidef_conjTranspose_mul_self`; `conjTranspose = transpose` for reals.) -/
theorem cocycleGram_posSemidef (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    (cocycleGram A T n x).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (cocycle A T n x)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The Gram-matrix family `x ↦ (cocycle A T n x)ᵀ * (cocycle A T n x)` is measurable: the cocycle
is measurable, transpose is entrywise (hence measurable), and matrix multiplication is jointly
measurable (`Oseledets.instMeasurableMul₂Matrix`). -/
theorem measurable_cocycleGram [MeasurableSpace X] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : Measurable A) {T : X → X} (hT : Measurable T) (n : ℕ) :
    Measurable (fun x => cocycleGram A T n x) := by
  have hcoc : Measurable (fun x => cocycle A T n x) := measurable_cocycle hA hT n
  have htr : Measurable (fun x => (cocycle A T n x)ᵀ) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simp only [Matrix.transpose_apply]
    exact ((measurable_pi_apply i).comp (measurable_pi_apply j)).comp hcoc
  exact htr.mul hcoc

/-- The real spectrum of the (positive-semidefinite) Gram matrix lies in `[0, ∞)`: any spectral
value is nonnegative (`StarOrderedRing.nonneg_iff_spectrum_nonneg` applied to `0 ≤ Sᵀ S`). -/
theorem cocycleGram_spectrum_nonneg (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) {s : ℝ} (hs : s ∈ spectrum ℝ (cocycleGram A T n x)) : 0 ≤ s := by
  have hle : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ cocycleGram A T n x :=
    (cocycleGram_posSemidef A T n x).nonneg
  exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _).mp hle s hs

/-- **Kernel of the Gram matrix = kernel of the cocycle.** A vector `v` of Euclidean space is in the
kernel of `toEuclideanCLM (Sᵀ S)` iff it is in the kernel of `toEuclideanCLM S`: indeed
`⟪v, (Sᵀ S) v⟫ = ⟪S v, S v⟫ = ‖S v‖²`, which vanishes iff `S v = 0`. -/
theorem ker_toEuclideanCLM_cocycleGram (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) :
    LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycleGram A T n x)).toLinearMap
      = cocycleKerEuclid A T n x := by
  set M := cocycle A T n x with hM
  ext v
  simp only [cocycleKerEuclid, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hv
    -- `0 = ⟪v, (Mᵀ M) v⟫ = ⟪M v, M v⟫`, so `M v = 0`.
    have hinner : ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycleGram A T n x) v⟫ = 0 := by
      rw [hv, inner_zero_right]
    rw [Matrix.inner_toEuclideanCLM] at hinner
    have hMv : ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) M v, Matrix.toEuclideanCLM (𝕜 := ℝ) M v⟫
        = (0 : ℝ) := by
      rw [Matrix.inner_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
      rw [cocycleGram, ← hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose] at hinner
      exact hinner
    exact inner_self_eq_zero.mp hMv
  · intro hv
    rw [cocycleGram]
    have : Matrix.toEuclideanCLM (𝕜 := ℝ) (Mᵀ * M) v
        = Matrix.toEuclideanCLM (𝕜 := ℝ) Mᵀ (Matrix.toEuclideanCLM (𝕜 := ℝ) M v) := by
      rw [map_mul]; rfl
    rw [this, hv, map_zero]

private theorem isSelfAdjoint_cocycleGram (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) : IsSelfAdjoint (cocycleGram A T n x) :=
  (cocycleGram_isHermitian A T n x)

/-- The indicator `indicator (Iic 0) 1` is `{0,1}`-valued, hence idempotent: it equals its own
square everywhere (in particular on the spectrum). -/
private theorem indicator_mul_self :
    (fun s : ℝ => Set.indicator (Set.Iic 0) (1 : ℝ → ℝ) s * Set.indicator (Set.Iic 0) 1 s)
      = Set.indicator (Set.Iic 0) (1 : ℝ → ℝ) := by
  funext s
  by_cases hs : s ∈ Set.Iic 0
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

/-- The projector `P = cfc (indicator (Iic 0) 1) S` is idempotent: `P * P = P`, because the
indicator squares to itself on the (finite) spectrum and `cfc` is multiplicative. -/
private theorem kerProj_idempotent (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    IsIdempotentElem (cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (cocycleGram A T n x)) := by
  have hfin := (cocycleGram A T n x).finite_real_spectrum
  have hcont : ContinuousOn (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ))
      (spectrum ℝ (cocycleGram A T n x)) := hfin.continuousOn _
  unfold IsIdempotentElem
  rw [← cfc_mul _ _ _ hcont hcont, indicator_mul_self]

/-- The projector `P = cfc (indicator (Iic 0) 1) S` is self-adjoint (the CFC of a real-valued
function of a self-adjoint matrix is self-adjoint). -/
private theorem kerProj_isSelfAdjoint (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) :
    IsSelfAdjoint (cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (cocycleGram A T n x)) :=
  cfc_predicate _ _

/-- `S * P = 0`, where `P = cfc (indicator (Iic 0) 1) S`: on the spectrum `⊆ [0, ∞)` of the
positive-semidefinite `S`, the function `id · indicator (Iic 0) 1` vanishes (at `s = 0` because
`id = 0`; at `s > 0` because the indicator is `0`), so `cfc (id · indicator) S = cfc 0 S = 0` and,
by multiplicativity of `cfc`, this equals `S * P`. -/
private theorem cocycleGram_mul_kerProj (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) :
    cocycleGram A T n x
      * cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (cocycleGram A T n x) = 0 := by
  have hfin := (cocycleGram A T n x).finite_real_spectrum
  have hcontInd : ContinuousOn (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ))
      (spectrum ℝ (cocycleGram A T n x)) := hfin.continuousOn _
  have hcontId : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ (cocycleGram A T n x)) :=
    continuousOn_id
  have hself : IsSelfAdjoint (cocycleGram A T n x) := isSelfAdjoint_cocycleGram A T n x
  -- `S = cfc id S`, so `S * P = cfc (id · indicator) S`.
  have hmul : cocycleGram A T n x
      * cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (cocycleGram A T n x)
      = cfc (fun s => id s * Set.indicator (Set.Iic 0) (1 : ℝ → ℝ) s) (cocycleGram A T n x) := by
    rw [cfc_mul _ _ _ hcontId hcontInd, cfc_id ℝ (cocycleGram A T n x)]
  rw [hmul]
  -- on the spectrum `id · indicator (Iic 0) 1 = 0`.
  have hspec : (spectrum ℝ (cocycleGram A T n x)).EqOn
      (fun s => id s * Set.indicator (Set.Iic 0) (1 : ℝ → ℝ) s) (fun _ => 0) := by
    intro s hs
    have hnonneg : 0 ≤ s := cocycleGram_spectrum_nonneg A T n x hs
    by_cases hs0 : s ∈ Set.Iic 0
    · have : s = 0 := le_antisymm (by simpa using hs0) hnonneg
      simp [this]
    · simp [Set.indicator_of_notMem hs0]
  rw [cfc_congr hspec]
  simp

/-- The range of the projector `P = cfc (indicator (Iic 0) 1) S` is the kernel of `S`. The inclusion
`range P ⊆ ker S` is from `S * P = 0` (`cocycleGram_mul_kerProj`); the reverse inclusion is from
`(1 - P) v = (cfc h S) (S v) = 0` for `v ∈ ker S`, where `h` is a continuous function with
`id · h = indicator (Ioi 0) 1` on the finite spectrum, so `1 - P = cfc h S * S`. -/
private theorem range_toEuclideanCLM_kerProj (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (cocycleGram A T n x))).toLinearMap
      = LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycleGram A T n x)).toLinearMap := by
  set S := cocycleGram A T n x with hS
  set P := cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) S with hP
  have hfin := S.finite_real_spectrum
  apply le_antisymm
  · -- range P ⊆ ker S, from S * P = 0.
    rintro - ⟨w, rfl⟩
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    have hSP : S * P = 0 := cocycleGram_mul_kerProj A T n x
    have : Matrix.toEuclideanCLM (𝕜 := ℝ) S (Matrix.toEuclideanCLM (𝕜 := ℝ) P w)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) (S * P) w := by rw [map_mul]; rfl
    rw [this, hSP, map_zero, ContinuousLinearMap.zero_apply]
  · -- ker S ⊆ range P: for v ∈ ker S, P v = v.
    intro v hv
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
    -- `h s := if s = 0 then 1 else 0` is `1` on `{0}` and `0` elsewhere; on the spectrum
    -- `id s * h s = 0 = indicator (Ioi 0) 1 - 0`... we instead show `(1 - P) v = 0`.
    -- Define `g s := indicator (Ioi 0) 1 s / s` continuously: use `h s = if s ≤ 0 then 0 else 1/s`.
    -- On the finite spectrum every function is `ContinuousOn`, so pick `h := fun s => if s ≤ 0 then
    -- 0 else 1 / s` and verify `id · h = (1 - indicator (Iic 0) 1)` on the spectrum.
    set h : ℝ → ℝ := fun s => if s ≤ 0 then 0 else 1 / s with hh
    have hcontH : ContinuousOn h (spectrum ℝ S) := hfin.continuousOn _
    have hcontId : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ S) := continuousOn_id
    have hcontInd : ContinuousOn (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (spectrum ℝ S) :=
      hfin.continuousOn _
    -- `1 - P = cfc (1 - indicator) S = cfc (id · h) S = cfc h S * S`.
    have hself : IsSelfAdjoint S := isSelfAdjoint_cocycleGram A T n x
    have hkey : (1 : Matrix (Fin d) (Fin d) ℝ) - P = cfc h S * S := by
      -- LHS as a single CFC: `1 - P = cfc (fun s => 1 - indicator s) S`.
      have hcontOne : ContinuousOn (1 : ℝ → ℝ) (spectrum ℝ S) := hfin.continuousOn _
      have hLHS : (1 : Matrix (Fin d) (Fin d) ℝ) - P
          = cfc (fun s => (1 : ℝ → ℝ) s - Set.indicator (Set.Iic 0) (1 : ℝ → ℝ) s) S := by
        rw [cfc_sub (1 : ℝ → ℝ) _ S hcontOne hcontInd, cfc_one ℝ S, hP]
      -- RHS as a single CFC: `cfc h S * S = cfc (fun s => h s * id s) S`.
      have hRHS : cfc h S * S = cfc (fun s => h s * id s) S := by
        rw [cfc_mul _ _ _ hcontH hcontId, cfc_id ℝ S]
      rw [hLHS, hRHS]
      apply cfc_congr
      intro s hs
      have hnonneg : 0 ≤ s := cocycleGram_spectrum_nonneg A T n x (by rw [hS] at hs; exact hs)
      simp only [Pi.one_apply, hh, id_eq]
      by_cases hs0 : s = 0
      · simp [hs0]
      · have hpos : 0 < s := lt_of_le_of_ne hnonneg (Ne.symm hs0)
        rw [Set.indicator_of_notMem (by simpa using hpos), if_neg (by linarith)]
        rw [one_div_mul_cancel (ne_of_gt hpos)]; norm_num
    -- apply `(1 - P)` to `v` through `toEuclideanCLM`.
    have hPv : Matrix.toEuclideanCLM (𝕜 := ℝ) P v = v := by
      have happly : Matrix.toEuclideanCLM (𝕜 := ℝ) ((1 : Matrix (Fin d) (Fin d) ℝ) - P) v
          = Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc h S * S) v := by rw [hkey]
      rw [map_sub, map_one] at happly
      have hright : Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc h S * S) v
          = Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc h S) (Matrix.toEuclideanCLM (𝕜 := ℝ) S v) := by
        rw [map_mul]; rfl
      rw [hright, hv, map_zero] at happly
      exact (sub_eq_zero.mp happly).symm
    exact ⟨v, hPv⟩

/-- **The pointwise spectral bridge.** The orthogonal-projection matrix onto the `n`-step cocycle
kernel `cocycleKerEuclid A T n x` equals the spectral `≤ 0` projector
`cfc (Set.indicator (Set.Iic 0) 1)` of the Gram matrix `(cocycle A T n x)ᵀ * (cocycle A T n x)`.

The CFC element `P = cfc (indicator (Iic 0) 1) S` is a self-adjoint idempotent, hence a
`IsStarProjection` of `EuclideanSpace ℝ (Fin d)` whose range is the cocycle kernel
(`range_toEuclideanCLM_kerProj` with `ker_toEuclideanCLM_cocycleGram`); a star projection is
the orthogonal projection onto its range (`isStarProjection_iff_eq_starProjection_range`), and
transporting back through the star-algebra equivalence `Matrix.toEuclideanCLM` recovers
`orthProjMatrix`. -/
theorem orthProjMatrix_cocycleKerEuclid_eq_spectralProjector
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    orthProjMatrix (cocycleKerEuclid A T n x)
      = cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (cocycleGram A T n x) := by
  set S := cocycleGram A T n x with hS
  set P := cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) S with hP
  -- `toEuclideanCLM P` is a star projection.
  have hidem : IsIdempotentElem (Matrix.toEuclideanCLM (𝕜 := ℝ) P) := by
    have := kerProj_idempotent A T n x
    unfold IsIdempotentElem at this ⊢
    rw [← map_mul, this]
  have hsa : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) P) := by
    have := kerProj_isSelfAdjoint A T n x
    rw [isSelfAdjoint_iff] at this ⊢
    rw [← map_star, this]
  have hstar : IsStarProjection (Matrix.toEuclideanCLM (𝕜 := ℝ) P) := ⟨hidem, hsa⟩
  -- a star projection equals the orthogonal projection onto its range.
  obtain ⟨_, hpeq⟩ := isStarProjection_iff_eq_starProjection_range.mp hstar
  -- the range is the cocycle kernel.
  have hrange : LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) P).toLinearMap
      = cocycleKerEuclid A T n x := by
    rw [range_toEuclideanCLM_kerProj A T n x, ker_toEuclideanCLM_cocycleGram A T n x]
  -- assemble: `toEuclideanCLM (orthProjMatrix K) = K.starProjection = toEuclideanCLM P`.
  have hcoe : Matrix.toEuclideanCLM (𝕜 := ℝ) (orthProjMatrix (cocycleKerEuclid A T n x))
      = (cocycleKerEuclid A T n x).starProjection := by
    rw [orthProjMatrix, StarAlgEquiv.apply_symm_apply]
  have hPeq : Matrix.toEuclideanCLM (𝕜 := ℝ) P
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (orthProjMatrix (cocycleKerEuclid A T n x)) := by
    rw [hcoe, hpeq, ← hrange]
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).injective hPeq.symm

/-- **Measurability of the finite-step cocycle-kernel projector.** For each fixed step `n`, the
orthogonal-projection matrix onto the `n`-step cocycle kernel `cocycleKerEuclid A T n x` is
measurable in `x`. By the spectral bridge `orthProjMatrix_cocycleKerEuclid_eq_spectralProjector` it
equals the spectral `≤ 0` projector `cfc (indicator (Iic 0) 1)` of the measurable, self-adjoint Gram
family `(cocycle A T n ·)ᵀ * (cocycle A T n ·)`, whose measurability is
`Oseledets.measurable_spectralProjector`.

This is the per-step analytic engine for the measurability of the bottom flag space of the singular
(non-invertible) Oseledets filtration (Quas, *Multiplicative Ergodic Theorems and Applications*,
2013, Theorem 2). -/
theorem measurable_orthProjMatrix_cocycleKer [MeasurableSpace X] [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T) (n : ℕ) :
    Measurable (fun x => orthProjMatrix (cocycleKerEuclid A T n x)) := by
  have heq : (fun x => orthProjMatrix (cocycleKerEuclid A T n x))
      = fun x => cfc (Set.indicator (Set.Iic 0) (1 : ℝ → ℝ)) (cocycleGram A T n x) := by
    funext x
    exact orthProjMatrix_cocycleKerEuclid_eq_spectralProjector A T n x
  rw [heq]
  exact measurable_spectralProjector 0 (fun x => cocycleGram A T n x)
    (measurable_cocycleGram hA hT n) (fun x => isSelfAdjoint_cocycleGram A T n x)

end Oseledets
