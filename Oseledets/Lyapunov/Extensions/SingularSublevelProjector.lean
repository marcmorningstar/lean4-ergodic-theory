/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Extensions.SingularKernelProjector
import Oseledets.Lyapunov.ForwardMeasurable

/-!
# Measurability of the finite-step Gram sublevel spectral subspace

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem degenerates
from a direct-sum decomposition to a measurable **filtration**
`ℝ^d = V₁(ω) ⊇ ⋯ ⊇ V_{k+1}(ω) = {0}` (Quas, *Multiplicative Ergodic Theorems and Applications*,
Universidade de São Paulo lecture notes, 2013, **Theorem 2**; after Oseledec and Raghunathan). The
*intermediate* slow spaces `V_j(ω)` are the spans of the singular directions whose singular value
lies below the `j`-th gap, i.e. the spectral subspaces of the cocycle **Gram** matrix
`(cocycle A T n x)ᵀ (cocycle A T n x)` corresponding to eigenvalues `≤ t` for the appropriate
threshold `t = (gap)²`. This file delivers, for each *fixed step* `n` and *arbitrary* threshold
`t ≥ 0`, a measurable choice of that finite-step approximant — the direct generalization of the
bottom kernel stratum (`Oseledets.cocycleKerEuclid`, threshold `0`) to an arbitrary sublevel `t`.

## Strategy

The construction reuses the entire `SingularKernelProjector.lean` engine verbatim, replacing the
threshold `0` by a free parameter `t`: the Gram matrix `cocycleGram A T n x` is unchanged, and the
spectral projector `cfc (Set.indicator (Set.Iic t) 1)` onto its `≤ t` eigenspace is again a
self-adjoint idempotent — because the `{0,1}`-valued indicator squares to itself on the (finite)
spectrum (`indicator_mul_self`), and `cfc` is multiplicative (`idempotent_cfc_indicator`) and
preserves self-adjointness (`isSelfAdjoint_cfc_indicator`). None of these facts uses positivity of
`t`. Its measurability in `x` is exactly `Oseledets.measurable_spectralProjector` for the
measurable, self-adjoint Gram family (`measurable_cocycleGram`, `cocycleGram_isHermitian`), and the
range-subspace measurability follows from the projector/range bridge
`Oseledets.measurableSubspace_range_of_measurable` — precisely the pattern of `vslow`.

## Main definitions

* `Oseledets.cocycleSublevelEuclid`: the `n`-step Gram sublevel spectral subspace at threshold `t`,
  i.e. the range of the spectral `≤ t` projector `cfc (Set.indicator (Set.Iic t) 1) (Gram)`,
  transported to a subspace of `EuclideanSpace ℝ (Fin d)`. At `t = 0` this is the cocycle kernel.

## Main results

* `Oseledets.measurableSubspace_cocycleSublevelEuclid`: for each fixed `n` and threshold `t`, the
  family `x ↦ cocycleSublevelEuclid A T n t x` is a `MeasurableSubspace`.

## gap

The threshold `t` is here a **free parameter**: it is not yet identified with a concrete
Lyapunov/singular-value gap of the cocycle. Pinning `t` to the `j`-th spectral gap requires the
exterior-power exponents from the Kingman subadditive machinery (the singular-value asymptotics),
which is *not* in this module. Likewise the monotone limit in `n` — the analogue of
`Oseledets.eventualKer` for the bottom stratum that assembles the genuine, `n`-independent flag
space `V_j(ω)` — is deferred to a follow-up; this module supplies only the per-step, per-threshold
measurable approximant.
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- The **`n`-step Gram sublevel spectral subspace** at threshold `t`: the range of the spectral
`≤ t` projector `cfc (Set.indicator (Set.Iic t) 1)` of the cocycle Gram matrix
`(cocycle A T n x)ᵀ (cocycle A T n x)`, transported to a subspace of `EuclideanSpace ℝ (Fin d)`.

It is the span of the singular directions of `cocycle A T n x` whose squared singular value is `≤ t`
— the finite-step approximant of an intermediate slow space `V_j(ω)` of the singular Oseledets flag
(Quas, *Multiplicative Ergodic Theorems and Applications*, 2013, Theorem 2). At `t = 0` it is the
cocycle kernel `cocycleKerEuclid A T n x`. -/
noncomputable def cocycleSublevelEuclid (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (t : ℝ) (x : X) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ)
    (cfc (Set.indicator (Set.Iic t) (1 : ℝ → ℝ)) (cocycleGram A T n x))).toLinearMap

/-- The threshold-`t` indicator `Set.indicator (Set.Iic t) 1` is `{0,1}`-valued, hence idempotent:
it equals its own square everywhere (in particular on the spectrum). This is the threshold-agnostic
generalization of the `t = 0` fact used for the kernel stratum. -/
private theorem indicator_mul_self (t : ℝ) :
    (fun s : ℝ => Set.indicator (Set.Iic t) (1 : ℝ → ℝ) s
        * Set.indicator (Set.Iic t) 1 s)
      = Set.indicator (Set.Iic t) (1 : ℝ → ℝ) := by
  funext s
  by_cases hs : s ∈ Set.Iic t
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

/-- The spectral `≤ t` projector `P = cfc (Set.indicator (Set.Iic t) 1) (Gram)` is idempotent:
`P * P = P`, because the indicator squares to itself on the (finite) spectrum and `cfc` is
multiplicative. (Threshold-agnostic generalization of `kerProj_idempotent`.) -/
private theorem idempotent_cfc_indicator (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (t : ℝ) (x : X) :
    IsIdempotentElem
      (cfc (Set.indicator (Set.Iic t) (1 : ℝ → ℝ)) (cocycleGram A T n x)) := by
  have hfin := (cocycleGram A T n x).finite_real_spectrum
  have hcont : ContinuousOn (Set.indicator (Set.Iic t) (1 : ℝ → ℝ))
      (spectrum ℝ (cocycleGram A T n x)) := hfin.continuousOn _
  unfold IsIdempotentElem
  rw [← cfc_mul _ _ _ hcont hcont, indicator_mul_self]

/-- The spectral `≤ t` projector `P = cfc (Set.indicator (Set.Iic t) 1) (Gram)` is self-adjoint (the
CFC of a real-valued function of a self-adjoint matrix is self-adjoint). (Threshold-agnostic
generalization of `kerProj_isSelfAdjoint`.) -/
private theorem isSelfAdjoint_cfc_indicator (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (t : ℝ) (x : X) :
    IsSelfAdjoint (cfc (Set.indicator (Set.Iic t) (1 : ℝ → ℝ)) (cocycleGram A T n x)) :=
  cfc_predicate _ _

/-- **Measurability of the `n`-step Gram sublevel spectral subspace.** For each fixed step `n` and
threshold `t`, the family `x ↦ cocycleSublevelEuclid A T n t x` is a `MeasurableSubspace`.

The defining matrix `cfc (Set.indicator (Set.Iic t) 1) (cocycleGram A T n x)` is, for every `x`, a
self-adjoint idempotent (`isSelfAdjoint_cfc_indicator`, `idempotent_cfc_indicator`), and it is
measurable in `x` by `Oseledets.measurable_spectralProjector` applied to the measurable,
self-adjoint Gram family (`measurable_cocycleGram`, `cocycleGram_isHermitian`). The projector/range
bridge
`Oseledets.measurableSubspace_range_of_measurable` then makes the range subspaces measurable —
exactly the `vslow` pattern.

This is the per-step, per-threshold analytic engine for the measurability of an intermediate slow
space of the singular (non-invertible) Oseledets filtration (Quas, *Multiplicative Ergodic Theorems
and Applications*, 2013, Theorem 2). -/
theorem measurableSubspace_cocycleSublevelEuclid [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T) (n : ℕ)
    (t : ℝ) :
    MeasurableSubspace (fun x => cocycleSublevelEuclid A T n t x) := by
  have hmeas : Measurable
      (fun x => cfc (Set.indicator (Set.Iic t) (1 : ℝ → ℝ)) (cocycleGram A T n x)) :=
    measurable_spectralProjector t (fun x => cocycleGram A T n x)
      (measurable_cocycleGram hA hT n) (fun x => cocycleGram_isHermitian A T n x)
  exact measurableSubspace_range_of_measurable
    (fun x => cfc (Set.indicator (Set.Iic t) (1 : ℝ → ℝ)) (cocycleGram A T n x)) hmeas
    (fun x => isSelfAdjoint_cfc_indicator A T n t x)
    (fun x => (idempotent_cfc_indicator A T n t x))

end Oseledets
