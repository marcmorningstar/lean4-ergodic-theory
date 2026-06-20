/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Extensions.SingularSublevelProjector

/-!
# The threshold-`t` Gram sublevel family as a measurable building block of the singular flag

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem degenerates
from a direct-sum decomposition to a measurable **filtration**
`ℝ^d = V₁(ω) ⊇ ⋯ ⊇ V_{k+1}(ω) = {0}` (Quas, *Multiplicative Ergodic Theorems and Applications*,
Universidade de São Paulo lecture notes, 2013, **Theorem 2**; after Oseledec and Raghunathan). The
*intermediate* slow spaces `V_j(ω)` are the spans of the singular directions whose squared singular
value lies below the `j`-th gap `t = (gap)²`, i.e. the spectral subspaces of the cocycle Gram matrix
`(cocycle A T n x)ᵀ (cocycle A T n x)` with eigenvalues `≤ t`.

`Oseledets.Lyapunov.Extensions.SingularSublevelProjector` (module 1) built, for each fixed step `n`
and threshold `t ≥ 0`, a measurable choice of that finite-step approximant — the spectral `≤ t`
subspace `cocycleSublevelEuclid A T n t x`, the generalization of the bottom kernel stratum
(threshold `0`) to an arbitrary sublevel `t`. This file is the threshold-`t` analogue of the
*eventual* (stabilized, `n → ∞`) step taken for the kernel stratum in
`Oseledets.Lyapunov.Extensions.SingularEventualKernelProjector`
(`measurable_orthProjMatrix_eventualKer`).

## Strategy and honest scope

The eventual kernel-stratum projector measurability of `SingularEventualKernelProjector.lean` rests
on **monotonicity in `n`**: the bottom sublevel `Set.Iic 0`, i.e. the kernel
`cocycleKerEuclid A T n x`, *grows* with `n` (`cocycleKerEuclid_mono`) because more directions
collapse as the cocycle composes, and a monotone family of subspaces has a clean per-vector
star-projection limit `Submodule.starProjection_tendsto_closure_iSup`
(`tendsto_starProjection_cocycleKerEuclid`), whose pointwise-in-`x` limit of the measurable
finite-step projectors is measurable (`measurable_of_tendsto_metrizable`).

For a **fixed positive threshold `t`** this monotone-limit argument does **not** transfer: the
sublevel space `{ squared singular value ≤ t }` of the composed cocycle `cocycle A T n x` is *not*
in general monotone in `n`. Composing one more step rescales the singular values (the singular
values of `cocycle A T (n+1) x = cocycle A T n (T x) · A x` are not nested between those of
`cocycle A T n x`), so a direction can enter or leave the fixed `≤ t` sublevel as `n` grows. Hence
neither `cocycleSublevelEuclid_mono` nor `Submodule.starProjection_tendsto_closure_iSup` is
available, and the clean stabilized `n → ∞` limit is **not** constructed here (see `## gap`).

The tractable, honestly-scoped deliverable is therefore the **`n`-indexed measurable family** only:
this file re-exports module 1's per-fixed-`n`, per-threshold measurability under the descriptive
name `measurableSubspace_cocycleSublevel` so it sits in the singular flag's API alongside the
kernel-stratum modules, and records the obstruction to the eventual limit (and to per-fixed-`n`
equivariance) explicitly.

## Main results

* `Oseledets.measurableSubspace_cocycleSublevel`: for each fixed step `n` and threshold `t`, the
  threshold-`t` Gram sublevel family `x ↦ cocycleSublevelEuclid A T n t x` is a `MeasurableSubspace`
  — the per-step, per-threshold measurable building block of an intermediate slow space `V_j(ω)` of
  the singular Oseledets filtration (Quas, 2013, Theorem 2). This is a re-export of
  `measurableSubspace_cocycleSublevelEuclid`.

## gap

The genuine **stabilized eventual sublevel space** at a fixed positive threshold `t` — the `n → ∞`
analogue of `Oseledets.eventualKerEuclid` and of `measurable_orthProjMatrix_eventualKer` — is
**not** built here, and is not buildable by the monotone-limit technique of
`SingularEventualKernelProjector.lean`. The obstruction is the **non-monotonicity** of the
fixed-`t` sublevel family in `n`: unlike the kernel sublevel `Set.Iic 0`
(`cocycleKerEuclid_mono`, `SingularEventualKernelProjector.lean`), the family
`n ↦ cocycleSublevelEuclid A T n t x` is not monotone for `t > 0`, because composing the cocycle
rescales its singular values and so directions cross the fixed `≤ t` threshold in both directions.
The honest stabilized flag space `V_j(ω)` requires the **singular-value gap** that makes the family
*eventually* monotone — i.e. choosing the threshold `t` to lie strictly between the `j`-th and
`(j+1)`-th Lyapunov/singular-value exponents — and that identification is the
Kingman/exterior-power exponent asymptotics, which is not in this module.

The **per-fixed-`n` equivariance** `A x · cocycleSublevelEuclid A T (n+1) t x ⊆`
`cocycleSublevelEuclid A T n t (T x)` is likewise **omitted**: it is *not* purely algebraic for
`t > 0`. The kernel-stratum equivariance (`mapsTo_cocycleKer`, `SingularKernelEquivariant.lean`)
works only because membership in
the threshold-`0` sublevel is the algebraic condition `cocycle · v = 0`, preserved by left
multiplication (`0` maps to `0`). For `t > 0` the threshold is *not* covariant under `A x`: a
direction with squared singular value `≤ t` need not have its `A x`-image land in the `≤ t` sublevel
over `T x`, since `A x` rescales lengths and the threshold does not transform with it. So no
purely-algebraic `Set.MapsTo` holds, and asserting one would be false; it is therefore not stated.
-/

open MeasureTheory

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- **Measurability of the threshold-`t` Gram sublevel family (per fixed step `n`).** For each fixed
step `n` and threshold `t`, the family `x ↦ cocycleSublevelEuclid A T n t x` — the spectral `≤ t`
subspace of the cocycle Gram matrix `(cocycle A T n x)ᵀ (cocycle A T n x)`, transported to a
subspace of `EuclideanSpace ℝ (Fin d)` — is a `MeasurableSubspace`.

This is the per-step, per-threshold measurable building block of an intermediate slow space
`V_j(ω)` of the singular (non-invertible) Oseledets filtration (Quas, *Multiplicative Ergodic
Theorems and Applications*, 2013, Theorem 2), the threshold-`t` generalization of the bottom kernel
stratum. It is a re-export of `measurableSubspace_cocycleSublevelEuclid` (module 1,
`SingularSublevelProjector.lean`); the genuine stabilized `n → ∞` sublevel space at a fixed positive
threshold is *not* assembled — see this module's `## gap` for the non-monotonicity obstruction. -/
theorem measurableSubspace_cocycleSublevel [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T) (n : ℕ)
    (t : ℝ) :
    MeasurableSubspace (fun x => cocycleSublevelEuclid A T n t x) :=
  measurableSubspace_cocycleSublevelEuclid hA hT n t

end Oseledets
