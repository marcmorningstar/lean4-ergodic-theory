/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import ErgodicTheory.Lyapunov.Extensions.SingularKernelSubmodule

/-!
# The eventual (stabilized) kernel of a singular linear cocycle

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem
degenerates from a direct-sum decomposition to a **filtration**
`ℝ^d = V₁(ω) ⊃ V₂(ω) ⊃ ⋯ ⊃ V_k(ω) ⊃ {0}`, whose bottom space `{0}` is the limit of the
directions the matrix products ultimately collapse. This file builds the **eventual
kernel** of the cocycle: the supremum (union) over all step counts `n` of the finite-`n`
kernel submodules `ErgodicTheory.cocycleKer A T n x`. Since the kernel family is monotone
(`cocycleKer_le_add`: once a direction is collapsed it stays collapsed), this supremum is
the *stabilized* bottom stratum of the singular Oseledets flag — the eventual kernel
`⨆ n, cocycleKer A T n x`.

Two facts are recorded: the kernel family is monotone in the step count
(`cocycleKer_mono`), and each finite-step kernel embeds in the eventual one
(`cocycleKer_le_eventualKer`). A crude dimension bound `finrank ≤ d`
(`finrank_eventualKer_le`) follows from the ambient finite dimension.

Literature source (impl-i6-evker): A. Quas, *Multiplicative Ergodic Theorems and
Applications* (lecture notes, Universidade de São Paulo, 2013), **Theorem 2** (Oseledets
theorem, non-invertible form; after Oseledec [12] and Raghunathan [13]). There the
non-invertible conclusion is the measurable filtration `ℝ^d = V₁(ω) ⊃ V₂(ω) ⊃ ⋯ ⊃
V_{k+1}(ω) = {0}` with `A_ω V_j(ω) ⊆ V_j(σ ω)`; the bottom `V_{k+1}(ω) = {0}` is the
stabilized kernel — the directions collapsed in the limit — which the eventual kernel of
this file makes concrete as the monotone supremum of the finite-`n` step kernels.

## Main definitions

* `ErgodicTheory.eventualKer`: the eventual kernel `⨆ n, cocycleKer A T n x`, the stabilized
  union of all step-kernels and the monotone-limit bottom of the singular filtration flag.

## Main results

* `ErgodicTheory.cocycleKer_mono`: the step-kernel family `fun n => cocycleKer A T n x` is
  monotone in the step count `n` (collapsed directions stay collapsed).
* `ErgodicTheory.cocycleKer_le_eventualKer`: each finite-step kernel `cocycleKer A T n x`
  sits inside the eventual kernel `eventualKer A T x`.
* `ErgodicTheory.finrank_eventualKer_le`: the eventual kernel has dimension at most `d`.

## Remaining gap toward the measurable equivariant flag

This module supplies the *stabilized bottom* `eventualKer A T x` of the flag as an
algebraic supremum at a fixed base point `x`. The full Quas Theorem 2 conclusion still
requires: (i) the singular-value exponents `λ₁ > ⋯ > λ_k` from the Kingman/exterior-power
machinery; (ii) the limiting slow spaces `V_j(ω)` as Cauchy limits in the Grassmannian of
spans of the smallest singular vectors of `cocycle A T n x`; (iii) measurability of
`x ↦ V_j(x)` and the equivariance `A_ω V_j(ω) ⊆ V_j(σ ω)`. In particular the eventual
kernel here is *not yet* shown to be equivariant (`A x` mapping `eventualKer A T x` into
`eventualKer A T (T x)`) nor measurable in `x`; only the per-base-point monotone-limit
algebra is formalized.
-/

namespace ErgodicTheory

variable {X : Type*} {d : ℕ}

/-- **Kernel monotonicity in the step count.** The step-kernel family
`fun n => cocycleKer A T n x` is monotone: as the cocycle composes along the orbit, once a
direction is collapsed it stays collapsed, so the kernel can only grow. Proved from the
one-step inclusion `cocycleKer A T n x ≤ cocycleKer A T (1 + n) x` (an instance of
`cocycleKer_le_add`). -/
theorem cocycleKer_mono (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Monotone (fun n => cocycleKer A T n x) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show cocycleKer A T n x ≤ cocycleKer A T (n + 1) x
  rw [Nat.add_comm n 1]
  exact cocycleKer_le_add A T 1 n x

/-- The **eventual kernel** of the cocycle at `x`: the supremum (union) over all step
counts `n` of the finite-step kernels `cocycleKer A T n x`. Because the step-kernel family
is monotone (`cocycleKer_mono`), in the finite-dimensional space `Fin d → ℝ` this supremum
stabilizes, and it is the bottom space `{0}` analogue — the directions the cocycle
ultimately collapses — of the singular Oseledets filtration flag `ℝ^d = V₁(ω) ⊃ ⋯ ⊃ {0}`
(Quas, *Multiplicative Ergodic Theorems and Applications*, 2013, Theorem 2; after Oseledec
and Raghunathan). -/
noncomputable def eventualKer (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Submodule ℝ (Fin d → ℝ) :=
  ⨆ n, cocycleKer A T n x

/-- Each finite-step kernel `cocycleKer A T n x` sits inside the eventual kernel
`eventualKer A T x`: the eventual kernel is the union of all step-kernels. -/
theorem cocycleKer_le_eventualKer (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) :
    cocycleKer A T n x ≤ eventualKer A T x :=
  le_iSup (fun k => cocycleKer A T k x) n

/-- The **eventual kernel has dimension at most `d`**: it is a submodule of the ambient
`d`-dimensional space `Fin d → ℝ`. -/
theorem finrank_eventualKer_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Module.finrank ℝ (eventualKer A T x) ≤ d := by
  have h := Submodule.finrank_le (eventualKer A T x)
  rwa [Module.finrank_fin_fun] at h

end ErgodicTheory
