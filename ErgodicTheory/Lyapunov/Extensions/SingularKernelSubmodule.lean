/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import ErgodicTheory.Cocycle.Basic

/-!
# The collapsing-kernel submodule of a singular linear cocycle

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem
degenerates from a direct-sum decomposition to a **filtration**
`ℝ^d = V₁(ω) ⊃ V₂(ω) ⊃ ⋯ ⊃ V_k(ω) ⊃ {0}`, and the bottom space of that flag is the
*eventual kernel* — the directions the matrix products ultimately collapse. This file
records the finite-`n` building block of that bottom space: the **kernel submodule**
`ErgodicTheory.cocycleKer A T n x`, the set of vectors annihilated by the `n`-step cocycle.

The headline result is **kernel monotonicity along the orbit**: once a direction is
collapsed by the cocycle it stays collapsed, so the kernel can only grow as the cocycle
composes (`cocycleKer_le_add`). Together with the rank–nullity identity
`finrank (cocycleKer) = d - cocycleRank` (`finrank_cocycleKer`) this is the dimension
data of the bottom stratum of the singular filtration. The full measurable flag
`V₁(ω) ⊃ ⋯ ⊃ {0}` of the singular MET is *not* constructed here; see the module note
below for the precise remaining gap.

Literature source (impl-i6-flag): A. Quas, *Multiplicative Ergodic Theorems and
Applications* (lecture notes, Universidade de São Paulo, 2013), **Theorem 2** (Oseledets
theorem, non-invertible form; after Oseledec [12] and Raghunathan [13]). There the
non-invertible conclusion is the measurable filtration `ℝ^d = V₁(ω) ⊃ V₂(ω) ⊃ ⋯ ⊃
V_{k+1}(ω) = {0}` with `A_ω V_j(ω) ⊆ V_j(σ ω)`; the bottom `V_{k+1}(ω) = {0}` together
with the equivariance `A_ω V_j(ω) ⊆ V_j(σ ω)` is the abstraction the kernel submodule
of this file makes concrete at finite `n`.

## Main definitions

* `ErgodicTheory.cocycleKer`: the kernel `LinearMap.ker (cocycle A T n x).mulVecLin` of the
  `n`-step cocycle — the directions collapsed after `n` steps.

## Main results

* `ErgodicTheory.cocycleKer_zero`: `cocycleKer A T 0 x = ⊥` (the zero-step cocycle is the
  identity, with trivial kernel).
* `ErgodicTheory.cocycleKer_le_add`: **kernel monotonicity** —
  `cocycleKer A T n x ≤ cocycleKer A T (m + n) x`: collapsed directions stay collapsed,
  so the kernel only grows as the cocycle composes along the orbit.
* `ErgodicTheory.finrank_cocycleKer`: the rank–nullity identity
  `finrank (cocycleKer A T n x) = d - (cocycle A T n x).rank` — the kernel dimension is
  the corank of the `n`-step cocycle.

## Remaining gap toward the full singular filtration

This module supplies the *bottom* of the flag at finite time: a single monotone family
of kernel submodules with its dimension. The full Quas Theorem 2 conclusion additionally
requires (i) the singular-value exponents `λ₁ > ⋯ > λ_k` from the Kingman/exterior-power
machinery, (ii) the limiting slow spaces `V_j(ω) = lim_n (span of the smallest singular
vectors of `cocycle A T n x`) as a Cauchy sequence in the Grassmannian, and (iii) their
measurability and equivariance `A_ω V_j(ω) ⊆ V_j(σ ω)`. None of (i)–(iii) is formalized
here; only the algebraic kernel/corank data is.
-/

namespace ErgodicTheory

variable {X : Type*} {d : ℕ}

/-- The **kernel submodule of the `n`-step cocycle**: the directions in `ℝ^d` (here
`Fin d → ℝ`) collapsed to `0` by `cocycle A T n x`. In the non-invertible Oseledets
theorem (Quas, *Multiplicative Ergodic Theorems and Applications*, 2013, Theorem 2;
after Oseledec and Raghunathan) the eventual such kernel is the bottom of the singular
filtration flag `ℝ^d = V₁(ω) ⊃ ⋯ ⊃ {0}`. -/
noncomputable def cocycleKer (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) : Submodule ℝ (Fin d → ℝ) :=
  LinearMap.ker (cocycle A T n x).mulVecLin

/-- **Vector-level membership** in the cocycle kernel: `v` is collapsed iff the matrix-vector
product `A⁽ⁿ⁾(x) ·ᵥ v` vanishes. The bridge from the submodule to a usable pointwise condition. -/
theorem mem_cocycleKer {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {n : ℕ} {x : X}
    {v : Fin d → ℝ} : v ∈ cocycleKer A T n x ↔ (cocycle A T n x).mulVec v = 0 := by
  rw [cocycleKer, LinearMap.mem_ker, Matrix.mulVecLin_apply]

/-- The zero-step cocycle is the identity, so its kernel is trivial. -/
@[simp] theorem cocycleKer_zero (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    cocycleKer A T 0 x = ⊥ := by
  rw [cocycleKer, cocycle_zero, Matrix.mulVecLin_one, LinearMap.ker_id]

/-- **Kernel monotonicity along the orbit.** The kernel of the `n`-step cocycle is
contained in the kernel of the `(m + n)`-step cocycle: once a direction is collapsed by
`cocycle A T n x` it stays collapsed under the later block `cocycle A T m (T^[n] x)`, so
the kernel can only grow as the cocycle composes. This is the monotone bottom stratum of
the singular Oseledets filtration. -/
theorem cocycleKer_le_add (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (m n : ℕ)
    (x : X) :
    cocycleKer A T n x ≤ cocycleKer A T (m + n) x := by
  rw [cocycleKer, cocycleKer, cocycle_add, Matrix.mulVecLin_mul]
  exact LinearMap.ker_le_ker_comp _ _

/-- **Rank–nullity for the cocycle kernel.** The kernel dimension is the corank of the
`n`-step cocycle: `finrank (cocycleKer A T n x) = d - (cocycle A T n x).rank`. -/
theorem finrank_cocycleKer (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) :
    Module.finrank ℝ (cocycleKer A T n x) = d - (cocycle A T n x).rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (cocycle A T n x).mulVecLin
  rw [Module.finrank_fin_fun] at h
  have hrank : (cocycle A T n x).rank
      = Module.finrank ℝ (LinearMap.range (cocycle A T n x).mulVecLin) := rfl
  have hker : Module.finrank ℝ (cocycleKer A T n x)
      = Module.finrank ℝ (LinearMap.ker (cocycle A T n x).mulVecLin) := rfl
  rw [hker, hrank]
  omega

end ErgodicTheory
