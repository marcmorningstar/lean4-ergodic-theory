/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Data.Matrix.Mul
import Oseledets.Lyapunov.Extensions.SingularEventualKernel

/-!
# Equivariance of the kernel stratum of a singular linear cocycle

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem
degenerates from a direct-sum decomposition to a **filtration**
`ℝ^d = V₁(ω) ⊃ V₂(ω) ⊃ ⋯ ⊃ V_k(ω) ⊃ {0}` whose defining property is **equivariance**:
`A_ω V_j(ω) ⊆ V_j(σ ω)` — the generator `A_ω` pushes each space of the flag forward along
the base dynamics. This file establishes that equivariance for the *bottom* stratum of the
flag, the collapsing kernel: the generator `A x` maps the `n`-step kernel
`cocycleKer A T (n+1) x` into the one-shorter kernel `cocycleKer A T n (T x)` over the
shifted base point, and consequently maps the eventual kernel `eventualKer A T x` into
`eventualKer A T (T x)`.

The mechanism is the cocycle decomposition `cocycle A T (n+1) x = cocycle A T n (T x) * A x`
(`cocycle_succ`): a vector collapsed by the `(n+1)`-step cocycle at `x` has its `A x`-image
collapsed by the `n`-step cocycle at `T x`. This is the matrix-level shadow of the
literature equivariance.

Literature source (impl-i6-equiv): A. Quas, *Multiplicative Ergodic Theorems and
Applications* (lecture notes, Universidade de São Paulo, 2013), **Theorem 2** (Oseledets
theorem, non-invertible form; after Oseledec [12] and Raghunathan [13]). There the
non-invertible conclusion is the measurable filtration
`ℝ^d = V₁(ω) ⊃ V₂(ω) ⊃ ⋯ ⊃ V_{k+1}(ω) = {0}` with equivariance `A_ω V_j(ω) ⊆ V_j(σ ω)`.
The bottom `V_{k+1}(ω) = {0}` is the stabilized kernel; its equivariance — `A_ω` mapping the
collapsing directions over `ω` to those over `σ ω` — is exactly what this file makes
concrete at finite `n` and in the stabilized limit (`eventualKer_equivariant`).

## Main results

* `Oseledets.cocycle_succ_mulVec`: the **kernel-shift identity**
  `(cocycle A T (n+1) x).mulVec v = (cocycle A T n (T x)).mulVec ((A x).mulVec v)` — the
  `(n+1)`-step action factors as the `A x` action followed by the `n`-step action at `T x`.
* `Oseledets.mapsTo_cocycleKer`: the **per-step equivariance** —
  `A x` maps `cocycleKer A T (n+1) x` into `cocycleKer A T n (T x)`.
* `Oseledets.eventualKer_equivariant`: the **headline equivariance of the kernel stratum**
  — `A x` maps `eventualKer A T x` into `eventualKer A T (T x)`.

## Remaining gap toward the measurable equivariant flag

This module supplies equivariance for the bottom stratum (the kernel) of the singular flag.
The full Quas Theorem 2 conclusion still requires, beyond this equivariance: (i) the
singular-value exponents `λ₁ > ⋯ > λ_k` from the Kingman/exterior-power machinery; (ii) the
intermediate slow spaces `V_j(ω)` as Cauchy limits in the Grassmannian of spans of the
smallest singular vectors of `cocycle A T n x`; and (iii) **measurability of the flag** —
`x ↦ V_j(x)` as a measurable map into the Grassmannian (the Borel σ-algebra of subspaces of
`ℝ^d` under the gap/Hausdorff metric, see Quas, *Detailed point* after Theorem 1). The
equivariance proved here is purely algebraic and pointwise in `x`; measurability of
`x ↦ eventualKer A T x` into the Grassmannian is the precise remaining gap and is not
addressed here.
-/

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- **Kernel-shift identity.** The `(n+1)`-step cocycle action factors as the generator
action `A x` followed by the `n`-step action over the shifted point `T x`:
`(cocycle A T (n+1) x).mulVec v = (cocycle A T n (T x)).mulVec ((A x).mulVec v)`. This is the
matrix-vector form of the cocycle decomposition `cocycle A T (n+1) x = cocycle A T n (T x) *
A x` (`cocycle_succ`), via `Matrix.mulVec_mulVec`. -/
theorem cocycle_succ_mulVec (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ)
    (x : X) (v : Fin d → ℝ) :
    (cocycle A T (n + 1) x).mulVec v
      = (cocycle A T n (T x)).mulVec ((A x).mulVec v) := by
  rw [cocycle_succ, ← Matrix.mulVec_mulVec]

/-- **Per-step equivariance of the kernel stratum.** The generator `A x` maps the
`(n+1)`-step kernel `cocycleKer A T (n+1) x` into the one-shorter kernel
`cocycleKer A T n (T x)` over the shifted base point `T x`: a direction collapsed by the
`(n+1)`-step cocycle at `x` has its `A x`-image collapsed by the `n`-step cocycle at `T x`.
This is the finite-`n` shadow of the Oseledets equivariance `A_ω V_j(ω) ⊆ V_j(σ ω)`
(Quas, Theorem 2). -/
theorem mapsTo_cocycleKer (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) :
    Set.MapsTo (A x).mulVec (cocycleKer A T (n + 1) x) (cocycleKer A T n (T x)) := by
  intro v hv
  rw [SetLike.mem_coe, mem_cocycleKer] at hv ⊢
  rw [← cocycle_succ_mulVec]
  exact hv

/-- **Headline equivariance of the kernel stratum.** The generator `A x` maps the eventual
kernel `eventualKer A T x` into the eventual kernel `eventualKer A T (T x)` over the shifted
base point: the directions the cocycle ultimately collapses over `x` are pushed forward by
`A x` to directions ultimately collapsed over `T x`. This is the equivariance
`A_ω V_j(ω) ⊆ V_j(σ ω)` of the bottom stratum of the singular Oseledets filtration (Quas,
*Multiplicative Ergodic Theorems and Applications*, 2013, Theorem 2; after Oseledec and
Raghunathan). -/
theorem eventualKer_equivariant (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Set.MapsTo (A x).mulVec (eventualKer A T x) (eventualKer A T (T x)) := by
  intro v hv
  rw [SetLike.mem_coe, eventualKer,
    Submodule.mem_iSup_of_directed _ (cocycleKer_mono A T x).directed_le] at hv
  obtain ⟨n, hn⟩ := hv
  have hn1 : v ∈ cocycleKer A T (n + 1) x := cocycleKer_mono A T x (Nat.le_succ n) hn
  have himg : (A x).mulVec v ∈ cocycleKer A T n (T x) :=
    mapsTo_cocycleKer A T n x hn1
  exact cocycleKer_le_eventualKer A T n (T x) himg

end Oseledets
