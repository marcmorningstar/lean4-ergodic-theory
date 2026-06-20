/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Oseledets.Cocycle.Basic
import Oseledets.Lyapunov.Extensions.SingularEventualKernel

/-!
# The measurable graph of the eventual-kernel family of a singular cocycle

For a non-invertible (singular) cocycle the Oseledets multiplicative ergodic theorem
degenerates from a direct-sum decomposition to a **filtration**
`ℝ^d = V₁(ω) ⊃ V₂(ω) ⊃ ⋯ ⊃ V_k(ω) ⊃ {0}` whose bottom space is the *eventual kernel*
`eventualKer A T x = ⨆ n, cocycleKer A T n x` — the directions the matrix products
ultimately collapse. Constructing the *measurable* singular flag requires, by the
Kuratowski–Ryll-Nardzewski measurable-selection theorem, that the set-valued map
`x ↦ eventualKer A T x` have a **measurable graph**: the set
`{(x, v) | v ∈ eventualKer A T x}` must be measurable in `X × (Fin d → ℝ)`. This file
delivers exactly that prerequisite.

The bridge is the **directed-union characterization** `mem_eventualKer`: because the
finite-step kernels `cocycleKer A T n x` are monotone in `n` (`cocycleKer_mono`), their
supremum is their union, so `v ∈ eventualKer A T x` iff *some* finite step `n` already
collapses `v`, i.e. `(cocycle A T n x) *ᵥ v = 0`. The graph is then the countable union
over `n : ℕ` of the per-step graphs `{(x, v) | (cocycle A T n x) *ᵥ v = 0}`, each of which
is measurable: `(x, v) ↦ (cocycle A T n x) *ᵥ v` is measurable (a finite sum of products
of the measurable cocycle entries with the coordinates of `v`) and `{· = 0}` is a
measurable (closed) condition. A countable union of measurable sets is measurable, giving
`measurableSet_graph_eventualKer`. Sectioning the graph at a fixed `v` gives
`measurableSet_mem_eventualKer`, the measurability of `{x | v ∈ eventualKer A T x}`.

Literature source (impl-i6-mgraph): A. Quas, *Multiplicative Ergodic Theorems and
Applications* (lecture notes, Universidade de São Paulo, 2013), **Theorem 2** (Oseledets
theorem, non-invertible form; after Oseledec [12] and Raghunathan [13]), whose measurable
filtration `ℝ^d = V₁(ω) ⊃ ⋯ ⊃ V_{k+1}(ω) = {0}` demands a measurable choice of each flag
space; the measurable graph proved here is the standard first step toward such a selection.

## Main results

* `Oseledets.mem_eventualKer`: the **directed-union characterization** —
  `v ∈ eventualKer A T x ↔ ∃ n, (cocycle A T n x) *ᵥ v = 0` (via `mem_iSup_of_directed`
  on the monotone step-kernel chain and `mem_cocycleKer`).
* `Oseledets.measurable_cocycleMulVec`: the map
  `(x, v) ↦ (cocycle A T n x) *ᵥ v` is measurable on `X × (Fin d → ℝ)`.
* `Oseledets.measurableSet_graph_cocycleKer`: each per-step graph
  `{(x, v) | (cocycle A T n x) *ᵥ v = 0}` is measurable.
* `Oseledets.measurableSet_graph_eventualKer`: the **measurable graph of the
  eventual-kernel family** `{(x, v) | v ∈ eventualKer A T x}` (a countable union of the
  per-step graphs).
* `Oseledets.measurableSet_mem_eventualKer`: for a fixed `v`, the section
  `{x | v ∈ eventualKer A T x}` is measurable.

## Remaining gap toward the measurable equivariant flag

This module supplies the **measurable graph** of the bottom flag space `x ↦ eventualKer
A T x`. Converting a measurable graph into a *measurable subspace map* — `x ↦ eventualKer
A T x` measurable into the Grassmannian `Gr(ℝ^d)` (Borel σ-algebra of the gap/Hausdorff
metric on subspaces) — is the content of the **Kuratowski–Ryll-Nardzewski measurable
selection theorem** (a measurable graph with closed sections in a Polish space admits a
measurable selector; iterating selects a measurable basis, hence a measurable subspace
map). That selection theorem, and the measurability of the *intermediate* slow spaces
`V_j(ω)` (Cauchy limits in the Grassmannian of spans of the smallest singular vectors of
`cocycle A T n x`) together with their exponents `λ₁ > ⋯ > λ_k` from the
Kingman/exterior-power machinery, are **not** formalized here; only the measurable graph
of the bottom (kernel) stratum is. Mathlib does not yet provide
Kuratowski–Ryll-Nardzewski for subspace-valued maps, so this is the precise next gap.
-/

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- **Directed-union characterization of the eventual kernel.** A vector `v` lies in the
eventual kernel `eventualKer A T x = ⨆ n, cocycleKer A T n x` iff *some* finite step `n`
already collapses it: `(cocycle A T n x) *ᵥ v = 0`. Because the step-kernel family is
monotone (`cocycleKer_mono`), hence directed, the supremum is the union of the steps
(`Submodule.mem_iSup_of_directed`), and membership in the `n`-th step unfolds to the
matrix-vector equation by `mem_cocycleKer`. This is the bridge from the `iSup` submodule
to a countable existential over a closed/measurable condition. -/
theorem mem_eventualKer {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {x : X}
    {v : Fin d → ℝ} :
    v ∈ eventualKer A T x ↔ ∃ n, (cocycle A T n x).mulVec v = 0 := by
  rw [eventualKer, Submodule.mem_iSup_of_directed _ (cocycleKer_mono A T x).directed_le]
  exact exists_congr fun n => mem_cocycleKer

/-- The matrix-vector product map `(x, v) ↦ (cocycle A T n x) *ᵥ v` is **measurable** on
the product space `X × (Fin d → ℝ)`. Coordinate `i` of the product is the finite sum
`∑ j, cocycle A T n x i j * v j`; each summand multiplies a measurable cocycle entry
(`measurable_cocycle` composed with the matrix-entry projections) with a measurable
coordinate `v j`, and a finite sum of measurable real functions is measurable. -/
theorem measurable_cocycleMulVec [MeasurableSpace X] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : Measurable A) {T : X → X} (hT : Measurable T) (n : ℕ) :
    Measurable (fun p : X × (Fin d → ℝ) => (cocycle A T n p.1).mulVec p.2) := by
  have hcoc : Measurable (fun x => cocycle A T n x) := measurable_cocycle hA hT n
  have hentry : ∀ i j : Fin d, Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) :=
    fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i)
  refine measurable_pi_iff.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (((hentry i j).comp hcoc).comp measurable_fst).mul
    ((measurable_pi_apply j).comp measurable_snd)

/-- Each **per-step kernel graph** `{(x, v) | (cocycle A T n x) *ᵥ v = 0}` is a measurable
subset of `X × (Fin d → ℝ)`: the preimage of `{0}` under the measurable map
`(x, v) ↦ (cocycle A T n x) *ᵥ v` (`measurable_cocycleMulVec`); `Fin d → ℝ` is a standard
Borel space, so the diagonal — equivalently `{· = 0}` — is measurable. -/
theorem measurableSet_graph_cocycleKer [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T)
    (n : ℕ) :
    MeasurableSet {p : X × (Fin d → ℝ) | (cocycle A T n p.1).mulVec p.2 = 0} :=
  measurableSet_eq_fun (measurable_cocycleMulVec hA hT n) measurable_const

/-- **The measurable graph of the eventual-kernel family.** The set
`{(x, v) | v ∈ eventualKer A T x}` is a measurable subset of `X × (Fin d → ℝ)`. By the
directed-union characterization `mem_eventualKer` it equals the countable union over
`n : ℕ` of the per-step graphs `{(x, v) | (cocycle A T n x) *ᵥ v = 0}`, each measurable by
`measurableSet_graph_cocycleKer`; a countable union of measurable sets is measurable. This
is the Kuratowski–Ryll-Nardzewski prerequisite for a measurable selection of the kernel
subspace — the first rigorous step toward a Grassmannian-measurable singular flag. -/
theorem measurableSet_graph_eventualKer [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T) :
    MeasurableSet {p : X × (Fin d → ℝ) | p.2 ∈ eventualKer A T p.1} := by
  have hset : {p : X × (Fin d → ℝ) | p.2 ∈ eventualKer A T p.1}
      = ⋃ n, {p : X × (Fin d → ℝ) | (cocycle A T n p.1).mulVec p.2 = 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact mem_eventualKer
  rw [hset]
  exact MeasurableSet.iUnion fun n => measurableSet_graph_cocycleKer hA hT n

/-- **Measurability of the eventual-kernel section at a fixed vector.** For each fixed
`v : Fin d → ℝ`, the set `{x | v ∈ eventualKer A T x}` is measurable. It is the section at
`v` of the measurable graph `measurableSet_graph_eventualKer`; equivalently, by
`mem_eventualKer`, the countable union over `n` of the measurable level sets
`{x | (cocycle A T n x) *ᵥ v = 0}`. -/
theorem measurableSet_mem_eventualKer [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T)
    (v : Fin d → ℝ) :
    MeasurableSet {x : X | v ∈ eventualKer A T x} := by
  have hset : {x : X | v ∈ eventualKer A T x}
      = ⋃ n, {x : X | (cocycle A T n x).mulVec v = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact mem_eventualKer
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  have hmeas : Measurable (fun x => (cocycle A T n x).mulVec v) :=
    (measurable_cocycleMulVec hA hT n).comp (measurable_id.prodMk measurable_const)
  exact measurableSet_eq_fun hmeas measurable_const

end Oseledets
