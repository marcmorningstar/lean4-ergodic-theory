/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Data.Nat.Lattice
import Oseledets.Lyapunov.Extensions.SingularRankMinor

/-!
# Measurable dimension data of the singular Oseledets filtration

For the singular (non-invertible) multiplicative ergodic theorem the Oseledets
decomposition degenerates to a **measurable filtration**
`ℝ^d = V₁(x) ⊃ V₂(x) ⊃ ⋯ ⊃ {0}`, whose strata carry the dimension data — the
multiplicities `m_j` — of the flag (A. Quas, *Multiplicative Ergodic Theorems and
Applications*, lecture notes, Universidade de São Paulo, December 2013, Theorem 2 —
the non-invertible Oseledets theorem after Oseledec [12] and Raghunathan [13]). The
ranks `cocycleRank A T n x` of the matrix products are **antitone** in `n`
(`Oseledets.cocycleRank_add_le_right`: the rank cannot increase as the cocycle
composes along the orbit). Since `ℕ` is well-founded the infimum over `n` is
therefore *attained*: it is the **eventual** (stabilised) rank of the cocycle, and
`d` minus it is the **eventual-kernel dimension**, i.e. the multiplicity of the
kernel stratum of the singular flag (the bottom space `V_{k+1}(x)` collapses to `0`
exactly along the directions counted here).

`Oseledets.Lyapunov.Extensions.SingularRankMinor` supplied the per-step measurable
dimension function `measurable_cocycleRank`. This file **closes the eventual
dimension data**:

* `Oseledets.eventualRank A T x := ⨅ n, cocycleRank A T n x` — the stabilised rank;
* `Oseledets.measurable_eventualRank` — it is measurable (a countable infimum of the
  measurable `ℕ`-valued rank functions);
* `Oseledets.eventualKerDim A T x := d - eventualRank A T x` and
  `Oseledets.measurable_eventualKerDim` — the eventual-kernel dimension is measurable.

The route for the infimum is the `ℕ`-valued **level-set** characterisation: a
`ℕ`-valued function is measurable once each singleton fibre `{x | f x = k}` is
measurable (`measurable_to_countable'`), and each fibre is the difference
`{x | k ≤ f x} \ {x | k + 1 ≤ f x}` of the **lower** level sets. The infimum
distributes over `≤` from below — `k ≤ ⨅ n, cocycleRank A T n x ↔ ∀ n, k ≤ cocycleRank
A T n x` (`le_ciInf_iff'`, valid because `ℕ` is a `ConditionallyCompleteLinearOrderBot`)
— so `{x | k ≤ eventualRank A T x} = ⋂ n, {x | k ≤ cocycleRank A T n x}` is a countable
intersection of the measurable rank level sets coming from `measurable_cocycleRank`,
avoiding any `ENat` cast.

## Main definitions

* `Oseledets.eventualRank`: `⨅ n, cocycleRank A T n x`, the stabilised cocycle rank.
* `Oseledets.eventualKerDim`: `d - eventualRank A T x`, the eventual-kernel dimension.

## Main results

* `Oseledets.le_eventualRank_iff`: `k ≤ eventualRank A T x ↔ ∀ n, k ≤ cocycleRank A T n x`.
* `Oseledets.measurableSet_le_eventualRank`: `{x | k ≤ eventualRank A T x}` is measurable.
* `Oseledets.measurable_eventualRank`: `x ↦ eventualRank A T x` is measurable.
* `Oseledets.measurable_eventualKerDim`: `x ↦ eventualKerDim A T x` is measurable.
-/

open MeasureTheory

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-- The **eventual (stabilised) rank** of the cocycle: the infimum over `n` of the
per-step ranks `cocycleRank A T n x`. Because the ranks are antitone in `n`
(`cocycleRank_add_le_right`) and `ℕ` is well-founded this infimum is attained — it is
the rank that the matrix products eventually settle at. In the non-invertible
Oseledets theorem (Quas, *Multiplicative Ergodic Theorems and Applications*, 2013,
Theorem 2; after Oseledec and Raghunathan) this equals `d` minus the eventual-kernel
dimension, i.e. `d` minus the multiplicity of the kernel stratum of the singular
filtration. -/
noncomputable def eventualRank (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) : ℕ :=
  ⨅ n, cocycleRank A T n x

/-- The **eventual-kernel dimension** of the cocycle: `d` minus the eventual rank.
This is the multiplicity of the kernel stratum of the singular Oseledets filtration —
the number of directions eventually collapsed by the matrix products. -/
noncomputable def eventualKerDim (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) : ℕ :=
  d - eventualRank A T x

/-- **Lower level-set characterisation of the eventual rank.** Since the `ℕ`-infimum
distributes over `≤` from below (`le_ciInf_iff'`, valid because `ℕ` is a
`ConditionallyCompleteLinearOrderBot`), `k ≤ eventualRank A T x` holds iff every step
already has rank `≥ k`. -/
theorem le_eventualRank_iff (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) (k : ℕ) :
    k ≤ eventualRank A T x ↔ ∀ n, k ≤ cocycleRank A T n x := by
  rw [eventualRank]
  exact le_ciInf_iff'

/-- **The lower rank level set is measurable.** `{x | k ≤ eventualRank A T x}` equals the
countable intersection `⋂ n, {x | k ≤ cocycleRank A T n x}` of the measurable rank level
sets from `measurable_cocycleRank` (each `ℕ`-valued, hence every level set measurable). -/
theorem measurableSet_le_eventualRank [MeasurableSpace X] {k : ℕ}
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X}
    (hT : Measurable T) :
    MeasurableSet {x | k ≤ eventualRank A T x} := by
  have hset : {x | k ≤ eventualRank A T x}
      = ⋂ n, {x | k ≤ cocycleRank A T n x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact le_eventualRank_iff A T x k
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  exact (measurable_cocycleRank hA hT n) MeasurableSet.of_discrete

/-- **The eventual-rank dimension function is measurable.** The infimum over `n` of the
measurable `ℕ`-valued rank functions is measurable: a `ℕ`-valued function is measurable
once every singleton fibre `{x | f x = k}` is measurable (`measurable_to_countable'`),
and each fibre is the difference `{x | k ≤ f x} \ {x | k + 1 ≤ f x}` of the lower rank
level sets from `measurableSet_le_eventualRank`. This closes the measurable eventual
dimension datum of the singular filtration. -/
theorem measurable_eventualRank [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X}
    (hT : Measurable T) :
    Measurable (fun x => eventualRank A T x) := by
  refine measurable_to_countable' fun k => ?_
  have hfib : (fun x => eventualRank A T x) ⁻¹' {k}
      = {x | k ≤ eventualRank A T x} \ {x | k + 1 ≤ eventualRank A T x} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
    omega
  rw [hfib]
  exact (measurableSet_le_eventualRank hA hT).diff (measurableSet_le_eventualRank hA hT)

/-- **The eventual-kernel dimension function is measurable.** It is `(d - ·)` composed
with the measurable `eventualRank` (`measurable_eventualRank`); every map `ℕ → ℕ` is
measurable because `ℕ` carries the discrete (`⊤`) `MeasurableSpace`
(`measurable_from_top`). This closes the measurable dimension datum — the kernel-stratum
multiplicity — of the singular Oseledets filtration. -/
theorem measurable_eventualKerDim [MeasurableSpace X]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X}
    (hT : Measurable T) :
    Measurable (fun x => eventualKerDim A T x) :=
  measurable_from_top.comp (measurable_eventualRank hA hT)

end Oseledets
