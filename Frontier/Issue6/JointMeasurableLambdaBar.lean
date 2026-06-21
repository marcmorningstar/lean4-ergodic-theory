/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.GrowthFunction
import Oseledets.Lyapunov.Measurable
import Oseledets.Lyapunov.Extensions.SingularKernelMeasurableGraph
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Joint measurability of the upper Lyapunov growth function

The upper Lyapunov growth function
`lambdaBar A T x v = limsup_n (1/n) · log ‖A⁽ⁿ⁾(x) · v‖`
(`Oseledets.lambdaBar`, in `Oseledets.Lyapunov.GrowthFunction`) is known to be measurable in
the base point `x` for each *fixed* vector `v` (`Oseledets.measurable_lambdaBar_apply`). The
measurable singular forward Oseledets filtration, however, needs the **joint** measurability
in the pair `(x, v)`: the slow flag at `x` is the sublevel set `{v | lambdaBar A T x v ≤ c}`,
and measurable selection of that set-valued map requires its graph
`{(x, v) | lambdaBar A T x v ≤ c}` to be measurable in `X × EuclideanSpace ℝ (Fin d)`, which
follows at once from joint measurability of `lambdaBar`.

## Main result

* `Oseledets.jointMeasurable_lambdaBar`: the map
  `(x, v) ↦ lambdaBar A T x v` is measurable on `X × EuclideanSpace ℝ (Fin d)`, given a
  measurable cocycle generator `A` and a measurable base dynamics `T`.

## Proof outline

`lambdaBar A T x v` is the `limsup` over `n : ℕ` of the per-step summands
`s n (x, v) = (n : ℝ)⁻¹ · log ‖toEuclideanCLM (cocycle A T n x) v‖`.
By `Measurable.limsup` it suffices to show each `s n` is jointly measurable, and for that it
suffices to show `(x, v) ↦ ‖toEuclideanCLM (cocycle A T n x) v‖` is jointly measurable.

The bridge to the existing `Fin d → ℝ` infrastructure is the identity
`toEuclideanCLM M v = toLp 2 (M *ᵥ ofLp v)` (Mathlib's `Matrix.ofLp_toEuclideanCLM` together
with `WithLp.toLp_ofLp`). Therefore the norm factors as

`(x, v) ↦ (x, ofLp v) ↦ (cocycle A T n x) *ᵥ (ofLp v) ↦ toLp 2 (·) ↦ ‖·‖`,

where:
* `ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)` is continuous, hence measurable;
* `(x, w) ↦ (cocycle A T n x) *ᵥ w` is jointly measurable
  (`Oseledets.measurable_cocycleMulVec`);
* `toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)` and the norm are continuous.

Source: S. Filip, *Notes on the Multiplicative Ergodic Theorem* (arXiv:1710.10694), §2.3
(measurability of the Lyapunov data underlying the Oseledets filtration).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- **Joint measurability of the cocycle action norm.** For each fixed step `n`, the map
`(x, v) ↦ ‖toEuclideanCLM (cocycle A T n x) v‖` is measurable on
`X × EuclideanSpace ℝ (Fin d)`.

The action is rewritten through the `EuclideanSpace ≃ (Fin d → ℝ)` linear isometry: by
`Matrix.ofLp_toEuclideanCLM` and `WithLp.toLp_ofLp`,
`toEuclideanCLM M v = toLp 2 (M *ᵥ ofLp v)`, so the norm is the composition of the continuous
`ofLp`, the jointly measurable matrix-vector action `measurable_cocycleMulVec`, the continuous
`toLp`, and the continuous norm. -/
theorem measurable_norm_toEuclideanCLM_cocycle {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : Measurable A) {T : X → X} (hT : Measurable T) (n : ℕ) :
    Measurable (fun p : X × EuclideanSpace ℝ (Fin d) =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n p.1) p.2‖) := by
  -- Rewrite the action through `EuclideanSpace ≃ (Fin d → ℝ)`:
  -- `toEuclideanCLM M v = toLp 2 (M *ᵥ ofLp v)`.
  -- `toEuclideanCLM M v = toLp 2 (M *ᵥ ofLp v)` definitionally (`ofLp_toEuclideanCLM` and
  -- `toLp_ofLp` are both `rfl`), so the two presentations of the norm are the same function.
  have hrw : (fun p : X × EuclideanSpace ℝ (Fin d) =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n p.1) p.2‖)
      = fun p : X × EuclideanSpace ℝ (Fin d) =>
        ‖(WithLp.toLp 2 ((cocycle A T n p.1).mulVec (WithLp.ofLp p.2)) :
          EuclideanSpace ℝ (Fin d))‖ := rfl
  rw [hrw]
  -- `(x, v) ↦ (x, ofLp v)` is measurable (`ofLp` continuous on the Borel `EuclideanSpace`).
  have hofLp : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) :=
    (PiLp.continuous_ofLp 2 fun _ : Fin d => ℝ).measurable
  have hmap : Measurable (fun p : X × EuclideanSpace ℝ (Fin d) => (p.1, WithLp.ofLp p.2)) :=
    measurable_fst.prodMk (hofLp.comp measurable_snd)
  -- `(x, w) ↦ (cocycle A T n x) *ᵥ w` is jointly measurable.
  have hmulVec : Measurable (fun q : X × (Fin d → ℝ) => (cocycle A T n q.1).mulVec q.2) :=
    measurable_cocycleMulVec hA hT n
  -- Compose, then post-compose with the continuous `toLp` and the continuous norm.
  have htoLp : Continuous (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    PiLp.continuous_toLp 2 fun _ : Fin d => ℝ
  exact (continuous_norm.comp htoLp).measurable.comp (hmulVec.comp hmap)

/-- **Joint measurability of the upper Lyapunov growth function.** The map
`(x, v) ↦ lambdaBar A T x v` is measurable on `X × EuclideanSpace ℝ (Fin d)`, given a
measurable cocycle generator `A` and measurable base dynamics `T`.

`lambdaBar A T x v` is the `limsup_n` of the per-step summands
`(n : ℝ)⁻¹ · log ‖toEuclideanCLM (cocycle A T n x) v‖`; each summand is jointly measurable
(`measurable_norm_toEuclideanCLM_cocycle`, then `Real.log`, scaled by the constant `n⁻¹`),
and `Measurable.limsup` lifts the per-step measurability to the limsup. -/
theorem jointMeasurable_lambdaBar [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : Measurable A) {T : X → X} (hT : Measurable T) :
    Measurable (fun p : X × EuclideanSpace ℝ (Fin d) => lambdaBar A T p.1 p.2) := by
  -- `lambdaBar A T x v = limsup_n s n (x, v)` with
  -- `s n (x, v) = (n : ℝ)⁻¹ · log ‖toEuclideanCLM (cocycle A T n x) v‖`.
  refine Measurable.limsup (fun n => ?_)
  have hnorm : Measurable (fun p : X × EuclideanSpace ℝ (Fin d) =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n p.1) p.2‖) :=
    measurable_norm_toEuclideanCLM_cocycle hA hT n
  exact measurable_const.mul (Real.measurable_log.comp hnorm)

end Oseledets
