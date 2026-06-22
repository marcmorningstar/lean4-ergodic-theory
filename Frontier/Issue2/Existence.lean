/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue2.Framing
import Frontier.Issue2.MFDerivMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Existence of a measurable framing — the WALL of issue #2

`Frontier/Issue2/Framing.lean` proves, sorry-free, that **given** a `MeasurableFraming` (a
measurable trivialization of the tangent bundle), the manifold derivative cocycle becomes a
genuine measurable matrix cocycle and feeds the matrix Oseledets theorem. This file addresses the
remaining content: **constructing** such a framing on a smooth finite-dimensional second-countable
manifold. This is the genuine wall of issue #2.

## The mathematical fact (Filip, *Notes on the MET*, §2.2.2)

> "Any vector bundle [over a standard Borel base] can be **measurably trivialized**, i.e. it is
> measurably isomorphic to `Ω × ℝⁿ`."

The constructive proof, specialised to the tangent bundle of a manifold:

1. A σ-compact (hence second-countable) finite-dimensional manifold admits a **countable atlas**
   `(cₖ)ₖ` whose chart sources cover `M`.
2. **Disjointify** the open chart-source cover into a countable **measurable partition** `(Pₖ)`,
   `Pₖ ⊆ (chartAt H xₖ).source`, `⋃ Pₖ = M` (`Set.disjointed`, `iUnion_disjointed`; each `Pₖ`
   Borel since charts are open).
3. On each `Pₖ` the tangent-bundle trivialization `trivializationAt E (TangentSpace I) xₖ` provides
   a **continuous** family of linear frames `Trivialization.continuousLinearEquivAt`. Selecting,
   for each `x`, the frame of the unique block `Pₖ ∋ x`, glues a single **global** frame
   `frame : (x : M) → TangentSpace I x ≃L[ℝ] E`.
4. The conjugated derivative `framedGenerator` is measurable, because on each block `Pₖ` it
   coincides with the **chart-coordinate representation** of the derivative
   (`inTangentCoordinates I I T T (mfderiv I I T)`), *continuous on the chart neighbourhood* by
   `ContMDiffAt.mfderiv_const` (with `m = 0`); a function continuous (hence measurable) on each
   block of a countable measurable partition is measurable.

## What is delivered here, and what is the BLOCKED leaf

* `measurable_of_measurable_on_countable_cover` — the **measure-theory glue**, step 4's tail:
  a function measurable on each block of a countable measurable cover is measurable. Proved
  sorry-free via `Set.liftCover` and `measurable_liftCover`.
* `MeasurableFraming.of_measurablePartitionFrame` — the **honest reduction**: a global frame
  whose conjugated derivative is measurable on each block of a countable measurable partition
  assembles into a `MeasurableFraming`. Proved sorry-free (it is `of_measurable_on_countable_cover`
  applied to the conjugated derivative). This isolates exactly the analytic input still owed: the
  *per-block measurability* hypothesis `hblock`.
* `exists_measurableFraming_of_sigmaCompact` — the **WALL**: existence of a framing on a σ-compact
  smooth manifold. A single BLOCKED leaf; see its docstring for the two precise missing pieces.

## What is missing in Mathlib (verified by exhaustive grep over `Mathlib/Geometry/Manifold/`)

* **No** measurability result for `mfderiv`/`tangentMap`; **no** measurable bundle trivialization or
  measurable frame field (only the *continuous*/*smooth* `Trivialization` and *smooth*
  `IsLocalFrameOn`). The per-block continuity of the conjugated derivative is a genuine theorem —
  `ContMDiffAt.mfderiv_const` (`Mathlib.Geometry.Manifold.ContMDiffMFDeriv`, `m = 0`) — but that
  module's import chain is absent from the precompiled Mathlib cache in this environment, so wiring
  it forces a multi-hour from-source rebuild. It is therefore the named obligation `hblock`, not
  faked.
-/

open Filter Topology Function Set MeasureTheory
open scoped Manifold

namespace Frontier.Issue2

/-! ### Measure-theory glue: measurable on a countable measurable cover ⇒ measurable -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **A function measurable on each block of a countable measurable cover is measurable.** This is
the tail of the measurable-trivialization argument (gluing the per-chart continuous frames into one
global measurable frame). Proved sorry-free: `g` equals its own `Set.liftCover` over the cover, and
`measurable_liftCover` glues the per-block measurable restrictions. -/
theorem measurable_of_measurable_on_countable_cover {ι : Type*} [Countable ι]
    (t : ι → Set α) (htm : ∀ i, MeasurableSet (t i)) (htU : ⋃ i, t i = univ)
    {g : α → β} (hg : ∀ i, Measurable ((t i).restrict g)) :
    Measurable g := by
  have hcover :
      g = Set.liftCover t (fun i => (t i).restrict g)
        (fun _ _ _ _ _ => rfl) htU := by
    funext x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ t i := by
      have : x ∈ ⋃ i, t i := htU ▸ mem_univ x
      simpa using this
    rw [Set.liftCover_of_mem hi]
    rfl
  rw [hcover]
  exact measurable_liftCover t htm (fun i => (t i).restrict g) hg (fun _ _ _ _ _ => rfl) htU

/-! ### The reduction: a measurable partition + per-block measurable frames give a framing -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Assembly lemma (the honest reduction).** Given a global frame
`frame : (x : M) → TangentSpace I x ≃L[ℝ] E` and a countable measurable cover `(P k)` of `M` such
that the conjugated derivative `x ↦ frame (T x) ∘L mfderiv I I T x ∘L (frame x).symm` is measurable
on each block `P k`, the frame assembles into a `MeasurableFraming I T`.

Proved sorry-free via `measurable_of_measurable_on_countable_cover`. This isolates exactly the
analytic input still owed (`hblock`), which is supplied — on a smooth manifold — by the
chart-coordinate continuity of `mfderiv` (`ContMDiffAt.mfderiv_const`; see the module docstring). -/
def MeasurableFraming.of_measurablePartitionFrame {T : M → M}
    (P : ℕ → Set M) (hPmeas : ∀ k, MeasurableSet (P k)) (hPcover : ⋃ k, P k = univ)
    (frame : (x : M) → TangentSpace I x ≃L[ℝ] E)
    (hblock : ∀ k,
      Measurable ((P k).restrict fun x : M =>
        (frame (T x) : TangentSpace I (T x) →L[ℝ] E).comp
          ((mfderiv I I T x).comp ((frame x).symm : E →L[ℝ] TangentSpace I x)))) :
    MeasurableFraming I T where
  frame := frame
  measurable_framedGenerator :=
    measurable_of_measurable_on_countable_cover P hPmeas hPcover hblock

/-! ### The wall: existence on a σ-compact smooth manifold

The feasibility analysis (`docs/research/frontier/issue2/FEASIBILITY-2026-06-22.md`, Strategy β)
showed that the original "disjointified-trivialization" plan in this file's docstring is a **red
herring** for Mathlib's tangent-bundle model: since `TangentSpace I x` is *definitionally* the model
space `E` for every `x`, one may take the **globally constant identity frame**
`frame x := ContinuousLinearEquiv.refl ℝ E`. The `MeasurableFraming` obligation then collapses
*verbatim* into measurability of `x ↦ mfderiv I I T x` — i.e. Leaf A
(`Frontier.Issue2.measurable_mfderiv_of_contMDiff_boundaryless`). No per-point bundle
trivialization, no chart-selector, no `Trivialization.continuousLinearEquivAt` are needed.

Because this file's `E` carries only `[NormedSpace ℝ E]` (not the inner-product / finite-dimensional
structure of `DerivativeCocycleManifold.lean`), the sharp analytic core is restated here in its
minimal context as `measurable_mfderiv_of_contMDiff_boundaryless'`. It is the *same* irreducible
measurability fact, with the same honest `[I.Boundaryless]` + `ContMDiff I I 1 T` + σ-compact
hypotheses; see the Leaf-A docstring for the residual moving-chart-index recovery gap. -/

/-- The manifold derivative `x ↦ mfderiv I I T x`, recorded with the homogeneous model-fibre type
`E →L[ℝ] E` (legitimate since `TangentSpace I x` is definitionally `E`). This packaging gives the
derivative a non-dependent codomain, so that `Measurable` makes sense; it mirrors
`Frontier.Issue2.bundleDerivativeCocycle` (kept local here, where `E` carries only `NormedSpace`). -/
noncomputable def mfderivModel (T : M → M) (x : M) : E →L[ℝ] E := mfderiv I I T x

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The sharp analytic core (issue #2 wall), restatement for the framing existence.**
Measurability of the manifold derivative `x ↦ mfderiv I I T x : E →L[ℝ] E` (`mfderivModel`) for a
`C¹` self-map `T` of a **boundaryless** σ-compact manifold with its Borel σ-algebra. Delegates to the
full chart-glue measurability `Frontier.Issue2.measurable_mfderivHom` (`mfderivModel T = mfderivHom I T`
by `rfl`); the only residual is the moving-trivialization-index coordinate-change continuity isolated
there. The honest hypothesis `[FiniteDimensional ℝ E]` (used to reduce operator-norm continuity of
the coordinate changes to pointwise continuity) is added here; it is automatic in the MET setting. -/
theorem measurable_mfderivModel_of_contMDiff_boundaryless
    [FiniteDimensional ℝ E]
    [I.Boundaryless]
    [SigmaCompactSpace M] [SecondCountableTopology H] {T : M → M}
    (hT : ContMDiff I I 1 T) :
    Measurable (mfderivModel (I := I) T) :=
  measurable_mfderivHom hT

/-- **Existence of a measurable framing on a σ-compact boundaryless C¹ manifold.**
For a `C¹`, σ-compact (hence second-countable) **boundaryless** manifold `M` with its Borel
σ-algebra, and any `ContMDiff I I 1` self-map `T`, the tangent bundle admits a `MeasurableFraming`.

**Strategy β (the report's collapse of this leaf into Leaf A).** Take the globally constant identity
frame `frame x := ContinuousLinearEquiv.refl ℝ E`, legitimate because `TangentSpace I x` is
*definitionally* `E`. The conjugated derivative `frame (T x) ∘L mfderiv I I T x ∘L (frame x).symm`
is then *definitionally* `mfderivModel T x = mfderiv I I T x`, so the framing's measurability
obligation is exactly measurability of `x ↦ mfderiv I I T x` — supplied by the sharp core
`measurable_mfderivModel_of_contMDiff_boundaryless`. The disjointified-atlas / trivialization
machinery in the old plan is unnecessary. -/
theorem exists_measurableFraming_of_sigmaCompact
    [FiniteDimensional ℝ E]
    [I.Boundaryless]
    [SigmaCompactSpace M] [SecondCountableTopology H]
    {T : M → M} (hT : ContMDiff I I 1 T) :
    Nonempty (MeasurableFraming I T) :=
  ⟨{ frame := fun _ => ContinuousLinearEquiv.refl ℝ E
     measurable_framedGenerator := by
       -- the conjugated derivative with the constant identity frame is `mfderiv` itself
       -- (`id ∘L mfderiv ∘L id` is definitionally `mfderiv`), i.e. `mfderivModel T`.
       show Measurable (mfderivModel (I := I) T)
       exact measurable_mfderivModel_of_contMDiff_boundaryless (I := I) hT }⟩

end Frontier.Issue2
