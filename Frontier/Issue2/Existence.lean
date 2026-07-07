/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue2.Framing
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

/-! ### The wall: existence on a σ-compact smooth manifold -/

/-- **Existence of a measurable framing on a σ-compact smooth manifold (the WALL of issue #2).**
For a `C¹` finite-dimensional, σ-compact (hence second-countable) manifold `M` with its Borel
σ-algebra, and any `MDifferentiable` self-map `T`, the tangent bundle admits a `MeasurableFraming`.

The construction is the disjointified-countable-atlas argument of the module docstring: a countable
atlas exists by σ-compactness; its open chart sources disjointify to a countable measurable
partition; each block carries the continuous trivialization frame
`Trivialization.continuousLinearEquivAt`; gluing
(`MeasurableFraming.of_measurablePartitionFrame`) gives a global frame whose conjugated derivative
is measurable because it is the (continuous) chart-coordinate representation of `mfderiv` on each
block.

The proof is a single BLOCKED leaf. Two precise pieces are owed, both Mathlib-scale:

* **(A) per-block continuity** of `x ↦ inTangentCoordinates I I T T (mfderiv I I T) x₀ x` on a chart
  neighbourhood of `x₀`. This is exactly `ContMDiffAt.mfderiv_const` at `m = 0`
  (`Mathlib.Geometry.Manifold.ContMDiffMFDeriv`), a genuine theorem whose import chain is **not in
  the precompiled Mathlib cache here** (wiring it forces a from-source rebuild of the
  manifold-derivative chain);
* **(B) a measurable chart-selector** picking, measurably in `x`, the block of the disjointified
  cover containing `x`, plus identifying the per-block frame's conjugated derivative with the
  continuous in-coordinates map from (A) — infrastructure Mathlib does not package for manifolds.

Given (A)+(B), the proof is `MeasurableFraming.of_measurablePartitionFrame` applied to the
disjointified countable atlas. -/
theorem exists_measurableFraming_of_sigmaCompact
    [SigmaCompactSpace M] [SecondCountableTopology H]
    {T : M → M} (hT : MDifferentiable I I T) :
    Nonempty (MeasurableFraming I T) := by
  sorry
  -- BLOCKED: see the docstring. Requires (A) `ContMDiffAt.mfderiv_const` (uncached import chain)
  -- for the per-block continuity of `inTangentCoordinates I I T T (mfderiv I I T) x₀`, and (B) a
  -- measurable chart-selector over the disjointified countable atlas — neither available in the
  -- Mathlib build here. The reduction itself (`of_measurablePartitionFrame`) is sorry-free above.

end Frontier.Issue2
