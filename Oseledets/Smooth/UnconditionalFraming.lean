/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.SigmaCompact
import Oseledets.Smooth.Framing

/-!
# Unconditional measurability of the manifold derivative cocycle (issue #9, no chart regularity)

The prior (LCC-conditional) route proved measurability of `x ↦ mfderiv I I T x` on a
σ-compact boundaryless `C¹` manifold by *un-conjugating* the fixed-base in-coordinates
representative with **moving-source-index** coordinate changes `x ↦ tangentCoordChange I x c x`;
those are continuous only under the extra hypothesis `[LocallyConstantChartAt H M]` (the canonical
`chartAt x` is a pathological selector).

This file removes that hypothesis. The trick is to choose the linear frame **piecewise from a fixed
reference chart per block**. On the block at source/target references `a`/`b`, the frame at `x` is
the *fixed-reference* coordinate change `tangentCoordChange I x a x` (source side, with inverse
`tangentCoordChange I a x x`) and `tangentCoordChange I (T x) b (T x)` (target side). The
*conjugated* generator
`x ↦ tangentCoordChange I (T x) b (T x) ∘L mfderiv I I T x ∘L tangentCoordChange I a x x`
is **exactly** the `fderivWithin` of the **fixed-chart-written** map
`extChartAt I b ∘ T ∘ (extChartAt I a).symm`. Since `T` is `C¹`, this fixed-chart-written map is
`ContDiffOn ℝ 1`, so its `fderivWithin` is continuous (`ContDiffOn.continuousOn_fderiv_of_isOpen`) —
with **no chart-regularity hypothesis**. The moving native charts `chartAt x`, `chartAt (T x)`
cancel algebraically inside the conjugated composite; they never appear as standalone moving-index
factors.

## Main results

* `tangentCoordChange_eq_mfderiv_extChartAt` / `tangentCoordChange_eq_mfderivWithin_extChartAt_symm`
  — the two fixed-reference coordinate-change factors written as chart derivatives.
* `conjGen_eq_fixedChart_fderivWithin` — the two-reference conjugated generator equals the
  `fderivWithin` of the fixed-chart-written map.
* `continuousOn_conjGen_block2` — **the crux**: the two-reference conjugated generator is
  `ContinuousOn` the block, with **no** `LocallyConstantChartAt`.
* `continuousOn_framedGenerator_block` — the single-reference (`b = T a`) crux, in the exact
  `tangentCoordChange` form of the issue task.
* `exists_measurableFraming_of_sigmaCompact` — **unconditional** existence of a
  `MeasurableFraming` on a σ-compact boundaryless `C¹` manifold (no `LocallyConstantChartAt`).

## References

* S. Filip, *Notes on the Multiplicative Ergodic Theorem*, arXiv:1710.10694, §2.2.2.
-/

open Filter Topology Set Function MeasureTheory
open scoped Manifold

namespace Oseledets

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless]

/-! ### The two fixed-reference coordinate-change factors as chart derivatives -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
/-- The **target** fixed-reference factor is the derivative of the fixed target chart at the moving
image point: for `y ∈ (chartAt H b).source`,
`tangentCoordChange I y b y = mfderiv (extChartAt I b) y`.
Extracted from the first `congr` bullet of `inTangentCoordinates_eq_mfderiv_comp`. -/
theorem tangentCoordChange_eq_mfderiv_extChartAt {b y : M} (hy : y ∈ (chartAt H b).source) :
    tangentCoordChange I y b y = mfderiv I 𝓘(ℝ, E) (extChartAt I b) y := by
  have hd : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I b) y :=
    mdifferentiableAt_extChartAt (by simpa using hy)
  rw [tangentCoordChange_def]
  simp_all [mfderiv]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
/-- The **source** fixed-reference factor is the derivative of the inverse fixed source chart at the
moving image point: for `x ∈ (chartAt H a).source`,
`tangentCoordChange I a x x = mfderivWithin (extChartAt I a).symm (range I) (extChartAt I a x)`.
Extracted from the second `congr` bullet of `inTangentCoordinates_eq_mfderiv_comp`. -/
theorem tangentCoordChange_eq_mfderivWithin_extChartAt_symm {a x : M}
    (hx : x ∈ (chartAt H a).source) :
    tangentCoordChange I a x x =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I a).symm (range I) (extChartAt I a x) := by
  rw [tangentCoordChange_def]
  simp only [mfderivWithin, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, inter_univ]
  rw [if_pos]
  · simp [Function.comp_def, OpenPartialHomeomorph.left_inv (chartAt H a) hx]
  · apply mdifferentiableWithinAt_extChartAt_symm
    apply (extChartAt I a).map_source
    simpa using hx

/-! ### The fixed-chart-written map and its smoothness -/

/-- The manifold derivative recorded with the homogeneous model-fibre type `E →L[ℝ] E`
(legitimate since `TangentSpace I x` is definitionally `E`). This packaging gives `mfderiv` a
non-dependent `E →L[ℝ] E` type so it can be `.comp`-osed with the model-space `tangentCoordChange`
factors (the `TangentSpace` synonym is not reducible, so the bare `mfderiv I I T x` would not
unify). -/
def mfderivHom (T : M → M) (x : M) : E →L[ℝ] E := mfderiv I I T x

variable (I) in
/-- The map `T` written in the **fixed** reference charts: source chart `extChartAt I a`, target
chart `extChartAt I b`. A map between model spaces `E → E`. -/
def fixedChartWritten2 (T : M → M) (a b : M) : E → E :=
  extChartAt I b ∘ T ∘ (extChartAt I a).symm

variable (H) in
/-- The open block at source reference `a`, target reference `b`: points of the chart at `a` whose
image lies in the chart at `b`. -/
def block2 (T : M → M) (a b : M) : Set M :=
  (chartAt H a).source ∩ T ⁻¹' (chartAt H b).source

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
theorem isOpen_block2 {T : M → M} (hT : Continuous T) (a b : M) :
    IsOpen (block2 (H := H) T a b) :=
  (chartAt H a).open_source.inter ((chartAt H b).open_source.preimage hT)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
/-- The fixed-chart-written map is `ContDiffOn ℝ 1` on the image of the block under the fixed
source chart. This is `contMDiffOn_iff_of_subset_source` for the `C¹` map `T` and the chart pair
`(a, b)` — **no** chart-regularity hypothesis. -/
theorem contDiffOn_fixedChartWritten2 {T : M → M} (hT : ContMDiff I I 1 T) (a b : M) :
    ContDiffOn ℝ 1 (fixedChartWritten2 I T a b)
      (extChartAt I a '' block2 (H := H) T a b) := by
  have hsub : block2 (H := H) T a b ⊆ (chartAt H a).source := inter_subset_left
  have hmaps : MapsTo T (block2 (H := H) T a b) (chartAt H b).source := fun x hx => hx.2
  exact ((contMDiffOn_iff_of_subset_source (n := 1) (f := T) (I := I) (I' := I)
    hsub hmaps).1 hT.contMDiffOn).2

/-! ### The fold: the conjugated generator equals the fixed-chart `fderivWithin` -/

variable (I) in
/-- The **two-reference conjugated generator**: the manifold derivative `mfderiv I I T x`
conjugated by the *fixed-reference* coordinate changes — source reference `a`, target reference
`b`. -/
def conjGen (T : M → M) (a b : M) (x : M) : E →L[ℝ] E :=
  (tangentCoordChange I (T x) b (T x)).comp
    ((mfderivHom (I := I) T x).comp (tangentCoordChange I a x x))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
/-- **The fold identity.** On the block, the two-reference conjugated generator equals the
`fderivWithin` of the **fixed-chart-written** map `extChartAt I b ∘ T ∘ (extChartAt I a).symm`,
evaluated at the moving image point `extChartAt I a x`. The moving native charts `chartAt x`,
`chartAt (T x)` cancel inside.

The three factors `tangentCoordChange I (T x) b (T x)`, `mfderiv I I T x`,
`tangentCoordChange I a x x` are rewritten as the fixed chart derivatives `D(extChartAt I b)`,
`DT`, `D((extChartAt I a).symm)`; the manifold chain rule (`mfderivWithin_comp` /
`mfderiv_comp_mfderivWithin`) re-assembles them into the single derivative of the composite, which
is then identified with the Fréchet derivative (`mfderivWithin_eq_fderivWithin`). -/
theorem conjGen_eq_fixedChart_fderivWithin {T : M → M} (hT : MDifferentiable I I T)
    {a b x : M} (hx : x ∈ block2 (H := H) T a b) :
    conjGen I T a b x =
      fderivWithin ℝ (fixedChartWritten2 I T a b) (range I) (extChartAt I a x) := by
  obtain ⟨hxs, hxt⟩ := hx
  -- Source-membership facts.
  have hcsx : extChartAt I a x ∈ (extChartAt I a).target := by
    apply (extChartAt I a).map_source; rwa [extChartAt_source]
  have hsymm : (extChartAt I a).symm (extChartAt I a x) = x :=
    (extChartAt I a).left_inv (by rwa [extChartAt_source])
  -- Rewrite the three factors as chart derivatives.
  rw [conjGen, tangentCoordChange_eq_mfderiv_extChartAt hxt,
    tangentCoordChange_eq_mfderivWithin_extChartAt_symm hxs,
    show mfderivHom (I := I) T x = mfderivWithin I I T univ x by
      rw [mfderivHom, mfderivWithin_univ]]
  -- Differentiability facts for the chain rule.
  have hsymmDiff : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I a).symm (range I)
      (extChartAt I a x) := mdifferentiableWithinAt_extChartAt_symm hcsx
  have hbDiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I b) (T x) :=
    mdifferentiableAt_extChartAt (by simpa using hxt)
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, E) (range I) (extChartAt I a x) := by
    apply UniqueDiffWithinAt.uniqueMDiffWithinAt
    exact I.uniqueDiffOn _ (extChartAt_target_subset_range a hcsx)
  have hTatsymm : MDifferentiableWithinAt I I T univ x := (hT x).mdifferentiableWithinAt
  have hTsymmComp : MDifferentiableWithinAt 𝓘(ℝ, E) I (T ∘ (extChartAt I a).symm) (range I)
      (extChartAt I a x) := by
    apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I)
    · rw [hsymm]; exact hT x
    · exact hsymmDiff
  -- assemble: D(ct) ∘ DT ∘ D(cs.symm) = D(ct ∘ T ∘ cs.symm) on `range I`, as `mfderivWithin`.
  have hfold1 : (mfderivWithin I I T univ x).comp
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I a).symm (range I) (extChartAt I a x))
      = mfderivWithin 𝓘(ℝ, E) I (T ∘ (extChartAt I a).symm) (range I) (extChartAt I a x) :=
    (mfderivWithin_comp_of_eq (I := 𝓘(ℝ, E)) (I' := I) (I'' := I) (u := univ)
      (g := T) (f := (extChartAt I a).symm) hTatsymm hsymmDiff (subset_univ _) huniq hsymm).symm
  have hfold2 : (mfderiv I 𝓘(ℝ, E) (extChartAt I b) (T x)).comp
        (mfderivWithin 𝓘(ℝ, E) I (T ∘ (extChartAt I a).symm) (range I) (extChartAt I a x))
      = mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt I b ∘ (T ∘ (extChartAt I a).symm)) (range I)
          (extChartAt I a x) :=
    (mfderiv_comp_mfderivWithin_of_eq (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
      (g := extChartAt I b) (f := T ∘ (extChartAt I a).symm)
      hbDiff hTsymmComp huniq (by rw [Function.comp_apply, hsymm])).symm
  rw [← mfderivWithin_eq_fderivWithin (f := fixedChartWritten2 I T a b) (s := range I)
    (x := extChartAt I a x)]
  -- prove the operator equality on vectors (association-agnostic).
  ext v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- LHS: `D(ct)(Tx) (DT_x (D(cs.symm)(cs x) v))`; RHS: `D(ct∘T∘cs.symm)(cs x) v`.
  rw [show mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (fixedChartWritten2 I T a b) (range I) (extChartAt I a x)
      = mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt I b ∘ (T ∘ (extChartAt I a).symm)) (range I)
          (extChartAt I a x) from rfl,
    ← hfold2, ← hfold1]
  rfl

/-! ### The crux: continuity of the conjugated generator on the block (no chart regularity) -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
  [I.Boundaryless] in
/-- The fixed source chart `x ↦ extChartAt I a x` is continuous on the block (it is the chart map,
continuous on its source). -/
theorem continuousOn_extChartAt_source_block2 {T : M → M} (a b : M) :
    ContinuousOn (extChartAt I a) (block2 (H := H) T a b) :=
  (continuousOn_extChartAt a).mono (by
    intro x hx; rw [extChartAt_source]; exact hx.1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **CRUX LEMMA.** On the block `block2 H T a b`, the two-reference conjugated generator `conjGen`
is `ContinuousOn`, with **no** chart-regularity hypothesis (`LocallyConstantChartAt`-free). It
equals the `fderivWithin` of the fixed-chart-written `C¹` map composed with the continuous fixed
source chart; the moving native charts cancel inside. -/
theorem continuousOn_conjGen_block2 {T : M → M} (hT : ContMDiff I I 1 T) (a b : M) :
    ContinuousOn (conjGen I T a b) (block2 (H := H) T a b) := by
  set img : Set E := extChartAt I a '' block2 (H := H) T a b with himg_def
  have hcd : ContDiffOn ℝ 1 (fixedChartWritten2 I T a b) img :=
    contDiffOn_fixedChartWritten2 hT a b
  -- `img` is open: `cs '' block = cs.symm ⁻¹' block ∩ cs.target`, an intersection of opens.
  have himg_eq : img =
      (extChartAt I a).symm ⁻¹' block2 (H := H) T a b ∩ (extChartAt I a).target := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, (extChartAt I a).map_source (by rw [extChartAt_source]; exact hz.1)⟩
      rw [mem_preimage, (extChartAt I a).left_inv (by rw [extChartAt_source]; exact hz.1)]
      exact hz
    · rintro ⟨hy1, hy2⟩
      exact ⟨(extChartAt I a).symm y, by rwa [mem_preimage] at hy1, (extChartAt I a).right_inv hy2⟩
  have hImgOpen : IsOpen img := by
    rw [himg_eq, Set.inter_comm]
    exact (continuousOn_extChartAt_symm a).isOpen_inter_preimage (isOpen_extChartAt_target a)
      (isOpen_block2 hT.continuous a b)
  -- With `range I = univ`, `fderivWithin ℝ g (range I) = fderiv ℝ g`, continuous on the open `img`.
  have hfderivCont :
      ContinuousOn (fderivWithin ℝ (fixedChartWritten2 I T a b) (range I)) img := by
    have heq : (fderivWithin ℝ (fixedChartWritten2 I T a b) (range I))
        = (fderiv ℝ (fixedChartWritten2 I T a b)) := by
      funext y; rw [I.range_eq_univ, fderivWithin_univ]
    rw [heq]
    exact hcd.continuousOn_fderiv_of_isOpen hImgOpen le_rfl
  -- Compose with the continuous fixed source chart `cs` on the block.
  have hcomp : ContinuousOn
      ((fderivWithin ℝ (fixedChartWritten2 I T a b) (range I)) ∘ (extChartAt I a))
      (block2 (H := H) T a b) :=
    hfderivCont.comp (continuousOn_extChartAt_source_block2 a b)
      (fun x hx => Set.mem_image_of_mem _ hx)
  refine hcomp.congr (fun x hx => ?_)
  exact conjGen_eq_fixedChart_fderivWithin (hT.mdifferentiable one_ne_zero) hx

/-! ### The single-reference crux in the task's exact `tangentCoordChange` form -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **THE CRUX (task statement, `tangentCoordChange` form).** On the block
`(chartAt H a).source ∩ T ⁻¹' (chartAt H (T a)).source`, with the **fixed-chart frame** at
reference points `a` (source) / `T a` (target) — `(φ_a x).symm := tangentCoordChange I a x x` on
the source side, `φ_{Ta}(T x) := tangentCoordChange I (T x) (T a) (T x)` on the target side — the
conjugated generator
`x ↦ tangentCoordChange I (T x) (T a) (T x) ∘L mfderiv I I T x ∘L tangentCoordChange I a x x`
(the middle factor carried by the model-fibre cast `mfderivHom`) is `ContinuousOn`, with **NO
chart-regularity hypothesis** (no `LocallyConstantChartAt`).

The make-or-break lemma of the unconditional construction: the moving canonical charts `chartAt x`,
`chartAt (T x)` *cancel* inside the conjugated composite, which equals the `fderivWithin` of the
fixed-chart-written `C¹` map (continuity is then C¹-automatic). It is the `b = T a` instance of
`continuousOn_conjGen_block2`. -/
theorem continuousOn_framedGenerator_block {T : M → M} (hT : ContMDiff I I 1 T) (a : M) :
    ContinuousOn (fun x =>
      (tangentCoordChange I (T x) (T a) (T x)).comp
        ((mfderivHom (I := I) T x).comp (tangentCoordChange I a x x)))
      ((chartAt H a).source ∩ T ⁻¹' (chartAt H (T a)).source) :=
  continuousOn_conjGen_block2 hT a (T a)

/-! ### Assembly: the piecewise trivialization frame and unconditional existence -/

/-- The **fixed-reference tangent frame** at base point `c`, evaluated at `x`: the
`continuousLinearEquivAt` of the tangent-bundle trivialization at `c`. On `(chartAt H c).source`
(the trivialization base set) its forward map is `tangentCoordChange I x c x` and its inverse is
`tangentCoordChange I c x x`. Off the base set we fall back to a junk membership proof (the
trivialization equiv is total in `x` via `Classical`); only the on-block values are used. -/
def tangentFrameAt (c : M) (x : M) : TangentSpace I x ≃L[ℝ] E := by
  classical
  exact if hx : x ∈ (chartAt H c).source then
    (trivializationAt E (TangentSpace I) c).continuousLinearEquivAt ℝ x
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hx)
  else ContinuousLinearEquiv.refl ℝ (TangentSpace I x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
/-- The frame as a continuous linear map equals `tangentCoordChange I x c x` on the chart source. -/
theorem tangentFrameAt_coe {c x : M} (hx : x ∈ (chartAt H c).source) :
    ((tangentFrameAt (I := I) c x) : TangentSpace I x →L[ℝ] E) =
      tangentCoordChange I x c x := by
  classical
  rw [tangentFrameAt, dif_pos hx,
    Bundle.Trivialization.coe_continuousLinearEquivAt_eq',
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
/-- The frame inverse as a continuous linear map equals `tangentCoordChange I c x x`. -/
theorem tangentFrameAt_symm_coe {c x : M} (hx : x ∈ (chartAt H c).source) :
    (((tangentFrameAt (I := I) c x).symm) : E →L[ℝ] TangentSpace I x)
      = tangentCoordChange I c x x := by
  classical
  rw [tangentFrameAt, dif_pos hx,
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq',
    TangentBundle.symmL_trivializationAt_eq_core hx]

/-! ### Unconditional existence of a measurable framing -/

variable [MeasurableSpace M] [BorelSpace M]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [I.Boundaryless] [BorelSpace M] in
/-- A function measurable on each block of a countable measurable cover is measurable (local copy,
proved sorry-free via `Set.liftCover`). -/
theorem measurable_of_measurable_on_countable_cover'' {ι : Type*} [Countable ι]
    (t : ι → Set M) (htm : ∀ i, MeasurableSet (t i)) (htU : ⋃ i, t i = univ)
    {g : M → (E →L[ℝ] E)} (hg : ∀ i, Measurable ((t i).restrict g)) :
    Measurable g := by
  have hcover :
      g = Set.liftCover t (fun i => (t i).restrict g) (fun _ _ _ _ _ => rfl) htU := by
    funext x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ t i := by
      have : x ∈ ⋃ i, t i := htU ▸ mem_univ x
      simpa using this
    rw [Set.liftCover_of_mem hi]; rfl
  rw [hcover]
  exact measurable_liftCover t htm (fun i => (t i).restrict g) hg (fun _ _ _ _ _ => rfl) htU

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [I.Boundaryless]
  [MeasurableSpace M] [BorelSpace M] in
/-- **Framed generator under the piecewise frame equals `conjGen` (pointwise).** At a single point
`x` of the block, if the global frame coincides at `x` with `tangentFrameAt a` and at `T x` with
`tangentFrameAt b`, then the framed generator at `x` equals the two-reference conjugated generator
`conjGen I T a b x`. -/
theorem framedGenerator_eq_conjGen {T : M → M} {a b : M}
    (frame : (x : M) → TangentSpace I x ≃L[ℝ] E) {x : M} (hx : x ∈ block2 (H := H) T a b)
    (hfa : frame x = tangentFrameAt a x) (hfb : frame (T x) = tangentFrameAt b (T x)) :
    (frame (T x) : TangentSpace I (T x) →L[ℝ] E).comp
        ((mfderiv I I T x).comp ((frame x).symm : E →L[ℝ] TangentSpace I x))
      = conjGen I T a b x := by
  have hxs : x ∈ (chartAt H a).source := hx.1
  have hxt : T x ∈ (chartAt H b).source := hx.2
  rw [hfa, hfb, conjGen, tangentFrameAt_coe hxt, tangentFrameAt_symm_coe hxs]
  rfl

set_option linter.unusedSectionVars false in
/-- **Unconditional existence of a measurable framing on a σ-compact boundaryless C¹ manifold.**
For a `C¹`, σ-compact (hence Lindelöf) **boundaryless** manifold `M` with its Borel σ-algebra, and
any `ContMDiff I I 1` self-map `T`, the tangent bundle admits a `MeasurableFraming` — **with no
`LocallyConstantChartAt` hypothesis**.

The frame is chosen **piecewise from a fixed reference chart per block** (`tangentFrameAt`); the
conjugated generator on each pair-block `Pₙ ∩ T⁻¹ Pₘ` is the two-reference conjugated generator
`conjGen I T aₙ aₘ`, continuous there by the crux `continuousOn_conjGen_block2`. A σ-compact space
is Lindelöf, so the chart-source cover has a countable subcover `(chartAt H aₙ).source`;
disjointifying gives a countable Borel partition `Pₙ`, and the products `Pₙ ∩ T⁻¹ Pₘ` form a
countable Borel cover on each piece of which the conjugated generator is continuous, hence
measurable; the pieces glue. -/
theorem exists_measurableFraming_of_sigmaCompact
    [SigmaCompactSpace M] {T : M → M} (hT : ContMDiff I I 1 T) :
    Nonempty (MeasurableFraming I T) := by
  classical
  -- Lindelöf countable subcover of the chart-source cover `{(chartAt H a).source}`.
  have hcover : ⋃ a : M, (chartAt H a).source = univ :=
    eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_chart_source H x⟩
  obtain ⟨s, hs_count, _, hs_cover⟩ :=
    (isLindelof_univ (X := M)).elim_nhds_subcover (fun a => (chartAt H a).source)
      (fun a _ => (chartAt H a).open_source.mem_nhds (mem_chart_source H a))
  -- If `M` is empty, the framing is trivial (every map is measurable on a subsingleton).
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨⟨fun _ => ContinuousLinearEquiv.refl ℝ E, Subsingleton.measurable⟩⟩
  -- `M` nonempty: enumerate the countable reference set `s` as a sequence `a : ℕ → M` whose chart
  -- sources cover `M`.
  obtain ⟨a, ha_surj⟩ :
      ∃ a : ℕ → M, ∀ x : M, (∃ n, x ∈ (chartAt H (a n)).source) := by
    obtain ⟨a, ha⟩ := Set.countable_iff_exists_subset_range.1 hs_count
    refine ⟨a, fun x => ?_⟩
    have : x ∈ (⋃ c ∈ s, (chartAt H c).source) := hs_cover (mem_univ x)
    rw [mem_iUnion₂] at this
    obtain ⟨c, hc, hxc⟩ := this
    obtain ⟨n, rfl⟩ := ha hc
    exact ⟨n, hxc⟩
  -- Disjointify the open chart-source cover into a Borel partition `P`.
  set U : ℕ → Set M := fun n => (chartAt H (a n)).source with hU_def
  set P : ℕ → Set M := disjointed U with hP_def
  have hPsub : ∀ n, P n ⊆ U n := fun n => disjointed_le U n
  have hPmeas : ∀ n, MeasurableSet (P n) := fun n =>
    MeasurableSet.disjointed (fun k => ((chartAt H (a k)).open_source).measurableSet) n
  have hPcover : ⋃ n, P n = univ := by
    rw [hP_def, iUnion_disjointed]
    exact eq_univ_of_forall fun x => by
      obtain ⟨n, hn⟩ := ha_surj x; exact mem_iUnion.2 ⟨n, hn⟩
  -- The global frame: on `P n`, use `tangentFrameAt (a n)`; choose the unique block index.
  -- `idx x` = least `n` with `x ∈ P n` (exists by cover; unique by disjointness).
  have hidx : ∀ x : M, ∃ n, x ∈ P n := fun x => by
    have : x ∈ ⋃ n, P n := by rw [hPcover]; exact mem_univ x
    exact mem_iUnion.1 this
  set idx : M → ℕ := fun x => Nat.find (hidx x) with hidx_def
  have hidx_mem : ∀ x, x ∈ P (idx x) := fun x => Nat.find_spec (hidx x)
  have hidx_unique : ∀ {x : M} {n : ℕ}, x ∈ P n → idx x = n := by
    intro x n hn
    by_contra hne
    have hd : Disjoint (P (idx x)) (P n) := by
      rw [hP_def]; exact disjoint_disjointed U hne
    exact Set.disjoint_left.1 hd (hidx_mem x) hn
  set frame : (x : M) → TangentSpace I x ≃L[ℝ] E :=
    fun x => tangentFrameAt (a (idx x)) x with hframe_def
  refine ⟨⟨frame, ?_⟩⟩
  -- measurability of the framed generator: glue over the countable cover `{P n ∩ T⁻¹' P m}`.
  set G : M → (E →L[ℝ] E) := fun x =>
    (frame (T x) : TangentSpace I (T x) →L[ℝ] E).comp
      ((mfderiv I I T x).comp ((frame x).symm : E →L[ℝ] TangentSpace I x)) with hG_def
  -- index the cover by `ℕ × ℕ`
  set Q : ℕ × ℕ → Set M := fun p => P p.1 ∩ T ⁻¹' P p.2 with hQ_def
  have hQmeas : ∀ p, MeasurableSet (Q p) := fun p =>
    (hPmeas p.1).inter ((hPmeas p.2).preimage hT.continuous.measurable)
  have hQcover : ⋃ p, Q p = univ := by
    refine eq_univ_of_forall fun x => ?_
    refine mem_iUnion.2 ⟨(idx x, idx (T x)), hidx_mem x, ?_⟩
    rw [mem_preimage]; exact hidx_mem (T x)
  -- On each `Q (n,m)`, `G = conjGen I T (a n) (a m)`, continuous by the crux.
  refine measurable_of_measurable_on_countable_cover'' Q hQmeas hQcover (fun p => ?_)
  obtain ⟨n, m⟩ := p
  -- `Q (n,m) ⊆ block2 T (a n) (a m)`
  have hQsub : Q (n, m) ⊆ block2 (H := H) T (a n) (a m) := by
    intro x hx
    exact ⟨hPsub n hx.1, by rw [mem_preimage]; exact hPsub m hx.2⟩
  -- on `Q (n,m)`, `idx x = n` and `idx (T x) = m`, so `frame` is the fixed-reference frame.
  have hframe_eq : Set.restrict (Q (n, m)) G
      = Set.restrict (Q (n, m)) (conjGen I T (a n) (a m)) := by
    funext y
    have hy1 : (y : M) ∈ P n := y.2.1
    have hy2 : T (y : M) ∈ P m := y.2.2
    change G (y : M) = conjGen I T (a n) (a m) (y : M)
    rw [hG_def]
    refine framedGenerator_eq_conjGen frame (hQsub y.2) ?_ ?_
    · change tangentFrameAt (a (idx (y : M))) (y : M) = tangentFrameAt (a n) (y : M)
      rw [hidx_unique hy1]
    · change tangentFrameAt (a (idx (T (y : M)))) (T (y : M)) = tangentFrameAt (a m) (T (y : M))
      rw [hidx_unique hy2]
  -- continuity ⇒ measurability of the restriction.
  rw [hframe_eq]
  have hcontQ : ContinuousOn (conjGen I T (a n) (a m)) (Q (n, m)) :=
    (continuousOn_conjGen_block2 hT (a n) (a m)).mono hQsub
  exact (continuousOn_iff_continuous_restrict.1 hcontQ).measurable

end

end Oseledets
