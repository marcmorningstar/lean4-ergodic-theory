/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Topology.Compactness.Lindelof

/-!
# Borel measurability of the manifold derivative `x ↦ mfderiv I I T x`

This module supplies the single analytic core behind issue #2: for a `C¹` self-map `T` of a
**boundaryless**, σ-compact (Lindelöf) manifold `M` equipped with its Borel σ-algebra, the manifold
derivative `x ↦ mfderiv I I T x`, viewed (via the definitional `TangentSpace I x = E`) as a map
`M → (E →L[ℝ] E)`, is Borel measurable.

## Strategy (chart-local gluing)

Fix a base point `a : M`. On the open block
`V a := (chartAt H a).source ∩ T ⁻¹' (chartAt H (T a)).source` the *fixed-base in-coordinates
representative* `R a x := inTangentCoordinates I I id T (fun x => mfderiv I I T x) a x` is **continuous**
near `a` (it is even `C⁰` by `ContMDiffAt.mfderiv_const`, `m = 0`, `n = 1`). By
`inTangentCoordinates_eq` it equals
`tangentCoordChange I (T x) (T a) (T x) ∘L mfderiv I I T x ∘L tangentCoordChange I a x x`,
so `mfderiv I I T x` is recovered by *un-conjugating* with two coordinate changes. Using
`mfderiv_chartAt_eq_tangentCoordChange` each recovery factor is the manifold derivative of a **fixed
chart** at the moving point — itself continuous on the block by a second application of
`ContMDiffAt.mfderiv_const` (charts are smooth). Hence `mfderiv I I T` is continuous on each block.

A σ-compact space is Lindelöf, so the open cover `{V a}ₐ` (each `a ∈ V a`) admits a **countable**
subcover; the chart-local continuous (hence measurable) pieces glue to a global measurable map via
`measurable_of_isOpen_cover_countable`-style gluing (`Set.liftCover` / `measurable_liftCover`).

The hypotheses (`[I.Boundaryless]`, `ContMDiff I I 1 T`, σ-compact `M`, second-countable `H`) are the
honest ones identified in `docs/research/frontier/issue2/FEASIBILITY-2026-06-22.md`.
-/

open Filter Topology Set Function
open scoped Manifold

namespace Frontier.Issue2

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless]

/-- The manifold derivative recorded with the homogeneous model-fibre type `E →L[ℝ] E` (legitimate
since `TangentSpace I x` is definitionally `E`). -/
def mfderivHom (T : M → M) (x : M) : E →L[ℝ] E := mfderiv I I T x

theorem mfderivHom_eq (T : M → M) (x : M) : mfderivHom (I := I) T x = mfderiv I I T x := rfl

/-! ### Continuity of the manifold derivative of a fixed chart at a moving point -/

variable [SigmaCompactSpace M] [SecondCountableTopology H]

/-- For a `C¹` map `T`, the fixed-base in-coordinates representative
`x ↦ inTangentCoordinates I I id T (mfderiv I I T) a x` is continuous at `a`. This is
`ContMDiffAt.mfderiv_const` with `m = 0`, `n = 1`. -/
theorem continuousAt_inTangentCoordinates_mfderiv {T : M → M} (hT : ContMDiff I I 1 T) (a : M) :
    ContinuousAt
      (inTangentCoordinates I I id T (fun x => mfderiv I I T x) a) a := by
  have h : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) 0
      (inTangentCoordinates I I id T (fun x => mfderiv% T x) a) a :=
    (hT a).mfderiv_const (le_refl 1)
  exact h.continuousAt

/-! ### Un-conjugation: recovering `mfderiv` from the in-coordinates representative -/

/-- The in-coordinates representative, written via `tangentCoordChange`, with `f = id`, `g = T`.
For `x ∈ (chartAt H a).source` and `T x ∈ (chartAt H (T a)).source`,
`inTangentCoordinates I I id T (mfderiv I I T) a x
  = tangentCoordChange I (T x) (T a) (T x) ∘L mfderiv I I T x ∘L tangentCoordChange I a x x`. -/
theorem inTangentCoordinates_mfderiv_eq {T : M → M} {a x : M}
    (hx : x ∈ (chartAt H a).source) (hy : T x ∈ (chartAt H (T a)).source) :
    inTangentCoordinates I I id T (fun x => mfderiv I I T x) a x =
      (tangentCoordChange I (T x) (T a) (T x)).comp
        ((mfderivHom (I := I) T x).comp (tangentCoordChange I a x x)) := by
  rw [inTangentCoordinates_eq (I := I) (I' := I) id T (fun x => mfderiv I I T x) hx hy]
  rfl

/-- Recovery of `mfderiv` from the in-coordinates representative on a chart block, by
un-conjugating with the inverse coordinate changes (telescoping via `tangentCoordChange_comp`
and `tangentCoordChange_self`). The recovery factors are `tangentCoordChange I (T a) (T x) (T x)`
on the left and `tangentCoordChange I x a x` on the right. -/
theorem mfderiv_eq_unconj {T : M → M} {a x : M}
    (hx : x ∈ (chartAt H a).source) (hy : T x ∈ (chartAt H (T a)).source) :
    mfderivHom (I := I) T x =
      (tangentCoordChange I (T a) (T x) (T x)).comp
        ((inTangentCoordinates I I id T (fun x => mfderiv I I T x) a x).comp
          (tangentCoordChange I x a x)) := by
  rw [inTangentCoordinates_mfderiv_eq hx hy]
  -- Source-membership facts in `extChartAt` source (= chart source for boundaryless).
  have hxs : x ∈ (extChartAt I a).source := by rwa [extChartAt_source]
  have hxx : x ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact mem_chart_source H x
  have hys : T x ∈ (extChartAt I (T a)).source := by rwa [extChartAt_source]
  have hyy : T x ∈ (extChartAt I (T x)).source := by
    rw [extChartAt_source]; exact mem_chart_source H (T x)
  -- ext on a vector
  ext v
  simp only [ContinuousLinearMap.coe_comp', comp_apply]
  -- Right telescope: tcc I a x x (tcc I x a x v) = tcc I x x x v = v
  have hright : tangentCoordChange I a x x (tangentCoordChange I x a x v) = v := by
    rw [tangentCoordChange_comp ⟨⟨hxx, hxs⟩, hxx⟩]
    exact tangentCoordChange_self hxx
  rw [hright]
  -- Left telescope on the value w := mfderivHom T x v
  have hleft : tangentCoordChange I (T a) (T x) (T x)
      (tangentCoordChange I (T x) (T a) (T x) (mfderivHom (I := I) T x v)) =
        mfderivHom (I := I) T x v := by
    rw [tangentCoordChange_comp ⟨⟨hyy, hys⟩, hyy⟩]
    exact tangentCoordChange_self hyy
  exact hleft.symm

/-! ### The sharp residual gap: continuity of the moving-trivialization-index coordinate change

Both recovery factors in `mfderiv_eq_unconj` are values of `x ↦ tangentCoordChange I x c x`
(the coordinate change whose **first/source trivialization index moves with the point**, equal by
`mfderiv_chartAt_eq_tangentCoordChange` to `mfderiv I I (chartAt H c) x`). Mathlib provides
continuity of `tangentCoordChange I p q` only for **fixed** indices `p q`
(`continuousOn_tangentCoordChange`) and of `Trivialization.continuousLinearMapAt` only pointwise,
never as a function of the base point for a single trivialization. Supplying continuity of this
moving-index coordinate change is the entire residual content of issue #2; it is isolated here as the
single sharp obligation `continuousOn_tangentCoordChange_movingIndex`. Everything else in this module
(the un-conjugation telescoping above, the chart-glue below, **and the dual moving-target-index
factor `continuousOn_tangentCoordChange_movingTargetIndex`, which is derived from this one by
continuous-linear-map inversion**) is proved sorry-free around it. So this module — and hence the
whole issue-#9 measurability chain — now rests on exactly **one** `sorry`. -/

/-- **The sharp residual gap (issue #2).** The coordinate change with moving source index
`x ↦ tangentCoordChange I x c x` is continuous on the chart source `(chartAt H c).source`.

By `mfderiv_chartAt_eq_tangentCoordChange` this is exactly continuity of `x ↦ mfderiv I I (chartAt H c) x`
on the chart domain — the manifold derivative of a *fixed* chart map at the moving point. Mathlib has
no lemma for this: `ContMDiffAt.mfderiv_const` only yields continuity of the in-coordinates
representative (which reintroduces this very coordinate change), and the single-trivialization
`continuousLinearMapAt` carries no base-point continuity statement. Closing it is the
moving-trivialization-index continuity flagged in
`docs/research/frontier/issue2/FEASIBILITY-2026-06-22.md`. -/
theorem continuousOn_tangentCoordChange_movingIndex (c : M) :
    ContinuousOn (fun x => tangentCoordChange I x c x) (chartAt H c).source := by
  sorry

/-! ### Continuity of the recovery factors on a chart block -/

/-- The right recovery factor `x ↦ tangentCoordChange I x a x` is continuous on `(chartAt H a).source`
(direct instance of the sharp gap). -/
theorem continuousOn_rightFactor (a : M) :
    ContinuousOn (fun x => tangentCoordChange I x a x) (chartAt H a).source :=
  continuousOn_tangentCoordChange_movingIndex a

/-- The dual moving-**target**-index coordinate change `x ↦ tangentCoordChange I c x x` is continuous
on `(chartAt H c).source`. This is **proved** (not a separate gap): on the chart source the maps
`tangentCoordChange I x c x` and `tangentCoordChange I c x x` are mutually inverse continuous linear
maps (telescoping to the identity via `tangentCoordChange_comp`/`_self`), so this factor equals
`ContinuousLinearMap.inverse (tangentCoordChange I x c x)`; continuity then follows from
`continuousOn_tangentCoordChange_movingIndex` and the analyticity (hence continuity) of
`ContinuousLinearMap.inverse` at invertible values (`IsInvertible.contDiffAt_map_inverse`, using
`[FiniteDimensional ℝ E] ⇒ CompleteSpace E`). Thus the single residual primitive is
`continuousOn_tangentCoordChange_movingIndex` alone. -/
theorem continuousOn_tangentCoordChange_movingTargetIndex (c : M) :
    ContinuousOn (fun x => tangentCoordChange I c x x) (chartAt H c).source := by
  set s : Set M := (chartAt H c).source with hs_def
  -- For `x ∈ s`, `tcc I x c x` and `tcc I c x x` are mutually inverse continuous linear maps,
  -- telescoping to the identity via `tangentCoordChange_comp`/`_self`.
  have key : ∀ x ∈ s, (tangentCoordChange I x c x ∘L tangentCoordChange I c x x
        = ContinuousLinearMap.id ℝ E) ∧
      (tangentCoordChange I c x x ∘L tangentCoordChange I x c x = ContinuousLinearMap.id ℝ E) := by
    intro x hx
    have hxc : x ∈ (extChartAt I c).source := by rwa [extChartAt_source]
    have hxx : x ∈ (extChartAt I x).source := by
      rw [extChartAt_source]; exact mem_chart_source H x
    constructor
    · ext v
      simp only [ContinuousLinearMap.coe_comp', comp_apply, ContinuousLinearMap.id_apply]
      rw [tangentCoordChange_comp ⟨⟨hxc, hxx⟩, hxc⟩]
      exact tangentCoordChange_self hxc
    · ext v
      simp only [ContinuousLinearMap.coe_comp', comp_apply, ContinuousLinearMap.id_apply]
      rw [tangentCoordChange_comp ⟨⟨hxx, hxc⟩, hxx⟩]
      exact tangentCoordChange_self hxx
  -- The moving-target-index factor equals `inverse` of the moving-source-index factor on `s`.
  have hinv : EqOn (fun x => tangentCoordChange I c x x)
      (fun x => ContinuousLinearMap.inverse (tangentCoordChange I x c x)) s := by
    intro x hx
    exact (ContinuousLinearMap.inverse_eq (key x hx).1 (key x hx).2).symm
  refine ContinuousOn.congr ?_ hinv
  -- Continuity within `s` at each `x`: compose continuity of the source-index factor with
  -- continuity of `inverse` at its (invertible) value.
  intro x hx
  have hg : ContinuousWithinAt (fun y => tangentCoordChange I y c y) s x :=
    continuousOn_tangentCoordChange_movingIndex c x hx
  have hInvertible : (tangentCoordChange I x c x).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (key x hx).1 (key x hx).2
  have hcontInv : ContinuousAt ContinuousLinearMap.inverse (tangentCoordChange I x c x) :=
    (hInvertible.contDiffAt_map_inverse (n := 1)).continuousAt
  exact (hcontInv.tendsto).comp hg

/-- The left recovery factor `x ↦ tangentCoordChange I (T a) (T x) (T x)` is continuous on the block
`(chartAt H a).source ∩ T ⁻¹' (chartAt H (T a)).source`: precompose the moving-target-index gap
(`continuousOn_tangentCoordChange_movingTargetIndex` at `c := T a`) with the continuous `T`. -/
theorem continuousOn_leftFactor {T : M → M} (hT : Continuous T) (a : M) :
    ContinuousOn (fun x => tangentCoordChange I (T a) (T x) (T x))
      ((chartAt H a).source ∩ T ⁻¹' (chartAt H (T a)).source) := by
  have hcomp : ContinuousOn ((fun y => tangentCoordChange I (T a) y y) ∘ T)
      ((chartAt H a).source ∩ T ⁻¹' (chartAt H (T a)).source) := by
    apply (continuousOn_tangentCoordChange_movingTargetIndex (T a)).comp hT.continuousOn
    intro x hx
    exact hx.2
  exact hcomp

/-! ### Per-block continuity, then measurability, of the manifold derivative -/

variable (H) in
/-- The open block at base point `a`: points of the chart at `a` whose image lies in the chart at
`T a`. It is an open neighbourhood of `a` (`mem_block_self`), and these blocks cover `M`. -/
def derivBlock (T : M → M) (a : M) : Set M :=
  (chartAt H a).source ∩ T ⁻¹' (chartAt H (T a)).source

theorem isOpen_derivBlock {T : M → M} (hT : Continuous T) (a : M) :
    IsOpen (derivBlock H T a) :=
  (chartAt H a).open_source.inter ((chartAt H (T a)).open_source.preimage hT)

theorem mem_derivBlock_self (T : M → M) (a : M) : a ∈ derivBlock H T a :=
  ⟨mem_chart_source H a, mem_chart_source H (T a)⟩

/-- On its block, the manifold derivative `mfderivHom T` is continuous: it is the un-conjugation
(`mfderiv_eq_unconj`) of the continuous in-coordinates representative by the two continuous recovery
factors. -/
theorem continuousOn_mfderivHom_block {T : M → M} (hT : ContMDiff I I 1 T) (a : M) :
    ContinuousOn (mfderivHom (I := I) T) (derivBlock H T a) := by
  -- the in-coordinates representative is continuous on the block (continuous at `a`, but we only
  -- need continuity *on* the block; we get it via continuity at every block point? No — the
  -- `mfderiv_const` continuity is only *at* `a`. We instead use the explicit recovery formula,
  -- which holds *pointwise* on the block, with each recovery factor continuous on the block, and the
  -- in-coordinates representative replaced by its `tangentCoordChange`-expansion `R'` which is
  -- continuous on the block.)
  -- Expand `mfderivHom T x` on the block via the un-conjugation identity, all in `tangentCoordChange`
  -- terms (the in-coordinates representative is itself a product of tangentCoordChange factors with
  -- `mfderiv`, but we keep it abstract and prove continuity of the whole composite directly).
  classical
  -- We prove continuity *at each point* `b` of the block by re-basing the representative at `b`.
  apply continuousOn_of_forall_continuousAt
  intro b hb
  -- Re-base at `b`: on the block at `b`, use `mfderiv_eq_unconj` with base `b`.
  -- The representative `R b` is continuous at `b`; the recovery factors are continuous near `b`.
  have hRb : ContinuousAt (inTangentCoordinates I I id T (fun x => mfderiv I I T x) b) b :=
    continuousAt_inTangentCoordinates_mfderiv hT b
  -- block at `b`
  have hbBlock : b ∈ derivBlock H T b := mem_derivBlock_self T b
  -- right factor `tcc I x b x` continuous on `(chartAt H b).source`, hence at `b`
  have hright : ContinuousAt (fun x => tangentCoordChange I x b x) b :=
    (continuousOn_rightFactor b).continuousAt
      ((chartAt H b).open_source.mem_nhds (mem_chart_source H b))
  -- left factor continuous on the block at `b`, hence at `b`
  have hleft : ContinuousAt (fun x => tangentCoordChange I (T b) (T x) (T x)) b :=
    (continuousOn_leftFactor hT.continuous b).continuousAt
      ((isOpen_derivBlock hT.continuous b).mem_nhds hbBlock)
  -- The composite is continuous at `b`.
  have hcompCA : ContinuousAt
      (fun x => (tangentCoordChange I (T b) (T x) (T x)).comp
        ((inTangentCoordinates I I id T (fun x => mfderiv I I T x) b x).comp
          (tangentCoordChange I x b x))) b := by
    have h1 : ContinuousAt
        (fun x => (inTangentCoordinates I I id T (fun x => mfderiv I I T x) b x).comp
          (tangentCoordChange I x b x)) b :=
      (isBoundedBilinearMap_comp.continuous.continuousAt).comp (hRb.prodMk hright)
    exact (isBoundedBilinearMap_comp.continuous.continuousAt).comp (hleft.prodMk h1)
  -- `mfderivHom T` agrees with this composite on the block at `b` (an nhd of `b`), so it is
  -- continuous at `b`.
  refine hcompCA.congr ?_
  have hnhd : derivBlock H T b ∈ 𝓝 b :=
    (isOpen_derivBlock hT.continuous b).mem_nhds hbBlock
  filter_upwards [hnhd] with x hx
  exact (mfderiv_eq_unconj hx.1 hx.2).symm

/-! ### Measurable gluing over a countable cover of blocks -/

variable [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace (E →L[ℝ] E)] [BorelSpace (E →L[ℝ] E)]

/-- A function continuous on an open set, restricted to that set, is measurable. -/
theorem measurable_restrict_of_continuousOn {f : M → (E →L[ℝ] E)} {s : Set M}
    (hs : IsOpen s) (hf : ContinuousOn f s) : Measurable (s.restrict f) := by
  have : Continuous (s.restrict f) := by
    rw [continuousOn_iff_continuous_restrict] at hf
    exact hf
  exact this.measurable

/-- A function measurable on each set of a countable measurable cover is measurable (local copy of
the glue lemma, proved sorry-free via `Set.liftCover`). -/
theorem measurable_of_measurable_on_countable_cover' {ι : Type*} [Countable ι]
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

/-- **The core result.** For a `C¹` self-map `T` of a boundaryless, σ-compact manifold `M` (Borel
σ-algebra), the manifold derivative `x ↦ mfderiv I I T x : E →L[ℝ] E` is measurable. Proved by gluing
the per-block continuous representatives over a countable subcover (Lindelöf) — modulo the single
sharp residual gap `continuousOn_tangentCoordChange_movingIndex` /
`continuousOn_tangentCoordChange_movingTargetIndex`. -/
theorem measurable_mfderivHom {T : M → M} (hT : ContMDiff I I 1 T) :
    Measurable (mfderivHom (I := I) T) := by
  -- Lindelöf: the open cover `{derivBlock H T a}` (each `a ∈ derivBlock H T a`) has a countable
  -- subcover.
  have hcover : ⋃ a : M, derivBlock H T a = univ := by
    refine eq_univ_of_forall fun x => ?_
    exact mem_iUnion.2 ⟨x, mem_derivBlock_self T x⟩
  have hLindelof := (isLindelof_univ (X := M))
  obtain ⟨s, hs_count, _, hs_cover⟩ :=
    hLindelof.elim_nhds_subcover (fun a => derivBlock H T a)
      (fun a _ => (isOpen_derivBlock hT.continuous a).mem_nhds (mem_derivBlock_self T a))
  -- index by the countable set `s`
  haveI : Countable s := hs_count.to_subtype
  -- the subfamily covers `univ`
  have hsU : ⋃ a : s, derivBlock H T (a : M) = univ := by
    refine eq_univ_of_forall fun x => ?_
    have : x ∈ ⋃ a ∈ s, derivBlock H T a := hs_cover (mem_univ x)
    simp only [mem_iUnion, exists_prop] at this
    obtain ⟨a, ha, hx⟩ := this
    exact mem_iUnion.2 ⟨⟨a, ha⟩, hx⟩
  -- glue
  refine measurable_of_measurable_on_countable_cover'
    (fun a : s => derivBlock H T (a : M))
    (fun a => (isOpen_derivBlock hT.continuous (a : M)).measurableSet) hsU ?_
  intro a
  exact measurable_restrict_of_continuousOn (isOpen_derivBlock hT.continuous (a : M))
    (continuousOn_mfderivHom_block hT (a : M))

end

end Frontier.Issue2
