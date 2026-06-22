/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Compactness.SigmaCompact
import Frontier.Issue2.MFDerivMeasurable
import Oseledets.Cocycle.Norm
import Oseledets.MultiplicativeErgodic

/-!
# The derivative (tangent) cocycle of a smooth self-map of a manifold

This is the **manifold generalisation** of `Oseledets/Smooth/DerivativeCocycle.lean`
(the `EuclideanSpace ℝ (Fin d)` case). For a `C¹` self-map `T : M → M` of a finite-dimensional
manifold `M` modelled on a *real inner-product* model space `E` (so the tangent spaces inherit an
inner product and `M` is morally Riemannian with the model metric), the family of manifold
derivatives `x ↦ mfderiv I I T x` is a linear cocycle over `T`: by the manifold chain rule
(`mfderiv_comp`) the derivative of the `n`-th iterate `T^[n]` factors as a product of derivatives
along the orbit.

There are three layers, mirroring the task brief:

1. **The bundle cocycle.** `bundleDerivativeCocycle I T x := mfderiv I I T x`, recorded as an
   endomorphism `E →L[ℝ] E` of the model fibre. The *native* type of `mfderiv I I T x` is
   `TangentSpace I x →L[ℝ] TangentSpace I (T x)`, but in Mathlib `TangentSpace I x` is, *by
   definition*, the model space `E` for every `x` (an abuse of definitional equality that
   "definitionally trivialises" the tangent bundle over a chart-free type synonym). Giving the
   generator the homogeneous endomorphism type `E →L[ℝ] E` (by `rfl`) is what makes the family a
   genuine linear cocycle — composable, with a `Monoid` for `IsUnit`, and a non-dependent codomain
   for `Measurable`.

2. **The chain-rule cocycle identity** (`bundleDerivativeCocycle_iterate_succ`,
   `chainRule_cocycle_manifold`): the product of derivatives along the orbit equals
   `mfderiv I I (T^[n]) x`, proved by induction from `mfderiv_comp` exactly as in the Euclidean
   file (`Oseledets.chainRule_cocycle`).

3. **The matrix framing** (`derivativeCocycleManifold`): transport the endomorphism of `E` to a
   matrix `Matrix (Fin d) (Fin d) ℝ` through a *fixed* linear isometry
   `E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)` (`frameEquiv`, built from `stdOrthonormalBasis ℝ E`) and the
   star-algebra equivalence `Matrix.toEuclideanCLM`. This is the "measurable trivialisation /
   orthonormal frame field" of the task — and here it is even *globally constant* because the model
   fibre is fixed: the conjugating frame does not depend on `x`. The matrix cocycle then feeds the
   matrix MET `Oseledets.oseledets_filtration` verbatim.

## The wall

The single genuine obstruction is **measurability of `x ↦ mfderiv I I T x`** as a map
`M → (E →L[ℝ] E)` (equivalently, of the framed generator `derivativeCocycleManifold I T`). Mathlib
has *no* measurability theory for the manifold derivative: `mfderiv` is defined chart-locally as
`if MDifferentiableAt … then fderivWithin (writtenInExtChartAt …) … else 0`, and there is no global
lemma `Measurable (fun x => mfderiv I I T x)` (the analogue of `measurable_fderiv` used in the
Euclidean file), nor any `MeasurableSpace` instance produced from a `ChartedSpace` structure.
Mathlib supplies none of this, but it is **now proved sorry-free** under the honest chart-regularity
hypothesis `[LocallyConstantChartAt H M]` (charts locally constant in the base point — necessary,
since for an arbitrary `ChartedSpace` the unconstrained `chartAt` selection can make
`x ↦ mfderiv I I T x` non-measurable); see `Frontier.Issue2.MFDerivMeasurable.measurable_mfderivHom`.
Hence `measurable_bundleDerivativeCocycle` is sorry-free. The hypothesis form `hAmeas` of
`oseledets_filtration_derivativeCocycleManifold` is retained so that conditional headline stays
independent of any chart-regularity assumption.

## Main definitions

* `Frontier.Issue2.frameEquiv` — the fixed framing `E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)`.
* `Frontier.Issue2.bundleDerivativeCocycle` — the bundle generator `x ↦ mfderiv I I T x`.
* `Frontier.Issue2.derivativeCocycleManifold` — the matrix generator (framed bundle generator).

## Main results

* `Frontier.Issue2.bundleDerivativeCocycle_iterate_succ` — bundle chain-rule cocycle identity
  (one-step recursion; **sorry-free**).
* `Frontier.Issue2.chainRule_cocycle_manifold` — the matrix cocycle represents the framed
  `mfderiv I I (T^[n]) x` (**sorry-free**).
* `Frontier.Issue2.det_derivativeCocycleManifold_ne_zero` — nonvanishing determinant from
  invertibility of each bundle generator (**sorry-free**).
* `Frontier.Issue2.measurable_bundleDerivativeCocycle` — measurability of the bundle generator
  (**proved sorry-free** under `[LocallyConstantChartAt H M]`).
* `Frontier.Issue2.oseledets_filtration_derivativeCocycleManifold` — the Oseledets filtration for
  the derivative cocycle of an ergodic `C¹` self-map of `M`, taking the framed-generator
  measurability as a hypothesis (so this statement is itself **sorry-free**).

## References

* L. Arnold, *Random Dynamical Systems*, Springer (1998), Ch. 4 (MET on bundles and manifolds).
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
* J. Bochi, *The multiplicative ergodic theorem of Oseledets* (lecture notes, 2008), Exercise ii.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator Manifold

namespace Frontier.Issue2

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (E) in
/-- The model dimension: `finrank ℝ E`. The tangent spaces of `M` are all (definitionally) `E`, so
this is the fibre dimension of the tangent bundle, and the side of the cocycle matrices. -/
abbrev modelDim : ℕ := Module.finrank ℝ E

variable (E) in
/-- The **fixed framing** of the model fibre: a linear isometry
`E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))`, obtained from an arbitrary chosen orthonormal
basis (`stdOrthonormalBasis`). Conjugating a tangent-space endomorphism by this isometry turns it
into an endomorphism of `EuclideanSpace`, hence (via `Matrix.toEuclideanCLM`) into a matrix.

Crucially this framing is **globally constant** — it does not depend on the base point `x` — because
Mathlib models every tangent space `TangentSpace I x` on the *same* fixed space `E`. This is exactly
the measurable bundle trivialisation required by the manifold MET, here in its simplest (constant)
incarnation. -/
def frameEquiv : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (modelDim E)) :=
  (stdOrthonormalBasis ℝ E).repr

variable (E) in
/-- The framing as a *continuous linear equivalence* `E ≃L[ℝ] EuclideanSpace ℝ (Fin (modelDim E))`,
the underlying CLE of `frameEquiv`. Conjugating endomorphisms of `E` by `frameCLE` lands in
endomorphisms of `EuclideanSpace`. -/
def frameCLE : E ≃L[ℝ] EuclideanSpace ℝ (Fin (modelDim E)) :=
  (frameEquiv E).toContinuousLinearEquiv

@[simp] theorem frameCLE_apply (v : E) : frameCLE E v = frameEquiv E v := rfl

@[simp] theorem frameCLE_symm_apply (w : EuclideanSpace ℝ (Fin (modelDim E))) :
    (frameCLE E).symm w = (frameEquiv E).symm w := rfl

theorem norm_frameCLE (v : E) : ‖frameCLE E v‖ = ‖v‖ := (frameEquiv E).norm_map v

theorem norm_frameCLE_symm (w : EuclideanSpace ℝ (Fin (modelDim E))) :
    ‖(frameCLE E).symm w‖ = ‖w‖ := (frameEquiv E).symm.norm_map w

variable (E) in
/-- The **framing algebra isomorphism**: conjugation by `frameCLE` followed by `toEuclideanCLM.symm`,
packaged as an algebra equivalence
`(E →L[ℝ] E) ≃ₐ[ℝ] Matrix (Fin (modelDim E)) (Fin (modelDim E)) ℝ`.

Because it is an algebra equivalence it sends `1 ↦ 1` and products to products; this is precisely
what turns the *bundle* cocycle (a product of endomorphisms `mfderiv` along the orbit) into a
*matrix* cocycle without any side conditions. It is the algebraic heart of the bundle-to-matrix
reduction. (Continuity, needed only for the measurability of the matrix generator, is recorded
separately in `continuous_frameAlg`.) -/
def frameAlg : (E →L[ℝ] E) ≃ₐ[ℝ] Matrix (Fin (modelDim E)) (Fin (modelDim E)) ℝ :=
  (frameCLE E).conjContinuousAlgEquiv.toAlgEquiv.trans
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (modelDim E))).symm.toAlgEquiv

@[simp] theorem frameAlg_apply (L : E →L[ℝ] E) :
    frameAlg E L =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (modelDim E))).symm
        ((frameCLE E).conjContinuousAlgEquiv L) :=
  rfl

/-- The framing `frameAlg E` is continuous: it is `toEuclideanCLM.symm ∘ conjugation-by-frameCLE`,
where conjugation is continuous and `toEuclideanCLM.symm` is an `ℝ`-linear map between
finite-dimensional spaces (hence continuous). Used for the measurability of the matrix generator. -/
theorem continuous_frameAlg : Continuous (frameAlg E) := by
  have h1 : Continuous (frameCLE E).conjContinuousAlgEquiv :=
    (frameCLE E).conjContinuousAlgEquiv.continuous
  -- `toEuclideanCLM.symm` as an `ℝ`-linear map between finite-dimensional spaces is continuous
  have h2 : Continuous
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (modelDim E))).symm.toAlgEquiv.toLinearMap :=
    LinearMap.continuous_of_finiteDimensional _
  exact h2.comp h1

/-- The image of an endomorphism `L : E →L[ℝ] E` under the conjugation `frameCLE ∘L L ∘L frameCLE⁻¹`
acts on `EuclideanSpace` with the same operator norm as `L`: `frameCLE` and its inverse are
isometries (the underlying maps of the `LinearIsometryEquiv` `frameEquiv`), so conjugation by them
preserves the operator norm (`opNorm_comp_le` both ways with `norm_map`). -/
theorem norm_conj_frameCLE (L : E →L[ℝ] E) :
    ‖(frameCLE E).conjContinuousAlgEquiv L‖ = ‖L‖ := by
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  -- the underlying maps of `frameCLE`, `frameCLE.symm` are isometries
  have hfwd : ∀ v : E, ‖(frameCLE E) v‖ = ‖v‖ := norm_frameCLE
  have hinv : ∀ w : EuclideanSpace ℝ (Fin (modelDim E)), ‖(frameCLE E).symm w‖ = ‖w‖ :=
    norm_frameCLE_symm
  refine le_antisymm ?_ ?_
  · -- ‖e ∘L L ∘L e⁻¹‖ ≤ ‖L‖
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun w => ?_
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    calc ‖(frameCLE E) (L ((frameCLE E).symm w))‖
        = ‖L ((frameCLE E).symm w)‖ := hfwd _
      _ ≤ ‖L‖ * ‖(frameCLE E).symm w‖ := L.le_opNorm _
      _ = ‖L‖ * ‖w‖ := by rw [hinv]
  · -- ‖L‖ ≤ ‖e ∘L L ∘L e⁻¹‖, via the reverse conjugation
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have key : L v = (frameCLE E).symm ((frameCLE E).conjContinuousAlgEquiv L ((frameCLE E) v)) := by
      simp [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
    rw [key, hinv, ← hfwd v]
    exact ((frameCLE E).conjContinuousAlgEquiv L).le_opNorm _

/-- The framing preserves the L2 operator norm: a matrix `frameAlg E L` has the same norm as the
endomorphism `L` of `E`. Both `frameCLE` (an isometry) and `toEuclideanCLM` are norm-preserving. -/
theorem norm_frameAlg (L : E →L[ℝ] E) : ‖frameAlg E L‖ = ‖L‖ := by
  rw [frameAlg_apply, ← Matrix.l2_opNorm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
  exact norm_conj_frameCLE L

variable (I) in
/-- The **bundle derivative cocycle generator** of `T : M → M`: the manifold (Fréchet) derivative
`x ↦ mfderiv I I T x`, recorded as an honest **endomorphism of the model fibre** `E →L[ℝ] E`.

The native type of `mfderiv I I T x` is `TangentSpace I x →L[ℝ] TangentSpace I (T x)`, but Mathlib
defines `TangentSpace I x` as the model space `E` for *every* `x` (an abuse of definitional
equality), so this coercion to `E →L[ℝ] E` is `rfl`. Giving it the homogeneous endomorphism type
here is what makes the family a genuine linear cocycle over `T` (composable, with a `Monoid` for
`IsUnit`, and a non-dependent codomain for `Measurable`) — exactly the "definitionally trivialised
tangent bundle" the manifold MET relies on. -/
def bundleDerivativeCocycle (T : M → M) (x : M) : E →L[ℝ] E :=
  mfderiv I I T x

/-- The bundle generator carries `mfderiv I I T x` (an equality that is `rfl`, since the tangent
spaces are definitionally `E`). -/
theorem bundleDerivativeCocycle_apply (T : M → M) (x : M) :
    bundleDerivativeCocycle I T x = mfderiv I I T x := rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- Iterates of an `MDifferentiable` self-map are `MDifferentiable` (the manifold analogue of
`Differentiable.iterate`). Derived by induction from `MDifferentiable.comp`. -/
theorem mdifferentiable_iterate {T : M → M} (hT : MDifferentiable I I T) :
    ∀ n : ℕ, MDifferentiable I I (T^[n])
  | 0 => by simpa only [Function.iterate_zero] using mdifferentiable_id
  | (n + 1) => by
      rw [Function.iterate_succ]
      exact (mdifferentiable_iterate hT n).comp hT

/-- **Bundle chain-rule cocycle identity** (the one-step recursion). For `MDifferentiable` `T`, the
manifold derivative of `T^[n+1]` factors through the orbit by the manifold chain rule
(`mfderiv_comp`, using `T^[n+1] = T^[n] ∘ T`):
`Dₓ(T^[n+1]) = D_{Tx}(T^[n]) ∘ Dₓ T`. The composition is well-typed because every tangent space is
the same model space `E`. This drives the inductive matrix-cocycle identity below, exactly as
`fderiv_comp` does in the Euclidean `Oseledets.chainRule_cocycle`. -/
theorem bundleDerivativeCocycle_iterate_succ {T : M → M} (hT : MDifferentiable I I T)
    (n : ℕ) (x : M) :
    mfderiv I I (T^[n + 1]) x =
      (mfderiv I I (T^[n]) (T x)).comp (mfderiv I I T x) := by
  have hcomp : T^[n + 1] = T^[n] ∘ T := by
    rw [Function.iterate_succ]
  rw [hcomp, mfderiv_comp x (mdifferentiable_iterate hT n (T x)) (hT x)]

variable (I) in
/-- The **derivative (tangent) cocycle generator** of `T : M → M`: the matrix representing the
framed manifold derivative. This is the bundle generator `bundleDerivativeCocycle I T x : E →L[ℝ] E`
(the endomorphism of the model fibre carrying `mfderiv I I T x`) pushed through the framing algebra
`frameAlg` to a square matrix. It feeds the matrix MET `Oseledets.oseledets_filtration`. -/
def derivativeCocycleManifold (T : M → M) :
    M → Matrix (Fin (modelDim E)) (Fin (modelDim E)) ℝ :=
  fun x => frameAlg E (bundleDerivativeCocycle I T x)

omit [IsManifold I 1 M] in
@[simp] theorem derivativeCocycleManifold_apply (T : M → M) (x : M) :
    derivativeCocycleManifold I T x = frameAlg E (bundleDerivativeCocycle I T x) :=
  rfl

/-- **Matrix chain-rule cocycle identity.** For `MDifferentiable` `T`, the matrix
`cocycle (derivativeCocycleManifold I T) T n x` equals the framed derivative of the `n`-th iterate,
`frameAlg E (mfderiv I I (T^[n]) x)`. Proved by induction, peeling the innermost factor `T` from
both the cocycle recursion (`cocycle_succ`) and the iterate (`bundleDerivativeCocycle_iterate_succ`),
and using that `frameAlg E` is an algebra equivalence (`map_one`, `map_mul`). -/
theorem chainRule_cocycle_manifold {T : M → M} (hT : MDifferentiable I I T) (n : ℕ) (x : M) :
    Oseledets.cocycle (derivativeCocycleManifold I T) T n x =
      frameAlg E (mfderiv I I (T^[n]) x) := by
  induction n generalizing x with
  | zero =>
    rw [Oseledets.cocycle_zero, Function.iterate_zero, mfderiv_id]
    -- `ContinuousLinearMap.id ℝ (TangentSpace I x)` is defeq to `(1 : E →L[ℝ] E)`
    exact (map_one (frameAlg E)).symm
  | succ n ih =>
    rw [Oseledets.cocycle_succ, ih (T x), derivativeCocycleManifold_apply, ← map_mul,
      bundleDerivativeCocycle_iterate_succ hT n x]
    -- the remaining goal `frameAlg E (a * b) = frameAlg E (a ∘L b)` is `rfl`:
    -- multiplication in `E →L[ℝ] E` is composition.
    rfl

/-- The matrix generator has the same L2 operator norm as the manifold derivative:
`‖derivativeCocycleManifold I T x‖ = ‖mfderiv I I T x‖`. This is the bridge identifying the matrix
integrability hypotheses with the genuine `log⁺‖Dₓ T‖` ones (the framing is an isometry). -/
theorem norm_derivativeCocycleManifold (T : M → M) (x : M) :
    ‖derivativeCocycleManifold I T x‖ = ‖mfderiv I I T x‖ := by
  rw [derivativeCocycleManifold_apply]
  exact norm_frameAlg _

/-- If every bundle generator `bundleDerivativeCocycle I T x : E →L[ℝ] E` (the model-fibre
endomorphism carrying `mfderiv I I T x`) is invertible, then the matrix generator's determinant
never vanishes. Invertibility transfers across the framing algebra equivalence `frameAlg`, and a
matrix is a unit iff its determinant is. Using `bundleDerivativeCocycle` (whose declared type is the
homogeneous `E →L[ℝ] E`) makes `IsUnit` — and `IsUnit.map (frameAlg E)` — well-typed; by
`bundleDerivativeCocycle_apply` this is exactly invertibility of `mfderiv I I T x`. -/
theorem det_derivativeCocycleManifold_ne_zero {T : M → M}
    (hiso : ∀ x, IsUnit (bundleDerivativeCocycle I T x)) (x : M) :
    (derivativeCocycleManifold I T x).det ≠ 0 := by
  have hunit : IsUnit (derivativeCocycleManifold I T x) := (hiso x).map (frameAlg E)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- **The sharp analytic core (issue #2 wall, boundaryless C¹ form).**
Measurability of the manifold derivative `x ↦ mfderiv I I T x : E →L[ℝ] E` for a `C¹` self-map `T`
of a **boundaryless** manifold, equipped with its Borel σ-algebra.

This is the single irreducible measurability obligation behind the manifold MET, isolated as a
`sorry` with the sharpest honest hypotheses identified by the feasibility analysis
(`docs/research/frontier/issue2/FEASIBILITY-2026-06-22.md`, Strategy α/γ):

* `[I.Boundaryless]` ⇒ `range I = univ`, so chart-locally
  `mfderiv I I T x = fderiv ℝ (writtenInExtChartAt I I x T) (extChartAt I x x)` (no `fderivWithin`
  over `range I`; Mathlib has **no** `measurable_fderivWithin` over a proper closed set, only over
  `univ` via the unconditional `measurable_fderiv`);
* `ContMDiff I I 1 T` (C¹) ⇒ `ContMDiffAt.mfderiv_const` makes the fixed-base in-coordinates
  representative `inTangentCoordinates I I id T (mfderiv I I T) x₀` *continuous* on a chart
  neighbourhood of each `x₀`;
* `[SigmaCompactSpace M] [SecondCountableTopology H]` ⇒ a countable atlas, so the chart-local
  measurable representatives glue (via `measurable_of_measurable_on_countable_cover`) into a global
  measurable map.

The remaining gap is the *recovery* step: passing from the (continuous, hence measurable) fixed-base
representative `inTangentCoordinates … x₀` back to `mfderiv I I T x` itself requires conjugating by
two `tangentCoordChange` factors whose **chart index moves with the base point** — a
moving-trivialization-index continuity that Mathlib packages only *inside* `inTangentCoordinates`
(via the smooth-tangent-bundle machinery), never as an isolable factor. Closing it is the
~250-400-line chart-algebra telescoping flagged at ~70% odds in the report. It is recorded here as a
single sharp, fully-typed `sorry` — strictly stronger hypotheses than the original opaque leaf, and
faithful to the literature (Filip §2.2.2; Arnold, *RDS*, Ch. 4). -/
theorem measurable_mfderiv_of_contMDiff_boundaryless
    [I.Boundaryless] [LocallyConstantChartAt H M] [MeasurableSpace M] [BorelSpace M]
    [SigmaCompactSpace M] [SecondCountableTopology H] {T : M → M}
    (hT : ContMDiff I I 1 T) :
    Measurable (bundleDerivativeCocycle I T) :=
  -- `bundleDerivativeCocycle I T x = mfderiv I I T x = mfderivHom I T x` (all `E →L[ℝ] E`, by `rfl`).
  -- The full chart-glue measurability is in `Frontier.Issue2.measurable_mfderivHom`; the only
  -- residual is the moving-trivialization-index coordinate-change continuity isolated there.
  measurable_mfderivHom hT

/-- **Measurability of the manifold derivative cocycle generator — THE WALL.**

To feed the matrix MET, the generator `x ↦ derivativeCocycleManifold I T x` must be measurable for
the Borel σ-algebra of `M`. Since `frameAlg E` and the matrix-entry projections are continuous, this
reduces to measurability of the *manifold derivative* `x ↦ mfderiv I I T x` as a map
`M → (E →L[ℝ] E)` (the manifold analogue of `measurable_fderiv`). Under the **honest boundaryless /
C¹ / σ-compact** hypotheses it is exactly the sharp core
`measurable_mfderiv_of_contMDiff_boundaryless`: `bundleDerivativeCocycle I T x` is, by definition,
`mfderiv I I T x`. -/
theorem measurable_bundleDerivativeCocycle
    [I.Boundaryless] [LocallyConstantChartAt H M] [MeasurableSpace M] [BorelSpace M]
    [SigmaCompactSpace M] [SecondCountableTopology H] {T : M → M}
    (hT : ContMDiff I I 1 T) :
    Measurable (bundleDerivativeCocycle I T) :=
  measurable_mfderiv_of_contMDiff_boundaryless hT

/-- The framing `frameAlg E` is measurable into the entrywise (Pi) measurable structure on matrices:
each matrix entry `(frameAlg E L) i j` is a continuous (`ℝ`-linear, finite-dimensional) function of
`L`, hence measurable. (We argue entrywise because the matrix carries the Pi measurable structure,
which is not registered as the Borel σ-algebra of its norm topology, so `Continuous.measurable` does
not apply directly.) -/
theorem measurable_frameAlg : Measurable (frameAlg E) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  -- the `(i, j)` entry map `L ↦ (frameAlg E L) i j` is continuous (norm topology), hence measurable
  have hcont : Continuous fun L : E →L[ℝ] E => frameAlg E L i j :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_frameAlg)
  exact hcont.measurable

/-- Measurability of the matrix generator follows from the bundle-derivative measurability (proved
under `[LocallyConstantChartAt H M]`) by measurability of the framing `frameAlg E`. Stated
separately so the dependence is explicit; the matrix MET takes this as the hypothesis `hAmeas`. -/
theorem measurable_derivativeCocycleManifold
    [I.Boundaryless] [LocallyConstantChartAt H M] [MeasurableSpace M] [BorelSpace M]
    [SigmaCompactSpace M] [SecondCountableTopology H] {T : M → M}
    (hT : ContMDiff I I 1 T) :
    Measurable (derivativeCocycleManifold I T) :=
  (measurable_frameAlg (E := E)).comp (measurable_bundleDerivativeCocycle hT)

/-- **Oseledets multiplicative ergodic theorem for the derivative cocycle of a manifold map.**

Let `T` be an ergodic measure-preserving `MDifferentiable` self-map of a finite-dimensional manifold
`M` (modelled on an inner-product space `E`), with everywhere-nonsingular tangent cocycle and
integrable log-derivative data `log⁺‖Dₓ T‖, log⁺‖(Dₓ T)⁻¹‖ ∈ L¹(μ)`. Then there is an
`A`-equivariant Lyapunov filtration of the (framed) tangent space with the exact growth
`(1/n) log‖D(T^[n]) v‖ → λᵢ` along each stratum, for `A := derivativeCocycleManifold I T`.

The integrability hypotheses are stated for the matrix generator; by `norm_derivativeCocycleManifold`
these are exactly the genuine `log⁺‖mfderiv‖` (and inverse) conditions. The first conjunct records
that the cocycle is the genuine tangent cocycle: each factor
`cocycle (derivativeCocycleManifold I T) T n x` equals `frameAlg E (mfderiv I I (T^[n]) x)`.

The measurability hypothesis `hAmeas` is exactly what `measurable_derivativeCocycleManifold` would
supply once the manifold-derivative measurability wall (see there) is discharged; taking it as a
hypothesis here isolates that single Mathlib-scale gap and keeps **this** theorem `sorry`-free. -/
theorem oseledets_filtration_derivativeCocycleManifold
    [MeasurableSpace M] {μ : Measure M} [IsProbabilityMeasure μ] {T : M → M}
    (hT : Ergodic T μ) (hdiff : MDifferentiable I I T)
    (hdet : ∀ x, (derivativeCocycleManifold I T x).det ≠ 0)
    (hAmeas : Measurable (derivativeCocycleManifold I T))
    (hint : Oseledets.IntegrableLogNorm (derivativeCocycleManifold I T) μ)
    (hint' : Oseledets.IntegrableLogNorm (fun x => (derivativeCocycleManifold I T x)⁻¹) μ) :
    (∀ (n : ℕ) (x : M),
        Oseledets.cocycle (derivativeCocycleManifold I T) T n x
          = frameAlg E (mfderiv I I (T^[n]) x)) ∧
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) →
        M → Submodule ℝ (EuclideanSpace ℝ (Fin (modelDim E)))),
      StrictAnti lam ∧
      (∀ i, Oseledets.MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (derivativeCocycleManifold I T x)).toLinearMap
            (V i x) = V i (T x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin (modelDim E)))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log
                  ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (Oseledets.cocycle (derivativeCocycleManifold I T) T n x) v‖)
              atTop (𝓝 (lam i))) :=
  ⟨fun n x => chainRule_cocycle_manifold hdiff n x,
    Oseledets.oseledets_filtration hT (derivativeCocycleManifold I T) hdet hAmeas hint hint'⟩

end

end Frontier.Issue2
