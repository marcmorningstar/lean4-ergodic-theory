/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ForwardMeasurable
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# From a measurable subspace frame to a measurable orthogonal projector

For a measurably-varying family of subspaces `V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))`
the multiplicative ergodic theorem (in its measurable / non-invertible form) needs the
**orthogonal-projection matrix** `x ↦ orthProjMatrix (V x)` to be measurable. This file
delivers the *finite-dimensional constant-rank* route to that fact: starting from a
measurable family of vectors that is, for each `x`, an **orthonormal basis** of `V x`, the
projector is the (manifestly measurable) Gram matrix of the frame.

This is the converter on which the unconditional singular Oseledets filtration ("issue #6")
turns: the measurable graph of the eventual-kernel family
(`Oseledets.measurableSet_graph_eventualKer`) plus constant kernel dimension yields, by a
finite measurable stratification + Gram–Schmidt, exactly such a measurable orthonormal frame.
The clean, fully `sorry`-free heart of the converter — *measurable orthonormal frame ⇒
measurable projector* — is `measurable_orthProjMatrix_of_orthonormalFrame`. The remaining,
genuinely measure-theoretic, step (a measurable orthonormal frame **exists** for a
measurable-graph constant-rank family) is the Kuratowski–Ryll-Nardzewski / Castaing content
that Mathlib does not yet provide; it is isolated in
`exists_measurable_orthonormalFrame_of_measurableGraph` and flagged there.

## Main definitions

* `Oseledets.IsMeasurableOrthonormalFrame`: a family `e : X → Fin m → EuclideanSpace ℝ (Fin d)`
  is a measurable orthonormal frame for `V` when each component map is measurable and, for
  every `x`, `e x` is orthonormal and spans `V x`.

## Main results

* `Oseledets.starProjection_eq_sum_inner_smul_of_span`: for an orthonormal family `e` whose
  span is `K`, the orthogonal projection onto `K` is `v ↦ ∑ i, ⟪e i, v⟫ • e i`.
* `Oseledets.orthProjMatrix_entry_eq_sum`: the `(a, b)` entry of `orthProjMatrix K` equals
  `∑ i, e i a * e i b` for such a frame — the Gram (outer-product sum) formula.
* `Oseledets.measurable_orthProjMatrix_of_orthonormalFrame`: **the converter's core** —
  a measurable orthonormal frame for `V` makes `x ↦ orthProjMatrix (V x)` measurable
  (hence `MeasurableSubspace V`).
* `Oseledets.measurable_gramSchmidt`, `Oseledets.measurable_gramSchmidtNormed`: Gram–Schmidt
  is measurable in its input frame (`sorry`-free).
* `Oseledets.isMeasurableOrthonormalFrame_gramSchmidtNormed`: a measurable, pointwise
  independent, pointwise spanning frame orthonormalises to a measurable orthonormal frame
  (`sorry`-free) — this discharges the orthonormalisation half of the converter.
* `Oseledets.measurableSubspace_of_measurableGraph_constDim`: **the target** — a measurable
  graph together with constant finite rank gives a measurable projector. It is reduced to the
  core via the frame-existence lemma below.

## The isolated measure-theoretic gap

* `Oseledets.exists_measurable_independentSpanningFrame_of_measurableGraph` (`sorry`, BLOCKED):
  existence of a *measurable, pointwise linearly-independent, pointwise spanning* frame from a
  measurable graph at constant rank. This is the **only** remaining gap: orthonormalisation is
  proved `sorry`-free above, so what is missing is just the finite-dimensional Castaing
  representation — countably many measurable selections of the graph slices, dense in each
  fibre, plus a measurable size-`m`-independent-subset stratification. Mathlib lacks both the
  measurable-selection (Kuratowski–Ryll-Nardzewski) theorem and a `MeasurableSpace` structure on
  `Submodule`/`Grassmannian`, so the dense-measurable-selection step has no Mathlib API to
  invoke. `Oseledets.exists_measurable_orthonormalFrame_of_measurableGraph` and the target
  inherit `sorry` from it; everything else in the file is `sorry`-free.

Literature: C. González-Tokman, A. Quas, *A semi-invertible operator Oseledets theorem*
(ETDS 2014), Appendix B (measurable Grassmannian, nice bases) and G. Froyland, S. Lloyd,
A. Quas, *Lyapunov exponents and the semi-invertible MET* (ETDS 2010), Lemma 6 (projection
measurability), adapted to the elementary finite-dimensional Euclidean setting.
-/

open scoped Matrix
open Submodule

namespace Oseledets

variable {d : ℕ}

section Frame

variable {m : ℕ} {K : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
  {e : Fin m → EuclideanSpace ℝ (Fin d)}

/-- **Projection via an orthonormal frame.** If `e` is an orthonormal family in
`EuclideanSpace ℝ (Fin d)` whose span is `K`, then the orthogonal projection onto `K` sends
`v` to `∑ i, ⟪e i, v⟫ • e i`. We verify the defining property of `starProjection`: the
candidate lies in `K` and `v` minus it is orthogonal to every spanning vector `e j`. -/
theorem starProjection_eq_sum_inner_smul_of_span
    (hon : Orthonormal ℝ e) (hspan : span ℝ (Set.range e) = K)
    (v : EuclideanSpace ℝ (Fin d)) :
    K.starProjection v = ∑ i, (inner ℝ (e i) v) • e i := by
  -- The candidate point `p ∈ K` and its orthogonality characterise the projection.
  set p : EuclideanSpace ℝ (Fin d) := ∑ i, (inner ℝ (e i) v) • e i with hp
  have hpK : p ∈ K := by
    rw [← hspan]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- It suffices to check orthogonality of `v - p` against each `e j` (these span `K`).
  refine eq_starProjection_of_mem_of_inner_eq_zero hpK ?_
  -- Reduce `∀ w ∈ K, ⟪v - p, w⟫ = 0` to the spanning generators `e j`.
  rw [← hspan]
  refine fun w hw => Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, rfl⟩
    -- `⟪v - p, e j⟫ = ⟪v, e j⟫ - ∑ i ⟪e i, v⟫ ⟪e i, e j⟫ = ⟪v, e j⟫ - ⟪e j, v⟫ = 0`.
    rw [inner_sub_left, hp, sum_inner]
    have hδ : ∀ i, (inner ℝ ((inner ℝ (e i) v) • e i) (e j))
        = (inner ℝ (e i) v) * (if i = j then 1 else 0) := by
      intro i
      rw [inner_smul_left, RCLike.conj_to_real, (orthonormal_iff_ite.mp hon) i j]
    simp only [hδ, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j (fun i => inner ℝ (e i) v)]
    simp only [Finset.mem_univ, if_true]
    rw [real_inner_comm (e j) v, sub_self]
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro a x _ hx
    rw [inner_smul_right, hx, mul_zero]

/-- **Gram (outer-product) formula for the projector matrix.** For an orthonormal frame `e`
spanning `K`, the `(a, b)` entry of `orthProjMatrix K` equals `∑ i, e i a * e i b`. Using
`orthProjMatrix K a b = ⟪single a, starProjection K (single b)⟫` and the frame projection
formula, the coordinate identities `⟪single a, w⟫ = w a` and `⟪e i, single b⟫ = e i b`
collapse the sum to the stated real bilinear form. -/
theorem orthProjMatrix_entry_eq_sum
    (hon : Orthonormal ℝ e) (hspan : span ℝ (Set.range e) = K) (a b : Fin d) :
    orthProjMatrix K a b = ∑ i, e i a * e i b := by
  -- `toEuclideanCLM (orthProjMatrix K) = starProjection K`, so the entry is an inner product.
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℝ) (orthProjMatrix K) = K.starProjection := by
    rw [orthProjMatrix, StarAlgEquiv.apply_symm_apply]
  have hentry : orthProjMatrix K a b
      = inner ℝ (EuclideanSpace.single a (1 : ℝ))
          (K.starProjection (EuclideanSpace.single b (1 : ℝ))) := by
    rw [← hclm, Matrix.inner_toEuclideanCLM]
    -- `single a 1 ⬝ᵥ M *ᵥ single b 1 = M a b`.
    simp [EuclideanSpace.single, dotProduct, Matrix.mulVec, PiLp.single_apply,
      Finset.sum_ite_eq, eq_comm]
  rw [hentry, starProjection_eq_sum_inner_smul_of_span hon hspan, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp only [map_one, one_mul, RCLike.conj_to_real]
  ring

end Frame

variable {X : Type*} [MeasurableSpace X]

/-- A family `e : X → Fin m → EuclideanSpace ℝ (Fin d)` is a **measurable orthonormal frame**
for `V` when each coordinate map `x ↦ e x i` is measurable and, for every `x`, the tuple
`e x` is orthonormal and spans `V x`. This is the structured input consumed by the projector
converter `measurable_orthProjMatrix_of_orthonormalFrame`. -/
structure IsMeasurableOrthonormalFrame {m : ℕ}
    (V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (e : X → Fin m → EuclideanSpace ℝ (Fin d)) : Prop where
  /-- Each frame component varies measurably in `x`. -/
  measurable : ∀ i, Measurable fun x => e x i
  /-- The frame is orthonormal at every point. -/
  orthonormal : ∀ x, Orthonormal ℝ (e x)
  /-- The frame spans the assigned subspace at every point. -/
  span : ∀ x, span ℝ (Set.range (e x)) = V x

/-- **The converter's sorry-free core.** A measurable orthonormal frame for `V` makes the
orthogonal-projection matrix `x ↦ orthProjMatrix (V x)` measurable. Each matrix entry is the
finite sum `∑ i, e x i a * e x i b` (`orthProjMatrix_entry_eq_sum`), a finite sum of products
of measurable real functions, hence measurable; the matrix measurable structure is entrywise
(`Oseledets.instMeasurableSpaceMatrix`). -/
theorem measurable_orthProjMatrix_of_orthonormalFrame {m : ℕ}
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {e : X → Fin m → EuclideanSpace ℝ (Fin d)} (hframe : IsMeasurableOrthonormalFrame V e) :
    Measurable fun x => orthProjMatrix (V x) := by
  -- Reduce matrix measurability to entrywise measurability.
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
  -- Rewrite the entry as the measurable Gram sum.
  have hentry : (fun x => orthProjMatrix (V x) a b)
      = fun x => ∑ i, e x i a * e x i b := by
    funext x
    exact orthProjMatrix_entry_eq_sum (hframe.orthonormal x) (hframe.span x) a b
  rw [hentry]
  -- A finite sum of products of measurable coordinate maps is measurable.
  -- The coordinate projection `w ↦ w c` is continuous on `EuclideanSpace`, hence measurable.
  have hcoord : ∀ c : Fin d,
      Measurable fun w : EuclideanSpace ℝ (Fin d) => w c := fun c =>
    (PiLp.continuous_apply 2 (β := fun _ : Fin d => ℝ) c).measurable
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((hcoord a).comp (hframe.measurable i)).mul ((hcoord b).comp (hframe.measurable i))

/-- A measurable orthonormal frame witnesses `MeasurableSubspace V`. -/
theorem measurableSubspace_of_orthonormalFrame {m : ℕ}
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {e : X → Fin m → EuclideanSpace ℝ (Fin d)} (hframe : IsMeasurableOrthonormalFrame V e) :
    MeasurableSubspace V :=
  measurable_orthProjMatrix_of_orthonormalFrame hframe

/-! ### Measurable Gram–Schmidt: orthonormalising a measurable independent frame -/

section MeasurableGramSchmidt

open InnerProductSpace

variable {m : ℕ} {f : X → Fin m → EuclideanSpace ℝ (Fin d)}

/-- **`gramSchmidt` is measurable in the frame.** For a measurable frame `f`, each
Gram–Schmidt output `x ↦ gramSchmidt ℝ (f x) n` is measurable. Proof by well-founded (`<`)
induction on `n : Fin m` using the recursion `gramSchmidt f n = f n - ∑_{i < n} (⟪gs i, f n⟫ /
‖gs i‖²) • gs i` (`gramSchmidt_def''`): each summand is built from the (inductively measurable)
earlier outputs by measurable inner products, real inversion (measurable everywhere, junk value
at 0), and scalar multiplication. -/
theorem measurable_gramSchmidt (hf : ∀ i, Measurable fun x => f x i) (n : Fin m) :
    Measurable fun x => gramSchmidt ℝ (f x) n := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    -- Rewrite the `n`-th output via the explicit normalised recursion.
    have hrec : (fun x => gramSchmidt ℝ (f x) n)
        = fun x => f x n - ∑ i ∈ Finset.Iio n,
          ((inner ℝ (gramSchmidt ℝ (f x) i) (f x n)) /
            (‖gramSchmidt ℝ (f x) i‖ : ℝ) ^ 2) • gramSchmidt ℝ (f x) i := by
      funext x
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (f x) n).symm
    rw [hrec]
    refine (hf n).sub (Finset.measurable_sum _ fun i hi => ?_)
    -- `i < n`, so `gramSchmidt ℝ (· ) i` is measurable by the induction hypothesis.
    have hi' : i < n := Finset.mem_Iio.mp hi
    have hgsi : Measurable fun x => gramSchmidt ℝ (f x) i := ih i hi'
    refine Measurable.smul ?_ hgsi
    exact (hgsi.inner (hf n)).div ((hgsi.norm).pow_const 2)

/-- **`gramSchmidtNormed` is measurable in the frame.** Immediate from `measurable_gramSchmidt`:
`gramSchmidtNormed ℝ f n = ‖gramSchmidt ℝ f n‖⁻¹ • gramSchmidt ℝ f n`, a measurable scalar
(real inversion of a measurable norm) times a measurable vector. -/
theorem measurable_gramSchmidtNormed (hf : ∀ i, Measurable fun x => f x i) (n : Fin m) :
    Measurable fun x => gramSchmidtNormed ℝ (f x) n := by
  simp only [gramSchmidtNormed]
  have hgs : Measurable fun x => gramSchmidt ℝ (f x) n := measurable_gramSchmidt hf n
  exact Measurable.smul (by simpa using hgs.norm.inv) hgs

end MeasurableGramSchmidt

/-! ### From a measurable independent spanning frame to an orthonormal frame -/

open InnerProductSpace

variable {m : ℕ}

/-- **Orthonormalising a measurable independent spanning frame.** If `f : X → Fin m →
EuclideanSpace ℝ (Fin d)` is a measurable family that is, for every `x`, linearly independent
and spans `V x`, then its Gram–Schmidt normalisation is a measurable orthonormal frame for `V`.
This discharges sub-steps (2)–(3) of the converter (orthonormalisation) entirely
`sorry`-free, leaving only the production of the independent spanning frame itself (the
Castaing/KRN selection, sub-step (1)). -/
theorem isMeasurableOrthonormalFrame_gramSchmidtNormed
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {f : X → Fin m → EuclideanSpace ℝ (Fin d)} (hf : ∀ i, Measurable fun x => f x i)
    (hindep : ∀ x, LinearIndependent ℝ (f x)) (hspan : ∀ x, span ℝ (Set.range (f x)) = V x) :
    IsMeasurableOrthonormalFrame V (fun x => gramSchmidtNormed ℝ (f x)) where
  measurable i := measurable_gramSchmidtNormed hf i
  orthonormal x := gramSchmidtNormed_orthonormal (hindep x)
  span x := by
    rw [span_gramSchmidtNormed_range, span_gramSchmidt, hspan]

/-! ### The measure-theoretic gap: from a measurable graph to a measurable frame -/

/-- **Existence of a measurable orthonormal frame from a measurable graph at constant rank.**
A measurable graph `{(x, v) | v ∈ V x}` together with constant finite dimension `m` yields a
measurable orthonormal frame `e` for `V`.

**This is the single genuinely measure-theoretic gap of the converter and is left `sorry`
(BLOCKED).** This is now the *only* gap of the converter: orthonormalisation has been split off
and proved `sorry`-free (`measurable_gramSchmidt`, `measurable_gramSchmidtNormed`,
`isMeasurableOrthonormalFrame_gramSchmidtNormed`), so all that remains is to produce — from the
bare measurable graph at constant rank — a **measurable, pointwise linearly-independent,
pointwise spanning** frame `f : X → Fin m → EuclideanSpace ℝ (Fin d)`. The finite-dimensional
construction is standard but its single essential ingredient has no Mathlib foothold:

* **Castaing representation (the crux).** One needs countably many measurable selections
  `wₖ : X → EuclideanSpace ℝ (Fin d)` with `wₖ x ∈ V x` for all `x` and `{wₖ x}ₖ` *dense*
  (equivalently here, spanning, since `V x` is finite-dimensional) in `V x`. This is the content
  of the **Kuratowski–Ryll-Nardzewski measurable selection theorem** for a closed-valued
  measurable multifunction into a Polish space. Mathlib has **no** measurable selection theorem of
  this form (no KRN, no Castaing representation, and no `MeasurableSpace` on `Submodule` /
  `Grassmannian`), so there is no lemma to invoke; proving it from scratch is itself a
  Mathlib-scale development (the `iSup`/graph machinery this file sits above was built as its first
  step). Once the `wₖ` are in hand, choosing at each `x` the lexicographically-first size-`m`
  subset on which the selections are independent (a measurable `Gram ≠ 0` condition; constant rank
  `m` guarantees one exists) and gluing across these finitely-many measurable strata with
  `Measurable.piecewise` yields the required independent spanning frame `f`. That gluing is
  elementary and uses only existing Mathlib API, so the genuine blocker is exactly the bullet
  above.

Literature: González-Tokman–Quas (ETDS 2014), Appendix B (separability of the Grassmannian,
nice/`2`-nice bases, `(F, B_G(X))`-measurable subspace maps) and the Castaing–Valadier theory of
measurable multifunctions. -/
theorem exists_measurable_independentSpanningFrame_of_measurableGraph
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {m : ℕ}
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    ∃ f : X → Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, Measurable fun x => f x i) ∧ (∀ x, LinearIndependent ℝ (f x)) ∧
        (∀ x, span ℝ (Set.range (f x)) = V x) := by
  sorry -- BLOCKED: finite-dim Castaing representation (KRN measurable selection) absent in
        -- Mathlib; see the docstring — this is the *only* remaining gap (orthonormalisation is
        -- proved sorry-free downstream).

/-- **Existence of a measurable orthonormal frame from a measurable graph at constant rank.**
Combines the (blocked) independent-spanning-frame existence with `sorry`-free Gram–Schmidt
orthonormalisation (`isMeasurableOrthonormalFrame_gramSchmidtNormed`). The dependence on `sorry`
is inherited solely from `exists_measurable_independentSpanningFrame_of_measurableGraph`. -/
theorem exists_measurable_orthonormalFrame_of_measurableGraph
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {m : ℕ}
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    ∃ e : X → Fin m → EuclideanSpace ℝ (Fin d), IsMeasurableOrthonormalFrame V e := by
  obtain ⟨f, hf, hindep, hspan⟩ :=
    exists_measurable_independentSpanningFrame_of_measurableGraph hgraph hdim
  exact ⟨_, isMeasurableOrthonormalFrame_gramSchmidtNormed hf hindep hspan⟩

/-- **The target converter (constant rank).** A measurable graph together with constant finite
dimension `m` makes the orthogonal-projection matrix `x ↦ orthProjMatrix (V x)` measurable.
The proof extracts a measurable orthonormal frame from the graph
(`exists_measurable_orthonormalFrame_of_measurableGraph`) and feeds it to the `sorry`-free core
`measurable_orthProjMatrix_of_orthonormalFrame`. Consequently the inherited dependence on
`sorry` is confined to the one Castaing/KRN measurable-selection gap. -/
theorem measurableSubspace_of_measurableGraph_constDim
    {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {m : ℕ} [NeZero d]
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    Measurable (fun x => orthProjMatrix (V x)) := by
  obtain ⟨e, hframe⟩ := exists_measurable_orthonormalFrame_of_measurableGraph hgraph hdim
  exact measurable_orthProjMatrix_of_orthonormalFrame hframe

end Oseledets
