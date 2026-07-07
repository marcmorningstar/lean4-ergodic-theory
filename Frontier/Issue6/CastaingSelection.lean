/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Frontier.Issue6.MeasurableGraphToProjector
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# A measurable independent spanning frame from a measurable subspace family

For a measurably-varying family of subspaces `V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))`
of *constant finite rank* `m`, the singular ("issue #6") multiplicative ergodic theorem needs a
single **measurable independent spanning frame** `f : X → Fin m → EuclideanSpace ℝ (Fin d)` —
i.e. a measurable family of `m`-tuples that is, at every `x`, linearly independent and spans
`V x`. Composed with the `sorry`-free Gram–Schmidt orthonormalisation of
`Frontier.Issue6.MeasurableGraphToProjector`, this delivers the measurable orthogonal
projector, hence `MeasurableSubspace V`.

## The clean reduction used here

The classical route to the frame is the Kuratowski–Ryll-Nardzewski / Castaing measurable
selection theorem for a closed-valued measurable multifunction into a Polish space. In the
**finite-dimensional Hilbert** setting `EuclideanSpace ℝ (Fin d)` there is a far shorter and
fully elementary route that bypasses measurable selection entirely, isolating the *single*
genuinely measure-theoretic ingredient.

The key observation is a **polarisation identity for the orthogonal projector**. Writing
`P x := (V x).starProjection` for the orthogonal projection onto `V x` (every subspace of a
finite-dimensional space is complete, hence has an orthogonal projection), and `e_a` for the
standard basis vector `EuclideanSpace.single a 1`, one has, because `P x` is self-adjoint and
idempotent,
`⟪e_b, P x e_a⟫ = ⟪P x e_b, P x e_a⟫`,
so every coordinate of the projected basis vector `P x e_a` is an inner product of two
projections. Inner products of projections are, by the polarisation identity, real combinations
of the squared norms `‖P x c‖²`, and
`‖P x c‖² = ‖c‖² − infDist c (V x)²`
(Pythagoras: `c = P x c + (c − P x c)` is an orthogonal decomposition and `infDist c (V x)`
realises `‖c − P x c‖`). Hence **every coordinate of every projected basis vector `P x e_a` is a
measurable function of the scalar maps `x ↦ infDist c (V x)`** for finitely many fixed `c`.

The `d` projected basis vectors `P x e_0, …, P x e_{d-1}` lie in `V x` and span it (orthogonal
projection is surjective onto its range `V x`, and the `e_a` span the ambient space). From these
`d` measurable spanning vectors a measurable independent size-`m` subframe is extracted by a
finite measurable stratification over the `Finset.powersetCard m` of index subsets on which the
selection is independent — a `Gram`-determinant `≠ 0` condition; constant rank `m` guarantees one
such subset exists at every `x`.

## The single measure-theoretic input

Everything above is `sorry`-free **given** the hypothesis

* `MeasurableInfDist V`: for every `c`, the map `x ↦ infDist c (V x)` is measurable.

This is exactly **weak measurability** of the multifunction `x ↦ V x` (since for a ball
`{x | (V x) ∩ ball c r ≠ ∅} = {x | infDist c (V x) < r}`), the standing hypothesis of the
Kuratowski–Ryll-Nardzewski theorem. The remaining gap of the converter is therefore reduced to
the single implication **measurable graph ⟹ `MeasurableInfDist`**, which for the
subspace-valued, constant-rank multifunction is the projection-of-a-Borel-set-with-σ-compact-
sections fact (Arsenin–Kunugui / Saint-Raymond), absent from Mathlib. It is isolated as
`measurableInfDist_of_measurableGraph` and is the *only* place a `sorry` remains; every algebraic
and measurable-combination step is proved.

## Main definitions

* `Frontier.MeasurableInfDist`: weak measurability of `V`, i.e. `x ↦ infDist c (V x)` measurable
  for every `c`.

## Main results

* `Frontier.measurable_starProjection_apply`: from `MeasurableInfDist`, `x ↦ (V x).starProjection u`
  is measurable for each fixed `u` (`sorry`-free).
* `Frontier.exists_measurable_independentSpanningFrame_of_measurableInfDist`: from
  `MeasurableInfDist` plus constant rank `m`, a measurable independent spanning frame exists
  (`sorry`-free) — the abstract KRN/Castaing deliverable.
* `ErgodicTheory.exists_measurable_independentSpanningFrame_of_measurableGraph`: the target verbatim,
  obtained by feeding the (isolated, `sorry`) `measurableInfDist_of_measurableGraph` into the
  previous result.

Literature: Kuratowski–Ryll-Nardzewski, *A general theorem on selectors* (1965); Castaing–Valadier,
*Convex Analysis and Measurable Multifunctions*; C. González-Tokman, A. Quas, *A semi-invertible
operator Oseledets theorem* (ETDS 2014), Appendix B.
-/

open scoped Matrix
open Metric MeasureTheory Submodule

namespace Frontier

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- **Weak measurability of a subspace-valued multifunction.** The family
`V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))` is `MeasurableInfDist` when, for every fixed
point `c`, the distance map `x ↦ infDist c (V x)` is measurable. For a multifunction into a
metric space this is equivalent to the Kuratowski–Ryll-Nardzewski weak-measurability condition
(`{x | V x ∩ ball c r ≠ ∅}` measurable for all `c`, `r`). -/
def MeasurableInfDist (V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin d), Measurable fun x => infDist c (V x)

/-! ### Algebraic core: projector coordinates as distance combinations -/

section ProjectionAlgebra

variable (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))

/-- **Distance to a subspace is the norm of the projection residual.** For a closed (here:
finite-dimensional, hence complete) subspace `K`, `infDist c K = ‖c − K.starProjection c‖`. The
orthogonal projection realises the infimum `⨅ x : K, ‖c − x‖` (`starProjection_minimal`), and
`infDist` is exactly that infimum (`infDist_eq_iInf`, with `dist = ‖· − ·‖`). -/
theorem infDist_eq_norm_sub_starProjection (c : EuclideanSpace ℝ (Fin d)) :
    infDist c (K : Set (EuclideanSpace ℝ (Fin d))) = ‖c - K.starProjection c‖ := by
  rw [starProjection_minimal, infDist_eq_iInf]
  simp_rw [dist_eq_norm]
  rfl

/-- **Pythagoras for the projector.** `‖K.starProjection c‖² = ‖c‖² − infDist c K ²`. The
orthogonal decomposition `c = K.starProjection c + (c − K.starProjection c)` has orthogonal
summands, so `‖c‖² = ‖K.starProjection c‖² + ‖c − K.starProjection c‖²`, and the residual norm
is `infDist c K` by `infDist_eq_norm_sub_starProjection`. -/
theorem norm_starProjection_sq (c : EuclideanSpace ℝ (Fin d)) :
    ‖K.starProjection c‖ ^ 2
      = ‖c‖ ^ 2 - infDist c (K : Set (EuclideanSpace ℝ (Fin d))) ^ 2 := by
  have horth : inner ℝ (K.starProjection c) (c - K.starProjection c) = (0 : ℝ) := by
    rw [real_inner_comm]
    exact K.starProjection_inner_eq_zero c (K.starProjection c) (K.starProjection_apply_mem c)
  have hsplit : c = K.starProjection c + (c - K.starProjection c) := by abel
  have hpyth : ‖c‖ ^ 2 = ‖K.starProjection c‖ ^ 2 + ‖c - K.starProjection c‖ ^ 2 := by
    have hcc : ‖c‖ ^ 2 = ‖K.starProjection c + (c - K.starProjection c)‖ ^ 2 := by
      rw [← hsplit]
    rw [hcc, ← real_inner_self_eq_norm_sq, inner_add_add_self, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, horth, real_inner_comm, horth]
    ring
  rw [infDist_eq_norm_sub_starProjection]; linarith

/-- **A projector coordinate is a distance combination.** The `b`-th coordinate of the projected
vector `K.starProjection u` equals
`½[(‖single b‖² − infDist (single b) K²) + (‖u‖² − infDist u K²) −
   (‖single b − u‖² − infDist (single b − u) K²)]`.
Self-adjointness and idempotency give `(K.starProjection u) b = ⟪K.starProjection (single b),
K.starProjection u⟫`; polarisation expands the inner product into squared norms of projections;
each squared norm is `‖·‖² − infDist · K²` by `norm_starProjection_sq` (with
`K.starProjection (single b) − K.starProjection u = K.starProjection (single b − u)`). -/
theorem starProjection_apply_coord (u : EuclideanSpace ℝ (Fin d)) (b : Fin d) :
    (K.starProjection u) b
      = ((‖(EuclideanSpace.single b (1 : ℝ))‖ ^ 2
            - infDist (EuclideanSpace.single b (1 : ℝ)) (K : Set _) ^ 2)
          + (‖u‖ ^ 2 - infDist u (K : Set _) ^ 2)
          - (‖(EuclideanSpace.single b (1 : ℝ)) - u‖ ^ 2
            - infDist ((EuclideanSpace.single b (1 : ℝ)) - u) (K : Set _) ^ 2)) / 2 := by
  set s : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single b (1 : ℝ) with hs
  -- Coordinate as an inner product of projections (self-adjoint + idempotent).
  have hcoord : (K.starProjection u) b
      = inner ℝ (K.starProjection s) (K.starProjection u) := by
    rw [inner_starProjection_left_eq_right,
      starProjection_eq_self_iff.mpr (K.starProjection_apply_mem u), hs,
      EuclideanSpace.inner_single_left]
    simp
  -- Polarisation of the real inner product.
  have hpolar : inner ℝ (K.starProjection s) (K.starProjection u)
      = (‖K.starProjection s‖ ^ 2 + ‖K.starProjection u‖ ^ 2
          - ‖K.starProjection s - K.starProjection u‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]; ring
  rw [hcoord, hpolar, ← map_sub, norm_starProjection_sq, norm_starProjection_sq,
    norm_starProjection_sq]

end ProjectionAlgebra

/-! ### Measurability of the projected basis vectors -/

section Measurable

variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-- **A fixed vector projects measurably.** Under `MeasurableInfDist V`, for each fixed `u` the
map `x ↦ (V x).starProjection u` is measurable. Each coordinate `b` of the projected vector is,
by `starProjection_apply_coord`, a fixed real-arithmetic combination of the three measurable
scalar maps `x ↦ infDist c (V x)` (for `c ∈ {single b, u, single b − u}`); a finite arithmetic
combination of measurable real functions is measurable, and measurability into
`EuclideanSpace ℝ (Fin d)` is checked coordinatewise. -/
theorem measurable_starProjection_apply (hV : MeasurableInfDist V)
    (u : EuclideanSpace ℝ (Fin d)) :
    Measurable fun x => (V x).starProjection u := by
  -- It suffices to show the underlying `Fin d → ℝ` map is measurable: `toLp 2` is continuous,
  -- and `toLp 2 ∘ ofLp = id` on `EuclideanSpace`.
  suffices h : Measurable fun x => (WithLp.ofLp ((V x).starProjection u) : Fin d → ℝ) by
    simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp h
  refine measurable_pi_iff.2 fun b => ?_
  -- Rewrite the coordinate as the distance combination.
  have hcoord : (fun x => (WithLp.ofLp ((V x).starProjection u) : Fin d → ℝ) b)
      = fun x => ((‖(EuclideanSpace.single b (1 : ℝ))‖ ^ 2
            - infDist (EuclideanSpace.single b (1 : ℝ)) (V x : Set _) ^ 2)
          + (‖u‖ ^ 2 - infDist u (V x : Set _) ^ 2)
          - (‖(EuclideanSpace.single b (1 : ℝ)) - u‖ ^ 2
            - infDist ((EuclideanSpace.single b (1 : ℝ)) - u) (V x : Set _) ^ 2)) / 2 := by
    funext x; exact starProjection_apply_coord (V x) u b
  rw [hcoord]
  -- Each `infDist c (V ·)` is measurable; constants and arithmetic preserve measurability.
  exact ((((measurable_const.sub ((hV _).pow_const 2)).add
    (measurable_const.sub ((hV u).pow_const 2))).sub
      (measurable_const.sub ((hV _).pow_const 2))).div_const 2)

end Measurable

/-! ### Extracting a measurable independent subframe from a measurable spanning family -/

section SubframeExtraction

open Matrix

variable {n : ℕ}

/-- **Det of a matrix with measurable entries is measurable.** The Leibniz expansion
`det M = ∑_σ ε σ * ∏ i, M (σ i) i` is a finite sum of finite products of the (measurable) entry
maps. -/
theorem measurable_det_of_entries {M : X → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, Measurable fun x => M x i j) :
    Measurable fun x => (M x).det := by
  simp_rw [Matrix.det_apply]
  refine Finset.measurable_sum _ fun σ _ => ?_
  exact Measurable.const_smul (Finset.measurable_prod _ fun i _ => hM (σ i) i) _

/-- **Independence of a measurable family is a measurable event.** For measurable vectors
`h i : X → EuclideanSpace ℝ (Fin d)`, the set of `x` at which `i ↦ h i x` is linearly independent
is measurable: it is the nonvanishing locus of the Gram determinant
`det (gram ℝ (h · x))`, whose entries `⟪h i x, h j x⟫` are measurable, and which vanishes exactly
where the family is dependent (`Matrix.det_gram_ne_zero_iff_linearIndependent`). -/
theorem measurableSet_linearIndependent {h : Fin n → X → EuclideanSpace ℝ (Fin d)}
    (hh : ∀ i, Measurable (h i)) :
    MeasurableSet {x | LinearIndependent ℝ (fun i => h i x)} := by
  have hdet : Measurable fun x => (Matrix.gram ℝ (fun i => h i x)).det :=
    measurable_det_of_entries fun i j => by
      simp only [Matrix.gram_apply]; exact (hh i).inner (hh j)
  have hset : {x | LinearIndependent ℝ (fun i => h i x)}
      = {x | (Matrix.gram ℝ (fun i => h i x)).det ≠ 0} := by
    ext x; exact (Matrix.det_gram_ne_zero_iff_linearIndependent).symm
  rw [hset]
  exact hdet (measurableSet_singleton 0).compl

end SubframeExtraction

/-! ### The KRN/Castaing deliverable: a measurable independent spanning frame -/

section Frame

variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {m : ℕ}

omit [MeasurableSpace X] in
/-- A measurable spanning family `g : Fin d → X → EuclideanSpace ℝ (Fin d)` of `V` at constant
rank `m` contains, at every `x`, an independent `m`-subframe: there is an index map
`ι : Fin m → Fin d` with `i ↦ g (ι i) x` linearly independent. This is the pointwise (non-
measurable) extraction; `finrank (V x) = m` forces the extracted independent family to span,
hence have exactly `m` members. -/
theorem exists_independent_subindex
    (g : Fin d → X → EuclideanSpace ℝ (Fin d))
    (hspan : ∀ x, span ℝ (Set.range (fun a => g a x)) = V x)
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) (x : X) :
    ∃ ι : Fin m → Fin d, LinearIndependent ℝ (fun i => g (ι i) x) := by
  classical
  obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' ℝ (fun a => g a x)
  haveI : Finite κ := Finite.of_injective a ha_inj
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = m := by
    have h1 : Module.finrank ℝ (span ℝ (Set.range ((fun a => g a x) ∘ a)))
        = Fintype.card κ := finrank_span_eq_card ha_li
    have h2 : Module.finrank ℝ (span ℝ (Set.range ((fun a => g a x) ∘ a)))
        = Module.finrank ℝ (V x) := by rw [ha_span, hspan]
    rw [h1] at h2
    rw [hdim] at h2
    omega
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hcard
  exact ⟨a ∘ e.symm, ha_li.comp _ e.symm.injective⟩

open scoped Classical in
/-- **Recursive measurable picker.** Given a measurable spanning family `g`, scan a list `L` of
candidate index maps and output the first `i ↦ g (ι i) x` that is linearly independent
(falling back to the zero frame if none in `L` works). Built from `Measurable.piecewise` on the
measurable independence events, it is the engine of the measurable subframe selection. -/
noncomputable def pickIndependent (g : Fin d → X → EuclideanSpace ℝ (Fin d)) :
    List (Fin m → Fin d) → X → (Fin m → EuclideanSpace ℝ (Fin d))
  | [], _ => fun _ => 0
  | ι :: L, x =>
    if LinearIndependent ℝ (fun i => g (ι i) x) then (fun i => g (ι i) x)
    else pickIndependent g L x

/-- Each component of `pickIndependent g L` is measurable, by induction on `L` using
`Measurable.piecewise` on the measurable independence event (`measurableSet_linearIndependent`). -/
theorem measurable_pickIndependent {g : Fin d → X → EuclideanSpace ℝ (Fin d)}
    (hg : ∀ a, Measurable (g a)) (L : List (Fin m → Fin d)) (i : Fin m) :
    Measurable fun x => pickIndependent g L x i := by
  classical
  induction L with
  | nil => simp only [pickIndependent]; exact measurable_const
  | cons ι L ih =>
    have hset : MeasurableSet {x | LinearIndependent ℝ (fun i => g (ι i) x)} :=
      measurableSet_linearIndependent fun j => hg (ι j)
    have heq : (fun x => pickIndependent g (ι :: L) x i)
        = {x | LinearIndependent ℝ (fun i => g (ι i) x)}.piecewise
            (fun x => g (ι i) x) (fun x => pickIndependent g L x i) := by
      funext x
      by_cases hx : LinearIndependent ℝ (fun i => g (ι i) x) <;>
        simp [pickIndependent, Set.piecewise, hx]
    rw [heq]
    exact Measurable.piecewise hset (hg (ι i)) ih

omit [MeasurableSpace X] in
/-- Every component of `pickIndependent g L x` lies in `V x`, provided every `g a x` does: each
output coordinate is some `g (ι i) x ∈ V x` or the fallback `0 ∈ V x`. -/
theorem pickIndependent_mem {g : Fin d → X → EuclideanSpace ℝ (Fin d)} {x : X}
    (hmem : ∀ a, g a x ∈ V x) (L : List (Fin m → Fin d)) (i : Fin m) :
    pickIndependent g L x i ∈ V x := by
  classical
  induction L with
  | nil => simp only [pickIndependent]; exact (V x).zero_mem
  | cons ι L ih =>
    by_cases hι : LinearIndependent ℝ (fun i => g (ι i) x)
    · simp only [pickIndependent, hι, if_true]; exact hmem (ι i)
    · simp only [pickIndependent, hι, if_false]; exact ih

omit [MeasurableSpace X] in
/-- If some `ι ∈ L` makes `i ↦ g (ι i) x` independent, then `pickIndependent g L x` is independent
(it selects the first such `ι`). -/
theorem pickIndependent_linearIndependent {g : Fin d → X → EuclideanSpace ℝ (Fin d)}
    (L : List (Fin m → Fin d)) (x : X)
    (hx : ∃ ι ∈ L, LinearIndependent ℝ (fun i => g (ι i) x)) :
    LinearIndependent ℝ (fun i => pickIndependent g L x i) := by
  classical
  induction L with
  | nil => simp at hx
  | cons ι L ih =>
    by_cases hι : LinearIndependent ℝ (fun i => g (ι i) x)
    · have : (fun i => pickIndependent g (ι :: L) x i) = fun i => g (ι i) x := by
        funext i; simp [pickIndependent, hι]
      rw [this]; exact hι
    · have hL : ∃ ι ∈ L, LinearIndependent ℝ (fun i => g (ι i) x) := by
        obtain ⟨ι', hι'mem, hι'⟩ := hx
        rcases List.mem_cons.mp hι'mem with h | h
        · exact absurd (h ▸ hι') hι
        · exact ⟨ι', h, hι'⟩
      have : (fun i => pickIndependent g (ι :: L) x i)
          = fun i => pickIndependent g L x i := by
        funext i; simp [pickIndependent, hι]
      rw [this]; exact ih hL

/-- **A measurable spanning family yields a measurable independent spanning subframe.** From a
measurable family `g : Fin d → X → EuclideanSpace ℝ (Fin d)` that, at every `x`, lies in `V x` and
spans `V x`, at constant rank `m`, the recursive picker `pickIndependent` over the (finite) list
of all index maps `Fin m → Fin d` produces a measurable frame `f` that is, at every `x`, linearly
independent and spans `V x`. Independence holds because `exists_independent_subindex` guarantees a
good index map is in the list; spanning then follows since an independent `m`-family inside the
`m`-dimensional `V x` is a basis. -/
theorem exists_measurable_independentSpanningFrame_of_spanningFamily
    (g : Fin d → X → EuclideanSpace ℝ (Fin d)) (hg : ∀ a, Measurable (g a))
    (hmem : ∀ a x, g a x ∈ V x)
    (hspan : ∀ x, span ℝ (Set.range (fun a => g a x)) = V x)
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    ∃ f : X → Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, Measurable fun x => f x i) ∧ (∀ x, LinearIndependent ℝ (f x)) ∧
        (∀ x, span ℝ (Set.range (f x)) = V x) := by
  classical
  set L : List (Fin m → Fin d) := (Finset.univ : Finset (Fin m → Fin d)).toList with hL
  refine ⟨fun x => pickIndependent g L x, fun i => measurable_pickIndependent hg L i, ?_, ?_⟩
  · intro x
    obtain ⟨ι, hι⟩ := exists_independent_subindex g hspan hdim x
    exact pickIndependent_linearIndependent L x ⟨ι, by simp [hL], hι⟩
  · intro x
    -- The frame is independent (above) and lies in `V x`; an independent `m`-family in an
    -- `m`-dimensional space spans it.
    have hindep : LinearIndependent ℝ (fun i => pickIndependent g L x i) := by
      obtain ⟨ι, hι⟩ := exists_independent_subindex g hspan hdim x
      exact pickIndependent_linearIndependent L x ⟨ι, by simp [hL], hι⟩
    have hsub : ∀ i, pickIndependent g L x i ∈ V x := fun i =>
      pickIndependent_mem (fun a => hmem a x) L i
    -- `span (range f) ≤ V x` since each `f i ∈ V x`; equality by dimension count.
    have hle : span ℝ (Set.range (fun i => pickIndependent g L x i)) ≤ V x := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩; exact hsub i
    have hfin : Module.finrank ℝ
        (span ℝ (Set.range (fun i => pickIndependent g L x i))) = m := by
      rw [finrank_span_eq_card hindep, Fintype.card_fin]
    -- A submodule of `V x` with finrank `m = finrank (V x)` equals `V x`.
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [hdim, hfin])

end Frame

/-! ### The projected standard basis is a measurable spanning family -/

section ProjectedBasis

variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-- The standard basis vectors `EuclideanSpace.single a 1` span the whole space. -/
theorem span_range_single_eq_top :
    span ℝ (Set.range (fun a : Fin d => (EuclideanSpace.single a (1 : ℝ))))
      = (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
  classical
  have hset : (Set.range (fun a : Fin d => (EuclideanSpace.single a (1 : ℝ))))
      = Set.range (EuclideanSpace.basisFun (Fin d) ℝ) := by
    ext v
    simp only [Set.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, (EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin d) a).trans ha⟩,
      fun ⟨a, ha⟩ => ⟨a, (EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin d) a).symm.trans ha⟩⟩
  rw [hset]
  exact (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq

/-- The orthogonal projections of the standard basis span the subspace: orthogonal projection
is surjective onto its range `K`, and the standard basis spans the ambient space, so the
projected images span `K`. -/
theorem span_range_starProjection_single (K : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    span ℝ (Set.range
        (fun a : Fin d => K.starProjection (EuclideanSpace.single a (1 : ℝ)))) = K := by
  have hrange : (Set.range
      (fun a : Fin d => K.starProjection (EuclideanSpace.single a (1 : ℝ))))
      = (K.starProjection : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).toLinearMap
          '' (Set.range (fun a : Fin d => (EuclideanSpace.single a (1 : ℝ)))) := by
    rw [← Set.range_comp]; rfl
  rw [hrange, Submodule.span_image, span_range_single_eq_top, Submodule.map_top]
  exact K.range_starProjection

/-- **The abstract Castaing/KRN deliverable.** From weak measurability (`MeasurableInfDist V`) and
constant finite rank `m`, a measurable independent spanning frame for `V` exists. The projected
standard basis `g a x := (V x).starProjection (single a 1)` is, by
`measurable_starProjection_apply`, measurable, lies in `V x`, and (by
`span_range_starProjection_single`) spans `V x`; feeding it to
`exists_measurable_independentSpanningFrame_of_spanningFamily` extracts the independent subframe.

This is `sorry`-free; its only nontrivial input, `MeasurableInfDist V`, is exactly the
Kuratowski–Ryll-Nardzewski weak-measurability hypothesis. -/
theorem exists_measurable_independentSpanningFrame_of_measurableInfDist {m : ℕ}
    (hV : MeasurableInfDist V) (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    ∃ f : X → Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, Measurable fun x => f x i) ∧ (∀ x, LinearIndependent ℝ (f x)) ∧
        (∀ x, span ℝ (Set.range (f x)) = V x) := by
  refine exists_measurable_independentSpanningFrame_of_spanningFamily
    (fun a x => (V x).starProjection (EuclideanSpace.single a (1 : ℝ)))
    (fun a => measurable_starProjection_apply hV _)
    (fun a x => (V x).starProjection_apply_mem _)
    (fun x => span_range_starProjection_single (V x)) hdim

end ProjectedBasis

/-! ### Connecting to the measurable graph: the single remaining gap -/

section Graph

variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-- **Measurable graph ⟹ weak measurability (the isolated gap).** A measurable graph
`{(x, v) | v ∈ V x}` makes `x ↦ infDist c (V x)` measurable for every `c`, i.e. yields
`MeasurableInfDist V`.

**This is the one genuinely measure-theoretic step the rest of the converter is reduced to, and
it is left `sorry` (BLOCKED).** Mathematically,
`{x | infDist c (V x) < r} = {x | (V x) ∩ ball c r ≠ ∅}
   = Prod.fst '' ({(x, v) | v ∈ V x} ∩ (Set.univ ×ˢ ball c r))`,
the projection onto `X` of a measurable subset of `X × EuclideanSpace ℝ (Fin d)` whose
`x`-sections `V x ∩ ball c r` are **σ-compact** (they are open subsets of the finite-dimensional,
hence locally compact, subspace `V x`). The projection of a Borel set with σ-compact sections is
Borel — this is the **Arsenin–Kunugui / Saint-Raymond theorem** (equivalently the measurable
projection theorem for `K_σ`-section sets). Mathlib has the analytic-set / Lusin–Souslin
machinery (`MeasureTheory.AnalyticSet`, `measurableSet_range_of_continuous_injective`,
`AnalyticSet.measurablySeparable`) but **not** the Arsenin–Kunugui projection theorem, and no
`MeasurableSpace`/`Borel` structure on the Grassmannian; the projection of a Borel set is in
general only analytic, so the elementary route fails and the σ-compact-section strengthening is
required. Note this gap is *equivalent* to the converter's target itself: `infDist c (V x)
= ‖c − (V x).starProjection c‖`, so `x ↦ infDist c (V x)` measurable is interderivable with
`x ↦ (V x).starProjection` (the projector) measurable — confirming this is a single irreducible
node, not a removable detour.

The precise missing Mathlib fact is therefore: *the projection `Prod.fst '' S` onto `X` of a
measurable set `S ⊆ X × Y` (`Y` Polish/σ-compact) all of whose `x`-sections are σ-compact is
measurable* (Arsenin–Kunugui). Once available, this lemma is a one-line consequence via the
displayed identity. -/
theorem measurableInfDist_of_measurableGraph
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1}) :
    MeasurableInfDist V := by
  sorry -- BLOCKED: Arsenin–Kunugui measurable-projection theorem (Borel set with σ-compact
        -- sections has Borel projection) is absent from Mathlib; see the docstring. This is the
        -- single remaining measure-theoretic gap, equivalent to the converter's target itself.

end Graph

namespace _root_.Oseledets

variable {V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}

/-- **The target (verbatim).** A measurable graph together with constant finite dimension `m`
yields a measurable, pointwise linearly-independent, pointwise spanning frame for `V`.

The graph is converted to weak measurability `MeasurableInfDist V`
(`Frontier.measurableInfDist_of_measurableGraph`, the single isolated `sorry`), and the abstract
Castaing/KRN deliverable `Frontier.exists_measurable_independentSpanningFrame_of_measurableInfDist`
(fully `sorry`-free) produces the frame. The dependence on `sorry` is confined to the
Arsenin–Kunugui measurable-projection step; the entire algebraic and measurable-combination
content — projector-coordinate distance identities, projected-basis spanning, Gram-determinant
independence events, and the recursive measurable subframe selection — is proved. -/
theorem exists_measurable_independentSpanningFrame_of_measurableGraph {m : ℕ}
    (hgraph : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ V p.1})
    (hdim : ∀ x, Module.finrank ℝ (V x) = m) :
    ∃ f : X → Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, Measurable fun x => f x i) ∧ (∀ x, LinearIndependent ℝ (f x)) ∧
        (∀ x, Submodule.span ℝ (Set.range (f x)) = V x) :=
  Frontier.exists_measurable_independentSpanningFrame_of_measurableInfDist
    (Frontier.measurableInfDist_of_measurableGraph hgraph) hdim

end _root_.Oseledets

end Frontier
