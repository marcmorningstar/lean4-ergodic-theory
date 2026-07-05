/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.Flow
import ErgodicTheory.Continuous.SuspensionSpaceExponent
import ErgodicTheory.Entropy.KSEntropyJoin
import ErgodicTheory.Entropy.Fekete
import ErgodicTheory.Multifractal.Measure
import ErgodicTheory.Multifractal.Degeneracy
import ErgodicTheory.Multifractal.RefiningLimit

/-!
# Flow-refined partition and finite-resolution multifractal observables (issue #18)

This file builds the **flow-transported coarse-grained partition** and the
**finite-resolution (pre-limit) observable layer** of issue #18, abstractly over a supplied
measure-preserving flow `φ : ErgodicTheory.MeasurePreservingFlow μ`. It is a definitions + interface
layer on top of the existing entropy partition machinery (`ErgodicTheory.Entropy`) and the
coarse-grained multifractal measure layer of issue #16 (`ErgodicTheory.Multifractal.Measure`); the
heavy multifractal theorems are already proved there and are *consumed*, not re-derived, here.

The bridge is deliberately minimal: the entire #16 ↔ #18 interface is the cell-mass family
`cellMassFamily P : ι → ℝ`, `i ↦ (μ (P.cells i)).toReal`. This is *exactly* the weight family
consumed by `ErgodicTheory.Multifractal.partitionFunctionMeasure` / `renyiDimMeasure` / `renyiDimFlow`,
so none of `Z_q`, `τ(q)`, `D_q`, `f(α)` is redefined here.

## Main definitions

* `ErgodicTheory.Multifractal.dynamicalRefine`: the depth-`n` flow-refined partition, the join over
  `k = 0, …, n-1` of the pullbacks `(φ (k • Δ))⁻¹ P` of a supplied seed partition `P`, realized
  with the flat `Fin n → ι` index discipline of `ErgodicTheory.Entropy.ksJoin`.
* `ErgodicTheory.Multifractal.cellMassFamily`: the cell-mass family `i ↦ (μ (P.cells i)).toReal`, the
  whole #16 ↔ #18 interface.
* `ErgodicTheory.Multifractal.IsHeterogeneous`: the honest non-uniformity hypothesis on `P` — two
  cells of distinct mass. Its failure is *exactly* the equal-measure monofractal degeneracy of #16.
* `ErgodicTheory.Multifractal.finiteTimePartitionEntropy`: the depth-`n` (pre-limit) Shannon entropy
  of `dynamicalRefine`, distinct from its Kolmogorov–Sinai (Fekete) limit.
* `ErgodicTheory.Multifractal.finiteTimeFlowExponent`: the finite-time (pre-limit) Lyapunov estimator
  `log ‖coverCocycle (x, s) t‖ / t`, the function inside the `Tendsto` of `HasFlowExponent`.

## Main results

* `ErgodicTheory.Multifractal.cellMassFamily_sum_eq_one`: the cell masses sum to `1` (genuine
  probabilities) — the non-vacuity of the interface.
* `ErgodicTheory.Multifractal.not_isHeterogeneous_iff_equalMeasure`: `¬ IsHeterogeneous μ P` iff all
  cell masses are equal — i.e. the equal-measure hypothesis of `partitionFunction_equalMeasure` /
  `renyiDim_equalMeasure`, the monofractal single-point spectrum that #16 characterizes.
* `ErgodicTheory.Multifractal.hasFlowExponent_of_tendsto_finiteTimeFlowExponent`: a converging
  finite-time estimator at a representative certifies the class's `HasFlowExponent`.
* `ErgodicTheory.Multifractal.RefiningLimitConvergesProp`: the `ε → 0` mesh-refinement convergence of
  the cell-mass family, stated (signature only) with a cross-reference to the #16 degenerate-
  uniform limit `renyiDim_uniform_tendsto_dim`; the general non-uniform refining limit stays #16's
  deferred content, so #18 does not re-request it.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory.Multifractal

open ErgodicTheory.Entropy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-! ### N1 — flow-transported coarse-grained partition + cell-mass family -/

/-- The cell family of the depth-`n` flow-refined join: at an index `f : Fin n → ι` it is the
intersection `⋂ₖ (φ (k • Δ))⁻¹ (P_{f k})` of the pullbacks of the chosen seed-cells `P` along the
flow at the equally-spaced times `0, Δ, 2Δ, …, (n-1)Δ`. This is the flow-transported analogue of
`ErgodicTheory.Entropy.ksJoinCells`, with the flow map `φ (k • Δ)` in place of the discrete iterate
`T^[k]`; for `n = 0` the empty intersection is the whole space. -/
def dynamicalRefineCells {ι : Type*} [Fintype ι] (φ : MeasurePreservingFlow μ)
    (P : MeasurePartition μ ι) (Δ : ℝ) (n : ℕ) (f : Fin n → ι) : Set X :=
  ⋂ k : Fin n, (φ ((k : ℕ) • Δ)) ⁻¹' P.cells (f k)

/-- The **depth-`n` flow-refined partition** `⋁ₖ (φ (k • Δ))⁻¹ P`, the join over the equally spaced
flow times `k • Δ` (`k = 0, …, n-1`) of the pullbacks of a supplied seed partition `P`, indexed by
`Fin n → ι` (the flat index discipline of `ErgodicTheory.Entropy.ksJoin`). This is the flow-transported
coarse-grained partition of issue #18; the seed `P` is supplied (not hardcoded), so the
construction is abstract in the measurable space `X`. Each cell is a finite intersection of
preimages of measurable cells under the measurable, measure-preserving flow maps `φ (k • Δ)`; two
distinct indices differ at some `k`, where the seed cells are almost-everywhere disjoint and the
measure-preserving `φ (k • Δ)` keeps them a.e. disjoint after pullback; and the cells cover the
space because at each coordinate `k` the point `φ (k • Δ) x` lies in some seed cell. -/
noncomputable def dynamicalRefine {ι : Type*} [Fintype ι] (φ : MeasurePreservingFlow μ)
    (P : MeasurePartition μ ι) (Δ : ℝ) (n : ℕ) : MeasurePartition μ (Fin n → ι) where
  cells := dynamicalRefineCells φ P Δ n
  measurable f := by
    refine MeasurableSet.iInter fun k => ?_
    exact (P.measurable (f k)).preimage (φ.measurable ((k : ℕ) • Δ))
  aedisjoint := by
    intro f g hfg
    simp only [Function.onFun]
    obtain ⟨k, hk⟩ : ∃ k, f k ≠ g k := by
      by_contra h
      exact hfg (funext fun k => not_not.mp fun hk => h ⟨k, hk⟩)
    have hsub₁ : dynamicalRefineCells φ P Δ n f
        ⊆ (φ ((k : ℕ) • Δ)) ⁻¹' P.cells (f k) := Set.iInter_subset _ k
    have hsub₂ : dynamicalRefineCells φ P Δ n g
        ⊆ (φ ((k : ℕ) • Δ)) ⁻¹' P.cells (g k) := Set.iInter_subset _ k
    refine AEDisjoint.mono ?_ hsub₁ hsub₂
    simp only [AEDisjoint, ← Set.preimage_inter]
    rw [(φ.measurePreserving ((k : ℕ) • Δ)).measure_preimage
      ((P.measurable (f k)).inter (P.measurable (g k))).nullMeasurableSet]
    exact P.aedisjoint hk
  cover := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hx : ∀ k : Fin n, ∃ i, (φ ((k : ℕ) • Δ)) x ∈ P.cells i := fun k => by
      have : (φ ((k : ℕ) • Δ)) x ∈ ⋃ i, P.cells i := P.cover ▸ Set.mem_univ _
      exact Set.mem_iUnion.mp this
    choose f hf using hx
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iInter.mpr fun k => hf k⟩

@[simp]
lemma dynamicalRefine_cells {ι : Type*} [Fintype ι] (φ : MeasurePreservingFlow μ)
    (P : MeasurePartition μ ι) (Δ : ℝ) (n : ℕ) :
    (dynamicalRefine φ P Δ n).cells = dynamicalRefineCells φ P Δ n := rfl

/-- The **cell-mass family** `i ↦ (μ (P.cells i)).toReal` of a finite measurable partition `P`.
This `ι → ℝ` family is the *entire* #16 ↔ #18 interface: it is exactly the weight family consumed
by `ErgodicTheory.Multifractal.partitionFunctionMeasure` / `renyiDimMeasure` / `renyiDimFlow`. (So
`Z_q`, `τ(q)`, `D_q`, `f(α)` are not redefined here — they are the #16 functions on this family.) -/
noncomputable def cellMassFamily {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι) :
    ι → ℝ :=
  fun i => (μ (P.cells i)).toReal

@[simp]
lemma cellMassFamily_apply {ι : Type*} [Fintype ι] (P : MeasurePartition μ ι) (i : ι) :
    cellMassFamily P i = (μ (P.cells i)).toReal := rfl

/-- **Non-vacuity of the interface.** The cell masses of a partition of a probability space are
genuine probabilities summing to `1`. A thin wrapper over
`ErgodicTheory.Entropy.MeasurePartition.sum_toReal_measure_eq_one`. -/
theorem cellMassFamily_sum_eq_one {ι : Type*} [Fintype ι] [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) :
    ∑ i, cellMassFamily P i = 1 :=
  P.sum_toReal_measure_eq_one

/-! ### N4 — honest heterogeneity (non-uniform target) -/

/-- **Heterogeneity (non-uniformity) of a partition.** `IsHeterogeneous μ P` holds when two cells
carry distinct mass: `∃ i j, (μ (P.cells i)).toReal ≠ (μ (P.cells j)).toReal`. This is a *supplied*
hypothesis for the genuinely multifractal downstream of #18; it is **false** for a uniform
(Haar / Lebesgue) measure, where all cells carry the same mass, so it is never asserted for an
arbitrary `μ`. By `not_isHeterogeneous_iff_equalMeasure`, its failure is exactly the equal-measure
hypothesis of the #16 monofractal degeneracy `renyiDim_equalMeasure`. -/
def IsHeterogeneous {ι : Type*} [Fintype ι] (μ : Measure X) (P : MeasurePartition μ ι) :
    Prop :=
  ∃ i j, (μ (P.cells i)).toReal ≠ (μ (P.cells j)).toReal

/-- **Failure of heterogeneity is exactly the equal-measure hypothesis.** `¬ IsHeterogeneous μ P`
holds iff all cell masses are equal, `∀ i j, (μ (P.cells i)).toReal = (μ (P.cells j)).toReal`.
This equal-mass condition is precisely the hypothesis of the #16 monofractal-degeneracy results
`ErgodicTheory.Multifractal.partitionFunction_equalMeasure` and `renyiDim_equalMeasure`
(`ErgodicTheory/Multifractal/Degeneracy.lean`): when it holds, the whole Rényi spectrum collapses to
the single box-counting point `log N / (-log ε)`. So the heterogeneity hypothesis is genuinely
non-trivial — its negation is the single-point-spectrum monofractal case #16 characterizes. -/
theorem not_isHeterogeneous_iff_equalMeasure {ι : Type*} [Fintype ι]
    (P : MeasurePartition μ ι) :
    ¬ IsHeterogeneous μ P ↔
      ∀ i j, (μ (P.cells i)).toReal = (μ (P.cells j)).toReal := by
  unfold IsHeterogeneous
  push Not
  rfl

/-! ### N2b — finite-time observables (pre-limits, distinct from their asymptotic limits) -/

/-- The **depth-`n` (finite-time) partition entropy** of the flow-refined partition: the Shannon
entropy `H(⋁ₖ (φ (k • Δ))⁻¹ P)` of the depth-`n` truncation `dynamicalRefine φ P Δ n`. This is the
*pre-limit* observable, distinct from the Kolmogorov–Sinai (Fekete) limit `ksEntropyPartition`; the
latter is the `(1/n)`-average limit of these as `n → ∞`. -/
noncomputable def finiteTimePartitionEntropy {ι : Type*} [Fintype ι]
    (φ : MeasurePreservingFlow μ) (P : MeasurePartition μ ι) (Δ : ℝ) (n : ℕ) : ℝ :=
  ErgodicTheory.Entropy.entropy μ (dynamicalRefine φ P Δ n).cells

@[simp]
lemma finiteTimePartitionEntropy_def {ι : Type*} [Fintype ι]
    (φ : MeasurePreservingFlow μ) (P : MeasurePartition μ ι) (Δ : ℝ) (n : ℕ) :
    finiteTimePartitionEntropy φ P Δ n
      = ErgodicTheory.Entropy.entropy μ (dynamicalRefine φ P Δ n).cells := rfl

section FlowExponent

variable {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X ≃ᵐ X) {τ : X → ℝ}
  (hτ : Measurable τ) {c : ℝ}

/-- The **finite-time (pre-limit) flow Lyapunov estimator (FTLE)** at a fixed finite flow time `t`:
`log ‖coverCocycle (x, s) t‖ / t`, the function whose `atTop` limit defines
`ErgodicTheory.HasFlowExponent`. For each fixed `t` this is the finite-time exponent estimate; the
asymptotic exponent `L` is its `t → ∞` limit, related by
`hasFlowExponent_of_tendsto_finiteTimeFlowExponent`. This estimator is suspension-flow-specific
(it reads the cover cocycle), the finite-time Lyapunov estimator the issue asks for. -/
noncomputable def finiteTimeFlowExponent (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (x : X) (s : ℝ)
    (t : ℝ) : ℝ :=
  Real.log ‖coverCocycle A T hτ hc hcpos (x, s) t‖ / t

/-- **The FTLE limit at a representative certifies the flow exponent.** If the finite-time flow
estimator `finiteTimeFlowExponent (x, s) ·` at a representative `(x, s)` of the orbit class
`q : SuspensionSpace T hτ` (so `suspensionMk (x, s) = q`) converges to `L` as the flow time
`t → ∞`, then the class `q` carries the flow exponent `L`, witnessed by `(x, s)` — that is,
`HasFlowExponent A T hτ hc hcpos q L` holds. This is the honest content of "the FTLE limit is the
flow exponent": `finiteTimeFlowExponent` is *defined* to be the function inside the `Tendsto` of
`HasFlowExponent`, so a converging estimator at a single representative directly produces a
`HasFlowExponent` witness. The converse — that *every* representative's estimator converges to the
same `L` — is the representative-invariance proved, under base-cocycle invertibility, by
`ErgodicTheory.hasFlowExponent_of_suspensionAct`; it is not a definitional consequence, so this is an
implication, not an `↔`. -/
theorem hasFlowExponent_of_tendsto_finiteTimeFlowExponent (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    (q : SuspensionSpace T hτ) (x : X) (s : ℝ) (hmk : suspensionMk T hτ (x, s) = q) (L : ℝ)
    (hconv : Tendsto (fun t : ℝ => finiteTimeFlowExponent A T hτ hc hcpos x s t) atTop (𝓝 L)) :
    HasFlowExponent A T hτ hc hcpos q L :=
  ⟨x, s, hmk, hconv⟩

end FlowExponent

/-! ### N3c — mesh-refinement convergence: statement + cross-reference to #16 (no proof)

The general `ε → 0` mesh-refinement convergence of the cell-mass family (and hence of the Rényi
dimension built on it) to the local-dimension spectrum is, for a *genuinely multifractal*
(non-uniform) measure, the deferred research-grade content of issue #16, item 6 — it needs the
Ledrappier–Young absolute continuity of conditional measures, the same Mathlib-absent ingredient
blocking the Pesin–SRB work (issue #10); see the module docstring of
`ErgodicTheory.Multifractal.RefiningLimit`. So #18 does **not** re-request it: it records the
convergence as a `Prop`-valued predicate with the honest cross-reference, and the one case that
*is* provable — the degenerate uniform / monofractal case — is already discharged unconditionally
by `ErgodicTheory.Multifractal.renyiDim_uniform_tendsto_dim` (the `Tendsto … (𝓝[Ioo 0 1] 0)` limit),
which this layer simply points at rather than duplicating. -/

variable {ι : ℝ → Type*} [∀ ε, Fintype (ι ε)]

/-- **Mesh-refinement convergence of the cell-mass spectrum (predicate, no proof).** For a refining
family of partitions `P ε : MeasurePartition μ (ι ε)` at scales `ε ∈ (0, 1)`, the Rényi dimension
`renyiDimMeasure μ (P ε) ε q` built on the cell-mass families `cellMassFamily (P ε)` converges, as
`ε → 0`, to a limit dimension `D q`:
`Tendsto (fun ε => renyiDimMeasure μ (P ε) ε q) (𝓝[Set.Ioo 0 1] 0) (𝓝 (D q))`.

This is *stated only* (as the `Prop` it asserts), with no proof, by design: the general non-uniform
refining limit is the deferred content of issue #16, item 6 (the Ledrappier–Young / exact-
dimensionality frontier; see `ErgodicTheory.Multifractal.RefiningLimit`), so #18 does not re-request
it. The *degenerate uniform / monofractal case* of this very convergence is already proved
unconditionally as `ErgodicTheory.Multifractal.renyiDim_uniform_tendsto_dim` (and its measure mirror
`renyiDimMeasure_uniform_eq_dim`), where `D q ≡ d` is the constant box-counting dimension. -/
def RefiningLimitConvergesProp (μ : Measure X) (P : ∀ ε, MeasurePartition μ (ι ε))
    (D : ℝ → ℝ) (q : ℝ) : Prop :=
  Tendsto (fun ε => renyiDimMeasure μ (P ε) ε q) (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝 (D q))

/-- **Discharge of the mesh-refinement convergence in the degenerate uniform case.** When the
refining family is uniform — each `P ε` has all cells of equal mass `(Fintype.card (ι ε))⁻¹` with
the `d`-dimensional dyadic-grid count `Fintype.card (ι ε) = ε ^ (-d)` — the mesh-refinement
convergence predicate `RefiningLimitConvergesProp` holds with the constant limit `D q ≡ d`. This is
exactly `ErgodicTheory.Multifractal.renyiDim_uniform_tendsto_dim` transported to `renyiDimMeasure` via
the cell-mass family, the *only* case of the general (deferred) refining limit provable
unconditionally. -/
theorem refiningLimitConvergesProp_of_uniform [∀ ε, Nonempty (ι ε)] [IsProbabilityMeasure μ]
    (P : ∀ ε, MeasurePartition μ (ι ε)) {d : ℝ}
    (huniform : ∀ ε i, (μ ((P ε).cells i)).toReal = (Fintype.card (ι ε) : ℝ)⁻¹)
    (hcard : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, (Fintype.card (ι ε) : ℝ) = ε ^ (-d)) (q : ℝ) :
    RefiningLimitConvergesProp μ P (fun _ => d) q := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
  intro ε hε
  exact (renyiDimMeasure_uniform_eq_dim (P ε) (huniform ε) hε.1 hε.2 (hcard ε hε) q).symm

end ErgodicTheory.Multifractal
