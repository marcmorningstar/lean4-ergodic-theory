/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.Degeneracy
import Oseledets.Multifractal.Measure
import Mathlib.Topology.Order.Real

/-!
# Coarse-grained multifractal analysis: the refining-partition limit (degenerate case)

This file discharges the **degenerate (uniform / monofractal) case** of the refining-partition
limit of issue #16, item 6: *for the uniform (Haar / Lebesgue) measure the multifractal Rényi
spectrum degenerates to a single point, recovered exactly in the refining limit `ε → 0`.*

Concretely, partition `d`-dimensional space at scale `ε ∈ (0, 1)` into a uniform grid of
`N = ε ^ (-d)` cells of equal weight `p i = N⁻¹` (the dyadic-grid scaling of `d`-dimensional
Lebesgue measure). Then `Degeneracy.renyiDim_equalMeasure` gives, for *every* `q`,
`D_q = log N / (-log ε)`, and feeding the count `N = ε ^ (-d)` in collapses this to
`D_q = d`, **exactly**, for every `ε ∈ (0, 1)` and every `q` (`Real.log_rpow` turns
`log (ε ^ (-d))` into `(-d) · log ε`, which cancels against `-log ε ≠ 0`). The per-resolution
value is therefore the *constant* `d`, so the refining limit `ε → 0` is the trivial limit of a
constant: `Tendsto (fun ε => renyiDim (p ε) ε q) (𝓝[Set.Ioo 0 1] 0) (𝓝 d)`.

## Main results

* `Oseledets.Multifractal.renyiDim_uniform_eq_dim`: the load-bearing per-resolution identity
  `D_q = d` for a uniform partition with `Fintype.card ι = ε ^ (-d)`.
* `Oseledets.Multifractal.renyiDim_uniform_tendsto_dim`: the refining-limit corollary, packaging
  the constant value as an actual `Tendsto … (𝓝[Set.Ioo 0 1] 0) (𝓝 d)`.
* `Oseledets.Multifractal.renyiDimMeasure_uniform_eq_dim`: the measure-level mirror.

## Scope (what is, and is NOT, formalized here)

This is **only** the degenerate uniform / monofractal case, where the per-resolution dimension is
constant in `ε` and the limit is trivial. The **general non-uniform refining limit** (item 6 for a
genuinely multifractal measure, where `D_q(ε)` varies with `ε` and one must control the limit) and
**item 5** (the pointwise *local dimension* `lim_{r→0} log μ(B(x,r)) / log r` and
exact-dimensionality of `μ`) are the *deep frontier* and are deliberately **not** formalized here.
The local dimension is a joint measure-*and*-metric invariant: it is not invariant under a general
measure-preserving map and requires the smooth / bi-Lipschitz dynamical structure
(Eckmann–Ruelle, Barreira–Pesin–Schmeling) that this library does not carry. See the issue for the
research-grade statement.
-/

open Real Filter Topology

namespace Oseledets.Multifractal

/-- **Per-resolution monofractal value.** For a uniform partition into `N = Fintype.card ι` cells
of equal weight `p i = N⁻¹`, with the count tuned to the `d`-dimensional dyadic-grid scaling
`N = ε ^ (-d)` (so the cells model `d`-dimensional Lebesgue measure at scale `ε`), the Rényi
(generalized) dimension is *exactly* `d` for **every** `q` and every `ε ∈ (0, 1)`. Indeed
`renyiDim_equalMeasure` gives `D_q = log N / (-log ε)`, and `log N = log (ε ^ (-d)) = (-d) log ε`
cancels the denominator `-log ε ≠ 0`. -/
theorem renyiDim_uniform_eq_dim {ι : Type*} [Fintype ι] [Nonempty ι] {p : ι → ℝ} {ε d : ℝ}
    (hp : ∀ i, p i = (Fintype.card ι : ℝ)⁻¹) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hcard : (Fintype.card ι : ℝ) = ε ^ (-d)) (q : ℝ) :
    renyiDim p ε q = d := by
  have hlogε_neg : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hlogε_ne : Real.log ε ≠ 0 := ne_of_lt hlogε_neg
  rw [renyiDim_equalMeasure hp hε0 hε1 q, hcard, Real.log_rpow hε0]
  -- now: (-d * log ε) / (- log ε) = d, with log ε ≠ 0
  field_simp

/-- **Refining-partition limit (degenerate / monofractal case).** Take a refining family of uniform
partitions: at each scale `ε ∈ (0, 1)` an index type `ι ε` of `Fintype.card (ι ε) = ε ^ (-d)` cells,
each carrying the equal weight `(Fintype.card (ι ε))⁻¹` (the dyadic-grid model of `d`-dimensional
Lebesgue measure). By `renyiDim_uniform_eq_dim` the per-resolution Rényi dimension equals the
constant `d` for every such `ε` and every `q`, so the refining limit `ε → 0` recovers the single
spectral point `d` **exactly**:
`Tendsto (fun ε => renyiDim (p ε) ε q) (𝓝[Set.Ioo 0 1] 0) (𝓝 d)`. This is the degenerate case of
issue #16, item 6. -/
theorem renyiDim_uniform_tendsto_dim {ι : ℝ → Type*} [∀ ε, Fintype (ι ε)] [∀ ε, Nonempty (ι ε)]
    {p : ∀ ε, ι ε → ℝ} {d : ℝ}
    (huniform : ∀ ε i, p ε i = (Fintype.card (ι ε) : ℝ)⁻¹)
    (hcard : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, (Fintype.card (ι ε) : ℝ) = ε ^ (-d)) (q : ℝ) :
    Tendsto (fun ε => renyiDim (p ε) ε q) (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝 d) := by
  -- The function equals the constant `d` on `Set.Ioo 0 1`, where the limit filter lives.
  refine Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
  intro ε hε
  exact (renyiDim_uniform_eq_dim (huniform ε) hε.1 hε.2 (hcard ε hε) q).symm

/-- **Measure-level mirror of the monofractal value.** For a probability measure `μ` and a uniform
partition `P` with each cell of equal measure `(Fintype.card ι)⁻¹` and the count tuned to the
`d`-dimensional scaling `Fintype.card ι = ε ^ (-d)`, the Rényi dimension of `μ` is *exactly* `d`
for every `q` and every `ε ∈ (0, 1)`. This is `renyiDimMeasure_equalMeasure` fed the count
`N = ε ^ (-d)`. -/
theorem renyiDimMeasure_uniform_eq_dim {α : Type*} {ι : Type*} [MeasurableSpace α] [Fintype ι]
    [Nonempty ι] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (P : Oseledets.Entropy.MeasurePartition μ ι) {ε d : ℝ}
    (huniform : ∀ i, (μ (P.cells i)).toReal = (Fintype.card ι : ℝ)⁻¹)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hcard : (Fintype.card ι : ℝ) = ε ^ (-d)) (q : ℝ) :
    renyiDimMeasure μ P ε q = d :=
  renyiDim_uniform_eq_dim huniform hε0 hε1 hcard q

end Oseledets.Multifractal
