/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.Degeneracy
import ErgodicTheory.Multifractal.Measure
import Mathlib.Topology.Order.Real

/-!
# Coarse-grained multifractal analysis: the refining-partition limit (degenerate case)

This file discharges the **degenerate (uniform / monofractal) case** of the refining-partition
limit of issue #16, item 6: *for the uniform (Haar / Lebesgue) measure the multifractal Rényi
spectrum degenerates to a single point, recovered exactly in the refining limit as the mesh scale
tends to `0`.*

Concretely, partition `d`-dimensional space at scale `ε ∈ (0, 1)` into a uniform grid of
`N = ε ^ (-d)` cells of equal weight `p i = N⁻¹` (the dyadic-grid scaling of `d`-dimensional
Lebesgue measure). Then `Degeneracy.renyiDim_equalMeasure` gives, for *every* `q`,
`D_q = log N / (-log ε)`, and feeding the count `N = ε ^ (-d)` in collapses this to
`D_q = d`, **exactly**, for every `ε ∈ (0, 1)` and every `q` (`Real.log_rpow` turns
`log (ε ^ (-d))` into `(-d) · log ε`, which cancels against `-log ε ≠ 0`). This
**per-resolution identity** `renyiDim_uniform_eq_dim` is the load-bearing content of the file.

## Why the refining limit is taken along a *discrete* scale sequence

The naive "all-`ε`" formulation — a single family `ι : ℝ → Type` with
`(Fintype.card (ι ε) : ℝ) = ε ^ (-d)` for **every** `ε ∈ (0, 1)` — is **unsatisfiable for every
`d ≠ 0`**: the left-hand side is a natural-number cardinality (an integer), while `ε ↦ ε ^ (-d)`
is strictly monotone and hence injective on the continuum `(0, 1)`, so it takes non-integer values
at all but countably many `ε`. A `Tendsto` conclusion carrying that hypothesis would be *vacuously*
true and certify nothing at positive dimension. The honest refining limit is therefore taken along
a **discrete dyadic scale sequence** `εₙ = 2 ^ (-n)`, where the count constraint becomes the
*natural-number* equation `Fintype.card (ι n) = 2 ^ (n * d)` — satisfiable at **every** `d : ℕ` (the
witness `ι n := Fin (2 ^ (n * d))` is recorded below). Along this sequence the per-resolution value
is the constant `d`, so the limit `n → ∞` recovers the single spectral point `d` exactly.

## Main results

* `ErgodicTheory.Multifractal.renyiDim_uniform_eq_dim`: the load-bearing per-resolution identity
  `D_q = d` for a uniform partition with `Fintype.card ι = ε ^ (-d)`.
* `ErgodicTheory.Multifractal.renyiDim_uniform_seq_tendsto_dim`: the refining-limit corollary along
  the dyadic sequence `εₙ = 2 ^ (-n)` with the satisfiable count `Fintype.card (ι n) = 2 ^ (n * d)`,
  packaging the constant value as `Tendsto (fun n => renyiDim (p n) (2 ^ (-n)) q) atTop (𝓝 d)`.
* `ErgodicTheory.Multifractal.renyiDimMeasure_uniform_eq_dim`: the measure-level mirror of the
  per-resolution identity.

An `example` immediately after `renyiDim_uniform_seq_tendsto_dim` instantiates its hypothesis family
for **every** `d : ℕ` (index `ι n := Fin (2 ^ (n * d))`), certifying non-vacuity.

## Scope (what is, and is NOT, formalized here)

This is **only** the degenerate uniform / monofractal case, where the per-resolution dimension is
constant in `ε` and the (sequential) limit is trivial. The pointwise *local dimension* itself is
defined, and its absolutely-continuous case proved, in
`ErgodicTheory.Multifractal.LocalDimension` (item 5). What stays
the genuine frontier is the **general non-uniform refining limit** (item 6 for a genuinely
multifractal measure) and **general exact-dimensionality** — a.e.-constancy of the local dimension
for a singular / SRB measure, and the Young / Ledrappier–Young identity. These need the absolute
continuity of conditional measures on unstable manifolds (the Ledrappier–Young core), the same
Mathlib-absent ingredient that blocks the library's Pesin–SRB work (issue #10), not any missing
metric or ergodic theorem (the Lyapunov exponents, entropy, Margulis–Ruelle inequality, and a
pointwise Birkhoff theorem are all already present). See the issue for the research-grade statement.
-/

open Real Filter Topology

namespace ErgodicTheory.Multifractal

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

/-- **Refining-partition limit (degenerate / monofractal case), along a dyadic scale sequence.**
Take a refining family of uniform partitions indexed by the *discrete* scale sequence
`εₙ = 2 ^ (-n)`: at depth `n` an index type `ι n` of `Fintype.card (ι n) = 2 ^ (n * d)` cells, each
carrying the equal weight `(Fintype.card (ι n))⁻¹` (the dyadic-grid model of `d`-dimensional
Lebesgue measure at scale `2 ^ (-n)`). The count constraint is the **natural-number** equation
`Fintype.card (ι n) = 2 ^ (n * d)`, which is *satisfiable* at every `d : ℕ` — unlike the naive
all-`ε ∈ (0, 1)` constraint `(Fintype.card (ι ε) : ℝ) = ε ^ (-d)`, which forces `d = 0` because a
cardinality is an integer while `ε ↦ ε ^ (-d)` is injective on the continuum (see the module
docstring). At each `n ≥ 1` the equation `2 ^ (n * d) = (2 ^ (-n)) ^ (-d)` (rpow) lets
`renyiDim_uniform_eq_dim` fire, giving the per-resolution value `d`; so the sequence is eventually
constant and the refining limit `n → ∞` recovers the single spectral point `d` **exactly**:
`Tendsto (fun n => renyiDim (p n) (2 ^ (-n)) q) atTop (𝓝 d)`. This is the degenerate case of
issue #16, item 6. -/
theorem renyiDim_uniform_seq_tendsto_dim {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, Nonempty (ι n)] {p : ∀ n, ι n → ℝ} {d : ℕ}
    (huniform : ∀ n i, p n i = (Fintype.card (ι n) : ℝ)⁻¹)
    (hcard : ∀ n, 1 ≤ n → Fintype.card (ι n) = 2 ^ (n * d)) (q : ℝ) :
    Tendsto (fun n => renyiDim (p n) ((2 : ℝ) ^ (-(n : ℝ))) q) atTop (𝓝 (d : ℝ)) := by
  -- The sequence equals the constant `d` for every `n ≥ 1`, so it converges to `d`.
  refine Tendsto.congr' ?_ tendsto_const_nhds
  refine (Filter.eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hε0 : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hε1 : (2 : ℝ) ^ (-(n : ℝ)) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcardR : (Fintype.card (ι n) : ℝ) = ((2 : ℝ) ^ (-(n : ℝ))) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul_neg, hcard n hn,
      show ((n : ℝ) * (d : ℝ)) = ((n * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    ring
  exact (renyiDim_uniform_eq_dim (huniform n) hε0 hε1 hcardR q).symm

/-- **Satisfiability witness for the sequential refining limit.** For every dimension `d : ℕ` the
hypothesis family of `renyiDim_uniform_seq_tendsto_dim` is instantiable: take the index family
`ι n := Fin (2 ^ (n * d))` with the uniform weights `(Fintype.card (ι n))⁻¹`. Then
`Fintype.card (ι n) = 2 ^ (n * d)` holds by `Fintype.card_fin` for **every** `n` (not merely
vacuously), so the theorem's `Tendsto` conclusion is a genuine convergence at every `d` — the
non-vacuity certificate the naive all-`ε` formulation cannot provide. -/
example (d : ℕ) (q : ℝ) :
    Tendsto (fun n => renyiDim (fun _ : Fin (2 ^ (n * d)) =>
        (Fintype.card (Fin (2 ^ (n * d))) : ℝ)⁻¹) ((2 : ℝ) ^ (-(n : ℝ))) q)
      atTop (𝓝 (d : ℝ)) := by
  haveI hne : ∀ n : ℕ, Nonempty (Fin (2 ^ (n * d))) := fun n => ⟨⟨0, by positivity⟩⟩
  exact renyiDim_uniform_seq_tendsto_dim (ι := fun n => Fin (2 ^ (n * d)))
    (p := fun n _ => (Fintype.card (Fin (2 ^ (n * d))) : ℝ)⁻¹)
    (fun _ _ => rfl) (fun n _ => Fintype.card_fin _) q

/-- **Measure-level mirror of the monofractal value.** For a probability measure `μ` and a uniform
partition `P` with each cell of equal measure `(Fintype.card ι)⁻¹` and the count tuned to the
`d`-dimensional scaling `Fintype.card ι = ε ^ (-d)`, the Rényi dimension of `μ` is *exactly* `d`
for every `q` and every `ε ∈ (0, 1)`. This is `renyiDimMeasure_equalMeasure` fed the count
`N = ε ^ (-d)`. -/
theorem renyiDimMeasure_uniform_eq_dim {α : Type*} {ι : Type*} [MeasurableSpace α] [Fintype ι]
    [Nonempty ι] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (P : ErgodicTheory.Entropy.MeasurePartition μ ι) {ε d : ℝ}
    (huniform : ∀ i, (μ (P.cells i)).toReal = (Fintype.card ι : ℝ)⁻¹)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hcard : (Fintype.card ι : ℝ) = ε ^ (-d)) (q : ℝ) :
    renyiDimMeasure μ P ε q = d :=
  renyiDim_uniform_eq_dim huniform hε0 hε1 hcard q

end ErgodicTheory.Multifractal
