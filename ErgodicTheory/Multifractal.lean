/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.Defs
import ErgodicTheory.Multifractal.Degeneracy
import ErgodicTheory.Multifractal.LogConvex
import ErgodicTheory.Multifractal.Monotone
import ErgodicTheory.Multifractal.Measure
import ErgodicTheory.Multifractal.RefiningLimit
import ErgodicTheory.Multifractal.LocalDimension
import ErgodicTheory.Multifractal.HausdorffDimension
import ErgodicTheory.Multifractal.SymbolicDimension
import ErgodicTheory.Multifractal.SymbolicDimensionBernoulli
import ErgodicTheory.Multifractal.Source.FlowEmpirical
import ErgodicTheory.Multifractal.Source.FlowPartition
import ErgodicTheory.Multifractal.BernoulliErgodic
import ErgodicTheory.Multifractal.BernoulliEntropy
import ErgodicTheory.Multifractal.BernoulliDimension
import ErgodicTheory.Multifractal.BernoulliTwoSided
import ErgodicTheory.Multifractal.BernoulliTwoSidedEntropy
import ErgodicTheory.Multifractal.BernoulliTwoSidedErgodic
import ErgodicTheory.Multifractal.BernoulliHeterogeneous
import ErgodicTheory.Multifractal.BernoulliSuspensionFlow
import ErgodicTheory.Multifractal.BernoulliSuspensionFlowErgodic
import ErgodicTheory.Multifractal.BernoulliSuspensionWitness
import ErgodicTheory.Multifractal.BernoulliTwoSidedGenerating
import ErgodicTheory.Multifractal.BernoulliTwoSidedSystemEntropy
import ErgodicTheory.Multifractal.BernoulliSuspensionEntropy
import ErgodicTheory.Multifractal.BernoulliSuspensionCondEntropy
import ErgodicTheory.Multifractal.BernoulliTwoSidedMixing
import ErgodicTheory.Multifractal.BernoulliSuspensionTimeOneErgodic
import ErgodicTheory.Multifractal.RenyiEntropy
import ErgodicTheory.Multifractal.RenyiRate
import ErgodicTheory.Multifractal.RenyiBernoulli

/-!
# Coarse-grained multifractal analysis of an invariant measure

This is the aggregator module for the **coarse-grained (finite-resolution) multifractal analysis**
of an invariant probability measure of a measure-preserving map or flow (issue #16). It collects
the finite-partition core: the generalized partition function `Z_q`, the mass exponent `τ(q)`, the
Rényi / generalized dimensions `D_q` (with the `q = 1` information-dimension branch), and the
singularity spectrum `f(α)` (the Legendre transform of `τ`), together with their basic theory.

## Layout

* `ErgodicTheory.Multifractal.Defs` — the four core definitions `partitionFunction` (`Z_q`),
  `massExponent` (`τ`), `renyiDim` (`D_q`), `singularitySpectrum` (`f(α)`) on an abstract weight
  family `p : ι → ℝ`, plus elementary lemmas (`Z_1 = 1`, `τ(1) = 0`, positivity, the `0 < p i`
  guard).
* `ErgodicTheory.Multifractal.Degeneracy` — the equal-measure (uniform / monofractal) degeneracy
  `Z_q = N^{1-q}`, `D_q ≡ log N / (-log ε)` (issue #16, item 4c).
* `ErgodicTheory.Multifractal.LogConvex` — the mathematical heart: log-convexity of `Z_q`
  (the Hölder / cumulant-convexity argument) and concavity of `τ`.
* `ErgodicTheory.Multifractal.Monotone` — the monotonicity `D_q` is non-increasing in `q`
  (issue #16, item 4b), over all of `ℝ`.
* `ErgodicTheory.Multifractal.Measure` — the measure/flow layer: the same quantities for an actual
  invariant probability measure `μ` and a finite `MeasurePartition`, the `q = 1` information
  dimension as Shannon entropy `/ (-log ε)`, and the connector to a `MeasurePreservingFlow`'s
  invariant measure.
* `ErgodicTheory.Multifractal.RefiningLimit` — the degenerate (uniform / monofractal) case of the
  refining-partition limit (issue #16, item 6): for a uniform family with `N = ε^{-d}` cells,
  `D_q(P_ε) = d` at every resolution, so the `ε → 0` limit is `d`.
* `ErgodicTheory.Multifractal.LocalDimension` — the pointwise local dimension
  `d_μ(x) = lim_{r→0} log μ(B(x,r)) / log r` (issue #16, item 5), with the **absolutely-continuous
  case** proved: for `μ ≪` Haar on a finite-dimensional real inner-product space, `d_μ(x) = finrank`
  a.e. (exact-dimensionality in the a.c. case).

The finite-resolution core (issue #16, items 1–4) is self-contained and sorry-free, as are the
uniform case of the refining limit (item 6) and the absolutely-continuous case of the local
dimension (item 5). What remains the genuine frontier is the **general (singular) exact-
dimensionality** — a.e.-constancy of `d_μ` for an SRB / hyperbolic measure and the Young /
Ledrappier–Young identity `d_μ = h_μ · (1/λ₁ − …)` — together with the general non-uniform refining
limit. These need the absolute continuity of conditional measures on unstable manifolds (the
Ledrappier–Young core), the same Mathlib-absent ingredient that blocks the library's Pesin–SRB work
(issue #10); the Lyapunov exponents, KS entropy, the Margulis–Ruelle inequality, and a pointwise
Birkhoff theorem are all already present in this library.
-/
