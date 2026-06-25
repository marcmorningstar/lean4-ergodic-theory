/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Multifractal.Defs
import Oseledets.Multifractal.Degeneracy
import Oseledets.Multifractal.LogConvex
import Oseledets.Multifractal.Monotone
import Oseledets.Multifractal.Spectrum
import Oseledets.Multifractal.Measure

/-!
# Coarse-grained multifractal analysis of an invariant measure

This is the aggregator module for the **coarse-grained (finite-resolution) multifractal analysis**
of an invariant probability measure of a measure-preserving map or flow (issue #16). It collects
the finite-partition core: the generalized partition function `Z_q`, the mass exponent `τ(q)`, the
Rényi / generalized dimensions `D_q` (with the `q = 1` information-dimension branch), and the
singularity spectrum `f(α)` (the Legendre transform of `τ`), together with their basic theory.

## Layout

* `Oseledets.Multifractal.Defs` — the four core definitions `partitionFunction` (`Z_q`),
  `massExponent` (`τ`), `renyiDim` (`D_q`), `singularitySpectrum` (`f(α)`) on an abstract weight
  family `p : ι → ℝ`, plus elementary lemmas (`Z_1 = 1`, `τ(1) = 0`, positivity, the `0 < p i`
  guard).
* `Oseledets.Multifractal.Degeneracy` — the equal-measure (uniform / monofractal) degeneracy
  `Z_q = N^{1-q}`, `D_q ≡ log N / (-log ε)` (issue #16, item 4c).
* `Oseledets.Multifractal.LogConvex` — the mathematical heart: log-convexity of `Z_q` (the Hölder /
  cumulant-convexity argument) and concavity of `τ`.
* `Oseledets.Multifractal.Monotone` — the monotonicity `D_q` is non-increasing in `q` (issue #16,
  item 4b), over all of `ℝ`.
* `Oseledets.Multifractal.Spectrum` — the singularity-spectrum (Legendre transform) bounds for
  `f(α)` (issue #16, item 3).
* `Oseledets.Multifractal.Measure` — the measure/flow layer: the same quantities for an actual
  invariant probability measure `μ` and a finite `MeasurePartition`, the `q = 1` information
  dimension as Shannon entropy `/ (-log ε)`, and the connector to a `MeasurePreservingFlow`'s
  invariant measure.

The finite-resolution core (issue #16, items 1–4) is self-contained and sorry-free. The pointwise
local dimension and the refining-partition limit (items 5–6) are not part of this layer.
-/
