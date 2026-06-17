# Oseledets MET formalization — final composition

> **Status: COMPLETE.** The one-sided Oseledets multiplicative ergodic theorem is proved
> sorry-free, together with its companion corollaries, ten additive extensions, the two-sided
> splitting, and the continuous-flow version. The whole library builds clean, is Mathlib-style
> linter-clean under `linter.mathlibStandardSet`, and every headline result is guarded in
> `test/AxiomAudit.lean` (a separate `AxiomAudit` lib, so the library source carries no
> `#print axioms`) to depend on exactly `[propext, Classical.choice, Quot.sound]` (the build fails
> if this ever drifts). This document maps the finished library.

## Core theorem

* `Oseledets.oseledets_filtration` (`Oseledets/MultiplicativeErgodic.lean`) — the one-sided MET
  in filtration form: for an ergodic measure-preserving `T` and an integrable invertible matrix
  cocycle generator, `k` distinct Lyapunov exponents `λ₁ > ⋯ > λ_k` and a measurable
  `A`-equivariant flag along which `(1/n) log‖A⁽ⁿ⁾(x) v‖ → λᵢ` on each stratum.
* `Oseledets.IsOseledetsFiltration` + `oseledets_filtration'` (`Oseledets/Lyapunov/Corollaries.lean`)
  — the conclusion bundled as a consumable predicate.

## Companion corollaries (`Oseledets/Lyapunov/Corollaries.lean`)

Canonical growth-sublevel characterization `IsOseledetsFiltration.ae_mem_iff_limsup_le` and
uniqueness; top exponent = operator-norm growth rate; a.e.-constant multiplicities / dimensions.

## Additive extensions (`Oseledets/Lyapunov/`)

* `Spectrum.lean` — the full Lyapunov spectrum as a consumable object (`exponents`, antitone,
  `exponents_tendsto_log_singularValue`).
* `ExponentSums.lean` — positive/nonneg/negative exponent sums, sign/vanishing, top-`k` telescoping.
* `ExteriorCocycle.lean` — exterior/wedge (k-volume) growth via the compound cocycle.
* `DetIdentity.lean` — trace/determinant identity (`sumAllExp_eq_integral_log_abs_det`).
* `Inverse.lean` — inverse / time-reversal (`singularValues_inv`, `topExponent_inv_eq_neg_bot`).
* `Restriction.lean` — restriction to an invariant subbundle: sub-spectrum interlacing, and the
  **full restricted (strict) Oseledets filtration** realized inside the subbundle
  (`restricted_strict_filtration`, with top level `W` via explicit conjuncts since the ambient
  `IsOseledetsFiltration` hard-codes `V 0 = ⊤`).
* `NonErgodic.lean` — non-ergodic relaxation (a.e.-defined exponents).
* `Regularity.lean` — Fekete inf form, upper/lower semicontinuity of the exponents in the generator,
  and the **L¹ / uniform-integrability (Vitali) regime** (`tendsto_integral_logSprod_of_unifIntegrable`
  and the a.e.-convergence helper) feeding the same USC results under a.e. generator convergence.
* `Singular.lean` — one-sided results without invertibility: `log⁺` upper bounds, their **genuine
  EReal limits**, and the **bare-log `limsup` = top exponent** sharpening when that exponent is
  positive (a genuine bare-log limit is false for singular cocycles).

## Two-sided splitting (`Oseledets/TwoSided/`)

`Oseledets.oseledets_splitting` (`SplittingAssembly.lean`) — for an invertible base, an invariant
`DirectSum.IsInternal` decomposition `Eᵢ = Vᵢ ⊓ W_{rev i}` with two-sided growth `±λᵢ`, assembled
from the backward cocycle, the reflection of the spectrum, transversality, and the restricted
backward envelope (phases P0–P8).

## Continuous-flow MET (`Oseledets/Continuous/`)

`Oseledets.oseledets_flow` (`MultiplicativeErgodicFlow.lean`) — the continuous-time / measure-
preserving-ℝ-flow version: exponents, a measurable **flow-equivariant** filtration
(`map (A t x) (Vⁱ x) = Vⁱ (φ t x)` for all real `t`), and exact **continuous-parameter** growth
`(1/t) log‖A(t,x) v‖ → λᵢ` as `t → ∞`. Built by reducing to the discrete theorem at the time-1
map (`Flow.lean` reduction identity, `Reduction.lean`), upgrading integer-time growth to the
continuous parameter via a between-times sandwich (`BetweenTimes.lean`), and proving real-time
equivariance via a discrete-limsup shift-invariance (`Equivariance.lean`).

## Conventions (pinned)

Cocycle newest-factor-left; scoped L2 operator norm `Matrix.Norms.L2Operator`; vectors
`EuclideanSpace ℝ (Fin d)` acted on via `Matrix.toEuclideanCLM`; GL encoded as `det ≠ 0`;
`log⁺ = Real.posLog`; subspace measurability via `orthProjMatrix` / `MeasurableSubspace`;
`autoImplicit` off (declare all variables); new modules imported from `Oseledets.lean`.

## Build

`lake build` (incremental, whole-library; the efficient inner loop and the authoritative QA gate
together with `AxiomAudit`). **Never `lake exe cache get` in this devcontainer** — the cache host
is DNS-blocked; the Mathlib cache is already present. Warm per-edit feedback is provided by the
external `leancheck` Claude plugin (`github.com/marcmorningstar/leancheck`).
