# Oseledets MET formalization — final composition

> **Status: COMPLETE.** The one-sided Oseledets multiplicative ergodic theorem is proved
> sorry-free, together with its companion corollaries, ten additive extensions, the two-sided
> splitting, the continuous-flow version, and a finite-dimensional **quantum-information layer**
> (operator entropy, Lieb joint convexity, the partial-trace data-processing inequality, CNT dynamical
> entropy, and Petz recovery + equality — issues #22–#28). The whole library builds clean, is enforced
> linter-clean under `linter.mathlibStandardSet` (warnings promoted to errors in `lakefile.toml`,
> so `lake build` and CI fail on any lint regression), and every headline result is guarded in
> `test/AxiomAudit.lean` (a separate `AxiomAudit` lib, so the library source carries no
> `#print axioms`) to depend on exactly `[propext, Classical.choice, Quot.sound]` (the build fails
> if this ever drifts). This document maps the finished library.

## Core theorem

* `ErgodicTheory.oseledets_filtration` (`ErgodicTheory/MultiplicativeErgodic.lean`) — the one-sided MET
  in filtration form: for an ergodic measure-preserving `T` and an integrable invertible matrix
  cocycle generator, `k` distinct Lyapunov exponents `λ₁ > ⋯ > λ_k` and a measurable
  `A`-equivariant flag along which `(1/n) log‖A⁽ⁿ⁾(x) v‖ → λᵢ` on each stratum.
* `ErgodicTheory.IsOseledetsFiltration` + `oseledets_filtration'`
  (`ErgodicTheory/Lyapunov/Extensions/Corollaries.lean`)
  — the conclusion bundled as a consumable predicate.

## Companion corollaries (`ErgodicTheory/Lyapunov/Extensions/Corollaries.lean`)

Canonical growth-sublevel characterization `IsOseledetsFiltration.ae_mem_iff_limsup_le` and
uniqueness; top exponent = operator-norm growth rate; a.e.-constant multiplicities / dimensions.

## Additive extensions (`ErgodicTheory/Lyapunov/Extensions/`)

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

## Two-sided splitting (`ErgodicTheory/TwoSided/`)

`ErgodicTheory.oseledets_splitting` (`SplittingAssembly.lean`) — for an invertible base, an invariant
`DirectSum.IsInternal` decomposition `Eᵢ = Vᵢ ⊓ W_{rev i}` with two-sided growth `±λᵢ`, assembled
from the backward cocycle, the reflection of the spectrum, transversality, and the restricted
backward envelope (phases P0–P8).

## Continuous-flow MET (`ErgodicTheory/Continuous/`)

`ErgodicTheory.oseledets_flow` (`MultiplicativeErgodicFlow.lean`) — the continuous-time / measure-
preserving-ℝ-flow version: exponents, a measurable **flow-equivariant** filtration
(for each `t`, for a.e. `x`, `map (A t x) (Vⁱ x) = Vⁱ (φ t x)` — the null set depends on `t`, weaker
than a single flow-invariant conull set), and exact **continuous-parameter** growth
`(1/t) log‖A(t,x) v‖ → λᵢ` as `t → ∞`. Built by reducing to the discrete theorem at the time-1
map (`Flow.lean` reduction identity, `Reduction.lean`), upgrading integer-time growth to the
continuous parameter via a between-times sandwich (`BetweenTimes.lean`), and proving real-time
equivariance via a discrete-limsup shift-invariance (`Equivariance.lean`).

## Quantum-information layer (`ErgodicTheory/OperatorEntropy/`)

A self-contained finite-dimensional quantum-information cluster added on top of the MET core
(issues #22–#28), reusing the repo's matrix / continuous-functional-calculus infrastructure.
All results are sorry-free, linter-clean, and guarded in `test/AxiomAudit.lean`.

* **Foundations** (`Basic.lean`, `RelativeEntropy.lean`, `Klein.lean`) — `DensityMatrix`, the von
  Neumann entropy, the Umegaki relative entropy `S(ρ‖σ) = Tr ρ(log ρ − log σ)`, and the scalar
  Klein / Peierls inequality.
* **Subadditivity & Lieb** (`Lieb/`) — Klein's inequality ⟹ subadditivity, and **Lieb's theorem**,
  the joint convexity of the quantum relative entropy (`relEntropyMat_jointly_convex`).
* **Data processing** (`Lieb/DataProcessing*.lean`) — the **partial-trace data-processing inequality**
  `S(Tr_E ρ ‖ Tr_E σ) ≤ S(ρ‖σ)` for arbitrary ρ and faithful σ (`relEntropyMonotone_partialTrace`), its
  **faithful-ancilla Stinespring-family** extension (`monotonicity_relEntropy_under_stinespring`), and the
  no-section obstruction. (No DPI for an arbitrary CPTP/Kraus channel is claimed.)
* **Petz recovery + equality** (`Lieb/`) — the **Petz recovery map** and **both directions of
  Petz's equality theorem**: recovery ⟹ saturation of the DPI (`petz_recovery_implies_equality`,
  #22) and, fully general (#28), saturation ⟹ recovery (`petz_equality_recovery_general`, for
  every faithful-state `KrausChannel`), whose analytic heart is the modular-cocycle intertwining
  `partialTrace_equality_imp_intertwinesIt`.
* **Dynamical entropy** (`CNT/`) — the CNT / ALF quantum dynamical entropy, whose **abelian corner
  recovers the classical Kolmogorov–Sinai entropy** (`cntDynamicalEntropyAbelian_eq_ksEntropy`) —
  the bridge back to the MET core's ergodic theory.

## Conventions (pinned)

Cocycle newest-factor-left; scoped L2 operator norm `Matrix.Norms.L2Operator`; vectors
`EuclideanSpace ℝ (Fin d)` acted on via `Matrix.toEuclideanCLM`; GL encoded as `det ≠ 0`;
`log⁺ = Real.posLog`; subspace measurability via `orthProjMatrix` / `MeasurableSubspace`;
`autoImplicit` off (declare all variables); new modules imported from `ErgodicTheory.lean`.

## Build

`lake build` (incremental, whole-library; the efficient inner loop and the authoritative QA gate
together with `AxiomAudit`). **Never `lake exe cache get` in this devcontainer** — the cache host
is DNS-blocked; the Mathlib cache is already present. Warm per-edit feedback is provided by the
external `leancheck` Claude plugin (`github.com/marcmorningstar/leancheck`).
