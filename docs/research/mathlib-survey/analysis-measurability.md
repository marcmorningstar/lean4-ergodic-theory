# Mathlib survey — area: analysis-measurability

Scope: measurability/integrability of matrix-valued and `log ‖A(x)‖`-type
functions; flag/Grassmannian types; `limsup`/`liminf`/`Tendsto` for `(1/n)·log`
limits; `Real.log`, `log⁺` (`posLog`), `Integrable` plumbing for the Oseledets
multiplicative ergodic theorem (MET). Paths relative to the `Mathlib` package
root. Read from source at v4.30.0-rc2 (not typechecked).

## Executive summary (build-vs-reuse boundary)

REUSE: Borel/measurable structure on `Matrix m n α` (it is definitionally
`m → n → α`, inherits Pi MeasurableSpace/Topology/BorelSpace and, for finite
indices over `ℝ`, SecondCountableTopology ⇒ Measurable ↔ StronglyMeasurable);
continuity (⇒ measurability) of all matrix ops (mul/det/trace/...);
measurable_log, measurable_norm, measurable_real_toNNReal; Real.posLog (`log⁺`)
with prod/sum/mul subadditivity estimates; full Integrable/AEStronglyMeasurable
API; limsup/liminf/Tendsto + tendsto_of_liminf_eq_limsup + Measurable.limsup;
Fekete's subadditive lemma (Subadditive.tendsto_lim); Flag (Submodule K V) +
Module.Basis.toFlag; Hermitian spectral theorem / PosSemidef / singularValues /
gramSchmidt / finrank.

MUST BUILD: Kingman subadditive ergodic theorem (absent); Birkhoff pointwise
ergodic theorem (only mean/von Neumann exists); ErgodicTheory/Lyapunov/Furstenberg
(none); measurable family of subspaces / measurable flag structure (no Borel
structure on Flag/Grassmannian); subspace-Grassmannian (Module.Grassmannian uses
quotient convention); packaged Integrable(log⁺‖A‖) + posLog measurability.

See full detail in the StructuredOutput `found`/`missing`/`notes` fields.
