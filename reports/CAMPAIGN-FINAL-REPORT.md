# Oseledets Frontier Campaign — Final Report (2026-06-22)

> **To continue the work, attach a session to `reports/CONTINUATION-STATE.md`** — the single
> self-contained handoff (current residuals, measured priorities, infra, invariants, next actions).
> This file is the narrative retrospective.


Autonomous CEO-orchestrated effort to resolve the 4 open GitHub issues (#8, #9, #10, #11) — the
research-level `BLOCKED` leaves of the otherwise-complete Oseledets MET formalization.

## Outcome in one line

**No issue fully closed sorry-free** (each was correctly labelled research-level), but **every wall
was driven from an opaque black-box `sorry` down to its true mathematical floor**: a small set of
sharp, individually-typed, literature-attributed residual lemmas — all faithful (no headline
weakened), no hidden unsoundness, build green throughout. Two walls (#8, #9) now rest on a **single**
missing Mathlib primitive each.

## Method

3 super-workflows in waves of warm `lwt` worktrees (one per agent), every implementation agent
pipelined into an adversarial `mathematician` QA pass (≥4 QA passes total + a final end-to-end
faithfulness diff). Orchestrator did all git/merges/authoritative builds; workers were git-blocked
and iterated on warm leancheck. Resource watchdog ran throughout — **zero RAM alerts**.

- **Recon** (4 agents): firecrawl literature + Mathlib grep → honest feasibility per issue.
- **Wave 1** (8 agents): decompose every wall. **Wave 2** (6 agents): drive closeable walls to a
  single residual. **Wave 3** (5 agents): final closure push on #8 & #9's single residuals.
- ~30 agent-runs, ~4.0M subagent tokens. Branch `campaign/issues-8-11`.

## Per-issue final state

### #8 — Yamamoto singular-value limit  → **1 residual** (closest to closure)
Strategy C (exterior-power / Gelfand) succeeded structurally. Now sorry-free: Gelfand-for-compound
(`tendsto_prod_singularValues_pow`), the `^{1/n}`→`(1/n)log` telescoping (`yamamoto_prod_to_index`),
the nilpotency/vanishing bridge, spectral-radius = max charpoly-root-modulus, sorting, and the `j>d`
boundary. The **named issue leaf** `spectralRadius_compound_eq_prod_eigenvalueModuli` is itself now
sorry-free. **Single residual:** `spectrum(exteriorPower.map(M_ℂ)) = the j-fold products of M's
eigenvalues` (`Yamamoto.lean:352`) — needs ℂ-triangularization (Schur or generalized-eigenspace
flag), a self-contained matrix-analysis development absent from Mathlib.

### #9 — measurability of the manifold derivative cocycle  → **1 residual**
The entire chain is sorry-free — incl. `Existence.lean` and `DerivativeCocycleManifold.lean` (**zero
sorry**), the headline `oseledets_filtration_derivativeCocycleManifold`, the constant-frame collapse
of the framing leaf, the un-conjugation telescoping, the dual coordinate-change factor (closed via
`ContinuousLinearMap.inverse` continuity), and the Lindelöf countable-cover measurable gluing — all
under the honest hypotheses `[I.Boundaryless]`, `ContMDiff I I 1 T`, σ-compact. **Single residual:**
`continuousOn_tangentCoordChange_movingIndex` (`MFDerivMeasurable.lean:150`) — continuity of the
tangent-bundle coordinate change with **moving trivialization index**; Mathlib provides this only for
*fixed* indices. Three independent agents confirmed it is a genuine missing primitive, not a reachable
gap.

### #10 — Pesin entropy formula, SRB reverse inequality  → at honest floor (2 residuals)
The one reachable analytic substep **L1b** (Radon–Nikodym density rate via the Lévy-upward martingale
`Integrable.tendsto_ae_condExp`) is now **sorry-free** (`rate_log_div_tendsto_zero_of_tendsto_pos`).
The opaque sorry was split into two literature-typed leaves: `manePropLowerBound` (Mañé Layer 1, Prop
7.7 — needs a *countable*-partition Kolmogorov–Sinai API + the **Shannon–McMillan–Breiman** theorem,
both absent from Mathlib) and `localEntropy_ge_unstableJacobian` (Layer 2 — the genuine multi-year
Pesin / Ledrappier–Young geometry: measurable Eˢ⊕Eᵘ splitting, unstable foliation + its absolute
continuity, leaf disintegration). Not pursued further — a confirmed multi-year wall.

### #11 — Arsenin–Kunugui everywhere-Borel projection  → **1 residual** (definitive DST wall)
Re-routed (Strategy B) so the everywhere-Borel issue-#6 target rests on a single Euclidean box leaf
`measurableSet_image_fst_of_subset_compact_box` (`ArseninKunugui.lean:297`). Two independent agents +
literature (Srivastava §4.7) confirmed it reduces to **Novikov 4.6.5 (the coanalytic reduction
theorem)** — the coanalytic (Π¹₁) pointclass is absent from Mathlib; a genuine multi-PR descriptive-
set-theory development. The downstream consumers (`CastaingSelection:476`, `MeasurableGraphToProjector:398`)
are chained to this one wall. (The **a.e.** singular filtration — the standard MET notion — was
already done sorry-free pre-campaign; this is the everywhere-Borel strengthening.)

## Residual sorry census (authoritative, from `lake build` warnings)
```
#8  Frontier/Issue1/Yamamoto.lean:352              spectrum of exterior power = j-fold products
#9  Frontier/Issue2/MFDerivMeasurable.lean:150     moving-index tangent coordinate-change continuity
#10 Frontier/Issue4Pesin/ManeLowerBound.lean:166   Mané Layer 1 (countable-partition KS + SMB)
#10 Frontier/Issue4Pesin/ManeLowerBound.lean:201   Mané Layer 2 (Pesin/Ledrappier–Young geometry)
#11 Frontier/Issue6/ArseninKunugui.lean:297        Novikov 4.7.4 box leaf (coanalytic reduction)
#11 Frontier/Issue6/CastaingSelection.lean:476     consumer, chained to #11 wall
#11 Frontier/Issue6/MeasurableGraphToProjector.lean:398  consumer, chained to #11 wall
```
`lake build` (default `Oseledets`+`AxiomAudit`+`Frontier` root): **green**; headline MET axiom audit
unchanged = `[propext, Classical.choice, Quot.sound]`. Nothing migrated to `Oseledets/` (correct:
migration requires sorry-free).

## Recommended next steps — measured by the dependency-DAG spike (critical-path depth × width)
The "next steps" are now ranked by **measured** effort, not vibes (DAG reports:
`docs/research/frontier/issue{4,6}/DAG-*.md`; Mathlib node-availability grep-verified + adversarially
audited). Parallel-Claude wall-clock ≈ critical-path-depth × per-node design+prove time (breadth is
absorbed by running many warm-worktree agents at once).

| Target | Residual | depth × width | Parallel-Claude | Human/PR cadence |
|---|---|---|---|---|
| **#9** (most tractable) | `continuousOn_tangentCoordChange_movingIndex` (one tangent-bundle lemma) | shallow | ~a session | days |
| **#8** | `spectrum(⋀ʲA) = j-fold products` (needs ℂ-triangularization) | shallow | days–~2 wks | weeks |
| **#11** (near-term — RECLASSIFIED) | one sorry `4.7.2`, chain `4.6.5 → 4.7.1 → 4.7.2` | 3 × 1 | ~1–2.5 wks | ~6–10 wks (1–2 PRs) |
| **#10** (genuinely large) | 8 design-novel nodes in series (foliation AC, disintegration along Wᵘ) | 8 × 6 | ~4–6 months | ~3–6 years |

**#11 reclassified** from "multi-year DST programme" to near-term: the full Effros/Π¹₁/transfinite-
derivative tower is absent from Mathlib BUT off the critical path (the repo routes through a Euclidean
re-route), and Mathlib already has the separation engine (`MeasurablySeparable.iUnion`,
`measurablySeparable_range_of_disjoint`). Real remaining work = the 4.6.2 generalized-first-separation
induction + the 4.7.1/4.7.2 structure lemmas. **#10** stays large because its critical path is 8
*serial* design-novel nodes — parallelism absorbs the off-path Layer-1 (SMB + countable-partition KS
API) but cannot compress the Layer-2 foliation chain (Amdahl's law); the two deepest nodes (absolute
continuity of Wᵘ, disintegration of μ along Wᵘ) are the historically hardest pieces of Ledrappier–Young
and have no Mathlib precursors.

Detailed per-wave records: `reports/implementation/WAVE1-RESULTS.md`, the workflow outputs, and the
recon feasibility reports under `docs/research/frontier/issue*/FEASIBILITY-*.md`.
