# CONTINUATION STATE — Oseledets frontier issues #8–#11

**This file is the single self-contained handoff.** Attach a new session to it ("read
`reports/CONTINUATION-STATE.md` and continue") and everything needed is here: role, infra, invariants,
current residuals (file:line), measured priorities, the method that worked, and the exact next actions.
Last updated 2026-06-22 (#8 AND #9 closed unconditionally + migrated into the linted `Oseledets`
library; only #11 and #10 remain). #9's chart-regularity wall fell to a measurable fixed-chart frame.

---

## 1. Role & goal

You are the CEO/orchestrator of an autonomous Lean 4 + Mathlib formalization campaign on
`marcmorningstar/lean4-oseledets`. You **delegate** to parallel `lean-worker`/`mathematician` agents in
warm git worktrees and **observe from the top**; you personally do all git/merges/authoritative builds.

The core Oseledets MET is COMPLETE. The open work is 4 research-level strengthenings = `BLOCKED` `sorry`
leaves in the unlinted `Frontier.Issue*` staging lib (GitHub issues #8/#9/#10/#11). A prior campaign
drove each from an opaque sorry to a small, sharp, literature-attributed residual — all faithful, no
unsoundness, `lake build` green, axiom audit unchanged. **Goal of a continuation run: close residuals,
sorry-free.**

## 2. Current state (branch `campaign/issues-8-11`, draft PR #12)

Residual sorries (authoritative — from `lake build` warnings, not docstring greps):

| Issue | File:line | Status |
|---|---|---|
| **#8** | `Oseledets/Lyapunov/Extensions/Yamamoto.lean` | ✅ **CLOSED sorry-free + MIGRATED to the linted lib** (proof `bf92e09`; migration `654837e`+`e874e6d`). `compoundMatrix_charpoly_roots_eq` proved via new `Frontier/Issue1/Schur.lean` (ℂ-Schur, a correctly-attributed Apache-2.0 graft of `leanprover-community/physlib`'s `Mathematics/SchurTriangulation.lean`) + functorial Cauchy–Binet (`compoundAbstract_mul` via `exteriorPower.map_comp`) + triangular-minor det lemmas + diagonal→`powersetCard` bridge. Axiom audit clean on the target + `yamamoto_singularValues_tendsto`/`exponents_const_general`/`spectralRadius_compound_eq_prod_eigenvalueModuli`. **✅ MIGRATED to the linted `Oseledets/` library**: Schur delinted into the quarantined shim `Oseledets/Mathlib/SchurTriangulation.lean` (physlib attribution kept, `autoImplicit`→explicit per-section `variable`s — incl. a shared `universe u` for the `cond b m n` instances and a decl-level `{E}` on `SchurTriangulationAux.of`); Yamamoto at `Oseledets/Lyapunov/Extensions/Yamamoto.lean` (import re-pointed, lines wrapped, `push_neg`→`push Not`). Both imported from `Oseledets.lean`; 4 `#print axioms` guards in `test/AxiomAudit.lean` confirm `[propext, Classical.choice, Quot.sound]`. Full `lake build` green under `warningAsError`; `Frontier/Issue1` removed. **#8 fully done.** |
| **#9** | `Oseledets/Smooth/{FrameAlg,Framing,UnconditionalFraming,UnconditionalMET}.lean` | ✅ **CLOSED UNCONDITIONALLY + MIGRATED to the linted lib** (`356c731`+`2f1aa5b`+`081cd50`). The `LocallyConstantChartAt` hypothesis is **GONE**. Breakthrough: `MeasurableFraming` needs only the *conjugated generator* measurable, not the frame — so a **piecewise fixed-reference-chart** frame over a disjointified countable atlas makes `framedGenerator` equal the fixed-chart `fderivWithin(extChartAt b ∘ T ∘ (extChartAt a).symm)` (continuous, C¹), measurable on the countable Borel partition; the moving `chartAt` cancels algebraically, so NO chart regularity is needed. Delivered: `exists_measurableFraming_of_sigmaCompact` (no LCC) + the framed-cocycle MET `oseledets_filtration_framedTangentCocycle`/`exists_oseledets_filtration_framedTangentCocycle` (`hAmeas` discharged unconditionally). 3 `#print axioms` guards = the standard triple; `lake build` green under `warningAsError`. Superseded LCC chain (`LocallyConstantChartAt`/`MFDerivMeasurable`/`Existence`/canonical `DerivativeCocycleManifold`) removed; `Frontier/Issue2` deleted. **#9 fully done.** |
| **#10** | `Frontier/Issue4Pesin/ManeLowerBound.lean:177,208` | ⛔ Out of scope (unchanged). Layer-1 (SMB + countable-partition KS-entropy API) + Layer-2 foliation chain (abs. continuity of Wᵘ, disintegration of μ along Wᵘ): measured ~4–6 months, 8 nodes in series, no Mathlib precursors. 2 sorries. |
| **#11** | `Frontier/Issue6/ArseninKunugui.lean:301` (+ `CastaingSelection.lean:479`, `MeasurableGraphToProjector.lean:405`) | ⛔ **BLOCKED — missing Mathlib chapter** (confirmed, grep-verified). `exists_borel_openSection_structure` = Srivastava 4.7.2 needs the **coanalytic pointclass + generalized reduction theorem 4.6.5** (absent; Mathlib has only the first-separation engine `AnalyticSet.measurablySeparable`/`MeasurablySeparable.iUnion`). The re-scoping shortcut provably fails. **Correction to prior handoff:** the 2 extra sorry sites are NOT a 1-line forward — `_AK` lives in the top module `ArseninKunugui` but the stale sorries are in modules it imports (`CastaingSelection`←`MeasurableGraphToProjector`), so collapsing 3→1 needs relocating the `_AK` core to a base module (a real, if mechanical, refactor of a blocked wall). ~2–4 sessions to actually close. |

Headline signatures faithful vs pre-campaign `origin/main` except the documented, approved additions:
#8 benign `[NeZero d]`. **#9 carries NO added hypothesis** — the earlier `[LocallyConstantChartAt H M]`
was superseded and removed (the result is now unconditional). No `axiom`/`native_decide`/`admit`/
`sorryAx`/`implemented_by` anywhere. **Lessons:** (1) a sharp-looking isolated `sorry` is not
automatically a *true* lemma — re-verify the *statement*; (2) a campaign "wall" may be an
over-constraint — #9 fell once we used a **measurable** fixed-chart frame instead of forcing the
moving-index map *continuous*. Re-examine each wall for an architectural shortcut before declaring it
Mathlib-scale (this directly cracked #9, rated "days–weeks Mathlib-scale", in one run).

## 3. Measured priority queue (from the dependency-DAG spike — critical-path depth × parallel width)

Ranked by **measured** effort (DAG reports `docs/research/frontier/issue{4,6}/DAG-*.md`, Mathlib
node-availability grep-verified + adversarially audited). Parallel-Claude wall-clock ≈ critical-path
depth × per-node design+prove time (breadth is absorbed by running many warm agents at once).

**#8 and #9 are both COMPLETE** — sorry-free, migrated into the linted upstreamable `Oseledets`
library, axiom-audited, and **closed on GitHub**. #8: proof `bf92e09`, migration `654837e`+`e874e6d`.
#9: **UNCONDITIONAL** (no `LocallyConstantChartAt`), `356c731`+`2f1aa5b`+`081cd50`. Remaining open work, ranked:

| Priority | Target | Parallel-Claude | Notes |
|---|---|---|---|
| **✅ DONE** | **#8 → `Oseledets/`** | done (`654837e`+`e874e6d`) | Migrated: Schur vendored as the quarantined `Oseledets/Mathlib/SchurTriangulation.lean` shim (delint-only — `autoImplicit`→explicit per-section `variable`s incl. a shared `universe u` for the `cond` instances + decl-level `{E}` on `.of`; `push_neg`→`push Not`), Yamamoto at `Oseledets/Lyapunov/Extensions/Yamamoto.lean`, 4 axiom guards added, `Frontier/Issue1` removed. `lake build` green under `warningAsError`. |
| **✅ DONE** | **#9 unconditional** | done (`356c731`+`2f1aa5b`+`081cd50`) | `LocallyConstantChartAt` was NOT needed: a piecewise fixed-reference-chart frame makes `framedGenerator` a fixed-chart `fderivWithin` (continuous C¹, measurable unconditionally), since `MeasurableFraming` requires only the *generator* measurable. Migrated to `Oseledets/Smooth/`, axiom-audited, closed. The over-constraint was forcing the moving-index map *continuous*; **measurable** suffices for the MET. |
| **3** | **#11** | ~2–4 sessions | **BLOCKED on a missing Mathlib chapter**: the coanalytic pointclass + generalized reduction theorem 4.6.5 (Srivastava). Mathlib has only the first-separation engine. Build: `CoanalyticSet` + closure lemmas → 4.6.5 reduction induction (the heart) → 4.7.1 → 4.7.2 (`exists_borel_openSection_structure`); then relocate `_AK` to a base module + forward the 2 stale sorries. The re-scoping shortcut provably fails. |
| **4** | **#10** | ~4–6 months | Genuinely large; 8 design-novel nodes in **series** (Layer-2 foliation: abs. continuity of Wᵘ, disintegration of μ along Wᵘ — no Mathlib precursors). Don't brute-force; at most land SMB as a standalone. |

**Recommended next run:** **#8 and #9 are both done** (closed unconditionally, migrated, axiom-audited).
The only open issues are **#11** (priority 3 — Arsenin–Kunugui measurable projection; the handoff calls
it blocked on a missing coanalytic/reduction Mathlib chapter, ~2–4 sessions) and **#10** (priority 4,
~4–6 months). **Before grinding either, run a skeptical #9-style recon: is the "wall" a real Mathlib gap
or a campaign over-constraint with an architectural shortcut?** #9 was rated "days–weeks Mathlib-scale"
and fell in one run once we replaced the continuity requirement with measurability. For #11, test
whether the projection/selection can route through `AnalyticSet.measurablySeparable` /
universal-measurability (already in Mathlib via `Oseledets.MeasureTheory.AnalyticUniversallyMeasurable`)
rather than the full coanalytic reduction theorem. Optional polish on #8: when Mathlib gains its own
Schur decomposition, delete the `Oseledets/Mathlib/SchurTriangulation.lean` shim and re-point `Yamamoto`.

## 4. Infrastructure (all verified working)

- **`gh`** is installed + authenticated — use it for issues/PRs. (`gh pr edit` may hit a Projects-classic
  GraphQL bug → PATCH via REST API with a token from `git credential fill`, host github.com.) Refs #8–#11,
  don't auto-close.
- **Warm lean-worker:** `.claude/scripts/lwt add <branch>` → warm worktree under `/home/vscode` (Mathlib
  cache symlinked — NEVER let a build recompile Mathlib; the `ContMDiffMFDeriv` subtree IS cached, fine to
  import). Prereq: leancheck plugin installed (`claude plugin install leancheck@lean-tools`). Subagents may
  run `lwt` but are git-BLOCKED (`.claude/hooks/block-subagent-git.sh`); leancheck auto-reports after each
  worker edit. Pre-provision worktrees **serially** from the orchestrator (avoids a `git worktree add` race).
- **firecrawl** CLI preconfigured for literature (`firecrawl search/scrape/map`).
- **RAM ceiling:** ~6–8 concurrent warm builds safe (32 cores, ~25 GB free; user OKs up to 15 agents,
  stagger cold builds). Resource watchdog templates in `reports/infra/`.
- **Build gates:** `lake build Frontier.<Module>` (staging, sorry-OK) for iteration; `lake build`
  (default `Oseledets`+`AxiomAudit`+`Frontier` root, must stay green) as the library gate.

## 5. Invariants (never violate)

1. Every Lean worker gets its OWN warm `lwt` worktree.
2. **Workers never run git**; the orchestrator does all merges/commits/pushes + authoritative builds.
3. Never `sorry`/axiomatize in the imported `Oseledets` lib. Partial work stays in `Frontier.Issue*`.
4. **Migrate `Frontier.Issue*` → `Oseledets/` only when fully sorry-free**, then keep
   `#print axioms = [propext, Classical.choice, Quot.sound]`.
5. Don't weaken a headline to "close" it; honest added hypotheses are OK but must be documented + QA-checked.
6. Multiple adversarial QA passes; commit + push at every milestone; report progress to files + issues.

## 6. Method that worked (reuse it)

Background **Workflow** super-workflows in waves: `pipeline(implement → mathematician QA)`, with
`agentType:'lean-worker'` for impl and `agentType:'mathematician'` for adversarial QA, forced structured
schema output. **Tournament**: run 2–3 independent attempts per wall (distinct strategies), keep the best
branch (they touch the same file in separate worktrees → no conflict, you merge one). Integrate by copying
the winning (disjoint) files into the campaign branch, authoritative-build, commit, push. Tear down
worktrees + monitors at the end. The campaign ran recon → 3 implementation waves → a DAG spike; ~35 agents,
0 RAM alerts.

## 7. Pointers
- Narrative retrospective: `reports/CAMPAIGN-FINAL-REPORT.md`
- Per-wave detail: `reports/implementation/WAVE1-RESULTS.md` + workflow outputs
- Feasibility recon: `docs/research/frontier/issue*/FEASIBILITY-*.md`
- Measured DAGs: `docs/research/frontier/issue{4,6}/DAG-*.md`
- Memory: `memory/frontier-campaign-infra.md`, `memory/frontier-campaign-outcome.md`
