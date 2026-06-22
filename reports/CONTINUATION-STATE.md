# CONTINUATION STATE — Oseledets frontier issues #8–#11

**This file is the single self-contained handoff.** Attach a new session to it ("read
`reports/CONTINUATION-STATE.md` and continue") and everything needed is here: role, infra, invariants,
current residuals (file:line), measured priorities, the method that worked, and the exact next actions.
Last updated 2026-06-22.

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

| Issue | File:line | The one missing thing | Status |
|---|---|---|---|
| **#8** | `Frontier/Issue1/Yamamoto.lean:352` | `spectrum(exteriorPower.map M_ℂ) = j-fold products of eigenvalues` (needs ℂ-triangularization: Schur or `Module.End.iSup_maxGenEigenspace_eq_top` + wedge-basis charpoly). The named issue leaf itself is already sorry-free; everything else in #8 too. | 1 sorry |
| **#9** | `Frontier/Issue2/MFDerivMeasurable.lean:150` | `continuousOn_tangentCoordChange_movingIndex`: continuity of the tangent coord change with **moving** trivialization index (= `x ↦ mfderiv I I (chartAt H c) x`). Mathlib has only the fixed-index `continuousOn_tangentCoordChange`. **`Existence.lean` + `DerivativeCocycleManifold.lean` + the headline are already sorry-free.** | 1 sorry |
| **#10** | `Frontier/Issue4Pesin/ManeLowerBound.lean:166,201` | Mañé Layer 1 (`manePropLowerBound`: needs Shannon–McMillan–Breiman + countable-partition KS-entropy API) and Layer 2 (`localEntropy_ge_unstableJacobian`: multi-year Pesin geometry). L1b already sorry-free. | 2 sorries |
| **#11** | `Frontier/Issue6/ArseninKunugui.lean:297` (+ chained `CastaingSelection.lean:476`, `MeasurableGraphToProjector.lean:398`) | `measurableSet_image_fst_of_subset_compact_box` = Srivastava 4.7.2; chain `4.6.5 → 4.7.1 → 4.7.2`. | 1 sorry (+2 chained) |

Headline signatures verified faithful vs pre-campaign `origin/main` (only honest added hypotheses:
#9 `[I.Boundaryless]`,`[SigmaCompactSpace]`,C¹; #8 benign `[NeZero d]`). No
`axiom`/`native_decide`/`admit`/`sorryAx`/`implemented_by` anywhere in `Frontier.Issue*`.

## 3. Measured priority queue (from the dependency-DAG spike — critical-path depth × parallel width)

Ranked by **measured** effort (DAG reports `docs/research/frontier/issue{4,6}/DAG-*.md`, Mathlib
node-availability grep-verified + adversarially audited). Parallel-Claude wall-clock ≈ critical-path
depth × per-node design+prove time (breadth is absorbed by running many warm agents at once).

| Priority | Target | depth × width | Parallel-Claude | Notes |
|---|---|---|---|---|
| **1** | **#9** | shallow | ~a session | one tangent-bundle lemma; most tractable; likely upstreamable |
| **2** | **#8** | shallow | days–~2 wks | ℂ-triangularization is the sub-wall (worthwhile Mathlib contribution) |
| **3** | **#11** | 3 × 1 | ~1–2.5 wks | **near-term** — Effros/Π¹₁ tower is OFF the critical path; Mathlib already has the separation engine `MeasurablySeparable.iUnion` / `measurablySeparable_range_of_disjoint`. Real work = the 4.6.2 generalized-first-separation induction + 4.7.1/4.7.2 structure lemmas |
| **4** | **#10** | 8 × 6 | ~4–6 months | genuinely large; 8 design-novel nodes in **series**. Parallelism absorbs off-path Layer-1 (SMB + countable-partition KS API) but **cannot** compress the Layer-2 foliation chain. Two deepest, no Mathlib precursors: absolute continuity of Wᵘ, disintegration of μ along Wᵘ. Don't brute-force — at most a sharper decomposition / land SMB as a standalone |

**Recommended next run:** take **#9, #8, #11 as one campaign** — independent file sets, parallelize
cleanly. #9 first (fastest full close of an issue). Closing #9 ⇒ migrate the whole `Frontier/Issue2`
chain into `Oseledets/` and confirm `#print axioms = [propext, Classical.choice, Quot.sound]`.

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
