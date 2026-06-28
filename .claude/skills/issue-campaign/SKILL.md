---
name: issue-campaign
description: >-
  Orchestrate a multi-agent campaign to fully resolve a GitHub issue in this Lean 4 +
  Mathlib repo — parallel recon + firecrawl research (naming sources), de-risking scouts,
  warm-worktree (lwt) Lean workers in parallel, multi-lens adversarial QA with auto-fix,
  then integrate → cold-build gate → axiom audit → commit/push → close → file follow-ups →
  update memory. Use this WHENEVER the user wants to attack, grind, solve, formalize, or fully resolve (by
  proving) a GitHub issue — e.g. "full attack on issue #N", "solve #N", "resolve #N", "grind
  the open issues", "prove the theorem in issue #N" — even if they never say "campaign". It is
  for RESOLVING an issue by proving its content, NOT for merely viewing/explaining one, an
  administrative close (duplicate/wontfix/stale), or a one-off build-error fix. Acting as
  CEO/orchestrator you DELEGATE all proof work to subagents and never write Lean yourself.
  Especially apt for formalization issues that need a new theorem proved sorry-free.
---

# Issue Campaign — the proven method

You are the **CEO / orchestrator**. You decompose, delegate, integrate, and gate — you do
**not** write Lean proofs yourself. This wins because (a) many workers grind in parallel on
isolated warm worktrees, and (b) your own context stays clean (you keep conclusions, not
file dumps). This method has closed issues #8, #9, #16, #19, and #20 in this repo.

Read `CLAUDE.md` first — its orchestration rules and build invariants are law here. Then run
the loop below. Track phases with the task tools so progress survives context summarization.

## The loop

1. **Recon** — understand the issue and the terrain before dispatching anyone.
2. **De-risk** — send scouts to pin down the cheapest route and confirm the hard pieces are
   reachable (not walls) *before* committing implementers.
3. **Implement** — decompose into independent pieces; grind them in parallel on warm worktrees.
4. **QA** — multi-lens adversarial review with auto-fix, beyond the axiom audit.
5. **Integrate & close** — wire, gate, commit, push, close, file follow-ups, update memory.

Each phase feeds the next; read every result before deciding the next move. Don't skip
de-risking — a 20-minute scout routinely saves an hour of an implementer hitting a wall.

## Non-negotiable invariants

These come from `CLAUDE.md` and hard-won experience. Honor them or the campaign corrupts.

- **Warm `lwt` worktree, one per Lean worker, always.** Each worker runs
  `WT=$(.claude/scripts/lwt add <branch> | tail -1)` (never `--no-warm`) and works only under
  `$WT`. Isolated `.lake/build` + the Mathlib-cache symlink is what lets workers build in
  parallel without racing each other or triggering a multi-hour Mathlib rebuild. A *plain*
  git worktree (e.g. `Workflow`'s `isolation:'worktree'`) lacks the cache and is forbidden for
  Lean builds — workers must use `lwt`.
- **Workers never run `git`.** A worker reset once wiped siblings' edits. The orchestrator
  does *all* git: merges, commits, pushes, and the authoritative builds.
- **Warm leancheck is the mandated iteration loop (CLAUDE.md inv #1); the cold `lake build
  <Module>` (or full `lake build`) is the authoritative gate.** Verify warm works at session
  start; only if it's *confirmed broken this session* (it has been — see traps) do workers fall
  back to cold-iterating, which is slow but correct since the cold build gates either way.
- **Never `sorry`, never axiomatize.** `warningAsError` makes any `sorry`/lint a build failure.
  Partial work stays out of the imported build until it compiles honestly.
- **Every headline result gets a `#guard_msgs in #print axioms` audit** in `test/AxiomAudit.lean`
  equal to `[propext, Classical.choice, Quot.sound]`. The build fails if this ever changes.
- **Name your sources.** Use `firecrawl` to find the standard proof; cite the textbook +
  theorem number in doc comments and the closing comment (the formalization mirrors known math).

## Phase 1 — Recon

Fan out *read-only* recon in parallel (use `Explore` for codebase mapping, `mathematician` for
math + `firecrawl` research). You keep the conclusions, not the file contents. Cover:

- The exact issue text and its checklist (`gh issue view <N> --json ...`).
- The existing one-sided / analogous results to mirror (signatures, proof skeletons, the API).
- The predicates/objects the issue names, and what already exists vs is missing.
- The downstream consumer (what the issue *unlocks*) and its precise open obligations.
- The standard math proof (firecrawl the textbook; identify the cheapest route and the *traps*
  — e.g. "reduce X to Y as a black box" framings that provably fail).

Synthesize into a precise work breakdown: what's independent, what's the keystone, what's
uncertain. Write the design into a task description so it survives summarization.

## Phase 2 — De-risk (scouts before implementers)

For every uncertain or "hard" piece, send a `mathematician` scout to:
- determine whether the needed machinery **already exists** (exact lemma name + `file:line`,
  verified with `lake env lean #check` in a throwaway lwt worktree), and
- give a **verdict** (SMALL / MEDIUM / LARGE / WALL) with a concrete, name-precise Lean skeleton,
  or — if it's a wall — the precise missing keystone.

This is where you catch the difference between "needs a 50-line lemma" and "needs a multi-week
theory" — and where you *confirm* genuine walls. (E.g. #20's keystone needed a martingale piece
that turned out to already exist, `condEntropy_tendsto_iSup`; while #20's *literal* fibre target
`condKsEntropy=0` was confirmed blocked — which is exactly what justified rescoping to the
downstream `ksEntropy(suspension)=Hnu`. See the Rescope principle.)

## Phase 3 — Implement (parallel warm-worktree workers)

Decompose the work into **independent** pieces (each buildable on its own). Dispatch a
`lean-worker` per piece, each provisioning its own warm `lwt` worktree. Give each worker: the
exact target signature, the verified skeleton, the existing lemmas to use, and the invariants
above. Tell it to report the final signature, branch, files, cold-build tail, and a `sorry/axiom`
grep — and to **not** run git.

- **Scale aggressively; burn tokens, don't waste them.** Compute and tokens are plentiful here —
  the bottleneck is *correctness and coverage*, not cost. Default to a wide attack: fan out up to
  **~16 warm workers**, in **waves of ~6–8 concurrent** to stay under the RAM line (~0.5 GB/serve
  daemon + 2–4 GB per coincident elaboration — RAM, not CPU, is the limit). Spend freely on what
  *improves the answer*: parallel coverage of independent pieces, **2–3× redundancy on a
  single-point-of-failure keystone** (first green wins), de-risking scouts, and adversarial QA —
  this is exactly the force that cracked #20's fibre wall. The only thing to avoid is *wasted*
  spend, which adds latency + RAM pressure without improving the result: fanning out inherently
  serial work, redundant workers on an already-done piece, polling harness-tracked background
  tasks, or re-deriving facts you already established. Decide by the problem — scale where
  parallelism genuinely helps, and lean wide whenever the user signals max thoroughness (ultracode
  on, a `/goal` autonomous loop, or an explicit "burn tokens / scale up").
- **Use a `Workflow` for research→fan-out→assembly** (the proven shape: research-decompose →
  `parallel()` sub-lemma workers → orchestrator assembles). See
  `references/workflow-templates.md` for a copy-adaptable script. Note: inside a workflow each
  agent must still provision its own `lwt` worktree (don't rely on `isolation:'worktree'`).
- **Redundancy is cheap insurance** for a single-point-of-failure keystone: race 2–3 workers,
  first green wins. Skip it once a piece is essentially done.

## Phase 4 — Multi-lens adversarial QA (with auto-fix)

The axiom audit is necessary but not sufficient. Run a `Workflow` that reviews the new modules
through **five independent lenses** in parallel — (1) mathematical faithfulness / no statement
weakening, (2) vacuity & hypothesis honesty (is the result non-vacuous? any hypothesis secretly
trivializing it?), (3) soundness beyond axioms (`sorry`/`cast`/defeq abuse; guard coverage),
(4) reuse / simplification, (5) style / naming / docs — then a **single adversarial
synthesis-verifier** that reads the actual code and confirms or rejects each finding
(default-skeptical, dedup). Auto-apply the confirmed real findings, re-build, and commit. See
`references/workflow-templates.md` for the QA workflow script. The why: this catches the failure
modes the build can't — a faithfully-typechecking proof of a *weaker* statement, a vacuously-true
theorem, a duplicate definition. (#16's wrong item-5 deferral was caught by a multi-agent audit.
But the biggest #19/#20 catches — a provably-false reduction route, a falsely-assumed time-1-map
ergodicity, the two-sided→one-sided black-box trap — surfaced earlier at recon/de-risk; treat
Phase 4 as the backstop, and do adversarial checking at recon/de-risk too, not only here.)

## Phase 5 — Integrate & close

You (orchestrator) do all of this:

1. **Integration worktree.** `lwt add issue-<N>` off `main`; keep the *main* checkout on `main`
   so worker `lwt`-adds branch cleanly. Copy each green module from its worker worktree into the
   integration tree (file-copy staging; rename on collision — see traps).
2. **Wire aggregators by hand.** Add imports to `Oseledets.lean` and any sub-aggregator
   (`Oseledets/Multifractal.lean`, …); add the `#print axioms` guards + imports to
   `test/AxiomAudit.lean`. Verify each new headline's axiom set first with `lake env lean`.
3. **Definitive gate.** Run the full `lake build` (lib + `AxiomAudit`) in the integration tree
   *and* a final one in the `main` checkout after merging. Both must be green.
4. **Commit / merge / push.** Commit on `issue-<N>`, `git merge --ff-only` into `main`, push.
   End commit messages with the `Co-Authored-By` + `Claude-Session` trailers from your harness
   instructions, and `feat(#N …)` / `refactor(#N …)` subjects.
5. **Close.** Post a comprehensive `gh issue comment` (deliverables + theorem names + files +
   route + sources + honest rescopes), then `gh issue close <N> --reason completed`.
6. **Follow-ups & memory.** File precise follow-up issues for any documented wall; tear down
   campaign worktrees (`lwt remove <branch> --delete-branch`, never the shared cache or
   unrelated trees); write a `<issue>-campaign.md` memory + a `MEMORY.md` pointer capturing the
   non-obvious route, traps, and rescopes.

## Rescope principle (important)

When the issue's *literal* target is blocked by a structural wall, ask what the literal target
was *for* and deliver that **downstream objective** directly — it is often cleaner and is the
honest win. (#20 wanted `condKsEntropy(fibre)=0` only to conclude `ksEntropy(suspension)=Hnu`;
the literal was blocked, so we proved the absolute `ksEntropy(suspension)=Hnu` directly and
filed the literal as a follow-up.) Document the rescope transparently; never quietly weaken.

## Running autonomously under `/goal`

This skill is the *method*; `/goal` is the *forcing loop* that drives it. Set a goal whose
condition names this skill plus an objective, **verifiable** finish line — the session Stop hook
then blocks stopping until it's met and re-injects the directive each turn (auto-clearing on
success):

- Single issue: `/goal Use the issue-campaign skill to fully resolve issue #N — keep going until
  it's proved sorry-free, axiom-clean, the full lake build is green, pushed to main, and the issue
  is CLOSED.`
- All open issues: `/goal Grind the open issues one at a time with the issue-campaign skill until
  each is closed (proved, axiom-clean, pushed); file follow-ups for any wall.`

For a multi-issue goal, pick an ordering and run this loop once per issue, reusing the same infra.
Anchor the finish line to something objectively checkable (issue CLOSED + main build green) so the
hook can actually release — a vague condition loops forever (end early with `/goal clear`). It runs
hot (many subagents, workflows, and cold builds); that's intended for autonomous grinding.

## Traps & reusable templates

- `references/traps.md` — the catalog of gotchas that have actually bitten campaigns (worker
  idle-on-background-build, `set_option`/`omit` placement, codepoint line-length, same-target
  file collisions, broken warm leancheck, measure-instance clashes, …). Skim it before Phase 3.
- `references/workflow-templates.md` — copy-adaptable `Workflow` scripts for the research→fan-out
  pattern and the multi-lens QA pattern.
