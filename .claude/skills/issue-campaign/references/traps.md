# Trap catalog

Gotchas that have actually bitten campaigns in this repo. Skim before Phase 3 (implement) and
Phase 5 (integrate). Each entry: the symptom, the cause, the fix.

## Orchestration / worker behaviour

- **Workers idle-notify after kicking off a background build.** A `lean-worker` that runs
  `lake build` in the background often ends its turn with "I'll wait for the monitor to report"
  and stops — its background build is in *its* session, which you can't see. Symptom: a
  completion notification whose result is just "waiting…". **Fix:** take over — read the
  worker's file in its worktree, run the authoritative build yourself, and act on the result.
  (The #20 corollary, transport, and hoist workers all did this.)

- **Two `lake build`s in the same worktree.** If you take over a worker's build while the worker
  is also building in the same `.lake/build`, lake's workspace lock serializes them — no
  corruption, both finish — but avoid relying on it. Prefer one builder per worktree.

- **Workers branch off `main`, not your integration branch.** `lwt add` bases the new worktree on
  the *current HEAD of the main checkout*. Keep the main checkout on `main` during the campaign so
  workers branch cleanly; do integration in a separate `lwt add issue-<N>` worktree. If a later
  worker needs an earlier worker's not-yet-merged module, either merge it to `main` first or have
  the worker `cp` the dependency file into its own worktree (the proven pattern for corollaries).

- **Two parallel workers given the same `targetModule` write colliding files.** Independent
  worktrees, same relative path, different content (e.g. two workers both create
  `ProductRectangleEntropy.lean`). **Fix:** rename one on integration (and confirm no public-decl
  name clash). When dispatching, give each worker a distinct module path up front.

## Lean / Mathlib syntax & lint (warningAsError is on)

- **`set_option … in` / `omit … in` must come BEFORE the docstring**, not between the docstring
  and the `theorem`. Wrong order → `unexpected token 'set_option'/'omit'; expected 'lemma'`.
  Canonical: `omit […] in` / `set_option … in`, then `/-- doc -/`, then `theorem`.

- **The longLine linter counts CODEPOINTS, not bytes.** A line with Unicode math symbols
  (`≤ ⨆ σ ℤ`) can be well under 100 codepoints while `awk 'length>100'` (bytes) flags it — and
  vice-versa. Renaming an identifier longer (e.g. `injOn`→`injective`, +4) can push a doc line to
  101 codepoints. **Fix:** reflow; verify with the actual build, not byte-counting.

- **No `show` / defeq-coercion tactic; no deprecated `push_neg`.** The mathlibStandardSet linter
  rejects these. Use `change`/`unfold`/direct `exact`, and `simp only [not_exists, …]` instead.

- **`noncomputable def` of a class-typed value** (e.g. `MeasurableSpace α`) must be `@[reducible]`
  if you want `hsat := rfl` to see through it.

- **TypeClass-instance defeq errors** ("synthesized type class instance is not definitionally
  equal…") with `condEntropy`/`condExpKernel`/a sub-σ-algebra `𝒜`: declare `{𝒜 : MeasurableSpace α}`
  in the `variable` line BEFORE the ambient `[mα]`, so `mα` wins `[MeasurableSpace α]` resolution
  (the `Cond*.lean` idiom). Avoid `@`-spelling the kernel with explicit instance args.

- **Anonymous `local instance` auto-name collisions** across two modules that an aggregator both
  imports ("environment already contains …"). Give local instances explicit, unique names.

- **Measure-instance clashes** (e.g. two modules each setting a local `MeasureSpace`/`volume` on
  the same type) → ambiguous `volume`. Re-establish the needed local instances per module and
  don't import the conflicting sibling; inline literals where possible.

## Build / environment

- **Warm leancheck can be broken in worktrees.** This session: `leanclient` absent + the leancheck
  PostToolUse hook logs "skip edit outside project root" for `/home/vscode/...` worktree paths, so
  warm incremental feedback didn't work and workers cold-iterated. This is slow but correct — the
  cold `lake build` is the gate regardless, and `lwt` still gives the essential isolation. Tell
  workers up front so they don't wait on warm feedback that never comes.

- **Never let a worktree build without the Mathlib cache** — a plain `git worktree` (or
  `Workflow`'s `isolation:'worktree'`) recompiles Mathlib from source for hours. Always `lwt`.

- **`gh` works** in this environment (used for `issue view/comment/close/create`). The Mathlib
  cache is already present; never run `lake exe cache get` (DNS-blocked, hangs).

## Math / scoping

- **"Reduce the hard theorem to an existing one as a black box" is often a trap.** Verify the
  reduction actually holds (the #20 two-sided→one-sided generator reduction provably fails: a
  finite window forward-saturates only to a half-line). Prefer the route the standard reference
  actually uses.

- **A structural wall ≠ the objective is unreachable.** If the literal target needs missing
  machinery, deliver its downstream *purpose* directly and file the literal as a follow-up (see
  the Rescope principle in SKILL.md).

- **Audit your own deferral claims.** A lone probe can over-broadly declare "wall / library lacks
  X". Before deferring, send a scout to confirm with grep-verified negatives + a feasibility
  verdict (#16's "no smooth structure" deferral was wrong; the real wall was narrower).

- **Mathlib has no measure-theoretic entropy** (only topological). All KS-entropy machinery is the
  project's own `ErgodicTheory/Entropy/`. Don't expect `MeasureTheory.measureEntropy`.
