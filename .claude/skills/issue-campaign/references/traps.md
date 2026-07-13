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

- **Distrust the issue text; recon against the actual repo first.** Issues have named nonexistent
  objects (`catSqrtTwoSuspFlow`), asked for things the repo *itself proves impossible* (#59's
  `0 < cntDynamicalEntropy` contradicted the axiom-audited `cntDynamicalEntropy_eq_zero`;
  #58's "strict drop at each step" is impossible when stage 1 is a conjugacy), and worried about
  problems that don't exist here (#58's "a.e./boundary null sets" — the repo's AW tiling is exact,
  so equivariance/injectivity hold *everywhere*). Also the reverse: a "notoriously hard" premise
  may conflate two questions — #60's hidden-Markov "hardness" concerned closed *forms* of a rate,
  while the *inequality* was an easy per-n DPI. Pin the truth value at recon, before implementers.

- **Literature "explicit formulas" can be quasi-metrics only.** Papers claiming a formula is
  "bi-Lipschitz equivalent to" a metric are NOT claiming it *is* a metric — #63's finite-route
  Bowen–Walters formulas provably violate the triangle inequality (two machine-checked
  counterexamples: interpolation does not repair it, and no finite endpoint-local route family
  can, since optimal chains route through middle base points). When formalizing a "standard"
  explicit metric, verify the axioms numerically on adversarial examples first; an embedding
  realization (Kuratowski-style test functions, triangle free from norms) can be far cheaper than
  the classical chain-infimum.

- **For no-recovery / seal witnesses, check `Λρ ≠ Λσ`.** If both states map to the same image, the
  "no common recovery" conclusion is trivially set-theoretic (one function can't send one input to
  two outputs) and carries zero information-theoretic content — a QA lens caught exactly this on
  #59's first seal formulation. Same genus: a certificate about a *single* map can be impossible
  for structural reasons (every unital *-endo of M_d is inner ⇒ always preserves a MASA) — the
  honest statement may need to be about a *pair* of objects.

## Worker & model management

- **Fable subagents die on the 64k output-token limit** — twice on #63's keystone, even with
  explicit output-discipline instructions (the blowup is in the model's own response, mid-task).
  For hard keystones prefer **Opus with a fully-worked proof plan** (case lists, route choices,
  fallbacks) over Fable with freedom; when the orchestrator works out the delicate cases itself
  and writes them into the brief, Opus lands them.

- **Race keystone workers with *different architectures*, and pipe refutations between them.** A
  racer that fails by *disproving the shared plan* (V1b refuting the min-of-three metric) is as
  valuable as one that succeeds — SendMessage the finding to the surviving racer mid-flight.

- **Record agent IDs at launch** (a table of worker→ID). SendMessage to the wrong sibling happens
  easily when IDs are recalled from launch order; the recipient will (correctly) ignore it, but
  the intended recipient never sees it.

- **SendMessage can resume a *finished* agent from its transcript** — the cheapest way to demand a
  final report, push a build error back, or redirect after new intel. Conversely, `TaskStop`
  agents that keep re-waiting/re-editing after their final report (one "corrected a regression"
  post-report; ground truth = your own gate build, then stop them).

- **Workflow QA: read `journal.jsonl` when the verifier output looks degenerate.** One verifier
  returned `{"summary": "test", confirmed: []}` while all five lenses had real findings — the lens
  results were intact in the journal; adjudicate them yourself rather than re-running. Also brief
  verifiers that they may *empirically test* dubious lens claims (one disproved a "duplicate
  declaration breaks the build" blocker by compiling the scenario: identical-type theorem
  duplicates dedup at import; different types error).

## CI / landing (protected main)

- **Protected-main landing flow**: push branch → `gh pr create` (body `Resolves #N` auto-closes on
  merge) → wait for CI → `gh api -X DELETE .../branches/main/protection/required_pull_request_reviews`
  → `gh pr merge --merge` → `gh api -X PATCH .../required_pull_request_reviews
  -F required_approving_review_count=1` → `git pull --ff-only` (merge commits keep local main an
  ancestor; `git reset` is deny-listed).

- **Poll `gh pr checks` until checks REGISTER before `--watch`.** A watcher launched immediately
  after `pr create` exits with "no checks reported" and you can merge un-gated by accident. Idiom:
  `until gh pr checks <br> | grep -q pending; do sleep 15; done; gh pr checks <br> --watch`.

- **Blueprint CI ("Build project") fails independently of the Lean build.** Two recurring causes:
  (a) using a LaTeX environment never declared in `blueprint/src/macros/common.tex` (check the
  `\newtheorem` inventory before writing `\begin{remark}` etc.); (b) `checkdecls` requires FULLY
  QUALIFIED names in `\lean{}` — the wiring worker's axiom-audit report is the authoritative
  source for exact namespaces; docs workers guessing prefixes fail CI one round later.

## Toolchain pins (v4.30.0-rc2 era — verify before trusting)

- `abs_add` is GONE → `abs_add_le`; `div_le_iff₀` is current.
- `Nat.Prime 5` needs `decide` (norm_num extension not always in scope); `Irrational` lives in
  `Mathlib.NumberTheory.Real.Irrational`; `Real.summable_abs_int_rpow` needs the `Real.` prefix.
- `Matrix.IsDiag` needs an explicit `import Mathlib.LinearAlgebra.Matrix.IsDiag`.
- `ℕ → Bool` has NO bundled `MetricSpace` instance (only `MetrizableSpace`), so
  `MetricSpace C(ℕ→Bool, ·)` won't synthesize — use `unitInterval` as a compact-metric carrier.
- `PolishSpace C(X,Y)` synthesizes only with `ContinuousMap.Compact` +
  `UniformSpace.CompactConvergence` + `ContinuousMap.SecondCountableSpace` imported *together* —
  a missing one looks like a fundamental gap (it isn't).
- `σ` (U+03C3) becomes a RESERVED TOKEN under some imports — don't use it as a term binder.
- Instance-loop hazard: `[CompactSpace][MetrizableSpace] ⇒ IsCompletelyMetrizableSpace` must be a
  *theorem* used via `haveI`, not a global instance (loops with the prio-90
  `IsCompletelyMetrizableSpace.MetrizableSpace`).
