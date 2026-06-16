# leancheck — warm Lean feedback (via `lake serve`) + cold-build gate for LLM workers

Gives agents automatic per-edit Lean diagnostics by driving the **real Lean language server**
(`lake serve`) — the same engine every Lean editor uses — and enforces an authoritative cold
`lake build` before any worker may finish. The agent just writes Lean and reads compiler-style
errors as `additionalContext`; it never sees JSON or the LSP protocol.

The engine is the maintained **`leanclient`** library (what `lean-lsp-mcp` is built on). It owns the
hard parts — import resolution, incremental within-file elaboration, the diagnostics-finalization
handshake (`waitForDiagnostics` + `$/lean/fileProgress` + the 4.22 grace window), stale-import
auto-rebuild, and `lean --server` process lifecycle. So `leancheck.py` is thin plumbing (a Unix
socket + a non-blocking warm queue), **not** a re-implementation of a checker. This replaced an
earlier bespoke warm-REPL that was a parade of edge cases (cold-start cutoff, stale single env,
"already declared" on wired files, per-import-set env juggling).

## Behavior
- **One persistent `lake serve`.** It loads the project's `.olean` closure once and elaborates open
  files against it.
- **First open of a file** elaborates it — tens of seconds to a few minutes for a Mathlib-heavy file
  (inherent: loading the import closure; same one-time cost as a cold `lake env lean`).
- **Warm re-checks are ~instant** (incremental within-file elaboration), and **accurate for existing
  wired files** (the LSP elaborates the file from source against its imports — no self-collision).
- **Non-blocking:** a check on a not-yet-warm file returns a "warming" note immediately and elaborates
  it on a background thread; the real diagnostics arrive automatically on the next edit. So the hook
  never blocks the agent and never hits a hook timeout.

## Pieces
- `.claude/leancheck/leancheck.py` — engine + CLI:
  - `leancheck <file.lean>` warm diagnostics (non-blocking; talks to the daemon over a Unix socket);
  - `leancheck --cold <file|module>` authoritative `lake build` (the QA gate);
  - `leancheck --warm [file]` start the daemon (with a file, also start warming it); `--stop` clean
    shutdown (kills `lake serve` + its `lean --server` child via leanclient); `--selftest` offline tests.
- `.claude/hooks/post-edit-leancheck.py` — PostToolUse(Edit|Write|MultiEdit, `Oseledets/**/*.lean`):
  calls leancheck and returns the report as `additionalContext`; if the daemon isn't up yet it spawns
  a detached background start and returns a "warming" note. Logs to `/tmp/leancheck-hook.log`.
- `.claude/hooks/warm-leancheck.sh` — SessionStart hook: starts the daemon in the background.
- `.claude/hooks/stop-coldbuild.py` — Stop/SubagentStop: cold-builds every touched module and blocks
  the stop on failure (loop-guarded). The authoritative gate.
- `.claude/leancheck/run-tests.sh` — offline `--selftest` suites of all three scripts (no Lean,
  no server, no network).
- `.claude/agents/lean-worker.md` — frontmatter wires the hooks for subagents; the body tells the
  agent to rely on the automatic report and the cold gate.

## Wiring (and why it works for subagents)
- **Main session** (incl. `claude -p`): hooks in `.claude/settings.json` (`SessionStart`, `PostToolUse`,
  `PreToolUse` git block).
- **Subagents** (`lean-worker`): hooks in the agent **frontmatter** — settings.json hooks do not run
  inside subagent tool calls.
- The daemon socket is keyed by `LEANCHECK_KEY` (default `oseledets`) so all callers share one server.

## Cross-file behavior (honest)
`lake serve` resolves `import`s from compiled `.olean` — **not** from other files' live buffers. This
was verified directly against the server: editing a dependency's source (even open and live-edited)
does **not** make a dependent see it; the dependency must be rebuilt (`lake build`) to regenerate its
olean. So a `leancheck` reflects the file's own current source but sees its dependencies as last built.
This is a Lean fundamental (imports are compiled artifacts), true of the LSP, the REPL, and `lake`
alike — there is no Python-style source-level hot reload of imports in Lean. The cold `lake build` +
guarded `AxiomAudit` are the source of truth and catch any cross-file staleness.

## Dependency
`leanclient` (pip): installed by `.devcontainer/post-create.sh`
(`pip install --user --break-system-packages leanclient`). The project must be **built** (oleans
present — true in this devcontainer) since imports resolve from oleans; the daemon constructs the
client with `prevent_cache_get=True` (the cache fetch is DNS-blocked here and would otherwise stall).

## Env knobs
`LEANCHECK_ROOT` [cwd], `LEANCHECK_KEY` [oseledets], `LEANCHECK_MAXFILES` [8] (max files held open in
the server before idle ones are closed), `LEANCHECK_HOOK_LOG` [/tmp/leancheck-hook.log].

## Tests
`bash .claude/leancheck/run-tests.sh` → all three `--selftest` suites (pure formatting / decision
logic). End-to-end validated against the real server: clean existing file → `✓ no errors`; a
deliberate `(1:Nat)=2 := rfl` → error at the correct `line:col`; warm re-check ~instant; clean
shutdown. The cold `lake build` + guarded `AxiomAudit` remain the authoritative gate, so any
warm/cold divergence only costs iteration time.
