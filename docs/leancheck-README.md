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
- **Re-checks see your latest edit.** Each re-check first re-syncs the file's *current on-disk content*
  into the server (a `didChange`) before reading diagnostics. Without this the language server would
  keep returning the diagnostics from the file's *first* open — i.e. stale results that ignore later
  edits. (The first iteration after a fresh open is the "warming" note; the re-sync applies to every
  subsequent check.)
- **Non-blocking:** a check on a not-yet-warm file returns a "warming" note immediately and elaborates
  it on a background thread; the real diagnostics arrive automatically on the next edit. So the hook
  never blocks the agent and never hits a hook timeout.
- **Concurrency:** the daemon handles each connection on its own thread and holds *no* global server
  lock — leanclient is internally thread-safe (its diagnostics wait releases the per-file lock on a
  condition variable while a dedicated reader thread updates state). So a slow warm/recheck of one
  file never stalls the accept loop or a concurrent check of another file. The warm uses a generous
  background timeout (`LEANCHECK_WARM_MAX`, 240s); a re-check is bounded (`LEANCHECK_RECHECK_MAX`,
  55s) to stay under the post-edit hook's 80s budget — a longer wait returns a "may be incomplete;
  cold build is authoritative" note rather than a hook timeout.
- **Robust lifecycle:** the daemon is a per-root **singleton** (an `flock` on `<sock>.lock`), so two
  racing callers can never spawn — and orphan — a second multi-GB `lake serve`. Liveness is probed by
  an actual socket *connection*, not by the socket file's mere existence, so a stale socket left by a
  crashed/SIGKILLed daemon is detected, swept, and the daemon respawned (instead of silently
  disabling warm feedback). A pidfile (`<sock>.pid`) lets a fresh daemon reap a predecessor's orphaned
  `lake serve` after an ungraceful death.

## Pieces
- `.claude/leancheck/leancheck.py` — engine + CLI:
  - `leancheck <file.lean>` warm diagnostics (non-blocking; talks to the daemon over a Unix socket);
  - `leancheck --cold <file|module>` authoritative `lake build` (the QA gate);
  - `leancheck --warm [file]` start the daemon (with a file, also start warming it); `--stop` clean
    shutdown — signals the daemon over its socket so leanclient kills `lake serve` + its
    `lean --server` child (falls back to the pidfile if the socket is already gone; a no-op if neither
    exists); `--selftest` offline tests.
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
- The daemon socket is keyed **per project root** (a hash of the realpath'd `CLAUDE_PROJECT_DIR`), so
  each worktree/checkout gets its OWN `lake serve` bound to its own root, while all callers within one
  tree share that server. **Worktree-safe.**

## Cross-file behavior (honest)
`lake serve` resolves `import`s from compiled `.olean` — **not** from other files' live buffers. This
was verified directly against the server: editing a dependency's source (even open and live-edited)
does **not** make a dependent see it; the dependency must be rebuilt (`lake build`) to regenerate its
olean. So a `leancheck` reflects the file's own current source but sees its dependencies as last built.
This is a Lean fundamental (imports are compiled artifacts), true of the LSP, the REPL, and `lake`
alike — there is no Python-style source-level hot reload of imports in Lean. The cold `lake build` +
guarded `AxiomAudit` are the source of truth and catch any cross-file staleness.

## Mathlib-rebuild guard
If Mathlib's oleans are absent — a fresh checkout, or (more insidiously) a worktree created without
the prebuilt `.lake` cache or its symlink — any `lake build`/`lake serve` recompiles Mathlib from
source (HOURS). Every leancheck entry point (`<file>`, `--warm`, `--cold`, daemon start) first checks
for Mathlib's oleans and, if missing, **aborts with a loud warning** instead of silently starting the
rebuild; `leancheck --check-mathlib` reports the status explicitly. Opt into the rebuild only by
choice: `LEANCHECK_ALLOW_MATHLIB_REBUILD=1`. (A *direct* `lake build` is not guarded — run
`leancheck --check-mathlib` first if unsure whether the cache is in place.)

## Dependency
`leanclient` (pip): installed by `.devcontainer/post-create.sh`
(`pip install --user --break-system-packages leanclient`). The project must be **built** (oleans
present — true in this devcontainer) since imports resolve from oleans; the daemon constructs the
client with `prevent_cache_get=True` (the cache fetch is DNS-blocked here and would otherwise stall).

## Env knobs
`LEANCHECK_ROOT` [cwd], `LEANCHECK_KEY` [derived per project root], `LEANCHECK_SOCKDIR` [/tmp]
(directory for the daemon's `<key>.sock`, `.sock.lock`, `.sock.pid`), `LEANCHECK_MAXFILES` [8] (max
files held open in the server before idle ones are closed), `LEANCHECK_WARM_MAX` [240] (background
first-open ceiling, seconds), `LEANCHECK_RECHECK_MAX` [55] (re-check diagnostics-wait ceiling, kept
under the hook budget), `LEANCHECK_HOOK_LOG` [/tmp/leancheck-hook.log],
`LEANCHECK_ALLOW_MATHLIB_REBUILD` [unset] (set to `1` to opt past the Mathlib-rebuild guard and
accept a from-scratch compile).

## Tests
`bash .claude/leancheck/run-tests.sh` runs all three `--selftest` suites — pure formatting / decision
logic only (no Lean, no daemon, no network).

End-to-end behavior is validated by a separate live driver (not part of the offline suite, since it
needs a real `lake serve`). Last run (2026-06-16, against the real server) all green: non-blocking
warming (`warming` note in <12s); warmed clean file → `✓ no errors`; **edit the file to
`(1:Nat)=2 := rfl` and the re-check reports `error: Type mismatch` at the right `line:col`** (the
staleness regression test); edit it back → `✓ no errors`; SIGKILL the daemon → next check sweeps the
stale socket and respawns; two racing `--daemon` spawns collapse to one survivor (flock); `--stop`
removes the socket + pidfile; zero leaked `lake serve` processes. The cold `lake build` + guarded
`AxiomAudit` remain the authoritative gate, so any warm/cold divergence only costs iteration time.
