# leancheck — warm-REPL Lean feedback + cold-build gate for LLM workers

Cuts the ~80–168 s cold `lake env lean` import cost to ~ms per re-check by keeping a warm
`leanprover-community/repl` process and caching one Lean environment **per file's import-set**, and
delivers diagnostics to the agent **automatically on each edit** (via a PostToolUse hook) — the agent
just writes Lean and reads compiler-style errors, never JSON. A Stop hook then enforces an
authoritative cold `lake build` before any worker may finish, so "done" always means "really verified."

Built on a validated warm-REPL evaluation (repl @ `f0a88bfca1fa` = our `v4.30.0-rc2`; warm re-check
~0.012 s; verdict matches cold).

## Per-file environments — why editing *existing* files works
A file `F` is checked against an environment built from **`F`'s own `import` lines** (which never
include `F` itself), not from a single monolithic `import Oseledets`. So a file already wired into the
build does **not** collide with itself (`… has already been declared`). Envs are cached per
import-set, so:
- **First** check of `F` (or any file with the same imports): builds that env (~30–60 s — it loads
  `F`'s import closure, same one-time cost as a cold `lake env lean`).
- **Every subsequent** re-check of `F` (the edit loop): ~0.3 s, and **accurate** — clean files report
  `✓ no errors`; real errors are reported with correct `line:col`.

This is what makes the accelerator useful for the common case (iterating on an existing module), not
just for brand-new files. Memory is bounded: once more than `LEANCHECK_MAXENVS` (default 4) distinct
import-sets have been seen, the REPL is restarted (cached envs rebuild lazily on demand).

## Pieces
- `.claude/leancheck/leancheck.py` — engine + CLI (stdlib only, no pip deps):
  - `leancheck <file.lean>` warm check against the file's own-imports env (built/cached per set);
  - `leancheck --cold <file|module>` authoritative `lake build` (the QA gate);
  - `leancheck --warm [file]` start the daemon (with a file, also pre-build that file's env);
    `--stop` kill daemon; `--selftest` offline logic tests.
  - Imports are pulled out to build the env; `set_option`s are prepended to the body for
    `mathlibStandardSet` parity; REPL line numbers map back to the original file via `kept_linenos`
    (no off-by-N); non-error prelude messages are dropped.
- `.claude/hooks/post-edit-leancheck.py` — PostToolUse(Edit|Write|MultiEdit, `Oseledets/**/*.lean`):
  **NON-BLOCKING.** If the daemon is up it runs the check and returns the report as
  `additionalContext`; if the daemon is down it spawns a *detached* background start and returns
  instantly with a "warming" note (so the hook can never exceed its timeout and have its stdout
  discarded — the original failure mode). Records the touched module and appends a trace line per
  invocation to `/tmp/leancheck-hook.log`.
- `.claude/hooks/warm-leancheck.sh` — SessionStart hook: starts the shared daemon in the background
  at session start (idempotent, detached).
- `.claude/hooks/stop-coldbuild.py` — Stop/SubagentStop: cold-builds every touched module; on failure
  emits `{"decision":"block","reason":…}` to force the agent to continue; clean → allows stop.
  Loop-guard: blocks ≤ `MAX_TRIES` (6), then allows stop with an `UNVERIFIED` banner. Logs too.
- `.claude/leancheck/run-tests.sh` — runs the offline `--selftest` suites of all three scripts
  (engine import-split / line-map / formatting, hook target-detection / JSON envelope, cold-gate
  decision logic). No Lean, no daemon, no network.
- `.claude/agents/lean-worker.md` — frontmatter wires the hooks for subagents; the body tells the
  agent to rely on the **automatic** report and the authoritative cold gate (a manual
  `leancheck <file>` is only an optional fallback during the brief first-build window).

## How the hooks are wired (and why it works for subagents)
- **Main session** (incl. `claude -p`): hooks in `.claude/settings.json` (`SessionStart` warmer,
  `PostToolUse` leancheck, `PreToolUse` git block).
- **Subagents** (`lean-worker`): hooks in the agent's **frontmatter** — `.claude/settings.json` hooks
  do *not* run inside subagent tool calls, so the PostToolUse + Stop hooks are duplicated there.
- The daemon is keyed by `LEANCHECK_KEY` (**default `oseledets`**, a stable per-repo key) so the
  SessionStart warmer, the PostToolUse hook, and any manual `leancheck` call share ONE daemon.

## Delivery: root cause + fix (measured 2026-06-16, verified via `claude -p --debug hooks`)
Early subagents received *no* passive report (and sometimes hallucinated "clean"). Root cause: the
hook's leancheck call on the **first** edit blocked on the cold daemon start/import and was cut off
before it could emit. Fix = the **non-blocking** PostToolUse hook + the **SessionStart** background
start + the stable shared key. Verified end-to-end in a fresh `claude -p` process: the PostToolUse hook
returned `additionalContext (45 chars)` and the model reported receiving the warm report with no action
of its own. Separately, the **per-file environment** rework (above) makes warm checks of already-wired
files accurate (previously they reported every declaration as "already declared").

## Env knobs
`LEANCHECK_ROOT` (repo root), `LEANCHECK_REPL` (repl binary), `LEANCHECK_KEY` (daemon socket key,
default `oseledets`), `LEANCHECK_SETOPTS`, `LEANCHECK_MAXENVS` (max cached per-import-set envs before
the REPL is restarted, default 4), `LEANCHECK_HOOK_LOG` (default `/tmp/leancheck-hook.log`).

## Tests
`bash .claude/leancheck/run-tests.sh` → all three `--selftest` suites (pure logic only; safe to run
anywhere). End-to-end behavior validated manually: hook cold→"warming"/warm→diagnostics; per-file env
makes existing wired files check correctly (`Flow.lean`, `Corollaries.lean` → `✓ no errors`; a
deliberate break → error at the right `line:col` in ~0.3 s); fresh `claude -p` delivery confirmed. The
cold `lake build` + guarded `AxiomAudit` remain the authoritative gate, so a warm/cold divergence only
ever costs iteration time.

## Resource note
Each cached env keeps that file's import closure resident (~1.5–2 GB). With the default
`LEANCHECK_MAXENVS = 4` the daemon holds at most ~4 such envs before restarting (re-warming lazily);
the common single-file edit loop keeps exactly one. The key is stable per-repo, so parallel workers
share the daemon (requests serialize over the socket).
