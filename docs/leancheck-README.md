# leancheck — warm-REPL Lean feedback + cold-build gate for LLM workers

Cuts the ~80–168 s cold `lake env lean` import cost to ~ms per re-check by keeping a warm
`leanprover-community/repl` process loaded with `import Oseledets`, and delivers diagnostics to the
agent **automatically on each edit** (via a PostToolUse hook) — the agent just writes Lean and reads
compiler-style errors, never JSON. A Stop hook then enforces an authoritative cold `lake build`
before any worker may finish, so "done" always means "really verified."

Built on a validated warm-REPL evaluation (repl @ `f0a88bfca1fa` = our `v4.30.0-rc2`; warm re-check
~0.012 s; verdict matches cold).

## Pieces
- `.claude/leancheck/leancheck.py` — engine + CLI (stdlib only, no pip deps):
  - `leancheck <file.lean>` warm check (lazy-starts a REPL daemon over a Unix socket);
  - `leancheck --cold <file|module>` authoritative `lake build` (the QA gate);
  - `leancheck --warm` pre-warm; `--stop` kill daemon; `--selftest` offline logic tests.
  - Imports are stripped from the submission (already in the warm env) and `set_option`s are
    prepended for `mathlibStandardSet` parity; REPL line numbers are mapped back to the original
    file exactly via `kept_linenos` (no off-by-N).
- `.claude/hooks/post-edit-leancheck.py` — PostToolUse(Edit|Write|MultiEdit, `Oseledets/**/*.lean`):
  **NON-BLOCKING.** If the daemon is warm it runs the fast check and returns the report as
  `additionalContext`; if the daemon is cold it spawns a *detached* background warm-up and returns
  instantly with a short "warming" note (so the hook can never exceed its timeout and have its
  stdout discarded — the original failure mode). Records the touched module for the cold gate and
  appends a trace line per invocation to `/tmp/leancheck-hook.log`.
- `.claude/hooks/warm-leancheck.sh` — SessionStart hook: warms the shared daemon in the background
  at session start (idempotent, detached), so the first edit's PostToolUse check is already instant.
- `.claude/hooks/stop-coldbuild.py` — Stop/SubagentStop: cold-builds every touched module; on
  failure emits `{"decision":"block","reason":…}` to force the agent to continue; clean → allows
  stop. Loop-guard: blocks ≤ `MAX_TRIES` (6), then allows stop with an `UNVERIFIED` banner so a
  stuck state is reported, never hung. Also logs to `/tmp/leancheck-hook.log`.
- `.claude/leancheck/run-tests.sh` — runs the offline `--selftest` suites of all three scripts
  (engine line-mapping/formatting, hook target-detection/JSON envelope, cold-gate decision logic).
  No Lean, no daemon, no network needed.
- `.claude/agents/lean-worker.md` — frontmatter wires the hooks for subagents; the body tells the
  agent to rely on the **automatic** report and the authoritative cold gate (it does not call Lean
  itself — a manual `leancheck <file>` is only an optional fallback during the brief warming window).

## How the hooks are wired (and why it works for subagents)
- **Main session** (incl. `claude -p`): hooks live in `.claude/settings.json`
  (`SessionStart` warmer, `PostToolUse` leancheck, `PreToolUse` git block).
- **Subagents** (`lean-worker`): hooks live in the agent's **frontmatter** — `.claude/settings.json`
  hooks do *not* run inside subagent tool calls, so the PostToolUse + Stop hooks are duplicated there.
- The daemon is keyed by `LEANCHECK_KEY` (**default `oseledets`** — a stable per-repo key, not the
  session id) so the SessionStart warmer, the PostToolUse hook, and any manual `leancheck` call all
  share ONE warm REPL.

## Delivery: root cause + fix (measured 2026-06-16, verified via `claude -p --debug hooks`)
Early subagents received *no* passive report (and sometimes hallucinated "clean"). Root cause: the
hook's leancheck call on the **first** edit blocked on the ~1–3 min cold daemon import; the hook was
cut off before it could emit, so no `additionalContext` was delivered. Fix = the **non-blocking**
PostToolUse hook above + the **SessionStart** background warmer + the stable shared key. Verified
end-to-end in a fresh `claude -p` process: SessionStart warms the daemon, the PostToolUse hook
returns `additionalContext (45 chars)` in ~0.08 s, and the model reports receiving the warm report
("`✓ no errors`") with no action of its own. The cold-branch returns a "warming" note in ~57 ms.

## Known limitation — re-checking an already-imported file
The warm env is `import Oseledets`, i.e. the whole root. A warm check submits only the file *body*
against that env, so checking a file that is **already wired into the root** makes every declaration
report `already been declared` (false positives). The warm check is therefore accurate for **new**
files (the worker's normal case — its declarations aren't yet in the env) and for any not-yet-imported
file; for editing a file that is already part of `import Oseledets`, use the cold path
(`leancheck --cold <module>` / `lake build`). The cold `lake build` is the source of truth regardless.

## Env knobs
`LEANCHECK_ROOT` (repo root), `LEANCHECK_REPL` (repl binary), `LEANCHECK_KEY` (daemon socket key,
default `oseledets`), `LEANCHECK_IMPORT` (default `import Oseledets`; **never** bare `import Mathlib`
— that yields a broken env), `LEANCHECK_SETOPTS`, `LEANCHECK_HOOK_LOG` (default
`/tmp/leancheck-hook.log`).

## Tests
`bash .claude/leancheck/run-tests.sh` → all three `--selftest` suites (pure logic only; safe to run
anywhere). The end-to-end hook behavior (cold→warming, warm→diagnostics, non-target→silent) and the
`claude -p` delivery were validated manually as recorded above; the cold `lake build` + guarded
`AxiomAudit` remain the authoritative gate, so a warm/cold divergence only ever costs iteration time.

## Per-worker resource note
The shared daemon keeps one warm REPL (~1.5–2 GB resident). Fine on this box (31–64 GB). Because the
key is stable per-repo, parallel workers share the one daemon (requests are serialized over the
socket); when a new module is added the daemon's env goes stale for it, so the orchestrator rebuilds
the root and re-warms (`leancheck --stop && leancheck --warm`) between phases.
