# leancheck — warm-REPL Lean feedback + cold-build gate for LLM workers

Cuts the ~80–168 s cold `lake env lean` import cost to ~ms per re-check by keeping a warm
`leanprover-community/repl` process loaded with `import Oseledets`, and delivers diagnostics to
the agent **automatically on each edit** — the agent just writes Lean and reads compiler-style
errors, never JSON. A Stop hook then enforces an authoritative cold `lake build` before any
worker may finish, so "done" always means "really verified."

Built on the validated finding in `docs/plan/lean-server-evaluation.md`
(repl @ `f0a88bfca1fa` = our `v4.30.0-rc2`; warm re-check ~0.012 s; verdict matches cold).

## Pieces
- `.claude/leancheck/leancheck.py` — engine + CLI (stdlib only, no pip deps):
  - `leancheck <file.lean>` warm check (lazy-starts a per-key REPL daemon over a Unix socket);
  - `leancheck --cold <file|module>` authoritative `lake build` (the QA gate);
  - `leancheck --warm` pre-warm; `--stop` kill daemon; `--selftest` offline logic tests.
  - Imports are stripped from the submission (already in the warm env) and `set_option`s are
    prepended for `mathlibStandardSet` parity; REPL line numbers are mapped back to the original
    file exactly via `kept_linenos` (no off-by-N).
- `.claude/hooks/post-edit-leancheck.py` — PostToolUse(Edit|Write|MultiEdit, `Oseledets/**/*.lean`):
  runs the warm check, returns the report as `additionalContext`, and logs the touched module.
- `.claude/hooks/stop-coldbuild.py` — Stop/SubagentStop: cold-builds every touched module; on
  failure emits `{"decision":"block","reason":…}` to force the agent to continue; clean → allows
  stop. Loop-guard: blocks ≤ `MAX_TRIES` (6), then allows stop with an `UNVERIFIED` banner so a
  stuck state is reported, never hung.
- `.claude/agents/lean-worker.md` — frontmatter wires the two hooks (alongside the git block) and
  tells the agent to rely on the automatic feedback and the cold gate instead of calling Lean.

## Deploy (in the MAIN repo, on a FRESH session)
Hook command paths are absolute `/workspaces/lean4-oseledets/.claude/...` (matching the existing
`block-git.sh`), so this branch is meant to be merged into the main repo. After merging:
1. One-time: build the REPL (the eval already did this in `/tmp/lean-repl`; for a permanent
   install put it at `.lake/packages/REPL` or set `LEANCHECK_REPL`):
   `git clone https://github.com/leanprover-community/repl /tmp/lean-repl && \
    (cd /tmp/lean-repl && git checkout f0a88bfca1fa && lake build)`
2. `chmod +x .claude/leancheck/leancheck.py .claude/hooks/*.py`
3. **Restart the session** (hooks arm only at session start — same as the git block) and
   dispatch a throwaway `lean-worker` that Edits a `.lean` file; confirm it gets a leancheck
   report automatically and that a deliberately-broken edit cannot stop (cold gate blocks).
4. Optional pre-warm before a batch: `LEANCHECK_KEY=<session> leancheck --warm` (else the first
   edit pays the one-time ~168 s import).

## Env knobs
`LEANCHECK_ROOT` (repo root), `LEANCHECK_REPL` (repl binary), `LEANCHECK_KEY` (per-worker socket
isolation — the hooks set it to the session id), `LEANCHECK_IMPORT` (default `import Oseledets`;
**never** bare `import Mathlib` — that yields a broken env), `LEANCHECK_SETOPTS`.

## Status / what is and isn't tested here
- Pure logic (import-stripping, exact line remap, response→diagnostics formatting, sorry/clean
  cases) is covered by `leancheck.py --selftest` and passes.
- **End-to-end warm/cold was NOT run in this worktree**: a fresh git worktree has no
  `.lake/build` oleans (gitignored) and `lake exe cache get` is DNS-blocked here, so the REPL
  can't load Mathlib in the worktree. The underlying warm REPL was already measured working in
  the main repo (see the evaluation doc); run step 3 above there to validate the full hook loop.
- Invariant preserved: warm = fast inner-loop feedback; the cold `lake build` (Stop gate +
  orchestrator's umbrella build + guarded `AxiomAudit`) remains the source of truth.

## Per-worker resource note
Each worker keeps one warm REPL (~1.5–2 GB resident). Fine at concurrency 4–8 on this box
(31–64 GB). The socket is keyed by `LEANCHECK_KEY` so parallel workers don't collide.
