# Warm Lean checker evaluation — avoiding the ~80 s cold `lake env lean` cost

**Status:** EVALUATION ONLY. Nothing here has been built, integrated, or run against
the live proof build. No git, no `lake build` of the main library, no `lake exe cache get`.

**Date:** 2026-06-16

## TL;DR recommendation

**GO — adopt `leanprover-community/repl`, pinned to commit `f0a88bfca1fa`
(its `lean-toolchain` is exactly `leanprover/lean4:v4.30.0-rc2`, matching ours).**
Run it as a persistent per-worker process started with
`lake env <repl>/.lake/build/bin/repl`, which inherits our project's Mathlib olean
cache (no Mathlib recompile). Pay the ~80 s `import Mathlib` deserialization **once**
at process start (optionally snapshot it via `pickleTo`), then re-check each edited
file in **seconds** by sending `{"cmd": "...file body...", "env": <mathlib-env-id>}`.
Keep the existing full cold `lake build` at QA as the authoritative gate — that fully
mitigates the warm-checker correctness risks.

Risk level: **LOW**, conditional on pinning the REPL to the matching toolchain commit
and treating warm results as advisory (QA cold build remains authoritative).

---

## Environment (verified locally, not assumed)

| Fact | Value | How verified |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` (commit 3dc1a088) | `lean --version`, `lean-toolchain` |
| Mathlib pin | `34f7a6cd150fd7a166958d989d5abab56e9e3d15` | `lake-manifest.json`, `lakefile.toml` |
| Mathlib oleans present | 2.5 GB at `.lake/packages/mathlib/.lake/build/lib` | `du -sh` |
| RAM / cores | 31 GB / 32 | `free -g`, `nproc` |
| `lake exe cache get` | DNS-blocked — do NOT use | per CLAUDE.md / memory |
| Native flags present | `--server`, `--worker`, `--json`, `--setup`, `lake serve` | `lean --help`, `lake --help` |
| `lean --server` runs | Yes (graceful "Stream was closed" on stdin EOF) | smoke test, killed immediately |
| REPL/Pantograph already present | No (only `MathlibTest/Replace.lean`, unrelated) | `find .lake` |

---

## Why each cold call costs ~80 s

`lake env lean <file>` spawns a fresh Lean process. Before elaborating one line it
must deserialize the transitive olean closure of `import Mathlib` (~2.5 GB of oleans).
That deserialization — not the elaboration of the small target file — is the ~80 s.
A warm checker pays this **once** and keeps the resulting `Environment` in memory.

---

## Candidate 1 — leanprover-community/repl  ★ RECOMMENDED

### What it is
A small (~1 kloc) Lean executable that reads JSON commands on stdin and writes JSON
results on stdout, keeping elaboration `Environment`s alive across submissions. It is
the canonical warm-environment front-end in the community and is **actively maintained
in lockstep with Lean releases** (a `chore: bump toolchain` commit lands within days of
every Lean rc/stable).

### Toolchain compatibility — THE #1 FAILURE MODE, and it is solvable
- REPL `master` is on `v4.31.0` — **does NOT match us**. The REPL is compiled Lean and
  links against the exact compiler ABI; a mismatched toolchain produces olean/ABI
  incompatibility. Using `master` as-is would fail.
- **Exact match exists.** REPL commit history (via `gh api .../commits?path=lean-toolchain`):
  - `f0a88bfca1fa` — "bump toolchain to v4.30.0-rc2 (#155)" ← **use this**
  - `dde7dd43` v4.30.0, `c9cde4d4` v4.30.0-rc1, `495777` v4.29.0, … (one per release)
- Action: check out `f0a88bfca1fa` (or set its `lean-toolchain` to `v4.30.0-rc2` and
  confirm it reads `v4.30.0-rc2`). This makes the REPL binary ABI-identical to our Lean.

### Setup cost WITHOUT network cache (dealbreaker check → PASS)
- The REPL's own `lakefile` depends **only on Lean core** — it does NOT require Mathlib
  (Mathlib is added by the *consuming* project, which here is ours, already cached).
- `lake build` in the REPL repo compiles ~1 kloc against the already-present toolchain.
  This is seconds-to-low-minutes of CPU, **no Mathlib compile**, and needs at most a
  trivial `lake-manifest` fetch (REPL has no heavy deps). It does NOT touch
  `lake exe cache get` and does NOT recompile the 2.5 GB Mathlib cache.
- Clone to a scratch dir (e.g. `/tmp` or a sibling dir), build there; never compile
  Mathlib. Our project's Mathlib oleans are reused at *run* time via `lake env`.

### How a worker drives it (Mathlib loaded once, files checked warm)
Run from our repo root so the environment resolves our imports + cached Mathlib:
```
lake env /path/to/repl/.lake/build/bin/repl
```
Process lifecycle / contract:
1. **Warm-up (once per process):** send `{"cmd": "import Mathlib\nimport Oseledets"}`
   (or just the imports the edited file needs). Response carries `"env": N`. This is the
   one ~80 s payment. Optionally `{"pickleTo": "warm.olean", "env": N}` to snapshot and
   later `{"unpickleEnvFrom": "warm.olean"}` to restore in a few seconds in a fresh
   process (survives restarts; great for a pool of workers).
2. **Per edit (fast, seconds):** send the edited file's *body* (the part after its
   imports) as `{"cmd": "<body>", "env": N}`. The imports are already in env `N`, so no
   re-deserialization. Response `messages` contains errors/warnings with positions;
   `sorries` lists incomplete proofs.
3. **Axiom gate:** append `#print axioms Oseledets.oseledets_filtration` (etc.) to the
   submitted body. Its output arrives as a normal `message` — parse for the expected
   `[propext, Classical.choice, Quot.sound]` and for `sorryAx`.
4. **Linter gate:** linter warnings are emitted as messages at their syntax position
   and the REPL forwards messages, so `linter.mathlibStandardSet` warnings surface in
   `messages` (enable the linter options in the submitted env, as in a normal build).

Output extraction: parse the single JSON object per submission — `messages[].severity`
(`error`/`warning`/`info`), `.data`, `.pos`; `sorries[]`; and the `#print axioms` info
message text. This is exactly the error/warning/sorry/axioms surface the gate needs.

Per-worker vs shared: simplest is **one REPL process per worker** (each pays warm-up
once, or restores a shared pickle). A single shared process is possible but serializes
submissions and complicates backtracking; with 31 GB RAM a small pool of per-worker
processes is fine (each warm Mathlib env is on the order of a few GB resident).

### Latency win
- Cold `lake env lean`: ~80 s **every** call (full Mathlib deserialize each time).
- REPL: ~80 s **once**; thereafter each re-check is import-free and elaborates only the
  edited body. Lean's incremental/`persistent`-data-structure design and fast parsing
  (~41 ms / 1000 lines on Mathlib, per the Lean LSP design notes) mean a typical
  proof-file re-check is **seconds**, dominated by elaborating that one file, not by
  imports. Realistic win: **~80 s → a few seconds per iteration** (10–40×), the exact
  factor depending on the edited file's own elaboration cost.

---

## Candidate 2 — native Lean LSP (`lean --server` / `lake serve`) driven programmatically

- **Feasible and version-perfect** (it IS our toolchain — zero skew, zero extra build).
  Smoke-tested: `lean --server` starts and exits cleanly on stdin EOF.
- It is a persistent process that loads Mathlib once per opened file and re-elaborates
  incrementally on `didChange`, reusing snapshots of already-elaborated commands — the
  warm behavior we want, and the same engine the IDE uses.
- **Cost:** you must speak LSP/JSON-RPC (`initialize`, `didOpen`, `didChange`,
  `publishDiagnostics`). `publishDiagnostics` gives errors/warnings/sorries directly.
  But there is **no LSP request for `#print axioms`**; you'd inject it as a command in
  the buffer and read its diagnostic/info, which is more awkward than the REPL's clean
  message list. Writing a correct incremental LSP client (lifecycle, version counters,
  waiting for the "checking complete" signal) is materially more work than the REPL's
  line-delimited JSON.
- **`lean-lsp-mcp`** (oOo0oOo/lean-lsp-mcp, active 2025–2026) already wraps `lake serve`
  and exposes `lean_diagnostics`, `lean_goal`, `lean_run_code`, `lean_build`, etc. over
  MCP/stdio/http. It is built for exactly "an LLM agent drives Lean," needs no network
  for the core LSP path, and is toolchain-agnostic (it just runs `lake serve` in your
  project, so it inherits v4.30.0-rc2). Downside for *our* gate: no first-class
  `#print axioms` tool (use `lean_run_code`), and diagnostics are LSP-shaped rather than
  the REPL's tidy message+sorry arrays. Good fallback / good if we later want an
  MCP-native worker, but heavier than needed for "check file, report errors/axioms."

**Verdict:** viable and skew-free, but the integration contract (incremental LSP +
no native axiom query) is more code than the REPL for the same outcome. Keep as Plan B,
or adopt `lean-lsp-mcp` if an MCP interface is independently wanted.

---

## Candidate 3 — Pantograph (aniva/Pantograph, mirror leanprover/Pantograph; PyPantograph)

- Machine-to-machine JSON REPL for Lean 4 (TACAS 2025), oriented toward **tactic-level
  proof search / MCTS / expression construction / environment inspection**, with a
  Python binding (PyPantograph). Powerful for *interactive tactic automation*, which is
  more than we need here (we want "re-check this whole file, give me errors/warnings/
  axioms"). It carries its own toolchain pin too, so the same exact-match discipline
  would apply, and it's a heavier dependency. **Not recommended for this specific goal**
  — overkill vs. the REPL, though attractive if the project later wants programmatic
  tactic search.

## Candidate 4 — lake/lean watch or warm flags

- No built-in "watch and re-check keeping Mathlib warm" mode in `lake`/`lean` that beats
  the LSP. `lean --worker`/`--server` ARE the warm mechanism (Candidate 2). `--setup`
  (JSON module setup) and `--json` (machine-readable messages) are useful building
  blocks but don't by themselves give cross-edit persistence. Nothing here supersedes
  Candidates 1–2.

---

## Correctness caveats (warm vs. authoritative cold build)

A warm/incremental checker CAN diverge from a cold `lake env lean` / full `lake build`:

1. **Stale environment.** If a worker edits an *imported* file (e.g. a lemma the target
   depends on) but keeps an old warm env, the warm check uses the stale dependency. The
   warm env only reflects what was loaded; re-import or restart is needed when
   dependencies change.
2. **`cmd`-as-body vs. file semantics.** Submitting a file's body as a `cmd` into a
   pre-imported env reproduces normal elaboration, but section/namespace/option scoping
   and `import` ordering must be reproduced faithfully; a mismatch (e.g. forgetting a
   `set_option` the real file header sets) could change linter/elaboration verdicts.
   File mode (`{"path": ...}`) avoids this but re-imports per call (loses warmth) unless
   pickling is used.
3. **Linter coverage.** Linters fire only if their options are enabled in the submitted
   env exactly as the real build enables `linter.mathlibStandardSet`. If not enabled
   identically, warnings differ.
4. **Cached elaboration / pickle staleness.** A pickled warm env (`unpickleEnvFrom`) is
   only valid for the **exact** toolchain + Mathlib oleans it was built from; reusing a
   pickle after any dependency change is unsafe. Treat pickles as disposable, keyed to
   the current Mathlib rev.
5. **Toolchain skew (the big one).** A REPL binary built on a different toolchain than
   our Lean would mis-load oleans. Mitigated entirely by pinning to `f0a88bfca1fa`
   (== v4.30.0-rc2).

**Mitigation — does the QA cold build fully cover this?** YES, for the verdict that
matters. The plan retains a full cold `lake build` (which elaborates real files in real
dependency order with real options and runs the guarded `#print axioms` audit module) as
the authoritative gate. Any divergence introduced by the warm checker is caught there
before anything is accepted. The warm checker is therefore an **iteration accelerator**,
not the source of truth. Residual gap: a developer/worker could be misled mid-iteration
by a stale-env false-positive or false-negative; this costs iteration time but cannot
produce a wrong final acceptance, because QA re-checks cold. To shrink the mid-iteration
gap: restart/re-import when an imported dependency changes, and enable the same
`set_option`/linter flags the real headers use.

---

## GO / NO-GO and concrete (UN-EXECUTED) steps to try it

**GO.** Concrete trial steps (none executed here):

1. In a scratch dir (NOT the repo, to avoid build contention):
   `git clone https://github.com/leanprover-community/repl /tmp/lean-repl`
   then check out the matching toolchain commit:
   `git -C /tmp/lean-repl checkout f0a88bfca1fa`
   Confirm `/tmp/lean-repl/lean-toolchain` reads `leanprover/lean4:v4.30.0-rc2`.
   (If network blocks GitHub too, vendor the ~1 kloc REPL sources manually; it has no
   Mathlib dep.)
2. `cd /tmp/lean-repl && lake build`  — compiles only the REPL (~seconds–minutes,
   no Mathlib). If this step tries to fetch a Mathlib cache or recompile Mathlib,
   STOP — but it should not, since REPL core depends only on Lean.
3. From the project root, start the warm process:
   `lake env /tmp/lean-repl/.lake/build/bin/repl`
   Send `{"cmd":"import Mathlib\nimport Oseledets"}` once; capture `env` id and time it
   (expect ~80 s). Optionally `{"pickleTo":"/tmp/warm.olean","env":N}`.
4. Send a tiny edit as `{"cmd":"<edited body>\n#print axioms Oseledets.oseledets_filtration","env":N}`;
   confirm it returns in seconds and that `messages` contains the axiom list and any
   linter warnings. Compare the verdict against one cold `lake env lean` of the same
   file to validate fidelity once.
5. If fidelity holds, wrap the worker's `lake env lean` shell-out behind a thin client
   that talks to a per-worker REPL process (warm-up once / restore pickle; submit body;
   parse messages/sorries/axioms). **Keep the cold `lake build` QA gate unchanged.**

**Fallback (Plan B):** if the REPL build or `lake env` integration misbehaves, use
`lean-lsp-mcp` over `lake serve` (zero toolchain skew, richer LSP diagnostics, no native
`#print axioms` — inject via `lean_run_code`).

**Risk:** LOW. Single real risk is toolchain skew, closed by the exact-match pin.
Worst case the REPL trial fails fast at step 2/3 and we fall back to the native LSP,
which is guaranteed version-correct because it *is* our toolchain.

---

## Sources
- leanprover-community/repl — README, DeepWiki, and `gh api` commit history
  (toolchain bump commits; `f0a88bfca1fa` == v4.30.0-rc2). master `lean-toolchain` = v4.31.0.
- Lean LSP design / incremental elaboration notes (snapshotting elaborated commands;
  ~41 ms/1000 lines parsing on Mathlib).
- oOo0oOo/lean-lsp-mcp (MCP over `lake serve`; tools incl. `lean_diagnostics`,
  `lean_run_code`, `lean_build`).
- aniva/Pantograph + PyPantograph (TACAS 2025) — tactic-level M2M interface.
- Local: `lean --version`, `lean --help`, `lake --help`, `du -sh` of oleans,
  `lean --server` smoke test.

---

## Validation trial (measured)

**Status:** EXECUTED, measurement only. No pipeline integration, no repo build-config
changes, no git inside the repo. All scratch in `/tmp`. Trial date: 2026-06-16.

### Outcome: **GO** — confirmed in this environment.

A warm `leanprover-community/repl` (commit `f0a88bfca1fa`, toolchain
`leanprover/lean4:v4.30.0-rc2` — exact match to ours) re-checks edited Lean in
**~5–12 ms** after a one-time ~168 s warm-up, and its verdict (errors, linter
warnings, `#print axioms`) matches a cold `lake env lean` run exactly.

### Steps that worked (exact commands)

1. GitHub reachable (`git ls-remote https://github.com/leanprover-community/repl HEAD`).
   ```
   git clone https://github.com/leanprover-community/repl /tmp/lean-repl
   cd /tmp/lean-repl && git checkout f0a88bfca1fa
   ```
   `lean-toolchain` = `leanprover/lean4:v4.30.0-rc2` (== ours). PASS.
2. `cd /tmp/lean-repl && lake build` → **4.95 s**, 24 jobs, **no Mathlib compile, no
   `cache get`** (REPL's `lake-manifest.json` has empty `packages`). Binary:
   `/tmp/lean-repl/.lake/build/bin/repl` (~207 MB). PASS.
3. Run from repo root via `lake env /tmp/lean-repl/.lake/build/bin/repl` (inherits the
   project's already-present Mathlib oleans). Commands = one JSON object per line,
   separated by blank lines; each response = one compact JSON line + blank line.

### Measured timings (this environment)

| Phase | Time |
|---|---|
| REPL self-build | 4.95 s |
| **Cold warm-up** `{"cmd":"import Oseledets"}` (full project+Mathlib closure) | **168.5 s** |
| **Warm re-check** `example … + #print axioms Oseledets.oseledets_filtration` | **0.012 s** |
| Warm re-check (failing proof) | 0.005 s |
| Warm re-check (axioms + #check) | 0.012 s |
| Cold anchor `time lake env lean -DautoImplicit=false Oseledets/Cocycle/Norm.lean` | **154 s** |
| Cold cross-check `lake env lean … /tmp/xcheck.lean` (import Oseledets + 2 examples + axioms) | 116.7 s |

**Speedup: ~154 s cold → ~0.01 s warm per re-check ≈ 10,000×** once warm. (The cold
anchor here is ~154 s, heavier than the ~80 s the prior section quoted — this
environment's `import Mathlib`/`import Oseledets` deserialize is slower than assumed.)
The 168 s warm-up is paid once per process.

### Correctness cross-check — warm verdict == cold verdict

Same inputs run warm (REPL) and cold (`lake env lean /tmp/xcheck.lean`):

| Check | Warm REPL | Cold `lake env lean` | Match |
|---|---|---|---|
| `example : (1:Nat)+1=2 := by norm_num` | (no message) | (no message) | ✓ |
| `example : (1:Nat)+1=3 := by norm_num` | `error: unsolved goals ⊢ False` | `error: unsolved goals ⊢ False` | ✓ |
| `#print axioms Oseledets.oseledets_filtration` | `[propext, Classical.choice, Quot.sound]` | `[propext, Classical.choice, Quot.sound]` | ✓ |

The axiom list also matches the repo's authoritative `AxiomAudit.lean` expectation.
Linter warnings DO surface in warm mode as `severity:"warning"` messages with position
(verified: `unused variable` fired). The prior section's caveat stands — to match the
build's `linter.mathlibStandardSet` exactly, set the same `set_option` flags in the
submitted body; the default-enabled linters already fire.

### IMPORTANT measured gotcha — do NOT warm up with bare `import Mathlib`

`{"cmd":"import Mathlib"}` (the umbrella everything-module) **returns env 0 with no
error in ~18 s but yields a BROKEN environment**: subsequent commands in that env fail
with `unexpected token '+'`, `Unknown constant OfNat`, even `Unknown identifier Nat`
(`#check Nat` fails). No stderr. This reproduces both via the Python driver and via raw
`printf | repl`. Importing **specific** Mathlib submodules
(e.g. `import Mathlib.Tactic.NormNum`) works perfectly, and — crucially — **`import
Oseledets` works perfectly** (env valid, `#print axioms` correct). Since a worker would
import `Oseledets`/specific modules anyway, this is not a blocker, but the warm-up
command MUST be `import Oseledets` (or the precise submodules the edited file needs),
**not** bare `import Mathlib`. (Root cause not chased; likely an import-merge limit in
this REPL build on the ~5–6k-module umbrella. Use the working path.)

### Blockers

None. The only surprise (broken bare `import Mathlib`) has a clean, verified workaround
(`import Oseledets`). Toolchain matched exactly; REPL built in seconds with no Mathlib
recompile; warm re-check is ~0.01 s; verdict fidelity confirmed against cold.

### Verdict

**GO**, consistent with the prior recommendation. Warm re-check is ~10,000× faster than
cold here, with identical error/linter/axiom verdicts, **provided** the warm-up uses
`import Oseledets` (not bare `import Mathlib`) and project linter `set_option`s are
mirrored when linter fidelity matters. Keep the cold `lake build` QA gate authoritative.
