# CLAUDE.md — project orientation

This repository is a **Lean 4 + Mathlib formalization of the Oseledets
multiplicative ergodic theorem (MET)**. It is a single-purpose Lean project
(not a monorepo).

## ⚠️ Orchestration rules for the goal loop (DO NOT FORGET)

When grinding the open issues (#4/#5/#6) as an autonomous orchestrator, these are **invariants**,
not preferences. They must survive context summarization:

1. **Warm Lean checker is MANDATORY for every Lean worker.** Each agent that writes/iterates Lean
   gets its OWN warm `lwt` worktree — `.claude/scripts/lwt add <branch>` (default, **NEVER**
   `--no-warm`). The per-worktree `lake serve` daemon (leancheck PostToolUse hook) gives near-instant
   incremental re-checks. Cold-building after every edit takes ~30–60 s and makes iteration crawl —
   that is forbidden as the inner loop.
2. **One cold `lake build <Module>` per agent = the FINAL authoritative gate**, not the iteration
   loop. Warm leancheck is for iterating; the single cold build validates before reporting.
3. **One worktree per agent. Always.** Isolated `.lake/build` per tree ⇒ daemon + final build can't
   race siblings (the `setup.json` corruption mode is structurally excluded across trees).
4. **Parallel agents are encouraged** — multiple workers per issue, run in **waves of ~6–8 concurrent**
   warm worktrees to stay under the RAM line (~0.5 GB per serve daemon + ~2–4 GB per coincident build,
   ~31 GB usable on a 32-core box). CPU is not the bottleneck; RAM during simultaneous elaboration is.
5. **Never `sorry`, never axiomatize.** `warningAsError` makes any `sorry` a build failure; partial
   work stays OUT of the imported build until it compiles honestly. Every headline theorem keeps a
   `#guard_msgs in #print axioms` audit = `[propext, Classical.choice, Quot.sound]`.
6. **Workers never run git** (a worker reset once wiped siblings' edits). The orchestrator does all
   merges/commits/pushes and runs the authoritative builds.

## Status

**COMPLETE.** The target theorem `ErgodicTheory.oseledets_filtration`
(`ErgodicTheory/MultiplicativeErgodic.lean`) is fully proved sorry-free, together with companion
corollaries (`ErgodicTheory/Lyapunov/Extensions/Corollaries.lean`: spectrum uniqueness,
top-exponent = norm growth, a.e.-constant multiplicities, …), the additive extensions
(`ErgodicTheory/Lyapunov/Extensions/`:
Lyapunov spectrum, exponent sums, exterior/wedge growth, trace–det identity, inverse/time-
reversal, restriction, non-ergodic, regularity, singular), the **two-sided splitting**
(`ErgodicTheory/TwoSided/`: `oseledets_splitting`), and the **continuous-flow MET**
(`ErgodicTheory/Continuous/`: `oseledets_flow`). A guarded audit module
(`test/AxiomAudit.lean`, a separate `AxiomAudit` lib kept out of the upstreamable library so the
library source has no `#print axioms`) checks on every build — via `#guard_msgs in #print axioms`
— that the target theorem and each of these results depend on exactly
`[propext, Classical.choice, Quot.sound]` (the build fails if this ever changes; it is
not printed). The `ErgodicTheory` library is built with `linter.mathlibStandardSet` enabled and
warnings promoted to errors (`lakefile.toml`), so `lake build` — and hence CI — fails on any
style-lint regression. See `docs/progress/STATE.md` for the final composition.

A **finite-dimensional quantum-information layer** (`ErgodicTheory/OperatorEntropy/`, issues
#22–#28) has since been added on the same matrix/CFC infrastructure: the von Neumann and
Umegaki relative entropies, Klein's inequality and **Lieb's joint-convexity theorem**, the
**CPTP data-processing inequality**, the **CNT dynamical entropy** (whose abelian corner
recovers the classical Kolmogorov–Sinai entropy), and **both directions of Petz's equality
theorem** (Petz recovery ⟺ saturation of the data-processing inequality) — all sorry-free and
guarded in `test/AxiomAudit.lean` to the same axiom set.

## Layout

| Path | Purpose |
|---|---|
| `ErgodicTheory.lean` | Library root; imports every module of the formalization. |
| `ErgodicTheory/` | Library modules: `Cocycle/`, `Ergodic/`, `Lyapunov/` (incl. `Lyapunov/Extensions/` for the post-theorem corollaries), `MultiplicativeErgodic.lean` (the proved target theorem), `TwoSided/`, `Continuous/`. |
| `ErgodicTheory/OperatorEntropy/` | Finite-dim quantum-information layer (issues #22–#28): von Neumann & Umegaki relative entropy, Klein/Lieb joint convexity, the CPTP data-processing inequality, CNT dynamical entropy (abelian corner = classical KS entropy), and the Petz recovery + equality theorem (both directions). |
| `test/AxiomAudit.lean` | The guarded axiom-check (separate `AxiomAudit` lib; not part of the `ErgodicTheory` library). |
| `lakefile.toml` | Package config: the `ErgodicTheory` lib + the `AxiomAudit` test lib (both default targets), depends on Mathlib. |
| `lean-toolchain` | Pinned Lean version (`leanprover/lean4:v4.30.0-rc2`). |
| `lake-manifest.json` | Pinned dependency revisions. |
| `.github/workflows/` | CI: `lake build` on push and PR. |
| `.devcontainer/` | Lean 4 dev container. |

## Build commands

```bash
lake build          # build the library (alias: make build)
lake exe cache get  # fetch the Mathlib precompiled cache (first checkout ONLY — see below)
lake clean          # remove local build artifacts (make clean)
```

**Do not run `lake exe cache get` in this devcontainer**: the cache host is
DNS-blocked here and the command stalls indefinitely (verified 2026-06-10).
The Mathlib cache is already present (fetched by `.devcontainer/post-create.sh`
at container creation); incremental `lake build` is all that is ever needed.

**Mathlib-rebuild guard.** If Mathlib's oleans are ever absent (a fresh checkout, or — more
insidiously — a git worktree created without the prebuilt `.lake` cache or its symlink), any
`lake build`/`lake serve` recompiles Mathlib *from source* (hours). Warm per-edit Lean feedback is
provided by the external **`leancheck` Claude plugin** (`github.com/marcmorningstar/leancheck`),
whose `lake serve` daemon **aborts with a loud warning** rather than start such a rebuild (override
only by choice with `LEANCHECK_ALLOW_MATHLIB_REBUILD=1`). A direct `lake build` is *not* guarded and
is the authoritative gate — make sure the Mathlib cache is in place before building.

**Parallel agents — one worktree each.** Many agents grinding proofs at once must NOT share a
checkout: they race git's working tree and `.lake/build`. Give each its own git worktree with
`.claude/scripts/lwt` (a thin launcher over the `lwt` tool in the leancheck plugin):

```bash
WT=$(.claude/scripts/lwt add my-branch | tail -1)   # symlinks the shared Mathlib cache, copies the
                                                     # compiled .lake/build (first build = no-op),
                                                     # starts a per-worktree warm lake serve
# ... run an agent with cwd = $WT; it gets warm feedback + incremental builds, conflict-free ...
.claude/scripts/lwt remove my-branch --delete-branch # clean teardown (shared cache untouched)
```

Worktrees land under `/home/vscode` (overlay) because the checkout is on a slow 9p mount. `lwt list`
shows which trees are provisioned/warm. Merge the good branches back from the main checkout.

## Conventions

- `autoImplicit` is **off** (set in `lakefile.toml`) — declare implicit
  variables explicitly.
- New modules go under `ErgodicTheory/` and must be imported (directly or
  transitively) from `ErgodicTheory.lean` so they are part of the build.
- Keep the build green: every commit should `lake build` cleanly, with no
  `sorry` left unflagged.

## Web research (Firecrawl)

Web search/scrape is **preconfigured and ready** — for any agent, just call the
`firecrawl` CLI directly. No env vars, no setup, no auth flow:

```bash
firecrawl search "Oseledets multiplicative ergodic theorem proof"   # find sources
firecrawl scrape "https://arxiv.org/pdf/1710.10694"                 # get a page as markdown
firecrawl map "https://leanprover-community.github.io/mathlib4_docs" # list a site's URLs
```

It points at a self-hosted Firecrawl instance on the devcontainer host
(`host.docker.internal:3002`); the endpoint is persisted in the CLI's own
config (`~/.config/firecrawl-cli`) by `.devcontainer/post-create.sh`, so it
works in every shell.

- **Ignore** the `Could not fetch account info` line in `firecrawl --status` —
  the self-hosted instance has no account/credit tracking. Search/scrape/map
  still work; the CLI is authenticated.
- Output defaults to stdout; add `-o <file>` to save (the `firecrawl:*` skills
  use `.firecrawl/`, which is git-ignored).
- Prefer `firecrawl` over the built-in WebFetch/WebSearch for richer, full-page
  markdown when researching the math.

## Agents

`.claude/agents/` provides two domain-neutral helpers for Lean work:
`lean-worker` (implements proofs/definitions directly) and `mathematician`
(adversarial exploration + verification). Use them for formalization tasks.
