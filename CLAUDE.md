# CLAUDE.md — project orientation

This repository is a **Lean 4 + Mathlib formalization of the Oseledets
multiplicative ergodic theorem (MET)**. It is a single-purpose Lean project
(not a monorepo).

## Status

**COMPLETE.** The target theorem `Oseledets.oseledets_filtration`
(`Oseledets/MultiplicativeErgodic.lean`) is fully proved sorry-free, together with companion
corollaries (`Oseledets/Lyapunov/Corollaries.lean`: spectrum uniqueness, top-exponent = norm
growth, a.e.-constant multiplicities, …), the additive extensions (`Oseledets/Lyapunov/`:
Lyapunov spectrum, exponent sums, exterior/wedge growth, trace–det identity, inverse/time-
reversal, restriction, non-ergodic, regularity, singular), the **two-sided splitting**
(`Oseledets/TwoSided/`: `oseledets_splitting`), and the **continuous-flow MET**
(`Oseledets/Continuous/`: `oseledets_flow`). A guarded audit module
(`test/AxiomAudit.lean`, a separate `AxiomAudit` lib kept out of the upstreamable library so the
library source has no `#print axioms`) checks on every build — via `#guard_msgs in #print axioms`
— that the target theorem and each of these results depend on exactly
`[propext, Classical.choice, Quot.sound]` (the build fails if this ever changes; it is
not printed). The library is Mathlib-style linter-clean under
`linter.mathlibStandardSet`. See `docs/progress/STATE.md` for the final composition.

## Layout

| Path | Purpose |
|---|---|
| `Oseledets.lean` | Library root; imports every module of the formalization. |
| `Oseledets/` | Library modules: `Cocycle/`, `Ergodic/`, `Lyapunov/` (incl. `Corollaries.lean`), `MultiplicativeErgodic.lean` (the proved target theorem), `TwoSided/`, `Continuous/`. |
| `test/AxiomAudit.lean` | The guarded axiom-check (separate `AxiomAudit` lib; not part of the `Oseledets` library). |
| `lakefile.toml` | Package config: the `Oseledets` lib + the `AxiomAudit` test lib (both default targets), depends on Mathlib. |
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
`lake build`/`lake serve` recompiles Mathlib *from source* (hours). The `leancheck` harness
(`docs/leancheck-README.md`) detects this and **aborts with a loud warning** rather than start the
rebuild silently; override only by choice with `LEANCHECK_ALLOW_MATHLIB_REBUILD=1`. A direct
`lake build` is *not* guarded — run `leancheck --check-mathlib` first if unsure whether the cache
is in place.

## Conventions

- `autoImplicit` is **off** (set in `lakefile.toml`) — declare implicit
  variables explicitly.
- New modules go under `Oseledets/` and must be imported (directly or
  transitively) from `Oseledets.lean` so they are part of the build.
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
