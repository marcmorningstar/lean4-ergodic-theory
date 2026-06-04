# CLAUDE.md — project orientation

This repository is a **Lean 4 + Mathlib formalization of the Oseledets
multiplicative ergodic theorem (MET)**. It is a single-purpose Lean project
(not a monorepo).

## Status

Freshly scaffolded skeleton. The `Oseledets` library builds an empty shell —
no mathematical content yet. Build it to confirm the toolchain and Mathlib
dependency are wired up correctly, then grow the formalization from here.

## Layout

| Path | Purpose |
|---|---|
| `Oseledets.lean` | Library root; imports every module of the formalization. |
| `Oseledets/` | Library modules. Currently only `Basic.lean` (placeholder). |
| `lakefile.toml` | Package config: one `Oseledets` lib, depends on Mathlib. |
| `lean-toolchain` | Pinned Lean version (`leanprover/lean4:v4.30.0-rc2`). |
| `lake-manifest.json` | Pinned dependency revisions. |
| `.github/workflows/` | CI: `lake build` on push and PR. |
| `.devcontainer/` | Lean 4 dev container. |

## Build commands

```bash
lake build          # build the library (alias: make build)
lake exe cache get  # fetch the Mathlib precompiled cache (first checkout)
lake clean          # remove local build artifacts (make clean)
```

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
