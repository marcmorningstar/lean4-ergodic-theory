# DevContainer Reference

A minimal Lean 4 + Mathlib development container, plus the Firecrawl CLI wired
to the host's self-hosted instance for web research.

## What the container provides

| Tool | Purpose |
|---|---|
| elan | Lean toolchain manager (toolchain resolved per-project from `lean-toolchain`) |
| `lake` | Lean build tool (ships with the toolchain) |
| `build-essential`, `git`, `curl`, `ca-certificates`, `sudo` | basics for elan/lake and `post-create.sh` |
| Node.js + `firecrawl-cli` | installed by `post-create.sh`; web search/scrape via the host's self-hosted Firecrawl |

## Build commands

```bash
lake build      # build the Oseledets library (alias: make build)
make clean      # lake clean
```

With a warm Mathlib cache this is fast; a cold cache (`lake exe cache get`)
downloads precompiled oleans rather than compiling Mathlib from source.

## Post-create script

`post-create.sh` runs automatically after container creation:

1. Installs the Lean toolchain pinned in `lean-toolchain` (currently `leanprover/lean4:v4.30.0-rc2`).
2. Fetches the precompiled Mathlib cache (`lake exe cache get`).
3. Installs Node.js + `firecrawl-cli` and points it at the host's self-hosted
   Firecrawl instance (`http://host.docker.internal:3002`, no auth) via
   `firecrawl login`. See the project `CLAUDE.md` for usage.

## Picking up work after rebuild

After the container rebuilds, `post-create.sh` handles setup automatically.
Verify with:

```bash
lake build                 # Lean library builds clean
firecrawl --status         # Firecrawl configured (ignore "account info" line)
```
