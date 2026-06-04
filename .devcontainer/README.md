# DevContainer Reference

## What the container provides

After rebuild, the container supports all three `make` targets out of the box:

| Target           | Command          | What it does                              |
|------------------|------------------|-------------------------------------------|
| `make lean`      | `lake build`     | Typecheck all Lean 4 source files         |
| `make papers`    | `xelatex` × 3   | Build the three companion PDFs            |
| `make blueprint` | `latexmk`        | Build the blueprint PDF                   |
| `make all`       | all of the above | Full build                                |

## Installed tooling

### Already in the previous Dockerfile

| Package          | Purpose                                      |
|------------------|----------------------------------------------|
| `curl`           | Download elan installer                      |
| `ca-certificates`| HTTPS for git/curl                           |
| `git`            | Version control, lake dependency fetching    |
| `build-essential`| C compiler needed by some lake/Lean steps    |
| `sudo`           | DevContainer user privilege escalation       |
| `python3`        | Required by Pygments / leanblueprint         |
| elan             | Lean toolchain manager (installed via script)|

### Added in this update

**APT packages:**

| Package                      | Purpose                                              |
|------------------------------|------------------------------------------------------|
| `python3-pip`                | Install Python packages (Pygments, leanblueprint)    |
| `python3-dev`                | Python headers for native pip builds (`pygraphviz`)  |
| `graphviz`                   | Runtime tooling used by `pygraphviz` / blueprint deps |
| `graphviz-dev`               | Graphviz headers needed to build `pygraphviz`        |
| `pkg-config`                 | Lets `pygraphviz` discover Graphviz during install   |
| `texlive-xetex`             | XeLaTeX engine — papers use `fontspec` (Unicode)     |
| `texlive-latex-extra`        | LaTeX packages: `minted`, `enumitem`, `booktabs`, `mathtools` |
| `texlive-science`            | Additional math/science LaTeX packages               |
| `texlive-fonts-recommended`  | Standard fonts for TeX                               |
| `latexmk`                    | Build automation — used by `make blueprint`          |

**Python packages (pip):**

| Package         | Purpose                                                      |
|-----------------|--------------------------------------------------------------|
| `Pygments`      | Syntax highlighting backend for `minted` (Lean code blocks)  |
| `leanblueprint` | Lean 4 blueprint tooling — brings `plasTeX`, `plastexdepgraph`, `plastexshowmore` |

## Post-create script

`post-create.sh` runs automatically after container creation:

1. Installs the Lean toolchain pinned in `lean-toolchain` (currently `leanprover/lean4:v4.30.0-rc2`)
2. Runs `lake update` to resolve dependencies
3. Runs `lake exe cache get` to fetch precompiled Mathlib oleans (~2 GB download, saves hours of compilation)

## Image size

- Base image (debian:trixie-slim): ~80 MB
- With system packages + TeX Live: ~1.2 GB
- After post-create (Lean toolchain + Mathlib cache): ~4–5 GB total

## Picking up work after rebuild

After the container rebuilds, `post-create.sh` handles Lean setup automatically. To verify everything works:

```bash
make all        # full build: lean + papers + blueprint
```

Or individually:

```bash
lake build      # ~2 min with cached oleans, ~45 min without
make papers     # ~30 seconds
make blueprint  # ~10 seconds
```
