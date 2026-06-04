# Oseledets — Lean 4 formalization

A Lean 4 + Mathlib formalization of the **Oseledets multiplicative ergodic
theorem** (MET).

> Status: **skeleton.** The project is freshly scaffolded — the library
> currently builds an empty shell with no mathematical content yet. The
> theorem statements and proofs are added incrementally from here.

## Layout

```
Oseledets.lean        -- library root; imports every module
Oseledets/
  Basic.lean          -- placeholder module (no content yet)
lakefile.toml         -- package config (single `Oseledets` library, depends on Mathlib)
lean-toolchain        -- pinned Lean version
```

## Building

```bash
lake build        # or: make build
```

Mathlib is the only dependency. In a fresh checkout, fetch the precompiled
cache before the first build:

```bash
lake exe cache get
```

(The devcontainer's `post-create.sh` does this automatically.)

## Development environment

A `.devcontainer/` is provided (Lean 4 + the `leanprover.lean4` VS Code
extension). Open the repo in a devcontainer-aware editor to get a ready-to-go
toolchain.
