# Oseledets — Lean 4 formalization

A Lean 4 + Mathlib formalization of the **Oseledets multiplicative ergodic
theorem** (MET).

> Status: **complete.** The target theorem `Oseledets.oseledets_filtration`
> (`Oseledets/MultiplicativeErgodic.lean`) is fully proved: the library builds
> sorry-free and the axiom audit prints exactly
> `[propext, Classical.choice, Quot.sound]`.

## Layout

```
Oseledets.lean        -- library root; imports every module
Oseledets/
  Cocycle/            -- iterated linear cocycle, norms, Furstenberg–Kesten
  Ergodic/            -- maximal ergodic inequality, Birkhoff, Kingman
  Lyapunov/           -- exponents, filtration, measurability, final assembly
  MultiplicativeErgodic.lean  -- the proved target theorem (MET, filtration form)
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
