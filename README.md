# Oseledets — Lean 4 formalization

A Lean 4 + Mathlib formalization of the **Oseledets multiplicative ergodic theorem** (MET)
and a broad layer of companion results.

## Status: complete

Three headline theorems are fully proved, sorry-free:

| Theorem | File |
|---|---|
| `Oseledets.oseledets_filtration` — one-sided MET (filtration form) | `Oseledets/MultiplicativeErgodic.lean` |
| `Oseledets.oseledets_splitting` — two-sided splitting | `Oseledets/TwoSided/SplittingAssembly.lean` |
| `Oseledets.oseledets_flow` — continuous-flow MET | `Oseledets/Continuous/MultiplicativeErgodicFlow.lean` |

together with a layer of companion results (`Oseledets/Lyapunov/Extensions/`: the Lyapunov
spectrum, exponent sums, the trace–determinant identity, exterior/wedge growth, the inverse
spectrum, restriction to invariant subbundles, the non-ergodic spectrum, regularity of the
exponents, and singular one-sided bounds).

The library builds sorry-free, is enforced linter-clean under Mathlib's
`linter.mathlibStandardSet` (warnings are promoted to errors), and a guarded axiom audit
(`test/AxiomAudit.lean`) confirms every headline result and its corollaries depend on exactly
`[propext, Classical.choice, Quot.sound]`.

## Layout

```
Oseledets.lean        -- library root; imports every module
Oseledets/
  Cocycle/            -- iterated linear cocycle, norms, Furstenberg–Kesten
  Ergodic/            -- maximal ergodic inequality, Birkhoff, Kingman
  Lyapunov/           -- Lyapunov exponents, the limsup filtration, the final assembly chain
    Extensions/       -- post-theorem corollaries (spectrum, exponent sums, det identity,
                      --   exterior growth, inverse, restriction, non-ergodic, regularity, singular)
  MultiplicativeErgodic.lean  -- the one-sided MET (filtration form)
  TwoSided/           -- the two-sided splitting
  Continuous/         -- the continuous-flow MET
test/
  AxiomAudit.lean     -- guarded #print-axioms regression (separate lib; not upstreamable source)
lakefile.toml         -- package config (Oseledets + AxiomAudit libraries; depends on Mathlib)
lean-toolchain        -- pinned Lean version
docs/                 -- research notes, design records, references.bib, progress state
```

## Building

```bash
lake build        # or: make build  — builds the library and the axiom audit
```

Mathlib is the only dependency. In a fresh checkout, fetch the precompiled cache first:

```bash
lake exe cache get
```

(The devcontainer's `post-create.sh` does this automatically.)

The `Oseledets` library is built with `linter.mathlibStandardSet` enabled and warnings promoted
to errors, so `lake build` (and CI) fails on any style-lint regression.

## Development environment

A `.devcontainer/` is provided (Lean 4 + the `leanprover.lean4` VS Code extension). Open the
repo in a devcontainer-aware editor for a ready-to-go toolchain.
