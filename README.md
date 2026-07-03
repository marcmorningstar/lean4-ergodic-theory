# Oseledets — Lean 4 formalization

[![Blueprint and documentation](https://github.com/marcmorningstar/lean4-oseledets/actions/workflows/blueprint.yml/badge.svg)](https://github.com/marcmorningstar/lean4-oseledets/actions/workflows/blueprint.yml)
[![Build](https://github.com/marcmorningstar/lean4-oseledets/actions/workflows/push.yml/badge.svg)](https://github.com/marcmorningstar/lean4-oseledets/actions/workflows/push.yml)

A Lean 4 + Mathlib formalization of the **Oseledets multiplicative ergodic theorem** (MET)
and a broad layer of companion results.

📖 **[Blueprint](https://marcmorningstar.github.io/lean4-oseledets/blueprint/)** ·
**[Blueprint (PDF)](https://marcmorningstar.github.io/lean4-oseledets/blueprint.pdf)** ·
**[Dependency graph](https://marcmorningstar.github.io/lean4-oseledets/blueprint/dep_graph_document.html)** ·
**[API documentation](https://marcmorningstar.github.io/lean4-oseledets/docs/)**

(The documentation site is published once the repository is public and GitHub Pages is enabled.)

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

The library also includes a finite-dimensional **quantum-information layer**
(`Oseledets/OperatorEntropy/`, issues #22–#28), built on the same matrix/CFC infrastructure:
the von Neumann and Umegaki relative entropies, Klein's inequality and **Lieb's joint-convexity
theorem**, the **CPTP data-processing inequality** (`monotonicity_relEntropy_under_CPTP`), the
**CNT dynamical entropy** (whose abelian corner recovers the classical Kolmogorov–Sinai entropy,
`cntDynamicalEntropyAbelian_eq_ksEntropy`), and **both directions of Petz's equality theorem** —
recovery ⟹ saturation (`petz_recovery_implies_equality`) and, fully general, saturation ⟹
recovery (`petz_equality_recovery_general`, for every faithful-state `KrausChannel`). All
sorry-free and axiom-audited.

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
  OperatorEntropy/    -- finite-dim quantum-information layer (issues #22–#28): von Neumann &
                      --   Umegaki relative entropy, Klein/Lieb joint convexity, the CPTP
                      --   data-processing inequality, CNT dynamical entropy, Petz recovery +
                      --   equality theorem (both directions)
test/
  AxiomAudit.lean     -- guarded #print-axioms regression (separate lib; not upstreamable source)
blueprint/            -- leanblueprint LaTeX source (web + PDF; \lean-linked to declarations)
home_page/            -- Jekyll landing page for the GitHub Pages site
lakefile.toml         -- package config (Oseledets + AxiomAudit libraries; depends on Mathlib + checkdecls)
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

## Blueprint and documentation

The repository ships a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) blueprint
under `blueprint/` whose nodes are `\lean`-linked to the formalized declarations, plus a
`doc-gen4` API-documentation build. The `.github/workflows/blueprint.yml` workflow compiles the
blueprint (web + PDF + dependency graph) and the API docs and deploys them to GitHub Pages on every
push to `main`; on pull requests it builds them as a dry run without deploying.

To build the blueprint locally (requires a TeX distribution, `graphviz`, and
`pip install leanblueprint`):

```bash
lake build                          # the Lean library must be built first
leanblueprint pdf                   # blueprint/print/print.pdf
leanblueprint web                   # blueprint/web/ (also writes blueprint/lean_decls)
lake exe checkdecls blueprint/lean_decls   # verify every \lean{...} name exists
```

`checkdecls` is wired into `lakefile.toml`, so `lake exe checkdecls blueprint/lean_decls` (run by
CI) fails the build if any blueprint declaration name drifts from the Lean source.

## Development environment

A `.devcontainer/` is provided (Lean 4 + the `leanprover.lean4` VS Code extension). Open the
repo in a devcontainer-aware editor for a ready-to-go toolchain.
