# ErgodicTheory — Lean 4 formalization

[![Blueprint and documentation](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/blueprint.yml/badge.svg)](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/blueprint.yml)
[![Build](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/push.yml/badge.svg)](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/push.yml)

A large-scale Lean 4 + Mathlib formalization of smooth ergodic theory, built around the
**Oseledets multiplicative ergodic theorem** (MET) and extending through Kolmogorov–Sinai
entropy theory, **Krieger's finite generator theorem**, the pointwise
**Shannon–McMillan–Breiman theorem**, the **Margulis–Ruelle inequality**, a coarse-grained
**multifractal formalism**, and a finite-dimensional **quantum-information layer**
(Lieb's joint convexity, the data-processing inequality, Petz's equality theorem).

**306 modules · ~85,000 lines · ~2,200 theorems — sorry-free, linter-enforced, and with 496
declarations continuously axiom-audited down to `[propext, Classical.choice, Quot.sound]`.**

📖 **[Project site](https://marcmorningstar.github.io/lean4-ergodic-theory/)** ·
**[Blueprint](https://marcmorningstar.github.io/lean4-ergodic-theory/blueprint/)** ·
**[Blueprint (PDF)](https://marcmorningstar.github.io/lean4-ergodic-theory/blueprint.pdf)** ·
**[Dependency graph](https://marcmorningstar.github.io/lean4-ergodic-theory/blueprint/dep_graph_document.html)**

## Headline theorems

All declarations live in the `ErgodicTheory` namespace (omitted below).

| Declaration | What it proves |
|---|---|
| `oseledets_filtration` | The one-sided Oseledets MET (filtration form): distinct Lyapunov exponents `λ₁ > ⋯ > λ_k` and a measurable equivariant flag with exact growth `(1/n) log‖A⁽ⁿ⁾(x)v‖ → λᵢ` on each stratum |
| `oseledets_splitting` | The two-sided MET: an invariant direct-sum Oseledets splitting `Eᵢ = Vᵢ ⊓ W_{rev i}` with two-sided growth `±λᵢ` over an invertible base |
| `oseledets_flow` | The continuous-time MET for measure-preserving ℝ-flows, with flow-equivariant filtration and continuous-parameter growth |
| `Krieger.krieger_finite_generator` | Krieger's finite generator theorem: an ergodic aperiodic automorphism with `h(T) < log k` has a two-sided generator of size `≤ k` |
| `Krieger.ae_tendsto_div_infoFun` | The pointwise Shannon–McMillan–Breiman theorem `(1/n)·iₙ(x) → h(P,T)` a.e. |
| `Entropy.abramov_rokhlin` | The Abramov–Rokhlin addition formula `h(T) = h(S) + h(T \| comap π)` for skew products |
| `Entropy.ksEntropy_eq_ksEntropyPartition_of_generating` | The Kolmogorov–Sinai generator theorem `h(T) = h(T,P)` (with a two-sided variant) |
| `margulisRuelle_sharp` | The Margulis–Ruelle inequality `h_μ(T) ≤ ∑ λᵢ⁺` |
| `OperatorEntropy.Lieb.relEntropyMat_jointly_convex` | **Lieb's theorem**: joint convexity of the Umegaki relative entropy |
| `OperatorEntropy.Lieb.relEntropyMonotone_partialTrace` | The partial-trace data-processing inequality `S(Tr_E ρ ‖ Tr_E σ) ≤ S(ρ‖σ)` (arbitrary ρ, faithful σ) |
| `OperatorEntropy.Lieb.petz_equality_recovery_general` | Petz's equality theorem, fully general: DPI saturation ⟹ Petz recovery, for every faithful-state Kraus channel |

Every theorem above (and ~490 further results) is guarded in `test/AxiomAudit.lean` by
`#guard_msgs in #print axioms`: the build **fails** if any of them ever acquires an axiom beyond
`propext`, `Classical.choice`, `Quot.sound` — so in particular none depends on `sorryAx`.

## What is formalized

### The Oseledets core (`Cocycle/`, `Ergodic/`, `Lyapunov/`, `TwoSided/`, `Continuous/`)

The iterated linear cocycle with Furstenberg–Kesten theory, the maximal ergodic inequality with
Birkhoff's and Kingman's theorems, and the full assembly of the one-sided MET
(`MultiplicativeErgodic.lean`), the two-sided splitting, and the continuous-flow version.
`Lyapunov/Extensions/` adds the post-theorem corollary layer: the Lyapunov spectrum as a
consumable object, positive/negative exponent sums, the trace–determinant identity,
exterior/wedge (k-volume) growth, the inverse/time-reversal spectrum, restriction to invariant
subbundles, the non-ergodic relaxation, regularity of the exponents in the generator
(semicontinuity, a Vitali/uniform-integrability regime), and one-sided singular bounds without
invertibility. `Singular/` supplies the measurable orthogonal projector of the singular forward
filtration (via `MeasureTheory/`: Lusin's theorem that analytic sets are universally measurable).

### Entropy and generators (`Entropy/`, `Krieger/`)

A self-contained Kolmogorov–Sinai entropy theory (~80 modules): partitions and joins, conditional
and relative entropy, KS entropy as a Fekete limit, the generator theorem (one- and two-sided),
the Abramov–Rokhlin formula, and the Margulis–Ruelle inequality `h ≤ ∑λ⁺` connecting entropy back
to the Lyapunov spectrum. On top of it, the full coding stack for **Krieger's finite generator
theorem** — Rokhlin/Kakutani towers, name counting, sentinel/prefix codes — together with the
pointwise SMB theorem and the Krieger–Keane–Serafin countable generator.

### Multifractal analysis (`Multifractal/`)

The coarse-grained multifractal formalism of an invariant measure: partition function `Z_q`, mass
exponent `τ(q)` (proved concave — the Legendre-transform heart), Rényi/generalized dimensions
`D_q` (proved monotone, with the `q = 1` information-dimension branch), local and Hausdorff
dimension (`dimH μ = h_μ/log 2` for Bernoulli measures), and a fully constructed Bernoulli
suspension flow realizing a genuinely `q`-dependent spectrum.

### Smooth maps and worked examples (`Smooth/`, `Examples/`)

The derivative (tangent) cocycle of a smooth self-map, feeding the MET, and the foliation-free
expanding-case **Pesin = Rokhlin identity** `∑λ⁺ = ∫ log|det DₓT| dμ`. Concrete systems
instantiate the abstract theory end to end: the **Arnold cat map** as a genuine hyperbolic
automorphism of 𝕋² (measure-preserving, ergodic, positive top exponent, entropy bounds) and the
**doubling map** (Lyapunov spectrum, Ruelle bound, Rokhlin entropy equality).

### Quantum information (`OperatorEntropy/`)

A finite-dimensional quantum-information layer on the same matrix/CFC infrastructure: the von
Neumann and Umegaki relative entropies, Klein's inequality, **Lieb's joint-convexity theorem**,
the **partial-trace data-processing inequality** (arbitrary ρ, faithful σ) with its
faithful-ancilla Stinespring-family extension (`monotonicity_relEntropy_under_stinespring`; no
DPI for an arbitrary CPTP channel is claimed), the **CNT dynamical entropy** whose abelian corner
recovers classical KS entropy (the system-level identity
`cntDynamicalEntropyAbelian_eq_ksEntropy` is a disclosed `0 = 0` on the finite-permutation model;
the substantive content is the per-resolution
`vonNeumannEntropy_corrMatrix_eq_ksEntropySeq`), and **both directions of Petz's equality
theorem** — recovery ⟹ DPI saturation (`petz_recovery_implies_equality`) and, fully general,
saturation ⟹ recovery (`petz_equality_recovery_general`), whose analytic heart is the
modular-cocycle intertwining `partialTrace_equality_imp_intertwinesIt`.

## Trust story

- **Sorry-free**: warnings are promoted to errors in `lakefile.toml`, so any `sorry` fails
  `lake build` (and CI). In-progress material lives in the separate `Frontier` staging library,
  unreachable from the default build.
- **Linter-enforced**: the whole `ErgodicTheory` library builds under Mathlib's
  `linter.mathlibStandardSet` with warnings-as-errors, so CI fails on any style-lint regression.
- **Axiom-audited**: `test/AxiomAudit.lean` guards 496 declarations with
  `#guard_msgs in #print axioms` on every build. (This certifies axiom-cleanliness; theorems with
  hypotheses are, as always, exactly as strong as their hypotheses — the blueprint states them in
  full.)
- **Blueprint-checked**: `lake exe checkdecls` (run by CI) verifies every `\lean{...}` name in the
  blueprint against the built library, so the blueprint cannot drift from the source.

## Layout

```
ErgodicTheory.lean        -- library root; imports every module
ErgodicTheory/
  Cocycle/            -- iterated linear cocycle, norms, Furstenberg–Kesten
  Ergodic/            -- maximal ergodic inequality, Birkhoff, Kingman
  Lyapunov/           -- Lyapunov exponents, the limsup filtration, the final assembly chain
    Extensions/       -- post-theorem corollaries (spectrum, exponent sums, det identity, exterior
                      --   growth, inverse, restriction, non-ergodic, regularity, singular)
  MultiplicativeErgodic.lean  -- the one-sided MET (filtration form)
  TwoSided/           -- the two-sided splitting
  Continuous/         -- the continuous-flow MET (+ suspension flows)
  Singular/           -- measurable projector of the singular forward filtration
  Entropy/            -- Kolmogorov–Sinai entropy theory: partitions, conditional entropy,
                      --   generator theorem, Abramov–Rokhlin, Margulis–Ruelle
  Krieger/            -- Krieger's finite generator theorem, SMB, Rokhlin towers, coding
  Multifractal/       -- Z_q, τ(q), Rényi dimensions D_q, local/Hausdorff dimension,
                      --   Bernoulli-suspension witness
  Smooth/             -- derivative cocycle, expanding-case Pesin = Rokhlin identity
  Examples/           -- Arnold cat map, doubling map, Rokhlin-equality witnesses
  OperatorEntropy/    -- quantum information: relative entropy, Klein/Lieb, data processing,
                      --   CNT dynamical entropy, Petz recovery + equality
  MeasureTheory/      -- classical residuals (analytic sets universally measurable, covering
                      --   numbers from volume)
test/
  AxiomAudit.lean     -- guarded #print-axioms regression (separate lib; not upstreamable source)
blueprint/            -- leanblueprint LaTeX source (web + PDF; \lean-linked to declarations)
home_page/            -- Jekyll landing page for the GitHub Pages site
Frontier/             -- disclosed staging area (separate `Frontier` lake lib): import-free, sorry-free
                      --   root; the sorry-carrying Frontier.Issue* subtree is unreachable from any default build
lakefile.toml         -- package config (ErgodicTheory + AxiomAudit + Frontier libraries)
lean-toolchain        -- pinned Lean version (leanprover/lean4:v4.30.0-rc2)
docs/                 -- research notes, design records, references.bib, progress state
```

## Building

```bash
lake build        # or: make build  — builds the library and the axiom audit
```

The dependencies are Mathlib (pinned in `lake-manifest.json`) and
[checkdecls](https://github.com/PatrickMassot/checkdecls), a tiny standalone utility used by the
blueprint CI. In a fresh checkout, fetch the precompiled Mathlib cache first:

```bash
lake exe cache get
```

(The devcontainer's `post-create.sh` does this automatically.)

## Blueprint

The repository ships a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) blueprint
under `blueprint/` — ten chapters covering the cocycle theory, the ergodic theorems, the Lyapunov
assembly, the MET and its corollaries, the two-sided and continuous versions, and the quantum
entropy/Petz layer — whose nodes are `\lean`-linked to the formalized declarations. The
`.github/workflows/blueprint.yml` workflow compiles the blueprint (web + PDF + dependency graph)
and deploys it to GitHub Pages on every push to `main`; on pull requests it builds as a dry run
without deploying. (The doc-gen4 API reference is deliberately not built in CI — regenerating
HTML for the entire Mathlib import closure exceeds the CI budget.)

To build the blueprint locally (requires a TeX distribution, `graphviz`, and
`pip install leanblueprint`):

```bash
lake build                          # the Lean library must be built first
leanblueprint pdf                   # blueprint/print/print.pdf
leanblueprint web                   # blueprint/web/ (also writes blueprint/lean_decls)
lake exe checkdecls blueprint/lean_decls   # verify every \lean{...} name exists
```

## Development environment

A `.devcontainer/` is provided (Lean 4 + the `leanprover.lean4` VS Code extension). Open the
repo in a devcontainer-aware editor for a ready-to-go toolchain.

## License

Apache 2.0 — see [LICENSE](LICENSE).
