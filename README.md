# ErgodicTheory — Lean 4 formalization

[![Blueprint and documentation](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/blueprint.yml/badge.svg)](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/blueprint.yml)
[![Build](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/push.yml/badge.svg)](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/push.yml)

A large-scale Lean 4 + Mathlib formalization of smooth ergodic theory, built around the
**Oseledets multiplicative ergodic theorem** (MET) and extending through Kolmogorov–Sinai
entropy theory, **Krieger's finite generator theorem**, the pointwise
**Shannon–McMillan–Breiman theorem**, the **Margulis–Ruelle inequality** and the volume-case
**Pesin entropy formula**, **Livšic cohomological rigidity theory**, a representative-free
suspension-flow Lyapunov/entropy theory, a coarse-grained **multifractal formalism**, and a
finite-dimensional **quantum-information layer** (Lieb's joint convexity, the data-processing
inequality, Petz's equality theorem).

**370 modules · ~98,000 lines · ~2,700 theorems — sorry-free, linter-enforced, and with 646
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
| `integral_log_abs_det_le_ksEntropy` | The **Rokhlin inequality** `∫ log|det DₓT| dμ ≤ h_μ(T)` (generator-free, for `μ ≪ volume`) |
| `sumPosExp_le_ksEntropy_of_SRB` | The SRB reverse Pesin inequality `∑ λᵢ⁺ ≤ h_μ(T)`, discharging the hard leaf of issue #10 |
| `pesin_entropy_formula_spectral` | The **volume-case Pesin entropy formula** `h_μ(T) = ∑ λᵢ⁺` (both inequalities combined) |
| `Examples.Rokhlin.pesin_formula_doublingMap` | The first non-vacuous full-system Pesin instance: `h = ∑ λ⁺ = log 2` for the doubling map |
| `OperatorEntropy.Lieb.relEntropyMat_jointly_convex` | **Lieb's theorem**: joint convexity of the Umegaki relative entropy |
| `OperatorEntropy.Lieb.relEntropyMonotone_partialTrace` | The partial-trace data-processing inequality `S(Tr_E ρ ‖ Tr_E σ) ≤ S(ρ‖σ)` (arbitrary ρ, faithful σ) |
| `OperatorEntropy.Lieb.petz_equality_recovery_general` | Petz's equality theorem, fully general: DPI saturation ⟹ Petz recovery, for every faithful-state Kraus channel |
| `isHolderCoboundary_iff` | The **abstract Livšic theorem**: over a system with the exponential-closing property and a dense orbit, a Hölder function is a Hölder coboundary iff all its periodic-orbit sums vanish |
| `Livsic.livsic_measurable_rigidity` | **Full measurable Livšic rigidity** (Katok–Hasselblatt 19.2.4): over the two-sided full shift a merely measurable a.e.-solution of a Hölder cohomological equation agrees a.e. with a genuine Hölder coboundary |
| `not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero` | The **flow-Livšic obstruction**: a continuous roof with a nonzero closed-orbit integral is not a flow coboundary (instantiated on the cat-map suspension) |
| `ae_flowExponentAt_eq_base_div_roof` | The **representative-free suspension-flow Lyapunov exponent** `flowExponentAt = λ_base / ∫τ` a.e. — a genuine `Quotient.lift` value on orbit classes, not just a chosen representative |
| `ergodic_suspensionFlowMap_one_const_roof` | **Time-1 ergodicity** of the constant-**irrational**-roof suspension flow of an ergodic base with unimodular-eigenvalue rigidity |
| `ksEntropy_bernConstSuspension_time_one` | **Suspension entropy descent**: for a rational roof `r`, `h(ζ⁽ʳ⁾₁) = h_base / r`, built on the discrete entropy power rule `Entropy.ksEntropy_iterate` (`h(Tⁿ) = n·h(T)`) |
| `OperatorEntropy.CNT.ksEntropy_eq_cntDynamicalEntropy` | The **CNT collapse**: classical KS entropy equals the *full* CNT dynamical entropy on the abelian corner (a disclosed `0 = 0`; the genuine obstruction to a Fekete rate is `OperatorEntropy.CNT.not_subadditive_cnt_entropySeq`) |
| `measurable_orthProjMatrix_lambdaSublevel` | The **everywhere-Borel singular filtration** (issue #11): the orthogonal projector onto a sublevel set of the forward Lyapunov filtration is Borel measurable, via the Novikov projection theorem |

Every theorem above (and ~630 further results) is guarded in `test/AxiomAudit.lean` by
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
invertibility. `Singular/` supplies the everywhere-Borel orthogonal projector of the singular
forward filtration (`measurable_orthProjMatrix_lambdaSublevel`, issue #11), resting on the
descriptive-set-theoretic residuals in `MeasureTheory/` (see below).

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
expanding-case **Pesin = Rokhlin identity** `∑λ⁺ = ∫ log|det DₓT| dμ`. On top of this, the
**volume-case Pesin entropy formula** `h_μ(T) = ∑λ⁺` is now discharged (issue #10): the reverse
SRB inequality `∑λ⁺ ≤ h_μ(T)` follows from the standalone, generator-free **Rokhlin inequality**
`∫ log|det DₓT| dμ ≤ h_μ(T)`, combined with Margulis–Ruelle for the forward direction. Concrete
systems instantiate the abstract theory end to end: the **Arnold cat map** as a genuine hyperbolic
automorphism of 𝕋² (measure-preserving, ergodic, positive top exponent, entropy bounds) and the
**doubling map**, which now carries the first non-vacuous full-system Pesin instance in the
library — `h = ∑λ⁺ = log 2` (Lyapunov spectrum, Ruelle bound, binary-expansion generator).

### Livšic cohomological rigidity (`Livsic/`)

The Livšic theory of when a Hölder observable is a coboundary. The abstract engine
(`isHolderCoboundary_iff`) proves, for any system with an exponential-closing property and a dense
orbit, that a Hölder `φ` is a Hölder coboundary iff every periodic-orbit sum vanishes; it is
instantiated on the one-sided full shift (`Livsic.livsic_fullShift`), the two-sided full shift
(`livsic_biShift`), subshifts of finite type (`livsic_sft`), the Arnold cat map
(`CatMapToral.livsic_catTorus`), and the doubling map (`livsic_doublingMap`). The measurable-rigidity
tier culminates in the full **Katok–Hasselblatt 19.2.4** theorem (`Livsic.livsic_measurable_rigidity`):
a merely measurable a.e.-solution of the cohomological equation is a.e. equal to a genuine Hölder
coboundary. On the continuous-time side, the **flow-Livšic obstruction**
(`not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero`, witnessed by
`CatMapToral.const_one_not_isFlowCoboundary_catSuspension`) shows a roof with a nonzero closed-orbit
integral cannot be a flow coboundary — the converse (a full flow-Livšic theorem) is a documented
frontier.

### Suspension flows (`Continuous/`)

Beyond the abstract continuous-flow MET, the library builds the concrete **suspension/special flow**
of a base map under a roof function and analyzes its Lyapunov and entropy data. The flow Lyapunov
exponent is constructed **representative-free** as a `Quotient.lift` over orbit classes and computed
to `ae_flowExponentAt_eq_base_div_roof` — `flowExponentAt = λ_base / ∫τ` a.e. — with the cat-map
suspension as a fully worked positive-exponent instance
(`CatMapToral.catSuspension_flowExponentAt_eq_base_div_roof`). On the entropy side, the discrete
**entropy power rule** `Entropy.ksEntropy_iterate` (`h(Tⁿ) = n·h(T)`) descends through the constant-roof
time-change to give the time-1 entropy `h(ζ⁽ʳ⁾₁) = h_base / r` for every **rational** roof `r`
(`ksEntropy_bernConstSuspension_time_one`; the irrational-`r` case needs the deep half of Abramov's
homogeneity theorem and is disclosed as out of scope). Complementarily, the constant-roof time-1 map
of an ergodic Bernoulli base is **ergodic exactly when the roof is irrational**
(`ergodic_suspensionFlowMap_one_const_roof`).

### Descriptive-set-theoretic residuals (`MeasureTheory/`, `Singular/`)

The measurability of the singular Oseledets projector rests on a small library of classical
descriptive set theory built here from scratch: **Lusin's theorem** in the graph-measurability form
(`lusin_continuousOn`), the **generalized first separation theorem** for a sequence of analytic sets
(`generalized_first_separation`), the **Kunugui–Novikov** open-section separation
(`kunuguiNovikov_openSections`), and the **Novikov projection theorem** (Srivastava 4.7.11) that a
Borel set with compact vertical sections has Borel projection
(`measurableSet_image_fst_of_isCompact_sections`). Together they discharge the everywhere-Borel
singular filtration `measurable_orthProjMatrix_lambdaSublevel` (issue #11).

### Quantum information (`OperatorEntropy/`)

A finite-dimensional quantum-information layer on the same matrix/CFC infrastructure: the von
Neumann and Umegaki relative entropies, Klein's inequality, **Lieb's joint-convexity theorem**,
the **partial-trace data-processing inequality** (arbitrary ρ, faithful σ; also in the literal
faithful-case form `relEntropyMonotone_partialTrace_faithful` for positive-definite ρ, σ) with its
faithful-ancilla Stinespring-family extension (`monotonicity_relEntropy_under_stinespring`; no
DPI for an arbitrary CPTP channel is claimed), the **CNT dynamical entropy** whose abelian corner
recovers classical KS entropy — the system-level identity `cntDynamicalEntropyAbelian_eq_ksEntropy`
(and its full-partition upgrade `ksEntropy_eq_cntDynamicalEntropy`, a supremum over *all*
operational partitions) is a disclosed `0 = 0` on the finite-permutation model, so the substantive
content is the per-resolution `vonNeumannEntropy_corrMatrix_eq_ksEntropySeq`, together with the
explicit **subadditivity counterexample** `not_subadditive_cnt_entropySeq` showing why the CNT rate
must be defined as an infimum rather than a Fekete limit — and **both directions of Petz's equality
theorem** — recovery ⟹ DPI saturation (`petz_recovery_implies_equality`) and, fully general,
saturation ⟹ recovery (`petz_equality_recovery_general`), whose analytic heart is the
modular-cocycle intertwining `partialTrace_equality_imp_intertwinesIt`.

### Status and documented frontiers

The GitHub issue tracker is at **zero open issues** — every formalization target has been discharged
sorry-free. A handful of mathematical frontiers are *disclosed in place* rather than silently
elided, and they are recorded honestly in the module docstrings: the descriptive-set layer proves
the compact-section (Novikov) projection theorem but not the full Π¹₁-boundedness / general
Arsenin–Kunugui uniformization; the suspension time-1 entropy `h(ζ⁽ʳ⁾₁) = h_base / r` is proved for
rational roofs, the irrational case needing the deep half of Abramov's flow-entropy homogeneity;
and the flow-Livšic story establishes the periodic-integral obstruction but not a full converse
(flow coboundary from vanishing closed-orbit integrals). Each such boundary is stated as a
hypothesis or a scoped instance, never hidden.

## Trust story

- **Sorry-free**: warnings are promoted to errors in `lakefile.toml`, so any `sorry` fails
  `lake build` (and CI). `main` is sorry-free everywhere; in-progress/experimental material lives
  on the `frontier` branch and reaches `main` only through clean, sorry-free PRs.
- **Linter-enforced**: the whole `ErgodicTheory` library builds under Mathlib's
  `linter.mathlibStandardSet` with warnings-as-errors, so CI fails on any style-lint regression.
- **Axiom-audited**: `test/AxiomAudit.lean` guards 646 declarations with
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
  Continuous/         -- the continuous-flow MET + suspension flows (flow exponent, entropy descent,
                      --   time-1 ergodicity)
  Livsic/             -- Livšic cohomological rigidity (abstract iff, full-shift/two-sided/SFT/
                      --   cat-map/doubling instances, full measurable rigidity, flow obstruction)
  Singular/           -- everywhere-Borel projector of the singular forward filtration
  Entropy/            -- Kolmogorov–Sinai entropy theory: partitions, conditional entropy,
                      --   generator theorem, Abramov–Rokhlin, Margulis–Ruelle
  Krieger/            -- Krieger's finite generator theorem, SMB, Rokhlin towers, coding
  Multifractal/       -- Z_q, τ(q), Rényi dimensions D_q, local/Hausdorff dimension,
                      --   Bernoulli-suspension witness
  Smooth/             -- derivative cocycle, Rokhlin inequality, volume-case Pesin formula
  Examples/           -- Arnold cat map, doubling map, Pesin/Rokhlin-equality witnesses
  OperatorEntropy/    -- quantum information: relative entropy, Klein/Lieb, data processing,
                      --   CNT dynamical entropy, Petz recovery + equality
  MeasureTheory/      -- descriptive-set residuals (Lusin, Novikov first separation, Kunugui–Novikov,
                      --   the Novikov compact-section projection theorem, covering numbers)
test/
  AxiomAudit.lean     -- guarded #print-axioms regression (separate lib; not upstreamable source)
blueprint/            -- leanblueprint LaTeX source (web + PDF; \lean-linked to declarations)
home_page/            -- Jekyll landing page for the GitHub Pages site
lakefile.toml         -- package config (ErgodicTheory + AxiomAudit libraries)
lean-toolchain        -- pinned Lean version (leanprover/lean4:v4.30.0-rc2)
docs/                 -- Mathlib-conventions guide, references.bib, finished-library state map
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
under `blueprint/` — chapters covering the cocycle theory, the ergodic theorems, the Lyapunov
assembly, the MET and its corollaries, the two-sided and continuous versions, the entropy
theory, and the quantum entropy/Petz layer — whose nodes are `\lean`-linked to the formalized
declarations. The
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
