# Complete QA of the repository and the proof — 2026-06-10

Full-project quality assurance pass over the completed formalization, performed at
commit `b117b10` on branch `met-formalization`. Method: fresh ground-truth build +
independent axiom audit, then two multi-agent review rounds — (1) five parallel
read-only auditors (definition fidelity, literature comparison, proof-integrity
sweep, repo hygiene, STATE.md accuracy), (2) adversarial verification (an
end-to-end Lean semantic witness plus two independent refuters attacking the
phase-1 "faithful MET" verdict along logical and analytic lenses, all probes
compiled against the built library).

## Verdict

**The proof is sound and the theorem is the real MET.** No mathematical,
logical, or soundness finding at any severity. All remaining findings are
repository hygiene: stale documentation predating completion, untracked scratch
debris, and CI coverage gaps.

## Evidence for the headline verdict

1. **Build**: `lake build` green, 2933 jobs, zero errors. Only warnings: three
   `push_neg` deprecation warnings in `Oseledets/Lyapunov/TopGapEnvelope.lean`
   (lines 838, 849, 1068).
2. **Axiom audit (fresh, independent of build-log replay)**: a standalone file
   importing the built library printed, for `oseledets_filtration`,
   `oseledets_filtration_dim_zero`, `oseledets_filtration_of_topgap`, and
   `topGapMassEnvelope_ae`:
   `depends on axioms: [propext, Classical.choice, Quot.sound]` — exactly the
   standard Mathlib set; in particular no `sorryAx`, no `Lean.ofReduceBool`.
3. **Integrity sweep** (all 50 tracked library files): zero code-level
   occurrences of `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/
   `@[extern]`/`unsafe`/`opaque`/`partial def` (every textual hit is in a
   docstring/comment). No `macro`/`elab`/`notation` declarations — no syntax
   shadowing. No in-repo `Norm`/`Inner`/`NormedRing` instances — the L2 operator
   norm is the genuine Mathlib `Matrix.Norms.L2Operator` scoped instance. No
   proved-`False` lemma. `set_option`s limited to linter suppression and
   `maxHeartbeats`. Import closure exact: `Oseledets.lean` imports all 49
   modules directly; no orphans, no dangling imports. Toolchain pinned
   (`v4.30.0-rc2`); mathlib rev consistent between `lakefile.toml` and
   `lake-manifest.json`.
4. **Definition fidelity** (all pass): `cocycle` is the left-ordered product
   `A(T^{n-1}x)⋯A(x)` with proved cocycle identity; `IntegrableLogNorm` is
   `Integrable (Real.posLog ‖·‖)` (textbook `log⁺`, L2 operator norm);
   `hint'` applies it to the Mathlib `nonsing_inv`, the true inverse under the
   pointwise `det ≠ 0` hypothesis; `MeasurableSubspace` is measurability of the
   orthogonal-projection matrix (`starProjection` through `toEuclideanCLM.symm`)
   — a genuine, subspace-determining encoding.
5. **Literature comparison**: hypotheses are exactly the standard one-sided MET
   set (ergodic m.p.t. on a probability space, measurable GL(d,ℝ)-cocycle,
   `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹` — both sides correctly required for finite real
   exponents). Conclusion delivers all five hallmarks of the filtration form:
   strictly decreasing exponents, measurable subspace family, a.e. strict flag
   `⊤ = V₀ ⊋ ⋯ ⊋ V_k = ⊥`, exact `A`-equivariance, exact per-vector growth
   `(1/n)log‖Aⁿ(x)v‖ → λᵢ` on each shell. Quantifier structure is the correct
   strength: `k`, `lam`, `V` deterministic (outside the a.e.), `v` inside a
   single a.e. quantifier (strong form).
6. **End-to-end semantic witness** (`qa-witness.lean` in this directory,
   compiles sorry-free against the library, axioms again exactly
   `[propext, Classical.choice, Quot.sound]`):
   - `qa_nonvacuity` — instantiates every hypothesis concretely
     (`X = Unit`, `μ = dirac ()`, `T = id`, `d = 1`, `A = 2 • 1`) and applies
     the theorem: the hypothesis set is satisfiable, the theorem is not vacuous.
   - `qa_semantic_pin` — extracts from the conclusion that `k = 1` **and**
     `lam 0 = Real.log 2`, the true Lyapunov exponent of the system. The formal
     statement *forces* the genuine exponent; no degenerate reading of the
     conclusion survives.
7. **Adversarial refutation, logical lens** (verdict: confirmed-sound): compiled
   probes show strata cannot merge distinct rates (`tendsto_nhds_unique`), every
   `lam i` is realized on a nonempty shell (strict drops), `k` cannot be
   inflated (`lam` injects into realized rates), `k = 0` forces `d = 0`,
   equivariance is full (injectivity from `det ≠ 0`), the `n = 0` term is
   harmless, and the statement uses the full `Tendsto` limit (not limsup).
8. **Adversarial refutation, analytic lens** (verdict: confirmed-sound; 7
   compiled probes): the matrix norm is the spectral/operator norm — separator
   `‖diagonal ![2,3]‖ = 3` (Frobenius would be `√13`); the vector norm is
   genuinely L2/`PiLp 2` with no coercion trap; the action is standard `mulVec`
   with newest-on-left composition consistent between the equivariance and
   growth conjuncts (single-step equivariance iterates correctly to
   `cocycle 2`); `log`/`posLog` never hit a degenerate argument in the growth
   range (`v ≠ 0` forced by `v ∉ V i.succ x`, cocycle invertible); the
   entrywise Pi σ-algebra on matrices is definitionally Borel for the normed
   topology, so `Measurable A` is the standard hypothesis.

## Findings (all non-mathematical)

### Major — stale entry-point documentation contradicting completion

| # | File | Problem |
|---|------|---------|
| F1 | `README.md:6-8` | Says "Status: **skeleton** … empty shell with no mathematical content yet"; layout block (lines 14-15) lists only the deleted `Oseledets/Basic.lean`. |
| F2 | `Oseledets.lean:71-72` | Root docstring: "The development is currently a `sorry`-stubbed skeleton"; layout list (62-69) names only 8 of 49 modules. |
| F3 | `Oseledets/MultiplicativeErgodic.lean:11-13` | Module docstring says the theorem "is stated here with the proof left as `sorry`" — in the file where it is fully proved. |
| F4 | `docs/progress/STATE.md:3-8` | Orientation header still directs fresh agents to "the active phase `docs/plan/blueprints/m4-kingman-v2.md`…" — there is no active phase; contradicts the COMPLETE banner 6 lines below. |

### Minor

| # | File | Problem |
|---|------|---------|
| F5 | `CLAUDE.md:20` | Layout row: "`Oseledets/` … Currently only `Basic.lean` (placeholder)" — file deleted, 49 modules exist. Rest of CLAUDE.md verified accurate. |
| F6 | repo root | 82 untracked `scratch_*.lean` (~1.8 MB); `.gitignore` has no pattern for them. Their conclusions are durably recorded in STATE.md / blueprints. |
| F7 | `.github/workflows/` | `push.yml` triggers only on `main`; `push_pr.yml` only on PRs to `main` — the branch (97 commits ahead) has had zero CI runs. `push_pr.yml` `timeout-minutes: 60` (vs 120 on main) is tight for the heavy proof files (`OseledetsLimit.lean` 227 KB, `Kingman.lean` 192 KB). Otherwise sound (lean-action fetches the Mathlib cache). |
| F8 | `docs/progress/STATE.md:407,415` | Still-live guidance (pinned Conventions, Resumption notes) is stranded *below* the "Historical state" marker; the "Never `lake exe cache get` (DNS-blocked)" note contradicts CLAUDE.md/README, which advise running it. |
| F9 | `docs/progress/STATE.md:28` | The one-line historical marker is easy to miss: later headings read present-tense ("Current phase", "Open `sorry`s (4…)", "What is next") and would mislead heading/grep navigation. |
| F10 | `Oseledets/Lyapunov/TopGapEnvelope.lean:838,849,1068` | Three deprecated `push_neg` uses (warning: prefer `push Not`). |

### Optional enhancements (info)

- Surface the a.e.-constant stratum dimensions/multiplicities as an explicit
  corollary (`∃ m : Fin k → ℕ, ∀ᵐ x, ∀ i, finrank (V i x) = m i`); implied by
  the statement but a referee must reconstruct it.
- Add the standard companion corollaries: `λ₁ = lim (1/n) log‖Aⁿ(x)‖` and the
  canonical characterization `Vᵢ(x) = {v : limsup ≤ λᵢ}` (uniqueness of the
  filtration). The internal `lambdaSublevel` machinery already proves the
  latter, so it should be cheap to extract.
- Promote `qa-witness.lean` into the library (e.g. `Oseledets/QA/Witness.lean`,
  imported from the root) so the semantic pin becomes a standing CI regression.

## Recommended actions

1. Refresh F1–F5 (five doc edits; exact replacement text in the finding
   details above — essentially: state COMPLETE + axiom set, fix layout lists).
2. Delete `scratch_*.lean` and add `/scratch_*.lean` to `.gitignore` (F6).
3. Open the PR to `main` promptly (gives the branch its first CI run); raise
   `push_pr.yml` timeout to 120 (F7).
4. Restructure STATE.md: move live guidance above the historical marker,
   reconcile the `cache get` advice with CLAUDE.md, and retitle historical
   sections "(historical)" (F8, F9).
5. Replace the three `push_neg` uses with `push Not` (F10).

— QA run: 2 workflows, 8 agents, ~540k subagent tokens; all Lean probes and the
witness compiled against the library built at `b117b10`.

## Resolution (same day, 2026-06-10)

All findings F1–F10 were fixed in the working tree:

- **F1–F5**: README status + layout, `Oseledets.lean` root docstring + layout,
  `MultiplicativeErgodic.lean` header, STATE.md orientation header, CLAUDE.md
  layout row — all now state the completed status accurately.
- **F6**: all 82 `scratch_*.lean` deleted; `/scratch_*.lean` added to `.gitignore`.
- **F7**: `push.yml` now also triggers on pushes to `met-formalization`;
  `push_pr.yml` `timeout-minutes` raised 60 → 120.
- **F8/F9**: STATE.md restructured — pinned Conventions + Resumption notes moved
  above a prominent `# HISTORICAL RECORD` heading; misleading historical headings
  retitled. The `lake exe cache get` contradiction was reconciled by *testing it*:
  it stalls in this devcontainer (DNS-blocked, killed at 45 s), so STATE.md's
  warning was correct and CLAUDE.md now carries an explicit do-not-run caveat.
- **F10**: the three `push_neg` uses replaced with `push Not`.

Post-fix verification: full `lake build` green (2933 jobs), **zero warnings**,
`TopGapEnvelope` re-elaborated with the `push Not` change, and the axiom audit
unchanged — `oseledets_filtration` depends on exactly
`[propext, Classical.choice, Quot.sound]`.

Remaining (deliberately not done, optional enhancements only): the explicit
multiplicity/uniqueness/`λ₁ = lim (1/n)log‖Aⁿ‖` corollaries and the promotion of
`qa-witness.lean` into the library as a CI regression.
