# Oseledets MET formalization — living state

> Single source of truth for resuming this project. Fresh agent: read this file top
> to bottom, then `docs/research/understanding.md` (the math + the L0–L7 lemma
> ladder), `docs/research/target-and-milestones.md` (target + milestones M0–M13),
> and `docs/plan/` (decision record + phased plan + api-notes). Charter: `PROMPT.md`.

_Last updated: 2026-06-05 (autonomous run; user away → self-approving checkpoints,
recorded in `docs/plan/decision-record.md`)._

## Target (one line)

`sorry`-free Lean 4 + Mathlib formalization of the **one-sided Oseledets MET in
filtration form** (milestone **M10** / layer **L6.1**), stated in Lean as
`Oseledets.oseledets_filtration` in `Oseledets/MultiplicativeErgodic.lean`.

## Current phase

**Phase 3 = M1 (maximal ergodic inequality) — COMPLETE (the keystone).**
`setIntegral_birkhoffSum_pos_nonneg` proved sorry-free via Garsia's argument (~14
auxiliary lemmas: `maxBirkhoff` + nonneg/succ/measurable/integrable, the constant-pull
`add_sup'_eq`, the pointwise Garsia inequality `maxBirkhoff_le_add`, `birkhoffSum_congr_ae`,
the fixed-N crux `setIntegral_maxBirkhoff_pos_nonneg`, monotone/iUnion of the positivity
sets, and the `f→g` measurable-representative reduction). Build green; main statement
byte-identical to the QA'd skeleton; axioms `[propext, Classical.choice, Quot.sound]`;
open `sorry`s 8 → 7. (Phases 0–2 before: skeleton QA-passed; cocycle infra; condExp∘MP.)
**Next: M3 (Birkhoff) and M4 (Kingman) are now both UNLOCKED by M1.**

## What is done

- ✅ **Green build from source** (cache host DNS-blocked, as documented — never run
  `lake exe cache get`; just `lake build`, incremental). Full Mathlib closure for our
  imports is compiled and cached.
- ✅ Research dossier + Mathlib survey + self-approved target/route/plan (committed in
  `d3922ae` on branch `met-formalization`).
- ✅ **Phase 0 skeleton written and compiling green.** 7 modules under `Oseledets/`:
  - `Cocycle/Basic.lean` — `cocycle` def (newest factor left) + `cocycle_zero/_succ/_one`,
    **`cocycle_add` (identity) and `measurable_cocycle` PROVED (Phase 1)**,
    `IntegrableLogNorm` predicate; the project-wide `instMeasurableSpaceMatrix`
    (Pi/Borel measurable structure on matrices) and `instMeasurableMul₂Matrix`
    (matrix multiplication measurable — added in Phase 1), neither in Mathlib.
  - `Cocycle/FurstenbergKesten.lean` — `furstenbergKesten_top`, `_bot` (`sorry`, M5).
  - `Ergodic/MaximalErgodic.lean` — `setIntegral_birkhoffSum_pos_nonneg` (`sorry`, M1).
  - `Ergodic/Birkhoff.lean` — `condExp_invariants_comp` (M2), `tendsto_birkhoffAverage_ae`
    (M3), `tendsto_birkhoffAverage_ae_integral` (ergodic) — all `sorry`.
  - `Ergodic/Kingman.lean` — `IsSubadditiveCocycle` predicate, `tendsto_kingman`,
    `tendsto_kingman_ergodic` (`sorry`, M4).
  - `Lyapunov/MeasurableSubspace.lean` — `orthProjMatrix`, `MeasurableSubspace` (M7 infra).
  - `MultiplicativeErgodic.lean` — `oseledets_filtration` (the TARGET, `sorry`, M10).
- ✅ Gate checks: `lake build` exit 0 (only `sorry` warnings); **no custom `axiom`
  declarations**; `#print axioms oseledets_filtration` = `[propext, sorryAx,
  Classical.choice, Quot.sound]` (only standard axioms + the intended `sorryAx` gaps).

## Open `sorry`s (7 — all intended planned gaps; the implementation backlog)

_Closed so far: `cocycle_add`, `measurable_cocycle` (P1); `condExp_invariants_comp` (P2,
M2); `setIntegral_birkhoffSum_pos_nonneg` (P3, M1). `Cocycle/Basic` and
`Ergodic/MaximalErgodic` are sorry-free._

| Decl | File | Milestone |
|---|---|---|
| `tendsto_birkhoffAverage_ae` | Ergodic/Birkhoff | M3 (now unlocked: M1+M2 ready) |
| `tendsto_birkhoffAverage_ae_integral` | Ergodic/Birkhoff | M3 (ergodic) |
| `tendsto_kingman` | Ergodic/Kingman | M4 |
| `tendsto_kingman_ergodic` | Ergodic/Kingman | M4 (ergodic) |
| `furstenbergKesten_top` | Cocycle/FurstenbergKesten | M5 |
| `furstenbergKesten_bot` | Cocycle/FurstenbergKesten | M5 |
| `oseledets_filtration` | MultiplicativeErgodic | M10 (TARGET) |

Not yet in the skeleton (deferred to their implementation phases): the Lyapunov layer
L4.x (growth function `λ̄`, ultrametric algebra, the limsup flag), L5.x (limsup→lim
induction), and measurability of the exponents/filtration (M7 proper). The target is
stated and `sorry`; these intermediate lemmas are added when their phase begins.

## What is next (in order)

1. ✅ Phase 0 (skeleton) committed `4ed4225`; blueprints `5b64baa`.
2. ✅ Phase 1 (cocycle infra) — `cocycle_add`, `measurable_cocycle` proved (`c23b73e`).
3. ✅ Phase 2 (M2) — `condExp_invariants_comp` proved (`4e5feec`).
4. ✅ Phase 3 (M1, keystone) — `setIntegral_birkhoffSum_pos_nonneg` proved.
5. ⏳ **M3 (pointwise Birkhoff)** — now unlocked (= M1 + M2). Use the maximal
   inequality `setIntegral_birkhoffSum_pos_nonneg` + `condExp_invariants_comp`;
   blueprint `m3-birkhoff.md`. Prove `tendsto_birkhoffAverage_ae` + the ergodic
   corollary.
6. ⏳ **M4 (Kingman)** — also unlocked via Katznelson–Weiss (from M1); blueprint
   `m4-kingman.md`. Then M5 (Furstenberg–Kesten), the Lyapunov layers, and assembly.

**Proof blueprints** for the three hard theorems (M1/M3/M4) are in
`docs/plan/blueprints/` — exact Mathlib lemma maps + auxiliary lemmas + pitfalls.

**Routing insight (from the blueprints) — M1 is the keystone.** The maximal ergodic
inequality (M1) unlocks BOTH:
- M3 (pointwise Birkhoff) = M1 + M2, and
- M4 (Kingman) via the **Katznelson–Weiss** route (M1 + truncation/stopping argument),
  which the `m4-kingman.md` blueprint recommends over Steele (Steele needs M3 first and
  a bespoke greedy-partition lemma with no Mathlib support).
So after M2, **prove M1 next** — it is the single highest-leverage unlock. Prove the
Kingman private lemmas under `[IsFiniteMeasure μ]` (the MET only uses probability
measures); fix the EReal/−∞ convention before M4 (`m4-kingman.md §1`).

## Conventions (pinned — see decision-record.md / api-notes.md)

Cocycle newest-factor-left; scoped L2 operator norm `Matrix.Norms.L2Operator`; vectors
`EuclideanSpace ℝ (Fin d)` acted on via `Matrix.toEuclideanCLM`; GL encoded as
`det ≠ 0`; `log⁺ = Real.posLog`; Kingman to be generalized to `EReal` later;
subspace measurability via `orthProjMatrix`/`MeasurableSubspace`.

## Resumption notes

- Branch `met-formalization`; baseline `2bead01`; research/plan commit `d3922ae`.
- Build is incremental: `lake build`. Never `lake exe cache get` (DNS-blocked, stalls).
- Per-file builds are slow (~150s, heavy import-closure load); a single whole-library
  `lake build` shares the environment and is the efficient inner loop.
- One commit per QA-passed phase, Mathlib-style message + `Co-Authored-By` line.
