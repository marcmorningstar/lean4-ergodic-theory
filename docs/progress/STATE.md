# Oseledets MET formalization — living state

> Single source of truth for resuming this project. Fresh agent: read this file top
> to bottom, then `docs/research/understanding.md` (the math + the L0–L7 lemma
> ladder), `docs/research/target-and-milestones.md` (target + milestones M0–M13),
> `docs/plan/` (decision record + phased plan + api-notes), and for the active phase
> `docs/plan/blueprints/m4-kingman-v2.md` + `docs/research/scratch/m4-L9-notes.md`.
> Charter: `PROMPT.md`.

_Last updated: 2026-06-05 (autonomous run; user away → self-approving checkpoints,
recorded in `docs/plan/decision-record.md`)._

## Target (one line)

`sorry`-free Lean 4 + Mathlib formalization of the **one-sided Oseledets MET in
filtration form** (milestone **M10** / layer **L6.1**), stated in Lean as
`Oseledets.oseledets_filtration` in `Oseledets/MultiplicativeErgodic.lean`.

## Current phase

**M4 = Kingman's subadditive ergodic theorem — REDUCED to a single core lemma.**
`tendsto_kingman` and `tendsto_kingman_ergodic` are now **proved `sorry`-free**, modulo
ONE isolated private core lemma `ae_tendsto_cdiv` in `Oseledets/Ergodic/Kingman.lean`:

> `ae_tendsto_cdiv` — *for `μ`-a.e. `x`, the normalized cocycle `cdiv g n x = g (n+1) x /
> (n+1)` converges to the value `G x` of some integrable `G`.*

This packages the entire analytic content of Kingman not reducible to generic measure
theory (the stopping-time / greedy block partition + the Fatou integrability step).
**Open `sorry`s 5 → 4** (the two Kingman milestone `sorry`s are discharged; one new core
`sorry` introduced). Build green; `#print axioms tendsto_kingman` / `…_ergodic` =
`[propext, sorryAx, Classical.choice, Quot.sound]`. Independent checker: **PASS**.

Everything else in `Kingman.lean` is `sorry`-free and derives from the core by soft
arguments: a.e. boundedness (`ae_bddBelow_cdiv`, convergent ⇒ bounded), `limsup ≤ liminf`
(`ae_limsup_le_liminf_div`), envelope integrability (`int_limsup_div_integrable`),
`T`-invariance (`limsup_div_comp_ae` via `ae_eq_comp_of_le_comp`), and the pointwise-squeeze
assembly (`tendsto_of_le_liminf_of_limsup_le`). The route mirrors the proven M3 Birkhoff
proof. Also: 6 lemmas in `Ergodic/Birkhoff.lean` were de-privatized for reuse
(`condExp_invariants_comp_self`, `ae_forall_orbit_eq`, `ae_bddAbove/ae_bddBelow_birkhoffAverage`,
`limsup_eq_of_sub_tendsto_zero`, `measure_setOf_lt_limsup_eq_zero`).

**Next: prove `ae_tendsto_cdiv` (the core).** Plan (`docs/plan/blueprints/m4-kingman-v2.md`
§4, refined in `docs/research/scratch/m4-L9-notes.md`), do the `limsup`/`liminf` in **EReal**
to avoid the ℝ junk value at `−∞`:
1. **Envelope (EReal):** `limsup (↑cdiv) ≤ ↑B < ⊤` a.e., `B = μ[g 1 | invariants T]` — from
   A1' (`cdiv ≤ birkhoffAverage g₁`) + M3 (`birkhoffAverage g₁ → B`).
2. **Fatou (`ℝ≥0∞`):** `limsup (↑cdiv) > ⊥` a.e. **and** integrability — `lintegral_liminf_le`
   on `ofReal (birkhoffAverage g₁ − cdiv) ≥ 0`; the `ℝ≥0∞` liminf genuinely sees `+∞`,
   excluding the `→ −∞` set without needing boundedness-below. Uses the Fekete `γ`
   (`exists_fekete`, retained as scaffolding).
3. **Stopping time (EReal):** `limsup (↑cdiv) ≤ liminf (↑cdiv)` a.e. — THE hard core. Induced
   stopping sequence `Sⱼ` (recursion), block subadditivity `le_sum_blocks` (retained
   scaffolding), truncation `max (liminf) (−M)`, three limit passages `n→∞` (Birkhoff on
   `1_{B_L}`), `L→∞` (`μ(B_L)→0`), `M→∞, ε→0`. See m4-L9-notes.md §A for the induced-sequence
   encoding (single remainder, no overrun singletons) and §B for the −∞/EReal subtlety.
4. **Combine:** `⊥ < limsup ≤ liminf ≤ limsup ≤ B < ⊤` ⇒ finite common value ⇒ `Tendsto` to
   `G := toReal`, integrable.

Then M5 (Furstenberg–Kesten, `Cocycle/FurstenbergKesten.lean`, blueprint
`m5-furstenberg-kesten.md`), the Lyapunov layers (`lyapunov-to-target.md`), and assembly
into the target `oseledets_filtration`.

## What is done

- ✅ **Green build from source** (cache host DNS-blocked — never run `lake exe cache get`;
  just `lake build`, incremental, ~3 min whole-library). Per-file builds slow (~150s).
- ✅ Research dossier + Mathlib survey + self-approved target/route/plan (`d3922ae`).
- ✅ **Phase 0 skeleton** + **P1 cocycle infra** + **P2 condExp∘MP (M2)** + **P3 maximal
  ergodic inequality (M1)** + **M3 pointwise Birkhoff** — all committed, `sorry`-free.
- ✅ **M4 research & design** → verified blueprint `docs/plan/blueprints/m4-kingman-v2.md`
  (pointwise-squeeze route; risk concentrated in the stopping-time core). Sources scraped to
  `docs/research/sources/kingman-*.md`.
- ✅ **M4 foundation** (commit `18f9069`, WIP checkpoint): assembled L0–L11 of the Kingman
  ladder; `tendsto_kingman` / `tendsto_kingman_ergodic` fully assembled via the pointwise
  squeeze.
- ✅ **M4 reduction** (this phase): the three entangled stubs collapsed into the single core
  `ae_tendsto_cdiv`, from which all soft facts derive; 5 → 4 open `sorry`s; QA PASS.

## Open `sorry`s (4 — all intended planned gaps)

| Decl | File | Milestone |
|---|---|---|
| `ae_tendsto_cdiv` | Ergodic/Kingman | M4 (the core — stopping-time + Fatou; the only Kingman gap) |
| `furstenbergKesten_top` | Cocycle/FurstenbergKesten | M5 |
| `furstenbergKesten_bot` | Cocycle/FurstenbergKesten | M5 |
| `oseledets_filtration` | MultiplicativeErgodic | M10 (TARGET) |

Not yet in the skeleton (deferred to their phases): the Lyapunov layers L4.x/L5.x and the
measurability of exponents/filtration (M7). Added when their phase begins.

## What is next (in order)

1. ✅ P0–P3, M2, M1, M3 (committed).
2. ✅ M4 research/design → v2 blueprint; M4 foundation (`18f9069`); M4 reduction (this commit).
3. ⏳ **Prove `ae_tendsto_cdiv`** (the Kingman core) → closes M4 fully (4 → 3). EReal route above.
4. ⏳ M5 Furstenberg–Kesten (`m5-furstenberg-kesten.md`); then Lyapunov layers
   (`lyapunov-to-target.md`); then assemble `oseledets_filtration`.

## Conventions (pinned — see decision-record.md / api-notes.md)

Cocycle newest-factor-left; scoped L2 operator norm `Matrix.Norms.L2Operator`; vectors
`EuclideanSpace ℝ (Fin d)` acted on via `Matrix.toEuclideanCLM`; GL encoded as
`det ≠ 0`; `log⁺ = Real.posLog`; Kingman stated in `ℝ` under the `BddBelow` proviso
(`EReal` used only internally in the core proof); subspace measurability via
`orthProjMatrix`/`MeasurableSubspace`.

## Resumption notes

- Branch `met-formalization`; baseline `2bead01`; research/plan `d3922ae`; M4 foundation
  checkpoint `18f9069`.
- Build is incremental: `lake build`. Never `lake exe cache get` (DNS-blocked, stalls).
- A single whole-library `lake build` shares the environment and is the efficient inner loop.
- One commit per QA-passed phase, Mathlib-style message + `Co-Authored-By` line.
- **Parallel worktree agents are infeasible here**: git worktrees don't carry the gitignored
  `.lake` Mathlib build cache (and `cache get` is blocked), so a fresh worktree would rebuild
  all of Mathlib. Hard proofs must be done by a single agent in the main repo.
