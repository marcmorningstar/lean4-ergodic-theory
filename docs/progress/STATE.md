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

**M4 = Kingman's subadditive ergodic theorem — REDUCED to the single combinatorial core.**
`tendsto_kingman`, `tendsto_kingman_ergodic`, AND the analytic core `ae_tendsto_cdiv` are now
all **proved `sorry`-free**, modulo ONE isolated private lemma `ae_ereal_limsup_le_liminf` in
`Oseledets/Ergodic/Kingman.lean`:

> `ae_ereal_limsup_le_liminf` — *for `μ`-a.e. `x`, `liminf (ecdiv g · x) = limsup (ecdiv g · x)`
> in `EReal`* (the load-bearing direction is `limsup ≤ liminf`; the reverse is unconditional).

This isolates the entire content of Kingman not reducible to generic measure theory or to the
Fatou integrability step: **the stopping-time / Riesz-leaders block partition** — the single
irreducible combinatorial nugget. The Fatou finiteness + integrability (step 2) and the
pointwise-squeeze combine (step 4) are now done and route-agnostic; `ae_tendsto_cdiv` consumes
the isolated lemma plus those proven pieces. **Open `sorry`s remain 4** (the Kingman gap moved
from `ae_tendsto_cdiv` down into `ae_ereal_limsup_le_liminf`; no net change in count). Build
green; `#print axioms tendsto_kingman` / `…_ergodic` = `[propext, sorryAx, Classical.choice,
Quot.sound]`. Independent checker: **PASS** (verified no circularity — the integrability lemma
`int_limsup_div_integrable_aux` proves `Integrable (limsup cdiv)` via a pure `ℝ≥0∞` Fatou
argument using only boundedness *above*, never routing through `ae_tendsto_cdiv`).

Everything else in `Kingman.lean` is `sorry`-free and derives from the core by soft
arguments: a.e. boundedness (`ae_bddBelow_cdiv`, convergent ⇒ bounded), `limsup ≤ liminf`
(`ae_limsup_le_liminf_div`), envelope integrability (`int_limsup_div_integrable`),
`T`-invariance (`limsup_div_comp_ae` via `ae_eq_comp_of_le_comp`), and the pointwise-squeeze
assembly (`tendsto_of_le_liminf_of_limsup_le`). The route mirrors the proven M3 Birkhoff
proof. Also: 6 lemmas in `Ergodic/Birkhoff.lean` were de-privatized for reuse
(`condExp_invariants_comp_self`, `ae_forall_orbit_eq`, `ae_bddAbove/ae_bddBelow_birkhoffAverage`,
`limsup_eq_of_sub_tendsto_zero`, `measure_setOf_lt_limsup_eq_zero`).

**Next: prove `ae_ereal_limsup_le_liminf` (THE last Kingman gap).** Steps 1, 2, 4 below are
DONE (sorry-free, verified). Only step 3 remains.
1. ✅ **Envelope (EReal):** `limsup (↑cdiv) ≤ ↑B < ⊤` a.e. (`ae_ereal_limsup_le_condExp`).
2. ✅ **Fatou (`ℝ≥0∞`):** `limsup (↑cdiv) > ⊥` a.e. (`ae_bot_lt_ereal_limsup`) **and**
   integrability of `limsup cdiv` (`int_limsup_div_integrable_aux`, pure `ℝ≥0∞` Fatou, no
   circularity, uses only boundedness above). Helpers: `fdefect`, `integral_fdefect`,
   `ae_liminf_ofReal_fdefect_lt_top`, `ae_liminf_fdefect_lt_top`.
3. ⏳ **Stopping time (EReal):** `limsup (↑cdiv) ≤ liminf (↑cdiv)` a.e. — THE hard core, the
   lone Kingman `sorry` (`ae_ereal_limsup_le_liminf`). **ROUTE: Derriennic / Riesz "leaders"**
   (`docs/research/scratch/m4-step3-derriennic-route.md`), NOT Avila–Bochi truncation.
   - ✅ **L-A** (`sum_leaders_nonpos`) — Riesz's leader lemma (Karlsson Lemma 3.2), pure finite
     strong induction, no measure theory. The genuinely novel combinatorial nucleus. PROVEN.
     Plus `leaderSet` def + `mem_leaderSet_shift` reindexing engine.
   - ✅ **L-B** (`sum_leaders_cocycle_nonpos`) — pointwise leader inequality for the cocycle
     (instantiate L-A at `S j = g n x − g(n−j)(T^[j]x)`). PROVEN.
   - ✅ **L-C** (`limsup_setIntegral_div_nonpos`) — Derriennic's maximal inequality (Karlsson
     Lemma 3.4): for measurable `T`-invariant `B` with `∀ᵐ x∈B, ∃k, g(k+1)x<0`, the EReal
     `limsup (∫_B g(n+1))/(n+1) ≤ 0`. PROVEN. Built on new infra: `bcoc` (increment `bᵢ`),
     `LambdaSet`/`ASet` (Karlsson's Λ/A), `psiCoc` (localized indicator increment),
     `mem_leaderSet_iff_mem_LambdaSet` (leader ⟺ `T^[k]x∈Λ_{n−k}`), `sum_bcoc_telescope`,
     `sum_setIntegral_psiCoc_nonpos` (★ telescoped integral ineq), `sum_setIntegral_bcoc_eq`,
     `setIntegral_comp_iterate_of_invariants`, `ASet_mono`/`nullMeasurableSet_ASet`. Imports
     added: `MeasureTheory.Integral.DominatedConvergence`, `Analysis.Asymptotics.SpecificAsymptotics`.
   - ✅ **L-D first half** — the target `ae_ereal_limsup_le_liminf` is now CLOSED, reduced to the
     non-positive case `ae_ereal_limsup_le_liminf_nonpos`. Reduction infra (all proven): the
     companion `vcoc g n := g n − birkhoffSum T (g 1) n` with `vcoc_subadditive`/`vcoc_nonpos`/
     `vcoc_integrable`/`vcoc_bddBelow`/`ecdiv_eq_ecdiv_vcoc_add` (gap-transfer via M3 finite limit),
     and the `T^[M]`-subsequence cocycle `vM g M n := g(nM) − ∑_{i<n} g M (T^[iM])` with
     `vM_subadditive` (subadditive for `T^[M]`), `vM_nonpos` (n≥1), `vM_integrable`,
     `vM_measurePreserving`.
   - ⏳ **L-D second half** — the lone remaining `sorry`, isolated in `ae_ereal_limsup_le_liminf_nonpos`
     (Kingman.lean ~1573). The `E_{α}` contradiction (Karlsson §3.3). Now PARTIALLY built:
     - ✅ **LD-a** `liminf_div_comp_ae` (+ `liminf_cdiv_le_comp`, `liminf_eq_of_sub_tendsto_zero`) —
       a.e. `T`-invariance of the ℝ-valued liminf envelope (mirrors `limsup_div_comp_ae`); now also
       wired into `tendsto_kingman`. NOTE: insufficient for `E_α` directly (for the non-positive
       cocycle `liminf cdiv` can be `⊥`, `BddBelow` fails) → still need an **EReal** invariance
       analogue of `ae_eq_comp_of_le_comp` (rational/±∞ level sets).
     - ✅ **LD-b** `setIntegral_div_le_level` (Karlsson Prop 3.5, β-version of L-C): for invariant
       `B`, real `β`, `∀ᵐ x∈B ∃k, a(k+1)x<(k+1)β` ⟹ `limsup (∫_B a(n+1))/(n+1) ≤ β·μ(B)`. Plus
       EReal helpers `erealAddCoeIso`, `ereal_limsup_add_coe`.
     - ⏳ **LD-c** subsequence squeeze `f_M=f̄`, `g_M=f` (non-positivity+subadditivity, ratios
       `(n+1)M/(nM+k)→1`) — the hardest analytic piece, unwritten.
     - ⏳ **LD-d** additive `T^[M]`-Birkhoff assembly (M3 on level `g M`), **LD-e** final
       contradiction (LD-b on `E`, β=−Mα; Fekete lower bound; `μ(E)≤ε/α→0`; union over `α=1/k`).
4. ✅ **Combine:** `⊥ < limsup ≤ liminf ≤ limsup ≤ B < ⊤` ⇒ finite common value ⇒ `Tendsto`
   to `G := toReal`, integrable — done inside `ae_tendsto_cdiv`.

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
| `ae_ereal_limsup_le_liminf` | Ergodic/Kingman | M4 (the lone core — stopping-time/Riesz-leaders; the only Kingman gap) |
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
