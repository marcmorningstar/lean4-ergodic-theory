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

**M4 = Kingman's subadditive ergodic theorem — ✅ COMPLETE, fully `sorry`-free.**
`tendsto_kingman` and `tendsto_kingman_ergodic` are proved with `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (**no `sorryAx`**). `Oseledets/Ergodic/Kingman.lean`
(~2740 lines) has zero `sorry`. Independent checker: **PASS** (no circularity, vacuity, or
cheating; public signatures unchanged; only `Kingman.lean` modified). The whole proof follows
the scraped **Karlsson "leaders" proof** (`docs/research/sources/kingman-karlsson-maximal-proof.md`),
not a reinvention.

The structure (top-level): the a.e. convergence is a pointwise squeeze mirroring the proven M3
Birkhoff proof, reduced to the analytic core `ae_tendsto_cdiv` (a.e. convergence of
`cdiv g n x = g(n+1)x/(n+1)` to an integrable limit), itself reduced to the EReal stopping-time
lemma `ae_ereal_limsup_le_liminf` (`liminf (ecdiv g ·x) = limsup (ecdiv g ·x)` a.e.). Two
analytic engines feed it: a `ℝ≥0∞` Fatou step (integrability + `limsup > ⊥`, using only
boundedness above — no circularity) and the Karlsson route, proved in full:

- **L-A** `sum_leaders_nonpos` — Riesz's leader lemma (Karlsson Lemma 3.2), pure finite strong
  induction (the combinatorial nucleus); `leaderSet`/`mem_leaderSet_shift`.
- **L-B** `sum_leaders_cocycle_nonpos` — pointwise leader inequality for the cocycle.
- **L-C** `limsup_setIntegral_div_nonpos` — Derriennic's maximal inequality (Lemma 3.4); built
  on `bcoc`/`LambdaSet`/`ASet`/`psiCoc`, `mem_leaderSet_iff_mem_LambdaSet`, the telescoped
  integral inequality, and a dominated-convergence Cesàro tail.
- **Prop 3.5** `setIntegral_div_le_level` — the β-level form of L-C.
- **Reduction** to the non-positive companion `vcoc g n := g n − birkhoffSum T (g 1) n`
  (`vcoc_*`, gap-transfer `ecdiv_eq_ecdiv_vcoc_add` via M3), and the `T^[M]`-subsequence cocycle
  `vM g M n := g(nM) − ∑_{i<n} g M(T^[iM])` (`vM_subadditive`/`vM_nonpos`/`vM_integrable`).
- **EReal envelope `T`-invariance** `ereal_ae_eq_comp_of_le_comp` →
  `liminf_ecdiv_comp_ae`/`limsup_ecdiv_comp_ae` (the ℝ version fails: non-positive `liminf` may
  be `⊥`).
- **LD-c squeeze** `limsup_ecdiv_eq_block`/`liminf_ecdiv_eq_block` — full envelope = `M`-block
  subsequence envelope, from `block_sandwich` + the EReal ratio squeezes.
- **LD-d/LD-e** `block_decomp`/`usub_vM`/`limsup_block_eq`/`liminf_block_eq` +
  `measure_gap_set_eq_zero` — the additive `T^[M]`-Birkhoff assembly and the `E_α` contradiction
  (Karlsson §3.3) closing the core.

Also: 6 lemmas in `Ergodic/Birkhoff.lean` were de-privatized for reuse
(`condExp_invariants_comp_self`, `ae_forall_orbit_eq`, `ae_bddAbove/ae_bddBelow_birkhoffAverage`,
`limsup_eq_of_sub_tendsto_zero`, `measure_setOf_lt_limsup_eq_zero`).

**M5 = Furstenberg–Kesten — ✅ COMPLETE, fully `sorry`-free.** `furstenbergKesten_top` and
`furstenbergKesten_bot` are proved (`#print axioms` = `[propext, Classical.choice, Quot.sound]`),
applying `tendsto_kingman_ergodic` to `log‖A⁽ⁿ⁾‖` / `log‖(A⁽ⁿ⁾)⁻¹‖`. New file
`Oseledets/Cocycle/Norm.lean` (the L2-opNorm/inverse measurability bridge — the topology is
`rfl`-equal to the Pi product topology, no instance diamond; checker-verified). `_top`'s
signature was strengthened (R4) with `hA : det ≠ 0` and `hint' : IntegrableLogNorm A⁻¹` to keep
the ℝ-valued limit (needed for Kingman's `hbdd`); `_bot` unchanged. Independent checker: **PASS**.

**Now in progress: the Lyapunov layers → the target `oseledets_filtration` (M6–M10).** See
`docs/plan/blueprints/lyapunov-to-target.md` (6-module arc, build order in §8) +
`target-and-milestones.md`. The only open `sorry` left. Two flagged risks: the M7
measurable-selection gap (Mathlib coverage partial; §4.3 fixed-threshold mitigation) and the
L5.3 tempered block-triangular estimate (§7).

Module progress (build order `Ultrametric → GrowthFunction → Filtration → Measurable →
Subbundle → Limit`):
- ✅ **`Lyapunov/Ultrametric.lean`** (L4.3, pure linear algebra) — `IsUltrametricGrowth`
  (scaling + non-Archimedean), `add_eq_max_of_ne`, `sum_ne_zero_and_g_eq_sup'` (engine),
  `linearIndependent_of_injOn`, `finite_range` (spectrum ≤ `finrank`), `sublevel` (submodule)
  + `sublevel_mono`. Sorry-free, axioms clean. Imported from `Oseledets.lean`.
- ✅ **`Lyapunov/GrowthFunction.lean`** (L4.1–4.2) — `lambdaBar A T x v = limsup (n⁻¹·log‖A⁽ⁿ⁾(x)v‖)`,
  with `lambdaBar_smul` (scaling, unconditional), `lambdaBar_equivariant` (`A`-equivariance, with
  two a.e.-discharged `IsBoundedUnder` hyps from the `(n+1)⁻¹` reindex), `lambdaBar_mem_Icc` (FK
  sandwich → a.e. finite in `[lamBot, lamTop]`), `lambdaBar_add_le` (non-Archimedean), and the
  bundle `isUltrametricGrowth_lambdaBar` (a.e., `d=0` degenerate case handled; boundedness
  discharged via `growthSeq_bounded`). Sorry-free, axioms clean. Imported from `Oseledets.lean`.
- ✅ **`Lyapunov/Filtration.lean`** (L4.4, the limsup flag) — `spectrum`/`specCard`/`specList`
  (descending via `orderEmbOfFin ∘ Fin.rev`), `Vflag` (total, junk-off-null-set via `dite` on
  `IsUltrametricGrowth`), `Vflag_zero` (=⊤ via spectrum max), `Vflag_last` (=⊥), `Vflag_strictAnti`
  (strict, witnessed), `lambdaBar_eq_on_stratum` (exactness), and the a.e. equivariance pair
  `spectrum_equivariant_ae` + `Vflag_equivariant` (stated on `lambdaSublevel` at a FIXED threshold
  `t`, deliberately sidestepping `Fin k`/`Fin(k+1)` index transport — the consumer rewrites with
  `spectrum_equivariant_ae` first). Structural theorems carry a per-point `hx : IsUltrametricGrowth
  (lambdaBar A T x)`; equivariance carries the full FK hypothesis set. Needed one public bridge
  lemma `lambdaBar_equivariant_ae` added to `GrowthFunction.lean` (a.e. ∀v equivariance, boundedness
  pulled back along `T` measure-preserving). Sorry-free, axioms clean. Imported from `Oseledets.lean`.
- 🔄 **`Measurable.lean`** (M7) — **measurability route RESOLVED & re-architected** (Lean-verified;
  see `docs/plan/blueprints/m7-measurable-strategy-v2.md`). The abstract-flag route hit a genuine
  Mathlib gap (no Kuratowski–Ryll-Nardzewski / Castaing measurable selection; a fixed countable
  family cannot span an arbitrary subspace — the "dense family" idea is FALSE). **User directive:
  build missing Mathlib infra properly, no shortcuts, will upstream** ([[measurability-build-infra]]).
  Resolution: route measurability through the **concrete CFC spectral projections** of the Oseledets
  limit `Λ x = lim ((A⁽ⁿ⁾)ᵀA⁽ⁿ⁾)^{1/2n}`. Define `Vᵢ x := range (toEuclideanCLM (cfc gᵢ (Λ x)))`
  (gap fn `gᵢ`); then `orthProjMatrix (Vᵢ x) = cfc gᵢ (Λ x)` definitionally, and that is measurable
  via the **polynomial bypass** (`cfc gᵢ (Λ x) = aeval (Λ x) q`, fixed Lagrange interpolant on the
  a.e.-constant spectrum) — full Borel, NO selection/analytic-sets. The CFC-continuity route is
  blocked by a non-synthesizing `IsometricContinuousFunctionalCalculus ℝ (Matrix..ℝ)` instance, so
  the polynomial bypass is essential (verified by compilation). **Banked sorry-free so far:**
  `measurable_lambdaBar_apply`, `orthProjMatrix_apply`, `measurable_orthProjMatrix_iff` (reduction),
  `instMeasurableAdd₂Matrix`, `measurable_matrix_pow`, `measurable_aeval_matrix`, and the crux
  `measurable_cfc_eqOn_polynomial`. The eliminable BLOCKED `measurable_starProjection_apply` was
  REMOVED (abstract route abandoned). Terminal `MeasurableSubspace Vᵢ` is gated on `Λ` (Limit module).
- ⏳ **`ExteriorNorm.lean`** then **`OseledetsLimit.lean`** (Route II — see
  `docs/plan/blueprints/limit-endgame.md`, make-or-break spike compiled in `scratch_limit_spike.lean`).
  **ENDGAME ROUTE DECIDED: Route II (the SVD/Gram limit `Λ x = lim ((A⁽ⁿ⁾)ᵀA⁽ⁿ⁾)^{1/2n}`).** Since the
  measurability pivot already forces `Λ` into existence, `Λ` supplies EVERY target conjunct as genuine
  limits (exponents = log eigenvalues, flag = eigenspace sums, exact growth = SVD read-off,
  measurability = the committed CFC crux). The limsup §5–6 tempering/block-triangular machinery is
  **demoted to the Route-I fallback** (`lyapunov-to-target.md` §5–6), used only if eigenspace
  convergence (§3.3) stalls. The committed L4.1–4.4 limsup flag is RETAINED to name exponents and as
  the a.e. bridge target (`Vᵢ = lambdaSublevel` a.e.).
  - ✅ **`ExteriorNorm.lean`** (NEW, pure multilinear algebra, no dynamics, upstreamable; namespace
    `ExteriorNorm`) — **COMPLETE, fully `sorry`-free.** Diamond-safe approach:
    NO inner-product instance on `⋀^k E` (it unfolds to a submodule with an existing `AddCommGroup`;
    a fresh `NormedAddCommGroup` breaks `IsTopologicalAddGroup` synthesis — verified). Instead the
    Hodge structure is carried as DATA via `hodgeTrivialization : ⋀^k E ≃ₗ EuclideanSpace` (the wedge
    o.n. basis of `stdOrthonormalBasis ℝ E` → standard Euclidean basis); all metric reasoning happens
    in the Euclidean target. Sorry-free & axiom-clean: `exteriorTrivialization`, `wedgeBasis`,
    `hodgeTrivialization`, `exteriorOpNorm`, the **submultiplicativity engine `exteriorOpNorm_comp_le`**
    (via `exteriorPower.map_comp` + `opNorm_comp_le`), the **SVD orthogonality core**
    `inner_apply_eigenvectorBasis_eq` (`⟪f uᵢ, f uⱼ⟫ = δᵢⱼ σᵢ²`), the **det-Gram kernel**
    (`hodgeForm` + `innerₗ_eq_coord`: the det-Gram form agrees with the Euclidean inner product through
    the o.n.-basis-wedge trivialization ⟹ o.n.-basis-change invariance `exteriorOpNorm_onbTriv_eq`),
    the **bridge** `exteriorOpNorm_hodge_eq_prod_singularValues` (`‖⋀^k f‖ = ∏_{i<k} σᵢ(f)`, via SVD
    diagonalization of `conjExteriorMap` on wedge bases + `prod_le_prod_top` max-product), and the crux
    `prod_singularValues_comp_le` (`∏σ(g∘f) ≤ ∏σ(g)·∏σ(f)`). QA gate PASS: `lake build` green (2897
    jobs); zero `sorry`; both bridge theorems depend only on `[propext, Classical.choice, Quot.sound]`
    (no `sorryAx`/`native_decide`); statements verified non-vacuous. Repo now holds 1 sorry (the target).
  - 🔄 **`OseledetsLimit.lean`** (NEW) — **scalar layer L1–L6 + M-1 DONE, fully `sorry`-free** (route:
    `oseledets-limit-route.md`). Banked sorry-free & axiom-clean: **M-1** `sigma_le_opNorm`
    (`σᵢ(toEuclideanLin M) ≤ ‖M‖`) + companions; **L1** `Sprod`/`gram`/`Sprod_submul`/
    `isSubadditiveCocycle_logSprod` (correct Kingman index convention); **L3** the integrability
    sandwich `integrable_logSprod`/`bddBelow_logSprod` + `Sprod_pos` (`k ≤ d`, via `det ≠ 0`);
    **L4** `tendsto_GammaK` and the clean end-to-end `tendsto_GammaK_of_integrableLogNorm` (genuine
    ergodic `Γ_k` limit via `tendsto_kingman_ergodic` + the ExteriorNorm submultiplicativity);
    **L5** `tendsto_log_singularValue` (`λᵢ = Γ_{i+1}−Γ_i`, antitone); **L6** `sq_singularValues_eq_gram_eigenvalue`.
    The L3 measurability obligation `measurable_Sprod` was closed PROPERLY (no measurable-selection
    cop-out) by building the **compound-matrix bridge in `ExteriorNorm.lean`**: `compoundMatrix k M`
    (entries = `k×k` minors), `conjExteriorMap_eq_toEuclideanLin_compound`, and the public
    `prod_singularValues_eq_l2_opNorm_compound` (`∏_{i<k} σᵢ(toEuclideanLin M) = ‖C_k(M)‖`) — so
    `Sprod` is measurable via measurable minors + continuous L2 op-norm. QA gate PASS: `lake build`
    green (2898 jobs); only the target `sorry` remains; all scalar-layer + compound-bridge decls
    depend only on `[propext, Classical.choice, Quot.sound]`.
  - **`OseledetsLimit.lean` REMAINING (L7+, task #19, the crux):** (§3.3, highest risk, no Mathlib
    Davis–Kahan) eigenspace/projection convergence `Qₙ^{1/2n} → Λ` via a from-scratch gapped
    self-adjoint Cauchy-projection argument; (§3.4) bridge `Vᵢ = lambdaSublevel` a.e.; the forward
    limit on each stratum; measurability hookup (CFC polynomial bypass); assemble target. ~4–8 sessions.
  - Build order NOW: `… → Measurable` (done) → `ExteriorNorm` (done) → `OseledetsLimit` (scalar done;
    crux next) → `MultiplicativeErgodic`.
  - Mathlib HAS (verified): real Hermitian CFC, `posSemidef_conjTranspose_mul_self`, sorted Hermitian
    eigenvalues/eigenvectorBasis, CFC `rpow`/`sqrt`, `exteriorPower.map`/`map_comp`,
    `LinearMap.singularValues` (basic API only). CAVEAT: `Filter.Tendsto.cfc` routes through the
    non-synthesizing `IsometricContinuousFunctionalCalculus ℝ (Matrix..ℝ)` — use the polynomial bypass.
  M7 scout: `docs/research/scratch/m7-measurable-scout.md`; measurability plan: `m7-measurable-strategy-v2.md`.

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
| `oseledets_filtration` | MultiplicativeErgodic | M10 (TARGET) |

(Down to **1** open `sorry`: M4 Kingman and M5 Furstenberg–Kesten are both fully closed.
The lone remaining gap is the final target `oseledets_filtration`.)

Not yet in the skeleton (deferred to their phases): the Lyapunov layers L4.x/L5.x and the
measurability of exponents/filtration (M7). Added when their phase begins.

## What is next (in order)

1. ✅ P0–P3, M2, M1, M3 (committed).
2. ✅ M4 research/design → v2 blueprint; M4 foundation (`18f9069`); M4 reduction.
3. ✅ **M4 Kingman fully closed** (Karlsson leaders route, L-A→L-E): `ae_tendsto_cdiv` and
   `ae_ereal_limsup_le_liminf` proved; 4 → 3 open `sorry`s; axioms clean; checker PASS.
4. ⏳ **M5 Furstenberg–Kesten** (`m5-furstenberg-kesten.md`) — NEXT; then Lyapunov layers
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
