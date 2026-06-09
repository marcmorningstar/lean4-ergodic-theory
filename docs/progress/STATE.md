# Oseledets MET formalization — living state

> Single source of truth for resuming this project. Fresh agent: read this file top
> to bottom, then `docs/research/understanding.md` (the math + the L0–L7 lemma
> ladder), `docs/research/target-and-milestones.md` (target + milestones M0–M13),
> `docs/plan/` (decision record + phased plan + api-notes), and for the active phase
> `docs/plan/blueprints/m4-kingman-v2.md` + `docs/research/scratch/m4-L9-notes.md`.
> Charter: `PROMPT.md`.

_Last updated: 2026-06-09 (endgame phase: per-vector exact growth reduced to the
verified S4 crux; foundations committed at `4812bd5`)._

## ENDGAME STRUCTURE (2026-06-09) — the target reduced to ONE crux lemma

The analytic core (L7–L9, Λ exists/measurable/eigenvalues `=e^{λᵢ}`, L12 foundation) is **done**
and committed. The remaining target `oseledets_filtration` decomposes into: per-vector exact growth
(lower + upper), measurable `V` (L10), `V_Λ = lambdaSublevel` a.e. (L11), assemble (L13). New work
lives in **`Oseledets/Lyapunov/Forward.lean`** (wired into the root; green at `4812bd5`).

**The single irreducible new mathematics is the per-vector growth UPPER bound, which reduces
entirely to the crux lemma S4 (= (A′)):**

> **S4 / (A′).** For `v` with NO Λ-component above `λᵢ` (i.e. `Pᶜ_∞ v = 0` for thresholds
> `c > e^{λᵢ}`), and `cₘ` straddling block m−1/m with `1 ≤ m ≤ i`:
> `limsup (1/n) log ‖Pᶜᵐₙ v‖ ≤ λᵢ − λₘ₋₁`.

S4 is **VERIFIED TRUE** (mathematician, 400-digit numerics on real product cocycles). It is a
*vector-aware* (sharp) Davis–Kahan leakage rate, strictly sharper than the operator-norm projector
rate `λₘ−λₘ₋₁` (the gap `λₘ−λᵢ` is the gain from `v` being in a deep slow block). **Two traps
confirmed (do NOT take them):** (i) the Abel-summation route with the operator-norm rate is BROKEN
(too weak for ≥3 exponents above `v`); (ii) routing S4 through the band quadratic form
`inner_cfc_ge_band` is CIRCULAR (it needs the very growth bound being proved) and gives the wrong
rate. **Non-circular handle:** `‖Pᶜᵐₙ v‖ = ‖(Pᶜᵐₙ − Pᶜᵐ_∞) v‖` (since `Pᶜᵐ_∞ v = 0`), then
telescope the off-diagonal sin-Θ (`offdiag_sin_le_residual_div_gap`,
`norm_offdiag_residual_compound_le`, `perturbed_compound_gram_ceiling`) **carrying the fixed vector
`v`** across the `i−m+1` intermediate gaps (each contributes one σ-ratio, compounding to
`e^{n(λᵢ−λₘ₋₁)}`). Sub-lemma ladder S0–S5; S4 is the HIGH-difficulty node (est. several sessions).
`inner_cfc_ge_band` is the LOWER-bound tool only. There is **no** simpler upper-bound route (the
operator-norm and quadratic-form shortcuts both fail; S4 is equivalent in content to the bound).

**Given S4, the upper bound is a simple per-block split** (NO Abel): `‖Aⁿv‖² = Σⱼ σⱼ²|⟨v,eⱼ⟩|²`,
slow part `≤ sᵢ²‖v‖²` (→λᵢ), fast block `l` `≤ sₗ²·a_{l+1}²` → `λₗ + (λᵢ−λₗ) = λᵢ` via S4 at
`m=l+1`; then log-of-finite-sum.

**The LOWER bound is clean and robust** (no rate): `c^{2n}‖Pᶜₙv‖² ≤ ‖Aⁿv‖²`
(`inner_cfc_ge_band` with `Q=qpow`, `f=(·)^{2n}`, `a=c^{2n}`, plus `gram = cfc((·)^{2n}) qpow`),
then `Pᶜₙv → Pᶜ_∞v ≠ 0` gives `liminf ≥ log c` for every `c < e^{λᵢ}`, so `liminf ≥ λᵢ`.

**Banked sorry-free in `Forward.lean` (`4812bd5`):** `inner_cfc_ge_band` (Gram band bound, the
lower-bound foundation) and the deterministic distinct-exponent enumeration
`distinctExp`/`numExp`/`expEnum` (+ `expEnum_strictAnti`/`exists_expEnum_eq`/… — the `k` exponents
`λ₀>⋯>λ_{k-1}` for the target). **In progress:** lower-bound chain (`gram_eq_cfc_qpow`,
`cocycle_apply_sq_ge_band`, `log_le_liminf_log_cocycle_apply`).

**L10 (measurable V):** `V i x := range(toEuclideanLin(cfc gᵢ Λ̂ x))` with `gᵢ` a CONTINUOUS gap
interpolant (0/1 on the a.e.-constant spectrum `{e^{λⱼ}}`) and `Λ̂` = `oseledetsLimit` sanitized to
self-adjoint (junk→0/I off the good set) so `cfc gᵢ Λ̂` is a genuine projector EVERYWHERE; then
`orthProjMatrix(V i x) = cfc gᵢ Λ̂ x`, measurable via `measurable_cfc_continuous`
(global, no spectrum hypothesis). `MeasurableSubspace` then via `measurable_orthProjMatrix_iff`.

**L13 (assemble):** exponents `= expEnum lamS` (deterministic via `exists_lam_tendsto_singularValue`);
`V_Λ = lambdaSublevel` a.e. (L11: `⊆` via lower bound, `⊇` via S4 upper bound) so `V` inherits
`Vflag` strict-anti/equivariance/`lambdaBar_eq_on_stratum`; per-vector limit = lower+upper; spectrum
a.e.-constant by ergodicity. Handle `d=0` degenerate case separately.


## Target (one line)

`sorry`-free Lean 4 + Mathlib formalization of the **one-sided Oseledets MET in
filtration form** (milestone **M10** / layer **L6.1**), stated in Lean as
`Oseledets.oseledets_filtration` in `Oseledets/MultiplicativeErgodic.lean`.

## Current phase

**M6–M10 Lyapunov layers → the target (the only open `sorry`).** M4 Kingman + M5
Furstenberg–Kesten are fully closed (details below). The active front is the **L7c crux**
in `Oseledets/Lyapunov/{ExteriorNorm,OseledetsLimit}.lean` — a.e. convergence of
`qpow A T n x = (Qₙ)^{1/(2n)}` (the Oseledets limit `Λ`). **Route: `oseledets-l7c-route.md`
§J is the SOURCE OF TRUTH** (the earlier §G/§H/§I deficit route was found CIRCULAR and is
superseded — see §J.0). The corrected route uses the refined Davis–Kahan **off-diagonal**
sin-Θ. Banked sorry-free: the band projector + algebra (L7c.0/0.5/1), the tempered factor
(L7c.2), the corrected sin-Θ core `offdiag_sin_le_residual_div_gap` + root-test engine
`summable_of_logLimit_neg` (L7c.3a/4), the off-diagonal residual estimate + ceiling
(`norm_offdiag_residual_compound_le`, `perturbed_compound_gram_ceiling`), the Plücker
eigenpair bridge (`plucker_eigenpair_ceiling_standard`) + Frobenius back-transport
(`norm_proj_sub_le_wedge`) + det-Gram glue (`inner_hodgeTrivialization_ιMulti`), the
coordinate bridge + frame extraction (`bandProjector_indicator_eq_frame`), the rank-1 lower
bound (`norm_sq_compound_mul_ge`), the abstract per-step bound
`norm_bandProjector_succ_sub_le`, and the a.e.-summability packaging
`summable_norm_bandProjector_succ_sub`. **L7c.3 is now COMPLETE** (commit `da6b8cc`): the
unsorted↔sorted eigenframe reconciliation (`bandProjector_indicator_eq_sortedTopFrame`, via the
trace-zero symmetric-idempotent device), the concrete cocycle per-step bound
(`norm_bandProjector_succ_sub_le_cocycle`, all abstract hyps discharged), and a.e.
band-projector convergence (`exists_tendsto_bandProjector_cocycle`) are all banked sorry-free.
The convergence still THREADS two hypotheses to be discharged in L7d: `hstepAE` (a.e.-eventual
cut/gap/regime stability) and `hblog`/`hLneg` (the root-test log-limit `(1/n)log bCocycle →
λₖ−λₖ₋₁ < 0`). **NEXT (resumption):** discharge `hblog`/`hLneg` (closed form from committed
`tendsto_log_singularValue` two-index + `tendsto_logNorm_compound_orbit_div_atTop_zero` + the
`bCocycle` algebra) and `hstepAE` (from `eigenvalues_qpow_tendsto`: for `c` strictly between
two DISTINCT Lyapunov exponents `e^{λₖ₋₁} > c > e^{λₖ}`, eventually exactly `k` qpow eigenvalues
exceed `c` and `κ²r²<1`) ⟹ UNCONDITIONAL `tendsto_bandProjector` at each distinct-exponent gap.
**L7 is now COMPLETE** (commit `da38811`): `tendsto_qpow` discharges `L7_statement` in FULL
generality (arbitrary multiplicity) — the Oseledets limit `Λ = lim ((A⁽ⁿ⁾)ᵀA⁽ⁿ⁾)^{1/2n}` EXISTS
a.e., sorry-free. The analytic heart of the MET is done. **REMAINING = L8–L13** (connect `Λ` to the
target `oseledets_filtration`; the committed `Filtration.lean` limsup flag `Vflag`/`specList`/
`lambdaSublevel` already has strict-anti + equivariance + `lambdaBar_eq_on_stratum`, so the missing
links are): **L8** a named MEASURABLE `Λ` (extract from `tendsto_qpow`'s a.e. limit via
`measurable_of_tendsto`); **L9** `Λ` Hermitian-PD, its eigenvalues `= e^{λᵢ}` (from
`eigenvalues_qpow_tendsto` + continuity); **L10** measurable `V i x := range (cfc gᵢ Λ)` via the
committed CFC polynomial bypass (`measurable_cfc_eqOn_polynomial` in `Measurable.lean`); **L11**
`Vᵢ = lambdaSublevel` a.e. (so V inherits strict-anti/equivariance/growth from `Vflag`); **L12** the
genuine two-sided limit `(1/n)log‖A⁽ⁿ⁾v‖ → λᵢ` on each stratum (limsup-flag gives only limsup;
the SVD/`Λ` structure upgrades it to a limit); **L13** assemble. Spectrum/exponents made
a.e.-constant by ergodicity (`specCard`/`specList` constant; `λᵢ = Γ`-limits).
**PROGRESS UPDATE (commits through `abb1096`):** L7 COMPLETE (`tendsto_qpow`, Λ exists);
**L8 DONE** (`oseledetsLimit` measurable, via `measurable_cfc_continuous` — Weierstrass-poly CFC
measurability); **L9 DONE** (`oseledetsLimit_eigenvalues₀_eq`: eigenvalues₀ Λ = e^{λᵢ}, via the
NEW `Weyl.abs_eigenvalues₀_sub_le`/`tendsto_eigenvalues₀` eigenvalue-continuity infra — missing
from Mathlib, upstreamable); **L12 FOUNDATION DONE** (`norm_sq_cocycle_apply_eq_inner_gram`
`‖A⁽ⁿ⁾v‖²=⟪gram_n v,v⟫`, op-norm sandwich, and `tendsto_log_cocycle_apply_of_eq_exponents` — the
genuine two-sided limit in the EQUAL-exponent/conformal regime).
**THE REMAINING SUB-CRUX = general L12 exact-growth + L11 (interdependent), then L10 + L13:**
- **L12 general (per-vector):** `(1/n)log‖A⁽ⁿ⁾v‖ → λ(v)` = top active Oseledets exponent of v.
  LOWER bound `liminf ≥ λ(v)` is clean (keep the dominant gram term: `⟪gram_n v,v⟫ ≥
  μ_{i₀,n}|⟨v,u_{i₀,n}⟩|²`, `(1/2n)log μ_{i₀,n} → λ_{i₀}`, component → `⟨v,Λ-eigvec⟩≠0`, no rate).
  **UPPER bound `limsup ≤ λ(v)` is the genuine sub-crux**: for v in bottom Λ-blocks, the top-block
  leakage `‖P^{>cᵢ}(qpow_n)v‖ = ‖(P_n−P)v‖` must decay faster than the top singular value grows —
  a naive single-projector bound FAILS when multiple exponent-blocks sit above λᵢ
  (`‖ΔP_n‖ ~ e^{−n·gap}` need not beat `e^{n(λ_max−λᵢ)}`). Needs a BLOCK-BY-BLOCK rate argument
  (each block's projector converges at its own gap rate; telescope). Recommend a focused SPIKE on
  this before building. Interdependent with L11.
- **L11 (`Vᵢ = lambdaSublevel` a.e.):** the hard direction `V_Λ ⊆ lambdaSublevel` is exactly the
  L12 upper bound (`v ∈ bottom Λ-blocks ⟹ limsup ≤ λᵢ`); the easy direction is the L12 lower bound.
  Once L12 general lands, L11 follows; then V inherits `Vflag`'s strict-anti/equivariance.
- **L10 (measurable V):** `V i x := ` Λ-spectral-projector range (band projector at threshold cᵢ),
  measurable via the committed CFC polynomial bypass / `measurable_cfc_continuous`.
- **L13 (assemble `oseledets_filtration`):** spectrum a.e.-constant by ergodicity (`specCard`/
  `specList`/`λᵢ=Γ`-limits constant); package V + lam + the flag/equivariance/exact-growth.
RESUMPTION ENTRY POINTS (committed): `norm_sq_cocycle_apply_eq_inner_gram`,
`tendsto_bandProjector_of_gap`, `oseledetsLimit_eigenvalues₀_eq`, `Weyl.tendsto_eigenvalues₀`,
the `Filtration.lean` `Vflag`/`lambdaSublevel`/`lambdaBar_eq_on_stratum`/`Vflag_equivariant`.

Legacy detail (L8–L13 also reads): Λ measurability via the committed CFC polynomial bypass;
Λ eigen-data; `Vᵢ = lambdaSublevel` a.e.; forward limit on strata; assemble
`oseledets_filtration`). **Practical risk:** fully-instantiated `⋀^k`-finrank statements hit
the elaborator heartbeat ceiling — use the abstract-operator + scoped-lemma pattern.

---

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
  - **L7 scaffolding (L7a/L7b) DONE, `sorry`-free** (plan: `oseledets-l7-crux.md`). `gram_posSemidef`/
    `gram_isSelfAdjoint`; `qpow A T n x := cfc (·^(1/(2n))) (gram A T n x)` (the matrix `(Qₙ)^{1/2n}`)
    + `qpow_isSelfAdjoint`; the `L7_statement` Λ-existence Prop (stated, not proved); and the eigenvalue
    layer: new infra `roots_charpoly_cfc_eq` + `eigenvalues₀_cfc_of_monotoneOn` (sorted eigenvalues of
    `cfc f A` = `f ∘ eigenvalues`, `MonotoneOn (Ici 0)` form), `gram_eigenvalues₀_eq_sq_singularValues`,
    `eigenvalues₀_qpow_eq` (`= σᵢ^{1/n}`), and **L7b** `eigenvalues_qpow_tendsto` (eigenvalues of `qpow`
    → `e^{λᵢ}` a.e., from `tendsto_log_singularValue`). All axiom-clean.
  - **L7c projector scaffolding (L7c.0 + L7c.5) DONE, `sorry`-free** (route: `oseledets-l7c-route.md`).
    `bandProjector A T χ n x := cfc χ (qpow A T n x)` + `bandProjector_isSelfAdjoint` (`cfc_predicate`)
    + `bandProjector_mul_self` (idempotent on the gap, via `cfc_mul`+`cfc_congr` — orthogonal projector);
    and the Cauchy packaging `cauchySeq_of_summable_norm_sub` (general matrix sequence with summable
    increments is Cauchy) ⟹ `cauchySeq_cfc_of_summable` ⟹ `exists_tendsto_cfc_of_summable`. All on plain
    `Matrix _ _ ℝ` with the BARE Hermitian CFC (no isometric instance). Axiom-clean. The mathematical
    weight remaining is entirely in supplying the *summability* of the projector increments (L7c.3/L7c.4).
  - **L7c.3a (the crux's analytic core) DONE, `sorry`-free.** `sin_sq_le_rayleigh_deficit_div_gap`:
    the elementary rank-1 Rayleigh-gap sin-Θ bound (`‖v' − ⟪v',v₀⟫v₀‖² ≤ ε/(μ₀−μ₁)` for a near-maximal
    unit `v'`), the Parseval + one-`nlinarith`-kernel replacement for the absent Mathlib Davis–Kahan
    sin-Θ. Abstract (any real inner product space), upstreamable, axiom-clean. Route verified in
    `oseledets-l7c-route.md` §G: the committed exterior-power machinery collapses the block-projector
    problem to THIS rank-1 lemma, so no abstract block sin-Θ theorem is needed. Remaining crux nodes:
    L7c.3b (exterior Rayleigh-deficit via `compoundMatrix`, needs single-index `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖σⱼ(X)`),
    L7c.3c (Plücker subspace↔eigenline bridge assembling `norm_bandProjector_succ_sub_le`).
  - **L7c.2 (tempered one-step factor) DONE, `sorry`-free.** `tendsto_logNorm_orbit_div_atTop_zero` and
    `..._inv_...`: `(1/n)·log‖A(Tⁿx)‖ → 0` and `(1/n)·log‖A(Tⁿx)⁻¹‖ → 0` a.e. De-privatized
    `Ergodic/Birkhoff.lean`'s `ae_tendsto_orbit_div_atTop_zero` (Birkhoff orbital tail `n⁻¹·g(Tⁿx)→0`
    for integrable `g`) and instantiated at the integrable signed log-norms (`integrable_logNorm_cocycle`
    at `n=1`, `cocycle A T 1 = A`). Axiom-clean. Feeds L7c.4 summability.
  - **L7c.1 + L7c.3b.0 + L7c.3c.0 (foundational geometry nodes) DONE, `sorry`-free** (route §H, 8
    probes compiled). In `ExteriorNorm.lean`: `compoundMatrix_mul` (matrix-level Cauchy–Binet
    `Cₖ(B·M) = Cₖ(B)·Cₖ(M)`) + `toEuclideanLin_compoundMatrix_mul` (the linear-map form the rank-1
    deficit chain consumes), via committed `conjExteriorMap_eq_toEuclideanLin_compound` +
    `exteriorPower.map_comp`; and `singularValues_zero_sq_le_sum` (`σ₀² ≤ Σσᵢ²`, the operator≤Frobenius
    core, stated through `toEuclideanLin` to dodge the L2/Frobenius instance diamond). In
    `OseledetsLimit.lean` (L7c.1): `bandProjector_indicator_mul_self` (the 0/1-indicator band projector
    is idempotent — a genuine orthogonal projector; continuity discharged via finite spectrum),
    `cfc_eq_eigenvectorUnitary_conj` (explicit `cfc χ M = U·diag(χ∘eig)·Uᴴ`), and `bandProjector_rank`
    (rank = #{eigenvalues with χ≠0} = dim of the top block). Axiom-clean. Remaining: L7c.3b (rank-1
    deficit), L7c.3c.1 (Frobenius 2k back-transport), L7c.3c (assemble `norm_bandProjector_succ_sub_le`),
    L7c.4 (hsum), L7d (assemble `L7_statement`).
  - **`OseledetsLimit.lean` REMAINING (L7c.3+, task #22, the crux):** (§3.3, highest risk, NEW infra
    M-2′, no Mathlib Davis–Kahan) the gapped self-adjoint **projection-Cauchy** estimate (per-distinct-λ,
    NOT per-index) ⟹ `oseledetsLimit Λ` exists (L7d, closure compiled); then (§3.4) bridge
    `Vᵢ = lambdaSublevel` a.e. (L11), forward limit on each stratum (L12), measurability hookup via the
    committed CFC polynomial bypass (L8/L10), assemble target (L13). Critical path L7c → L7d → {L10,L11}
    → L12 → L13. ~4–8 sessions; L7c is the single irreducible hard node.
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
