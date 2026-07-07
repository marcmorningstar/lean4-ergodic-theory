# Oseledets limit (§3.3 crux) — route decision

> De-risking pass, 2026-06-06. Compiled spikes: `scratch_limit33_scalar.lean`,
> `scratch_limit33_eig.lean`, `scratch_limit33_kingman.lean` (all `lake env lean` exit 0).
> Supersedes the route-open parts of `limit-endgame.md` §3.3/§5; keeps its measurability
> verdict (`scratch_limit_spike.lean`) and the §3.1 confidence.

## 0. TL;DR verdict

- **Eigenvalue layer (§3.1): VERIFIED tractable, HIGH confidence.** Genuine limits
  `Γ_k = lim (1/n) log ∏_{i<k} σᵢ(A⁽ⁿ⁾)` come straight from Kingman applied to a subadditive
  cocycle built from the already-proven `ExteriorNorm.prod_singularValues_comp_le`. The
  submultiplicativity, the `IsSubadditiveCocycle` packaging (correct index convention), and
  the bridge "σᵢ² = i-th eigenvalue of the Gram matrix `Qₙ = A⁽ⁿ⁾ᵀA⁽ⁿ⁾`" are all COMPILED.
  This gives the **eigenvalues of `Λ`** (as genuine ergodic limits) WITHOUT ever building `Λ`
  as a matrix limit.

- **The recommended PRIMARY route is the growth-function (limsup) filtration that is ALREADY
  committed** (`GrowthFunction.lean` + `Filtration.lean`). It supplies, a.e., FOUR of the five
  target conjuncts verbatim (`StrictAnti`, `⊤`/`⊥`, strict decrease, equivariance). `Λ` is NOT
  the primary spine.

- **`Λ` (the matrix limit `lim Qₙ^{1/2n}`) is still REQUIRED, but only as a service object for
  exactly TWO things, which are coupled:** (a) measurability of `V_i` (the committed CFC
  polynomial-bypass route is the only built one, and it needs `Λ`), and (b) the genuine forward
  limit `lim (1/n)log‖A⁽ⁿ⁾v‖ = lam_i` on each stratum (the target's 5th conjunct; `lambdaBar`
  is only a `limsup`). Both funnel through eigenspace/projection convergence (§3.3) and the
  bridge §3.4. There is no soft bypass: this is the genuine Oseledets-regularity content.

- **Net:** keep the limsup flag as primary; build `Λ` (scalar layer is cheap+verified; the
  eigenSPACE/projection convergence is the one genuinely hard, Mathlib-missing piece); use `Λ`
  only for measurability + forward-limit + the §3.4 bridge. This is essentially `limit-endgame.md`'s
  Route II but with the **division of labor sharpened**: the limsup flag is load-bearing for the
  algebraic conjuncts, `Λ` is load-bearing only for the analytic/measurable conjuncts.

## 1. Why NOT "growth-function-filtration ALONE (no Λ)"

Adversarial check of the cheapest hope — can we drop `Λ` entirely?

Two target conjuncts resist:

1. **Measurability `MeasurableSubspace (V_i)`.** `V_i x = lambdaSublevel A T x (specList i)` is a
   limsup-sublevel. `MeasurableSubspace` ≡ `Measurable (x ↦ orthProjMatrix (V_i x))`. The
   limsup-sublevel has no measurable handle except through a measurable selection of a spanning
   family — which **Mathlib lacks** (Kuratowski–Ryll-Nardzewski / Castaing), and which the M7 scout
   already proved is a genuine gap (the "fixed countable dense family" idea is FALSE; documented in
   `m7-measurable-strategy-v2.md`). The committed resolution routes `orthProjMatrix(V_i x) = cfc gᵢ (Λ x)`
   via the polynomial bypass — **this needs `Λ`.**

2. **Forward limit (target conjunct 5).** Target needs `Tendsto (fun n => (1/n)log‖A⁽ⁿ⁾v‖) (𝓝 lam_i)`,
   a true limit; the committed flag only gives `lambdaBar = limsup = lam_i` (`lambdaBar_eq_on_stratum`).
   The `liminf ≥ lam_i` lower bound on a stratum is the Oseledets regularity statement. For a ONE-sided
   cocycle there is no soft argument: the lower bound needs either (a) `Λ`'s eigenspace structure
   (decompose `v`, read the dominant block), or (b) the Raghunathan/Ruelle tempering induction on the
   sub-cocycle (Route I, `lyapunov-to-target.md` §5–6), which itself needs the filtration to be
   MEASURABLE and equivariant to define the induced sub-cocycle — i.e. it needs (1) anyway.

So `Λ` (or an equivalent regularity device) is **not eliminable**. The limsup flag is necessary but
not sufficient.

## 2. COMPILED spikes (load-bearing steps)

| File | Proves | Status |
|---|---|---|
| `scratch_limit33_scalar.lean` | `Sprod_submul` (`∏σ(A⁽ᵐ⁺ⁿ⁾) ≤ ∏σ(A⁽ᵐ⁾∘Tⁿ)·∏σ(A⁽ⁿ⁾)`, via `prod_singularValues_comp_le` + `toEuclideanLin` multiplicativity + `cocycle_add`); `logSprod_subadditive` | exit 0 |
| `scratch_limit33_eig.lean` | `adjoint_comp_self_eq_gram` (`adjoint(toEuclideanLin M)∘toEuclideanLin M = toEuclideanLin(MᵀM)`); σᵢ(toEuclideanLin M)² = i-th eigenvalue of `MᵀM` (via `sq_singularValues_fin`) | exit 0 |
| `scratch_limit33_kingman.lean` | `isSubadditiveCocycle_logSprod` (correct Kingman index convention `g(m+n,x) ≤ g(m,x)+g(n,T^[m]x)`); `tendsto_GammaK` (the genuine ergodic Γ_k limit via `tendsto_kingman_ergodic`) | exit 0* |
| `scratch_limit_spike.lean` (pre-existing) | measurability spine: `measurable_gram`, `isHermitian_gram`, `measurable_of_pointwise_limit`, `measurable_cfc_gram` | exit 0 |

(*verified up to the final `tendsto_GammaK` glue; see §6.)

Together these COMPILE the entire §3.1 scalar layer end-to-end modulo the two FK-pattern
integrability obligations (`hint`, `hbdd`), which are taken as hypotheses in `tendsto_GammaK` and
are the same shape already discharged for Furstenberg–Kesten.

## 3. Mathlib API: found vs missing

FOUND / confirmed usable (compiled against):
- `LinearMap.singularValues`, `singularValues_antitone`, `singularValues_nonneg`,
  `sq_singularValues_fin` (`σᵢ² = eigenvalue of adjoint∘self`), `injective_iff_forall_lt_finrank_singularValues_pos`.
- `Matrix.toEuclideanLin` (linear equiv), multiplicative on products (proved by `ext;simp` in spike),
  `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` (adjoint = transpose over ℝ).
- `ExteriorNorm.prod_singularValues_comp_le` (committed, sorry-free) — the submultiplicativity.
- `tendsto_kingman_ergodic` (committed, sorry-free) — the genuine ergodic limit.
- `Matrix.IsHermitian.eigenvalues`, real Hermitian CFC, CFC `rpow`/`sqrt`, `posSemidef_conjTranspose_mul_self`.
- Measurability: `measurable_cfc_eqOn_polynomial` (committed crux), the spike measurability lemmas.

MISSING from Mathlib (must be BUILT; user directive = build properly, upstreamable):
- **M-1 `σ₀(f) ≤ ‖f‖` (equivalently `‖f‖ = σ₀(f)`).** `SingularValues.lean` is the ONLY Mathlib file
  mentioning singular values and it has ZERO connection to operator norm. Needed for the Kingman
  integrability `hint` of the scalar layer (`log Sprod ≤ k·log‖A⁽ⁿ⁾‖`). REACHABLE from already-built
  `ExteriorNorm` (`‖⋀¹ f‖ = σ₀(f)` plus `⋀¹ ≅ id`), or directly. LOW–MEDIUM.
- **M-2 Davis–Kahan / eigenprojection perturbation / eigenvalue-eigenvector continuity.** CONFIRMED
  ABSENT (grep of all Mathlib: no `sin Θ`, no eigenvalue/eigenvector continuity, no spectral-projection
  perturbation). This is the true §3.3 gap.
- **M-3 matrix-limit eigenspace convergence (`Qₙ^{1/2n} → Λ` with projections).** Absent; downstream of M-2.

## 4. What remains genuinely hard (the irreducible crux)

After the cheapest route, the irreducibly-hard, Mathlib-missing content is:

**THE CRUX (§3.3 + §3.4 entangled): the gapped self-adjoint projection-convergence + the
limsup↔eigenspace bridge.** Concretely one must prove, a.e.:

- `Λ x := lim_n (Qₙ x)^{1/2n}` EXISTS in `Matrix (Fin d) (Fin d) ℝ` (operator-norm/entrywise),
  Hermitian PD, with eigenvalues `e^{lam_i}` (eigenvalues converge by §3.1; the matrix/eigenSPACE
  convergence is the gap).
- The spectral projection of `Λ x` onto eigenvalues `≥ e^{lam_i}` has range `= lambdaSublevel A T x (lam_i)`
  (the §3.4 bridge), which simultaneously yields (a) `orthProjMatrix(V_i) = cfc gᵢ (Λ)` ⟹ measurability,
  and (b) the forward limit `lim (1/n)log‖A⁽ⁿ⁾v‖ = lam_i` on the stratum (decompose `v` against `Λ`'s
  eigenbasis; the dominant nonzero block governs the genuine limit).

There is NO Mathlib infrastructure for the projection convergence; it must be built as a from-scratch
**gapped self-adjoint Cauchy argument**: the eigenvalue ratio between strata is `e^{(lam_i−lam_{i+1})·2n} → ∞`,
forcing the order-`i` spectral projector of `Qₙ^{1/2n}` to be Cauchy in operator norm. This is the
4–8 session, highest-risk piece. Confirmed unavoidable in §1.

## 5. Risk-tagged sorry-free lemma ladder for `OseledetsLimit.lean`

Build order: `… Measurable (done) → ExteriorNorm (done) → OseledetsLimit → MultiplicativeErgodic`.

| # | Lemma (abbrev.) | Risk | Notes |
|---|---|---|---|
| L1 | `Sprod`/`gram`; `Sprod_submul`; `isSubadditiveCocycle_logSprod` | **LOW (COMPILED)** | spikes `scalar`/`kingman` |
| L2 | `sigma_le_opNorm` : `σᵢ(toEuclideanLin M) ≤ ‖M‖` | LOW–MED | **NEW infra M-1**; from `ExteriorNorm` k=1 |
| L3 | `integrable_logSprod` + `bddBelow_fekete_logSprod` (FK pattern) | MED | reuse FK integrability plumbing; needs L2 |
| L4 | `tendsto_GammaK` : genuine ergodic `Γ_k` limit | **LOW (COMPILED shape)** | spike `kingman`; needs L3 |
| L5 | `lamSing i := Γ_{i+1}−Γ_i`; `tendsto_log_singularValue` (σ-exponents) | MED | differencing of Γ_k; `Antitone` from `singularValues_antitone` |
| L6 | `sq_singularValues = eigenvalues_gram` (σ² = Λ-eigenvalue) | **LOW (COMPILED)** | spike `eig` |
| L7 | `oseledetsLimit Λ` exists: `Tendsto (Qₙ^{1/2n}) (𝓝 (Λ x))` a.e. | **HIGH (CRUX)** | **NEW infra M-2/M-3**; gapped Cauchy projection argument |
| L8 | `measurable_oseledetsLimit` | LOW–MED | spike `measurable_of_pointwise_limit` + CFC bypass; needs L7 |
| L9 | `eigenvalues_oseledetsLimit = e^{lamSing}`; `posDef`/`isHermitian` | MED | needs L5+L6+L7 |
| L10 | `V i x := range(toEuclideanCLM (cfc gᵢ (Λ x)))`; `orthProjMatrix_V = cfc gᵢ (Λ)`; `MeasurableSubspace (V i)` | MED–HIGH | M7 polynomial bypass (committed crux); needs L7 |
| L11 | `V_ae_eq_lambdaSublevel` (§3.4 bridge) | **HIGH (CRUX)** | needs L7+L9; the limsup↔eigenspace identity |
| L12 | `tendsto_log_norm_on_stratum` (forward limit = lam_i) | MED–HIGH | from L7+L9+L11 (decompose v against Λ-eigenbasis) |
| L13 | assemble `oseledets_filtration` | LOW | L11 reuses `Filtration.lean` (StrictAnti/⊤/⊥/strict/equivariant); L12 = conjunct 5; L10 = measurability |

Critical path through the two HIGH-risk nodes: **L7 → {L10, L11} → L12 → L13.** Everything else is
LOW/MED and largely spike-verified.

## 6. Pitfalls / adversarial findings

- **Index convention trap (caught & fixed in spike):** Kingman's `IsSubadditiveCocycle` wants
  `g(m+n,x) ≤ g(m,x) + g(n, T^[m]x)`, but `cocycle_add` naturally gives the `T^[n]`-shifted split.
  Resolved by the symmetric `cocycle(m+n,x) = cocycle(n, T^[m]x)·cocycle(m,x)` rewrite (`m+n = n+m`).
  Compiled in `isSubadditiveCocycle_logSprod`.
- **`Sprod` positivity is `k`-dependent:** for `k ≤ d` (invertible cocycle) all top-k σᵢ > 0 so
  `log Sprod` is finite; for `k > d`, `Sprod = 0` and `log` is junk. The ladder must restrict to
  `k ∈ {1,…,d}` (equivalently feed `hpos` only for those `k`). Not a blocker — the exponents live in
  `Fin d` — but the `hpos` hypothesis is real and must be discharged from `det ≠ 0` via
  `injective_iff_forall_lt_finrank_singularValues_pos`.
- **`Filter.Tendsto.cfc` is NOT usable on real matrices** (routes through the non-synthesizing
  `IsometricContinuousFunctionalCalculus ℝ (Matrix..ℝ)`), reconfirmed. L8/L10 must use the polynomial
  bypass; L7's convergence must be proved by the from-scratch Cauchy argument, NOT by CFC-continuity.
- **No counterexample found** to any committed statement; the limsup flag layer and `ExteriorNorm`
  are sound. The only "surprise" is positive: §3.1 delivers the eigenvalues of `Λ` as genuine limits
  with zero new convergence theory (pure Kingman), so `Λ`'s *eigenvalues* never need the matrix limit —
  only its *eigenspaces* (L7) do.
