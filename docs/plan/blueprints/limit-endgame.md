# Limit endgame — the Oseledets limit `Λ` and the final analytic stretch to `oseledets_filtration`

> Author: planning pass, 2026-06-06. Make-or-break spike compiled (`scratch_limit_spike.lean`,
> `lake env lean` exit 0, sorry-free). Supersedes §5–6 of `lyapunov-to-target.md` for the
> *route decision*; reuses everything below the L4.4 flag.

## 0. TL;DR / route decision

**Adopt Route II (the SVD / Gram-limit object `Λ`) as the PRIMARY spine of the endgame, and
DISCARD the limsup tempering / block-triangular peel-and-induct machinery of
`lyapunov-to-target.md` §5–6 (Subbundle / Limit) as the route to the growth rates.**

Rationale, in one paragraph: the measurability pivot (`m7-measurable-strategy-v2.md`) already
forces `Λ x = lim_n (Qₙ x)^{1/(2n)}`, `Qₙ x = (A⁽ⁿ⁾(x))ᵀ A⁽ⁿ⁾(x)`, into existence — the concrete
flag subspaces are CFC-projection ranges of `Λ`. Once `Λ` exists a.e. with its eigen-data, it
supplies **every** conjunct of the target *directly and as genuine limits* (not just limsup):
the exponents are `lam i = log(eigenvalues of Λ)`, `StrictAnti` is the descending eigenvalue
order, the flag is the sum-of-eigenspaces filtration, equivariance is the intertwining
`Λ(Tx) · A x = A x · Λ x` up to the cocycle, exact growth `lim (1/n)log‖A⁽ⁿ⁾ v‖ = lam i` on each
stratum is read off the SVD, and measurability is the (already-compiled) CFC crux. Keeping BOTH
the limsup blueprint AND `Λ` would mean proving the deep `Vᵢ = lambdaSublevel` bridge AND the
block-triangular induction — strictly more work than `Λ` alone. So `Λ` is built once and is the
single analytic core; the limsup `lambdaBar`/`Vflag` machinery (L4.1–4.4, already committed) is
**retained only to NAME the exponents and as the a.e. bridge target** (`Vᵢ = lambdaSublevel` a.e.),
not as a separate proof of the growth rates.

**Honest cost verdict.** `Λ`-existence (a.e. convergence of `(Qₙ)^{1/(2n)}` *with eigenspace
convergence*) is the single largest remaining piece of the project — comparable in size to
Kingman. It is genuinely hard and Mathlib is missing two infrastructure pieces (operator norm
on exterior powers; a clean SVD/eigenspace-convergence packaging). Estimate: **3–6 implementation
sessions for the scalar (singular-value) convergence, plus 4–8 sessions for eigenspace
convergence and the gap/projection-convergence argument** — the latter being the true crux.
Measurability, by contrast, is essentially done (spike + committed crux).

## 1. Make-or-break spike result (COMPILED)

File `scratch_limit_spike.lean` (`lake env lean`, exit 0, sorry-free; one benign
`unusedSectionVars` linter warning). It verifies the *measurability* spine of Route II using only
already-built modules and the committed crux `measurable_cfc_eqOn_polynomial`:

- `measurable_gram` — `x ↦ (cocycle A T n x)ᵀ * (cocycle A T n x)` is measurable (transpose is an
  index permutation of the Pi structure; `measurable_cocycle` + `Measurable.mul`).
- `isHermitian_gram` — each Gram matrix is `IsSelfAdjoint` (for ℝ, `conjTranspose = transpose`, so
  `(MᵀM)ᵀ = MᵀM` by `transpose_mul`+`transpose_transpose`). Feeds the `hMsa` hypothesis of the crux.
- `measurable_of_pointwise_limit` — **the `Measurable Λ` shape**: a pointwise (entrywise) limit of
  measurable matrix maps is measurable. Crucially proved **against the repo's Pi `MeasurableSpace`
  on matrices** (`instMeasurableSpaceMatrix`), reducing to scalar entries via `measurable_pi_iff` +
  `tendsto_pi_nhds` (twice) + `measurable_of_tendsto_metrizable` on ℝ. **This sidesteps the
  `BorelSpace (Matrix ..)` instance that does NOT hold for the Pi structure** — a real subtlety the
  v2 plan glossed (`measurable_of_tendsto_metrizable` needs `BorelSpace`; we never invoke it on
  matrices, only on ℝ entries).
- `measurable_cfc_gram` — each spectral approximant `x ↦ cfc g (Qₙ x)` is measurable: a direct
  application of the committed `measurable_cfc_eqOn_polynomial` to `measurable_gram`/`isHermitian_gram`.

**Verdict:** the measurability of `Λ` and of the CFC flag projections is cheap and verified. The
risk in Route II is *entirely* in the analytic existence of `Λ` (§3), not its measurability.

## 2. Verified Mathlib inventory (grep/build-confirmed)

EXISTS and BUILDS (built locally this session where olean was missing):
- `Matrix.IsHermitian.instContinuousFunctionalCalculus` (real Hermitian CFC) — used by committed crux.
- `Matrix.posSemidef_conjTranspose_mul_self` (`LinearAlgebra/Matrix/PosDef.lean:355`) — `Aᴴ A ⪰ 0`.
- `Matrix.IsHermitian.eigenvalues`, `eigenvalues₀`, `eigenvalues₀_antitone` (sorted!),
  `eigenvectorBasis`, `eigenvectorUnitary`, `eigenvalues_mem_spectrum_real`
  (`Analysis/Matrix/Spectrum.lean`).
- `CFC.rpow` / `CFC.nnrpow` / `CFC.sqrt` and the `Pow A ℝ` instance
  (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`, built this session) —
  gives `(Qₙ x) ^ (1/(2n) : ℝ)` as a CFC element on a PSD matrix.
- `Filter.Tendsto.cfc` (`CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean:261`) — continuity
  of `a ↦ cfc f a` in the operator. **CAVEAT (verified):** its proof routes through
  `continuousOn_cfc`, which needs `IsometricContinuousFunctionalCalculus ℝ (Matrix..ℝ)` — the very
  instance the v2 plan proved does NOT synthesize for real matrices. So this lemma is NOT directly
  usable on `Matrix .. ℝ`; for projection convergence (§3.3 / lemma 7) use the polynomial-bypass
  continuity argument (per-`n` interpolating polynomial + `aeval` continuity) or convergence of
  `eigenvalues`/`eigenvectorBasis` directly. Treat `Filter.Tendsto.cfc` as motivation, not API.
- `LinearMap.singularValues` (`Analysis/InnerProductSpace/SingularValues.lean`, NEW 2026) —
  `singularValues = √(eigenvalues (adjoint ∘ self))`, `Antitone`, `support`-finite. Directly models
  the singular values of `A⁽ⁿ⁾` and their connection to `Qₙ`'s eigenvalues.
- `exteriorPower.map` (`LinearAlgebra/ExteriorPower/Basic.lean:258`), `map_comp`, `map_id`,
  `finrank_eq`, `instFinite`, `Basis` — the functor `⋀^k` on linear maps (for the Raghunathan route).
- `Matrix.instStarOrderedRing` (`Analysis/Matrix/Order.lean:104`, scoped `MatrixOrder`) — PSD = `0 ≤ ·`.
- `measurable_of_tendsto_metrizable`, `tendsto_pi_nhds`, `measurable_cocycle`, the committed
  `measurable_cfc_eqOn_polynomial`, `measurable_aeval_matrix`, `measurable_matrix_pow`.

MISSING from Mathlib (must be BUILT — see §3 sub-projects):
- **No operator norm / inner product on `⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))`.** Exterior powers are
  bare modules. The Raghunathan route needs `‖⋀^k f‖ = ∏_{i<k} σᵢ(f)` and submultiplicativity,
  which requires putting an inner product on `⋀^k` first. (grep: zero `InnerProductSpace`/`Norm`
  instances on `exteriorPower`.)
- **No matrix `rpow`/`sqrt` as a `Matrix`-specific object** (only generic CFC `rpow`). Fine — the
  generic `Pow (Matrix..) ℝ` from CFC suffices.
- **No SVD-as-decomposition** (`A = U Σ Vᵀ`) and **no eigenspace-convergence lemma**. This is the
  true gap (§3.3).

## 3. The analytic core: existence of `Λ` (the make-or-break MATH)

`Λ x := lim_{n} (Qₙ x) ^ (1/(2n) : ℝ)`, `Qₙ x = (cocycle A T n x)ᵀ (cocycle A T n x)`, the limit
taken in `Matrix (Fin d) (Fin d) ℝ` (equivalently, in operator norm — finite-dim, so all norms and
the Pi topology agree; `Matrix` over ℝ is a complete f.d. normed space). Hermitian PSD for each `n`
(`isHermitian_gram`, spike). The limit exists a.e. and is Hermitian PSD with eigenvalues `e^{lam i}`.

This decomposes into two independent obligations, in increasing difficulty:

### 3.1 Scalar layer — singular-value / eigenvalue convergence (the "diagonal" of `Λ`) — HARD but standard

CLAIM: for each `i`, `(1/n) log σᵢ(A⁽ⁿ⁾(x)) → lam i` a.e. (a genuine limit), where `σᵢ` is the
`i`-th singular value (descending), and `lam` is a.e. constant under ergodicity. Equivalently
`(1/(2n)) log (i-th eigenvalue of Qₙ x) → lam i`.

CLEANEST LEAN ROUTE — **Raghunathan via exterior powers + Kingman on each `⋀^k`**:
- The product of the top `k` singular values is `σ₁⋯σ_k(A⁽ⁿ⁾) = ‖⋀^k (A⁽ⁿ⁾)‖` (operator norm of the
  `k`-th exterior power). `n ↦ log‖⋀^k(cocycle A T n x)‖` is **subadditive** (because
  `⋀^k` is a functor: `⋀^k(MN) = ⋀^k M · ⋀^k N` via `exteriorPower.map_comp`, and operator norm is
  submultiplicative). Apply the already-proven `tendsto_kingman_ergodic` to get a genuine limit
  `Γ_k = lim (1/n) log‖⋀^k(A⁽ⁿ⁾)‖` a.e. (constant). Then `lam_1 + ⋯ + lam_k = Γ_k`, and the
  individual `lam i = Γ_i − Γ_{i-1}` — singular values converge by differencing.
- This REUSES the project's two engines (Kingman + the FK plumbing pattern) and needs NO new
  convergence theorem — the convergence is Kingman's. **The only new analytic content is the
  exterior-power operator-norm identity.**

NEW MATHLIB SUB-PROJECT A (exterior-power operator norm): put an inner product on
`⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))` (the induced Gram/Hodge inner product on decomposables
`⟨v₁∧⋯∧v_k, w₁∧⋯∧w_k⟩ = det(⟨vᵢ,wⱼ⟩)`), prove `⋀^k f` is bounded with
`‖⋀^k f‖ = ∏_{i<k} σᵢ(f)`, and `⋀^k(g∘f) = ⋀^k g ∘ ⋀^k f` (have `map_comp`) is norm-submultiplicative.
COST: **substantial, 3–5 sessions**; this is a genuine Mathlib contribution. The inner product
construction is the bulk; the `‖⋀^k f‖ = ∏σᵢ` identity follows from the SVD of `f` diagonalizing
`⋀^k f` on the induced o.n. basis of `k`-fold wedges of singular vectors (use the new
`LinearMap.singularValues` + `Matrix.IsHermitian.eigenvectorBasis`).
ALTERNATIVE (cheaper, avoids exterior powers): work directly with eigenvalues of `Qₙ` via
Courant–Fischer min-max (`Analysis/InnerProductSpace/Rayleigh.lean`) to show
`λ_k(Q_{m+n}) ≤ ‖·‖²·λ_k(...)` style submultiplicativity of the *product* of top-k eigenvalues —
but the product-of-eigenvalues submultiplicativity is exactly the exterior-power statement in
disguise (`∏_{i≤k} λᵢ(M) = ‖⋀^k‖²`), so Sub-project A is essentially unavoidable for a clean proof.

### 3.2 Eigenvalue → `lam`, and `StrictAnti` — EASY given 3.1

Group equal limits: the distinct values among `{lam i}` are `lam_distinct : Fin k → ℝ`,
`StrictAnti`, `k ≤ d`. `k` and `lam_distinct` are a.e. constant (Kingman limits are constant under
ergodicity). This matches `specCard`/`specList` of the committed `Filtration.lean` once §3.4 is done.

### 3.3 Eigenspace / projection convergence — THE TRUE CRUX — HARDEST

CLAIM: `(Qₙ x)^{1/(2n)} → Λ x` *as matrices* (not just eigenvalues), and the spectral projection of
`Λ x` onto the span of eigenvalues `≥ e^{lam i}` equals the Oseledets subspace. Eigenvalue
convergence (§3.1) does NOT imply matrix convergence — the eigenSPACES must converge too. This is
the part of Oseledets that is *not* a soft consequence of Kingman; it is the genuine "regularity"
content. Classical proofs (Ruelle, Raghunathan, Walters §10):
- Show the eigenprojections `P_n^{(i)}` of `Qₙ^{1/(2n)}` form a Cauchy sequence in operator norm,
  using the SPECTRAL GAP: between strata `i` and `i+1` the eigenvalue ratio is `e^{(lam i − lam_{i+1})·2n} → ∞`,
  and a perturbation/`sin Θ` (Davis–Kahan-type) bound forces the projections to converge geometrically.
- Mathlib has NO Davis–Kahan / `sin Θ` theorem and no eigenprojection-perturbation API. **This must
  be built**, or replaced by a from-scratch Cauchy argument specific to the gapped self-adjoint
  setting.
COST: **4–8 sessions, highest risk.** This is where Route II's "analytic core" really lives.

NOTE on what we actually NEED: for the TARGET we do not strictly need full matrix convergence of
`Qₙ^{1/(2n)}`; we need (a) the limit `Λ` to EXIST (for the CFC projections / measurability), and
(b) the genuine forward limit `lim (1/n)log‖A⁽ⁿ⁾ v‖ = lam i` on each stratum. (b) can be obtained
*without* projection convergence if we instead run the limsup→lim upgrade — see §5 fallback. So
§3.3 is the price of making `Λ` the literal limit object; if it proves too costly, define `Λ`
differently (§5).

### 3.4 Bridge `Vᵢ = lambdaSublevel A T x (lam i)` a.e. — REQUIRED regardless, MEDIUM-HARD

Identify the concrete `Λ`-eigenspace flag with the committed limsup flag `Vflag`/`lambdaSublevel`.
This is the "abstract = concrete" obligation #8 of the v2 plan. With §3.1+§3.3 in hand it is:
`v ∈ (i-th Λ-eigenspace-sum) ↔ limsup (1/n)log‖A⁽ⁿ⁾ v‖ ≤ lam i`, both equal to the SVD growth rate
of `v`. MEDIUM-HARD; it is the lemma that lets the committed `Filtration.lean` results
(`Vflag_strictAnti`, `Vflag_equivariant`, `lambdaBar_eq_on_stratum`) be reused verbatim for the
final `V`.

## 4. Module plan: re-scope `Subbundle`/`Limit` → a single `OseledetsLimit` module

Replace the two planned modules `Lyapunov/Subbundle.lean` and `Lyapunov/Limit.lean` with:

`Oseledets/Lyapunov/ExteriorNorm.lean` (NEW Mathlib-style infra, Sub-project A) — imported before:
`Oseledets/Lyapunov/OseledetsLimit.lean` (the analytic core + assembly).

Plus, if Sub-project A is split out for upstreaming, `ExteriorNorm` may be a candidate Mathlib PR.

### Ordered lemmas for `OseledetsLimit.lean` (signatures abbreviated; `X,d,μ,T` as in repo)

1. `gram (A T n x) : Matrix … := (cocycle A T n x)ᵀ * (cocycle A T n x)` + `measurable_gram`,
   `posSemidef_gram`, `isHermitian_gram`. **DONE in spike** (move in). LOW.
2. `exteriorGrowth A T k : ℕ → X → ℝ := fun n x => Real.log ‖exteriorPower.map k (toEuclideanLin (cocycle A T n x))‖`.
   `isSubadditiveCocycle_exteriorGrowth` via `exteriorPower.map_comp` + submultiplicative norm
   (needs ExteriorNorm). MEDIUM (given ExteriorNorm).
3. `tendsto_exteriorGrowth (Kingman) : ∃ Γ : Fin (d+1) → ℝ, ∀ k, ∀ᵐ x, (1/n) exteriorGrowth..k → Γ k`.
   Apply `tendsto_kingman_ergodic` per `k` (exactly the FK pattern; reuse `det_cocycle_ne_zero`,
   integrability via `‖⋀^k‖ ≤ ‖·‖^k`). MEDIUM. [HARD analytic input lives in ExteriorNorm, not here.]
4. `lamSing A T : Fin d → ℝ := fun i => Γ (i+1) − Γ i` (singular-value exponents, descending) +
   `tendsto_singularValue_log`. MEDIUM. **[scalar layer DONE here, §3.1]**
5. `oseledetsLimit Λ : X → Matrix …` + `tendsto_qpow_oseledetsLimit : ∀ᵐ x, Tendsto (fun n => (gram..n x)^(1/(2n)) ) atTop (𝓝 (Λ x))`. **HARDEST (§3.3)**. Mark `-- HARD`.
6. `measurable_oseledetsLimit : Measurable Λ` — from 5 + `measurable_of_pointwise_limit` (spike) +
   `measurable_gram` + measurability of the CFC `rpow` approximant (the `Pow .. ℝ` is `cfc`, so use
   `measurable_cfc_eqOn_polynomial` with a per-`n` interpolating polynomial, OR `Filter.Tendsto.cfc`
   continuity composed with measurability). LOW-MEDIUM (spike shows the shape).
7. `oseledetsLimit_isHermitian`, `..posSemidef`, `eigenvalues_oseledetsLimit : eigenvalues (Λ x) = e^{lamSing..}`.
   From 5 + `Filter.Tendsto.cfc` continuity of eigenvalues / `Tendsto`. MEDIUM.
8. `V i x := ⨆ (eigenspaces of Λ x with eigenvalue ≥ e^{lam i})`, concretely
   `LinearMap.range (toEuclideanCLM (cfc gᵢ (Λ x)))` with `gᵢ` the gap function. Plus
   `orthProjMatrix_V_eq_cfc` (the §1 collapse of v2) and `measurableSubspace_V` (v2 §4 ladder, the
   gap-polynomial interpolation). MEDIUM-HIGH (v2 plan; measurability crux DONE).
9. `V_ae_eq_lambdaSublevel : ∀ᵐ x, ∀ i, V i x = lambdaSublevel A T x (lam i)` (§3.4 bridge).
   MEDIUM-HARD. **This is the hinge that imports all committed `Filtration.lean` structure.**
10. `tendsto_log_norm_on_stratum` (exact growth, genuine limit) — for `v` in stratum `i`,
    `(1/n)log‖A⁽ⁿ⁾ v‖ → lam i`, from the SVD (§3.1) + the eigenspace decomposition of `v` against
    `Λ` (§3.3) projecting `v` onto the `≥ e^{lam i}` block. MEDIUM (given 5,7,8).

### Assembly of the TARGET `oseledets_filtration` (which lemma supplies each conjunct)

- `k`, `lam : Fin k → ℝ`: distinct values of `lamSing` (4), a.e. constant — `= specList`/`specCard`
  via the bridge (9), or directly from grouped `Γ`-differences. **`StrictAnti lam`**: descending by
  construction of `Γ`-differences / `eigenvalues₀_antitone`.
- `V : Fin (k+1) → X → Submodule …`: the concrete `V i` of (8) (junk `⊥` off the a.e. good set).
- `∀ i, MeasurableSubspace (V i)`: `measurableSubspace_V` (8) — the **already-compiled** CFC crux is
  the load-bearing step.
- a.e. `V 0 = ⊤`, `V (last) = ⊥`, strict decrease, equivariance: via the bridge (9) +
  the committed `Vflag_zero`/`Vflag_last`/`Vflag_strictAnti`/`Vflag_equivariant` of `Filtration.lean`
  (these are why we KEEP the limsup flag layer).
- exact growth `(1/n)log‖A⁽ⁿ⁾ v‖ → lam i`: `tendsto_log_norm_on_stratum` (10). This is the conjunct
  that under Route I needed the entire §5–6 block-triangular induction; under Route II it is a
  direct SVD read-off.

## 5. Fallback if §3.3 (eigenspace convergence) proves too costly

Keep `Λ` as a DEFINED object via the scalar limit only, and recover the exact-growth conjunct (10)
**without** matrix convergence of `Qₙ^{1/(2n)}`, by the limsup→lim upgrade. Two sub-options:
- (5a) Resurrect ONLY `lyapunov-to-target.md` §5.2 ("extremes on an invariant subbundle are genuine
  limits", FK applied to the trivialized sub-cocycle) + §6 induction for the growth rates, and use
  `Λ` solely for measurability (the v2 original division of labor). This is Route I, and is the
  documented fallback. Cost: the §5–6 block-triangular induction (Bochi Lemma 12/13) — itself
  3–5 hard sessions, but uses NO missing Mathlib infra.
- (5b) Define `Λ` directly as `cfc (interpolating-step) ...` of a *single* limit object obtained from
  the Γ-limits and the (separately proven) projection convergence restricted to what (10) needs.

**Recommendation:** attempt §3.1 (exterior/Kingman scalar layer) FIRST — it is the highest-value,
reuses Kingman, and is needed in every route. Then attempt §3.3; if it stalls, fall to (5a) for the
growth rates while retaining the §3.1 scalar exponents and the CFC measurability. Do NOT delete
`lyapunov-to-target.md` §5–6 from the repo docs — demote it to "Route I fallback."

## 6. Build-order change vs `lyapunov-to-target.md` §8

OLD: `… Filtration → Measurable → Subbundle → Limit → assemble`.
NEW:
`Ultrametric → GrowthFunction → Filtration → Measurable` (all committed) →
`ExteriorNorm` (new infra; no dynamics) →
`OseledetsLimit` (analytic core + bridge + assemble) → `MultiplicativeErgodic`.
`Subbundle`/`Limit` are NOT created; their content is either subsumed by `OseledetsLimit` (growth
rates via SVD) or demoted to the Route I fallback doc.

## 7. Confidence rating and riskiest lemmas

Overall confidence the endgame is completable as planned: **MEDIUM**. The measurability spine is
DONE/compiled (HIGH). The scalar exponent layer (§3.1) is HIGH-confidence-but-laborious (Kingman is
already done; only ExteriorNorm is new). The riskiest two lemmas:

1. **`tendsto_qpow_oseledetsLimit` (§3.3, lemma 5) — eigenspace/projection convergence.** No Mathlib
   Davis–Kahan / eigenprojection-perturbation API; must build a gapped-self-adjoint Cauchy argument.
   **HIGHEST RISK.** Mitigation: the §5 fallback (Route I growth rates) removes the dependency of the
   TARGET on full matrix convergence, leaving §3.3 needed only to *define* `Λ` as a literal limit.
2. **`ExteriorNorm` Sub-project A (§3.1) — inner product + operator norm `‖⋀^k f‖ = ∏σᵢ` on
   `exteriorPower`.** Genuinely missing from Mathlib; the construction (Hodge inner product on
   decomposables, well-definedness via the alternating universal property) is delicate. MEDIUM-HIGH
   risk, but standard and upstreamable.

Everything else (Gram measurability, CFC crux, the committed L4 flag, the assembly glue,
`StrictAnti`, `⊤`/`⊥`, equivariance) is LOW-to-MEDIUM and largely in hand.
