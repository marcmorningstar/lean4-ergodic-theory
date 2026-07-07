# Oseledets L7c — de-risking scout: route decision + sub-lemma ladder

> Bounded scouting pass, 2026-06-07. De-risks **L7c**, the single irreducible hard node of the MET
> formalization: a.e. convergence of the self-adjoint matrix sequence `qpow A T n x = (Qₙ)^{1/(2n)}`
> (eigenvalues already converge by the committed `eigenvalues_qpow_tendsto`; the content is that the
> eigenSPACES / block spectral projectors converge, pinned by the growing spectral gaps). NOT an
> implementation; produces a verified route decision and a risk-tagged ladder. Compiled probes
> (all `lake env lean`, repo root): `scratch_l7c_cx_instances.lean` (compiled, reports expected
> synth failures), `scratch_l7c_projector.lean` (compiled, exit 0), `scratch_l7c_cstar_check.lean`
> (blocked by a missing cache `.olean`, source-confirmed only) — this scout — plus the pre-existing
> `scratch_l7_*.lean`.
> Refines `oseledets-l7-crux.md` §B.1/§C/§E. Corrects two stale claims (see §F surprises). Does not
> modify committed library files.

## A. Recommended route — VERDICT

**Route 1 (direct relative-gap projector-Cauchy bound, on PLAIN real matrices), built from scratch.**

The crux is to prove, for `μ`-a.e. `x`, that `qpow A T n x` is a Cauchy sequence in the
finite-dimensional matrix metric, hence converges (the committed `L7_statement`). The mechanism:

1. Group eigenvalue indices by **distinct** limit exponents `e^{λ₁} > … > e^{λ_p}` (the committed
   `specList`/`specCard` enumerate distinct exponents descending). NEVER per singular-value index —
   see §F.
2. For each gap `j` (between distinct `λⱼ > λⱼ₊₁`) pick a threshold `cⱼ` strictly between `e^{λⱼ}`
   and `e^{λⱼ₊₁}`. Let `Πₙ⁽ʲ⁾` be the orthogonal projector of `qpow_n` onto eigenvalues `> cⱼ`.
3. **The new infra (L7c):** `{Πₙ⁽ʲ⁾}ₙ` is Cauchy in operator norm, by a *relative-gap angle bound*
   on the top-`j` right-singular subspaces of consecutive iterates `Mₙ = A⁽ⁿ⁾`, `Mₙ₊₁ = A(Tⁿx)·Mₙ`.
4. `Matrix (Fin d) (Fin d) ℝ` is complete (`scratch_l7_cauchy.lean` D), so each `Πₙ⁽ʲ⁾ → P⁽ʲ⁾`;
   assemble `Λ := Σⱼ e^{λⱼ}·(P⁽ʲ⁾ − P⁽ʲ⁺¹⁾)` and show `qpow_n → Λ` from projector + eigenvalue limits.

**Why the projectors can be DEFINED with the bare real CFC (no isometric instance):** the cutoff
projector `Πₙ⁽ʲ⁾ = cfc χⱼ (qpow_n)` for a continuous cutoff `χⱼ` (1 above `cⱼ`, 0 below) equals, via
`cfc_congr` on the *finite* spectrum, the cfc of the exact 0/1 indicator — an idempotent self-adjoint
matrix = the orthogonal block projector. The bare `Matrix.IsHermitian.instContinuousFunctionalCalculus
ℝ` (FOUND) suffices for `cfc`, `cfc_congr`, `cfc_mul`, `cfc_predicate`; all of P1/P2/P3 below compiled
on PLAIN `Matrix _ _ ℝ` (`scratch_l7c_projector.lean`). The CFC explicit formula
`Matrix.IsHermitian.cfc f A = U · diag(f∘eigenvalues) · Uᴴ` makes the projector concrete.

### Why the other routes lose

- **Route 2 (continuous-cutoff CFC projector relying on continuity-in-operator / `Filter.Tendsto.cfc`):
  BLOCKED, and even its complexification escape is now refuted (§C, §F SURPRISE 1).** The
  operator-variable continuity lemmas (`continuousOn_cfc`, `Filter.Tendsto.cfc`,
  `lipschitzOnWith_cfc_fun`) live in the `RCLike` section and require
  `[IsometricContinuousFunctionalCalculus 𝕜 A IsSelfAdjoint]`, which needs `[CStarAlgebra A]`. This
  instance does NOT synthesize for plain `Matrix n n ℝ` (pinned, `scratch_l7_cfc_synth.lean`) **nor for
  `Matrix n n ℂ`** — `CStarAlgebra (Matrix n n ℂ)` FAILS to synthesize (compiled,
  `scratch_l7c_cx_instances.lean`). The proper `CStarAlgebra` lives only on the type-synonym wrapper
  `CStarMatrix n n ℂ` (Mathlib `CStarMatrix.lean:816`, `instCStarAlgebra`; isometric ℝ-CFC available
  there — `scratch_l7c_cstar_check.lean`). So Route 2 would require porting the entire committed
  `qpow`/`gram` construction off plain `Matrix ℝ` onto `CStarMatrix _ _ ℂ`, with real↔complex↔wrapper
  transfer lemmas — a major refactor. **And it would not even shrink the crux:** continuity-in-operator
  only TRANSFERS convergence; it cannot CREATE the convergence of `qpow_n` (it requires an
  already-convergent operator sequence as input). See §F SURPRISE 2.
- **Route 3 (Riesz/holomorphic contour projector `(1/2πi)∮(z−A)⁻¹dz`): REJECT.** Needs complexification
  (same wrapper problem) + contour integration of the resolvent over ℂ. Mathlib has `resolvent`/
  `resolventSet`/`isOpen_resolventSet` but no spectral-projection-by-contour, no `spectralProjection`,
  no Riesz functional calculus producing band projectors (grep: absent, §C). Heaviest route; the
  contour estimate is itself the same relative-gap content dressed in analytic machinery.
- **Route 4 (cheaper device): NONE found.** The projective-measure / growth-dichotomy proof (Filip
  notes Lemma 2.3.1; Chicago REU; = blueprint "Route I") avoids the matrix limit but needs the
  filtration measurable+equivariant first — relocating the dependency at comparable cost, and it does
  NOT discharge the committed `L7_statement` (which literally asserts `Tendsto (qpow…) (𝓝 (Λ x))`). A
  direct `qpow_n` Cauchy via "`‖log H_{n+1} − log H_n‖` summable" is FALSE (eigenvectors rotate; §F
  counterexample). No subadditive/monotone matrix trick yields `qpow_n` Cauchy without the gap content.

## B. Precise Lean statement(s) of the new infra to build (per distinct-λ)

The crux factors into one ABSTRACT self-adjoint lemma + one COCYCLE-specific gap input. State per
distinct exponent / per gap.

### B.1 The abstract gapped-projector-Cauchy lemma (the irreducible new infra)

```lean
open scoped Matrix.Norms.L2Operator in
/-- Abstract crux. A sequence of self-adjoint matrices whose spectrum splits, for `n` large, into a
top block `> c` and a bottom block `< c` with the projector increments summable, has a convergent
band projector. Stated for the cutoff CFC `Πₙ = cfc χ Hₙ` of a fixed continuous 0/1 cutoff `χ` at
`c`. -/
theorem cauchySeq_bandProjector
    {d : ℕ} (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (hH : ∀ n, IsSelfAdjoint (H n))
    (χ : ℝ → ℝ) (hχ : Continuous χ) (c : ℝ)
    -- eventually `c` lies in a spectral gap of `Hₙ`, with χ = the exact 0/1 indicator there:
    (hgap : ∀ᶠ n in atTop, (spectrum ℝ (H n)).EqOn χ (Set.indicator (Set.Ioi c) 1))
    -- the geometric (relative-gap) increment bound that makes the projectors Cauchy:
    (hsum : Summable (fun n => ‖cfc χ (H (n+1)) - cfc χ (H n)‖)) :
    CauchySeq (fun n => cfc χ (H n))
```
The real mathematical weight is `hsum`; this lemma is the *packaging* (Cauchy from summable
increments + completeness, via `cauchySeq_of_summable_dist` or `cauchySeq_finset` telescoping). LOW
once `hsum` is supplied.

### B.2 The relative-gap angle bound that DISCHARGES `hsum` (the genuine §3.3 content)

```lean
/-- The single-step angle bound. Let `Mₙ = A⁽ⁿ⁾x` and `Mₙ₊₁ = A(Tⁿx)·Mₙ`. The orthogonal projector
`Πₙ⁽ʲ⁾` onto the top-`j` right-singular subspace of `Mₙ` (= eigenspace of `Qₙ` for the top-`j`
eigenvalues) moves between `n` and `n+1` by at most the RELATIVE gap times the one-step distortion:
`‖Πₙ₊₁⁽ʲ⁾ − Πₙ⁽ʲ⁾‖ ≤ Cⱼ · ‖A(Tⁿx)‖ · ‖A(Tⁿx)⁻¹‖ · σⱼ₊₁(Mₙ)/σⱼ(Mₙ)`.
(`Cⱼ` an absolute constant; this is the multiplicative/relative Davis–Kahan sin-Θ bound for singular
subspaces under an invertible left perturbation.) -/
theorem norm_bandProjector_succ_sub_le
    {d : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (j : ℕ) (n : ℕ) (x : X) :
    ‖Πj A T (n+1) x - Πj A T n x‖
      ≤ Cj * ‖A (T^[n] x)‖ * ‖(A (T^[n] x))⁻¹‖
          * (Matrix.toEuclideanLin (cocycle A T n x)).singularValues (j+1)
          / (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j
```
Combined with the committed scalar layer: `(1/n)·log(σⱼ₊₁/σⱼ) → λⱼ₊₁ − λⱼ < 0`
(`tendsto_log_singularValue`, two indices, distinct exponents) and the tempered one-step factor
`(1/n)·log(‖A(Tⁿx)‖‖A⁻¹‖) → 0` a.e. (Birkhoff / `IntegrableLogNorm`, already in the FK plumbing),
the RHS is eventually `≤ e^{−cn}`, hence `hsum` holds a.e. This is **the irreducible piece** and is
entirely absent from Mathlib (no Davis–Kahan, no sin-Θ, no singular-subspace perturbation; §C).

### B.3 Assembly (`L7c → L7d`)

```lean
/-- For a.e. `x`, `qpow A T n x` converges. -/
theorem cauchySeq_qpow {A} (hA : ∀ x, (A x).det ≠ 0) … :
    ∀ᵐ x ∂μ, CauchySeq (fun n => qpow A T n x)
-- assemble qpow_n = Σⱼ (eigenvalue on block j)·Πₙ⁽ʲ⁾ ; each Πₙ⁽ʲ⁾ Cauchy (B.1+B.2),
-- each block eigenvalue → e^{λⱼ} (committed eigenvalues_qpow_tendsto); products/sums of
-- Cauchy/convergent sequences are Cauchy.

theorem L7d {A} … : L7_statement μ T A   -- via cauchySeq_tendsto_of_complete (probe E)
```

## C. Mathlib API: found vs missing (independent verification, this scout)

**FOUND (compiled against, plain real matrices unless noted):**
- `Matrix.IsHermitian.instContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint` — the BARE
  (non-isometric) CFC instance. Sufficient to DEFINE the projectors.
- `cfc_congr : (spectrum ℝ a).EqOn f g → cfc f a = cfc g a` (`…/Unital.lean:417`). Compiled, P1.
  This is the bridge continuous-cutoff → exact indicator on the finite matrix spectrum, and the same
  device the committed `measurable_cfc_eqOn_polynomial` uses.
- `cfc_mul`, `cfc_predicate` (idempotent + self-adjoint of the cutoff cfc = orthogonal projector).
  Compiled, P2a/P2b/P2c.
- `Matrix.IsHermitian.cfc` explicit triple-product formula `U · diag(f∘eigenvalues) · Uᴴ`
  (`HermitianFunctionalCalculus.lean:132`) + `cfc_eq`; `eigenvectorUnitary`, `spectral_theorem`,
  `eigenvalues₀`/`eigenvalues₀_antitone`, `spectrum_real_eq_range_eigenvalues` (`Matrix/Spectrum.lean`).
- `CompleteSpace (Matrix _ _ ℝ)`, `cauchySeq_tendsto_of_complete` (probes D/E). Compiled, P3.
- `Submodule.orthogonalProjection` (CLM), `orthogonalProjection_eq_sum_rankOne` (`PiL2.lean`) — to
  describe block projectors concretely if needed.
- `CStarAlgebra (CStarMatrix n n ℂ)` + isometric ℝ-CFC ON THE WRAPPER (`CStarMatrix.lean:816`) —
  available, but only for the wrapper type, not plain matrices (so not used by Route 1).
- Committed scalar layer: `tendsto_log_singularValue`, `sigma_le_opNorm`, `inv_opNorm_inv_le_sigma`,
  `singularValues_cocycle_pos`, `eigenvalues_qpow_tendsto`, `eigenvalues₀_qpow_eq`.

**MISSING (must be BUILT; upstreamable):**
- **M-2′ — singular-subspace / eigenprojection perturbation (Davis–Kahan / sin-Θ), RELATIVE form.**
  CONFIRMED ABSENT: no `davis`/`kahan`, no sin-Θ spectral object, no eigenvalue/eigenvector
  continuity, no subspace-angle-perturbation, no singular-subspace distance, no `spectralProjection`/
  Riesz contour projector (grep over all Mathlib). `Matrix/Gershgorin.lean` gives only eigenvalue
  *localization*, not projector perturbation. **This is the irreducible §3.3 gap = B.2.**
- **M-3 — the assembled gapped matrix-limit (`qpow_n → Λ`) = `cauchySeq_qpow` + `L7d`.** Absent;
  built from B.1+B.2.
- (Confirmed) **M-2 — operator-variable CFC continuity unusable on the committed type.** Both real and
  complex plain matrices lack `CStarAlgebra`/isometric CFC; only the `CStarMatrix` wrapper has it.

## D. Compiled micro-steps (this scout) vs UNVERIFIED

| Probe file | Claim | Status |
|---|---|---|
| `scratch_l7c_cx_instances.lean` | `CStarAlgebra (Matrix n n ℂ)` and isometric ℝ-CFC for `Matrix n n ℂ` FAIL to synthesize (SURPRISE 1) | **COMPILED — reports the two `synthInstanceFailed` (exit 1 expected; READ the output)** |
| `scratch_l7c_projector.lean` | P1 `cfc_congr`; P2a `cfc_predicate`; P2b `cfc_mul`; P2c idempotent cutoff ⇒ projector; P3 completeness — all on PLAIN `Matrix _ _ ℝ` (bare CFC) | **COMPILED (exit 0, only unused-var warnings)** |
| `scratch_l7c_cstar_check.lean` | The wrapper `CStarMatrix n n ℂ` has `CStarAlgebra` + isometric ℝ-CFC | **NOT compile-verified here** — `CStarMatrix.olean` absent from the local cache (no `lake exe cache get` per directive); claim is SOURCE-confirmed at `Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:816` (`instance instCStarAlgebra : CStarAlgebra (CStarMatrix n n A)`) but UNVERIFIED by compile |

**UNVERIFIED (asserted, not compiled — these ARE the L7c work):**
- B.2 the relative-gap single-step angle bound `norm_bandProjector_succ_sub_le`. No probe; this is the
  new theorem to prove. The numeric form of the constant `Cⱼ` and whether the bound is best stated via
  `‖Π‖`-difference vs `sin∠` is to be settled during implementation.
- B.1 `hsum`-from-scalar-layer (needs B.2 + the tempered one-step factor a.e.).
- B.3 assembly and `Λ` Hermitian-PD eigen-data.

## E. Risk-tagged sorry-free sub-lemma ladder (L7c → L7d)

Build inside `OseledetsLimit.lean` (or a new `OseledetsProjector.lean`). All on PLAIN
`Matrix (Fin d) (Fin d) ℝ`; bare CFC instance only.

| # | Lemma (abbrev.) | Risk | Effort | Notes |
|---|---|---|---|---|
| L7c.0 | `bandProjector A T j n x := cfc χⱼ (qpow_n)`; self-adjoint + idempotent on the good set (`cfc_predicate`,`cfc_mul`,`cfc_congr`) | **LOW (probe-backed)** | <0.5 sess | P1/P2 compiled |
| L7c.1 | `bandProjector = Πⱼ`(top-`j` eigenprojector of `Qₙ`): range/eigenvalue identification via explicit `IsHermitian.cfc` formula | MED | 1 sess | `eigenvectorUnitary`,`spectrum_real_eq_range_eigenvalues` |
| L7c.2 | one-step factor a.e.: `(1/n)·log(‖A(Tⁿx)‖‖A⁻¹‖) → 0` | LOW–MED | 0.5–1 sess | Birkhoff over `IntegrableLogNorm`; FK plumbing exists |
| L7c.3 | **relative-gap angle bound B.2 (`norm_bandProjector_succ_sub_le`)** | **HIGH (CRUX, NEW — M-2′)** | 4–8 sess | Davis–Kahan sin-Θ for singular subspaces, invertible-left perturbation; absent from Mathlib; the irreducible piece |
| L7c.4 | `hsum` a.e.: RHS of B.2 eventually `≤ e^{−cn}`, summable | MED | 1 sess | L7c.2 + L7c.3 + `tendsto_log_singularValue` (two indices) |
| L7c.5 | `cauchySeq_bandProjector` (B.1 packaging): Cauchy from summable increments + completeness | LOW–MED | 0.5–1 sess | `cauchySeq_of_summable_dist`/telescoping; probe D/E |
| L7d | `cauchySeq_qpow` ⇒ `L7_statement` (assemble blocks×eigenvalues; `cauchySeq_tendsto_of_complete`) | MED | 1–1.5 sess | needs L7c.1/4/5 + committed `eigenvalues_qpow_tendsto` |

**Critical path: L7c.3 → L7c.4 → L7c.5 → L7d.** The single irreducible new-infra node is **L7c.3**
(the relative-gap singular-subspace angle bound). Everything else is LOW/MED or probe-backed.
Net estimate for L7c→L7d: ~8–14 sessions, dominated by L7c.3.

## F. Counterexamples / pitfalls found

- **SURPRISE 1 (route-doc correction).** `oseledets-l7-crux.md` §F speculated the isometric ℝ-CFC fails
  for real matrices because of the "scoped L2 norm / missing real CStarAlgebra ℝ-structure". The
  sharper truth: the bundled **`CStarAlgebra` class is registered on NEITHER `Matrix n n ℝ` NOR
  `Matrix n n ℂ`** under the scoped L2 norm — only on the dedicated wrapper `CStarMatrix n n A`
  (`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:816`). So complexification does NOT rescue Route 2
  on the committed type; one would have to refactor onto `CStarMatrix _ _ ℂ`. Compiled:
  `scratch_l7c_cx_instances.lean` (both fail), `scratch_l7c_cstar_check.lean` (wrapper succeeds).
- **SURPRISE 2 (architecture).** Even granting the isometric instance, `Filter.Tendsto.cfc` /
  `continuousOn_cfc` only TRANSFER convergence (input: a convergent operator sequence). They CANNOT
  produce the convergence of `qpow_n` — that is exactly the unknown. So no continuity-of-cfc lemma,
  however obtained, discharges the crux; the from-scratch relative-gap estimate (B.2) is unavoidable
  on every route. This re-confirms `oseledets-l7-crux.md`'s "M-2 unusable" verdict for a deeper reason
  than stated.
- **Eigenvector rotation under equal eigenvalues (the core counterexample).** Eigenvalue convergence
  of `qpow_n` does NOT imply matrix convergence: take `Hₙ = Rₙ diag(1,1) Rₙᵀ = I` — trivial — but with
  `diag(1, 1+1/n)` and `Rₙ` an angle-`θₙ` rotation that does not converge, the eigenVALUES converge
  (→1,1) while the top eigenVECTOR `Rₙe₁` need not. What forbids this in our setting is a GENUINE gap
  `e^{λⱼ} > e^{λⱼ₊₁}` (strict) plus the relative-gap bound B.2; with a real gap the top-`j`
  *eigenspace* is pinned. This is precisely why a naive "`‖log Hₙ₊₁ − log Hₙ‖` summable" claim is FALSE
  and why B.2 (not eigenvalue convergence) is the crux.
- **Per-distinct-λ, NEVER per-singular-value-index.** When a distinct exponent has multiplicity > 1,
  the individual eigenprojector inside the cluster is NOT Cauchy (eigenvectors rotate WITHIN the equal
  block); only the SUMMED block projector over a maximal gap-separated cluster is. State B.1/B.2/L7c
  per gap `cⱼ` between DISTINCT exponents (consistent with the committed `specList`/`specCard`). A
  per-index projector statement would be FALSE for multiplicity > 1.
- **Degenerate equal-exponent strata / `k>d`.** Across a non-gap (consecutive equal exponents) there is
  no threshold `cⱼ`; the ladder must skip to the next DISTINCT exponent. For the one-sided invertible
  cocycle (`det ≠ 0`), `Qₙ` is PD throughout, all `σᵢ > 0`, `e^{λᵢ} > 0`; no zero-eigenvalue
  degeneracy. The number of gaps is `specCard − 1`. Safe.
- **No counterexample to any committed statement.** The committed scalar/eigenvalue layer and
  `L7_statement` remain sound; the corrections are about the M-2/complexification route only.

## G. Crux L7c.3 — verified proof route (de-risking pass 2, 2026-06-07)

> Adversarial re-audit of §A/§B/§E, hunting the CHEAPEST correct route for the increment bound.
> Worked the inequality out on paper, verified its truth + direction + constant numerically (Python,
> thousands of random ill-conditioned cases), and COMPILED the load-bearing Lean facts in four new
> probes `scratch_l7c3_{index,rayleigh,assembly,sintheta}.lean` (all `lake env lean`, exit 0; read
> exit codes explicitly — the `lake env` wrapper masked a real error on one earlier run, exactly the
> §F hazard). Conclusions below SUPERSEDE the cost estimate in §E for node L7c.3.

### G.0 Index convention — CHECKED (and it bites)

Committed `cocycle A T (n+1) x = cocycle A T n (T x) * A x` (newest factor LEFT). The left-mult
recurrence the perturbation step needs, `Mₙ₊₁ = A(Tⁿx)·Mₙ`, is NOT definitional — it is
`cocycle_add A T 1 n` after `Nat.add_comm` + `cocycle_one`. COMPILED (`scratch_l7c3_index.lean`,
first `example`). So `B := A(T^[n] x)` is the one-step left factor; `κ(B) = ‖A(Tⁿx)‖·‖A(Tⁿx)⁻¹‖`.

### G.1 The increment bound is TRUE — with constant `C = 1`, ratio `σₖ/σₖ₋₁`, on `sin∠` (NOT `tan`)

Let `Pₙ⁽ᵏ⁾` be the orthogonal projector onto the top-`k` RIGHT-singular subspace of `Mₙ`
(= top-`k` eigenspace of `Qₙ = MₙᵀMₙ`; INDEPENDENT of the power `1/(2n)` — the band projector
`Πₙ⁽ʲ⁾ = cfc χⱼ Hₙ` equals exactly this `Pₙ⁽ᵏⱼ⁾`, the power only relabels eigenvalues). The cut index
`k = kⱼ` must sit at a genuine exponent gap `λ_{k-1} > λ_k`. Then, verified numerically over `d=5`,
all `k`, ill-conditioned `B` (50k+ trials, max ratio **0.52**):

```
‖Pₙ₊₁⁽ᵏ⁾ − Pₙ⁽ᵏ⁾‖  ≤  κ(A(Tⁿx)) · σₖ(Mₙ) / σₖ₋₁(Mₙ)        [C = 1]
```

This CONFIRMS §B.2 (the route doc's `Cⱼ·‖A‖‖A⁻¹‖·σⱼ₊₁/σⱼ`) with the explicit constant `1` and pins
the 0-indexed ratio as `σₖ/σₖ₋₁` (bottom-of-bottom-block over bottom-of-top-block at the cut).

SURPRISES / pitfalls found, each a real correctness constraint:
- **It is genuinely a `sin∠` bound, not `tan∠`.** The `tan` version blows up (max ratio 518 in the
  same experiment). So `‖Pₙ₊₁−Pₙ‖ = sin∠(Eₙ,Eₙ₊₁)` is the right LHS; any proof that produces a
  `tan`-shaped estimate is WRONG.
- **Naive triangle/quadratic-form juggling gives only the WEAK (≈1) bound, not `σₖ/σₖ₋₁`.** Worked it
  out: `‖Mₙu‖² = ‖Mₙ Pₙu‖² + ‖Mₙ(I−Pₙ)u‖²` (orthogonal eigenspaces of `Qₙ`) plus the lower bound
  `‖Mₙu‖ ≥ σₖ₋₁(Mₙ)/κ(B)` yields only `‖w‖² ≤ (σ₀²−(σₖ₋₁/κ)²)/(σ₀²−σₖ²)` — the `σ₀` ruins it. The
  sharp `σₖ/σₖ₋₁` constant is a genuine sin-Θ statement; there is no elementary triangle-inequality
  shortcut on the plain matrices. **The route doc's HIGH risk on L7c.3 stands.**
- **Cutting INSIDE a multiplicity block is FALSE.** With `σ₁ = σ₂` (cut at a non-gap), `‖Pₙ₊₁−Pₙ‖`
  reaches **1.0** (projector NOT Cauchy) and the RHS does not decay (`σₖ/σₖ₋₁ → 1`). Re-confirms
  "per DISTINCT exponent, never per index" as a hard correctness requirement, not style.

### G.2 The CHEAPEST correct route: exterior rank-1 Rayleigh-gap sin-Θ (NOT block Davis–Kahan)

VERDICT: **a full abstract Davis–Kahan / block sin-Θ theorem is NOT needed.** The exterior-power
machinery already committed (`compoundMatrix`, `prod_singularValues_eq_l2_opNorm_compound`,
`exteriorPower.map_comp` functoriality) collapses the block problem to a **rank-1 dominant-eigenvector
sin-Θ**, which has a fully ELEMENTARY (Parseval-only) proof. The reduction (numerically verified):

1. Top-`k` right-singular subspace of `Mₙ` ↔ (Plücker) the dominant eigenLINE of
   `Cₙ := (⋀^k Mₙ)ᵀ(⋀^k Mₙ) = ⋀^k Qₙ` on `⋀^k ℝᵈ ≅ ℝ^(d chok)`. Functoriality gives
   `⋀^k Mₙ₊₁ = (⋀^k B)(⋀^k Mₙ)`.
2. At a genuine gap `λ_{k-1} > λ_k`, the top two singular values of `⋀^k Mₙ` are
   `σ₀···σ_{k-1}` and `σ₀···σ_{k-2}σ_k`, ratio EXACTLY `σ_k/σ_{k-1}` (verified) — so the dominant
   eigenline of `Cₙ` is SIMPLE and gapped. A simple gapped top eigenline is the easiest sin-Θ case.
3. **Elementary rank-1 Rayleigh-gap lemma (the irreducible core, fully provable):** for self-adjoint
   `C` with top eigenvalue `μ₀`, second `≤ μ₁ < μ₀`, top unit eigenvector `v₀`, and ANY unit `v'`
   with `⟨C v', v'⟩ ≥ μ₀ − ε`, one has `sin²∠(v', v₀) ≤ ε/(μ₀ − μ₁)`. Proof = Pythagoras
   (`Submodule.norm_sq_eq_add_norm_sq_projection`, COMPILED) + the purely algebraic kernel
   `μ₀−ε ≤ μ₀c+b, b ≤ μ₁s, c+s=1 ⟹ s ≤ ε/(μ₀−μ₁)` (`nlinarith` after `c := 1−s`, COMPILED in
   `scratch_l7c3_sintheta.lean`). NO abstract Davis–Kahan, NO Riesz contour, NO operator-CFC
   continuity.
4. The Rayleigh deficit `ε = μ₀(Cₙ) − ⟨Cₙ v', v'⟩` for `v' =` dominant eigenvector of `Cₙ₊₁`
   is bounded by `(κ(⋀^k B)·σ_k/σ_{k-1})²` (verified, max ratio 0.18), via
   `⟨Cₙ v',v'⟩ = ‖⋀^k Mₙ v'‖² = ‖(⋀^kB)⁻¹ ⋀^k Mₙ₊₁ v'‖² ≥ ‖⋀^k Mₙ₊₁ v'‖²/‖⋀^kB‖² ≥ μ₀(Cₙ₊₁)/‖⋀^kB‖²`
   and `μ₀(Cₙ₊₁) ≥ μ₀(Cₙ)/‖(⋀^kB)⁻¹‖²`. Hence `sin∠ ≤ κ(⋀^kB)·σ_k/σ_{k-1}`.

Trade-off, stated honestly: the exterior route uses `κ(⋀^k B) = ‖⋀^kB‖‖(⋀^kB)⁻¹‖` (LOOSER than the
direct `κ(B)`), but `(1/n)log κ(⋀^kB)` is STILL tempered → 0 a.e. (it is `≤ k·log‖B‖ + k·log‖B⁻¹‖`
up to the committed `sigma_le_opNorm`/`prod_singularValues` sandwich), so summability is unaffected.
The WIN is that the irreducible analytic content shrinks from a block sin-Θ theorem (which Mathlib
lacks entirely and which would have to be built from scratch) to ONE scalar `nlinarith` kernel +
Pythagoras + the ALREADY-COMMITTED exterior bridge. This is strictly cheaper than building block
Davis–Kahan and is the recommended route.

Why NOT the direct (non-exterior) block route: it needs (i) the per-vector restricted-Rayleigh
bounds `v∈Eₙ ⟹ ‖Mₙv‖≥σₖ₋₁‖v‖` and `v∈Eₙ^⊥ ⟹ ‖Mₙv‖≤σₖ‖v‖` for the BLOCK (provable from the
eigenbasis but more bookkeeping), AND (ii) a genuine block sin-Θ assembly (multi-dimensional
principal angles). The exterior route replaces (ii) by the rank-1 lemma. Both need the eigenbasis
facts (COMPILED, `scratch_l7c3_rayleigh.lean`); only the exterior route avoids multi-dim sin-Θ.

### G.3 EXACT Lean statements (Mathlib-style, plain real matrices / inner product spaces)

```lean
-- G.3a  THE irreducible core (abstract, real inner product space). Bare IsSymmetric, NO CFC instance.
theorem sin_sq_le_rayleigh_deficit_div_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : E →ₗ[ℝ] E} (hC : C.IsSymmetric)
    {μ₀ μ₁ : ℝ} {v₀ : E} (hv₀ : ‖v₀‖ = 1) (hev : C v₀ = μ₀ • v₀)   -- top eigenpair
    (hgap : μ₁ < μ₀) (hμ₁ : ∀ w, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ μ₁ * ‖w‖^2)  -- second-eigval ceiling
    {v' : E} (hv' : ‖v'‖ = 1) {ε : ℝ} (hRay : μ₀ - ε ≤ ⟪C v', v'⟫_ℝ) :
    ‖v' - (⟪v', v₀⟫_ℝ) • v₀‖^2 ≤ ε / (μ₀ - μ₁)
-- proof: Pythagoras ‖v'‖²=‖proj‖²+‖perp‖² (Submodule.norm_sq_eq_add_norm_sq_projection on span{v₀});
--        ⟪C v',v'⟫ = μ₀·c + ⟪C perp,perp⟫ ≤ μ₀ c + μ₁ s; then the COMPILED nlinarith kernel.

-- G.3b  the one-step exterior Rayleigh-deficit bound (cocycle-specific; uses committed exterior API)
theorem rayleigh_deficit_le {d : ℕ} (M B : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.det ≠ 0) (k : ℕ) (hk : k ≤ d) (hgap : 0 < σ (k-1) M - σ k M /-genuine gap-/) :
    -- μ₀(⋀^k M) − ⟨(⋀^k M)·v', v'⟩  ≤  (‖⋀^kB‖·‖(⋀^kB)⁻¹‖)² · (σₖ M / σₖ₋₁ M)² · μ₀(⋀^k M)
    sorry  -- via ‖compoundMatrix k (B*M)‖, prod_singularValues_eq_l2_opNorm_compound, compound mult.

-- G.3c  band-projector increment bound (= §B.2, now DERIVED from G.3a+G.3b)
theorem norm_bandProjector_succ_sub_le {d : ℕ}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (j n : ℕ) (x : X) :
    ‖bandProjector A T j (n+1) x - bandProjector A T j n x‖
      ≤ ‖A (T^[n] x)‖^kⱼ * ‖(A (T^[n] x))⁻¹‖^kⱼ * (σ kⱼ (Mₙ) / σ (kⱼ-1) (Mₙ))   -- κ(⋀^kⱼ B)≤‖B‖^k‖B⁻¹‖^k

-- G.3d  packaging: Cauchy from summable increments  (COMPILED, scratch_l7c3_index.lean)
theorem cauchySeq_of_summable_succ_sub {E} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (hsum : Summable (fun n => ‖f (n+1) - f n‖)) : CauchySeq f

-- G.3e  geometric decay ⇒ summable  (COMPILED, scratch_l7c3_assembly.lean)
theorem summable_of_le_exp_neg (a : ℕ → ℝ) (han : ∀ n, 0 ≤ a n) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ n, a n ≤ Real.exp (-c * n)) : Summable a
```

### G.4 The verified ladder (replaces the L7c.3 row of §E)

| # | Lemma | Risk | Effort | Probe / Mathlib |
|---|---|---|---|---|
| L7c.0 | `bandProjector := cfc χⱼ Hₙ`; self-adj + idempotent on good set | LOW (probe-backed §A) | <0.5 | `cfc_predicate/_mul/_congr` |
| L7c.1 | `bandProjector = Pₙ⁽ᵏⱼ⁾` (top-`kⱼ` eigenproj of `Qₙ`), power-independent | MED | 1 | `IsHermitian.cfc` formula; repo `orthProjMatrix` pattern |
| L7c.2 | tempered factor `(1/n)log(‖A(Tⁿx)‖‖A⁻¹‖) → 0` a.e. | **LOW (already proved)** | <0.5 | repo `ae_tendsto_orbit_div_atTop_zero` (Birkhoff.lean:187, currently `private`) |
| L7c.3a | rank-1 Rayleigh-gap sin-Θ core `sin_sq_le_rayleigh_deficit_div_gap` | **MED** (was HIGH) | 1–2 | **COMPILED kernel** `scratch_l7c3_sintheta.lean` (Pythagoras + nlinarith) |
| L7c.3b | exterior Rayleigh-deficit `rayleigh_deficit_le` (compound API) | **HIGH** | 2–3 | committed `prod_singularValues_eq_l2_opNorm_compound`, `exteriorPower.map_comp`; needs single-index `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖σⱼ(X)` (BUILD) |
| L7c.3c | assemble `norm_bandProjector_succ_sub_le` (G.3a∘G.3b + Plücker subspace↔eigenline) | **HIGH** | 1–2 | the subspace↔eigenline (Plücker) bridge is new infra |
| L7c.4 | `hsum` a.e. (geometric decay ⇒ summable) | LOW–MED | 0.5–1 | **COMPILED** `scratch_l7c3_{assembly,index}.lean` + `tendsto_log_singularValue` |
| L7c.5 | `cauchySeq_bandProjector` (Cauchy from summable incr.) | **LOW (COMPILED)** | <0.5 | `scratch_l7c3_index.lean` |
| L7d  | `cauchySeq_qpow ⇒ L7_statement` (assemble blocks×eigenvalues) | MED | 1–1.5 | `scratch_l7c3_assembly.lean` (smul-limit, completeness) + committed `eigenvalues_qpow_tendsto` |

Net L7c→L7d: **~7–11 sessions** (down from §E's 8–14), dominated now by L7c.3b+L7c.3c (the
exterior-deficit estimate + the Plücker subspace↔eigenline bridge), NOT by an abstract Davis–Kahan
theorem. The single-index exterior submultiplicativity `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖·σⱼ(X)` is a small new
lemma (Mathlib has only the product form `prod_singularValues_comp_le`; min-max is absent).

### G.5 What was COMPILED vs argued on paper (honest ledger)

| Probe | Claim | Status |
|---|---|---|
| `scratch_l7c3_index.lean` | (i) `Mₙ₊₁ = A(Tⁿx)·Mₙ` from committed cocycle; (ii) Cauchy ⇐ summable increments | **COMPILED exit 0** |
| `scratch_l7c3_rayleigh.lean` | eigenbasis `apply_eigenvectorBasis`, `eigenvalues_antitone`, `singularValues_antitone`, `sq_singularValues` — the restricted-Rayleigh ingredients | **COMPILED exit 0** |
| `scratch_l7c3_assembly.lean` | geometric-decay ⇒ summable; `Tendsto.smul` block assembly; `cauchySeq_tendsto_of_complete` | **COMPILED exit 0** |
| `scratch_l7c3_sintheta.lean` | Pythagoras `norm_sq_eq_add_norm_sq_projection`; **the algebraic kernel of the rank-1 sin-Θ bound** | **COMPILED exit 0** |

ARGUED ON PAPER + verified NUMERICALLY only (Python, not Lean):
- The increment bound `‖Pₙ₊₁−Pₙ‖ ≤ κ(B)σₖ/σₖ₋₁` with `C=1` (max ratio 0.52 over 50k+ trials).
- The exterior reduction: top-2 singular-value ratio of `⋀^k M` equals `σₖ/σₖ₋₁` (exact).
- The full chain `sin²∠ ≤ ε/g ≤ (κ(⋀^kB)·σₖ/σₖ₋₁)²` (max 0.18) and the rank-1 kernel `sin² ≤ ε/g`
  (tight, ratio 1.0).
- The `tan` form FAILS (518); cutting inside a multiplicity block FAILS (1.0). Both are correctness
  guards, not yet Lean-encoded.

These four numerically-verified inequalities are the L7c.3 work to formalize; the Lean *kernels* they
rest on are the four compiled probes above. No committed statement is contradicted.

## H. L7c.3b/c + L7c.1 — verified geometry route (de-risking pass 3, 2026-06-07)

> Adversarial scout of the three still-HIGH nodes (L7c.1, L7c.3b, L7c.3c), targeting the exact
> Lean-provable statements, the Mathlib found-vs-missing ledger, and the CHEAPEST correct path for
> the Plücker back-transport. FOUR new compiled probes (all `lake env lean`, repo root, exit codes
> read explicitly): `scratch_l7c3bc_rank1.lean`, `scratch_l7c3bc_eigproj.lean`,
> `scratch_l7c3bc_plucker.lean`, `scratch_l7c3bc_frobenius.lean`. Two §G claims CORRECTED below
> (H.1 SURPRISE A, H.2 SURPRISE B). No committed statement contradicted.

### H.0 Verdict (TL;DR)

1. **L7c.3b does NOT need single-index σⱼ submultiplicativity.** §G.4 lists "needs single-index
   `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖·σⱼ(X)` (BUILD)" as a sub-task. This is an OVERSTATEMENT: the rank-1
   reduction (§G.2) only ever touches the TOP eigenvalue / operator norm of the compound, so the
   chain needs only PER-VECTOR operator-norm facts `‖P w‖ ≤ ‖P‖‖w‖`, `‖w‖ ≤ ‖P⁻¹‖‖P w‖`
   (probe `rank1`, all immediate from `ContinuousLinearMap.le_opNorm`). The min-max single-index
   lemma — which Mathlib genuinely lacks — is NOT on the critical path. (SURPRISE A.)
2. **L7c.3c back-transport is UNAVOIDABLE but the sharp principal-angle identity can be SIDESTEPPED.**
   The committed `L7_statement` fixes the limit object as a `d×d` matrix (`qpow → Λ`), so the `d×d`
   band projectors `bandProjector = cfc χ qpow` must be shown Cauchy; one cannot stay in `⋀^k`-space.
   But the SHARP `‖P_E − P_E'‖_op = sin θ_max` (needs principal angles — ABSENT from Mathlib) is NOT
   required: a **Frobenius route with a dimension-only constant 2k** works and avoids principal
   angles entirely (H.2, probes `plucker`+`frobenius`).
3. **L7c.1 is MED and fully probe-backed** (probe `eigproj`): the cfc-indicator equals the top-block
   eigenprojector via the explicit `IsHermitian.cfc = U·diag(χ∘eig)·Uᴴ` formula.

Net revised estimate L7c.3b → L7c.3c → L7d: **~5.5–8.5 sessions** (down from §G.4's 7–11), because
the σⱼ min-max build is removed (SURPRISE A) and the back-transport uses only soft trace algebra +
AM-GM + the committed det-Gram kernel, not a Davis–Kahan/principal-angle theory build.

### H.1 L7c.3b — the rank-1 exterior Rayleigh-deficit bound (exact statements)

The chain of §G.2 step 4, restated PRECISELY (no σⱼ index). With `Cₙ := compoundᵀ·compound` where
`compound := compoundMatrix k Mₙ` (so `Cₙ = ⋀^k Qₙ` on `⋀^k ℝᵈ`), and `v'` = top unit eigenvector
of `Cₙ₊₁`:

```
⟨Cₙ v', v'⟩ = ‖toEuclideanLin(compound k Mₙ) · v'‖²                       -- adjoint∘self Rayleigh
‖toEuclideanLin(compound k Mₙ) v'‖ ≥ ‖toEuclideanLin(compound k Mₙ₊₁) v'‖ / ‖⋀^kB‖
                                                                          -- ⋀^k Mₙ₊₁ = (⋀^kB)(⋀^k Mₙ)
μ₀(Cₙ₊₁) = ‖toEuclideanLin(compound k Mₙ₊₁) v'‖²                           -- v' is top eigvec
μ₀(Cₙ₊₁) ≥ μ₀(Cₙ) / ‖(⋀^kB)⁻¹‖²
⟹ μ₀(Cₙ) − ⟨Cₙ v', v'⟩ ≤ (1 − 1/(‖⋀^kB‖‖(⋀^kB)⁻¹‖)²)·μ₀(Cₙ)
                       ≤ (‖⋀^kB‖‖(⋀^kB)⁻¹‖)²·(σₖ/σₖ₋₁)²·μ₀(Cₙ)            -- §G.3b, ε form
```

**LOAD-BEARING facts (all COMPILED in `scratch_l7c3bc_rank1.lean`, exit 0):**
- `‖P w‖ ≤ ‖P‖·‖w‖` = `P.le_opNorm w` (CLM).
- `‖w‖ ≤ ‖Pinv‖·‖P w‖` from `Pinv ∘ P = id` (`congrArg` + `le_opNorm`).
- `⟨(adjoint P ∘ₗ P) w, w⟩ = ‖P w‖²` (`adjoint_inner_left` + `real_inner_self_eq_norm_sq`).
- `⟨C w, w⟩ ≤ ‖C‖·‖w‖²` for symmetric `C` (`real_inner_le_norm` + `le_opNorm`).

**NEW sub-lemma still to BUILD (small, LOW–MED):** the compound-multiplicativity
`toEuclideanLin (compoundMatrix k (B*M)) = toEuclideanLin (compoundMatrix k B) ∘ₗ toEuclideanLin (compoundMatrix k M)`
(Cauchy–Binet at the matrix level). DERIVABLE from committed `conjExteriorMap_eq_toEuclideanLin_compound`
+ `exteriorPower.map_comp` (the same telescoping used in `exteriorOpNorm_comp_le`). And
`μ₀(compoundᵀcompound) = ‖compound‖²` = `(∏_{i<k} σᵢ)²` from the committed
`prod_singularValues_eq_l2_opNorm_compound` + top-eigenvalue-of-AᵀA = op-norm².

Exact target signature (replaces the `sorry` in §G.3b `rayleigh_deficit_le`): unchanged in shape,
but the proof uses ONLY the rank-1 facts above + the new compound-mult lemma — NOT a σⱼ lemma.

> **SURPRISE A (corrects §G.4):** the row "needs single-index `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖σⱼ(X)` (BUILD)"
> is unnecessary. The min-max/Courant–Fischer single-index bound is genuinely ABSENT from Mathlib
> (confirmed: `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` has only def, `_nonneg`,
> `_antitone`, the `sq_singularValues_fin` eigenvalue bridge, support/rank — NO min-max; and
> `Rayleigh.lean` has only the GLOBAL `iSup/iInf` top/bottom eigenvalue characterization, no
> codim-j variational form). But the rank-1 route never needs it. Removing this build is the main
> cost saving of this pass.

### H.2 L7c.3c — the Plücker back-transport: the Frobenius route (avoids principal angles)

The output of the rank-1 lemma (G.3a) is a sin-Θ bound on the dominant eigenLINE of `Cₙ = ⋀^k Qₙ`,
i.e. on the decomposable unit wedges `wₙ`, `wₙ₊₁` (Plücker images of o.n. frames of the top-k
eigenspaces `Eₙ`, `Eₙ₊₁`). The band projector `bandProjector A T χ n x` is (by L7c.1) the `d×d`
orthogonal projector `P_{Eₙ}`. We must bound `‖P_{Eₙ₊₁} − P_{Eₙ}‖` (L2 operator norm) by the wedge
sine. **Numerically verified, tight (ratio 1.0, 50k+ trials, gapped PD pairs, d≤6):**

```
‖P_E − P_E'‖_op²  ≤  1 − ⟨w_E, w_E'⟩²   ( = sin²∠_wedge )           (SHARP — needs principal angles)
```

The SHARP form needs `‖P−P'‖_op = sin θ_max` and `⟨w,w'⟩ = ∏cos θᵢ`, i.e. principal-angle theory,
which **Mathlib LACKS ENTIRELY** (grep: no `principalAngle`, no sin-Θ, no
`‖orthogonalProjection K − orthogonalProjection K'‖` identity, no Davis–Kahan). Building it is the
expensive path. **The CHEAPER substitute (this scout's recommendation):** a Frobenius bound with a
dimension-only constant, decomposing into pieces that need only trace algebra, AM-GM, and the
COMMITTED det-Gram kernel — no principal angles:

```
‖P − P'‖_op²  ≤  ‖P − P'‖_F²                                  -- self-adjoint: spectral radius ≤ HS
‖P − P'‖_F²   =  tr((P−P')²) = 2k − 2·tr(P·P')               -- P²=P, P'²=P', tr P = tr P' = (k:ℝ)
tr(P·P')      =  ‖UᵀV‖_F²  =  Σ cos²θᵢ                        -- P = UUᵀ, P' = VVᵀ; cyclic trace
k − ‖UᵀV‖_F²  ≤  k·(1 − det(UᵀV)²)                            -- AM-GM (k·∏cos² ≤ Σcos², det²≤1)
det(UᵀV)²     =  ⟨w_E, w_E'⟩²                                  -- COMMITTED hodgeForm_ιMulti det-Gram
⟹  ‖P − P'‖_op²  ≤  2k·(1 − ⟨w_E,w_E'⟩²)  =  2k·sin²∠_wedge
```

The constant `2k ≤ 2d` is a fixed dimension constant, so summability (L7c.4/L7c.5) is UNAFFECTED:
`sin∠_wedge ≤ κ(⋀^kB)·σₖ/σₖ₋₁` (G.3a∘G.3b) still decays geometrically a.e., and `√(2k)` is a
harmless multiplicative constant.

**LOAD-BEARING facts COMPILED:**
- `scratch_l7c3bc_plucker.lean` (exit 0): the decomposable-wedge inner product = cross-Gram
  determinant `det⟨v j, w i⟩` (via `exteriorPower.pairingDual_ιMulti_ιMulti` — the public path of
  the committed private `hodgeForm_ιMulti`); o.n. frame ⟹ self-Gram = `1`, det = 1 (unit wedge);
  the SCALAR back-transport closer `pd² ≤ 1−cmax², detc² ≤ cmax² ⟹ pd² ≤ 1−detc²` (`nlinarith`);
  the two-factor `(ab)² ≤ b²` core for `|cos| ≤ 1`.
- `scratch_l7c3bc_frobenius.lean` (exit 0): the trace identity `tr((P−Q)²) = 2k − 2 tr(PQ)` for
  self-adjoint idempotents of trace `k` (`trace_mul_comm` + `trace_sub/_add`, `abel` — matrices are
  NONCOMMUTATIVE so `ring` FAILS, use `abel` for the additive expansion); the AM-GM two-factor base
  `2−(t₀+t₁) ≤ 2(1−t₀t₁)`; the packaging `k·D ≤ S ⟹ k−S ≤ k(1−D)`; the sqrt closer
  `op² ≤ twok(1−d²), 0≤1−d² ⟹ op ≤ √twok·√(1−d²)`.

**Still to BUILD for L7c.3c (MED–HIGH but BOUNDED, no principal angles):**
- `‖M‖_op ≤ ‖M‖_F` for self-adjoint `M` on `Matrix (Fin d) (Fin d) ℝ` (L2 op-norm). Cleanest via the
  committed singular-value bridge: `‖M‖ = σ₀(toEuclideanLin M)` and `σ₀² ≤ Σσᵢ² = tr(MᵀM)`. There is
  norm-instance friction (L2-operator vs Frobenius `NormedAddCommGroup` instances on `Matrix`); the
  bridge sidesteps it by working through `toEuclideanLin`.
- the general-k AM-GM `k·∏cos² ≤ Σcos²` via `Real.geom_mean_le_arith_mean_weighted` (uniform weights
  `1/k`) + `∏cos² ≤ 1`. (FOUND in `Mathlib/Analysis/MeanInequalities.lean`.)
- the trace/Plücker glue: `tr(P_E P_E') = ‖UᵀV‖_F²` and `det(UᵀV) = ⟨w_E, w_E'⟩` tying the committed
  `compoundMatrix`/`hodgeForm_ιMulti` to the o.n. frames produced by `eigenvectorUnitary`.

> **SURPRISE B (sharpens §G):** the projector-difference ↔ wedge-sine identity (the genuinely novel
> "Plücker back-transport" infra) does NOT require the principal-angle machinery one would expect
> from a literal Davis–Kahan reading. Replacing the SHARP operator-norm identity by the LOOSER
> Frobenius bound with constant `2k` keeps summability and trades a (large) principal-angle theory
> build for soft trace algebra + AM-GM + the already-committed det-Gram kernel. This is the cheapest
> correct path and is what the implementation should take.

### H.3 L7c.1 — eigenprojector identification (exact statement + compiled load-bearing step)

For a threshold `c` strictly between the k-th and (k+1)-th sorted eigenvalues of `qpow A T n x`,
and `χ` continuous with `(spectrum ℝ (qpow…)).EqOn χ (indicator (Ioi c) 1)`, the band projector
equals the orthogonal projector onto the top-k eigenvectors:

```lean
theorem bandProjector_eq_orthProj_topBlock {A} {T} {χ : ℝ → ℝ} {c : ℝ} (n : ℕ) (x : X)
    (heq : (spectrum ℝ (qpow A T n x)).EqOn χ (Set.indicator (Set.Ioi c) 1))
    (hgap : … c strictly between eigenvalues k and k+1 …) :
    bandProjector A T χ n x
      = orthProjMatrix (span of eigenvectors of (gram A T n x) with eigenvalue > c²ⁿ)   -- d×d projector
```

**Load-bearing step COMPILED in `scratch_l7c3bc_eigproj.lean` (exit 0):**
- `cfc χ A = hA.cfc χ` (`cfc_eq`) and `hA.cfc χ = U · diag(ofReal∘χ∘eig) · Uᴴ`
  (`Matrix.IsHermitian.cfc` + `Unitary.conjStarAlgAut_apply`).
- {0,1}-valued χ∘eig ⟹ `diag(ofReal∘χ∘eig)` idempotent (`diagonal_mul_diagonal`); conjugation by the
  unitary `U` (via `Unitary.coe_star_mul_self : star U * U = 1`) preserves idempotence ⟹ `cfc χ A` is
  a genuine orthogonal projector.
- `cfc_congr heq` replaces continuous χ by the exact indicator on the (finite) spectrum.
- `indicator (Ioi c) 1 (eig i) = 1` iff `c < eig i`, else `0` (`Set.indicator_of_mem`/`_notMem`) —
  the diagonal selects exactly the top block.

The remaining work (MED, ~1 sess) is identifying the conjugated diagonal projector with
`orthProjMatrix (top-block span)` — reuse the committed `Measurable.lean` `orthProjMatrix` pattern
(a self-adjoint idempotent equals the orthogonal projection onto its range) — plus pinning that
`eigenvalues(qpow) > c ↔ eigenvalues(gram) > c²ⁿ` via the committed `eigenvalues₀_qpow_eq`.

### H.4 Mathlib found-vs-missing ledger (min-max σⱼ + projector-angle), this scout

**FOUND (compiled against):**
- `ContinuousLinearMap.le_opNorm`, `LinearMap.adjoint_inner_left`, `real_inner_le_norm`,
  `real_inner_self_eq_norm_sq` — the rank-1 chain (probe `rank1`).
- `Matrix.IsHermitian.cfc` explicit formula, `cfc_eq`, `cfc_congr`, `Unitary.conjStarAlgAut_apply`,
  `Unitary.coe_star_mul_self`, `diagonal_mul_diagonal`, `Set.indicator_of_mem/_notMem` (probe
  `eigproj`).
- `exteriorPower.pairingDual_ιMulti_ιMulti`, `exteriorPower.map_apply_ιMulti` — decomposable-wedge
  inner = det⟨vⱼ,wᵢ⟩ (probe `plucker`; mirrors committed `hodgeForm_ιMulti`).
- `Matrix.trace_mul_comm`, `Matrix.trace_sub/_add`, `Real.sq_sqrt` — Frobenius cores (probe
  `frobenius`). `Real.geom_mean_le_arith_mean_weighted` (`MeanInequalities.lean`) for general-k AM-GM.
- Committed: `prod_singularValues_eq_l2_opNorm_compound`, `conjExteriorMap_eq_toEuclideanLin_compound`,
  `exteriorPower.map_comp`, `sigma_le_opNorm`, `singularValues_le_opNorm`, `eigenvalues₀_qpow_eq`,
  `gram_eigenvalues₀_eq_sq_singularValues`, `sin_sq_le_rayleigh_deficit_div_gap`, `hodgeForm_ιMulti`
  (private), `orthProjMatrix` pattern.

**MISSING (confirmed ABSENT; the route AVOIDS each):**
- **Single-index σⱼ min-max / Courant–Fischer / `σⱼ(P∘Y) ≤ ‖P‖σⱼ(Y)`** — absent (`SingularValues.lean`
  has no min-max; `Rayleigh.lean` only global top/bottom). AVOIDED by the rank-1 reduction (H.1).
- **Principal angles / sin-Θ / Davis–Kahan / `‖orthogonalProjection K − orthogonalProjection K'‖`
  identity** — absent entirely. AVOIDED by the Frobenius route (H.2).
- **Compound-multiplicativity `compoundMatrix k (B*M) = compoundMatrix k B * compoundMatrix k M`** —
  absent (no matrix-level Cauchy–Binet). To BUILD (LOW–MED) from functoriality.
- **`‖M‖_op ≤ ‖M‖_F`** for the L2 operator norm — to BUILD (MED) via the singular-value bridge.

### H.5 COMPILED-vs-argued table (this pass)

| Probe | Claims | Status |
|---|---|---|
| `scratch_l7c3bc_rank1.lean` | rank-1 per-vector op-norm chain (H.1): `le_opNorm`, inverse lower bound, `⟨adjoint∘self w,w⟩=‖Pw‖²`, symmetric-Rayleigh ≤ `‖C‖‖w‖²` | **COMPILED exit 0** |
| `scratch_l7c3bc_eigproj.lean` | L7c.1 (H.3): `cfc_eq`+explicit `IsHermitian.cfc`; idempotent diag + unitary-conjugation projector; `cfc_congr`; indicator selects top block | **COMPILED exit 0** |
| `scratch_l7c3bc_plucker.lean` | decomposable-wedge inner = det-Gram; o.n. frame ⟹ unit wedge; scalar back-transport closer; `(ab)²≤b²` | **COMPILED exit 0** (unused-var warns) |
| `scratch_l7c3bc_frobenius.lean` | Frobenius back-transport cores (H.2): `tr((P−Q)²)=2k−2tr(PQ)`; AM-GM two-factor; `k·D≤S⟹k−S≤k(1−D)`; sqrt closer | **COMPILED exit 0** (`abel` not `ring` — matrices noncommutative) |

ARGUED + verified NUMERICALLY only (Python, not Lean):
- `‖P_E−P_E'‖_op² ≤ 1−⟨w,w'⟩²` (sharp, tight ratio 1.0) and `‖·‖_op² ≤ 2k(1−⟨w,w'⟩²)` (Frobenius,
  dimension-uniform); `k·∏tᵢ ≤ Σtᵢ` for tᵢ∈[0,1] (0 violation); top-2 singular-ratio of `⋀^k M`
  equals `σₖ/σₖ₋₁`.
- The Frobenius bound is NOT controlled by `1−⟨w,w'⟩²` with a CONSTANT < `k` (ratio grows with k —
  the `2k` factor is necessary, not removable).

### H.6 Revised risk-tagged sub-ladder (supersedes the L7c.3b/3c rows of §G.4)

| # | Lemma | Risk | Effort | Probe / route |
|---|---|---|---|---|
| L7c.1 | `bandProjector = orthProj(top-k eigenspace)` | MED | 1 | **COMPILED** `eigproj`; `orthProjMatrix` pattern + `eigenvalues₀_qpow_eq` |
| L7c.3b.0 | compound-mult `⋀^k(B*M) = (⋀^kB)(⋀^kM)` (matrix-level Cauchy–Binet) | LOW–MED | 0.5 | committed `conjExteriorMap_eq…` + `map_comp` |
| L7c.3b | rank-1 exterior Rayleigh-deficit `rayleigh_deficit_le` (NO σⱼ) | MED | 1–1.5 | **COMPILED** `rank1` + `sin_sq_le_rayleigh_deficit_div_gap` + L7c.3b.0 |
| L7c.3c.0 | `‖M‖_op ≤ ‖M‖_F` for self-adjoint (via σ-bridge) | MED | 1 | committed `prod_singularValues…`; norm-instance friction |
| L7c.3c.1 | Frobenius back-transport `‖P−P'‖_op² ≤ 2k(1−⟨w,w'⟩²)` | HIGH (bounded) | 1.5–2 | **COMPILED** `frobenius`+`plucker`; AM-GM `geom_mean_le_arith_mean_weighted` |
| L7c.3c | assemble `norm_bandProjector_succ_sub_le` (G.3a∘G.3b∘3c.1, Plücker glue) | MED | 1 | det-Gram = wedge inner (committed `hodgeForm_ιMulti`) |
| L7c.4/5/L7d | (unchanged from §G.4) | LOW–MED | 1.5–2.5 | `scratch_l7c3_*` |

**Critical path: L7c.3b.0 → L7c.3b → L7c.3c.0 → L7c.3c.1 → L7c.3c → L7c.4 → L7d.** No single node is
the old "abstract Davis–Kahan"; the irreducible analytic content is the already-COMMITTED
`sin_sq_le_rayleigh_deficit_div_gap` (G.3a). Net L7c.3b→L7c.3c→L7d: **~5.5–8.5 sessions**.

### H.7 Flags on §G claims

- §G.4 row L7c.3b "needs single-index `σⱼ(⋀^kB·X) ≤ ‖⋀^kB‖σⱼ(X)` (BUILD)" — **CORRECTED**: not
  needed (H.1, SURPRISE A). Removed from the ladder.
- §G.4 row L7c.3c "the subspace↔eigenline (Plücker) bridge is new infra" — **REFINED**: the bridge
  is real, but it is the Frobenius `2k`-constant route (trace + AM-GM + det-Gram), NOT a
  principal-angle/Davis–Kahan build (H.2, SURPRISE B). The sharp `sin θ_max` identity is sidestepped.
- §G.2 step 4 chain — **CONFIRMED** Lean-expressible exactly as written with the committed compound
  API + the rank-1 facts (H.1, probe `rank1`); one new compound-mult lemma (L7c.3b.0) is required.
- No committed statement is contradicted; `sin_sq_le_rayleigh_deficit_div_gap`, `eigenvalues₀_qpow_eq`,
  `prod_singularValues_eq_l2_opNorm_compound`, `L7_statement` all remain sound.

## I. L7c.3b→L7d — assembled chain (verified)

> Final de-risking pass 4, 2026-06-07. Nails the EXACT Lean-provable statement chain from the
> committed pieces through `norm_bandProjector_succ_sub_le` and on to `L7_statement`, resolving
> UNCERTAINTY 1 (compound top-2 eigenvalues / the `hμ₁` ceiling) and UNCERTAINTY 2 (projector↔wedge
> glue). THREE new compiled probes (all `lake env lean`, repo root, exit 0; codes echoed):
> `scratch_l7c3final_top2eig.lean`, `scratch_l7c3final_glue.lean`, `scratch_l7c3final_chain.lean`.
> One §G/§H CORRECTION below (I.3 SURPRISE C — the relative-gap amplifier). No committed statement
> contradicted.

### I.0 RESOLVED — UNCERTAINTY 1: top-2 eigenvalues of `Cₙ = (⋀^k Mₙ)ᵀ(⋀^k Mₙ) = ⋀^k Qₙ`

The committed `exteriorOpNorm_hodge_eq_prod_singularValues` proof DIAGONALIZES `conjExteriorMap`
internally: its `hortho` shows the standard-basis images of the SVD-basis conjugated exterior map
are PAIRWISE ORTHOGONAL with weights `c i = ∏_{a∈S_i} σ_a²`, `S_i` over the k-subsets of `Fin nE`.
These weights ARE the eigenvalues of `Cₙ = adjoint∘self` (a self-adjoint operator, diagonal in that
o.n. basis). Hence, CONFIRMED:

- **eigenvalues of `Cₙ` = `{ (∏_{a∈S} σ_a)² : |S| = k }`** (the SVD diagonalization).
- **`μ₀(Cₙ) = (∏_{i<k} σᵢ)² = ‖compoundMatrix k Mₙ‖²`** — top prefix set `{0,…,k-1}`, maximal by the
  committed `prod_le_prod_top`; and `= ‖compound‖²` via `prod_singularValues_eq_l2_opNorm_compound`
  (top eigenvalue of `AᵀA = ‖A‖²`). Probe `top2eig` (1a/1c/1e).
- **`μ₁(Cₙ) = (σ₀···σ_{k-2}·σ_k)² = (∏_{i<k-1}σᵢ²)·σ_k²`** — the SECOND set swaps `σ_{k-1}→σ_k`;
  it is `≤ μ₀` exactly when `σ_k ≤ σ_{k-1}` (genuine gap). Probe `top2eig` (1b/1c).
- **GAP `μ₀ − μ₁ = (∏_{i<k-1}σᵢ²)·(σ_{k-1}² − σ_k²)`, `> 0 ⟺ σ_{k-1} > σ_k`** (and all prefix
  factors `> 0`). Probe `top2eig` (1d). At a genuine exponent gap the dominant eigenLINE of `Cₙ` is
  SIMPLE, so `sin_sq_le_rayleigh_deficit_div_gap` applies with `v₀` the decomposable wedge of the
  top-k right-singular vectors.

**The `hμ₁` ceiling (cleanest Lean route).** `hμ₁ : ∀ w ⊥ v₀, ⟪Cₙ w, w⟫ ≤ μ₁‖w‖²`. In the SVD
o.n. eigenbasis of `Cₙ`, write `w = Σ aᵢ eᵢ`; orthogonality to `v₀ = e_{i₀}` (the top index) means
`a_{i₀}=0`. Then `⟪Cₙ w,w⟫ = Σ cᵢ aᵢ²` and every remaining weight `cᵢ ≤ μ₁` (the top is dropped),
so `⟪Cₙ w,w⟫ ≤ μ₁ Σ aᵢ² = μ₁‖w‖²`. The PURE scalar kernel (weighted sum, weights `≤ μ₁` off the
dropped support) is COMPILED in probe `top2eig` (1f). This is strictly softer than re-proving the
diagonalization: it consumes the committed `hortho` orthogonality directly. **No new abstract
spectral theorem is needed for the ceiling.**

### I.1 RESOLVED — UNCERTAINTY 2: projector↔wedge glue (the Frobenius back-transport)

For orthonormal frames `U,V : Matrix (Fin d) (Fin k) ℝ` (columns = o.n. bases of `Eₙ,Eₙ₊₁`),
`P = U·Uᵀ`, `P' = V·Vᵀ`:

- **`tr(P·P') = ‖UᵀV‖_F²`** — cyclic trace `tr(UUᵀVVᵀ) = tr((UᵀV)(UᵀV)ᵀ)` then
  `tr(AAᵀ)=Σ A²`. COMPILED probe `glue` (G1/G1'). Matrices NONCOMMUTATIVE: used `Matrix.mul_assoc`
  + `trace_mul_comm`, not `ring`.
- **`det(UᵀV) = ⟪w_{Eₙ}, w_{Eₙ₊₁}⟫`** (det-Gram = decomposable-wedge inner product) — via the
  committed `hodgeForm_ιMulti`'s public path `exteriorPower.pairingDual_ιMulti_ιMulti`. COMPILED
  probe `glue` (G2).
- **`k·∏cos²θᵢ ≤ Σcos²θᵢ`** — ELEMENTARY: each `cos²≤1 ⟹ ∏ ≤ each factor ⟹ k·∏ = Σ_j(∏) ≤ Σ_j cos²_j`.
  NO `geom_mean` needed (contra §H.6's "AM-GM `geom_mean_le_arith_mean_weighted`" suggestion — the
  uniform-weight geom-mean is AVOIDABLE; the one-line product-≤-factor argument suffices). COMPILED
  probe `glue` (G3 general-Finset + G3-range). **This simplifies the §H.2 build (no MeanInequalities
  dependency).**

Chaining (the committed `singularValues_zero_sq_le_sum` gives `‖P−P'‖_op² ≤ ‖P−P'‖_F²` through the
σ-bridge; the trace identity `tr((P−P')²)=2k−2tr(PP')` is the committed-style `frobenius` probe):
`‖P−P'‖_op² ≤ ‖P−P'‖_F² = 2k − 2tr(PP') = 2k − 2‖UᵀV‖_F² ≤ 2k(1−det(UᵀV)²) = 2k(1−⟪w,w'⟫²)
= 2k·sin²∠_wedge`.

**Band projector gives the frame `U` DIRECTLY.** `bandProjector A T χ n x = cfc χ (qpow)
= U·diag(χ∘eig)·Uᴴ` by committed `cfc_eq_eigenvectorUnitary_conj`. For the 0/1 top-block indicator,
`diag` selects the top-k columns of the eigenvector unitary `U`, so `bandProjector = U_top·U_topᵀ`
with `U_top` = those columns — i.e. `P = U Uᵀ` is IMMEDIATE (the diag-selector·unitary collapses to
the column-frame outer product; idempotence under unitary conjugation COMPILED probe `glue` (G4)).
So no separate "extract the frame from the projector" lemma is needed.

### I.2 EXACT node signatures (L7c.3b through L7d)

```lean
-- L7c.3b  exterior Rayleigh-deficit  (NO σⱼ min-max; rank-1 facts + compound-mult)
theorem rayleigh_deficit_le {d : ℕ} (M B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hgap : (toEuclideanLin M).singularValues k
                                   < (toEuclideanLin M).singularValues (k-1)) :
    -- μ₀(Cₙ) − ⟨Cₙ v', v'⟩ ≤ (‖compound k B‖·‖(compound k B)⁻¹‖)²·(σₖ M/σₖ₋₁ M)²·μ₀(Cₙ)
    -- where v' = top eigenvector of Cₙ₊₁ = (compound k (B*M))ᵀ(compound k (B*M))
    sorry  -- via toEuclideanLin_compoundMatrix_mul + rank-1 facts (scratch_l7c3bc_rank1) + I.0

-- L7c.3c.0  ‖M‖_op ≤ ‖M‖_F  (committed singularValues_zero_sq_le_sum + σ-bridge)
theorem opNorm_le_frobenius {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    (toEuclideanLin M).singularValues 0 ≤ Real.sqrt (∑ i, (toEuclideanLin M).singularValues i ^ 2)

-- L7c.3c.1  Frobenius back-transport  (trace + AM-GM + det-Gram glue, constant 2k)
theorem norm_proj_sub_le_wedge {d k : ℕ} (U V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ‖U*Uᵀ - V*Vᵀ‖ ^ 2 ≤ 2 * k * (1 - (Uᵀ * V).det ^ 2)   -- = 2k·sin²∠_wedge

-- L7c.3c  the assembled increment bound (G.3a ∘ L7c.3b ∘ L7c.3c.1 + Plücker glue)
theorem norm_bandProjector_succ_sub_le {d : ℕ}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (χ : ℝ → ℝ) (kⱼ n : ℕ) (x : X)
    (hgap : … genuine exponent gap at index kⱼ …) :
    ‖bandProjector A T χ (n+1) x - bandProjector A T χ n x‖
      ≤ Real.sqrt (2 * kⱼ)
        * ‖A (T^[n] x)‖ ^ kⱼ * ‖(A (T^[n] x))⁻¹‖ ^ kⱼ
        * ((toEuclideanLin (cocycle A T n x)).singularValues kⱼ
            / (toEuclideanLin (cocycle A T n x)).singularValues (kⱼ-1))
-- NOTE: see I.3 SURPRISE C — the honest RHS carries a relative-gap amplifier; the displayed
-- clean form holds EVENTUALLY (n large, σₖ/σₖ₋₁ ≤ 1/√2), which is all L7c.4 summability needs.

-- L7c.4  hsum a.e.  (geometric decay of the RHS ⟹ summable increments)
theorem summable_norm_bandProjector_succ_sub {A T χ} (… a.e. hyps …) :
    ∀ᵐ x ∂μ, Summable (fun n => ‖bandProjector A T χ (n+1) x - bandProjector A T χ n x‖)
-- via: (1/n)·log(RHS) → λ_{kⱼ} − λ_{kⱼ-1} < 0 a.e. using committed `tendsto_log_singularValue`
--      (two distinct indices) + tempered `tendsto_logNorm_orbit_div_atTop_zero` /
--      `tendsto_logNorm_inv_orbit_div_atTop_zero` (the κ(⋀^kB) ≤ ‖B‖^k‖B⁻¹‖^k factor, log/n → 0);
--      √(2kⱼ) constant harmless. Then eventual ρⁿ-decay ⟹ Summable. (scratch_l7c3final_chain C3–C5)

-- L7c.5  packaging  (COMMITTED)
theorem cauchySeq_cfc_of_summable …            -- already in OseledetsLimit.lean
theorem exists_tendsto_cfc_of_summable …       -- already in OseledetsLimit.lean

-- L7d  cauchySeq_qpow ⇒ L7_statement
theorem cauchySeq_qpow {A T} (… a.e. hyps …) :
    ∀ᵐ x ∂μ, CauchySeq (fun n => qpow A T n x)
-- assemble qpow_n = Σⱼ (block eigenvalue)·(P⁽ʲ⁾ₙ − P⁽ʲ⁺¹⁾ₙ); each bandProjector Cauchy (L7c.5),
-- each block eigenvalue → e^{λⱼ} (committed eigenvalues_qpow_tendsto); products/sums of
-- Cauchy/convergent matrix sequences are Cauchy (CompleteSpace).
theorem L7d {A T} (… ) : L7_statement μ T A
-- = cauchySeq_qpow + cauchySeq_tendsto_of_complete (the committed L7_statement is ∃Λ, qpow→Λ a.e.)
```

### I.3 §G/§H correction — SURPRISE C (the relative-gap amplifier)

§G.2 step 4 / §H.1 claim the deficit→sin chain "collapses to `sin²∠ ≤ C·κ(⋀^kB)²·(σ_k/σ_{k-1})²`"
with `C` absolute. The LITERAL algebra (probe `chain` C1-literal, COMPILED) gives, with `a=σ_{k-1}²`,
`b=σ_k²`, `pre=∏_{i<k-1}σ²`, `ε ≤ κ²·(b/a)·μ₀`, `μ₀=pre·a`, `μ₀−μ₁=pre·(a−b)`:

```
sin²∠ ≤ ε/(μ₀−μ₁) ≤ κ²·b/(a−b) = κ²·σ_k²/(σ_{k-1}² − σ_k²).
```

To rewrite this as `C·κ²·(σ_k/σ_{k-1})² = C·κ²·b/a` one needs `C ≥ a/(a−b) = σ_{k-1}²/(σ_{k-1}²−σ_k²)`
— **a relative-gap AMPLIFIER that is NOT a fixed/absolute constant** (it blows up as the gap closes,
`b↑a`). So §G/§H's "`C` absolute" is, strictly, FALSE for a SINGLE generic `n`.

**Why it is harmless (and the fix).** Along the orbit, `(σ_k/σ_{k-1})² = b/a → 0` because
`(1/n)log(σ_k/σ_{k-1}) → λ_k − λ_{k-1} < 0` (committed `tendsto_log_singularValue`, distinct
exponents). Hence EVENTUALLY `b ≤ a/2`, where the amplifier `a/(a−b) ≤ 2`, giving the clean
`sin²∠ ≤ 2·κ²·(σ_k/σ_{k-1})²` (probe `chain` C1-amplifier, COMPILED). Since L7c.4 only needs EVENTUAL
geometric decay of the increments (`Summable` is a tail property), the displayed clean RHS in
`norm_bandProjector_succ_sub_le` is correct from some `n₀(x)` onward — exactly the regime
summability lives in. **Fix to the doc: state `norm_bandProjector_succ_sub_le` either (a) with the
honest RHS `κ²·σ_k²/(σ_{k-1}²−σ_k²)` (always true), or (b) with the clean `2·κ²·(σ_k/σ_{k-1})²` under
the EVENTUAL hypothesis `σ_k ≤ σ_{k-1}/√2`. Route (a) is cleaner to prove; route (b) feeds L7c.4
directly.** Either way summability is unaffected; the crux estimate stands. The probe `chain` also
recompiles the rest of the chain: C2 (sin²→op `√(2k)`), C3/C3′ (`κ(⋀^kB) ≤ ‖B‖^k‖B⁻¹‖^k`, log/n→0),
C4/C4-const (the `λ_k−λ_{k-1}<0` log-limit), C5 (`ρⁿ` ⟹ Summable).

### I.4 Mathlib found-vs-missing delta (this pass)

**FOUND / committed (compiled against):**
- Committed: `sin_sq_le_rayleigh_deficit_div_gap`, `prod_singularValues_eq_l2_opNorm_compound`,
  `toEuclideanLin_compoundMatrix_mul`/`compoundMatrix_mul`, `singularValues_zero_sq_le_sum`,
  `cfc_eq_eigenvectorUnitary_conj`, `bandProjector`/`_indicator_mul_self`/`_rank`,
  `tendsto_log_singularValue`, `tendsto_logNorm_orbit_div_atTop_zero`(+inv),
  `eigenvalues_qpow_tendsto`, `cauchySeq_cfc_of_summable`, `exists_tendsto_cfc_of_summable`;
  internal diagonalization `hortho`/`prod_le_prod_top`/`opNorm_eq_of_ortho`; `hodgeForm_ιMulti`.
- Mathlib: `exteriorPower.pairingDual_ιMulti_ιMulti`, `Matrix.trace_mul_comm`, `Finset.mul_prod_erase`,
  `Finset.prod_le_one`, `Finset.prod_le_prod`, `Real.sq_sqrt`, `summable_geometric_of_lt_one`,
  `Summable.of_nonneg_of_le`, `Tendsto.const_mul`/`.add`, `tendsto_inv_atTop_zero`,
  `div_le_iff₀`/`le_div_iff₀` (NOTE: `div_le_div_iff` was renamed/removed — use the `iff₀` pair).

**MISSING (to BUILD, all BOUNDED, no Davis–Kahan / no principal angles / no σⱼ min-max):**
- `rayleigh_deficit_le` (L7c.3b) — assembled from committed rank-1 facts + `toEuclideanLin_compound…`.
- `opNorm_le_frobenius` (L7c.3c.0) — from `singularValues_zero_sq_le_sum`; minor norm-instance care.
- `norm_proj_sub_le_wedge` (L7c.3c.1) — trace algebra + the ELEMENTARY `k·∏≤Σ` (NO `geom_mean`).
- `norm_bandProjector_succ_sub_le` (L7c.3c), `summable_…` (L7c.4), `cauchySeq_qpow`/`L7d` — assembly.

### I.5 COMPILED-vs-argued table (this pass)

| Probe | Genuinely new step it pins | Status |
|---|---|---|
| `scratch_l7c3final_top2eig.lean` | compound TOP-2 eigenvalue identification: `μ₀=(∏σ)²`, `μ₁=prefix·σ_k²`, GAP factorization `pre·(σ_{k-1}²−σ_k²)>0`, and the `hμ₁` weighted-sum ceiling kernel | **COMPILED exit 0** (unused-var warns) |
| `scratch_l7c3final_glue.lean` | `tr(PP')=‖UᵀV‖_F²` (cyclic trace), `det(UᵀV)=⟪w,w'⟫` (det-Gram), the ELEMENTARY `k·∏cos²≤Σcos²` (no geom_mean), `P=UDUᵀ` idempotent | **COMPILED exit 0** |
| `scratch_l7c3final_chain.lean` | deficit→sin LITERAL collapse + the relative-gap AMPLIFIER correction (SURPRISE C), sin²→op `√(2k)`, `∏σ≤Mᵏ`, log/n→0 tempering, `λ_k−λ_{k-1}<0` log-limit, `ρⁿ⟹Summable` | **COMPILED exit 0** (unused-var warns) |

ARGUED on paper (not Lean-encoded this pass): the FULL diagonalization that the `hortho` weights ARE
the `Cₙ` eigenvalues (re-deriving it duplicates ~120 committed lines — instead the SCALAR
consequences feeding `μ₀,μ₁,gap,hμ₁` are compiled); the numeric tightness (`‖P−P'‖_op² ≤ 1−⟪w,w'⟫²`
sharp, `2k` necessary) from §H. No committed statement is contradicted.

### I.6 Build order (critical path)

```
L7c.1  (bandProjector = top-k orthProj; COMPILED eigproj + I.1 G4)
  └─ L7c.3b.0  compoundMatrix_mul                      [COMMITTED]
       └─ L7c.3b  rayleigh_deficit_le                  [rank-1 facts + I.0 top-2 eig + hμ₁ ceiling]
            └─ (committed sin_sq_le_rayleigh_deficit_div_gap)
  L7c.3c.0  opNorm_le_frobenius                        [committed singularValues_zero_sq_le_sum]
  L7c.3c.1  norm_proj_sub_le_wedge                     [I.1 glue: trace + k·∏≤Σ + det-Gram]
       └─ L7c.3c  norm_bandProjector_succ_sub_le       [G.3a∘3b∘3c.1; honest-RHS or eventual clean]
            └─ L7c.4  summable_… a.e.                  [I.3 chain C3–C5 + tendsto_log_singularValue]
                 └─ L7c.5  (COMMITTED cauchySeq_cfc_of_summable / exists_tendsto_cfc_of_summable)
                      └─ L7d  cauchySeq_qpow ⇒ L7_statement   [+ committed eigenvalues_qpow_tendsto]
```

Net L7c.3b→L7d remains **~5.5–8.5 sessions** (§H.6 estimate UNCHANGED). The two uncertainties are
resolved with no new HIGH node; the only correction (SURPRISE C, relative-gap amplifier) is a
statement-shape fix to `norm_bandProjector_succ_sub_le`, not new analytic content.

## J. L7c.3c CORRECTED — refined Davis–Kahan OFF-DIAGONAL route (B1 blocker fix, 2026-06-07)

> CRITICAL CORRECTNESS PASS. The orchestrator found that the §G/§H/§I route — built on the committed
> `sin_sq_le_rayleigh_deficit_div_gap` (Rayleigh-DEFICIT) + `rayleigh_deficit_le` (crude κ-bound) — is
> **CIRCULAR and yields only a NON-SUMMABLE estimate**. This pass verifies the blocker, establishes the
> CORRECT route (refined Davis–Kahan in OFF-DIAGONAL form), cross-checks it against the literature
> (Davis–Kahan 1970 via Stewart–Sun; Trung Vu's note; Columbia AML notes — all firecrawl-scraped), and
> delivers exact Lean statements with FOUR new compiled probes (`scratch_l7cJ_*.lean`, all `lake env
> lean`, exit codes read explicitly — the `lake env` wrapper masked a real `.olean`-missing error and a
> docstring parse error on early runs, exactly the §F hazard). Numerics: Python, d ≤ 6, all k, 50k+
> ill-conditioned gapped trials. THREE §G/§H/§I claims corrected (J.5 SURPRISE D/E/F). No committed
> statement is contradicted — but two committed lemmas are now BYPASSED (J.6).

### J.0 The blocker B1 — VERIFIED (the deficit route is circular / non-summable)

Committed chain: `‖Pₙ₊₁−Pₙ‖² ≤ 2k·sin²θ`, `sin²θ ≤ ε/(μ₀−μ₁)` (`sin_sq_le_rayleigh_deficit_div_gap`),
`ε = μ₀−⟨Cₙv',v'⟩ ≤ (1−1/κ²)μ₀` (`rayleigh_deficit_le`, the ONLY provable deficit bound), `μ₀−μ₁ =
μ₀(1−r²)`, `r = σₖ/σₖ₋₁`. Hence the committed bound is

```
sin²θ ≤ (1 − 1/κ²)/(1 − r²),    κ = κ(⋀ᵏB(Tⁿx)),  r = σₖ(Mₙ)/σₖ₋₁(Mₙ).
```

Along the orbit `r → 0` GEOMETRICALLY, BUT `κ` is only TEMPERED (`(1/n)log κ → 0`) with `κ ≥ κ₀ > 1`
on a positive-density set (positive Lyapunov spread). So `1 − 1/κ²` is bounded BELOW away from 0 and
does NOT decay. **NUMERICALLY CONFIRMED** (orbit simulation, `κ(⋀ᵏB)² ≈ 8100`, n = 1..25): the crude
`sin²θ` bound `→ 0.9999` and STAYS there for all n while the true `sin θ → 0` geometrically; `Σ crude`
grows ~linearly (tail ratio **1.000** ⟹ diverges). Worse, `ε ≈ μ₀ sin²θ` ALWAYS (since `⟨Cₙv',v'⟩ ≥
μ₀cos²θ`), so the deficit→sin route is **structurally circular** — it can never beat the crude κ-bound.
COMPILED as a Lean obstruction in `scratch_l7cJ_crude_fails.lean` (J4, exit 0): `crude_logLimit_zero`
proves the crude per-step ROOT-TEST log-limit is `0` (NOT `< 0`) whenever `cₙ = 1−1/κₙ² ∈ [δ,1)`, and
`crude_not_tendsto_zero` proves the crude bound is not even a null sequence. **The Rayleigh-deficit
lemma is the WRONG TOOL; B1 is real.**

### J.1 The FIX — refined Davis–Kahan OFF-DIAGONAL rank-1 sin-Θ (VERIFIED, COMPILED)

For the PERTURBED symmetric `C̃` (top unit eigvec `ṽ`, eigval `μ̃₀`), the UNPERTURBED top eigenline
`v₀` (`P = ⟨·,v₀⟩v₀`), and `ν` an upper Rayleigh ceiling of `C̃` on `v₀^⊥`:

```
sin θ(ṽ,v₀) = ‖ṽ − ⟨ṽ,v₀⟩v₀‖  ≤  ‖(I−P) C̃ v₀‖ / (μ̃₀ − ν),   (I−P)C̃v₀ = C̃ v₀ − ⟨C̃v₀,v₀⟩v₀.
```

Derivation (exact identity): from `C̃ṽ = μ̃₀ṽ`, write `ṽ = p v₀ + w` (`p=⟨ṽ,v₀⟩`, `w=(I−P)ṽ`); then
`μ̃₀ w − (I−P)C̃w = p·(I−P)C̃v₀`, take `⟨·,w⟩`, use `⟨C̃w,w⟩ ≤ ν‖w‖²` and `|p|≤1`:
`(μ̃₀−ν)‖w‖² ≤ p⟨(I−P)C̃v₀,w⟩ ≤ ‖(I−P)C̃v₀‖·‖w‖`. **LITERATURE CROSS-CHECK:** this is the eigenvector
RESIDUAL form of Davis–Kahan sin-Θ (Theorem 3 of the Columbia AML notes `‖F₁ᵀE₀‖ ≤ ‖F₁ᵀHE₀‖/δ`; the
Sylvester/residual mechanism of Trung Vu's note `‖sinΘ‖_F ≤ ‖ΔU₁‖_F/δ`). It does NOT require the
perturbation `C̃−C` to be small (`C̃ = κ²-scaled C` here): the GAIN is that the numerator `(I−P)C̃v₀`
is the OFF-DIAGONAL block, which for `C̃ = Gᵀ(HᵀH)G` only sees singular values `≤ τ₁`.

**COMPILED** (`scratch_l7cJ_offdiag_sintheta.lean`, exit 0) as the abstract lemma — the load-bearing
NEW core that REPLACES `sin_sq_le_rayleigh_deficit_div_gap`:

```lean
theorem offdiag_sin_le_residual_div_gap {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : E →ₗ[ℝ] E} {μ₀ ν : ℝ} {v₀ vt : E} (hv₀ : ‖v₀‖ = 1) (hvtnorm : ‖vt‖ = 1)
    (hev : C vt = μ₀ • vt) (hgap : ν < μ₀)
    (hν : ∀ w : E, ⟪w, v₀⟫_ℝ = 0 → ⟪C w, w⟫_ℝ ≤ ν * ‖w‖ ^ 2) :
    ‖vt - (⟪vt, v₀⟫_ℝ) • v₀‖ ≤ ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ / (μ₀ - ν)
```

Note: no `IsSymmetric` needed (the proof is pure Pythagoras-free Rayleigh + Cauchy–Schwarz + `|p|≤1`).
NUMERICALLY: the refined bound tracks the true sin almost exactly (max `sint/refined = 1.0000`, valid),
decays geometrically; `Σ refined` finite (tail ratio **0.646** ⟹ summable). **Both the blocker AND the
fix are confirmed in the same orbit experiment.**

### J.2 The off-diagonal NUMERATOR estimate (VERIFIED, COMPILED modulo SVD ceiling)

`‖(I−P) Cₙ₊₁ v₀‖ ≤ τ₀·τ₁·‖compound k B‖²`, `τ₀ = ∏_{i<k}σᵢ = ‖compound k M‖ = √μ₀`, `τ₁ = (∏_{i<k-1}σᵢ)σₖ
= √μ₁`. NUMERICALLY VERIFIED, worst ratio **0.50** (20k trials, d ≤ 6, all k — bound holds with slack).
Via `Cₙ₊₁ = adjoint(G')∘ₗG'`, `G' = H∘ₗG` (functoriality `toEuclideanLin_compoundMatrix_mul`), the
chain reduces to: for `z ⊥ v₀` unit, `⟨Cₙ₊₁v₀,z⟩ = ⟨HGv₀,HGz⟩ ≤ ‖H‖²·‖Gv₀‖·‖Gz‖ ≤ ‖H‖²·τ₀·τ₁`, using
`‖Gv₀‖ = τ₀` (top right-sing) and `‖Gz‖ ≤ τ₁` (SECOND singular value on `v₀^⊥`). **COMPILED**
(`scratch_l7cJ_offdiag_estimate.lean`, exit 0): `offdiag_estimate_modulo_svd` proves the WHOLE chain
from the operator-norm facts (`le_opNorm`, `adjoint_inner_left`, CS) MODULO the single SVD hypothesis
`hperp : ∀z⊥v₀, ‖z‖≤1 → ‖Gz‖ ≤ τ₁`. **SURPRISE D (corrects §H.1):** the §G/§H "needs only PER-VECTOR
op-norm facts; no σⱼ" is RIGHT, AND `hperp` is dischargeable WITHOUT new SVD min-max — it is exactly the
committed `plucker_eigenpair_ceiling` (PB2): `‖Gz‖² = ⟨Cₙz,z⟩ ≤ μ₁‖z‖² = τ₁²‖z‖²` for `z ⊥ v₀`.

### J.3 The denominator `μ̃₀ − ν > 0` — CORRECTED (SURPRISE E)

**The orchestrator's proposed `ν = λmax of (I−P)C̃(I−P)` and lower bound `μ̃₀−ν ≥ τ₀²(1−r²)/‖H⁻¹‖²` are
NUMERICALLY FALSE in general.** Cauchy-interlacing forces `ν ∈ [μ̃₁, μ̃₀]`, so `μ̃₀−ν ≤ gap(Cₙ₊₁)` (NOT
`≥`); the realized denominator can be **~100× smaller** than the orchestrator's lower bound
(`min denom/denomlb = 0.008`, 8k trials). It stays positive (`min ≈ 8.9e-7 > 0`) but small — compensated
by a correspondingly small off-diagonal numerator, keeping the RATIO controlled.

**The CLEAN PROVABLE route (this pass's fix):** take `ν := μ₁(Cₙ)·‖H‖²` (NOT the compression top — which
Lean cannot easily access). Then:
- `hν` holds: `∀z⊥v₀, ⟨Cₙ₊₁z,z⟩ = ‖HGz‖² ≤ ‖H‖²‖Gz‖² = ‖H‖²⟨Cₙz,z⟩ ≤ ‖H‖²μ₁‖z‖² = ν‖z‖²` —
  via per-vector op-norm + committed PB2. **VERIFIED: 0 violations / 15k trials.**
- `μ̃₀ − ν > 0` ⟺ `μ₁‖H‖² < μ̃₀`, and `μ̃₀ ≥ μ₀/‖H⁻¹‖²`, so suffices `μ₁/μ₀ = r² < 1/κ²` ⟺ `r < 1/κ`
  — the EVENTUAL regime (since `r → 0`, `κ` tempered). **VERIFIED: 0 violations in r < 1/κ regime.**

This is CLEANER than the orchestrator's route and bypasses the compression-eigenvalue access problem.

### J.4 The summable per-step bound + root test (VERIFIED, COMPILED)

Composing J.1∘J.2∘J.3 with `ν = μ₁‖H‖²`, `denom ≥ μ₀/‖H⁻¹‖² − μ₁‖H‖² = (τ₀²/‖H⁻¹‖²)(1 − κ²r²)`:

```
sin θ ≤ τ₀τ₁‖H‖² / ((τ₀²/‖H⁻¹‖²)(1−κ²r²)) = κ²·r/(1 − κ²r²),   κ = ‖⋀ᵏB‖·‖(⋀ᵏB)⁻¹‖, r = σₖ/σₖ₋₁.
```

**EXPONENT a = 2, CONSTANT C = 1** (eventually). NUMERICALLY: `sin θ ≤ κ²r/(1−κ²r²)` holds with max ratio
**0.189** in the eventual regime `r < 1/κ` (0 violations, 20k trials). The per-step band-projector bound:
`‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·sin θ_wedge ≤ √(2k)·κ²·r/(1−κ²r²)` (back-transport committed
`norm_proj_sub_le_wedge` + `inner_hodgeTrivialization_ιMulti`). SUMMABLE by the ROOT TEST: `(1/n)log(RHS)
→ λₖ − λₖ₋₁ < 0` (committed `tendsto_log_singularValue` two indices; `κ²` tempered via
`tendsto_logNorm_orbit_div_atTop_zero` + inv, log/n → 0). **COMPILED** (`scratch_l7cJ_summable.lean`, J3):
`summable_of_logLimit_neg` (root-test engine: `(1/n)log aₙ → L < 0` + `aₙ ≥ 0` ⟹ `Summable aₙ`) and
`summable_of_eventually_le_geometric` (geometric tail ⟹ summable). The contrast J4 (`crude_logLimit_zero`,
limit `= 0`) is precisely the input the root test REJECTS.

### J.5 EXACT corrected node signatures (replaces §I.2)

```lean
-- L7c.3a (NEW CORE, COMPILED) — refined off-diagonal sin-Θ (abstract, real IPS). REPLACES the deficit lemma.
theorem offdiag_sin_le_residual_div_gap … (as in J.1) …

-- L7c.3b (REPLACES committed `rayleigh_deficit_le`) — the off-diagonal numerator + ν ceiling, cocycle.
--   numerator: ‖(I−Pₙ) Cₙ₊₁ v₀‖ ≤ ‖compound k M‖·(∏_{i<k-1}σᵢ·σₖ)·‖compound k B‖²
--   ceiling  : ν := (∏_{i<k-1}σᵢ²·σₖ²)·‖compound k B‖²  (from committed PB2 `plucker_eigenpair_ceiling`)
--   gap      : μ̃₀ − ν > 0  for σₖ/σₖ₋₁ < 1/κ(⋀ᵏB)   (EVENTUAL)
-- proof: offdiag_estimate_modulo_svd (COMPILED) + plucker_eigenpair_ceiling (committed) + per-vector op-norm.

-- L7c.3c (UNCHANGED shape) — increment bound, now via offdiag_sin_le_residual_div_gap ∘ L7c.3b ∘ back-transport
theorem norm_bandProjector_succ_sub_le … :
    ‖bandProjector A T χ (n+1) x - bandProjector A T χ n x‖
      ≤ Real.sqrt (2 * kⱼ) * (κ(⋀^kⱼ B))² * (σ kⱼ Mₙ / σ (kⱼ-1) Mₙ) / (1 - (κ²·r²))
-- honest RHS carries 1/(1−κ²r²); EVENTUALLY (r < 1/(√2·κ)) this is ≤ 2, giving clean √(2kⱼ)·2·κ²·r.

-- L7c.4 (COMPILED engine) — summability via root test
theorem summable_of_logLimit_neg (a : ℕ → ℝ) (hnn : ∀ n, 0 ≤ a n) (hpos : ∀ᶠ n in atTop, 0 < a n)
    {L : ℝ} (hL : L < 0) (hlog : Tendsto (fun n => (n:ℝ)⁻¹ * Real.log (a n)) atTop (𝓝 L)) : Summable a
```

### J.6 Compiled-vs-argued ledger + the revised ladder (which committed lemmas SURVIVE / are BYPASSED)

| Probe | Genuinely new step it pins | Status |
|---|---|---|
| `scratch_l7cJ_offdiag_sintheta.lean` | **L7c.3a refined off-diagonal sin-Θ** (the new load-bearing core, abstract real IPS, no symmetry, no CFC) | **COMPILED exit 0** |
| `scratch_l7cJ_offdiag_estimate.lean` | off-diagonal numerator chain `⟨Cₙ₊₁v₀,z⟩ ≤ τ₀τ₁‖H‖²` modulo PB2 ceiling `hperp`; residual ⊥ v₀; Gram-Rayleigh = ‖·‖² | **COMPILED exit 0** |
| `scratch_l7cJ_summable.lean` | root-test engine `summable_of_logLimit_neg` + geometric-tail `summable_of_eventually_le_geometric` | **COMPILED exit 0** |
| `scratch_l7cJ_crude_fails.lean` | **the B1 obstruction**: crude root-test log-limit `= 0` (not `< 0`); crude bound not null | **COMPILED exit 0** |

ARGUED + verified NUMERICALLY only (Python, not Lean): the crude orbit-divergence (tail ratio 1.0) vs
refined convergence (0.646); off-diag numerator ratio ≤ 0.50; `ν = μ₁‖H‖²` ceiling (0 viol/15k) + gap
positivity in `r<1/κ` (0 viol/15k); final `sin ≤ κ²r/(1−κ²r²)` (max 0.189, 0 viol/20k, exponent a=2).

**COMMITTED pieces that SURVIVE and compose into the corrected route:**
`plucker_eigenpair_ceiling` (PB2 — now supplies the `ν` ceiling directly), `eigenpair_ceiling_transport`,
`norm_proj_sub_le_wedge` (FULLY PROVED back-transport, unchanged), `inner_hodgeTrivialization_ιMulti`
(det-Gram = wedge inner = `⟨ṽ,v₀⟩`), `compoundMatrix_gram`, `toEuclideanLin_compoundMatrix_mul`
(functoriality `G' = H∘G`), `rayleigh_compound_eq_norm_sq`, `rayleigh_compound_mul_le`,
`tendsto_log_singularValue`, `tendsto_logNorm_orbit_div_atTop_zero` (+inv), `eigenvalues_qpow_tendsto`,
`cauchySeq_cfc_of_summable`.

**COMMITTED pieces now BYPASSED (the deficit route):**
`sin_sq_le_rayleigh_deficit_div_gap` (OseledetsLimit.lean:851 — the deficit lemma, REPLACED by
`offdiag_sin_le_residual_div_gap`) and `rayleigh_deficit_le` (ExteriorNorm.lean:1495 — the crude κ-bound
`ε ≤ (1−1/κ²)μ₀`, which only ever produces the non-summable estimate; REPLACED by the off-diagonal
numerator estimate). Their helper `rayleigh_deficit_kernel` is also orphaned. These remain SOUND theorems
(no false statement) — they are simply the WRONG TOOL for summability.

### J.7 Revised risk-tagged sub-ladder (supersedes §I.6 / §H.6 for the crux)

| # | Lemma | Risk | Effort | Probe / route |
|---|---|---|---|---|
| L7c.3a | `offdiag_sin_le_residual_div_gap` (abstract refined off-diagonal sin-Θ) | **LOW (COMPILED)** | <0.5 | `scratch_l7cJ_offdiag_sintheta` |
| L7c.3b.0 | compound-mult `⋀^k(B·M) = (⋀^kB)(⋀^kM)` | LOW | — | **COMMITTED** `compoundMatrix_mul` |
| L7c.3b.ν | `ν = μ₁(Cₙ)‖⋀ᵏB‖²` ceiling for `Cₙ₊₁` on `v₀^⊥` (PB2 + per-vector op-norm) | **LOW–MED** | 0.5–1 | `offdiag_estimate_modulo_svd` (COMPILED) + committed PB2 |
| L7c.3b | off-diagonal numerator `‖(I−P)Cₙ₊₁v₀‖ ≤ τ₀τ₁‖⋀ᵏB‖²` | **MED** | 1–1.5 | `offdiag_estimate_modulo_svd` (COMPILED) + PB2 `hperp` |
| L7c.3b.gap | `μ̃₀ − ν > 0` eventual (`σₖ/σₖ₋₁ < 1/κ`) | MED | 0.5 | committed singular-value sandwich; eventual via `tendsto_log_singularValue` |
| L7c.3c | assemble `norm_bandProjector_succ_sub_le` (3a∘3b∘back-transport) | MED | 1–1.5 | committed `norm_proj_sub_le_wedge` + `inner_hodgeTrivialization_ιMulti` |
| L7c.4 | `summable_…` a.e. (root test) | **LOW (COMPILED)** | 0.5 | `scratch_l7cJ_summable` + `tendsto_log_singularValue` + tempered factor |
| L7c.5/L7d | (committed packaging + assembly) | LOW–MED | 1.5–2 | committed `cauchySeq_cfc_of_summable`, `eigenvalues_qpow_tendsto` |

**Critical path: L7c.3b.ν → L7c.3b → L7c.3c → L7c.4 → L7d.** The single irreducible analytic core is now
the COMPILED `offdiag_sin_le_residual_div_gap` (not an abstract block Davis–Kahan, not the bypassed
deficit lemma). Honest revised net L7c.3→L7d: **~5–7 sessions**, dominated by L7c.3b (discharging
`hperp`/`ν` via PB2 + the gap-positivity tail argument).

### J.8 Residual gaps / honest flags

1. **The clean bound is EVENTUAL, not uniform.** `μ̃₀ − ν > 0` (hence the displayed `sin ≤ κ²r/(1−κ²r²)`)
   holds only for `r < 1/κ` — confirmed positive-measure-eventually since `r → 0` geometrically while
   `κ` is tempered. Summability is a tail property, so this suffices; but `norm_bandProjector_succ_sub_le`
   must be stated either with the honest RHS `κ²σₖ²/(σₖ₋₁²/‖H⁻¹‖²·‖H‖²·… )` (always true where `denom>0`)
   or under the eventual hypothesis. This is the same EVENTUAL caveat as §I.3 SURPRISE C, now load-bearing
   for the gap, not just the amplifier.
2. **SURPRISE F:** the orchestrator's denominator identity `μ̃₀−ν ≈ κ²τ₀²(1−r²)` and its lower bound are
   FALSE in general (J.3). The fix re-defines `ν = μ₁‖H‖²` (a PROVABLE ceiling, not the realized
   compression top); the realized denominator is smaller, but the off-diagonal numerator shrinks in lock-step.
   The final bound is robust; the intermediate `≈ gap` intuition is not.
3. **`hperp`/`ν` via PB2 is the one MED node left to wire.** `offdiag_estimate_modulo_svd` is COMPILED
   modulo `hperp`; discharging `hperp` = `‖Gz‖² = ⟨Cₙz,z⟩ ≤ μ₁‖z‖²` needs identifying `v₀` (top eigvec of
   `Cₙ`) with the committed `plucker_eigenpair_ceiling`'s `i₀` and `‖toEuclideanLin(compound M) z‖² =
   ⟨adjoint∘self z, z⟩` (committed `rayleigh_compound_eq_norm_sq`). No new analytic content; bookkeeping only.
4. **No abstract block Davis–Kahan, no principal angles, no σⱼ min-max** are needed — the exterior rank-1
   reduction + the COMPILED off-diagonal lemma + committed PB2/back-transport close the route.
