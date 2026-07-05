# Oseledets L7 crux (§3.3) — scouting verdict

> De-risking scout, 2026-06-07. Bounded pass: feasibility verdict + risk-tagged ladder, NOT an
> implementation. Compiled probes (all `lake env lean`, repo root): `scratch_l7_cfc_synth.lean`,
> `scratch_l7_cfc_tendsto.lean`, `scratch_l7_cauchy.lean`, `scratch_l7_statement.lean`.
> Refines `oseledets-limit-route.md` §4–6 and `limit-endgame.md` §3.3–§5; corrects one stale claim
> (see surprise in §F). Does not modify committed library files.

## A. The precise Lean statement of L7

The cleanest expressible form (compiled to typecheck against the committed `ErgodicTheory.gram` in
`scratch_l7_statement.lean`):

```lean
-- gram A T n x = (cocycle A T n x)ᵀ * cocycle A T n x   (committed, OseledetsLimit.lean)
def L7_statement (μ : Measure X) (T : X → X) (A : X → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ Λ : X → Matrix (Fin d) (Fin d) ℝ,
    ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => cfc (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹)) (gram A T n x))
        atTop (𝓝 (Λ x))
```

Decisions pinned by the probes:

- **Exponent / root formulation.** The `n`-th term is `cfc (· ^ (1/(2n))) (Qₙ x)`, i.e. the CFC
  `rpow` of the *Gram matrix* `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾`. The Gram matrix is `PosSemidef` and
  `IsSelfAdjoint` (compiled, `scratch_l7_cfc_tendsto.lean` B/C'), so the CFC `rpow` is well-typed and
  noncomputable-well-defined (compiled, C; needs `open scoped MatrixOrder` + `Mathlib.Analysis.Matrix.Order`).
  This is the matrix `(Qₙ)^{1/(2n)}`, whose eigenvalues are `σᵢ(A⁽ⁿ⁾)^{1/n}` and which → `Λ`.
- **Topology of the limit.** `𝓝 (Λ x)` is the metric topology on `Matrix (Fin d) (Fin d) ℝ` (the
  scoped L2-operator metric `Matrix.Norms.L2Operator`, equivalently the entrywise/finite-dim
  topology — all equivalent in finite dimension). The space is `CompleteSpace` (compiled,
  `scratch_l7_cauchy.lean` D), so the limit, once Cauchy, exists by `cauchySeq_tendsto_of_complete`
  (compiled, E).
- **Proof must NOT use `Filter.Tendsto.cfc`** (the CFC-continuity-in-`a` lemma). See §C: its required
  instance does not exist for real matrices. The convergence must be a from-scratch Cauchy argument.

The downstream consumers fix what `Λ` must additionally satisfy (proved jointly with L7, not in the
bare statement above): `Λ x` Hermitian PosDef, eigenvalues `e^{λᵢ}` (the `tendsto_log_singularValue`
exponents), spectral-projection ranges `= lambdaSublevel` (the §3.4 bridge).

## B. Recommended proof mechanism + cheaper-route assessment

### B.1 Mechanism (the gapped self-adjoint Cauchy argument)

There is NO Mathlib infrastructure for eigenprojection convergence (§C). The mechanism must be built
from scratch:

1. **Scalar layer (DONE/verified).** `tendsto_log_singularValue` (committed) gives, a.e., genuine
   limits `(1/n) log σᵢ(A⁽ⁿ⁾) → λᵢ^{sing}`, hence `σᵢ(A⁽ⁿ⁾)^{1/n} → e^{λᵢ^{sing}}` — the eigenvalues
   of `(Qₙ)^{1/(2n)}` converge. NO new convergence theory needed (pure Kingman).
2. **Projection Cauchy (the CRUX).** For consecutive *distinct* exponents `λᵢ^{sing} > λᵢ₊₁^{sing}`,
   the eigenvalue ratio of `(Qₙ)^{1/(2n)}` across the gap is `e^{(λᵢ−λᵢ₊₁)·(1+o(1))} > 1`, so over the
   *unnormalized* `Qₙ` the ratio is `e^{(λᵢ−λᵢ₊₁)·n·(1+o(1))} → ∞`. The order-`i` spectral projector
   `Pₙ⁽ⁱ⁾` (sum of eigenprojections of `Qₙ` for the top-`i` block) is then Cauchy in operator norm:
   the standard estimate `‖Pₙ⁽ⁱ⁾ − Pₘ⁽ⁱ⁾‖ ≲ (ratio)⁻¹` via a resolvent/contour or a direct
   `gap`-controlled bound. `Matrix` is complete (D), so each `Pₙ⁽ⁱ⁾ → P⁽ⁱ⁾`; assembling the blocks
   with the scalar eigenvalues gives `(Qₙ)^{1/(2n)} → Λ := ∑ᵢ e^{λᵢ} (P⁽ⁱ⁾ − P⁽ⁱ⁺¹⁾)`.
3. **Closure.** `CauchySeq → Tendsto` via `cauchySeq_tendsto_of_complete` (E). `Λ` Hermitian PD
   because each term is, and the limit of self-adjoints is self-adjoint (continuity of `star`).

This is the 4–8 session, highest-risk node. The hard sub-piece is step 2 (the gap→projection-Cauchy
estimate), which is **new infra M-2/M-3** (§C).

### B.2 Cheaper-route hunt — VERDICT: neither Λ-dependent conjunct is fully escapable

**(i) Forward limit (conjunct 5), without Λ — PARTIAL, does NOT shrink the crux.**
For `v ∈ Vᵢ ∖ Vᵢ₊₁` we need `lim (1/n) log‖A⁽ⁿ⁾v‖ = λᵢ`, a true limit. The committed flag gives only
`limsup = specList i` (`lambdaBar_eq_on_stratum`). Adversarial analysis of the squeeze:
- The singular values bound the growth only through `σ_{d-1}(A⁽ⁿ⁾)‖v‖ ≤ ‖A⁽ⁿ⁾v‖ ≤ σ₀(A⁽ⁿ⁾)‖v‖`.
  These are the *extreme* exponents; for a generic interior stratum `i` they give `λ_{d-1} ≤ liminf`
  and `limsup ≤ λ₀`, which is FAR too weak — no per-stratum lower bound.
- To route a *specific* `v` to a *specific* exponent `λᵢ`, you must know which singular directions `v`
  charges, i.e. you need the eigenspace decomposition of `v` against `Λ`. There is no soft
  subadditive squeeze that sees the stratum index. **The liminf lower bound on an interior stratum is
  exactly the Oseledets-regularity content and is not obtainable from the limsup flag + singular
  values alone.** The ONE exception is the TOP stratum `i=0`: `limsup ≤ λ₀^{sing}` is free from
  `‖A⁽ⁿ⁾v‖ ≤ σ₀‖v‖` (modulo the M-1 *equality* `σ₀ = ‖A⁽ⁿ⁾‖`, currently only an inequality in repo),
  and FK-top gives the matching liminf — but only for `i=0`, not a general route.
- The documented fallback (`limit-endgame.md` §5a / Route I, Bochi Lemma 12–13 block-triangular
  induction) does avoid matrix convergence, but it *itself* needs the filtration MEASURABLE and
  equivariant to define the induced sub-cocycle — i.e. it needs (ii) below, which needs `Λ`. So it
  relocates rather than removes the dependency, at a cost (3–5 hard sessions) comparable to the crux.

**Conclusion:** the forward limit cannot be obtained more cheaply than via `Λ`'s eigenspaces (or the
equally-hard Route I). It does NOT shrink the crux.

**(ii) Measurability of Vᵢ, without Λ — NO cheaper route; the compound-matrix bridge does NOT help.**
Idea tested: use the new `ExteriorNorm.compoundMatrix` / `prod_singularValues_eq_l2_opNorm_compound`
bridge to get a measurable handle on `lambdaSublevel` directly (via measurable rank/kernel of compound
maps), sidestepping `Λ`. Adversarial finding:
- The compound bridge makes `x ↦ Sprod A T k n x` measurable (already used in committed
  `measurable_Sprod`) — but that is measurability of a *scalar growth product at fixed n*, NOT of the
  *limsup-sublevel subspace* `Vᵢ x = lambdaSublevel A T x (specList i)`.
- `MeasurableSubspace (Vᵢ) ≡ Measurable (x ↦ orthProjMatrix (Vᵢ x))`. The sublevel of a *limsup* has
  no measurable handle except a measurable selection of a spanning frame (Kuratowski–Ryll-Nardzewski),
  which Mathlib lacks and which `m7-measurable-strategy-v2.md` proved is a genuine dead-end (the
  "fixed dense family" idea is FALSE). Compound matrices are about exterior *norms*, not about
  selecting a frame for the sublevel; they give no projection-matrix measurability.
- The ONLY built route is the committed CFC polynomial bypass `measurable_cfc_eqOn_polynomial`, which
  needs `Λ` (the self-adjoint matrix whose CFC gap-projector equals `orthProjMatrix (Vᵢ)`).

**Conclusion:** measurability also genuinely needs `Λ`. No cheaper route shrinks the crux on either
front. This independently re-confirms `oseledets-limit-route.md` §1.

## C. Mathlib API: found vs missing (independent verification)

**FOUND (compiled against):**
- `CompleteSpace (Matrix (Fin d) (Fin d) ℝ)` — `infer_instance` (finite-dim over complete ℝ, via
  `Analysis/Normed/Module/FiniteDimension.lean:576`). Compiled, `scratch_l7_cauchy.lean` D.
- `cauchySeq_tendsto_of_complete : CauchySeq u → ∃ L, Tendsto u atTop (𝓝 L)`
  (`Topology/UniformSpace/Cauchy.lean:429`). Compiled, E.
- `Matrix.posSemidef_conjTranspose_mul_self` + `conjTranspose_eq_transpose_of_trivial` ⇒
  `(Mᵀ M).PosSemidef` and `IsSelfAdjoint (Mᵀ M)` (needs `import Mathlib.Analysis.Matrix.Order`,
  `open scoped MatrixOrder` for the `StarOrderedRing` instance). Compiled, `scratch_l7_cfc_tendsto.lean`
  B/C'.
- `cfc (· ^ p) (Mᵀ M) : Matrix (Fin d) (Fin d) ℝ` — CFC `rpow` well-typed on the Gram matrix.
  Compiled, C. (Also `CFC.sqrt`, `PosSemidef.inv_sqrt` etc. in `Analysis/Matrix/Order.lean`.)
- `Matrix.IsHermitian.instContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint`
  (`Analysis/Matrix/HermitianFunctionalCalculus.lean:97`) — the *bare* (non-isometric) CFC instance.
  This is what the polynomial bypass uses and is sufficient for L8/L10.
- All of the committed scalar layer (`tendsto_GammaK`, `tendsto_log_singularValue`,
  `sq_singularValues_eq_gram_eigenvalue`, `sigma_le_opNorm`).

**MISSING (must be BUILT; user directive = build properly, upstreamable):**
- **M-2 — CFC-continuity in the operator variable on real matrices. CONFIRMED ABSENT and
  COMPILE-PINNED.** `Filter.Tendsto.cfc` (`CFC/Continuity.lean:261`) requires
  `[IsometricContinuousFunctionalCalculus 𝕜 A IsSelfAdjoint]`, which in turn (via
  `IsSelfAdjoint.instIsometricContinuousFunctionalCalculus`, `CFC/Basic.lean:183`) requires
  `[CStarAlgebra A]`. For `A = Matrix (Fin d) (Fin d) ℝ` under the scoped L2 norm this instance does
  **not** synthesize — pinned with `#guard_msgs` in `scratch_l7_cfc_synth.lean` (compiles, exit 0),
  EVEN with `Mathlib.Analysis.CStarAlgebra.Matrix` imported. (`Matrix.instCStarRing` is over `RCLike 𝕜`
  with the scoped norm, but the *real* `CStarAlgebra ℝ`-algebra structure needed by the isometric ℝ
  instance is not in place.) So `Filter.Tendsto.cfc` is genuinely unusable here; the L7 convergence
  must be the from-scratch Cauchy argument, and L8/L10 measurability must stay on the polynomial
  bypass. **Route-doc M-2 / m7-doc line 118: CONFIRMED.**
- **M-2′ — Davis–Kahan / sin Θ / eigenprojection perturbation / eigenvalue-eigenvector continuity.**
  CONFIRMED ABSENT: grep of all Mathlib finds no `davis.kahan`, no `sinΘ`/sin-theta spectral object
  (the `sin`/`Θ` hits are all trigonometry), no eigenvalue/eigenvector continuity, no spectral
  projection / Riesz contour projection, no `spectralProjection`/`spectralMeasure`, no spectral-gap
  object. This is the true §3.3 gap and the bulk of the work.
- **M-3 — gapped matrix-limit eigenspace convergence (`(Qₙ)^{1/(2n)} → Λ` with projectors).** Absent;
  it is the theorem to be built from M-2′. Precise target = `L7_statement` (§A) plus the joint
  eigen-data conclusions.
- (Pre-existing) **M-1 equality `σ₀(f) = ‖f‖` / Courant–Fischer.** The repo has only the inequality
  `sigma_le_opNorm` (`σᵢ ≤ ‖M‖`). The reverse `‖Mv‖ ≤ σ₀‖v‖` (the per-vector top-singular bound) is
  not built; it is needed only if one pursues the (insufficient) `i=0` cheap forward bound. LOW.

## D. Compiled micro-steps (this scout) vs UNVERIFIED

| Probe file | Claim | Status |
|---|---|---|
| `scratch_l7_cfc_synth.lean` | M-2: isometric CFC ℝ-instance for real matrices FAILS to synthesize (`#guard_msgs`-pinned) ⇒ `Filter.Tendsto.cfc` unusable | **COMPILED (exit 0)** |
| `scratch_l7_cfc_tendsto.lean` | (B) `(MᵀM).PosSemidef`; (C') `IsSelfAdjoint (MᵀM)`; (C) `cfc (·^p) (MᵀM)` well-typed | **COMPILED (exit 0)** |
| `scratch_l7_cauchy.lean` | (D) `CompleteSpace (Matrix _ _ ℝ)`; (E) `CauchySeq → ∃ L, Tendsto`; (F) gap `a<b → 0<b−a` | **COMPILED (exit 0)** |
| `scratch_l7_statement.lean` | the `L7_statement` typechecks against committed `gram`; `gram` is `PosSemidef` | **COMPILED (exit 0)** |

**UNVERIFIED (asserted, not compiled — would be the actual L7 work):**
- The gap → projection-Cauchy operator-norm estimate (step B.1.2). This is M-2′/M-3 itself; no probe.
- The §3.4 bridge `range(spectral projector of Λ) = lambdaSublevel` a.e.
- The eigenvalue-data of `Λ` (`= e^{λᵢ}`, Hermitian PD) as the assembled limit.

## E. Risk-tagged sorry-free sub-lemma ladder (L7 → L13)

Refines `oseledets-limit-route.md` §5 with the mechanism pinned above. Build inside
`OseledetsLimit.lean`, then `MultiplicativeErgodic.lean`.

| # | Lemma (abbrev.) | Risk | Effort | Notes |
|---|---|---|---|---|
| L7a | `gram_posSemidef` / `gram_isSelfAdjoint` / `qpow n x := cfc (·^(1/(2n))) (gram..)` well-typed | **LOW (COMPILED)** | <0.5 sess | probes B/C/C' |
| L7b | `eigenvalues_qpow_tendsto` : eigenvalues of `qpow n x` → `e^{λᵢ}` a.e. | LOW–MED | 1 sess | from `tendsto_log_singularValue` + `sq_singularValues_eq_gram_eigenvalue` |
| L7c | **M-2′ infra**: `gap → ‖Pₙ⁽ⁱ⁾ − Pₘ⁽ⁱ⁾‖` Cauchy bound for gapped self-adjoint sequences | **HIGH (CRUX, NEW)** | 4–8 sess | Davis–Kahan-type; absent from Mathlib; the irreducible piece |
| L7d | `cauchySeq_qpow` ⇒ `oseledetsLimit Λ` exists via `cauchySeq_tendsto_of_complete` | MED | 1 sess | needs L7c; closure compiled (probe E) |
| L8 | `measurable_oseledetsLimit` | LOW–MED | 1 sess | `measurable_of_tendsto_metrizable` + `measurable_Sprod`-style entrywise; needs L7d |
| L9 | `Λ` Hermitian PD; `eigenvalues = e^{λᵢ}` | MED | 1 sess | needs L7b+L7d |
| L10 | `V i x := range(toEuclideanCLM (cfc gᵢ (Λ x)))`; `orthProjMatrix_V = cfc gᵢ Λ`; `MeasurableSubspace` | MED–HIGH | 2 sess | committed `measurable_cfc_eqOn_polynomial` (bare CFC, NOT isometric); needs L8+L9 |
| L11 | `V_ae_eq_lambdaSublevel` (§3.4 bridge) | **HIGH (CRUX)** | 2–3 sess | needs L7d+L9; limsup↔eigenspace identity |
| L12 | `tendsto_log_norm_on_stratum` (forward limit = λᵢ) | MED–HIGH | 2 sess | needs L7d+L9+L11; decompose `v` against Λ-eigenbasis |
| L13 | assemble `oseledets_filtration` | LOW | 1 sess | L11 reuses `Filtration.lean` (StrictAnti/⊤/⊥/strict/equivariant); L12 = conjunct 5; L10 = measurability |

**Critical path through the HIGH nodes: L7c → L7d → {L10, L11} → L12 → L13.** The single irreducible
new-infra node is **L7c** (the gapped-self-adjoint projection-Cauchy estimate); everything else is
LOW/MED or spike-verified.

## F. Counterexamples / pitfalls found

- **SURPRISE / stale-claim correction.** The route doc and m7 doc were right that the isometric CFC
  ℝ-instance does not synthesize — but the *reason stated* ("scoped L2 norm" only) is incomplete: it
  fails even WITH `Mathlib.Analysis.CStarAlgebra.Matrix` imported (so the `CStarRing` instance present)
  because the isometric ℝ-instance additionally needs the real `CStarAlgebra ℝ`-structure on the
  matrix algebra, which is not registered. The net verdict (M-2 unusable) is UNCHANGED and now
  `#guard_msgs`-pinned in `scratch_l7_cfc_synth.lean`. Scouting hazard: a bare background "exit 0" from
  `lake env lean` does NOT mean the file is error-free — `lake env` is a wrapper whose exit code can be
  0 while the compiled file has errors in its output; always read the output, never trust the wrapper
  exit alone. (This bit this scout once mid-pass.)
- **Equal-exponent / degenerate strata.** The Cauchy/gap argument (L7c) requires `λᵢ > λᵢ₊₁`
  *strictly*. Across a non-gap (equal consecutive singular-value exponents) the projector is NOT
  individually Cauchy — only the *summed* block projector over a maximal gap-separated group is. The
  ladder must group by *distinct* `λ` (the `specList`/`specCard` already enumerate DISTINCT exponents
  descending, so this is consistent), and L7c must be stated per-gap, not per-singular-value-index.
  Not a blocker, but a real correctness constraint: a per-`i`-singular-value projector statement would
  be FALSE when multiplicities > 1.
- **`k > d` / zero-block degeneracy.** `Sprod`/`gram` positivity is `k ≤ d`-restricted (committed
  `Sprod_pos`); for the limit, `Qₙ` is invertible PD throughout (`det ≠ 0`), so `(Qₙ)^{1/(2n)}` is PD
  and all `e^{λᵢ} > 0`; no zero eigenvalue degeneracy in the one-sided invertible setting. Safe.
- **No counterexample found** to any committed statement. The committed scalar layer, limsup flag, and
  measurability spine remain sound. The only surprise is the import-subtlety correction above; the
  mathematical verdict (Λ unavoidable, crux = L7c, both cheaper routes fail) stands and is
  independently re-confirmed.
