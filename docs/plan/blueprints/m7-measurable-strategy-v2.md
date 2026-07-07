# M7 measurability — corrected strategy v2 (Route B, CFC, crux compiled)

> Author: adversarial verification pass, 2026-06-06.
> Supersedes `m7-measurable-strategy.md` (Strategy A). The v1 plan parked the kernel
> `measurable_starProjection_apply` as a permanent `BLOCKED` sorry. This v2 plan REPLACES that kernel
> with a concrete construction whose make-or-break crux **compiles sorry-free** (see
> `/workspaces/lean4-oseledets/scratch_m7_spike.lean`, `lake env lean`-clean, exit 0).

## 0. Verdict

**Adopt Route B (concrete CFC spectral projections), but via the POLYNOMIAL BYPASS, not via
`continuousOn_cfc`.** The v1 plan's rejection of Route B rested on two claims that are *correct in
isolation but miss the actual construction*:

- v1: "CFC needs `cfc 1_{(-∞,t]}`, an indicator, discontinuous at `t`." — TRUE for a fixed-threshold
  spectral cut. The fix (and the explicit content of the orchestrator's Route B) is a **continuous
  gap function** `gᵢ`: `= 1` above `e^{λᵢ}`, `= 0` below `e^{λ_{i+1}}`, linear in the gap. Because
  the Lyapunov spectrum is a.e. a FIXED gapped set, `gᵢ` is locally constant on a neighborhood of the
  *whole* a.e. spectrum, so it can be replaced by a fixed interpolating polynomial there.
- v1: "no eigenprojection measurability in Mathlib." — TRUE, and we never use one. We never touch
  eigenvectors/eigenprojections; the projection comes out of `cfc` as a single algebra element.

**The real obstacle is different from what v1 stated, and I found it by compiling:**
`continuousOn_cfc` (Continuity.lean:235) requires `[IsometricContinuousFunctionalCalculus 𝕜 A p]`.
This instance does **NOT** synthesize for `A = Matrix (Fin d) (Fin d) ℝ`:

```
-- VERIFIED by infer_instance FAILURE (scratch probe, now deleted):
--   IsometricContinuousFunctionalCalculus ℝ (Matrix (Fin d) (Fin d) ℝ) IsSelfAdjoint   -- FAILS
--   CStarAlgebra (Matrix (Fin d) (Fin d) ℂ)                                           -- not registered
-- The generic instance `IsSelfAdjoint.instIsometricContinuousFunctionalCalculus`
-- (Basic.lean:183) needs a COMPLEX `CStarAlgebra A`, which `Matrix .. ℝ` can never be
-- (CStarAlgebra extends NormedAlgebra ℂ A). Even for `Matrix .. ℂ` it diamonds against the
-- Hermitian CFC instance and fails to fire.
```

So the `continuousOn_cfc` route is itself BLOCKED at the instance level. **The polynomial bypass
avoids it entirely**, using only the *bare* `ContinuousFunctionalCalculus ℝ (Matrix .. ℝ) IsSelfAdjoint`
(which DOES synthesize — `Matrix.IsHermitian.instContinuousFunctionalCalculus`,
HermitianFunctionalCalculus.lean:97).

### Rejected routes, with the disproving objection

| Route | Objection (verified) |
|---|---|
| **A (v1: fixed-threshold limsup flag) + fixed-family selection** | Step-7 "fixed family spans every subspace" is the dead-end #1 falsehood; v1 itself flagged it and parked the kernel as permanent BLOCKED. Does not deliver Borel. |
| **P (compact-section / Arsenin–Kunugui projection)** | Theorem absent from Mathlib (grep-confirmed: `Polish/Basic.lean` only gives analytic ⇒ universally measurable). Building Arsenin–Kunugui from scratch is a multi-file descriptive-set-theory effort; then still needs KRN selection + measurable gramSchmidt. Highest incremental cost. |
| **B via `continuousOn_cfc`** | `IsometricContinuousFunctionalCalculus ℝ (Matrix..ℝ)` does not synthesize (verified). Would require building the isometric instance for real matrices under the scoped L2 norm, compatibly with the existing Hermitian CFC instance — real upstream work, and unnecessary. |
| **B via the polynomial bypass (CHOSEN)** | No objection survives. Crux compiles. See §2. |

## 1. The construction (how it discharges the target)

Current target (MeasurableSubspace.lean): `MeasurableSubspace V := Measurable fun x ↦ orthProjMatrix (V x)`,
with `orthProjMatrix K = (toEuclideanCLM ℝ).symm K.starProjection`.

**Key definitional collapse.** Do NOT define the flag spaces abstractly as `lambdaSublevel` and then
try to project a fixed vector onto them (the `measurable_starProjection_apply` kernel — the thing v1
could not do). Instead **define the i-th concrete flag projection matrix as the CFC element**

```
Pᵢ x  :=  cfc gᵢ (Λ x)        -- a real symmetric idempotent matrix
Vᵢ x  :=  LinearMap.range (toEuclideanCLM ℝ (Pᵢ x))      -- the concrete subspace
```

where `Λ x = lim_n (cocycle A T n x)ᵀ (cocycle A T n x))^{(1/(2n))}` is the Oseledets limit matrix
(Hermitian PSD, exists a.e. — the Limit module, required regardless), and `gᵢ` is the continuous gap
function. Then, because `cfc gᵢ (Λ x)` is a self-adjoint idempotent (a star-projection), it **equals
the starProjection of its own range**, so

```
orthProjMatrix (Vᵢ x) = (toEuclideanCLM ℝ).symm (Vᵢ x).starProjection = Pᵢ x = cfc gᵢ (Λ x).
```

Measurability of `x ↦ orthProjMatrix (Vᵢ x)` is therefore literally measurability of `x ↦ cfc gᵢ (Λ x)`
— **the make-or-break crux, which is COMPILED** (§2). The `measurable_starProjection_apply` kernel
(the fixed-vector projection onto an abstractly-specified subspace) is never needed and should be
deleted from the target. The abstract `lambdaSublevel` flag is still used for the *spectral
statements* of the MET (exponents, equivariance), but its **measurability is routed through the
concrete `Vᵢ`** via the a.e. identification `Vᵢ x = lambdaSublevel A T x (λᵢ-threshold)` — see §4.

## 2. Compiled crux (`scratch_m7_spike.lean`, sorry-free, `lake env lean` exit 0)

```lean
theorem measurable_cfc_eqOn_polynomial
    (g : ℝ → ℝ) (q : Polynomial ℝ)
    (M : X → Matrix (Fin d) (Fin d) ℝ) (hM : Measurable M)
    (hMsa : ∀ x, IsSelfAdjoint (M x))
    (hagree : ∀ x, (spectrum ℝ (M x)).EqOn g q.eval) :
    Measurable (fun x => cfc g (M x)) := by
  have hpt : ∀ x, cfc g (M x) = (Polynomial.aeval (M x)) q := fun x => by
    rw [cfc_congr (hagree x), cfc_polynomial q (M x) (hMsa x)]
  simp only [hpt]; exact (measurable_aeval_matrix q).comp hM
```

Supporting (also compiled in the spike): `measurable_aeval_matrix (q) : Measurable (a ↦ aeval a q)`
by `Polynomial.induction_on` (uses repo `instMeasurableMul₂Matrix` + a one-line `instMeasurableAdd₂Matrix`);
`measurable_matrix_pow`.

Mathematical reading: on the a.e. good set the spectrum of `Λ x` is the fixed finite gapped set
`{e^{λ₁} > … > e^{λ_k}}`; a single fixed polynomial `q` interpolates the continuous `gᵢ` at those
finitely many points (`q = ∑ⱼ gᵢ(e^{λⱼ}) · Lagrange basis`), so `gᵢ.EqOn q.eval (spectrum ℝ (Λ x))`,
giving `cfc gᵢ (Λ x) = aeval (Λ x) q`, polynomial — hence measurable — in `Λ x`. **No measurable
selection, no analytic sets, no Grassmannian, full Borel.**

## 3. Verified Mathlib citations (each `#check`'d / grep'd / compiled)

| Fact | Location | Status |
|---|---|---|
| `Matrix.IsHermitian.instContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint` | `Analysis/Matrix/HermitianFunctionalCalculus.lean:97` | `infer_instance` ✓ (compiled) |
| `cfc_congr {f g} (hfg : (spectrum R a).EqOn f g) : cfc f a = cfc g a` | `…/CFC/Unital.lean:417` | used in spike ✓ |
| `cfc_polynomial (q) (a) (ha : p a) : cfc q.eval a = aeval a q` | `…/CFC/Unital.lean:593` | used in spike ✓ |
| `Polynomial.aeval_C`, `aeval_X`, `aeval_monomial`, `induction_on` | `Algebra/Polynomial/AlgebraMap.lean:297` etc. | used in spike ✓ |
| `instMeasurableMul₂Matrix` | repo `ErgodicTheory/Cocycle/Basic.lean:78` | reused ✓ |
| `Submodule.range_starProjection : range U.starProjection = U` | `…/Projection/Basic.lean:277` | for §1 bridge |
| `Submodule.isIdempotentElem_starProjection`, `eq_starProjection_of_mem_of_inner_eq_zero` | `…/Projection/Basic.lean:273,211` | for §1 bridge |
| `measurable_of_tendsto_metrizable (hf) (lim) : Measurable g` | `…/BorelSpace/Metrizable.lean:51` | for `Λ` measurability |
| `Matrix.toEuclideanCLM` (ℝ) symm | used by `orthProjMatrix` already | reused |
| `IsometricContinuousFunctionalCalculus ℝ (Matrix..ℝ) IsSelfAdjoint` | — | **does NOT synthesize** (verified). NOT used. |
| `continuousOn_cfc` | `…/CFC/Continuity.lean:235` | needs the missing isometric instance. NOT used. |
| Borel projection of Borel set (Route P) | absent (`Polish/Basic.lean` only analytic) | NOT used. |

## 4. Lemma ladder for `ErgodicTheory/Lyapunov/Measurable.lean` (revised)

Reuse from v1 (unchanged, HIGH): `measurable_lambdaBar_apply`, `orthProjMatrix_apply`,
`measurable_orthProjMatrix_iff`, the ergodic-constancy chain (`specCard_ae_const`, `specList_ae_const`).

New / revised:

1. `measurable_aeval_matrix`, `measurable_matrix_pow`, `instMeasurableAdd₂Matrix` — **DONE** (spike).
   Move into `ErgodicTheory/Cocycle/Basic.lean` next to `instMeasurableMul₂Matrix`. LOW.
2. `measurable_cfc_eqOn_polynomial` — **DONE** (spike). The crux. LOW (given 1).
3. `measurable_OseledetsLimit : Measurable Λ` — from the Limit module's pointwise a.e. convergence via
   `measurable_of_tendsto_metrizable` + `measurable_cocycle`. Depends on Limit module. MEDIUM, but the
   convergence is proven there for the MET conclusion regardless ⇒ near-zero incremental cost.
4. `gapPolynomial : Fin k → Polynomial ℝ` and `gapPoly_eqOn` — Lagrange interpolation of the gap step
   at the fixed spectrum `{e^{λⱼ}}`; `gapPoly_eqOn x : (spectrum ℝ (Λ x)).EqOn gᵢ (gapPolynomial i).eval`
   on the a.e. good set. MEDIUM (algebraic; `Lagrange.interpolate` is in Mathlib).
5. `Pᵢ := cfc gᵢ (Λ ·)` is a star-projection: `IsIdempotentElem (Pᵢ x)` + `IsSelfAdjoint (Pᵢ x)`
   from `cfc_idempotent`/`cfc.IsSelfAdjoint` on the a.e. good set. MEDIUM.
6. `orthProjMatrix_Vᵢ_eq_cfc : orthProjMatrix (Vᵢ x) = cfc gᵢ (Λ x)` — the §1 collapse, via
   `range_starProjection` + the self-adjoint-idempotent ⇒ starProjection bridge. MEDIUM (elementary).
7. `measurableSubspace_Vᵢ : MeasurableSubspace Vᵢ` [terminal] — combine 2+3+4+6 +
   `Measurable.piecewise` on the measurable a.e. good set (junk value `⊥`/`0` elsewhere). HIGH (given above).
8. `Vᵢ_ae_eq_lambdaSublevel` — the abstract=concrete identification (L5.5). This is the ONLY genuinely
   deep obligation, and it is **required for the MET conclusion anyway** (the limsup exponents must be
   shown to equal the SVD/limit exponents). Measurability of the abstract flag is then inherited a.e.
   from `measurableSubspace_Vᵢ`.

## 5. Build-cost estimate & confidence

| Item | Incremental cost (measurability-specific) | Confidence |
|---|---|---|
| Crux + matrix-algebra infra (1,2) | DONE, compiled | CERTAIN |
| `Λ` measurable (3) | ~20 lines, gated on Limit module existing | HIGH |
| Gap polynomial / interpolation (4) | ~40–80 lines | MEDIUM-HIGH |
| Star-projection facts + collapse (5,6) | ~60–100 lines | MEDIUM-HIGH |
| Terminal `measurableSubspace_Vᵢ` (7) | ~40 lines glue | HIGH |
| `Vᵢ = lambdaSublevel` a.e. (8) | the MET's deep theorem — **NOT measurability-incremental** | (lives in L5.5) |

Net measurability-incremental cost beyond the (independently-required) Limit and L5.5 layers:
**roughly one file, ~250 lines, no new Mathlib gaps.** This is dramatically less than Route P
(a descriptive-set-theory subproject) and avoids the permanent `BLOCKED` sorry of v1.

## 6. Build-order interaction (recommended change)

v1 placed M7 standalone on the abstract flag, ending in a BLOCKED kernel. v2 makes M7's terminal
measurability **depend on the Limit module** (for `Λ`) and defines the concrete `Vᵢ` there. Therefore:

- **Build the Limit module (Oseledets limit `Λ`, a.e. convergence) BEFORE the terminal M7 lemma.**
  The crux (§2) and matrix infra (§4.1–2) are independent and can land now (they are compiled).
- Define the concrete subspaces `Vᵢ` in / alongside the Subbundle module; M7 supplies their
  measurability, and L5.5 supplies `Vᵢ = lambdaSublevel` a.e. This **inverts** v1's claimed dependency
  (v1 said "M7 is a prerequisite of L5.2's measurable frame"); under v2 there is no measurable-frame
  selection at all — the projection is a single CFC element — so the frame/selection sub-arc of v1
  (steps 7–9 there: `measurableFrame`, `gramSchmidt` measurability) is **deleted**.
- Net: remove the v1 frame-selection sub-arc; add a thin `Λ`-measurability lemma + the CFC collapse.

## 7. Surprises (highest-value)

1. **The stated v1 reason for rejecting Route B was not the real blocker.** v1 said "CFC can't do it
   (indicator discontinuous)"; in fact a continuous gap function handles it. The ACTUAL blocker for
   the *continuity*-based CFC route is a missing **typeclass instance**
   (`IsometricContinuousFunctionalCalculus ℝ (Matrix..ℝ)`), discoverable only by compiling — exactly
   the step both prior paper-only passes skipped.
2. **The polynomial bypass needs neither that instance nor `continuousOn_cfc`.** `cfc_congr` +
   `cfc_polynomial` reduce the projection to `aeval (Λ x) q`, a polynomial in the matrix, on the a.e.
   good set. This is strictly cheaper and fully Borel.
3. **The `measurable_starProjection_apply` kernel — the thing the entire v1 plan was organized around
   and could not discharge — is ELIMINABLE, not just hard.** By defining `Vᵢ` as a CFC-projection
   range, `orthProjMatrix (Vᵢ x)` is *definitionally* `cfc gᵢ (Λ x)`; there is no fixed-vector
   projection onto an abstract subspace to compute. The hard selection problem was an artifact of
   choosing the abstract `lambdaSublevel` as the *primary* object instead of the concrete CFC range.
