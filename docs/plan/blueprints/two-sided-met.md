# Blueprint: the two-sided Oseledets theorem (splitting form)

**Target.** `ErgodicTheory.oseledets_splitting` — for an *invertible* ergodic
measure-preserving system `T : X ≃ᵐ X` and a measurable invertible cocycle generator
`A` with `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹(μ)`: exponents `λ₁ > ⋯ > λ_k`, and a measurable,
`A`-equivariant **splitting** `ℝᵈ = E₁(x) ⊕ ⋯ ⊕ E_k(x)` with
`(1/n) log‖A⁽ⁿ⁾(x)v‖ → λᵢ` and `(1/n) log‖A⁽⁻ⁿ⁾(x)v‖ → −λᵢ` for nonzero `v ∈ Eᵢ(x)`,
where `A⁽⁻ⁿ⁾(x) = (A⁽ⁿ⁾(T⁻ⁿx))⁻¹`.

References: Viana, *Lectures on Lyapunov Exponents*, §4.2 (Thm 4.2); Arnold, *Random
Dynamical Systems*, Thm 3.4.11. The route below is the standard
filtration-intersection route, adapted so that **no measurable frame selection** is
ever needed (the same design constraint that shaped the one-sided proof, see
`docs/plan/blueprints/m7-measurable-strategy-v2.md`).

**Status of this document**: blueprint only. Every Lean statement below was
typechecked as a `sorry`-skeleton against the committed library (validation
artifacts: `/tmp/ts_stmt.lean`, `/tmp/ts_phase0.lean`, `/tmp/ts_meas_inf.lean`,
`/tmp/ts_interfaces.lean`, `/tmp/ts_assembly.lean`; transient — re-create from the
snippets in this file). Phase 0 was validated with **real proofs** (zero sorry except
the conull utility); the `MeasurableSubspace.inf` *assembly* was also validated with a
real proof modulo its per-point lemma.

---

## 0. Survey answers (the six questions)

### 0.1 Invertibility encoding

Use `T : X ≃ᵐ X` (`MeasurableEquiv`) with `hT : Ergodic T μ` (the coercion
`⇑T : X → X` is automatic in `Ergodic`/`cocycle`).

**SURPRISE (positive):** Mathlib **already has everything**:

* `MeasureTheory.MeasurePreserving.symm (e : α ≃ᵐ β) : MeasurePreserving e μa μb → MeasurePreserving e.symm μb μa`
  (`Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:73`);
* `Ergodic.symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ` **and**
  `Ergodic.symm_iff` (`Mathlib/Dynamics/Ergodic/Ergodic.lean:188`).

So the anticipated "small NEW lemma" (ergodicity of the inverse) does **not** exist as
a gap; zero new ergodic-theory infrastructure is required for the encoding. Validated:
`example (hT : Ergodic T μ) : Ergodic T.symm μ := hT.symm` compiles.

Iterate bookkeeping (`T^[n] ∘ T.symm^[n] = id` etc.) is `Function.LeftInverse.iterate`
applied to `fun y => T.apply_symm_apply y` — also fully stock.

### 0.2 Backward generator and cocycle relation

`backwardGen A T x := (A (T.symm x))⁻¹`. The relation

```
cocycle (backwardGen A T) (⇑T.symm) n x = (cocycle A (⇑T) n ((⇑T.symm)^[n] x))⁻¹
```

**was proved for real** during validation (≈15-line induction; `/tmp/ts_phase0.lean`,
`cocycle_backwardGen`), using `Matrix.mul_inv_rev` (unconditional in Mathlib) and a
new trivial companion recursion `cocycle_succ'` (newest factor on the right, from
`cocycle_add` with `m = 1`). The dual form `B⁽ⁿ⁾(Tⁿy) = (A⁽ⁿ⁾y)⁻¹`
(`cocycle_backwardGen_iterate`) is a 3-line corollary and is the key identity that
makes the transversality crux work *without* moving-point singular-value arguments.

Hypothesis transfer — all proved for real in validation:

* `det ≠ 0`: `Matrix.det_nonsing_inv` + `Ring.inverse_eq_inv'`;
* measurability: `measurable_inv_matrix` (already in `ErgodicTheory/Cocycle/Norm.lean`)
  composed with `T.symm.measurable`;
* integrability swap: `MeasurePreserving.integrable_comp_of_integrable` (the idiom
  already used by `FurstenbergKesten.lean`), plus `Matrix.nonsing_inv_nonsing_inv`
  for the `(B x)⁻¹ = A (T.symm x)` rewrite.

### 0.3 Splitting encoding

**Decision: `DirectSum.IsInternal (fun i : Fin k => E i x)`** in the public statement,
proved via `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` (verified
present and applicable at `EuclideanSpace ℝ (Fin d)`; `/tmp/ts_assembly.lean`).
Rationale: a single standard Mathlib predicate downstream users can eliminate however
they like; the `iSupIndep` + `⨆ = ⊤` pair is exactly what the assembly proves anyway.
The full statement skeleton (with `IsInternal`, `E i ≠ ⊥`, equivariance, and both
growth limits) typechecks: see §1.

### 0.4 Transversality/dimension crux — full ladder

The crux is **`χ⁺(v) + χ⁻(v) ≥ 0`** (forward + backward exponents of the same vector),
from which `V(a) ⊓ U(b) = ⊥` whenever `a + b < 0`. The proof avoids both measurable
frame selection and moving-point singular values; the full ladder is Phases 3–5
(§3 below). New analytic content vs. plumbing:

| Step | Content | New analytic? |
|---|---|---|
| Kingman constant = limit of integral means | `tendsto_kingman_ergodic_means` | **YES** (the repo's `tendsto_kingman_ergodic` explicitly defers this; see §0.4.1) |
| Restricted cocycle `Cᵢ = A·P_{Vᵢ}` is a genuine cocycle | a.e. equivariance, floor trick | plumbing + 1 idea (⊔-floor for everywhere-subadditivity) |
| Restricted top exponent = `λᵢ` | Kingman + stratum witness + finite-basis bound | mild (uses one-sided growth statement only) |
| Backward-orbit envelope `limsup (1/n) log‖A⁽ⁿ⁾(T⁻ⁿx)·P_{Vᵢ(T⁻ⁿx)}‖ ≤ λᵢ` | Kingman over `T⁻¹` + means matching | **YES** (the heart) |
| `χ⁺ + χ⁻ ≥ 0`, `V(a) ⊓ U(b) = ⊥` | envelope + backward decay + `B⁽ⁿ⁾(x) = (A⁽ⁿ⁾(T⁻ⁿx))⁻¹` | linear algebra |
| invariant conull sets under `T, T⁻¹` | `exists_conull_biinvariant` (countable ∩ of iterate preimages) | plumbing, ~50 lines |
| constancy of `dim(Vᵢ ⊓ Wⱼ)` | **NOT NEEDED** in this route | — |
| complementarity counting | dims from §0.4.2 + reflection lemma (§0.4.3) + Grassmann formula | combinatorics |

**Note (surprise):** the textbook step "`x ↦ dim(Vᵢ(x) ⊓ Wⱼ(x))` is invariant, hence
a.e. constant by ergodicity" is *unnecessary*: the crux argument contradicts the
existence of **any** nonzero vector of the intersection pointwise on a conull set, so
the intersection is `⊥` a.e. directly. Ergodicity enters only through Kingman.

#### 0.4.1 The hidden Kingman gap

`ErgodicTheory/Ergodic/Kingman.lean:3393` (docstring of `tendsto_kingman_ergodic`):
*"That constant is the Fekete infimum …; identifying it with the infimum is
**deferred**."* The two-sided theorem is the first consumer that needs the
identification (to equate the Kingman constants of `gₙ` over `T` and of
`hₙ := gₙ ∘ (T.symm)^[n]` over `T.symm`, whose integral means coincide). This is
Phase 3, genuinely new but self-contained and upstreamable.

#### 0.4.2 Dimension formula (the plumbing cost)

The route needs `finrank (Vᵢ x) = #{j < d | lam0 j ≤ λᵢ}` a.e. (and the same for the
backward filtration). The committed witness family is `V'` (`SlowFlagBridge.lean`)
built from `Vslow A T (exp t) x = range (slowProjector …)`, the CFC spectral sublevel
of the sanitized limit operator `lambdaHat`, and the repo already has the orthonormal
eigenbasis with eigenvalue data
(`limitEigenbasis`, `limitEigenbasis_eigenpair_exp`: `Λ̂ (bₑ) = exp(lamSing x e) • bₑ`)
and `lamSing_eq_of_tendsto` (a.e. `lamSing x j = lam0 j`). What is missing is purely:

* `cfc f M v = f(c) • v` for an eigenvector `v` of a self-adjoint matrix `M`
  (per-point Lagrange interpolation through `cfc_congr` + `cfc_polynomial`, the same
  bypass pattern as `measurable_cfc_eqOn_polynomial` — **pointwise, so no
  measurability needed**);
* rank of a self-adjoint idempotent that is diagonal in an orthonormal basis
  (`Orthonormal.linearIndependent` + `finrank_span_eq_card`).

This is Phase 1 (~350 lines). It is the main plumbing item, but every ingredient is
already in the repo or Mathlib.

### 0.5 Measurability of `x ↦ Vᵢ(x) ⊓ Uᵢ(x)`

**Honest answer:** `MeasurableSubspace` does **not** close under `⊓` for free, and
Mathlib has **no** von Neumann alternating-projection theorem (verified by grep:
nothing under `Mathlib/Analysis/InnerProductSpace/**` matches). But the cost is
modest and the route is fully compatible with the repo's established pattern:

* Per-point lemma (`tendsto_pow_orthProj_inf`): for `S := P_K P_L P_K` (self-adjoint,
  PSD, `‖S‖ ≤ 1`), `S^n → P_{K ⊓ L}`. Finite-dimensional spectral theorem
  (`Matrix.IsHermitian.eigenvectorBasis`, already exercised by `LimitEigenbasis.lean`):
  eigenvalues lie in `[0,1]`, the `1`-eigenspace is exactly `K ⊓ L`
  (`⟨Sv, v⟩ = ‖P_L P_K v‖²` + the Cauchy–Schwarz equality chain), and `c^n → 0` for
  `c ∈ [0,1)`. ≈200 lines of clean linear algebra, **no measurability content**.
* Assembly (`MeasurableSubspace.inf`): each `x ↦ (P_{Vx} P_{Wx} P_{Vx})^n` is
  measurable (`measurable_matrix_pow`, `MeasurableMul₂`), entrywise
  `measurable_of_tendsto_metrizable` — *exactly* the pattern of
  `measurable_cfc_continuous` (`Lyapunov/Measurable.lean`). **The assembly was proved
  for real during validation** (`/tmp/ts_meas_inf.lean`; compiles with only the
  per-point lemma sorried).

Why not CFC on `P_V + P_W` (eigenvalue-2 eigenspace): the indicator at `2` is
discontinuous and the spectral gap `1 ± cos(principal angles)` varies with `x`, so
neither `measurable_cfc_eqOn_polynomial` (needs one global polynomial) nor
`measurable_cfc_continuous` (needs continuity) applies. The `S^n` route is strictly
simpler than dimension-stratification. This was flagged as the potential hidden-cost
item; verdict: **real but bounded** (~280 lines, Phase 7, fully parallelizable).

### 0.6 Final statement

Typechecked skeleton in §1 (validated verbatim in `/tmp/ts_stmt.lean`).

---

## 1. The target statement (validated)

```lean
theorem oseledets_splitting
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X ≃ᵐ X}
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (E : Fin k → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => E i x) ∧
      ∀ᵐ x ∂μ,
        DirectSum.IsInternal (fun i => E i x) ∧
        (∀ i, E i x ≠ ⊥) ∧
        (∀ i, Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (E i x)
          = E i (T x)) ∧
        (∀ i, ∀ v ∈ E i x, v ≠ 0 →
          Tendsto
            (fun n : ℕ => (n : ℝ)⁻¹ *
              Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
            atTop (𝓝 (lam i)) ∧
          Tendsto
            (fun n : ℕ => (n : ℝ)⁻¹ *
              Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                (cocycle A T n ((⇑T.symm)^[n] x))⁻¹ v‖)
            atTop (𝓝 (-lam i)))
```

Conventions: forward/backward limits are two `ℕ`-indexed `Tendsto`s (Lean-idiomatic;
the `n → −∞` limit is exactly the second one under `A⁽⁻ⁿ⁾(x) = (A⁽ⁿ⁾(T⁻ⁿx))⁻¹`,
recorded as the simp lemma `cocycle_backwardGen` of Phase 0). `d = 0` is admitted
(`k = 0`; `IsInternal` of the empty family over the zero module holds). No `[NeZero d]`
in the public statement — the dichotomy is handled in Phase 8 as in
`MultiplicativeErgodic.lean`.

---

## 2. Mathematical route

Notation: `S := T.symm`, `B := backwardGen A T`, `A⁽ⁿ⁾(x) := cocycle A T n x`,
`B⁽ⁿ⁾(x) := cocycle B S n x = (A⁽ⁿ⁾(S^[n]x))⁻¹`.

1. **One-sided, strong form, applied twice.** Forward `(T, A)`: singular spectrum
   `lam0` (antitone on `[0,d)`), `k := numExp lam0 d` distinct exponents
   `λᵢ = expEnum lam0 d i`, filtration `V` (the committed measurable witness `V'` of
   `SlowFlagBridge.lean`), **plus the new dimension formula**
   `finrank (V i x) = #{j < d | lam0 j ≤ λᵢ}` a.e. Backward `(S, B)`: same with
   `mu0`, `l := numExp mu0 d`, `μₐ`, filtration `W`.
2. **Exponent reflection.** `Σⱼ lam0 j = ∫ log|det A| dμ` (Birkhoff on the additive
   cocycle `log|det A⁽ⁿ⁾|` + per-index singular convergence + `|det| = ∏σⱼ`);
   `Σⱼ mu0 j = ∫ log|det B| dμ = −∫ log|det A| dμ`. Combined with the **crux counting
   bound** (step 4) and a pure multiset **reflection lemma**, this forces
   `mu0 j = −lam0 (d−1−j)`, hence `l = k` and `μₐ = −λ_{k−1−a}` with matching
   multiplicities. (No exterior-power identities for `‖Λ^q M⁻¹‖` needed — the
   determinant identity + majorization replaces them.)
3. **Backward-orbit restricted envelope** (the analytic heart). For each forward level
   `Vᵢ`: `gₙ(y) := log(‖A⁽ⁿ⁾(y)·P_{Vᵢ(y)}‖ ⊔ floorₙ(y))` with
   `floorₙ(y) := ∏_{j<n} σ_min(A(T^[j]y))` is an *everywhere* subadditive, integrable
   cocycle over `T` (the ⊔-floor repairs the junk-point failure of plain
   `log‖cocycle (A·P)‖`); on the biinvariant conull good set it agrees with
   `log‖A⁽ⁿ⁾·P‖`. Kingman over `T` gives constant `χᵢ`; `χᵢ = λᵢ` (≥: stratum
   witness; ≤: bound `‖A⁽ⁿ⁾P‖ ≤ Σ_{basis of Vᵢ(y)} ‖A⁽ⁿ⁾eⱼ‖` over a *pointwise
   classical* orthonormal basis + the one-sided growth statement + log-sum-max).
   Then `hₙ(x) := gₙ(S^[n]x)` is subadditive over `S` with `∫hₙ = ∫gₙ`
   (measure-preservation), so Kingman over `S` + **Phase-3 means identification**
   gives the same constant:
   `limsupₙ (1/n) log‖A⁽ⁿ⁾(S^[n]x)·P_{Vᵢ(S^[n]x)}‖ ≤ λᵢ` a.e.
4. **Crux.** For a.e. `x`, nonzero `v ∈ Vᵢ(x)` with backward decay
   `limsup (1/n) log‖B⁽ⁿ⁾(x)v‖ ≤ b`: with `vₙ := B⁽ⁿ⁾(x)v ∈ Vᵢ(S^[n]x)`
   (forward equivariance along the backward orbit) and `A⁽ⁿ⁾(S^[n]x)vₙ = v`,
   `log‖v‖ ≤ n(λᵢ + b + 2ε)` eventually — contradiction if `λᵢ + b < 0`. Hence
   `χ⁺(v) + χ⁻(v) ≥ 0` for all nonzero `v`, and `V(a) ⊓ U(b) = ⊥` for `a + b < 0`
   (sublevels at arbitrary thresholds), giving the counting bound
   `#{lam0 ≤ a} + #{mu0 ≤ b} ≤ d` consumed by step 2.
5. **Splitting assembly.** `Uᵢ := W (Fin.rev i).castSucc = {χ⁻ ≤ −λᵢ}` and
   `Eᵢ := V i.castSucc ⊓ Uᵢ`. Dims: `finrank Uᵢ = d − finrank (V i.succ)`
   (reflection), `V i.succ ⊓ Uᵢ = ⊥` (crux) ⟹ `V i.succ ⊕ Uᵢ = ⊤`
   ⟹ `finrank Eᵢ = mᵢ ≥ 1` (Grassmann). Independence:
   `⨆_{j≠i} Eⱼ ≤ U_{i−1} ⊔ V i.succ` and
   `Eᵢ ⊓ (U_{i−1} ⊔ V i.succ) = ⊥` (two crux instances). Totality:
   `V i.castSucc = Eᵢ ⊔ V i.succ` by dimension, telescoped. Equivariance:
   `Submodule.map_inf` (injective) + the two one-sided equivariances (backward one
   transported through `B (T x) = (A x)⁻¹`). Growth: `v ∈ Eᵢ \ {0}` lies in the `i`-th
   forward stratum and the `rev i`-th backward stratum (crux excludes deeper levels),
   so both one-sided growth statements apply verbatim.

---

## 3. Phases

All phases ≤ ~400 lines, each independently `lake build`-able (imports listed),
each with explicit deliverable lemmas. `sorry`-free per phase; statements below
are the validated skeleton forms.

### P0 — `ErgodicTheory/TwoSided/Invertible.lean` (~220 lines) — VALIDATED WITH REAL PROOFS

Imports: `ErgodicTheory.Cocycle.Basic`, `ErgodicTheory.Cocycle.Norm`,
`Mathlib.Dynamics.Ergodic.Ergodic`.

* `backwardGen (A) (T : X ≃ᵐ X) : X → Matrix (Fin d) (Fin d) ℝ := fun x => (A (T.symm x))⁻¹`
* `backwardGen_det_ne_zero` — proved (validation).
* `measurable_backwardGen` — proved.
* `integrableLogNorm_backwardGen : MeasurePreserving T μ μ → IntegrableLogNorm (fun x => (A x)⁻¹) μ → IntegrableLogNorm (backwardGen A T) μ` — proved.
* `integrableLogNorm_backwardGen_inv` (uses `hA`) — proved.
* `cocycle_succ' : cocycle A T (n+1) x = A (T^[n] x) * cocycle A T n x` — proved.
* `cocycle_backwardGen : cocycle (backwardGen A T) (⇑T.symm) n x = (cocycle A (⇑T) n ((⇑T.symm)^[n] x))⁻¹` — proved.
* `cocycle_backwardGen_iterate : cocycle (backwardGen A T) (⇑T.symm) n ((⇑T)^[n] y) = (cocycle A (⇑T) n y)⁻¹` — proved.
* `exists_conull_biinvariant : MeasurableSet S → μ Sᶜ = 0 → ∃ S' ⊆ S, MeasurableSet S' ∧ μ S'ᶜ = 0 ∧ (∀ x ∈ S', T x ∈ S') ∧ (∀ x ∈ S', T.symm x ∈ S')`
  — TODO (countable intersection `⋂_{n:ℕ} (T^[n])⁻¹' S ∩ ⋂_{n:ℕ} (T.symm^[n])⁻¹' S`,
  conull by measure-preservation of each iterate; ~50 lines).
* Convenience: `det_ne_zero`/`measurable`/`integrable` bundle for `(⇑T.symm, backwardGen A T)`
  so later phases can instantiate one-sided theorems in one line.

Risk: **low** (already 90% proved).

### P1 — `ErgodicTheory/TwoSided/SpectralRank.lean` (~350 lines)

Imports: `ErgodicTheory.Lyapunov.ForwardV`, `ErgodicTheory.Lyapunov.LimitEigenbasis`,
`ErgodicTheory.Lyapunov.OseledetsLimit`, `Mathlib.LinearAlgebra.Lagrange`.

* `cfc_apply_of_eigenvector (M : Matrix (Fin d) (Fin d) ℝ) (hM : IsSelfAdjoint M)
  (f : ℝ → ℝ) {c : ℝ} {v} (hv : Matrix.toEuclideanLin M v = c • v) (hv0 : v ≠ 0) :
  Matrix.toEuclideanLin (cfc f M) v = f c • v` — per-point: eigenvalue ∈ spectrum,
  Lagrange polynomial `q` interpolating `f` on the (finite) spectrum,
  `cfc_congr` + `cfc_polynomial` + `aeval`-on-eigenvector. *No measurability.*
* `finrank_range_of_orthonormal_diag (P selfadj idempotent, b : OrthonormalBasis,
  P bₑ = εₑ • bₑ, εₑ ∈ {0,1}) : finrank (range P) = #{e | εₑ = 1}`.
* `ae_finrank_Vslow` (validated statement):
  ```lean
  ∀ᵐ x ∂μ, ∀ t : ℝ,
    Module.finrank ℝ (Vslow A T (Real.exp t) x)
      = ((Finset.range d).filter (fun j => lam0 j ≤ t)).card
  ```
  via `limitEigenbasis_eigenpair_exp`, a.e. `lamSing = lam0` (from `hlam0` +
  `lamSing_eq_of_tendsto`, countable conjunction over `j < d`), and
  `exp`-monotonicity of the threshold.

Risk: **medium** — CFC/eigenvector plumbing; all in the style the repo has already
exercised (`measurable_cfc_eqOn_polynomial`, `norm_cfc_le_of_forall_eigenvalue_abs_le`).
Fallback: if the `cfc`-eigenvector route fights the API, compute
`finrank (range (slowProjector))` as `trace` (trace of an orthogonal projection =
rank; trace of `cfc f Λ̂ = Σₑ f(exp lamSing e)` via diagonalization) — same
ingredients, different normal form.

### P2 — `ErgodicTheory/TwoSided/StrongExport.lean` (~300 lines)

Imports: `ErgodicTheory.Lyapunov.AssemblyTopGap` (transitively the whole pipeline),
`ErgodicTheory.TwoSided.SpectralRank`.

* `oseledets_filtration_dims` (validated statement; `[NeZero d]`): the one-sided
  theorem with the data exposed instead of quantified —
  `∃ lam0, antitone ∧ (singular-value tendsto) ∧ ∃ V, MeasurableSubspace ∧ ∀ᵐ x,
  ⊤/⊥/strict/equivariant/growth-at `expEnum lam0 d i` ∧
  finrank (V i.castSucc x) = ((Finset.range d).filter (fun j => lam0 j ≤ expEnum lam0 d i)).card`.

Proof = re-run of the committed composition with the concrete witness: obtain `lam0`
(`exists_lam_tendsto_singularValue`); discharge `htopgap` via `topGapMassEnvelope_ae`;
build `hspec`/`hslowflag`/`hgrowth` exactly as `oseledets_filtration_of_topgap` +
`oseledets_filtration_of_upper'` do (all sub-lemmas are public:
`hspec_standing`, `hslowflag_of_upper`, `hbdd_of_fk`, `hub_of_growthFunction`,
`hlb_of_slowflag_ident`, `hgrowth_of_upper_lower`, `forward_graded_overlap'`,
`hbridge_of_forward_graded`, `limsup_le_of_mem_Vslow`, …); take
`V := V' A T lam0` (`SlowFlagBridge.lean` — everywhere-measurable, `hmeas'_V'`),
structural block from `vassembled_structure_ae` transported through
`hae_of_slowflag`; dims from `ae_finrank_Vslow` + `hslowflag`
(`V' i x = Vslow (exp λᵢ) x` on the interior by definition of `slowCutoff`).

Risk: **low–medium** — pure orchestration; ~130 lines of the existing assembly are
mirrored (no upstream file is edited). Watch: `Fin.cast` bookkeeping (precedent:
`FiltrationAssembly.lean`).

### P3 — `ErgodicTheory/TwoSided/KingmanMeans.lean` (~250 lines) — NEW ANALYTIC CONTENT

Imports: `ErgodicTheory.Ergodic.Kingman`, `ErgodicTheory.Ergodic.Birkhoff`.

* `tendsto_kingman_ergodic_means` (validated statement):
  ```lean
  ∃ c : ℝ, Tendsto (fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1)) atTop (𝓝 c) ∧
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 c)
  ```
  under the hypotheses of `tendsto_kingman_ergodic`.

Proof plan (both directions of `c = lim (∫gₙ)/n =: L`; the means converge by Fekete,
`Subadditive.tendsto_lim`):
* `c ≤ L`: for fixed `n`, iterate subadditivity: `g (m*n) x ≤ Σ_{j<m} g n (T^[jn] x)`;
  divide by `mn`, `m → ∞`; LHS → `c` (sub-sequence of an a.e. convergent sequence);
  RHS → Birkhoff average of `(1/n) gₙ` for `T^[n]` (measure-preserving; ergodicity NOT
  needed) whose conditional-expectation limit integrates to `(1/n)∫gₙ`; integrate the
  pointwise inequality.
* `c ≥ L`: Fatou on the **nonnegative** sequence `Aₙ − cdivₙ ≥ 0` where
  `Aₙ := birkhoffAverage ℝ T (g 1) (n+1)` (nonnegativity = singleton subadditivity,
  re-derive the 10-line `le_birkhoffSum_one`): `∫Aₙ = ∫g 1` and `∫cdivₙ → L`, while
  `Aₙ − cdivₙ → B − c` a.e.; Fatou gives `∫g1 − L ≥ ∫g1 − c`.

Risk: **medium** — `EReal/ofReal` Fatou bookkeeping (the Kingman file shows the
pattern); self-contained; prime upstreaming candidate.

### P4a — `ErgodicTheory/TwoSided/RestrictedCocycle.lean` (~300 lines)

Imports: P0, P3, `ErgodicTheory.Lyapunov.MeasurableSubspace`, `ErgodicTheory.Cocycle.FurstenbergKesten`.

For a *fixed* measurable family `V : X → Submodule …` (consumed at `V := Vᵢ`):

* `restGen A V x := A x * orthProjMatrix (V x)`; `sFloor A n x := ∏_{j<n} (‖(A (T^[j]x))⁻¹‖)⁻¹`.
* `restLog A V T n x := Real.log (‖cocycle (restGen A V) T n x‖ ⊔ sFloor A n x)`.
* `isSubadditiveCocycle_restLog` — *everywhere* (floor multiplicativity
  `sFloor (m+n) = sFloor m · sFloor n ∘ T^[m]`, `max(ab, cd) ≤ max(a,c)·max(b,d)` for
  nonnegatives, `Real.log` monotone; no a.e. caveat).
* `integrable_restLog` — sandwich `log (sFloor) ≤ restLog n ≤ Σ log⁺‖A∘T^[j]‖ + …`
  (mirror `integrable_logNorm_cocycle`).
* `restLog_eq_on_good` — on a biinvariant conull set where the flag equivariance holds
  along the orbit and `V ≠ ⊥`: `cocycle (restGen A V) T n y = cocycle A T n y * orthProjMatrix (V y)`
  (induction via one-step equivariance `P(Ty)·A(y)·P(y) = A(y)·P(y)`), and the `⊔` is
  absorbed (`‖A⁽ⁿ⁾P‖ ≥ σ_min(A⁽ⁿ⁾) ≥ sFloor` by `σ_min` supermultiplicativity).
* `restLog_kingman` : Kingman over `T` (via P3) — constant `χ_V` with identified means.
* Transfer: `restLog_backward_kingman` : `hₙ := restLogₙ ∘ (T.symm)^[n]` is
  subadditive over `T.symm` (index juggle through `cocycle_add`), `∫hₙ = ∫gₙ`
  (`MeasurePreserving.integral_comp'` on the iterate — small helper composing
  `T.symm` `n` times as a `MeasurableEquiv` by induction), Kingman over `T.symm`
  (via `hT.symm` + P3) — **same constant** `χ_V`.

Risk: **medium–high** (most delicate bookkeeping of the project: the ⊔-floor and the
good-set induction). Mitigation: the floor is only needed to make hypotheses
*everywhere*-true for Kingman; all identifications are a.e.

### P4b — `ErgodicTheory/TwoSided/RestrictedExponent.lean` (~300 lines)

Imports: P4a, P2.

* `limsup_log_sum_le_max` : `limsup (1/n) log (Σ_{j∈s} aⱼ(n)) ≤ max_j limsup (1/n) log aⱼ(n)`
  for finitely many eventually-positive sequences (check `Ultrametric.lean` for a
  reusable form first).
* `exists_stratum` : every nonzero `v ∈ V i x` lies in some stratum `j ≥ i`
  (finite flag descent; pure order logic on the flag).
* `restricted_const_eq` : `χ_{Vᵢ} = λᵢ`:
  * `≥` — a.e. stratum witness from strictness; on the good set
    `cocycle (restGen) n x v = A⁽ⁿ⁾x v` for `v ∈ Vᵢ(x)`;
  * `≤` — a.e. pointwise: `stdOrthonormalBasis` of `Vᵢ(y)` (classical, per-point),
    `‖A⁽ⁿ⁾P w‖ ≤ Σⱼ ‖A⁽ⁿ⁾eⱼ‖` (Bessel `|⟪eⱼ, Pw⟫| ≤ 1`), each `eⱼ` in a stratum
    `≥ i` so its growth `≤ λᵢ`, then `limsup_log_sum_le_max`; conclude through the
    a.e.-constant Kingman limit.
* `ae_limsup_restricted_backward_le` (validated statement, with `hattain` dropped —
  only the `≤` direction is consumed):
  ```lean
  ∀ᵐ x ∂μ, limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
    ‖cocycle A (⇑T) n ((⇑T.symm)^[n] x) * orthProjMatrix (V ((⇑T.symm)^[n] x))‖) atTop ≤ lam
  ```

Risk: **medium**.

### P5 — `ErgodicTheory/TwoSided/Transversality.lean` (~300 lines)

Imports: P0, P2, P4b.

* `inf_eq_bot_of_neg_sum` (validated per-point statement): from the backward-orbit
  envelope for `Vx` at rate `a`, backward decay `≤ b` on `Ux`, and `a + b < 0`:
  `Vx ⊓ Ux = ⊥`. Core: `v = A⁽ⁿ⁾(S^[n]x) (B⁽ⁿ⁾(x)v)` (P0 identities),
  `B⁽ⁿ⁾(x)v ∈ Vᵢ(S^[n]x)` (equivariance on the biinvariant good set),
  `log‖v‖ ≤ hₙ(x) + log‖B⁽ⁿ⁾(x)v‖ → −∞`.
* `ae_crux` : a.e. `x`, for all pairs of forward level `i` / backward level `a` with
  `λᵢ + μₐ < 0` (finitely many): `V i.castSucc x ⊓ W a.castSucc x = ⊥`. Assembles the
  envelope (one application of P4b per forward level), the backward growth statement
  (strata of `W`, flag descent), and `exists_conull_biinvariant`.
* `ae_counting` : at a.e. point (hence, the bound being deterministic, outright):
  `∀ a b : ℝ, a + b < 0 → #{j<d | lam0 j ≤ a} + #{j<d | mu0 j ≤ b} ≤ d`
  (thresholds→levels conversion + dims of P2 + `Submodule.finrank_sup_add_finrank_inf_eq`).

Risk: **medium** — a.e.-set juggling; mitigated by bundling all a.e. facts into one
`filter_upwards` over the biinvariant good set.

### P6 — `ErgodicTheory/TwoSided/Reflection.lean` (~320 lines)

Imports: P0, P2, `ErgodicTheory.Ergodic.Birkhoff`; pure parts import only Mathlib.

* `abs_det_eq_prod_singularValues : |M.det| = ∏ i, (toEuclideanLin M).singularValues i`
  (if not already derivable from `ExteriorNorm.lean`'s Gram-determinant section —
  check `Sprod` at `k = d` first; else: `det(MᵀM) = det M ^ 2`, eigenvalues of `MᵀM`
  are `σᵢ²`, `Matrix.IsHermitian.det_eq_prod_eigenvalues`).
* `integrable_log_abs_det` : `|log|det A x|| ≤ d·(log⁺‖A x‖ + log⁺‖(A x)⁻¹‖)`.
* `sum_lam0_eq_integral_log_abs_det` (validated statement):
  `Σ_{j<d} lam0 j = ∫ log|det (A x)| dμ` — Birkhoff (`tendsto_birkhoffAverage_ae`,
  ergodic version) vs. the sum of the `d` singular-value limits, uniqueness of a.e.
  limits at one point of the conull intersection.
* `sum_mu0_eq_neg_sum_lam0` : change of variables `MeasurePreserving.integral_comp'`
  + `det_nonsing_inv`.
* `reflect_of_counting_and_sum` (validated statement; **pure combinatorics**):
  antitone `p q` on `[0,d)`, counting bound `∀ a b, a+b<0 → #{p ≤ a} + #{q ≤ b} ≤ d`,
  `Σq = −Σp` ⟹ `∀ j < d, q j = −p (d−1−j)`. Proof: the bound at `b, a := −q(j)−ε`
  gives the sorted domination `q j ≥ −p (d−1−j)` (antitone tuples ARE their own
  sorted enumerations); pointwise `≥` + equal sums ⟹ pointwise `=`.
* Corollaries: `numExp mu0 d = numExp lam0 d`,
  `expEnum mu0 d a = −expEnum lam0 d (Fin.rev a)`, and the backward dimension formula
  `#{j | mu0 j ≤ −λᵢ} = d − #{j | lam0 j ≤ λ_{i+1}}` (with the `i+1 = k` edge).

Risk: **low–medium** (Finset/`Fin.rev` fiddle; zero deep content).

### P7 — `ErgodicTheory/TwoSided/MeasurableInf.lean` (~280 lines) — PARALLELIZABLE

Imports: `ErgodicTheory.Lyapunov.Measurable` only. Independent of P1–P6.

* `inner_projComp_eq / one_eigenspace_projComp` : for projections `P_K, P_L`:
  `(P_K P_L P_K) v = v ↔ v ∈ K ⊓ L`.
* `tendsto_pow_orthProj_inf` (validated statement):
  `Tendsto (fun n => (orthProjMatrix K * orthProjMatrix L * orthProjMatrix K) ^ n) atTop (𝓝 (orthProjMatrix (K ⊓ L)))`
  — spectral theorem for the self-adjoint contraction, eigenvalues in `[0,1]`,
  `c^n → if c = 1 then 1 else 0`.
* `MeasurableSubspace.inf` — **assembly already proved in validation**
  (`/tmp/ts_meas_inf.lean`): powers measurable, entrywise
  `measurable_of_tendsto_metrizable`.

Risk: **medium** (the per-point lemma is honest linear algebra; the pattern is
established). Fallback: none needed beyond elbow grease; if the spectral-theorem API
resists, diagonalize `S` via `Matrix.IsHermitian.spectral_theorem` exactly as
`LimitEigenbasis.lean` does.

### P8 — `ErgodicTheory/TwoSided/SplittingAssembly.lean` + statement (~400 lines)

Imports: P0–P7, `Mathlib.Algebra.DirectSum.Module`,
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`.

Toolkit verified (`/tmp/ts_assembly.lean`):
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`,
`Submodule.finrank_sup_add_finrank_inf_eq`, `Submodule.eq_top_of_finrank_eq`,
`Submodule.eq_of_le_of_finrank_eq`, `Submodule.map_inf`,
`Submodule.equivMapOfInjective` + `LinearEquiv.finrank_eq`, `Submodule.mem_sup`,
`finrank_euclideanSpace`, `Fin.rev`.

* `Esplit i x := V i.castSucc x ⊓ W (Fin.rev i).castSucc x` (after P6's `l = k`).
* `finrank_Esplit` : `= #{j | lam0 j = λᵢ} ≥ 1` (Grassmann + P5 + P6).
* `iSupIndep_Esplit`, `iSup_Esplit_eq_top` (the §2.5 lattice argument; ~120 lines of
  `Fin` bookkeeping).
* `Esplit_equivariant` (`Submodule.map_inf` + transported backward equivariance via
  `backwardGen (T x) = (A x)⁻¹`).
* `Esplit_growth_forward`, `Esplit_growth_backward` (stratum membership from two crux
  instances + the one-sided growth statements; backward rewritten through
  `cocycle_backwardGen`).
* `MeasurableSubspace (Esplit i)` := `MeasurableSubspace.inf` (P7).
* `oseledets_splitting_dim_zero` (mirror of `oseledets_filtration_dim_zero`).
* **`oseledets_splitting`** (§1) + `#print axioms` audit.

Risk: **medium** (volume of `Fin`/index bookkeeping; precedent throughout
`FiltrationAssembly.lean`).

### Dependency graph

```
P0 ──┬────────────► P4a ─► P4b ─► P5 ─┐
     │                                ├─► P8 (statement)
P1 ─► P2 ──────────►──────────────────┤
P3 ─► P4a          P6 ◄── P2, P5 ─────┤
P7 (independent) ─────────────────────┘
```

P3, P7, and (P1→P2) can run in parallel from day one; P6's reflection lemma and det
identities are also independent of P4/P5 (only `ae_counting` consumption is ordered).

---

## 4. Effort estimate

| Phase | Lines | lean-worker sessions |
|---|---|---|
| P0 | ~220 | 1 (mostly done in validation) |
| P1 | ~350 | 2 |
| P2 | ~300 | 1–2 |
| P3 | ~250 | 1–2 |
| P4a | ~300 | 2 |
| P4b | ~300 | 1–2 |
| P5 | ~300 | 1–2 |
| P6 | ~320 | 2 |
| P7 | ~280 | 1–2 |
| P8 | ~400 | 2–3 |
| **Total** | **~3,000** | **14–20 sessions** |

For calibration: the one-sided MET took ~26,000 lines; the two-sided extension is
~12% on top, with the two genuinely new analytic nodes (P3 Kingman means, P4
backward-orbit envelope) being far smaller than any of the one-sided cruxes.

---

## 5. Risk register

| # | Risk | Likelihood | Impact | Fallback |
|---|---|---|---|---|
| R1 | **P1 dimension formula** fights the CFC/eigenvector API (`cfc` on real symmetric matrices has been touchy; cf. the `IsometricContinuousFunctionalCalculus` absence noted in `Measurable.lean`) | med | blocks P2 | trace route: `rank P = trace P` for orthogonal projections, `trace (cfc f Λ̂) = Σ f(exp lamSing e)` via `Matrix.IsHermitian.spectral_theorem`; both avoid applying `cfc` to vectors |
| R2 | **P3 Fatou direction** (`c ≥ L`) — integrability/AEMeasurable bookkeeping in the `ofReal` Fatou step | med | blocks P4a transfer | mirror the exact `ENNReal.ofReal`-Fatou pattern of `int_limsup_div_integrable_aux` (same file); if `birkhoffAverage` for `T^[n]` is awkward in the `≤` direction, replace by the conditional-expectation form already exported by `Birkhoff.lean` |
| R3 | **P4a ⊔-floor bookkeeping** — everywhere-subadditivity of the floored restricted log | med | core path | the floor is the only known fix that keeps the repo's Kingman signature (`∀ m n x`); if it leaks, generalize `IsSubadditiveCocycle` to an a.e. version *inside the new file* (re-deriving `tendsto_kingman` for it by modifying on a null set — `g` can be redefined to `0` off an invariant conull set, restoring everywhere-subadditivity) |
| R4 | **P5 a.e./index juggling** — many simultaneous a.e. layers | med | delays | single bundled `GoodSet` predicate + `exists_conull_biinvariant`; all quantifiers over `Fin k × Fin k` are finite |
| R5 | **P7 per-point von Neumann lemma** — spectral theorem API for real symmetric matrices | low–med | blocks only E-measurability | the repo already drives `Matrix.IsHermitian.eigenvectorBasis` (ExteriorNorm §, LimitEigenbasis); worst case, prove `S^n v → P v` vector-wise via the eigenbasis expansion, then matrix entries via `orthProjMatrix_apply` |
| R6 | **P2 statement drift** — the strong export must restate ~70 lines of conclusion; copy-paste skew vs. `oseledets_filtration` | low | rework | the validated `/tmp/ts_interfaces.lean` statement is the contract; keep it verbatim |
| R7 | hidden `[NeZero d]` leaks into the public statement | low | cosmetic | `d = 0` branch handled exactly as `oseledets_filtration_dim_zero` |
| R8 | backward strong export needs its own `TopGapMassEnvelope` discharge | — (non-risk) | — | `topGapMassEnvelope_ae` is fully general in `(T, A)`; instantiate at `(⇑T.symm, backwardGen A T)` with the P0 hypothesis bundle |

Explicitly **not** needed (dead ends avoided by design): exterior-power norms of
inverses (`‖Λ^q M⁻¹‖`) — replaced by the determinant identity + reflection lemma;
measurable selection of orthonormal frames — replaced by per-point classical bases
inside a.e. arguments; constancy of `dim(Vᵢ ⊓ Wⱼ)` via ergodicity — replaced by the
pointwise crux; alternating-projection theory beyond the single `S^n` lemma.

---

## 6. Validation artifacts (re-creatable)

| File | Contents | Result |
|---|---|---|
| `/tmp/ts_stmt.lean` | `oseledets_splitting` statement | ✓ typechecks (sorry body) |
| `/tmp/ts_phase0.lean` | P0, real proofs | ✓ all proved except `exists_conull_biinvariant` (deliberate) |
| `/tmp/ts_meas_inf.lean` | P7 statements + assembly | ✓ assembly **proved**; per-point lemma sorried |
| `/tmp/ts_interfaces.lean` | P1, P2, P3, P4b, P5, P6 lemma statements | ✓ all typecheck |
| `/tmp/ts_assembly.lean` | P8 Mathlib toolkit | ✓ all `example`s prove |

## 7. Surprises found during blueprinting

1. **`Ergodic.symm` already exists in Mathlib** (with `symm_iff`) — the invertibility
   phase has essentially zero new ergodic-theory content.
2. **The repo's Kingman deliberately defers the constant identification**
   (`tendsto_kingman_ergodic` docstring). The two-sided theorem is the first consumer
   that requires it (P3) — this, not the filtration intersection, is the most
   load-bearing *new* analytic lemma.
3. **No ergodic constancy of intersection dimensions is needed**: the pointwise crux
   (`χ⁺ + χ⁻ ≥ 0` via the backward-orbit restricted envelope) kills nonzero
   intersection vectors outright on a conull set.
4. **Exterior powers of inverses are avoidable**: backward singular spectrum =
   reflected negated forward spectrum follows from the determinant Birkhoff identity
   plus a 1-page multiset majorization (reflection lemma), given the crux counting
   bound — no `σ(M⁻¹)` calculus.
5. `MeasurableSubspace` ⊓-closure (the flagged hidden-cost item) is real but cheap:
   the measurability *assembly* already compiles today; only one per-point
   linear-algebra lemma (`S^n → P_{K⊓L}`) is owed.
