# Mathlib survey: Ergodic theory (for Oseledets MET)

Survey of the **existing** Mathlib 4 API relevant to formalizing the Oseledets
multiplicative ergodic theorem (MET). Read directly from the Mathlib source tree
at `.lake/packages/mathlib/Mathlib`. Paths below are relative to the mathlib
package root (`.lake/packages/mathlib/`).

## Executive summary (the load-bearing questions)

| Question | Answer |
|---|---|
| 1. Kingman's subadditive ergodic theorem | **NOT FOUND.** No `Kingman`, no a.e. convergence of subadditive cocycles. Only Fekete's lemma (deterministic) exists: `Subadditive.tendsto_lim`. |
| 2. Birkhoff *pointwise* ergodic theorem (a.e. convergence of Birkhoff averages) | **NOT FOUND.** `birkhoffSum`/`birkhoffAverage` are defined, and the **von Neumann *mean* ergodic theorem** (L²/Hilbert, operator form) exists — but there is **no** a.e./pointwise convergence theorem for measure-preserving maps. |
| 3. Furstenberg–Kesten theorem | **NOT FOUND.** The string `furstenberg`/`kesten` appears nowhere in Mathlib. |
| 4. Measure-preserving / ergodicity API | **FOUND, mature.** `MeasurePreserving`, `PreErgodic`, `Ergodic`, `QuasiErgodic`, `Conservative`, invariant-function-is-a.e.-constant lemmas. |
| 5. Conditional expectation API (for L¹ proof) | **FOUND, mature.** `condExp` (`μ[f|m]`), tower property, `setIntegral_condExp`, conditional Jensen, plus `MeasurableSpace.invariants f` (the invariant σ-algebra). |

Also confirmed **NOT FOUND**: `oseledets`, `lyapunov`, `multiplicative ergodic`
(no prior art for the target theorem itself — expected).

---

## Found API

### A. Subadditivity / Fekete (deterministic only)

File: `Mathlib/Analysis/Subadditive.lean`

- **def** `Subadditive (u : ℕ → ℝ) : Prop` := `∀ m n, u (m + n) ≤ u m + u n`.
  The plain real-sequence notion of subadditivity.
- **def** `Subadditive.lim (_h : Subadditive u) : ℝ` := `sInf ((fun n => u n / n) '' Ici 1)`.
  Candidate limit of `u n / n`.
- **theorem** `Subadditive.lim_le_div (hbdd : BddBelow (range fun n => u n / n)) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n / n`.
- **theorem** `Subadditive.apply_mul_add_le (k n r) : u (k*n + r) ≤ k * u n + u r`.
- **theorem** `Subadditive.tendsto_lim (hbdd : BddBelow (range fun n => u n / n)) : Tendsto (fun n => u n / n) atTop (𝓝 h.lim)`.
  **Fekete's lemma**: a bounded-below subadditive sequence's `u n / n` converges.

> **Role in MET.** This is the *deterministic* skeleton. Kingman's theorem is the
> a.e./stochastic upgrade: for a subadditive cocycle `g_{m+n} ≤ g_m + g_n ∘ f^m`
> over a measure-preserving `f`, `g_n / n` converges a.e. (and in L¹). Fekete is
> what one applies pointwise *after* the hard ergodic work, or as the model for
> the limit object. **Kingman itself must be built.**

### B. Birkhoff sums & averages (definitions + algebra; NO ergodic convergence)

Files: `Mathlib/Dynamics/BirkhoffSum/{Basic,Average,NormedSpace}.lean`

- **def** `birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M` := `∑ k ∈ range n, g (f^[k] x)` (`[AddCommMonoid M]`).
- **def** `birkhoffAverage (R) (f : α → α) (g : α → M) (n : ℕ) (x : α) : M` := `(n : R)⁻¹ • birkhoffSum f g n x` (`[DivisionSemiring R] [Module R M]`).
- Cocycle/algebra lemmas (Basic): `birkhoffSum_succ`, `birkhoffSum_succ'`,
  `birkhoffSum_add (m n) : birkhoffSum f g (m+n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x)`,
  `birkhoffSum_add'` (additivity in `g`), `birkhoffSum_apply_sub_birkhoffSum`,
  `birkhoffSum_of_comp_eq` (invariant `g`), `Function.IsFixedPt.birkhoffSum_eq`.
- Average lemmas (Average): `birkhoffAverage_add/sub/neg`,
  `birkhoffAverage_of_comp_eq`, `birkhoffAverage_apply_sub_birkhoffAverage`,
  `map_birkhoffAverage`, `birkhoffAverage_congr_ring`.
- Normed/metric estimates (NormedSpace): `dist_birkhoffAverage_birkhoffAverage_le`,
  `tendsto_birkhoffAverage_apply_sub_birkhoffAverage` (the "almost invariant"
  difference → 0 when `g` bounded along the orbit), `uniformEquicontinuous_birkhoffAverage`,
  `isClosed_setOf_tendsto_birkhoffAverage`, `Function.IsFixedPt.tendsto_birkhoffAverage`.

> **Role in MET.** `birkhoffSum_add` is *exactly* the additive-cocycle identity;
> the subadditive cocycle `g_{m+n} ≤ g_m + g_n ∘ f^[m]` generalizes it. These give
> the algebra for free; the convergence theorem (Birkhoff/Kingman) does not exist.

### C. Mean (von Neumann) ergodic theorem — the ONLY ergodic-convergence theorem present

File: `Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean`

- **theorem** `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure (f : E →ₗ[𝕜] E) (hf : LipschitzWith 1 f) (g : E →L[𝕜] LinearMap.eqLocus f 1) (hg_proj …) (hg_ker …) (x : E) : Tendsto (birkhoffAverage 𝕜 f id · x) atTop (𝓝 (g x))` (normed-space version).
- **theorem** `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (f : E →L[𝕜] E) (hf : ‖f‖ ≤ 1) (x : E) : Tendsto (birkhoffAverage 𝕜 f id · x) atTop (𝓝 ((LinearMap.eqLocus f 1).orthogonalProjection x))`.
  **Von Neumann Mean Ergodic Theorem** in a Hilbert space (`[RCLike 𝕜] [InnerProductSpace 𝕜 E] [CompleteSpace E]`).

> **Role in MET.** This is L²-convergence of an *operator's* Birkhoff averages to a
> projection. It is NOT the pointwise (a.e.) Birkhoff theorem and does not give
> Kingman. Possibly reusable as a lemma in some proof strategies, but not the core.

### D. Measure-preserving maps

File: `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean` (namespace `MeasureTheory`)

- **structure** `MeasurePreserving (f : α → β) (μa) (μb) : Prop` with fields `measurable : Measurable f`, `map_eq : map f μa = μb`.
- Key lemmas: `MeasurePreserving.id`, `.comp`, `.symm` (for `α ≃ᵐ β`),
  `.iterate (hf) : ∀ n, MeasurePreserving f^[n] μ μ`, `.measure_preimage`,
  `.quasiMeasurePreserving`, `.sigmaFinite`, `.sfinite`, `.smul_measure`,
  `.exists_mem_iterate_mem` (finite measure ⇒ recurrence seed),
  `Measurable.measurePreserving`.

> **Role in MET.** `MeasurePreserving f μ μ` + `.iterate` is the hypothesis on the
> base dynamics. `.measure_preimage`/invariance feed the cocycle integrability and
> the conditional-expectation step.

### E. Ergodicity

File: `Mathlib/Dynamics/Ergodic/Ergodic.lean`

- **structure** `PreErgodic (f : α → α) (μ) : Prop` — field `aeconst_set : MeasurableSet s → f ⁻¹' s = s → EventuallyConst s (ae μ)` (invariant measurable sets are null or co-null).
- **structure** `Ergodic (f) (μ) : Prop extends MeasurePreserving f μ μ, PreErgodic f μ`.
- **structure** `QuasiErgodic (f) (μ) : Prop extends QuasiMeasurePreserving f μ μ, PreErgodic f μ`.
- Lemmas: `PreErgodic.ae_empty_or_univ`, `.prob_eq_zero_or_one`, `.of_iterate`;
  `Ergodic.quasiErgodic`, `Ergodic.ae_empty_or_univ_of_{preimage,ae_le,image}_ae_le(')`,
  `Ergodic.symm`/`symm_iff`; `MeasurePreserving.ergodic_of_ergodic_semiconj`, `ergodic_conjugate_iff`.

File: `Mathlib/Dynamics/Ergodic/Function.lean` — **invariant function ⇒ a.e. constant**:
- **theorem** `Ergodic.ae_eq_const_of_ae_eq_comp_ae (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c` (also `QuasiErgodic`/`PreErgodic` variants and an `AEEqFun` version `Ergodic.eq_const_of_compMeasurePreserving_eq`).

Concrete ergodic examples (for tests/instances), `Mathlib/Dynamics/Ergodic/AddCircle.lean`:
`AddCircle.ergodic_nsmul`, `ergodic_zsmul`, `ergodic_nsmul_add`, `ergodic_zsmul_add`.
Group-action ergodicity: `Mathlib/Dynamics/Ergodic/Action/{Basic,OfMinimal}.lean`.

> **Role in MET.** When `f` is ergodic the Lyapunov exponents / Kingman limit are
> a.e. *constant* — `Ergodic.ae_eq_const_of_ae_eq_comp_ae` is precisely the tool
> that collapses the invariant limit function to a constant.

### F. Conservative systems / Poincaré recurrence

File: `Mathlib/Dynamics/Ergodic/Conservative.lean` (namespace `MeasureTheory`)

- **structure** `Conservative (f) (μ) : Prop extends QuasiMeasurePreserving f μ μ` with recurrence field.
- `MeasurePreserving.conservative` (finite measure ⇒ conservative),
  `Conservative.ae_mem_imp_frequently_image_mem` (Poincaré recurrence),
  `.frequently_measure_inter_ne_zero`, `.ae_frequently_mem_of_mem_nhds`.

> **Role in MET.** Recurrence is a standard ingredient in Kingman-style proofs
> (and in the Avila–Bochi / Karlsson–Margulis approaches). Available if needed.

### G. The invariant σ-algebra (for the L¹/conditional-expectation proof)

File: `Mathlib/MeasureTheory/MeasurableSpace/Invariants.lean` (namespace `MeasurableSpace`)

- **def** `invariants [MeasurableSpace α] (f : α → α) : MeasurableSpace α` — the σ-algebra of measurable `s` with `f ⁻¹' s = s`.
- **theorem** `measurableSet_invariants : MeasurableSet[invariants f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s`.
- `invariants_id`, `invariants_le (f) : invariants f ≤ ‹MeasurableSpace α›`,
  `le_invariants_iterate`, `measurable_invariants_of_semiconj`,
  `comp_eq_of_measurable_invariants : Measurable[invariants f] g → g ∘ f = g`.

> **Role in MET.** This is the σ-algebra `ℐ` against which one conditions in the L¹
> (Garsia/conditional-expectation) proof of Kingman: the limit is `μ[g₁ | invariants f]`-type,
> and under ergodicity `invariants f` is a.e. trivial ⇒ constant limit.

### H. Conditional expectation

Files: `Mathlib/MeasureTheory/Function/ConditionalExpectation/*.lean`

- **def (irreducible)** `condExp (m : MeasurableSpace α) (μ : Measure α) (f : α → E) : α → E`, notation **`μ[f | m]`** (`Basic.lean`). Returns `0` unless `m ≤ m₀` and `SigmaFinite (μ.trim hm)`.
- **theorem** `condExp_const (hm : m ≤ m₀) (c) [IsFiniteMeasure μ] : μ[fun _ => c | m] = fun _ => c`.
- **theorem** `condExp_add (hf hg : Integrable …) (m) : μ[f + g | m] =ᵐ[μ] μ[f|m] + μ[g|m]`.
- **theorem** `condExp_smul (c : 𝕜) (f) (m) : μ[c • f | m] =ᵐ[μ] c • μ[f|m]`.
- **lemma** `condExp_mono (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) : μ[f|m] ≤ᵐ[μ] μ[g|m]` (`Basic.lean:482`, real-valued).
- **theorem** `setIntegral_condExp (hm) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in s, (μ[f|m]) x ∂μ = ∫ x in s, f x ∂μ`.
- **theorem** `integral_condExp (hm) [SigmaFinite (μ.trim hm)] : ∫ x, (μ[f|m]) x ∂μ = ∫ x, f x ∂μ`.
- **theorem** `condExp_condExp_of_le (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] : μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁]` (**tower property**).
- **theorem** `norm_condExp_le : (‖μ[f|m] ·‖) ≤ᵐ[μ] μ[(‖f ·‖)|m]` (`CondJensen.lean`; L¹-contraction style bound).
- **Conditional Jensen** (`CondJensen.lean`): `ConvexOn.map_condExp_le`, `ConvexOn.map_condExp_le_univ` (`φ ∘ μ[f|m] ≤ᵐ μ[φ∘f|m]`), and concave duals `ConcaveOn.condExp_map_le(_univ)`.
- **theorem** `tendsto_condExp_unique`, `tendsto_condExpL1_of_dominated_convergence` (`Basic.lean`) — convergence/uniqueness of conditional expectations.
- "Pull out what is known": `condExp_mul_of_stronglyMeasurable_left/right`, `condExp_stronglyMeasurable_mul_of_bound`, `condExp_smul_of_aestronglyMeasurable_*` (`PullOut.lean`).
- L¹/L² operator construction underpinning the above: `condExpL1`, `condExpL1CLM`, `condExpL2` (`CondexpL1.lean`, `CondexpL2.lean`), with `norm_condExpL2_le`, `setIntegral_condExpL1`, etc.
- Indicator/real specifics: `condExp_indicator`, `condExp_ae_eq_restrict_zero` (`Indicator.lean`); real-valued helpers in `Real.lean`; `condExp_of_aestronglyMeasurable'`, `condExp_of_stronglyMeasurable` (`Basic.lean`).

> **Role in MET.** This is the engine for the L¹ proof of Kingman (conditioning on
> `MeasurableSpace.invariants f`): tower property, `setIntegral_condExp`,
> monotonicity, and conditional Jensen are all present. **Missing link:** there is
> NO lemma stating that `condExp` commutes with composition by a measure-preserving
> map (e.g. `μ[g ∘ f | invariants f] = μ[g | invariants f] ∘ f` a.e.), which a
> Kingman proof needs — this must be built.

### Other named "ergodic" results (not the pointwise theorem)

- `Mathlib/NumberTheory/WellApproximable.lean`: `AddCircle.addWellApproximable_ae_empty_or_univ` — **Gallagher's ergodic theorem** (Diophantine approximation). Specialized; not Birkhoff/Kingman.
- `Mathlib/MeasureTheory/Function/Intersectivity.lean`: a Poincaré-recurrence refinement whose *docstring* mentions "the ergodic theorem" but does not contain Birkhoff/Kingman.
- `Mathlib/Order/Birkhoff.lean`, `Mathlib/Analysis/Convex/Birkhoff.lean`: unrelated ("Birkhoff representation theorem" for lattices; "Birkhoff–von Neumann" for doubly-stochastic matrices).

---

## Gaps (must build)

These do **not** exist in Mathlib and are on the critical path to MET:

1. **Kingman's subadditive ergodic theorem.** No statement, no proof, no
   subadditive-cocycle notion over a dynamical system. (Mathlib has only Fekete's
   deterministic `Subadditive.tendsto_lim` and the additive `birkhoffSum`/algebra.)
   This is the single biggest build item.
   - Subsidiary: a **subadditive cocycle** structure/predicate
     `g_{m+n} ≤ g_m + g_n ∘ f^[m]` (generalizing `birkhoffSum_add`), with the
     integrability hypotheses (`g₁ ∈ L¹`, sup-integrability for the lower bound).
   - Subsidiary: the a.e. limit is `invariants f`-measurable and = a constant
     under ergodicity (reuse `Ergodic.ae_eq_const_of_ae_eq_comp_ae`).

2. **Birkhoff pointwise ergodic theorem.** A.e. convergence of
   `birkhoffAverage ℝ f g n x` to `μ[g | invariants f]` for `MeasurePreserving f μ`,
   `g ∈ L¹`. Not present (only the von Neumann *mean*/L² theorem). It is the
   additive special case of Kingman, or provable independently (maximal ergodic
   inequality, which is also **absent**).
   - Subsidiary: **maximal ergodic inequality** / Garsia's lemma — not in Mathlib.

3. **Furstenberg–Kesten theorem.** Convergence of `(1/n) log ‖A_n‖` for a stationary
   matrix cocycle. Absent. (It is the norm-cocycle corollary of Kingman; build on
   top of items 1 + matrix-norm submultiplicativity.)

4. **Oseledets / multiplicative ergodic theorem & Lyapunov exponents.** Entirely
   absent (`oseledets`, `lyapunov`, `multiplicative ergodic` — zero hits). The whole
   target. Needs: matrix/operator cocycles, singular values / log of exterior
   powers, the filtration of Oseledets subspaces, and Kingman applied to
   `log ‖Λ^k A_n‖`.

5. **`condExp` vs. measure-preserving composition.** No lemma like
   `μ[g ∘ f | invariants f] =ᵐ[μ] μ[g | invariants f] ∘ f` (or `μ[g∘f | m] = μ[g|m]∘f`
   for `f`-invariant `m`). Needed to run the conditional-expectation proof of
   Birkhoff/Kingman. Must be built from `setIntegral_condExp` + `MeasurePreserving`.

6. **Subadditive cocycle integrability / lower-bound (BddBelow) machinery in the
   stochastic setting.** Fekete's `BddBelow` hypothesis must be replaced by an
   integrable lower-bound argument; not present.

---

## Notes for the build-vs-reuse boundary

- **Reuse wholesale:** the measure-preserving/ergodic/conservative API (D–F), the
  invariant σ-algebra (G), the full conditional-expectation toolkit (H), Birkhoff
  *algebra* and Fekete (A–B). These cover the *infrastructure* of a Kingman proof.
- **Build:** the actual convergence theorems (Kingman → Furstenberg–Kesten →
  Oseledets) plus the maximal ergodic inequality and the
  `condExp`/measure-preserving compatibility lemma. The recommended path is L¹
  Kingman via conditioning on `MeasurableSpace.invariants f`, then specialize.
- Search method: ripgrep over the source confirmed absences with case-insensitive
  and CamelCase/snake variants (`kingman`, `furstenberg`, `kesten`, `oseledets`,
  `lyapunov`, `pointwise/individual/maximal ergodic`). "Kingman", "Furstenberg",
  "Kesten", "Oseledets", "Lyapunov" each have **zero** occurrences anywhere in
  `Mathlib/`.
