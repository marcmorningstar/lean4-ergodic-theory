# Mathlib survey — Dynamics & Cocycles (for Oseledets MET)

Area: **dynamics-cocycles**. Survey of the *existing* Mathlib 4 API supporting a
formalization of the Oseledets multiplicative ergodic theorem (MET). Paths are
relative to the mathlib package root
(`/workspaces/lean4-oseledets/.lake/packages/mathlib/`). Searched via ripgrep over
the `.lean` source (CamelCase + snake_case variants, multiple namespaces).

## TL;DR — the four definitive questions

1. **Matrix/linear COCYCLE over a dynamical system?** — **NOT FOUND.** There is
   *no* notion of a measurable/linear cocycle over a measure-preserving system.
   Every `cocycle`/`Cocycle` hit in Mathlib is in an unrelated area: group
   cohomology (`RepresentationTheory.*`, `Algebra.Lie.Cochain`), fiber bundles /
   gluing (`Topology.FiberBundle.Basic`, `CategoryTheory.GlueData`), or modular
   forms (`NumberTheory.ModularForms.SlashActions`). None is a dynamical cocycle.
2. **LYAPUNOV EXPONENTS?** — **NOT FOUND.** Zero occurrences of `lyapunov`
   (any case) anywhere in Mathlib.
3. **`Mathlib/Dynamics/Ergodic/`** — present and reasonably mature, but it stops
   at definitions + zero-one laws + the *mean* (von Neumann) ergodic theorem. No
   pointwise (Birkhoff) ergodic theorem, no Kingman subadditive ergodic theorem.
   See "Found API" below for the file-by-file inventory.
4. **Products of random matrices / Furstenberg theory?** — **NOT FOUND.** Zero
   occurrences of `furstenberg`, `random matric*`, `random_matrix`. No theory of
   random-matrix-product norm growth.

**Build-vs-reuse picture:** the *generic dynamical-systems substrate* is
reusable (measure-preserving, ergodic, Birkhoff sums, `IsInvariant`, Fekete).
The *entire MET-specific layer*—cocycles, Lyapunov exponents, the Oseledets
splitting, Kingman, and the pointwise ergodic theorem—must be **built from
scratch**. This is the dominant cost of the project.

---

## Found API (reusable)

### A. Measure-preserving maps — `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
The base layer for "the dynamics `T` preserves `μ`".

- **structure** `MeasureTheory.MeasurePreserving (f : α → β) (μa) (μb) : Prop`
  — fields `measurable : Measurable f`, `map_eq : map f μa = μb`. The hypothesis
  carrier for the driving system `(T, μ)` of MET.
- **theorem** `MeasureTheory.MeasurePreserving.iterate (hf : MeasurePreserving f μ μ) : ∀ n, MeasurePreserving f^[n] μ μ`
  — iterates of `T` stay measure-preserving; needed to push the cocycle along orbits.
- **theorem** `MeasureTheory.MeasurePreserving.comp` / `.symm` / `.congr` — composition,
  inverse (for invertible MET via `MeasurableEquiv`), a.e.-congruence.
- **theorem** `MeasureTheory.MeasurePreserving.measure_preimage` — invariance of
  measure under preimage; used throughout integrability/Birkhoff arguments.
- **theorem** `MeasureTheory.MeasurePreserving.quasiMeasurePreserving` — bridge to
  the quasi-MP API (Birkhoff a.e. lemmas).

### B. Ergodicity — `Mathlib/Dynamics/Ergodic/Ergodic.lean`
- **structure** `PreErgodic (f : α → α) (μ) : Prop` — `aeconst_set`: every measurable
  strictly-invariant set is a.e. empty or full.
- **structure** `Ergodic (f : α → α) (μ) : Prop extends MeasurePreserving f μ μ, PreErgodic f μ`
  — the ergodicity hypothesis under which the MET exponents become a.e. constant.
- **structure** `QuasiErgodic` — quasi-MP variant.
- **theorem** `PreErgodic.prob_eq_zero_or_one [IsProbabilityMeasure μ]` — zero-one law.
- **theorem** `PreErgodic.ae_empty_or_univ` / `Ergodic.ae_empty_or_univ_of_preimage_ae_le`
  — invariant sets are trivial; the mechanism that turns the (a priori
  `x`-dependent) Lyapunov spectrum into a.e.-constant values.
- **theorem** `Ergodic.of_iterate` / `MeasurePreserving.ergodic_of_ergodic_semiconj` /
  `ergodic_conjugate_iff` — transfer of ergodicity along (semi)conjugacies.

### C. Ergodic-invariant functions — `Mathlib/Dynamics/Ergodic/Function.lean`
- **theorem** `Ergodic.ae_eq_const_of_ae_eq_comp_ae (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ) ...`
  — an a.e.-`T`-invariant measurable function is a.e. constant. This is *exactly*
  the lemma that upgrades "the Lyapunov exponent is `T`-invariant" to "it is an
  a.e. constant" in the ergodic case. **High value.**
- **theorem** `Ergodic.eq_const_of_compMeasurePreserving_eq`, plus the
  `PreErgodic`/`QuasiErgodic` analogues.

### D. Ergodic group actions — `Mathlib/Dynamics/Ergodic/Action/{Basic,OfMinimal,Regular}.lean`
- **class** `ErgodicSMul (G α) [SMul G α] (μ)` / `ErgodicVAdd` — ergodicity of an
  action; relevant only if MET is phrased over a group/semigroup action of time.
- **theorem** `ergodicSMul_iterateMulAct {f} (hf : Measurable f) : ErgodicSMul (IterateMulAct f) α μ ↔ Ergodic f μ`
  — bridge between the `ℕ`-action `f^[·]` and `Ergodic f`.

### E. Conservativity / recurrence — `Mathlib/Dynamics/Ergodic/Conservative.lean`
- **structure** `Conservative (f : α → α) (μ) : Prop extends QuasiMeasurePreserving f μ μ`
  — Poincaré recurrence framework.
- **theorem** `MeasureTheory.MeasurePreserving.conservative` (a finite-measure-preserving
  map is conservative), `Conservative.ae_mem_imp_frequently_image_mem`, etc.
  Recurrence is occasionally used in MET proofs but not on the critical path.

### F. Birkhoff sums & averages — `Mathlib/Dynamics/BirkhoffSum/{Basic,Average,NormedSpace,QuasiMeasurePreserving}.lean`
The *definitions and algebra* of orbit averages exist; the *convergence theorem*
does not (see Gaps).

- **def** `birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := ∑ k ∈ range n, g (f^[k] x)`
  (`Basic.lean`) — `[AddCommMonoid M]`.
- **def** `birkhoffAverage (R) (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := (n : R)⁻¹ • birkhoffSum f g n x`
  (`Average.lean`) — `[DivisionSemiring R] [AddCommMonoid M] [Module R M]`.
- **theorem** `birkhoffSum_add (f) (g) (m n) (x) : birkhoffSum f g (m + n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x)`
  — the **(additive) cocycle identity** for Birkhoff sums. This is the additive
  prototype of the multiplicative cocycle relation `A^(m+n)(x) = A^(n)(T^m x) · A^(m)(x)`.
  Reusable as the model to imitate; not the matrix cocycle itself.
- **theorem** `birkhoffSum_apply_sub_birkhoffSum`, `birkhoffAverage_apply_sub_birkhoffAverage`
  — "almost invariance" of the average under `T` (telescoping).
- **theorem** `birkhoffAverage_ae_eq_of_ae_eq` (`QuasiMeasurePreserving.lean`) — a.e.
  well-definedness of averages.
- **theorem** `isClosed_setOf_tendsto_birkhoffAverage`, `uniformEquicontinuous_birkhoffAverage`,
  `tendsto_birkhoffAverage_apply_sub_birkhoffAverage` (`NormedSpace.lean`) — topological
  helpers, but **no almost-everywhere convergence statement**.

### G. Fekete's lemma (subadditive *sequences*) — `Mathlib/Analysis/Subadditive.lean`
- **def** `Subadditive (u : ℕ → ℝ) : Prop := ∀ m n, u (m + n) ≤ u m + u n`.
- **def** `Subadditive.lim` and
  **theorem** `Subadditive.tendsto_lim (hbdd : BddBelow (range fun n => u n / n)) : Tendsto (fun n => u n / n) atTop (𝓝 h.lim)`
  — **Fekete's lemma**: `u n / n` converges. This is the *deterministic* skeleton
  of the top Lyapunov exponent (`(1/n) log‖A^(n)(x)‖`). Kingman's *subadditive
  ergodic theorem* (the a.e. / random version, which MET actually needs) is the
  measurable generalization and is **NOT** in Mathlib — Fekete is the closest
  existing result and a useful building block.

### H. Invariance & flows (generic) — `Mathlib/Dynamics/Flow.lean`
- **def** `IsInvariant (ϕ : τ → α → α) (s : Set α) : Prop := ∀ t, MapsTo (ϕ t) s s`
  — set invariance; the Oseledets subspaces `E_i(x)` are fiberwise invariant
  ("`A(x) · E_i(x) = E_i(T x)`"), so this is the conceptual template, though MET
  invariance is *equivariant over fibers*, not a single invariant set.
- **def** `IsForwardInvariant`, **structure** `Flow`, **def** `Flow.orbit`,
  **theorem** `isInvariant_iff_image_eq`. Mostly for continuous-time; MET is
  discrete-time (`ℕ`-iteration), so these are background, not core.
- `Function.iterate` (`f^[n]`, core library) and `Function.IsFixedPt`
  (`Mathlib/Dynamics/FixedPoints/`) underpin the time-`n` map.

### I. Mean (von Neumann) ergodic theorem — `Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean`
- **theorem** `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure` and
  **theorem** `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`
  — von Neumann **mean** ergodic theorem in Hilbert space (`L²` convergence of
  Birkhoff averages of a contraction to the orthogonal projection onto fixed
  points). This is the *only* ergodic-convergence theorem currently in Mathlib.
  It is the mean (not pointwise) theorem and does not give a.e. convergence;
  MET needs the pointwise/subadditive machinery instead.

### J. Linear-algebra / spectral tools for the MET fiber analysis (reusable, outside `Dynamics/`)
These support the *linear* side of MET (the cocycle takes values in matrices /
operators and the exponents come from singular values).

- **def** `LinearMap.singularValues (T : E →ₗ[𝕜] F) : ℕ →₀ ℝ` and theorems
  `singularValues_nonneg`, `singularValues_antitone`, `support_singularValues`,
  `sq_singularValues_fin` (`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`)
  — singular values of a finite-dim linear map as `√` of eigenvalues of `Tᴴ∘T`.
  **Directly the objects whose `(1/n) log` give the Lyapunov spectrum.** New file
  (2026), finite-dimensional only.
- **theorem** `LinearMap.IsSymmetric.spectral_theorem` / `def LinearMap.IsSymmetric.diagonalization`
  / `LinearMap.IsSymmetric.eigenvalues` (`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`)
  — finite-dim spectral theorem for self-adjoint operators; basis for SVD and for
  the limiting symmetric operator `lim ((A^(n))ᴴ A^(n))^{1/2n}` in MET.
- **`Mathlib/Analysis/Matrix/{Hermitian,PosDef,Spectrum,HermitianFunctionalCalculus}.lean`**
  — Hermitian/positive-definite matrices, matrix spectrum, continuous functional
  calculus (e.g. matrix `√`, `log`); needed to define `log` of the symmetric part.
- **`Mathlib/Analysis/Matrix.lean`** + `Mathlib/Analysis/Normed/Operator/*` — matrix /
  operator norms (the `‖A^(n)(x)‖` whose log-growth is the top exponent). Note: the
  L²-operator-norm instance on `Matrix` is *not* the default; expect to select a
  norm explicitly (Frobenius vs operator) when defining exponents.

### K. Probability scaffolding (for the random-product / i.i.d. setting)
- `MeasureTheory.MeasurePreserving` + `IsProbabilityMeasure` give the
  measure-preserving-shift model of stationary sequences.
- **theorem** `ProbabilityTheory.strong_law_ae` / `strong_law_ae_real`
  (`Mathlib/Probability/StrongLaw.lean`) — SLLN; the i.i.d.-scalar analogue of the
  (missing) Kingman theorem, reusable for the commutative/`1×1` sanity case and as
  a proof-pattern reference.
- `Mathlib/Probability/IdentDistrib.lean` (`IdentDistrib`), `Independence/*`
  (`iIndepFun`), `ProductMeasure.lean`, `Kernel/IonescuTulcea/*` — i.i.d. /
  stationarity infrastructure for a Furstenberg-style random-matrix-product MET.
  No `stationary`/`shift-invariance` predicate specialized to processes exists; it
  is encoded via `MeasurePreserving` of a shift.

---

## Gaps (must build) — the MET-specific layer

Everything below is **NOT FOUND** in Mathlib and is on the critical path.

1. **Multiplicative / linear cocycle over a dynamical system.** No definition.
   Must build `A : α → (E →L[𝕜] E)` (or `Matrix n n 𝕜`) together with the
   iterated cocycle `A^(n)(x) := A(T^[n-1] x) ∘ ⋯ ∘ A(x)` and the **cocycle
   identity** `A^(m+n)(x) = A^(n)(T^[m] x) ∘ A^(m)(x)`. (The *additive* prototype
   `birkhoffSum_add` exists and should be imitated.) Likely a new
   `ErgodicTheory/Cocycle.lean`. Decide bundling (structure vs. plain hypotheses) and
   integrability condition `log⁺‖A‖ ∈ L¹`.

2. **Lyapunov exponents.** No definition. Must build
   `λ(x) := lim_{n} (1/n) log ‖A^(n)(x)‖` (top exponent) and the full spectrum via
   `(1/n) log σ_i(A^(n)(x))` using `LinearMap.singularValues`. Includes: the limit
   exists a.e. (needs Kingman, item 3), `T`-invariance, and—under `Ergodic`—a.e.
   constancy (reuse `Ergodic.ae_eq_const_of_ae_eq_comp_ae`).

3. **Kingman's subadditive ergodic theorem.** NOT FOUND. The measurable
   generalization of Fekete (`Subadditive.tendsto_lim`) to a sequence of
   integrable functions with `g_{m+n} ≤ g_m + g_n ∘ T^m`: a.e. convergence of
   `g_n/n`. This is the analytic engine of MET. Large standalone item.

4. **Pointwise (Birkhoff) individual ergodic theorem.** NOT FOUND. Mathlib has
   only the *mean* ergodic theorem (item I). The a.e. convergence of
   `birkhoffAverage` to the conditional expectation onto the invariant σ-algebra
   is missing and is typically a prerequisite (or co-requisite) for Kingman.
   The `birkhoffSum`/`birkhoffAverage` *definitions* exist (item F); the
   convergence theorem does not.

5. **The Oseledets theorem itself + the filtration/splitting.** NOT FOUND. The
   `T`-equivariant measurable filtration `V_1(x) ⊃ V_2(x) ⊃ …` (or Oseledets
   splitting `⊕ E_i(x)` in the invertible case), the limiting operator
   `Λ(x) = lim ((A^(n)(x))ᴴ A^(n)(x))^{1/(2n)}`, and the statement that the cocycle
   grows like `e^{λ_i n}` on `E_i`. Entirely new; the spectral/SVD tools in item J
   are reusable inputs.

6. **Products of random matrices / Furstenberg theory.** NOT FOUND. No theory of
   `‖M_n ⋯ M_1‖` for random matrices, Furstenberg's formula, positivity of the
   top exponent, or the i.i.d. specialization of MET. Would be built on top of
   items 1–5 plus the probability scaffolding in item K.

7. **Process-level "stationary"/"shift-invariant" predicate.** NOT FOUND as a
   named notion; only expressible via `MeasurePreserving` of a shift map. A thin
   convenience layer may be worth building.

---

## Notes & search methodology

- Searched case-insensitively over the whole `Mathlib/` source tree for:
  `cocycle`/`Cocycle`, `lyapunov`/`Lyapunov`, `oseledets`, `multiplicative ergodic`,
  `furstenberg`, `random matric*`/`random_matrix`, `subadditive`/`kingman`,
  `birkhoff`/`pointwise ergodic`/`individual ergodic`, `IsInvariant`,
  `singular value`/`polar decomposition`/`spectral theorem`. CamelCase and
  snake_case variants and multiple namespaces checked.
- `cocycle` matches exist but are *all* unrelated (group cohomology, fiber
  bundles, modular forms) — confirmed by reading the file contexts. There is no
  dynamical cocycle.
- The `Dynamics/` tree is broad (entropy, flows, omega-limits, symbolic dynamics,
  rotation number, fixed/periodic points) but none of it touches Lyapunov theory.
- Net assessment: Mathlib gives a **solid generic ergodic-theory substrate** and
  **good finite-dimensional linear-algebra/spectral tooling**, but the analytic
  heart of MET — Kingman + the pointwise ergodic theorem — and the *entire*
  cocycle/Lyapunov/Oseledets vocabulary are absent and must be built. Plan the
  project around building items 1–5; reuse heavily for measure-preservation,
  ergodicity-to-constancy, Birkhoff definitions, Fekete, SVD, and the spectral
  theorem.
