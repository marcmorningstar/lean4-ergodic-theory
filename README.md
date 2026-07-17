# ErgodicTheory — Lean 4 formalization

[![Blueprint and documentation](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/blueprint.yml/badge.svg)](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/blueprint.yml)
[![Build](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/push.yml/badge.svg)](https://github.com/marcmorningstar/lean4-ergodic-theory/actions/workflows/push.yml)

A large-scale Lean 4 + Mathlib formalization of smooth ergodic theory, built around the
**Oseledets multiplicative ergodic theorem** (MET) and extending through Kolmogorov–Sinai
entropy theory, **Krieger's finite generator theorem**, the pointwise
**Shannon–McMillan–Breiman theorem**, the **Margulis–Ruelle inequality** and the volume-case
**Pesin entropy formula**, **Livšic cohomological rigidity theory**, a representative-free
suspension-flow Lyapunov/entropy theory, a coarse-grained **multifractal formalism**, and a
finite-dimensional **quantum-information layer** (Lieb's joint convexity, the data-processing
inequality, Petz's equality theorem).

**428 modules · ~117,000 lines · ~3,300 theorems — sorry-free, linter-enforced, and with 731
declarations continuously axiom-audited down to `[propext, Classical.choice, Quot.sound]`.**

📖 **[Project site](https://marcmorningstar.github.io/lean4-ergodic-theory/)** ·
**[Blueprint](https://marcmorningstar.github.io/lean4-ergodic-theory/blueprint/)** ·
**[Blueprint (PDF)](https://marcmorningstar.github.io/lean4-ergodic-theory/blueprint.pdf)** ·
**[Dependency graph](https://marcmorningstar.github.io/lean4-ergodic-theory/blueprint/dep_graph_document.html)**

## Headline theorems

All declarations live in the `ErgodicTheory` namespace (omitted below).

| Declaration | What it proves |
|---|---|
| `oseledets_filtration` | The one-sided Oseledets MET (filtration form): distinct Lyapunov exponents `λ₁ > ⋯ > λ_k` and a measurable equivariant flag with exact growth `(1/n) log‖A⁽ⁿ⁾(x)v‖ → λᵢ` on each stratum |
| `oseledets_splitting` | The two-sided MET: an invariant direct-sum Oseledets splitting `Eᵢ = Vᵢ ⊓ W_{rev i}` with two-sided growth `±λᵢ` over an invertible base |
| `oseledets_flow` | The continuous-time MET for measure-preserving ℝ-flows, with flow-equivariant filtration and continuous-parameter growth |
| `Krieger.krieger_finite_generator` | Krieger's finite generator theorem: an ergodic aperiodic automorphism with `h(T) < log k` has a two-sided generator of size `≤ k` |
| `Krieger.ae_tendsto_div_infoFun` | The pointwise Shannon–McMillan–Breiman theorem `(1/n)·iₙ(x) → h(P,T)` a.e. |
| `Entropy.abramov_rokhlin` | The Abramov–Rokhlin addition formula `h(T) = h(S) + h(T \| comap π)` for skew products |
| `Entropy.ksEntropy_eq_ksEntropyPartition_of_generating` | The Kolmogorov–Sinai generator theorem `h(T) = h(T,P)` (with a two-sided variant) |
| `margulisRuelle_sharp` | The Margulis–Ruelle inequality `h_μ(T) ≤ ∑ λᵢ⁺` |
| `integral_log_abs_det_le_ksEntropy` | The **Rokhlin inequality** `∫ log|det DₓT| dμ ≤ h_μ(T)` (generator-free, for `μ ≪ volume`) |
| `sumPosExp_le_ksEntropy_of_SRB` | The SRB reverse Pesin inequality `∑ λᵢ⁺ ≤ h_μ(T)`, discharging the hard leaf of issue #10 |
| `pesin_entropy_formula_spectral` | The **volume-case Pesin entropy formula** `h_μ(T) = ∑ λᵢ⁺` (both inequalities combined) |
| `Examples.Rokhlin.pesin_formula_doublingMap` | The first non-vacuous full-system Pesin instance: `h = ∑ λ⁺ = log 2` for the doubling map |
| `CatMapToral.catTorus_ksEntropy_eq` | **The cat-map entropy theorem** (Adler–Weiss 1967 / Sinai): `h(catTorus) = log((3+√5)/2) = log λ₊` — the **exact Kolmogorov–Sinai entropy of a hyperbolic system, formalized end-to-end** (we have not located a prior formalization). Lower bound via a `5×5` grid partition + eigencoordinate telescoping slab; upper bound via the golden two-box Adler–Weiss Markov partition (exact cover with *empty* junk cell), shown a literal two-sided generator, and a golden transfer-matrix path count |
| `OperatorEntropy.Lieb.relEntropyMat_jointly_convex` | **Lieb's theorem**: joint convexity of the Umegaki relative entropy |
| `OperatorEntropy.Lieb.relEntropyMonotone_partialTrace` | The partial-trace data-processing inequality `S(Tr_E ρ ‖ Tr_E σ) ≤ S(ρ‖σ)` (arbitrary ρ, faithful σ) |
| `OperatorEntropy.Lieb.petz_equality_recovery_general` | Petz's equality theorem, fully general: DPI saturation ⟹ Petz recovery, for every faithful-state Kraus channel |
| `isHolderCoboundary_iff` | The **abstract Livšic theorem**: over a system with the exponential-closing property and a dense orbit, a Hölder function is a Hölder coboundary iff all its periodic-orbit sums vanish |
| `Livsic.livsic_measurable_rigidity` | **Full measurable Livšic rigidity** (Katok–Hasselblatt 19.2.4): over the two-sided full shift a merely measurable a.e.-solution of a Hölder cohomological equation agrees a.e. with a genuine Hölder coboundary |
| `not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero` | The **flow-Livšic obstruction**: a continuous roof with a nonzero closed-orbit integral is not a flow coboundary (instantiated on the cat-map suspension) |
| `livsic_suspensionFlow_constRoof` | The **flow-Livšic tier-III equivalence** for constant-roof suspension flows: a flow observable is a flow coboundary iff every closed-orbit integral of its induced base observable vanishes (flow-native form `..._orbitIntegral`) — transfer function glued **exactly** across the fundamental-domain seam by the base cohomological equation; cat instance `CatMapToral.livsic_catSuspensionFlow` closes the former flow-converse frontier for constant roofs |
| `CatMapToral.livsic_catSuspensionHolderFlow` | The **classical-strength (Hölder) flow-Livšic theorem** on the Arnold cat-map suspension flow: a Hölder flow observable admits a Hölder flow transfer function iff its induced base observable has vanishing periodic sums — the library's first Hölder-regularity flow-Livšic result, measured against the Bowen–Walters embedding metric `embDist`. Abstract engine `livsic_holderFlow_constRoof` (constant roof, both tier 2 and the issue's tier-4 Anosov-presentation statement) and `livsic_holderFlow_varRoof` (variable Lipschitz roof); roof-Lipschitz is essential (a merely Hölder roof degrades the exponent to `r²`) |
| `ae_flowExponentAt_eq_base_div_roof` | The **representative-free suspension-flow Lyapunov exponent** `flowExponentAt = λ_base / ∫τ` a.e. — a genuine `Quotient.lift` value on orbit classes, not just a chosen representative |
| `ergodic_suspensionFlowMap_one_const_roof` | **Time-1 ergodicity** of the constant-**irrational**-roof suspension flow of an ergodic base with unimodular-eigenvalue rigidity |
| `ksEntropy_flow_eq_mul` | **Abstract Abramov flow-entropy homogeneity** `h(φ_t) = t·h(φ_1)` (in `EReal`, `t > 0`) for any measure-continuous measure-preserving flow on a standard Borel probability space (Ito's elementary generator-free proof) |
| `ksEntropy_bernConstSuspension_time_one_irrational` | **Suspension entropy descent, all roofs**: `h(ζ⁽ʳ⁾₁) = h_base / r` for **every** roof `r > 0` (irrational included), via `ksEntropy_flow_eq_mul` — retiring the former rational-only restriction |
| `CatMapToral.catTorus_eigenfunction_ae_zero` | **Cat-map eigenfunction rigidity**: a measurable `g : 𝕋² → ℂ` with `g(catTorus x) = l·g(x)`, `‖l‖ = 1`, `l ≠ 1`, vanishes a.e. (Fourier transport along infinite orbits + Parseval; Einsiedler–Ward §2.4) |
| `CatMapToral.catTorus_mixing` | **Strong mixing of the Arnold cat map** for Haar measure — the library's first smooth mixing example — via character decorrelation and an L²-density argument over the Fourier basis (keystone `tendsto_catCorr`, Koopman isometry); re-derives eigenfunction rigidity through the reusable mixing interface `eigenfunction_ae_zero_of_mixing` (corollary `catTorus_eigenfunction_ae_zero_of_mixing`) |
| `CatMapToral.catCorr_decay` | **Exponential decay of correlations for the cat map** (the library's first quantitative-rate mixing statement): for the Fourier coefficient-decay class `𝒞_s` (`s > 2`) the centred correlation decays like `C·θᵏ`, `θ = λ₊^(−(s−2)/4)`, via the Diophantine norm-form growth bound `lemma_beta` (`Q(p,q) = p²−pq−q²`) and a Parseval character split. Consequences: Green–Kubo variance `catGreenKubo_fourierDecay` (`Var(Sₙ)/n → σ²`), Chebyshev concentration `catConcentration_fourierDecay` (`≤ B/(nε²)`), the deterministic exponent-estimator rate `catExponent_rate` (`\|log‖Aⁿ‖/n − log λ₊\| ≤ C₀/n`), and suspension-flow transport `catSuspensionDecay_fourierDecay` (`θ^⌊t⌋`, base-centred). Full CLT deferred (no martingale CLT in Mathlib) |
| `CatMapToral.ergodic_catSuspension_timeOne_const_irrational` | **Time-1 ergodicity of the cat suspension**: the constant-irrational-roof cat-map suspension flow has an ergodic time-1 map (cat-side twin of the Bernoulli result; `ergodic_catSuspension_timeOne_sqrtTwo` at `r = √2`) |
| `quotientFlowCocycle` / `exists_flowCocycle_cohomologous_to_cover` | **The quotient-level suspension `FlowCocycle`**: over the constant-unit-roof suspension of an invertible base, a genuine continuous-time `FlowCocycle` built from the two-sided matrix cocycle `cocycleZ` and the measurable canonical representative — the flow's own derivative data now lives on the same `FlowCocycle` interface `oseledets_flow` consumes. Cohomologous to the cover cocycle via a rep-level frame; cat instance `CatMapToral.catQuotientFlowCocycle` has a.e. exponent `log((3+√5)/2)` |
| `OperatorEntropy.CNT.ksEntropy_eq_cntDynamicalEntropy` | The **CNT collapse**: classical KS entropy equals the *full* CNT dynamical entropy on the abelian corner (a disclosed `0 = 0`; the genuine obstruction to a Fekete rate is `OperatorEntropy.CNT.not_subadditive_cnt_entropySeq`) |
| `CatMapToral.isFactorMap_awSymbFull` / `injective_awSymbFull` | **The Adler–Weiss coding as a factor and a conjugacy** (issue #58): the two-sided golden itinerary `awSymbFull : 𝕋² → (Fin 5)^ℤ` is a measure-theoretic factor onto the golden 5-symbol SFT with the shift intertwining holding **everywhere** (empty junk cell — no discarded null set), and is injective on the nose, hence a measurable embedding and a measure conjugacy onto its range. The SFT₅ image has entropy exactly `log((3+√5)/2)` (`ksEntropy_mapAwSymbFull_eq`) — a coding preserves entropy |
| `CatMapToral.catSymbolicFlowTower` | **The depth-two symbolic flow tower** (issue #58): instantiating the unit-roof suspension functor (`suspensionFactorMap`, `isFactorMap_suspensionFactorMap`) twice lifts the Adler–Weiss coding and the source-merge lumping to the mapping-torus flows — cat suspension ≅ SFT₅ suspension (injective conjugacy stage) → 2-symbol suspension (a genuine non-injective flow factor with a **strict** entropy drop `h(ζ²₁) ≤ log 2 < log((3+√5)/2)`), the merged level pinned positive in `[log λ₊ − log 2, log 2]` by `CatMapToral.coarseAW_ksEntropyPartition_pos` |
| `OperatorEntropy.quantum_seal_dephase` / `_faithful` | **The dephasing recovery seal** (issue #59): the dephasing channel exhibits a strict Umegaki relative-entropy drop against a non-uniform diagonal reference (`log 2` for the pure state `\|+⟩⟨+\|`; `log 2 − h₂((1+r)/2)` for the faithful family `ρ_r`, via the binary-entropy strict maximum), hence no faithful-ancilla Stinespring recovery. A QA pass repaired a degenerate `σ = I/2` witness (documented) |
| `OperatorEntropy.CNT.cex_strictly_above_abelian` | **The per-resolution non-commutativity certificate** (issue #59): on the finite-dimensional witness, every abelian operational partition yields exactly zero correlation entropy at every resolution (rank-one Gram collapse), while the non-commuting partition is strictly positive at resolution 2 — the honest form of "entropy strictly above every abelian restriction", the system-level CNT rate being the disclosed `0 = 0` of `cntDynamicalEntropy_eq_zero` |
| `OperatorEntropy.CNT.cntCumulativeEntropy_le_reservoir` / `vonNeumannEntropy_corrMatrix_pauliPartition_eq` | **The CNT reservoir cap, and its tightness** (issue #69): the iterated-refinement cumulative CNT entropy is capped by the finite reservoir `2·log d` uniformly in the resolution `n` (`cntEntropySeq_bddAbove` is the bounded-saturation form), so the per-step rate is squeezed to `0` via the generic engine `rate_to_zero_of_cumulative_bounded`. The cap is **tight** at `d = 2`: the Pauli operational partition (`pauliPartition`) at the maximally mixed state fills `log(d²) = log 4` at a single step for every unital `*`-endomorphism (`corrMatrix_pauliPartition_one`), so the finite-dim rate-zero theorem is saturation of a finite reservoir, not an identically-zero artifact — and the naive `log d` cap is false for this correlation-matrix API. Standard ingredient: Connes–Narnhofer–Thirring 1987 |
| `OperatorEntropy.blockEntropy_eq` / `tendsto_blockEntropy_div` | **The growing-tower spatial rate** (issue #70): the growing-finite qubit tower (`Qbits n`, `card = 2ⁿ`; capacity-enlargement embedding `shiftAdjoinQubit : A ↦ 1 ⊗ A`; marginal-consistent state family `rhoPow ρ n = ρ^{⊗n}`) has block entropy exactly `n·S(ρ)` (`blockEntropy_eq`, iterated von Neumann additivity), so the per-step spatial rate converges to `S(ρ)` (`tendsto_blockEntropy_div`), positive off the pure states (`blockEntropy_rhoR_pos`) and `= n·log 2` at the maximally mixed state (`blockEntropy_maximallyMixed`). This is a **growing-finite** tower, not the completed `⊗_ℤ M₂` chain; the spatial rate is complementary to — no tension with — the fixed-`d` temporal `cntDynamicalEntropy_eq_zero`. Standard ingredient: Nielsen–Chuang §11.3; Ohya–Petz |
| `OperatorEntropy.growingQuantumWorld_exists` | **The bundled sealed-and-alive growing world** (issue #70): the witness `GrowingQuantumWorld` packages, on one growing-finite object, positive spatial per-step entropy production, a **channel-level** per-stage dephasing seal at the world's own block states (`quantum_seal_dephase_kron_faithful`, the `dephaseKronId` channel lifted over an arbitrary ancilla block, reference pair with distinct dephased images), and a base-factor non-commutativity certificate. The bundling is the repo's contribution; its ingredients (von Neumann additivity, the Petz-recovery seal, CNT non-commutativity) are standard. Connes–Narnhofer–Thirring 1987; Petz 1986/2003; Nielsen–Chuang §11.3 |
| `OperatorEntropy.quantumBernoulliShift_exists` | **The quantum Bernoulli shift, directed-local form** (issue #71): the witness `QuantumBernoulliShift` bundles the fixed directed system of local algebras `M_{2ⁿ}` with a commuting unital `⋆`-injective inclusion (`appendQubit`) and shift (`shiftAdjoinQubit`), a shift-invariant tracial state built from compatible finite marginals (`rhoPow_shiftAdjoinQubit_pairing`, `appendQubit_maximallyMixed_pairing`), the temporal site-window entropy rate `= log 2` (`windowEntropy_tracial`, `tendsto_windowEntropy_div_tracial`) with a site-translation stationarity certificate (`shiftIter_pairing`), and a per-level dephasing seal at the tracial blocks (`chain_seal_dephase_faithful`). Honest scope: this is the **growing-finite / directed-local** representation, **not** the completed C\*-chain `⊗_ℤ M₂` (Mathlib has no non-commutative inductive limit — `Ring.DirectLimit` is `CommRing`-only), and the rate is a bespoke site-window rate, not the full CNT supremum over all finite subalgebras. Connes–Narnhofer–Thirring 1987; Bratteli–Robinson II §5.3; Ohya–Petz; Powers 1967 |
| `OperatorEntropy.modAut` / `modAut_diagState_ne_id` | **The finite modular clock and its intrinsic-clock dichotomy** (issue #71): the modular automorphism group `σ_t(a) = ρ^{it} a ρ^{-it}` on the existing Lieb `cpow`/`upow` API, with the automorphism-group laws, the `β = 1` KMS boundary identity `kms_boundary` (disclosed as trace cyclicity, holding for every invertible ρ), and tower compatibility `modAut_shiftAdjoinQubit`. The substantive content is the dichotomy: the tracial (maximally mixed) state has **trivial** flow (`modAut_maximallyMixed_eq_id`), while a non-tracial faithful product state has a **provably nontrivial** flow (`modAut_diagState_ne_id`, witness `E₀₁ ↦ −E₀₁`). Honest scope: a finite matrix-algebra shadow — no GNS, no Tomita–Takesaki uniqueness, no genuine type-III structure of the completed chain. Bratteli–Robinson II §5.3; Ohya–Petz; Powers 1967 |
| `measurable_orthProjMatrix_lambdaSublevel` | The **everywhere-Borel singular filtration** (issue #11): the orthogonal projector onto a sublevel set of the forward Lyapunov filtration is Borel measurable, via the Novikov projection theorem |
| `Multifractal.renyiRateSup_map_blockCode_le` / `renyiEntropy_merge_le` | **The Rényi c-function, tier 1** (issue #60): the static Rényi data-processing inequality `H_q(merge p) ≤ H_q(p)` holds for every order `q ≥ 0` (`renyiEntropy_merge_le`, elementary per-fibre sign-compensation of `x ↦ x^q`), and the **dynamical** `q`-Rényi rate (limsup/liminf of the normalized length-`n` cylinder Rényi entropies) is monotone under one-block factor codes **unconditionally** — no stationarity, no rate-existence — via the per-`n` inequality (`renyiRateSup_map_blockCode_le`, `renyiRateInf_map_blockCode_le`; the suspected hidden-Markov wall concerned closed *forms*, not the inequality). Honest boundary: general-measurable-factor monotonicity for `q ≠ 1` is FALSE (Takens–Verbitskiy 2002 — the invariant dynamical Rényi entropy degenerates to `+∞` for `q < 1` and to `h_KS` for `q ≥ 1`), so `q = 1` is the unique seal-grade monotone at full generality |
| `Multifractal.renyiRateSup_bern` / `renyiRate_strict_drop_uniformFin3` | **Exact Bernoulli Rényi rates + strict-drop witness** (issue #60): for the i.i.d. measure `bern ν` the rate is exactly the static single-symbol Rényi entropy `h_q = H_q(ν)`, realized as an honest `limsup = liminf` (`renyiRateSup_bern`, `renyiRateInf_bern`), and the one-block pushforward stays Bernoulli (`map_blockCode_bern`). A genuine merge gluing two `ν`-atoms strictly lowers the rate for every `q ∈ (0,1) ∪ (1,∞)` (`renyiRateSup_map_blockCode_bern_lt`), certified non-vacuously by a compile-time uniform `Fin 3 → Fin 2` witness at `q = 2` (`renyiRate_strict_drop_uniformFin3`) |
| `sectionExists_analyticSet` / `isSealed_coanalyticSet` | **Descriptive complexity of the seal** (issue #61): over the Polish parameter space `Params X = C(X,X)³ × P(X)²` of continuous-dynamics systems on a compact metric carrier, section-existence `{p \| ∃ continuous equivariant measure-preserving section}` is **analytic** (`Σ¹₁`) — the continuous image `Prod.fst` of the closed section relation (`isClosed_sectionRel`) — and sealedness is dually **coanalytic** (`Π¹₁`); the identity parameter certifies non-vacuity (`sectionExists_nonempty`). Disclosed frontiers (not delivered): the `L⁰`/MALG measurable-section parametrization (Foreman–Rudolph–Weiss) needs `L⁰`-as-Polish, and tier-3 `Σ¹₁`-completeness needs Borel-reduction machinery — both absent from Mathlib |
| `MeasureTheory.polishSpace_probabilityMeasure` / `continuous_probabilityMeasure_map_compact` | **Two Mathlib-gap fills for the DST layer** (issue #61): the space `P(X)` of Borel probability measures on a compact metric `X` is **Polish** (compact + metrizable ⇒ completely metrizable, upgrading the Prokhorov/Lévy–Prokhorov package), and the pushforward `(f, ν) ↦ f_* ν : C(X,Y) × P(X) → P(Y)` is **jointly continuous** in the pair (Billingsley mapping-theorem-adjacent; filter form `tendsto_probabilityMeasure_map_of_tendsto`) — both natural upstream candidates |

Every theorem above (and ~650 further results) is guarded in `test/AxiomAudit.lean` by
`#guard_msgs in #print axioms`: the build **fails** if any of them ever acquires an axiom beyond
`propext`, `Classical.choice`, `Quot.sound` — so in particular none depends on `sorryAx`.

## What is formalized

### The Oseledets core (`Cocycle/`, `Ergodic/`, `Lyapunov/`, `TwoSided/`, `Continuous/`)

The iterated linear cocycle with Furstenberg–Kesten theory, the maximal ergodic inequality with
Birkhoff's and Kingman's theorems, and the full assembly of the one-sided MET
(`MultiplicativeErgodic.lean`), the two-sided splitting, and the continuous-flow version.
`Lyapunov/Extensions/` adds the post-theorem corollary layer: the Lyapunov spectrum as a
consumable object, positive/negative exponent sums, the trace–determinant identity,
exterior/wedge (k-volume) growth, the inverse/time-reversal spectrum, restriction to invariant
subbundles, the non-ergodic relaxation, regularity of the exponents in the generator
(semicontinuity, a Vitali/uniform-integrability regime), and one-sided singular bounds without
invertibility. `Singular/` supplies the everywhere-Borel orthogonal projector of the singular
forward filtration (`measurable_orthProjMatrix_lambdaSublevel`, issue #11), resting on the
descriptive-set-theoretic residuals in `MeasureTheory/` (see below).

### Entropy and generators (`Entropy/`, `Krieger/`)

A self-contained Kolmogorov–Sinai entropy theory (~80 modules): partitions and joins, conditional
and relative entropy, KS entropy as a Fekete limit, the generator theorem (one- and two-sided),
the Abramov–Rokhlin formula, and the Margulis–Ruelle inequality `h ≤ ∑λ⁺` connecting entropy back
to the Lyapunov spectrum. On top of it, the full coding stack for **Krieger's finite generator
theorem** — Rokhlin/Kakutani towers, name counting, sentinel/prefix codes — together with the
pointwise SMB theorem and the Krieger–Keane–Serafin countable generator.

### Multifractal analysis (`Multifractal/`)

The coarse-grained multifractal formalism of an invariant measure: partition function `Z_q`, mass
exponent `τ(q)` (proved concave — the Legendre-transform heart), Rényi/generalized dimensions
`D_q` (proved monotone, with the `q = 1` information-dimension branch), local and Hausdorff
dimension (`dimH μ = h_μ/log 2` for Bernoulli measures), and a fully constructed Bernoulli
suspension flow realizing a genuinely `q`-dependent spectrum. On top of this the **Rényi entropy
rate** layer (issue #60) proves the `c`-function tier-1 monotonicity: the static Rényi
data-processing inequality `H_q(merge p) ≤ H_q(p)` for every `q ≥ 0`, its lift to the dynamical
Rényi rate `renyiRateSup`/`renyiRateInf` (limsup/liminf of the normalized length-`n` cylinder Rényi
entropies), which is monotone under one-block factor codes unconditionally (per-`n`, no
stationarity), the exact Bernoulli closed form `h_q(bern ν) = H_q(ν)` with strict drops under
genuine merges, and the honest boundary that general-factor monotonicity for `q ≠ 1` is false
(Takens–Verbitskiy degeneracy), leaving `q = 1` as the unique seal-grade monotone.

### Smooth maps and worked examples (`Smooth/`, `Examples/`)

The derivative (tangent) cocycle of a smooth self-map, feeding the MET, and the foliation-free
expanding-case **Pesin = Rokhlin identity** `∑λ⁺ = ∫ log|det DₓT| dμ`. On top of this, the
**volume-case Pesin entropy formula** `h_μ(T) = ∑λ⁺` is now discharged (issue #10): the reverse
SRB inequality `∑λ⁺ ≤ h_μ(T)` follows from the standalone, generator-free **Rokhlin inequality**
`∫ log|det DₓT| dμ ≤ h_μ(T)`, combined with Margulis–Ruelle for the forward direction. Concrete
systems instantiate the abstract theory end to end: the **Arnold cat map** as a genuine hyperbolic
automorphism of 𝕋² (measure-preserving, ergodic, **strongly mixing** — `catTorus_mixing`, the
library's first smooth mixing example, proved by Fourier character decorrelation over an L² Hilbert
basis — positive top exponent) whose **exact Kolmogorov–Sinai entropy is now computed** —
`catTorus_ksEntropy_eq : h(catTorus) = log((3+√5)/2) = log λ₊`, the entropy statement of the
**Adler–Weiss** classification (PNAS 57, 1967) and Sinai's sum-of-positive-exponents formula, and
the exact entropy of a hyperbolic system formalized end-to-end (we have not located a prior formalization; details below) — and the **doubling map**,
which now carries the first non-vacuous full-system Pesin instance in the
library — `h = ∑λ⁺ = log 2` (Lyapunov spectrum, Ruelle bound, binary-expansion generator).

The cat-map entropy equality `catTorus_ksEntropy_eq` (issue #52) is `le_antisymm` of two
structurally distinct geometric mechanisms. The **lower bound** `log λ₊ ≤ h(catTorus)`
(`catTorus_ksEntropy_ge`, with strict positivity `catTorus_ksEntropy_pos` as its Tier 1) uses a
`5×5` grid partition: a nearest-lift telescoping argument (`CatMapTelescope.lean`) confines every
atom of the forward grid join to a `√5·(9/25)·λ·μⁿ`-measure eigencoordinate slab (the **wall lemma**
`catTorus_gridJoinAtom_volume_le`), forcing the atom count — and hence the entropy — to grow like
`λ₊ⁿ`, glued through the positive-measure atom-count backbone `Entropy.posAtomCount`. The **upper
bound** `h(catTorus) ≤ log λ₊` (`catTorus_ksEntropy_le`) exhibits the golden **two-box Adler–Weiss
Markov partition** `catAWPartition`: its cover is *exact* — the junk cell is literally empty
(`awCell_zero_eq_empty`) via a four-case skew-lattice reduction, with genuine disjointness and cell
measures summing to 1 — and by cat-map expansiveness it is a **literal two-sided generator**
(`isGeneratingTwoSided_catAWPartition`), through a new generic Blackwell bridge
`Krieger.isGeneratingTwoSided_of_separating` (separating family ⇒ `IsGeneratingTwoSided` on a
standard Borel space). The two-sided generator theorem then reduces `h(catTorus)` to the
partition-relative entropy, which a golden transfer-matrix count of admissible itineraries
(`catAW_ksEntropyPartition_le`, weight recurrence `W(n+1) = λ·W(n)`) bounds by `log λ₊`.

On top of the qualitative mixing, the cat map now carries a full **statistical-laws layer** (issue
#62): the exponential decay of correlations `catCorr_decay` — `|∫f·(g∘Tᵏ) − ∫f∫g| ≤ C·θᵏ`,
`θ = λ₊^(−(s−2)/4)`, for the Fourier coefficient-decay class `𝒞_s` (`s > 2`) — proved by the
Einsiedler–Ward Fourier mechanism: a Parseval character split
(`hasSum_correlation_fourier_ne_zero`) whose shifted index is expanded by the invariant integer norm
form `Q(p,q) = p²−pq−q²` (discriminant 5), giving the Diophantine growth bound `lemma_beta`
`(√5−2)λ₊ᵏ/‖n‖ ≤ ‖Aᵏn‖`, with the far-frequency tail summed by `tsum_bracket_rpow_tail_le`. The
class `𝒞_s` replaces Hölder honestly: a 2D Hölder modulus decays too slowly to feed the lattice
sums. Summable correlations then yield the second-moment limit laws — Green–Kubo variance
`catGreenKubo_fourierDecay` (`Var(Sₙ)/n → σ² = ρ(0) + 2∑ρ(k+1)`), the linear variance bound
`catVariance_linear_fourierDecay`, and finite-sample Chebyshev concentration
`catConcentration_fourierDecay` (`μ{|Sₙf/n − ∫f| ≥ ε} ≤ B/(nε²)`) — plus the deterministic
finite-sample **exponent-estimator rate** `catExponent_rate` (`|log‖catℝⁿ‖/n − log λ₊| ≤ C₀/n`, from
a Cayley–Hamilton two-sided Gelfand bound) and the constant-roof suspension-flow transport
`catSuspensionDecay_fourierDecay` (decay `θ^⌊t⌋` of fibre-product observables). Three honest
deferrals are disclosed in place: a full dynamical **CLT** is out of reach (Mathlib has no
martingale/Gordin CLT, so only second-moment laws are proved), **entropy-from-orbit** estimation
would need an SMB theorem *with rates*, and the suspension-flow decay **requires base-centred**
observables (`∫g = 0`) — a constant-roof suspension is never mixing as a flow, the fibre rotation
carrying no mixing. Sources: Einsiedler–Ward Ch. 2; Katok–Hasselblatt §17–18; Coudène;
Cornfeld–Fomin–Sinai Ch. 11.

The entropy *number* of the Adler–Weiss partition is upgraded to the coding *map* and a symbolic
flow tower (issue #58). The two-sided golden itinerary `awSymbFull : 𝕋² → (Fin 5)^ℤ` is a genuine
measure-theoretic factor map onto the golden 5-symbol subshift of finite type
(`isFactorMap_awSymbFull`), with the shift intertwining holding **everywhere, not merely a.e.** —
the repo's half-open golden tiling has an *empty* (not just null) junk cell, so no boundary null
set is discarded — and it is **injective on the nose** (`injective_awSymbFull`), hence a measurable
embedding and a measure conjugacy onto its range (`measurableEmbedding_awSymbFull`,
`measurePreserving_awSymbEquivRange`). Because a conjugacy preserves entropy, the SFT₅ image has KS
entropy **exactly** `log((3+√5)/2)` (`ksEntropy_mapAwSymbFull_eq`) — the issue's hoped-for strict
drop at *every* stage is impossible on a coding, and is disclosed as such. Merging the five branches
to the two golden rectangles gives the coarse two-cell partition `coarseAWPartition`, whose entropy
is bracketed in the nontrivial band `[log λ₊ − log 2, log 2]`: the abstract `log 2` ceiling
(`coarseAWPartition_ksEntropy_le`) and the **keystone strict positivity**
`coarseAW_ksEntropyPartition_pos` (via a per-fine-cylinder `λ₊⁻ⁿ` volume decay against a `2ⁿ`
transfer-matrix fibre count, positive because `λ₊ = (3+√5)/2 > 2`). Instantiating the abstract
unit-roof **suspension functor** `suspensionFactorMap` (`isFactorMap_suspensionFactorMap`, the
constant-roof Ambrose–Kakutani functoriality) twice lifts the two codings to a depth-two flow tower
`catSymbolicFlowTower`: cat suspension ≅ SFT₅ suspension (the injective conjugacy stage) → 2-symbol
suspension (a genuine non-injective flow factor with a **strict** flow-entropy drop
`h(ζ²₁) ≤ log 2 < log((3+√5)/2)`), all three levels alive. Disclosed in place: the pushforward =
explicit-golden-Markov-measure cylinder identification is deferred, and the issue's √2-roof tower
object does not exist (roof `1` is used throughout). Sources: Adler–Weiss 1970 (Memoirs AMS 98);
Adler BAMS 1998; Lind–Marcus Ch. 6; Kemeny–Snell (lumpability); Ambrose–Kakutani 1942.

### Livšic cohomological rigidity (`Livsic/`)

The Livšic theory of when a Hölder observable is a coboundary. The abstract engine
(`isHolderCoboundary_iff`) proves, for any system with an exponential-closing property and a dense
orbit, that a Hölder `φ` is a Hölder coboundary iff every periodic-orbit sum vanishes; it is
instantiated on the one-sided full shift (`Livsic.livsic_fullShift`), the two-sided full shift
(`livsic_biShift`), subshifts of finite type (`livsic_sft`), the Arnold cat map
(`CatMapToral.livsic_catTorus`), and the doubling map (`livsic_doublingMap`). The measurable-rigidity
tier culminates in the full **Katok–Hasselblatt 19.2.4** theorem (`Livsic.livsic_measurable_rigidity`):
a merely measurable a.e.-solution of the cohomological equation is a.e. equal to a genuine Hölder
coboundary. On the continuous-time side, the **flow-Livšic obstruction**
(`not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero`, witnessed by
`CatMapToral.const_one_not_isFlowCoboundary_catSuspension`) shows a roof with a nonzero closed-orbit
integral cannot be a flow coboundary; the **converse now closes at tier III** for constant-roof
suspension flows (`livsic_suspensionFlow_constRoof`, with the flow-native closed-orbit-integral form
`livsic_suspensionFlow_constRoof_orbitIntegral`): a flow observable is a flow coboundary iff all its
closed-orbit integrals vanish, the transfer function being glued **exactly** across the
fundamental-domain seam `s = τ` by the base cohomological equation — no metric estimate, since
`IsFlowCoboundary` is a regularity-free notion. The Arnold cat map is the worked instance
(`CatMapToral.livsic_catSuspensionFlow` + `_orbitIntegral`, discharging the base direction with
`livsic_catTorus`), certified non-vacuous on both sides: the constant observable `1` is not a flow
coboundary, while `CatMapToral.sinFibreObservable` (the `sin(2π·)` fibre profile, zero-mean over one
lap) is (`isFlowCoboundary_sinFibreObservable`). The regularity-free tier-III converse is now
**upgraded to the classical-strength Hölder-regularity theorem** (issue #63): over the Bowen–Walters
embedding metric `embDist` a *Hölder* flow observable admits a *Hölder* flow transfer function iff
its induced base observable has vanishing periodic sums — abstractly `livsic_holderFlow_constRoof`
(+`_orbitIntegral`) for any base with the exponential-closing property and a dense orbit (both tier 2
and the issue's tier-4 Anosov-presentation statement), and `livsic_holderFlow_varRoof` for a variable
Lipschitz roof (bounded below/above). The cat suspension is the worked instance
`CatMapToral.livsic_catSuspensionHolderFlow` — the library's first Hölder-regularity flow-Livšic
result — non-vacuous on both sides (`isHolderFlowCoboundary_sinFibreObservable` cobounds,
`const_one_not_isHolderFlowCoboundary_catSuspension` does not). The keystone is the cross-seam Hölder
gluing `holderWith_suspTransfer`; roof-Lipschitz (not merely Hölder) is essential to preserve the
exponent — a Hölder roof degrades it to `r²` (disclosed, not delivered). Sources: Livšic 1972;
Katok–Hasselblatt §19.2; Bowen–Walters 1972; Barreira–Saussol CMP 214 (2000); Barreira–Radu–Wolf
Dyn. Syst. 19 (2004) §2.1.

### Suspension flows (`Continuous/`)

Beyond the abstract continuous-flow MET, the library builds the concrete **suspension/special flow**
of a base map under a roof function and analyzes its Lyapunov and entropy data. The flow Lyapunov
exponent is constructed **representative-free** as a `Quotient.lift` over orbit classes and computed
to `ae_flowExponentAt_eq_base_div_roof` — `flowExponentAt = λ_base / ∫τ` a.e. — with the cat-map
suspension as a fully worked positive-exponent instance
(`CatMapToral.catSuspension_flowExponentAt_eq_base_div_roof`). The flow's **own derivative data**
now lives on the same `FlowCocycle` interface that `oseledets_flow` consumes: over an invertible base
under the constant unit roof, the two-sided ℤ-indexed matrix cocycle `cocycleZ` (`TwoSided/`) plus a
**measurable canonical representative** `unitFwd q = (baseIter ⌊s⌋ x, Int.fract s)` of each orbit
class assemble into a genuine `quotientFlowCocycle` on the mapping torus (`Continuous/`), the four
`FlowCocycle` fields following from `cocycleZ`'s two-sided cocycle law through the floor split
`⌊a+t⌋ = ⌊a⌋ + ⌊Int.fract a + t⌋`. This is the **measurable-trivialization escape route** past the
non-descent obstruction: the issue's *class*-function conjugacy is provably impossible (different
representatives of a class carry different `⌊s⌋`), so the honest statement
`exists_flowCocycle_cohomologous_to_cover` is a **rep-level frame** `C(x,s) = cocycleZ ⌊s⌋ x`
relating the quotient cocycle to the cover cocycle `coverCocycle`, collapsing to the
conjugation-free canonical identity at the canonical representative. The exponent transports along
the `atTop` half-line to `flowExponentAt`, and the cat instance `CatMapToral.catQuotientFlowCocycle`
realizes a genuine flow cocycle with a.e. growth rate `log((3+√5)/2)`
(`catQuotientFlowCocycle_exponent`). The **general non-constant roof is out of scope** and disclosed:
the orbit quotient has no measurable canonical representative for a non-constant roof, so only the
exponent (not the matrix cocycle) descends there. On the entropy side, the full
**Abramov flow-entropy homogeneity** `h(φ_t) = t·h(φ_1)` (`t > 0`) is proved abstractly for any
measure-continuous measure-preserving flow on a standard Borel probability space
(`ksEntropy_flow_eq_mul`), following Ito's elementary generator-free argument (Nagoya Math. J. 41
(1971), 1–5): measure-continuity forces `H(φ_τP | P) → 0`, a two-family Shannon comparison
(`Entropy.entropy_finJoin_le_add_sum_condEntropy`) and an ε–δ alignment proposition
(`exists_isLUB_ksEntropyPartition_flow_ratio`, stated honestly in `EReal` — the ℝ form fails for
infinite-entropy flows) then pin the ratio. Applied to the measure-continuous Bernoulli suspension
flow (`measureContinuous_bernSuspensionFlow`, keystone
`tendsto_measureReal_symmDiff_suspensionFlowMap`), it gives the time-1 entropy
`h(ζ⁽ʳ⁾₁) = h_base / r` for **every** roof `r > 0`
(`ksEntropy_bernConstSuspension_time_one_irrational`), retiring the former rational-roof restriction.
Complementarily, the constant-roof time-1 map of an ergodic Bernoulli base is **ergodic exactly when
the roof is irrational** (`ergodic_suspensionFlowMap_one_const_roof`), with a cat-map twin
(`CatMapToral.ergodic_catSuspension_timeOne_const_irrational`, witnessed at `r = √2`). Cat-side, the
eigenfunction-rigidity theorem `CatMapToral.catTorus_eigenfunction_ae_zero` — any measurable
`g : 𝕋² → ℂ` with `g(catTorus x) = l·g(x)`, `‖l‖ = 1`, `l ≠ 1`, vanishes a.e. — supplies the Fourier
rigidity behind the cat suspension's ergodic time-1 map. The suspension space also carries a genuine
**Bowen–Walters metric** (issue #63): rather than the naive finite-route gauge `routeDist` — provably
*not* a metric (the low/high routes are essential; documented counterexamples to the triangle
inequality) — the honest metric `embDist` is realized by a Kuratowski-type embedding into
`X →ᵇ ℝ` (two height-weighted test bundles `muFun`/`nuFun` plus a circle-height gauge), proved a
metric (`embDist_triangle`, `embDist_eq_zero`), inducing the quotient topology
(`suspensionMetricSpace`), Polish for a compact base (`suspensionPolish`), with the flow 5-Lipschitz
in time (`embDist_flow_le`). The variable-roof version `embDistVar` (roof bounded below by `ρmin`)
normalizes fibre heights to the unit circle — making the seam gluing roof-independent — with the flow
`(5/ρmin)`-Lipschitz (`embDistVar_flow_le`); rescaling a variable roof to a constant one is a wall
(bi-Lipschitz only when the roof is cohomologous to a constant), so the metric is built directly on
the normalized coordinate. This metric is the substrate for the Hölder-regularity flow-Livšic theory
above.

### Descriptive-set-theoretic residuals (`MeasureTheory/`, `Singular/`)

The measurability of the singular Oseledets projector rests on a small library of classical
descriptive set theory built here from scratch: **Lusin's theorem** in the graph-measurability form
(`lusin_continuousOn`), the **generalized first separation theorem** for a sequence of analytic sets
(`generalized_first_separation`), the **Kunugui–Novikov** open-section separation
(`kunuguiNovikov_openSections`), and the **Novikov projection theorem** (Srivastava 4.7.11) that a
Borel set with compact vertical sections has Borel projection
(`measurableSet_image_fst_of_isCompact_sections`). Together they discharge the everywhere-Borel
singular filtration `measurable_orthProjMatrix_lambdaSublevel` (issue #11).

The same analytic/coanalytic vocabulary settles a **complexity** question about
measurable-conjugacy invariants (issue #61). Over the Polish parameter space
`Params X = C(X,X)³ × P(X)²` of continuous-dynamics systems `(T, S, π, μ, ν)` on a compact metric
carrier `X`, the **section relation** (a continuous, measure-preserving, equivariant right inverse
of the factor map `π`) cuts out a closed subset of `Params X × C(X,X)` (`isClosed_sectionRel`), so
section-existence `{p | ∃ s, SectionRel p s}` is **analytic** (`Σ¹₁`, a continuous projection of a
closed set — `sectionExists_analyticSet`) and the sealed set is dually **coanalytic** (`Π¹₁`,
`isSealed_coanalyticSet`), with the identity parameter certifying non-vacuity
(`sectionExists_nonempty`). Two Polish-space facts that Mathlib lacked make the hierarchy apply and
are proved here as upstream candidates: `P(X)` is Polish for compact metric `X`
(`polishSpace_probabilityMeasure`, via compact + metrizable ⇒ completely metrizable) and the
pushforward `(f, ν) ↦ f_* ν` is jointly continuous (`continuous_probabilityMeasure_map_compact`).
Disclosed, not delivered: the classical `L⁰`/MALG measurable-section parametrization
(Foreman–Rudolph–Weiss) needs `L⁰`-as-Polish, and the tier-3 `Σ¹₁`-completeness (non-Borelness of
the seal) needs Borel-reduction machinery — both absent from Mathlib — and a concrete sealed witness
is left to its own follow-up.

### Quantum information (`OperatorEntropy/`)

A finite-dimensional quantum-information layer on the same matrix/CFC infrastructure: the von
Neumann and Umegaki relative entropies, Klein's inequality, **Lieb's joint-convexity theorem**,
the **partial-trace data-processing inequality** (arbitrary ρ, faithful σ; also in the literal
faithful-case form `relEntropyMonotone_partialTrace_faithful` for positive-definite ρ, σ) with its
faithful-ancilla Stinespring-family extension (`monotonicity_relEntropy_under_stinespring`; no
DPI for an arbitrary CPTP channel is claimed), the **CNT dynamical entropy** whose abelian corner
recovers classical KS entropy — the system-level identity `cntDynamicalEntropyAbelian_eq_ksEntropy`
(and its full-partition upgrade `ksEntropy_eq_cntDynamicalEntropy`, a supremum over *all*
operational partitions) is a disclosed `0 = 0` on the finite-permutation model, so the substantive
content is the per-resolution `vonNeumannEntropy_corrMatrix_eq_ksEntropySeq`, together with the
explicit **subadditivity counterexample** `not_subadditive_cnt_entropySeq` showing why the CNT rate
must be defined as an infimum rather than a Fekete limit — and **both directions of Petz's equality
theorem** — recovery ⟹ DPI saturation (`petz_recovery_implies_equality`) and, fully general,
saturation ⟹ recovery (`petz_equality_recovery_general`), whose analytic heart is the
modular-cocycle intertwining `partialTrace_equality_imp_intertwinesIt`.

On top of this the layer now carries **genuinely non-commutative sealed dynamics**, honestly
rescoped (issue #59). The issue's literal tier-1 goal — a *system-level* strictly positive quantum
dynamical entropy in finite dimension — is **provably impossible** by the repo's own
`cntDynamicalEntropy_eq_zero`, and this is disclosed prominently. What survives are two honest
certificates. First, a **per-resolution correlation-entropy dichotomy** `cex_strictly_above_abelian`:
on the witness system (identity dynamics, invariant pure state `|0⟩⟨0|`) *every* diagonal/abelian
operational partition yields exactly **zero** correlation entropy at every resolution (a rank-one
Gram collapse, `cex_abelian_restriction_entropy_zero`), while the non-commuting partition has
strictly positive entropy at resolution 2 — issue #59's "entropy strictly above every abelian
restriction", stated at the per-resolution level where the non-commutativity actually lives. Second,
the **dephasing recovery seals** `quantum_seal_dephase` (pure-state, a strict relative-entropy drop
of `log 2`) and `quantum_seal_dephase_faithful` (faithful-state, drop `log 2 − h₂((1+r)/2)` via
Mathlib's binary-entropy strict maximum): the dephasing channel's strict data-processing drop against
a **non-uniform** diagonal reference `diagState s` forecloses any faithful-ancilla Stinespring
recovery — a QA pass caught and repaired a degenerate `σ = I/2` formulation (which makes the
no-recovery content vacuous), documented in the module docstring; supporting spectral lemmas
`vonNeumannEntropy_eq_zero_of_sq_eq`, `vonNeumannEntropy_conj`, `relEntropy_maximallyMixed`. Third, a
**canonical-MASA incompatibility certificate** `qDynamics_seal_no_common_canonical_masa` on a
Pythagorean `(3,4,5)` unitary (all entries in `ℚ(i)`, so `norm_num` closes each claim): the seal's
diagonal MASA is not dynamics-invariant and the dynamics' eigenbasis MASA is not seal-invariant. The
natural Hadamard/rotation choices provably *fail* (the circular MUB basis is simultaneously
dephasing- and swap-invariant, hence a common MASA); and since every unital `*`-endomorphism of `M_d`
is inner (Skolem–Noether) it always preserves *some* MASA, so the certificate is necessarily about
the dynamics/seal **pair**. Disclosed: the Petz-MAP corollary is not shipped (it would need a
general-`KrausChannel` DPI absent from the repo), and the no-common-MASA-over-all-conjugates statement
is proved only pairwise on the two canonical candidate MASAs. Sources: Connes–Narnhofer–Thirring
1987; Alicki–Fannes 2001; Neshveyev–Størmer 2006; Petz 1986/2003; Wilde; the MUB literature.

The finite-dimensional degeneracy `cntDynamicalEntropy_eq_zero` is recast as **saturation of a
finite reservoir** rather than an identically-zero artifact (issue #69), and its complementary
**growing-tower** companion is constructed (issue #70). On the reservoir side, the iterated-refinement
cumulative CNT/ALF entropy is capped by `2·log d = log(d²)` uniformly in the resolution `n`
(`CNT.cntCumulativeEntropy_le_reservoir`, with the bounded-saturation form `CNT.cntEntropySeq_bddAbove`),
so the per-step rate is squeezed to `0` through a generic domain-neutral engine
`rate_to_zero_of_cumulative_bounded` (nonnegative bounded sequence ⟹ `a n / n → 0`) — the quantum
pigeonhole in the same shape as the classical count-vs-cardinality face. This cap is **tight** at
`d = 2`: the Pauli operational partition `CNT.pauliPartition` at the maximally mixed state `I/2` makes
the correlation matrix at `n = 1` itself maximally mixed on the four-element index set, filling
`log(d²) = log 4` at a single step for every unital `*`-endomorphism
(`CNT.corrMatrix_pauliPartition_one`, `CNT.vonNeumannEntropy_corrMatrix_pauliPartition_eq`), which also
shows the naive `log d` cap is false for the correlation-matrix construction. On the growing side, the
**growing-finite qubit tower** `blockEntropy_eq` bundles the finite blocks `M₂ ↪ M₄ ↪ M₈ ↪ ⋯` — carrier
`Qbits n` of cardinality `2ⁿ`, capacity-enlargement embedding `shiftAdjoinQubit : A ↦ 1 ⊗ A` adjoining
one fresh qubit per step, and the marginal-consistent product state `rhoPow ρ n = ρ^{⊗n}` — with block
entropy exactly `n·S(ρ)` (iterated von Neumann additivity `vonNeumannEntropy_additive_kronecker`), hence
a per-step **spatial** rate converging to `S(ρ)` (`tendsto_blockEntropy_div`), positive off the pure
states (`blockEntropy_rhoR_pos`) and equal to `n·log 2` at the maximally mixed state
(`blockEntropy_maximallyMixed`). The dephasing seal is lifted uniformly over an arbitrary ancilla block —
the `dephaseKronId` partial-dephasing channel on `M₂ ⊗ M_blk` still admits no faithful-ancilla
Stinespring recovery, with a reference pair `(ρ_r, diagState s)` whose dephased images are distinct
(`quantum_seal_dephase_kron_faithful`, pure-input variant `quantum_seal_dephase_kron`). The bundled
witness `GrowingQuantumWorld` (`growingQuantumWorld_exists`) carries all three on one growing object:
positive spatial entropy production, the per-stage seal at the world's own block states `ρ_r^{⊗n}`, and
a base-factor non-commutativity certificate. Honest scope, stated in the module docstrings: this is the
**growing-finite** tower, not the completed `⊗_ℤ M₂` chain (that idealization's directed-local first cut
is issue #71 below; the completed C\*-chain itself stays out of reach — Mathlib has no non-commutative
inductive limit); the
step is capacity enlargement, not forgetting; the seal is a **channel-level (single-step) seal per
stage**, not a flow seal; and the spatial per-step rate is complementary to — with no tension against —
the fixed-`d` temporal `cntDynamicalEntropy_eq_zero`. The CNT/QIT ingredients are standard
(Connes–Narnhofer–Thirring, *Comm. Math. Phys.* **112** (1987) 691–719; Ohya–Petz, *Quantum Entropy and
Its Use*; Nielsen–Chuang §11.3; Petz 1986/2003); the reservoir-tightness and the bundling of rate + seal
+ non-commutativity on one growing object are this repository's contribution.

The growing tower's **forgetting-twin** is then assembled as the **quantum Bernoulli shift** in the
directed-local representation (issue #71). Where the spatial rate of issue #70 comes from *enlarging* the
algebra one qubit per step, the temporal rate here comes from **forgetting on a fixed hierarchy**: the
witness `quantumBernoulliShift_exists` / `QuantumBernoulliShift` bundles the fixed directed system of
local algebras `M_{2ⁿ}` with a commuting unital `⋆`-injective inclusion (`appendQubit`, far-end site) and
shift (`shiftAdjoinQubit`, capacity enlargement), a shift-invariant tracial state given by compatible
finite marginals (`rhoPow_shiftAdjoinQubit_pairing` is shift-invariance of *every* product state;
`appendQubit_maximallyMixed_pairing`), the temporal **site-window entropy rate** `= log 2`
(`windowEntropy_tracial`, `tendsto_windowEntropy_div_tracial`) certified stationary by the
site-translation identity `shiftIter_pairing`, and a per-level dephasing seal at the tracial blocks
(`ChainSealed`, `chain_seal_dephase_faithful`) — rate and seal on one fixed non-commutative object.
Alongside it, the **finite modular clock** `modAut` (`σ_t(a) = ρ^{it} a ρ^{-it}`, on the existing Lieb
`cpow`/`upow` infrastructure) carries the automorphism-group laws, the `β = 1` KMS boundary identity
`kms_boundary`, tower compatibility `modAut_shiftAdjoinQubit`, and the **intrinsic-clock dichotomy** that
makes the modular reading non-vacuous: the tracial state has trivial flow (`modAut_maximallyMixed_eq_id`)
while a non-tracial faithful (Powers-type) product state has provably nontrivial flow
(`modAut_diagState_ne_id`, witness `E₀₁ ↦ −E₀₁`). Honest scope, disclosed prominently in the module
docstrings: this is the **growing-finite / directed-local** representation, **not** the completed C\*-chain
`⊗_ℤ M₂` (Mathlib has no non-commutative inductive limit — `Ring.DirectLimit` is `CommRing`-only, and no
GNS/Tomita–Takesaki is built); the entropy is a **bespoke site-window rate**, not the full CNT supremum
over all finite subalgebras; and the KMS boundary identity is trace cyclicity (holding for every invertible
ρ), with the modular content residing in the dichotomy and the group/tower laws. Sources:
Connes–Narnhofer–Thirring, *Comm. Math. Phys.* **112** (1987) 691–719 (shift entropy `= log 2 =` entropy
density); Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics II*, §5.3; Ohya–Petz,
*Quantum Entropy and Its Use*; R. T. Powers, *Ann. of Math.* **86** (1967).

### Status and documented frontiers

The GitHub issue tracker is at **zero open issues** — every formalization target has been discharged
sorry-free. A handful of mathematical frontiers are *disclosed in place* rather than silently
elided, and they are recorded honestly in the module docstrings: the descriptive-set layer proves
the compact-section (Novikov) projection theorem but not the full Π¹₁-boundedness / general
Arsenin–Kunugui uniformization; and the flow-Livšic story now closes the tier-III converse for
**constant-roof** suspension flows (`livsic_suspensionFlow_constRoof`, seam glued by an exact
identity) and its **Hölder-regularity** upgrade for both constant and variable *Lipschitz* roofs
(`livsic_holderFlow_constRoof`, `livsic_holderFlow_varRoof`, on the Bowen–Walters embedding metric),
leaving only the flow-Livšic theorem for a roof that is *merely Hölder* (not Lipschitz) — where the
fibre-comparison change of variables degrades the transfer exponent from `r` to `r²` — as the
remaining disclosed front;
likewise the quotient suspension `FlowCocycle` is built for the **constant unit roof** only, since a
non-constant roof has no measurable canonical orbit-representative in the library (only the flow
exponent, not the matrix cocycle, descends there), and the issue's *class*-level cocycle conjugacy
is provably impossible so the honest export is the rep-level frame. Each such boundary is stated as
a hypothesis or a scoped instance, never hidden.

## Trust story

- **Sorry-free**: warnings are promoted to errors in `lakefile.toml`, so any `sorry` fails
  `lake build` (and CI). `main` is sorry-free everywhere; in-progress/experimental material lives
  on the `frontier` branch and reaches `main` only through clean, sorry-free PRs.
- **Linter-enforced**: the whole `ErgodicTheory` library builds under Mathlib's
  `linter.mathlibStandardSet` with warnings-as-errors, so CI fails on any style-lint regression.
- **Axiom-audited**: `test/AxiomAudit.lean` guards 731 declarations with
  `#guard_msgs in #print axioms` on every build. (This certifies axiom-cleanliness; theorems with
  hypotheses are, as always, exactly as strong as their hypotheses — the blueprint states them in
  full.)
- **Blueprint-checked**: `lake exe checkdecls` (run by CI) verifies every `\lean{...}` name in the
  blueprint against the built library, so the blueprint cannot drift from the source.

### Attribution and novelty

This README and the blueprint document what is formalized and cite the classical sources each proof
follows. Phrases like "the library's first …" are internal navigation, not priority claims. In a few
places where we could not locate a statement or construction in the literature (noted in the relevant
module docstrings), we say so explicitly — such notes are invitations for correction, not assertions
of novelty; whether anything here is mathematically new is for the community to judge.

## Layout

```
ErgodicTheory.lean        -- library root; imports every module
ErgodicTheory/
  Cocycle/            -- iterated linear cocycle, norms, Furstenberg–Kesten
  Ergodic/            -- maximal ergodic inequality, Birkhoff, Kingman
  Lyapunov/           -- Lyapunov exponents, the limsup filtration, the final assembly chain
    Extensions/       -- post-theorem corollaries (spectrum, exponent sums, det identity, exterior
                      --   growth, inverse, restriction, non-ergodic, regularity, singular)
  MultiplicativeErgodic.lean  -- the one-sided MET (filtration form)
  TwoSided/           -- the two-sided splitting; the two-sided ℤ-indexed cocycle cocycleZ
  Continuous/         -- the continuous-flow MET + suspension flows (flow exponent, entropy descent,
                      --   time-1 ergodicity, abstract Abramov flow-entropy homogeneity,
                      --   constant-roof flow-Livšic tier-III equivalence, the quotient-level
                      --   suspension FlowCocycle from cocycleZ + measurable canonical rep, the
                      --   unit-roof suspension factor functor suspensionFactorMap, the
                      --   Bowen–Walters embedding metric embDist/embDistVar + Polishness)
  Livsic/             -- Livšic cohomological rigidity (abstract iff, full-shift/two-sided/SFT/
                      --   cat-map/doubling instances, full measurable rigidity, flow obstruction,
                      --   Hölder-regularity flow-Livšic for constant + variable Lipschitz roofs)
  Singular/           -- everywhere-Borel projector of the singular forward filtration
  Entropy/            -- Kolmogorov–Sinai entropy theory: partitions, conditional entropy,
                      --   generator theorem, Abramov–Rokhlin, Margulis–Ruelle, Ruelle atom-count
                      --   backbone (incl. the positive-measure atom count posAtomCount)
  Krieger/            -- Krieger's finite generator theorem, SMB, Rokhlin towers, coding,
                      --   the Blackwell separating ⇒ two-sided-generating bridge
  Multifractal/       -- Z_q, τ(q), Rényi dimensions D_q, local/Hausdorff dimension,
                      --   Bernoulli-suspension witness, the Rényi entropy rate + factor-code
                      --   data-processing inequality (c-function tier 1)
  Smooth/             -- derivative cocycle, Rokhlin inequality, volume-case Pesin formula
  Examples/           -- Arnold cat map (strong mixing, eigenfunction rigidity, ergodic time-1
                      --   suspension, flow-Livšic + Hölder flow-Livšic instances, the sharp entropy
                      --   h = log((3+√5)/2) via grid-telescope lower bound + Adler–Weiss generator
                      --   upper bound, the Adler–Weiss coding as a factor/conjugacy onto the golden
                      --   SFT + coarse two-box partition + depth-two symbolic flow tower, quotient
                      --   flow cocycle, statistical laws: exponential decay of correlations,
                      --   Green–Kubo, concentration, exponent rate), doubling map, Pesin/Rokhlin
                      --   witnesses
  OperatorEntropy/    -- quantum information: relative entropy, Klein/Lieb, data processing,
                      --   CNT dynamical entropy (the finite reservoir cap + its d=2 Pauli-partition
                      --   tightness), Petz recovery + equality, the dephasing recovery seals +
                      --   per-resolution non-commutativity + canonical-MASA certificates, and the
                      --   growing-finite qubit tower (GrowingTower/: linear block entropy n·S(ρ),
                      --   Kronecker-lifted dephasing seal, the bundled sealed-and-alive world; plus
                      --   its forgetting-twin, the directed-local quantum Bernoulli shift with
                      --   temporal site-window rate log 2 + the finite modular-clock dichotomy)
  MeasureTheory/      -- descriptive-set residuals (Lusin, Novikov first separation, Kunugui–Novikov,
                      --   the Novikov compact-section projection theorem, covering numbers; P(X)
                      --   Polish + joint pushforward continuity; analyticity of section-existence)
test/
  AxiomAudit.lean     -- guarded #print-axioms regression (separate lib; not upstreamable source)
blueprint/            -- leanblueprint LaTeX source (web + PDF; \lean-linked to declarations)
home_page/            -- Jekyll landing page for the GitHub Pages site
lakefile.toml         -- package config (ErgodicTheory + AxiomAudit libraries)
lean-toolchain        -- pinned Lean version (leanprover/lean4:v4.30.0-rc2)
docs/                 -- Mathlib-conventions guide, references.bib, finished-library state map
```

## Building

```bash
lake build        # or: make build  — builds the library and the axiom audit
```

The dependencies are Mathlib (pinned in `lake-manifest.json`) and
[checkdecls](https://github.com/PatrickMassot/checkdecls), a tiny standalone utility used by the
blueprint CI. In a fresh checkout, fetch the precompiled Mathlib cache first:

```bash
lake exe cache get
```

(The devcontainer's `post-create.sh` does this automatically.)

## Blueprint

The repository ships a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) blueprint
under `blueprint/` — chapters covering the cocycle theory, the ergodic theorems, the Lyapunov
assembly, the MET and its corollaries, the two-sided and continuous versions, the entropy
theory, and the quantum entropy/Petz layer — whose nodes are `\lean`-linked to the formalized
declarations. The
`.github/workflows/blueprint.yml` workflow compiles the blueprint (web + PDF + dependency graph)
and deploys it to GitHub Pages on every push to `main`; on pull requests it builds as a dry run
without deploying. (The doc-gen4 API reference is deliberately not built in CI — regenerating
HTML for the entire Mathlib import closure exceeds the CI budget.)

To build the blueprint locally (requires a TeX distribution, `graphviz`, and
`pip install leanblueprint`):

```bash
lake build                          # the Lean library must be built first
leanblueprint pdf                   # blueprint/print/print.pdf
leanblueprint web                   # blueprint/web/ (also writes blueprint/lean_decls)
lake exe checkdecls blueprint/lean_decls   # verify every \lean{...} name exists
```

## Development environment

A `.devcontainer/` is provided (Lean 4 + the `leanprover.lean4` VS Code extension). Open the
repo in a devcontainer-aware editor for a ready-to-go toolchain.

## License

Apache 2.0 — see [LICENSE](LICENSE).
