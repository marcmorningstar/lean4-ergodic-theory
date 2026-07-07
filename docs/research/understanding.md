# Understanding the Oseledets Multiplicative Ergodic Theorem (MET)

A self-contained mathematical account of the MET as we will formalize it, plus
the full chosen proof route as a dependency-ordered ladder of lemmas, each tagged
**exists in Mathlib** (with the declaration) or **to build**. Written so a fresh
agent with no other context can understand both the mathematics and the plan.

Cross-checked against the pinned Mathlib source under
`/workspaces/lean4-oseledets/.lake/packages/mathlib/Mathlib` (toolchain
`leanprover/lean4:v4.30.0-rc2`). Wherever a Mathlib fact is load-bearing the
declaration name and file have been spot-verified on disk (noted inline).

---

## 0. The object: a linear cocycle over a measure-preserving system

Fix a dimension `d ∈ ℕ`. The data are:

- A **probability space** `(X, 𝓐, μ)`.
- A **measure-preserving transformation** `T : X → X` (`μ(T⁻¹ B) = μ(B)`). For the
  splitting form `T` must be **invertible** (bimeasurable); for the filtration form
  it need not be.
- A measurable **generator** `A : X → GL(d, ℝ)` (or, more generally, into real
  `d × d` matrices; `GL` is what we target).

The **iterated cocycle** (newest factor on the left — the "matrices on the left"
convention used by Bochi, Viana, Filip):

```
A⁽⁰⁾(x) = Id,    A⁽ⁿ⁾(x) = A(Tⁿ⁻¹x) · A(Tⁿ⁻²x) ⋯ A(Tx) · A(x)   (n ≥ 1).
```

It obeys the **cocycle identity**

```
A⁽ᵐ⁺ⁿ⁾(x) = A⁽ᵐ⁾(Tⁿx) · A⁽ⁿ⁾(x).
```

When `T` is invertible the cocycle extends to negative times by
`A⁽⁻ⁿ⁾(x) = A(T⁻ⁿx)⁻¹ ⋯ A(T⁻¹x)⁻¹`, so `A⁽ⁿ⁾(x)⁻¹ = A⁽⁻ⁿ⁾(Tⁿx)`.

Fix any norm `‖·‖` on `ℝᵈ`; use the induced operator norm on matrices (all norms
equivalent in finite dimension). The **co-norm** is `m(L) = inf_{‖v‖=1} ‖Lv‖`; for
invertible `L`, `m(L) = ‖L⁻¹‖⁻¹`.

### 0.1 The integrability hypothesis (load-bearing — state it exactly)

With `log⁺ t := max(log t, 0)`:

- **One-sided / filtration form** (and Furstenberg–Kesten top exponent):
  `log⁺‖A‖ ∈ L¹(μ)`, i.e. `∫_X max(0, log‖A(x)‖) dμ < ∞`.
- **Two-sided / splitting form** (and the finite bottom exponent): additionally
  `log⁺‖A⁻¹‖ ∈ L¹(μ)`.

It is **`log⁺`, not `log`**: the lower tail may be `−∞`, so the bottom exponent
`λ_k = −∞` is legitimate in the pure one-sided non-invertible setting. Working in
`GL(d,ℝ)` with `log⁺‖A⁻¹‖ ∈ L¹` keeps it finite. Do **not** strengthen to
`log ∈ L¹`; it would exclude valid cocycles. In Mathlib `log⁺` is
`Real.posLog = fun r ↦ max 0 (log r)`, notation `log⁺`
(`Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`, **exists**).

### 0.2 Ergodicity

All clean statements assume `μ` is **ergodic** for `T`. Then the exponents `λᵢ`,
their count `k`, and multiplicities `dᵢ = dim Eⁱ` are a.e. **constant**. Without
ergodicity they become `T`-invariant measurable functions (ergodic decomposition).
The collapsing tool — *an a.e. `T`-invariant measurable function is a.e. constant*
— is `Ergodic.ae_eq_const_of_ae_eq_comp_ae`
(`Mathlib/Dynamics/Ergodic/Function.lean`, **exists**, verified).

---

## 1. The theorem, in its two structural forms

The MET refines Furstenberg–Kesten (which resolves only the top and bottom
exponents, with no subspaces) to resolve **all** distinct exponents and attach
geometry. There are two inequivalent geometric forms. **The filtration needs only
the one-sided hypotheses; the splitting requires invertibility.** This distinction
governs the whole plan.

### 1.1 One-sided MET — filtration / flag form  (our TARGET; Filip Thm 2.2.6, Bochi Thm 2, Zhu Thm 5.1)

> **Hypotheses.** `(X,μ)` a probability space, `T : X → X` ergodic
> measure-preserving (not necessarily invertible), `A : X → GL(d,ℝ)` measurable
> with `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹(μ)`.
>
> **Conclusion.** There exist reals `λ₁ > λ₂ > ⋯ > λ_k` (the **Lyapunov
> exponents**) and, for `μ`-a.e. `x`, a strictly decreasing **flag** of subspaces
> ```
> ℝᵈ = V¹ₓ ⊋ V²ₓ ⊋ ⋯ ⊋ V_kₓ ⊋ V_{k+1}ₓ = {0}
> ```
> such that for every `1 ≤ i ≤ k`:
> - **(equivariance)** `A(x) · Vⁱₓ = Vⁱ_{Tx}`, `k` and `λᵢ` are `T`-invariant;
> - **(growth)** `lim_{n→∞} (1/n) log‖A⁽ⁿ⁾(x)·v‖ = λᵢ` for all `v ∈ Vⁱₓ ∖ V^{i+1}ₓ`;
> - **(measurability)** `x ↦ Vⁱₓ`, `x ↦ λᵢ(x)` measurable.

Intrinsic description of the flag: `Vⁱₓ = { v : lim (1/n) log‖A⁽ⁿ⁾(x)v‖ ≤ λᵢ }`.
The multiplicity of `λᵢ` is `dim Vⁱ − dim V^{i+1}`. **Why only a flag, not a
splitting:** forward in time you can detect "grows no faster than `λᵢ`" (a closed,
nested condition), but you cannot canonically pick a complement — the directions
growing *exactly* at `λᵢ` are not forward-determined.

### 1.2 Two-sided MET — Oseledets splitting form  (future milestone; Bochi Thm 1, Filip Variant 2.2.10)

> **Hypotheses.** As above but `T` **invertible** and both `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹`.
>
> **Conclusion.** Reals `λ₁ > ⋯ > λ_k` and, a.e., a **direct-sum decomposition**
> ```
> ℝᵈ = E¹ₓ ⊕ E²ₓ ⊕ ⋯ ⊕ E_kₓ
> ```
> with `A(x)Eⁱₓ = Eⁱ_{Tx}` (genuine equivariance), the **two-sided** limit
> `lim_{n→±∞} (1/n) log‖A⁽ⁿ⁾(x)v‖ = λᵢ` for all `0 ≠ v ∈ Eⁱₓ`, and subexponential
> angle decay between the `Eⁱ`. The flag is recovered by `Vⁱ = Eⁱ ⊕ ⋯ ⊕ E_k`.

The splitting is obtained from the filtration by **applying the one-sided theorem
to the inverse cocycle** (forward flag `V⁺` of `T`, backward flag `V⁻` of `T⁻¹`,
with `η_j = −λ_{k+1−j}`) and intersecting: `Eᵢ = V⁺ⁱ ∩ V⁻^{k+1−i}`. Invertibility
and `log⁺‖A⁻¹‖ ∈ L¹` enter only here.

### 1.3 Equivalent classical (Ruelle/Oseledets) form, for context

The original limit `Λ(x) = lim_{n} (A⁽ⁿ⁾(x)* A⁽ⁿ⁾(x))^{1/2n}` exists; the
`exp λᵢ` are the eigenvalues of `Λ(x)` with multiplicities, and the orthogonal
filtration comes from its eigenspaces. The eigenvalues `λᵢ = lim (1/n) log σᵢ(A⁽ⁿ⁾)`
are the limiting growth rates of the **singular values**. This is the
exterior-power/singular-value route (Route B below). We use it only as a conceptual
cross-check and as the source of the multiplicity/spectrum bookkeeping; it is **not**
our primary proof route (see §3).

---

## 2. The proof routes, and which one we take

Every route bottoms out in the **pointwise Birkhoff ergodic theorem**, and the two
classical routes additionally in **Kingman's subadditive ergodic theorem**. The
decisive Mathlib facts (all spot-verified on disk):

- **Pointwise Birkhoff ergodic theorem: ABSENT.** Only the *mean* (von Neumann,
  L²) theorem exists (`Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean`:
  `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`). No a.e.
  convergence of `birkhoffAverage`. `birkhoffSum`/`birkhoffAverage` are defined
  (`Mathlib/Dynamics/BirkhoffSum/`) but only their algebra exists.
- **Maximal ergodic inequality / Garsia / Hopf lemma: ABSENT** (the usual gate to
  pointwise Birkhoff). Verified: zero hits.
- **Kingman subadditive ergodic theorem: ABSENT.** Only Fekete's *deterministic*
  lemma exists: `Subadditive.tendsto_lim` over `ℝ`, needing `BddBelow`
  (`Mathlib/Analysis/Subadditive.lean`).
- **Furstenberg–Kesten, Lyapunov, Oseledets: ABSENT** (zero hits).

So **both** pointwise Birkhoff and Kingman are missing — this dominates the cost
and shapes the route choice.

| Route | Engine | Extra heavy machinery | Mathlib gap to build |
|---|---|---|---|
| **A. Filip induction-on-dimension** (§3) | pointwise Birkhoff | Krylov–Bogoliubov-in-families + Krein–Milman on the projective bundle; measurable subbundles | pointwise Birkhoff; fibered invariant-measure compactness; measurable selection |
| **B. Classical Kingman + exterior powers** (Bochi/Viana/Ruelle) | Kingman (⇒ Birkhoff) | exterior-power norms, ordered SVD, Grassmannian completeness | **Kingman** (⇒ pointwise Birkhoff); inner product/norm on `⋀ᵏ`; `‖⋀ᵏA‖ = ∏σᵢ`; ordered singular values |
| C. Karlsson–Margulis (NPC geometry) | own maximal inequality | CAT(0)/Busemann/Cartan–Hadamard geometry | essentially all of NPC metric geometry |
| D. Filip geometric / Noncommutative ET | Kingman | symmetric spaces, Kaimanovich regularity, horofunctions | Lie/symmetric-space apparatus |

Routes C and D require building large theories (NPC geometry, symmetric spaces)
with little reuse for a single theorem — **rejected**.

### Chosen route: **B (classical Kingman → Furstenberg–Kesten → induction-on-dimension), one-sided filtration first.**

Rationale (this is the lightest *credible* footprint given what Mathlib actually
has, and the most faithful path to a sorry-free proof):

1. **Kingman is the smaller, more self-contained, more reusable build than the
   alternative.** Route A's hardest piece is *fibered* Krylov–Bogoliubov + Krein–
   Milman + extreme-point-is-ergodic + measurable subbundles on the projective
   bundle — a bespoke functional-analysis/measure-theory gadget with a custom
   weak-* topology, of which essentially none is packaged in Mathlib. Kingman, by
   contrast, has a single classical proof (Steele 1989) resting on **only** the
   pointwise Birkhoff theorem plus elementary partition combinatorics, is
   independently valuable, and lands Furstenberg–Kesten almost for free.
2. **Pointwise Birkhoff must be built either way** (Route A needs it on the
   projective bundle; Route B needs it inside Kingman and for tempering). So we pay
   that cost once, at the bottom, and reuse it.
3. **Kingman directly gives the top exponent** (Furstenberg–Kesten), which is the
   cleanest first real milestone and isolates the hardest dependency early.
4. The induction-on-dimension peeling (Bochi/Zhu Route A-math, but Kingman-backed)
   avoids the need to *build* the complete Grassmannian-with-`|sinθ|`-metric and the
   eigenspace-Cauchy estimate of the pure exterior-power route. We use exterior
   powers and singular values only where Mathlib already supports them (functorial
   `exteriorPower.map`, `LinearMap.singularValues`, spectral theorem, `CFC.sqrt`),
   namely to *identify* multiplicities/spectrum, not as the existence engine.

The two-sided splitting is then a corollary obtained by running the one-sided
theorem on the inverse cocycle and intersecting filtrations.

---

## 3. The chosen proof, as a dependency-ordered ladder of lemmas

Convention fixed once: exponents **decreasing** `λ₁ > ⋯ > λ_k`; flag
`ℝᵈ = V¹ ⊋ ⋯ ⊋ V_k ⊋ 0` with `Vⁱ = {v : λ̄(x,v) ≤ λᵢ}`; cocycle factors prepended on
the left. `λ̄(x,v) := limsup_{n} (1/n) log‖A⁽ⁿ⁾(x)v‖`.

Each item is tagged **[EXISTS]** (reuse, with decl) or **[BUILD]**. Ordered so each
strictly depends only on earlier items.

### Layer 0 — Mathlib substrate (all EXISTS; reuse wholesale)

- **L0.1** Measure-preserving / ergodic API: `MeasureTheory.MeasurePreserving`,
  `MeasurePreserving.iterate`, `Ergodic`, `PreErgodic.ae_empty_or_univ`.
  *(`Mathlib/Dynamics/Ergodic/{MeasurePreserving,Ergodic}.lean`.)* **[EXISTS]**
- **L0.2** Invariant-⇒-constant: `Ergodic.ae_eq_const_of_ae_eq_comp_ae`.
  *(`Mathlib/Dynamics/Ergodic/Function.lean`.)* **[EXISTS]**
- **L0.3** Birkhoff sums/averages + algebra: `birkhoffSum`, `birkhoffAverage`,
  `birkhoffSum_add` (the additive cocycle identity — prototype to imitate).
  *(`Mathlib/Dynamics/BirkhoffSum/`.)* **[EXISTS]**
- **L0.4** Conditional expectation toolkit (for the Birkhoff/Kingman L¹ proof):
  `condExp` (`μ[f|m]`), `condExp_condExp_of_le` (tower), `setIntegral_condExp`,
  `condExp_mono`, conditional Jensen, `MeasurableSpace.invariants`.
  *(`Mathlib/MeasureTheory/.../ConditionalExpectation/*`, `.../MeasurableSpace/Invariants.lean`.)*
  **[EXISTS]**
- **L0.5** Fekete: `Subadditive.tendsto_lim` (bounded-below subadditive `ℝ`-seq).
  *(`Mathlib/Analysis/Subadditive.lean`.)* **[EXISTS]** — used for `aₙ = ∫gₙ` and as the
  model for the limit object.
- **L0.6** `log⁺`: `Real.posLog` + monotonicity/subadditivity lemmas.
  *(`Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`.)* **[EXISTS]**
- **L0.7** Matrix L2 operator norm, submultiplicative: `Matrix.l2_opNorm_mul`,
  `l2_opNorm_def`, `l2_opNorm_mulVec` (scoped `Matrix.Norms.L2Operator`).
  *(`Mathlib/Analysis/CStarAlgebra/Matrix.lean`.)* **[EXISTS]**
- **L0.8** `GL(d,ℝ)`, `det` monoid hom, `det_mul`.
  *(`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`, `.../Determinant/Basic.lean`.)*
  **[EXISTS]**
- **L0.9** Spectral/singular-value tooling (for spectrum identification, two-sided
  cross-check): `LinearMap.singularValues` (+ `_antitone`, `sq_singularValues_fin`),
  `LinearMap.IsSymmetric.eigenvalues`/`spectral_theorem`, `CFC.sqrt`,
  `Matrix.PosSemidef`, `exteriorPower.map`/`map_comp` (functorial `⋀ᵏA`).
  *(`Mathlib/Analysis/InnerProductSpace/{SingularValues,Spectrum}.lean`,
  `.../Rpow/Basic.lean`, `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean`.)* **[EXISTS]**
- **L0.10** Flag of submodules: `Flag` / `Module.Basis.toFlag`
  *(`Mathlib/LinearAlgebra/Basis/Flag.lean`)*. **[EXISTS]** — but **no measurable
  structure on flags/Grassmannian** (see Risks).

### Layer 1 — the pointwise ergodic theorem (the bottom gate)

- **L1.1** **Maximal ergodic inequality** (Hopf/Garsia): for `f ∈ L¹`, the maximal
  function set has the integral bound. *Prerequisite for L1.2.* **[BUILD]** (absent;
  zero hits for maximal/Hopf/Garsia ergodic).
- **L1.2** **`condExp` vs measure-preserving composition**:
  `μ[g ∘ T | invariants T] =ᵐ μ[g | invariants T] ∘ T` (and the `T`-invariant-σ-algebra
  version). **[BUILD]** (no such lemma; build from `setIntegral_condExp` +
  `MeasurePreserving`). Note `ContinuousLinearMap.comp_condExp_comm` exists but is a
  *different* statement (CLM through condExp), not composition with the dynamics.
- **L1.3** **Pointwise (Birkhoff) ergodic theorem**: for `MeasurePreserving T μ`,
  `g ∈ L¹`, `birkhoffAverage ℝ T g n x → μ[g | invariants T] x` for `μ`-a.e. `x`
  (and in L¹); under `Ergodic`, the limit is the constant `∫g dμ`.
  *Depends on:* L1.1, L1.2, L0.2, L0.4. **[BUILD]** (the single most reusable new
  result; everything above it in the ladder uses it).

### Layer 2 — Kingman's subadditive ergodic theorem

- **L2.1** **Subadditive cocycle predicate**: `g : ℕ → X → ℝ` (or `EReal`) with
  `g (n+m) x ≤ g n x + g m (T^[n] x)` a.e., `g 1` (i.e. `g₁⁺`) integrable.
  Generalizes `birkhoffSum_add`. **[BUILD]** (thin def + basic lemmas).
- **L2.2** **Partition / sub-additivity-by-blocks** (Steele Step 0): for any
  consecutive-interval partition of `{0,…,n−1}`,
  `gₙ(x) ≤ Σᵢ g_{ℓᵢ}(T^{kᵢ}x)`. **[BUILD]** (induction on L2.1).
- **L2.3** **Reduction to a non-positive process** (Steele Step 1): subtract the
  Birkhoff sum of `g₁`; `g̃ₙ ≤ 0`, still subadditive, same limit shifted by the
  Birkhoff limit. *Depends on:* L1.3, L2.1. **[BUILD]**
- **L2.4** **`T`-invariance of `liminf gₙ/n`** (Steele Step 2): `g ≤ g∘T` and
  measure-preservation force `g∘T =ᵐ g`. *Depends on:* L0.1. **[BUILD]**
- **L2.5** **Greedy covering / fundamental lemma** (Steele Steps 3–6): truncate,
  define the bad sets `B_L`, run the greedy block-selection, get the length lower
  bound, apply L1.3 to the indicator `1_{B_L}`, peel `n` then `L` to squeeze
  `limsup gₙ/n ≤ liminf gₙ/n`. *Depends on:* L1.3, L2.2, L2.3, L2.4. **[BUILD]** —
  the most intricate (index-bookkeeping) part.
- **L2.6** **Kingman**: `gₙ/n → G` a.e., `G` `T`-invariant in `[−∞,+∞)`,
  `∫G = inf_n (1/n)∫gₙ`; constant `= inf` under ergodicity (via L0.2).
  *Depends on:* L2.3–L2.5. **[BUILD]**
  *(EReal/`−∞` bookkeeping: decide once whether to work in `EReal` throughout or
  carry the `inf_n ∫gₙ/n > −∞` proviso; see Risks.)*

### Layer 3 — Furstenberg–Kesten (extremal exponents)

- **L3.1** **Linear-cocycle infrastructure**: define `A⁽ⁿ⁾`, prove the cocycle
  identity `A⁽ᵐ⁺ⁿ⁾ = A⁽ⁿ⁾∘T^[m]·A⁽ᵐ⁾`, the integrability predicate
  `Integrable (log⁺‖A·‖)`, measurability of `x ↦ A⁽ⁿ⁾(x)` and `x ↦ log‖A⁽ⁿ⁾(x)v‖`.
  *Depends on:* L0.7, L0.8. **[BUILD]**
- **L3.2** **`gₙ = log‖A⁽ⁿ⁾‖` is a subadditive cocycle**: from `l2_opNorm_mul` +
  cocycle identity + monotone `log`. `g₁⁺ = log⁺‖A‖ ∈ L¹` by hypothesis.
  *Depends on:* L2.1, L3.1, L0.7. **[BUILD]**
- **L3.3** **Furstenberg–Kesten, top exponent**: `λ⁺(x) = lim (1/n) log‖A⁽ⁿ⁾(x)‖`
  exists a.e., `T`-invariant, `∫λ⁺ = inf_n (1/n)∫log‖A⁽ⁿ⁾‖`; constant `λ₁` if
  ergodic. *Depends on:* L2.6, L3.2. **[BUILD]**
- **L3.4** **Furstenberg–Kesten, bottom exponent**: same with the conorm
  `−log m(A⁽ⁿ⁾) = log‖A⁽ⁿ⁾⁻¹‖` (superadditive ⇒ apply Kingman to its negative),
  using `log⁺‖A⁻¹‖ ∈ L¹`; gives `λ_k` finite a.e. and `λ_k ≤ λ⁺`.
  *Depends on:* L2.6, L3.1, L3.2. **[BUILD]**

### Layer 4 — the limsup spectrum and the limsup flag (one-sided)

- **L4.1** **Finiteness of `λ̄(x,v)`** for all `v ≠ 0`: sandwiched between `λ_k` and
  `λ⁺` via `‖A⁽ⁿ⁾‖⁻¹‖v‖ ≤ ‖A⁽ⁿ⁾v‖ ≤ ‖A⁽ⁿ⁾‖‖v‖`. *Depends on:* L3.3, L3.4. **[BUILD]**
- **L4.2** **`λ̄(x,·)` is a non-Archimedean (ultrametric) growth function**:
  `λ̄(x,cv)=λ̄(x,v)` (`c≠0`), `λ̄(x,v+w) ≤ max`, with `=` when `λ̄(x,v)≠λ̄(x,w)`;
  equivariance `λ̄(x,v) = λ̄(Tx, A(x)v)`. *Depends on:* L4.1. **[BUILD]**
- **L4.3** **Ultrametric linear algebra** (pure, no dynamics): a function with the
  L4.2 axioms takes ≤ `d` distinct finite values, the level sets
  `{v : λ̄ ≤ t}` are subspaces, vectors of distinct values are independent.
  **[BUILD]** (elementary, self-contained linear algebra).
- **L4.4** **The limsup flag** (Bochi Lemma 8 / Zhu Prop 5.2): distinct values
  `λ₁ > ⋯ > λ_k` (`k ≤ d`); `Vⁱₓ = {v : λ̄(x,v) ≤ λᵢ}` is a strictly decreasing,
  `A`-equivariant flag; `λ̄ = λᵢ` exactly on `Vⁱ ∖ V^{i+1}`. *Depends on:* L4.2, L4.3.
  **[BUILD]**
- **L4.5** **Measurability** of `x ↦ k(x)`, `x ↦ λᵢ(x)`, `x ↦ Vⁱₓ` (Zhu Prop 5.10).
  *Depends on:* L4.4, and a **measurable-subspace / measurable-selection** layer.
  **[BUILD]** (heavy; see Risks — needs measurable structure on subspaces).

### Layer 5 — upgrade limsup → genuine lim (the heart, one-sided)

- **L5.1** **Tempering / Birkhoff corollary** (Bochi Lemma 6): if `φ∘T − φ` is
  integrable then `(1/n) φ(Tⁿx) → 0` a.e. *Depends on:* L1.3. **[BUILD]** (short
  corollary of pointwise Birkhoff).
- **L5.2** **Extremes on an invariant subbundle are genuine limits** (Bochi Lemma
  11 / Zhu Lemma 5.11): for a measurable `A`-invariant subbundle `Wₓ`,
  `lim (1/n) log‖A⁽ⁿ⁾|_W‖ = max_{v∈W} λ̄(x,v)` and
  `lim (1/n) log m(A⁽ⁿ⁾|_W) = min_{v∈W} λ̄(x,v)`. Proof: trivialize `W` by a
  measurable orthonormal frame to a sub-cocycle in `GL(l)`, apply Furstenberg–Kesten
  (L3.3/L3.4). *Depends on:* L3.3, L3.4, L4.4, L4.5. **[BUILD]**
- **L5.3** **Tempered block-triangular estimate** (Bochi Lemma 12 / Zhu Fact 5.20):
  in the orthogonal block form `A = [[B,0],[C, A|_W]]` relative to `W`, the
  off-diagonal `C⁽ⁿ⁾` grows no faster than the diagonal blocks (controlled by L5.1).
  *Depends on:* L5.1, L5.2. **[BUILD]**
- **L5.4** **Peel one exponent** (Bochi Lemma 13 / Zhu Lemma 5.19): with the bottom
  subbundle `W = V_k`, the quotient cocycle `B` on `W⊥` has the same limsup spectrum
  on the upper layers, one fewer exponent, and the genuine limit transports back to
  `A`. *Depends on:* L5.2, L5.3. **[BUILD]**
- **L5.5** **Induction ⇒ genuine forward limit on every layer** (Bochi Thm 2 / Zhu
  Prop 5.26): induct on `k` using L5.2 (base, bottom bundle) and L5.4 (step), giving
  `lim (1/n) log‖A⁽ⁿ⁾(x)v‖ = λᵢ` for all `v ∈ Vⁱ ∖ V^{i+1}`, and uniformity over unit
  vectors. *Depends on:* L5.2, L5.4. **[BUILD]**

### Layer 6 — the TARGET: one-sided MET (filtration)

- **L6.1** **One-sided MET** = assemble L4.4 (flag + equivariance), L4.5
  (measurability), L5.5 (genuine limit). *Depends on:* L4.4, L4.5, L5.5. **[BUILD]**
  **This is the recommended target theorem (see target-and-milestones.md).**

### Layer 7 — two-sided splitting (FUTURE; not in the initial target)

- **L7.1** Backward filtration: apply L6.1 to the inverse cocycle of `T⁻¹` (needs
  `T` invertible). **[BUILD]**
- **L7.2** Subexponential angle decay between forward/backward filtration pieces
  (Bochi Addendum 5): from L5.1 applied to `log sin∠(F¹,F²)`. **[BUILD]**
- **L7.3** `Eᵢ = V⁺ⁱ ∩ V⁻^{k+1−i}` is an equivariant complemented splitting with the
  two-sided limit. *Depends on:* L7.1, L7.2. **[BUILD]**

### Dependency summary (bottom → top)

```
[EXISTS substrate L0]
        │
   maximal ineq (L1.1) + condExp∘MP (L1.2)
        └──▶ pointwise Birkhoff (L1.3) ──────────────┐
                    │                                │
        subadditive cocycle (L2.1–2.5)               │ (tempering L5.1)
                    └──▶ KINGMAN (L2.6) ──▶ Furstenberg–Kesten top/bottom (L3.3/3.4)
                                                       │
                            limsup spectrum + limsup flag (L4.1–4.5)
                                                       │
                            limsup→lim: extremes(L5.2)+temper(L5.3)+peel(L5.4)+induct(L5.5)
                                                       │
                            ONE-SIDED MET — filtration (L6.1)  ◀── TARGET
                                                       │
                            inverse cocycle + angles + intersect (L7.x) ──▶ splitting (future)
```

---

## 4. What we reuse vs. build (one-line summary)

- **Reuse wholesale:** the measure-preserving/ergodic substrate, conditional
  expectation, invariant σ-algebra, Birkhoff-sum algebra, Fekete, `posLog`, matrix
  L2 operator norm, `GL`/`det`, singular values, spectral theorem, `CFC.sqrt`,
  functorial exterior powers, the `Flag` order type. (Layer 0.)
- **Build, in order:** maximal ergodic inequality + `condExp∘MP` ⇒ **pointwise
  Birkhoff** (L1) ⇒ subadditive-cocycle machinery ⇒ **Kingman** (L2) ⇒
  **Furstenberg–Kesten** (L3) ⇒ limsup spectrum/flag (L4) ⇒ limsup→lim
  induction (L5) ⇒ **one-sided MET** (L6); later the **two-sided splitting** (L7).

The two genuinely large, novel sub-projects are **pointwise Birkhoff** (L1) and
**Kingman** (L2); they are the early milestones precisely because everything else
depends on them. The most error-prone analytic piece is the Kingman greedy-covering
bound (L2.5); the most infrastructure-heavy is the measurable-subspace layer (L4.5).
