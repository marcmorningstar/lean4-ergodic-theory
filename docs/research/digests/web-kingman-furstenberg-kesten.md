# Digest — Kingman's Subadditive Ergodic Theorem & the Furstenberg–Kesten Theorem

**Source cluster:** `kingman-furstenberg-kesten`
**Role in the project:** These two theorems are *the* key dynamical dependencies
for the Oseledets multiplicative ergodic theorem (MET). Kingman is the analytic
engine; Furstenberg–Kesten (F–K) is its first matrix-product application (the top
and bottom Lyapunov exponents); the full Oseledets splitting/filtration is the
refinement that resolves *all* exponents and their subspaces.

Logical chain (Viana, *Lectures on Lyapunov Exponents*, Ch. 3–4):
**Birkhoff ⟹ Kingman ⟹ Furstenberg–Kesten ⟹ Oseledets MET.**

---

## Primary sources scraped

| File | What it gives |
|---|---|
| `sources/wikipedia-kingman-subadditive-ergodic-theorem.md` | Exact Kingman statement (function form + equivalent process form); **full Steele (1989) proof transcribed** with all six steps; applications (Birkhoff, Fekete, LIS). |
| `sources/steele-1989-kingman-proof.md` | Steele, *Kingman's subadditive ergodic theorem*, Ann. IHP B **25**(1) 1989, 93–98. The canonical short proof (no maximal inequality, no Riesz lemma). OCR slightly garbled but structurally complete. |
| `sources/planetmath-furstenberg-kesten-theorem.md` | Clean, precise F–K statement: one-sided λ_max (needs `log⁺‖A‖ ∈ L¹`), two-sided λ_min (needs `log⁺‖A⁻¹‖ ∈ L¹`); both `= lim = inf/sup`; both `f`-invariant; "direct consequence of Kingman" via subadditivity of `log‖φₙ‖`. |
| `sources/viana-impa-lle-furstenberg-kesten.md` | Viana's book: ToC/preface/Ch.1. Dimension-2 F–K statement (Thm 1.1), `λ⁺ ≥ λ⁻`, the explicit Ch.3 proof outline (subadditive thm → F–K → Herman → Oseledets dim 2), index entries pinning "Oseledets flag" vs "Oseledets decomposition". |
| `sources/wikipedia-oseledets-theorem.md` (sibling-agent scrape, cross-read) | The **filtration form** `ℝⁿ = R₁ ⊃ … ⊃ R_m ⊃ R_{m+1}={0}` of MET and the L¹-integrability of both `log‖C‖` and `log‖C⁻¹‖`. |

*Note:* the Wikipedia article *Furstenberg–Kesten theorem* does **not exist**
(redlink); PlanetMath + Viana were used instead. The Steele PDF (via Wayback)
scraped as one long line — content is all there, just newline-free.

---

## 1. Kingman's Subadditive Ergodic Theorem

### 1.1 Setup and exact statement (function form)

Let `T` be a **measure-preserving transformation** of a probability space
`(Ω, Σ, μ)` (i.e. `μ(T⁻¹A) = μ(A)` for all `A ∈ Σ`). Let `{gₙ}_{n∈ℕ}`,
`n ≥ 1`, be a sequence of **`L¹(μ)` (integrable) real functions** satisfying the
**subadditivity relation**

> **(S)** &nbsp;&nbsp; `g_{n+m}(x) ≤ gₙ(x) + g_m(Tⁿ x)` &nbsp; for all `n, m ≥ 1`, a.e. `x`.

**Conclusion.** The limit

> `g(x) := lim_{n→∞} gₙ(x)/n`

exists for `μ`-a.e. `x`, with values in `[−∞, +∞)` (i.e. `g(x) ≥ −∞`, possibly
`−∞`, never `+∞`), and the limit function `g` is **`T`-invariant** (`g∘T = g`
a.e.).

In particular:
- If `T` is **ergodic**, then `g` is `μ`-a.e. **constant**, equal to
  `inf_{n≥1} (1/n) ∫ gₙ dμ = lim_{n→∞} (1/n) ∫ gₙ dμ`.
- (General invariant version) `g(x) = inf_n E[gₙ | I](x)/n` where `I` is the
  invariant σ-field; convergence is also **in `L¹`** provided
  `inf_n (1/n) ∫ gₙ dμ > −∞` (the standard integrability proviso — see §1.5).

> ⚠️ **Direction/sign convention.** The relation **(S)** above is the
> *subadditive* convention used by Wikipedia/Steele (`g_{n+m} ≤ gₙ + g_m∘Tⁿ`),
> and matches the matrix application `gₙ = log‖φₙ‖` directly. Some sources state
> a *superadditive* version with the inequality reversed (e.g. the
> longest-increasing-subsequence example uses `M*_{k+m} ≥ M*_k + M*_m∘T^k`);
> they are dual via `g ↦ −g`. **For F–K / Oseledets we use the subadditive form
> exactly as in (S).**

The quantity `lim ∫gₙ/n = inf_n ∫gₙ/n` is itself an instance of **Fekete's
subadditive lemma** applied to the deterministic sequence `aₙ := ∫ gₙ dμ`
(subadditive since integrating (S) and using `T`-invariance of `μ` gives
`a_{n+m} ≤ aₙ + a_m`). Kingman is the "random-variable version of Fekete."

### 1.2 Equivalent statement (subadditive *process* form)

A family of real random variables `X(m,n)` for `0 ≤ m < n ∈ ℕ` is a
**subadditive process** if

> `X(m+1, n+1) = X(m,n) ∘ T` &nbsp; (stationarity / cocycle covariance), and
> `X(0,n) ≤ X(0,m) + X(m,n)` &nbsp; (subadditivity).

Then there is a `T`-invariant `Y ∈ [−∞, +∞)` with `lim_n (1/n) X(0,n) = Y` a.s.

**Dictionary between the two forms** (so a Lean formalization can pick one):
- `gₙ := X(0,n)` for `n ≥ 1`;
- `X(m, m+n) := gₙ ∘ Tᵐ` for `m ≥ 0`.

### 1.3 Degenerate / boundary cases worth noting for formalization
- `gₙ := Σ_{j=0}^{n-1} f∘Tʲ` (i.e. additive, equality in (S)) ⟹ recovers
  **Birkhoff's pointwise ergodic theorem**.
- `gₙ ≡ cₙ` constant functions ⟹ recovers **Fekete's subadditive lemma**.
- These two are the natural sanity-check special cases / unit tests.

### 1.4 Steele's proof — full skeleton (the route to formalize)

Steele (1989) is the standard "simplest" proof: it uses **only Birkhoff's
pointwise ergodic theorem** plus elementary partition/covering combinatorics; it
deliberately avoids any maximal inequality or the combinatorial Riesz lemma.
Below is the ordered skeleton, with the lemma each step needs and what it
depends on. (Steele's own numbering merged with the Wikipedia §-headings, which
transcribe the same proof.)

**Step 0 — Subadditivity by partition (combinatorial core).**
From (S), iterating: for any partition of the integer block `{0, …, n−1}` into
consecutive intervals `{kᵢ, …, kᵢ+ℓᵢ−1}`,
> `gₙ(x) ≤ Σᵢ g_{ℓᵢ}(T^{kᵢ} x).`
*Needs:* just (S) and induction. *Depends on:* nothing external. This is the
combinatorial backbone reused in Steps 4–6.

**Step 1 — Reduce to `gₙ ≤ 0` (negative process).**
Define `f̃ₙ := gₙ − Σ_{j=0}^{n-1} g₁∘Tʲ`. By the singleton partition,
`gₙ ≤ Σ_{j=0}^{n-1} g₁∘Tʲ`, so `f̃ₙ ≤ 0`, and `f̃ₙ` is still subadditive.
By **Birkhoff** the average `(1/n)Σ_{j<n} g₁∘Tʲ` converges a.e. (and in `L¹`)
to a `T`-invariant function; hence `gₙ/n` converges iff `f̃ₙ/n` does, with the
same invariant target shifted by the Birkhoff limit. So **WLOG `gₙ(x) ≤ 0`.**
*Needs:* Birkhoff pointwise (+ `L¹`) ergodic theorem; `g₁ ∈ L¹`.
*Depends on:* Birkhoff. **(This is the single hard external dependency.)**

**Step 2 — `g := liminf gₙ/n` is `T`-invariant.**
From `g_{n+1} ≤ g₁ + gₙ∘T` divide by `n+1`, take `liminf`: get `g ≤ g∘T`.
Since `T` preserves `μ`, for each `c∈ℝ` the sets `{g ≥ c}` and
`T⁻¹{g ≥ c} = {g∘T ≥ c}` satisfy `{g≥c} ⊂ {g∘T≥c}` with equal measure, so they
agree a.e.; ranging over rational `c` gives `g∘T = g` a.e.
*Needs:* measure-preservation; "subset of equal finite measure ⟹ a.e. equal";
countable (rational) exhaustion. *Depends on:* nothing beyond measure theory.

**Step 3 — Truncation `g' := max(g, −M)`.**
`g'` is `T`-invariant, bounded below, integrable. It suffices to prove, for
every `ε>0` and `M>0`, the a.e. **upper bound**
> `limsup gₙ/n ≤ g' + ε`,
because letting `ε↓0` then `M→∞` yields `limsup gₙ/n ≤ liminf gₙ/n =: g`, and
squeezing gives the a.e. limit. (`liminf ≤ limsup` is automatic.)
*Needs:* monotone limits over `ε`, `M`. *Depends on:* Step 2.

**Step 4 — Fundamental lemma / the covering algorithm ("bounding the truncation").**
Fix `ε, M>0`. For `L = 1,2,…` set
> `B_L := { x : g_ℓ(x)/ℓ > g'(x)+ε for all ℓ ∈ {1,…,L} }`,
> `A_L := B_Lᶜ = { x : ∃ ℓ ≤ L, g_ℓ(x)/ℓ ≤ g'(x)+ε }`.
Since `g' ≥ g = liminf gₙ/n`, the `B_L` **shrink to a null set** as `L→∞`.
Fix `x`, `L`, and `n > L`. Greedily partition `{0,…,n−1}`: at the least
unused `k`, if `T^k x ∈ A_L` pick `ℓ ≤ L` with `g_ℓ(T^k x) ≤ ℓ(g'(x)+ε)` and
cut the interval `{k,…,k+ℓ−1}` ("type 1") when it fits (`k+ℓ−1 ≤ n−1`);
otherwise cut the singleton `{k}` ("type 2", forced near the right end, at most
`L−1` of them); if `T^k x ∈ B_L`, cut singleton `{k}` ("type 3").
Apply Step 0 + `gₙ ≤ 0` to drop type-2/3 terms:
> `gₙ(x) ≤ Σ_{type 1} g_{ℓᵢ}(T^{kᵢ}x) ≤ (g'(x)+ε) · Σ_{type 1} ℓᵢ`,
and **lower-bound the covered length**:
> `(1/n) Σ_{type 1} ℓᵢ ≥ 1 − (L−1)/n − (1/n) Σ_{k<n} 1_{B_L}(T^k x)`.
(The `(L−1)/n` accounts for type-2 singletons; the indicator sum counts type-3.)
*Needs:* Step 0 (partition inequality), `gₙ ≤ 0`, the greedy-partition counting
argument. *Depends on:* Steps 1, 3. **This counting argument is the most
intricate part to formalize.**

**Step 5 — Peel off `n` (apply Birkhoff to the bad-set indicator).**
Let `n→∞`. By **Birkhoff**, `(1/n) Σ_{k<n} 1_{B_L}(T^k x) → 1̄_{B_L}(x)` a.e.,
with `0 ≤ 1̄_{B_L} ≤ 1` and `∫ 1̄_{B_L} = μ(B_L)`. Hence a.e.
> `limsup gₙ/n ≤ g'(x)·(1 − 1̄_{B_L}(x)) + ε`
(using `g' ≤ 0` here, so the sign bookkeeping flips as in the source).
*Needs:* Birkhoff again, for the indicator `1_{B_L}`. *Depends on:* Step 4.

**Step 6 — Peel off `L` (Markov-type argument).**
As `L→∞`: `1_{B_L}` decreases to a null set, so `μ(B_L) = ∫ 1̄_{B_L} → 0`, and
`1̄_{B_L}` is monotone decreasing. A Markov-inequality-style argument gives a.e.
> `limsup gₙ/n ≤ g'(x) + ε`,
the bound required by Step 3. Letting `ε↓0`, `M→∞` finishes.
*Needs:* monotone convergence / Markov inequality; `μ(B_L)→0`.
*Depends on:* Steps 3, 5.

**Net dependency summary for Kingman:** the *only* nontrivial external input is
**Birkhoff's pointwise ergodic theorem** (used twice: Step 1 and Step 5), plus
standard `μ`-measure-theory (a.e. equality of equal-measure nested sets,
monotone/dominated convergence, Fekete on `∫gₙ`). Everything else is elementary
partition combinatorics.

### 1.5 The `L¹` / integrability fine print
- Hypothesis: each `gₙ ∈ L¹`. (Equivalently in the matrix application below, the
  one-step `log⁺` integrability — see §2.)
- The limit `g` can be `−∞` on a positive-measure set *unless* one assumes
  `inf_n (1/n)∫gₙ dμ > −∞`; that proviso is exactly what upgrades a.e.
  convergence to **`L¹` convergence** and keeps the Lyapunov exponent finite.
- `g₁ ∈ L¹` is what powers the Birkhoff reduction in Step 1; without it the
  reduction-to-negative trick breaks.

---

## 2. The Furstenberg–Kesten Theorem

F–K = Kingman applied to `gₙ = log‖φₙ‖`. It is the d-dimensional strong law of
large numbers for the norm of a product of (random / cocycle) matrices. Original:
H. Furstenberg & H. Kesten, *Products of random matrices*, Ann. Math. Statist.
**31** (1960), 457–469.

### 2.1 Setup (cocycle form, PlanetMath / Viana Ch. 3)

- `(M, μ)` probability space, `f : M → M` measure-preserving.
- `A : M → GL(d, ℝ)` measurable (the **generator**). [One-sided/non-invertible
  variant: `A : M → ` matrices, not necessarily invertible — F–K still holds for
  `λ_max`.]
- The **multiplicative (linear) cocycle**
  > `φⁿ(x) := A(fⁿ⁻¹x) · A(fⁿ⁻²x) ⋯ A(fx) · A(x)`, &nbsp; `φ⁰(x) = Id`,
  satisfying the **cocycle identity** `φ^{n+m}(x) = φⁿ(fᵐ x) · φᵐ(x)`.
  (In the i.i.d. random-matrix picture: `Lₙ = L_{n−1}⋯L₁L₀`, `Lⱼ` i.i.d., and
  `f` is the Bernoulli shift.)

### 2.2 Integrability hypothesis (the crucial condition — quote it exactly)

> `log⁺‖A‖ ∈ L¹(μ)`, &nbsp; where &nbsp; `log⁺‖A‖ := max{ log‖A‖, 0 }`.

For the lower exponent / two-sided statement additionally:

> `log⁺‖A⁻¹‖ ∈ L¹(μ)`.

(Equivalently for Oseledets: both `log‖A‖` and `log‖A⁻¹‖` integrable.) Only the
**positive part** need be integrable for `λ_max` to exist in `[−∞, +∞)`; the
matrix norm `‖·‖` is any operator norm (all equivalent in finite dim).

### 2.3 Statement — top (maximal) exponent [one-sided, semigroup, `A : X→` matrices]

If `log⁺‖A‖ ∈ L¹(μ)`, then for `μ`-a.e. `x` the limit

> `λ_max(x) := lim_{n→∞} (1/n) log‖φⁿ(x)‖`

**exists** in `[−∞, +∞)`, is **`f`-invariant** (`λ_max∘f = λ_max`), `λ_max⁺` is
integrable, and

> `∫ λ_max dμ = lim_{n→∞} (1/n) ∫ log‖φⁿ‖ dμ = inf_{n≥1} (1/n) ∫ log‖φⁿ‖ dμ`.

If `f` (more precisely the system) is **ergodic**, `λ_max` is a.e. a constant
`λ₁` (the **top Lyapunov exponent**). This is the precise reading of the slogan
`(1/n) log‖Aⁿ‖ → λ₁` a.e.

**Why it follows from Kingman:** `gₙ(x) := log‖φⁿ(x)‖` is **subadditive**:
submultiplicativity of the operator norm + the cocycle identity give
`‖φ^{n+m}(x)‖ ≤ ‖φⁿ(fᵐx)‖·‖φᵐ(x)‖`, hence
`g_{n+m}(x) ≤ gₘ(x) + gₙ(fᵐx)` (relation (S)). Integrability of `g₁ = log‖A‖⁺`
(plus the easy lower bound) puts `gₙ ∈ L¹`. Apply Kingman. ∎
*(This single submultiplicativity inequality is the entire "new" content; the
analytic heavy lifting is all inside Kingman → Birkhoff.)*

### 2.4 Statement — bottom (minimal) exponent [two-sided / invertible]

If additionally `log⁺‖A⁻¹‖ ∈ L¹(μ)` (so `A` is `GL(d,ℝ)`-valued and `f`
invertible), then for `μ`-a.e. `x`

> `λ_min(x) := lim_{n→∞} −(1/n) log‖φ⁻ⁿ(x)‖ = lim_{n→∞} (1/n) log‖φⁿ(x)⁻¹‖⁻¹`

exists, is `f`-invariant, `λ_min⁺` integrable, and

> `∫ λ_min dμ = lim_n (1/n) ∫ log‖φ⁻ⁿ‖ dμ = sup_n (1/n) ∫ log‖φ⁻ⁿ‖ dμ`
> &nbsp;(equivalently, via the *conorm* `‖B⁻¹‖⁻¹`, `lim (1/n) log‖Lₙ⁻¹‖⁻¹ = λ⁻`).

**Always** `λ_min ≤ λ_max` (since `‖B‖ ≥ ‖B⁻¹‖⁻¹`). If `|det Aᵢ| = 1` for all
`i` then `λ_min ≤ 0 ≤ λ_max` (Viana §1.1, Thm 1.1; `λ⁺ + λ⁻ = 0` in dim 2 when
det = ±1, Exercise 1.1). `λ_max` and `λ_min` are the **extremal Lyapunov
exponents**.

### 2.5 What F–K does *not* give (motivates Oseledets)
F–K resolves only the **two extremal** exponents `λ_max, λ_min` and gives **no
subspaces**. It also does **not** control individual matrix entries
`(1/n)log|φⁿ_{i,j}|` in general (Viana Exercise 1.3 / Furstenberg–Kesten:
entrywise convergence holds only if all entries of every `Aᵢ` are strictly
positive). The full spectrum and the invariant subspaces are the job of
Oseledets.

---

## 3. From F–K to the Oseledets MET (the two structural forms)

The MET refines F–K by resolving *all* `m ≤ d` distinct exponents and attaching
geometry. Two inequivalent geometric forms — **the splitting requires
invertibility, the filtration does not.** This distinction is central for the
formalization.

### 3.1 Filtration / flag form (one-sided; needs only `A : X →` matrices, `log⁺‖A‖∈L¹`)

(Oseledets Wikipedia; Viana §3.4.1, §4.2 "constructing the Oseledets flag".)
There exist distinct values `λ₁ > λ₂ > … > λ_m` (the Lyapunov exponents) and an
`x`-dependent **decreasing filtration of subspaces**

> `ℝᵈ = V₁(x) ⊋ V₂(x) ⊋ … ⊋ V_m(x) ⊋ V_{m+1}(x) = {0}`

such that for every `u ∈ V_i(x) \ V_{i+1}(x)`,

> `lim_{n→∞} (1/n) log‖φⁿ(x) u‖ = λ_i`.

**Equivariance (covariance):** `φⁿ(x)·V_i(x) ⊆ V_i(fⁿ x)` — the cocycle maps the
filtration at `x` into the filtration at `fⁿx` (for invertible cocycles,
equality). The dimensions `dᵢ = dim V_i − dim V_{i+1}` are the **multiplicities**
of `λᵢ`, with `Σ dᵢ·... ` and `Σ (per-vector exponents) = lim (1/n) log|det φⁿ|`.
This is the form that drops out directly from Kingman/F–K applied to `φⁿ` and to
exterior powers `Λ^k φⁿ` (Herman's formula, Viana §3.3) — **no inverse needed.**

### 3.2 Direct-sum (Oseledets) splitting form (two-sided; needs invertibility)

(PlanetMath "Oseledet's decomposition"; Viana §4.3 "upgrading to a
decomposition"; index "Oseledets decomposition".)
If `f` is invertible **and** both `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹`, the filtration
splits into an `x`-dependent **direct sum (Oseledets splitting)**

> `ℝᵈ = E₁(x) ⊕ E₂(x) ⊕ … ⊕ E_m(x)`,

with `V_i(x) = E_i(x) ⊕ E_{i+1}(x) ⊕ … ⊕ E_m(x)`, each `E_i(x)` of dimension
`dᵢ`, such that **for every nonzero `u ∈ E_i(x)`** (two-sided limit)

> `lim_{n→±∞} (1/n) log‖φⁿ(x) u‖ = λ_i`.

**Equivariance:** `φ(x)·E_i(x) = E_i(fx)` (genuine equality — the splitting is
`φ`-invariant). Obtaining the `Eᵢ` from the flags requires intersecting the
forward flag `V_i⁺` with a backward flag `V_i⁻` built from `φ⁻ⁿ`; this is
**exactly where invertibility (`A⁻¹`, the `log⁺‖A⁻¹‖` hypothesis) enters**, via
"subexponential decay of angles" (Viana §4.3.2). Without invertibility you get
only the filtration of §3.1, not the splitting.

> **One-line takeaway for the plan:** filtration/flag ⇐ one-sided + `log⁺‖A‖∈L¹`;
> direct-sum splitting ⇐ two-sided/invertible + also `log⁺‖A⁻¹‖∈L¹`.

---

## 4. What a Lean 4 + Mathlib proof of Kingman would require

**Target statement (Mathlib-flavored).** Given
`{Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]`,
`(T : Ω → Ω)` with `MeasurePreserving T μ μ`, a sequence `g : ℕ → Ω → ℝ` with
`∀ n, Integrable (g n) μ` and the subadditivity
`g (n+m) x ≤ g n x + g m (T^[n] x)` (a.e.), conclude:
`∀ᵐ x ∂μ, Tendsto (fun n => g n x / n) atTop (𝓝 (G x))` for some `T`-invariant
`G : Ω → ℝ` (valued in `EReal`/allowing `−∞`), with the ergodic/`inf E[gₙ]/n`
identification.

### 4.1 Mathlib pieces available (the foundation is largely there)
- **Birkhoff pointwise ergodic theorem** — `MeasureTheory.Ergodic` /
  `Mathlib.Dynamics.BirkhoffSum.*`; `birkhoffAverage`, and the a.e. convergence
  of Birkhoff averages (the *one* nontrivial external dependency for Kingman). ✅
  *Verify the exact name/strength of the pointwise + `L¹` convergence lemma in
  the pinned Mathlib; this is the load-bearing import.*
- `MeasurePreserving`, `MeasureTheory.Measure`, `Integrable`, `Filter.Tendsto`,
  `liminf`/`limsup` on `EReal`, monotone & dominated convergence — all present.
- a.e.-equality of nested sets of equal finite measure (Step 2) — derivable from
  `measure_diff`/`MeasureTheory.ae_eq` lemmas.
- **Fekete's subadditive lemma** for the deterministic `aₙ = ∫gₙ` — check
  `Mathlib` (`Subadditive`/`Filter.Tendsto` div-`n` lemmas exist for real
  subadditive sequences, e.g. `Subadditive.tendsto_lim`). ✅ likely reusable.

### 4.2 What must be built (no off-the-shelf Mathlib lemma)
1. **The partition/covering inequality (Step 0)** — a clean lemma
   `g n x ≤ ∑ over a consecutive-interval partition, g ℓᵢ (T^[kᵢ] x)`. Needs a
   tidy combinatorial encoding of "partition of `Finset.range n` into consecutive
   blocks" + induction on (S). Moderate.
2. **The greedy covering algorithm (Step 4)** — the genuinely intricate part:
   define `A_L, B_L`; the greedy block-selection; the length lower bound
   `(1/n)Σ_{type1} ℓᵢ ≥ 1 − (L−1)/n − (1/n)Σ 1_{B_L}∘T^k`. This is fiddly
   index-bookkeeping; expect this to dominate the effort.
3. **Two Birkhoff applications** glued to (2): once to reduce to `gₙ ≤ 0`
   (Step 1), once on `1_{B_L}` (Step 5).
4. **EReal handling**: the limit may be `−∞`; either work in `EReal` throughout
   or carry the `inf_n ∫gₙ/n > −∞` proviso to stay in `ℝ`. Decide early — it
   affects every statement.
5. **`T`-invariance of the limit (Step 2)** and the final squeeze (Steps 3,6).

### 4.3 Then F–K is short
Once Kingman is in place, **Furstenberg–Kesten is genuinely easy**: define
`gₙ x = log‖φⁿ x‖`, prove subadditivity from
`norm_mul_le`/submultiplicativity + the cocycle identity, prove `g₁ ∈ L¹` from
`log⁺‖A‖ ∈ L¹` (plus a lower `L¹` bound, e.g. via `log‖A⁻¹‖` or
`log‖φⁿ‖ ≥ −n·something`), and invoke Kingman. The two-sided `λ_min` is the same
with `φ⁻ⁿ` and the `log⁺‖A⁻¹‖` hypothesis. Mathlib needs: matrix operator norm
submultiplicativity (`Matrix`/`ContinuousLinearMap` `opNorm` — present), `Real.log`
+ `log⁺` lemmas, and the cocycle `BirkhoffSum`-style product (likely build a small
`cocycle` def).

### 4.4 Easy vs. hard (summary)
- **Easy to formalize:** statement plumbing; Fekete on `∫gₙ`; the F–K reduction
  *given Kingman*; the Birkhoff/Fekete special-case sanity checks.
- **Hard to formalize:** Step 4 greedy-covering length bound (combinatorial
  index juggling); `EReal`/`−∞` bookkeeping consistency; pinning the exact
  Mathlib Birkhoff a.e.+`L¹` lemma and matching hypotheses.
- **External Mathlib dependency that gates everything:** the **pointwise (and
  `L¹`) Birkhoff ergodic theorem**. If its current form in the pinned Mathlib is
  weaker than needed, that becomes prerequisite work.
- **Invertibility watch:** the *filtration* form of Oseledets is reachable from
  the one-sided Kingman/F–K; the *direct-sum splitting* form additionally needs
  `log⁺‖A⁻¹‖∈L¹` and the backward cocycle. Keep the two hypothesis-sets separate
  in the Lean API from the start.

---

## 5. Exact definitions quoted (for fidelity)

- **Subadditivity (Wikipedia/Steele):**
  `g_{n+m}(x) ≤ g_n(x) + g_m(Tⁿ x)`.
- **Subadditive process (Wikipedia):**
  `X(m+1,n+1) = X(m,n)∘T` and `X(0,n) ≤ X(0,m) + X(m,n)`.
- **Kingman conclusion (Wikipedia):**
  `lim_{n→∞} gₙ(x)/n =: g(x) ≥ −∞` for μ-a.e. x, `g` `T`-invariant; constant if
  ergodic, then `= inf_n E[gₙ]/n`.
- **`log⁺` (PlanetMath):** `log⁺‖A‖ = max{ log‖A‖, 0 }`.
- **F–K top (PlanetMath):** `λ_max(x) = lim_n (1/n) log‖φⁿ(x)‖`; exists a.e.;
  `∫λ_max dμ = lim_n (1/n)∫log‖φⁿ‖dμ = inf_n (1/n)∫log‖φⁿ‖dμ`.
- **F–K bottom (PlanetMath):** `λ_min(x) = lim_n −(1/n) log‖φ⁻ⁿ(x)‖`;
  `∫λ_min dμ = sup_n (1/n)∫log‖φ⁻ⁿ‖dμ`; needs `log⁺‖A⁻¹‖∈L¹`.
- **Both `f`-invariant (PlanetMath):** `λ_min∘f = λ_min`, `λ_max∘f = λ_max` a.e.
- **Oseledets filtration (Wikipedia):**
  `ℝⁿ = R₁ ⊃ … ⊃ R_m ⊃ R_{m+1} = {0}`, limit `= λ_i` on `R_i \ R_{i+1}`.

## 6. Citations
- J. Michael Steele, *Kingman's subadditive ergodic theorem*, Ann. Inst. Henri
  Poincaré (B) **25**(1), 1989, 93–98.
- J. F. C. Kingman, *The ergodic theory of subadditive stochastic processes*,
  J. Roy. Statist. Soc. B **30**, 1968, 499–510; *Subadditive ergodic theory*,
  Ann. Probab. **1**, 1973, 883–909.
- H. Furstenberg & H. Kesten, *Products of random matrices*, Ann. Math. Statist.
  **31**, 1960, 457–469.
- M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Univ. Press (Ch. 3–4).
- V. I. Oseledets, *A multiplicative ergodic theorem…*, Trans. Moscow Math. Soc.
  **19**, 1968, 197–231.
- Wikipedia: *Kingman's subadditive ergodic theorem*; *Oseledets theorem*.
- PlanetMath: *Furstenberg–Kesten theorem*.
- S. Lalley, Kingman lecture notes; Pitman, *Subadditive ergodic theory* (Lec.12)
  — alternate proof references cited by Wikipedia.
