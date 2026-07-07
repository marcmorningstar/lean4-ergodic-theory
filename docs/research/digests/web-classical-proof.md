# Digest — Classical proof of the Oseledets Multiplicative Ergodic Theorem (MET)

**Source cluster:** `classical-proof`
**Focus:** the classical proof of the MET for `d×d` linear cocycles via Kingman's
subadditive ergodic theorem + Furstenberg–Kesten, including (a) the
inductive/dimension-peeling route building the flag, and (b) the
Ruelle exterior-power / singular-value route producing Oseledets' original limit
`(A_n^* A_n)^{1/2n}`. We carefully separate the **one-sided (semigroup,
`A: M → GL_d`)** version giving a **filtration/flag** from the **two-sided
(invertible)** version giving a **direct-sum splitting**.

## Sources scraped (raw markdown saved under `docs/research/sources/`)

| File | Author / origin | Route it documents |
|---|---|---|
| `zhu-uchicago-reu2023-met.md` | **A. Zhu**, UChicago REU 2023 (after Viana, Walters, Bochi) | Full rigorous proof: Kingman → Furstenberg–Kesten → limsup flag → induction on dimension. **Primary source.** |
| `macpherson-bristol-oseledets.md` | **M. Artigiani**, 2013 (Bristol ADS notes) | Statement of one-sided (flag) and two-sided (splitting) versions; full 2D proof via most-contracted/expanded singular vectors; `E_1(x,T)=E_2(x,T^{-1})` trick; singular-value computation. |
| `kelliher-ucr-geometry-lecturenotes.md` | **J. Kelliher**, after **Ruelle (1979)** | Exterior-power route: Kingman + Furstenberg–Kesten on `T^{∧q}` ⟹ existence of `Λ_x = lim (A_n^*A_n)^{1/2n}`; eigenspaces of `Λ_x` give the filtration. |

(The `sources/` directory also contains pre-existing scrapes — Filip 2017, Wikipedia
entries, Scholarpedia, PSU/Amit notes — not part of this cluster's three target URLs.)

---

## 0. Common setup and notation

- `(M, B, μ)` a probability space (Zhu: complete separable); `f: M → M` a
  **measure-preserving transformation**, i.e. `μ(f^{-1}(B)) = μ(B)` for all
  `B ∈ B`. The quadruple `(M, B, μ, f)` is a **dynamical system**.
- `A: M → GL(d, ℝ)` measurable (the **generator**). The **linear cocycle**
  defined by `A` over `f` is `F: M × ℝ^d → M × ℝ^d`, `F(x,v) = (f(x), A(x)v)`.
- Iterates: `F^n(x,v) = (f^n(x), A_n(x) v)` where the **cocycle matrix product** is
  ```
  A_n(x) = A(f^{n-1}(x)) · A(f^{n-2}(x)) ··· A(f(x)) · A(x).
  ```
  (Note the order: newest factor on the left.) Cocycle identity:
  `A_{m+n}(x) = A_n(f^m(x)) · A_m(x)`.
- If `f` is invertible: `A_{-n}(x) = A_n(f^{-n}(x))^{-1}`.
- Operator/spectral norm `‖A‖ := sup_{|v|=1} |Av|`; it is submultiplicative
  `‖AB‖ ≤ ‖A‖‖B‖`, and `‖A‖ = σ_1(A)` = largest singular value.
- `log^+ t := max{log t, 0}`.

### The integrability hypothesis (exact form — load-bearing)

**One-sided / general `GL_d` (Zhu Thm 1.8, 5.1):**
> `log^+ ‖A^{±1}‖` are integrable w.r.t. `μ`, i.e. both
> `∫_M log^+ ‖A(x)‖ dμ < ∞` and `∫_M log^+ ‖A(x)^{-1}‖ dμ < ∞`.

This is the hypothesis Zhu uses throughout (both `+` and `-` directions, even in
the one-sided version, because she works in `GL_d` and needs `λ^-` to be finite).

**Furstenberg–Kesten (the minimal hypothesis for the top exponent):**
- Zhu Thm 4.2 / Artigiani Thm 2: `log^+ ‖A^{±}‖ ∈ L^1(μ)` gives both `λ^+` and `λ^-`.
- Ruelle/Kelliher Cor 3.2 (Furstenberg–Kesten, real `m×m` matrices, not nec.
  invertible): only **`log^+ ‖T(·)‖ ∈ L^1(M,ρ)`** is needed to get the top
  exponent `χ(x) = lim (1/n) log ‖T_x^n‖` (may be `−∞`).

**Ruelle/Kelliher MET (Thm 2.1, discrete time):** `T: M → {real m×m matrices}`
measurable with **`log^+ ‖T(·)‖ ∈ L^1(M,ρ)`** (one-sided only; `T` need not be
invertible — `λ^{(1)}` may be `−∞`). `τ: M → M` measure-preserving.

> **Version distinction on hypotheses:** the *flag/filtration* (one-sided) version
> only needs `log^+ ‖A‖ ∈ L^1` (Ruelle). Working in `GL_d` and/or wanting the
> bottom exponent finite needs `log^+ ‖A^{-1}‖ ∈ L^1` too. The *splitting*
> (two-sided) version needs `f` invertible **and** `log^+ ‖A^{±1}‖ ∈ L^1`.

---

## 1. Theorem statements and all version distinctions

### 1A. One-sided MET — flag / filtration form (Zhu Thm 5.1 = Thm 1.8)

> Suppose `log^+ ‖A^{±1}‖` are integrable w.r.t. `μ`. Then for **μ-a.e.** `x ∈ M`
> there exist `k = k(x) ∈ ℕ`, reals `λ_1(x) > λ_2(x) > ··· > λ_k(x)`, and a
> **flag** (strictly decreasing chain of subspaces)
> ```
> ℝ^d = V_x^1 ⊋ V_x^2 ⊋ ··· ⊋ V_x^k ⊋ {0}
> ```
> such that for all `1 ≤ i ≤ k`:
> - **(a) Invariance/equivariance:** `k(f(x)) = k(x)`, `λ_i(f(x)) = λ_i(x)`, and
>   `A(x) · V_x^i = V_{f(x)}^i`.
> - **(b) Measurability:** `x ↦ k(x)`, `x ↦ λ_i(x)`, `x ↦ V_x^i` are measurable.
> - **(c) Exponential growth:** `lim_{n→∞} (1/n) log |A_n(x) v| = λ_i(x)` for all
>   `v ∈ V_x^i \ V_x^{i+1}` (with `V_x^{k+1} := {0}`).

The `λ_i(x)` are the **Lyapunov exponents**; their multiset (with multiplicities
`dim V_x^i − dim V_x^{i+1}`) is the **Lyapunov spectrum**. `V_x^i` is the
**Oseledets filtration / flag**. The subspace `V_x^i` is exactly
`{ v : lim (1/n) log|A_n(x)v| ≤ λ_i(x) }` (so the flag is intrinsic — the slow
directions). The **top** exponent `λ_1 = λ^+` and the **bottom** `λ_k = λ^-`
(Zhu Remark 5.12).

> **Why only a flag here, not a splitting?** With `f` one-sided you can detect
> "growing slower than `λ_i`" (a closed condition giving nested subspaces) but you
> cannot canonically choose a complement: the directions that grow *exactly* at
> `λ_i` are not well-defined forward in time.

### 1B. Two-sided MET — Oseledets splitting form (Artigiani Thm 3)

> Suppose `f: M → M` is **invertible** and both `log^+ ‖A‖` and `log^+ ‖A^{-1}‖`
> are in `L^1(μ)`. Then for **μ-a.e.** `x`, there exist `λ_1(x) > ··· > λ_{k(x)}(x)`
> and a **direct-sum decomposition (Oseledets splitting)**
> ```
> ℝ^d = E_1(x) ⊕ E_2(x) ⊕ ··· ⊕ E_{k(x)}(x)
> ```
> such that:
> - **(i) Equivariance:** `A(x) E_i(x) = E_i(f(x))`; and the flag is recovered by
>   `L_i(x) = ⊕_{j=i}^{k(x)} E_j(x)` (so `E_i` are the graded pieces of the flag).
> - **(ii) Two-sided exponent:** `lim_{n→±∞} (1/n) log ‖A_n(x) v‖ = λ_i(x)` for
>   all nonzero `v ∈ E_i(x)`. (Note: the limit holds in **both** time directions.)
> - **(iii) Measurability** of `k, λ_i, E_i`.
> - **(iv) Orbit-invariance** of `k, λ_i, E_i`.
> - **(v) Subexponential angle decay:** for disjoint index sets `I ∩ J = ∅`,
>   `lim_{n→±∞} (1/n) log ∠( ⊕_{i∈I} E_i(f^n x), ⊕_{j∈J} E_j(f^n x) ) = 0`
>   (the Oseledets subspaces stay "tempered" — angles don't collapse exponentially).

> **Filtration vs splitting (the central distinction):** invertibility upgrades the
> nested flag `V^1 ⊋ ··· ⊋ V^k` into a *graded* `E_1 ⊕ ··· ⊕ E_k`. Set
> `E_i = V_+^i ∩ V_-^{...}` where `V_±` are the forward/backward filtrations; the
> direct-sum complement to `V^{i+1}` inside `V^i` is supplied by the **backward**
> filtration. The splitting is **NOT available in the one-sided setting.**

### 1C. Ruelle exterior-power form (Kelliher Thm 2.1, discrete time)

> Let `T: M → {real m×m matrices}` measurable, `log^+ ‖T(·)‖ ∈ L^1(M,ρ)`, `τ`
> measure-preserving, `T_x^n = T_{τ^{n-1}(x)} ··· T_{τ(x)} T_x`. Then there is a
> full-measure forward-invariant `Γ ⊆ M` such that for `x ∈ Γ`:
> 1. **`Λ_x := lim_{n→∞} ((T_x^n)^* T_x^n)^{1/2n}` exists** (Oseledets' *original*
>    limit — a positive semidefinite symmetric matrix).
> 2. Let `exp λ_x^{(1)} < ··· < exp λ_x^{(s)}` be the **eigenvalues of `Λ_x`**
>    (`λ_x^{(1)}` may be `−∞`), with eigenspaces `U_x^{(1)}, …, U_x^{(s)}`,
>    `m_x^{(r)} = dim U_x^{(r)}`. The maps `x ↦ λ_x^{(r)}`, `x ↦ m_x^{(r)}` are
>    `τ`-invariant. Set `V_x^{(0)} = {0}`, `V_x^{(r)} = U_x^{(1)} ⊕ ··· ⊕ U_x^{(r)}`
>    (note: here the indexing is **increasing** in exponent, opposite to Zhu).
>    Then for `u ∈ V_x^{(r)} \ V_x^{(r-1)}`:
>    `lim_{n→∞} (1/n) log ‖T_x^n u‖ = λ_x^{(r)}`.
> The `{V^{(r)}}` form a **filtration** `{0} = V^{(0)} ⊆ ··· ⊆ V^{(s)} = ℝ^m`, and
> `V^{(r)} = { u : lim (1/n) log‖T^n_x u‖ ≤ λ^{(r)} }`.
> **Corollary (invertible case):** if `T_x^t` is invertible for all `t,x` then
> `T_x^t V^{(r)}_x = V^{(r)}_{φ(t,x)}` — equivariance of the filtration. **It does
> NOT follow that `T_x^t U^{(r)}_x = U^{(r)}_{φ(t,x)}`** (the eigenspaces of `Λ`
> are not equivariant; only the splitting from the two-sided theorem is).

> **Key conceptual point (Ruelle route):** the eigenspaces `U^{(r)}_x` of the
> *limit* `Λ_x` give a genuine **orthogonal** filtration `V^{(r)}`, but these are
> NOT the equivariant Oseledets subspaces; equivariance only holds for the nested
> `V^{(r)}`. To get the equivariant *splitting* you still need invertibility (run
> the same construction on `T^{-1}` / backward time and intersect).

### 1D. Trivial model (single matrix, motivates everything) — Zhu Thm 3.1

For `B ∈ GL(d)` **normal**, eigenvalues `|ν_1| ≥ ··· ≥ |ν_d|`, orthonormal
eigenvectors `w_i`, `E_i = span{w_i, …, w_d}`: then `ℝ^d = E_1 ⊋ ··· ⊋ E_d ⊋ {0}`
and `lim (1/n) log|B^n w| = log|ν_i|` for `w ∈ E_i \ E_{i+1}`.
Key lemma 3.2: for unit `w ∈ E_i`, `|B^n w| ≤ |ν_i|^n` (via spectral theorem,
`B = PDP^*`). This is the constant-cocycle case `m=1` of the MET.

### 1E. Ergodic case (corollary)

If `f` is **ergodic** (only invariant sets have measure 0 or 1; equivalently every
`f`-invariant measurable `g` is a.e. constant), then `k(x)`, `λ_i(x)`, and
`dim V_x^i` are **constant a.e.** (Zhu Cor 6.3, Artigiani remark, Kelliher remark).
Applies to Bernoulli shifts (i.i.d. random matrix products) and irrational
rotations (quasi-periodic Schrödinger cocycles).

---

## 2. The auxiliary theorems (the engine)

### Kingman's Subadditive Ergodic Theorem (Zhu Thm 4.1, Kelliher Thm 3.1)

> Let `φ_n : M → [−∞, +∞)`, `n ≥ 1`, be **subadditive** relative to `f`:
> `φ_{m+n} ≤ φ_m + φ_n ∘ f^m` for all `m, n ≥ 1`, with `φ_1^+ ∈ L^1(μ)`. Then
> `φ_n / n` converges μ-a.e. to an `f`-invariant `φ: M → [−∞, +∞)`, `φ^+ ∈ L^1`, and
> `∫ φ dμ = lim_n (1/n)∫ φ_n dμ = inf_n (1/n)∫ φ_n dμ ∈ [−∞, +∞)`.

**Dependency:** This is the black box at the bottom of every route. Both Zhu and
Kelliher take it as given (Zhu cites Viana Thm 3.3). **For Lean this is the
foundational lemma to obtain or build** (Mathlib status: Birkhoff is in Mathlib;
Kingman is the gap).

- **Birkhoff** (Zhu Thm 4.7) is the special case `φ_n = Σ_{j<n} φ∘f^j` (additive).
- **Corollary 4.8 (Zhu):** if `ψ := φ∘f − φ ∈ L^1(μ)` then `(1/n) φ(f^n x) → 0`
  a.e. — used to control the cocycle "tail" / make `d_ε(x)` tempered.

### Furstenberg–Kesten (Zhu Thm 4.2, Artigiani Thm 2, Kelliher Cor 3.2)

> Under `log^+ ‖A^{±1}‖ ∈ L^1(μ)`, the **extremal Lyapunov exponents**
> ```
> λ^+(x) = lim_{n→∞} (1/n) log ‖A_n(x)‖,   λ^-(x) = lim_{n→∞} (1/n) log ‖A_n(x)^{-1}‖^{-1}
> ```
> exist μ-a.e., are `f`-invariant and `μ`-integrable, with
> `∫ λ^+ dμ = lim (1/n)∫ log‖A_n‖ dμ` etc.

**Proof (the model application of Kingman, Zhu §4):** `φ_n(x) := log ‖A_n(x)‖` is
**subadditive** (submultiplicativity of `‖·‖`); `ψ_n(x) := log ‖A_n(x)^{-1}‖^{-1}`
is **super**-additive (apply Kingman to `−ψ_n`). `log^+ ‖A^{±1}‖ ∈ L^1` gives
`φ_1^+ ∈ L^1`. Integrability of the limit `λ^+` (i.e. `λ^+ ∈ L^1`, both signs)
follows from `‖B‖ ≥ ‖B^{-1}‖^{-1}` and measure-preservation. **`λ^±` finite a.e.
is essential** for the rest (Zhu Remark 4.6).

---

## 3. Proof skeleton — Route A: Zhu/Viana–Walters–Bochi (induction on dimension)

This is the most fully detailed source. Strategy: first prove the theorem with
`limsup` in place of `lim` (parts (a),(b),(c')), then upgrade `limsup → lim` by an
**induction on `k(x)`** (the number of distinct exponents), peeling one exponent
at a time and recursing on a lower-dimensional cocycle.

Notation: `λ(x,v) := limsup_{n→∞} (1/n) log |A_n(x) v|`, with `λ(x,0) = −∞`.

**Step A0 — Furstenberg–Kesten gives the extremes.** (Zhu §4, Thm 4.2, depends:
Kingman 4.1.) Establishes `λ^±` exist and are finite a.e. ⟹ for every `v ≠ 0`,
`λ^-(x) ≤ λ(x,v) ≤ λ^+(x)`, so `λ(x,v)` is finite (Lemma 5.3(i)).

**Step A1 — `v ↦ λ(x,·)` is a "filtration function" (Lemma 5.3).** For a.e. `x`,
all `v, v' ≠ 0`:
(i) `λ(x,v)` finite, between `λ^-` and `λ^+`;
(ii) `λ(x, cv) = λ(x,v)` for `c ≠ 0`;
(iii) `λ(x, v+v') ≤ max{λ(x,v), λ(x,v')}` (ultrametric / non-Archimedean);
(iv) **equivariance:** `λ(x,v) = λ(f(x), A(x) v)`.
Depends on: definition of `A_n`, the sandwich `‖A_n‖^{-1}|v| ≤ |A_n v| ≤ ‖A_n‖|v|`
(via `‖A_n^{-1}‖^{-1} ≤ |A_n v|/|v|`), and Lemma 5.5 (limsup of sums of exponentials).

**Step A1' — abstract algebra of non-Archimedean functions (Lemma 5.4).** Any
`g: ℝ^d → ℝ ∪ {−∞}` with `g(v+w) ≤ max{g(v),g(w)}`, `g(cv)=g(v)`, `g(0)=−∞`
satisfies: (a) if `g(v) ≠ g(w)` then `g(v+w) = max`; (b) distinct values
`g(v_1),…,g(v_m)` ⟹ `v_1,…,v_m` linearly independent; (c) **`g` takes at most `d`
distinct finite values.** This is the linear-algebra heart: it forces the spectrum
to be finite (`≤ d` exponents). Depends only on the ultrametric axioms.

**Step A2 — construct the limsup flag (Prop 5.2, parts (a),(c')).** Define
`K_x = { λ(x,v) : v ≠ 0 }`. By A1+A1'(c), `K_x` is finite with `k=k(x) ≤ d`
elements `λ_1(x) > ··· > λ_k(x)`. Define `V_x^i = { v ≠ 0 : λ(x,v) ≤ λ_i(x) } ∪ {0}`.
By A1(ii),(iii) these are **subspaces**, strictly nested ⟹ flag. For
`v ∈ V_x^i \ V_x^{i+1}`, the ultrametric forces `λ(x,v) = λ_i(x)` exactly (part c').
Equivariance (a) from A1(iv) + `A(x)` invertible (so `K_x = K_{f(x)}`,
`A(x) V_x^i = V_{f(x)}^i`).

**Step A3 — measurability (Prop 5.10, part (b)).** Recursive: `V_x^1 = ℝ^d` trivially
measurable; `λ_1(x) = max_i λ(x, e_i)` over a basis is measurable; then
`V_*^2 = {(x,v) : λ(x,v) < λ_1(x)}` is measurable, its projection
`π(V_*^2) = {k(x) ≥ 2}` is measurable (projection of a product-measurable set,
Fact 5.9), `x ↦ V_x^2` measurable via measurable selection of bases. Iterate.
Depends on: Grassmannian `Gr(d)` with Hausdorff metric `d_Grass`, the
measurable-graph ⇔ measurable-map characterizations (Lemma 5.7 for compact-set-valued
maps, Lemma 5.8 for subspace-valued maps), measurable selection (Castaing–Valadier /
Kuratowski–Ryll-Nardzewski). **This is heavy measurable-selection machinery —
likely the hardest part to formalize.**

**Step A4 — base-case lemma (Lemma 5.11, the skew-product / subadditive-on-bundles
lemma).** For a measurable **invariant** sub-bundle `x ↦ V_x` (`A(x)V_x = V_{f(x)}`):
```
(a) lim (1/n) log ‖A_n(x)|_{V_x}‖ = max{ λ(x,v) : v ∈ V_x \ {0} },
(b) lim (1/n) log ‖(A_n(x)|_{V_x})^{-1}‖^{-1} = min{ λ(x,v) : v ∈ V_x \ {0} }.
```
Taking `V_x = ℝ^d` recovers `λ_1 = λ^+`, `λ_k = λ^-` (Remark 5.12). The point:
the **max and min of `λ(x,·)` on a bundle are realized as honest limits, not just
limsups**, which is what later turns limsup into lim.
*Proof ingredients:* restrict to constant `dim V_x = l` (measurable), trivialize
`V_x ≅ ℝ^l` via measurable orthonormal frame (Gram–Schmidt, Lemma 5.8), get a new
cocycle `D(x) = A(x)|_{V_x} ∈ GL(l)` with `log^+‖D^{±1}‖ ∈ L^1`. Projectivize to
`G: M × ℙℝ^l → M × ℙℝ^l`, `Φ(x,[v]) = log(|D(x)v|/|v|)`. Then `Σ_{j<n} Φ(G^j) =
log(|D^n v|/|v|)`, so `S_n = log‖D^n‖`, `I_n = log‖(D^n)^{-1}‖^{-1}`. Apply:
- **Theorem 5.14 (skew-product variational principle):** for `G(x,v)=(f(x),G_x(v))`
  with `G_x` continuous on a **compact** `P`, the limits
  `I(x) = lim (1/n) inf_v Σ Φ(G^j)`, `S(x) = lim (1/n) sup_v Σ Φ(G^j)` exist a.e.,
  and there are `G`-invariant measures `η_I, η_S` projecting to `μ` with
  `∫ Φ dη_I = ∫ I dμ`, `∫ Φ dη_S = ∫ S dμ`. *Proof:* `−I_n` subadditive ⟹ Kingman
  gives the limit; build `η_I` as a weak* limit of empirical measures along a
  measurable selection `v_n(x) ∈ argmin`; compactness of `M(μ)` (probability
  measures projecting to `μ`).
- **Corollary 5.15:** a.e. `x` has `v_I(x), v_S(x) ∈ P` realizing `I(x), S(x)` as
  genuine limits (via Birkhoff on the invariant measure + projection). This yields
  vectors achieving the max/min, upgrading limsup to lim at the extremes.
*Dependencies:* Kingman 4.1, Birkhoff 4.7, compactness of `ℙℝ^l` and of `M(μ)` in
weak* topology, measurable selection (Lemma 5.7).

**Step A5 — inductive-step lemma (Lemma 5.19, peeling one exponent).** Setup: `V_x`
a measurable invariant sub-bundle and `f`-invariant integrable `α(x) < β(x)` with
(i) `λ(x,v) ≤ α(x)` for `v ∈ V_x\{0}`, (ii) `λ(x,u) ≥ β(x)` for `u ∉ V_x`. Write
`A(x)` in block-triangular form w.r.t. `ℝ^d = V_x ⊕ V_x^⊥`:
```
A(x) = [ B(x)   0   ]      B: V_x^⊥ → V_{f(x)}^⊥  (the "quotient" cocycle)
       [ C(x)  D(x) ]      D: V_x   → V_{f(x)}     (= A(x)|_{V_x})
```
(block-triangular because `A(x) V_x = V_{f(x)}` — invariance gives the upper-right 0).
Then for `u ∈ V_x^⊥ \ {0}`, `v ∈ V_x`:
(a) `limsup (1/n) log|B_n(x) u| = limsup (1/n) log|A_n(x)(u+v)|`;
(b) **if `lim (1/n) log|B_n(x)u|` exists, then `lim (1/n) log|A_n(x)(u+v)|` exists
and equals it.**
*Proof ingredients:* `A_n` has block form with off-diagonal
`C_n(x) = Σ_{j=0}^{n-1} D_{n-j-1}(f^{j+1}x) C(f^j x) B_j(x)`; bound each factor
(`‖B_j u‖ ≤ b_ε e^{j(γ+ε)}`, `‖C(f^j x)‖ ≤ c_ε e^{jε}` from Cor 4.8, and the **key**
- **Fact 5.20:** `‖D_n(f^m x)‖ ≤ d_ε(x) e^{α(x)n + (m+n)ε}` — a *tempered* bound on
  the contracting block, proved via Cor 4.8 (`(1/m) log b_ε(f^m x) → 0`) using
  Lemma 5.11(a) `lim (1/n)log‖D_n‖ ≤ α`). Conclude `|C_n u|` grows at rate
  `≤ max{α, rate of B}+3ε`, so the off-diagonal cannot dominate; the gap `α < β`
  separates the two blocks.
*Dependencies:* Lemma 5.11, Cor 4.8 (Birkhoff corollary), Lemma 5.5.

**Step A6 — the induction (Prop 5.26, part (c)).** Assume (WLOG by restricting to
invariant measurable sets) `k(x) ≡ k` and `dim V_x^k ≡ l` constant.
- **Base case `i = k`:** apply Lemma 5.11 to `V_x = V_x^k`: max = min = `λ_k(x)`, so
  `lim (1/n) log|A_n(x) v| = λ_k(x)` for all `v ∈ V_x^k \ {0}` (limsup is a lim here).
- **Inductive step:** apply Lemma 5.19 with `α = λ_k`, `β = λ_{k-1}`,
  `V_x = V_x^k`. The block `B(x)` defines a **new cocycle of one fewer exponent**
  on `V_x^⊥ ≅ ℝ^{d-l}`, whose flag is `U_x^i := V_x^⊥ ∩ V_x^i`. By 5.19(a) the
  `B`-cocycle's limsup-spectrum equals the `A`-cocycle's on `V^i \ V^{i+1}`. Apply
  Lemma 5.11 to `U_x^{k-1}` (for the `B`-cocycle) to get `lim` exists `= λ_{k-1}`;
  then 5.19(b) transports the genuine limit back to `A` on `V_x^{k-1} \ V_x^k`.
- **Recurse** on `B` (decompose `ℝ^{d-l} = U^{k-1} ⊕ (U^{k-1})^⊥`, etc.), peeling
  `λ_{k-2}, …, λ_1`. After `k` steps, `lim (1/n) log|A_n(x)v| = λ_i(x)` for all `i`,
  all `v ∈ V_x^i \ V_x^{i+1}`. ∎

> **Route A summary of the dependency DAG:**
> Kingman (4.1) ⟶ Furstenberg–Kesten (4.2) + Birkhoff (4.7) ⟶ Lemma 5.3 (filtration
> fn) + Lemma 5.4 (≤ d values) ⟶ Prop 5.2 (limsup flag) + Prop 5.10 (measurability).
> Separately Kingman + skew-product (Thm 5.14, Cor 5.15) ⟶ Lemma 5.11 (extremes are
> limits). Lemma 5.11 + Cor 4.8 ⟶ Fact 5.20 ⟶ Lemma 5.19 (peel). Lemma 5.11 + 5.19
> ⟶ Prop 5.26 (induction ⟹ lim). Done one-sided.

---

## 4. Proof skeleton — Route B: Ruelle exterior powers / singular values (Kelliher)

This is Oseledets' **original** route via `Λ_x = lim (A_n^*A_n)^{1/2n}`, mediated by
exterior powers. Conceptually cleaner for the *eigenvalue* part; the *eigenspace
convergence* is the "hard work."

**Step B0 — `log^+‖T‖ tail vanishes.** By Birkhoff applied to `f_n = log^+‖T(τ^{n-1}x)‖`,
`(1/n) log^+‖T(τ^{n-1}x)‖ → 0` a.e. (so single-step growth is subexponential).

**Step B1 — Furstenberg–Kesten on all exterior powers `T^{∧q}`.** Exterior power
`A^{∧q}` acts on `∧^q ℝ^m` by `A^{∧q}(v_{i_1}∧···∧v_{i_q}) = Av_{i_1}∧···∧Av_{i_q}`.
Functorial: `(AB)^{∧q} = A^{∧q} B^{∧q}` (Lemma 3.3), so `(T^n_x)^{∧q} = (T^{∧q})^n_x`.
Apply Furstenberg–Kesten (Cor 3.2) to the cocycle `T^{∧q}` (`log^+‖T^{∧q}‖ ∈ L^1`
since `‖T^{∧q}‖ ≤ ‖T‖^q`): for each `q = 1,…,m`,
`lim (1/n) log ‖(T^n_x)^{∧q}‖` exists and is `τ`-invariant a.e.
*Dependency:* Kingman ⟹ Furstenberg–Kesten; exterior algebra (Lemma 3.3, 5.4).

**Step B2 — singular values of products converge.** Key identity (Lemma 5.5,
Kelliher): `‖A^{∧q}‖ = σ_m σ_{m-1} ··· σ_{m-q+1}` where `σ_1 ≤ ··· ≤ σ_m` are the
singular values of `A` (eigenvalues of `√(A^*A)`). [Proof: `(√(A^*A))^{∧q}` and
`√((A^*A)^{∧q})` agree on basis elements; `‖A^{∧q}‖ = max eigenvalue of
`√((A^*)^{∧q}A^{∧q})` = product of top `q` singular values.] So
`(1/n) log‖(T^n)^{∧q}‖ = (1/n) log( t_n^{(m)} ··· t_n^{(m-q+1)} )` where
`t_n^{(1)} ≤ ··· ≤ t_n^{(m)}` are eigenvalues of `((T^n)^*T^n)^{1/2} = √((T^n)^*T^n)`.
Taking successive differences (`q=1`, then `q=2`, …) the existence of the
exterior-power limits forces **each** `χ^{(p)} := lim (1/n) log t_n^{(p)}` to exist
and be finite, `p = 1,…,m`. **This is the "easy work": eigenvalues converge.**
*This is the singular-value heart of the classical proof.*

**Step B3 — the Fundamental Lemma (Prop 1.3 of Ruelle, Kelliher Lemma 4.1).**
> Given real `m×m` matrices `T_n` with `limsup (1/n) log‖T_n‖ ≤ 0` and `T^n = T_n···T_1`,
> if all `lim (1/n) log‖(T^n)^{∧q}‖` exist (`q=1,…,m`), then
> `Λ = lim ((T^n)^* T^n)^{1/2n}` exists, with eigenvalues `exp λ^{(r)}` and
> eigenspaces `U^{(r)}` giving the filtration and Lyapunov limits.
- *Eigenvalue part (easy):* B2 above.
- *Eigenspace part ("hard work", Kelliher §8, Lemma 8.1):* show the eigenspaces
  `U_n^{(r)}` of `((T^n)^*T^n)^{1/2}` (grouped by which `χ^{(r)}` their log-eigenvalue
  tends to) form a **Cauchy sequence in the Grassmannian** `Gr_{m_r}^m` and hence
  converge to `U^{(r)}`. The quantitative estimate (Lemma 8.1):
  `max{ |⟨u,u'⟩| : u ∈ U_n^{(r)}, u' ∈ U_{n+k}^{(r')}, ‖u‖=‖u'‖=1 } ≤ K e^{-n(|λ^{(r')}-λ^{(r)}| - δ)}`
  — eigenspaces with **different** exponents become exponentially orthogonal; with
  the **same** exponent (`r=r'`) the spaces are Cauchy (Cor 8.2). Grassmannian is
  complete ⟹ limit `U^{(r)}` exists ⟹ `Λ` exists (eigenvalues + eigenspaces
  determine the matrix). *Dependencies:* metric on Grassmannian
  `d(U,V) = max{|⟨u,v^⊥⟩|} = |sin θ|` (Lemma 6.1, 6.2); projection lemma 5.6.
- *Lyapunov limit (clean):* for `u = c_1 u_1 + ··· + c_r u_r ∈ V^{(r)}\V^{(r-1)}`,
  `c_r ≠ 0`, write `((T^n)^*T^n)^{1/2} u ∼ Σ c_i e^{nλ^{(i)}} u_i`; then
  `(1/n) log‖T^n u‖ = (1/2n) log( Σ c_i^2 e^{2nλ^{(i)}} ) → λ^{(r)}` (L'Hôpital /
  dominant-term). Uses `‖T^n u‖ = ‖√((T^n)^*T^n) u‖` and orthogonality of `U^{(r)}`.

**Step B4 — assemble MET.** Apply the Fundamental Lemma to `T_n = T(τ^{n-1}x)` on
`Γ = Γ_1 ∩ Γ_2` (Birkhoff full-measure set ∩ exterior-power-limit full-measure set).
This proves Kelliher Thm 2.1.

> **Route B vs Route A:** Route B produces the **orthogonal** filtration from
> eigenspaces of the symmetric limit `Λ_x` (so the `V^{(r)}` are canonical and
> orthogonal but the eigenspaces `U^{(r)}` are NOT equivariant). Route A produces the
> **equivariant** flag directly from growth rates. Route B's "hard work" is the
> Grassmannian Cauchy estimate; Route A's hard work is the skew-product/measurable
> selection (Lemma 5.11/5.19). Both bottom out in **Kingman + Furstenberg–Kesten**.

---

## 5. Upgrading flag ⟶ splitting via invertibility (the two-sided theorem)

Three concrete mechanisms appear across sources for why **invertibility** is what
turns the one-sided flag into the two-sided direct-sum splitting:

1. **Time-reversal duality (Artigiani, "Numerical considerations" §):**
   `E_1(x, T) = E_2(x, T^{-1})` and `E_2(x, T) = E_1(x, T^{-1})` in 2D; generally
   the **backward** Oseledets filtration `V_-^i(x)` (the flag of the inverse cocycle
   `A_{-n}`) is *increasing* where the forward `V_+^i` is decreasing, and the
   equivariant graded piece is `E_i(x) = V_+^i(x) ∩ V_-^{(complementary index)}(x)`.
   The intersection of the forward filtration with the backward filtration supplies
   a *canonical complement*, producing `ℝ^d = ⊕ E_i`. This requires `f` and `A`
   invertible so that `A_{-n}` is defined.

2. **Two-sided limit (Artigiani Thm 3(ii)):** on the splitting, the exponent limit
   holds as `n → ±∞`, not just `n → +∞`. The forward limit `+λ_i` pins down the
   forward-filtration position; the backward limit `−λ_i` (running `A^{-1}`) pins
   down the backward-filtration position; their intersection is `E_i`.

3. **2D explicit construction (Artigiani Thm 4, full proof).** For `A: M → SL(2,ℝ)`
   (reduce `GL_2` to `SL_2` by dividing by `√|det|`; Lyapunov spectra differ by the
   Birkhoff average `t(x)` of `log√|det|`, same filtration). With
   `λ(x) = lim (1/n) log‖A_n(x)‖` (Furstenberg–Kesten):
   - If `λ(x) = 0`: `lim (1/n) log‖A_n v‖ = 0` for **all** `v` (sandwich
     `‖A_n‖^{-1}‖v‖ ≤ ‖A_n v‖ ≤ ‖A_n‖‖v‖`).
   - If `λ(x) > 0`: there is a line `L^s(x)` with rate `−λ(x)` on `L^s\{0}` and
     `+λ(x)` off `L^s`. **Construction (singular vectors):** let `s_n(x), u_n(x)` be
     the **most contracted / most expanded unit vectors** of `A_n(x)`
     (`‖A_n s_n‖ = ‖A_n‖^{-1}`, `‖A_n u_n‖ = ‖A_n‖`); these are **orthogonal** and
     their images orthogonal. Show `limsup (1/n) log|sin ∠(s_n, s_{n+1})| ≤ −2λ(x)`,
     so `s_n` is **Cauchy** (`‖s_{n+k} − s_n‖ ≤ C e^{n(−2λ+ε)}`) ⟹ `s_n → s(x)`,
     defining `L^s(x) = ℝ s(x)` with `lim (1/n) log‖A_n s(x)‖ = −λ(x)`. Vectors off
     `L^s(x)`: write `v = cos γ_n s_n + sin γ_n u_n` with `sin γ_n` bounded away from
     0; then `‖A_n v‖ ≳ e^{nλ}`, giving rate `+λ`. Equivariance `A(x)L^s(x) = L^s(f x)`
     from the rate computation. Doing this for `F` and `F^{-1}` and combining gives the
     full invertible 2D MET. **The singular-vector Cauchy argument is the prototype of
     the Grassmannian Cauchy argument in Route B.**

> **Formalization note on the splitting:** the cleanest formal route to the
> two-sided splitting is: prove the one-sided flag theorem (Route A or B), apply it
> to the inverse cocycle to get the backward flag, then define `E_i` as the
> intersection and verify it is a complement + equivariant + two-sided limit. This
> reuses the one-sided theorem as a black box twice.

---

## 6. Definitions quoted exactly (for faithful formalization)

- **Subadditive sequence** (Zhu): `φ_n : M → [−∞,+∞)`, `n ≥ 1`, is *subadditive
  relative to f* if `φ_{m+n} ≤ φ_m + φ_n ∘ f^m` for all `m,n ≥ 1`; *super-additive*
  if `≥`. *(essentially) f-invariant*: `φ(f(x)) = φ(x)` for a.e. `x`.
- **Linear cocycle** (Zhu Def 2.3 / Artigiani): for dynamical system `(M,B,μ,f)`
  and measurable `A: M → GL(d)`, the cocycle is `F(x,v) = (f(x), A(x)v)`;
  `A_n(x) = A(f^{n-1}(x))···A(f(x))·A(x)`.
- **Flag** (Zhu §5): a *decreasing* family `ℝ^d = V^1 ⊋ ··· ⊋ V^k ⊋ {0}` of
  linear subspaces.
- **Filtration** (Kelliher §2): the *nested* `{0} = V^{(0)} ⊆ ··· ⊆ V^{(s)} = ℝ^m`;
  intrinsically `V^{(r)} = { u : lim (1/t) log‖T^t_x u‖ ≤ λ^{(r)} }`.
- **Measurable sub-bundle / invariant** (Zhu §5.3): `x ↦ V_x` is a *measurable
  sub-bundle* if it satisfies the equivalent measurability conditions of Lemma 5.8;
  it is *invariant* if `A(x) V_x = V_{f(x)}` a.e.
- **Exterior power of a matrix** (Kelliher §3): for `A` real `m×m`, `A^{∧q}` is the
  `(C(m,q) × C(m,q))` matrix with `A^{∧q}(x_1 ∧ ··· ∧ x_q) = A x_1 ∧ ··· ∧ A x_q`;
  inner product `⟨u_1∧···∧u_q, w_1∧···∧w_q⟩ = det(⟨u_i, w_j⟩)`.
- **Singular values** (Artigiani / Kelliher): for `B`, `σ_i = √(α_i)` where `α_i`
  are the (nonneg.) eigenvalues of `B^T B = B^* B`; `‖B‖ = σ_max`.
- **Oseledets' limit** (Kelliher Thm 2.1(1)): `Λ_x = lim_{n→∞} ((T^n_x)^* T^n_x)^{1/2n}`.
- **Grassmannian metric** (Kelliher §6, Zhu §5.2): `d(U,V) = max{ |⟨u, v^⊥⟩| :
  u ∈ U, v^⊥ ∈ V^⊥, ‖u‖=‖v^⊥‖=1 } = |sin θ(U,V)|`; or `d_Grass(V,W) =
  d_Hausdorff(S^{d-1}∩V, S^{d-1}∩W)`.

---

## 7. Formalization notes (what's easy / hard, Mathlib pieces)

**Likely available / straightforward in Mathlib:**
- Birkhoff pointwise ergodic theorem (`MeasureTheory.Ergodic` / Birkhoff is in Mathlib).
- Operator norm, submultiplicativity, spectral theorem for self-adjoint matrices,
  singular value / polar decomposition basics (`Matrix`, `InnerProductSpace`,
  `LinearAlgebra` — symmetric matrices diagonalize, `IsSymmetric.eigenvalue...`).
- Exterior powers `∧^q` (`ExteriorAlgebra` / `LinearMap.exteriorPower` /
  `Matrix.... ` — functoriality `(AB)^{∧q} = A^{∧q}B^{∧q}` should be derivable).
- Grassmannian as a metric space — likely needs building (Mathlib has
  `Submodule`/subspaces but a complete metric Grassmannian with the `|sin θ|`
  metric is probably not packaged).

**The central gap — Kingman's subadditive ergodic theorem.** Not in Mathlib (as of
knowledge cutoff). Every route depends on it. This is the keystone to either find,
port (e.g. from an existing formalization), or prove. Recommended **first
milestone**. Furstenberg–Kesten then follows almost immediately
(`φ_n = log‖A_n‖` subadditive ⟹ Kingman).

**Hardest analytic pieces:**
- *Route A:* the skew-product variational lemma (Thm 5.14) needs compactness of the
  space of probability measures projecting to `μ` in weak* topology + measurable
  selection (Kuratowski–Ryll-Nardzewski / Castaing–Valadier). Measurable selection
  is a substantial dependency probably not in Mathlib in usable form.
- *Route A:* Lemma 5.19 / Fact 5.20 — the tempered block-triangular estimate. Pure
  hard analysis but elementary (Borel–Cantelli-flavored), self-contained once Cor 4.8
  (Birkhoff corollary) is available.
- *Route B:* the Grassmannian Cauchy estimate (Lemma 8.1) — needs completeness of the
  Grassmannian and the exponential-orthogonality estimate. Conceptually self-contained.

**Recommended formalization order (mirrors the math dependency):**
1. Kingman ⟹ 2. Furstenberg–Kesten (top + bottom exponents, extremal Lyapunov) ⟹
3. one-sided MET **flag** version (choose Route A induction OR Route B exterior
powers — Route A avoids building the complete Grassmannian and the eigenspace-Cauchy
estimate, but needs measurable selection; Route B avoids measurable selection but
needs Grassmannian completeness + singular value/exterior algebra). ⟹
4. two-sided MET **splitting** via applying (3) to the inverse cocycle and
intersecting filtrations (needs `f`, `A` invertible).

**Easiest "first real theorem" to formalize end-to-end:** the **trivial model**
(Zhu Thm 3.1, single normal matrix) — pure linear algebra (spectral theorem), no
ergodic theory. Good sanity check of the statement shape (`flag`,
`v ∈ V^i \ V^{i+1}`, `lim (1/n)log|B^n v| = log|ν_i|`). Then **Furstenberg–Kesten**
once Kingman is available, then the 2D invertible case (Artigiani Thm 4) which is the
smallest case exhibiting the full flag→splitting phenomenon.

**Statement-shape choices to pin down for Lean:**
- index convention: Zhu indexes exponents **decreasing** (`λ_1 > ··· > λ_k`,
  `V^1 ⊋ ··· ⊋ V^k`); Kelliher/Ruelle indexes **increasing** (`λ^{(1)} < ··· <
  λ^{(s)}`, `V^{(1)} ⊆ ··· ⊆ V^{(s)}`). Pick one and be consistent.
- `λ(x,v) = limsup (1/n) log|A_n(x)v|` is the cleanest primitive; the flag is
  `V^i = {v : λ(x,v) ≤ λ_i}` and the theorem says `limsup = lim` on each stratum.
- `GL_d(ℝ)` vs general real `m×m` (Ruelle allows non-invertible `T`, with
  `λ^{(1)} = −∞` possible) — decide whether the one-sided theorem targets `GL_d`
  (Zhu) or all matrices (Ruelle).
