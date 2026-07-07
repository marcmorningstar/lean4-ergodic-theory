# Digest — Routes to the Oseledets Multiplicative Ergodic Theorem (MET) and their formalization difficulty

**Source cluster:** `routes-comparison`
**Purpose:** primary input to the Lean 4 + Mathlib formalization plan. Surveys the
landscape of proof routes for the MET, their external dependencies, what is already
in Mathlib vs. what must be built, and a recommendation.

**Primary sources used (raw scrapes in `docs/research/sources/`):**

- `wikipedia-multiplicative-ergodic-theorem.md` — Oseledets/Wikipedia: cocycle defn,
  two-sided `L¹(log‖C‖, log‖C⁻¹‖)` hypothesis, filtration form; notes Raghunathan's
  conceptually different proof and the Ruelle/Margulis/Karlsson/Ledrappier extensions.
- `wikipedia-lyapunov-exponent.md` — singular-value / `Λ = lim (1/2t) log(Y Yᵀ)`
  formulation (the object of the classical route), Lyapunov spectrum, regularity.
- `viana-lectures-lyapunov-exponents.md` — Viana, *Lectures on Lyapunov Exponents*
  (Cambridge 2014), TOC + Ch.1–2; the canonical **Kingman-based** proof (Ch. 3–4).
- `filip-2017-notes-MET.md` — Filip, *Notes on the Multiplicative Ergodic Theorem*
  (arXiv:1710.10694); induction-on-dimension proof, **exterior-power exponent calculus**,
  and the geometric/Karlsson–Margulis "Noncommutative Ergodic Theorem".
- `karlsson-margulis-1999-nonpositive-curvature.md` — Karlsson–Margulis,
  *A Multiplicative Ergodic Theorem and Nonpositively Curved Spaces* (CMP 208, 1999);
  full proof via a custom maximal ergodic inequality + Busemann geometry.
- `zhu-uchicago-reu2023-met.md` — Zhu, UChicago REU 2023; explicit route comparison
  and the Raghunathan reference [Israel J. Math. 32 (1979) 356–362].
- `wikipedia-kingman-subadditive-ergodic-theorem.md` — exact Kingman statement (key dependency).

---

## 0. Conventions and the two structural distinctions that matter most

Throughout, `(Ω, B, μ, T)` is a probability measure-preserving system, `T` ergodic
(the general case follows by ergodic decomposition). A **(one-sided) linear cocycle**
is a measurable `A : Ω → GL_d(ℝ)` (sometimes a semigroup-valued map; `A` need not be
invertible for the one-sided theorem). Write the iterated cocycle

```
A_n(x) = A(T^{n-1} x) ··· A(T x) A(x),    n ≥ 1,   A_0(x) = I.
```

The cocycle identity is `A_{n+m}(x) = A_n(T^m x) · A_m(x)`. Wikipedia (Oseledets) uses
the continuous-time form `C(x, t+s) = C(x(t), s) C(x, t)`, `C(x,0) = I`.

Two distinctions run through every statement and must be tracked precisely:

**(D1) one-sided vs. two-sided.**
- *One-sided* (`T` need not be invertible; `A : Ω → GL_d` or even into a semigroup):
  needs only `log⁺‖A‖ ∈ L¹`. Conclusion is a **filtration/flag** of subspaces.
- *Two-sided* (`T` invertible; apply the result to both `T` and `T⁻¹`): needs
  `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹`. Conclusion upgrades to a **direct-sum (Oseledets)
  splitting**.

**(D2) filtration/flag vs. direct-sum splitting.**
- *Filtration / flag* (one-sided): a decreasing chain of `T`-invariant subbundles
  `ℝ^d = V¹_x ⊋ V²_x ⊋ ··· ⊋ V^{k+1}_x = {0}` with `lim (1/n) log‖A_n(x) v‖ = λ_i`
  for `v ∈ V^i_x \ V^{i+1}_x`. (Filip writes it as an increasing filtration
  `0 ⊊ V^{≤λ_k} ⊊ ··· ⊊ V^{≤λ_1} = V`.)
- *Direct-sum splitting* (two-sided, **requires invertibility**): a `T`-invariant
  decomposition `ℝ^d = E¹_x ⊕ ··· ⊕ E^k_x` with
  `lim_{n→±∞} (1/n) log‖A_n(x) v‖ = λ_i` for `0 ≠ v ∈ E^i_x` (note the sign of `1/n`
  flips as `n → −∞`). Filip's construction: `V^{λ_j} = V^{≤λ_j} ∩ V^{≤η_{k+1−j}}`,
  the intersection of the forward filtration with the backward (`T⁻¹`) filtration.

---

## 1. Precise theorem statements and version distinctions

### 1.1 One-sided MET (filtration form) — Filip Thm 2.2.6 (quoted)

> Suppose `V → (Ω, B, μ, T)` is a cocycle over an ergodic probability
> measure-preserving system. Assume `V` is equipped with a metric `‖−‖` on each fiber
> such that
> ```
> ∫_Ω log⁺ ‖T_ω‖_op  dμ(ω) < ∞        (2.2.7)
> ```
> Here `log⁺(x) := max(0, log x)`. Then there exist real numbers
> `λ_1 > λ_2 > ··· > λ_k` (with perhaps `λ_k = −∞`) and `T`-invariant subbundles of `V`
> defined for a.e. `ω`:
> ```
> 0 ⊊ V^{≤λ_k} ⊊ ··· ⊊ V^{≤λ_1} = V
> ```
> such that for vectors `v ∈ V^{≤λ_i}_ω \ V^{≤λ_{i+1}}_ω`,
> ```
> lim_{N→∞} (1/N) log ‖T^N v‖ → λ_i.        (2.2.8)
> ```

Invariance means `T_ω : V_ω → V_{Tω}` carries `V^{≤λ_i}_ω → V^{≤λ_i}_{Tω}`
(*equivariance* of the filtration). The multiplicity of `λ_i` is
`dim V^{≤λ_i} − dim V^{≤λ_{i+1}}`. The filtration and exponents are **canonical**
(characterized by (2.2.8)).

Notable: the one-sided theorem needs only `log⁺‖A‖ ∈ L¹` — it does **not** require
`A` invertible (Filip even allows `λ_k = −∞`, covering non-invertible / degenerate
cocycles). Karlsson–Margulis state the same with `A : X → GL_N(ℝ)` and both
`∫ log⁺‖A‖ < ∞` and `∫ log⁺‖A⁻¹‖ < ∞` because they aim directly at the symmetric-space
(two-sided-flavored) regularity statement.

### 1.2 Two-sided MET (Oseledets splitting) — Filip Variant 2.2.10 (quoted/paraphrased)

> Suppose `T : Ω → Ω` is **invertible**, and the cocycle on `V` for the map `T⁻¹`
> satisfies the same assumptions. Applying the result to `T⁻¹` gives exponents `η_j` and
> the **backward** filtration `V^{≤η_j}`. Compatibility forces `η_j = −λ_{k+1−j}` and
> `k' = k`. Defining `V^{λ_j} := V^{≤λ_j} ∩ V^{≤η_{k+1−j}}` yields a `T`-invariant
> direct-sum decomposition
> ```
> V = V^{λ_1} ⊕ ··· ⊕ V^{λ_k},
> ```
> whose defining dynamical property is
> ```
> 0 ≠ v ∈ V^{λ_i}  ⇔  lim_{N→±∞} (1/N) log ‖T^N v‖ = λ_i.
> ```

This is the form needed for Pesin theory / non-uniform hyperbolicity. **It strictly
requires invertibility** of both `T` and the fiber maps; the splitting does not exist
in general for one-sided cocycles (the filtration is the best you get).

### 1.3 Classical singular-value / Lyapunov-regularity form (Wikipedia Lyapunov + Karlsson–Margulis)

For the derivative cocycle `Y(t)` (`Ẏ = J Y`, `Y(0) = I`), the limit
```
Λ = lim_{t→∞} (1/2t) log( Y(t) Yᵀ(t) )
```
exists (Oseledets); the Lyapunov exponents `λ_i` are the **eigenvalues of `Λ`**,
equivalently `λ_i = lim_{t→∞} (1/t) log α_i(Y(t))` where `α_i` are the **singular values**
(square roots of eigenvalues of `Y* Y`). Karlsson–Margulis phrase **Lyapunov regularity**
of `A_n(x)` as: there is a positive-definite symmetric `Λ = Λ(x)` with
```
(1/n) log ‖A_n Λ^{−n}‖ → 0   and   (1/n) log ‖Λ^n A_n^{−1}‖ → 0,      (KM 1.1)
```
i.e. `A_n` behaves asymptotically like the iterate `Λ^n`. They also note the
geometric reformulation in the symmetric space `Y = GL_N(ℝ)/O_N(ℝ)` with distance
`d(y, gy) = (Σ_i (log σ_i)²)^{1/2}` (`σ_i` = eigenvalues of `(g gᵀ)^{1/2}`):
`(1/n) d(Λ^{−n} y, A_n^{−1} y) → 0` is equivalent to (KM 1.1).

### 1.4 Exact statement of the integrability hypothesis (the crux)

- One-sided: `∫_Ω log⁺ ‖A(ω)‖_op dμ < ∞`, `log⁺ := max(0, log ·)`.
- Two-sided: additionally `∫_Ω log⁺ ‖A(ω)⁻¹‖_op dμ < ∞`.
- Equivalent packaging (Viana §2): `log‖A^{±1}‖ ∈ L¹(μ)`.
- Karlsson–Margulis general form: cocycle into semicontractions of `(Y,d)` with
  `∫_X d(y, w(x)·y) dμ < ∞` (first-moment condition), which under `Y = GL_N/O_N`
  specializes to the `log⁺` condition above.

Why `log⁺` and not `log` or `L¹` of `log`: subadditivity (below) only needs an
upper bound on the positive part to invoke Kingman; the lower part is allowed to be
`−∞` (hence `λ_k = −∞` is permitted in the one-sided theorem). This is the single
most important hypothesis to get right in Lean: it is `Integrable (fun ω => max 0 (Real.log ‖A ω‖))`.

---

## 2. The four proof routes

### Route 1 — Classical: Kingman + Furstenberg–Kesten (+ subadditivity of singular values / exterior powers). [Oseledets 1968; Ruelle 1979; Viana Ch. 3–4]

This is the mainstream modern route (Viana, Walters, Bochi; Zhu's REU follows it).

**External dependencies (in order of use):**

1. **Birkhoff pointwise ergodic theorem** (base case `d = 1` and many sub-steps):
   for `f ∈ L¹`, `(1/N) Σ_{i<N} f(T^i ω) → ∫ f dμ` a.e. (Filip Thm 2.1.3).
2. **Kingman's subadditive ergodic theorem** (the engine). Exact statement
   (`wikipedia-kingman...`): for `T` measure-preserving and `{g_n} ⊂ L¹` with
   `g_{n+m}(x) ≤ g_n(x) + g_m(T^n x)`, the limit `lim_n g_n(x)/n =: g(x) ≥ −∞` exists
   a.e. and is `T`-invariant (constant if ergodic). Applied with
   `g_n(x) = log‖A_n(x)‖`, which is subadditive because `‖A_{n+m}‖ ≤ ‖A_n(T^m·)‖·‖A_m‖`
   and `log` is monotone + `log(ab) = log a + log b`.
3. **Furstenberg–Kesten theorem** (immediate corollary of 2): the extremal exponents
   `λ⁺ = lim (1/n) log‖A_n‖` and `λ⁻ = lim (1/n) log‖A_n^{-1}‖^{-1}` exist a.e.
   (Viana Thm 1.1 / §2). `λ⁺ ≥ λ⁻`; if `|det A| = 1` then `λ⁺ ≥ 0 ≥ λ⁻`.
4. **Singular values & exterior powers** to peel off the full spectrum: apply
   Furstenberg–Kesten to the induced cocycle `Λ^p A` on `⋀^p ℝ^d`. The exponents of
   `⋀^p A` are the `p`-fold partial sums of the leading exponents, so
   `lim (1/n) log‖⋀^p A_n‖ = λ_1 + ··· + λ_p`, which recovers each `λ_i` by
   differencing. (Filip §3.1.1: `Λ^k(L)` has exponents `{λ_{i_1}+···+λ_{i_k}}`.)
   The singular values `σ_1 ≥ ··· ≥ σ_d` of `A_n` and the eigenvectors of
   `(A_n^* A_n)^{1/2}` build the filtration; their convergence is the content of
   Ruelle's proof.

**Proof skeleton (one-sided, the form Viana proves in Ch. 4):**
1. Establish Furstenberg–Kesten (top exponent) via Kingman on `log‖A_n‖`.  [dep: 2,3]
2. **Construct the Oseledets flag** (Viana §4.2.1): the most-contracted directions of
   `A_n* A_n` converge; the slowest-growing subspace is `V^{≤λ_k}`, etc.
3. **Measurability** of the flag (§4.2.2) — measurable selection.
4. **Time averages of skew products** (§4.2.3) over the projectivization `ℙ(V)` —
   Birkhoff on the projective bundle.  [dep: 1]
5. **Dimension reduction / induction** (§4.2.5): pass to a `T`-invariant subbundle and
   recurse; complete the proof (§4.2.6). Each layer's exponent comes from
   Furstenberg–Kesten on the appropriate exterior power.  [dep: 3,4]

**Proof skeleton (two-sided, Viana §4.3):**
6. **Upgrade filtration to decomposition** (§4.3.1): intersect forward and backward
   filtrations (`V^{λ_j} = V^{≤λ_j} ∩ V^{≤η_{k+1−j}}`).  [needs invertibility]
7. **Subexponential decay of angles** between Oseledets subspaces (§4.3.2): the angle
   `∠(E^i, E^j)` along the orbit decays subexponentially — proved with Birkhoff/Borel–
   Cantelli. This is the technical heart that makes the splitting honest.  [dep: 1]
8. **Consequences** (§4.3.3): the `lim_{n→±∞}` characterization, tempered norms.

### Route 1′ — Filip's induction-on-dimension variant (same dependencies, cleaner). [Filip §2.3–2.5]

Filip's actual write-up is the most formalization-friendly packaging of Route 1.
It avoids explicit singular-value bookkeeping, replacing it by two lemmas plus
induction on `dim V`:

- **Lemma 2.3.1 (Reducibility / growth dichotomy):** at least one of
  (i) all nonzero `v` grow at one rate `λ`, uniformly on `‖v‖=1`; or
  (ii) there is a nontrivial proper `T`-invariant subbundle `E ⊊ V`.
  *Proof (§2.4):* on the projective bundle `ℙ(V) → Ω`, minimize `η ↦ ∫ f dη` over
  `T`-invariant probability measures projecting to `μ`, where `f([v]) = log(‖Tv‖/‖v‖)`;
  take an **ergodic extreme point** `η` of the minimizing set; apply **Birkhoff** to
  `f`. Uses **Krylov–Bogoliubov in families** (existence + weak-* compactness of
  `M¹(ℙ(V), μ)^T`).  [dep: Birkhoff; Krylov–Bogoliubov; weak-* compactness on the
  projective bundle]
- **Lemma 2.3.3 (Unusual growth implies splitting):** for a short exact sequence
  `0 → E → V → F → 0` with `E` growing at `λ_E`, `F` at `λ_F`, if `λ_E > λ_F` then the
  sequence splits `T`-invariantly. *Proof (§2.5):* solve the cohomological equation
  `τ_ω = T_E^{-1} τ_{Tω} T_F − T_E^{-1} U_ω` by the geometric series
  `τ_ω = −Σ_{n≥0} (T_E^{n+1})^{-1} U_{T^n ω} T_F^n`, which converges because
  `‖U_{T^nω}‖ = e^{o(n)}` (Birkhoff on `log⁺‖U‖ ∈ L¹`) while the `E`/`F` rates differ.
  [dep: Birkhoff; geometric-series convergence estimate]
- **Main proof (§2.3):** induct on `dim V`. Base case `dim = 1` ≡ Birkhoff
  (Remark 2.2.11). Inductive step: apply Lemma 2.3.1; if reducible pick `E` of minimal
  codimension, recurse on `E`, then glue with Lemma 2.3.3.

This route uses **only Birkhoff + linear algebra of cocycles + a Krylov–Bogoliubov /
weak-* compactness argument on the projective bundle**, and notably **avoids needing
Kingman as a separate black box** (Filip's argument re-derives growth rates via Birkhoff
on `ℙ(V)`). The exterior-power calculus (§3.1.1) is used to *describe* exponents of
derived cocycles, not as a load-bearing step in the existence proof.

### Route 2 — Raghunathan. [Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*, Israel J. Math. 32 (1979) 356–362; cited by Zhu [6] and Wikipedia]

A "conceptually different proof" (Wikipedia). It is the **singular-value / exterior-
algebra** route in its purest form: build the limiting positive-definite `Λ(x)`
(equivalently the limit `lim (A_n* A_n)^{1/2n}`) directly, using
Furstenberg–Kesten/Kingman on each exterior power `⋀^p` to control all partial sums of
exponents simultaneously, then read off the splitting from the eigenspaces of `Λ`.

**External dependencies:** Kingman (or Furstenberg–Kesten) on `⋀^p` cocycles; full
**polar / singular-value decomposition** and **functional calculus** `(·)^{1/2n}` for
symmetric positive-definite matrices; convergence of `(A_n* A_n)^{1/2n}` (the
hard analytic core). It is short on paper but analytically dense.

### Route 3 — Karlsson–Margulis (subadditive cocycles on nonpositively curved spaces). [Karlsson–Margulis, CMP 208 (1999) 107–123; full text scraped]

Generalizes the MET to cocycles `u(n,x) = w(x) w(Tx) ··· w(T^{n-1}x)` valued in a
semigroup of **semicontractions** (nonexpanding maps) of a uniformly convex, Busemann
nonpositively-curved complete metric space `(Y,d)` — e.g. a CAT(0)/Cartan–Hadamard
space or a uniformly convex Banach space. The symmetric space `Y = GL_N(ℝ)/O_N(ℝ)`
case **is equivalent to the Oseledets theorem**.

**Main theorem (Thm 2.1, quoted):** under `∫_X d(y, w(x)·y) dμ < ∞`, for a.e. `x` the
limit `A := lim_n (1/n) d(y, y_n(x))` exists; and if `A > 0`, there is a **unique
geodesic ray** `γ(·, x)` from `y` with `lim_n (1/n) d(γ(An, x), y_n(x)) = 0`.
(`y_n(x) := u(n,x)·y`.) Under `Y = GL_N/O_N`, the ray `γ` encodes `Λ(x) = e^H`, giving
Lyapunov regularity.

**Proof skeleton (Sect. 4–5):**
1. `a(n,x) := d(y, y_n(x))` is a **subadditive cocycle** (triangle inequality +
   semicontraction); `∫ a⁺(1,·) dμ < ∞` from the moment condition.  [§5.1]
2. Existence of `A = lim a_n/n` is the **subadditive ergodic theorem** (their
   Corollary 4.3, which they reprove).  [self-contained Kingman]
3. **Custom maximal ergodic inequality** (**Lemma 4.1**) via **F. Riesz's "leaders"
   lemma**: the set `E_1` of `x` with infinitely many `n` s.t.
   `a(n,x) − a(n−k, T^k x) ≥ 0` for all `1 ≤ k ≤ n` has positive measure.
4. **Proposition 4.2** (ergodic strengthening): for every `ε>0`, a.e. `x` admits
   `K(x)` and infinitely many `n` with `a(n,x) − a(n−k,T^k x) ≥ (A−ε)k` for `K ≤ k ≤ n`.
   Corollary 4.3 = Kingman.
5. **Geometric Lemma 3.1** (uniform convexity): if `d(y,x)+d(x,z) ≤ d(y,z)+εd(y,x)`
   then `x` is close to the geodesic `[y,z]`. Combined with Prop. 4.2, the points
   `y_{n_i}` lie near rays `γ_i`; uniform convexity makes `{γ_i(R)}` **Cauchy**, so
   `γ_i → γ` (a ray).  [§5.2–5.3]
6. Conclude `(1/k) d(γ(Ak), y_k) → 0`; uniqueness from convexity.  [§5.4]

Crucially, KM emphasize (Intro) that **the usual reduction to Birkhoff/Kingman is
impossible here**; they substitute their own maximal inequality (Lemma 4.1). The
**invertible/two-sided analogue is FALSE in general** (Remark 2.4: a parabolic isometry
of a warped-product Cartan–Hadamard manifold has no bi-infinite approximating geodesic).

### Route 4 — Filip exterior-algebra (geometric / Noncommutative Ergodic Theorem). [Filip §3–4]

Filip §3–4 recasts Oseledets geometrically: linear-algebra operations on cocycles
(`⊗`, dual, `Hom`, `⋀^k`) act predictably on exponents (§3.1.1), the symmetric space
`GL_N/O_N` and its Cartan/horofunction/Busemann structure encode the splitting (§3.2–3.5),
and the general statement is the **Noncommutative Ergodic Theorem** (§4.3–4.4) — Filip's
exposition of the Karlsson–Margulis result via **horofunctions / Busemann functions**.
So Filip's "exterior-algebra route" = Route 1′'s exponent calculus for the *statement*
+ Route 3's geometry for the *general proof*. The mean / `CAT(0)` / direct-integral
versions (§5) are further generalizations (Mean MET, Mean Kingman).

---

## 3. Dependency matrix: in Mathlib vs. must be built

Mathlib status verified via the Mathlib4 DeepWiki *Dynamics and Ergodic Theory* pages
and Mathlib docs (`Mathlib.Dynamics.BirkhoffSum.*`, `Mathlib.LinearAlgebra.ExteriorPower.*`).

| Dependency | Needed by | Mathlib today | Gap |
|---|---|---|---|
| `MeasurePreserving`, `Ergodic`, `Conservative` | all | **Yes** (`Mathlib/Dynamics/Ergodic/`) | — |
| `BirkhoffSum`, `birkhoffAverage` | all | **Yes** (`Mathlib/Dynamics/BirkhoffSum/`) | definitions only |
| **Mean** ergodic theorem (L² von Neumann) | — | **Yes** | — |
| **Birkhoff POINTWISE ergodic theorem** (a.e. convergence) | 1, 1′, 2, 3 | **NO** (only `BirkhoffSum`/mean; pointwise lives in external repos, e.g. `lua-vr/pointwise-birkhoff`) | **must build / port** |
| **Kingman subadditive ergodic theorem** | 1, 2, 3 | **NO** (absent) | **must build** (Route 1′ can sidestep) |
| Furstenberg–Kesten | 1, 2 | **NO** (corollary of Kingman) | build after Kingman |
| Krylov–Bogoliubov (invariant measures, weak-* compactness) | 1′ | **Partial** (`MeasureTheory` weak-* exists; KB in families on `ℙ(V)` not packaged) | build the families version |
| Exterior powers `⋀^k`, basis, `finrank` | 1, 2, 4 | **Yes** (`Mathlib.LinearAlgebra.ExteriorPower.{Basic,Basis}`) | algebraic side good |
| Operator norm `‖·‖_op`, `GL_d`, `ContinuousLinearMap` | all | **Yes** | — |
| Singular-value / polar decomposition of matrices; `(·)^{1/2}` PD functional calculus | 1, 2 | **Partial/NO** (spectral theorem & CFC for self-adjoint exist; a packaged real-matrix SVD with ordered singular values is thin) | build SVD layer |
| `log⁺` integrability plumbing (`Integrable (max 0 (log ‖A·‖))`) | all | buildable from `MeasureTheory` | small |
| CAT(0)/Busemann nonpositive curvature, uniform convexity, geodesics, ideal boundary, horofunctions | 3, 4 | **NO** (essentially none of metric geometry of NPC spaces) | **large build** |
| Grassmannian/flag bundles, measurable subbundles, angles between subspaces, subexponential decay | 1, 1′ | **Partial** (`Grassmannian` thin; measurable selection exists) | moderate build |

**Bottom line on the common prerequisite:** every route except the metric-geometry
specifics rests on the **pointwise Birkhoff theorem**, which is *not yet in Mathlib*.
Routes 1/2/3 additionally want **Kingman**. So the first formalization milestone — for
*any* route — is pointwise Birkhoff, then Kingman.

---

## 4. Recommendation for a Lean 4 + Mathlib formalization

**Take Route 1′ (Filip's induction-on-dimension proof), one-sided first, then the
two-sided upgrade — backed by Kingman built on top of pointwise Birkhoff.**

Reasoning:

1. **Smallest novel-geometry surface.** Route 1′ lives entirely in finite-dimensional
   linear algebra + measure theory + the projective bundle. It needs *no* CAT(0) /
   Busemann / Cartan–Hadamard geometry. Routes 3 and 4 (Karlsson–Margulis / Filip
   geometric) require building essentially the whole theory of nonpositively curved
   metric spaces, geodesics, ideal boundaries and horofunctions in Mathlib — a
   multi-year prerequisite with little reuse for this single theorem. Reject 3/4 as the
   *primary* route (keep KM as the conceptual cross-check for the regularity statement).

2. **Best Mathlib leverage.** It reuses `Ergodic`, `BirkhoffSum`,
   `ExteriorPower`, operator norms, and (once added) pointwise Birkhoff. Lemma 2.3.3 is
   a convergent geometric series — pure analysis Mathlib handles well. Lemma 2.3.1's
   Krylov–Bogoliubov-in-families is the main genuinely new measure-theoretic gadget but
   is far cheaper than NPC geometry.

3. **Can defer/avoid Kingman as a monolith.** Filip's existence argument routes growth
   rates through **Birkhoff on the projective bundle**, so the heavy Kingman machinery
   is not strictly required to *exist* before the MET — though formalizing Kingman is
   still highly desirable (it is independently valuable and underpins Furstenberg–Kesten,
   and gives the cleanest top-exponent statement). Route 2 (Raghunathan), by contrast,
   front-loads the hardest analysis (convergence of `(A_n*A_n)^{1/2n}` and a full ordered
   SVD), which Mathlib does not yet support cleanly.

4. **Matches the structural distinctions cleanly.** Prove the **one-sided filtration**
   theorem first (only `log⁺‖A‖ ∈ L¹`, no invertibility); then obtain the **two-sided
   Oseledets splitting** exactly as Filip Variant 2.2.10: run the one-sided theorem for
   `T⁻¹`, intersect the forward and backward filtrations, and prove subexponential decay
   of angles (Viana §4.3.2). This keeps the two hard cases (D1/D2) cleanly separated and
   lets the two-sided invertibility hypotheses enter only at the upgrade step.

**Suggested milestone ordering for Lean:**
1. Pointwise Birkhoff ergodic theorem (`ae` convergence of `birkhoffAverage`). *(prereq, currently missing)*
2. Kingman subadditive ergodic theorem. *(prereq for FK; reuse F. Riesz "leaders" lemma as in KM §4)*
3. Furstenberg–Kesten (top exponent) as a corollary; `log⁺` integrability plumbing.
4. Linear-cocycle infrastructure: iterated cocycle `A_n`, invariant subbundles,
   projective bundle `ℙ(V)`, Krylov–Bogoliubov in families.
5. One-sided MET via Filip Lemma 2.3.1 + Lemma 2.3.3 + induction on `dim`.
6. Exterior-power exponent calculus (`⋀^k`) to identify multiplicities/spectrum.
7. Two-sided Oseledets splitting (intersect filtrations; subexponential angle decay).

---

## 5. Pitfalls / faithfulness notes

- **`log⁺`, not `log`.** The integrability condition is on `max(0, log‖A‖)` only; the
  lower tail may be `−∞`, so `λ_k = −∞` is legitimate in the one-sided theorem
  (Filip 2.2.6). Do **not** strengthen to `log ∈ L¹` — it would exclude valid cocycles.
- **Subadditivity direction.** `log‖A_{n+m}‖ ≤ log‖A_n(T^m·)‖ + log‖A_m‖`; matching
  Kingman's `g_{n+m}(x) ≤ g_n(x) + g_m(T^n x)` requires care with which side new factors
  are prepended (Filip/Viana prepend on the left: `A_n(x)=A(T^{n-1}x)···A(x)`; Zhu/some
  authors append — fix one convention).
- **Invertibility is essential only for the splitting.** The flag/filtration is the
  honest one-sided conclusion. KM Remark 2.4 gives an explicit counterexample showing
  the two-sided (bi-infinite geodesic) conclusion can fail beyond the linear case.
- **Equivariance** is part of the statement, not a corollary: the (sub)bundles satisfy
  `T_ω(V^{≤λ_i}_ω) = V^{≤λ_i}_{Tω}` (forward filtration) — must be carried explicitly.
- **Two notational conventions for the filtration** coexist: decreasing `V^i ⊋ V^{i+1}`
  (Wikipedia/Zhu) vs. increasing `V^{≤λ_k} ⊊ ··· ⊊ V^{≤λ_1}` (Filip). They are the same
  object indexed oppositely; pick the increasing-by-exponent-cap form for Lean to match
  Filip's proof.
- **Ergodicity** is assumed for constants; for the general case the exponents become
  `T`-invariant measurable functions `λ_i(x)`, `k(x)` (reduce via ergodic decomposition,
  which Mathlib supports in part).
