# Digest — Statement of the Oseledets Multiplicative Ergodic Theorem (MET)

**Source cluster:** `statement`
**Focus:** the precise statement(s) of the MET in all standard forms, exact
hypotheses (esp. the `log⁺` integrability condition), the conclusion
(Lyapunov exponents, the Oseledets splitting / filtration / flag,
equivariance), and the relation to Furstenberg–Kesten and Kingman.

**Primary sources used (raw scrapes in `docs/research/sources/`):**

1. `psu-zhu-oseledets-notes.md` — **Jairo Bochi, "The Multiplicative Ergodic
   Theorem of Oseledets" (May 27, 2008)**, lecture notes hosted on the PSU page
   `personal.science.psu.edu/jzd5895/docs/oseledets.pdf`. This is the most
   complete source: it gives both the two-sided and one-sided statements, all
   addenda, and a *full elementary proof skeleton* (Walters + Viana style, no
   exterior powers). Quotations below are transcribed from it; the OCR mangled
   sub/superscripts, so I reconstruct standard notation faithfully.
2. `scholarpedia-oseledets-theorem.md` — **V. I. Oseledets, "Oseledets
   theorem", Scholarpedia 3(1):1846 (2008)** (the author's own encyclopedia
   article). Gives the deterministic "Lyapunov regularity" formulation, the
   measurable (Theorem 3) and invertible (Theorem 4) versions, and the
   continuous-time cocycle version.
3. `wikipedia-oseledets-theorem.md` — **Wikipedia, "Oseledets theorem"** (the
   `Multiplicative_ergodic_theorem` title redirects here; the scrape
   `wikipedia-multiplicative-ergodic-theorem.md` is the identical article).
   Gives the abstract-cocycle filtration statement with the two-sided
   `log‖C‖`, `log‖C⁻¹‖` integrability hypotheses.

> Note: the assigned URL `scholarpedia.org/article/Multiplicative_ergodic_theorem`
> is an **empty page** ("There is currently no text in this page"); the real
> article lives at `.../article/Oseledets_theorem`, which I scraped instead.
> Wikipedia has **no** standalone Furstenberg–Kesten article (page does not
> exist), so the Furstenberg–Kesten statement below is taken from Bochi's
> Addendum 4.

---

## 0. Setup and notation (the linear cocycle)

Fix the dimension `d ∈ ℕ`. Let `(X, 𝓐, μ)` be a probability space and
`T : X → X` a measure-preserving transformation (m.p.t.). Fix any norm `‖·‖`
on `ℝᵈ`; use the same symbol for the induced operator norm on matrices.

Given a measurable **generator** `A : X → GL(d, ℝ)`, define the **iterated
cocycle** (Bochi writes `A⁽ⁿ⁾`):

> `A⁽⁰⁾(x) = Id`,
> `A⁽ⁿ⁾(x) = A(Tⁿ⁻¹x) · A(Tⁿ⁻²x) ⋯ A(Tx) · A(x)` for `n ≥ 1`.

(Newest factor on the **left**; this is the "matrices on the left" convention.)
This is exactly the cocycle identity over `T`:

> `A⁽ᵐ⁺ⁿ⁾(x) = A⁽ᵐ⁾(Tⁿ x) · A⁽ⁿ⁾(x)`   (Wikipedia: `C(x,t+s)=C(x(t),s)C(x,t)`,
> Scholarpedia continuous-time: `A(t+s,x)=A(t,Tˢx)A(s,x)`).

When `T` is invertible, the cocycle extends to negative times by
`A⁽⁻ⁿ⁾(x) = A(T⁻ⁿx)⁻¹ ⋯ A(T⁻¹x)⁻¹` (Scholarpedia Thm 4:
`A(t,x)=A⁻¹(Tᵗx)…A⁻¹(T⁻¹x)` for `t ≤ −1`), so that
`A⁽ⁿ⁾(x)⁻¹ = A⁽⁻ⁿ⁾(Tⁿ x)`.

Equivalent packaging (Bochi, Wikipedia): the **linear cocycle / skew-product**
`F : X × ℝᵈ → X × ℝᵈ`, `F(x, v) = (Tx, A(x)·v)`, whose `n`-th iterate is
`Fⁿ(x, v) = (Tⁿx, A⁽ⁿ⁾(x)·v)`.

**Co-norm / minimal stretch.** For a linear map `L`,
`m(L) = inf_{‖v‖=1} ‖Lv‖`; for invertible `L`, `m(L) = ‖L⁻¹‖⁻¹`. (Used to
characterize the bottom exponent.)

---

## 1. The integrability + measurability hypotheses (exact)

`log⁺ t := max(log t, 0)` for `t > 0`.

- **Measurability:** `A : X → GL(d, ℝ)` is measurable.
- **One-sided integrability (top exponent only / Furstenberg–Kesten):**
  > `log⁺ ‖A‖ ∈ L¹(μ)`,   i.e. `∫_X log⁺ ‖A(x)‖ dμ(x) < ∞`.

  This *alone* suffices for the Furstenberg–Kesten limit and for the
  one-sided **flag** version where `A` need not be invertible (Scholarpedia
  Theorem 3 needs only this; there `A : X → GL(m,ℝ)`).
- **Two-sided integrability (full MET, both flag-with-finite-limit and
  splitting):**
  > `log⁺ ‖A‖ ∈ L¹(μ)`   **and**   `log⁺ ‖A⁻¹‖ ∈ L¹(μ)`.

  Equivalently `‖log⁺‖A‖‖ + ‖log⁺‖A⁻¹‖‖` integrable; note
  `log⁻‖A‖ = log⁺‖A⁻¹‖`-bounded, and a clean equivalent form often used is
  `(log‖A‖)⁺` and `(log‖A‖)⁻` (= `(log ‖A⁻¹‖)⁺` up to `m(A)`) both integrable,
  i.e. `x ↦ max(‖A(x)‖, ‖A(x)⁻¹‖)` has integrable log. Wikipedia states it as
  `x ↦ log‖C(x,t)‖` and `x ↦ log‖C(x,t)⁻¹‖` both `L¹`.

**Why both are needed.** `log⁺‖A‖ ∈ L¹` bounds growth from above and gives the
top exponent finite a.e.; adding `log⁺‖A⁻¹‖ ∈ L¹` bounds *contraction* (bounds
the bottom exponent `λ_k` from below, makes `m(A⁽ⁿ⁾)` controllable) and makes
the lim **exist** (not merely lim sup) and, for invertible `T`, makes the
two-sided limits `n → ±∞` agree. The condition `log⁺‖A⁻¹‖ ∈ L¹` is also what
makes `log‖A‖ + log‖A⁻¹‖` integrable, which is the integrand controlling the
sub-exponential angle/coboundary estimates (Bochi, Addendum 5, Lemma 6).

**Ergodicity.** All "clean" statements below assume `μ` is **ergodic** for
`T`; then the exponents `λᵢ` and multiplicities `dᵢ` are *constants*. Without
ergodicity (Bochi, Exercise i) the same holds with the `λᵢ`, `k`, `dᵢ`
becoming measurable `T`-invariant a.e.-defined functions (via the ergodic
decomposition).

---

## 2. The exact statements, by version

### 2.1 Two-sided / invertible — DIRECT-SUM (Oseledets) SPLITTING form

> **Theorem 1 (Bochi; = Oseledets MET, two-sided).** Let `T` be an *invertible
> bimeasurable ergodic* transformation of the probability space `(X, μ)`. Let
> `A : X → GL(d, ℝ)` be measurable such that `log⁺‖A‖` and `log⁺‖A⁻¹‖` are
> integrable. Then there exist numbers
> > `λ₁ > λ₂ > ⋯ > λ_k`   (1)
>
> and for `μ`-almost every `x ∈ X` there exists a splitting
> > `ℝᵈ = E¹ₓ ⊕ E²ₓ ⊕ ⋯ ⊕ E_kₓ`   (2)
>
> such that for every `1 ≤ i ≤ k`,
> > `A(x) · Eⁱₓ = Eⁱ_{Tx}`   (equivariance)
>
> and
> > `lim_{n→±∞} (1/n) log‖A⁽ⁿ⁾(x)·vᵢ‖ = λᵢ`   for all non-zero `vᵢ ∈ Eⁱₓ`.  (3)
>
> The subspaces `Eⁱₓ` are unique `μ`-a.e. and depend measurably on `x`. The
> `λᵢ` are the **Lyapunov exponents**; (2) is the **Lyapunov / Oseledets
> splitting**. The dimensions `dᵢ = dim Eⁱₓ` are a.e. constant (forced by
> equivariance + ergodicity), and `d₁ + ⋯ + d_k = d`.

**Measurability of the bundles (Bochi, exact):** there exist measurable maps
`u₁, …, u_d : X → ℝᵈ` such that for each `i`, `Eⁱₓ` is spanned by the vectors
`u_j(x)` with `d₁+⋯+d_{i−1} < j ≤ d₁+⋯+dᵢ`.

**Scholarpedia Theorem 4 (same content, Oseledets's wording):** for `μ`-a.e.
`x`, `t ↦ A(t,x)` is Lyapunov regular as `t → ±∞`; there is a measurable
splitting `ℝᵐ = E_{k₁}(x) ⊕ ⋯ ⊕ E_{k_r}(x)` with
`lim_{t→±∞} (1/t) log‖A(t,x)e‖ = χᵢ(x)` for `0 ≠ e ∈ E_{kᵢ}(x)`,
`dim E_{kᵢ}(x) = kᵢ(x)`; uniform on subspaces:
`lim_{t→±∞} (1/t) log λ(eᵏ) = k·χᵢ(x)` uniformly over `eᵏ ⊂ E_{kᵢ}(x)`;
sub-exponential angles `lim_{t→±∞}(1/t) log sin(∠(E_{kᵢ}(Tᵗx), E_{kⱼ}(Tᵗx))) = 0`,
`i ≠ j`; and `T`-equivariance `χᵢ(Tx)=χᵢ(x)`, `kᵢ(Tx)=kᵢ(x)`,
`E_{kᵢ(x)}(Tx) = A(x)E_{kᵢ}(x)`. Oseledets calls the `E_{kᵢ}(x)` the
**Oseledets subspaces**.

> **Invertibility is essential for the splitting.** Bochi flags this explicitly:
> the construction of an *invariant complement* (his Lemma 14, the graph-transform
> fixed point) is "the first time we need `T` to be invertible". The one-sided
> theory only yields the nested flag (next subsection); turning the flag into a
> direct sum requires running the cocycle backwards.

### 2.2 One-sided / non-invertible — FILTRATION (Lyapunov flag) form

> **Theorem 2 (Bochi; one-sided MET).** Let `T` be an *ergodic* (not necessarily
> invertible) transformation of `(X, μ)`. Let `A : X → GL(d, ℝ)` be measurable
> with `log⁺‖A‖` and `log⁺‖A⁻¹‖` integrable. Then there exist numbers
> `λ₁ > ⋯ > λ_k` and for `μ`-a.e. `x` there exists a **flag**
> > `ℝᵈ = V¹ₓ ⊃ V²ₓ ⊃ ⋯ ⊃ V_kₓ ⊃ V_{k+1}ₓ = {0}`   (4)
>
> depending measurably on the point and invariant by the cocycle, such that
> > `lim_{n→∞} (1/n) log‖A⁽ⁿ⁾(x)·vᵢ‖ = λᵢ`   for all `vᵢ ∈ Vⁱₓ ∖ V^{i+1}ₓ`.  (5)
>
> Call (4) the **Lyapunov flag** of the cocycle.

**Relation between the two forms (Bochi, Exercise iii — exact):** when `T` is
invertible, the flag is recovered from the splitting by
> `Vⁱₓ = Eⁱₓ ⊕ E^{i+1}ₓ ⊕ ⋯ ⊕ E_kₓ`,

i.e. `Vⁱ` collects all directions whose forward exponent is `≤ λᵢ`. (Note the
*decreasing* indexing convention: `V¹` is everything, `V_k` is the slowest /
bottom bundle, with the `λᵢ` listed in **decreasing** order `λ₁ > ⋯ > λ_k`.)

> **Two indexing conventions appear in the literature — beware.** Bochi and
> Wikipedia order exponents **decreasingly** `λ₁ > ⋯ > λ_k` and define `Vⁱ` as
> `{v : exponent ≤ λᵢ}`, giving the nested chain `ℝᵈ = V¹ ⊃ ⋯ ⊃ V_k ⊃ 0`.
> Scholarpedia/Oseledets order exponents **increasingly** `χ₁ < χ₂ < ⋯ < χ_r`
> and define `Lᵢ = {e : χ(e) ≤ χᵢ}`, giving the *ascending* chain
> `0 = L₀ ⊂ L₁ ⊂ ⋯ ⊂ L_r = ℝᵐ` with `dim Lᵢ − dim L_{i−1} = kᵢ` the
> multiplicity. These are the same object; only the direction of the inclusions
> and the sign convention of the ordering differ. **For formalization, pick one
> and state it once.**

**One-sided lim-sup precursor (Bochi, Lemma 8 — exact construction of the flag):**
define `λ̄(x,v) = lim sup_{n→∞} (1/n) log‖A⁽ⁿ⁾(x)·v‖` for `v ≠ 0`. Integrability
of `log⁺‖A^{±1}‖` makes `λ̄(x,v)` finite a.e. for all `v ≠ 0`. Then
`λ̄(x, av) = λ̄(x,v)` and `λ̄(x, v+w) ≤ max(λ̄(x,v), λ̄(x,w))` with equality when
`λ̄(x,v) ≠ λ̄(x,w)`. Hence for each `t`, `Vₓ(t) = {v : λ̄(x,v) ≤ t} ∪ {0}` is a
**linear subspace**, vectors of distinct `λ̄` are independent, so `λ̄(x,·)` takes
at most `d` values `λ₁(x) > ⋯ > λ_{k(x)}(x)`, and `Vⁱₓ := Vₓ(λᵢ(x))`. (This is
"the flag with lim sup"; the work of the theorem is upgrading `lim sup` to an
honest two-sided `lim`.)

### 2.3 Abstract-cocycle filtration form (Wikipedia)

For a cocycle `C : X × T → ℝⁿˣⁿ` (`T = ℤ⁺` or `ℝ⁺`) over an ergodic invariant
`μ`, with `x ↦ log‖C(x,t)‖` and `x ↦ log‖C(x,t)⁻¹‖` both `L¹(μ)` for each `t`:
for `μ`-a.e. `x` and each non-zero `u ∈ ℝⁿ`,
> `λ = lim_{t→∞} (1/t) log( ‖C(x,t)u‖ / ‖u‖ )`

exists and takes (depending on `u`, **not** on `x`) up to `n` distinct values —
the Lyapunov exponents. If `λ₁ > ⋯ > λ_m` are the distinct values, there are
subspaces `ℝⁿ = R₁ ⊃ ⋯ ⊃ R_m ⊃ R_{m+1} = {0}` (depending on `x`) with the limit
equal to `λᵢ` for `u ∈ Rᵢ ∖ R_{i+1}`. (This is the flag form again; Wikipedia
states the *values* `λᵢ` are `x`-independent and exponent values are invariant
under `C¹` coordinate changes `g : X → X`.)

### 2.4 Deterministic "Lyapunov regularity" core (Scholarpedia, Theorems 1–2)

For a single sequence `A₀, A₁, …` of nonsingular `m×m` matrices with
`(1/t)log‖A_t‖ → 0` and `A(t) = A_{t−1}⋯A₀`, define the (lim sup) exponent
`χ(e) = lim sup (1/t) log‖A(t)e‖` of a nonzero vector, and for a `k`-dim
subspace `eᵏ` the exponent `χ(eᵏ) = lim sup (1/t) log λ(t, eᵏ)` where
`λ(t,eᵏ) = |det(A(t)|_{eᵏ})|`. `χ` takes values `χ₁ < ⋯ < χ_r`, with the
ascending filtration `Lᵢ` and multiplicities `kᵢ` as in §2.2. The sequence is
**Lyapunov regular** iff
> `∑_{i=1}^r kᵢ χᵢ = lim (1/t) log |det A(t)|`.

- **Theorem 1.** If `A(t)` is Lyapunov regular then exponents of all orders are
  *exact*: `χ(eᵏ) = lim (1/t) log λ(t, eᵏ)` (lim sup is a genuine lim).
- **Theorem 2.** If `A(t)` is Lyapunov regular then (i)
  `lim (A*(t)A(t))^{1/(2t)} = Λ`, a diagonal matrix; (ii) `exp(χ₁), …, exp(χ_r)`
  are the distinct eigenvalues of `Λ` with multiplicities `kᵢ`; (iii)
  `lim (1/t) log‖A(t)Λ^{−t}‖ = 0`.
- **Theorem 3 (measurable / ergodic, one-sided).** `t ↦ A(t,x)` is Lyapunov
  regular for `μ`-a.e. `x` (given `log⁺‖A‖ ∈ L¹`), `Λ = Λ(x)` measurable, and
  the filtration `L₁(x) ⊂ ⋯ ⊂ L_r(x) = ℝᵐ` measurable.

The `(A*A)^{1/(2t)} → Λ` content is the **singular-value / symmetric-cocycle**
viewpoint: `exp(χᵢ)` are the limiting singular value growth rates; this is the
"conventional" proof route via exterior powers that Bochi contrasts with his
elementary route (see §4).

### 2.5 Continuous-time version (Scholarpedia)

`A : ℝ × X → GL(m, ℝ)` is a cocycle over a measurable measure-preserving flow
`{Tᵗ}` (`Tᵗ⁺ˢ = TᵗTˢ`) iff `A(t+s, x) = A(t, Tˢx)A(s, x)`. If
`sup{ log⁺‖A(t,x)‖ : −1 ≤ t ≤ 1 }` is integrable, the analogues of Theorems 3–4
hold. (Examples: derivative cocycles of deterministic and stochastic flows.)

---

## 3. Top/bottom exponents, Furstenberg–Kesten, and the addenda

### 3.1 Furstenberg–Kesten = top Lyapunov exponent (Bochi, Addendum 4)

Kingman's subadditive ergodic theorem applied to `φ_n(x) = log‖A⁽ⁿ⁾(x)‖`
(subadditive: `φ_{m+n} ≤ φ_n∘Tᵐ + φ_m` because
`‖A⁽ᵐ⁺ⁿ⁾(x)‖ ≤ ‖A⁽ᵐ⁾(Tⁿx)‖·‖A⁽ⁿ⁾(x)‖`) gives the **Furstenberg–Kesten** limit
> `lim_{n→∞} (1/n) log‖A⁽ⁿ⁾(x)‖`   exists a.e. and `= λ₁` (top exponent),

and `= inf_n (1/n) ∫ log‖A⁽ⁿ⁾‖ dμ`. Bochi's Addendum 4 (exact):
> `λ₁ = lim_{n→+∞} (1/n) log‖A⁽ⁿ⁾(x)‖ = lim_{n→−∞} (1/n) log m(A⁽ⁿ⁾(x))`,
> `λ_k = lim_{n→+∞} (1/n) log m(A⁽ⁿ⁾(x)) = lim_{n→−∞} (1/n) log‖A⁽ⁿ⁾(x)‖`,

where `m(·)` is the co-norm. So the **top** exponent `λ₁` is the forward growth
rate of `‖A⁽ⁿ⁾‖` and the **bottom** exponent `λ_k` is the forward growth rate of
the co-norm `m(A⁽ⁿ⁾) = ‖(A⁽ⁿ⁾)⁻¹‖⁻¹` (i.e. of the smallest singular value).
Furstenberg–Kesten is *the* `d = 1`-flavored / norm-only fragment of the MET and
is logically prior in the proof.

### 3.2 Determinant / sum-of-exponents (Bochi, Exercise vi)

For `∅ ≠ J ⊂ {1,…,k}` and `F_x = ⊕_{j∈J} Eʲₓ`,
> `lim_{n→±∞} (1/n) log |det( A⁽ⁿ⁾(x)|_{F_x} )| = ∑_{j∈J} λⱼ · dim Eʲ`.

In particular `lim (1/n) log|det A⁽ⁿ⁾(x)| = ∑ⱼ dⱼ λⱼ` (trace formula; this is
exactly Scholarpedia's Lyapunov-regularity equality `∑ kᵢ χᵢ`).

### 3.3 Sub-exponential angles (Bochi, Addendum 5; Scholarpedia Thm 4)

For any nontrivial partition `J₁ ⊔ J₂ = {1,…,k}` with `Fⁱ = ⊕_{j∈Jᵢ} Eʲ`,
> `lim_{n→±∞} (1/n) log sin ∠( F¹_{Tⁿx}, F²_{Tⁿx} ) = 0`   a.e.

i.e. the Oseledets subspaces stay "sub-exponentially transverse" along orbits.
Proof input: `φ(x) = log sin∠(F¹ₓ, F²ₓ)` satisfies
`|φ(Tx) − φ(x)| ≤ log‖A(x)‖ + log‖A(x)⁻¹‖ ∈ L¹` (Exercise iv), then Lemma 6.

### 3.4 Uniformity (Bochi, Addendum 7)

For a.e. `x` the convergence in (3) is **uniform over unit vectors in `Eⁱₓ`**.

---

## 4. Proof skeleton (Bochi's elementary route — Walters + Viana, no exterior powers)

Bochi proves the **one-sided Theorem 2** first, then upgrades to the
**two-sided Theorem 1** by constructing invariant complements. The route is a
combination of Walters (1982, "A dynamical proof of the MET", `[W]`, one-sided)
and Viana/Mañé (`[V]`,`[M]`, two-sided). Distinctive feature: it routes through
Kingman + a Krylov–Bogolyubov compactness argument rather than exterior powers.

Ordered steps (each with its key lemma and dependencies):

1. **Finiteness + lim-sup flag (Lemma 8).** Build `λ̄(x,v)`, show it is finite
   a.e. and takes finitely many values; produce the measurable invariant flag
   `V¹ ⊃ ⋯ ⊃ V_k` with `λ̄(x,v) = λᵢ` on `Vⁱ ∖ V^{i+1}`.
   *Depends on:* `log⁺‖A^{±1}‖ ∈ L¹` (finiteness); elementary linear algebra of
   the function `λ̄` (subadditivity/scaling). *Mathlib needs:* `limsup` of a
   real sequence, subspace `{v : limsup ≤ t}`.

2. **Coboundary/Birkhoff lemma (Lemma 6).** If `φ : X → ℝ` with `φ∘T − φ`
   integrable (extended sense), then `lim_{n→±∞} (1/|n|) φ(Tⁿx) = 0` a.e.
   *Depends on:* Birkhoff's pointwise ergodic theorem + Poincaré recurrence.
   *Used by:* angle addendum (5), the tempering lemma (12), graph transform (14).
   *Mathlib status:* Birkhoff (`MeasureTheory.Birkhoff…` / ergodic averages) and
   Poincaré recurrence (`MeasureTheory.Conservative.…`) are present.

3. **Furstenberg–Kesten via Kingman (Theorem 3 / Addendum 4).** Apply Kingman's
   subadditive ergodic theorem to `φ_n = log‖A⁽ⁿ⁾‖` to get the top-exponent
   limit; dually to `−log m(A⁽ⁿ⁾)` for the bottom. *Depends on:* **Kingman's
   subadditive ergodic theorem** (the central analytic input). *Mathlib status:*
   **Kingman is NOT yet in Mathlib** — this is the main missing prerequisite.

4. **Krylov–Bogolyubov upgrade of lim sup to uniform lim (Lemma 9 / Cor 10).**
   On a skew-product `S : X × P → X × P` over `T` with `P` compact metric, for
   `ψ` in the separable Banach space `𝓕` of fibrewise-continuous functions with
   `∫ sup_u|ψ| < ∞`: if `lim sup (1/n) ψ⁽ⁿ⁾(x,u) ≥ c` for all `u`, the same holds
   with a `lim inf` *uniform over `P`*. *Depends on:* compactness of the space of
   `S`-invariant probability measures projecting to `μ` (Exercise ix),
   measurable selection (Exercise x), Kingman (applied to `inf_u ψ⁽ⁿ⁾`),
   Birkhoff. *Mathlib needs:* weak-* compactness of invariant measures,
   measurable selection — both partially present.

5. **Bottom bundle has an honest two-sided limit (Lemma 11).** Let `E = V_k`
   (bundle of least stretch, `λ_min = λ_k`). Using Lemma 9/Cor 10 on the induced
   projective skew-product, upgrade the lim sup on `E` to a uniform two-sided
   `lim`, and show `lim (1/n) log‖A⁽ⁿ⁾|_E‖ = lim (1/n) log m(A⁽ⁿ⁾|_E) = λ_min`.
   *Depends on:* steps 1, 3, 4; reduction to `ℝᵐ ⊂ ℝᵈ` via a measurable
   orthogonal conjugation `C : X → O(d,ℝ)`.

6. **Tempering / Pliss-type bound (Lemma 12).** For measurable `B` with
   `log⁺‖B‖ ∈ L¹` and `lim sup (1/n)‖B⁽ⁿ⁾‖ ≤ γ`: for each `ε > 0` there is a
   measurable `b_ε ≥ 0` with `‖B⁽ⁿ⁾(Tⁱx)‖ ≤ b_ε(x) e^{(γ+ε)n + ε|i|}`.
   *Depends on:* Lemma 6 (to kill the `c(Tⁱx)` factor sub-exponentially).
   This is the **tempered/tempering Lemma** (a.k.a. Tempering Kernel Lemma).

7. **Block triangularization / next exponent (Lemma 13 + Exercise xii).** Split
   `ℝᵈ = E⊥ ⊕ E` (orthogonal), write `A = [[B, 0],[C, A|_E]]`; show
   `λ_min(B) = λ_{k−1}` and that `F = V_{k−1}` (the penultimate flag space). The
   off-diagonal `C` is controlled by Lemma 12. **Induction** on this proves the
   one-sided **Theorem 2** in full (genuine limits on each flag layer).
   *Depends on:* steps 5, 6; co-norm monotonicity `m(B⁽ⁿ⁾) ≥ m(A⁽ⁿ⁾)`.

8. **Invariant complement = the splitting (Lemma 14).** *(First use of
   invertibility.)* Find a measurable **invariant** complement `G` to `E`
   (`G ⊕ E = ℝᵈ`, `A`-invariant) as a fixed point of the **graph transform**
   `Γ L = D + Φ L` on the Banach bundle of linear maps `E⊥ → E`; the fixed point
   is `L = ∑_{n≥0} Φⁿ D`, convergent because `‖ΦⁿD(x)‖ ≤ a(x) e^{(λ_k − λ_{k−1})n}`
   (exponential gap `λ_k < λ_{k−1}`) via three applications of Lemma 12.
   *Depends on:* steps 6, 7, the spectral gap, **invertibility of `T`** (to run
   `T⁻¹`, `B⁻¹`).

9. **Assemble the splitting (Theorem 1 + Addendum 7).** Set `E_k = V_k`; by
   Lemma 11, (3) holds for `i = k`. If `k = 1` done; else use Lemma 14 to get
   invariant `G` complementary to `E_k`, restrict the cocycle to `G` (whose flag
   is `V¹∩G ⊃ ⋯ ⊃ V_{k−1}∩G ⊃ 0` with exponents `λ₁ > ⋯ > λ_{k−1}`), set
   `E_{k−1} = V_{k−1} ∩ G`, and **recurse downward** to obtain the full direct
   sum `E¹ ⊕ ⋯ ⊕ E_k`. Uniformity (Addendum 7) falls out of Lemma 11.

**Dependency summary (bottom layer → top):**
`Birkhoff ergodic thm` + `Poincaré recurrence` ⟶ Lemma 6;
`Kingman subadditive ergodic thm` ⟶ Furstenberg–Kesten (Addendum 4) & Lemma 9;
`Krylov–Bogolyubov` (compactness of invariant measures) + `measurable selection`
⟶ Lemma 9/Cor 10 ⟶ Lemma 11; Lemma 6 ⟶ Lemma 12 ⟶ Lemma 13 (⟹ **Theorem 2,
one-sided, by induction**) and Lemma 14 (needs **invertibility**) ⟹ **Theorem 1,
two-sided splitting**.

**Alternative (conventional) route — Scholarpedia / Arnold / Ledrappier.** Use
exterior powers `Λᵏℝᵈ` and singular values: study the symmetric cocycle and show
`(A⁽ⁿ⁾(x)* A⁽ⁿ⁾(x))^{1/(2n)} → Λ(x)` (Scholarpedia Thm 2), whose log-eigenvalues
are the exponents with multiplicities; the flag/splitting come from the
eigenspaces of `Λ`. Raghunathan's proof also uses Kingman. Bochi notes this gives
"more useful information" but needs heavier linear algebra. For Mathlib this
route needs exterior powers / singular value decomposition / polar decomposition
infrastructure.

---

## 5. Quick comparison table (for the formalization plan)

| Aspect | One-sided (Thm 2 / Scholarpedia Thm 3) | Two-sided / invertible (Thm 1 / Scholarpedia Thm 4) |
|---|---|---|
| `T` | ergodic m.p.t., **not** necessarily invertible | **invertible** bimeasurable ergodic m.p.t. |
| Integrability | `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹` (Scholarpedia Thm 3 needs only `log⁺‖A‖`) | `log⁺‖A‖` **and** `log⁺‖A⁻¹‖ ∈ L¹` |
| Conclusion geometry | nested **flag** `ℝᵈ = V¹ ⊃ ⋯ ⊃ V_k ⊃ 0` (asc. `L₀⊂⋯⊂L_r` in Oseledets) | **direct-sum splitting** `ℝᵈ = E¹ ⊕ ⋯ ⊕ E_k` |
| Limit in (3)/(5) | `lim_{n→+∞}` only | `lim_{n→±∞}` (both agree) |
| Equivariance | `A(x)Vⁱₓ ⊆ Vⁱ_{Tx}` (invariant flag) | `A(x)Eⁱₓ = Eⁱ_{Tx}` (equivariant splitting) |
| Relation | `Vⁱ = Eⁱ ⊕ ⋯ ⊕ E_k` when invertible | refines the flag |
| Extra | — | sub-exp. angles, uniform `det` growth, unique a.e. `Eⁱ` |

---

## 6. Formalization-relevant remarks (for the planner)

- **Domain choices.** All sources are stated for `A : X → GL(d, ℝ)` (real). The
  cleanest first target is the **one-sided flag** (Theorem 2 / Scholarpedia
  Thm 3): it avoids inverting `T` (only `A` is inverted, and only its `log⁺` is
  needed). The **direct-sum splitting** (Theorem 1 / Thm 4) genuinely requires
  invertible `T` — defer it.
- **Hardest pieces:** (i) **Kingman's subadditive ergodic theorem** — *not in
  Mathlib*, must be formalized or assumed; it is the linchpin (Furstenberg–Kesten
  and Lemma 9 both need it). (ii) The Krylov–Bogolyubov compactness + measurable
  selection in Lemma 9. (iii) The graph-transform fixed point (Lemma 14) for the
  splitting.
- **Easier pieces that Mathlib likely supports:** Birkhoff pointwise ergodic
  theorem and Poincaré recurrence (Lemma 6); basic `GL(d,ℝ)`, operator norm,
  `limsup`/`liminf`, measurable functions; subspaces `{v : limsup ≤ t}`.
- **Watch the conventions:** (a) decreasing `λ₁>⋯>λ_k` (Bochi/Wiki) vs increasing
  `χ₁<⋯<χ_r` (Oseledets); (b) flag inclusion direction; (c) cocycle factor order
  (newest factor on the left here); (d) `log⁺` = `max(log, 0)`; (e) co-norm
  `m(L) = ‖L⁻¹‖⁻¹` characterizes the bottom exponent.
- **Statement to formalize first (recommended):** the existence of a.e.-constant
  `λ₁ > ⋯ > λ_k`, an `A`-invariant measurable flag, and the genuine forward
  limit (5) — equivalently the Furstenberg–Kesten top-exponent statement
  (`lim (1/n) log‖A⁽ⁿ⁾‖ = λ₁` a.e.) as the minimal milestone, since it isolates
  the Kingman dependency.
