# Digest — Filip's "Notes on the Multiplicative Ergodic Theorem" (source cluster: filip-notes)

**Primary source.** Simion Filip, *Notes on the Multiplicative Ergodic Theorem*,
arXiv:1710.10694v1 [math.DS], revised 31 Oct 2017. Based on lectures at summer
schools in Brazil, France, Russia.
Raw scrape: `/workspaces/lean4-oseledets/docs/research/sources/filip-2017-notes-MET.md`

**Companion source.** Amit Wolecki, *Oseledets' Theorem* (TAU seminar notes,
18 Aug 2019), which "closely follow Simion Filip's published notes" and expand
Filip's Section 2 with more detail.
Raw scrape: `/workspaces/lean4-oseledets/docs/research/sources/amit-oseledets-seminar-notes.md`

Both sources are tightly coupled, so this digest treats them as one cluster: Amit
is essentially a worked-out exposition of Filip §2 (the classical/elementary
proof). Where they differ (extra detail), it is flagged.

---

## 0. Two distinct proofs in Filip's notes

Filip gives **two** independent proofs of the MET. This is the single most
important structural fact for the formalization plan.

| | **Proof A — elementary (Filip §2 / all of Amit)** | **Proof B — geometric (Filip §3, §3.5)** |
|---|---|---|
| Main engine | Birkhoff pointwise ergodic theorem + Krylov–Bogoliubov + Krein–Milman | **Kingman subadditive ergodic theorem** + Birkhoff |
| Uses Kingman? | **No** — explicitly avoids it | **Yes** — central |
| Uses exterior powers ⋀ᵏ? | No | **Yes** — to extract all exponents from top exponents |
| Uses singular values / polar (KAK) decomposition? | No | **Yes** — Cartan projection, σᵢ |
| Structure | Induction on dim V, two lemmas, contraction on projective bundle | Reduces MET to a statement about *regular sequences* in the symmetric space GLₙ(ℝ)/Oₙ(ℝ); Kaimanovich's criterion |
| Output | Forward filtration directly | Cartan projection converges ⇒ all exponents; equivalence Prop 3.4.8 |

Filip's own framing (Introduction, "Outline"): *"The presented proof [§2] is based
on some geometric arguments and avoids the Kingman subadditive ergodic theorem."*
The geometric proof (§3.5) instead *"will make use of the Subadditive Ergodic
Theorem."*

For Lean formalization, **Proof A is the more self-contained route** if Mathlib
already has Birkhoff but not Kingman; **Proof B is shorter and more conceptual**
but rests on Kingman + a fair amount of Lie-theory/symmetric-space machinery
(the latter mostly avoidable if one stays at the level of singular values).

---

## 1. Ergodic-theory background (Filip §2.1, Amit §1.1)

### 1.1 Probability measure-preserving system (p.m.p.s.)
Let `Ω` be a separable, second-countable metric space, `B` its Borel σ-algebra,
`μ` a probability measure, `T : Ω → Ω` measurable. Push-forward
`T∗μ(A) := μ(T⁻¹(A))`. `μ` is **T-invariant** if `T∗μ = μ`. Then `(Ω,B,μ,T)` is a
**probability measure-preserving system**, written `T ↷ (Ω,μ)`.

### 1.2 Ergodicity
`(Ω,B,μ,T)` is **ergodic** if every measurable T-invariant set has measure 0 or 1:
`T⁻¹(A) = A ⇒ μ(A) ∈ {0,1}`.

### 1.3 Birkhoff Pointwise Ergodic Theorem (Filip Thm 2.1.3, Amit Thm 1.3)
> Assume `T ↷ (Ω,μ)` ergodic and `f ∈ L¹(Ω,μ)`. Then for μ-a.e. `ω`:
> `lim_{N→∞} (1/N) Σ_{i=0}^{N-1} f(Tⁱω) = ∫_Ω f dμ`.

**Relaxed integrability (Filip Rmk 2.1.4):** write `f = f₊ + f₋` with `f₊ ≥ 0`,
`f₋ ≤ 0`. If only `f₊ ∈ L¹`, the conclusion still holds with `-∞` allowed as the
limit. (This is exactly the integrability regime the MET hypothesis lives in.)

**Multiplicative variant (Filip 2.1.5):** with `g := exp(f)`,
`lim_N (g(ω)g(Tω)···g(T^{N-1}ω))^{1/N} = exp(∫_Ω log g dμ)`.

### 1.4 Kingman Subadditive Ergodic Theorem (Filip Thm 3.5.2 — needed ONLY for Proof B)
> Let `T ↷ (Ω,μ)` ergodic. Let `{fᵢ}` be functions with `f₁ ∈ L¹(Ω,μ)` and the
> **subadditivity condition**
> `f_i(ω) + f_j(Tⁱω) ≥ f_{i+j}(ω)  ∀ω, ∀i,j ≥ 1.   (3.5.3)`
> Then for μ-a.e. `ω`, `lim_{N→∞} (1/N) f_N(ω)` exists (possibly `-∞`) and equals
> `inf_N (1/N) ∫_Ω f_N dμ`.

Filip's note after the statement: integrating (3.5.3) shows each `f_i` is bounded
above by an `L¹` function, hence is (`L¹` function) + (everywhere-negative
function). Companion: **Fekete's lemma** (Filip 3.5.4): for a subadditive *sequence*
`a_{n+m} ≤ a_n + a_m`, `lim_N a_N/N = inf_N a_N/N` (possibly `-∞`). Kingman is the
"random/ergodic Fekete."

---

## 2. Setup: vector bundles and cocycles

### 2.1 Vector bundle (Amit Def 1.6)
`V → (Ω,B,μ,T)` of dimension `d`: a space `V` with continuous surjection
`π : V → Ω` such that each fiber `V_ω := π⁻¹({ω})` is a `d`-dim ℝ-vector space, with
local trivializations `φ : U × ℝᵈ → π⁻¹(U)` linear-iso on fibers. Filip's
gluing-cocycle definition (§2.2.2): cover `{U_α}`, gluing maps
`φ_{α,β} : U_α ∩ U_β → GLₙℝ` with `φ_{γ,α}·φ_{β,γ}·φ_{α,β} = 1`. **Any vector bundle
can be measurably trivialized** (≅ Ω × ℝⁿ), so for formalization one may WLOG take
the trivial bundle and a measurable map `Ω → GL_d`.

### 2.2 Cocycle (Filip §2.2.3, Amit Def 1.7–1.8)
**Filip's "bundle" form:** `V` is a cocycle over `T` if the `T`-action lifts to `V`
by linear maps `T_ω : V_ω → V_{Tω}` varying measurably; **assume `T_ω` always
invertible** (Filip states this in §2.2.3; it is used pervasively, e.g. in the
projective-bundle T-invariance argument).

**Amit's explicit cocycle map form** (Def 1.7): `α : ℤ_{≥0} × Ω → GL(d,ℝ)` with
> `α(m+n, x) = α(m, Tⁿx) ∘ α(n, x).   (1)`

For invertible `T`, extend to `α : ℤ × Ω → GL(d,ℝ)` with (1) for all `m,n ∈ ℤ`.
The induced fiber maps satisfy the **chain rule**
`(T^N)_ω = T_{T^{N-1}ω} ∘ ··· ∘ T_ω`, i.e. `T^N v` means the N-step product.

### 2.3 Subbundle / invariance / quotient / exact sequences (Amit Def 2.2–2.5)
- `W ⊂ V` is a **subbundle** of dim `d' ≤ d`; **T-invariant** if `T_ω W_ω = W_{Tω}`.
- Bundle morphism `f : V → W`: commutes with projections (`π₁ = π₂∘f`) and is fiberwise
  linear. Kernel = preimage of zero bundle.
- Quotient `(V/E)_ω := V_ω/E_ω`; direct sum `(V⊕W)_ω := V_ω ⊕ W_ω`.
- **Short exact sequence** `0 → E → V → F → 0` (fiberwise exact).
- **Exponents are additive over exact sequences (Filip 2.2.9(iii), Amit Note 2.6):**
  in `W → V → V/W`, the exponents of `V` are the union (with multiplicity) of those
  of `W` and `V/W`.
- **Inherited integrability (Filip Rmk 2.3.2, Amit Rmk 2.10):** if `E ⊂ V` is an a.e.
  T-invariant subbundle, the integrability condition (2.2.7) holds for `E` and `V/E`
  with the natural norms.

### 2.4 Metric convention (Filip Rmk 2.2.5)
A "metric" on a vector space/bundle = symmetric positive-definite bilinear form
= positive-definite inner product. Real and complex (Hermitian) cases both work
(Filip Rmk 3.1.4(iii)); Lyapunov exponents are real in both.

---

## 3. Theorem statements (precise)

### 3.1 One-sided / forward MET (Filip Thm 2.2.6, Amit Thm 1.12)
> **Hypotheses.** `V → (Ω,B,μ,T)` a cocycle over an **ergodic** p.m.p.s. Each fiber
> carries a metric `‖−‖`. **Integrability condition:**
> `∫_Ω log⁺ ‖T_ω‖_op dμ(ω) < ∞     (2.2.7)`
> where `log⁺(x) := max(0, log x)` and `‖−‖_op` is the operator norm.
>
> **Conclusion.** There exist real numbers `λ₁ > λ₂ > ··· > λ_k` (with possibly
> `λ_k = -∞`) and **T-invariant subbundles** of `V`, defined for a.e. `ω`, forming a
> strict **filtration**
> `0 ⊊ V^{≤λ_k} ⊊ ··· ⊊ V^{≤λ_1} = V`
> such that for `v ∈ V^{≤λ_i}_ω \ V^{≤λ_{i+1}}_ω`:
> `lim_{N→∞} (1/N) log ‖T^N v‖ = λ_i.   (2.2.8)`
> The limit is **uniform** over `{v : ‖v‖ = 1}` in a fixed fiber `V^{≤λ_i}_ω \ V^{≤λ_{i+1}}_ω` (Amit's statement makes this uniformity explicit).

**Terminology (Filip Rmk 2.2.9, Amit Note 1.13):**
- `V^{≤λ_•}` is the **forward Oseledets filtration**.
- `λ_i` are the **Lyapunov exponents**.
- **Multiplicity** of `λ_i` := `dim V^{≤λ_i} − dim V^{≤λ_{i+1}}`. Exponents are often
  relisted with multiplicity as `λ₁ ≥ ··· ≥ λ_d`.
- The filtration and exponents are **canonical**: they are *defined* by the growth
  property (2.2.8).

Note the **one-sided version requires only forward integrability of `T_ω`** and
yields only a *filtration* (nested subspaces), **not** a direct-sum splitting.
`T_ω` is still assumed invertible as maps, but `T` need not be an invertible
transformation of `Ω`.

### 3.2 Two-sided / invertible MET — the Oseledets splitting (Filip Variant 2.2.10, Amit Note 2.1)
> Now assume `T : Ω → Ω` is **invertible** and the cocycle for `T⁻¹` satisfies the
> *same* hypotheses. Applying the forward theorem to `T⁻¹` gives `k'` exponents `η_j`
> and a **backward Oseledets filtration** `V^{≤η_{k'}} ⊊ ··· ⊊ V^{≤η_1}` with
> `lim_{N→∞} (1/N) log ‖T^{-N} v‖ = η_j` for `v ∈ V^{≤η_j} \ V^{≤η_{j+1}}`.
>
> Compatibility with forward behavior forces `η_j = -λ_{k+1-j}` and `k' = k`.
> Defining
> `V^{λ_j} := V^{≤λ_j} ∩ V^{≤η_{k+1-j}}`
> gives a **T-invariant direct-sum decomposition (Oseledets splitting)**
> `V = V^{λ_1} ⊕ ··· ⊕ V^{λ_k}`
> with the **two-sided defining property**:
> `0 ≠ v ∈ V^{λ_i}  ⇔  lim_{N→±∞} (1/N) log ‖T^N v‖ = λ_i.`
> (The sign of the `1/N` factor flips as `N → -∞`.)

**Crucial distinction for the plan:** the *flag/filtration* form (§3.1) is the
one-sided object and needs only forward integrability; the *direct-sum splitting*
`E_1 ⊕ ··· ⊕ E_k` (here `V^{λ_1} ⊕ ··· ⊕ V^{λ_k}`) is the two-sided object and
**requires invertibility of `T` plus backward integrability** (it is built by
intersecting forward and backward filtrations).

### 3.3 Geometric form (Filip Thm 3.5.1) — used in Proof B
> `E → Ω` a cocycle over ergodic `T`, metric `‖−‖`, with **both-sided** integrability
> `∫_Ω log⁺ ‖T_ω‖_op dμ < ∞`  and  `∫_Ω log⁺ ‖T_ω⁻¹‖_op dμ < ∞`.
> Consider the bundle `X` whose fiber `X_ω` is the space of metrics on `E_ω`
> (i.e. `GL(E_ω)/O(E_ω)`). Then the sequence of metrics `‖v‖_N := ‖T^N v‖` is a
> **regular sequence** in `X_ω` for μ-a.e. `ω`.

Filip's **Proposition 3.4.8** proves this is *equivalent* to the classical MET
(3.1). Three equivalent conditions:
1. The (classical) Oseledets theorem holds for `E_ω`.
2. The sequence of metrics `‖v‖_N := ‖T^N v‖` is regular in `GL(V_ω)/O(V_ω)`.
3. There is an invertible self-adjoint `Λ : V_ω → V_ω` (for the fixed metric) with
   `|⟨Λ^{-2n}(T^n)† T^n v, v⟩| = o(n)` for all `v` (`†` = adjoint). Here `Λ` acts as
   the scalar `e^{λ_j}` on `V^{λ_j}_ω`; the eigenspaces of `Λ` recover the splitting.

**Filip Rmk 3.5.7:** the integrability assumption on `T_ω⁻¹` is not strictly
necessary; without it one must extend "regular sequence" to allow super-linear
divergence in flat directions. For a cocycle valued in `SLₙ(ℝ)`, forward
integrability of `T_ω` **implies** that of `T_ω⁻¹`.

---

## 4. PROOF A (elementary, Kingman-free) — Filip §2.3–§2.5 / Amit §2

Top-level structure: **induction on `d = dim V`**, driven by two lemmas.

### 4.1 The base case (dim 1 ⇔ Birkhoff) — Filip Rmk 2.2.11, Amit Prop 2.8
For a line bundle, set `f(ω) := log(‖T_ω v‖/‖v‖) = log‖T_ω‖_op` (independent of
`v ≠ 0`). The integrability (2.2.7) ⇔ `f₊ ∈ L¹`. Telescoping the cocycle,
`(1/N) Σ_{m=0}^{N-1} f(Tᵐω) = (1/N) log(‖T^N v‖/‖v‖)`, so Birkhoff gives
`(1/N) log‖T^N v‖ → ∫ f dμ =: λ₁`. The converse (`O ⇒ B`) builds the skew product
`T(ω,v) = (Tω, exp(f(ω))·v)`. **Dependency: Birkhoff (1.3) only.**

### 4.2 Lemma A1 — Reducibility / growth dichotomy (Filip Lemma 2.3.1, Amit Lemma 2.9)
> At least one (perhaps both) holds:
> (i) ∃ `λ ∈ ℝ` such that for a.e. `ω` and all nonzero `v ∈ V_ω`,
>     `(1/N) log‖T^N v‖ → λ`, **uniformly** over `‖v‖ = 1` for fixed `ω`; or
> (ii) ∃ a nontrivial proper T-invariant subbundle `E ⊊ V`, defined μ-a.e.

**Proof of Lemma A1 (Filip §2.4, Amit pp. 12–16) — the "contraction on the
projective bundle" step.**

1. Form the **projective bundle** `P(V) →^π Ω`; `T` lifts to `P(V)` by
   projective-linear maps `T̃(ω,[v]) = (Tω, [T_ω v])`.
2. Define `M₁(P(V), μ) := { η prob. measure on P(V) : π∗η = μ }` (measures
   projecting to `μ`), with the **weak-\*** topology dual to functions measurable on
   `P(V)`, continuous on a.e. fiber. `T` acts on this space by push-forward; T-invariance
   of the projection uses `T̃⁻¹π⁻¹(A) = π⁻¹(T⁻¹A)`, which **needs invertibility of the
   fiber maps**.
3. **Krylov–Bogoliubov in families** (Filip Exercise 2.4.2(ii); Amit Thm 2.13):
   `M₁(P(V),μ)` is weak-\* (sequentially) compact and has ≥ 1 T-invariant measure.
4. Define `f([v]) := log(‖Tv‖/‖v‖)`. Then `∫f : M₁(P(V),μ) → ℝ`, `η ↦ ∫ f dη` is
   continuous. The set `M₁(P(V),μ)^T` of T-invariant measures is nonempty, weak-\*
   compact, and **convex**, so `∫f` attains a minimum on it; the minimizing set is a
   **closed convex set**.
5. **Krein–Milman** (Amit Thm 2.14): the minimizing set has an **extreme point** `η`.
   Being extremal in the minimizing convex set ⇒ `η` is **ergodic** for the `T̃`-action
   on `P(V)`.
6. Apply **Birkhoff** to `f` and `η`: for `η`-a.e. `[v]`,
   `(1/N) Σ f(Tᵐ[v]) = (1/N) log(‖T^N v‖/‖v‖) → ∫ f dη =: λ`.
7. Let `M ⊂ P(V)` be the full-`η`-measure set where this holds; `M_ω := M ∩ P(V_ω)`.
   Then `M` is `T`-invariant, `M_ω ≠ ∅` for a.e. `ω` (since `μ(π(M)) = 1`), and
   `E := ⋃_ω span(M_ω)` is a **T-invariant subbundle** (constant fiber dimension by an
   ergodicity argument). 
   - If `E ⊊ V` proper ⇒ case (ii).
   - If `E = V`: every vector is a combination of vectors growing at rate `λ`, so
     growth `≤ λ`; a **weak-\* limit / contradiction argument** (build measures
     `η_i = (1/N_i) Σ δ_{Tᵐ[v_i]}` from a hypothetical slow-growing unit sequence, take
     weak-\* limit `η_ε`, show `∫ f dη_ε ≤ λ - ε`, contradicting minimality of `λ`)
     forces growth **exactly** `λ`, uniformly ⇒ case (i).

**Dependencies of Lemma A1:** Krylov–Bogoliubov (in families), Krein–Milman,
Birkhoff, weak-\* compactness of measures on a compact metric projective bundle,
and **invertibility of the fiber maps** (for the T-action on measures). Notably
**no Kingman**.

### 4.3 Lemma A2 — Unusual growth implies splitting (Filip Lemma 2.3.3, Amit Lemma 2.11)
> Given a SES of cocycles `0 → E ↪→ V →^p F → 0`. Suppose ∃ `λ_E, λ_F ∈ ℝ` with, for
> a.e. `ω`, `(1/N) log‖T^N e‖ → λ_E` for all `e ∈ E_ω \ 0` and `(1/N) log‖T^N f‖ → λ_F`
> for all `f ∈ F_ω \ 0`, **uniformly** on unit vectors. **If `λ_E > λ_F`** then the SES
> **splits T-invariantly**: ∃ linear `σ : F → V` with `V = E ⊕ σ(F)`, `p∘σ = 1_F`,
> and the decomposition is T-invariant. (`λ_F = -∞` allowed.)

**Proof of Lemma A2 (Filip §2.5, Amit pp. 16–18) — the convergent-series /
"hyperbolic graph transform" step.**

1. Pick any lift `σ₀ : F → V` with `V = E ⊕ σ₀(F)` (e.g. `F ≅ E^⊥` via the metric).
   In this splitting the cocycle is block-upper-triangular:
   `T = [[T_E, U],[0, T_F]]`, with `T_{E,ω}: E_ω→E_{Tω}`, `T_{F,ω}: F_ω→F_{Tω}`,
   `U_ω : F_ω → E_{Tω}`.
2. Any other lift `σ = σ₀ + τ` with `τ : F → E`. The condition that `σ(F)` is
   T-invariant reduces to the **cohomological equation**
   `T_{E,ω}∘τ_ω + U_ω = τ_{Tω}∘T_{F,ω}`, i.e.
   `τ_ω = T_{E,ω}⁻¹∘τ_{Tω}∘T_{F,ω} − T_{E,ω}⁻¹∘U_ω.   (2.5.3)`
3. **Formal solution** (geometric-series / Neumann-type):
   `τ_ω = −Σ_{n=0}^∞ (T^{n+1}_{E,ω})⁻¹ ∘ U_{Tⁿω} ∘ T^n_{F,ω}.   (2.5.4)`
4. **Convergence** uses `λ_E > λ_F` plus Birkhoff:
   - Birkhoff on `log⁺‖U‖_op ∈ L¹` ⇒ `‖U_{Tⁿω}‖_op = e^{o(n)}` (sub-exponential).
   - From the uniform growth: `‖(T^{n+1}_{E,ω})⁻¹‖ ~ e^{-nλ_E + o(n)}`,
     `‖T^n_{F,ω} v‖ ~ e^{nλ_F + o(n)}`.
   - Each term `≤ e^{n(λ_F − λ_E) + o(n)}`, and `λ_F − λ_E < 0` ⇒ exponentially
     convergent, uniform in `ω` over a basis of `F_ω`.
5. The splitting is **tempered** (Filip Rmk 2.3.6): `(1/N) log(‖σ(T^N v)‖/‖T^N v‖) → 0`,
   so `σ(F)` has the same Lyapunov exponent as `F`.

**Dependencies of Lemma A2:** Birkhoff (for the `e^{o(n)}` bound on `‖U‖`),
uniform growth on `E` and `F` (hypothesis), invertibility of `T_E`. **No Kingman.**

### 4.4 The induction (Filip Proof of Thm 2.2.6; Amit pp. 9–12, fully detailed)
Induct on `d = dim V`.
- `d = 1`: base case §4.1.
- Assume true for dim `≤ d-1`; let `dim V = d`. Lemma A1 gives a dichotomy:
  - **Case (i):** single exponent `λ₁`, trivial filtration — done.
  - **Case (ii):** there is a proper T-invariant `E ⊊ V`. Pick `E` of **maximal
    dimension** (Filip: minimal codimension). Then `V/E` has **no** proper invariant
    subbundle, so by Lemma A1 again, `V/E` has a **single** exponent `λ'`.
    By induction, `E` has exponents `λ₁ > ··· > λ_k` and filtration `E^{≤λ_i}` (these
    are also subbundles of `V`). The exponents of `V` are `{λ', λ₁,…,λ_k}`.
    - If `λ' ≥ λ₁`: the top exponent of `V` is `λ'`; arrange the filtration putting
      `V` (or the appropriate level) on top. (Amit handles `λ'>λ₁` and `λ'=λ₁`
      separately; needs the `U_N` estimate below.)
    - If `λ' < λ₁`: apply **Lemma A2** to `0 → E/E^{≤λ_2} ↪→ V/E^{≤λ_2} → V/E → 0`
      (note `E/E^{≤λ_2}` has the single top exponent `λ₁ > λ' = λ_{V/E}`), obtaining a
      splitting `σ : V/E → V/E^{≤λ_2}`. Pull back: `V^{≤λ_2} := τ⁻¹(σ(V/E))` where
      `τ : V → V/E^{≤λ_2}`. Then vectors outside `V^{≤λ_2}` grow at `λ₁`; `V^{≤λ_2}`
      has max exponent `max{λ_2, λ'}` and dim `< d`, so induction supplies its
      filtration. Set `V^{≤λ_1} := V`. **Iterate Lemma A2** on `V^{≤λ_i}` until
      `λ_{i+1} < λ'`, building the full Oseledets filtration.

**Amit's extra detail (the `U_N` operator-norm estimate):** in the block form
`T^N = [[T^N_E, U_{N,ω}],[0, H^N_ω]]`, one shows
`U_{N+1,ω} = Σ_{m=0}^N T^{N-m}_{E,T^{m+1}ω} U_{Tᵐω} H^m_ω`, and by picking the
maximal term, `‖U_{N+1,ω}‖_op ≤ (N+1)‖T^{N-k}_{E}U_{Tᵏω}H^k‖_op`, giving
`limsup (1/N) log‖U_N‖_op ≤ λ'`. This guarantees vectors projecting nontrivially to
`V/E` grow at exactly `λ'`. (This is the concrete computation behind "exponents are
additive over exact sequences".)

**Net dependency tree for Proof A:**
Birkhoff ⟶ {dim-1 base case, the `e^{o(n)}` bounds};
Krylov–Bogoliubov(+families) + Krein–Milman + weak-\* compactness ⟶ Lemma A1;
Birkhoff + uniform growth ⟶ Lemma A2;
Lemma A1 + Lemma A2 + induction ⟶ MET. **Kingman not used.**

---

## 5. PROOF B (geometric, via singular values / exterior powers / Kingman) — Filip §3, §3.5

This is the route that explicitly realizes the "exterior powers ⋀ᵏ to get all
exponents from top exponents of ⋀ᵏA" architecture the task highlights.

### 5.1 Linear-algebra inputs (Filip §3.1, §3.2.6)
**Operations and their exponents (Filip §3.1.1)** — for cocycles `L` (exps `λ_i`),
`N` (exps `η_j`), listed with multiplicity:
- `L ⊗ N`: exponents `{λ_i + η_j}`.
- `L^∨` (dual): exponents `{-λ_i}`.
- `Hom(L,N)`: exponents `{η_j - λ_i}`.
- **`⋀^k(L)`: exponents `{λ_{i_1} + ··· + λ_{i_k} : i_1 < ··· < i_k}`.**

**Singular values / polar decomposition (Filip §3.2.6):** for `T : V → W` with metrics,
`T†T` is self-adjoint with eigenvalues `σ_1(T)² ≥ ··· ≥ σ_n(T)²` (the **singular
values** `σ_i`). The top one is the operator norm: `σ_1(T) = ‖T‖_op`. On exterior
powers,
`σ_1(⋀^k T) = σ_1(T)···σ_k(T)`,
i.e. **`‖⋀^k T‖_op = ∏_{i=1}^k σ_i(T)`** = product of the top `k` singular values.
This is the key identity that lets one read off the sum of the top `k` exponents
from the top exponent of `⋀^k T`.

**Polar / KAK (Filip §3.2.5):** for `g ∈ SLₙℝ`, `gg^t = k_1 d_1 k_1^t`,
`g^t g = k_2 d_2 k_2^t` (spectral theorem), `d_1 = d_2 = d`, `g = k_1 √d k_2`
(`k_i ∈ SOₙ`), the singular-value/`KAK` decomposition `G = K A⁺ K`. The **Cartan
projection** `r(g) ∈ a⁺` is the diagonal matrix with `i`-th entry `log σ_i(g)`
(Filip §3.3.5).

### 5.2 The proof (Filip §3.5)
1. Set `f_N(ω) := log‖(T^N)_ω‖_op`. Submultiplicativity `‖A∘B‖ ≤ ‖A‖·‖B‖` gives the
   **subadditivity** `f_{i+j}(ω) ≤ f_i(ω) + f_j(Tⁱω)` (3.5.3). With `f_1 ∈ L¹`
   (the integrability hypothesis), **Kingman (3.5.2)** applies:
   `lim (1/N) log‖(T^N)_ω‖_op = λ_1` exists μ-a.e. Since `‖T^N‖_op = σ_1(T^N)`, this is
   the **top Lyapunov exponent**.
2. **Apply the same to the exterior-power bundles `⋀^k V`.** Because
   `‖⋀^k T^N‖_op = σ_1(T^N)···σ_k(T^N)`, Kingman on `⋀^k` yields convergence of
   `(1/N) log(σ_1···σ_k)(T^N)` for each `k`. Subtracting consecutive `k`'s shows **all
   (normalized) singular values `(1/N) log σ_k(T^N)` converge** — these limits are the
   Lyapunov exponents (with multiplicity).
3. Equivalently: the **Cartan projection `(1/N) r(x_N)` converges** in `a⁺`, where
   `x_N` are the pulled-back metrics after `N` steps. ("Distances converge" condition.)
4. **Small-steps condition:** Birkhoff applied to `f(ω) = log⁺‖T_ω‖_op` and
   `f(ω) = log⁺‖T_ω⁻¹‖_op` gives `(1/N) f(T^N ω) → 0`, i.e. `d(x_N, x_{N+1}) = o(N)`
   (uses *both-sided* integrability).
5. By **Kaimanovich's regularity criterion (Thm 3.3.9)** — *small steps* + *distances
   converge* ⇒ the sequence `{x_N}` is **regular** in the symmetric space
   `X_ω = GL(V_ω)/O(V_ω)`. This is exactly the geometric MET (Thm 3.5.1).
6. **Prop 3.4.8** translates regularity back to the classical filtration/splitting:
   the limiting Cartan projection's distinct values give the exponents `λ_j`; the
   self-adjoint operator `Λ` (eigenvalue `e^{λ_j}` on `V^{λ_j}`) furnishes the
   splitting, whose partial sums give the filtration.

**Dependencies of Proof B:** **Kingman (central)** + Birkhoff (small steps) +
singular-value theory (spectral theorem, `‖⋀^k T‖ = ∏σ_i`) + exterior powers +
Kaimanovich's regularity theorem (which itself rests on comparison geometry of
nonpositively curved symmetric spaces / law of sines in negative curvature, Filip
§3.3.9–3.3.12).

### 5.3 Kaimanovich regularity (Filip §3.3.6–3.3.9), for completeness
A sequence `{x_n}` in `X = G/K` is **regular** if ∃ a geodesic ray `γ` and `θ ≥ 0`
with `d(x_n, γ(θn)) = o(n)`. **Thm 3.3.9 (Kaimanovich):** `{x_n}` is regular ⇔
(small steps) `d(x_n, x_{n+1}) = o(n)` **and** (distances converge)
`α := lim r(x_n)/n` exists in `a⁺`. Nonpositive curvature is essential. Proof sketch
(hyperbolic-plane case): law of sines in constant negative curvature controls the
angles `φ_n = ∠(x_n e x_{n+1})`, giving `|φ_n| ≤ e^{-θn + o(n)}`, so total angle
converges and the limiting geodesic `o(n)`-tracks `x_n`.

---

## 6. Symmetry refinements (Filip §3.1.3–3.1.4)

- **Symplectic cocycles** (rank `2g`, T-preserved symplectic form): spectrum is
  symmetric `λ_1 ≥ ··· ≥ λ_g ≥ -λ_g ≥ ··· ≥ -λ_1`; symplectic-orthogonal of
  `V^{≤λ_{i+1}}` is `V^{≤-λ_i}`. (Via iso `V ≅ V^∨`, whose exponents are negated.)
- **Volume-preserving** diffeo: top exterior power has exponent 0, hence
  `Σ_i λ_i = 0` on `TM`.
- **Signature-(p,q) bilinear form** (`p ≥ q`): spectrum
  `λ_1 ≥ ··· ≥ λ_q ≥ 0 ··· 0 ≥ -λ_q ≥ ··· ≥ -λ_1`, with ≥ `p-q` zero exponents.

---

## 7. Formalization assessment (for the Lean 4 + Mathlib plan)

### 7.1 What Mathlib likely already provides / needs
- **Birkhoff pointwise ergodic theorem:** present in Mathlib
  (`MeasureTheory.Ergodic`/`Birkhoff`-style results). Both proofs need it; Proof A
  needs *only* Birkhoff among the deep ergodic theorems.
- **Kingman subadditive ergodic theorem:** **not** (to my knowledge) in Mathlib.
  Proof B needs it; Proof A avoids it. This is the decisive factor: **Proof A is the
  recommended primary route** unless one first formalizes Kingman.
- **Operator norm, singular values, spectral theorem for self-adjoint operators,
  exterior powers `⋀^k`:** Mathlib has the spectral theorem (`LinearMap.IsSymmetric`,
  `isHermitian` eigenbasis) and exterior powers (`exteriorPower`), but the identity
  `‖⋀^k T‖_op = ∏_{i≤k} σ_i(T)` and a clean singular-value API may need building.
- **Krylov–Bogoliubov:** Mathlib has a Krylov–Bogoliubov existence result for
  invariant measures on compact spaces; the **"in families" / fibered version**
  over `P(V)` (Filip Exercise 2.4.2(ii)) is more bespoke and likely needs work.
- **Krein–Milman:** present in Mathlib (`krein_milman`).
- **Weak-\* compactness of probability measures on a compact metric space:** present
  (Prokhorov / `MeasureTheory` weak topology), but `M₁(P(V),μ)` with the
  "continuous on a.e. fiber" duality is a custom topology.

### 7.2 Easiest pieces
- The **dim-1 ⇔ Birkhoff** equivalence (§4.1) — direct telescoping; very Lean-friendly.
- The **Lemma A2 convergent-series** estimate (§4.3) — a clean analytic geometric-series
  bound once the uniform growth hypotheses are available; self-contained.
- **Exponent bookkeeping** over exact sequences / the additivity statements — algebraic.
- **Singular-value identity** `‖⋀^k T‖ = ∏σ_i` (finite-dim spectral theorem) is a
  concrete linear-algebra fact, independent of any ergodic theory.

### 7.3 Hardest pieces
- The **fibered Krylov–Bogoliubov + Krein–Milman extreme-point ⇒ ergodic** argument
  in Lemma A1: heavy measure-theory/functional-analysis machinery (weak-\* topology on
  fibered measures, push-forward action, extreme points are ergodic). This is the
  crux and the most likely formalization bottleneck for Proof A.
- **Measurable selection / measurable subbundles:** constructing `E = ⋃ span(M_ω)` as
  a genuine measurable T-invariant subbundle with a.e.-constant dimension (Amit's
  ergodicity argument) requires measurable-selection / measurable-rank lemmas that may
  be partly missing in Mathlib.
- The whole **symmetric-space / Kaimanovich** apparatus (Proof B, §3.3): comparison
  geometry, CAT(0), Cartan projection — substantial and probably out of scope for a
  first formalization. Best to extract only the **singular-value Kingman** core if one
  goes the Proof-B way, and skip the metric-geometry packaging.
- **Kingman itself** (if Proof B): a major standalone formalization effort.

### 7.4 Recommended formalization route
1. State the **one-sided forward MET** (§3.1) first; it needs only forward
   integrability and yields the filtration. Use measurable trivialization to reduce
   to `Ω × ℝᵈ` and a measurable `A : Ω → GL_d(ℝ)`.
2. Pursue **Proof A**: Birkhoff base case → Lemma A1 (the hard analytic core) →
   Lemma A2 → induction on dimension. This dodges Kingman.
3. Derive the **two-sided splitting** (§3.2) as a corollary by applying the one-sided
   theorem to `T⁻¹` and intersecting filtrations — explicitly flag that this step
   needs `T` invertible and backward integrability.
4. Treat the geometric/Kingman material (Proof B, §3, §5) as an alternative/secondary
   formalization, valuable mainly for the clean `‖⋀^k T‖ = ∏σ_i` viewpoint and for
   anyone who first lands Kingman in Mathlib.

---

## 8. Out-of-scope material in the source (catalogued, not core MET)

Filip §4 (**Noncommutative Ergodic Theorem**, Karlsson–Ledrappier / Gouëzel–Karlsson):
horofunctions, Busemann functions, linear drift, isometries/semi-contractions of
proper metric spaces; Thm 4.3.1 gives `lim (1/N) d(g_ω···g_{T^{N-1}ω}x_0, x_0) = l`
and a measurable horofunction `h_ω` detecting the drift, with equivariance only in
CAT(0)/δ-hyperbolic settings. Filip §5 (**Mean MET**) covers CAT(0) spaces, direct
integrals, and a Mean Kingman theorem. These generalize the MET but are well beyond
the classical linear-cocycle statement targeted by the formalization, and are not
recommended for the initial Lean effort.
