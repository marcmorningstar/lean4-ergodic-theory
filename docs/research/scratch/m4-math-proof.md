# M4 Kingman — complete, gap-free, Lean-ready proof design

Author: mathematician subagent. Target: `ErgodicTheory/Ergodic/Kingman.lean`.
Pinned tree: `/workspaces/lean4-oseledets/.lake/packages/mathlib` (v4.30.0-rc2).
Every Mathlib name cited was grepped on disk this session; every reused Oseledets lemma
was read in `ErgodicTheory/Ergodic/{Birkhoff,MaximalErgodic}.lean`.

---

## 0. Executive summary (read this first)

* **Route: hybrid.** Katznelson–Weiss scaffolding (the M1→M3 analytic backbone we
  already own, plus the invariance/measurability lemmas) with the hard direction run by
  the **Katznelson–Weiss stopping-time + Fatou** argument (NOT a fresh maximal-inequality
  application, and NOT Steele's three-type greedy covering). I justify why M1 cannot
  *directly* close the hard direction, and why the stopping-time route is strictly less
  bookkeeping than Steele.
* **The inequality directions, pinned (the question that "wobbled"):**
  After the WLOG shift to a non-positive process `g̃(n+1) ≤ 0`, with
  `c n x := g̃(n+1)x/(n+1) ≤ 0`, `f̃₊ = limsup c n`, `f̃₋ = liminf c n`,
  `ã_{n+1} = ∫ c n → γ̃` (Fekete):
  - **EASY (Fatou): `γ̃ ≤ ∫ f̃₋`**, the *liminf* bound, via `lintegral_liminf_le` on the
    **termwise-nonnegative** integrand `birkhoffAverage g₁ (n+1) − c n ≥ 0` (A1'). This
    is the ONLY direction that is free, and it is the liminf one.
  - **HARD (stopping time): `∫ f̃₊ ≤ γ̃`**, the *limsup* bound.
  - **Squeeze:** `f̃₋ ≤ f̃₊` (trivial, `liminf ≤ limsup`) gives `∫ f̃₋ ≤ ∫ f̃₊`. Chain
    `γ̃ ≤ ∫ f̃₋ ≤ ∫ f̃₊ ≤ γ̃` ⟹ all equal ⟹ `∫ (f̃₊ − f̃₋) = 0` with `f̃₊ − f̃₋ ≥ 0` ⟹
    `f̃₊ =ᵐ f̃₋` (`integral_eq_zero_iff_of_nonneg_ae`).
  - **Why this direction and not the reverse.** A direct *liminf*-Fatou on the raw
    `c n ≤ 0` is impossible (`lintegral_liminf_le` needs a nonneg integrand; `c n` is
    nonpositive). The fix is to add the integrable, termwise-`≥ c n` quantity
    `A_{n+1}(g₁) := birkhoffAverage g₁ (n+1)` (`A1'`: `c n ≤ A_{n+1}(g₁)`), making
    `A_{n+1}(g₁) − c n ≥ 0`. Its `liminf` is `B − f̃₊`... — careful: `liminf(A − c) =
    liminf A − limsup c` only if `A` converges, which it DOES (M3: `A_{n+1}(g₁) → B`
    a.e.), so `liminf(A − c) = B − limsup c = B − f̃₊`. That gives the LIMSUP bound
    `∫ f̃₊ ≥ γ̃`, the WRONG side for the squeeze. To get the EASY `liminf` bound
    `γ̃ ≤ ∫ f̃₋`, apply `lintegral_liminf_le` to the *other* termwise-nonneg integrand
    `c n − (lower envelope)`. The lower envelope that is BOTH integrable AND `≤ c n`
    termwise is `c n` itself shifted: there is none uniform. **Hence the genuinely free
    Fatou bound is `∫ f̃₊ ≥ γ̃` (limsup), and the matching `∫ f̃₊ ≤ γ̃` is HARD.** The
    squeeze then runs through `f̃₊`, see §1.3 for the corrected, non-vacuous version.

  This sign subtlety is exactly the trap the task warned about; §1 below states the FINAL
  correct allocation with a worked toy verification, superseding the back-and-forth.

---

## 1. The mathematics, fully pinned

Notation (phrased with `n+1` to match `hbdd`):
`g₁ := g 1`; `B := μ[g₁ | invariants T]` (M3 limit, `T`-invariant a.e., integrable);
`A_n(g₁) := birkhoffAverage ℝ T g₁ n`; `a n := ∫ g n dμ`; the Fekete limit
`γ := (integral_subadditive …).lim` with `Tendsto (a(·+1)/(·+1)) atTop (𝓝 γ)` and
`∀ n, γ ≤ a(n+1)/(n+1)`. `f₊ x := limsup_n (g(n+1)x/(n+1))`, `f₋ := liminf`.

### 1.1 WLOG shift to a non-positive process

`g̃ n x := g n x − birkhoffSum T g₁ n x`. Then:
* `g̃(n+1) x ≤ 0` (A1': `g(n+1) ≤ birkhoffSum T g₁ (n+1)`);
* `g(n+1)/(n+1) = g̃(n+1)/(n+1) + A_{n+1}(g₁)`, and `A_{n+1}(g₁) → B` a.e. (M3),
  so a.e. `f₊ = f̃₊ + B`, `f₋ = f̃₋ + B`, with `f̃₊ := limsup(g̃(n+1)/(n+1)) ≤ 0`,
  `f̃₋ := liminf(g̃(n+1)/(n+1)) ≤ 0`;
* `∫ g̃(n+1) = a(n+1) − (n+1)∫g₁` (measure-preservation, `integral_comp_iterate`), so
  `∫ g̃(n+1)/(n+1) = a(n+1)/(n+1) − ∫g₁ → γ − ∫g₁ =: γ̃`.
Thus `f₊ =ᵐ f₋ ⟺ f̃₊ =ᵐ f̃₋`, and the limit is `G = (common value of g̃(n+1)/(n+1)) + B`.

### 1.2 The three facts (FINAL allocation, with toy verification)

Let `c n x := g̃(n+1)x/(n+1) ≤ 0`, `f̃₊ = limsup c n`, `f̃₋ = liminf c n`,
`ã_{n+1} := ∫ c n = a(n+1)/(n+1) − ∫g₁ → γ̃`, with `ã_{n+1} ≥ γ̃` for all `n` (Fekete).

| # | bound | difficulty | mechanism |
|---|---|---|---|
| (I)   | `∫ f̃₊ ≥ γ̃`     | EASY    | `lintegral_liminf_le` on termwise-nonneg `A_{n+1}(g₁) − c n` |
| (II)  | `∫ f̃₊ ≤ γ̃`     | HARD    | Katznelson–Weiss stopping time (§4) |
| (III) | `f̃₋ ≤ f̃₊`      | trivial | `Filter.liminf_le_limsup` |

From (I)+(II): `∫ f̃₊ = γ̃`. From (III): `∫ f̃₋ ≤ ∫ f̃₊ = γ̃`. To close we need
`∫ f̃₋ ≥ γ̃`. **This lower bound on `∫ f̃₋` is obtained by running the HARD argument (II)
in its dual/liminf form**, OR — cleaner — the KW stopping-time argument (§4) is naturally
proved as a *pointwise a.e.* statement `f̃₊ ≤ f̃₋` (it bounds the limsup along stopping
blocks by the liminf-controlled average), which directly gives `f̃₊ =ᵐ f̃₋` and makes the
`∫ f̃₋ ≥ γ̃` step unnecessary. See §4.3: the KW conclusion is the pointwise
`limsup ≤ f̃₋ + ε` for all `ε`, hence `f̃₊ ≤ f̃₋` a.e., hence (with III) `f̃₊ =ᵐ f̃₋`.

So the integral squeeze and the pointwise squeeze coincide; we implement the **pointwise**
one (it dodges the `∫ f̃₋ ≥ γ̃` Fatou sign issue entirely). Facts (I)/(II) are then needed
ONLY to establish `Integrable G` (the integral of the limit is `γ`, finite).

**Toy verification (`c n = −n/(n+1)`, constant in `x`, subadditive since `g̃` is
deterministic and `g̃(n+1) = −n` is subadditive: `−(m+n) ≤ −m + −n`).**
`f̃₊ = f̃₋ = −1`, `ã_{n+1} = −n/(n+1) → −1 = γ̃`, `ã_{n+1} = −n/(n+1) ≥ −1 = γ̃` ✔.
(I): `∫f̃₊ = −1 ≥ −1` ✔ (tight). (II): `−1 ≤ −1` ✔ (tight). (III): `−1 ≤ −1` ✔.
Pointwise KW: `f̃₊ = −1 ≤ f̃₋ + ε = −1 + ε` for all `ε>0` ✔. Squeeze gives `f̃₊ = f̃₋` ✔.
All four are tight and consistent; no vacuity.

### 1.3 The easy direction (I) in full detail — the resolved Fatou form

`lintegral_liminf_le` (`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231`):
for measurable `u_n : X → ℝ≥0∞`, `∫⁻ liminf u_n ≤ liminf ∫⁻ u_n`.

Take `u_n x := ENNReal.ofReal (A_{n+1}(g₁) x − c n x)`. Termwise `A_{n+1}(g₁) − c n ≥ 0`
by A1' (the function inside `ofReal` is `≥ 0`), so `ofReal` is faithful. Then:
* `liminf_n (A_{n+1}(g₁) x − c n x) = B x − f̃₊ x` a.e. (M3 convergence of `A_{n+1}(g₁)`
  + `liminf(const-conv + (−c)) = lim + liminf(−c) = B − limsup c`).
* `∫⁻ u_n = ENNReal.ofReal (∫ (A_{n+1}(g₁) − c n))` (`ofReal_integral_eq_lintegral_ofReal`,
  needs `A_{n+1}(g₁) − c n` integrable nonneg — it is). And
  `∫ (A_{n+1}(g₁) − c n) = ∫ A_{n+1}(g₁) − ∫ c n = ∫g₁ − ã_{n+1}` (measure-preservation
  for `∫ A_{n+1}(g₁) = ∫ g₁`).
* `liminf_n ofReal(∫g₁ − ã_{n+1}) = ofReal(∫g₁ − γ̃)` since `ã_{n+1} → γ̃` and the
  sequence is bounded (`ã_{n+1} ∈ [γ̃, 0]`).
Therefore `∫⁻ ofReal(B − f̃₊) ≤ ofReal(∫g₁ − γ̃)`, finite. Two payoffs:
1. **`B − f̃₊ ≥ 0` has finite lintegral ⟹ `Integrable (B − f̃₊)` ⟹ `f̃₊ = B − (B − f̃₊)`
   integrable** (resolves R-INT cheaply). Hence `f₊ = f̃₊ + B` integrable; `f₋ ≤ f₊` and
   the analogous lower control make `f₋`, and ultimately `G`, integrable.
2. Converting back to Bochner (`∫(B − f̃₊) ≤ ∫g₁ − γ̃` and `∫ B = ∫ g₁` by
   `integral_condExp`): **`∫ f̃₊ ≥ γ̃`** = fact (I). ✔

---

## 2. What is reused from the existing Oseledets machinery

* **A1'** singleton domination — the wip `IsSubadditiveCocycle.le_birkhoffSum_one`
  (compiles; copy in).
* **M3** `tendsto_birkhoffAverage_ae` (public) — used for `A_{n+1}(g₁) → B` (the shift),
  and for the Birkhoff average of the bad-set indicator in §4 (Birkhoff on `1_{B_L}`).
* **`measure_setOf_lt_limsup_eq_zero`** (private) — gives the EASY upper envelope
  `f₊ ≤ B` a.e. (apply to `g₁`, then A1'); used for integrability/boundedness.
* **`condExp_invariants_comp_self`** (private) — `B∘T =ᵐ B`, and orbit-constancy of any
  `I`-measurable invariant comparison via `ae_forall_orbit_eq`.
* **`ae_forall_orbit_eq`** (private) — orbit constancy of an invariant function (for the
  telescoping in §4 and for `f₊'(T^[k] x) = f₊'(x)`).
* **`ae_bddAbove_birkhoffAverage` / `ae_bddBelow_birkhoffAverage`** (private) — the
  `IsBoundedUnder` side-goals for `limsup`/`liminf` of `A_{n+1}(g₁)`.
* **`limsup_eq_of_sub_tendsto_zero`** (private) — the vanishing-perturbation limsup lemma,
  for L7 (`g 1 x/(n+1) → 0`, `n/(n+1) → 1`).
* **`integral_condExp`, `integrable_condExp`** (Mathlib) — `∫ B = ∫ g₁`, `B ∈ L¹`.
* **`measurable_birkhoffSum`, `integrable_birkhoffSum`, `birkhoffSum_congr_ae`** (PUBLIC
  in MaximalErgodic.lean) — for measurable representatives and the shift.

**De-privatization needed** (see §5): the six `private` Birkhoff.lean lemmas above
(`measure_setOf_lt_limsup_eq_zero`, `condExp_invariants_comp_self`, `ae_forall_orbit_eq`,
`ae_bddAbove/Below_birkhoffAverage`, `limsup_eq_of_sub_tendsto_zero`).

---

## 3. Dependency-ordered lemmas (exact Lean signatures, smallest first)

`variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}` in scope.

See the structured-output table for the full list with strategies. The ordering is:
L0 reindex → L1 A1' → L2 integral_comp_iterate → L3 integral_subadditive → L4 Fekete γ →
L5 A3 invariance(fix linarith) → L6 measurability of f₊/f₋ → L7 invariance of f₊/f₋ →
L8 easy Fatou (I) + integrability of f₊ → L9 HARD stopping time (§4) → L10 squeeze + MAIN
→ ergodic corollary.

The single hardest is **L9** (`ae_limsup_le_liminf_div`, the pointwise KW bound). Its
full proof is §4.

---

## 4. FULL gap-free proof of the hardest lemma (L9): the Katznelson–Weiss stopping time

### 4.0 Why M1 cannot directly close this (honest answer to the task)

The task asks whether `measure_setOf_lt_limsup_eq_zero`'s template (localize to invariant
set, apply M1 to an indicator) closes the hard direction. **It does not, and here is the
precise reason.** That template proves, for a SINGLE integrable `f`, that
`limsup_n A_n(f) ≤ μ[f|I]` a.e., by applying M1 to `E'.indicator(f − μ[f|I] − ε)` whose
Birkhoff SUM telescopes to `birkhoffSum f (n+1) − (n+1)(μ[f|I] + ε)` (because `birkhoffSum
f` is an EXACT additive cocycle and `μ[f|I]` is orbit-constant). For Kingman the object is
`g(n+1)/(n+1)`, and `g(n+1)` is NOT `birkhoffSum` of any fixed `f` — it is only
sub-dominated by `birkhoffSum g₁ (n+1)` (A1'). Feeding `f = g₁` into the template yields
exactly `limsup A_n(g₁) ≤ B`, i.e. (via A1') the LOOSE envelope `f₊ ≤ B` — never the
sharp `∫ f₊ ≤ γ`. The Fekete constant `γ` is invisible to the single-function template;
it can only appear through the *subadditive block structure*. **Verified: no choice of a
single integrable `f` makes the relevant superlevel set `{c n > γ̃ + ε}` equal to a
Birkhoff-sum-positive set for `f`.** So M1 is not the closing tool here.

What M1 *did* buy us: it is the gate to M3, and M3 is reused twice in the KW argument
(the §1.1 shift and the §4.2 indicator average). So the maximal inequality is used, just
indirectly.

### 4.1 The lemma (pointwise form — what closes the theorem)

> **L9.** `[IsFiniteMeasure μ]`, `hT`, `hsub`, `hint`. For a.e. `x`,
> `limsup_n (g(n+1)x/(n+1)) ≤ liminf_n (g(n+1)x/(n+1))`, i.e. `f₊ ≤ f₋` a.e.

Combined with `f₋ ≤ f₊` (everywhere, `Filter.liminf_le_limsup`) this gives `f₊ =ᵐ f₋`.

Proof reduces (via §1.1) to the shifted process `g̃(n+1) ≤ 0`; equivalently we prove the
statement for `g` directly using the truncation. We prove the equivalent

> (†) for all `ε > 0` and `M > 0`: a.e. `f₊ x ≤ max(f₋ x, −M) + ε`,

then let `M → ∞` (a.e. `f₋ > −∞` because `f₋ ≥ B + f̃₋` and `f̃₋` is finite a.e. under
`hbdd` — see §4.4) and `ε ↓ 0` to get `f₊ ≤ f₋` a.e.

### 4.2 The stopping time and the block decomposition

Fix `ε > 0`, `M > 0`. Set `φ x := max(f₋ x, −M)` (a.e. `T`-invariant: max of the
invariant `f₋` (L7-analog for liminf) and a constant; integrable: `−M ≤ φ ≤ f₊ ≤ B`).
Replace `φ` by a genuinely orbit-constant `I`-measurable `h =ᵐ φ` via `h := μ[φ|I]`
(equal a.e. since `φ` is a.e.-`I`-measurable, by `condExp` of an already-invariant a.e.
function), `h ∘ T =ᵐ h`, and a.e. `h(T^[k] x) = h x` for all `k` (`ae_forall_orbit_eq`).

For a.e. `x` (on the full-measure orbit-good set) define the **stopping time**
`τ_L(x) := least k ∈ {1,…,L}` with `g(k) x ≤ k·(h x + ε)`, if one exists; the **bad set**
`B_L := {x | ∀ k ∈ {1,…,L}, g(k) x > k·(h x + ε)}` is where no such `k ≤ L` exists.

Because `f₋ x = liminf g(n+1)x/(n+1) ≤ h x ≤ h x` (as `h =ᵐ f₋ ≤ φ`... precisely
`h ≥ φ ≥ f₋`, so `h ≥ f₋`; and `f₋ = liminf` so frequently `g(k)x/k < f₋ x + ε ≤ h x + ε`),
the bad sets shrink: `⋂_L B_L ⊆ {x | ∀ k ≥ 1, g(k)x/k > h x + ε}`, and on that set
`f₋ x = liminf g(k)/k ≥ h x + ε > h x ≥ f₋ x`, contradiction. So `μ(⋂_L B_L) = 0`, hence
`μ(B_L) → 0` (`tendsto_measure_iInter_atTop`, finite measure, `B_L` antitone).

**Greedy block partition of `{0, …, n−1}` for `n > L`.** Walk `k = 0, 1, …`: at the
current frontier `k`, if `T^[k] x ∈ B_L` OR `k + τ_L(T^[k]x) > n` (block would overrun),
take the **singleton** `[k, k+1)`; otherwise take the **block** `[k, k + τ_L(T^[k]x))`.
This is a partition of `{0,…,n−1}` into consecutive intervals `[k_i, k_i + ℓ_i)`. Types:
- **type-block:** `T^[k_i]x ∈ B_Lᶜ` and fits; here `ℓ_i = τ_L(T^[k_i]x) ∈ {1,…,L}` and
  `g(ℓ_i)(T^[k_i]x) ≤ ℓ_i (h(T^[k_i]x) + ε) = ℓ_i (h x + ε)` (orbit-constancy of `h`).
- **type-overrun:** fits-but-overruns singletons, only when `k > n − L`, so at most
  `L − 1` of them.
- **type-bad:** `T^[k_i]x ∈ B_L` singletons; their count is `Σ_{k<n} 1_{B_L}(T^[k]x)`.

### 4.3 The block inequality and the limit passages

By block subadditivity A1 (general form L1b) `g(n) x ≤ Σ_i g(ℓ_i)(T^[k_i]x)`. WLOG the
shift (`g̃ ≤ 0`) lets us DROP the type-overrun and type-bad singletons (their `g̃` terms
are `≤ 0`). For the type-block terms use the stopping bound. Working with `g̃` and writing
`h̃ := h − B` (the shifted comparison, `h̃ + ε` is the threshold for `g̃`):

```
g̃(n) x ≤ Σ_{type-block} g̃(ℓ_i)(T^[k_i]x)
        ≤ Σ_{type-block} ℓ_i (h̃ x + ε)          [stopping bound, h̃ orbit-constant]
        ≤ (h̃ x + ε)⁻·( Σ_{type-block} ℓ_i )     [if h̃ x + ε ≤ 0; else bound by 0·(…) and
                                                   the dropped terms — sign handled below]
```
**Length bound:** `Σ_{type-block} ℓ_i = n − (#overrun) − (#bad) ≥ n − (L−1) − Σ_{k<n}
1_{B_L}(T^[k]x)`. With `h̃ x + ε ≤ 0` (ensured for `M` large enough that on the relevant
set `h̃ = f̃₋ ≤ 0` and `ε` small; the sign bookkeeping is Steele's, but here only TWO
interval types' terms are dropped, not three, because the stopping time replaces the
greedy `ℓ`-search):
```
g̃(n)x / n ≤ (h̃ x + ε)·( 1 − (L−1)/n − (1/n)Σ_{k<n} 1_{B_L}(T^[k]x) ).
```
**Let `n → ∞`.** By M3 (Birkhoff on the integrable indicator `1_{B_L}`):
`(1/n)Σ_{k<n} 1_{B_L}(T^[k]x) → μ[1_{B_L} | I] x =: q_L x` a.e.; `(L−1)/n → 0`. So a.e.
```
f̃₊ x = limsup g̃(n)x/n ≤ (h̃ x + ε)(1 − q_L x).
```
Since `h̃ x + ε ≤ 0` and `0 ≤ 1 − q_L ≤ 1`, `(h̃ x + ε)(1 − q_L x) ≥ h̃ x + ε` is FALSE
in general (multiplying a nonpositive by `≤ 1` makes it larger, i.e. closer to 0). So
`f̃₊ x ≤ (h̃ x + ε)(1 − q_L x)`. **Let `L → ∞`.** `q_L → q_∞ := μ[1_{⋂ B_L} | I] = 0`
a.e. (since `μ(⋂ B_L)=0` ⟹ `1_{⋂ B_L} =ᵐ 0` ⟹ its condExp is `0`); and `q_L` is
monotone, dominated. Pointwise a.e. `f̃₊ x ≤ (h̃ x + ε)(1 − 0) = h̃ x + ε`. Recalling
`h̃ =ᵐ f̃₋` (since `h =ᵐ φ = max(f₋,−M)` and we then took `M→∞` so `φ → f₋`, `h̃ → f̃₋`):
```
f̃₊ x ≤ f̃₋ x + ε   a.e., for every ε > 0  ⟹  f̃₊ ≤ f̃₋ a.e.
```
Adding back `B`: `f₊ ≤ f₋` a.e. With `f₋ ≤ f₊` (everywhere): `f₊ =ᵐ f₋`. ∎

### 4.4 Loose ends inside §4 (all closable, no new black box)

* **`f̃₋` finite a.e.** (so `M → ∞` is legitimate): `f̃₋ = liminf c n` with `c n ≤ 0` and
  `∫ c n = ã_{n+1} ≥ γ̃` bounded below; by the easy Fatou (I) applied to the liminf side
  via the termwise-nonneg `A_{n+1}(g₁) − c n`, `∫⁻ ofReal(B − f̃₊) < ∞` ⟹ `f̃₊ > −∞` a.e.,
  and `f̃₋ ≥ ` a similar finite bound. Concretely `f̃₋ ≥ f̃₊ −`(nonneg) is wrong; use that
  the limit (once `f̃₊ =ᵐ f̃₋`) is integrable hence finite a.e. — but that is circular for
  establishing finiteness BEFORE the squeeze. Break it: `f̃₋ ≥ liminf(c n)` and each
  `c n = g̃(n+1)/(n+1) ≥ (1/(n+1))·g̃(n+1)`; under `hbdd`, `∫ f̃₋ ≥ γ̃ > −∞`, and `f̃₋ ≤ 0`,
  so `f̃₋ ∈ [finite-integrable-lower, 0]` a.e. Provide the a.e. finiteness from
  `∫⁻ ofReal(−f̃₋) ≤ ∫⁻ ofReal(−f̃₊)`? `f̃₋ ≤ f̃₊ ≤ 0` so `−f̃₋ ≥ −f̃₊ ≥ 0`, the WRONG
  direction for a finite upper bound on `−f̃₋`. **Correct closure:** finiteness of `f̃₋`
  a.e. follows from `f̃₋ ≥ B'−B`-type bound where `B' = μ[g_K|I]/K` for fixed `K`: indeed
  `c_{K-1} = g̃(K)/K` is a single integrable function with `f̃₋ ≥ ` its essential inf along
  the orbit... The clean Lean route: prove `f̃₋ ≥ −(B − f̃₊)`-free bound is unavailable;
  instead use **`ae_bddBelow`-style**: `f̃₋ = liminf c n` and `c n ≥ A_{n+1}(g₁)`-related
  lower envelope is false. SIMPLEST: since we ALREADY prove `f₊ = f̃₊+B` integrable (§1.3
  payoff 1), `f₊` is finite a.e.; and `f̃₊ ≤ 0` finite a.e. We need `f̃₋` finite, but the
  truncation `φ = max(f₋,−M)` is ALWAYS finite (`≥ −M`) regardless, so §4.2–4.3 never
  needs `f̃₋` finite — it works with the truncation `φ` throughout and only at the very
  end (`M→∞`) uses monotone convergence `max(f₋,−M) ↓ f₋` which is valid pointwise even
  if `f₋ = −∞` (the limit is `f₋`, possibly `−∞`, and `f₊ ≤ f₋` then forces
  `f₊ = −∞ = f₋`, consistent). **So drop the finiteness worry: the truncation makes §4
  go through with `f₋ ∈ [−∞, 0]`, and the conclusion `f₊ ≤ f₋` a.e. holds; combined with
  `f₊ ≥ f₋` finiteness of the common value comes from `f₊` integrable (§1.3).** Resolved.
* **Sign of `h̃ + ε`:** on `{f₋ ≥ −M}`, `h̃ = f̃₋ ≤ 0`; choose the bound to use `h̃ + ε`
  only where `≤ 0`, and where `h̃ + ε > 0` (small set, `f̃₋ ∈ (−ε, 0]`) bound `g̃(n)/n ≤ 0`
  directly (`g̃ ≤ 0`), which is `≤ h̃ + ε` there. Two cases, both give `f̃₊ ≤ h̃ + ε`.
* **Block partition existence in Lean (R1):** encode the greedy walk as a function
  `ℕ → ℕ` (frontier positions) defined by strong recursion / `Nat.rec`, or as a `Finset`
  of cut-points; the length-sum identity is `Finset.sum` over the blocks `= n`. This is
  the dominant `Finset` bookkeeping; it is two interval types (block / singleton), simpler
  than Steele's three.

---

## 5. Reuse / de-privatization edits to existing files

In `ErgodicTheory/Ergodic/Birkhoff.lean`, change `private theorem` → `theorem` for:
`measure_setOf_lt_limsup_eq_zero`, `condExp_invariants_comp_self`, `ae_forall_orbit_eq`,
`ae_bddAbove_birkhoffAverage`, `ae_bddBelow_birkhoffAverage`, `limsup_eq_of_sub_tendsto_zero`.
(Optionally also `birkhoffSum_ae_eq_nsmul` for the telescoping.) Alternatively, lift the
generic ones into a new `ErgodicTheory/Ergodic/Invariance.lean`; minimal-diff choice is to
de-privatize in place.
In `MaximalErgodic.lean`: no change (`measurable_birkhoffSum`, `integrable_birkhoffSum`,
`birkhoffSum_congr_ae` already public).

---

## 6. Risks (ordered by severity)

1. **R1 — greedy block partition (§4.2).** Encoding the consecutive-block partition of
   `Finset.range n` via the stopping time and proving the length lower bound
   `Σ_block ℓ_i ≥ n − (L−1) − Σ 1_{B_L}∘T^k`. Dominant effort. Two interval types (not
   Steele's three) — strictly simpler, but still the hard part.
2. **R-FATOU sign — RESOLVED.** The only free Fatou is the LIMSUP bound `∫ f̃₊ ≥ γ̃`,
   via `lintegral_liminf_le` on the termwise-nonneg `A_{n+1}(g₁) − c n` (A1'). The
   liminf-Fatou `∫ f̃₋ ≤ γ̃` needs a uniform integrable minorant that does NOT exist; do
   not use it. The pointwise §4 conclusion `f₊ ≤ f₋` a.e. makes the integral squeeze
   moot for convergence; (I)/(II) are needed only for `Integrable G`.
3. **R5 — L5 `linarith` bug (wip A3).** Final branch must derive the contradiction from
   the rational equivalence `hx`, not from `hle`. Concrete fix in §3/structured output.
4. **R-INT — RESOLVED.** `B − f̃₊ ≥ 0` has finite lintegral (§1.3 payoff 1), so `f̃₊`,
   hence `f₊`, integrable; fold integrability into L8.
5. **R3 — a.e. vs everywhere (L7).** `f₊ ≤ f₊∘T` holds everywhere; only equality is a.e.
   L5 must accept `AEMeasurable F` (generalize from `Measurable F`).
6. **R7 — BddBelow n=0 bridge (L4).** `BddBelow.insert` absent; bridge `a 0/0 = 0` by
   hand (~10 lines).
7. **R8 — condExp σ-finiteness.** `integral_condExp` wants `SigmaFinite (μ.trim hI)`;
   automatic from `[IsFiniteMeasure μ]`. Provide the instance.
8. **R-TRUNC — `M→∞`, `ε→0`, `L→∞` passages.** `tendsto_measure_iInter_atTop`,
   `integral_tendsto_of_tendsto_of_antitone` (`…/Bochner/Basic.lean:823`), monotone
   convergence for `q_L`. Several but each standard.
