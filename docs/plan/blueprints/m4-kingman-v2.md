# Blueprint v2 — M4: Kingman's subadditive ergodic theorem (`tendsto_kingman`)

**Target file:** `ErgodicTheory/Ergodic/Kingman.lean`
**Layer / milestone:** L2 / M4 (analytic engine of the Oseledets MET).
**Status of inputs:** M1/M2/M3 are all **proved sorry-free** in
`ErgodicTheory/Ergodic/{MaximalErgodic,Birkhoff}.lean`. Baseline `lake build` is green
(Kingman has the two target `sorry`s). All Mathlib names below were grepped on disk in
the pinned tree (`v4.30.0-rc2`) **this session** and are confirmed present unless flagged.

This v2 supersedes `m4-kingman.md` and reconciles three upstream research outputs
(design-lead JSON, source-grounding JSON, inventory JSON) that **conflicted with each
other** on the inequality directions. The conflict is resolved from scratch in §1.

---

## 0. Executive summary

* **Route: pointwise Katznelson–Weiss / Steele, NOT an integral squeeze.** The a.e.
  convergence is closed by a *pointwise* sandwich (`liminf ≤ limsup` everywhere, plus the
  hard `limsup ≤ liminf` a.e.), exactly mirroring the existing M3 proof
  (`tendsto_birkhoffAverage_ae`, which sandwiches `limsup ≤ μ[g|I] ≤ liminf`). The
  Avila–Bochi *integral* squeeze `∫f♭ ≥ L ≥ ∫f♯` is **not used for convergence** — it is
  only used to get `Integrable G`.
* **This dissolves the entire "which direction is Fatou" wobble.** The wobble existed only
  because the design lead tried to route convergence through an integral squeeze, which
  forces a delicate Fatou sign. The pointwise route needs Fatou **once**, and only for
  integrability, where the sign is unambiguous (see §1.4).
* **The single hard lemma is L9** (`ae_limsup_le_liminf_div`): the stopping-time / greedy
  block partition. Its full gap-free proof is §4. Everything else is light.
* **De-privatize 6 lemmas in `Birkhoff.lean`** (§5); add 4 imports to `Kingman.lean`. No
  change to `MaximalErgodic.lean`.

---

## 1. The mathematics, pinned and re-derived (resolves the conflict)

### 1.0 The conflict, named

The three upstream outputs disagree:

| Output | Claims the FREE/EASY Fatou bound is | Claims HARD bound(s) |
|---|---|---|
| design-lead **scratch §1.2** | `∫ f̃₊ ≥ γ̃` (a **limsup** lower bound) | `∫ f̃₊ ≤ γ̃` |
| design-lead **exec-summary / JSON** | `γ̃ ≤ ∫ f̃₋` (a **liminf** lower bound) | (inconsistent within itself) |
| **source-grounding** (Avila–Bochi) | `∫ f♭ ≤ L` (a **liminf upper** bound) | `L ≤ ∫f♭` AND `∫f♯ ≤ L` |

These cannot all be right. **Resolution: the source-grounding (Avila–Bochi) statement of
the Fatou direction is the correct one** — Fatou *only ever* yields `∫ liminf ≤ liminf ∫`,
i.e. an **upper** bound on `∫(liminf)`. The design-lead scratch's "`∫ f̃₊ ≥ γ̃` is the free
Fatou bound" is **wrong in sign** (it is a *lower* bound on a *limsup*, which Fatou cannot
deliver directly); its own JSON then contradicts the scratch. **But none of this matters
for convergence**, because we do not use an integral squeeze at all (§1.1). The only place
Fatou appears is §1.4, where we need it in exactly the Avila–Bochi orientation and only to
bound the *positive part* of an integrable difference.

### 1.1 The squeeze is POINTWISE (the key simplification)

Write `c n x := g (n+1) x / (n+1)`, `f₊ x := limsup_n (c n x)`, `f₋ x := liminf_n (c n x)`.
The target a.e. limit is `G := f₋`. The convergence statement
`Tendsto (c · x) atTop (𝓝 (f₋ x))` follows pointwise from
`tendsto_of_le_liminf_of_limsup_le` once we know, a.e.,

> (S1) `f₊ x ≤ f₋ x`   [hard, L9]   and   (S2) `f₋ x ≤ f₊ x`   [trivial, `liminf_le_limsup`].

This is **structurally identical** to the existing M3 proof, where the role of the common
value is played by `μ[g|I]`. **No integral of `f₊` or `f₋` enters the convergence proof.**
This is Steele's Step 3 (digest lines 123–128) and Katznelson–Weiss; it is *cleaner* than
Avila–Bochi's integral squeeze, which the design-lead JSON adopted and then got tangled in.

The boundedness side-conditions for (S1)/(S2) and for `tendsto_of_le_liminf_of_limsup_le`
(`IsBoundedUnder (·≤·)` and `(·≥·)` of `c · x`) come from `ae_bddAbove_birkhoffAverage` /
`ae_bddBelow_birkhoffAverage` applied to `g₁`, transported through the WLOG shift (§1.3) —
see L10.

### 1.2 What the integral facts are still needed for: `Integrable G` only

`G = f₋ =ᵐ f₊`. We need `Integrable G`. Sandwich:
* **upper:** `f₊ ≤ B := μ[g₁ | invariants T]` a.e. (loose envelope; `B` integrable). Proof:
  A1' gives `c n ≤ birkhoffAverage ℝ T g₁ (n+1)`, and M3 gives
  `birkhoffAverage ℝ T g₁ (n+1) → B` a.e., so `f₊ = limsup c n ≤ limsup A_{n+1}(g₁) = B`
  a.e. (also obtainable from `measure_setOf_lt_limsup_eq_zero`).
* **lower:** `f₊` (hence `G`) is integrable because `B − f₊ ≥ 0` has *finite lintegral*
  (Fatou, §1.4), so `B − f₊` is integrable, so `f₊ = B − (B − f₊)` is integrable. This is
  the **one** genuine use of Fatou, in the unambiguous Avila–Bochi orientation.

So: the math has exactly one Fatou step, it is the `∫ liminf ≤ liminf ∫` orientation, and
it is used only to certify `Integrable G`. The "direction wobble" never touches convergence.

### 1.3 WLOG shift to a non-positive process (needed for §4, not for §1.1)

`g̃ (n) x := g n x − birkhoffSum T g₁ n x`. Then (A1', L1) `g̃ (n+1) x ≤ 0`, and
`c n x = g̃ (n+1) x / (n+1) + birkhoffAverage ℝ T g₁ (n+1) x`. Since
`birkhoffAverage ℝ T g₁ (n+1) → B` a.e. (M3), a.e. `f₊ = f̃₊ + B`, `f₋ = f̃₋ + B`, where
`f̃₊ := limsup (g̃(n+1)/(n+1)) ≤ 0`, `f̃₋ := liminf (…) ≤ 0`. Hence **`f₊ ≤ f₋ a.e. ⟺
f̃₊ ≤ f̃₋ a.e.`** (adding the common a.e.-finite `B` preserves `≤`). L9 proves `f̃₊ ≤ f̃₋`
for the non-positive process; the shift transfers it to `f₊ ≤ f₋`.

> **Note on `g 0`:** A1' is stated only for `n+1` (it is *false* at `n=0`: subadditivity at
> `(0,0)` forces `g 0 ≥ 0`, the wrong sign). Kingman's conclusion at `n=0` is vacuous since
> the statement's sequence is `(n:ℝ)⁻¹ * g n` whose `n=0` term is `0⁻¹·g 0 = 0`; L0 handles
> the reindex so `g 0` is never touched.

### 1.4 The Fatou step, fully pinned (the ONLY Fatou use)

`u n x := ENNReal.ofReal (birkhoffAverage ℝ T g₁ (n+1) x − c n x)`. By A1' the real
argument is `≥ 0`, so `ofReal` is faithful and `u n` is measurable (representatives, L6
style). `lintegral_liminf_le` (`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231`,
needs `Measurable`):

```
∫⁻ liminf_n (u n) ≤ liminf_n (∫⁻ u n).
```
* `liminf_n (A_{n+1}(g₁) x − c n x) = B x − f₊ x` a.e.
  (`A_{n+1}(g₁) → B` converges (M3), so `liminf(conv − c) = lim conv − limsup c = B − f₊`).
* `∫⁻ u n = ENNReal.ofReal (∫ (A_{n+1}(g₁) − c n))` by `ofReal_integral_eq_lintegral_ofReal`
  (integrand integrable nonneg). `∫ A_{n+1}(g₁) = ∫ g₁` (measure-preservation,
  `integral_comp_iterate`/`birkhoffAverage`), `∫ c n = a(n+1)/(n+1)`; both bounded.
* `liminf_n ofReal(∫g₁ − a(n+1)/(n+1)) = ofReal(∫g₁ − γ) < ∞` (`a(n+1)/(n+1) → γ`, `hbdd`).

So `∫⁻ ofReal(B − f₊) < ∞`, giving (i) `B − f₊ ≥ 0` integrable ⟹ `f₊`, `G` integrable
(`integrable_of_le_of_le` or `B − (B−f₊)`), and — if one *wants* the integral identity —
(ii) `∫ f₊ ≥ γ` via `∫ B = ∫ g₁` (`integral_condExp`). We only need (i).

**Toy check (`g̃(n+1) = −n`, deterministic, subadditive `−(m+n) ≤ −m + −n`):**
`f̃₊ = f̃₋ = −1`; `a(n+1)/(n+1) = −n/(n+1) → −1 = γ`. (S1) `−1 ≤ −1` ✔, (S2) `−1 ≤ −1` ✔,
Fatou `∫⁻ ofReal(B − f₊) = ofReal(∫g₁ + 1) < ∞` ✔. Non-vacuous and tight.

---

## 2. Reused / de-privatized Oseledets machinery

| Lemma | File | Used for | Action |
|---|---|---|---|
| `tendsto_birkhoffAverage_ae` (M3) | Birkhoff.lean | shift `A_{n+1}(g₁)→B`; Birkhoff on `1_{B_L}` (§4 Step 5) | **public already** |
| `condExp_invariants_comp_self` | Birkhoff.lean | `B∘T =ᵐ B`; `h∘T =ᵐ h` | **de-privatize** |
| `ae_forall_orbit_eq` | Birkhoff.lean | orbit-constancy `h(T^[k]x)=h x` (§4 Step 4) | **de-privatize** |
| `ae_bddAbove_birkhoffAverage` | Birkhoff.lean | `IsBoundedUnder (·≤·)` for limsup (L7, L10) | **de-privatize** |
| `ae_bddBelow_birkhoffAverage` | Birkhoff.lean | `IsBoundedUnder (·≥·)` for liminf (L7, L10) | **de-privatize** |
| `limsup_eq_of_sub_tendsto_zero` | Birkhoff.lean | vanishing-perturbation limsup/liminf (L7) | **de-privatize** |
| `measure_setOf_lt_limsup_eq_zero` | Birkhoff.lean | (optional) loose envelope `f₊ ≤ B` | **de-privatize (optional)** |
| `measurable_birkhoffSum`, `integrable_birkhoffSum`, `birkhoffSum_congr_ae` | MaximalErgodic.lean | representatives, shift | **public already** |

`Birkhoff.lean` lemmas needed only *via* M3's public face (`tendsto_birkhoffAverage_ae`)
need no de-privatization. The de-privatization list is the 6 in the table (5 mandatory +
1 optional). Alternative: lift the generic ones into `ErgodicTheory/Ergodic/Invariance.lean`;
minimal-diff is in-place de-privatization.

---

## 3. Dependency-ordered lemma ladder

Scope: `variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}`.
Difficulties: trivial / easy / moderate / hard.

See the structured-output `ordered_lemmas` for exact signatures + per-lemma strategies.
Ladder order (each depends only on earlier ones):

```
L0  reindex  (n)⁻¹·g n  ↔  g(n+1)/(n+1)                     [trivial]
L1  A1'  g(n+1) ≤ birkhoffSum T g₁ (n+1)                    [easy]   (copy from wip)
L2  integral_comp_iterate  ∫ g n (T^[m]·) = ∫ g n           [easy]   (copy from wip)
L3  integral_subadditive  Subadditive (∫ g ·)               [easy]   (copy from wip)
L4  exists_fekete  γ + lower bounds + Tendsto                [moderate]
L5  ae_eq_comp_of_le_comp  (FIX linarith; AEMeasurable)      [moderate] (fix from wip)
L6  aemeasurable_limsup_div / liminf_div                     [moderate]
L7  limsup_div_comp_ae / liminf_div_comp_ae  (invariance)    [moderate]
L8  int_limsup_div_integrable  (Fatou ⟹ Integrable f₊)      [hard]
L1b le_sum_blocks  (general block subadditivity)             [moderate] (for L9 only)
L9  ae_limsup_le_liminf_div   ← THE HARD LEMMA (§4)          [hard]
L10 tendsto_kingman   (MAIN: pointwise squeeze + assemble)   [moderate]
L11 tendsto_kingman_ergodic                                  [easy]
```

---

## 4. Full gap-free proof of L9 (the stopping time)

### 4.0 Why M1 / the M3 template cannot shortcut this (honest finding)

`measure_setOf_lt_limsup_eq_zero` proves, for a **single** integrable `f`,
`limsup A_n(f) ≤ μ[f|I]` a.e., by feeding `E'.indicator (f − μ[f|I] − ε)` to M1; this works
because `birkhoffSum f` is an **exact additive cocycle** that telescopes against the
orbit-constant `μ[f|I]`. For Kingman, `g(n+1)` is only *sub-dominated* by `birkhoffSum g₁
(n+1)` (A1'), never *equal* to a Birkhoff sum of a fixed function. Feeding `f = g₁` yields
only the loose envelope `f₊ ≤ B` (which we reuse for integrability, §1.2), never the sharp
`f₊ ≤ f₋`. The Fekete constant appears only through the **block-subadditive** structure
(general A1, L1b), i.e. the stopping partition below. **Confirmed:** no single integrable
`f` makes the superlevel set `{c n > h + ε}` a Birkhoff-positive set. M1 is used only
*indirectly*, as the gate to M3, which L9 reuses in Step 5 (Birkhoff on `1_{B_L}`).

### 4.1 Statement (pointwise, on the shifted process)

> **L9.** `[IsFiniteMeasure μ] (hT) (hTm : Measurable T) (hsub) (hint) (hbdd)`. For a.e.
> `x`, `limsup_n (g(n+1)x/(n+1)) ≤ liminf_n (g(n+1)x/(n+1))`.

Via §1.3 it suffices to prove `f̃₊ ≤ f̃₋` a.e. for `g̃(n+1) ≤ 0`. We prove the equivalent

> (†) `∀ ε>0, ∀ M>0: a.e. f̃₊ x ≤ max(f̃₋ x, −M) + ε`,

then `M → ∞` (`max(f̃₋,−M) ↓ f̃₋` pointwise, even at `−∞`) and `ε ↓ 0` (rational, `ae_all_iff`)
give `f̃₊ ≤ f̃₋` a.e. The truncation by `−M` keeps everything finite a.e. so no `EReal`
bookkeeping is needed (R-EReal sidestepped).

### 4.2 Construction (fix `ε>0`, `M>0`)

* `φ x := max (f̃₋ x) (−M)`; a.e. `T`-invariant (L7 liminf variant + `max` with a constant),
  and `−M ≤ φ ≤ 0`.
* `h := μ[φ | invariants T]`. Then `h =ᵐ φ` (φ is a.e. `I`-measurable, being invariant),
  `h∘T =ᵐ h` (`condExp_invariants_comp_self`), and a.e. `h(T^[k]x) = h x` for **all** `k`
  (`ae_forall_orbit_eq`). Also `h ≤ 0` a.e. Work on the full-measure **GOOD** set where
  (i) orbit-constancy of `h`, (ii) `h x = φ x`, (iii) `f̃₋ x = liminf g̃(n+1)x/(n+1)`,
  (iv) the Step-5 Birkhoff convergence holds.
* **Bad sets:** `B_L := {x | ∀ k, 1≤k → k≤L → g̃ k x > k·(h x + ε)}`, antitone in `L`.
  On `⋂_L B_L ∩ GOOD`: `f̃₋ x = liminf g̃(k)/k ≥ h x + ε`; but `h x = φ x ≥ f̃₋ x`, so
  `f̃₋ x ≥ f̃₋ x + ε`, contradiction. Hence `μ(⋂_L B_L)=0`, so `μ(B_L) → 0`
  (`tendsto_measure_iInter_atTop`; `B_L` NullMeasurable via L6-style representatives,
  finite measure).

### 4.3 Greedy 2-type block partition of `{0,…,n−1}`, `n > L`

Frontier walk `k = 0,1,…`. At frontier `k`, set `y = T^[k] x`. Let
`τ := (least t ∈ {1,…,L} with g̃ t y ≤ t·(h y + ε))` if it exists.
* if `y ∈ B_L` (no such `τ`) **or** `k + τ > n` (overrun): cut **singleton** `[k,k+1)`;
* else: cut **block** `[k, k+τ)`.

This partitions `{0,…,n−1}` into consecutive blocks `[k_i, k_i+ℓ_i)`, `Σ ℓ_i = n`. Types:
* **type-block:** `ℓ_i = τ ∈ {1,…,L}`, and `g̃(ℓ_i)(T^[k_i]x) ≤ ℓ_i·(h(T^[k_i]x)+ε) =
  ℓ_i·(h x + ε)` (orbit-constancy (i)).
* **type-overrun:** singletons, only when `k > n − L`, so `≤ L−1` of them.
* **type-bad:** `y ∈ B_L` singletons, count `= Σ_{k<n} 1_{B_L}(T^[k]x)`.

**Lean encoding (R1, the dominant effort):** define the frontier sequence by strong
recursion `ℕ → ℕ`, `k_{i+1} = k_i + step(T^[k_i] x)` with `step` the chosen length; the
blocks are `Finset.range`-indexed; `Σ ℓ_i = n` is `Finset.sum` telescoping. Use
`Function.iterate_add_apply` (`f^[m+n] x = f^[m] (f^[n] x)`) to relate
`T^[k_i] x` along the walk, and L1b (`le_sum_blocks`) for block subadditivity.

### 4.4 Block inequality and the three limit passages

By L1b: `g̃(n)x ≤ Σ_i g̃(ℓ_i)(T^[k_i]x)`. Since `g̃ ≤ 0`, drop overrun + bad terms (each
`≤ 0`); bound type-block terms by the stopping bound:
```
g̃(n)x ≤ Σ_block ℓ_i·(h x + ε).
```
Length lower bound: `Σ_block ℓ_i = n − #overrun − #bad ≥ n − (L−1) − Σ_{k<n}1_{B_L}(T^[k]x)`.
**Sign split on `h x + ε`:**
* `h x + ε ≤ 0`: a nonpositive factor times the *smaller* length bound gives a *larger*
  product, so `Σ_block ℓ_i·(h x+ε) ≤ (h x+ε)·(n−(L−1)−Σ1_{B_L}∘T^k)`. Divide by `n`:
  `g̃(n)x/n ≤ (h x+ε)(1 − (L−1)/n − (1/n)Σ_{k<n}1_{B_L}(T^[k]x))`.
* `h x + ε > 0` (small set, `f̃₋ x ∈ (−ε,0]`): `g̃(n)x/n ≤ 0 < h x+ε`, and since the RHS
  factor `(1 − …) ∈ [0,1]` with `h x+ε>0`, `0 ≤ (h x+ε)(1−…)`; same bound holds.

**Step 5 (`n → ∞`).** `1_{B_L}` integrable (indicator of NullMeasurable set, finite
measure). M3: `(1/n)Σ_{k<n}1_{B_L}(T^[k]x) = birkhoffAverage T 1_{B_L} n x → q_L x :=
μ[1_{B_L}|I] x` a.e.; `(L−1)/n → 0`. Taking `limsup_n` (RHS converges, `(h x+ε)` constant
in `n`):
```
f̃₊ x ≤ (h x + ε)(1 − q_L x)   a.e.
```
**Step 6 (`L → ∞`).** `1_{B_L} ↓ 1_{⋂B_L} =ᵐ 0`, so `q_L = μ[1_{B_L}|I]` is antitone with
`∫ q_L = μ(B_L) → 0` (`integral_condExp` on the indicator; `q_L ≥ 0` by `condExp_nonneg`);
`integral_tendsto_of_tendsto_of_antitone` (`Bochner/Basic.lean:823`) + `q_L ≥ 0` ⟹
`q_L → q_∞` with `∫ q_∞ = 0`, `q_∞ ≥ 0` ⟹ `q_∞ =ᵐ 0`. Pass to the limit:
`f̃₊ x ≤ (h x + ε)(1 − 0) = h x + ε = φ x + ε` a.e.
**Step 7 (`M → ∞`, `ε → 0`).** `φ = max(f̃₋, −M) ↓ f̃₋` as `M → ∞`; so a.e.
`f̃₊ x ≤ f̃₋ x + ε` for all rational `ε > 0` (`ae_all_iff`); `ε ↓ 0` ⟹ `f̃₊ ≤ f̃₋` a.e. ∎

Adding `B` (§1.3): `f₊ ≤ f₋` a.e.

---

## 5. Required edits to existing files

* **`ErgodicTheory/Ergodic/Birkhoff.lean`** — change `private theorem` → `theorem` for:
  `condExp_invariants_comp_self`, `ae_forall_orbit_eq`, `ae_bddAbove_birkhoffAverage`,
  `ae_bddBelow_birkhoffAverage`, `limsup_eq_of_sub_tendsto_zero` (mandatory), and
  `measure_setOf_lt_limsup_eq_zero` (optional — only if the loose envelope is taken from it
  rather than re-derived from M3). Add `/-- … -/` docstrings if making them public triggers
  a lint (the repo lints public decls; they already have doc-comments — verify on build).
* **`ErgodicTheory/Ergodic/Kingman.lean`** — add imports:
  `import Mathlib.Analysis.Subadditive`,
  `import Mathlib.MeasureTheory.Integral.Lebesgue.Add` (Fatou),
  `import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator` (`condExp_indicator`),
  `import Mathlib.MeasureTheory.Integral.DominatedConvergence`
    (or `Mathlib.MeasureTheory.Integral.Bochner.Basic`, which already carries
    `integral_tendsto_of_tendsto_of_antitone`).
  The `[IsFiniteMeasure μ]` hypothesis is already on the fixed `tendsto_kingman` statement.
* **`ErgodicTheory/Ergodic/MaximalErgodic.lean`** — **no change**.

---

## 6. Honest risk list (severity-ordered)

1. **R1 (dominant) — the greedy 2-type partition (§4.3).** Encoding the frontier walk
   (`ℕ→ℕ` strong recursion), the consecutive-block `Finset`, `Σ ℓ_i = n`, and the length
   lower bound `Σ_block ℓ_i ≥ n − (L−1) − Σ1_{B_L}∘T^k`. This is the heaviest `Finset`/index
   bookkeeping in the whole MET. Two interval types (simpler than Steele's three), but still
   the hard part. **Budget the most time here; flag if it exceeds the per-`sorry` budget**
   — a `sorry -- BLOCKED:` on the length bound is the acceptable fallback if it overruns.
2. **R-CRIT (confirmed finding, not a risk to fix) — M1 does not shortcut the hard
   direction.** The M3 template (`measure_setOf_lt_limsup_eq_zero`) yields only the loose
   `f₊ ≤ B`, never `f₊ ≤ f₋`; the Fekete constant is invisible to any single-function
   template (§4.0). The stopping combinatorics is unavoidable. This contradicts the old
   blueprint's hope that the hard direction "falls out of M1 in a page."
3. **R-FATOU (resolved by route change) — direction confusion is moot.** Convergence is a
   *pointwise* squeeze (§1.1); Fatou is used **once**, only for `Integrable G`, in the
   unambiguous `∫ liminf ≤ liminf ∫` orientation (§1.4). Do **not** attempt an integral
   squeeze for convergence — that is what tangled all three upstream outputs.
4. **R5 (concrete bug to fix) — L5 `ae_eq_comp_of_le_comp` final `linarith`.** The wip
   branch `F x < F (T x)` does `have := hle x; linarith`, which is *consistent* (no
   contradiction). FIX: in that branch pick rational `c` with `F x < c < F (T x)`
   (`exists_rat_btwn`); `c ≤ F (T x)` ⟹ `x ∈ T⁻¹{c ≤ F}` ⟹ by `hx c`, `x ∈ {c ≤ F}` ⟹
   `c ≤ F x`, contradicting `F x < c`. Both branches use `hx`, neither uses `hle` at the
   end. (Mirror of the already-correct `F (T x) < F x` branch.)
5. **R3 — `f₊`/`f₋` are AEMeasurable, not Measurable (L6).** L5 must accept `AEMeasurable F`
   (use a measurable representative `F0 =ᵐ F` for the level-set `NullMeasurableSet`, transfer
   the conclusion). The pointwise `f₊ ≤ f₊∘T` is *everywhere*; only the equality is a.e.
6. **R-INT (resolved) — integrability is not circular.** `B − f₊ ≥ 0` has finite lintegral
   (§1.4), so `B − f₊` integrable, so `f₊ = B − (B−f₊)` integrable; fold into L8 *before* L9
   (L8 does not depend on L9).
7. **R7 — `BddBelow.insert` absent (L4).** The `n+1`-indexed `hbdd` must bridge to the
   `n`-indexed `range (∫g·/·)` for `Subadditive.tendsto_lim`. The `n=0` point is
   `(∫g 0)/0 = 0` (`div_zero`); extend a bounded-below set by one point by hand
   (`⟨min lb 0, …⟩` via `rcases n`, ~10 lines).
8. **R8 — `SigmaFinite (μ.trim hI)` for `integral_condExp`.** **Automatic** from
   `[IsFiniteMeasure μ]` (`isFiniteMeasure_trim` instance + `IsFiniteMeasure → SigmaFinite`);
   verified present. Provide `hI := MeasurableSpace.invariants_le T` as the existing Birkhoff
   proofs do; instance resolution finds the rest.
9. **R-TRUNC — the three limit passages (§4.4 Steps 5–7).** Each needs a boundedness/
   domination witness: `tendsto_measure_iInter_atTop` (`MeasureSpace.lean:637`, verified),
   `integral_tendsto_of_tendsto_of_antitone` (`Bochner/Basic.lean:823`, verified), `ae_all_iff`
   over rational `ε`. All standard; the truncation by `−M` keeps witnesses finite.
10. **R-NAMES (inventory corrections, do not trip on these):**
    - `Filter.tendsto_add_atTop_iff_nat` **EXISTS** (inventory wrongly flagged absent; used
      in Mathlib `Exponential.lean`). Safe for L0/L4 reindexing.
    - The ergodic corollary should use `Ergodic.ae_eq_const_of_ae_eq_comp_ae`
      (`Dynamics/Ergodic/Function.lean:103`, takes `AEStronglyMeasurable`), exactly as the
      existing M3 corollary does — **not** the JSON's `…_comp₀` (which needs `NullMeasurable`;
      both exist, `_ae` is cleaner).
    - Bochner-integral Fatou is genuinely **absent**; use `lintegral_liminf_le` + the
      `ofReal` shift (§1.4). This is the one real Mathlib gap and the route accounts for it.

---

## 7. Confidence

**Medium.** The analytic backbone (L0–L8, L10, L11) is light and reuses proven M3 machinery
almost verbatim; the route change to a *pointwise* squeeze removes the only genuine source
of design error (the Fatou-direction wobble). The single concentrated risk is **R1**, the
`Finset` partition combinatorics in L9 — the only place a `sorry -- BLOCKED:` is plausible
if the index bookkeeping overruns the per-lemma budget. Closing M4 fully sorry-free hinges
entirely on L9's partition; everything else is high-confidence.
