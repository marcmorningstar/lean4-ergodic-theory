# L9 implementation refinements — addendum to `m4-kingman-v2.md`

Two refinements found while reviewing v2 §4. The v2 blueprint is the authority; this
sharpens the two hardest pieces. Read v2 §4 first, then this.

---

## A. Cleaner encoding of the stopping partition: the *induced sequence* `Sⱼ`

v2 §4.3 describes a generic "greedy 2-type block partition with overrun singletons". That
is correct but the overrun-singleton bookkeeping (≤ L−1 of them, near the right end) is
extra pain. The following **induced-sequence** encoding is equivalent, sharper, and much
lighter in Lean: there are **no per-block overrun singletons** — a single remainder term
handles the right end.

Fix `x` on the GOOD set (where `h` is orbit-constant: `h (T^[k] x) = h x =: hx` for all
`k`, from `ae_forall_orbit_eq`; `h := μ[φ|I]`, `φ := max (f̃₋) (−M)`, `H := hx + ε`).
Work on the **non-positive** process `g̃` (`g̃ (n+1) ≤ 0`, v2 §1.3).

**Stopping length.** `τ : X → ℕ`,
`τ y := if (∃ t ∈ Finset.Icc 1 L, g̃ t y ≤ t * (h y + ε)) then (least such t) else 1`.
Implement the "least such t" with `Nat.find` on the decidable predicate, or
`Finset.min'` over `{t ∈ Icc 1 L | g̃ t y ≤ t*(h y+ε)}`. Always `1 ≤ τ y ≤ L`.
On the bad set `B_L` (defined below) the witness set is empty, so `τ y = 1`.

**Induced sequence.** `ℓ : ℕ → ℕ`, `ℓ i := τ (T^[S i] x)`, where `S : ℕ → ℕ`,
`S 0 = 0`, `S (i+1) = S i + ℓ i`. So `S i = ∑_{j<i} ℓ j` (matches L1b's offset exactly)
and, since every `ℓ i ≥ 1`, `S` is **strictly increasing** and `S i ≥ i` (easy induction).

**Block count for a given `n`.** `m := Nat.findGreatest (fun k => S k ≤ n) n` (or
`(Finset.filter (fun k => S k ≤ n) (range (n+1))).max'`). Because `S i ≥ i`, `{k | S k ≤ n}`
is finite and `S m ≤ n < S (m+1)`. The right-end gap `n − S m` satisfies
`0 ≤ n − S m < L` (since `S (m+1) = S m + ℓ m ≤ S m + L` and `n < S (m+1)`).

**The block inequality (uses L1b + nonpositivity, no overrun singletons).**
```
g̃ n x ≤ g̃ (S m) x                       -- subadditivity at (S m, n − S m); remainder g̃(n−S m)(…) ≤ 0
       ≤ ∑_{i<m} g̃ (ℓ i) (T^[S i] x)     -- L1b (le_sum_blocks), all ℓ i ≥ 1
```
Split the sum by whether `y_i := T^[S i] x ∈ B_L`:
* `y_i ∉ B_L`: `ℓ i = τ y_i` is a *good* stop, so `g̃ (ℓ i) y_i ≤ ℓ i * (h y_i + ε)` and
  `h y_i = hx` (orbit-constancy) ⟹ term `≤ ℓ i * H`.
* `y_i ∈ B_L`: `ℓ i = 1`, term `g̃ 1 y_i ≤ 0`.
Hence
```
g̃ n x ≤ H * (∑_{good i<m} ℓ i)  = H * (S m − Bcount),   Bcount := #{i<m | y_i ∈ B_L}.
```
(`∑_{i<m} ℓ i = S m`; good + bad split; bad blocks have `ℓ = 1`.)

**Length / count bounds.**
* `S m ≥ n − L + 1`  (from `S m > n − L`).
* `Bcount = ∑_{i<m} 1_{B_L}(T^[S i] x) ≤ ∑_{k<n} 1_{B_L}(T^[k] x) =: I n`
  (the `S i`, `i<m`, are **distinct** indices in `[0,n)` since `S` is strictly increasing
  and `S (m−1) < S m ≤ n`; summing a nonneg function over a subset).

**Two sign cases on `H = hx + ε`.**
* `H ≤ 0`: `H*(S m − Bcount) ≤ H*((n−L+1) − I n)` (nonpositive factor flips the `≥`),
  so `g̃ n x / n ≤ H * (1 − (L−1)/n − (I n)/n)` for `n > L`.
* `H > 0`: skip the partition entirely — `g̃ n x / n ≤ 0 < H`, and the final target
  `f̃₊ ≤ φ x + ε = H` is immediate from `f̃₊ ≤ 0` (g̃ nonpositive). So the partition is
  only ever run in the `H ≤ 0` branch (this is *why* the `−M` truncation matters: it keeps
  `H = hx + ε ∈ [−M+ε, 0]` bounded in the nontrivial branch).

**Three limit passages** (v2 §4.4, unchanged):
* `n → ∞`: `(I n)/n = birkhoffAverage T 1_{B_L} n x → q_L x := μ[1_{B_L}|I] x` (M3,
  `tendsto_birkhoffAverage_ae`); `(L−1)/n → 0`. So `limsup_n g̃(n)/n ≤ H*(1 − q_L x)`.
* `L → ∞`: `1_{B_L} ↓` with `μ(B_L) → 0` (`tendsto_measure_iInter_atTop`, finite measure,
  `μ(⋂_L B_L) = 0`), `q_L` antitone nonneg, `∫ q_L = μ(B_L) → 0`
  (`integral_condExp` on the indicator) ⟹ `q_L ↓ 0` a.e.
  (`integral_tendsto_of_tendsto_of_antitone`). So `f̃₊ x ≤ H = φ x + ε`.
* `M → ∞, ε ↓ 0`: `max(f̃₋,−M) ↓ f̃₋`; `ae_all_iff` over rational `ε` ⟹ `f̃₊ ≤ f̃₋` a.e.

**Net Lean effort:** `τ` (Nat.find), `S`/`ℓ` recursion, `S i ≥ i` + strict-mono, `m` via
`Nat.findGreatest`, one `L1b` application, a good/bad `Finset.sum` split, the two length
bounds, the sign split, three standard limit lemmas. No consecutive-block `Finset`
partition object, no overrun-singleton counting.

---

## B. The −∞ / junk-value subtlety (v2 underweights this) — must establish bounded-below

**Problem.** For `u : ℕ → ℝ`, Mathlib's `Filter.limsup u atTop`, `Filter.liminf u atTop`
return a **junk value `0`** when `u` is unbounded (e.g. `u n → −∞` ⟹ both are `0`, via
`Real.sSup_empty = 0` / `Real.sInf` of an unbounded-below set). So:

* `f₊ := limsup (c · x)`, `f₋ := liminf (c · x)` with `c n x = g(n+1)x/(n+1)` are **only
  meaningful where `c · x` is bounded** a.e. Where `c n x → −∞`, both are junk `0`.
* `Filter.liminf_le_limsup` (used for the trivial S2 direction and inside
  `tendsto_of_le_liminf_of_limsup_le`) **requires `IsBoundedUnder (·≤·)` and `(·≥·)`**.
  Bounded-above is free (`c n ≤ birkhoffAverage g₁ (n+1) ≤ ae_bddAbove`). **Bounded-below
  (`IsBoundedUnder (·≥·) ⟺ f₋ > −∞`) is NOT free** and is the crux.

**Why hbdd makes it true (but not for free).** If `c · x → −∞` on a positive-measure set,
then `d n := birkhoffAverage g₁ (n+1) − c n ≥ 0` (A1') has `d n → +∞` there, and the
finite Fatou bound `∫⁻ liminf d_n ≤ liminf ∫⁻ d_n = ofReal(∫g₁ − γ) < ∞` (`hbdd` ⟹ `γ`
finite) forbids `liminf d_n = ∞` on positive measure. **This is exactly L8, and it MUST be
done in `ℝ≥0∞`** (`u n := ENNReal.ofReal (d n x)`, `lintegral_liminf_le`): only the
`ℝ≥0∞`-valued `liminf` genuinely sees `+∞`. The ℝ-valued junk computation gives `0` on the
`→−∞` set and proves nothing there.

**The logical chain that closes finiteness (do it in this order):**
1. **L8 (ℝ≥0∞ Fatou):** `∀ᵐ x, liminf_n (ofReal (d n x)) < ∞`. Translate to
   `∀ᵐ x, f₊ x > −∞` (i.e. `limsup c·x > −∞`, equivalently `¬ (c·x → −∞)`). This already
   **excludes the `c·x → −∞` set as null.** Also yields `B − f₊ ≥ 0` integrable ⟹
   `f₊ = B − (B − f₊)` integrable ⟹ `f₊ < ∞` a.e. So **`f₊` finite a.e.**
2. **L9:** `∀ᵐ x, f₊ x ≤ f₋ x`. (The truncation `−M` makes L9's argument robust to a
   possibly-`−∞` `f̃₋`.)
3. **Combine:** off a null set, `f₋ ≥ f₊ > −∞` (step 1) and `f₋ ≤ f₊ < ∞`, so **`f₋` is
   finite a.e. ⟹ `IsBoundedUnder (·≥·)` a.e. (bounded-below).** Only now is
   `tendsto_of_le_liminf_of_limsup_le` (L10) applicable.

**Action items for the implementer:**
* In **L8**, additionally export `∀ᵐ x, f₊ x > −∞` (or directly
  `∀ᵐ x, IsBoundedUnder (· ≥ ·) atTop (fun n => c n x)` after combining with L9 in L10).
  The cheapest packaging: L8 returns `Integrable f₊` *and* the `> −∞` fact; L10 derives
  bounded-below from `f₊ ≤ f₋` (L9) + `f₊ > −∞`.
* In **L10**, do **not** assume bounded-below before L9. Derive it: `hbelow x` from
  `(L9 x : f₊ ≤ f₋)` and `(L8 x : f₊ > −∞)` ⟹ `f₋ > −∞` ⟹ `IsBoundedUnder (·≥·)`.
  Bounded-above is independent (A1' + `ae_bddAbove_birkhoffAverage` on `g₁`).
* If the ℝ-junk wrangling for "`liminf (ofReal d_n) < ∞ ⟹ f₊ > −∞`" gets painful, an
  alternative is to phrase **f₊, f₋ in `EReal`** (coe `c n` to `EReal`; `limsup`/`liminf`
  are total, `liminf ≤ limsup` is unconditional) for L8/L9/L10, then transfer to the
  ℝ statement at the very end via `EReal.toReal` once finiteness (`≠ ⊥`, `≠ ⊤`) is known.
  Pick whichever is lighter; the ℝ + explicit-boundedness route mirrors M3 and is
  preferred if the `> −∞` extraction is clean.

**Sanity:** the existing M3 proof avoids this because `birkhoffAverage g (n) x` is bounded
both ways a.e. (`ae_bddAbove`/`ae_bddBelow_birkhoffAverage`); for Kingman the lower bound
is the whole content, so it cannot be assumed — it is produced by L8+L9 as above.
