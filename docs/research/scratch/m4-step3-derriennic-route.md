# Step 3 (the hard core) — prefer the Derriennic "leaders" route, not Avila–Bochi

**Decision.** The isolated hard lemma (`ae_ereal_limsup_le_liminf`, i.e. `limsup ≤ liminf`
a.e. for the normalized subadditive cocycle) should be proved by the **Riesz/Derriennic
"leaders" route** transcribed in `docs/research/sources/kingman-karlsson-maximal-proof.md`
(Karlsson, *A proof of the subadditive ergodic theorem*), **not** the Avila–Bochi /
Steele stopping-time truncation in `m4-kingman-v2.md` §4 / `m4-L9-notes.md` §A.

**Why.** Both are published, correct proofs. But the Derriennic route's hard core is a
single clean finite induction (Riesz's leader lemma) with **no measure theory and no nested
limit passages**, and its a.e.-convergence superstructure is structurally identical to
machinery this repo already owns sorry-free (the `E_{α,β}` two-bound contradiction =
`measure_setOf_lt_limsup_eq_zero` in `Birkhoff.lean`). The Avila–Bochi route needs a greedy
frontier walk + a good/bad split + three nested limit passages (n→∞, L→∞, M→∞/ε→0) — strictly
more moving parts. (Karlsson's own appendix confirms our v2 R-CRIT finding: Garsia/M1 gives
only the loose envelope `f₊ ≤ B`, never the sharp bound; the sharp bound needs the leaders
lemma, a finite induction — not a stronger measure-theoretic maximal inequality.)

The envelope (step 1), Fatou finiteness+integrability (step 2), and combine (step 4) are
route-agnostic and already done / in progress — unaffected by this choice.

---

## The Derriennic route, mapped to Lean

Notation: `a n x := g n x` (the cocycle, `a 0 = 0` not assumed — but the relevant lemmas use
`n ≥ 1`); reduce to the **non-positive** process `v n := g n − birkhoffSum T (g 1) n` first
(A1' ⇒ `v (n+1) ≤ 0`; `g 1` Birkhoff-converges by M3, so `g n /n` converges iff `v n /n`
does). Work with `v`. Goal: `∀ᵐ x, limsup (v(n+1)x/(n+1)) ≤ liminf (v(n+1)x/(n+1))`.

### L-A. Riesz's leader lemma (pure finite combinatorics — NO measure theory)

```
/-- An index `u < n` is a **leader** of `c : ℕ → ℝ` (length `n`) if some forward partial
sum `c u + c (u+1) + … + c j` (u ≤ j < n) is negative. The sum of `c` over its leaders is
≤ 0. -/
private theorem sum_leaders_nonpos (n : ℕ) (c : ℕ → ℝ)
    (leader : ℕ → Prop) [DecidablePred leader]
    (hleader : ∀ u, leader u ↔ u < n ∧ ∃ j, u ≤ j ∧ j < n ∧ ∑ i ∈ Finset.Icc u j, c i < 0) :
    ∑ u ∈ (Finset.range n).filter leader, c u ≤ 0
```
Proof: strong induction on `n` (Karlsson Lemma 3.2). Case split on whether `0` is a leader.
If not, all leaders lie in `{1,…,n−1}` (shift, apply IH). If `0` is a leader, take the least
`k` with `c 0+…+c k < 0`; then `0,…,k` are all leaders (minimality ⇒ `c i+…+c k < 0` for
`i ≤ k`) and `c 0+…+c k < 0`; the remaining leaders are leaders of `c_{k+1},…` (IH).
This is the one genuinely combinatorial nugget; budget the most care here. `Finset.Icc`,
`Finset.sum_Icc_consecutive`, `Nat.find` for "least k", strong recursion / `Nat.strong_induction`.

### L-B. Telescoping identity for the subadditive cocycle

`b n x := a n x − a (n-1) (T x)` for `n ≥ 1`. Then (Karlsson, §3.2):
* `a n x = ∑_{k=0}^{n-1} b (n-k) (T^[k] x)`  (telescoping; `a 0 = 0` on the shifted process —
  for `v` this holds since `v 0 = 0`? CHECK: `v 0 = g 0 − birkhoffSum (g1) 0 = g 0 − 0 = g 0`.
  Subadditivity forces `g 0 ≥ 0`, not `= 0`. So state telescoping carefully for `n ≥ 1` with
  the partial-sum convention, mirroring the existing `birkhoffSum` index handling.)
* `a n x − a (n-k) (T^[k] x) = ∑_{i=0}^{k-1} b (n-i) (T^[i] x)` (the prefix sum).
Prove both by induction on the range; reuse `Finset.sum_range_succ`, `Function.iterate_add_apply`.

### L-C. Derriennic's maximal inequality (Karlsson Lemma 3.4 + Prop 3.5)

```
private theorem setIntegral_div_le_of_liminf_lt [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {a : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T a) (hint : ∀ n, Integrable (a n) μ) {α : ℝ}
    -- B := {x | liminf (a (n+1) x/(n+1)) < α}, T-invariant (a.e.)
    : ∀ᵐ … →  limsup_n (1/n) ∫_B a n  ≤ α · μ(B).toReal
```
Proof (Karlsson Lemma 3.4 for `α=0`, then Prop 3.5 applies it to `a n − nα`, itself a
subadditive cocycle):
* `Λ_n := {x | inf_{1≤k≤n} (a n x − a (n-k) (T^[k] x)) < 0}`; `A_n := {x | inf_{1≤k≤n} a k x < 0} ⊆ Λ_n`.
* For each `n`, apply **L-A** with `c k := b (n-k) (T^[k] x)`: the leader condition
  `T^[k] x ∈ Λ_{n-k}` matches "some forward partial sum of `c` is < 0" (via L-B), so
  `∑_{k : T^[k]x ∈ Λ_{n-k}} b (n-k) (T^[k] x) ≤ 0` pointwise.
* Integrate over the invariant set `B`; push `T^[k]` through `μ` (measure-preservation,
  `integral_comp_iterate` already in the file) to telescope `∑_i ∫_{B∩Λ_i} b i`.
* Bound `∫_B a n = ∑_i ∫_{B∩Λ_i} b_i + ∑_i ∫_{B∖Λ_i} b_i ≤ 0 + ∑_{i} ∫_{B∖A_i} a⁺(1)`,
  and `(1/n)∑_{i<n} ∫_{B∖A_i} a⁺(1) → 0` since `a⁺ 1 ∈ L¹`, `A_i ↑`, `B ⊆ ⋃A_i`
  (dominated/monotone convergence: `∫_{B∖A_i} a⁺(1) → ∫_{B∖⋃A_i} a⁺(1) = 0`).
Reuses: `integral_comp_iterate`, `measure_preimage`, `tendsto_setIntegral_of_monotone`-style
(see `MaximalErgodic.lean`), `integral_finsetSum`.

### L-D. a.e. convergence ⇒ `limsup ≤ liminf` (Karlsson §3.3, = existing repo pattern)

For the non-positive `v` (so `α < 0` regime is the relevant one; the `α ≥ 0` side is trivial
from `v ≤ 0`): for rationals `α < β`, the set `E_{α,β} := {x | liminf < α < β < limsup}` is
a.e. `T`-invariant (L7-style, already have `limsup_div_comp_ae`); apply **L-C** to get both
`∫_{E} v 1 ≤ … ≤ α·μ(E)` and (via the additive/`-v` companion) `β·μ(E) ≤ ∫_{E} …`, forcing
`μ(E_{α,β}) = 0`. Union over rational `α<β` ⇒ `limsup ≤ liminf` a.e. This is the SAME
two-bound contradiction already carried out sorry-free in `measure_setOf_lt_limsup_eq_zero`
(`Birkhoff.lean`) for the additive case — adapt it, with L-C replacing the additive maximal
inequality.

---

## Risk note

The leader lemma (L-A) and the telescoping/T-invariance bookkeeping in L-C are the real work;
both are finite/combinatorial or reuse existing measure machinery, with no truncation and no
triple limit. If L-C's `B`-integral telescoping proves heavy, the fallback is still the
Avila–Bochi route in `m4-L9-notes.md` §A — but try Derriennic first; it is the lighter proof
and it is the one in the scraped sources, so it is "use the research, don't reinvent."
