# S4 — vector-aware sharp leakage (the upper-bound crux): Route B execution plan

> Verified-true route. This is the SOURCE OF TRUTH for formalizing the per-vector growth
> **upper bound** `limsup (1/n)log‖A⁽ⁿ⁾v‖ ≤ λᵢ`.

## ARCHITECTURE SOUNDNESS — VERIFIED (2026-06-09, high-precision numerics)

A later run claimed S4 was false / the orthogonal Λ-eigenspace filtration ≠ the growth filtration
(a Λ-slow eigenvector would grow *fast*). **That claim is WRONG — it was based on ill-conditioned
numerics** (low precision at large `N`: `gram_N` has condition `~e^{2N·λ_max}`, so the "slowest
eigenvector" is roundoff garbage unless `dps ≫ 2N·λ_max/ln10`). Re-verified correctly at **dps=600,
N=50** on a 3-block non-normal cocycle `G=diag(e³,e^{1.5},e⁰)+0.5·strict-upper`:
* the Λ-slowest eigenvector grows at **0 = λ_min** (slow) at every scale (consistency check
  `(1/N)log‖GⁿNv‖ ≈ 0` confirms it really is the slowest singular vector);
* the Λ-middle eigenvector grows at **1.5 = λ_mid**.
So **the orthogonal Λ-eigenspace filtration IS the forward growth filtration; `V_Λ = lambdaSublevel`
a.e. (L11) holds; S4 is TRUE.** The fast-overlap decay is **block-specific** (not band-edge),
confirmed directly: `⟪v_slow, u_fast(n)⟩ → −3 = λ_min−λ₀`, `⟪v_slow, u_mid(n)⟩ → −1.5 = λ_min−λ₁`.
The handle route below is therefore correct. (Scripts: `/tmp/lyap_check2.py`, `/tmp/lyap_overlap.py`.)

## The crux S4 (= (A′))

For `v` in the **slow** Oseledets subspace from `λᵢ` down (i.e. `P^{cᵢ}_∞ v = 0` for the single
threshold `cᵢ` straddling block `i−1/i`, `e^{λᵢ} < cᵢ < e^{λᵢ₋₁}`), and `cₘ` straddling block
`m−1/m` with `1 ≤ m ≤ i`:

    limsup_n (1/n) log ‖P^{cₘ}ₙ v‖  ≤  λᵢ − λₘ₋₁     (P^{cₘ}ₙ = bandProjector (Ioi cₘ) n x).

Given S4, the per-vector **upper bound** is a per-block split (NO Abel): `‖A⁽ⁿ⁾v‖² = Σⱼ σⱼ²|⟨v,eⱼ⟩|²`;
slow part `≤ sᵢ²‖v‖²`, fast block `l` `≤ sₗ²·‖P^{block l}v‖²` → `λₗ + (λᵢ−λₗ) = λᵢ`; log-of-finite-sum.

## DECISION: Route B (per-overlap), NOT Route A (projector difference)

`P^{cₘ}ₙ` is (eventual regime) the orthogonal projector onto the **top `mₘ` sorted Gram
eigenvectors** (`bandProjector_indicator_eq_sortedTopFrame`). So **exactly**

    ‖P^{cₘ}ₙ v‖² = Σ_{j < mₘ} ⟪v, uⱼ(n)⟫²        (uⱼ(n) = sortedGramEigenbasis A T n x j).

Bound each overlap `|⟪v,uⱼ(n)⟫|` (fast `j < mₘ ≤ i`) and sum the finitely many terms. **Key win:**
a single overlap is a `k=1` exterior phenomenon — `norm_offdiag_residual_compound_le` at `k=1`
collapses to the **plain Gram off-diagonal residual**, so the whole `⋀^k`/`compoundMatrix`/
`onbTriv`/`√(2k)`-Frobenius apparatus (and its elaborator-timeout cost) is **avoided** for S4. The
exterior machinery is needed only for the operator-norm projector *convergence* (already done), not
for the vector leakage.

## The rate (why it's sharp and non-circular)

`|⟪v,uⱼ(n)⟫| = |⟪v,uⱼ(n)⟫ − ⟪v,uⱼ(∞)⟫|` (since `v ⊥` limit fast subspace), bounded by the sin-Θ of
the fast eigenvector `uⱼ(n)` against the slow subspace where `v` lives. The off-diagonal residual,
evaluated against the **slow** reference, carries the **two-gap ratio** `r = σᵢ(n)/σₘ₋₁(n)` (slow-block
top over fast-block bottom), with `(1/n)log r → λᵢ − λₘ₋₁ < 0`. The naive operator-norm rate
`λₘ − λₘ₋₁` is too weak; the slow-reference `v₀` choice inside `norm_offdiag_residual_compound_le`
(with `μ₁ = σᵢ²` the slow ceiling) is what recovers the sharp rate. **Non-circular:** uses only
eigenvector/projector perturbation + limit orthogonality, never `‖A⁽ⁿ⁾v‖` growth. (Routing through
`inner_cfc_ge_band` is the circular trap — that lemma is the LOWER-bound tool only.)

## Sub-lemma ladder (Route B; place in OseledetsLimit.lean or Forward.lean)

| ID | Statement | Method (existing lemmas) | Diff |
|---|---|---|---|
| **S0** | `limitBandProjector` := `(tendsto_bandProjector_of_gap …).choose` + `tendsto_limitBandProjector` | package `tendsto_bandProjector_of_gap` + `choose_spec` | LOW |
| **S1** | nesting: `c ≤ c' → P^{c}_∞ v = 0 → P^{c'}_∞ v = 0` | `cfc_mono` on `𝟙_{(c',∞)} ≤ 𝟙_{(c,∞)}` over `finite_real_spectrum`, pass to limit; `bandProjector_indicator_mul_self` | LOW–MED |
| **S2** | `‖P^{cₘ}ₙ v‖² = Σ_{j<mₘ} ⟪v,uⱼ(n)⟫²` | `bandProjector_indicator_eq_sortedTopFrame` (= `W Wᵀ`, `WᵀW=1`) + `colE_sortedTopFrame` + `mulVec` + orthonormality | LOW |
| **S3** | `k=1` Gram off-diag residual: `‖Q_{n+1} uⱼ − ⟪Q_{n+1}uⱼ,uⱼ⟫uⱼ‖ ≤ σⱼ σᵢ cB²` | `norm_offdiag_residual_compound_le` **at k=1** (`compoundMatrix 1 M ≅ M`, small `compoundMatrix_one` lemma) + `perturbed_compound_gram_ceiling` (k=1, `μ₁=σᵢ²`) | MED–HIGH |
| **S4-CORE** | `|⟪v,uⱼ(n)⟫| ≤ ‖v‖·(σⱼσᵢcB²/(μ₀−ν))`, `(1/n)log → λᵢ−λⱼ` | `offdiag_sin_le_residual_div_gap` (`vt=uⱼ(n)`, `v₀`=limit fast dir); numerator S3; two-gap gap lower bound via `norm_sq_compound_mul_ge`-analogue (k=1) | **HIGH** |
| **S5** | S4 statement: `limsup (1/n)log‖P^{cₘ}ₙv‖ ≤ λᵢ−λₘ₋₁` | `Σ ≤ mₘ·max`; each `(1/n)log → λᵢ−λⱼ ≤ λᵢ−λₘ₋₁` (antitone, `j<mₘ≤m≤i`); `tendsto_log_singularValue` + finite-max limsup | MED |

## Flags
- **Hypothesis sharpening:** "no Λ-component above λᵢ" = the SINGLE threshold `cᵢ` straddling block
  `i−1/i` (S1 propagates upward). "All `c > e^{λᵢ}`" is strictly weaker — do not use it.
- **Eventual/a.e. + limsup** (not lim): all bounds hold only in the eventual regime `κ²r²<1`, `μ`-a.e.,
  exactly as `norm_bandProjector_succ_sub_le_cocycle` / `tendsto_bandProjector_of_gap`.
- Hardest node: **S4-CORE** (the only genuinely new analysis; isolates sin-Θ to one fast direction +
  slow vector, two-gap denominator). S3 friction is only the `compoundMatrix_one` identification.
