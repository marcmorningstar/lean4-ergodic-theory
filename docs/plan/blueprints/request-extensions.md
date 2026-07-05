# Blueprint: additive extensions to the Oseledets formalization

Planning document for the ten request items in `request_prompt.md`. **No proofs here** —
this drives implementation. Everything is purely *additive*: no existing decl is
removed, renamed, or weakened. Target: sorry-free, on the current toolchain / Mathlib pin.

All citations are `file:line` against the current tree. Decl names proposed for new work
are suggestions; the implementer may rename.

---

## 0. Map of the reusable API (STEP 1 output)

The development already produces, for the standard hypotheses
(`hT : Ergodic T μ`, `hA : ∀ x, (A x).det ≠ 0`, `hAmeas : Measurable A`,
`hint : IntegrableLogNorm A μ`, `hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ`,
`[IsProbabilityMeasure μ]`):

### Cocycle layer
- `ErgodicTheory.cocycle` — iterated cocycle, newest factor left (`Cocycle/Basic.lean:62`).
- `ErgodicTheory.cocycle_add` — cocycle identity (`Cocycle/Basic.lean:77`).
- `ErgodicTheory.cocycle_succ`, `cocycle_one`, `cocycle_zero` (`Cocycle/Basic.lean:67-74`).
- `ErgodicTheory.IntegrableLogNorm` — `log⁺‖A‖ ∈ L¹` (`Cocycle/Basic.lean:86`).
- `ErgodicTheory.measurable_cocycle` (`Cocycle/Basic.lean:105`); `instMeasurableSpaceMatrix`,
  `instMeasurableMul₂Matrix` (`Cocycle/Basic.lean:53,94`).
- `ErgodicTheory.det_cocycle_ne_zero` (`Cocycle/FurstenbergKesten.lean:57`).
- `ErgodicTheory.norm_cocycle_pos`, `norm_inv_cocycle_pos`, `norm_one_matrix`
  (`Cocycle/FurstenbergKesten.lean:65,73,84`).

### Furstenberg–Kesten (top/bottom exponent)
- `ErgodicTheory.furstenbergKesten_top` — `(1/n) log‖A⁽ⁿ⁾‖ → λ₁` a.e.
  (`Cocycle/FurstenbergKesten.lean:320`).
- `ErgodicTheory.furstenbergKesten_bot` — `(1/n) log‖(A⁽ⁿ⁾)⁻¹‖ → -λ_k` a.e.
  (`Cocycle/FurstenbergKesten.lean:359`).
- `isSubadditiveCocycle_logNorm` / `_inv` (`:116,134`);
  Birkhoff sandwich + integrability lemmas (`:154-312`);
  `integral_birkhoffSum` (`:230`).

### Singular-value / scalar layer (`Lyapunov/OseledetsLimit.lean`)
- `ErgodicTheory.gram` (`:121`) — Gram matrix `Qₙ = (A⁽ⁿ⁾)ᵀ A⁽ⁿ⁾`; `gram_posSemidef`,
  `gram_isSelfAdjoint` (`:531,541`).
- `ErgodicTheory.Sprod` (`:126`) — `∏_{i<k} σᵢ(A⁽ⁿ⁾)`; submult `Sprod_submul` (`:141`),
  subadditive cocycle `isSubadditiveCocycle_logSprod` (`:164`), positivity `Sprod_pos`
  (`:254`), measurability `measurable_Sprod` (`:334`), integrability `integrable_logSprod`
  (`:357`), `bddBelow_logSprod` (`:376`), Fekete bounds `logSprod_le` / `neg_le_logSprod`
  (`:270,289`).
- `LinearMap.singularValues_le_opNorm` / `ErgodicTheory.sigma_le_opNorm` (`:93,185`);
  `inv_opNorm_inv_le_sigma` (`:191`); `injective_toEuclideanLin` (`:230`);
  `singularValues_cocycle_pos` (`:242`).
- **`ErgodicTheory.tendsto_GammaK`** (`:434`) and
  **`tendsto_GammaK_of_integrableLogNorm`** (`:449`) — the genuine ergodic limit
  `Γ_k = lim (1/n) log Sprod_k`, a.e.-constant, for `k ≤ d`.
- `ErgodicTheory.tendsto_log_singularValue` (`:468`) — `λᵢ = Γ_{i+1} − Γ_i` per-σ limit.
- `ErgodicTheory.lamSing` (`:507`) — per-point junk-on-divergence per-σ exponent;
  `lamSing_eq_of_tendsto` (`:514`).
- **`ErgodicTheory.exists_lam_tendsto_singularValue`** (`:3131`) — the headline deterministic
  spectrum: `∃ lam : ℕ → ℝ`, antitone on `[0,d)`, with
  `(1/n) log σᵢ(A⁽ⁿ⁾) → lam i` a.e. for each `i < d`. **This is the single most reusable
  hook for items 1, 2, 3, 6, 7.**
- `ErgodicTheory.qpow` (`:550`), `qpow_posSemidef`/`_isSelfAdjoint` (`:556,563`);
  `eigenvalues_qpow_tendsto` (`:699`); `lamCocycle` (`:1950`).
- `ErgodicTheory.oseledetsLimit` (`:3445`) — the named limit matrix `Λ`;
  `measurable_oseledetsLimit`; `oseledetsLimit_isSelfAdjoint` (`:3496`);
  **`oseledetsLimit_eigenvalues₀_eq`** (`:3602`) — `eigenvalues₀(Λ x) i = e^{lamSing x i}`.
- `sq_singularValues_eq_gram_eigenvalue` (`:421`).

### Exterior-norm layer (`Lyapunov/ExteriorNorm.lean`)
- `ExteriorNorm.exteriorOpNorm`, `conjExteriorMap`, `exteriorOpNorm_comp_le` (`:90,81,107`).
- **`ExteriorNorm.exteriorOpNorm_hodge_eq_prod_singularValues`** (`:633`) — `‖⋀^k f‖ = ∏σᵢ`.
- **`ExteriorNorm.prod_singularValues_comp_le`** (`:1364`) — submult of `∏σ`.
- `ExteriorNorm.compoundMatrix` (`:899`); **`compoundMatrix_mul`** (Cauchy–Binet, `:976`);
  `compoundMatrix_transpose` (`:995`), `compoundMatrix_gram` (`:1004`),
  `compoundMatrix_one` (`:1404`), `compoundMatrix_mul_inv`/`_inv_mul`/`_eq_inv_mul`
  (`:1422,1427,1433`); `toEuclideanLin_compoundMatrix_mul` (`:1013`);
  **`prod_singularValues_eq_l2_opNorm_compound`** (`:1323`) — `∏σ = ‖C_k(M)‖`.
- `Weyl.abs_eigenvalues₀_sub_le` (`:2716`), `Weyl.tendsto_eigenvalues₀` (`:2731`).

### Filtration / spectrum layer
- `ErgodicTheory.lambdaBar` (`Lyapunov/GrowthFunction.lean:69`) — `limsup (1/n) log‖A⁽ⁿ⁾v‖`;
  `lambdaBar_equivariant`/`_ae` (`:335,637`), `isUltrametricGrowth_lambdaBar` (`:598`).
- `IsUltrametricGrowth.finite_range`, `.sublevel`, `.mem_sublevel`
  (`Lyapunov/Ultrametric.lean:179,218,247`).
- `ErgodicTheory.spectrum` (`Finset ℝ`), `specCard`, `specList` (descending enum), `Vflag`,
  `lambdaSublevel` (`Lyapunov/Filtration.lean:53,74,80,122,106`); `Vflag_zero/_last/
  _strictAnti`, `lambdaBar_eq_on_stratum`, `spectrum_equivariant_ae`, `Vflag_equivariant`
  (`:153,176,202,239,329,369`).
- `SpectrumConstancy.lean` — `spectrum_const_invariant_ae` (`:186`), `hspec_standing`
  (`:213`), spectrum-subset bridges (`:66-155`).

### Measurable subspaces & Oseledets predicate
- `ErgodicTheory.orthProjMatrix`, `MeasurableSubspace`
  (`Lyapunov/MeasurableSubspace.lean:39,47`).
- `ErgodicTheory.IsOseledetsFiltration` (predicate, `Corollaries.lean:109`);
  `oseledets_filtration'` (`:128`); `.ae_mem_iff_limsup_le` (`:266`); `.unique` (`:333`);
  `.k_pos` (`:368`); **`.tendsto_log_opNorm_cocycle`** (`:387`);
  `oseledets_top_exponent_eq_furstenbergKesten` (`:531`);
  `MeasurableSubspace.measurable_finrank` (`:242`), `trace_orthProjMatrix` (`:225`);
  **`.exists_finrank_ae_eq`** (deterministic dim profile `m`, `:569`);
  **`.exists_multiplicity`** (`:610`); `oseledets_filtration_with_multiplicities` (`:631`).
- The target `ErgodicTheory.oseledets_filtration` (`MultiplicativeErgodic.lean:48`).

### Ergodic engine (`Ergodic/Kingman.lean`)
- `IsSubadditiveCocycle` (`:89`); **`tendsto_kingman`** — *non-ergodic* version, limit is a
  `T`-invariant integrable `G` with `G = μ[g 1 | invariants T]` (`:3401`);
  **`tendsto_kingman_ergodic`** (`:3438`). The non-ergodic Kingman is the foundation for
  item 9's non-ergodic relaxation.
- Birkhoff: `Ergodic/Birkhoff.lean`.

**Key gap observed:** there is currently *no* packaged multiset/list of exponents with
multiplicities (only the existence statements produce `lam`/`m`), and *no* trace/det growth
result. Items 6, 1, 7 fill these.

---

## 1. Sum of positive (/ non-negative / negative) Lyapunov exponents

### (a) Reuse
- `exists_lam_tendsto_singularValue` (`OseledetsLimit.lean:3131`) gives the deterministic
  `lam : ℕ → ℝ` (indexed `0..d-1`, antitone). The full *with-multiplicity* list is exactly
  `fun i : Fin d => lam i`.
- `IsOseledetsFiltration.exists_multiplicity` (`Corollaries.lean:610`) gives the distinct
  exponents `lam : Fin k → ℝ` with multiplicities `m : Fin k → ℕ`, `∑ m = d`.

Either representation supports the sum; the **with-multiplicity Fin d form** (`lam : Fin d → ℝ`
from the singular-value layer) is the most convenient: the "counted with multiplicity" sums
are just `Finset` sums of a filtered `Fin d → ℝ`.

### (b) New defs/theorems  → new file `ErgodicTheory/Lyapunov/ExponentSums.lean`
This file should first package the **with-multiplicity exponent vector** (depends on item 6;
if item 6 lands first, reuse its `exponents : Fin d → ℝ`). Proposed, given a chosen
`lam : Fin d → ℝ` (the sorted full spectrum):

```lean
/-- Sum of strictly positive exponents (counted with multiplicity). -/
def sumPosExp (lam : Fin d → ℝ) : ℝ := ∑ i ∈ {i | 0 < lam i}, lam i      -- Finset.filter
def sumNonnegExp (lam : Fin d → ℝ) : ℝ := ∑ i ∈ {i | 0 ≤ lam i}, lam i
def sumNegExp (lam : Fin d → ℝ) : ℝ := ∑ i ∈ {i | lam i < 0}, lam i
```
plus the **packaged a.e.-constant real** form tied to the cocycle. The deliverable the
request emphasizes is "a single directly usable term": expose, under the standing
hypotheses,
```lean
theorem exists_sumPosExp :
    ∃ S : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n => (n:ℝ)⁻¹ *
      ∑ i ∈ Finset.range d,
        Real.posLog⁺?  -- see strategy: positive part of log σᵢ
      ) atTop (𝓝 S)
```
Cleaner: define the packaged constants directly from `lam` and prove they equal the
filtered sums; then separately prove the growth-rate identification (item 2).

Recommended concrete API:
- `ErgodicTheory.lyapPosSum A T μ : ℝ` (and `lyapNonnegSum`, `lyapNegSum`, `lyapTotalSum`) as
  the filtered sum over the sorted spectrum vector from item 6, packaged as a plain real
  (`noncomputable`, via `Classical.choose` on `exists_lam_tendsto_singularValue`, or — better
  — defined off item 6's `exponents`).

### (c) Strategy
Once the sorted `lam : Fin d → ℝ` exists (item 6), these are pure `Finset.sum` over
`Finset.univ.filter`. Mathlib: `Finset.sum_filter`, `Finset.filter`, `Finset.sum_le_sum`,
`Finset.sum_nonneg`. The "a.e.-constant" property is inherited: `lam` is deterministic, so
the sums are constants by construction; no further ergodic argument is needed beyond what
item 6 already discharged.

### (d) Difficulty: **trivial-to-moderate** (the only work is packaging + item 6 dependency).
Risk: low.

### (e) Dependencies: **item 6** (full spectrum vector). Without item 6 one can still define
the sums via `Classical.choose exists_lam_tendsto_singularValue`, but the cleaner path is to
do item 6 first.
Caveat: "counted with multiplicity" must use the `Fin d` vector, **not** the distinct
`spectrum : Finset ℝ`; be explicit in docstrings.

### (f) Hypotheses: needs ergodicity + det≠0 + both integrabilities (inherited from
`exists_lam_tendsto_singularValue`). The non-ergodic / singular relaxations are item 9.

---

## 2. Growth-rate / exterior characterization (partial sums ↔ wedge growth)

This is the mathematical heart and is **already essentially proved at the scalar level**.

### (a) Reuse
- `Γ_k = lim (1/n) log Sprod_k` is **exactly** the asymptotic growth rate of the product of
  the top-k singular values (`tendsto_GammaK_of_integrableLogNorm`, `:449`).
- `Sprod_k = ∏_{i<k} σᵢ = ‖compoundMatrix k (A⁽ⁿ⁾)‖`
  (`prod_singularValues_eq_l2_opNorm_compound`, `:1323`) — this is the **k-volume / largest
  minor** characterization. And `‖⋀^k f‖ = ∏σᵢ`
  (`exteriorOpNorm_hodge_eq_prod_singularValues`, `:633`).
- The exterior cocycle is a cocycle: `compoundMatrix_mul` (`:976`) is Cauchy–Binet, i.e.
  `C_k(A⁽ᵐ⁺ⁿ⁾) = C_k(A⁽ᵐ⁾∘Tⁿ)·C_k(A⁽ⁿ⁾)` after `cocycle_add`.

### (b) New defs/theorems → `ErgodicTheory/Lyapunov/ExteriorCocycle.lean`
```lean
/-- The k-th exterior (compound) cocycle generator. -/
def extGen (k : ℕ) (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) := ExteriorNorm.compoundMatrix k (A x)

/-- It is a cocycle: cocycle (extGen k A) T n x = compoundMatrix k (cocycle A T n x). -/
theorem cocycle_extGen_eq_compound (k n : ℕ) (x) :
    cocycle (extGen k A) T n x = ExteriorNorm.compoundMatrix k (cocycle A T n x)

/-- Partial sum Γ_k is the top exponent of the exterior cocycle. -/
theorem GammaK_eq_furstenbergKesten_compound ... :
    ∀ᵐ x, Tendsto (fun n => (n:ℝ)⁻¹ * Real.log ‖compoundMatrix k (cocycle A T n x)‖) atTop (𝓝 Γk)

/-- Γ_k = sum of top-k exponents (with multiplicity). -/
theorem GammaK_eq_sum_top_exponents (k ≤ d) : Γk = ∑ i ∈ Finset.range k, lam i
```
and the headline:
```lean
/-- Positive-exponent sum = top exponent of the exterior cocycle / largest-minor growth. -/
theorem sumPosExp_eq_GammaK_at_kpos : lyapPosSum = Γ_{k₊}    -- k₊ = #{i | 0 < lam i}
```
(because the partial sums `Γ_k` are maximized exactly at `k = #positive exponents`, since
`Γ_k − Γ_{k-1} = lam_{k-1}` flips sign there).

### (c) Strategy
1. `cocycle_extGen_eq_compound`: induction on `n` using `cocycle_succ`, `compoundMatrix_mul`,
   and `compoundMatrix_one` for the base. (`extGen` over `T` uses the same `T`.)
2. The exterior cocycle is genuinely a matrix cocycle: feed it to the FK machinery —
   either reuse `furstenbergKesten_top` on `extGen k A` (needs its `det ≠ 0` and
   integrability, which follow from `compoundMatrix_mul_inv` and operator-norm bounds), OR
   stay scalar and just rewrite `‖compoundMatrix k (cocycle …)‖ = Sprod_k` and reuse
   `tendsto_GammaK_of_integrableLogNorm`. **The scalar route is far cheaper** and avoids
   re-establishing integrability for the compound generator.
3. `Γk = ∑_{i<k} lam i`: telescoping. `Sprod_k = ∏_{i<k} σᵢ`, so
   `(1/n) log Sprod_k = ∑_{i<k} (1/n) log σᵢ → ∑_{i<k} lam i`
   (finite sum of convergents; `tendsto_finset_sum`). Use `tendsto_log_singularValue`
   per index and uniqueness of limits.
4. `k₊`-maximization: `Γ_k` is the running partial sum of an antitone sequence `lam`; the
   max is at the last nonneg index. Pure real arithmetic on a `Fin d → ℝ` antitone vector.

Mathlib: `tendsto_finset_sum`, `Finset.sum_range_succ`, `tendsto_nhds_unique`,
`Real.log_prod`.

### (d) Difficulty: **moderate** (scalar route). The exterior-cocycle-as-FK route is hard
(re-deriving integrability for the compound generator); **avoid it** — note as caveat.
Risk: medium-low.

### (e) Dependencies: items 1 + 6 (for `lam`, the sums). Provides the key identity consumed
by item 3.
Caveat (per request): the cleanest statement is at the **scalar `Sprod`/`compoundMatrix`
level**; the "k-th exterior power of the cocycle is itself a cocycle whose top exponent =
sum of top k exponents" is true and provable via `cocycle_extGen_eq_compound` +
`compoundMatrix_mul`, but tying it to `furstenbergKesten_top` on `extGen` requires its own
integrability (`log⁺‖C_k(A)‖ ≤ k·log⁺‖A‖ + C`, derivable but extra work). State both; prove
the scalar one as primary, the FK-on-exterior one as optional corollary.

### (f) Needs det≠0 + integrability + ergodicity (inherited). The largest-minor / top-k
volume growth statement (one-sided, upper bound) could drop `hint'`/det≠0 partially — see
item 9.

---

## 3. Sign and vanishing characterizations

### (a) Reuse
- The sums from item 1; the partial-sum/telescoping facts from item 2; antitonicity of `lam`
  from `exists_lam_tendsto_singularValue`.

### (b) New theorems → append to `ErgodicTheory/Lyapunov/ExponentSums.lean`
```lean
theorem lyapPosSum_nonneg : 0 ≤ lyapPosSum                        -- sum of nonneg terms
theorem lyapPosSum_eq_zero_iff : lyapPosSum = 0 ↔ ∀ i, lam i ≤ 0  -- non-expanding case
theorem lyapPosSum_pos_iff : 0 < lyapPosSum ↔ ∃ i, 0 < lam i
-- dual:
theorem lyapNegSum_nonpos, lyapNegSum_eq_zero_iff (↔ ∀ i, 0 ≤ lam i), lyapNegSum_neg_iff
```

### (c) Strategy
Pure `Finset` arithmetic over the filtered sums.
- nonneg: `Finset.sum_nonneg` (every summand `> 0` on the filter).
- `= 0 ↔ all ≤ 0`: a sum of *strictly positive* terms is `0` iff the filter is empty iff no
  exponent is positive. `Finset.sum_eq_zero_iff_of_nonneg` / `Finset.filter_eq_empty_iff`.
- `> 0 ↔ ∃ positive`: contrapositive of the above.
Mathlib: `Finset.sum_pos`, `Finset.sum_eq_zero_iff_of_nonneg`, `Finset.filter_eq_empty_iff`.

### (d) Difficulty: **trivial**. Risk: very low.

### (e) Dependencies: items 1, 6. (Item 2 not strictly required but its
`sumPosExp_eq_GammaK` makes the "non-expanding" interpretation crisp.)

### (f) Inherits standing hypotheses. No new hypotheses.

---

## 4. Regularity of exponents in the cocycle (HIGHEST VALUE — be precise)

This is the genuinely subtle item. **State strongly, with honest caveats.**

### What is TRUE (and provable from existing machinery):

**T1 — Subadditive/Fekete USC of the top exponent and of partial sums.**
The constant `Γ_k(A) = lim_n (1/n) log Sprod_k(A) = inf_n (1/n) ∫ log Sprod_k(A, n+1)`
(Fekete: a subadditive sequence's normalized limit is the **infimum**). An infimum of a
family of functions each *continuous* in the generator is **upper semicontinuous**. The
per-`n` integral `Aᵐ ↦ (1/n) ∫ log Sprod_k(Aᵐ, n) dμ` is continuous under suitable
convergence of generators `Aᵐ → A` (uniform, or L¹-log domination giving
`∫ log Sprod_k(Aᵐ,n) → ∫ log Sprod_k(A,n)` by dominated convergence). Hence
`Γ_k(A) = inf_n (…) ` is USC: `limsup_m Γ_k(Aᵐ) ≤ Γ_k(A)`.

This gives:
- top exponent `λ₁ = Γ_1` is USC in `A`;
- each partial sum `Γ_k` (sum of top-k exponents) is USC in `A`;
- the positive-exponent sum `lyapPosSum = max_k Γ_k` is USC (a finite max of USC functions
  is USC).

**T2 — Monotonicity is NOT generally available** (no natural order makes exponents monotone
in the generator), so we do *not* claim it. The deterministic per-σ exponents are antitone
*in the index* (`exists_lam_tendsto_singularValue`), which is different and already proved.

### What is FALSE / fails:
- **Full continuity of individual exponents fails** in general (classic: the spectrum can
  jump as a gap closes; eigenvalue continuity of the *limit operator* is fine, but the
  ergodic exponents are not jointly continuous — only USC for partial sums, and the
  *individual* `lam_i` are differences `Γ_{i+1} − Γ_i` of USC functions, hence neither USC
  nor LSC in general). The bottom exponent `λ_d = Γ_d − Γ_{d-1}`, and since `Γ_d = ∫log|det|`
  is actually *continuous* (linear in `log|det|`), `λ_d` is *lower* semicontinuous. State
  this asymmetry precisely.
- Continuity *does* hold at points of "one-point spectrum" / simple structure, and along
  sequences with no gap-collapse — but formalizing the exact continuity locus is
  research-level; **do not attempt** beyond stating USC.

### Hypotheses (be precise):
- "convergence of generators" must be made concrete. Two workable regimes:
  1. **Uniform/operator convergence with a uniform log-integrable envelope**:
     `Aᵐ → A` pointwise (entrywise) a.e. with `‖Aᵐ‖, ‖(Aᵐ)⁻¹‖` dominated by fixed
     L¹-log functions. Then dominated convergence gives `∫ log Sprod_k(Aᵐ, n) →
     ∫ log Sprod_k(A, n)` for each fixed `n`.
  2. **L¹-log convergence**: `posLog‖Aᵐ‖ → posLog‖A‖` in L¹ (and same for inverse). This is
     the natural hypothesis for the per-`n` integral continuity via L¹ continuity of the
     Birkhoff-dominated `log Sprod`.

### (a) Reuse
- The Fekete-infimum value: Kingman gives a.e.-constant limit; the constant is the Fekete
  inf (noted in `tendsto_kingman_ergodic` docstring, `Kingman.lean:3438`). May need a small
  lemma `Γ_k = ⨅ n, (∫ log Sprod_k (n+1))/(n+1)` — **check whether already extractable**; if
  not, add it (subadditive Fekete: `Subadditive.tendsto_lim` / Mathlib
  `Subadditive`-style API, or prove `lim = inf` directly from monotone Fekete).
- `integrable_logSprod`, Fekete bounds `logSprod_le`/`neg_le_logSprod` give the domination
  for DCT.
- `Weyl.tendsto_eigenvalues₀` (`ExteriorNorm.lean:2731`) is the *operator-limit* continuity
  (continuity of `eigenvalues₀(Λ)` in `Λ`); useful framing but NOT the same as continuity of
  ergodic exponents in the generator.

### (b) New defs/theorems → new file `ErgodicTheory/Lyapunov/Regularity.lean`
```lean
/-- Γ_k as a Fekete infimum (if not already available). -/
theorem GammaK_eq_iInf : Γk = ⨅ n : ℕ, (∫ x, Real.log (Sprod A T (n+1) x) ∂μ)/(n+1)

/-- Per-n integral continuity under L¹-log convergence. -/
theorem tendsto_integral_logSprod_of_L1 (hconv : ...) (n) :
    Tendsto (fun m => ∫ x, Real.log (Sprod (Aₘ m) T (n+1) x) ∂μ) l (𝓝 (∫ x, Real.log (Sprod A T (n+1) x) ∂μ))

/-- **USC of partial sums in the generator.** -/
theorem GammaK_upperSemicontinuous (hconv : ...) :
    limsup (fun m => Γk (Aₘ m)) l ≤ Γk A

/-- top exponent USC -/
theorem topExp_upperSemicontinuous ...
/-- positive-exponent sum USC -/
theorem lyapPosSum_upperSemicontinuous ...
/-- bottom exponent LSC (since Γ_d continuous, see item 7) -/
theorem botExp_lowerSemicontinuous ...
```

### (c) Strategy
1. `lim = inf` (Fekete): the normalized integral sequence `aₙ = (∫ log Sprod (n+1))/(n+1)`
   comes from a subadditive integral sequence `bₙ = ∫ log Sprod n` (subadditivity from
   `isSubadditiveCocycle_logSprod` integrated + measure preservation). Fekete: `bₙ/n → inf`.
   Mathlib: `Subadditive` namespace if applicable; else prove monotone-ratio inf directly.
2. Per-`n` integral continuity: DCT (`MeasureTheory.tendsto_integral_of_dominated_convergence`)
   with dominating function `k·(posLog‖Aₘ‖ + posLog‖Aₘ⁻¹‖)` controlled by the L¹-convergence
   hypothesis (Scheffé/uniform-integrability if needed). This is the analytically heaviest
   sub-step.
3. USC of an inf of continuous functions: `limsup_m (inf_n f_n(Aₘ)) ≤ inf_n limsup_m f_n(Aₘ)
   = inf_n f_n(A)`. Mathlib: `le_iInf`, `Filter.limsup_le_iInf`-style, `ciInf_le`.
4. Positive sum USC = finite max of USC: `Filter.limsup` of a max ≤ max of limsups.

### (d) Difficulty: **hard** (the DCT/L¹ step and the inf-USC plumbing). The Fekete `lim=inf`
may be moderate. Risk: **high** — main risk is the precise convergence hypothesis and the
uniform-integrability machinery. Time-box; if DCT step stalls, deliver USC under the
**stronger uniform-envelope hypothesis** (regime 1) first, then attempt L¹ (regime 2).

### (e) Dependencies: items 1, 2, 6, **7** (for `Γ_d = ∫log|det|` continuity ⇒ bottom-exp
LSC). Foundational lemma `Γ_k = inf` may also feed a cleaner item 2.
Caveats (MUST appear in docstrings):
- "USC, not continuous"; individual interior exponents are differences of USC ⇒ no
  semicontinuity in general; bottom exponent is LSC because `Γ_d` is continuous; top exponent
  and all top-k partial sums and the positive sum are USC.
- Hypothesis is uniform-or-L¹-log convergence with a fixed integrable envelope; pointwise
  generator convergence alone is insufficient (DCT needs domination).

---

## 5. Restriction to invariant sub-cocycles (invariant subbundle)

### (a) Reuse
- Equivariance API: `Vflag_equivariant` (`Filtration.lean:369`), `lambdaBar_equivariant_ae`
  (`GrowthFunction.lean:637`), `spectrum_equivariant_ae` (`:329`).
- `MeasurableSubspace`, `orthProjMatrix`, `measurable_finrank` (`MeasurableSubspace.lean`,
  `Corollaries.lean:242`).
- The whole `IsOseledetsFiltration` apparatus to *state* the restricted spectrum.

### (b) New defs/theorems → new file `ErgodicTheory/Lyapunov/Restriction.lean`
```lean
/-- A measurable, cocycle-invariant subbundle. -/
structure InvariantSubbundle (μ T A) where
  W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))
  meas : MeasurableSubspace W
  invariant_ae : ∀ᵐ x ∂μ, Submodule.map (toEuclideanCLM (A x)).toLinearMap (W x) = W (T x)

/-- The restricted growth function / spectrum on the subbundle. -/
def restrictedSpectrum (W) (x) : Finset ℝ := (spectrum A T x).filter (realized on W x)

/-- Sub-spectrum: restricted spectrum ⊆ full spectrum, a.e. -/
theorem restrictedSpectrum_subset_ae : ∀ᵐ x, restrictedSpectrum W x ⊆ spectrum A T x

/-- Interlacing of dimensions / exponents. -/
theorem restricted_finrank_profile ...
```

### (c) Strategy
The exponents of the restricted cocycle are realized by vectors *inside* `W x`; since every
nonzero `v ∈ W x` has `lambdaBar A T x v ∈ spectrum A T x` (it is realized in the ambient
space too), the restricted spectrum is a subset of the ambient spectrum — **immediate from
`lambdaBar_mem_spectrum`**. The interlacing of *multiplicities* (restricted multiplicity ≤
ambient multiplicity per exponent) follows from `finrank` monotonicity on the equivariant,
ergodically-constant dimensions (reuse `exists_finrank_ae_eq` logic restricted to `W ∩ Vflag`).
The harder part is producing a *full restricted `IsOseledetsFiltration`* (a flag inside `W`):
intersect the ambient `Vflag` with `W` — these intersections are equivariant (intersection of
equivariant subspaces under the bijection `toEuclideanCLM (A x)`) and measurable
(intersection of measurable subbundles — needs a `MeasurableSubspace` inf lemma; check
`Lyapunov/Measurable.lean` for span/sum/inf API, may need a new `MeasurableSubspace.inf`).

Mathlib/internal: `Submodule.map_inf` issues (map of inf — only ≤ in general; but the
bijection makes it equality via `Submodule.map_inf_eq` for injective maps — check
availability), `Submodule.finrank_mono`, `Submodule.equivMapOfInjective`.

### (d) Difficulty: **moderate-to-hard**. The "subset of ambient spectrum" and
multiplicity-interlacing are moderate; the full restricted-filtration-as-`IsOseledetsFiltration`
is hard (needs `MeasurableSubspace` closure under inf, and uniqueness to identify the
restricted flag). Risk: medium — the measurability-of-intersection lemma is the main unknown.

### (e) Dependencies: items 6 (spectrum object), and reuses uniqueness from `Corollaries`.
Caveat: deliver in two stages — (i) sub-spectrum subset + dimension interlacing (cheap),
(ii) full restricted Oseledets filtration (expensive; may be deferred if inf-measurability is
missing). Honest: interlacing here means restricted exponents are a sub-multiset of the
ambient exponent multiset (with multiplicities), NOT classical Cauchy eigenvalue interlacing.

### (f) Needs the same standing hypotheses. det≠0 on the restriction: the cocycle restricted
to an invariant subbundle is automatically injective there (ambient `A x` is invertible), so
no extra hypothesis. Ergodicity needed for constant restricted multiplicities.

---

## 6. Full spectrum as a consumable object (FOUNDATIONAL — do first)

### (a) Reuse
- `exists_lam_tendsto_singularValue` (`OseledetsLimit.lean:3131`) — the sorted with-multiplicity
  `lam : ℕ → ℝ` plus a.e. σ-limit. This *is* the spectrum; it just needs packaging as a total
  `Fin d → ℝ` consumable object with accessors.
- `IsOseledetsFiltration.exists_multiplicity` (`Corollaries.lean:610`) — distinct exponents +
  multiplicities.
- `oseledetsLimit_eigenvalues₀_eq` (`OseledetsLimit.lean:3602`) — eigenvalue tie to `Λ`.
- `lamSing` (`:507`), `tendsto_log_singularValue` (`:468`).

### (b) New defs/theorems → new file `ErgodicTheory/Lyapunov/Spectrum.lean`
```lean
/-- The full sorted Lyapunov spectrum with multiplicity, as a total Fin d → ℝ. -/
noncomputable def exponents (A T μ ...) : Fin d → ℝ :=
  fun i => Classical.choose (exists_lam_tendsto_singularValue …) i   -- the sorted lam

theorem exponents_antitone : Antitone (exponents …)
theorem exponents_tendsto_log_singularValue :
    ∀ i, ∀ᵐ x, Tendsto (fun n => (n:ℝ)⁻¹ * Real.log (σᵢ (cocycle A T n x))) atTop (𝓝 (exponents i))
/-- as a multiset / sorted list for consumers -/
noncomputable def exponentMultiset : Multiset ℝ := (Finset.univ.val).map (exponents …)
/-- accessor: i-th largest exponent -/
def topExponent := exponents 0      -- ties to lam 0 of the filtration
/-- eigenvalues-of-Λ tie -/
theorem exponents_eq_log_eigenvalues_oseledetsLimit :
    ∀ᵐ x, ∀ i, Real.exp (exponents i) = (oseledetsLimit A T x).IsHermitian-eigenvalues₀ i
```

### (c) Strategy
Wrap `exists_lam_tendsto_singularValue` with `Classical.choose` (or carry the data through a
structure). Antitonicity from the `∀ a b, a ≤ b → b < d → lam b ≤ lam a` clause (convert to
`Antitone` on `Fin d`). The eigenvalue tie: combine `oseledetsLimit_eigenvalues₀_eq` with
`lamSing = exponents i` a.e. (via `lamSing_eq_of_tendsto` and the σ-limit). The relation to the
filtration's distinct `lam`/`m`: `exponents` repeats each distinct value `m i` times; prove
`exponentMultiset = ∑ i, m i • {distinct lam i}` (consistency lemma) — uses
`exists_multiplicity` and uniqueness.

Mathlib: `Multiset.map`, `Finset.sort`, `Antitone`/`Fin` conversions, `Classical.choose_spec`.

### (d) Difficulty: **moderate** (mostly packaging; the consistency lemma between the
sorted-σ spectrum and the distinct-exponent/multiplicity spectrum needs uniqueness and is the
only real content). Risk: low-medium.

### (e) Dependencies: none upstream (foundational). **Everything in items 1, 2, 3, 7 builds
on `exponents`.** Do this FIRST.
Caveat: choose ONE canonical `exponents` and make all later sums/identities go through it, to
avoid two incompatible spectra in the codebase.

### (f) Needs full standing hypotheses (det≠0, both integrabilities, ergodicity).

---

## 7. Trace / determinant identity (sum of all exponents = ∫ log|det|)

### (a) Reuse
- `Γ_d = lim (1/n) log Sprod_d` and `Sprod_d = ∏_{i<d} σᵢ = |det(A⁽ⁿ⁾)|`
  (the product of *all* singular values is the absolute determinant). The compound at `k=d`
  is `1×1` with entry `det`: `compoundMatrix d M` has finrank-1 target and equals `det M`.
- `tendsto_GammaK_of_integrableLogNorm` at `k=d`.
- `det_cocycle_ne_zero`; `Matrix.det_mul`; `integral_birkhoffSum` (`FurstenbergKesten.lean:230`).

### (b) New defs/theorems → new file `ErgodicTheory/Lyapunov/DetIdentity.lean`
```lean
/-- ∏ all singular values = |det|. -/
theorem Sprod_d_eq_abs_det (n x) : Sprod A T d n x = |(cocycle A T n x).det|
/-- log|det(A⁽ⁿ⁾)| is an additive (Birkhoff) cocycle. -/
theorem log_abs_det_cocycle_eq_birkhoffSum :
    Real.log |（cocycle A T n x).det| = birkhoffSum T (fun y => Real.log |(A y).det|) n x
/-- Sum of all exponents = ∫ log|det A|. -/
theorem sum_exponents_eq_integral_log_abs_det :
    ∑ i, exponents i = ∫ x, Real.log |(A x).det| ∂μ
/-- = Γ_d, and the a.e. growth statement. -/
theorem tendsto_log_abs_det_cocycle :
    ∀ᵐ x, Tendsto (fun n => (n:ℝ)⁻¹ * Real.log |(cocycle A T n x).det|) atTop (𝓝 (∑ i, exponents i))
/-- Volume contraction: ∑ exponents < 0 ⟹ a.e. volume → 0. (corollary) -/
```

### (c) Strategy
1. `Sprod_d = |det|`: `∏_{i<d} σᵢ = |det|` — Mathlib likely has
   `LinearMap.prod_singularValues` or via `det = ∏ eigenvalues of √(MᵀM)`; if not, use
   `Sprod_d = ‖compoundMatrix d‖` and `compoundMatrix d M = (det M)` (1×1), whose L2 opNorm is
   `|det M|`. Cleanest: `compoundMatrix_d_eq_det` helper, then `‖(c : 1×1)‖ = |c|`.
2. `log|det(A⁽ⁿ⁾)| = birkhoffSum (log|det A|)`: induction via `cocycle_succ`,
   `Matrix.det_mul`, `Real.log_mul`, `Real.log_abs` — **exact analogue of
   `logNorm_cocycle_le_birkhoffSum` but with equality** (det is multiplicative, not just
   submultiplicative). This is clean.
3. Birkhoff ergodic theorem: `(1/n) birkhoffSum (log|det A|) → ∫ log|det A|` a.e. (need
   `log|det A| ∈ L¹`, which follows from `hint`+`hint'`: `|log|det A|| ≤ d·(posLog‖A‖ +
   posLog‖A⁻¹‖)`). Reuse `Ergodic/Birkhoff.lean` (find the a.e. Birkhoff convergence thm).
4. `= ∑ exponents`: combine with `Γ_d = ∑_{i<d} lam i` (item 2 telescoping) and
   `Γ_d = ∫log|det|` (steps 1-3) and uniqueness.

Mathlib: `Matrix.det_mul`, `Real.log_abs`, `Real.log_mul`, Birkhoff a.e. theorem,
`MeasureTheory.Integrable`.

### (d) Difficulty: **moderate**. Step 1 (`Sprod_d = |det|`) is the only uncertain piece —
need the right Mathlib lemma for det = product of singular values; if absent, the compound
route works. Risk: medium (depends on that one lemma).

### (e) Dependencies: items 6 (exponents), 2 (Γ_d telescoping). Needs `log|det A| ∈ L¹`
helper (derive from existing integrabilities). Provides bottom-exp continuity for item 4.
Caveat: integrability of `log|det A|` must be established; it is implied by `hint`+`hint'`
but is a new small lemma.

### (f) det≠0 needed (else `log|det|` undefined / `det=0` case). Integrability of both
log-norms needed. Ergodicity needed for the constant (Birkhoff). The non-ergodic version is
item 9 (replace constant by `∫_invariants`).

---

## 8. Inverse / time reversal

### (a) Reuse
- `furstenbergKesten_bot` (`FurstenbergKesten.lean:359`) already gives the bottom exponent via
  the inverse cocycle.
- `inv_opNorm_inv_le_sigma`, `sigma_le_opNorm` (`OseledetsLimit.lean:191,185`) — σᵢ(M) and
  σ_{d-1-i}(M⁻¹) reciprocity at the matrix level.
- `compoundMatrix_mul_inv` etc. for exterior reciprocity.

### (b) New defs/theorems → new file `ErgodicTheory/Lyapunov/Inverse.lean`
```lean
/-- The inverse (time-reversed) generator. -/
def invGen (A) (x) := (A x)⁻¹       -- as a cocycle over T (one-sided reversal of the matrix)
/-- σᵢ(M⁻¹) = 1 / σ_{d-1-i}(M). -/
theorem singularValues_inv (hM : det ≠ 0) (i < d) :
    σᵢ(toEuclideanLin M⁻¹) = (σ_{d-1-i}(toEuclideanLin M))⁻¹
/-- Inverse exponents are negatives in reversed order. -/
theorem exponents_inv_eq_neg_rev :
    exponents (invGen A) T μ i = - exponents A T μ (Fin.rev i)   -- ties λ_i^{inv} = -λ_{d-1-i}
/-- positive spectrum of A ↔ negative spectrum of A⁻¹ -/
theorem lyapPosSum_inv_eq_neg_lyapNegSum
```

### (b/c) Strategy & subtlety
The cleanest *honest* statement is at the **singular-value level**: for an invertible matrix,
the singular values of `M⁻¹` are the reciprocals of those of `M` in reversed order
(`σᵢ(M⁻¹) = σ_{d-1-i}(M)⁻¹`). This is a matrix-SVD fact — prove from
`Matrix.toEuclideanLin M⁻¹ = (toEuclideanLin M)⁻¹` and the relation between singular values of
a map and its inverse (eigenvalues of `(M⁻¹)ᵀM⁻¹ = (MMᵀ)⁻¹`; reciprocal eigenvalues; note
left vs right singular values coincide in sorted multiset). Then
`(1/n) log σᵢ(A⁽ⁿ⁾⁻¹) → -lam_{d-1-i}` a.e.

**Caveat on "time reversal":** with a *one-sided* `T` (not necessarily invertible), the true
two-sided time-reversed cocycle is not available. What IS clean: the *inverse cocycle*
`(cocycle A T n x)⁻¹`, whose singular-value exponents are `-exponents(rev)`. If `T` is
invertible (an automorphism), the genuine reversed cocycle `cocycle (A∘T⁻¹...) T⁻¹` relates by
a base change; state the full time-reversal only under `T` invertible + `T⁻¹` measure-
preserving. Otherwise restrict to the inverse-matrix-cocycle statement.

Inverse-integrability: `log⁺‖A⁻¹‖, log⁺‖A‖ ∈ L¹` (already assumed `hint`,`hint'`) is exactly
the symmetric hypothesis making the inverse spectrum exist — **note this explicitly**.

### (d) Difficulty: **moderate-to-hard**. `singularValues_inv` (reciprocal-reversed) is the
crux and may need a new SVD lemma not in Mathlib (`SingularValues` API is thin). Risk: medium-
high on that lemma. The full `T`-invertible time reversal is hard — caveat / defer.

### (e) Dependencies: item 6. Provides the bridge tying positive ↔ negative spectra
(complements item 3).
Caveat: deliver the inverse-matrix-cocycle reciprocity first; the genuine two-sided
time-reversed flow statement only under invertible `T` (or defer to item 10).

### (f) Needs det≠0 + both integrabilities (the inverse-integrability `hint'` is precisely
what is needed and is already standing). Ergodicity for constants.

---

## 9. Relaxations (non-ergodic; singular / one-sided without det≠0)

### (A) Non-ergodic version (exponents as invariant functions)

#### (a) Reuse
- **`tendsto_kingman`** (non-ergodic, `Kingman.lean:3401`): limit is a `T`-invariant
  integrable `G`, `G = μ[g 1 | invariants T]`. This is the engine — `tendsto_GammaK` currently
  uses the *ergodic* Kingman; a parallel `tendsto_GammaK_nonergodic` using `tendsto_kingman`
  yields `Γ_k(x)` as an invariant measurable function instead of a constant.
- `integrable_logSprod`, `bddBelow_logSprod`, `Sprod_pos` — all hypotheses of `tendsto_kingman`
  are already discharged for `log Sprod_k`.

#### (b) New theorems → `ErgodicTheory/Lyapunov/NonErgodic.lean`
```lean
theorem tendsto_GammaK_nonergodic (hmp : MeasurePreserving T μ μ) (k ≤ d) :
    ∃ G : X → ℝ, (G ∘ T =ᵐ G) ∧ Integrable G μ ∧
      ∀ᵐ x, Tendsto (fun n => (n:ℝ)⁻¹ * Real.log (Sprod A T k n x)) atTop (𝓝 (G x))
theorem exists_exponents_nonergodic :
    ∃ lam : ℕ → X → ℝ, (each invariant a.e.) ∧ ∀ i < d, ∀ᵐ x, σ-limit → lam i x
```
i.e. the entire item-6 spectrum as `T`-invariant measurable functions; sums (item 1) and the
det identity (item 7, with `∫log|det|` replaced by `μ[log|det A| | invariants T]`) carry over.

#### (c) Strategy: mechanical re-derivation swapping `tendsto_kingman_ergodic` →
`tendsto_kingman`. The σ-difference (`tendsto_log_singularValue`) is pointwise and unchanged.

#### (d) Difficulty: **moderate** (parallel plumbing of existing ergodic proofs). Risk: low-
medium (mostly copy-with-invariant-limit). This is "cheap given what we have" — include it.

#### (e) Dependencies: item 6 (to know the target shape). Independent of ergodicity.

### (B) Singular / one-sided without det≠0 (possibly-singular matrix cocycles)

#### (a) Reuse
- `Sprod`, `Sprod_submul` (`OseledetsLimit.lean:141`) — **submultiplicativity holds with NO
  invertibility** (it is pure `ExteriorNorm.prod_singularValues_comp_le`). The positivity
  `Sprod_pos` and the lower Fekete bound are what need det≠0; the **upper** half does not.
- `logSprod_le` (upper bound) needs `singularValues_cocycle_pos` (currently det≠0) only to
  take logs; for the *one-sided upper* statement use `posLog` or handle `Sprod = 0`.
- `furstenbergKesten_top`'s structure, but the bounded-below proviso fails without `hint'`.

#### (b) New theorems → `ErgodicTheory/Lyapunov/Singular.lean`
```lean
/-- One-sided top exponent for possibly-singular A, WITHOUT log⁺‖A⁻¹‖ and WITHOUT det≠0:
the normalized log-norm has an a.e. limit in [-∞, ∞) (EReal), or an upper bound λ₁⁺. -/
theorem limsup_logNorm_cocycle_le ... (only hint : IntegrableLogNorm A μ) :
    ∀ᵐ x, limsup (fun n => (n:ℝ)⁻¹ * Real.log ‖cocycle A T n x‖) ≤ λ₁
/-- top-k volume upper growth without inverse-integrability -/
theorem limsup_logSprod_le ...
```

#### (c) Strategy: subadditive cocycle `log⁺‖A⁽ⁿ⁾‖` (or `Sprod` via `posLog`) still satisfies
Kingman's *upper* conclusion without a finite lower bound — the limit lives in `[-∞,∞)`. Use
the EReal Kingman skeleton already inside `Kingman.lean` (the `ecdiv`/`ereal_limsup`
machinery, `:563+`). The positive-exponent / top-exponent *upper bounds* are the safe
deliverables; the full spectrum is not available for singular cocycles.

#### (d) Difficulty: **hard** (EReal-valued limits, handling `Sprod = 0`, `log 0 = -∞`).
Risk: high. **Lowest priority within item 9**; deliver only the top-exponent / top-k upper
bound, clearly scoped.

#### (e) Dependencies: none new; reuses FK skeleton. Caveat: only one-sided (upper) statements;
no filtration, no exact exponents for singular cocycles. State the `[-∞,∞)`-valued nature.

#### (f) This is the item that **drops** det≠0 and `hint'`. Be explicit: forward integrability
`hint` alone; ergodicity still used for a.e.-constant limit (or use non-ergodic 9A).

---

## 10. Lower priority (not blocking): two-sided splitting; continuous-time

- **Two-sided Oseledets splitting (Stage C).** Requires the *backward* filtration (from
  `T⁻¹` / inverse cocycle) and proving the direct-sum `E = ⊕ Eᵢ` with `Eᵢ` the intersection of
  forward-`Vᵢ` and backward-`V^{i}`. Needs invertible `T`. Reuse `furstenbergKesten_bot`,
  item 8's inverse spectrum, and `RuelleReverse.lean`/`ChainRecursion.lean`. **Research-to-hard;
  do not schedule now** — listed so it is not excluded. Largest new development.
- **Continuous-time / flow version.** A genuine new construction (cocycle over a flow `φ_t`,
  generator a measurable family of vector fields / matrices, exponents via `(1/t)log`). Not
  derivable from the discrete development; **research-level**, defer.

Difficulty: both **research-level**. Risk: very high. Explicitly out of scope for this round.

---

## STEP 3 — Implementation order & file layout

### Order (dependency-respecting, cheapest foundational first)

1. **#6 Full spectrum object** (`Spectrum.lean`) — foundational `exponents : Fin d → ℝ`,
   antitone, σ-limit, eigenvalue tie. Everything else consumes it. *(moderate)*
2. **#1 Exponent sums** (`ExponentSums.lean`) — `lyapPosSum`/`lyapNonnegSum`/`lyapNegSum`/
   `lyapTotalSum` over `exponents`. *(trivial-moderate)*
3. **#3 Sign/vanishing** (append to `ExponentSums.lean`) — pure arithmetic. *(trivial)*
4. **#7 Trace/det identity** (`DetIdentity.lean`) — `Sprod_d = |det|`, Birkhoff, `∑ exp =
   ∫log|det|`. Provides `Γ_d` continuity for #4. *(moderate)*
5. **#2 Exterior characterization** (`ExteriorCocycle.lean`) — `Γ_k = ∑ top-k exp =`
   minor/wedge growth; `lyapPosSum = Γ_{k₊}`. *(moderate)*
6. **#5 Restriction** (`Restriction.lean`) — sub-spectrum subset + interlacing (stage i),
   restricted filtration (stage ii, conditional on inf-measurability). *(moderate-hard)*
7. **#8 Inverse** (`Inverse.lean`) — `singularValues_inv`, `exponents_inv = -rev`. *(moderate-
   hard; one SVD lemma is the risk)*
8. **#4 Regularity** (`Regularity.lean`) — Fekete `lim=inf`, per-`n` DCT continuity, USC of
   top exp / partial sums / positive sum, LSC of bottom exp. *(hard; highest value)*
9. **#9 Relaxations** — `NonErgodic.lean` (moderate, cheap, do early if convenient),
   `Singular.lean` (hard, scoped to upper bounds, low priority).
10. **#10** — deferred (research-level), tracked only.

Note: #9A (NonErgodic) is independent and cheap; it can be slotted right after #6 if desired,
since it only re-plumbs Kingman.

### File layout (all under `ErgodicTheory/Lyapunov/`, all imported from `ErgodicTheory.lean`)
```
Spectrum.lean         (#6)   imports OseledetsLimit, Corollaries
ExponentSums.lean     (#1,#3) imports Spectrum
DetIdentity.lean      (#7)   imports Spectrum, ExteriorNorm, Ergodic/Birkhoff
ExteriorCocycle.lean  (#2)   imports Spectrum, ExteriorNorm, OseledetsLimit
Restriction.lean      (#5)   imports Corollaries, Filtration, Measurable
Inverse.lean          (#8)   imports Spectrum, OseledetsLimit
Regularity.lean       (#4)   imports Spectrum, DetIdentity, ExteriorCocycle, ExteriorNorm
NonErgodic.lean       (#9A)  imports OseledetsLimit, Kingman, Spectrum
Singular.lean         (#9B)  imports Cocycle/FurstenbergKesten, OseledetsLimit, Kingman
```
Each new file must be added to `ErgodicTheory.lean` and pass the `AxiomAudit` discipline
(`[propext, Classical.choice, Quot.sound]`); since all new results funnel through
`exists_lam_tendsto_singularValue` / `oseledets_filtration`, the axiom set is unchanged.

### Top 3 risks
1. **#4 DCT / L¹-log continuity step** (and the Fekete `lim = inf` extraction): the
   analytically heaviest, with a delicate hypothesis (uniform vs L¹-log). Mitigation: deliver
   USC under the stronger uniform-envelope hypothesis first; time-box the L¹ regime.
2. **Missing thin SVD lemmas**: `Sprod_d = |det|` (#7) and `σᵢ(M⁻¹) = σ_{d-1-i}(M)⁻¹` (#8) may
   not exist in Mathlib's sparse `SingularValues` API. Mitigation: route #7 through
   `compoundMatrix d = det` (already have compound API); for #8 build the reciprocal-singular-
   value lemma from `gram` eigenvalue reciprocity (`(M⁻¹)ᵀ M⁻¹ = (MᵀM)⁻¹` ⇒ reciprocal
   eigenvalues) — additive infra, upstreamable.
3. **#5 measurability of subspace intersection** (`MeasurableSubspace.inf`): if absent, the
   full restricted `IsOseledetsFiltration` is blocked. Mitigation: deliver the sub-spectrum
   subset + dimension interlacing (which avoid intersections) as the guaranteed part; treat
   the full restricted flag as stretch.
```
