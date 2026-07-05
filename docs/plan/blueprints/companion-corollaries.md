# Companion corollaries of `oseledets_filtration` — Lean-ready blueprint

> Author: mathematician pass, 2026-06-11. All statement skeletons **typecheck** against the
> current build (`/tmp/probe_companion.lean`, `lake env lean` — only `sorry` warnings), and the
> three name-sensitive glue steps are **fully proved** in probes
> (`/tmp/probe_glue.lean`, `/tmp/probe_glue2.lean`, `/tmp/probe_ergconst.lean` — zero sorries).
> Nothing here touches the proved main theorem or its assembly chain.

## 0. TL;DR / design decisions

| # | Corollary | Shape decision | Effort (lines) | Risk |
|---|---|---|---|---|
| C2a | growth-sublevel characterization | separate corollary, **witness-quantified** | ~120–160 | LOW |
| C3 | top exponent = norm growth | separate corollary, witness-quantified | ~180–250 | LOW |
| C2b | uniqueness of `(k, lam, V)` | separate corollary, two witnesses | ~150–200 (after C2a) | LOW-MED |
| C1 | a.e.-constant multiplicities | separate corollary + post-hoc strengthened `∃` | ~200–260 | LOW (all glue probed) |

**The single most important discovery** (see §6): all three corollaries are provable from the
*statement* of `oseledets_filtration` alone — quantified over an arbitrary witness `(k, lam, V)`
of its conclusion — with **no** access to the construction. C2a/C2b/C3 need literally nothing
from the repo's analytic layers; C1 additionally needs ergodicity + the `MeasurableSubspace`
conjunct. Consequently:

1. **Do NOT thread a multiplicity conjunct through the assembly chain.** The "free from the
   construction" route (the witness is `V'` = `Vslow` at deterministic cutoffs, a band
   projection of deterministic rank — confirmed below, §5.1) would require editing the
   statements of `oseledets_filtration`, `oseledets_filtration_of_topgap`,
   `oseledets_filtration_of_upper'`, `oseledets_filtration_of_slowflag`, and
   `oseledets_filtration_of_interfaces'`, plus a new `slowProjector` rank lemma. The
   witness-independent corollary subsumes it and costs less.
2. **Bundle the conclusion once** as a predicate `IsOseledetsFiltration` (§1). The repackaged
   existence theorem `oseledets_filtration'` is a 3-line proof (verified compiling, sorry-free,
   in the probe). All corollaries become `IsOseledetsFiltration.*` dot-notation lemmas — the
   exact Mathlib idiom (`IsLowerSet.*`, `IsVonNBounded.*`, …).

**Recommended implementation order**: §1 → C2a → C3 → C2b → C1 (cheapest first; C2b consumes
C2a; C1 is independent of the others).

---

## 1. Common infrastructure (NEW, target file `ErgodicTheory/Corollaries.lean`)

New module `ErgodicTheory/Corollaries.lean`, `import ErgodicTheory.MultiplicativeErgodic`, imported from
`ErgodicTheory.lean`. (If upstreamed: `Mathlib/Dynamics/Ergodic/Oseledets/Corollaries.lean`.)

### 1.1 The bundled predicate (typechecked verbatim)

```lean
/-- The conclusion of `oseledets_filtration`, bundled as a predicate on a candidate
exponent/filtration datum `(k, lam, V)`. -/
def IsOseledetsFiltration (μ : Measure X) (T : X → X) (A : X → Matrix (Fin d) (Fin d) ℝ)
    (k : ℕ) (lam : Fin k → ℝ)
    (V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  StrictAnti lam ∧
  (∀ i, MeasurableSubspace fun x => V i x) ∧
  ∀ᵐ x ∂μ,
    V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
    (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
    (∀ i : Fin (k + 1),
      Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (V i x) = V i (T x)) ∧
    (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ V i.succ x →
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
          atTop (𝓝 (lam i)))
```

The conjunction is **byte-identical** to the conclusion of `oseledets_filtration`
(`ErgodicTheory/MultiplicativeErgodic.lean:53-67`), so:

```lean
theorem oseledets_filtration' … :
    ∃ (k : ℕ) (lam : Fin k → ℝ) (V : …), IsOseledetsFiltration μ T A k lam V := by
  obtain ⟨k, lam, V, h1, h2, h3⟩ := oseledets_filtration hT A hA hAmeas hint hint'
  exact ⟨k, lam, V, h1, h2, h3⟩
```

— **PROVED** in the probe (no sorry). ~25 lines total for §1.1.

### 1.2 Flag-order helpers (NEW, shared by C2a/C2b/C3)

On the a.e. good set (the five-conjunct block at a point `x`):

1. `IsOseledetsFiltration.antitone_good` — `j ≤ j' → V j' x ≤ V j x`. From conjunct 3
   (`V i.succ x < V i.castSucc x`) by induction over the gap (`Fin.le_induction` /
   nat-valued induction). NEW, ~20 lines.
2. `IsOseledetsFiltration.exists_stratum_good` — for `v ≠ 0` there is `i : Fin k` with
   `v ∈ V i.castSucc x`, `v ∉ V i.succ x`, and `∀ j : Fin (k+1), v ∈ V j x ↔ (j : ℕ) ≤ i`.
   Take `i` = the largest index whose level contains `v`; uses `V 0 x = ⊤` (so the index set is
   nonempty), `V (Fin.last k) x = ⊥` (so the largest index is interior, since `v ≠ 0`), and
   step 1 (so membership is an initial segment). NEW, ~40 lines.
3. On the stratum of `v`, conjunct 5 gives `Tendsto … (𝓝 (lam i))`; hence
   `limsup … = lam i` by `Filter.Tendsto.limsup_eq`
   (Mathlib `Topology/Order/LiminfLimsup.lean:191`). 1 line at each use site.

These three are the entire engine for C2 and the lower half of C3.

---

## 2. C2 — canonical characterization and uniqueness (CHEAPEST)

### 2.1 C2a exact statement (typechecked)

```lean
/-- **C2a.** A.e., each filtration level is exactly the sublevel set of the
exponential growth rate. (Pointwise consequence of the defining a.e. block.) -/
theorem IsOseledetsFiltration.ae_mem_iff_limsup_le
    (hV : IsOseledetsFiltration μ T A k lam V) :
    ∀ᵐ x ∂μ, ∀ (i : Fin k) (v : EuclideanSpace ℝ (Fin d)),
      v ∈ V i.castSucc x ↔ v = 0 ∨
        limsup (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖) atTop ≤ lam i
```

Notes on the shape:
* The `v = 0 ∨ …` disjunct is forced: `Real.log ‖0‖ = Real.log 0 = 0`, so the bare limsup
  condition would wrongly exclude `0` whenever `lam i < 0`. This mirrors the repo's own
  `lambdaSublevel` membership (`mem_lambdaSublevel`, `ErgodicTheory/Lyapunov/Filtration.lean:109`).
* Indexing: levels `0 … k-1` are covered as `i.castSucc`; level `k` is `⊥` and is already a
  conjunct of the block, so it needs no clause.
* **No hypotheses beyond `hV`** — no ergodicity, no measurability, no invertibility, not even a
  probability measure. This is the headline surprise (§6.1).

### 2.2 C2a proof ladder

1. `filter_upwards [hV.2.2]`; fix a good `x`, an `i`, a `v`; WLOG `v ≠ 0` (the `v = 0` case is
   `Submodule.zero_mem` / `Or.inl rfl`).
2. (→) By §1.2.2 get the stratum `j` of `v`; `v ∈ V i.castSucc x` forces `(i : ℕ) ≤ (j : ℕ)`
   (initial-segment clause). §1.2.3: `limsup = lam j ≤ lam i` by `hV.1.antitone`
   (`StrictAnti.antitone`). EXISTING: `Filter.Tendsto.limsup_eq` (Mathlib).
3. (←) Contrapositive: if `v ∉ V i.castSucc x` then its stratum `j` has `(j : ℕ) < (i : ℕ)`,
   so `limsup = lam j > lam i` (`hV.1` strict), contradicting `limsup ≤ lam i`. EXISTING:
   same two lemmas.

Total: ~60 lines on top of §1.2. **No repo analytic lemma is consumed.**

*Cross-check against the construction* (not needed for the proof, but confirms consistency):
for the constructed witness the same identification is exactly the proved slow-flag chain —
forward inclusion `limsup_le_of_mem_Vslow` (`ErgodicTheory/Lyapunov/CapstoneWiring.lean:212`)
massaged by `vslow_subset_lambdaSublevel_of_upper` (`ErgodicTheory/Lyapunov/AssemblyFromUpper.lean:66`);
reverse inclusion `ae_lambdaSublevel_le_Vslow` (`ErgodicTheory/Lyapunov/SpectralIdentification.lean:349`);
combined by `hslowflag_of_upper` (`ErgodicTheory/Lyapunov/AssemblyFromUpper.lean:113`), instantiated at
`ErgodicTheory/Lyapunov/AssemblyTopGap.lean:149-152`; dictionary limsup ↔ `lambdaBar` is
`limsup_log_norm_cocycle_eq_lambdaBar` (`ErgodicTheory/Lyapunov/ForwardAngle.lean:289`) plus
`mem_lambdaSublevel` (`ErgodicTheory/Lyapunov/Filtration.lean:109`).

### 2.3 C2b exact statement (typechecked)

```lean
/-- **C2b.** Uniqueness: two Oseledets filtration data for the same cocycle agree —
same count, same exponents, a.e. the same subspaces. -/
theorem IsOseledetsFiltration.unique
    [IsProbabilityMeasure μ]
    {k₂ : ℕ} {lam₂ : Fin k₂ → ℝ}
    {V₂ : Fin (k₂ + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (hV : IsOseledetsFiltration μ T A k lam V)
    (hV₂ : IsOseledetsFiltration μ T A k₂ lam₂ V₂) :
    ∃ hk : k = k₂,
      (∀ i : Fin k, lam i = lam₂ (Fin.cast hk i)) ∧
      ∀ᵐ x ∂μ, ∀ i : Fin (k + 1), V i x = V₂ (Fin.cast (by omega) i) x
```

(The `Fin.cast (by omega) i` elaborates fine inside the `∃ hk` binder — verified in the probe.
`[IsProbabilityMeasure μ]` is genuinely needed: a good point must *exist*.)

### 2.4 C2b proof ladder

1. **Exponent identification.** Pick a single good point `x₀` in the intersection of the two
   a.e. blocks (`Filter.Eventually.and` + `Filter.Eventually.exists`; `μ.ae.NeBot` from
   `IsProbabilityMeasure`). At `x₀`, the set of realized limits
   `E := {r | ∃ v ≠ 0, Tendsto … (𝓝 r)}` equals `Set.range lam` *and* `Set.range lam₂`:
   * `⊆`: §1.2.2 + conjunct 5 + uniqueness of limits (`tendsto_nhds_unique`).
   * `⊇`: every stratum is nonempty by conjunct 3 (`SetLike.exists_of_lt` on
     `V i.succ x₀ < V i.castSucc x₀`; the witness is `≠ 0` because `0` lies in every level).
   NEW ~50 lines.
2. **Two strictly antitone enumerations of the same finite set coincide.** Helper
   `strictAnti_fin_range_eq : StrictAnti f → StrictAnti g → Set.range f = Set.range g →
   ∃ h : k = k₂, ∀ i, f i = g (Fin.cast h i)`. Route: pass to `Finset.image`, use
   `Finset.orderEmbOfFin_unique` (Mathlib `Data/Finset/Sort.lean:264`) on the reversed
   (strictMono) enumerations, or a direct double-induction. NEW ~50 lines (pure order/Fin
   bookkeeping; this is the fiddliest part of C2b). This yields `hk : k = k₂` and
   `lam = lam₂ ∘ Fin.cast hk`.
3. **Levelwise subspace identity.** `filter_upwards [C2a hV, C2a hV₂, hV.2.2, hV₂.2.2]`. For
   interior `i = j.castSucc`: both sides equal
   `{v | v = 0 ∨ limsup … ≤ lam j}` by C2a (membership extensionality, `Submodule.ext`).
   For `i = Fin.last k`: both sides are `⊥` (conjunct 2). Index transport along `Fin.cast hk`
   is `Fin.cast`-val bookkeeping (`Fin.coe_cast`). NEW ~50 lines.

Total: ~150–200 lines on top of C2a. EXISTING cited: `tendsto_nhds_unique`,
`SetLike.exists_of_lt`, `Finset.orderEmbOfFin_unique`, `Submodule.ext`.

### 2.5 Names and placement

* `ErgodicTheory.IsOseledetsFiltration.ae_mem_iff_limsup_le` (C2a)
* `ErgodicTheory.IsOseledetsFiltration.unique` (C2b)
* both in `ErgodicTheory/Corollaries.lean`, section `Uniqueness`.

---

## 3. C3 — top exponent = operator-norm growth

### 3.1 Exact statements (typechecked)

```lean
/-- The filtration is nontrivial in positive dimension. -/
theorem IsOseledetsFiltration.k_pos
    [IsProbabilityMeasure μ] (hd : 0 < d)
    (hV : IsOseledetsFiltration μ T A k lam V) : 0 < k

/-- **C3.** The top Lyapunov exponent is the exponential growth rate of the
operator norm of the cocycle. -/
theorem IsOseledetsFiltration.tendsto_log_opNorm_cocycle
    [IsProbabilityMeasure μ] (hA : ∀ x, (A x).det ≠ 0)
    (hV : IsOseledetsFiltration μ T A k lam V) (hk : 0 < k) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖)
      atTop (𝓝 (lam ⟨0, hk⟩))
```

(`‖cocycle A T n x‖` is the scoped `Matrix.Norms.L2Operator` norm, exactly as in
`furstenbergKesten_top`, `ErgodicTheory/Cocycle/FurstenbergKesten.lean:289`.) `hA` is needed
(norm positivity / nonvanishing of images); ergodicity and integrability are **not**.

### 3.2 Proof ladder

1. `k_pos`: at a good point, `k = 0` would force `⊤ = V 0 x = V (Fin.last 0) x = ⊥`,
   contradicting `finrank (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = d > 0`
   (`finrank_top`, `finrank_euclideanSpace_fin`). NEW ~15 lines.
2. **Column-sum bound** (NEW lemma, **fully proved in probe** `/tmp/probe_glue2.lean` B,
   ~30 lines):
   ```lean
   theorem Matrix.l2_opNorm_le_sum_norm_basisFun (M : Matrix (Fin d) (Fin d) ℝ) :
       ‖M‖ ≤ ∑ j, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M (EuclideanSpace.basisFun (Fin d) ℝ j)‖
   ```
   Proof: `Matrix.l2_opNorm_toEuclideanCLM` (Mathlib; already used at
   `ErgodicTheory/Lyapunov/GrowthFunction.lean:104`) + `ContinuousLinearMap.opNorm_le_bound` +
   basis expansion + `norm_sum_le` + the coordinate bound `PiLp.norm_apply_le` (Mathlib).
   Upstreamable; place in `ErgodicTheory/Cocycle/Norm.lean`.
3. **Upper half.** Fix good `x`, `ε > 0`. Each `e_j := EuclideanSpace.basisFun … j` is nonzero,
   so by §1.2.2 + conjunct 5 + `hV.1.antitone`, eventually
   `(1/n) log ‖M_n e_j‖ ≤ lam ⟨0,hk⟩ + ε/2` for **all** `j` simultaneously
   (`Filter.eventually_all` over `Fin d`). Step 2 then gives
   `‖M_n‖ ≤ d · exp (n (lam₀ + ε/2))`, so
   `(1/n) log ‖M_n‖ ≤ (log d)/n + lam₀ + ε/2 ≤ lam₀ + ε` eventually
   (`Real.log_le_log`, `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`-free, just
   `Finset.sum_le_card_nsmul` + log monotonicity). NEW ~90 lines (log bookkeeping; positivity
   from `norm_cocycle_pos`, `ErgodicTheory/Cocycle/FurstenbergKesten.lean:44` — needs
   `NeZero d`, available since `0 < d` follows from `0 < k` at a good point, cf. step 1
   reversed: `k > 0` plus `V 1 x < V 0 x = ⊤` forces `d > 0`).
4. **Lower half.** Pick `v` in the top stratum (`SetLike.exists_of_lt` on
   `V (0:Fin k).succ x < V (0:Fin k).castSucc x`, then `v ≠ 0` since `0 ∈ V _.succ x`).
   Conjunct 5: `(1/n) log ‖M_n v‖ → lam ⟨0,hk⟩`. Combine with
   `‖M_n v‖ ≤ ‖M_n‖ ‖v‖` (`ContinuousLinearMap.le_opNorm` +
   `Matrix.l2_opNorm_toEuclideanCLM`), so
   `(1/n) log ‖M_n‖ ≥ (1/n) log ‖M_n v‖ - (1/n) log ‖v‖ ≥ lam₀ - ε` eventually. Image
   nonvanishing: `det_cocycle_ne_zero` (`ErgodicTheory/Cocycle/FurstenbergKesten.lean:36`) +
   `injective_toEuclideanLin` (`ErgodicTheory/Lyapunov/OseledetsLimit.lean:228`). NEW ~50 lines.
5. **Assemble** via the ε-characterization of `Tendsto` on ℝ (`Metric.tendsto_atTop`,
   `Real.dist_eq`, `abs_sub_lt_iff`). ~20 lines.

Total: ~180–250 lines. **Neither Furstenberg–Kesten nor any singular-value lemma is needed**
(§6.2). Optional 5-line follow-up: combining with `furstenbergKesten_top`
(`ErgodicTheory/Cocycle/FurstenbergKesten.lean:289`) and `tendsto_nhds_unique` identifies the FK
constant with `lam ⟨0,hk⟩` (`oseledets_top_exponent_eq_furstenbergKesten`).

### 3.3 Names and placement

* `ErgodicTheory.IsOseledetsFiltration.k_pos`
* `Matrix.l2_opNorm_le_sum_norm_basisFun` (in `ErgodicTheory/Cocycle/Norm.lean`; Mathlib-bound)
* `ErgodicTheory.IsOseledetsFiltration.tendsto_log_opNorm_cocycle`
* optional `ErgodicTheory.oseledets_top_exponent_eq_furstenbergKesten`
* in `ErgodicTheory/Corollaries.lean`, section `TopExponent`.

---

## 4. C1 — a.e.-constant multiplicities

### 4.1 Shape decision: separate corollary, NOT a strengthened conjunct

The task's premise is **confirmed**: the witness handed to `oseledets_filtration` is
`V' A T lam0` (`ErgodicTheory/Lyapunov/SlowFlagBridge.lean:78`, threaded through
`oseledets_filtration_of_interfaces'`, `ErgodicTheory/Lyapunov/FiltrationAssemblyBridge.lean:261`),
whose interior level `i` is `Vslow A T (exp (expEnum lam0 d i)) x` — the **range of the
orthogonal band projector** `slowProjector` (`ErgodicTheory/Lyapunov/ForwardV.lean:174`), i.e. the
spectral projection of the sanitized limit `lambdaHat` below the deterministic cutoff. A.e. its
rank is `#{j : Fin d | lam0 j ≤ expEnum lam0 d i}` — deterministic — via
`spectrum_lambdaHat_eq_ae` (`ErgodicTheory/Lyapunov/SpectrumResiduals.lean:34`),
`ae_lamSing_eq_lam0` (`SpectrumResiduals.lean:304`), and a rank computation that would mimic
`bandProjector_rank` (`ErgodicTheory/Lyapunov/OseledetsLimit.lean:811`, whose proof via
`cfc_eq_eigenvectorUnitary_conj`, `OseledetsLimit.lean:799`, is generic in the Hermitian
matrix).

**But it is not "for free"**: that route needs (i) a new `slowProjector_rank` lemma (~60 lines),
(ii) a `finrank (range (toEuclideanCLM P)) = P.rank` bridge (~25 lines, via
`Matrix.rank_eq_finrank_range_toLin`, Mathlib `LinearAlgebra/Matrix/Rank.lean:285`, and
`Matrix.toLpLin_eq_toLin`), and above all (iii) **editing five committed theorem statements**
(the main theorem and the four assembly wrappers listed in §0.1) to thread the conjunct.
Meanwhile the ergodic route below is witness-independent, costs the same or less, and lets the
strengthened existential be derived *post hoc* without touching the proved chain:

```lean
theorem oseledets_filtration_with_multiplicities … :
    ∃ k lam V (m : Fin (k+1) → ℕ), IsOseledetsFiltration μ T A k lam V ∧
      StrictAnti m ∧ m 0 = d ∧ m (Fin.last k) = 0 ∧
      ∀ᵐ x ∂μ, ∀ i, Module.finrank ℝ (V i x) = m i :=
  -- obtain the witness from `oseledets_filtration'`, apply C1 to it.  (~15 lines)
```

### 4.2 Exact statements (typechecked)

```lean
/-- **C1.** Every Oseledets filtration has `μ`-a.e. constant level dimensions. -/
theorem IsOseledetsFiltration.exists_finrank_ae_eq
    [IsProbabilityMeasure μ] (hT : Ergodic T μ) (hA : ∀ x, (A x).det ≠ 0)
    (hV : IsOseledetsFiltration μ T A k lam V) :
    ∃ m : Fin (k + 1) → ℕ, StrictAnti m ∧ m 0 = d ∧ m (Fin.last k) = 0 ∧
      ∀ᵐ x ∂μ, ∀ i, Module.finrank ℝ (V i x) = m i

/-- **C1'.** Per-exponent multiplicities: positive, summing to `d`. -/
theorem IsOseledetsFiltration.exists_multiplicity
    [IsProbabilityMeasure μ] (hT : Ergodic T μ) (hA : ∀ x, (A x).det ≠ 0)
    (hV : IsOseledetsFiltration μ T A k lam V) :
    ∃ m : Fin k → ℕ, (∀ i, 0 < m i) ∧ (∑ i, m i) = d ∧
      ∀ᵐ x ∂μ, ∀ i : Fin k,
        Module.finrank ℝ (V i.castSucc x) = Module.finrank ℝ (V i.succ x) + m i
```

(`StrictAnti m` for `m : Fin (k+1) → ℕ` means `m 0 = d > m 1 > ⋯ > m k = 0` — the codimension
profile. C1' is the per-exponent version `mᵢ = dim Vᵢ − dim Vᵢ₊₁ ≥ 1`, `Σ mᵢ = d`.)

This is the corollary where ergodicity is genuinely load-bearing (§6.3): without it the level
dimensions of *some* witness could vary measurably across distinct ergodic components — here
`μ` is ergodic, so a.e.-invariant measurable ℕ-valued functions are a.e. constant.

### 4.3 Proof ladder (all three glue steps ALREADY VERIFIED in probes)

1. **Trace bridge** (NEW, ~35 lines, **fully proved** across `/tmp/probe_glue.lean` A and
   `/tmp/probe_glue2.lean` A'):
   ```lean
   theorem trace_orthProjMatrix (K : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
       Matrix.trace (orthProjMatrix K) = (Module.finrank ℝ K : ℝ)
   ```
   Route: `LinearMap.IsProj K K.starProjection` from `Submodule.starProjection_apply_mem` +
   `starProjection_eq_self_iff` (Mathlib `Analysis/InnerProductSpace/Projection/Basic.lean:192,265`);
   `LinearMap.IsProj.trace` (Mathlib `LinearAlgebra/Trace.lean:334`);
   `LinearMap.trace_eq_matrix_trace` (`Trace.lean:86`); and the round-trip
   `toMatrix basisFun basisFun (toEuclideanCLM M) = M` via `Matrix.toLpLin_eq_toLin`
   (NB: `Matrix.toEuclideanLin_eq_toLin` is **deprecated** in the pinned Mathlib — use the
   `toLpLin` name) + `LinearMap.toMatrix_toLin`. Place next to `orthProjMatrix` in
   `ErgodicTheory/Lyapunov/MeasurableSubspace.lean`.
2. **Measurability of the dimension** (NEW, ~25 lines, **fully proved** in
   `/tmp/probe_ergconst.lean` (ii)):
   ```lean
   theorem MeasurableSubspace.measurable_finrank (hV : MeasurableSubspace V) :
       Measurable fun x => Module.finrank ℝ (V x)
   ```
   Route: `x ↦ Matrix.trace (orthProjMatrix (V x))` is measurable (entrywise sums of the
   measurable projector family); `measurable_to_countable'` with singleton preimages pulled
   back along step 1 (`exact_mod_cast Iff.rfl` closes the cast).
3. **Equivariance transport** (NEW, ~25 lines): `(A x).det ≠ 0` makes
   `toEuclideanCLM (A x)` a linear auto-equivalence (`LinearEquiv.ofLinear` with inverse
   `toEuclideanCLM (A x)⁻¹`; the two cancellation identities are re-derivations of the
   *private* `Aclm_inv_left/right`, `ErgodicTheory/Lyapunov/Filtration.lean:292-302` — re-prove
   locally, 6 lines each, via `Matrix.nonsing_inv_mul`/`mul_nonsing_inv`). Then
   `LinearEquiv.finrank_map_eq` (Mathlib `LinearAlgebra/Dimension/Finrank.lean:121`) turns
   conjunct 4 into: a.e., `finrank (V i (T x)) = finrank (V i x)`.
4. **Ergodic constancy** (**fully proved pattern** in `/tmp/probe_ergconst.lean` (i)): for each
   `i`, apply `Ergodic.ae_eq_const_of_ae_eq_comp₀` (Mathlib
   `Dynamics/Ergodic/Function.lean:67`; ℕ is `Nonempty` + `CountablySeparated`) to
   `g := fun x => finrank ℝ (V i x)` with steps 2–3; get `m i`. Combine the finitely many `i`
   with `ae_all_iff`. ~30 lines.
5. **Profile structure** at a single good point (in the intersection of the block and the
   constancy sets): `StrictAnti m` from conjunct 3 + `Submodule.finrank_lt_finrank_of_lt`
   (Mathlib `LinearAlgebra/FiniteDimensional/Lemmas.lean:235`); `m 0 = d` from `V 0 x = ⊤`,
   `finrank_top`, `finrank_euclideanSpace_fin`; `m (last) = 0` from `finrank_bot`. ~30 lines.
6. **C1' from C1**: `m' i := m i.castSucc - m i.succ` (ℕ-subtraction safe by strict
   antitonicity); positivity from `StrictAnti`; `Σ m' = m 0 - m last = d` by `Fin` telescoping
   (`Finset.sum_range_succ_comm`-style induction; ~30 lines, `omega`-heavy).

Total: ~200–260 lines. EXISTING repo lemmas consumed: none beyond the `MeasurableSubspace`
definition (`ErgodicTheory/Lyapunov/MeasurableSubspace.lean:34`) and `orthProjMatrix` (`:26`).

### 4.4 Names and placement

* `ErgodicTheory.trace_orthProjMatrix` → `ErgodicTheory/Lyapunov/MeasurableSubspace.lean`
* `ErgodicTheory.MeasurableSubspace.measurable_finrank` → ibid.
* `ErgodicTheory.IsOseledetsFiltration.exists_finrank_ae_eq`,
  `ErgodicTheory.IsOseledetsFiltration.exists_multiplicity`,
  `ErgodicTheory.oseledets_filtration_with_multiplicities` → `ErgodicTheory/Corollaries.lean`,
  section `Multiplicities`.

---

## 5. Construction-side notes (recorded, NOT recommended for implementation)

### 5.1 Confirmation of the "deterministic band rank" premise

Chain (all committed): main witness = `V'` (`SlowFlagBridge.lean:78`) → interior level =
`Vslow A T (exp (slowCutoff lam0 d i)) x` with `slowCutoff = expEnum lam0 d ⟨i,_⟩`
(`SlowFlagBridge.lean:72`) → `Vslow t x = range (toEuclideanCLM (slowProjector t x))`
(`ForwardV.lean:174`) → `slowProjector = cfc (indicator (Iic t)) (lambdaHat …)`
(`ForwardV.lean:138`), a genuine orthogonal projector everywhere
(`slowProjector_isSelfAdjoint`/`slowProjector_mul_self`, `ForwardV.lean:144,152`). A.e. the
spectrum of `lambdaHat` is `{exp (lamSing x j)}` (`spectrum_lambdaHat_eq_ae`,
`SpectrumResiduals.lean:34`) and `lamSing x j = lam0 j` (`ae_lamSing_eq_lam0`,
`SpectrumResiduals.lean:304`), so the rank is the deterministic count
`#{j | lam0 j ≤ expEnum lam0 d i}`. The rank computation itself would be a verbatim adaptation
of `bandProjector_rank` (`OseledetsLimit.lean:811`) — its body already works for any Hermitian
matrix through `cfc_eq_eigenvectorUnitary_conj` (`OseledetsLimit.lean:799`).

### 5.2 Why we still do not take this route

The explicit value of `m` in terms of `lam0` cannot even be *stated* in the headline theorem
(the existential hides `lam0`), and threading `∃ m, …` through five committed statements is
strictly more invasive than §4. If a future consumer needs the explicit deterministic formula
(e.g. for the two-sided MET), implement `slowProjector_rank` + the finrank bridge then, as a
~100-line addition to `SpectrumResiduals.lean`, and *equate* it with the C1 multiplicities via
C2b uniqueness.

---

## 6. SURPRISES (flagged)

1. **Uniqueness is free.** C2a/C2b need *zero* repo machinery — the canonical growth-sublevel
   characterization and full uniqueness of `(k, lam, V)` are pointwise consequences of the
   theorem's own a.e. block (decreasing flag + exact per-stratum limits). The deep slow-flag
   identification (`hslowflag`, L11) that the *construction* sweated over is logically
   downstream of the *statement* once a witness exists.
2. **C3 needs neither Furstenberg–Kesten nor singular values.** The operator-norm growth rate
   converges to `lam 0` by a two-sided squeeze from the flag block alone (top-stratum vector
   from below; the **column-sum bound** `‖M‖ ≤ Σⱼ ‖M eⱼ‖` from above — proved in probe). The
   expected glue `σ_max = ‖·‖` and `exists_lam_tendsto_singularValue` at `i = 0` is never
   needed; instead C3 *yields* "FK constant = top Oseledets exponent" as a 5-line corollary.
3. **C1 is the only corollary where ergodicity is load-bearing**, and the
   `MeasurableSubspace` conjunct of the main theorem — which looked like a mere artifact of
   the measurable-selection infrastructure — is exactly what makes `x ↦ finrank (V i x)`
   measurable (via the trace of the orthoprojector, `LinearMap.IsProj.trace`). Hypothesis-drop
   check: dropping `Ergodic` to `MeasurePreserving` breaks C1 (dimensions can differ across
   invariant components) but leaves C2a/C2b/C3-as-stated intact except that C3's `lam ⟨0,hk⟩`
   and C2b's exponent identification still hold per the *given* witnesses (they quantify over
   witnesses of the same a.e. block, whose existence is what fails without ergodicity).
4. **The pinned Mathlib deprecation**: `Matrix.toEuclideanLin_eq_toLin` →
   `Matrix.toLpLin_eq_toLin` (different signature, `p q : ENNReal` arguments). Use the new
   name in step 4.3.1.
5. `Fin.cast (by omega) i` inside an `∃ hk : k = k₂, …` statement elaborates without tricks —
   no need for `Eq.mpr`-style index gymnastics in C2b's statement.

## 7. Honest effort assessment

All three corollaries are genuinely **cheap by this repo's standards** (for calibration: the
final assembly file alone is 175 lines; `OseledetsLimit.lean` is ~3500). None requires new
analytic content; total estimated ~650–900 lines including all helpers, the predicate, and the
repackaged existence theorems. The only step with real fiddle-risk is C2b's
enumeration-uniqueness Fin lemma (§2.4.2) — pure bookkeeping, but the repo's history shows
`Fin.cast`/`orderEmbOfFin` work routinely takes 2–3 attempts. C1 looked the most expensive on
paper (rank measurability was the open question) but all three of its glue steps are now
probe-verified, leaving only assembly. If exactly one corollary must be cut for budget, cut
C2b (C2a already delivers the canonical characterization; uniqueness is its Fin-bureaucratic
closure).

## 8. Probe inventory (compiled against current build, 2026-06-11)

| File | Contents | Status |
|---|---|---|
| `/tmp/probe_companion.lean` | `IsOseledetsFiltration`, `oseledets_filtration'` (proved), C1/C1'/C2a/C2b/C3/k_pos skeletons | ✓ typechecks, 6 sorries (the 6 corollary bodies) |
| `/tmp/probe_glue.lean` | C1 trace bridge (mod round-trip) | ✓ |
| `/tmp/probe_glue2.lean` | round-trip `toMatrix ∘ toEuclideanCLM = id`; C3 column-sum bound | ✓ sorry-free |
| `/tmp/probe_ergconst.lean` | ℕ-valued ergodic constancy; `finrank` measurability from `MeasurableSubspace` | ✓ sorry-free |
