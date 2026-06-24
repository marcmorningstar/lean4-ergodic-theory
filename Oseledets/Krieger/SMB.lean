/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.NameCount
import Oseledets.Krieger.InfoFunction
import Oseledets.Ergodic.Birkhoff
import Oseledets.Entropy.CondEntropyContinuous

/-!
# The Shannon–McMillan–Breiman theorem (entropy equipartition)

This file builds towards the **pointwise Shannon–McMillan–Breiman (SMB) theorem** — the
entropy-equipartition property that underlies Krieger's finite-generator theorem (issue #15).
For a measure-preserving `T` on a probability space `(α, μ)` and a finite measurable partition `P`,
the information functions `iₙ(x) = -log μ(atomₙ(x))` (built in `Oseledets.Krieger.InfoFunction`)
satisfy
`(1/n)·iₙ(x) → h(P,T) = ksEntropyPartition`  for `μ`-a.e. `x`.

## What is proved here (sorry-free)

* `Oseledets.Krieger.ae_limsup_div_infoFun_le_log_card` — the **crude name-count upper bound**:
  `limsup (1/n)·iₙ(x) ≤ log (card ι)` a.e.  This is the Algoet–Cover engine
  (`ae_forall_eventually_div_infoFun_le`) fed the *uniform* competing measure
  `qₙ ≡ (card ι)⁻ⁿ`, whose partition-function bound `∫⁻ exp(iₙ − n·log N) ≤ 1`
  (`lintegral_exp_infoFun_sub_log_card_le_one`) is the Markov–Borel–Cantelli core.  No ergodic
  theorem, no martingale.

The crude bound is the honest Birkhoff-free part of the SMB upper half.  Sharpening the rate from
`log (card ι)` to the Kolmogorov–Sinai entropy `h(P,T)` — and proving the matching lower bound —
requires the conditional-information martingale and the Birkhoff ergodic theorem; that is the
content of the blueprint below.

## Blueprint for the sharp theorem (the Breiman/ELW route)

The cleanest route (Einsiedler–Lindenstrauss–Ward, *Entropy in Ergodic Theory*, Ch. 2; Bruin,
*Ergodic Theory I*, Lecture 15; Breiman 1957/Chung 1961) is a single telescoping identity rather
than a two-sided sandwich.  Write the **conditional information function**
`I_{P|𝒜}(x) = -log (μ⟦P(x) | 𝒜⟧)(x)` and `gₖ(x) = I_{P | ⋁_{j=1}^{k-1} T⁻ʲP}(x)` (with `g₁ = I_P`).
The chain rule `I_{P∨Q} = I_Q + I_{P|Q}` telescopes to the **exact** identity

> `iₙ(x) = ∑_{j=0}^{n-1} g_{n-j}(Tʲ x)`.     [Bruin Lec. 15; ELW Ch. 2]

Let `g = lim_k gₖ` (a.e. and in `L¹`, by Lévy downward martingale convergence).  Then
`(1/n)·iₙ(x) = (1/n)∑_{j<n} g(Tʲx) + (1/n)∑_{j<n} (g_{n-j} − g)(Tʲx)`.
* The first term `→ ∫ g dμ = H(P | ⋁_{j≥1} T⁻ʲP) = h(P,T)` by **Birkhoff** (repo:
  `tendsto_birkhoffAverage_ae_integral`) and the conditional-entropy formula for `h`.
* The second (Cesàro tail) `→ 0` via the **Chung domination** `g* := supₙ gₙ ∈ L¹`, a maximal
  dominator `G_N = sup_{k≥N}|gₖ − g| → 0`, and dominated convergence + the ergodic theorem.

The convergence `gₖ → g` together with `∫ gₖ = H(P | ⋁₁^{k-1} T⁻ʲP) → h` is exactly the repo's
`condEntropy_tendsto_iSup` (the fixed-partition Lévy theorem) once `I_{P|𝒜}` is in place.

### Dependency-ordered residual sub-lemmas (NOT proved here)

The single genuinely missing piece of *infrastructure* is the pointwise conditional information
function `I_{P|𝒜}` and its chain rule / telescoping identity; everything else is assembled from
existing repo results.  See the module note at the bottom of this file for the precise Lean
signatures and the honest assessment of the hardest residual (Chung's `L¹` domination).

## References

* P. Algoet, T. Cover, *A sandwich proof of the Shannon–McMillan–Breiman theorem*,
  Ann. Probab. **16** (1988), 899–909.
* M. Einsiedler, E. Lindenstrauss, T. Ward, *Entropy in Ergodic Theory and Topological Dynamics*,
  Ch. 2 (SMB).
* H. Bruin, *Ergodic Theory I* (Univ. Wien), Lecture 15 (the telescoping/Breiman proof).
* L. Breiman, *The individual ergodic theorem of information theory*, Ann. Math. Statist.
  **28** (1957), 809–811; correction **31** (1960), 809–810.
* K. L. Chung, *A note on the ergodic theorem of information theory*, Ann. Math. Statist.
  **32** (1961), 612–614.  (The `L¹` maximal domination.)
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace Oseledets.Krieger

open Oseledets.Entropy

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [Fintype ι]
  {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

section CrudeUpperBound

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)

/-- **The uniform partition-function bound.** Feeding the Algoet–Cover engine the *uniform*
competing measure `qₙ ≡ (card ι)⁻ⁿ` amounts to checking
`∫⁻ x, ofReal (exp (iₙ x − n·log N)) ∂μ ≤ 1`, where `N = card ι`.

The integrand is constant on each itinerary fiber `Fₘ = {itinerary = g}`
(`infoFun_eq_sum_indicator`): there `iₙ = -log μ(cell g)`, so the value is
`(μ cell g)⁻¹ · N⁻ⁿ`, and `μ(Fₘ) = μ(cell g)` (`measure_itinerary_fiber`).  Hence the integral is
`∑_g [μ(cell g) > 0] · N⁻ⁿ ≤ Nⁿ · N⁻ⁿ = 1` because the join has at most `Nⁿ` non-null cells. -/
theorem lintegral_exp_infoFun_sub_log_card_le_one [Nonempty ι] :
    ∫⁻ x, ENNReal.ofReal (Real.exp (infoFun hT P n x - n * Real.log (Fintype.card ι))) ∂μ ≤ 1 := by
  classical
  -- **Per-fiber bound.** On the fiber `Fₘ = {itinerary = g}` the integrand is the constant
  -- `ofReal (exp (infoWeight g − n·log N))`; multiplied by `μ(Fₘ) = μ(cell g)` it is `≤ N⁻ⁿ`.
  have perfiber : ∀ g : Fin n → ι,
      ENNReal.ofReal (Real.exp (infoWeight hT P n g - n * Real.log (Fintype.card ι)))
          * μ {x | itinerary hT P n x = g}
        ≤ ENNReal.ofReal (Real.exp (-(n * Real.log (Fintype.card ι)))) := by
    intro g
    rw [measure_itinerary_fiber]
    set p : ℝ := (μ ((ksJoin hT P n).cells g)).toReal with hp
    have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hp0 with hpz | hppos
    · -- `μ(cell g) = 0`: the second factor vanishes.
      have hmz : μ ((ksJoin hT P n).cells g) = 0 := by
        have ht0 : (μ ((ksJoin hT P n).cells g)).toReal = 0 := by rw [← hp, ← hpz]
        rcases (ENNReal.toReal_eq_zero_iff _).mp ht0 with h | h
        · exact h
        · exact absurd h (measure_ne_top μ _)
      rw [hmz, mul_zero]; positivity
    · -- `μ(cell g) > 0`: `exp (infoWeight g) = p⁻¹`, so the product collapses to `exp(−n·log N)`.
      have hexp : Real.exp (infoWeight hT P n g) = p⁻¹ := by
        rw [infoWeight, ← hp, Real.exp_neg, Real.exp_log hppos]
      have hmu : μ ((ksJoin hT P n).cells g) = ENNReal.ofReal p := by
        rw [hp, ENNReal.ofReal_toReal]; exact measure_ne_top μ _
      rw [show infoWeight hT P n g - n * Real.log (Fintype.card ι)
            = infoWeight hT P n g + (-(n * Real.log (Fintype.card ι))) by ring,
        Real.exp_add, hexp, hmu, ← ENNReal.ofReal_mul (by positivity)]
      apply le_of_eq
      congr 1
      rw [mul_right_comm, inv_mul_cancel₀ (ne_of_gt hppos), one_mul]
  -- **Integrand as a fiber-indexed sum of constant indicators** (one summand survives per `x`).
  have hint_eq : (fun x => ENNReal.ofReal
        (Real.exp (infoFun hT P n x - n * Real.log (Fintype.card ι))))
      = fun x => ∑ g : Fin n → ι, Set.indicator {x | itinerary hT P n x = g}
          (fun _ => ENNReal.ofReal
            (Real.exp (infoWeight hT P n g - n * Real.log (Fintype.card ι)))) x := by
    funext x
    rw [Finset.sum_eq_single (itinerary hT P n x)]
    · rw [Set.indicator_of_mem (by rw [Set.mem_setOf_eq]), infoFun_eq_infoWeight_itinerary]
    · intro g _ hg
      exact Set.indicator_of_notMem (by rw [Set.mem_setOf_eq]; exact fun h => hg h.symm) _
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hint_eq, lintegral_finsetSum _
    (fun g _ => (measurable_const).indicator (measurableSet_itinerary_eq hT P n g))]
  -- **Sum the per-fiber bounds**, then `Nⁿ · N⁻ⁿ = 1`.
  have hbd : ∀ g : Fin n → ι, (∫⁻ a, Set.indicator {x | itinerary hT P n x = g}
        (fun _ => ENNReal.ofReal
          (Real.exp (infoWeight hT P n g - n * Real.log (Fintype.card ι)))) a ∂μ)
        ≤ ENNReal.ofReal (Real.exp (-(n * Real.log (Fintype.card ι)))) := by
    intro g
    rw [lintegral_indicator (measurableSet_itinerary_eq hT P n g), setLIntegral_const]
    exact perfiber g
  refine le_trans (Finset.sum_le_sum (fun g _ => hbd g)) ?_
  · rw [Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card (Fin n → ι) = (Fintype.card ι) ^ n := by simp
    have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [hcard, nsmul_eq_mul]
    have hexp : Real.exp (-(n * Real.log (Fintype.card ι))) = ((Fintype.card ι : ℝ) ^ n)⁻¹ := by
      rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
    rw [hexp, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hNpos.le,
      ENNReal.ofReal_natCast, Nat.cast_pow]
    apply le_of_eq
    refine ENNReal.mul_inv_cancel ?_ ?_
    · exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fintype.card_pos).ne')
    · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)

/-- **Crude name-count upper bound (Algoet–Cover engine, uniform competing measure).**
For `μ`-almost every `x`, `limsup_{n} (1/n)·iₙ(x) ≤ log (card ι)`.

This is the Markov–Borel–Cantelli core of the SMB upper half: instantiate the abstract engine
`ae_forall_eventually_div_infoFun_le` at the partition's information functions and rate
`R = log (card ι)`, with the uniform partition-function bound
`lintegral_exp_infoFun_sub_log_card_le_one`.  It is *Birkhoff-free*; sharpening
`log (card ι) ⤳ h(P,T)` is the blueprint above. -/
theorem ae_limsup_div_infoFun_le_log_card [Nonempty ι] :
    ∀ᵐ x ∂μ, Filter.limsup (fun n : ℕ => (1 / (n : ℝ)) * infoFun hT P n x) atTop
      ≤ Real.log (Fintype.card ι) := by
  -- The engine, at rate `R = log (card ι)`, in the `eventually` form.
  have hengine := ae_forall_eventually_div_infoFun_le
    (f := fun n => infoFun hT P n) (μ := μ)
    (fun n => measurable_infoFun hT P n)
    (R := Real.log (Fintype.card ι))
    (fun n => lintegral_exp_infoFun_sub_log_card_le_one hT P n)
  filter_upwards [hengine] with x hx
  -- Bounded below by `0` (`infoFun_nonneg`), eventually `≤ R + ε` for every `ε`; so `limsup ≤ R`.
  have hlb : ∀ n : ℕ, (0 : ℝ) ≤ (1 / (n : ℝ)) * infoFun hT P n x := fun n => by
    have := infoFun_nonneg hT P n x; positivity
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hbd : IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (1 / (n : ℝ)) * infoFun hT P n x) :=
    ⟨0, by rw [eventually_map]; exact Eventually.of_forall hlb⟩
  exact Filter.limsup_le_of_le hbd.isCoboundedUnder_le
    (by filter_upwards [hx ε hε] with n hn; linarith)

end CrudeUpperBound

/-! ### Blueprint residuals — precise Lean signatures for the sharp theorem

The sharp SMB theorem is reduced to the following sub-lemmas, in dependency order.  None is proved
here; each is stated as the exact signature a follow-up should fill, with the cleanest known route.
The hardest is `R5` (Chung's `L¹` domination); the rest are mechanical given the repo infra.

`R1` (conditional information function).  Define, for a sub-σ-algebra `𝒜 ≤ mα`,
`condInfoFun 𝒜 P x := -Real.log ((condExpKernel μ 𝒜 x) (P.cells (P-index of x))).toReal`
(equivalently `-log (μ⟦P(x) | 𝒜⟧ x)`).  Prove measurability and
`∫ condInfoFun 𝒜 P = condEntropy μ 𝒜 P.cells` (mirrors `integral_infoFun_eq`).

`R2` (chain rule / telescoping).  `infoFun hT P n x = ∑ j in Finset.range n,
  condInfoFun (σ of the (n-1-j)-step *future* join) P (T^[j] x)` — the Bruin/ELW identity
`iₙ(x) = ∑_{j<n} g_{n-j}(Tʲx)`.  Pure measure algebra from `I_{P∨Q} = I_Q + I_{P|Q}`.

`R3` (Lévy limit).  `gₖ := condInfoFun (⋁_{1}^{k-1} T⁻ʲP) P → g` a.e. and in `L¹`, where
`g := condInfoFun (⋁_{j≥1} T⁻ʲP) P`.  This is `MeasureTheory.tendsto_ae_condExp` composed with
`-log`, plus `condEntropy_tendsto_iSup` for the `L¹`/integral statement.

`R4` (Birkhoff term).  `(1/n)∑_{j<n} g(Tʲx) → ∫ g dμ = H(P | ⋁_{j≥1}T⁻ʲP) = h(P,T)` a.e., from
`tendsto_birkhoffAverage_ae_integral` and the KS conditional-entropy formula
`ksEntropyPartition hT P = condEntropy μ (⋁_{j≥1} comap (T^[j]) σP) P.cells`
(itself `condEntropy_tendsto_iSup` + the chain-rule telescoping of `ksEntropySeq`).

`R5` (Chung domination — HARDEST).  `g* := ⨆ₙ gₙ ∈ L¹(μ)`, hence by dominated convergence the
Cesàro tail `(1/n)∑_{j<n}(g_{n-j} − g)(Tʲx) → 0` a.e.  This is the one genuinely analytic gap:
Mathlib has Doob's maximal inequality (`maximal_ineq`) but NOT the `L log L`/`L¹` integrability of
the conditional-information maximal function for a finite partition (Chung 1961).  Best route:
the explicit Chung estimate `μ{g* > λ} ≤ (something)·e^{-λ}` per cell, giving
`∫ g* ≤ H(P) + (card ι)/e` or similar; this needs a fresh `≈150-line` development.

`SMB` (assembly).  `∀ᵐ x, Tendsto (fun n => iₙ x / n) atTop (𝓝 (ksEntropyPartition hT P))`,
by `R2 ▸ R3 ▸ R4 ▸ R5` and a Cesàro/squeeze.

### Why this is far more tractable here than general SMB (key infrastructure finding)

In the Breiman route the conditioning σ-algebra is *always* `σ(ksJoin hT P k)` — a **partition**
σ-algebra, never a general sub-σ-algebra (except in the single `k → ∞` Lévy limit).  For a partition
σ-algebra the repo already has an **explicit, computable** representative of the conditional
expectation: `Oseledets.Entropy.condCandidate B tⱼ` (`CondGivenPartitionBridge.lean`) is the
piecewise-constant function `ω ↦ μ(Bᵢ ∩ tⱼ)/μ(Bᵢ)` on cell `Bᵢ ∋ ω`, with
`condCandidate_ae_eq_condExp` proving it is `μ⟦tⱼ | σ(B)⟧`.  Consequently:

* `R1` `condInfoFun (σ(ksJoin Q k)) P` is just `-log` of the finite indicator sum `condCandidate` —
  measurable on the nose, no general `condExp` machinery; `∫ = condEntropy` is
  `condEntropyGivenPartition_eq_condEntropy_generated` (already proved).
* `R2` the chain-rule telescoping uses `entropy_join_eq_add_condEntropyGivenPartition` /
  `condEntropy_join_eq` (already proved, `CondChainRule.lean`) lifted to the pointwise information
  functions — finite measure algebra on the explicit `condCandidate`.
* `R4` the KS conditional-entropy identity is essentially `tendsto_condEntropy_genJoin_div`
  (`CondKSMovingLimit.lean`, proved), which already shows
  `H(A_n | σ(B_n))/n → condKsEntropyPartition`; with `Q = P` and the saturation
  `⨆ₙ σ(ksJoin P n) = mα` (a generator hypothesis) this *is*
  `ksEntropyPartition hT P = condEntropy μ (⋁_{j≥1}…) P.cells`.

So the *only* genuinely missing analysis is `R5` (Chung's `L¹` domination of the conditional-
information maximal function) plus the mechanical pointwise telescoping bookkeeping — a sharply
delimited gap, NOT a from-scratch SMB.

### Ergodicity (precise hypothesis for the constant limit)

The a.e. limit `= h = ksEntropyPartition` (a *constant*) requires `Ergodic T μ`; the crude bound
above (`ae_limsup_div_infoFun_le_log_card`) needs *neither* ergodicity *nor* Birkhoff.  Without
ergodicity the Birkhoff term `R4` converges to the invariant conditional expectation
`(μ[g | invariants T])` (the *relative* entropy rate), giving Algoet–Cover's non-ergodic
Theorem 3 form `∀ᵐ x, iₙ x / n → (μ[g | invariants T]) x`. -/

end Oseledets.Krieger
