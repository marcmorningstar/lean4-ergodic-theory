/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Oseledets.Entropy.KSEntropy

/-!
# The martingale-free Markov–Borel–Cantelli engine for the SMB upper bound

This file develops the **Algoet–Cover "Lemma 1"** — the elementary, *martingale-free* core of the
upper half of the Shannon–McMillan–Breiman (SMB) theorem that Krieger's finite-generator theorem
needs.  It is the one-line consequence of **Markov's inequality** and the **Borel–Cantelli lemma**:

> If `gₙ ≥ 0` are random variables with `∫ gₙ ≤ 1` for all `n`, then
> `limsup_{n→∞} (1/n) · log gₙ ≤ 0` almost everywhere.

This is exactly Lemma 1 of Algoet–Cover (1988); see the references.  The whole point of the
sandwich proof is that the *upper bound* on the information function reduces to applying this
engine to a likelihood ratio `gₙ = qₙ / pₙ` of an approximating sub-probability `qₙ` against the
true atom measure `pₙ = μ(atomₙ)`, because such a ratio automatically integrates to `≤ 1`.

## Main definitions / results

* `Oseledets.Krieger.ae_forall_eventually_div_log_le` — **the engine (always-true form).** For a
  sequence `g : ℕ → α → ℝ≥0∞` of a.e.-measurable functions with `∫⁻ gₙ ∂μ ≤ 1`, almost every `x`
  satisfies: for every `ε > 0`, *eventually* `(1/n) · log (gₙ x).toReal ≤ ε`.  Pure Markov +
  Borel–Cantelli, *no* ergodic theorem and *no* martingale convergence.

* `Oseledets.Krieger.ae_limsup_div_log_toReal_le_zero` — the `limsup` repackaging, under the extra
  hypothesis `1 ≤ gₙ x` (which makes the sequence bounded below, so its `limsup` is not a junk
  value): `limsup_n (1/n) · log (gₙ x).toReal ≤ 0` a.e.

* `Oseledets.Krieger.ae_forall_eventually_div_infoFun_le` — the **information-function name-count
  bound** at an abstract rate `R`: given measurable `f : ℕ → α → ℝ` (the information functions) and
  the partition-function bound `∫⁻ exp(fₙ − n·R) ∂μ ≤ 1`, almost every `x` satisfies, for every
  `ε > 0`, eventually `(1/n) · fₙ x ≤ R + ε`.  Instantiating `R = log #cells` gives the crude
  Birkhoff-free name-count bound `limsup (1/n)·infoFunₙ ≤ log #cells`.

The conversion of the rate to the Kolmogorov–Sinai entropy `h(P,T)` is the *second* half of the
sandwich and requires the **Birkhoff ergodic theorem** to evaluate the per-symbol codelength of the
approximating measure as a time average — see the module note below.  That half is intentionally
NOT in this file.

## Note on the rate (why this file stops at the engine)

The pure Markov+Borel–Cantelli engine, applied to the *uniform* approximation
`qₙ ≡ 1/#atoms`, gives only the crude bound `limsup (1/n) infoFunₙ ≤ log(card ι)` a.e.
To reach the sharp rate `h(P,T) = ksEntropyPartition`, Algoet–Cover feed the engine a *non-uniform*
likelihood ratio and then invoke the ergodic theorem (their eq. (33)); for the finite-partition
(Krieger) case the `m`-block approximation closes the gap to `h` via `ksEntropySeq m / m → h`
WITHOUT martingales.  This file proves the engine and the uniform corollary; the Birkhoff step is
left to a companion file.

## References

* P. H. Algoet and T. M. Cover, *A sandwich proof of the Shannon–McMillan–Breiman theorem*,
  Ann. Probab. **16** (1988), 899–909.  (Lemma 1 is `ae_limsup_div_log_toReal_le_zero`.)
* M. Einsiedler, T. Ward, *Ergodic Theory with a view towards Number Theory*, Ch. 2.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace Oseledets.Krieger

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Markov rearrangement.** From `c * μ A ≤ 1` with `0 < c < ∞`, deduce `μ A ≤ c⁻¹`. -/
private lemma meas_le_inv_of_mul_le_one {A : Set α} {c : ℝ≥0∞}
    (hc : 0 < c) (hctop : c ≠ ⊤) (hmark : c * μ A ≤ 1) : μ A ≤ c⁻¹ := by
  have h : c⁻¹ * (c * μ A) ≤ c⁻¹ * 1 := by gcongr
  rwa [← mul_assoc, ENNReal.inv_mul_cancel hc.ne' hctop, one_mul, mul_one] at h

/-- **Log–scaling glue.** If `0 ≤ v` and `v < exp (n·ε)` with `1 ≤ n` and `0 < ε`, then
`(1/n) · log v ≤ ε`.  The boundary `v = 0` is handled by `log 0 = 0 ≤ ε`. -/
private lemma div_log_le_of_lt_exp {v : ℝ} {n : ℕ} {ε : ℝ}
    (hv0 : 0 ≤ v) (hn : 1 ≤ n) (hε : 0 < ε) (hv : v < Real.exp (n * ε)) :
    (1 / (n : ℝ)) * Real.log v ≤ ε := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le hv0 with hv0' | hv0'
  · rw [← hv0', Real.log_zero, mul_zero]; exact hε.le
  · have hlog : Real.log v < n * ε := by
      have := Real.log_lt_log hv0' hv
      rwa [Real.log_exp] at this
    rw [one_div, inv_mul_le_iff₀ hnpos]; linarith

/-- **`toReal` from a strict `ofReal` bound.** If `g < ofReal t` with `0 < t` then
`g.toReal < t`. -/
private lemma toReal_lt_of_lt_ofReal {g : ℝ≥0∞} {t : ℝ} (ht : 0 < t)
    (h : g < ENNReal.ofReal t) : g.toReal < t := by
  have hne : g ≠ ⊤ := h.ne_top
  rw [← ENNReal.ofReal_toReal hne] at h
  exact (ENNReal.ofReal_lt_ofReal_iff ht).mp h

/-- **Geometric summability in `ℝ≥0∞`.** For `r < 1`, `∑' n, r ^ n ≠ ⊤`. -/
private lemma tsum_geometric_ne_top {r : ℝ≥0∞} (hr : r < 1) : ∑' n : ℕ, r ^ n ≠ ⊤ := by
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hr).ne'

/-- **`limsup ≤ b` from an eventual upper bound, for a sequence bounded below.** If `a` is
bounded below (which yields the coboundedness `limsup_le_of_le` needs) and eventually `≤ b`,
then `limsup a ≤ b`.

The boundedness-below hypothesis is genuinely required: in the conditionally-complete order `ℝ`,
the `limsup` of a sequence unbounded below (e.g. `a n = -n`) is a junk value, so
`limsup a ≤ b` can *fail* without it.  In the Shannon–McMillan–Breiman application the relevant
sequence is `(1/n) · infoFunₙ ≥ 0`, so boundedness below is free. -/
private lemma limsup_le_of_eventually_le {a : ℕ → ℝ} {b c : ℝ}
    (hlb : ∀ n, c ≤ a n) (h : ∀ᶠ n in atTop, a n ≤ b) : Filter.limsup a atTop ≤ b := by
  have hbd : IsBoundedUnder (· ≥ ·) atTop a := by
    refine ⟨c, ?_⟩
    rw [eventually_map]
    exact Eventually.of_forall hlb
  exact Filter.limsup_le_of_le hbd.isCoboundedUnder_le h

/-- **The Algoet–Cover engine (Lemma 1), single-`ε` step.**

For a sequence `g : ℕ → α → ℝ≥0∞` of a.e.-measurable functions with `∫⁻ gₙ ≤ 1` and a fixed
`ε > 0`, the set `Aₙ = {x | ofReal (exp (n·ε)) ≤ gₙ x}` has measure `≤ ofReal (exp (-(n·ε)))`
by Markov, these are summable (geometric), so by Borel–Cantelli almost every `x` is eventually
outside every `Aₙ`; there `(gₙ x).toReal < exp (n·ε)`, hence `(1/n)·log (gₙ x).toReal ≤ ε`. -/
private theorem ae_eventually_div_log_le {g : ℕ → α → ℝ≥0∞} (hg : ∀ n, AEMeasurable (g n) μ)
    (hint : ∀ n, ∫⁻ x, g n x ∂μ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, (1 / (n : ℝ)) * Real.log (g n x).toReal ≤ ε := by
  -- The bad sets.
  set A : ℕ → Set α := fun n => {x | ENNReal.ofReal (Real.exp ((n : ℝ) * ε)) ≤ g n x} with hA
  -- Measure bound via Markov.
  have hμA : ∀ n, μ (A n) ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * ε))) := by
    intro n
    set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((n : ℝ) * ε)) with hc
    have hcpos : 0 < c := by rw [hc, ENNReal.ofReal_pos]; exact Real.exp_pos _
    have hcne : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hAeq : A n = {x | c ≤ g n x} := by rw [hA, hc]
    have hmark : c * μ (A n) ≤ ∫⁻ x, g n x ∂μ := by
      rw [hAeq]; exact mul_meas_ge_le_lintegral₀ (hg n) c
    have hmark1 : c * μ (A n) ≤ 1 := le_trans hmark (hint n)
    have hinv : μ (A n) ≤ c⁻¹ := meas_le_inv_of_mul_le_one hcpos hcne hmark1
    refine hinv.trans (le_of_eq ?_)
    rw [hc, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
  -- Summability of the measures (geometric).
  have hsumm : ∑' n, μ (A n) ≠ ⊤ := by
    have hr1 : ENNReal.ofReal (Real.exp (-ε)) < 1 := by
      rw [ENNReal.ofReal_lt_one]; rw [Real.exp_lt_one_iff]; linarith
    have hcomp : ∀ n, μ (A n) ≤ ENNReal.ofReal (Real.exp (-ε)) ^ n := by
      intro n
      refine (hμA n).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    refine ne_top_of_le_ne_top (tsum_geometric_ne_top hr1) ?_
    exact ENNReal.tsum_le_tsum hcomp
  -- Borel–Cantelli: a.e. eventually outside `A n`.
  filter_upwards [ae_eventually_notMem hsumm] with x hx
  filter_upwards [hx, eventually_ge_atTop 1] with n hxn (hn : 1 ≤ n)
  -- `x ∉ A n` means `g n x < ofReal (exp (n ε))`.
  have hlt : g n x < ENNReal.ofReal (Real.exp ((n : ℝ) * ε)) := by
    have : x ∉ A n := hxn
    rw [hA] at this
    simp only [Set.mem_setOf_eq, not_le] at this
    exact this
  have hvlt : (g n x).toReal < Real.exp ((n : ℝ) * ε) :=
    toReal_lt_of_lt_ofReal (Real.exp_pos _) hlt
  exact div_log_le_of_lt_exp ENNReal.toReal_nonneg hn hε hvlt

/-- **Algoet–Cover Lemma 1, the always-true `eventually` form (the martingale-free engine).**

If `g : ℕ → α → ℝ≥0∞` are a.e.-measurable with `∫⁻ gₙ ∂μ ≤ 1` for all `n`, then for `μ`-almost
every `x` and every `ε > 0`, *eventually* `(1/n) · log (gₙ x).toReal ≤ ε`.

This is the *entire* probabilistic content of the SMB upper bound — Markov's inequality on the
nonnegative `gₙ` plus the Borel–Cantelli lemma, with the threshold ranging over `ε = 1/(k+1)`.
No ergodic theorem, no martingale convergence.  It is stated in the `eventually` form (rather than
as a `limsup` bound) because it is unconditionally true; the `limsup` repackaging
`ae_limsup_div_log_toReal_le_zero` additionally needs the sequence to be bounded below. -/
theorem ae_forall_eventually_div_log_le {g : ℕ → α → ℝ≥0∞} (hg : ∀ n, AEMeasurable (g n) μ)
    (hint : ∀ n, ∫⁻ x, g n x ∂μ ≤ 1) :
    ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (1 / (n : ℝ)) * Real.log (g n x).toReal ≤ ε := by
  -- Intersect the a.e. statements over `ε = 1/(k+1)`.
  have hcount : ∀ k : ℕ, ∀ᵐ x ∂μ,
      ∀ᶠ n : ℕ in atTop, (1 / (n : ℝ)) * Real.log (g n x).toReal ≤ (1 / (k + 1 : ℝ)) := by
    intro k
    have hε : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    exact ae_eventually_div_log_le hg hint hε
  rw [← ae_all_iff] at hcount
  filter_upwards [hcount] with x hx
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hx k] with n hn
  exact hn.trans hk.le

/-- **Algoet–Cover Lemma 1, the `limsup` form.**

If `g : ℕ → α → ℝ≥0∞` are a.e.-measurable with `∫⁻ gₙ ∂μ ≤ 1` and, pointwise, `1 ≤ gₙ x`
(so that `log (gₙ x).toReal ≥ 0` and the sequence `(1/n)·log (gₙ x).toReal` is bounded below by
`0`), then for `μ`-almost every `x`,
`limsup_{n→∞} (1/n) · log (gₙ x).toReal ≤ 0`.

The lower bound `1 ≤ gₙ x` is exactly what holds in the Shannon–McMillan–Breiman application,
where `gₙ x = (μ atomₙ)⁻¹ ≥ 1` since atoms have measure `≤ 1`; it is genuinely needed because the
`limsup` of an `ℝ`-sequence unbounded below is a junk value. -/
theorem ae_limsup_div_log_toReal_le_zero {g : ℕ → α → ℝ≥0∞} (hg : ∀ n, AEMeasurable (g n) μ)
    (hint : ∀ n, ∫⁻ x, g n x ∂μ ≤ 1) (hge : ∀ n x, 1 ≤ g n x) :
    ∀ᵐ x ∂μ,
      Filter.limsup (fun n : ℕ => (1 / (n : ℝ)) * Real.log (g n x).toReal) atTop ≤ 0 := by
  filter_upwards [ae_forall_eventually_div_log_le hg hint] with x hx
  -- The sequence is bounded below by `0`: `g n x ≥ 1 ⇒ (g n x).toReal ≥ 1 ⇒ log ≥ 0`.
  have hlb : ∀ n : ℕ, (0 : ℝ) ≤ (1 / (n : ℝ)) * Real.log (g n x).toReal := by
    intro n
    have hlog : 0 ≤ Real.log (g n x).toReal := by
      rcases eq_or_ne (g n x) ⊤ with htop | htop
      · simp [htop]
      · refine Real.log_nonneg ?_
        have := ENNReal.toReal_mono htop (hge n x)
        simpa using this
    positivity
  -- Each `ε > 0` gives an eventual upper bound; conclude `limsup ≤ 0`.
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hevent : ∀ᶠ n : ℕ in atTop, (1 / (n : ℝ)) * Real.log (g n x).toReal ≤ 0 + ε := by
    filter_upwards [hx ε hε] with n hn; linarith
  exact limsup_le_of_eventually_le hlb hevent

/-! ### The information-function name-count bound

The engine above is applied here to an *abstract* information function `infoFun : ℕ → α → ℝ`
(the eventual concrete object is `infoFunₙ x = -log (μ atomₙ).toReal` from
`Oseledets.Krieger.InfoFunction`, built in a sibling file; we keep this result decoupled from it).
The single hypothesis is the **partition-function bound at rate `R`**:
`∫⁻ exp(infoFunₙ − n·R) ∂μ ≤ 1`.  Feeding `gₙ x = ofReal (exp (infoFunₙ x − n·R))` to the engine
gives, for a.e. `x`, that eventually `(1/n)·infoFunₙ x ≤ R + ε`, for every `ε > 0`.

The two SMB instantiations:
* **Uniform / crude (`R = log #cells`, Birkhoff-free).**  `∫⁻ exp(infoFunₙ − n·log N)
  = N⁻ⁿ · #{atoms of positive measure} ≤ N⁻ⁿ · Nⁿ = 1`, giving the bound
  `limsup (1/n)·infoFunₙ ≤ log N`.  No ergodic theorem.
* **Sharp (`R = h(P,T)`).**  Requires a non-uniform competing measure and the Birkhoff ergodic
  theorem to evaluate its codelength as a time average (Algoet–Cover eq. (33)); the diagonal
  `ksEntropySeq m / m → h` then closes `R ↓ h`.  Not proved here. -/
theorem ae_forall_eventually_div_infoFun_le {f : ℕ → α → ℝ} (hf : ∀ n, Measurable (f n))
    {R : ℝ} (hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (Real.exp (f n x - n * R)) ∂μ ≤ 1) :
    ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (1 / (n : ℝ)) * f n x ≤ R + ε := by
  -- The likelihood ratio fed to the engine.
  set g : ℕ → α → ℝ≥0∞ := fun n x => ENNReal.ofReal (Real.exp (f n x - n * R)) with hg_def
  have hg : ∀ n, AEMeasurable (g n) μ := fun n =>
    (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hf n).sub measurable_const))).aemeasurable
  -- Pointwise: `log (g n x).toReal = f n x - n R`.
  have hlogeq : ∀ n x, Real.log (g n x).toReal = f n x - n * R := by
    intro n x
    rw [hg_def, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
  filter_upwards [ae_forall_eventually_div_log_le hg hbound] with x hx
  intro ε hε
  filter_upwards [hx ε hε, eventually_ge_atTop 1] with n hn (hn1 : 1 ≤ n)
  -- `(1/n)·(f n x − n R) ≤ ε`  ⇒  `(1/n)·f n x ≤ R + ε`.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  rw [hlogeq] at hn
  have hexp : (1 / (n : ℝ)) * (f n x - n * R) = (1 / (n : ℝ)) * f n x - R := by
    have : (1 / (n : ℝ)) * ((n : ℝ) * R) = R := by
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ hnne, one_mul]
    rw [mul_sub, this]
  rw [hexp] at hn
  linarith

end Oseledets.Krieger
