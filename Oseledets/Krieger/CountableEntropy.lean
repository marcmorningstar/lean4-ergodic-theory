/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.Partition
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Shannon entropy of a countable measurable partition

This file builds the **countable-partition Shannon entropy** layer needed for the unconditional
Krieger finite generator theorem (issue #15). Krieger's proof
(Downarowicz, *Entropy in Dynamical Systems*, Theorem 4.2.3) first produces a *countable*
generator with **finite static (Shannon) entropy**, and only then codes it into `Fin k`. The
repository's existing entropy stack (`Oseledets.Entropy.*`) is indexed by a `Fintype`; this file
extends the Shannon entropy `H(α) = ∑ᵢ negMulLog (μ(αᵢ))` to a *countable* family of cells via an
unconditional `tsum`, and proves the finiteness criterion that the Krieger limit-code construction
consumes.

## Representation

Following `Oseledets.Entropy.entropy`, the entropy is defined on *loose data* — a
`Countable`-indexed family of cells `s : ι → Set α` — so that it applies both to a countable
measurable
partition and to intermediate families. The companion bundle is the existing
`Oseledets.Entropy.MeasurePartition` (finite) for the agreement lemma.

Because `tsum` over `ℝ` returns the junk value `0` for a non-summable family, the honest
formalization of "the entropy is finite" is the **`Summable`** predicate on the termwise sequence
`i ↦ negMulLog (μ(sᵢ)).toReal`: when it holds, `Hμ` is the genuine infinite sum (and is finite,
being a real number); the finiteness criterion is therefore stated as a `Summable` conclusion.

## Main definitions

* `Oseledets.Krieger.cHμ`: the countable Shannon entropy `∑' i, negMulLog (μ (s i)).toReal` of a
  `Countable`-indexed family of cells `s : ι → Set α`.

## Main results

* `Oseledets.Krieger.cHμ_nonneg`: countable entropy is nonnegative for a probability measure.
* `Oseledets.Krieger.cHμ_eq_entropy`: for a `Fintype`-indexed family the countable entropy agrees
  with the finite `Oseledets.Entropy.entropy`, so the countable theory genuinely extends the finite
  one.
* `Oseledets.Krieger.summable_negMulLog_of_le`: **the comparison core.** If `0 ≤ p i ≤ c i ≤ e⁻¹`
  for all `i` and `i ↦ negMulLog (c i)` is summable, then `i ↦ negMulLog (p i)` is summable. This is
  the directly-consumable finiteness input: a partition cell used with probability `≤ cᵢ`, where
  `∑ negMulLog cᵢ < ∞`, contributes a summable entropy tail.
* `Oseledets.Krieger.summable_negMulLog_of_summable_index_mul`: **Downarowicz Fact 1.1.4.** If a
  countable nonnegative sub-probability family `p : ℕ → ℝ` satisfies `∑ i, i · pᵢ < ∞`, then its
  entropy `i ↦ negMulLog (pᵢ)` is summable, hence `H(p) < ∞`.
* `Oseledets.Krieger.cHμ_summable_of_summable_index_mul`: the same criterion phrased on a partition
  `μ`-measure family: if `∑ i, i · μ(sᵢ).toReal < ∞`, the countable entropy `cHμ μ s` is a genuine
  finite sum.

## References

* Tomasz Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §1.1 (Fact 1.1.4) and §4.2
  (the Krieger generator theorem).
* Peter Walters, *An Introduction to Ergodic Theory*, Springer (1982), Ch. 4.
* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
-/

open MeasureTheory Function Real

namespace Oseledets.Krieger

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

/-- The **countable Shannon entropy** `∑' i, negMulLog (μ (s i)).toReal` of a `Countable`-indexed
family of cells `s : ι → Set α` with respect to a measure `μ`. For a genuine partition this is
`- ∑ᵢ μ(sᵢ) log μ(sᵢ)`, the average information of learning which cell a random point lies in. The
`tsum` is unconditional; it returns `0` if the termwise sequence is not summable (see
`cHμ_summable_of_summable_index_mul` for the finiteness criterion that makes it a genuine sum). -/
noncomputable def cHμ (μ : Measure α) (s : ι → Set α) : ℝ :=
  ∑' i, Real.negMulLog (μ (s i)).toReal

@[simp]
lemma cHμ_def (μ : Measure α) (s : ι → Set α) :
    cHμ μ s = ∑' i, Real.negMulLog (μ (s i)).toReal := rfl

/-- Each entropy term `negMulLog (μ (s i)).toReal` is nonnegative for a probability measure, since
each cell has measure in `[0, 1]` and `negMulLog` is nonnegative there. -/
lemma negMulLog_measure_toReal_nonneg (μ : Measure α) [IsProbabilityMeasure μ] (A : Set α) :
    0 ≤ Real.negMulLog (μ A).toReal := by
  refine Real.negMulLog_nonneg ENNReal.toReal_nonneg ?_
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := A))
  rwa [ENNReal.toReal_one] at h

/-- Countable Shannon entropy is nonnegative for a probability measure: every term is nonnegative,
so the unconditional `tsum` is nonnegative (whether or not it converges, since `tsum` of a
non-summable nonnegative family is the junk value `0 ≥ 0`). -/
lemma cHμ_nonneg (μ : Measure α) [IsProbabilityMeasure μ] (s : ι → Set α) :
    0 ≤ cHμ μ s := by
  rw [cHμ_def]
  exact tsum_nonneg fun i => negMulLog_measure_toReal_nonneg μ (s i)

/-- **Finite agreement.** For a `Fintype`-indexed family of cells the countable Shannon entropy
`cHμ` agrees with the repository's finite `Oseledets.Entropy.entropy`: the unconditional `tsum`
over a finite index type collapses to the finite sum. This shows the countable theory genuinely
extends the finite one. -/
@[simp]
lemma cHμ_eq_entropy [Fintype ι] (μ : Measure α) (s : ι → Set α) :
    cHμ μ s = Oseledets.Entropy.entropy μ s := by
  rw [cHμ_def, Oseledets.Entropy.entropy_def, tsum_fintype]

/-! ### Monotonicity of `negMulLog` on the lower branch

The function `negMulLog x = -x log x` is increasing on `[0, e⁻¹]` (its maximum is at `e⁻¹`). This
is the lower-branch monotonicity used in Downarowicz's finiteness criterion (Fact 1.1.4): a cell
used with very small probability `p` contributes `negMulLog p`, dominated by `negMulLog c` for any
`p ≤ c ≤ e⁻¹`. -/

/-- `negMulLog` is monotone increasing on `[0, e⁻¹]`: it is `-(x log x)`, and `x ↦ x log x` is
strictly antitone there (`Real.mul_log_strictAntiOn`). -/
lemma negMulLog_monotoneOn_Icc :
    MonotoneOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) := by
  intro x hx y hy hxy
  have hanti := Real.mul_log_strictAntiOn.antitoneOn hx hy hxy
  simp only [Real.negMulLog_eq_neg]
  exact neg_le_neg hanti

/-- The monotone comparison for a single pair `0 ≤ p ≤ c ≤ e⁻¹`: `negMulLog p ≤ negMulLog c`. -/
lemma negMulLog_le_of_le {p c : ℝ} (hp : 0 ≤ p) (hpc : p ≤ c) (hc : c ≤ Real.exp (-1)) :
    Real.negMulLog p ≤ Real.negMulLog c :=
  negMulLog_monotoneOn_Icc ⟨hp, hpc.trans hc⟩ ⟨hp.trans hpc, hc⟩ hpc

/-! ### The comparison finiteness criterion -/

/-- **Comparison core for finite countable entropy.** If `0 ≤ p i ≤ c i ≤ e⁻¹` for all `i` and the
dominating entropy sequence `i ↦ negMulLog (c i)` is summable, then `i ↦ negMulLog (p i)` is
summable. This is the directly-consumable input for Krieger's limit-code construction: a partition
cell used with probability `≤ cᵢ`, with `∑ negMulLog cᵢ < ∞`, has a summable (hence finite)
entropy contribution. -/
lemma summable_negMulLog_of_le {p c : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hpc : ∀ i, p i ≤ c i)
    (hc : ∀ i, c i ≤ Real.exp (-1)) (hsum : Summable fun i => Real.negMulLog (c i)) :
    Summable fun i => Real.negMulLog (p i) :=
  Summable.of_nonneg_of_le
    (fun i => Real.negMulLog_nonneg (hp i) ((hpc i).trans (hc i) |>.trans (by
      rw [Real.exp_le_one_iff]; norm_num)))
    (fun i => negMulLog_le_of_le (hp i) (hpc i) (hc i)) hsum

/-! ### Downarowicz's Fact 1.1.4: the `∑ i·pᵢ < ∞` finiteness criterion

The criterion the Krieger limit-code construction (Downarowicz Thm 4.2.3) ultimately consumes: a
countable nonnegative sub-probability family whose index-weighted total `∑ i·pᵢ` is finite has
finite Shannon entropy. The proof is Downarowicz's two-branch split of each term against the
threshold `2⁻ⁱ`: above the threshold `negMulLog pᵢ = pᵢ·(−log pᵢ) ≤ pᵢ·(i·log 2)` since `−log` is
decreasing; below it `negMulLog pᵢ ≤ negMulLog 2⁻ⁱ = 2⁻ⁱ·(i·log 2)` since `negMulLog` is increasing
on `[0, e⁻¹] ⊇ [0, 2⁻ⁱ]` for `i ≥ 2`. Both dominating sequences are summable. -/

/-- `(1/2)^i ≤ e⁻¹` for `i ≥ 2`: indeed `(1/2)^i ≤ (1/2)^2 = 1/4`, and `1/4 ≤ e⁻¹` since
`e < 3 < 4`. This places `2⁻ⁱ` in the lower monotone branch `[0, e⁻¹]` of `negMulLog`. -/
lemma half_pow_le_exp_neg_one {i : ℕ} (hi : 2 ≤ i) : (1 / 2 : ℝ) ^ i ≤ Real.exp (-1) := by
  have h14 : (1 / 2 : ℝ) ^ i ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
      _ = 1 / 4 := by norm_num
  have he : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  exact h14.trans he

/-- `negMulLog ((1/2)^i) = (1/2)^i · (i · log 2)`. -/
lemma negMulLog_half_pow (i : ℕ) :
    Real.negMulLog ((1 / 2 : ℝ) ^ i) = (1 / 2 : ℝ) ^ i * (i * Real.log 2) := by
  rw [Real.negMulLog, Real.log_pow]
  have : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [this]; ring

/-- **The two-branch termwise domination** (Downarowicz Fact 1.1.4, per term). For `i ≥ 2` and a
sub-probability value `0 ≤ p ≤ 1`,
`negMulLog p ≤ (i·log 2)·p + (i·log 2)·(1/2)^i`.
Above the threshold `2⁻ⁱ` the first summand dominates (since `−log` is decreasing); below it the
second dominates (since `negMulLog` is increasing on `[0, 2⁻ⁱ]`). -/
lemma negMulLog_le_index_bound {i : ℕ} (hi : 2 ≤ i) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.negMulLog p ≤ (i * Real.log 2) * p + (i * Real.log 2) * (1 / 2 : ℝ) ^ i := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ (i : ℝ) * Real.log 2 := by positivity
  have hhalf_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ i := by positivity
  rcases le_or_gt ((1 / 2 : ℝ) ^ i) p with hge | hlt
  · -- Above the threshold: `negMulLog p = p·(−log p) ≤ p·(i·log 2)`.
    have hppos : 0 < p := lt_of_lt_of_le (by positivity) hge
    have hnlog_nonneg : 0 ≤ -Real.log p := by
      rw [neg_nonneg]; exact Real.log_nonpos hp0 hp1
    have hnlog_le : -Real.log p ≤ (i : ℝ) * Real.log 2 := by
      have hlogge : Real.log ((1 / 2 : ℝ) ^ i) ≤ Real.log p :=
        Real.log_le_log (by positivity) hge
      rw [Real.log_pow] at hlogge
      have : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
      rw [this] at hlogge
      -- `i·(−log 2) ≤ log p` ⟹ `−log p ≤ i·log 2`
      nlinarith [hlogge]
    have hbound : Real.negMulLog p ≤ ((i : ℝ) * Real.log 2) * p := by
      rw [Real.negMulLog, neg_mul, ← mul_neg]
      have := mul_le_mul_of_nonneg_left hnlog_le hp0
      nlinarith [this]
    nlinarith [mul_nonneg hL hhalf_nonneg]
  · -- Below the threshold: `negMulLog p ≤ negMulLog ((1/2)^i) = (1/2)^i·(i·log 2)`.
    have hmono : Real.negMulLog p ≤ Real.negMulLog ((1 / 2 : ℝ) ^ i) :=
      negMulLog_le_of_le hp0 hlt.le (half_pow_le_exp_neg_one hi)
    rw [negMulLog_half_pow] at hmono
    have : Real.negMulLog p ≤ ((i : ℝ) * Real.log 2) * (1 / 2 : ℝ) ^ i := by
      rw [mul_comm]; exact hmono
    nlinarith [mul_nonneg hL hp0]

/-- **Downarowicz Fact 1.1.4.** If a countable nonnegative sub-probability family `p : ℕ → ℝ`
(`0 ≤ pᵢ ≤ 1`) has finite index-weighted total `∑ i, i·pᵢ < ∞`, then its Shannon entropy sequence
`i ↦ negMulLog (pᵢ)` is summable, hence `H(p) = ∑ᵢ negMulLog pᵢ < ∞`.

This is the static finiteness input to Krieger's finite generator theorem: the inductively built
countable generator places cell `i` with measure controlled so that `∑ i·μ(cellᵢ) < ∞`, whence its
static entropy is finite. The proof dominates each entropy term (Downarowicz's two-branch split,
`negMulLog_le_index_bound`) by `(i·log 2)·pᵢ + (i·log 2)·2⁻ⁱ`; the first is summable from
`∑ i·pᵢ < ∞`, the second is the convergent series `∑ i·2⁻ⁱ`. -/
theorem summable_negMulLog_of_summable_index_mul {p : ℕ → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : Summable fun i : ℕ => (i : ℝ) * p i) :
    Summable fun i => Real.negMulLog (p i) := by
  -- The dominating sequence `g i = (i·log 2)·pᵢ + (i·log 2)·2⁻ⁱ`.
  -- `∑ i·pᵢ` summable ⟹ first summand summable (scale by `log 2`).
  have hA : Summable fun i : ℕ => Real.log 2 * ((i : ℝ) * p i) := hsum.mul_left _
  -- `∑ i·2⁻ⁱ` summable (geometric × polynomial).
  have hB0 : Summable fun i : ℕ => (i : ℝ) ^ 1 * (1 / 2 : ℝ) ^ i :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs]; norm_num)
  have hB : Summable fun i : ℕ => Real.log 2 * ((i : ℝ) * (1 / 2 : ℝ) ^ i) := by
    refine (hB0.mul_left (Real.log 2)).congr fun i => ?_
    rw [pow_one]
  set g : ℕ → ℝ := fun i => Real.log 2 * ((i : ℝ) * p i) +
      Real.log 2 * ((i : ℝ) * (1 / 2 : ℝ) ^ i) with hg_def
  have hg : Summable g := hA.add hB
  -- Compare on the tail `i ≥ 2`; summability is unaffected by the two head terms.
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le (fun i => Real.negMulLog_nonneg (hp0 _) (hp1 _))
    (fun i => ?_) ((summable_nat_add_iff 2).mpr hg)
  -- Termwise bound at index `i + 2 ≥ 2`.
  have hbound := negMulLog_le_index_bound (i := i + 2) (by omega) (hp0 (i + 2)) (hp1 (i + 2))
  simp only [hg_def]
  -- Rearrange the bound to match `g (i+2)`.
  have hcast : ((i + 2 : ℕ) : ℝ) = ((i : ℝ) + 2) := by push_cast; ring
  rw [hcast] at hbound ⊢
  nlinarith [hbound]

/-! ### The partition-level finiteness criterion -/

/-- **Finite static entropy of a countable partition (Krieger's static input).** If a `ℕ`-indexed
family of cells `s` of a probability space has finite index-weighted total mass
`∑ i, i·μ(sᵢ) < ∞`, then the entropy terms `i ↦ negMulLog (μ(sᵢ)).toReal` are summable, so the
countable Shannon entropy `cHμ μ s` is a genuine (finite) sum rather than the `tsum` junk value.

This is Downarowicz Fact 1.1.4 specialized to a `μ`-measure family: it is the criterion the Krieger
limit-code construction (Downarowicz Thm 4.2.3) verifies for the inductively built countable
generator, certifying that the generator has finite static entropy before it is coded into
`Fin k`. -/
theorem cHμ_summable_of_summable_index_mul (μ : Measure α) [IsProbabilityMeasure μ]
    {s : ℕ → Set α} (hsum : Summable fun i : ℕ => (i : ℝ) * (μ (s i)).toReal) :
    Summable fun i => Real.negMulLog (μ (s i)).toReal := by
  refine summable_negMulLog_of_summable_index_mul (fun i => ENNReal.toReal_nonneg)
    (fun i => ?_) hsum
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := s i))
  rwa [ENNReal.toReal_one] at h

end Oseledets.Krieger
