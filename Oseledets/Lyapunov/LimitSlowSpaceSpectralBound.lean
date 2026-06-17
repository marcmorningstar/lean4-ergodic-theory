/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.RuelleCore
import Oseledets.Lyapunov.Forward
import Oseledets.Lyapunov.ForwardV
import Oseledets.Lyapunov.OseledetsLimit.Limit
import Oseledets.Lyapunov.StratumLogGrowthBounds
import Oseledets.Lyapunov.ForwardSqueezeCore
import Oseledets.Cocycle.Basic

/-!
# The per-vector spectral upper bound on the limit slow space

For an ergodic cocycle `A⁽ⁿ⁾ = cocycle A T n` of invertible matrices over `(X, μ, T)`, a
vector in the limit slow space `vslow A T (exp t) x` has normalized log-growth bounded above
by the threshold `t`:

  `∀ᵐ x, ∀ t, ∀ v ∈ vslow A T (exp t) x, v ≠ 0 →`
  `      limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ t`.

The reverse-side overlap transfer of `Oseledets.RuelleCofactor` combines with the
almost-everywhere singular-value asymptotics to yield this bound.

## Main results

* `Oseledets.specTerm_envelope_slow`: at a slow singular index (one whose exponent satisfies
  `lamj ≤ lami`), the spectral term obeys `specTerm ≤ exp(n(2 lami + ε))` eventually, by pure
  SVD and Cauchy–Schwarz; no overlap-decay input is needed.
* `Oseledets.reverse_graded_overlap_bound`: for orthonormal bases `b, b'`, forward graded decay
  of the change-of-basis entries together with Ruelle's cofactor bound yields the
  transposed-graded reverse decay.
* `Oseledets.limsup_le_of_mem_vslow`: the per-vector spectral upper bound itself.

## Implementation notes

The bound `limsup_le_of_mem_vslow` follows from the envelope criterion
`limsup_inv_mul_log_norm_cocycle_apply_le`. Its two side conditions hold outright:
positivity `0 < ‖A⁽ⁿ⁾ v‖` for every `n` from `cocycle_apply_ne_zero` (`det (A x) ≠ 0` makes
`A⁽ⁿ⁾` invertible, hence injective on `v ≠ 0`), and the `IsCoboundedUnder (· ≤ ·)` condition
from a bounded-below lower bound (`isCoboundedUnder_le_of_boundedUnder_ge`).

The criterion takes the per-index envelope `specTerm ≤ exp(n(2t + ε))` for every spectral
index `j`. Slow indices (`lam j ≤ t`) follow from `specTerm_envelope_slow`. Fast indices
(`t < lam j`) rest on Ruelle's chain of singular-value estimates, entering through two
hypotheses: `hfwd`, the forward graded overlap bound (the level-increasing entries of the
change of basis between the limit eigenbasis and the time-`n` Gram eigenbasis decay at the
graded rate, the forward chain of Ruelle's Lemma 1.4); and `hbridge`, the band-limit bridge
from the reverse graded entry bound to the fast-index `specTerm` envelope (via
`tendsto_bandProjector_of_gap`). The forward bound is converted into the reverse bound by
`reverse_graded_overlap_bound`, which consumes `hrev`, Ruelle's reverse-side cofactor bound
for orthogonal matrices with graded forward decay
(`Oseledets.RuelleCofactor.entry_reverse_bound_of_orthogonal`).

## References

* David Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58
-/

open MeasureTheory Filter Topology Matrix
open scoped RealInnerProductSpace BigOperators

noncomputable section

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
variable {d : ℕ} {T : X → X}

/-! ## Positivity of the cocycle applied to a nonzero vector -/

/-- **Eventual (in fact universal) positivity of `‖A⁽ⁿ⁾ v‖`.**  Since `det (A x) ≠ 0`, every
cocycle matrix `A⁽ⁿ⁾` is invertible, hence `toEuclideanLin (A⁽ⁿ⁾)` is injective, so it sends the
nonzero `v` to a nonzero (positive-norm) vector for *every* `n`. -/
theorem eventually_pos_norm_cocycle_apply [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (x : X)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
  filter_upwards with n
  exact norm_pos_iff.mpr (cocycle_apply_ne_zero (T := T) hA n x hv)

/-! ## The slow-index `specTerm` envelope -/

/-- The squared overlap with the orthonormal Gram eigenbasis is bounded by `‖v‖²`
(Cauchy–Schwarz, the basis vectors being unit). -/
theorem inner_sq_sortedGramEigenbasis_le [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) (v : EuclideanSpace ℝ (Fin d))
    (j : Fin (Fintype.card (Fin d))) :
    (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2 ≤ ‖v‖ ^ 2 := by
  have hcs : |(inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)|
      ≤ ‖v‖ * ‖sortedGramEigenbasis A T n x j‖ :=
    abs_real_inner_le_norm v _
  have hunit : ‖sortedGramEigenbasis A T n x j‖ = 1 :=
    (sortedGramEigenbasis A T n x).orthonormal.1 j
  rw [hunit, mul_one] at hcs
  nlinarith [abs_nonneg (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ), hcs, norm_nonneg v,
    sq_abs (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ)]

/-- A nonnegative constant `C` is eventually dominated by `exp(n·δ)` for any `δ > 0`. -/
theorem eventually_const_le_exp (C : ℝ) (hC : 0 ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, C ≤ Real.exp ((n : ℝ) * δ) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · filter_upwards with n; rw [← hC0]; exact Real.exp_nonneg _
  · have hgrow : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * δ)) atTop atTop :=
      Real.tendsto_exp_atTop.comp
        (Filter.Tendsto.atTop_mul_const hδ tendsto_natCast_atTop_atTop)
    exact hgrow.eventually_ge_atTop C

/-- **The slow-index `specTerm` envelope.**  If the `j`-th singular exponent converges to
`lamj ≤ lami` (a *slow* index), then `specTermⱼ(n) ≤ exp(n(2 lami + ε))` eventually, for
every `ε > 0`.  Pure SVD + Cauchy–Schwarz: `specTerm = σⱼ²·⟪v,uⱼ⟫² ≤ σⱼ²·‖v‖²`, with
`σⱼ² ≤ exp(n(2lamj+ε/2)) ≤ exp(n(2lami+ε/2))` and `‖v‖² ≤ exp(n·ε/2)` eventually.  No
overlap-decay input is needed at a slow index. -/
theorem specTerm_envelope_slow [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) {x : X}
    {v : EuclideanSpace ℝ (Fin d)} {lami lamj : ℝ} (j : Fin (Fintype.card (Fin d)))
    (hjd : (j : ℕ) < d)
    (hσ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 lamj))
    (hslow : lamj ≤ lami) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) := by
  intro ε hε
  have hσpos : ∀ n : ℕ, 1 ≤ n →
      0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j :=
    fun n _ => singularValues_cocycle_pos hA n x hjd
  have hσenv := eventually_sq_singularValue_le_exp (T := T) j hσpos hσ (ε/2) (by linarith)
  have hCdom :=
    eventually_const_le_exp (‖v‖ ^ 2) (sq_nonneg _) (show (0:ℝ) < ε/2 by linarith)
  filter_upwards [hσenv, hCdom] with n hσn hCn
  rw [specTerm]
  have hov : (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2 ≤ ‖v‖ ^ 2 :=
    inner_sq_sortedGramEigenbasis_le A n x v j
  calc (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j ^ 2
          * (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2
      ≤ Real.exp ((n : ℝ) * (2 * lamj + ε/2)) * ‖v‖ ^ 2 := by
        apply mul_le_mul hσn hov (by positivity) (Real.exp_nonneg _)
    _ ≤ Real.exp ((n : ℝ) * (2 * lamj + ε/2)) * Real.exp ((n : ℝ) * (ε/2)) :=
        mul_le_mul_of_nonneg_left hCn (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * (2 * lamj + ε/2) + (n : ℝ) * (ε/2)) := by rw [← Real.exp_add]
    _ ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) := by
        apply Real.exp_le_exp.mpr
        have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        nlinarith [hslow, hnn]

/-! ## The reverse-side graded overlap transfer

An orthonormal change-of-basis matrix `S i j = ⟪b' j, b i⟫` is orthogonal (`S Sᵀ = 1`, pure
Parseval).  If its *forward* (level-increasing) entries decay at the graded rate
`c·exp(-(g j - g i)₊)`, then Ruelle's cofactor bound `hrev` transfers this to the *reverse*
(level-decreasing) entries: `|S i j| ≤ (d-1)!·c^{d-1}·exp(-(g i - g j))`.
`Oseledets.RuelleCofactor.SVDData.orthogonal_block_mass_symm` is the Frobenius-mass companion;
here `hrev` supplies the per-entry graded transfer. -/

open scoped Matrix in
/-- **Reverse-side graded overlap transfer.**  For orthonormal bases `b, b'` of a
finite-dimensional real inner product space, the change-of-basis matrix `S i j = ⟪b' j, b i⟫` is
orthogonal; given the forward graded decay of its entries, the cofactor bound `hrev` yields the
transposed-graded reverse bound on every entry. -/
theorem reverse_graded_overlap_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hrev : ∀ (S : Matrix (Fin d) (Fin d) ℝ), S * Sᵀ = 1 →
      ∀ (g : Fin d → ℝ) (c : ℝ), 1 ≤ c →
      (∀ a b : Fin d, |S a b| ≤ c * Real.exp (-(max (g b - g a) 0))) →
      ∀ i j : Fin d, |S i j| ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)))
    (b b' : OrthonormalBasis (Fin d) ℝ E) (g : Fin d → ℝ) (c : ℝ) (hc : 1 ≤ c)
    (hfwd : ∀ a e : Fin d,
      |(inner ℝ (b' e) (b a) : ℝ)| ≤ c * Real.exp (-(max (g e - g a) 0))) :
    ∀ i j : Fin d, |(inner ℝ (b' j) (b i) : ℝ)|
      ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)) := by
  set S : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.of (fun i j => (inner ℝ (b' j) (b i) : ℝ)) with hS
  have hortho : S * Sᵀ = 1 := by
    ext i k
    simp only [hS, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    have key := (b').sum_inner_mul_inner (b i) (b k)
    have hrw : ∀ e, (inner ℝ (b' e) (b i) : ℝ) * (inner ℝ (b' e) (b k) : ℝ)
        = (inner ℝ (b i) (b' e) : ℝ) * (inner ℝ (b' e) (b k) : ℝ) := by
      intro e; rw [real_inner_comm (b' e) (b i)]
    simp_rw [hrw]
    rw [key, (orthonormal_iff_ite.mp b.orthonormal i k)]
  exact hrev S hortho g c hc hfwd

/-! ## The per-vector spectral upper bound

The Ruelle-dependent content enters through three hypotheses:

* `hrev` — Ruelle's reverse-side cofactor bound
  (`Oseledets.RuelleCofactor.entry_reverse_bound_of_orthogonal`), with the exact statement
  needed;
* `hfwd` — the forward graded overlap bound, uniform in the band index, the output of the
  forward chain of Ruelle's Lemma 1.4 (`Oseledets.RuelleCofactor.SVDData.oneStep_sandwich` and
  `Oseledets.RuelleCofactor.chain_leakage_exp`, the full pairwise gap);
* `hbridge` — the band-limit bridge: from the reverse graded entry bound to the fast-index
  `specTerm` envelope, via the band-limit identification `tendsto_bandProjector_of_gap`.

The slow indices (`lam j ≤ t`) need no Ruelle input; they follow from
`specTerm_envelope_slow`.
-/

open Oseledets.RuelleCofactor in
/-- **Per-vector spectral upper bound on the limit slow space.**

For `μ`-a.e. `x`, every threshold `t`, and every nonzero `v` in the limit slow space
`vslow A T (exp t) x`, the cocycle growth obeys `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ t`.

The proof feeds the envelope criterion `limsup_inv_mul_log_norm_cocycle_apply_le` the
per-index `specTerm` envelopes: slow indices (`lam j ≤ t`) from `specTerm_envelope_slow`
(no Ruelle input); fast indices (`t < lam j`) from Ruelle's chain, which enters as two
hypotheses:

* `hfwd` — the forward graded overlap bound, uniform in the band index (Ruelle Lemma 1.4,
  `SVDData.oneStep_sandwich` + `chain_leakage_exp`): the level-increasing entries of the
  change of basis between the limit eigenbasis `b'` and the time-`n` Gram eigenbasis decay
  at the graded rate.
* `hbridge` — the band-limit bridge (`tendsto_bandProjector_of_gap`): from the *reverse*
  graded entry bound (produced here by applying `hrev` via `reverse_graded_overlap_bound`)
  to the fast-index `specTerm` envelope.

The hypothesis `hrev` is consumed by `reverse_graded_overlap_bound`, which turns the forward
graded decay `hfwd` into the reverse graded decay that `hbridge` requires.  Positivity and
the cobounded side condition are discharged by `cocycle_apply_ne_zero` and
`isBoundedUnder_log_norm_cocycle_apply`. -/
theorem limsup_le_of_mem_vslow
    [MeasureTheory.IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) (_hTmeas : Measurable T)
    {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (hrev : ∀ (S : Matrix (Fin d) (Fin d) ℝ), S * Sᵀ = 1 →
      ∀ (g : Fin d → ℝ) (c : ℝ), 1 ≤ c →
      (∀ a b : Fin d, |S a b| ≤ c * Real.exp (-(max (g b - g a) 0))) →
      ∀ i j : Fin d, |S i j| ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)))
    -- `lam`: the deterministic per-index singular exponents.
    (lam : ℕ → ℝ)
    (hlam : ∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam i)))
    -- the per-`x` limit fast/slow eigenbasis `b'` of `Λ`, graded by `g x` (`gⱼ = lamⱼ`).
    (b' : X → OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (g : X → Fin d → ℝ)
    -- `hfwd`: the forward graded overlap bound (Ruelle Lemma 1.4 forward chain).
    (hfwd : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ vslow A T (Real.exp t) x, v ≠ 0 →
      ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop,
        ∀ a e : Fin d, |(inner ℝ (b' x e)
            (sortedGramEigenbasis A T n x
              ⟨a, lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ c * Real.exp (-(max (g x e - g x a) 0)))
    -- `hbridge`: the band-limit bridge from reverse graded entries to the fast envelope.
    (hbridge : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ vslow A T (Real.exp t) x, v ≠ 0 →
      (∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop, ∀ i e : Fin d,
        |(inner ℝ (b' x e)
            (sortedGramEigenbasis A T n x
              ⟨i, lt_of_lt_of_eq i.2 (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g x i - g x e))) →
        ∀ j : Fin (Fintype.card (Fin d)), t < lam (j : ℕ) → ∀ ε > 0,
          ∀ᶠ n : ℕ in atTop,
          specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * t + ε))) :
    ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ vslow A T (Real.exp t) x, v ≠ 0 →
      Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) Filter.atTop ≤ t := by
  have hcard : Fintype.card (Fin d) = d := Fintype.card_fin d
  -- intersect the (finitely many) per-index a.e. singular-limit sets.
  have hallσ : ∀ᵐ x ∂μ, ∀ j : Fin (Fintype.card (Fin d)), Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j))
      atTop (𝓝 (lam (j : ℕ))) := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    have hjd : (j : ℕ) < d := lt_of_lt_of_eq j.2 hcard
    exact hlam (j : ℕ) hjd
  have hcob := isBoundedUnder_log_norm_cocycle_apply hT A hA hAmeas hint hint'
  filter_upwards [hallσ, hcob, hfwd, hbridge] with x hσx hcobx hfwdx hbridgex
  intro t v hvmem hv
  -- positivity (every `n`) and the cobounded side-condition.
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ :=
    eventually_pos_norm_cocycle_apply hA x hv
  have hbddge : IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) := (hcobx v hv).2
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) :=
    isCoboundedUnder_le_of_boundedUnder_ge hbddge
  -- the fast-index `specTerm` envelope, derived by consuming `hrev`:
  --   forward graded decay (`hfwd`) ──hrev──▶ reverse graded decay ──hbridge──▶ fast
  --   envelope.
  have hfast : ∀ j : Fin (Fintype.card (Fin d)), t < lam (j : ℕ) → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop,
      specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * t + ε)) := by
    -- the reverse graded entry bound at the (forward) constant `c0`, via `hrev`.
    obtain ⟨c0, hc0, hfwdn⟩ := hfwdx t v hvmem hv
    have hrevbound : ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop, ∀ i e : Fin d,
        |(inner ℝ (b' x e)
            (sortedGramEigenbasis A T n x
              ⟨i, lt_of_lt_of_eq i.2 (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g x i - g x e)) := by
      refine ⟨c0, hc0, ?_⟩
      filter_upwards [hfwdn] with n hn
      -- the time-`n` Gram eigenbasis reindexed to `Fin d`.
      set bn : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
        (sortedGramEigenbasis A T n x).reindex (finCongr hcard) with hbn
      have hbneq : ∀ a : Fin d, bn a = sortedGramEigenbasis A T n x
          ⟨(a : ℕ), lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩ := by
        intro a; rw [hbn, OrthonormalBasis.reindex_apply]; congr 1
      -- `b := bn`, `b' := b' x`; the reverse transfer via `hrev`.
      have hrevn := reverse_graded_overlap_bound (d := d) hrev
        (b := bn) (b' := b' x) (g := g x) c0 hc0
        (fun a e => by rw [hbneq a]; exact hn a e)
      intro i e
      have hrevie := hrevn i e
      rwa [hbneq i] at hrevie
    exact hbridgex t v hvmem hv hrevbound
  -- per-index envelope: slow (derived) vs fast (above).
  have henv : ∀ j : Fin (Fintype.card (Fin d)), ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * t + ε)) := by
    intro j
    by_cases hsl : lam (j : ℕ) ≤ t
    · have hjd : (j : ℕ) < d := lt_of_lt_of_eq j.2 hcard
      exact specTerm_envelope_slow hA j hjd (hσx j) hsl
    · exact hfast j (not_le.mp hsl)
  exact limsup_inv_mul_log_norm_cocycle_apply_le T A x v t henv hpos hcobdd

end Oseledets
