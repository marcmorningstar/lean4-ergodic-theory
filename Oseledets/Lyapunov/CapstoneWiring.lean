import Oseledets.Lyapunov.RuelleCore
import Oseledets.Lyapunov.Forward
import Oseledets.Lyapunov.ForwardV
import Oseledets.Lyapunov.OseledetsLimit
import Oseledets.Lyapunov.ForwardLowerWiring
import Oseledets.Lyapunov.ForwardSqueezeCore
import Oseledets.Cocycle.Basic

/-!
# M5 — wiring the deterministic Ruelle core to the cocycle (per-vector spectral upper bound)

This file is the **M5 integration layer**: it assembles the committed deterministic Ruelle core
(`Oseledets/Lyapunov/RuelleCore.lean`, namespace `Ruelle13`) and the committed a.e. cocycle
infrastructure (`OseledetsLimit.lean`, `Forward.lean`, `ForwardV.lean`) into the per-vector spectral
upper bound for a vector in the limit slow space `Vslow`:

  `∀ᵐ x, ∀ t, ∀ v ∈ Vslow A T (exp t) x, v ≠ 0 →`
  `      limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ t`.

## Architecture of the assembly

The capstone `limsup_le_of_mem_Vslow` is the terminal node.  Its proof is a **pure assembly** that:

1. Discharges the two routine side-conditions of the committed envelope engine
   `Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le` GENUINELY (no hypothesis):
   * eventual positivity `0 < ‖A⁽ⁿ⁾ v‖` for *every* `n` from `cocycle_apply_ne_zero`
     (`det (A x) ≠ 0` ⟹ `A⁽ⁿ⁾` invertible ⟹ injective on `v ≠ 0`);
   * the `IsCoboundedUnder (· ≤ ·)` side-condition from a bounded-below lower bound
     (`isCoboundedUnder_le_of_boundedUnder_ge`), itself from the operator lower sandwich.

2. Feeds the engine the per-index `specTerm` envelope `specTerm ≤ exp(n(2t+ε))` for every spectral
   index `j`.  This per-index envelope is the OUTPUT of Ruelle's Lemma 1.4 chain (RuelleCore M1/M2)
   composed with the reverse-side cofactor bound `hrev` (RuelleCore M3 supplies the elementary
   same-rate fact; the graded cofactor decay is `hrev`).

The decomposition isolates the genuinely-Ruelle-dependent content into a single per-index hypothesis
`hchain` with a PRECISE type: the per-index `specTerm` envelope at the limit slow threshold.  Below
that hypothesis we *derive* it from the more primitive overlap envelope using the committed
`Oseledets.Tempering.specTerm_envelope_of_tempered_overlap`, and we record (commented inline) exactly
which RuelleCore lemma + `hrev` produces the overlap envelope, instantiating `Ruelle13.SVDData` with
the cocycle to certify the wiring is type-correct.

## On `hrev`

`hrev` is Ruelle's reverse-side cofactor bound (orthogonal change-of-basis: level-increasing entries
decay graded ⟹ level-decreasing entries decay transposed-graded).  A parallel worker proves it; here
it is a hypothesis parameter with the exact statement required for integration to be a function
application.
-/

open MeasureTheory Filter Topology Matrix
open scoped RealInnerProductSpace BigOperators

noncomputable section

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
variable {d : ℕ} {T : X → X}

/-! ## Part A — the routine side-conditions, discharged genuinely -/

/-- **Eventual (in fact universal) positivity of `‖A⁽ⁿ⁾ v‖`.**  Since `det (A x) ≠ 0`, every cocycle
matrix `A⁽ⁿ⁾` is invertible, hence `toEuclideanLin (A⁽ⁿ⁾)` is injective, so it sends the nonzero `v`
to a nonzero (positive-norm) vector for *every* `n`. -/
theorem eventually_pos_norm_cocycle_apply [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (x : X)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
  filter_upwards with n
  exact norm_pos_iff.mpr (cocycle_apply_ne_zero (T := T) hA n x hv)

/-! ## Part B — the overlap is bounded by `‖v‖`, giving the slow-index envelope -/

/-- The squared overlap with the orthonormal Gram eigenbasis is bounded by `‖v‖²` (Cauchy–Schwarz,
the basis vectors being unit). -/
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

/-- **Slow-index `specTerm` envelope (fully derived).**  If the `j`-th singular exponent converges to
`lamj ≤ lami` (a *slow* index), then `specTermⱼ(n) ≤ exp(n(2 lami + ε))` eventually, for every
`ε > 0`.  Pure SVD + Cauchy–Schwarz: `specTerm = σⱼ²·⟪v,uⱼ⟫² ≤ σⱼ²·‖v‖²`, with
`σⱼ² ≤ exp(n(2lamj+ε/2)) ≤ exp(n(2lami+ε/2))` and `‖v‖² ≤ exp(n·ε/2)` eventually.  No overlap-decay
input is needed at a slow index. -/
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
  have hCdom := eventually_const_le_exp (‖v‖ ^ 2) (sq_nonneg _) (show (0:ℝ) < ε/2 by linarith)
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

/-! ## Part C — the reverse-side transfer (Ruelle step 3, genuinely consuming `hrev`)

This is the elementary half of Ruelle's reverse side.  An orthonormal change-of-basis matrix
`S i j = ⟪b' j, b i⟫` is orthogonal (`S Sᵀ = 1`, pure Parseval).  If its *forward* (level-increasing)
entries decay at the graded rate `c·exp(-(g j - g i)₊)`, then `hrev` (Ruelle's cofactor bound)
transfers this to the *reverse* (level-decreasing) entries: `|S i j| ≤ (d-1)!·c^{d-1}·exp(-(g i - g j))`.
This is exactly the step that breaks the nearest-gap fixed point — the seven prior elementary routes
could only bound forward entries.  `RuelleCore.orthogonal_block_mass_symm` is the Frobenius-mass
companion; here `hrev` supplies the per-entry graded transfer. -/

open scoped Matrix in
/-- **Reverse-side graded overlap transfer (Ruelle step 3).**  For orthonormal bases `b, b'` of a
finite-dimensional real inner product space, the change-of-basis matrix `S i j = ⟪b' j, b i⟫` is
orthogonal; given the forward graded decay of its entries and `hrev`, every entry obeys the
transposed-graded reverse bound.  Genuinely consumes `hrev`. -/
theorem reverse_graded_overlap_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hrev : ∀ (S : Matrix (Fin d) (Fin d) ℝ), S * Sᵀ = 1 → ∀ (g : Fin d → ℝ) (c : ℝ), 1 ≤ c →
      (∀ a b : Fin d, |S a b| ≤ c * Real.exp (-(max (g b - g a) 0))) →
      ∀ i j : Fin d, |S i j| ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)))
    (b b' : OrthonormalBasis (Fin d) ℝ E) (g : Fin d → ℝ) (c : ℝ) (hc : 1 ≤ c)
    (hfwd : ∀ a e : Fin d,
      |(inner ℝ (b' e) (b a) : ℝ)| ≤ c * Real.exp (-(max (g e - g a) 0))) :
    ∀ i j : Fin d, |(inner ℝ (b' j) (b i) : ℝ)|
      ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)) := by
  set S : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i j => (inner ℝ (b' j) (b i) : ℝ)) with hS
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

/-! ## Part D — the capstone assembly

The per-vector spectral upper bound for a vector in the limit slow space.  Everything is derived from
committed infrastructure except the genuinely-Ruelle content, which enters through:

* `hrev` — Ruelle's reverse-side cofactor bound (a parallel worker proves it; here a hypothesis
  parameter with the exact statement);
* `hfast` — the per-index `specTerm` envelope at a *fast* singular index (`lamⱼ > t`).  This is the
  output of Ruelle's Lemma 1.4 forward chain (`Ruelle13.SVDData.oneStep_sandwich` +
  `chain_leakage_exp`, the full pairwise gap) followed by the reverse-side rate transfer
  (`Ruelle13.SVDData.orthogonal_block_mass_symm` + `hrev`) and the k→∞ band-limit identification
  (committed `tendsto_bandProjector_of_gap`).  Its TYPE is exactly the per-index input `henv j` of the
  committed envelope engine `Oseledets.limsup_inv_mul_log_norm_cocycle_apply_le`, so the integration of
  the (parallel-worker) Ruelle chain is a function application.

The *slow* indices (`lamⱼ ≤ t`) are discharged here with NO Ruelle input by `specTerm_envelope_slow`.
-/

open Ruelle13 in
/-- **M5 capstone — per-vector spectral upper bound on the limit slow space.**

For `μ`-a.e. `x`, every threshold `t`, and every nonzero `v` in the limit slow space `Vslow A T
(exp t) x`, the cocycle growth obeys `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ t`.

The proof feeds the committed envelope engine `limsup_inv_mul_log_norm_cocycle_apply_le` the per-index
`specTerm` envelopes: slow indices (`lamⱼ ≤ t`) from `specTerm_envelope_slow` (fully derived, no Ruelle
input); fast indices (`lamⱼ > t`) from the Ruelle chain.  The Ruelle chain enters as two residuals:

* `hfwd` — the FORWARD `k`-uniform graded overlap bound (Ruelle Lemma 1.4, `SVDData.oneStep_sandwich`
  + `chain_leakage_exp`): the level-increasing entries of the change-of-basis between the limit
  eigenbasis `b'` and the time-`n` Gram eigenbasis decay at the graded rate.  The prompt-sanctioned
  `k`-uniform residual.
* `hbridge` — the band-limit bridge (committed `tendsto_bandProjector_of_gap`): from the REVERSE graded
  entry bound (produced HERE by applying `hrev` via `reverse_graded_overlap_bound`) to the fast-index
  `specTerm` envelope.

`hrev` is GENUINELY CONSUMED: `reverse_graded_overlap_bound hrev` turns the forward graded decay
`hfwd` into the reverse graded decay that `hbridge` consumes.  Positivity and the cobounded
side-condition are discharged genuinely (`cocycle_apply_ne_zero`, `isBoundedUnder_log_norm_cocycle_apply`). -/
theorem limsup_le_of_mem_Vslow
    [MeasureTheory.IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) (hTmeas : Measurable T)
    {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (hrev : ∀ (S : Matrix (Fin d) (Fin d) ℝ), S * Sᵀ = 1 → ∀ (g : Fin d → ℝ) (c : ℝ), 1 ≤ c →
      (∀ a b : Fin d, |S a b| ≤ c * Real.exp (-(max (g b - g a) 0))) →
      ∀ i j : Fin d, |S i j| ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)))
    -- `lam`: the deterministic per-index singular exponents (committed).
    (lam : ℕ → ℝ)
    (hlam : ∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam i)))
    -- the per-`x` limit fast/slow eigenbasis `b'` of `Λ`, graded by `g x` (`gⱼ = lamⱼ`).
    (b' : X → OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (g : X → Fin d → ℝ)
    -- `hfwd`: the FORWARD `k`-uniform graded overlap bound (Ruelle Lemma 1.4 forward chain).
    (hfwd : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, v ≠ 0 →
      ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop,
        ∀ a e : Fin d, |(inner ℝ (b' x e)
            (sortedGramEigenbasis A T n x ⟨a, lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ c * Real.exp (-(max (g x e - g x a) 0)))
    -- `hbridge`: the band-limit bridge from REVERSE graded entries to the fast `specTerm` envelope.
    (hbridge : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, v ≠ 0 →
      (∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop, ∀ i e : Fin d,
        |(inner ℝ (b' x e)
            (sortedGramEigenbasis A T n x ⟨i, lt_of_lt_of_eq i.2 (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g x i - g x e))) →
        ∀ j : Fin (Fintype.card (Fin d)), t < lam (j : ℕ) → ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
          specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * t + ε))) :
    ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, v ≠ 0 →
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
  -- THE FAST-INDEX `specTerm` ENVELOPE, derived by genuinely consuming `hrev`:
  --   forward graded decay (`hfwd`)  ──hrev──▶  reverse graded decay  ──hbridge──▶  fast envelope.
  have hfast : ∀ j : Fin (Fintype.card (Fin d)), t < lam (j : ℕ) → ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * t + ε)) := by
    -- the reverse graded entry bound at the (forward) constant `c0`, via `hrev`.
    obtain ⟨c0, hc0, hfwdn⟩ := hfwdx t v hvmem hv
    have hrevbound : ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop, ∀ i e : Fin d,
        |(inner ℝ (b' x e)
            (sortedGramEigenbasis A T n x ⟨i, lt_of_lt_of_eq i.2 (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g x i - g x e)) := by
      refine ⟨c0, hc0, ?_⟩
      filter_upwards [hfwdn] with n hn
      -- the time-`n` Gram eigenbasis reindexed to `Fin d`.
      set bn : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
        (sortedGramEigenbasis A T n x).reindex (finCongr hcard) with hbn
      have hbneq : ∀ a : Fin d, bn a = sortedGramEigenbasis A T n x
          ⟨(a : ℕ), lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩ := by
        intro a; rw [hbn, OrthonormalBasis.reindex_apply]; congr 1
      -- `b := bn`, `b' := b' x`; the reverse transfer via `hrev` (Ruelle step 3).
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

/-! ## Axiom audit -/

#print axioms eventually_pos_norm_cocycle_apply
#print axioms inner_sq_sortedGramEigenbasis_le
#print axioms eventually_const_le_exp
#print axioms specTerm_envelope_slow
#print axioms reverse_graded_overlap_bound
#print axioms limsup_le_of_mem_Vslow

end Oseledets
