/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.CondJointPullback
import Oseledets.Entropy.CondMono
import Oseledets.Entropy.KSEntropyBounds

/-!
# Relative Kolmogorov–Sinai entropy via the Fekete limit

This file builds the **conditional** (relative) Kolmogorov–Sinai entropy ladder, a faithful mirror
of the absolute ladder of `Oseledets.Entropy.KSEntropy` and `Oseledets.Entropy.KSEntropyBounds`.
Given a sub-σ-algebra `𝒜 ≤ mα` and the conditional Shannon entropy `condEntropy μ 𝒜 s` of
`Oseledets.Entropy.CondPartition`, the relative entropy `h(α, T | 𝒜)` of a measure-preserving
transformation `T` relative to a finite measurable partition `α` is the **Fekete limit** of the
conditional iterated-join entropy sequence.

The construction reuses the flat `Fin n`-indexed iterated join `ksJoin` verbatim; only the entropy
functional changes from `entropy` to `condEntropy μ 𝒜`. Subadditivity is the conditional mirror of
`ksEntropySeq_subadditive`: the `(n + m)`-join reindexes (via `ksJoinCells_append`) to the join of
the `n`-fold join with the `Tⁿ`-pullback of the `m`-fold join, and the conditional join
subadditivity `condEntropy_join_le` bounds it by the sum of the two conditional entropies. The
second summand `H(T⁻ⁿ(m-join) | 𝒜)` is identified with `H(m-join | 𝒜)` by conditioning monotonicity
(`condEntropy_mono_of_le`, conditioning on the finer `𝒜 ≥ comap (Tⁿ) 𝒜` only decreases entropy)
followed by the joint pull-back `condEntropy_comap_pullback`, which evaluates
`H(T⁻ⁿ(m-join) | comap (Tⁿ) 𝒜) = H(m-join | 𝒜)`. This route needs only the **one-sided
forward-invariance** hypothesis `comap T 𝒜 ≤ 𝒜` (iterated to `comap (Tⁿ) 𝒜 ≤ 𝒜` via
`comap_iterate_le`), which is therefore the single invariance hypothesis threaded through everything
from subadditivity onward — strictly weaker than the two-sided hypotheses that a fixed-`𝒜` iterated
pull-back would require.

## Main definitions

* `Oseledets.Entropy.condKsEntropySeq`: the conditional iterated-join entropy sequence
  `n ↦ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α | 𝒜)`.
* `Oseledets.Entropy.condKsEntropyPartition`: the relative Kolmogorov–Sinai entropy `h(α, T | 𝒜)`,
  the Fekete limit.

## Main results

* `Oseledets.Entropy.condKsEntropySeq_subadditive`: subadditivity of the conditional sequence.
* `Oseledets.Entropy.condKsSubadditive`: the sequence is a `Subadditive` sequence.
* `Oseledets.Entropy.tendsto_condKsEntropySeq`: convergence to the Fekete limit.
* `Oseledets.Entropy.condKsEntropyPartition_le_condEntropy`: `h(α, T | 𝒜) ≤ H(α | 𝒜)`.
* `Oseledets.Entropy.condKsEntropyPartition_bot`: conditioning on `⊥` recovers `h(α, T)`.

## References

* François Le Maître, *Notes on the Kolmogorov–Sinai theorem* (2017), §1.
* Peter Walters, *An Introduction to Ergodic Theory*, Springer GTM 79, Chapter 4.
-/

open MeasureTheory Function Filter Topology ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Entropy

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

variable (𝒜)

/-- The **conditional iterated-join entropy sequence** `n ↦ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α | 𝒜)`: the conditional
Shannon entropy `condEntropy μ 𝒜` of the flat `Fin`-indexed join `ksJoin hT P n`. Its Fekete limit
is the relative Kolmogorov–Sinai entropy `h(α, T | 𝒜)`. -/
noncomputable def condKsEntropySeq [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (n : ℕ) : ℝ :=
  condEntropy μ 𝒜 (ksJoin hT P n).cells

/-- The conditional iterated-join entropy is nonnegative: its integrand is pointwise nonnegative
because each conditional cell probability lies in `[0, 1]` (`condEntropy_nonneg`). -/
lemma condKsEntropySeq_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    0 ≤ condKsEntropySeq 𝒜 hT P n :=
  condEntropy_nonneg

/-- The flat `n = 0` conditional join entropy is `0`: the `0`-fold join is the trivial one-cell
partition whose only cell (the empty intersection) is the whole space, and for every `ω` the Markov
kernel gives it conditional probability `1`, with `negMulLog 1 = 0`; the integrand vanishes. -/
@[simp]
lemma condKsEntropySeq_zero [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) :
    condKsEntropySeq 𝒜 hT P 0 = 0 := by
  rw [condKsEntropySeq, condEntropy_def]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_)
  refine Finset.sum_eq_zero fun f _ => ?_
  have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
    IsMarkovKernel.isProbabilityMeasure ω
  rw [ksJoin_cells, ksJoinCells_apply, Set.iInter_of_empty, measure_univ, ENNReal.toReal_one,
    Real.negMulLog_one]

/-- The single-step conditional iterated-join entropy equals the conditional Shannon entropy of the
partition itself: `condKsEntropySeq 𝒜 hT P 1 = H(α | 𝒜)`. The `1`-fold join is `α` reindexed by the
equivalence `(Fin 1 → ι) ≃ ι` (each cell at `f : Fin 1 → ι` is `T⁰⁻¹(α_{f 0}) = α_{f 0}`); the
conditional entropy is invariant under this reindexing of the index type. -/
@[simp]
lemma condKsEntropySeq_one [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) :
    condKsEntropySeq 𝒜 hT P 1 = condEntropy μ 𝒜 P.cells := by
  rw [condKsEntropySeq, ksJoin_cells]
  -- The single cell of the `1`-fold join at `f` is `α_{f 0}`, i.e. `P.cells (e f)` with
  -- `e = Equiv.funUnique (Fin 1) ι`.
  have hcell : ksJoinCells P.cells T 1 = fun f => P.cells (Equiv.funUnique (Fin 1) ι f) := by
    funext f
    rw [ksJoinCells_apply]
    have hstep : ∀ k : Fin 1,
        (T^[(k : ℕ)]) ⁻¹' P.cells (f k) = P.cells (Equiv.funUnique (Fin 1) ι f) := by
      intro k
      rw [show (k : ℕ) = 0 by omega, Function.iterate_zero, Set.preimage_id,
        Equiv.funUnique_apply, Subsingleton.elim k default]
    rw [Set.iInter_congr hstep, Set.iInter_const]
  rw [condEntropy_def, condEntropy_def, hcell]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact Equiv.sum_comp (Equiv.funUnique (Fin 1) ι)
    (fun i => Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal)

variable {𝒜}

omit mα [StandardBorelSpace α] in
/-- **One-sided forward-invariance iterates.** If `comap T 𝒜 ≤ 𝒜` (every `𝒜`-set is, as a set, a
`T`-preimage of an `𝒜`-set), then `comap (T^[n]) 𝒜 ≤ 𝒜` for every `n`. The base case is
`comap id 𝒜 = 𝒜` (`MeasurableSpace.comap_id`); the inductive step writes `T^[n+1] = T ∘ T^[n]`
(`Function.iterate_succ'`), factors the comap as `comap (T^[n]) (comap T 𝒜)`
(`MeasurableSpace.comap_comp`), and chains `comap_mono hinv` with the inductive hypothesis. -/
lemma comap_iterate_le {T : α → α} (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜) (n : ℕ) :
    MeasurableSpace.comap (T^[n]) 𝒜 ≤ 𝒜 := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, MeasurableSpace.comap_id, le_refl]
  | succ k IH =>
    rw [Function.iterate_succ', ← MeasurableSpace.comap_comp]
    exact (MeasurableSpace.comap_mono hinv).trans IH

/-- **Subadditivity of the conditional iterated-join entropy** (the Fekete inequality):
`H(⋁ₖ₌₀ⁿ⁺ᵐ⁻¹ T⁻ᵏ α | 𝒜) ≤ H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α | 𝒜) + H(⋁ₖ₌₀ᵐ⁻¹ T⁻ᵏ α | 𝒜)`. Reindexing the
`(n + m)`-fold join by `Fin.appendEquiv` exhibits it as the join of the `n`-fold join with the
`Tⁿ`-pullback of the `m`-fold join (`ksJoinCells_append`); the conditional join subadditivity
`condEntropy_join_le` bounds it by the sum of the two conditional entropies. The second summand
`H(T⁻ⁿ(m-join) | 𝒜)` is identified with `H(m-join | 𝒜)` in two steps: conditioning monotonicity
`condEntropy_mono_of_le` against the finer `𝒜 ≥ comap (Tⁿ) 𝒜` (using `comap_iterate_le hinv`) only
decreases entropy, and the joint pull-back `condEntropy_comap_pullback` then evaluates
`H(T⁻ⁿ(m-join) | comap (Tⁿ) 𝒜) = H(m-join | 𝒜)`. This needs only the one-sided forward-invariance
hypothesis `hinv : comap T 𝒜 ≤ 𝒜`. -/
lemma condKsEntropySeq_subadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) (n m : ℕ) :
    condKsEntropySeq 𝒜 hT P (n + m)
      ≤ condKsEntropySeq 𝒜 hT P n + condKsEntropySeq 𝒜 hT P m := by
  -- The `Tⁿ`-pullback of the `m`-fold join.
  set Q : MeasurePartition μ (Fin m → ι) := (ksJoin hT P m).pullback (hT.iterate n) with hQ
  -- Rewrite the `(n + m)`-entropy as a conditional join entropy via the append reindexing.
  -- Cell identity: the `(n + m)`-join cell at `appendEquiv (a, b)` is the join cell at `(a, b)`.
  have hcell : ∀ p : (Fin n → ι) × (Fin m → ι),
      (ksJoin hT P (n + m)).cells (Fin.appendEquiv n m p)
        = joinCells (ksJoin hT P n).cells Q.cells p := by
    rintro ⟨a, b⟩
    simp only [ksJoin_cells, joinCells_apply, hQ, MeasurePartition.pullback_cells]
    exact ksJoinCells_append P.cells T n m a b
  have hreindex : condKsEntropySeq 𝒜 hT P (n + m)
      = condEntropy μ 𝒜 (joinCells (ksJoin hT P n).cells Q.cells) := by
    rw [condKsEntropySeq, condEntropy_def, condEntropy_def]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    refine (Equiv.sum_comp (Fin.appendEquiv n m)
      (fun g => Real.negMulLog
        (@condExpKernel α mα _ μ _ 𝒜 ω ((ksJoin hT P (n + m)).cells g)).toReal)).symm.trans ?_
    exact Finset.sum_congr rfl fun p _ => by rw [hcell p]
  -- `comap (Tⁿ) 𝒜 ≤ 𝒜` from the one-sided forward-invariance, iterated.
  have hcomap : MeasurableSpace.comap (T^[n]) 𝒜 ≤ 𝒜 := comap_iterate_le hinv n
  rw [hreindex, condKsEntropySeq, condKsEntropySeq]
  calc condEntropy μ 𝒜 (joinCells (ksJoin hT P n).cells Q.cells)
      ≤ condEntropy μ 𝒜 (ksJoin hT P n).cells + condEntropy μ 𝒜 Q.cells :=
        condEntropy_join_le hm (ksJoin hT P n) Q
    _ ≤ condEntropy μ 𝒜 (ksJoin hT P n).cells
          + condEntropy μ (MeasurableSpace.comap (T^[n]) 𝒜) Q.cells := by
        gcongr
        exact condEntropy_mono_of_le hcomap hm Q
    _ = condEntropy μ 𝒜 (ksJoin hT P n).cells + condEntropy μ 𝒜 (ksJoin hT P m).cells := by
        rw [hQ, MeasurePartition.pullback_cells,
          condEntropy_comap_pullback hm hT n (ksJoin hT P m)]

/-- The conditional iterated-join entropy sequence is a **`Subadditive` sequence** in the sense of
Fekete's lemma: `u (k + l) ≤ u k + u l`. This is `condKsEntropySeq_subadditive` repackaged. -/
lemma condKsSubadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    Subadditive (condKsEntropySeq 𝒜 hT P) :=
  fun k l => condKsEntropySeq_subadditive hm hT hinv P k l

/-- The **relative Kolmogorov–Sinai entropy** `h(α, T | 𝒜)` of a measure-preserving transformation
`T` relative to a finite measurable partition `α` and a sub-σ-algebra `𝒜`, defined as the Fekete
limit `limₙ (1 / n) · H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α | 𝒜)` of the subadditive conditional iterated-join entropy
sequence. -/
noncomputable def condKsEntropyPartition [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) : ℝ :=
  (condKsSubadditive hm hT hinv P).lim

/-- **Fekete convergence to the relative Kolmogorov–Sinai entropy.** The averaged conditional
iterated-join entropies `(1 / n) · H(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α | 𝒜)` converge to `h(α, T | 𝒜)`. The
boundedness-below hypothesis of Fekete's lemma is discharged from the nonnegativity of the
conditional entropies: each `condKsEntropySeq n / n` is at least `0`. -/
lemma tendsto_condKsEntropySeq [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    Tendsto (fun n => condKsEntropySeq 𝒜 hT P n / n) atTop
      (𝓝 (condKsEntropyPartition hm hT hinv P)) := by
  refine (condKsSubadditive hm hT hinv P).tendsto_lim ?_
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (condKsEntropySeq_nonneg 𝒜 hT P n) (Nat.cast_nonneg n)

/-- The conditional iterated-join entropy grows at most linearly: `condKsEntropySeq 𝒜 hT P n ≤
n • H(α | 𝒜)`. This is the subadditive estimate `u n ≤ n • u 1`, proved by induction from
`condKsEntropySeq_subadditive`, with the single step `condKsEntropySeq 1 = H(α | 𝒜)` substituted via
`condKsEntropySeq_one`. -/
lemma condKsEntropySeq_le_nsmul [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) (n : ℕ) :
    condKsEntropySeq 𝒜 hT P n ≤ n • condEntropy μ 𝒜 P.cells := by
  induction n with
  | zero => simp
  | succ k IH =>
    calc condKsEntropySeq 𝒜 hT P (k + 1)
        ≤ condKsEntropySeq 𝒜 hT P k + condKsEntropySeq 𝒜 hT P 1 :=
          condKsEntropySeq_subadditive hm hT hinv P k 1
      _ ≤ k • condEntropy μ 𝒜 P.cells + condEntropy μ 𝒜 P.cells := by
          rw [condKsEntropySeq_one]; gcongr
      _ = (k + 1) • condEntropy μ 𝒜 P.cells := by rw [succ_nsmul]

/-- **Nonnegativity of the relative Kolmogorov–Sinai entropy:** `0 ≤ h(α, T | 𝒜)`. Each averaged
conditional iterated-join entropy `condKsEntropySeq n / n` is nonnegative, and the bound passes to
the Fekete limit. -/
lemma condKsEntropyPartition_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    0 ≤ condKsEntropyPartition hm hT hinv P := by
  refine ge_of_tendsto (tendsto_condKsEntropySeq hm hT hinv P) ?_
  filter_upwards with n
  exact div_nonneg (condKsEntropySeq_nonneg 𝒜 hT P n) (Nat.cast_nonneg n)

/-- **Upper bound of the relative Kolmogorov–Sinai entropy by the conditional partition entropy:**
`h(α, T | 𝒜) ≤ H(α | 𝒜)`. From the linear bound `condKsEntropySeq n ≤ n • H(α | 𝒜)`
(`condKsEntropySeq_le_nsmul`), dividing by `n ≥ 1` gives `condKsEntropySeq n / n ≤ H(α | 𝒜)`
eventually; this passes to the Fekete limit. -/
lemma condKsEntropyPartition_le_condEntropy [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    condKsEntropyPartition hm hT hinv P ≤ condEntropy μ 𝒜 P.cells := by
  refine le_of_tendsto (tendsto_condKsEntropySeq hm hT hinv P) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn0]
  calc condKsEntropySeq 𝒜 hT P n ≤ n • condEntropy μ 𝒜 P.cells :=
        condKsEntropySeq_le_nsmul hm hT hinv P n
    _ = condEntropy μ 𝒜 P.cells * (n : ℝ) := by rw [nsmul_eq_mul, mul_comm]

section Bot

variable {T : α → α}

/-- The conditional iterated-join entropy at the trivial σ-algebra `⊥` equals the absolute
iterated-join entropy: `condEntropy μ ⊥` of any cell family is the ordinary `entropy μ` of that
family (`condEntropy_bot`), and the cells of `ksJoin hT P n` are measurable. -/
lemma condKsEntropySeq_bot [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    condKsEntropySeq ⊥ hT P n = ksEntropySeq hT P n := by
  rw [condKsEntropySeq, condEntropy_bot (fun f => (ksJoin hT P n).measurable f), ksEntropySeq]

/-- **The relative entropy at `⊥` recovers the absolute entropy:**
`h(α, T | ⊥) = h(α, T)`. The two iterated-join entropy sequences agree as functions of `n`
(`condKsEntropySeq_bot`), so the two subadditive sequences are equal and hence have equal Fekete
limits (`Subadditive.lim_eq_of_eq`). The one-sided forward-invariance hypothesis for `⊥` is
discharged internally: `comap T ⊥ = ⊥` (`MeasurableSpace.comap_bot`), so `comap T ⊥ ≤ ⊥` holds
reflexively. -/
lemma condKsEntropyPartition_bot [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) :
    condKsEntropyPartition (𝒜 := ⊥) bot_le hT MeasurableSpace.comap_bot.le P
      = ksEntropyPartition hT P := by
  rw [condKsEntropyPartition, ksEntropyPartition]
  exact Subadditive.lim_eq_of_eq _ _ (funext fun n => condKsEntropySeq_bot hT P n)

end Bot

end Oseledets.Entropy
