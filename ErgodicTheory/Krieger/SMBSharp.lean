/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.SMB
import ErgodicTheory.Entropy.CondGivenPartitionBridge
import ErgodicTheory.Entropy.CondEntropyContinuous
import ErgodicTheory.Entropy.JoinSigmaAlgebra
import ErgodicTheory.Entropy.FactorGeneratorSaturate
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The sharp Shannon–McMillan–Breiman theorem (Breiman/Bruin telescoping)

This file develops the **sharp** Shannon–McMillan–Breiman (SMB) theorem, sharpening the crude
name-count upper bound `limsup (1/n)·iₙ ≤ log (card ι)` of `ErgodicTheory.Krieger.SMB` to the
Kolmogorov–Sinai entropy rate `h(P,T)`, for an **ergodic** measure-preserving transformation `T`
and a finite measurable partition `P`.

The route is the **Breiman/Bruin telescoping identity** (Einsiedler–Lindenstrauss–Ward,
*Entropy in Ergodic Theory*, Ch. 2; Bruin, *Ergodic Theory I*, Lecture 15). The
**conditional information weight** of the `P`-cell `i₀` given the past coding `g`,
`condInfoWeight`, is the surprise `-log (μ(B-cell ∩ Pᵢ₀)/μ(B-cell))` of learning a point's `P`-cell
is `i₀` once its `B`-coding (the future itinerary) is known. The chain rule
`I_{P∨Q} = I_Q + I_{P|Q}`
becomes, at the level of these weights, the **one-step factorization**
`infoWeight_{n+1}(cons i₀ g) = infoWeight_n(g) + condInfoWeight i₀ g`,
which telescopes to `iₙ(x) = ∑_{j<n} g_{n-j}(Tʲx)`.

## Results proved here (sorry-free)

* `condInfoWeight` — the conditional information weight `-log (μ(Bᵦ ∩ Pᵢ)/μ(Bᵦ))` and its
  nonnegativity (`condInfoWeight_nonneg`).
* `ksJoinCells_cons` — the cell cons-factorization `cell_{n+1}(cons i₀ g) = Pᵢ₀ ∩ T⁻¹ cell_n(g)`.
* `infoWeight_succ_eq` — the **one-step telescoping factorization** of the iterated-join
  information weight: peeling the first coordinate splits `infoWeight_{n+1}` into the `n`-step
  weight (shifted by `T`) plus the conditional weight of the first symbol given the `T`-shifted
  `n`-step past. **The positivity hypothesis on the `(n+1)`-cell is load-bearing** — the pointwise
  identity *fails* at codes whose join cell is null (where `-log 0 = 0` is a junk value), which is
  precisely why the Breiman identity for the *information functions* holds only `μ`-a.e.
* `ksEntropySeq_succ_eq_add_condEntropyGivenPartition` / `ksEntropySeq_succ_eq_add_condEntropy` —
  the **integrated (entropy-level) chain rule** `H(⋁₀ⁿ) = H(⋁₀ⁿ⁻¹) + H(P | σ(T⁻¹⋁₀ⁿ⁻¹))`, the
  `μ`-mean of `infoWeight_succ_eq`, with the conditioning in σ-algebra form.
* `ksEntropySeq_eq_sum_condEntropy` — the **telescoped Breiman sum**
  `H(⋁₀ⁿ⁻¹) = ∑_{k<n} H(P | σ(T⁻¹⋁₀ᵏ⁻¹))`.
* `ksEntropyPartition_eq_condEntropy_iSup` — the **sharp Kolmogorov–Sinai rate as a conditional
  entropy**: `h(P,T) = H(P | ⋁_{j≥1} T⁻ʲP)`, the integral-level SMB rate (the `∫ g = h` that the
  pointwise a.e. theorem converges to), proved *unconditionally* via the telescoped sum + the
  fixed-partition Lévy theorem `condEntropy_tendsto_iSup` + the Cesàro mean `Filter.Tendsto.cesaro`.

## The pointwise a.e. SMB (now proved downstream)

The **pointwise a.e.** convergence `(1/n)·iₙ(x) → h(P,T)` for `μ`-a.e. `x` under `Ergodic T μ`
is **proved**: as `ErgodicTheory.Krieger.UpperSMB.ae_tendsto_div_infoFun_self` for the concrete
information function, and — parameterized by the Breiman telescoping — as
`ErgodicTheory.Krieger.SMBLeaves.ae_tendsto_div_infoFun`. By the integral-level identity above the
*target* `h` is `ksEntropyPartition_eq_condEntropy_iSup`; the a.e. statement decomposes into
(with `gₖ` the conditional information *function*):

* **R3/R4 (a.e. main term).** `(1/n)∑_{j<n} g_∞(Tʲx) → ∫ g_∞ = h` a.e., from
  `tendsto_birkhoffAverage_ae_integral` and `ksEntropyPartition_eq_condEntropy_iSup` (`∫ g_∞ = h`).
  The a.e. Lévy limit `gₖ → g_∞` is `MeasureTheory.tendsto_ae_condExp` (used inside
  `condEntropy_tendsto_iSup`).
* **R5 (Chung `L¹` maximal domination — now proved).** The Cesàro tail
  `(1/n)∑_{j<n}(g_{n-j} − g_∞)(Tʲx) → 0` a.e. needs `g* := ⨆ₖ gₖ ∈ L¹(μ)`. The per-cell maximal
  estimate `μ{x ∈ Pᵢ : g* > λ} ≤ e^{−λ}` (a Doob stopping-time bound on the conditional-probability
  martingale `pₖ = E(𝟙_{Pᵢ}|Cₖ)`: on `{τ = first k with pₖ < e^{−λ}} ∈ Cₖ`,
  `μ(Pᵢ ∩ {τ=k}) = ∫_{τ=k} pₖ ≤ e^{−λ}μ(τ=k)`) gives, by the layer-cake formula, `g* ∈ L¹`.
  This is discharged in `ErgodicTheory.Krieger.SMBLeaves` as `chungTail` +
  `lintegral_condInfoMaxFun_lt_top`, whence the Maker/Breiman tail `makerTail` and, downstream, the
  in-measure bound `ErgodicTheory.Krieger.UpperSMB.upperSMBInMeasure_of_ergodic`.

## References

* M. Einsiedler, E. Lindenstrauss, T. Ward, *Entropy in Ergodic Theory and Topological Dynamics*,
  Ch. 2 (SMB).
* H. Bruin, *Ergodic Theory I* (Univ. Wien), Lecture 15 (the telescoping/Breiman proof).
* L. Breiman, *The individual ergodic theorem of information theory*, Ann. Math. Statist.
  **28** (1957), 809–811; correction **31** (1960), 809–810.
* K. L. Chung, *A note on the ergodic theorem of information theory*, Ann. Math. Statist.
  **32** (1961), 612–614.  (The `L¹` maximal domination.)
-/

open MeasureTheory Filter Topology Real Function
open scoped ENNReal

namespace ErgodicTheory.Krieger

open ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [Fintype ι]
  {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

section CondInfoWeight

variable {β : Type*} [Fintype β]

/-- The **conditional information weight** of the `P`-cell index `i` given the `B`-cell index `b`:
the surprise `-log (μ(Bᵦ ∩ Pᵢ)/μ(Bᵦ))` of learning that a point of `Bᵦ` also lies in `Pᵢ`, i.e. the
value of the conditional information function `I_{P | σ(B)}` on the cell `Bᵦ` for a point whose
`P`-cell is `Pᵢ`. Here `B` may have a different (finite) index type than `P`. -/
noncomputable def condInfoWeight (B : MeasurePartition μ β) (P : MeasurePartition μ ι)
    (i : ι) (b : β) : ℝ :=
  -Real.log ((μ (B.cells b ∩ P.cells i)).toReal / (μ (B.cells b)).toReal)

/-- The conditional information weight is nonnegative: the conditional probability
`μ(Bᵦ ∩ Pᵢ)/μ(Bᵦ)` lies in `[0,1]`, so its log is nonpositive. -/
lemma condInfoWeight_nonneg (B : MeasurePartition μ β) (P : MeasurePartition μ ι) (i : ι) (b : β) :
    0 ≤ condInfoWeight B P i b := by
  rw [condInfoWeight, neg_nonneg]
  rcases eq_or_ne (μ (B.cells b)) 0 with h0 | h0
  · rw [h0, ENNReal.toReal_zero, div_zero, Real.log_zero]
  · refine Real.log_nonpos (by positivity) ?_
    rw [div_le_one_iff]
    refine Or.inl ⟨?_, ?_⟩
    · rw [ENNReal.toReal_pos_iff]
      exact ⟨pos_iff_ne_zero.mpr h0, measure_lt_top μ _⟩
    · exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.inter_subset_left)

end CondInfoWeight

section Telescope

omit [IsProbabilityMeasure μ] in
/-- **Cons-factorization of the flat-join cell.** The cell of the `(n+1)`-fold iterated join at the
code `Fin.cons i₀ g` is the `P`-cell `i₀` (the `0`-th symbol) intersected with the `T`-pullback of
the `n`-fold join cell at `g` (the future symbols). This is the cell-level form of
`⋁₀ⁿ T⁻ᵏP = P ∨ T⁻¹(⋁₀ⁿ⁻¹ T⁻ᵏP)`. -/
lemma ksJoinCells_cons (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)
    (i₀ : ι) (g : Fin n → ι) :
    (ksJoin hT P (n + 1)).cells (Fin.cons i₀ g)
      = P.cells i₀ ∩ T ⁻¹' (ksJoin hT P n).cells g := by
  simp only [ksJoin_cells, ksJoinCells_apply, Set.preimage_iInter]
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    refine ⟨?_, fun k => ?_⟩
    · -- The `0`-th coordinate: `T^[0] x = x ∈ P.cells (cons i₀ g 0) = P.cells i₀`.
      have h0 := h 0
      simpa using h0
    · -- The `(k+1)`-th coordinate: `T^[k+1] x = T^[k] (T x) ∈ P.cells (cons i₀ g k.succ)`.
      have hk := h k.succ
      rw [Fin.cons_succ, Fin.val_succ, Function.iterate_succ_apply] at hk
      exact hk
  · rintro ⟨h0, h⟩ k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa using h0
    · rw [Fin.cons_succ, Fin.val_succ, Function.iterate_succ_apply]
      exact h j

/-- **One-step telescoping factorization of the information weight.** Peeling the first symbol of
the `(n+1)`-step coding splits the iterated-join information weight into the `n`-step weight of the
*future* coding `g` plus the conditional information weight of the first symbol `i₀` given the
`T`-pullback of the `n`-step past:
`infoWeight_{n+1}(cons i₀ g) = infoWeight_n(g) + condInfoWeight (T⁻¹(⋁₀ⁿ⁻¹)) P i₀ g`.

This is the pure measure-algebra core of the Breiman identity `iₙ = ∑_{j<n} g_{n-j}∘Tʲ`. It rests
on the cell factorization `ksJoinCells_cons`, the measure-preservation of `T` (so the past cell has
the same measure before and after pulling back along `T`), and the additivity of `-log` on the
product `μ(Pᵢ₀ ∩ T⁻¹C) = (μ(T⁻¹C ∩ Pᵢ₀)/μ(T⁻¹C)) · μ(T⁻¹C)`.

**The positivity hypothesis `hpos : μ(Pᵢ₀ ∩ T⁻¹C) ≠ 0` is load-bearing**: at a code whose
`(n+1)`-cell is null but whose `n`-past cell is not, the `-log`s do not split additively
(`-log 0 = 0` is a junk value), so the identity is *false* there. This is exactly why the
telescoping identity for the *information functions* holds only `μ`-a.e.: the codes realised by
points all have positive-measure cells off a null set. -/
lemma infoWeight_succ_eq (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ)
    (i₀ : ι) (g : Fin n → ι)
    (hpos : μ (P.cells i₀ ∩ T ⁻¹' (ksJoin hT P n).cells g) ≠ 0) :
    infoWeight hT P (n + 1) (Fin.cons i₀ g)
      = infoWeight hT P n g
        + condInfoWeight ((ksJoin hT P n).pullback hT) P i₀ g := by
  -- Abbreviate the past cell `C` and its `T`-pullback `D = T⁻¹ C` (the `B`-cell of `g`).
  set C : Set α := (ksJoin hT P n).cells g with hC
  have hCmeas : MeasurableSet C := (ksJoin hT P n).measurable g
  -- `B`-cell of `g` is `T⁻¹ C`, with the same measure as `C` by measure-preservation.
  have hBcell : ((ksJoin hT P n).pullback hT).cells g = T ⁻¹' C := by
    rw [MeasurePartition.pullback_cells]
  have hmeasD : μ (T ⁻¹' C) = μ C := hT.measure_preimage hCmeas.nullMeasurableSet
  -- The `(n+1)`-cell, by the cons factorization.
  have hcell : (ksJoin hT P (n + 1)).cells (Fin.cons i₀ g) = P.cells i₀ ∩ T ⁻¹' C :=
    ksJoinCells_cons hT P n i₀ g
  -- From `hpos` (intersection nonnull): both the `(n+1)`-cell and the past cell are positive.
  have hDP0 : μ (P.cells i₀ ∩ T ⁻¹' C) ≠ 0 := hpos
  have hD0 : μ (T ⁻¹' C) ≠ 0 := fun h =>
    hDP0 (measure_mono_null Set.inter_subset_right h)
  -- Real-valued measures of the three relevant sets.
  have hDpos : (0 : ℝ) < (μ (T ⁻¹' C)).toReal := by
    rw [ENNReal.toReal_pos_iff]; exact ⟨pos_iff_ne_zero.mpr hD0, measure_lt_top μ _⟩
  have hDne : (μ (T ⁻¹' C)).toReal ≠ 0 := hDpos.ne'
  have hIPne : (μ (T ⁻¹' C ∩ P.cells i₀)).toReal ≠ 0 := by
    rw [ne_eq, ENNReal.toReal_eq_zero_iff, not_or, Set.inter_comm]
    exact ⟨hDP0, measure_ne_top μ _⟩
  -- The key scalar log-identity: `-log(num) = -log(d) + (-log(num/d))`, with `num = μ(Pᵢ₀∩T⁻¹C)`,
  -- `d = μ(T⁻¹C)`, using `log(num/d) = log num - log d` (`Real.log_div`, all factors nonzero) and
  -- `μ(T⁻¹C) = μ C`. The intersection commutes between the two written forms of `num`.
  have hnumcomm : (μ (P.cells i₀ ∩ T ⁻¹' C)).toReal = (μ (T ⁻¹' C ∩ P.cells i₀)).toReal := by
    rw [Set.inter_comm]
  have hkey : -Real.log (μ (P.cells i₀ ∩ T ⁻¹' C)).toReal
      = -Real.log (μ C).toReal
        + -Real.log ((μ (T ⁻¹' C ∩ P.cells i₀)).toReal / (μ (T ⁻¹' C)).toReal) := by
    rw [hnumcomm, Real.log_div hIPne hDne, ← hmeasD]
    ring
  -- Assemble: rewrite the two `infoWeight`s and the `condInfoWeight` and apply `hkey`.
  rw [infoWeight, infoWeight, condInfoWeight, hBcell, hcell]
  exact hkey

end Telescope

section IntegratedChainRule

open ErgodicTheory.Entropy

/-- **Integrated (entropy-level) telescoping chain rule.** The `(n+1)`-step join entropy splits as
the `n`-step join entropy of the *future* plus the conditional entropy of `P` given the `T`-pullback
`B := T⁻¹(⋁₀ⁿ⁻¹ T⁻ᵏP)` of the `n`-step past, *additive over the cells of `B`*:
`H(⋁₀ⁿ T⁻ᵏP) = H(⋁₀ⁿ⁻¹ T⁻ᵏP) + Hₐdd(P | T⁻¹(⋁₀ⁿ⁻¹ T⁻ᵏP))`.

This is the `μ`-integral of the pointwise one-step factorization `infoWeight_succ_eq`, obtained
cleanly from the absolute chain rule `entropy_join_eq_add_condEntropyGivenPartition` applied to the
join `B ∨ P` (which, reindexed by `g' ↦ (tail g', head g')`, is the `(n+1)`-fold join) together
with the `T`-invariance of join entropy (`entropy_pullback`). -/
theorem ksEntropySeq_succ_eq_add_condEntropyGivenPartition (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P (n + 1)
      = ksEntropySeq hT P n
        + condEntropyGivenPartition μ ((ksJoin hT P n).pullback hT).cells P.cells := by
  -- `B := T⁻¹(⋁₀ⁿ⁻¹ T⁻ᵏP)`, the `T`-pullback of the `n`-fold join.
  set B : MeasurePartition μ (Fin n → ι) := (ksJoin hT P n).pullback hT with hB
  -- Reindexing `(g, i₀) ↦ Fin.cons i₀ g : (Fin n → ι) × ι ≃ (Fin (n+1) → ι)`.
  set e : (Fin n → ι) × ι ≃ (Fin (n + 1) → ι) :=
    (Equiv.prodComm (Fin n → ι) ι).trans (Fin.consEquiv (fun _ => ι)) with he
  -- Under `e`, the `(n+1)`-cell is the `B ∨ P` join cell (intersection commuted).
  have hcelleq : ∀ p : (Fin n → ι) × ι,
      (ksJoin hT P (n + 1)).cells (e p) = joinCells B.cells P.cells p := by
    rintro ⟨g, i₀⟩
    have hep : e (g, i₀) = Fin.cons i₀ g := rfl
    rw [hep, joinCells_apply, hB, MeasurePartition.pullback_cells,
      ksJoinCells_cons hT P n i₀ g, Set.inter_comm (P.cells i₀)]
  -- Reindex `(n+1)`-join entropy as `entropy (joinCells B.cells P.cells)`.
  have hreindex : ksEntropySeq hT P (n + 1)
      = entropy μ (joinCells B.cells P.cells) := by
    rw [ksEntropySeq, ← entropy_reindex μ e (ksJoin hT P (n + 1)).cells, entropy_def, entropy_def]
    exact Finset.sum_congr rfl fun p _ => by rw [hcelleq p]
  -- Absolute chain rule `H(B ∨ P) = H(B) + Hₐdd(P | B)`, plus `H(B) = H(⋁₀ⁿ⁻¹)` (`T`-invariance).
  rw [hreindex, entropy_join_eq_add_condEntropyGivenPartition B P, ksEntropySeq, hB,
    entropy_pullback]

variable [StandardBorelSpace α]

/-- **Integrated telescoping chain rule, σ-algebra form.** Bridging the additive-over-cells
conditional entropy of `ksEntropySeq_succ_eq_add_condEntropyGivenPartition` to the σ-algebra
conditional entropy via `condEntropyGivenPartition_eq_condEntropy_generated`, the `(n+1)`-step join
entropy splits as
`H(⋁₀ⁿ T⁻ᵏP) = H(⋁₀ⁿ⁻¹ T⁻ᵏP) + H(P | σ(T⁻¹(⋁₀ⁿ⁻¹ T⁻ᵏP)))`,
where the conditioning σ-algebra is the one generated by the cells of the `T`-pullback of the
`n`-step past join. This is the entropy-level Breiman telescoping with the conditioning expressed in
the form consumed by the fixed-partition Lévy theorem `condEntropy_tendsto_iSup`. -/
theorem ksEntropySeq_succ_eq_add_condEntropy (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P (n + 1)
      = ksEntropySeq hT P n
        + condEntropy μ (generatedSigmaAlgebra μ ((ksJoin hT P n).pullback hT)) P.cells := by
  rw [ksEntropySeq_succ_eq_add_condEntropyGivenPartition hT P n,
    condEntropyGivenPartition_eq_condEntropy_generated ((ksJoin hT P n).pullback hT) P.cells
      P.measurable]

/-- **Telescoped Breiman sum (entropy level).** Iterating the σ-algebra chain rule, the `n`-step
join entropy is the sum of the conditional entropies of `P` given the `T`-pullback of the `k`-step
past, for `k = 0, …, n-1`:
`H(⋁₀ⁿ⁻¹ T⁻ᵏP) = ∑_{k<n} H(P | σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP)))`.

Each summand `H(P | σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP)))` is `condEntropy μ (σ(T⁻¹ ksJoin P k)) P.cells`, the
conditional entropy of `P` given the `k`-step *future* past — a decreasing sequence in `k` (more
conditioning), converging to the relative entropy rate `h(P,T)` by `condEntropy_tendsto_iSup`. This
is the integral-level statement of the Breiman telescoping `iₙ = ∑_{j<n} g_{n-j}∘Tʲ` (its `μ`-mean),
and combined with the Fekete limit it identifies `h(P,T) = lim_k H(P | σ(T⁻¹(⋁₀ᵏ⁻¹))) ` (a Cesàro
mean of a convergent sequence converges to the same limit). -/
theorem ksEntropySeq_eq_sum_condEntropy (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P n
      = ∑ k ∈ Finset.range n,
          condEntropy μ (generatedSigmaAlgebra μ ((ksJoin hT P k).pullback hT)) P.cells := by
  induction n with
  | zero => rw [ksEntropySeq_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [ksEntropySeq_succ_eq_add_condEntropy hT P n, ih, Finset.sum_range_succ]

end IntegratedChainRule

section SharpRateIdentity

open ErgodicTheory.Entropy

variable [StandardBorelSpace α]

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] in
/-- The generated σ-algebra of the (Fekete) `pullback` partition coincides with that of the
(factor) `pulledBack` partition: both have the cells `i ↦ T⁻¹' R.cells i`, and the generated
σ-algebra depends only on the range of the cells. -/
lemma generatedSigmaAlgebra_pullback_eq_pulledBack {β : Type*} [Fintype β]
    (hT : MeasurePreserving T μ μ) (R : MeasurePartition μ β) :
    generatedSigmaAlgebra μ (R.pullback hT) = generatedSigmaAlgebra μ (R.pulledBack hT) := by
  rw [generatedSigmaAlgebra, generatedSigmaAlgebra, MeasurePartition.pullback_cells,
    MeasurePartition.pulledBack_cells]

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] in
/-- The conditioning σ-algebras `σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP))` of the Breiman telescoping form an
*increasing* sequence in `k`: the `(k+1)`-step past join refines the `k`-step one, and `T`-pullback
preserves refinement. -/
lemma generatedSigmaAlgebra_pullback_ksJoin_mono (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) :
    Monotone fun k => generatedSigmaAlgebra μ ((ksJoin hT P k).pullback hT) := by
  intro M n hMn
  simp only
  rw [generatedSigmaAlgebra_pullback_eq_pulledBack hT (ksJoin hT P M),
    generatedSigmaAlgebra_pullback_eq_pulledBack hT (ksJoin hT P n),
    comap_generatedSigmaAlgebra_pulledBack hT (ksJoin hT P M),
    comap_generatedSigmaAlgebra_pulledBack hT (ksJoin hT P n)]
  exact MeasurableSpace.comap_mono (generatedSigmaAlgebra_ksJoin_mono hT P hMn)

/-- **The sharp Kolmogorov–Sinai rate as a conditional entropy (integral-level SMB rate).**
The Kolmogorov–Sinai entropy `h(P,T)` equals the conditional Shannon entropy of `P` given the
σ-algebra of the **strict future** `⨆ₖ σ(T⁻¹(⋁₀ᵏ⁻¹ T⁻ʲP)) = σ(⋁_{j≥1} T⁻ʲP)`:
`h(P,T) = H(P | ⋁_{j≥1} T⁻ʲP)`.

This is the integral-level statement of the sharp SMB rate (the `μ`-mean of the pointwise Breiman
identity `iₙ/n → h`), and the precise identity `∫ g = h` that the pointwise a.e. theorem
converges to. It is assembled, *unconditionally* (no ergodicity, no maximal-function domination),
from the telescoped Breiman sum `ksEntropySeq_eq_sum_condEntropy`, the fixed-partition Lévy theorem
`condEntropy_tendsto_iSup` applied to the increasing conditioning family
(`generatedSigmaAlgebra_pullback_ksJoin_mono`), and the Cesàro convergence
`Filter.Tendsto.cesaro` — the average of a convergent sequence has the same limit — matched against
the Fekete limit `tendsto_ksEntropySeq`. -/
theorem ksEntropyPartition_eq_condEntropy_iSup [Nonempty ι] (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) :
    ksEntropyPartition hT P
      = condEntropy μ (⨆ k, generatedSigmaAlgebra μ ((ksJoin hT P k).pullback hT)) P.cells := by
  -- The conditioning family and its limit conditional entropy.
  set 𝒜seq : ℕ → MeasurableSpace α :=
    fun k => generatedSigmaAlgebra μ ((ksJoin hT P k).pullback hT) with h𝒜
  have hmono : Monotone 𝒜seq := generatedSigmaAlgebra_pullback_ksJoin_mono hT P
  have hle : ∀ k, 𝒜seq k ≤ mα := fun k => generatedSigmaAlgebra_le _
  -- Lévy: the per-`k` conditional entropies converge to the conditional entropy given the iSup.
  have hlevy : Tendsto (fun k => condEntropy μ (𝒜seq k) P.cells) atTop
      (𝓝 (condEntropy μ (⨆ k, 𝒜seq k) P.cells)) :=
    condEntropy_tendsto_iSup 𝒜seq hmono hle P
  -- Cesàro: the average of those conditional entropies has the same limit.
  have hcesaro := Filter.Tendsto.cesaro hlevy
  -- The Cesàro average is exactly `ksEntropySeq n / n` by the telescoped Breiman sum.
  have havg : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, condEntropy μ (𝒜seq k) P.cells
      = ksEntropySeq hT P n / n := by
    intro n
    rw [ksEntropySeq_eq_sum_condEntropy hT P n, div_eq_inv_mul]
  -- So `ksEntropySeq n / n → condEntropy μ (⨆ k, 𝒜seq k) P.cells`; it also `→ h` by Fekete.
  have hfekete := tendsto_ksEntropySeq hT P
  have hlim : Tendsto (fun n => ksEntropySeq hT P n / n) atTop
      (𝓝 (condEntropy μ (⨆ k, 𝒜seq k) P.cells)) := by
    refine hcesaro.congr fun n => havg n
  exact tendsto_nhds_unique hfekete hlim

end SharpRateIdentity

end ErgodicTheory.Krieger
