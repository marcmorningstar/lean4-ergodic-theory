/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropySystem
import ErgodicTheory.Entropy.KSEntropyMono
import ErgodicTheory.Entropy.AbramovRokhlinPartition
import ErgodicTheory.Entropy.ProductRectangleEntropy
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The discrete entropy power rule `h(Tⁿ) = n · h(T)`

For a measure-preserving transformation `T` of a probability space and every `n : ℕ`, the
Kolmogorov–Sinai entropy of the `n`-th iterate is `n` times the entropy of `T`:

`h(Tⁿ) = n · h(T)`  (`ErgodicTheory.Entropy.ksEntropy_iterate`).

This is Walters, *An Introduction to Ergodic Theory*, Theorem 4.13 (in its `EReal`-valued,
non-invertible form; the statement holds for every `n`, including `n = 0`, where both sides are `0`,
and the `⊤` case where both sides are `+∞`). It is consumed by the suspension-flow entropy descent
(#38).

## Proof

The dynamical heart is the **partition-level identity** (for `n ≥ 1`)

`h(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα, Tⁿ) = n · h(α, T)`  (`ksEntropyPartition_iterate_ksJoin`),

proved from the **sequence-level reindexing identity**
`H(⋁ⱼ₌₀ᵐ⁻¹ (Tⁿ)⁻ʲ(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα)) = H(⋁ₗ₌₀ⁿᵐ⁻¹ T⁻ˡα)`
(`ksEntropySeq_iterate_ksJoin`): the double join `⋂ⱼ⋂ᵢ T⁻⁽ⁱ⁺ⁿʲ⁾α` is a reindexing, by the product
equivalence `Fin m × Fin n ≃ Fin (n·m)`, of the flat `nm`-fold join; entropy is invariant under this
reindexing. Composing Fekete limits along the subsequence `m ↦ n·m` yields the `n·` factor.

The two `iSup`-level inequalities `h(Tⁿ) = supₐ h(α, Tⁿ)` versus `n · supₐ h(α, T)` are then

* `h(α, Tⁿ) ≤ h(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα, Tⁿ) = n · h(α, T) ≤ n · h(T)` (refinement monotonicity), and
* `n · h(α, T) = h(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα, Tⁿ) ≤ h(Tⁿ)` (the partition identity fed back into the supremum),

with the scalar factor commuted through the `EReal` supremum via `nsmul_iSup_of_pos` (continuity of
`x ↦ n • x` on `EReal`). The `n = 0` case reduces to `h(id) = 0`.

## Main results

* `ErgodicTheory.Entropy.ksEntropy_iterate`: `h(Tⁿ) = n · h(T)`.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Theorem 4.13.
-/

open MeasureTheory Function Filter Topology

namespace ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  {T : α → α}

/-! ## Commuting `n • ·` through an `EReal` supremum -/

/-- `x ↦ n • x` is monotone on `EReal`. -/
private lemma monotone_nsmul_ereal (n : ℕ) : Monotone (fun x : EReal => n • x) :=
  nsmul_right_mono n

/-- **Commuting a positive scalar through an `EReal` supremum:** `n • (⨆ j, f j) = ⨆ j, n • f j`
for `n ≥ 1`. The map `x ↦ n • x = n · x` is monotone and continuous on `EReal` (its only potential
discontinuity, at `(0, ±∞)`/`(±∞, 0)`, is avoided by the fixed finite nonzero left factor `n`), so
it preserves the supremum (`Monotone.map_ciSup_of_continuousAt`); the empty-index case is handled
directly, as `n • ⊥ = ⊥` for `n ≥ 1`. -/
private lemma nsmul_iSup_of_pos {J : Sort*} {n : ℕ} (hn : 0 < n) (f : J → EReal) :
    n • (⨆ j, f j) = ⨆ j, n • f j := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · haveI := hJ
    rw [iSup_of_empty, iSup_of_empty]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [succ_nsmul, EReal.add_bot]
  · haveI := hJ
    have hne0 : (n : EReal) ≠ 0 := by
      rw [← EReal.coe_natCast]; exact_mod_cast hn.ne'
    have hcont : ContinuousAt (fun x : EReal => n • x) (⨆ j, f j) := by
      have hfun : (fun x : EReal => n • x) = (fun x : EReal => (n : EReal) * x) := by
        funext x; exact EReal.nsmul_eq_mul n x
      rw [hfun]
      have hpair : ContinuousAt (fun x : EReal => ((n : EReal), x)) (⨆ j, f j) := by
        fun_prop
      have hmul : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) ((n : EReal), ⨆ j, f j) := by
        refine EReal.continuousAt_mul (Or.inl hne0) (Or.inl hne0) (Or.inl ?_) (Or.inl ?_)
        · rw [← EReal.coe_natCast]; exact EReal.coe_ne_bot _
        · rw [← EReal.coe_natCast]; exact EReal.coe_ne_top _
      exact hmul.comp hpair
    exact Monotone.map_ciSup_of_continuousAt hcont (monotone_nsmul_ereal n)
      ⟨⊤, fun _ _ => le_top⟩

/-! ## Static and dynamical refinement monotonicity -/

/-- **Static refinement monotonicity of Shannon entropy.** If the partition `A` refines the
partition `B` (each cell `A k` is `μ`-a.e. contained in a single cell `B (g k)`), then
`H(B) ≤ H(A)`. Combine the join lower bound `H(B) ≤ H(B ∨ A)` (`entropy_le_entropy_join`) with the
refinement collapse `H(B ∨ A) = H(A)` (`entropy_joinCells_of_refines`). -/
lemma entropy_le_of_refines {κ : Type*} [Fintype ι] [Fintype κ] (B : MeasurePartition μ ι)
    (A : MeasurePartition μ κ) (g : κ → ι) (hrefine : ∀ k, A.cells k ≤ᵐ[μ] B.cells (g k)) :
    entropy μ B.cells ≤ entropy μ A.cells :=
  (entropy_le_entropy_join B A).trans_eq
    (entropy_joinCells_of_refines B.cells B.measurable B.aedisjoint A.cells g hrefine)

omit [IsProbabilityMeasure μ] in
/-- Cellwise a.e.-refinement is inherited by the iterated joins: if `A` refines `B` via `g`, then
the `m`-fold join `⋁ⱼ S⁻ʲA` refines `⋁ⱼ S⁻ʲB` via `f ↦ g ∘ f`. Preimages under the
measure-preserving iterates `Sʲ` preserve a.e.-containment, and a finite intersection is again an
a.e.-containment (`EventuallyLE.iInter`). -/
lemma ksJoin_cells_ae_le_of_refines {κ : Type*} [Fintype ι] [Fintype κ]
    {S : α → α} (hS : MeasurePreserving S μ μ) (B : MeasurePartition μ ι) (A : MeasurePartition μ κ)
    (g : κ → ι) (hrefine : ∀ k, A.cells k ≤ᵐ[μ] B.cells (g k)) (m : ℕ) (f : Fin m → κ) :
    (ksJoin hS A m).cells f ≤ᵐ[μ] (ksJoin hS B m).cells (fun j => g (f j)) := by
  simp only [ksJoin_cells, ksJoinCells_apply]
  refine EventuallyLE.iInter fun j => ?_
  rw [ae_le_set, ← Set.preimage_diff,
    (hS.iterate (j : ℕ)).measure_preimage
      ((A.measurable (f j)).diff (B.measurable (g (f j)))).nullMeasurableSet, ← ae_le_set]
  exact hrefine (f j)

/-- **Per-`m` dynamical refinement bound:** if `A` refines `B`, then `H(⋁ⱼ S⁻ʲB) ≤ H(⋁ⱼ S⁻ʲA)`. -/
lemma ksEntropySeq_le_of_refines {κ : Type*} [Fintype ι] [Fintype κ]
    {S : α → α} (hS : MeasurePreserving S μ μ) (B : MeasurePartition μ ι) (A : MeasurePartition μ κ)
    (g : κ → ι) (hrefine : ∀ k, A.cells k ≤ᵐ[μ] B.cells (g k)) (m : ℕ) :
    ksEntropySeq hS B m ≤ ksEntropySeq hS A m := by
  simp only [ksEntropySeq]
  exact entropy_le_of_refines (ksJoin hS B m) (ksJoin hS A m) (fun f j => g (f j))
    (fun f => ksJoin_cells_ae_le_of_refines hS B A g hrefine m f)

/-- **Refinement monotonicity of the partition-relative Kolmogorov–Sinai entropy:** if `A` refines
`B`, then `h(B, S) ≤ h(A, S)`. Divide the per-`m` bound `ksEntropySeq_le_of_refines` by `m` and pass
both Fekete limits. -/
lemma ksEntropyPartition_le_of_refines {κ : Type*} [Fintype ι] [Fintype κ]
    {S : α → α} (hS : MeasurePreserving S μ μ) (B : MeasurePartition μ ι) (A : MeasurePartition μ κ)
    (g : κ → ι) (hrefine : ∀ k, A.cells k ≤ᵐ[μ] B.cells (g k)) :
    ksEntropyPartition hS B ≤ ksEntropyPartition hS A := by
  refine le_of_tendsto_of_tendsto' (tendsto_ksEntropySeq hS B) (tendsto_ksEntropySeq hS A) ?_
  intro m
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    exact div_le_div_of_nonneg_right (ksEntropySeq_le_of_refines hS B A g hrefine m) hm0.le

/-! ## Reindexing invariance of `ksEntropyPartition` -/

omit [IsProbabilityMeasure μ] in
/-- Reindexing the underlying partition leaves the iterated-join entropy sequence unchanged. -/
lemma ksEntropySeq_reindex {κ : Type*} [Fintype ι] [Fintype κ] {S : α → α}
    (hS : MeasurePreserving S μ μ) (P : MeasurePartition μ ι) (e : κ ≃ ι) (m : ℕ) :
    ksEntropySeq hS (P.reindex e) m = ksEntropySeq hS P m := by
  simp only [ksEntropySeq]
  rw [← entropy_reindex μ (Equiv.arrowCongr (Equiv.refl (Fin m)) e) (ksJoin hS P m).cells]
  refine congrArg (entropy μ) (funext fun g => ?_)
  simp only [ksJoin_cells, ksJoinCells_apply, MeasurePartition.reindex_cells,
    Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_def, id_eq]

/-- **Reindexing invariance of `ksEntropyPartition`.** -/
lemma ksEntropyPartition_reindex {κ : Type*} [Fintype ι] [Fintype κ] {S : α → α}
    (hS : MeasurePreserving S μ μ) (P : MeasurePartition μ ι) (e : κ ≃ ι) :
    ksEntropyPartition hS (P.reindex e) = ksEntropyPartition hS P :=
  Subadditive.lim_eq_of_eq (ksSubadditive hS (P.reindex e)) (ksSubadditive hS P)
    (funext fun m => ksEntropySeq_reindex hS P e m)

/-- **The general `le_ksEntropy` bound over an arbitrary finite index:** every partition-relative
entropy `h(Q, S)` is below `h(S)`, without assuming `Q` is `Fin`-indexed. Reindex `Q` to a
`Fin`-indexed partition and invoke `le_ksEntropy`, using reindexing invariance. -/
lemma ksEntropyPartition_coe_le_ksEntropy {κ : Type*} [Fintype κ] {S : α → α}
    (hS : MeasurePreserving S μ μ) (Q : MeasurePartition μ κ) :
    ((ksEntropyPartition hS Q : ℝ) : EReal) ≤ ksEntropy hS := by
  rw [← ksEntropyPartition_reindex hS Q (Fintype.equivFin κ).symm]
  exact le_ksEntropy hS (Q.reindex (Fintype.equivFin κ).symm)

/-! ## The sequence-level and partition-level power identities -/

omit [IsProbabilityMeasure μ] in
/-- **Sequence-level power identity.** The `m`-fold join of the `n`-fold join `⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα` under
`Tⁿ` equals, up to the product reindexing `Fin m × Fin n ≃ Fin (n·m)`, the flat `nm`-fold join of
`α` under `T`; hence their Shannon entropies agree:
`H(⋁ⱼ₌₀ᵐ⁻¹ (Tⁿ)⁻ʲ(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα)) = H(⋁ₗ₌₀ⁿᵐ⁻¹ T⁻ˡα)`. Both cell families reduce to the double
intersection `⋂ⱼ⋂ᵢ T⁻⁽ⁱ⁺ⁿʲ⁾α`, matched under the index equivalence `E`. -/
lemma ksEntropySeq_iterate_ksJoin [Fintype ι] (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) (n m : ℕ) :
    ksEntropySeq (hT.iterate n) (ksJoin hT P n) m = ksEntropySeq hT P (n * m) := by
  simp only [ksEntropySeq]
  set φ : Fin m × Fin n ≃ Fin (n * m) :=
    finProdFinEquiv.trans (finCongr (mul_comm m n)) with hφ_def
  set E : (Fin m → Fin n → ι) ≃ (Fin (n * m) → ι) :=
    { toFun := fun g l => g (φ.symm l).1 (φ.symm l).2
      invFun := fun f j i => f (φ (j, i))
      left_inv := fun g => by funext j i; simp only [Equiv.symm_apply_apply]
      right_inv := fun f => by funext l; simp only [Prod.mk.eta, Equiv.apply_symm_apply] }
    with hE_def
  have hφval : ∀ (j : Fin m) (i : Fin n),
      ((φ (j, i) : Fin (n * m)) : ℕ) = (i : ℕ) + n * (j : ℕ) := by
    intro j i
    rw [hφ_def]
    simp only [Equiv.trans_apply, finCongr_apply]
    rfl
  have hprod : ∀ (H : Fin m × Fin n → Set α), (⋂ p, H p) = ⋂ j, ⋂ i, H (j, i) := by
    intro H; ext x; simp only [Set.mem_iInter, Prod.forall]
  rw [← entropy_reindex μ E (ksJoin hT P (n * m)).cells]
  refine congrArg (entropy μ) (funext fun g => ?_)
  have hEval : ∀ (j : Fin m) (i : Fin n), E g (φ (j, i)) = g j i := by
    intro j i
    rw [hE_def]
    simp only [Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  have hLHS : (ksJoin (hT.iterate n) (ksJoin hT P n) m).cells g
      = ⋂ (j : Fin m), ⋂ (i : Fin n), (T^[(i : ℕ) + n * (j : ℕ)])⁻¹' P.cells (g j i) := by
    simp only [ksJoin_cells, ksJoinCells_apply]
    refine Set.iInter_congr fun j => ?_
    rw [Set.preimage_iInter]
    refine Set.iInter_congr fun i => ?_
    rw [← Set.preimage_comp, ← Function.iterate_mul, ← Function.iterate_add]
  have hRHS : (ksJoin hT P (n * m)).cells (E g)
      = ⋂ (j : Fin m), ⋂ (i : Fin n), (T^[(i : ℕ) + n * (j : ℕ)])⁻¹' P.cells (g j i) := by
    simp only [ksJoin_cells, ksJoinCells_apply]
    rw [show (⋂ l : Fin (n * m), (T^[(l : ℕ)])⁻¹' P.cells (E g l))
        = ⋂ p : Fin m × Fin n, (T^[((φ p : Fin (n * m)) : ℕ)])⁻¹' P.cells (E g (φ p)) from
      Set.iInter_congr_of_surjective φ.symm φ.symm.surjective
        (fun l => by rw [Equiv.apply_symm_apply])]
    rw [hprod fun p => (T^[((φ p : Fin (n * m)) : ℕ)])⁻¹' P.cells (E g (φ p))]
    refine Set.iInter_congr fun j => Set.iInter_congr fun i => ?_
    rw [hφval j i, hEval j i]
  rw [hLHS, hRHS]

/-- **Partition-level power identity** (`n ≥ 1`): `h(⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏα, Tⁿ) = n · h(α, T)`.

The averaged sequence `m ↦ H(⋁ⱼ (Tⁿ)⁻ʲ(⋁ₖ T⁻ᵏα)) / m` converges to the left-hand side (Fekete),
and by `ksEntropySeq_iterate_ksJoin` it equals `m ↦ H(⋁ₗ T⁻ˡα)_{l < nm} / m = n · (H(...)_{l<nm} /
(nm))`, whose right factor converges to `h(α, T)` along the subsequence `m ↦ n·m`. Uniqueness of
limits pins the identity. -/
lemma ksEntropyPartition_iterate_ksJoin [Fintype ι] (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {n : ℕ} (hn : 0 < n) :
    ksEntropyPartition (hT.iterate n) (ksJoin hT P n) = (n : ℝ) * ksEntropyPartition hT P := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have L1 : Tendsto (fun m => ksEntropySeq hT P (n * m) / (m : ℝ)) atTop
      (𝓝 (ksEntropyPartition (hT.iterate n) (ksJoin hT P n))) := by
    refine (tendsto_ksEntropySeq (hT.iterate n) (ksJoin hT P n)).congr fun m => ?_
    rw [ksEntropySeq_iterate_ksJoin hT P n m]
  have hnm : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => le_mul_of_one_le_left (Nat.zero_le m) hn) tendsto_id
  have hsub : Tendsto (fun m => ksEntropySeq hT P (n * m) / (↑(n * m) : ℝ)) atTop
      (𝓝 (ksEntropyPartition hT P)) := (tendsto_ksEntropySeq hT P).comp hnm
  have L2 : Tendsto (fun m => ksEntropySeq hT P (n * m) / (m : ℝ)) atTop
      (𝓝 ((n : ℝ) * ksEntropyPartition hT P)) := by
    refine (hsub.const_mul (n : ℝ)).congr fun m => ?_
    rw [Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hnR]
  exact tendsto_nhds_unique L1 L2

/-! ## The entropy power rule -/

/-- **The discrete entropy power rule (Walters, Theorem 4.13):** `h(Tⁿ) = n · h(T)`.

For `n = 0` both sides are `0` (`h(id) = 0`, `ksEntropyPartition_id_eq_zero`). For `n ≥ 1` the two
inequalities of `le_antisymm` are:

* `h(Tⁿ) ≤ n · h(T)`: for each partition `Q`, refinement monotonicity and the partition-level power
  identity give `h(Q, Tⁿ) ≤ h(⋁ₖ T⁻ᵏQ, Tⁿ) = n · h(Q, T) ≤ n · h(T)`;
* `n · h(T) ≤ h(Tⁿ)`: commuting the scalar through the supremum (`nsmul_iSup_of_pos`), each term is
  `n · h(α, T) = h(⋁ₖ T⁻ᵏα, Tⁿ) ≤ h(Tⁿ)` by the partition-level power identity. -/
theorem ksEntropy_iterate (hT : MeasurePreserving T μ μ) (n : ℕ) :
    ksEntropy (hT.iterate n) = n • ksEntropy hT := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_nsmul]
    refine le_antisymm ?_ (ksEntropy_nonneg _)
    refine iSup_le fun m => iSup_le fun Q => ?_
    have h0 : ksEntropyPartition (hT.iterate 0) Q = 0 := ksEntropyPartition_id_eq_zero Q
    rw [h0]; simp
  · refine le_antisymm ?_ ?_
    · -- `h(Tⁿ) ≤ n · h(T)`
      refine iSup_le fun m => iSup_le fun Q => ?_
      have hrefine : ∀ f : Fin n → Fin m,
          (ksJoin hT Q n).cells f ≤ᵐ[μ] Q.cells (f ⟨0, hn⟩) := by
        intro f
        have hsub : (ksJoin hT Q n).cells f ⊆ Q.cells (f ⟨0, hn⟩) := by
          simp only [ksJoin_cells, ksJoinCells_apply]
          refine (Set.iInter_subset _ (⟨0, hn⟩ : Fin n)).trans ?_
          change (T^[0])⁻¹' Q.cells (f ⟨0, hn⟩) ⊆ Q.cells (f ⟨0, hn⟩)
          simp [Function.iterate_zero, Set.preimage_id]
        exact hsub.eventuallyLE
      have hreal : ksEntropyPartition (hT.iterate n) Q ≤ (n : ℝ) * ksEntropyPartition hT Q :=
        (ksEntropyPartition_le_of_refines (hT.iterate n) Q (ksJoin hT Q n) (fun f => f ⟨0, hn⟩)
          hrefine).trans_eq (ksEntropyPartition_iterate_ksJoin hT Q hn)
      calc ((ksEntropyPartition (hT.iterate n) Q : ℝ) : EReal)
          ≤ (((n : ℝ) * ksEntropyPartition hT Q : ℝ) : EReal) := EReal.coe_le_coe hreal
        _ = n • ((ksEntropyPartition hT Q : ℝ) : EReal) := by
            rw [← EReal.coe_nsmul, nsmul_eq_mul]
        _ ≤ n • ksEntropy hT := monotone_nsmul_ereal n (le_ksEntropy hT Q)
    · -- `n · h(T) ≤ h(Tⁿ)`
      have hSdef : ksEntropy hT
          = ⨆ m : ℕ, ⨆ P : MeasurePartition μ (Fin m),
              ((ksEntropyPartition hT P : ℝ) : EReal) := rfl
      have hexpand : n • ksEntropy hT
          = ⨆ m : ℕ, ⨆ P : MeasurePartition μ (Fin m),
              n • ((ksEntropyPartition hT P : ℝ) : EReal) := by
        rw [hSdef, nsmul_iSup_of_pos hn]
        exact iSup_congr fun m => nsmul_iSup_of_pos hn _
      rw [hexpand]
      refine iSup_le fun m => iSup_le fun P => ?_
      have hEq : n • ((ksEntropyPartition hT P : ℝ) : EReal)
          = ((ksEntropyPartition (hT.iterate n) (ksJoin hT P n) : ℝ) : EReal) := by
        rw [ksEntropyPartition_iterate_ksJoin hT P hn, ← EReal.coe_nsmul, nsmul_eq_mul]
      rw [hEq]
      exact ksEntropyPartition_coe_le_ksEntropy (hT.iterate n) (ksJoin hT P n)

end ErgodicTheory.Entropy
