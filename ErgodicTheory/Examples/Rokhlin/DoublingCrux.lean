/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.Elementary
import ErgodicTheory.Entropy.KSEntropy

/-!
# The doubling map's binary join cells (dynamical crux)

This module isolates the *dynamical* facts behind Rokhlin's entropy equality for the doubling map
`T : y ↦ 2 • y` on `UnitAddCircle = AddCircle (1 : ℝ)`. Let `α` be the **binary partition**
`{[0,1/2), [1/2,1)}` (the `mk`-images of those half-open real intervals). Its `n`-fold join
`⋁ₖ₌₀ⁿ⁻¹ T⁻ᵏ α` is the partition of the circle into the `2ⁿ` dyadic arcs of length `2⁻ⁿ`.

The crux `volume_binJoinCell` states that **every** cell of that `n`-fold join has volume exactly
`2⁻ⁿ`. Feeding it into the abstract reduction `ksEntropyPartition_of_uniform`
(file `AbstractEqui.lean`) yields `h(α, T) = log 2`.

## Structure of the argument

* `ksJoinCells_succ_head_tail`: the head/tail recursion `Cₙ₊₁,f = α_{f 0} ∩ T⁻¹(Cₙ, tail f)`.
* `mem_binCell_iff`: a circle point lies in `α_i` iff its `[0,1)`-representative lies in
  `binLift i = [i/2,(i+1)/2)`; this turns the `mk`-image cell into a measurable *preimage*.
* `volume_binCell_inter_preimage`: the dynamical heart, `volume (α_i ∩ T⁻¹ B) = volume B / 2`. The
  doubling map restricted to the half-arc `α_i` is the affine `2×`-magnification `x ↦ 2x - i` onto
  the whole circle, so it halves measures. The proof reduces — via the fundamental-domain measure
  formula `volume_eq_preimage_inter_Ico` and `Real.volume_preimage_mul_left` (factor `1/2`) — to
  the `ℤ`-translation invariance of `mk⁻¹' B` (`preimage_mk_add_int_eq`).
* `volume_binJoinCell`: induction on `n` via the head/tail recursion, halving the measure at each
  step from `volume univ = 1`.

For the integral side `∫ log|det D(2x)| dμ = ∫ log 2 = log 2` and the headline equality, see
`ErgodicTheory.Examples.Rokhlin.DoublingEquality`.
-/

open MeasureTheory Function Set
open scoped ENNReal

namespace ErgodicTheory.Examples.Rokhlin

open ErgodicTheory ErgodicTheory.Entropy

/-- Lift of the binary cell `i ∈ {0, 1}` to the fundamental domain `[0, 1)`: the half-open real
interval `[i/2, (i+1)/2)`. -/
noncomputable def binLift (i : Fin 2) : Set ℝ := Ico ((i : ℝ) / 2) (((i : ℝ) + 1) / 2)

/-- The `i`-th cell of the binary partition of the unit circle: the `mk`-image of
`[i/2, (i+1)/2)`. -/
noncomputable def binCell (i : Fin 2) : Set UnitAddCircle :=
  QuotientAddGroup.mk '' binLift i

/-- The canonical `[0,1)`-representative of a circle point: `AddCircle.equivIco 1 0` followed by the
subtype coercion. It is the unique real in `[0,1)` mapping to the given point under `mk`. -/
noncomputable def rep (y : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 0 y : ℝ)

lemma rep_mem_Ico (y : UnitAddCircle) : rep y ∈ Ico (0 : ℝ) 1 := by
  have h : (AddCircle.equivIco 1 0 y : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := (AddCircle.equivIco 1 0 y).2
  simpa only [zero_add] using h

@[simp] lemma mk_rep (y : UnitAddCircle) : (QuotientAddGroup.mk (rep y) : UnitAddCircle) = y :=
  AddCircle.coe_equivIco

lemma rep_coe_of_mem {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    rep (QuotientAddGroup.mk x : UnitAddCircle) = x := by
  have : x ∈ Ico (0 : ℝ) (0 + 1) := by rwa [zero_add]
  rw [rep, AddCircle.equivIco_coe_of_mem this]

/-- The lifted binary interval `[i/2,(i+1)/2)` sits inside the fundamental domain `[0,1)`. -/
lemma binLift_subset_Ico (i : Fin 2) : binLift i ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  simp only [binLift, mem_Ico] at hx
  fin_cases i <;>
    · simp only [mem_Ico] at hx ⊢
      constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]

/-- **Characterization of a binary cell via the canonical representative.** A circle point lies in
`binCell i` iff its `[0,1)`-representative lies in the lifted interval `binLift i = [i/2,(i+1)/2)`.
This turns the `mk`-image cell into a *preimage* of a measurable real set under the measurable map
`rep`, and is the workhorse for measurability, disjointness, and cover. -/
lemma mem_binCell_iff (i : Fin 2) (y : UnitAddCircle) : y ∈ binCell i ↔ rep y ∈ binLift i := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [rep_coe_of_mem (binLift_subset_Ico i hx)]
  · intro hy
    exact ⟨rep y, hy, mk_rep y⟩

/-- **Head/tail decomposition of an iterated-join cell.** Splitting off the `k = 0` factor,
`⋂ₖ₌₀ⁿ T⁻ᵏ(α_{f k}) = α_{f 0} ∩ T⁻¹(⋂ₖ₌₀ⁿ⁻¹ T⁻ᵏ(α_{(tail f) k}))`. The shifted factors at
`k = j+1` are `T⁻¹` of the corresponding `n`-fold-join factor because `T^[j+1] = T^[j] ∘ T`. -/
lemma ksJoinCells_succ_head_tail {ι : Type*} (cells : ι → Set UnitAddCircle)
    (T : UnitAddCircle → UnitAddCircle) (n : ℕ) (f : Fin (n + 1) → ι) :
    ksJoinCells cells T (n + 1) f
      = cells (f 0) ∩ T ⁻¹' ksJoinCells cells T n (Fin.tail f) := by
  ext x
  simp only [ksJoinCells_apply, mem_iInter, mem_inter_iff, mem_preimage]
  rw [Fin.forall_fin_succ]
  refine and_congr ?_ ?_
  · simp only [Function.iterate_zero, id_eq, Fin.val_zero]
  · refine forall_congr' fun k => ?_
    -- `T^[k.succ] x ∈ cells (f k.succ)` ↔ `T^[k] (T x) ∈ cells (Fin.tail f k)`.
    rw [Fin.val_succ, Function.iterate_succ_apply, Fin.tail]

/-! ### Measurability of the binary cells -/

/-- The canonical representative map `rep = Subtype.val ∘ equivIco 1 0` is measurable: it is the
forward map of the measurable equivalence `AddCircle.measurableEquivIco 1 0` post-composed with the
measurable subtype coercion. -/
lemma measurable_rep : Measurable (rep : UnitAddCircle → ℝ) := by
  have h1 : Measurable (AddCircle.measurableEquivIco (1 : ℝ) 0) :=
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  exact measurable_subtype_coe.comp h1

/-- The binary cells are measurable: by `mem_binCell_iff`, `binCell i = rep ⁻¹' binLift i`, the
preimage of the measurable real interval `binLift i` under the measurable map `rep`. -/
lemma measurableSet_binCell (i : Fin 2) : MeasurableSet (binCell i) := by
  have hset : binCell i = rep ⁻¹' binLift i := by
    ext y; rw [mem_binCell_iff]; rfl
  rw [hset]
  exact (measurableSet_Ico).preimage measurable_rep

/-! ### The dynamical half-scaling lemma

The single genuinely-dynamical input: the two doubling-map branches each magnify by `2`, so each
halves measures. -/

/-- The doubling map in `mk`-coordinates: `T (mk x) = mk (2 x)`. -/
lemma doublingMap_mk (x : ℝ) :
    doublingMap (QuotientAddGroup.mk x : UnitAddCircle) = (QuotientAddGroup.mk (2 * x)) := by
  rw [doublingMap, ← AddCircle.coe_nsmul]
  congr 1
  ring

/-- `mk⁻¹' B` is invariant under translation by an integer (here `i ∈ {0,1} ⊆ ℤ`): `mk (x + i) =
mk x`, so `x + i ∈ mk⁻¹' B ↔ x ∈ mk⁻¹' B`. We phrase it as a set translation identity. -/
lemma preimage_mk_add_int_eq {B : Set UnitAddCircle} (k : ℤ) :
    (fun x : ℝ => x + (k : ℝ)) ⁻¹' (QuotientAddGroup.mk ⁻¹' B) = QuotientAddGroup.mk ⁻¹' B := by
  ext x
  simp only [mem_preimage]
  have : (QuotientAddGroup.mk (x + (k : ℝ)) : UnitAddCircle) = QuotientAddGroup.mk x := by
    rw [QuotientAddGroup.mk_add]
    have hk : (QuotientAddGroup.mk ((k : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by simp⟩
    rw [hk, add_zero]
  rw [this]

/-- Fundamental-domain measure formula with the **half-open `[0,1)`** domain (the `Ico` analogue of
`AddCircle.add_projection_respects_measure`): for measurable `U`, `volume U = volume (mk⁻¹' U ∩
[0,1))`. Obtained from the `Ioc 0 1` version by `measure_congr`, since `Ioc 0 1 =ᵐ Ico 0 1`. -/
lemma volume_eq_preimage_inter_Ico {U : Set UnitAddCircle} (hU : MeasurableSet U) :
    volume U = volume (QuotientAddGroup.mk ⁻¹' U ∩ Ico (0 : ℝ) 1) := by
  have hIoc : volume U = volume (QuotientAddGroup.mk ⁻¹' U ∩ Ioc (0 : ℝ) 1) := by
    have := AddCircle.add_projection_respects_measure (T := 1) 0 hU
    simpa using this
  rw [hIoc]
  refine measure_congr ?_
  exact (Filter.EventuallyEq.refl _ _).inter (Ico_ae_eq_Ioc).symm

/-- **Half-scaling under the doubling map.** For any measurable `B ⊆ UnitAddCircle`, the part of
the preimage `T⁻¹ B` lying in the binary half-arc `α_i = binCell i` has exactly half the measure of
`B`. Indeed `T` restricted to `α_i = [i/2,(i+1)/2)` is the affine map `x ↦ 2x - i` onto the whole
circle (a measure `2×`-magnification), so it pulls `B` back to a set of half the measure inside
`α_i`. -/
lemma volume_binCell_inter_preimage (i : Fin 2) {B : Set UnitAddCircle} (hB : MeasurableSet B) :
    volume (binCell i ∩ doublingMap ⁻¹' B) = volume B / 2 := by
  -- Abbreviations: the real lift of `B`, and the real doubling-pullback.
  set P : Set ℝ := QuotientAddGroup.mk ⁻¹' B with hP
  -- Step 1: lift the LHS to the fundamental domain `[0,1)`.
  have hmeasInter : MeasurableSet (binCell i ∩ doublingMap ⁻¹' B) :=
    (measurableSet_binCell i).inter
      (hB.preimage ergodic_doublingMap.toMeasurePreserving.measurable)
  rw [volume_eq_preimage_inter_Ico hmeasInter]
  -- Step 2: identify the lifted set with `binLift i ∩ (2•)⁻¹' P` (exact on `[0,1)`).
  have hset : QuotientAddGroup.mk ⁻¹' (binCell i ∩ doublingMap ⁻¹' B) ∩ Ico (0 : ℝ) 1
      = binLift i ∩ (fun x : ℝ => 2 * x) ⁻¹' P := by
    ext x
    simp only [mem_inter_iff, mem_preimage, hP]
    constructor
    · rintro ⟨⟨hcell, hdb⟩, hx01⟩
      refine ⟨?_, ?_⟩
      · rw [mem_binCell_iff, rep_coe_of_mem hx01] at hcell; exact hcell
      · simp only [doublingMap_mk] at hdb; exact hdb
    · rintro ⟨hbl, hdb⟩
      have hx01 : x ∈ Ico (0 : ℝ) 1 := binLift_subset_Ico i hbl
      refine ⟨⟨?_, ?_⟩, hx01⟩
      · rw [mem_binCell_iff, rep_coe_of_mem hx01]; exact hbl
      · simp only [doublingMap_mk]; exact hdb
  rw [hset]
  -- Step 3: `binLift i = (2•)⁻¹' [i,i+1)`, so the set is `(2•)⁻¹'([i,i+1) ∩ P)`.
  have hbinLift_pre : binLift i = (fun x : ℝ => 2 * x) ⁻¹' Ico (i : ℝ) ((i : ℝ) + 1) := by
    ext x; simp only [binLift, mem_Ico, mem_preimage]; constructor <;> intro h <;>
      constructor <;> linarith [h.1, h.2]
  rw [hbinLift_pre, ← preimage_inter, Real.volume_preimage_mul_left (by norm_num : (2 : ℝ) ≠ 0)]
  -- Step 4: `volume ([i,i+1) ∩ P) = volume B`, by ℤ-translation invariance and the fund. domain.
  have hshift : volume (Ico (i : ℝ) ((i : ℝ) + 1) ∩ P) = volume B := by
    -- Translate by `c = +i` (measure preserving): `{x | x + i ∈ [i,i+1)} = [0,1)`,
    -- and `(·+i)⁻¹' P = P` by integer periodicity, so `[i,i+1) ∩ P ↦ [0,1) ∩ P`.
    have hPshift : (fun x : ℝ => x + (((i : ℤ)) : ℝ)) ⁻¹' P = P :=
      preimage_mk_add_int_eq (i : ℤ)
    have htrans : (fun x : ℝ => x + (((i : ℤ)) : ℝ)) ⁻¹' (Ico (i : ℝ) ((i : ℝ) + 1) ∩ P)
        = Ico (0 : ℝ) 1 ∩ P := by
      rw [preimage_inter, hPshift]
      congr 1
      ext x
      simp only [mem_preimage, mem_Ico]
      push_cast
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have hmp := measurePreserving_add_right (volume : Measure ℝ) (((i : ℤ)) : ℝ)
    have hpre := hmp.measure_preimage (s := Ico (i : ℝ) ((i : ℝ) + 1) ∩ P)
      ((measurableSet_Ico).inter (hB.preimage AddCircle.measurable_mk')).nullMeasurableSet
    rw [htrans] at hpre
    rw [← hpre, volume_eq_preimage_inter_Ico hB, hP, Set.inter_comm]
  rw [hshift]
  -- `ofReal |2⁻¹| * volume B = volume B / 2`.
  rw [show |(2 : ℝ)⁻¹| = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat]
  rw [div_eq_mul_inv, mul_comm]

/-! ### The join cell measure -/

/-- **Every binary `n`-fold-join cell of the doubling map has volume `2⁻ⁿ`.** Induction on `n` using
the head/tail recursion `ksJoinCells_succ_head_tail` and the half-scaling lemma
`volume_binCell_inter_preimage`: the base cell (`n = 0`) is the whole circle of measure `1`, and
each step multiplies the measure by `1/2`. -/
lemma volume_binJoinCell (n : ℕ) (f : Fin n → Fin 2) :
    volume (ksJoinCells binCell doublingMap n f) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  induction n with
  | zero =>
    -- `n = 0`: the empty intersection is the whole space, of measure `1 = (2^0)⁻¹`.
    simp only [ksJoinCells_apply, iInter_of_empty, pow_zero, inv_one]
    exact measure_univ
  | succ m ih =>
    -- Each measurable `m`-fold-join cell has measure `(2^m)⁻¹` (the IH); measurability of the
    -- cell follows from measurability of `binCell` and the measurable iterates of `T`.
    have hmeasCell : MeasurableSet (ksJoinCells binCell doublingMap m (Fin.tail f)) := by
      refine MeasurableSet.iInter fun k => ?_
      exact (measurableSet_binCell _).preimage
        (ergodic_doublingMap.toMeasurePreserving.iterate (k : ℕ)).measurable
    rw [ksJoinCells_succ_head_tail binCell doublingMap m f,
      volume_binCell_inter_preimage (f 0) hmeasCell, ih (Fin.tail f), pow_succ,
      ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp))]
    rw [div_eq_mul_inv]

end ErgodicTheory.Examples.Rokhlin
