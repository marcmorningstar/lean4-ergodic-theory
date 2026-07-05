/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.BernoulliSuspensionFlow
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The constant-roof suspension space is standard Borel

This module proves that the suspension (mapping-torus) space of a **standard Borel** base map under
the **constant roof** `τ ≡ 1` is again a standard Borel space, and specialises this to the
constant-roof Bernoulli suspension `SuspensionSpace biShiftEquiv measurable_oneRoof` over a standard
Borel alphabet.

A quotient by a group action carries the pushforward (coinduced) `MeasurableSpace`, which is *not*
automatically standard Borel. We obtain the property honestly, through the Ambrose–Kakutani
fundamental domain: for `τ ≡ 1` the box under the roof is `X × [0, 1)`, and the quotient projection
restricted to it is a *measurable bijection*. Concretely we build the measurable equivalence

`SuspensionSpace T hτ ≃ᵐ X × ↥(Set.Ico (0 : ℝ) 1)`,

whose forward map is the orbit-invariant *fundamental-domain coordinate*
`[x, s] ↦ (baseIter ⌊s⌋ x, Int.fract s)` and whose inverse is `(x, t) ↦ [x, t]`. Standard
Borelness is then transported across this equivalence (`standardBorelSpace_of_measurableEquiv`,
pulling back the Polish topology along the equivalence), using that `↥(Set.Ico (0 : ℝ) 1)` is
standard Borel (a measurable subset of `ℝ`) and that products of standard Borel spaces are standard
Borel.

## Main definitions

* `ErgodicTheory.suspensionUnitCoord`: the raw fundamental-domain coordinate
  `(x, s) ↦ (baseIter ⌊s⌋ x, Int.fract s)` on `X × ℝ`.
* `ErgodicTheory.suspensionUnitFwd` / `ErgodicTheory.suspensionUnitInv`: the two directions of the
  fundamental-domain coordinate bijection.
* `ErgodicTheory.suspensionUnitMeasurableEquiv`: the measurable equivalence
  `SuspensionSpace T hτ ≃ᵐ X × ↥(Set.Ico (0 : ℝ) 1)` for the constant roof.

## Main results

* `ErgodicTheory.standardBorelSpace_of_measurableEquiv`: a measurable equivalence transports
  `StandardBorelSpace`.
* `ErgodicTheory.standardBorelSpace_suspensionSpace_const_roof`: for `τ ≡ 1` and
  a standard Borel base,
  the suspension space is standard Borel.
* `ErgodicTheory.Multifractal.instStandardBorelSpace_suspensionSpace_bern`: the constant-roof
  Bernoulli
  suspension space `SuspensionSpace biShiftEquiv measurable_oneRoof` is standard Borel (for a
  standard Borel alphabet `α₀`).
-/

open MeasureTheory Set

namespace ErgodicTheory

/-- **A measurable equivalence transports `StandardBorelSpace`.** If `e : α ≃ᵐ β` and `β` is a
standard Borel space, then so is `α`: pull back a compatible Polish topology along `e` (the induced
topology), under which `e` is a topological embedding, so `α` is Polish and its measurable space is
the Borel σ-algebra. -/
theorem standardBorelSpace_of_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [hβ : StandardBorelSpace β] (e : α ≃ᵐ β) :
    StandardBorelSpace α := by
  obtain ⟨tβ, hbβ, hpβ⟩ := hβ.polish
  letI : TopologicalSpace β := tβ
  haveI : BorelSpace β := hbβ
  haveI : PolishSpace β := hpβ
  letI : TopologicalSpace α := TopologicalSpace.induced (e : α → β) tβ
  haveI : PolishSpace α := e.toEquiv.polishSpace_induced
  haveI : BorelSpace α := e.measurableEmbedding.borelSpace ⟨rfl⟩
  infer_instance

noncomputable section ConstRoof

open ErgodicTheory.Multifractal

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The **raw fundamental-domain coordinate** on `X × ℝ`: the first coordinate of the
fundamental-domain representative, `baseIter ⌊s⌋ x`, paired with the fractional height
`Int.fract s ∈ [0, 1)`. For the constant roof `τ ≡ 1` this descends through the suspension orbit
quotient (`suspensionUnitFwd`). -/
def suspensionUnitCoord (p : X × ℝ) : X × ↥(Set.Ico (0 : ℝ) 1) :=
  (suspensionBaseProjRaw T hτ p,
    ⟨Int.fract p.2, Set.mem_Ico.mpr ⟨Int.fract_nonneg p.2, Int.fract_lt_one p.2⟩⟩)

/-- The raw fundamental-domain coordinate is measurable: its first component is the measurable raw
base projection and its second is the measurable fractional part landing in the interval subtype. -/
theorem measurable_suspensionUnitCoord : Measurable (suspensionUnitCoord T hτ) := by
  unfold suspensionUnitCoord
  exact (measurable_suspensionBaseProjRaw T hτ).prodMk
    ((measurable_fract.comp measurable_snd).subtype_mk)

/-- For the constant roof `τ ≡ 1`, the signed roof Birkhoff sum is the index: `τ⁽ⁿ⁾ x = n`. -/
theorem roofSum_oneRoof (hτ1 : τ = fun _ => (1 : ℝ)) (n : ℤ) (x : X) :
    roofSum T hτ n x = (n : ℝ) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hone : τ (baseIter T hτ (k : ℤ) x) = 1 := congrFun hτ1 _
    rw [roofSum_add_one, ih, hone]; push_cast; ring
  | pred k ih =>
    have hone : τ (baseIter T hτ (-(k : ℤ) - 1) x) = 1 := congrFun hτ1 _
    have h := roofSum_add_one T hτ (-(k : ℤ) - 1) x
    rw [show (-(k : ℤ) - 1 + 1) = -(k : ℤ) by ring, ih, hone] at h
    push_cast at h ⊢
    linarith

/-- For the constant roof `τ ≡ 1`, the raw fundamental-domain coordinate is invariant under the
suspension orbit generator `G (x, s) = (T x, s − 1)`. The first coordinate is invariant by
`suspensionBaseProjRaw_gen`; the second because `Int.fract (s − 1) = Int.fract s`. -/
theorem suspensionUnitCoord_gen (hτ1 : τ = fun _ => (1 : ℝ)) (p : X × ℝ) :
    suspensionUnitCoord T hτ (suspensionGen T hτ p) = suspensionUnitCoord T hτ p := by
  refine Prod.ext ?_ ?_
  · exact suspensionBaseProjRaw_gen T hτ hτ1 p
  · apply Subtype.ext
    obtain ⟨x, s⟩ := p
    change Int.fract (s - τ x) = Int.fract s
    rw [hτ1]
    exact Int.fract_sub_one s

/-- The same invariance under the inverse generator, obtained from `suspensionUnitCoord_gen`. -/
theorem suspensionUnitCoord_gen_symm (hτ1 : τ = fun _ => (1 : ℝ)) (p : X × ℝ) :
    suspensionUnitCoord T hτ ((suspensionGen T hτ).symm p) = suspensionUnitCoord T hτ p := by
  have h := suspensionUnitCoord_gen T hτ hτ1 ((suspensionGen T hτ).symm p)
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm

/-- For the constant roof `τ ≡ 1`, the raw fundamental-domain coordinate is invariant under every
power of the suspension orbit generator, i.e. along the whole `ℤ`-action. -/
theorem suspensionUnitCoord_act (hτ1 : τ = fun _ => (1 : ℝ)) (n : ℤ) (p : X × ℝ) :
    suspensionUnitCoord T hτ (suspensionAct T hτ n p) = suspensionUnitCoord T hτ p := by
  induction n using Int.induction_on with
  | zero => rw [suspensionAct_zero]
  | succ k ih =>
    rw [add_comm, suspensionAct_add, suspensionAct_one, suspensionUnitCoord_gen T hτ hτ1, ih]
  | pred k ih =>
    rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one,
      suspensionUnitCoord_gen_symm T hτ hτ1, ih]

/-- The quotient projection identifies a point with each of its translates along the action:
`[suspensionAct n p] = [p]`. -/
theorem suspensionMk_act (n : ℤ) (p : X × ℝ) :
    suspensionMk T hτ (suspensionAct T hτ n p) = suspensionMk T hτ p := by
  letI := suspensionAddAction T hτ
  exact Quotient.sound ⟨n, suspension_vadd_eq_act T hτ n p⟩

/-- The fundamental-domain representative `(baseIter ⌊s⌋ x, Int.fract s)` lies in the same orbit as
`(x, s)` (for the constant roof), so they have the same quotient class. -/
theorem suspensionMk_unitCoord (hτ1 : τ = fun _ => (1 : ℝ)) (x : X) (s : ℝ) :
    suspensionMk T hτ (baseIter T hτ ⌊s⌋ x, Int.fract s) = suspensionMk T hτ (x, s) := by
  have heq : (baseIter T hτ ⌊s⌋ x, Int.fract s) = suspensionAct T hτ ⌊s⌋ (x, s) := by
    rw [suspensionAct_eq, roofSum_oneRoof T hτ hτ1, Int.self_sub_floor]
  rw [heq]
  exact suspensionMk_act T hτ ⌊s⌋ (x, s)

/-- The **forward fundamental-domain map** `[x, s] ↦ (baseIter ⌊s⌋ x, Int.fract s)`, the descent of
the orbit-invariant raw coordinate `suspensionUnitCoord` through the suspension orbit quotient (for
the constant roof `τ ≡ 1`). -/
def suspensionUnitFwd (hτ1 : τ = fun _ => (1 : ℝ)) :
    SuspensionSpace T hτ → X × ↥(Set.Ico (0 : ℝ) 1) :=
  letI := suspensionAddAction T hτ
  Quotient.lift (suspensionUnitCoord T hτ) fun p q h => by
    obtain ⟨n, hn⟩ := h
    have hn' : suspensionAct T hτ n q = p := hn
    rw [← hn', suspensionUnitCoord_act T hτ hτ1]

/-- The descent identity: `suspensionUnitFwd [p] = suspensionUnitCoord p`. -/
@[simp] theorem suspensionUnitFwd_mk (hτ1 : τ = fun _ => (1 : ℝ)) (p : X × ℝ) :
    suspensionUnitFwd T hτ hτ1 (suspensionMk T hτ p) = suspensionUnitCoord T hτ p := rfl

/-- The forward fundamental-domain map is measurable (measurability out of the quotient is
measurability of the composite with the projection, which is `suspensionUnitCoord`). -/
theorem measurable_suspensionUnitFwd (hτ1 : τ = fun _ => (1 : ℝ)) :
    Measurable (suspensionUnitFwd T hτ hτ1) := by
  letI := suspensionAddAction T hτ
  refine measurable_from_quotient.2 ?_
  exact measurable_suspensionUnitCoord T hτ

/-- The **inverse fundamental-domain map** `(x, t) ↦ [x, t]`, embedding the fundamental domain
`X × [0, 1)` into the suspension quotient. -/
def suspensionUnitInv (y : X × ↥(Set.Ico (0 : ℝ) 1)) : SuspensionSpace T hτ :=
  suspensionMk T hτ (y.1, (y.2 : ℝ))

/-- The inverse fundamental-domain map is measurable. -/
theorem measurable_suspensionUnitInv : Measurable (suspensionUnitInv T hτ) := by
  unfold suspensionUnitInv
  exact (measurable_suspensionMk T hτ).comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

/-- `suspensionUnitInv` is a left inverse of `suspensionUnitFwd`: the fundamental-domain
representative of a class lies in the same class. -/
theorem suspensionUnitInv_fwd (hτ1 : τ = fun _ => (1 : ℝ)) (q : SuspensionSpace T hτ) :
    suspensionUnitInv T hτ (suspensionUnitFwd T hτ hτ1 q) = q := by
  refine Quotient.inductionOn q (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspensionUnitInv T hτ (suspensionUnitFwd T hτ hτ1 (suspensionMk T hτ (x, s)))
    = suspensionMk T hτ (x, s)
  rw [suspensionUnitFwd_mk]
  change suspensionMk T hτ (baseIter T hτ ⌊s⌋ x, Int.fract s) = suspensionMk T hτ (x, s)
  exact suspensionMk_unitCoord T hτ hτ1 x s

/-- `suspensionUnitInv` is a right inverse of `suspensionUnitFwd`: on the fundamental domain
`X × [0, 1)` the floor is `0` and the fractional part is the identity. -/
theorem suspensionUnitFwd_inv (hτ1 : τ = fun _ => (1 : ℝ)) (y : X × ↥(Set.Ico (0 : ℝ) 1)) :
    suspensionUnitFwd T hτ hτ1 (suspensionUnitInv T hτ y) = y := by
  obtain ⟨x, t⟩ := y
  obtain ⟨tv, htv⟩ := t
  change suspensionUnitFwd T hτ hτ1 (suspensionMk T hτ (x, tv)) = (x, ⟨tv, htv⟩)
  rw [suspensionUnitFwd_mk]
  have hfloor : ⌊tv⌋ = 0 := Int.floor_eq_zero_iff.mpr htv
  have hfract : Int.fract tv = tv := Int.fract_eq_self.mpr ⟨htv.1, htv.2⟩
  refine Prod.ext ?_ ?_
  · change baseIter T hτ ⌊tv⌋ x = x
    rw [hfloor]
    change (suspensionAct T hτ 0 (x, (0 : ℝ))).1 = x
    rw [suspensionAct_zero]
  · apply Subtype.ext
    change Int.fract tv = tv
    exact hfract

/-- The **fundamental-domain measurable equivalence** for the constant roof `τ ≡ 1`:
`SuspensionSpace T hτ ≃ᵐ X × ↥(Set.Ico (0 : ℝ) 1)`, with forward map the orbit-invariant
fundamental-domain coordinate and inverse the quotient embedding of the box. -/
def suspensionUnitMeasurableEquiv (hτ1 : τ = fun _ => (1 : ℝ)) :
    SuspensionSpace T hτ ≃ᵐ (X × ↥(Set.Ico (0 : ℝ) 1)) where
  toFun := suspensionUnitFwd T hτ hτ1
  invFun := suspensionUnitInv T hτ
  left_inv := suspensionUnitInv_fwd T hτ hτ1
  right_inv := suspensionUnitFwd_inv T hτ hτ1
  measurable_toFun := measurable_suspensionUnitFwd T hτ hτ1
  measurable_invFun := measurable_suspensionUnitInv T hτ

/-- **The constant-roof suspension of a standard Borel base is standard Borel.** For `τ ≡ 1` the
suspension space is measurably equivalent to `X × ↥(Set.Ico (0 : ℝ) 1)` (the fundamental domain),
which is standard Borel (a product of a standard Borel space with a measurable subset of `ℝ`);
standard Borelness transports across the equivalence. -/
theorem standardBorelSpace_suspensionSpace_const_roof [StandardBorelSpace X]
    (hτ1 : τ = fun _ => (1 : ℝ)) :
    StandardBorelSpace (SuspensionSpace T hτ) := by
  haveI : StandardBorelSpace ↥(Set.Ico (0 : ℝ) 1) := measurableSet_Ico.standardBorel
  exact standardBorelSpace_of_measurableEquiv (suspensionUnitMeasurableEquiv T hτ hτ1)

end ConstRoof

namespace Multifractal

variable {α₀ : Type*} [MeasurableSpace α₀] [StandardBorelSpace α₀]

/-- **The constant-roof Bernoulli suspension space is standard Borel.** For a standard Borel
alphabet `α₀`, the two-sided shift base `BiShift α₀ = (ℤ → α₀)` is standard Borel (a countable
product), so the constant-roof (`τ ≡ 1`) suspension space
`SuspensionSpace biShiftEquiv measurable_oneRoof` is standard Borel by
`standardBorelSpace_suspensionSpace_const_roof`. -/
instance instStandardBorelSpace_suspensionSpace_bern :
    StandardBorelSpace
      (SuspensionSpace (biShiftEquiv (α₀ := α₀)) (measurable_oneRoof (α₀ := α₀))) :=
  standardBorelSpace_suspensionSpace_const_roof biShiftEquiv measurable_oneRoof rfl

end Multifractal

end ErgodicTheory
