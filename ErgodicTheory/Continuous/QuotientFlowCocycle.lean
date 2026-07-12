/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.TwoSided.CocycleZ
import ErgodicTheory.Continuous.Flow
import ErgodicTheory.Continuous.SuspensionFlowMP
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Continuous.SuspensionCoverFlow
import ErgodicTheory.Continuous.SuspensionDescent
import ErgodicTheory.Continuous.SuspensionLapCount
import ErgodicTheory.Continuous.SuspensionFlowExponentQuotient
import Mathlib.MeasureTheory.Function.Floor

/-!
# The genuine quotient `FlowCocycle` on the constant-roof suspension, and its cover cohomology

For an **invertible** measure-preserving base `T : X ≃ᵐ X` under the **constant unit roof** `τ ≡ 1`,
this module assembles the two-sided ℤ-cocycle `ErgodicTheory.cocycleZ` into a genuine
continuous-time `ErgodicTheory.FlowCocycle` on the suspension quotient
`SuspensionSpace T measurable_unitRoof` (the mapping torus), and relates it, over the quotient, to
the cover cocycle
`ErgodicTheory.coverCocycle` on
`X × ℝ`.

## The measurable-trivialization route

For the constant roof the fundamental domain is the box `X × [0, 1)`, and the quotient projection
restricted to it is a *measurable bijection* (`ErgodicTheory.suspensionUnitMeasurableEquiv`,
`ErgodicTheory.Continuous.SuspensionStandardBorel`). This is the measurable trivialization of the
suspension: over a standard Borel base every measurable bundle trivializes, so the flow cocycle can
be read off from a genuine measurable representative `unitFwd q = (baseIter ⌊s⌋ x, Int.fract s)` of
each orbit class `q = [x, s]`. Concretely the flow cocycle at time `t` reads the base laps completed
by the descended flow, namely `cocycleZ A T ⌊(unitFwd q).2 + t⌋ (unitFwd q).1`; the four
`FlowCocycle` fields are the ℤ-cocycle identity `cocycleZ_add` transported through the floor split
`⌊a + t⌋ = ⌊a⌋ + ⌊Int.fract a + t⌋`.

## Cohomology to the cover

Over the quotient the flow cocycle `quotientFlowCocycle` is cohomologous to the cover cocycle: at
the canonical representative it agrees with `coverCocycle` on the nose
(`quotientFlowCocycle_eq_coverCocycle`), and at a *general* representative `(x, s)` (with `0 ≤ s`)
the two differ by the measurable **rep-level frame** `C (x, s) = cocycleZ A T ⌊s⌋ x`
(`quotientFlowCocycle_frame`, packaged existentially as
`exists_flowCocycle_cohomologous_to_cover`). Because the frame is a function of the representative —
different representatives of the same class carry different `⌊s⌋` — a genuine *class*-level
conjugacy (the schematic `B = C ∘ φ_t · cover · C⁻¹`) collapses to the conjugation-free canonical
identity; the honest general statement is the rep-level frame. Finally the exponent transports:
along the (only) `atTop` half-line `0 ≤ t` the flow-cocycle growth rate equals the descended flow
exponent `flowExponentAt` (`flowExponentAt_quotientFlowCocycle`).

The **general non-constant roof is out of scope**: there is no measurable canonical representative
of the orbit quotient in the library for a non-constant roof (cf. the deferred-infrastructure note
in `ErgodicTheory.Continuous.SuspensionCocycle`), so the matrix-level descent is available only
for the constant roof handled here; the exponent alone descends for general bounded roofs
(`ErgodicTheory.flowExponentAt`).

## Main definitions

* `ErgodicTheory.unitFwd`: the measurable fundamental-domain coordinate of an orbit class.
* `ErgodicTheory.quotientFlowCocycle`: the genuine quotient `FlowCocycle` for the unit roof.

## Main results

* `ErgodicTheory.floor_add_split`: `⌊a + t⌋ = ⌊a⌋ + ⌊Int.fract a + t⌋`.
* `ErgodicTheory.lapCount_oneRoof`: for the unit roof, `lapCount t x = ⌊t⌋.toNat` (`0 ≤ t`).
* `ErgodicTheory.quotientFlowCocycle_eq_coverCocycle`: canonical-rep agreement with the cover.
* `ErgodicTheory.quotientFlowCocycle_frame`: the general-rep frame identity.
* `ErgodicTheory.exists_flowCocycle_cohomologous_to_cover`: the existential cohomology headline.
* `ErgodicTheory.flowExponentAt_quotientFlowCocycle`: exponent transport to `flowExponentAt`.
-/

open MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## Floor plumbing -/

/-- The floor split lemma `⌊a + t⌋ = ⌊a⌋ + ⌊Int.fract a + t⌋`. -/
theorem floor_add_split (a t : ℝ) :
    ⌊a + t⌋ = ⌊a⌋ + ⌊Int.fract a + t⌋ := by
  have h : a + t = (⌊a⌋ : ℝ) + (Int.fract a + t) := by
    rw [← add_assoc, Int.floor_add_fract]
  rw [h, Int.floor_intCast_add]

/-! ## The unit-roof return time and lap counter -/

/-- For the constant roof `τ ≡ 1` the `n`-th return time is `n`: `returnTime n x = n`. -/
theorem returnTime_oneRoof (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)
    (hτ1 : τ = fun _ => (1 : ℝ)) (n : ℕ) (x : X) :
    returnTime T hτ n x = (n : ℝ) := by
  unfold returnTime
  rw [roofSum_oneRoof T hτ hτ1]
  simp

/-- **The unit-roof lap counter is a floor.** For the constant roof `τ ≡ 1` and `0 ≤ u`, the number
of base returns completed by flow time `u` is `⌊u⌋.toNat`: the return times are the integers, so the
first-passage index is the integer part of `u`. -/
theorem lapCount_oneRoof (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)
    (hτ1 : τ = fun _ => (1 : ℝ)) {c : ℝ} (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c)
    {u : ℝ} (hu : 0 ≤ u) (x : X) :
    lapCount T hτ hc hcpos u x = ⌊u⌋.toNat := by
  have hle : returnTime T hτ (lapCount T hτ hc hcpos u x) x ≤ u :=
    lapCount_returnTime_le T hτ hc hcpos hu x
  have hgt : u < returnTime T hτ (lapCount T hτ hc hcpos u x + 1) x :=
    lapCount_lt_returnTime_succ T hτ hc hcpos hu x
  rw [returnTime_oneRoof T hτ hτ1] at hle
  rw [returnTime_oneRoof T hτ hτ1] at hgt
  have hfloor : ⌊u⌋ = (lapCount T hτ hc hcpos u x : ℤ) := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast; exact hle
    · push_cast at hgt ⊢; linarith
  rw [hfloor, Int.toNat_natCast]

/-! ## Assembling the `FlowCocycle` (constant roof `τ ≡ 1`) -/

section Assembly

variable (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X ≃ᵐ X)

/-- The constant unit roof function `fun _ : X => (1 : ℝ)` is measurable.  This is the roof used to
build the constant-`1` suspension `SuspensionSpace T measurable_unitRoof` on which the
quotient-level `FlowCocycle` below is defined. -/
theorem measurable_unitRoof : Measurable (fun _ : X => (1 : ℝ)) := measurable_const

/-- The forward fundamental-domain coordinate for the unit roof. -/
noncomputable def unitFwd (q : SuspensionSpace T (measurable_unitRoof (X := X))) :
    X × ↥(Set.Ico (0 : ℝ) 1) :=
  suspensionUnitFwd T (measurable_unitRoof (X := X)) rfl q

/-- **The quotient (suspension) flow cocycle for the constant roof `τ ≡ 1`.** At time `t` the
cocycle reads the base laps completed by the descended flow, `cocycleZ A T ⌊(unitFwd q).2 + t⌋
(unitFwd q).1`, over the measurable fundamental-domain representative `unitFwd q` of `q`. -/
noncomputable def quotientFlowCocycle {μ : Measure X} [SFinite μ]
    (hA : ∀ x, (A x).det ≠ 0) (hmeas : Measurable A) (hT : MeasurePreserving T μ μ) :
    FlowCocycle (suspensionFlow T (measurable_unitRoof (X := X)) hT
      (fun _ => le_refl (1 : ℝ)) one_pos) d where
  toFun t q := cocycleZ A T ⌊((unitFwd T q).2 : ℝ) + t⌋ (unitFwd T q).1
  map_zero' q := by
    have hmem := (unitFwd T q).2.2
    have hfloor : ⌊((unitFwd T q).2 : ℝ) + 0⌋ = 0 := by
      rw [add_zero]; exact Int.floor_eq_zero_iff.mpr hmem
    simp only [hfloor]
    exact cocycleZ_zero _
  det_ne_zero' t q := cocycleZ_det_ne_zero hA _ _
  cocycle' s t q := by
    -- `P` is the fundamental-domain coordinate of `q`
    set P := unitFwd T q with hP
    -- `q` is the class of `(P.1, ↑P.2)`
    have hq : q = suspensionMk T (measurable_unitRoof (X := X)) (P.1, (P.2 : ℝ)) :=
      (suspensionUnitInv_fwd T (measurable_unitRoof (X := X)) rfl q).symm
    -- the flow map is the descended vertical translation
    have hflow : (suspensionFlow T (measurable_unitRoof (X := X)) hT
        (fun _ => le_refl (1 : ℝ)) one_pos).toFun s q
        = suspensionMk T (measurable_unitRoof (X := X)) (P.1, (P.2 : ℝ) + s) := by
      change suspensionFlowMap T (measurable_unitRoof (X := X)) s q = _
      rw [hq, suspensionFlowMap_mk, suspensionTranslate_apply]
    -- base coordinate of the flowed point
    have hfwd1 : (unitFwd T ((suspensionFlow T (measurable_unitRoof (X := X)) hT
        (fun _ => le_refl (1 : ℝ)) one_pos).toFun s q)).1
        = baseIter T (measurable_unitRoof (X := X)) ⌊(P.2 : ℝ) + s⌋ P.1 := by
      unfold unitFwd
      rw [hflow, suspensionUnitFwd_mk]; rfl
    -- height coordinate of the flowed point
    have hfwd2 : ((unitFwd T ((suspensionFlow T (measurable_unitRoof (X := X)) hT
        (fun _ => le_refl (1 : ℝ)) one_pos).toFun s q)).2 : ℝ)
        = Int.fract ((P.2 : ℝ) + s) := by
      unfold unitFwd
      rw [hflow, suspensionUnitFwd_mk]; rfl
    -- reduce to the floor split + the ℤ-cocycle identity
    change cocycleZ A T ⌊(P.2 : ℝ) + (t + s)⌋ P.1
        = cocycleZ A T ⌊((unitFwd T ((suspensionFlow T (measurable_unitRoof (X := X)) hT
            (fun _ => le_refl (1 : ℝ)) one_pos).toFun s q)).2 : ℝ) + t⌋
            (unitFwd T ((suspensionFlow T (measurable_unitRoof (X := X)) hT
            (fun _ => le_refl (1 : ℝ)) one_pos).toFun s q)).1
          * cocycleZ A T ⌊(P.2 : ℝ) + s⌋ P.1
    rw [hfwd1, hfwd2, show (P.2 : ℝ) + (t + s) = ((P.2 : ℝ) + s) + t by ring, floor_add_split,
      add_comm ⌊(P.2 : ℝ) + s⌋ ⌊Int.fract ((P.2 : ℝ) + s) + t⌋,
      cocycleZ_add (measurable_unitRoof (X := X)) hA]
  measurable' t := by
    have hn : Measurable (fun q : SuspensionSpace T (measurable_unitRoof (X := X)) =>
        ⌊((unitFwd T q).2 : ℝ) + t⌋) := by
      refine Int.measurable_floor.comp ?_
      refine Measurable.add ?_ measurable_const
      exact (measurable_subtype_coe.comp measurable_snd).comp
        (measurable_suspensionUnitFwd T (measurable_unitRoof (X := X)) rfl)
    have hx : Measurable (fun q : SuspensionSpace T (measurable_unitRoof (X := X)) =>
        (unitFwd T q).1) :=
      measurable_fst.comp (measurable_suspensionUnitFwd T (measurable_unitRoof (X := X)) rfl)
    have hpair : Measurable (fun q : SuspensionSpace T (measurable_unitRoof (X := X)) =>
        (⌊((unitFwd T q).2 : ℝ) + t⌋, (unitFwd T q).1)) := hn.prodMk hx
    have hfun : Measurable (fun p : ℤ × X => cocycleZ A T p.1 p.2) :=
      measurable_from_prod_countable_right (fun n => measurable_cocycleZ hmeas n)
    exact hfun.comp hpair

/-! ## Cohomology to the cover cocycle -/

/-- **The cover cocycle over the unit roof is a `cocycleZ` at a floor index.** For `0 ≤ p.2 + t` the
suspension-flow cover cocycle equals the two-sided ℤ-cocycle at the completed-lap count `⌊p.2 + t⌋`:
`coverCocycle p t = cocycleZ A T ⌊p.2 + t⌋ p.1`. This is the cover-level shadow of
`quotientFlowCocycle`. -/
theorem coverCocycle_eq_cocycleZ_floor (p : X × ℝ) {t : ℝ} (hst : 0 ≤ p.2 + t) :
    coverCocycle A T (measurable_unitRoof (X := X)) (fun _ => le_refl (1 : ℝ)) one_pos p t
      = cocycleZ A T ⌊p.2 + t⌋ p.1 := by
  have h1 : coverCocycle A T (measurable_unitRoof (X := X)) (fun _ => le_refl (1 : ℝ)) one_pos p t
      = cocycle A (⇑T)
        (lapCount T (measurable_unitRoof (X := X)) (fun _ => le_refl (1 : ℝ)) one_pos (p.2 + t) p.1)
        p.1 := by
    simp only [coverCocycle, flowCocycleSection, suspensionCocycleReturn_returnTime]
  rw [h1, lapCount_oneRoof T (measurable_unitRoof (X := X)) rfl (fun _ => le_refl (1 : ℝ)) one_pos
      hst p.1,
    ← cocycleZ_natCast (A := A) (T := T) ⌊p.2 + t⌋.toNat p.1,
    Int.toNat_of_nonneg (Int.floor_nonneg.mpr hst)]

/-- **General-rep frame identity.** For a representative `(x, s)` with `0 ≤ s` and `0 ≤ t`, the
quotient flow cocycle differs from the cover cocycle by the measurable **rep-level frame**
`C (x, s) = cocycleZ A T ⌊s⌋ x`:
`quotientFlowCocycle t [x, s] = coverCocycle (x, s) t * (cocycleZ A T ⌊s⌋ x)⁻¹`.
The frame absorbs the `⌊s⌋` completed laps between the general representative and the canonical one;
it is proved from the ℤ-cocycle identity `cocycleZ_add`, the floor split `floor_add_split`, and the
cover formula `coverCocycle_eq_cocycleZ_floor`. -/
theorem quotientFlowCocycle_frame {μ : Measure X} [SFinite μ]
    (hA : ∀ x, (A x).det ≠ 0) (hmeas : Measurable A) (hT : MeasurePreserving T μ μ)
    (p : X × ℝ) (hs : 0 ≤ p.2) {t : ℝ} (ht : 0 ≤ t) :
    quotientFlowCocycle A T hA hmeas hT t (suspensionMk T (measurable_unitRoof (X := X)) p)
      = coverCocycle A T (measurable_unitRoof (X := X)) (fun _ => le_refl (1 : ℝ)) one_pos p t
        * (cocycleZ A T ⌊p.2⌋ p.1)⁻¹ := by
  have hst : (0 : ℝ) ≤ p.2 + t := by linarith
  have hB : quotientFlowCocycle A T hA hmeas hT t (suspensionMk T (measurable_unitRoof (X := X)) p)
      = cocycleZ A T ⌊Int.fract p.2 + t⌋ (baseIter T (measurable_unitRoof (X := X)) ⌊p.2⌋ p.1) := by
    change cocycleZ A T ⌊((unitFwd T (suspensionMk T (measurable_unitRoof (X := X)) p)).2 : ℝ) + t⌋
        (unitFwd T (suspensionMk T (measurable_unitRoof (X := X)) p)).1 = _
    unfold unitFwd
    rw [suspensionUnitFwd_mk]
    rfl
  rw [hB, coverCocycle_eq_cocycleZ_floor A T p hst]
  have hadd := cocycleZ_add (A := A) (T := T) (measurable_unitRoof (X := X)) hA
    ⌊Int.fract p.2 + t⌋ ⌊p.2⌋ p.1
  rw [show ⌊Int.fract p.2 + t⌋ + ⌊p.2⌋ = ⌊p.2 + t⌋ by
    rw [add_comm ⌊Int.fract p.2 + t⌋ ⌊p.2⌋, ← floor_add_split]] at hadd
  rw [hadd, mul_assoc, Matrix.mul_nonsing_inv _ (cocycleZ_det_ne_zero hA _ _).isUnit, mul_one]

/-- **Canonical-rep agreement with the cover (conjugation-free).** For `0 ≤ t`, the quotient flow
cocycle at any class `q` equals the cover cocycle at the *canonical* representative `unitFwd q`:
`quotientFlowCocycle t q = coverCocycle ((unitFwd q).1, (unitFwd q).2) t`. At the canonical
representative `⌊s⌋ = 0`, so the frame is the identity. -/
theorem quotientFlowCocycle_eq_coverCocycle {μ : Measure X} [SFinite μ]
    (hA : ∀ x, (A x).det ≠ 0) (hmeas : Measurable A) (hT : MeasurePreserving T μ μ)
    {t : ℝ} (ht : 0 ≤ t) (q : SuspensionSpace T (measurable_unitRoof (X := X))) :
    quotientFlowCocycle A T hA hmeas hT t q
      = coverCocycle A T (measurable_unitRoof (X := X)) (fun _ => le_refl (1 : ℝ)) one_pos
        ((unitFwd T q).1, ((unitFwd T q).2 : ℝ)) t := by
  have hst : (0 : ℝ) ≤ ((unitFwd T q).2 : ℝ) + t := by
    have h0 := (Set.mem_Ico.mp (unitFwd T q).2.2).1
    linarith
  rw [coverCocycle_eq_cocycleZ_floor A T ((unitFwd T q).1, ((unitFwd T q).2 : ℝ)) hst]
  rfl

/-- **Section identity on the base (`s = 0`).** On the base section the quotient flow cocycle is the
cover cocycle: `quotientFlowCocycle t [x, 0] = coverCocycle (x, 0) t` for `0 ≤ t`. This is the
frame identity at the canonical representative `(x, 0)` (`⌊0⌋ = 0`, frame `= 1`). -/
theorem quotientFlowCocycle_section {μ : Measure X} [SFinite μ]
    (hA : ∀ x, (A x).det ≠ 0) (hmeas : Measurable A) (hT : MeasurePreserving T μ μ)
    (x : X) {t : ℝ} (ht : 0 ≤ t) :
    quotientFlowCocycle A T hA hmeas hT t (suspensionMk T (measurable_unitRoof (X := X)) (x, 0))
      = coverCocycle A T (measurable_unitRoof (X := X)) (fun _ => le_refl (1 : ℝ)) one_pos (x, 0)
        t := by
  have hz : cocycleZ A T ⌊((x, (0 : ℝ)) : X × ℝ).2⌋ ((x, (0 : ℝ)) : X × ℝ).1 = 1 := by
    have h0 : ⌊((x, (0 : ℝ)) : X × ℝ).2⌋ = 0 := by simp
    rw [h0]; exact cocycleZ_zero _
  rw [quotientFlowCocycle_frame A T hA hmeas hT (x, 0) (le_refl 0) ht, hz, inv_one, mul_one]

/-- **The cohomology headline (existential form).** There is a genuine quotient `FlowCocycle` `B`
(the `quotientFlowCocycle`) and a **measurable, everywhere-invertible rep-level frame** `C : X × ℝ →
Matrix …` with `C (x, s) = cocycleZ A T ⌊s⌋ x`, such that over every representative `(x, s)` with
`0 ≤ s` (and `0 ≤ t`) the flow cocycle is the cover cocycle conjugated by the frame:
`B t [x, s] = coverCocycle (x, s) t * (C (x, s))⁻¹`.

The frame is a function of the *representative*, not the class (equivalent representatives carry
different `⌊s⌋`); a genuine class-level conjugacy collapses to the conjugation-free canonical
identity `quotientFlowCocycle_eq_coverCocycle`. This is the honest formalization of "a genuine
quotient `FlowCocycle` cohomologous to the cover cocycle via measurable rep-level frame data". -/
theorem exists_flowCocycle_cohomologous_to_cover {μ : Measure X} [SFinite μ]
    (hA : ∀ x, (A x).det ≠ 0) (hmeas : Measurable A) (hT : MeasurePreserving T μ μ) :
    ∃ (B : FlowCocycle (suspensionFlow T (measurable_unitRoof (X := X)) hT
        (fun _ => le_refl (1 : ℝ)) one_pos) d)
      (C : X × ℝ → Matrix (Fin d) (Fin d) ℝ),
      Measurable C ∧ (∀ p, (C p).det ≠ 0) ∧
      ∀ (p : X × ℝ), 0 ≤ p.2 → ∀ t : ℝ, 0 ≤ t →
        B t (suspensionMk T (measurable_unitRoof (X := X)) p)
          = coverCocycle A T (measurable_unitRoof (X := X)) (fun _ => le_refl (1 : ℝ)) one_pos p t
            * (C p)⁻¹ := by
  refine ⟨quotientFlowCocycle A T hA hmeas hT, fun p => cocycleZ A T ⌊p.2⌋ p.1, ?_, ?_, ?_⟩
  · have hpair : Measurable (fun p : X × ℝ => (⌊p.2⌋, p.1)) :=
      (Int.measurable_floor.comp measurable_snd).prodMk measurable_fst
    have hfun : Measurable (fun z : ℤ × X => cocycleZ A T z.1 z.2) :=
      measurable_from_prod_countable_right (fun n => measurable_cocycleZ hmeas n)
    exact hfun.comp hpair
  · intro p; exact cocycleZ_det_ne_zero hA _ _
  · intro p hs t ht
    exact quotientFlowCocycle_frame A T hA hmeas hT p hs ht

/-! ## Exponent transport -/

/-- **From `HasFlowExponent` to the canonical-representative growth limit.** If the orbit class `q`
carries the flow exponent `L`, then the cover-cocycle growth rate at the *canonical* representative
`unitFwd q` converges to `L`. The existential `HasFlowExponent` provides a limit at *some*
representative; the signed-step cross-representative uniqueness
`tendsto_exponent_iff_of_orbitRel` transfers it to the canonical one. -/
theorem hasFlowExponent_canonRep_tendsto [NeZero d] (hA : ∀ x, (A x).det ≠ 0)
    {q : SuspensionSpace T (measurable_unitRoof (X := X))} {L : ℝ}
    (hq : HasFlowExponent A T (measurable_unitRoof (X := X))
      (fun _ => le_refl (1 : ℝ)) one_pos q L) :
    Tendsto (fun t : ℝ => Real.log ‖coverCocycle A T (measurable_unitRoof (X := X))
        (fun _ => le_refl (1 : ℝ)) one_pos ((unitFwd T q).1, ((unitFwd T q).2 : ℝ)) t‖ / t)
      atTop (𝓝 L) := by
  obtain ⟨x, s, hmk, hL⟩ := hq
  have hcanon : suspensionMk T (measurable_unitRoof (X := X))
      ((unitFwd T q).1, ((unitFwd T q).2 : ℝ)) = q := by
    unfold unitFwd
    exact suspensionUnitInv_fwd T (measurable_unitRoof (X := X)) rfl q
  have hcls : suspensionMk T (measurable_unitRoof (X := X)) ((unitFwd T q).1, ((unitFwd T q).2 : ℝ))
      = suspensionMk T (measurable_unitRoof (X := X)) (x, s) := by rw [hcanon, hmk]
  letI := suspensionAddAction T (measurable_unitRoof (X := X))
  have hrel := Quotient.exact hcls
  change ((unitFwd T q).1, ((unitFwd T q).2 : ℝ)) ∈ AddAction.orbit ℤ (x, s) at hrel
  rw [AddAction.mem_orbit_iff] at hrel
  obtain ⟨m, hm⟩ := hrel
  have hm' : suspensionAct T (measurable_unitRoof (X := X)) m (x, s)
      = ((unitFwd T q).1, ((unitFwd T q).2 : ℝ)) := hm
  exact (tendsto_exponent_iff_of_orbitRel A T (measurable_unitRoof (X := X)) hA
    (fun _ => le_refl (1 : ℝ)) one_pos m (unitFwd T q).1 x ((unitFwd T q).2 : ℝ) s hm').mpr hL

/-- **Exponent transport.** If the orbit class `q` carries the flow exponent `L`, then the growth
rate of the quotient flow cocycle converges to the descended flow exponent `flowExponentAt q`
(`= L`). The `atTop` filter only sees `0 ≤ t`, where `quotientFlowCocycle` agrees with the cover
cocycle at the canonical representative (`quotientFlowCocycle_eq_coverCocycle`); the value is the
representative-free `flowExponentAt`. -/
theorem flowExponentAt_quotientFlowCocycle [NeZero d] (hA : ∀ x, (A x).det ≠ 0)
    (hmeas : Measurable A) {μ : Measure X} [SFinite μ] (hT : MeasurePreserving T μ μ)
    {q : SuspensionSpace T (measurable_unitRoof (X := X))} {L : ℝ}
    (hq : HasFlowExponent A T (measurable_unitRoof (X := X))
      (fun _ => le_refl (1 : ℝ)) one_pos q L) :
    Tendsto (fun t : ℝ => Real.log ‖quotientFlowCocycle A T hA hmeas hT t q‖ / t) atTop
      (𝓝 (flowExponentAt A T (measurable_unitRoof (X := X)) hA (fun _ => le_refl (1 : ℝ)) one_pos
        q)) := by
  have hval : flowExponentAt A T (measurable_unitRoof (X := X)) hA (fun _ => le_refl (1 : ℝ))
      one_pos q = L :=
    flowExponentAt_eq_of_hasFlowExponent A T (measurable_unitRoof (X := X)) hA
      (fun _ => le_refl (1 : ℝ)) one_pos hq
  rw [hval]
  have hcanon := hasFlowExponent_canonRep_tendsto A T hA hq
  have heq : (fun t : ℝ => Real.log ‖quotientFlowCocycle A T hA hmeas hT t q‖ / t)
      =ᶠ[atTop] (fun t : ℝ => Real.log ‖coverCocycle A T (measurable_unitRoof (X := X))
        (fun _ => le_refl (1 : ℝ)) one_pos ((unitFwd T q).1, ((unitFwd T q).2 : ℝ)) t‖ / t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [quotientFlowCocycle_eq_coverCocycle A T hA hmeas hT ht q]
  exact (tendsto_congr' heq).mpr hcanon

end Assembly

end ErgodicTheory
