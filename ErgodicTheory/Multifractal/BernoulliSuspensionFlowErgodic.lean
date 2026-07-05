/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.BernoulliSuspensionFlow
import ErgodicTheory.Multifractal.BernoulliTwoSidedErgodic
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodicity of the constant-roof Bernoulli suspension flow (and the time-`1` failure)

This module completes the dynamical picture of the constant-roof (`τ ≡ 1`) suspension flow
`bernSuspensionFlow ν` built in `ErgodicTheory.Multifractal.BernoulliSuspensionFlow`. It establishes
the sharp contrast between the *full* `ℝ`-flow and its *time-`1` map*:

* **The full `ℝ`-flow is ergodic iff the base shift is ergodic.** A measurable set invariant under
  *all* time-`t` maps `ζ_t` (`t ∈ ℝ`) is null or conull, provided the two-sided Bernoulli base shift
  `biShiftEquiv` is ergodic for `bernZ ν` (`ergodic_bernSuspensionFlow`).

* **The time-`1` map is *not* ergodic.** For the constant roof `τ ≡ 1` the time-`1` map of the flow
  is, on the fundamental box `BiShift α₀ × [0, 1)`, the skew map `(x, s) ↦ (T x, s)`: it leaves the
  *section coordinate* `s` untouched. Hence the saturated section set `{[x, s] | s < 1/2}` is a
  nontrivial time-`1`-invariant set, witnessing the failure of ergodicity
  (`not_ergodic_bernSuspensionFlow_one`).

## Why the time-`1` map fails but the full flow succeeds

The eigenfunction `g(x, s) = e^{2π i s}` on the suspension is a (non-constant) eigenfunction of the
time-`1` map with eigenvalue `1`: `g ∘ ζ_1 = g`, because `ζ_1 [x, s] = [x, s + 1] = [T x, s]` only
*re-bases* the height, leaving `e^{2π i s}` fixed. A non-constant time-`1`-invariant function blocks
ergodicity of `ζ_1`. The *full* flow, by contrast, moves the section coordinate continuously, so
`g ∘ ζ_t = e^{2π i t} g` is a genuine (non-trivial) eigenfunction of the flow's generator — there is
no non-constant function invariant under *all* `ζ_t`. This is the constant-roof special-flow
dichotomy of Cornfeld–Fomin–Sinai (*Ergodic Theory*, Springer 1982, Ch. 11): a special flow under a
constant roof is ergodic **iff** its base map is ergodic, even though no power (in particular the
time-`1` map) of such a flow is ever ergodic.

## Proof of the flow ergodicity

The crux is purely the *all-translation invariance*, requiring no circle ergodicity. Let
`A ⊆ SuspensionSpace` be invariant under every `ζ_t`. Lifting to the box `BiShift α₀ × ℝ` through
the quotient map `π = suspensionMk`:

1. *All vertical translations fix the lift.* For every `t` and `(x, s)`,
   `π (x, s) ∈ A ↔ ζ_t (π (x, s)) ∈ A ↔ π (x, s + t) ∈ A`, using `π ∘ S_t = ζ_t ∘ π` and
   `ζ_t ⁻¹' A = A`. Taking `t = s` from base height `0`, membership of `π (x, s)` in `A` depends
   only on the base point `x`, through `B := {x | π (x, 0) ∈ A}`. So the lift is the *cylinder*
   `B ×ˢ univ`.

2. *The base set is shift-invariant.* The generator `G (x, s) = (T x, s − 1)` keeps `π` fixed
   (`π (G p) = π p`), so `π (x, s) ∈ A ↔ π (T x, s − 1) ∈ A`, i.e. `x ∈ B ↔ T x ∈ B`. Thus
   `biShiftEquiv ⁻¹' B = B`.

3. *Apply base ergodicity.* `B` is measurable and shift-invariant, so `bernZ ν B ∈ {0, 1}` by
   `hbase`. The constant-roof box mass is `μ̂ A = (bernZ ν × volume) (B ×ˢ Ico 0 1)
   = bernZ ν B · 1`, so `μ̂ A ∈ {0, 1}`.

## Main results

* `ErgodicTheory.Multifractal.suspensionMeasure_eq_bernZ_base_of_flowInvariant`: for a
  flow-invariant measurable `A`, `μ̂ A = bernZ ν B` with `B = {x | π (x, 0) ∈ A}` the
  (shift-invariant) base set.
* `ErgodicTheory.Multifractal.ergodic_bernSuspensionFlow`: **the conditional flow ergodicity** —
  every all-`t`-invariant measurable set is null or conull, given base ergodicity.
* `ErgodicTheory.Multifractal.not_ergodic_bernSuspensionFlow_one`: **the time-`1` map is not
  ergodic** (the saturated section set `{[x, s] | s < 1/2}` is a nontrivial invariant set).
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace ErgodicTheory

namespace Multifractal

variable {α₀ : Type*} [MeasurableSpace α₀]

local notation "𝕋" => biShiftEquiv (α₀ := α₀)
local notation "𝕞" => measurable_oneRoof (α₀ := α₀)

/-! ### The generator fixes the quotient projection -/

/-- The orbit generator `G (x, s) = (T x, s − τ x)` keeps the quotient projection fixed:
`suspensionMk (suspensionGen p) = suspensionMk p`, since `p` and `G p = (-1) •ᵥ⁻¹ …` lie in the same
`ℤ`-orbit. (Here specialised to `G p = suspensionAct 1 p`.) -/
theorem suspensionMk_suspensionGen (p : BiShift α₀ × ℝ) :
    suspensionMk 𝕋 𝕞 (suspensionGen 𝕋 𝕞 p) = suspensionMk 𝕋 𝕞 p := by
  letI := suspensionAddAction 𝕋 𝕞
  refine Quotient.sound ⟨1, ?_⟩
  change suspensionAct 𝕋 𝕞 1 p = suspensionGen 𝕋 𝕞 p
  rw [suspensionAct_one]

/-! ### The base set of a flow-invariant set and its shift-invariance -/

/-- The **base set** of a measurable set `A` on the suspension: the points `x` whose height-`0`
representative `[x, 0]` lies in `A`. For a flow-invariant `A` this is the cylinder base
(`mem_suspensionMk_iff_mem_base`) and is shift-invariant (`base_set_shift_invariant`). -/
def flowInvariantBase (A : Set (SuspensionSpace 𝕋 𝕞)) : Set (BiShift α₀) :=
  {x | suspensionMk 𝕋 𝕞 (x, (0 : ℝ)) ∈ A}

@[simp] theorem mem_flowInvariantBase {A : Set (SuspensionSpace 𝕋 𝕞)} (x : BiShift α₀) :
    x ∈ flowInvariantBase A ↔ suspensionMk 𝕋 𝕞 (x, (0 : ℝ)) ∈ A := Iff.rfl

/-- The base set is measurable: it is the preimage of `A` along the measurable composite
`x ↦ suspensionMk (x, 0)`. -/
theorem measurableSet_flowInvariantBase {A : Set (SuspensionSpace 𝕋 𝕞)} (hA : MeasurableSet A) :
    MeasurableSet (flowInvariantBase A) := by
  have hcomp : Measurable (fun x : BiShift α₀ => suspensionMk 𝕋 𝕞 (x, (0 : ℝ))) :=
    (measurable_suspensionMk 𝕋 𝕞).comp (measurable_id.prodMk measurable_const)
  exact hcomp hA

variable (ν : Measure α₀) [IsProbabilityMeasure ν]

/-- **Cylinder structure of a flow-invariant set.** For an `A` invariant under every time-`t` map of
the flow, membership of `[x, s]` in `A` depends only on the base point `x` (through the base set),
for *every* height `s`: `[x, s] ∈ A ↔ x ∈ flowInvariantBase A`.

Using the descent commutation `ζ_t ∘ π = π ∘ S_t` (`suspensionFlowMap_mk`) and the invariance
`ζ_s ⁻¹' A = A`, the height `s` can be translated away to the base height `0`:
`[x, s] = ζ_s [x, 0] ∈ A ↔ [x, 0] ∈ A`. -/
theorem mem_suspensionMk_iff_mem_base {A : Set (SuspensionSpace 𝕋 𝕞)}
    (hinv : ∀ t : ℝ, (bernSuspensionFlow ν) t ⁻¹' A = A) (x : BiShift α₀) (s : ℝ) :
    suspensionMk 𝕋 𝕞 (x, s) ∈ A ↔ x ∈ flowInvariantBase A := by
  rw [mem_flowInvariantBase]
  have hflow : (bernSuspensionFlow ν) s (suspensionMk 𝕋 𝕞 (x, (0 : ℝ)))
      = suspensionMk 𝕋 𝕞 (x, s) := by
    rw [bernSuspensionFlow_apply, suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]
  have hpre : suspensionMk 𝕋 𝕞 (x, (0 : ℝ)) ∈ (bernSuspensionFlow ν) s ⁻¹' A
      ↔ suspensionMk 𝕋 𝕞 (x, (0 : ℝ)) ∈ A := by rw [hinv s]
  rw [mem_preimage, hflow] at hpre
  exact hpre

/-- **Shift-invariance of the base set.** For a flow-invariant `A`, the base set is invariant under
the two-sided Bernoulli shift: `biShiftEquiv ⁻¹' (flowInvariantBase A) = flowInvariantBase A`.

The orbit generator `G (x, s) = (T x, s − 1)` keeps the quotient projection fixed
(`suspensionMk_suspensionGen`), so `[T x, −1] = [x, 0]`. Specialising the cylinder identity
`mem_suspensionMk_iff_mem_base` at `(T x, −1)` gives
`T x ∈ base ↔ [T x, −1] ∈ A ↔ [x, 0] ∈ A ↔ x ∈ base`. -/
theorem base_set_shift_invariant {A : Set (SuspensionSpace 𝕋 𝕞)}
    (hinv : ∀ t : ℝ, (bernSuspensionFlow ν) t ⁻¹' A = A) :
    𝕋 ⁻¹' (flowInvariantBase A) = flowInvariantBase A := by
  ext x
  simp only [mem_preimage, mem_flowInvariantBase]
  -- `[T x, -1] = [x, 0]` because the orbit generator fixes the quotient projection.
  have horbit : suspensionMk 𝕋 𝕞 (𝕋 x, (-1 : ℝ)) = suspensionMk 𝕋 𝕞 (x, (0 : ℝ)) := by
    have hgen : suspensionGen 𝕋 𝕞 (x, (0 : ℝ)) = (𝕋 x, (-1 : ℝ)) := by
      rw [suspensionGen_apply]; simp [oneRoof]
    rw [← hgen, suspensionMk_suspensionGen]
  -- Membership of `[T x, -1]` reduces both ways through the cylinder identity.
  have h1 : suspensionMk 𝕋 𝕞 (𝕋 x, (-1 : ℝ)) ∈ A ↔ 𝕋 x ∈ flowInvariantBase A :=
    mem_suspensionMk_iff_mem_base ν hinv (𝕋 x) (-1)
  rw [mem_flowInvariantBase] at h1
  rw [← h1, horbit]

/-! ### The suspension mass of a flow-invariant set -/

/-- **The constant-roof mass of a flow-invariant set is the base mass.** For a flow-invariant
measurable `A`, the suspension probability `μ̂ A` equals `bernZ ν` of the base set
`B = flowInvariantBase A`.

For `τ ≡ 1` the box is `BiShift α₀ × [0, 1)` and `μ̂ = μ̂₀` (`suspensionMeasure_oneRoof_eq`). The
preimage of `A` through the quotient, intersected with the box, equals `B ×ˢ Ico 0 1` by the
cylinder identity `mem_suspensionMk_iff_mem_base` (membership depends only on the base point), so
the product mass is `bernZ ν B · volume (Ico 0 1) = bernZ ν B · 1`. -/
theorem suspensionMeasure_eq_bernZ_base_of_flowInvariant {A : Set (SuspensionSpace 𝕋 𝕞)}
    (hA : MeasurableSet A) (hinv : ∀ t : ℝ, (bernSuspensionFlow ν) t ⁻¹' A = A) :
    suspensionMeasure 𝕋 𝕞 (bernZ ν) A = bernZ ν (flowInvariantBase A) := by
  set B := flowInvariantBase A with hB
  have hBmeas : MeasurableSet B := measurableSet_flowInvariantBase hA
  -- Reduce to the raw measure and unfold the pushforward through `suspensionMk`.
  rw [suspensionMeasure_oneRoof_eq, suspensionMeasure₀,
    Measure.map_apply (measurable_suspensionMk _ _) hA,
    Measure.restrict_apply (measurable_suspensionMk _ _ hA)]
  -- The pulled-back set, intersected with the box, is the cylinder `B ×ˢ Ico 0 1`.
  have hbox : (suspensionMk 𝕋 𝕞 ⁻¹' A) ∩ suspensionDomain (oneRoof (α₀ := α₀))
      = B ×ˢ Set.Ico (0 : ℝ) 1 := by
    ext p
    obtain ⟨x, s⟩ := p
    simp only [mem_inter_iff, mem_preimage, suspensionDomain, mem_setOf_eq, mem_prod, mem_Ico,
      oneRoof]
    rw [mem_suspensionMk_iff_mem_base ν hinv x s, ← hB]
  rw [hbox, Measure.prod_apply (hBmeas.prod measurableSet_Ico)]
  -- The product mass: `bernZ ν B · volume (Ico 0 1) = bernZ ν B · 1`.
  have hfiber : ∀ x : BiShift α₀,
      volume (Prod.mk x ⁻¹' (B ×ˢ Set.Ico (0 : ℝ) 1))
        = Set.indicator B (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.mk_preimage_prod_right hx, Real.volume_Ico, sub_zero, ENNReal.ofReal_one,
        Set.indicator_of_mem hx]
    · rw [Set.mk_preimage_prod_right_eq_empty hx, measure_empty, Set.indicator_of_notMem hx]
  simp only [hfiber]
  rw [lintegral_indicator hBmeas, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, one_mul]

/-! ### The conditional flow ergodicity (T2) -/

/-- **Ergodicity of the constant-roof Bernoulli suspension flow (conditional on base ergodicity).**

Given that the two-sided Bernoulli shift `biShiftEquiv` is ergodic for `bernZ ν` (`hbase`), every
measurable set `A` invariant under *all* time-`t` maps of the suspension flow is null or conull:
`μ̂ A = 0 ∨ μ̂ A = 1`.

By `suspensionMeasure_eq_bernZ_base_of_flowInvariant` the mass `μ̂ A` equals `bernZ ν B` for the
base set `B = flowInvariantBase A`, which is measurable (`measurableSet_flowInvariantBase`) and
shift-invariant (`base_set_shift_invariant`); base ergodicity's zero-one law
(`PreErgodic.prob_eq_zero_or_one`) gives `bernZ ν B ∈ {0, 1}`. -/
theorem ergodic_bernSuspensionFlow (hbase : Ergodic 𝕋 (bernZ ν))
    {A : Set (SuspensionSpace 𝕋 𝕞)} (hA : MeasurableSet A)
    (hinv : ∀ t : ℝ, (bernSuspensionFlow ν) t ⁻¹' A = A) :
    suspensionMeasure 𝕋 𝕞 (bernZ ν) A = 0 ∨ suspensionMeasure 𝕋 𝕞 (bernZ ν) A = 1 := by
  rw [suspensionMeasure_eq_bernZ_base_of_flowInvariant ν hA hinv]
  exact hbase.toPreErgodic.prob_eq_zero_or_one
    (measurableSet_flowInvariantBase hA) (base_set_shift_invariant ν hinv)

/-! ### The time-`1` map is NOT ergodic (P1) -/

/-- The **constant roof has integer roof sums**: `roofSum n x = n` for `τ ≡ 1`. Each lap step adds
`τ (·) = 1`, so the integer roof sum telescopes to `n`. -/
theorem roofSum_oneRoof (n : ℤ) (x : BiShift α₀) :
    roofSum 𝕋 𝕞 n x = (n : ℝ) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [roofSum_add_one, ih]; simp only [oneRoof]; push_cast; ring
  | pred k ih =>
    have hstep : roofSum 𝕋 𝕞 (-(k : ℤ) - 1) x
        = roofSum 𝕋 𝕞 (-(k : ℤ)) x - 1 := by
      have h := roofSum_add_one 𝕋 𝕞 (-(k : ℤ) - 1) x
      have hcancel : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by ring
      rw [hcancel] at h
      simp only [oneRoof] at h
      linarith
    rw [hstep, ih]; push_cast; ring

/-- The **fractional height** descends to the suspension quotient: the orbit-invariant value
`Int.fract s` of a representative's height. Well-defined because the orbit generator subtracts the
*integer* roof `1` from the height (and a general orbit element subtracts the integer `n`), leaving
`Int.fract` unchanged. -/
noncomputable def fractHeight : SuspensionSpace 𝕋 𝕞 → ℝ :=
  letI := suspensionAddAction 𝕋 𝕞
  Quotient.lift (fun p : BiShift α₀ × ℝ => Int.fract p.2)
    (by
      intro p q h
      obtain ⟨n, hn⟩ := h
      have hn' : suspensionAct 𝕋 𝕞 n q = p := hn
      have hsnd : (suspensionAct 𝕋 𝕞 n q).2 = q.2 - (n : ℝ) := by
        rw [suspensionAct_snd, roofSum_oneRoof]
      have hp2 : p.2 = q.2 - (n : ℝ) := by rw [← hn', hsnd]
      change Int.fract p.2 = Int.fract q.2
      rw [hp2, Int.fract_sub_intCast])

@[simp] theorem fractHeight_mk (p : BiShift α₀ × ℝ) :
    fractHeight (suspensionMk 𝕋 𝕞 p) = Int.fract p.2 := rfl

/-- The fractional-height descent is measurable: out of the quotient it is the descent of the
measurable map `p ↦ Int.fract p.2`. -/
theorem measurable_fractHeight : Measurable (fractHeight (α₀ := α₀)) := by
  letI := suspensionAddAction 𝕋 𝕞
  refine measurable_from_quotient.2 ?_
  exact measurable_fract.comp measurable_snd

/-- The **saturated section set** `{q | fractHeight q < 1/2}` on the suspension: the orbit-invariant
descent of the half-open height slab `{[x, s] | Int.fract s < 1/2}`. For the constant roof it is a
nontrivial time-`1`-invariant set, the witness to the failure of time-`1` ergodicity. -/
def sectionHalf : Set (SuspensionSpace 𝕋 𝕞) :=
  fractHeight ⁻¹' Set.Iio (1 / 2)

/-- The section set is measurable: it is the preimage of `Iio (1/2)` along the measurable
fractional-height descent. -/
theorem measurableSet_sectionHalf : MeasurableSet (sectionHalf (α₀ := α₀)) :=
  measurable_fractHeight measurableSet_Iio

/-- **The section set is `ζ_1`-invariant.** The time-`1` map adds `1` to the representative's
height, which leaves `Int.fract` unchanged (`Int.fract_add_one`); hence
`fractHeight ∘ ζ_1 = fractHeight`, so the preimage `{fractHeight < 1/2}` is `ζ_1`-invariant. -/
theorem sectionHalf_flow_one_invariant :
    (bernSuspensionFlow ν) 1 ⁻¹' sectionHalf = sectionHalf := by
  ext q
  refine Quotient.inductionOn q (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change (bernSuspensionFlow ν) 1 (suspensionMk 𝕋 𝕞 (x, s)) ∈ sectionHalf
    ↔ suspensionMk 𝕋 𝕞 (x, s) ∈ sectionHalf
  simp only [sectionHalf, mem_preimage, bernSuspensionFlow_apply, suspensionFlowMap_mk,
    suspensionTranslate_apply, fractHeight_mk, mem_Iio, Int.fract_add_one]

/-- **The section set has mass `1/2`.** For `τ ≡ 1` the box is `BiShift α₀ × [0, 1)` and `μ̂ = μ̂₀`;
the preimage of `sectionHalf` through the quotient intersected with the box is the half-box
`BiShift α₀ × [0, 1/2)` (on the box `Int.fract s = s`), of product mass
`bernZ ν univ · volume (Ico 0 (1/2)) = 1 · (1/2)`. -/
theorem suspensionMeasure_sectionHalf :
    suspensionMeasure 𝕋 𝕞 (bernZ ν) sectionHalf = 1 / 2 := by
  rw [suspensionMeasure_oneRoof_eq, suspensionMeasure₀,
    Measure.map_apply (measurable_suspensionMk _ _) measurableSet_sectionHalf,
    Measure.restrict_apply (measurable_suspensionMk _ _ measurableSet_sectionHalf)]
  -- On the box `s ∈ [0,1)`, `Int.fract s = s`, so the slab is `univ ×ˢ Ico 0 (1/2)`.
  have hbox : (suspensionMk 𝕋 𝕞 ⁻¹' sectionHalf) ∩ suspensionDomain (oneRoof (α₀ := α₀))
      = (Set.univ : Set (BiShift α₀)) ×ˢ Set.Ico (0 : ℝ) (1 / 2) := by
    ext p
    obtain ⟨x, s⟩ := p
    simp only [sectionHalf, mem_inter_iff, mem_preimage, fractHeight_mk, mem_Iio, suspensionDomain,
      mem_setOf_eq, oneRoof, mem_prod, mem_univ, true_and, mem_Ico]
    constructor
    · rintro ⟨hlt, h0, _⟩
      rw [Int.fract_eq_self.2 ⟨h0, by linarith⟩] at hlt
      exact ⟨h0, hlt⟩
    · rintro ⟨h0, hlt⟩
      have hs1 : s < 1 := by linarith [(by norm_num : (1 / 2 : ℝ) < 1)]
      rw [Int.fract_eq_self.2 ⟨h0, hs1⟩]
      exact ⟨hlt, h0, hs1⟩
  rw [hbox, Measure.prod_apply (MeasurableSet.univ.prod measurableSet_Ico)]
  -- `∫⁻ x, volume (fiber) ∂bernZ ν = ofReal (1/2) · bernZ ν univ = 1/2`.
  have hfiber : ∀ x : BiShift α₀,
      volume (Prod.mk x ⁻¹' ((Set.univ : Set (BiShift α₀)) ×ˢ Set.Ico (0 : ℝ) (1 / 2)))
        = ENNReal.ofReal (1 / 2) := by
    intro x
    rw [Set.mk_preimage_prod_right (mem_univ x), Real.volume_Ico, sub_zero]
  simp only [hfiber]
  rw [lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat]

/-- **The time-`1` map of the constant-roof Bernoulli suspension flow is not ergodic.**

For `τ ≡ 1` the time-`1` map is `ζ_1 [x, s] = [x, s + 1] = [T x, s]`: it fixes the *fractional* part
of the height. Hence the saturated section set `sectionHalf = {q | fractHeight q < 1/2}` is
`ζ_1`-invariant (`sectionHalf_flow_one_invariant`), measurable (`measurableSet_sectionHalf`), and
has mass `1/2` (`suspensionMeasure_sectionHalf`) — strictly between `0` and `1`. So the zero-one law
fails: `ζ_1` is **not** ergodic.

This is the honest obstruction documented in the module header: the eigenfunction `e^{2π i s}` of
the flow generator descends to a non-constant `ζ_1`-invariant function (eigenvalue `e^{2π i · 1} =
1`), so no constant-roof special flow's time-`1` map is ever ergodic. -/
theorem not_ergodic_bernSuspensionFlow_one :
    ¬ Ergodic ((bernSuspensionFlow ν) 1) (suspensionMeasure 𝕋 𝕞 (bernZ ν)) := by
  intro herg
  have hzo := herg.toPreErgodic.prob_eq_zero_or_one (measurableSet_sectionHalf)
    (sectionHalf_flow_one_invariant ν)
  rw [suspensionMeasure_sectionHalf ν] at hzo
  rcases hzo with h | h
  · exact (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0) h
  · exact (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 1) h

/-! ### Unconditional flow ergodicity (the base hypothesis discharged) -/

/-- **The constant-roof Bernoulli suspension flow is ergodic, unconditionally.** Discharges the
base-ergodicity hypothesis of `ergodic_bernSuspensionFlow` with the proved two-sided Bernoulli
ergodicity (`ergodic_biShiftEquiv_bernZ`, the mixing/cylinder-approximation keystone): every
measurable set invariant under *all* time-`t` maps of the flow is null or conull. The time-`1`
map stays non-ergodic (`not_ergodic_bernSuspensionFlow_one`) — only the full flow is ergodic. -/
theorem ergodic_bernSuspensionFlow_uncond
    {A : Set (SuspensionSpace 𝕋 𝕞)} (hA : MeasurableSet A)
    (hinv : ∀ t : ℝ, (bernSuspensionFlow ν) t ⁻¹' A = A) :
    suspensionMeasure 𝕋 𝕞 (bernZ ν) A = 0 ∨ suspensionMeasure 𝕋 𝕞 (bernZ ν) A = 1 :=
  ergodic_bernSuspensionFlow ν (ergodic_biShiftEquiv_bernZ ν) hA hinv

end Multifractal

end ErgodicTheory
