/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionFlowMP
import Oseledets.Multifractal.BernoulliTwoSided
import Oseledets.Multifractal.BernoulliTwoSidedEntropy
import Oseledets.Entropy.FactorEntropy
import Mathlib.MeasureTheory.Function.Floor

/-!
# Positive metric entropy of the constant-roof suspension flow over a Bernoulli base

This module defines the **metric (Kolmogorov–Sinai) entropy of a measure-preserving flow** as the
entropy of its time-`1` map (the canonical Sinai definition), and proves the headline result of
issue #19: the **constant-roof (`τ ≡ 1`) suspension flow of the two-sided asymmetric Bernoulli
shift has positive metric entropy**.

## Construction

The base system is the invertible two-sided Bernoulli shift `biShiftEquiv` on `BiShift α₀` with the
i.i.d. measure `bernZ ν`. With the constant roof `τ ≡ 1` the suspension space is `BiShift α₀ × ℝ`
modulo the orbit relation `(x, s) ∼ (T x, s − 1)`, and the suspension flow is the time-translation
`ζ_t [x, s] = [x, s + t]`. The time-`1` map of this flow factors onto the base shift via the
projection to the *fundamental-domain representative's first coordinate*

`π [x, s] := (T^{⌊s⌋}) x`  (for `τ ≡ 1`, `⌊s⌋` is the unique lap index),

realised concretely as the orbit-invariant descent of `(x, s) ↦ baseIter T hτ ⌊s⌋ x`. This `π` is
measurable, measure-preserving (`π_* μ̂ = bernZ ν`, since for `τ ≡ 1` the box is
`BiShift α₀ × [0, 1)` and `π ∘ suspensionMk = fst` on it), and intertwines the time-`1` flow with
the base shift (`π ∘ ζ_1 = biShiftEquiv ∘ π`). It is therefore a **factor map**, so the factor-
relative entropy invariance `factor_relative_eq` transports the positive base partition entropy
`Hnu ν` to a lower bound on the flow's entropy.

## Main definitions

* `Oseledets.MeasurePreservingFlow.ksEntropy`: the metric entropy of a measure-preserving flow,
  defined as the Kolmogorov–Sinai entropy of its time-`1` map.
* `Oseledets.Multifractal.suspensionBaseProj`: the factor map `π` to the base shift.
* `Oseledets.Multifractal.coordPartitionZFin`: the time-`0` coordinate partition reindexed to a
  `Fin (Fintype.card α₀)`-indexed partition (so it enters the `Fin`-indexed system entropy `iSup`).

## Main results

* `Oseledets.Multifractal.measurePreserving_suspensionBaseProj`: `π` preserves the suspension
  probability measure, pushing it to `bernZ ν`.
* `Oseledets.Multifractal.suspensionBaseProj_comp_flow`: the intertwining `π ∘ ζ_1 = T ∘ π`.
* `Oseledets.Multifractal.suspensionFlow_bernZ_ksEntropy_pos`: the constant-roof Bernoulli
  suspension flow has strictly positive metric entropy.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace Oseledets

variable {X : Type*} [MeasurableSpace X]

/-- The **metric (Kolmogorov–Sinai) entropy of a measure-preserving flow** `φ`, defined as the
Kolmogorov–Sinai entropy of its time-`1` map `φ 1` (the canonical Sinai definition: the entropy of
a flow is the entropy of any one of its non-trivial time-`t` maps, normalised; we take `t = 1`). -/
noncomputable def MeasurePreservingFlow.ksEntropy {μ : Measure X} [IsProbabilityMeasure μ]
    (φ : MeasurePreservingFlow μ) : EReal :=
  Oseledets.Entropy.ksEntropy (φ.measurePreserving 1)

/-! ### Reindexing a partition along an equivalence of the index type -/

namespace Entropy

variable {α : Type*} [MeasurableSpace α] {ι κ : Type*}

omit [MeasurableSpace α] in
/-- The `n`-fold join cells of a reindexed partition are those of the original, reindexed at the
level of the join index `Fin n → κ ≃ Fin n → ι` by post-composition with `e`. -/
lemma ksJoinCells_reindex (cells : ι → Set α) (e : κ ≃ ι) (T : α → α)
    (n : ℕ) (f : Fin n → κ) :
    ksJoinCells (fun k => cells (e k)) T n f = ksJoinCells cells T n (fun i => e (f i)) := by
  rw [ksJoinCells_apply, ksJoinCells_apply]

/-- **Reindexing invariance of the iterated-join entropy.** Reindexing a partition along an
equivalence of index types leaves every iterated-join entropy `ksEntropySeq` unchanged: the join
cells are merely reindexed by `Fin n → κ ≃ Fin n → ι`, which permutes the summands. -/
lemma ksEntropySeq_reindex [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (e : κ ≃ ι) (n : ℕ) :
    ksEntropySeq hT (P.reindex e) n = ksEntropySeq hT P n := by
  rw [ksEntropySeq, ksEntropySeq, ksJoin_cells, ksJoin_cells]
  rw [← entropy_reindex μ (Equiv.piCongrRight (fun _ : Fin n => e)) (ksJoinCells P.cells T n)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MeasurePartition.reindex_cells, ksJoinCells_reindex]
  rfl

/-- **Reindexing invariance of the partition Kolmogorov–Sinai entropy.** The KS entropy
`h(α, T)` of a partition relative to `T` is unchanged when the partition's index type is reindexed
along an equivalence: the underlying subadditive sequences agree as functions of `n`, hence so do
their Fekete limits. -/
lemma ksEntropyPartition_reindex [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (e : κ ≃ ι) :
    ksEntropyPartition hT (P.reindex e) = ksEntropyPartition hT P := by
  rw [ksEntropyPartition, ksEntropyPartition]
  exact Subadditive.lim_eq_of_eq _ _ (funext fun n => ksEntropySeq_reindex hT P e n)

end Entropy

namespace Multifractal

open Oseledets.Entropy

variable {α₀ : Type*} [MeasurableSpace α₀]

/-! ### The base projection `π` for the constant roof -/

section BaseProj

variable (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The base shift advances `baseIter` by one lap while moving the base point by `T`:
`baseIter T hτ (n + 1) x = baseIter T hτ n (T x)`. (The first coordinate of the suspension action
is independent of the height coordinate, so `suspensionAct (n+1) (x, 0)` and
`suspensionAct n (T x, ·)` have the same first coordinate.) -/
theorem baseIter_succ (n : ℤ) (x : X) :
    baseIter T hτ (n + 1) x = baseIter T hτ n (T x) := by
  have h : suspensionAct T hτ (n + 1) (x, (0 : ℝ))
      = suspensionAct T hτ n (suspensionAct T hτ 1 (x, (0 : ℝ))) := by
    rw [suspensionAct_add]
  have hfst : (suspensionAct T hτ (n + 1) (x, (0 : ℝ))).1 = baseIter T hτ n (T x) := by
    rw [h, suspensionAct_one, suspensionGen_apply]
    rw [suspensionAct_fst]
  rw [baseIter, hfst]

/-- The other lap-advance identity: `baseIter T hτ (n + 1) x = T (baseIter T hτ n x)`. (Here the
generator is applied *after* the `n`-th iterate, moving the resulting base point by `T`.) -/
theorem baseIter_succ' (n : ℤ) (x : X) :
    baseIter T hτ (n + 1) x = T (baseIter T hτ n x) := by
  have h : suspensionAct T hτ (n + 1) (x, (0 : ℝ))
      = suspensionAct T hτ 1 (suspensionAct T hτ n (x, (0 : ℝ))) := by
    rw [add_comm, suspensionAct_add]
  have hfst : (suspensionAct T hτ (n + 1) (x, (0 : ℝ))).1 = T (baseIter T hτ n x) := by
    rw [h, suspensionAct_one, suspensionGen_apply, baseIter]
  rw [baseIter, hfst]

/-- The raw base projection on `X × ℝ` for the constant roof `τ ≡ 1`: send `(x, s)` to the first
coordinate of its fundamental-domain representative, which is `baseIter T hτ ⌊s⌋ x` (since
`⌊s⌋` is the unique lap index). This descends through the suspension orbit quotient. -/
noncomputable def suspensionBaseProjRaw (p : X × ℝ) : X := baseIter T hτ ⌊p.2⌋ p.1

@[simp] theorem suspensionBaseProjRaw_apply (p : X × ℝ) :
    suspensionBaseProjRaw T hτ p = baseIter T hτ ⌊p.2⌋ p.1 := rfl

/-- For the constant roof `τ ≡ 1`, the raw base projection is invariant along the suspension orbit
generator `G (x, s) = (T x, s − 1)`: `baseIter ⌊s⌋ x = baseIter ⌊s − 1⌋ (T x)`. -/
theorem suspensionBaseProjRaw_gen (hτ1 : τ = fun _ => (1 : ℝ)) (p : X × ℝ) :
    suspensionBaseProjRaw T hτ (suspensionGen T hτ p) = suspensionBaseProjRaw T hτ p := by
  obtain ⟨x, s⟩ := p
  rw [suspensionGen_apply, suspensionBaseProjRaw_apply, suspensionBaseProjRaw_apply]
  have hτx : τ x = 1 := by rw [hτ1]
  rw [hτx, Int.floor_sub_one]
  have hstep : baseIter T hτ ⌊s⌋ x = baseIter T hτ (⌊s⌋ - 1) (T x) := by
    rw [← baseIter_succ T hτ (⌊s⌋ - 1) x]
    congr 1
    ring
  exact hstep.symm

include hτ in
/-- The raw base projection is measurable. It is the composite of the measurable iterate
`(x, n) ↦ baseIter T hτ n x` (each lap fixed; `ℤ` countable) with the measurable index map
`(x, s) ↦ (x, ⌊s⌋)`. -/
theorem measurable_suspensionBaseProjRaw : Measurable (suspensionBaseProjRaw T hτ) := by
  have hb : Measurable (fun q : X × ℤ => baseIter T hτ q.2 q.1) := by
    refine measurable_from_prod_countable_left (fun n => ?_)
    have : (fun x : X => baseIter T hτ n x)
        = (fun p : X × ℝ => p.1) ∘ (suspensionAct T hτ n) ∘ (fun x : X => (x, (0 : ℝ))) := by
      funext x; rfl
    rw [this]
    exact measurable_fst.comp ((measurable_suspensionAct T hτ n).comp
      (measurable_id.prodMk measurable_const))
  have hidx : Measurable (fun p : X × ℝ => (p.1, ⌊p.2⌋)) :=
    measurable_fst.prodMk (Int.measurable_floor.comp measurable_snd)
  exact hb.comp hidx

end BaseProj

section BernoulliSuspension

variable (ν : Measure α₀) [IsProbabilityMeasure ν]

/-- The constant roof `τ ≡ 1` for the Bernoulli suspension. -/
abbrev oneRoof : BiShift α₀ → ℝ := fun _ => (1 : ℝ)

theorem measurable_oneRoof : Measurable (oneRoof (α₀ := α₀)) := measurable_const

omit [MeasurableSpace α₀] in
theorem oneRoof_le (x : BiShift α₀) : (1 : ℝ) ≤ oneRoof x := le_refl 1

/-- Local shorthand for the two-sided Bernoulli shift base `biShiftEquiv` (with `α₀` fixed by the
ambient section variables). -/
local notation "𝕋" => biShiftEquiv (α₀ := α₀)

/-- Local shorthand for the measurability proof `measurable_oneRoof` of the constant roof. -/
local notation "𝕞" => measurable_oneRoof (α₀ := α₀)

/-- The constant-roof Bernoulli **suspension flow**: the time-translation flow on the suspension of
the two-sided shift `biShiftEquiv` over `bernZ ν`, with roof `τ ≡ 1`. -/
noncomputable def bernSuspensionFlow :
    MeasurePreservingFlow
      (suspensionMeasure 𝕋 𝕞 (bernZ ν)) :=
  suspensionFlow (T := biShiftEquiv) 𝕞
    (hT := measurePreserving_biShiftEquiv_bernZ ν) (c := 1) oneRoof_le one_pos

@[simp] theorem bernSuspensionFlow_apply (t : ℝ) :
    (bernSuspensionFlow ν) t = suspensionFlowMap 𝕋 𝕞 t := rfl

/-- The integral of the constant roof `τ ≡ 1` against `bernZ ν` is `1`. -/
theorem integral_oneRoof : ∫ x, oneRoof (α₀ := α₀) x ∂(bernZ ν) = 1 := by
  simp only [oneRoof]
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]

/-- For `τ ≡ 1` the normalising constant is `1`, so the suspension probability measure coincides
with the raw pushforward measure `suspensionMeasure₀`. -/
theorem suspensionMeasure_oneRoof_eq :
    suspensionMeasure 𝕋 𝕞 (bernZ ν)
      = suspensionMeasure₀ 𝕋 𝕞 (bernZ ν) := by
  rw [suspensionMeasure, integral_oneRoof, ENNReal.ofReal_one, inv_one, one_smul]

/-- The suspension probability measure is a probability measure. -/
instance instIsProbabilityMeasureSuspensionMeasureBernZ : IsProbabilityMeasure
    (suspensionMeasure 𝕋 𝕞 (bernZ ν)) :=
  isProbabilityMeasure_suspensionMeasure 𝕋 𝕞
    (bernZ ν) (fun _ => zero_le_one) (integrable_const 1)
    (by rw [integral_oneRoof]; exact one_pos)

/-! ### The base projection as a factor map -/

/-- The **base projection** `π : SuspensionSpace → BiShift α₀` of the constant-roof Bernoulli
suspension: the orbit-invariant descent of `(x, s) ↦ baseIter ⌊s⌋ x`. On the fundamental domain
`BiShift α₀ × [0, 1)` it is the first coordinate; it intertwines the time-`1` flow with the base
shift. -/
noncomputable def suspensionBaseProj :
    SuspensionSpace 𝕋 𝕞 → BiShift α₀ :=
  letI := suspensionAddAction 𝕋 𝕞
  Quotient.lift (suspensionBaseProjRaw 𝕋 𝕞)
    (by
      intro p q h
      obtain ⟨n, hn⟩ := h
      have hn' : suspensionAct 𝕋 𝕞 n q = p :=
        hn
      -- The raw projection is invariant under the generator, hence under every power.
      have hgen : ∀ (r : BiShift α₀ × ℝ),
          suspensionBaseProjRaw 𝕋 𝕞
            (suspensionGen 𝕋 𝕞 r)
            = suspensionBaseProjRaw 𝕋 𝕞 r :=
        fun r => suspensionBaseProjRaw_gen _ _ rfl r
      have hgensymm : ∀ (r : BiShift α₀ × ℝ),
          suspensionBaseProjRaw 𝕋 𝕞
            ((suspensionGen 𝕋 𝕞).symm r)
            = suspensionBaseProjRaw 𝕋 𝕞 r :=
        fun r => by
          have h := hgen ((suspensionGen 𝕋
            𝕞).symm r)
          rw [MeasurableEquiv.apply_symm_apply] at h
          exact h.symm
      have hinv : ∀ (m : ℤ) (r : BiShift α₀ × ℝ),
          suspensionBaseProjRaw 𝕋 𝕞
            (suspensionAct 𝕋 𝕞 m r)
            = suspensionBaseProjRaw 𝕋 𝕞 r := by
        intro m
        induction m using Int.induction_on with
        | zero => intro r; rw [suspensionAct_zero]
        | succ k ih =>
          intro r
          rw [add_comm, suspensionAct_add, suspensionAct_one, hgen, ih]
        | pred k ih =>
          intro r
          rw [sub_eq_add_neg, add_comm, suspensionAct_add, suspensionAct_neg_one, hgensymm, ih]
      rw [← hn', hinv n q])

@[simp] theorem suspensionBaseProj_mk (p : BiShift α₀ × ℝ) :
    suspensionBaseProj (suspensionMk 𝕋 𝕞 p)
      = suspensionBaseProjRaw 𝕋 𝕞 p :=
  rfl

/-- The base projection is measurable. -/
theorem measurable_suspensionBaseProj : Measurable (suspensionBaseProj (α₀ := α₀)) := by
  letI := suspensionAddAction 𝕋 𝕞
  refine measurable_from_quotient.2 ?_
  exact measurable_suspensionBaseProjRaw 𝕋 𝕞

/-- On the fundamental domain `BiShift α₀ × [0, 1)`, the composite `π ∘ suspensionMk` is the first
coordinate: there `⌊s⌋ = 0`, so `baseIter 0 x = x`. -/
theorem suspensionBaseProj_comp_mk_on_domain {p : BiShift α₀ × ℝ}
    (hp : p ∈ suspensionDomain (oneRoof (α₀ := α₀))) :
    suspensionBaseProj
        (suspensionMk 𝕋 𝕞 p) = p.1 := by
  rw [suspensionBaseProj_mk, suspensionBaseProjRaw_apply]
  obtain ⟨h0, h1⟩ := hp
  have hfloor : ⌊p.2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    exact ⟨h0, by simpa only [oneRoof] using h1⟩
  rw [hfloor, baseIter, suspensionAct_zero]

/-- **The base projection preserves the suspension measure**, pushing it to `bernZ ν`. For `τ ≡ 1`
the box is `BiShift α₀ × [0, 1)`, on which `π ∘ suspensionMk = fst`; pulling a measurable target set
`E` back through the box gives `(bernZ ν × volume) (E × [0, 1)) = bernZ ν E · 1 = bernZ ν E`. -/
theorem measurePreserving_suspensionBaseProj :
    MeasurePreserving (suspensionBaseProj (α₀ := α₀))
      (suspensionMeasure 𝕋 𝕞 (bernZ ν))
      (bernZ ν) := by
  refine ⟨measurable_suspensionBaseProj, ?_⟩
  refine Measure.ext fun E hE => ?_
  rw [Measure.map_apply measurable_suspensionBaseProj hE]
  -- Reduce to the raw measure and unfold the pushforward through `suspensionMk`.
  rw [suspensionMeasure_oneRoof_eq, suspensionMeasure₀,
    Measure.map_apply (measurable_suspensionMk _ _)
      (measurable_suspensionBaseProj hE)]
  rw [Measure.restrict_apply (measurable_suspensionMk _ _ (measurable_suspensionBaseProj hE))]
  -- On the box, `π ∘ suspensionMk = fst`, so the preimage box equals `(fst⁻¹ E) ∩ box`.
  have hbox : (suspensionMk 𝕋 𝕞
      ⁻¹' (suspensionBaseProj ⁻¹' E)) ∩ suspensionDomain (oneRoof (α₀ := α₀))
      = ((fun p : BiShift α₀ × ℝ => p.1) ⁻¹' E) ∩ suspensionDomain (oneRoof (α₀ := α₀)) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
    intro hp
    rw [suspensionBaseProj_comp_mk_on_domain hp]
  rw [hbox]
  -- `(fst⁻¹ E) ∩ box = E ×ˢ Ico 0 1`, of product mass `bernZ ν E · 1 = bernZ ν E`.
  have hprod : ((fun p : BiShift α₀ × ℝ => p.1) ⁻¹' E) ∩ suspensionDomain (oneRoof (α₀ := α₀))
      = E ×ˢ Set.Ico (0 : ℝ) 1 := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, suspensionDomain, Set.mem_setOf_eq,
      Set.mem_prod, Set.mem_Ico, oneRoof]
  rw [hprod, Measure.prod_apply (hE.prod measurableSet_Ico)]
  have hfiber : ∀ x : BiShift α₀,
      volume (Prod.mk x ⁻¹' (E ×ˢ Set.Ico (0 : ℝ) 1))
        = (Set.indicator E (fun _ => (1 : ℝ≥0∞)) x) := by
    intro x
    by_cases hx : x ∈ E
    · rw [Set.mk_preimage_prod_right hx, Real.volume_Ico, sub_zero, ENNReal.ofReal_one,
        Set.indicator_of_mem hx]
    · rw [Set.mk_preimage_prod_right_eq_empty hx, measure_empty, Set.indicator_of_notMem hx]
  simp only [hfiber]
  rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, one_mul]

/-- **The base projection intertwines the time-`1` flow with the base shift.** For `τ ≡ 1`,
`ζ_1 [x, s] = [x, s + 1] = [T x, s]`, so `π ∘ ζ_1 = biShiftEquiv ∘ π`: pointwise on representatives,
`baseIter ⌊s + 1⌋ x = baseIter (⌊s⌋ + 1) x = biShiftMap (baseIter ⌊s⌋ x)`. -/
theorem suspensionBaseProj_comp_flow :
    suspensionBaseProj ∘ (bernSuspensionFlow ν) 1 = biShiftEquiv ∘ suspensionBaseProj := by
  funext y
  refine Quotient.inductionOn y (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspensionBaseProj ((bernSuspensionFlow ν) 1 (suspensionMk 𝕋 𝕞 (x, s)))
    = biShiftEquiv (suspensionBaseProj (suspensionMk 𝕋 𝕞 (x, s)))
  rw [bernSuspensionFlow_apply, suspensionFlowMap_mk, suspensionTranslate_apply,
    suspensionBaseProj_mk, suspensionBaseProj_mk, suspensionBaseProjRaw_apply,
    suspensionBaseProjRaw_apply, Int.floor_add_one, baseIter_succ']

/-! ### The base partition reindexed to a `Fin`-indexed partition -/

variable [Fintype α₀] [MeasurableSingletonClass α₀]

-- The `Fin`-reindexed base coordinate partition `coordPartitionZFin (bernZ ν)` and its entropy
-- identification `ksEntropyPartition_coordPartitionZFin_bernZ_eq : … = Hnu ν` are provided by the
-- companion module `Oseledets.Multifractal.BernoulliTwoSidedEntropy` (imported above), so the
-- headline below is unconditional (no `hbase` hypothesis).

/-! ### Positive metric entropy of the suspension flow -/

-- `[Fintype α₀]` is used in the proof (via `Hnu_pos`), not in the bare type.
set_option linter.unusedFintypeInType false in
/-- **The constant-roof Bernoulli suspension flow has positive metric entropy.**

For the two-sided asymmetric Bernoulli shift charging two distinct symbols `i ≠ j` with positive
mass, the single-symbol Shannon entropy `Hnu ν` is strictly positive (`Hnu_pos`). The base
projection `π` is a factor map from the time-`1` flow map onto the base shift, so the
factor-relative entropy invariance `factor_relative_eq` carries the partition entropy of the base
coordinate partition (equal to `Hnu ν` by hypothesis `hbase`) onto the pulled-back partition for
the flow, which is bounded above by the flow's metric entropy via `le_ksEntropy`.

The base partition-entropy identification `= Hnu ν` is supplied by the companion two-sided-Bernoulli
entropy module (`ksEntropyPartition_coordPartitionZFin_bernZ_eq`), so this statement is
unconditional. -/
theorem suspensionFlow_bernZ_ksEntropy_pos {i j : α₀} (hij : i ≠ j)
    (hi : 0 < (ν {i}).toReal) (hj : 0 < (ν {j}).toReal) :
    0 < (bernSuspensionFlow ν).ksEntropy := by
  -- The base coordinate-partition entropy equals `Hnu ν` (companion two-sided-Bernoulli module).
  have hbase : ksEntropyPartition (measurePreserving_biShiftEquiv_bernZ ν)
      (coordPartitionZFin (bernZ ν)) = Hnu ν :=
    ksEntropyPartition_coordPartitionZFin_bernZ_eq ν
  -- The time-`1` flow map and its measure-preservation.
  set φ := bernSuspensionFlow ν with hφ
  have hT1 : MeasurePreserving (φ 1)
      (suspensionMeasure 𝕋 𝕞 (bernZ ν))
      (suspensionMeasure 𝕋 𝕞 (bernZ ν)) :=
    φ.measurePreserving 1
  -- The base projection is a factor map.
  have hπ := measurePreserving_suspensionBaseProj ν
  have hπS : suspensionBaseProj ∘ (φ 1) = biShiftEquiv ∘ suspensionBaseProj :=
    suspensionBaseProj_comp_flow ν
  -- Pull the base coordinate partition back along `π`.
  set Q : MeasurePartition _ (Fin (Fintype.card α₀)) :=
    (coordPartitionZFin (bernZ ν)).pulledBack hπ with hQ
  -- Factor-relative entropy invariance: `h(π⁻¹ R, φ 1) = h(R, T)`.
  have hfac : ksEntropyPartition hT1 Q
      = ksEntropyPartition (measurePreserving_biShiftEquiv_bernZ ν)
          (coordPartitionZFin (bernZ ν)) := by
    rw [hQ]
    exact factor_relative_eq hT1 (measurePreserving_biShiftEquiv_bernZ ν) hπ hπS
      (coordPartitionZFin (bernZ ν))
  -- Chain the (real) entropy positivity through to the (EReal) system entropy.
  have hHpos : 0 < Hnu ν := Hnu_pos ν hij hi hj
  have hQpos : 0 < ksEntropyPartition hT1 Q := by rw [hfac, hbase]; exact hHpos
  have hle : ((ksEntropyPartition hT1 Q : ℝ) : EReal) ≤ Entropy.ksEntropy hT1 :=
    le_ksEntropy hT1 Q
  have hcoe : (0 : EReal) < ((ksEntropyPartition hT1 Q : ℝ) : EReal) := by
    exact_mod_cast hQpos
  calc (0 : EReal) < ((ksEntropyPartition hT1 Q : ℝ) : EReal) := hcoe
    _ ≤ Entropy.ksEntropy hT1 := hle
    _ = φ.ksEntropy := rfl

end BernoulliSuspension

end Multifractal

end Oseledets
