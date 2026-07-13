/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionMetric

/-!
# The Bowen–Walters metric for a variable roof bounded below

This module generalises the constant-roof-1 Bowen–Walters embedding metric of
`ErgodicTheory.Continuous.SuspensionMetric` to a **variable roof** `τ : X → ℝ` that is bounded
below by a positive constant `ρmin` (`hρ0 : ∀ x, ρmin ≤ τ x`, `hρpos : 0 < ρmin`). This is the
metric layer of the *variable-roof* suspension programme (issue #63, tier 3) and the substrate for
the variable-roof continuous-flow Livšic theory.

## Fibre rescaling by the roof (Bowen–Walters 1972, Barreira–Radu–Wolf §2.1)

Following Bowen–Walters (1972) and Barreira–Radu–Wolf (Dyn. Syst. 19, 2004, §2.1), the general-roof
Bowen–Walters distance rescales each fibre by its roof height:

`d_Y((x, t), (y, s)) = d₁((x, t / τ x), (y, s / τ y))`,

so the vertical coordinate is normalised to the *unit* circle `ℝ / ℤ` before comparison. The key
structural fact is that this normalisation makes the seam gluing `(x, τ x) ∼ (T x, 0)` **roof
independent**: the normalized height `u = s / τ x` runs over `[0, 1)` on every fibre regardless of
`τ`, and the endpoint `u → 1` glues to `u = 0` on the next fibre exactly as in the constant-roof
case. We may therefore *reuse verbatim* the constant-roof Kuratowski test bundles `muFun`, `nuFun`,
the circle-height distance `hgt` and the isometric embedding `kur` of
`ErgodicTheory.Continuous.SuspensionMetric`, feeding them the **normalized height** in place of the
raw height. All those lemmas are roof independent (statements about points of `X × ℝ`, not about
classes), so the embedding metric, its triangle inequality and its point separation descend with the
same `2 × 2` Kuratowski elimination.

The one ingredient not inherited from the constant-roof module is the **canonical
fundamental-domain representative**
`suspensionRepVar` for a variable roof: with `τ ≥ ρmin > 0` every orbit meets the box
`suspensionDomain τ = {(x, s) | 0 ≤ s < τ x}` exactly once (the roof-cocycle `roofSum n x` is
strictly increasing in `n` with gaps `≥ ρmin`, so it partitions `ℝ`), and the unique meeting index
descends through the quotient to a genuine representative map. The realisation cost of the variable
roof shows up only in the **flow-Lipschitz constant**: the flow moves the raw height at unit speed,
hence the normalized height at speed `1 / τ ≤ 1 / ρmin`, giving
`embDistVar (ζ_a q) (ζ_b q) ≤ (5 / ρmin) · |a − b|`.

## Route β is a wall

The alternative of *rescaling a variable roof to a constant roof* is **not** available: the time
change realising `τ` as a constant is bi-Lipschitz only when `τ` is cohomologous to a constant
(`τ = c + φ ∘ T − φ`), which is precisely the circular hypothesis one wants to avoid. That is why we
build the metric directly on the normalized fibre coordinate.

## Main definitions

* `ErgodicTheory.suspensionRepVar`: the canonical `suspensionDomain τ`-representative `(X × ℝ)` of a
  class, selected as the unique orbit representative in the fundamental box.
* `ErgodicTheory.normHeightVar`: the normalized fibre height `s / τ x ∈ [0, 1)` of the canonical
  representative.
* `ErgodicTheory.embDistVar`: the honest embedding metric on `SuspensionSpace T hτ` for a variable
  roof, the sum of the two Kuratowski test-bundle distances and the circle-height distance evaluated
  at the *normalized* representatives.

## Main results

* `suspensionRepVar_mem_domain`, `suspensionMk_suspensionRepVar`, `suspensionRepVar_mk`,
  `suspensionRepVar_injective`: the representative map lands in the box, is a section of the
  quotient, is the identity on the box, and is injective.
* `embDistVar_nonneg`, `embDistVar_self`, `embDistVar_comm`, **`embDistVar_triangle`**,
  **`embDistVar_eq_zero`**: `embDistVar` is a genuine metric.
* `embDistVar_le_three_hlen`, `embDistVar_vertical_le`, `embDistVar_seam_le`: the bi-Lipschitz
  **upper** move bounds (the vertical constant picks up `1 / ρmin`).
* `hgtVar_le_embDistVar`, `dist_base_le_embDistVar`, `dist_map_le_embDistVar_wrap`: the **lower**
  comparison primitives (height gap, mid-band base recovery, seam wrap).
* `embDistVar_le_five`, `embDistVar_step_le`, **`embDistVar_flow_le`**: the flow is
  `(5 / ρmin)`-Lipschitz in time on each orbit.

The metric-space topology packaging and Polishness (deliverable 8) are left concrete: they mirror
the constant-roof `embDist_continuous` / `suspensionMetricSpace` / `suspensionPolish` development,
whose seam-strip gluing becomes roof dependent (`{(x, s) | roofSum n x ≤ s < roofSum (n+1) x}`) and
requires `τ` continuous; the substantive metric content (1–7 above) is complete and sorry-free.
-/

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace ErgodicTheory

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-! ### Roof-free raw test-function primitives

These are the raw (point-level, not class-level) Kuratowski estimates that the constant-roof file
uses internally; we extract them as standalone lemmas because the variable-roof metric reuses them
at *normalized* heights. They are entirely roof independent. -/

/-- **Raw base-recovery bound.** The `2 × 2` Kuratowski elimination at a common height `u ∈ [0, 1]`:
`((1 − u)·u)·d(x, y)` is recovered from the two weighted test-bundle distances. -/
theorem dist_base_mul_le (hdiam : ∀ a b : X, dist a b ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x y : X) :
    (1 - u) * u * dist x y
      ≤ (1 - (1 - u) ^ 2) * dist (muFun T hdiam (x, u)) (muFun T hdiam (y, u))
        + u * dist (nuFun T hdiam (x, u)) (nuFun T hdiam (y, u)) := by
  have hkey : ((1 - u) * u) • (kur hdiam x - kur hdiam y)
      = (1 - (1 - u) ^ 2) • (muFun T hdiam (x, u) - muFun T hdiam (y, u))
        - u • (nuFun T hdiam (x, u) - nuFun T hdiam (y, u)) := by
    simp only [muFun, nuFun]; module
  have hc1 : (0 : ℝ) ≤ 1 - (1 - u) ^ 2 := by nlinarith
  have hlhs : (1 - u) * u * dist x y = ‖((1 - u) * u) • (kur hdiam x - kur hdiam y)‖ := by
    rw [norm_smul, Real.norm_eq_abs, norm_kur_sub, abs_of_nonneg (mul_nonneg (by linarith) hu0)]
  rw [hlhs, hkey]
  calc ‖(1 - (1 - u) ^ 2) • (muFun T hdiam (x, u) - muFun T hdiam (y, u))
          - u • (nuFun T hdiam (x, u) - nuFun T hdiam (y, u))‖
      ≤ ‖(1 - (1 - u) ^ 2) • (muFun T hdiam (x, u) - muFun T hdiam (y, u))‖
        + ‖u • (nuFun T hdiam (x, u) - nuFun T hdiam (y, u))‖ := norm_sub_le _ _
    _ = (1 - (1 - u) ^ 2) * dist (muFun T hdiam (x, u)) (muFun T hdiam (y, u))
        + u * dist (nuFun T hdiam (x, u)) (nuFun T hdiam (y, u)) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc1,
          abs_of_nonneg hu0, ← dist_eq_norm, ← dist_eq_norm]

/-- **Raw seam `muFun` bound.** At a height `u ∈ [0, 1]` the `muFun` bundle is within `1 − u` of its
seam image `muFun (T x, 0) = kur (T x)`. -/
theorem dist_muFun_seam_le (hdiam : ∀ a b : X, dist a b ≤ 1) {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x : X) : dist (muFun T hdiam (x, u)) (muFun T hdiam (T x, 0)) ≤ 1 - u := by
  have hsub : muFun T hdiam (x, u) - muFun T hdiam (T x, 0)
      = (1 - u) • (kur hdiam x - kur hdiam (T x)) := by simp only [muFun]; module
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub, abs_of_nonneg (by linarith)]
  calc (1 - u) * dist x (T x) ≤ (1 - u) * 1 :=
        mul_le_mul_of_nonneg_left (hdiam _ _) (by linarith)
    _ = 1 - u := mul_one _

/-- **Raw seam `nuFun` bound.** At a height `u ∈ [0, 1]` the `nuFun` bundle is within `1 − u` of its
seam image `nuFun (T x, 0) = kur (T x)`. -/
theorem dist_nuFun_seam_le (hdiam : ∀ a b : X, dist a b ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x : X) : dist (nuFun T hdiam (x, u)) (nuFun T hdiam (T x, 0)) ≤ 1 - u := by
  have hsub : nuFun T hdiam (x, u) - nuFun T hdiam (T x, 0)
      = (1 - u) ^ 2 • (kur hdiam x - kur hdiam (T x)) := by simp only [nuFun]; module
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub, abs_of_nonneg (sq_nonneg _)]
  have hsq : (1 - u) ^ 2 ≤ 1 - u := by nlinarith
  calc (1 - u) ^ 2 * dist x (T x) ≤ (1 - u) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (hdiam _ _) (sq_nonneg _)
    _ = (1 - u) ^ 2 := mul_one _
    _ ≤ 1 - u := hsq

/-- **Raw seam-wrap bound.** For heights `s, t ∈ [0, 1)` the `T`-image distance `d(T x, y)` is
controlled by the `muFun` distance up to the seam slack `(1 − s) + t`. -/
theorem dist_map_le_wrap (hdiam : ∀ a b : X, dist a b ≤ 1) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) (x y : X) :
    dist (T x) y ≤ dist (muFun T hdiam (x, s)) (muFun T hdiam (y, t)) + (1 - s) + t := by
  have key : kur hdiam (T x) - kur hdiam y
      = (muFun T hdiam (x, s) - muFun T hdiam (y, t))
        + (1 - s) • (kur hdiam (T x) - kur hdiam x)
        + t • (kur hdiam (T y) - kur hdiam y) := by
    simp only [muFun]; module
  rw [← norm_kur_sub hdiam (T x) y, key]
  have e1 : ‖(1 - s) • (kur hdiam (T x) - kur hdiam x)‖ = (1 - s) * dist (T x) x := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2.le]), norm_kur_sub]
  have e2 : ‖t • (kur hdiam (T y) - kur hdiam y)‖ = t * dist (T y) y := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, norm_kur_sub]
  calc ‖(muFun T hdiam (x, s) - muFun T hdiam (y, t))
          + (1 - s) • (kur hdiam (T x) - kur hdiam x) + t • (kur hdiam (T y) - kur hdiam y)‖
      ≤ ‖(muFun T hdiam (x, s) - muFun T hdiam (y, t))
          + (1 - s) • (kur hdiam (T x) - kur hdiam x)‖
        + ‖t • (kur hdiam (T y) - kur hdiam y)‖ := norm_add_le _ _
    _ ≤ (‖muFun T hdiam (x, s) - muFun T hdiam (y, t)‖
          + ‖(1 - s) • (kur hdiam (T x) - kur hdiam x)‖)
        + ‖t • (kur hdiam (T y) - kur hdiam y)‖ := by gcongr; exact norm_add_le _ _
    _ = dist (muFun T hdiam (x, s)) (muFun T hdiam (y, t)) + (1 - s) * dist (T x) x
        + t * dist (T y) y := by rw [← dist_eq_norm, e1, e2]
    _ ≤ dist (muFun T hdiam (x, s)) (muFun T hdiam (y, t)) + (1 - s) + t := by
        have hA : (1 - s) * dist (T x) x ≤ (1 - s) :=
          mul_le_of_le_one_right (by linarith [hs.2.le]) (hdiam _ _)
        have hB : t * dist (T y) y ≤ t := mul_le_of_le_one_right ht.1 (hdiam _ _)
        linarith

/-! ### The variable-roof canonical representative

With `τ ≥ ρmin > 0` every orbit of the suspension `ℤ`-action meets the box `suspensionDomain τ`
exactly once (`suspension_exists_unique_act_mem`). We choose that unique meeting index and descend
the resulting box representative through the orbit quotient. -/

variable {ρmin : ℝ} (hρpos : 0 < ρmin) (hρ0 : ∀ x, ρmin ≤ τ x)

include hτ hρpos hρ0 in
/-- Point form of the exactly-once meeting: every point of `X × ℝ` has a unique action-index landing
it in the box. -/
theorem suspension_exists_unique_act_mem' (p : X × ℝ) :
    ∃! n : ℤ, suspensionAct T hτ n p ∈ suspensionDomain τ := by
  obtain ⟨x, s⟩ := p
  exact suspension_exists_unique_act_mem T hτ hρ0 hρpos x s

/-- The unique action-index landing `p` in the box. -/
def repIndexVar (p : X × ℝ) : ℤ :=
  (suspension_exists_unique_act_mem' T hτ hρpos hρ0 p).exists.choose

theorem repIndexVar_mem (p : X × ℝ) :
    suspensionAct T hτ (repIndexVar T hτ hρpos hρ0 p) p ∈ suspensionDomain τ :=
  (suspension_exists_unique_act_mem' T hτ hρpos hρ0 p).exists.choose_spec

theorem repIndexVar_unique (p : X × ℝ) {n : ℤ}
    (hn : suspensionAct T hτ n p ∈ suspensionDomain τ) : n = repIndexVar T hτ hρpos hρ0 p :=
  (suspension_exists_unique_act_mem' T hτ hρpos hρ0 p).unique hn (repIndexVar_mem T hτ hρpos hρ0 p)

/-- The raw box representative of a point: the box translate of `p` along its unique meeting
index. -/
def repRawVar (p : X × ℝ) : X × ℝ := suspensionAct T hτ (repIndexVar T hτ hρpos hρ0 p) p

theorem repRawVar_mem (p : X × ℝ) : repRawVar T hτ hρpos hρ0 p ∈ suspensionDomain τ :=
  repIndexVar_mem T hτ hρpos hρ0 p

/-- The raw box representative is invariant along the orbit. -/
theorem repRawVar_act (n : ℤ) (p : X × ℝ) :
    repRawVar T hτ hρpos hρ0 (suspensionAct T hτ n p) = repRawVar T hτ hρpos hρ0 p := by
  set k := repIndexVar T hτ hρpos hρ0 (suspensionAct T hτ n p) with hk
  have hmem : suspensionAct T hτ (k + n) p ∈ suspensionDomain τ := by
    rw [suspensionAct_add]
    exact repIndexVar_mem T hτ hρpos hρ0 (suspensionAct T hτ n p)
  have heq : k + n = repIndexVar T hτ hρpos hρ0 p := repIndexVar_unique T hτ hρpos hρ0 p hmem
  change suspensionAct T hτ k (suspensionAct T hτ n p)
    = suspensionAct T hτ (repIndexVar T hτ hρpos hρ0 p) p
  rw [← suspensionAct_add, heq]

/-- The **variable-roof canonical representative** of a class: the raw box representative descended
through the orbit quotient. -/
def suspensionRepVar (q : SuspensionSpace T hτ) : X × ℝ :=
  letI := suspensionAddAction T hτ
  Quotient.lift (repRawVar T hτ hρpos hρ0)
    (fun p q h => by
      obtain ⟨n, hn⟩ := h
      have hn' : suspensionAct T hτ n q = p := hn
      rw [← hn', repRawVar_act]) q

@[simp] theorem suspensionRepVar_mk_raw (p : X × ℝ) :
    suspensionRepVar T hτ hρpos hρ0 (suspensionMk T hτ p) = repRawVar T hτ hρpos hρ0 p := rfl

/-- The canonical representative lands in the fundamental box `suspensionDomain τ`. -/
theorem suspensionRepVar_mem_domain (q : SuspensionSpace T hτ) :
    suspensionRepVar T hτ hρpos hρ0 q ∈ suspensionDomain τ := by
  induction q using Quotient.inductionOn with
  | _ p => exact repRawVar_mem T hτ hρpos hρ0 p

theorem suspensionRepVar_nonneg (q : SuspensionSpace T hτ) :
    0 ≤ (suspensionRepVar T hτ hρpos hρ0 q).2 :=
  (suspensionRepVar_mem_domain T hτ hρpos hρ0 q).1

theorem suspensionRepVar_lt (q : SuspensionSpace T hτ) :
    (suspensionRepVar T hτ hρpos hρ0 q).2 < τ (suspensionRepVar T hτ hρpos hρ0 q).1 :=
  (suspensionRepVar_mem_domain T hτ hρpos hρ0 q).2

/-- The class is the projection of its own canonical representative. -/
theorem suspensionMk_suspensionRepVar (q : SuspensionSpace T hτ) :
    suspensionMk T hτ (suspensionRepVar T hτ hρpos hρ0 q) = q := by
  induction q using Quotient.inductionOn with
  | _ p => exact suspensionMk_act T hτ (repIndexVar T hτ hρpos hρ0 p) p

/-- On the box, the canonical representative is the identity. -/
theorem suspensionRepVar_mk {x : X} {s : ℝ} (h : (x, s) ∈ suspensionDomain τ) :
    suspensionRepVar T hτ hρpos hρ0 (suspensionMk T hτ (x, s)) = (x, s) := by
  change repRawVar T hτ hρpos hρ0 (x, s) = (x, s)
  have h0 : suspensionAct T hτ 0 (x, s) ∈ suspensionDomain τ := by
    rw [suspensionAct_zero]; exact h
  have hidx : (0 : ℤ) = repIndexVar T hτ hρpos hρ0 (x, s) := repIndexVar_unique T hτ hρpos hρ0 _ h0
  change suspensionAct T hτ (repIndexVar T hτ hρpos hρ0 (x, s)) (x, s) = (x, s)
  rw [← hidx, suspensionAct_zero]

/-- The canonical representative map is injective. -/
theorem suspensionRepVar_injective {p q : SuspensionSpace T hτ}
    (h : suspensionRepVar T hτ hρpos hρ0 p = suspensionRepVar T hτ hρpos hρ0 q) : p = q := by
  have hc := congrArg (suspensionMk T hτ) h
  rwa [suspensionMk_suspensionRepVar, suspensionMk_suspensionRepVar] at hc

/-! ### The normalized height and the embedding metric -/

/-- The **normalized fibre height** `s / τ x ∈ [0, 1)` of the canonical representative `(x, s)`. -/
def normHeightVar (q : SuspensionSpace T hτ) : ℝ :=
  (suspensionRepVar T hτ hρpos hρ0 q).2 / τ (suspensionRepVar T hτ hρpos hρ0 q).1

/-- The roof value at the base point of the canonical representative is positive. -/
theorem roof_rep_pos (q : SuspensionSpace T hτ) :
    0 < τ (suspensionRepVar T hτ hρpos hρ0 q).1 :=
  lt_of_lt_of_le hρpos (hρ0 _)

/-- The normalized height lies in `[0, 1)`. -/
theorem normHeightVar_mem_Ico (q : SuspensionSpace T hτ) :
    normHeightVar T hτ hρpos hρ0 q ∈ Set.Ico (0 : ℝ) 1 := by
  have hpos := roof_rep_pos T hτ hρpos hρ0 q
  refine ⟨div_nonneg (suspensionRepVar_nonneg T hτ hρpos hρ0 q) hpos.le, ?_⟩
  exact (div_lt_one hpos).mpr (suspensionRepVar_lt T hτ hρpos hρ0 q)

theorem normHeightVar_nonneg (q : SuspensionSpace T hτ) : 0 ≤ normHeightVar T hτ hρpos hρ0 q :=
  (normHeightVar_mem_Ico T hτ hρpos hρ0 q).1

theorem normHeightVar_lt_one (q : SuspensionSpace T hτ) : normHeightVar T hτ hρpos hρ0 q < 1 :=
  (normHeightVar_mem_Ico T hτ hρpos hρ0 q).2

/-- The normalized height of a box point `[x, s]` is `s / τ x`. -/
theorem normHeightVar_mk {x : X} {s : ℝ} (h : (x, s) ∈ suspensionDomain τ) :
    normHeightVar T hτ hρpos hρ0 (suspensionMk T hτ (x, s)) = s / τ x := by
  unfold normHeightVar
  rw [suspensionRepVar_mk T hτ hρpos hρ0 h]

/-- The **variable-roof embedding distance**: the sum of the two Kuratowski test-bundle distances
and the circle-height distance, evaluated at the *normalized* canonical representatives. -/
def embDistVar (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) : ℝ :=
  dist (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
      (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q))
    + dist (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
        (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q))
    + hgt (normHeightVar T hτ hρpos hρ0 p) (normHeightVar T hτ hρpos hρ0 q)

/-- Evaluation of `embDistVar` on two box points `[x, s]`, `[y, t]` (with `(x, s), (y, t)` in the
box), in terms of their normalized heights `s / τ x`, `t / τ y`. -/
theorem embDistVar_box (hdiam : ∀ a b : X, dist a b ≤ 1) {x : X} {s : ℝ} {y : X} {t : ℝ}
    (hd : (x, s) ∈ suspensionDomain τ) (hd' : (y, t) ∈ suspensionDomain τ) :
    embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
      = dist (muFun T hdiam (x, s / τ x)) (muFun T hdiam (y, t / τ y))
        + dist (nuFun T hdiam (x, s / τ x)) (nuFun T hdiam (y, t / τ y))
        + hgt (s / τ x) (t / τ y) := by
  unfold embDistVar
  rw [normHeightVar_mk T hτ hρpos hρ0 hd, normHeightVar_mk T hτ hρpos hρ0 hd',
    suspensionRepVar_mk T hτ hρpos hρ0 hd, suspensionRepVar_mk T hτ hρpos hρ0 hd']

/-- The height gap between two normalized representatives has absolute value at most `1`. -/
theorem abs_normHeightVar_sub_le (p q : SuspensionSpace T hτ) :
    |normHeightVar T hτ hρpos hρ0 p - normHeightVar T hτ hρpos hρ0 q| ≤ 1 := by
  have hp := normHeightVar_mem_Ico T hτ hρpos hρ0 p
  have hq := normHeightVar_mem_Ico T hτ hρpos hρ0 q
  rw [abs_le]; exact ⟨by linarith [hp.1, hq.2], by linarith [hp.2, hq.1]⟩

/-- The embedding distance is nonnegative. -/
theorem embDistVar_nonneg (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    0 ≤ embDistVar T hτ hρpos hρ0 hdiam p q := by
  have hh := hgt_nonneg (abs_normHeightVar_sub_le T hτ hρpos hρ0 p q)
  have h1 : (0 : ℝ) ≤ dist
    (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
    (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q)) :=
    dist_nonneg
  have h2 : (0 : ℝ) ≤ dist
    (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
    (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q)) :=
    dist_nonneg
  unfold embDistVar; linarith

/-- The embedding distance to self is zero. -/
@[simp] theorem embDistVar_self (hdiam : ∀ a b : X, dist a b ≤ 1) (p : SuspensionSpace T hτ) :
    embDistVar T hτ hρpos hρ0 hdiam p p = 0 := by
  unfold embDistVar; simp

/-- The embedding distance is symmetric. -/
theorem embDistVar_comm (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    embDistVar T hτ hρpos hρ0 hdiam p q = embDistVar T hτ hρpos hρ0 hdiam q p := by
  unfold embDistVar
  rw [dist_comm (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, _)),
    dist_comm (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, _)),
    hgt_comm (normHeightVar T hτ hρpos hρ0 p)]

/-- **Triangle inequality** for the embedding distance. -/
theorem embDistVar_triangle (hdiam : ∀ a b : X, dist a b ≤ 1) (p q r : SuspensionSpace T hτ) :
    embDistVar T hτ hρpos hρ0 hdiam p r
      ≤ embDistVar T hτ hρpos hρ0 hdiam p q + embDistVar T hτ hρpos hρ0 hdiam q r := by
  have hμ := dist_triangle
    (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
    (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q))
    (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 r).1, normHeightVar T hτ hρpos hρ0 r))
  have hν := dist_triangle
    (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
    (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q))
    (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 r).1, normHeightVar T hτ hρpos hρ0 r))
  have hh := hgt_triangle (normHeightVar_mem_Ico T hτ hρpos hρ0 p)
    (normHeightVar_mem_Ico T hτ hρpos hρ0 q) (normHeightVar_mem_Ico T hτ hρpos hρ0 r)
  unfold embDistVar; linarith

/-- **Separation.** A zero embedding distance forces the classes to coincide: the height part gives
equal normalized heights, the two Kuratowski parts give `kur x = kur y` (hence `x = y`), and equal
normalized heights at a common base give equal raw heights. -/
theorem embDistVar_eq_zero (hdiam : ∀ a b : X, dist a b ≤ 1) {p q : SuspensionSpace T hτ}
    (h : embDistVar T hτ hρpos hρ0 hdiam p q = 0) : p = q := by
  set x := (suspensionRepVar T hτ hρpos hρ0 p).1 with hx
  set y := (suspensionRepVar T hτ hρpos hρ0 q).1 with hy
  set up := normHeightVar T hτ hρpos hρ0 p with hup
  set uq := normHeightVar T hτ hρpos hρ0 q with huq
  have hupI : up ∈ Set.Ico (0 : ℝ) 1 := normHeightVar_mem_Ico T hτ hρpos hρ0 p
  have huqI : uq ∈ Set.Ico (0 : ℝ) 1 := normHeightVar_mem_Ico T hτ hρpos hρ0 q
  have habs : |up - uq| ≤ 1 := abs_normHeightVar_sub_le T hτ hρpos hρ0 p q
  have hμnn : (0 : ℝ) ≤ dist (muFun T hdiam (x, up)) (muFun T hdiam (y, uq)) := dist_nonneg
  have hνnn : (0 : ℝ) ≤ dist (nuFun T hdiam (x, up)) (nuFun T hdiam (y, uq)) := dist_nonneg
  have hhnn : 0 ≤ hgt up uq := hgt_nonneg habs
  have hsum : dist (muFun T hdiam (x, up)) (muFun T hdiam (y, uq))
      + dist (nuFun T hdiam (x, up)) (nuFun T hdiam (y, uq)) + hgt up uq = 0 := h
  have hμ0 : dist (muFun T hdiam (x, up)) (muFun T hdiam (y, uq)) = 0 := by linarith
  have hν0 : dist (nuFun T hdiam (x, up)) (nuFun T hdiam (y, uq)) = 0 := by linarith
  have hh0 : hgt up uq = 0 := by linarith
  -- normalized heights agree
  have hheq : up = uq := by
    have hpos : (0 : ℝ) < 1 - |up - uq| := by
      have : |up - uq| < 1 := by rw [abs_lt]; constructor <;> linarith [hupI.1, hupI.2, huqI.1,
        huqI.2]
      linarith
    rw [hgt] at hh0
    have habs0 : |up - uq| = 0 := by
      rcases min_eq_iff.mp hh0 with ⟨e, _⟩ | ⟨e, _⟩
      · exact e
      · linarith
    have := abs_eq_zero.mp habs0; linarith
  have hmu' : muFun T hdiam (x, up) = muFun T hdiam (y, uq) := dist_eq_zero.mp hμ0
  have hnu' : nuFun T hdiam (x, up) = nuFun T hdiam (y, uq) := dist_eq_zero.mp hν0
  rw [hheq] at hmu' hnu'
  simp only [muFun, nuFun] at hmu' hnu'
  -- recover the base equality
  have hbase : kur hdiam x = kur hdiam y := by
    rcases eq_or_lt_of_le huqI.1 with hs0 | hspos
    · rw [← hs0] at hmu'; simpa using hmu'
    · have hspos' : (0 : ℝ) < uq := hspos
      have expand : ((1 - uq) * uq) • kur hdiam x
          = (1 - (1 - uq) ^ 2) • ((1 - uq) • kur hdiam x + uq • kur hdiam (T x))
            - uq • ((1 - uq) ^ 2 • kur hdiam x + (1 - (1 - uq) ^ 2) • kur hdiam (T x)) := by
        module
      have expand2 : ((1 - uq) * uq) • kur hdiam y
          = (1 - (1 - uq) ^ 2) • ((1 - uq) • kur hdiam y + uq • kur hdiam (T y))
            - uq • ((1 - uq) ^ 2 • kur hdiam y + (1 - (1 - uq) ^ 2) • kur hdiam (T y)) := by
        module
      have key : ((1 - uq) * uq) • kur hdiam x = ((1 - uq) * uq) • kur hdiam y := by
        rw [expand, expand2, hmu', hnu']
      have key0 : ((1 - uq) * uq) • (kur hdiam x - kur hdiam y) = 0 := by
        rw [smul_sub, key, sub_self]
      have hcne : (1 - uq) * uq ≠ 0 := ne_of_gt (mul_pos (by linarith [huqI.2]) hspos')
      rcases smul_eq_zero.mp key0 with hc | hxy
      · exact absurd hc hcne
      · exact sub_eq_zero.mp hxy
  have hxy : x = y := by
    have hd := (dist_kur hdiam x y).symm
    rw [hbase, dist_self] at hd
    exact dist_eq_zero.mp hd
  -- equal normalized heights + equal base ⇒ equal raw heights ⇒ equal representatives
  have hpospx : 0 < τ x := by rw [hx]; exact roof_rep_pos T hτ hρpos hρ0 p
  have e1 : up = (suspensionRepVar T hτ hρpos hρ0 p).2 / τ x := by
    rw [hup]; unfold normHeightVar; rw [hx]
  have e2 : uq = (suspensionRepVar T hτ hρpos hρ0 q).2 / τ y := by
    rw [huq]; unfold normHeightVar; rw [hy]
  have hue : (suspensionRepVar T hτ hρpos hρ0 p).2 / τ x
      = (suspensionRepVar T hτ hρpos hρ0 q).2 / τ x := by
    rw [← hxy] at e2; rw [← e1, ← e2]; exact hheq
  rw [div_eq_div_iff (ne_of_gt hpospx) (ne_of_gt hpospx)] at hue
  have hraw : (suspensionRepVar T hτ hρpos hρ0 p).2 = (suspensionRepVar T hτ hρpos hρ0 q).2 :=
    mul_right_cancel₀ (ne_of_gt hpospx) hue
  have hrep : suspensionRepVar T hτ hρpos hρ0 p = suspensionRepVar T hτ hρpos hρ0 q :=
    Prod.ext (hx.symm.trans (hxy.trans hy)) hraw
  exact suspensionRepVar_injective T hτ hρpos hρ0 hrep

/-! ### Upper move bounds -/

/-- **Horizontal upper bound.** Two classes at a common normalized height `u ∈ [0, 1)` (raw heights
`u · τ x` and `u · τ y`) are at embedding distance at most `3 · hlen u x y`. -/
theorem embDistVar_le_three_hlen (hdiam : ∀ a b : X, dist a b ≤ 1) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (x y : X) :
    embDistVar T hτ hρpos hρ0 hdiam
        (suspensionMk T hτ (x, u * τ x)) (suspensionMk T hτ (y, u * τ y)) ≤ 3 * hlen T u x y := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hdx : (x, u * τ x) ∈ suspensionDomain τ :=
    ⟨mul_nonneg hu.1 hxpos.le, by nlinarith [hu.2, hxpos]⟩
  have hdy : (y, u * τ y) ∈ suspensionDomain τ :=
    ⟨mul_nonneg hu.1 hypos.le, by nlinarith [hu.2, hypos]⟩
  rw [embDistVar_box T hτ hρpos hρ0 hdiam hdx hdy]
  rw [mul_div_cancel_right₀ u (ne_of_gt hxpos), mul_div_cancel_right₀ u (ne_of_gt hypos)]
  have hmu := dist_muFun_le_hlen T hdiam hu.1 hu.2.le x y
  have hnu := dist_nuFun_le T hdiam hu.1 hu.2.le x y
  have hdxy : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hdT : (0 : ℝ) ≤ dist (T x) (T y) := dist_nonneg
  have hnu2 : (1 - u) ^ 2 * dist x y + (1 - (1 - u) ^ 2) * dist (T x) (T y)
      ≤ 2 * hlen T u x y := by
    simp only [hlen]
    have e1 : (1 - u) ^ 2 * dist x y ≤ (1 - u) * dist x y := by
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - u by linarith [hu.2.le]) hu.1) hdxy]
    have e2 : (1 - (1 - u) ^ 2) * dist (T x) (T y) ≤ 2 * (u * dist (T x) (T y)) := by
      nlinarith [mul_nonneg (sq_nonneg u) hdT]
    have e3 : (0 : ℝ) ≤ (1 - u) * dist x y := mul_nonneg (by linarith [hu.2.le]) hdxy
    linarith
  have hz : hgt u u = 0 := hgt_self u
  linarith

/-- **Vertical upper bound.** Two classes on a common fibre at raw heights `s, s' ∈ [0, τ x)` are at
embedding distance at most `4 · |s − s'| / ρmin` (the flow-time Lipschitz constant picks up
`1 / ρmin`). -/
theorem embDistVar_vertical_le (hdiam : ∀ a b : X, dist a b ≤ 1) (x : X) {s s' : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (τ x)) (hs' : s' ∈ Set.Ico (0 : ℝ) (τ x)) :
    embDistVar T hτ hρpos hρ0 hdiam
        (suspensionMk T hτ (x, s)) (suspensionMk T hτ (x, s')) ≤ 4 * |s - s'| / ρmin := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hd : (x, s) ∈ suspensionDomain τ := ⟨hs.1, hs.2⟩
  have hd' : (x, s') ∈ suspensionDomain τ := ⟨hs'.1, hs'.2⟩
  rw [embDistVar_box T hτ hρpos hρ0 hdiam hd hd']
  have hu : s / τ x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hxpos.le, (div_lt_one hxpos).mpr hs.2⟩
  have hu' : s' / τ x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hs'.1 hxpos.le, (div_lt_one hxpos).mpr hs'.2⟩
  have hmu := dist_muFun_sameBase_le T hdiam x (s / τ x) (s' / τ x)
  have hnu := dist_nuFun_sameBase_le T hdiam x hu.1 hu.2.le hu'.1 hu'.2.le
  have hh := hgt_le_abs (s / τ x) (s' / τ x)
  have hval : |s / τ x - s' / τ x| = |s - s'| / τ x := by
    rw [div_sub_div_same, abs_div, abs_of_pos hxpos]
  have hkey : dist (muFun T hdiam (x, s / τ x)) (muFun T hdiam (x, s' / τ x))
      + dist (nuFun T hdiam (x, s / τ x)) (nuFun T hdiam (x, s' / τ x))
        + hgt (s / τ x) (s' / τ x) ≤ 4 * (|s - s'| / τ x) := by
    rw [hval] at hmu hnu hh; linarith [hmu, hnu, hh]
  refine hkey.trans ?_
  have hdiv : |s - s'| / τ x ≤ |s - s'| / ρmin :=
    div_le_div_of_nonneg_left (abs_nonneg _) hρpos (hρ0 x)
  rw [mul_div_assoc]
  linarith [hdiv]

/-- **Seam upper bound.** A class `[x, s]` (raw height `s ∈ [0, τ x)`) is within `3 · (1 − s / τ x)`
of the seam image `[T x, 0]`. -/
theorem embDistVar_seam_le (hdiam : ∀ a b : X, dist a b ≤ 1) (x : X) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (τ x)) :
    embDistVar T hτ hρpos hρ0 hdiam
        (suspensionMk T hτ (x, s)) (suspensionMk T hτ (T x, 0)) ≤ 3 * (1 - s / τ x) := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hTpos : 0 < τ (T x) := lt_of_lt_of_le hρpos (hρ0 (T x))
  have hd : (x, s) ∈ suspensionDomain τ := ⟨hs.1, hs.2⟩
  have hd' : (T x, (0 : ℝ)) ∈ suspensionDomain τ := ⟨le_refl 0, hTpos⟩
  rw [embDistVar_box T hτ hρpos hρ0 hdiam hd hd', zero_div]
  have hu : s / τ x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hxpos.le, (div_lt_one hxpos).mpr hs.2⟩
  have hmu := dist_muFun_seam_le T hdiam hu.1 hu.2.le x
  have hnu := dist_nuFun_seam_le T hdiam hu.1 hu.2.le x
  have hh : hgt (s / τ x) 0 ≤ 1 - s / τ x := by
    calc hgt (s / τ x) 0 ≤ 1 - |s / τ x - 0| := hgt_le_one_sub _ _
      _ = 1 - s / τ x := by rw [sub_zero, abs_of_nonneg hu.1]
  linarith

/-! ### Lower comparison primitives -/

/-- **Lower-bound primitive.** The normalized height gap is controlled by the embedding distance. -/
theorem hgtVar_le_embDistVar (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    hgt (normHeightVar T hτ hρpos hρ0 p) (normHeightVar T hτ hρpos hρ0 q)
      ≤ embDistVar T hτ hρpos hρ0 hdiam p q := by
  have h1 : (0 : ℝ) ≤ dist
    (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
    (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q)) :=
    dist_nonneg
  have h2 : (0 : ℝ) ≤ dist
    (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
    (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q)) :=
    dist_nonneg
  unfold embDistVar; linarith

/-- **Mid-band base recovery.** For two classes at a common normalized height `u ∈ [1/8, 7/8]` (raw
heights `u · τ x`, `u · τ y`) the base distance is controlled by the embedding distance:
`dist x y ≤ (64/7) · embDistVar`. The `2 × 2` Kuratowski elimination recovers `((1 − u)·u)·(kur x −
kur y)` with `(1 − u)·u ≥ 7/64`. -/
theorem dist_base_le_embDistVar (hdiam : ∀ a b : X, dist a b ≤ 1) {u : ℝ}
    (hu : u ∈ Set.Icc (1 / 8 : ℝ) (7 / 8)) (x y : X) :
    dist x y ≤ (64 / 7) *
      embDistVar T hτ hρpos hρ0 hdiam
        (suspensionMk T hτ (x, u * τ x)) (suspensionMk T hτ (y, u * τ y)) := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hu0 : (0 : ℝ) ≤ u := by linarith [hu.1]
  have hu1 : u ≤ 1 := by linarith [hu.2]
  have hu1' : u < 1 := by linarith [hu.2]
  have huI : u ∈ Set.Ico (0 : ℝ) 1 := ⟨hu0, hu1'⟩
  have hdx : (x, u * τ x) ∈ suspensionDomain τ :=
    ⟨mul_nonneg hu0 hxpos.le, by nlinarith [mul_pos (show (0 : ℝ) < 1 - u by linarith) hxpos]⟩
  have hdy : (y, u * τ y) ∈ suspensionDomain τ :=
    ⟨mul_nonneg hu0 hypos.le, by nlinarith [mul_pos (show (0 : ℝ) < 1 - u by linarith) hypos]⟩
  set E := embDistVar T hτ hρpos hρ0 hdiam
    (suspensionMk T hτ (x, u * τ x)) (suspensionMk T hτ (y, u * τ y)) with hEdef
  have hsum : dist (muFun T hdiam (x, u)) (muFun T hdiam (y, u))
      + dist (nuFun T hdiam (x, u)) (nuFun T hdiam (y, u)) = E := by
    rw [hEdef, embDistVar_box T hτ hρpos hρ0 hdiam hdx hdy,
      mul_div_cancel_right₀ u (ne_of_gt hxpos), mul_div_cancel_right₀ u (ne_of_gt hypos), hgt_self,
      add_zero]
  have hbase := dist_base_mul_le T hdiam hu0 hu1 x y
  have hc1 : (0 : ℝ) ≤ 1 - (1 - u) ^ 2 := by nlinarith
  have hμnn : (0 : ℝ) ≤ dist (muFun T hdiam (x, u)) (muFun T hdiam (y, u)) := dist_nonneg
  have hνnn : (0 : ℝ) ≤ dist (nuFun T hdiam (x, u)) (nuFun T hdiam (y, u)) := dist_nonneg
  have hwle : (1 - (1 - u) ^ 2) * dist (muFun T hdiam (x, u)) (muFun T hdiam (y, u))
      + u * dist (nuFun T hdiam (x, u)) (nuFun T hdiam (y, u)) ≤ E := by
    have h1 : (1 - (1 - u) ^ 2) * dist (muFun T hdiam (x, u)) (muFun T hdiam (y, u))
        ≤ dist (muFun T hdiam (x, u)) (muFun T hdiam (y, u)) := by nlinarith
    have h2 : u * dist (nuFun T hdiam (x, u)) (nuFun T hdiam (y, u))
        ≤ dist (nuFun T hdiam (x, u)) (nuFun T hdiam (y, u)) := by nlinarith
    linarith [hsum]
  have hcoeff : (7 : ℝ) / 64 ≤ (1 - u) * u := by nlinarith [hu.1, hu.2]
  have hdxy : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hfin : ((1 - u) * u) * dist x y ≤ E := le_trans hbase hwle
  have hstep : (7 / 64 : ℝ) * dist x y ≤ E :=
    le_trans (mul_le_mul_of_nonneg_right hcoeff hdxy) hfin
  linarith

/-- **Seam-wrap lower comparison.** For canonical box points `[x, s]`, `[y, t]` the `T`-image
distance is controlled by the embedding distance up to the seam slack
`(1 − s / τ x) + t / τ y`. -/
theorem dist_map_le_embDistVar_wrap (hdiam : ∀ a b : X, dist a b ≤ 1) {x : X} {s : ℝ} {y : X}
    {t : ℝ} (hs : (x, s) ∈ suspensionDomain τ) (ht : (y, t) ∈ suspensionDomain τ) :
    dist (T x) y
      ≤ embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
        + (1 - s / τ x) + t / τ y := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hu : s / τ x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hxpos.le, (div_lt_one hxpos).mpr hs.2⟩
  have hu' : t / τ y ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hypos.le, (div_lt_one hypos).mpr ht.2⟩
  have hwrap := dist_map_le_wrap T hdiam hu hu' x y
  have hmuE : dist (muFun T hdiam (x, s / τ x)) (muFun T hdiam (y, t / τ y))
      ≤ embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t)) := by
    rw [embDistVar_box T hτ hρpos hρ0 hdiam hs ht]
    have hνnn : (0 : ℝ) ≤ dist (nuFun T hdiam (x, s / τ x)) (nuFun T hdiam (y, t / τ y)) :=
      dist_nonneg
    have hhnn : 0 ≤ hgt (s / τ x) (t / τ y) := hgt_nonneg (by
      rw [abs_le]; exact ⟨by linarith [hu.1, hu'.2], by linarith [hu.2, hu'.1]⟩)
    linarith
  linarith

/-! ### The flow-Lipschitz estimate

The suspension flow moves the raw height at unit speed, hence the normalized height at speed
`1 / τ ≤ 1 / ρmin`. A time step below `ρmin` crosses at most one seam (consecutive seams are
`≥ ρmin` apart in time), so the vertical and seam bounds combine to a `(4 / ρmin)`-Lipschitz
step; the global bound `embDistVar ≤ 5` closes the large-step case. -/

/-- **Global bound.** The embedding distance never exceeds `5` (roof independent: normalized heights
lie in `[0, 1)`, the Kuratowski parts are `≤ 2` and the height part `≤ 1`). -/
theorem embDistVar_le_five (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    embDistVar T hτ hρpos hρ0 hdiam p q ≤ 5 := by
  have hup := normHeightVar_mem_Ico T hτ hρpos hρ0 p
  have huq := normHeightVar_mem_Ico T hτ hρpos hρ0 q
  have hμ : dist
      (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
      (muFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q))
      ≤ 2 := by
    rw [dist_eq_norm]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_muFun_le T hdiam hup.1 hup.2.le (suspensionRepVar T hτ hρpos hρ0 p).1
    have h2 := norm_muFun_le T hdiam huq.1 huq.2.le (suspensionRepVar T hτ hρpos hρ0 q).1
    linarith
  have hν : dist
      (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 p).1, normHeightVar T hτ hρpos hρ0 p))
      (nuFun T hdiam ((suspensionRepVar T hτ hρpos hρ0 q).1, normHeightVar T hτ hρpos hρ0 q))
      ≤ 2 := by
    rw [dist_eq_norm]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_nuFun_le T hdiam hup.1 hup.2.le (suspensionRepVar T hτ hρpos hρ0 p).1
    have h2 := norm_nuFun_le T hdiam huq.1 huq.2.le (suspensionRepVar T hτ hρpos hρ0 q).1
    linarith
  have hab : (0 : ℝ) ≤ |normHeightVar T hτ hρpos hρ0 p - normHeightVar T hτ hρpos hρ0 q| :=
    abs_nonneg _
  have hh : hgt (normHeightVar T hτ hρpos hρ0 p) (normHeightVar T hτ hρpos hρ0 q) ≤ 1 :=
    (hgt_le_one_sub _ _).trans (by linarith)
  unfold embDistVar; linarith

/-- **Unit-step flow bound.** For a time step `0 ≤ δ < ρmin`, the flow move `q₀ ↦ ζ_δ q₀` has
embedding distance at most `4 · δ / ρmin`. A step below `ρmin` crosses at most one seam, and the
vertical + seam bounds combine. -/
theorem embDistVar_step_le (hdiam : ∀ a b : X, dist a b ≤ 1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < ρmin) (q : SuspensionSpace T hτ) :
    embDistVar T hτ hρpos hρ0 hdiam q (suspensionFlowMap T hτ δ q) ≤ 4 * δ / ρmin := by
  set x := (suspensionRepVar T hτ hρpos hρ0 q).1 with hx
  set s := (suspensionRepVar T hτ hρpos hρ0 q).2 with hs
  have hxpos : 0 < τ x := by rw [hx]; exact roof_rep_pos T hτ hρpos hρ0 q
  have hs0 : 0 ≤ s := by rw [hs]; exact suspensionRepVar_nonneg T hτ hρpos hρ0 q
  have hslt : s < τ x := by rw [hs, hx]; exact suspensionRepVar_lt T hτ hρpos hρ0 q
  have hrep : suspensionRepVar T hτ hρpos hρ0 q = (x, s) := by rw [hx, hs]
  have hq0 : q = suspensionMk T hτ (x, s) := by
    rw [← hrep]; exact (suspensionMk_suspensionRepVar T hτ hρpos hρ0 q).symm
  have hflow : suspensionFlowMap T hτ δ q = suspensionMk T hτ (x, s + δ) := by
    rw [hq0, suspensionFlowMap_mk, suspensionTranslate_apply]
  rw [hflow, hq0]
  by_cases hcross : s + δ < τ x
  · -- no seam crossed: pure vertical move on fibre `x`
    have hsd : (s + δ) ∈ Set.Ico (0 : ℝ) (τ x) := ⟨by linarith, hcross⟩
    have hsp : s ∈ Set.Ico (0 : ℝ) (τ x) := ⟨hs0, hslt⟩
    have hv := embDistVar_vertical_le T hτ hρpos hρ0 hdiam x hsp hsd
    refine hv.trans ?_
    rw [div_le_div_iff₀ hρpos hρpos]
    have hval1 : |s - (s + δ)| = δ := by
      rw [show s - (s + δ) = -δ by ring, abs_neg, abs_of_nonneg hδ0]
    rw [hval1]
  · -- one seam crossed: route through the seam class `[T x, 0]`
    rw [not_lt] at hcross
    have hTpos : 0 < τ (T x) := lt_of_lt_of_le hρpos (hρ0 (T x))
    have hseam : suspensionMk T hτ (x, s + δ) = suspensionMk T hτ (T x, s + δ - τ x) := by
      have hact : (T x, s + δ - τ x) = suspensionAct T hτ 1 (x, s + δ) := by
        rw [suspensionAct_one, suspensionGen_apply]
      rw [hact, suspensionMk_act]
    rw [hseam]
    have hlt2 : s + δ - τ x < τ (T x) := by
      have : s + δ - τ x < δ := by linarith
      linarith [hδ.le, hρ0 (T x)]
    have hge2 : 0 ≤ s + δ - τ x := by linarith
    have htri := embDistVar_triangle T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s))
      (suspensionMk T hτ (T x, 0)) (suspensionMk T hτ (T x, s + δ - τ x))
    have hseamB := embDistVar_seam_le T hτ hρpos hρ0 hdiam x (s := s) ⟨hs0, hslt⟩
    have hvertB := embDistVar_vertical_le T hτ hρpos hρ0 hdiam (T x)
      (s := (0 : ℝ)) (s' := s + δ - τ x) ⟨le_refl 0, hTpos⟩ ⟨hge2, hlt2⟩
    have hval : |(0 : ℝ) - (s + δ - τ x)| = s + δ - τ x := by
      rw [show (0 : ℝ) - (s + δ - τ x) = -(s + δ - τ x) by ring, abs_neg, abs_of_nonneg hge2]
    rw [hval] at hvertB
    -- combine seam + vertical, then bound by `4 δ / ρmin`
    have hbound : 3 * (1 - s / τ x) + 4 * (s + δ - τ x) / ρmin ≤ 4 * δ / ρmin := by
      have hAeq : 3 * (1 - s / τ x) = 3 * (τ x - s) / τ x := by
        rw [mul_div_assoc, sub_div, div_self (ne_of_gt hxpos)]
      have hA : 3 * (1 - s / τ x) ≤ 3 * (τ x - s) / ρmin := by
        rw [hAeq, div_le_div_iff₀ hxpos hρpos]
        nlinarith [hρ0 x, hρpos, sub_nonneg.mpr hslt.le]
      have hnum : 3 * (τ x - s) + 4 * (s + δ - τ x) ≤ 4 * δ := by nlinarith [hslt]
      calc 3 * (1 - s / τ x) + 4 * (s + δ - τ x) / ρmin
          ≤ 3 * (τ x - s) / ρmin + 4 * (s + δ - τ x) / ρmin := by linarith [hA]
        _ = (3 * (τ x - s) + 4 * (s + δ - τ x)) / ρmin := by rw [← add_div]
        _ ≤ 4 * δ / ρmin := by
            rw [div_le_div_iff₀ hρpos hρpos]; nlinarith [hnum, hρpos]
    calc embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s))
          (suspensionMk T hτ (T x, s + δ - τ x))
        ≤ embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (T x, 0))
          + embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (T x, 0))
            (suspensionMk T hτ (T x, s + δ - τ x)) := htri
      _ ≤ 3 * (1 - s / τ x) + 4 * (s + δ - τ x) / ρmin := add_le_add hseamB hvertB
      _ ≤ 4 * δ / ρmin := hbound

/-- **Flow-Lipschitz estimate.** The suspension flow is `(5 / ρmin)`-Lipschitz in time on each
orbit: `embDistVar (ζ_a q) (ζ_b q) ≤ (5 / ρmin) · |a − b|`. Unit steps use `embDistVar_step_le`;
large steps the global bound `embDistVar_le_five`. -/
theorem embDistVar_flow_le (hdiam : ∀ a b : X, dist a b ≤ 1) (a b : ℝ) (q : SuspensionSpace T hτ) :
    embDistVar T hτ hρpos hρ0 hdiam
        (suspensionFlowMap T hτ a q) (suspensionFlowMap T hτ b q) ≤ 5 * |a - b| / ρmin := by
  -- reduce to a single flow step from a common base class
  have hmono : ∀ c d : ℝ, d ≤ c →
      embDistVar T hτ hρpos hρ0 hdiam
        (suspensionFlowMap T hτ c q) (suspensionFlowMap T hτ d q) ≤ 5 * |c - d| / ρmin := by
    intro c d hdc
    set q' := suspensionFlowMap T hτ d q with hq'
    have hdecomp : suspensionFlowMap T hτ c q = suspensionFlowMap T hτ (c - d) q' := by
      rw [hq', ← Function.comp_apply (f := suspensionFlowMap T hτ (c - d)),
        ← suspensionFlowMap_add, show c - d + d = c from by ring]
    rw [hdecomp]
    have hδ0 : 0 ≤ c - d := by linarith
    have hcd : |c - d| = c - d := abs_of_nonneg hδ0
    rcases lt_or_ge (c - d) ρmin with hsmall | hbig
    · have hstep := embDistVar_step_le T hτ hρpos hρ0 hdiam hδ0 hsmall q'
      rw [embDistVar_comm T hτ hρpos hρ0 hdiam (suspensionFlowMap T hτ (c - d) q') q']
      refine hstep.trans ?_
      rw [hcd, div_le_div_iff₀ hρpos hρpos]; nlinarith [hδ0, hρpos]
    · refine (embDistVar_le_five T hτ hρpos hρ0 hdiam _ _).trans ?_
      rw [le_div_iff₀ hρpos, hcd]; nlinarith [hbig, hρpos]
  rcases le_total b a with hba | hab
  · exact hmono a b hba
  · rw [embDistVar_comm T hτ hρpos hρ0 hdiam, abs_sub_comm]
    exact hmono b a hab

end

end ErgodicTheory
