/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Continuous.SuspensionFlow
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The Bowen–Walters metric on the constant-roof-1 suspension space

This module builds the **Bowen–Walters metric** on the suspension (mapping-torus) space
`SuspensionSpace T hτ` of a base map `T : X ≃ᵐ X` over a metric base `X` under the **constant
roof** `τ ≡ 1`. It is the metric layer of the continuous-flow suspension programme (issue #63,
tier 1) and the substrate on which the flow acts by (essentially) isometries in the time
direction.

## The horizontal length and the route distance

Following Bowen–Walters (1972), Barreira–Radu–Wolf (Dyn. Syst. 19, 2004, §2.1) and
Ledrappier–Lima–Sarig, a *horizontal* segment joins two points `(x, t)` and `(y, t)` at a common
height `t ∈ [0, 1)`, and its length is the **height-interpolated** value

`hlen t x y = (1 − t) · d(x, y) + t · d(T x, T y)`

so that `hlen 0 = d(x, y)` and `hlen 1 = d(T x, T y)` — matching the seam gluing
`(x, 1) ∼ (T x, 0)`. A *vertical* segment moves along the flow at unit speed. The Bowen–Walters
distance is the infimum of the total length over all concatenations ("chains") of horizontal and
vertical segments.

Because the roof is constant `1` and `diam X ≤ 1`, that chain infimum, evaluated on the canonical
fundamental-domain representatives `(x, s), (y, u)` with `s, u ∈ [0, 1)`, is bi-Lipschitz to the
minimum of **five** explicit routes:

* **direct** (no seam crossed): `|s − u| + min (hlen s x y) (hlen u x y)`;
* **low** (both flow down to the floor, jump at height `0`): `s + u + d(x, y)`;
* **high** (both flow up to the seam, jump at height `1`): `(1 − s) + (1 − u) + d(T x, T y)`;
* **up-wrap** (`p` flows up through the top seam, `q` flows down to the floor):
  `(1 − s) + u + d(T x, y)`;
* **down-wrap** (mirror): `s + (1 − u) + d(x, T y)`.

The `low` and `high` routes are essential: a naive minimum of only the direct and two wrap routes is
**provably not** a metric (it fails the triangle inequality when `T` strongly contracts a pair,
because the cheap path climbs both fibres to the seam and traverses at cost `d(T x, T y)` without
crossing it). We take the five-route minimum as the *route distance* `routeDist`, and define
`suspensionDist` by applying `routeDist` to the canonical representatives obtained from
`ErgodicTheory.suspensionUnitFwd`.

## The genuine metric: an explicit Kuratowski-type embedding

The route gauge `suspensionDist` is *provably not* a metric — it fails the triangle inequality (the
`low`/`high` routes are essential, and a documented counterexample shows the finite minimum is only
bi-Lipschitz to, not equal to, the chain-infimum distance). We therefore also build an **honest
metric** `embDist` realising the Bowen–Walters metric class through an explicit embedding, following
Bowen–Walters (1972), Barreira–Saussol (Comm. Math. Phys. 214, 2000) and Barreira–Radu–Wolf
(Dyn. Syst. 19, 2004, §2.1). Under `diam X ≤ 1` the **Kuratowski embedding** `kur a = dist a (·)`
isometrically embeds `X` into `X →ᵇ ℝ`; two test bundles `muFun (x, s)`, `nuFun (x, s)` interpolate
the Kuratowski images of `x` and `T x` with two *distinct* height weightings, and the circle-height
distance `hgt` measures the vertical `ℝ / ℤ` coordinate. Their sum, evaluated at the canonical
representatives, is `embDist`, which satisfies the genuine triangle inequality (the test parts by
the sup-norm triangle inequality of `X →ᵇ ℝ`, the height part by the `ℝ / ℤ` quotient metric) and
separates points (a `2 × 2` linear solve on the two weightings recovers the base point). `embDist`
is bi-Lipschitz to the route gauge, delivered as elementary comparison lemmas.

## Main definitions

* `ErgodicTheory.hlen`, `routeDirect`, `routeLow`, `routeHigh`, `routeUp`, `routeDown`, `routeDist`:
  the height-interpolated horizontal length, the five routes and their minimum on `X × ℝ`.
* `ErgodicTheory.suspensionRep`: the canonical `[0, 1)`-representative `(X × ℝ)` of a class.
* `ErgodicTheory.suspensionDist`: the route-gauge distance on `SuspensionSpace T hτ`.
* `ErgodicTheory.hgt`: the circle-height (`ℝ / ℤ`) geodesic distance on representatives.
* `ErgodicTheory.kur`, `muFun`, `nuFun`: the Kuratowski embedding and the two test bundles.
* `ErgodicTheory.embDist`: the honest embedding metric on `SuspensionSpace T hτ`.

## Main results

* `suspensionDist_self`, `_comm`, `_nonneg`, `_eq_zero`, `suspensionDist_le_*`,
  `suspensionDist_lt_cases`: the route-gauge reflexivity/symmetry/nonnegativity/separation, route
  bounds and downstream case lemma.
* `hgt_triangle`, `hgt_comm`, `hgt_self`, `hgt_nonneg`: the circle-height distance is a metric.
* `dist_kur`: the Kuratowski map is an isometry; `muFun_seam`, `nuFun_seam`: seam consistency;
  `continuous_kur`, `continuous_muFun`, `continuous_nuFun`.
* `embDist_nonneg`, `embDist_self`, `embDist_comm`, **`embDist_triangle`**, **`embDist_eq_zero`**:
  `embDist` is a genuine metric (triangle + separation, unlike the route gauge).
* `embDist_le_three_hlen`, `embDist_vertical_le`, `embDist_seam_le`: bi-Lipschitz **upper** move
  bounds (composed through `embDist_triangle`); `hgt_le_embDist`, `dist_muFun_le_embDist`,
  `dist_nuFun_le_embDist`, `dist_base_le_embDist`: the **lower** comparison primitives (the last a
  quantitative same-height base-distance bound `dist x y ≤ (16/3)·embDist`).
* the quotient `TopologicalSpace` instance, continuity of the projection, and
  `CompactSpace (SuspensionSpace T hτ)` for a compact base.
* **`embDist_continuous`**: quotient-continuity of `embDist (·) q` — the mapping-torus
  seam-continuity of `(x, s) ↦ embDist [x, s] q` across the integer seams, obtained by descending
  the seam-consistent `muFun`/`nuFun`/`hgt` strip data through the floor/fractional-part
  representative map via a `Continuous.if_le` gluing (needs `T`, `T⁻¹` continuous).
* **`embDist_isOpen_iff`**, **`suspensionMetricSpace`**: the metric topology *is* the quotient
  topology, packaging `embDist` as a Mathlib `MetricSpace` via `MetricSpace.ofDistTopology` with no
  diamond; **`suspensionPolish`**: the space is Polish for a compact base.
* **`embDist_flow_le`**: the flow is `5`-Lipschitz in time on each orbit
  (`embDist (ζ_a q) (ζ_b q) ≤ 5·|a − b|`), via the unit-step bound `embDist_step_le` and the global
  bound `embDist_le_five`.
-/

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace ErgodicTheory

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-! ### The height-interpolated horizontal length -/

/-- The **height-interpolated horizontal length** of the segment joining `(x, r)` and `(y, r)` in
the Bowen–Walters metric: `hlen r x y = (1 − r) · d(x, y) + r · d(T x, T y)`. At height `0` it is
`d(x, y)`, and at height `1` it is `d(T x, T y)`, matching the seam gluing `(x, 1) ∼ (T x, 0)`. -/
def hlen (r : ℝ) (x y : X) : ℝ := (1 - r) * dist x y + r * dist (T x) (T y)

@[simp] theorem hlen_zero (x y : X) : hlen T 0 x y = dist x y := by simp [hlen]

@[simp] theorem hlen_one (x y : X) : hlen T 1 x y = dist (T x) (T y) := by simp [hlen]

/-- The horizontal length is symmetric in its two base points. -/
theorem hlen_comm (r : ℝ) (x y : X) : hlen T r x y = hlen T r y x := by
  simp only [hlen, dist_comm]

@[simp] theorem hlen_self (r : ℝ) (x : X) : hlen T r x x = 0 := by simp [hlen]

/-- The horizontal length is nonnegative on `[0, 1]`. -/
theorem hlen_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x y : X) : 0 ≤ hlen T r x y := by
  have h1 : 0 ≤ (1 - r) * dist x y := mul_nonneg (by linarith) dist_nonneg
  have h2 : 0 ≤ r * dist (T x) (T y) := mul_nonneg hr0 dist_nonneg
  simpa [hlen] using add_nonneg h1 h2

/-- On `[0, 1]` the horizontal length vanishes exactly on the diagonal. -/
theorem hlen_eq_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {x y : X} (h : hlen T r x y = 0) :
    x = y := by
  have h1 : 0 ≤ (1 - r) * dist x y := mul_nonneg (by linarith) dist_nonneg
  have h2 : 0 ≤ r * dist (T x) (T y) := mul_nonneg hr0 dist_nonneg
  have hsum : (1 - r) * dist x y + r * dist (T x) (T y) = 0 := h
  have hle : (1 - r) * dist x y = 0 := by nlinarith
  have hdxy : dist x y = 0 := by
    have hrpos : 0 < 1 - r := by linarith
    have := mul_eq_zero.mp hle
    rcases this with h' | h'
    · exact absurd h' (by positivity)
    · exact h'
  exact (dist_eq_zero).mp hdxy

/-- **Same-height triangle inequality** for the horizontal length: at a fixed height `r ∈ [0, 1]`
the map `hlen r` is a pseudometric on the base, being a nonnegative convex combination of the two
metrics `d` and `d ∘ (T × T)`. -/
theorem hlen_triangle {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x y z : X) :
    hlen T r x z ≤ hlen T r x y + hlen T r y z := by
  have h1 : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  have h2 : dist (T x) (T z) ≤ dist (T x) (T y) + dist (T y) (T z) := dist_triangle _ _ _
  have hr' : (0 : ℝ) ≤ 1 - r := by linarith
  simp only [hlen]
  nlinarith [mul_le_mul_of_nonneg_left h1 hr', mul_le_mul_of_nonneg_left h2 hr0]

/-- **Height-Lipschitz bound.** When the base has diameter `≤ 1`, varying the height changes the
horizontal length by at most the height gap: `|hlen r x y − hlen r' x y| ≤ |r − r'|`. Indeed
`hlen r x y − hlen r' x y = (r − r')·(d(T x, T y) − d(x, y))` and the second factor lies in
`[−1, 1]`. -/
theorem hlen_height_lipschitz (hdiam : ∀ a b : X, dist a b ≤ 1) (r r' : ℝ) (x y : X) :
    |hlen T r x y - hlen T r' x y| ≤ |r - r'| := by
  have hd1 : dist x y ≤ 1 := hdiam x y
  have hd2 : dist (T x) (T y) ≤ 1 := hdiam _ _
  have hn1 : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hn2 : (0 : ℝ) ≤ dist (T x) (T y) := dist_nonneg
  have hkey : hlen T r x y - hlen T r' x y = (r - r') * (dist (T x) (T y) - dist x y) := by
    simp only [hlen]; ring
  rw [hkey, abs_mul]
  have hfac : |dist (T x) (T y) - dist x y| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  calc |r - r'| * |dist (T x) (T y) - dist x y| ≤ |r - r'| * 1 :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
    _ = |r - r'| := mul_one _

/-! ### The five routes and the route distance on `X × ℝ`

A finite minimum of only *three* routes (direct + the two seam-wraps) is **not** a metric: when `T`
strongly contracts a pair it violates the triangle inequality, because the cheapest path may climb
*both* fibres to the seam and traverse there at cost `d(T x, T y)` without crossing it (Barreira–
Radu–Wolf, Dyn. Syst. 19 (2004) §2.1, only claim a bi-Lipschitz equivalence of the finite minimum
to the chain-infimum metric). We therefore include the `low` and `high` routes below. -/

/-- The **direct route** (no seam crossed) between representatives `a = (x, s)` and `b = (y, u)`:
descend/ascend to a common height and jump horizontally, `|s − u| + min (hlen s x y) (hlen u x y)`.
-/
def routeDirect (a b : X × ℝ) : ℝ :=
  |a.2 - b.2| + min (hlen T a.2 a.1 b.1) (hlen T b.2 a.1 b.1)

/-- The **low route**: both points flow down to the floor and jump at height `0`,
`s + u + hlen 0 x y = s + u + d(x, y)`. -/
def routeLow (a b : X × ℝ) : ℝ := a.2 + b.2 + hlen T 0 a.1 b.1

/-- The **high route**: both points flow up to the seam and jump at height `1`,
`(1 − s) + (1 − u) + d(T x, T y)`. This is the route missed by a naive three-route minimum; it is
cheap exactly when `T` contracts the pair. -/
def routeHigh (a b : X × ℝ) : ℝ := (1 - a.2) + (1 - b.2) + dist (T a.1) (T b.1)

/-- The **up-wrap route**: `a` flows up through the top seam (arriving at base `T a.1`, height `0`),
`b` flows down to the floor, then a horizontal jump: `(1 − s) + u + d(T x, y)`. -/
def routeUp (a b : X × ℝ) : ℝ := (1 - a.2) + b.2 + dist (T a.1) b.1

/-- The **down-wrap route** (mirror of `routeUp`): `s + (1 − u) + d(x, T y)`. -/
def routeDown (a b : X × ℝ) : ℝ := a.2 + (1 - b.2) + dist a.1 (T b.1)

/-- The **route distance**: the minimum of the five routes (direct, low, high, up-wrap, down-wrap).
On canonical `[0, 1)`-representatives this is the bi-Lipschitz model of the Bowen–Walters distance.
-/
def routeDist (a b : X × ℝ) : ℝ :=
  min (routeDirect T a b)
    (min (routeLow T a b) (min (routeHigh T a b) (min (routeUp T a b) (routeDown T a b))))

theorem routeDirect_comm (a b : X × ℝ) : routeDirect T a b = routeDirect T b a := by
  simp only [routeDirect, abs_sub_comm a.2 b.2]
  rw [hlen_comm T a.2 a.1 b.1, hlen_comm T b.2 a.1 b.1, min_comm]

theorem routeLow_comm (a b : X × ℝ) : routeLow T a b = routeLow T b a := by
  simp only [routeLow]; rw [hlen_comm T 0 a.1 b.1]; ring

theorem routeHigh_comm (a b : X × ℝ) : routeHigh T a b = routeHigh T b a := by
  simp only [routeHigh, dist_comm]; ring

theorem routeUp_eq_routeDown_swap (a b : X × ℝ) : routeUp T a b = routeDown T b a := by
  simp only [routeUp, routeDown, dist_comm]; ring

theorem routeDown_eq_routeUp_swap (a b : X × ℝ) : routeDown T a b = routeUp T b a := by
  rw [routeUp_eq_routeDown_swap]

theorem routeDist_le_routeDirect' (a b : X × ℝ) : routeDist T a b ≤ routeDirect T a b :=
  min_le_left _ _

theorem routeDist_le_routeLow' (a b : X × ℝ) : routeDist T a b ≤ routeLow T a b :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem routeDist_le_routeHigh' (a b : X × ℝ) : routeDist T a b ≤ routeHigh T a b :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem routeDist_le_routeUp' (a b : X × ℝ) : routeDist T a b ≤ routeUp T a b :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))

theorem routeDist_le_routeDown' (a b : X × ℝ) : routeDist T a b ≤ routeDown T a b :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

theorem routeDist_le_swap (a b : X × ℝ) : routeDist T a b ≤ routeDist T b a := by
  refine le_min ?_ (le_min ?_ (le_min ?_ (le_min ?_ ?_)))
  · exact (routeDist_le_routeDirect' T a b).trans_eq (routeDirect_comm T a b)
  · exact (routeDist_le_routeLow' T a b).trans_eq (routeLow_comm T a b)
  · exact (routeDist_le_routeHigh' T a b).trans_eq (routeHigh_comm T a b)
  · exact (routeDist_le_routeDown' T a b).trans_eq (routeDown_eq_routeUp_swap T a b)
  · exact (routeDist_le_routeUp' T a b).trans_eq (routeUp_eq_routeDown_swap T a b)

/-- The route distance is symmetric. -/
theorem routeDist_comm (a b : X × ℝ) : routeDist T a b = routeDist T b a :=
  le_antisymm (routeDist_le_swap T a b) (routeDist_le_swap T b a)

/-- The direct route is nonnegative when the heights lie in `[0, 1]`. -/
theorem routeDirect_nonneg {a b : X × ℝ} (ha0 : 0 ≤ a.2) (ha1 : a.2 ≤ 1)
    (hb0 : 0 ≤ b.2) (hb1 : b.2 ≤ 1) : 0 ≤ routeDirect T a b := by
  have h1 : 0 ≤ hlen T a.2 a.1 b.1 := hlen_nonneg T ha0 ha1 _ _
  have h2 : 0 ≤ hlen T b.2 a.1 b.1 := hlen_nonneg T hb0 hb1 _ _
  have : 0 ≤ min (hlen T a.2 a.1 b.1) (hlen T b.2 a.1 b.1) := le_min h1 h2
  have habs : 0 ≤ |a.2 - b.2| := abs_nonneg _
  simpa [routeDirect] using add_nonneg habs this

theorem routeLow_nonneg {a b : X × ℝ} (ha0 : 0 ≤ a.2) (hb0 : 0 ≤ b.2) :
    0 ≤ routeLow T a b := by
  have : 0 ≤ hlen T 0 a.1 b.1 := hlen_nonneg T le_rfl zero_le_one _ _
  simp only [routeLow]; linarith

theorem routeHigh_nonneg {a b : X × ℝ} (ha1 : a.2 ≤ 1) (hb1 : b.2 ≤ 1) :
    0 ≤ routeHigh T a b := by
  have : 0 ≤ dist (T a.1) (T b.1) := dist_nonneg
  simp only [routeHigh]; linarith

theorem routeHigh_pos {a b : X × ℝ} (ha1 : a.2 < 1) (hb1 : b.2 ≤ 1) : 0 < routeHigh T a b := by
  have : 0 ≤ dist (T a.1) (T b.1) := dist_nonneg
  simp only [routeHigh]; linarith

theorem routeUp_pos {a b : X × ℝ} (ha1 : a.2 < 1) (hb0 : 0 ≤ b.2) : 0 < routeUp T a b := by
  have : 0 ≤ dist (T a.1) b.1 := dist_nonneg
  simp only [routeUp]; linarith

theorem routeDown_pos {a b : X × ℝ} (hb1 : b.2 < 1) (ha0 : 0 ≤ a.2) : 0 < routeDown T a b := by
  have : 0 ≤ dist a.1 (T b.1) := dist_nonneg
  simp only [routeDown]; linarith

theorem routeUp_nonneg {a b : X × ℝ} (ha1 : a.2 ≤ 1) (hb0 : 0 ≤ b.2) :
    0 ≤ routeUp T a b := by
  have : 0 ≤ dist (T a.1) b.1 := dist_nonneg
  simp only [routeUp]; linarith

theorem routeDown_nonneg {a b : X × ℝ} (hb1 : b.2 ≤ 1) (ha0 : 0 ≤ a.2) :
    0 ≤ routeDown T a b := by
  have : 0 ≤ dist a.1 (T b.1) := dist_nonneg
  simp only [routeDown]; linarith

/-- The route distance is nonnegative when the heights lie in `[0, 1]`. -/
theorem routeDist_nonneg {a b : X × ℝ} (ha0 : 0 ≤ a.2) (ha1 : a.2 ≤ 1)
    (hb0 : 0 ≤ b.2) (hb1 : b.2 ≤ 1) : 0 ≤ routeDist T a b :=
  le_min (routeDirect_nonneg T ha0 ha1 hb0 hb1)
    (le_min (routeLow_nonneg T ha0 hb0)
      (le_min (routeHigh_nonneg T ha1 hb1)
        (le_min (routeUp_nonneg T ha1 hb0) (routeDown_nonneg T hb1 ha0))))

/-! ### The canonical representative and the Bowen–Walters distance -/

variable (hτ1 : τ = fun _ => (1 : ℝ))

/-- The **canonical fundamental-domain representative** of a class `p`, a point `(x, s) ∈ X × ℝ`
with height `s ∈ [0, 1)`, extracted from `ErgodicTheory.suspensionUnitFwd`. -/
def suspensionRep (p : SuspensionSpace T hτ) : X × ℝ :=
  ((suspensionUnitFwd T hτ hτ1 p).1, ((suspensionUnitFwd T hτ hτ1 p).2 : ℝ))

/-- The height of a canonical representative lies in `[0, 1)`. -/
theorem suspensionRep_mem_Ico (p : SuspensionSpace T hτ) :
    (suspensionRep T hτ hτ1 p).2 ∈ Set.Ico (0 : ℝ) 1 :=
  (suspensionUnitFwd T hτ hτ1 p).2.2

theorem suspensionRep_nonneg (p : SuspensionSpace T hτ) : 0 ≤ (suspensionRep T hτ hτ1 p).2 :=
  (suspensionRep_mem_Ico T hτ hτ1 p).1

theorem suspensionRep_lt_one (p : SuspensionSpace T hτ) : (suspensionRep T hτ hτ1 p).2 < 1 :=
  (suspensionRep_mem_Ico T hτ hτ1 p).2

/-- Two classes with equal canonical representatives are equal (the representative map is
injective, being a section of the fundamental-domain bijection). -/
theorem suspensionRep_injective {p q : SuspensionSpace T hτ}
    (h : suspensionRep T hτ hτ1 p = suspensionRep T hτ hτ1 q) : p = q := by
  have hfwd : suspensionUnitFwd T hτ hτ1 p = suspensionUnitFwd T hτ hτ1 q := by
    have h' : ((suspensionUnitFwd T hτ hτ1 p).1, ((suspensionUnitFwd T hτ hτ1 p).2 : ℝ))
        = ((suspensionUnitFwd T hτ hτ1 q).1, ((suspensionUnitFwd T hτ hτ1 q).2 : ℝ)) := h
    have h1 := congrArg Prod.fst h'
    have h2 := congrArg Prod.snd h'
    exact Prod.ext h1 (Subtype.ext h2)
  calc p = suspensionUnitInv T hτ (suspensionUnitFwd T hτ hτ1 p) :=
          (suspensionUnitInv_fwd T hτ hτ1 p).symm
    _ = suspensionUnitInv T hτ (suspensionUnitFwd T hτ hτ1 q) := by rw [hfwd]
    _ = q := suspensionUnitInv_fwd T hτ hτ1 q

/-- The **Bowen–Walters distance** on the constant-roof suspension space: the route distance
between the canonical fundamental-domain representatives of the two classes. -/
def suspensionDist (p q : SuspensionSpace T hτ) : ℝ :=
  routeDist T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q)

/-- The distance is nonnegative. -/
theorem suspensionDist_nonneg (p q : SuspensionSpace T hτ) : 0 ≤ suspensionDist T hτ hτ1 p q :=
  routeDist_nonneg T (suspensionRep_nonneg T hτ hτ1 p) (suspensionRep_lt_one T hτ hτ1 p).le
    (suspensionRep_nonneg T hτ hτ1 q) (suspensionRep_lt_one T hτ hτ1 q).le

/-- The distance to self is zero. -/
theorem suspensionDist_self (p : SuspensionSpace T hτ) : suspensionDist T hτ hτ1 p p = 0 := by
  have hdir : routeDirect T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 p) = 0 := by
    simp [routeDirect]
  have hle : suspensionDist T hτ hτ1 p p ≤ 0 := by
    refine (min_le_left _ _).trans ?_
    exact hdir.le
  exact le_antisymm hle (suspensionDist_nonneg T hτ hτ1 p p)

/-- The distance is symmetric. -/
theorem suspensionDist_comm (p q : SuspensionSpace T hτ) :
    suspensionDist T hτ hτ1 p q = suspensionDist T hτ hτ1 q p :=
  routeDist_comm T _ _

/-! ### Separation -/

/-- **Separation.** The Bowen–Walters distance vanishes only on the diagonal: the high-, up- and
down-routes are strictly positive (heights are `< 1`), so a zero distance forces either the direct
route or the low route to zero. In the first case heights coincide and the bases agree
(`hlen_eq_zero`); in the second `s = u = 0` and `d(x, y) = 0`. Either way the representatives — and
hence the classes — coincide. -/
theorem suspensionDist_eq_zero {p q : SuspensionSpace T hτ}
    (h : suspensionDist T hτ hτ1 p q = 0) : p = q := by
  set a := suspensionRep T hτ hτ1 p with ha
  set b := suspensionRep T hτ hτ1 q with hb
  have ha0 : 0 ≤ a.2 := suspensionRep_nonneg T hτ hτ1 p
  have ha1 : a.2 < 1 := suspensionRep_lt_one T hτ hτ1 p
  have hb0 : 0 ≤ b.2 := suspensionRep_nonneg T hτ hτ1 q
  have hb1 : b.2 < 1 := suspensionRep_lt_one T hτ hτ1 q
  have hhi : 0 < routeHigh T a b := routeHigh_pos T ha1 hb1.le
  have hup : 0 < routeUp T a b := routeUp_pos T ha1 hb0
  have hdown : 0 < routeDown T a b := routeDown_pos T hb1 ha0
  have hdirnn : 0 ≤ routeDirect T a b := routeDirect_nonneg T ha0 ha1.le hb0 hb1.le
  have hlownn : 0 ≤ routeLow T a b := routeLow_nonneg T ha0 hb0
  have hzero : routeDist T a b = 0 := h
  have hR : 0 < min (routeHigh T a b) (min (routeUp T a b) (routeDown T a b)) :=
    lt_min hhi (lt_min hup hdown)
  -- the last three routes are strictly positive ⇒ direct or low route is zero
  have hcase : routeDirect T a b = 0 ∨ routeLow T a b = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hdc, hlc⟩ := hcon
    have hd' : 0 < routeDirect T a b := lt_of_le_of_ne hdirnn (Ne.symm hdc)
    have hl' : 0 < routeLow T a b := lt_of_le_of_ne hlownn (Ne.symm hlc)
    have hpos : 0 < routeDist T a b := lt_min hd' (lt_min hl' hR)
    linarith [hzero, hpos]
  have hrep : a = b := by
    rcases hcase with hdir0 | hlow0
    · have hmnn : 0 ≤ min (hlen T a.2 a.1 b.1) (hlen T b.2 a.1 b.1) :=
        le_min (hlen_nonneg T ha0 ha1.le _ _) (hlen_nonneg T hb0 hb1.le _ _)
      have habs0 : 0 ≤ |a.2 - b.2| := abs_nonneg _
      have hdirval : |a.2 - b.2| + min (hlen T a.2 a.1 b.1) (hlen T b.2 a.1 b.1) = 0 := hdir0
      have hheight : a.2 = b.2 := by
        have h1 : |a.2 - b.2| = 0 := by linarith
        have := abs_eq_zero.mp h1; linarith
      have hminz : min (hlen T a.2 a.1 b.1) (hlen T b.2 a.1 b.1) = 0 := by linarith
      have hhlen0 : hlen T a.2 a.1 b.1 = 0 := by
        rcases min_eq_iff.mp hminz with ⟨hA, _⟩ | ⟨hB, _⟩
        · exact hA
        · rw [hheight]; exact hB
      have hbase : a.1 = b.1 := hlen_eq_zero T ha0 ha1 hhlen0
      exact Prod.ext hbase hheight
    · have hdxy : 0 ≤ hlen T 0 a.1 b.1 := hlen_nonneg T le_rfl zero_le_one _ _
      have hlowval : a.2 + b.2 + hlen T 0 a.1 b.1 = 0 := hlow0
      have hs0 : a.2 = 0 := by linarith
      have hu0 : b.2 = 0 := by linarith
      have hhlen0 : hlen T 0 a.1 b.1 = 0 := by linarith
      have hbase : a.1 = b.1 := hlen_eq_zero T le_rfl zero_lt_one hhlen0
      exact Prod.ext hbase (by rw [hs0, hu0])
  exact suspensionRep_injective T hτ hτ1 hrep

/-! ### Representative values and route upper bounds -/

/-- The canonical representative of a class `[x, s]` with height `s ∈ [0, 1)` is `(x, s)` itself
(the fundamental domain is `X × [0, 1)` and the floor of `s` is `0`). -/
theorem suspensionRep_mk (x : X) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    suspensionRep T hτ hτ1 (suspensionMk T hτ (x, s)) = (x, s) := by
  have hy : suspensionUnitInv T hτ (x, ⟨s, hs⟩) = suspensionMk T hτ (x, s) := rfl
  have hfi := suspensionUnitFwd_inv T hτ hτ1 (x, ⟨s, hs⟩)
  rw [hy] at hfi
  unfold suspensionRep
  rw [hfi]

/-- A class is the projection of its own canonical representative: `[suspensionRep q] = q`. -/
theorem suspensionMk_suspensionRep (q : SuspensionSpace T hτ) :
    suspensionMk T hτ (suspensionRep T hτ hτ1 q) = q :=
  suspensionUnitInv_fwd T hτ hτ1 q

/-- The distance is bounded by the direct route between the representatives. -/
theorem suspensionDist_le_routeDirect (p q : SuspensionSpace T hτ) :
    suspensionDist T hτ hτ1 p q
      ≤ routeDirect T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) :=
  routeDist_le_routeDirect' T _ _

/-- The distance is bounded by the low route between the representatives. -/
theorem suspensionDist_le_routeLow (p q : SuspensionSpace T hτ) :
    suspensionDist T hτ hτ1 p q
      ≤ routeLow T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) :=
  routeDist_le_routeLow' T _ _

/-- The distance is bounded by the high route between the representatives. -/
theorem suspensionDist_le_routeHigh (p q : SuspensionSpace T hτ) :
    suspensionDist T hτ hτ1 p q
      ≤ routeHigh T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) :=
  routeDist_le_routeHigh' T _ _

/-- The distance is bounded by the up-wrap route between the representatives. -/
theorem suspensionDist_le_routeUp (p q : SuspensionSpace T hτ) :
    suspensionDist T hτ hτ1 p q
      ≤ routeUp T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) :=
  routeDist_le_routeUp' T _ _

/-- The distance is bounded by the down-wrap route between the representatives. -/
theorem suspensionDist_le_routeDown (p q : SuspensionSpace T hτ) :
    suspensionDist T hτ hτ1 p q
      ≤ routeDown T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) :=
  routeDist_le_routeDown' T _ _

/-- **Horizontal upper bound.** Two points at a common height `s ∈ [0, 1)` are at distance at most
the interpolated horizontal length `hlen s x y`. -/
theorem suspensionDist_le_hlen (x y : X) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    suspensionDist T hτ hτ1 (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, s))
      ≤ hlen T s x y := by
  refine (suspensionDist_le_routeDirect T hτ hτ1 _ _).trans ?_
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 y hs]
  simp only [routeDirect]
  have : min (hlen T s x y) (hlen T s x y) = hlen T s x y := min_self _
  rw [sub_self, abs_zero, this, zero_add]

/-- **Vertical upper bound.** Two points on a common fibre at heights `s, u ∈ [0, 1)` are at
distance at most `|s − u|` (move along the flow). -/
theorem suspensionDist_le_vertical (x : X) {s u : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    suspensionDist T hτ hτ1 (suspensionMk T hτ (x, s)) (suspensionMk T hτ (x, u))
      ≤ |s - u| := by
  refine (suspensionDist_le_routeDirect T hτ hτ1 _ _).trans (le_of_eq ?_)
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 x hu]
  simp only [routeDirect, hlen_self, min_self, add_zero]

/-- **Seam upper bound.** A point `[x, s]` (height `s ∈ [0, 1)`) is within `1 − s` of the seam
image `[T x, 0]` (i.e. `[x, 1]`), via the up-wrap route. -/
theorem suspensionDist_le_seam (x : X) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    suspensionDist T hτ hτ1 (suspensionMk T hτ (x, s))
      (suspensionMk T hτ (T x, 0)) ≤ 1 - s := by
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl 0, one_pos⟩
  refine (suspensionDist_le_routeUp T hτ hτ1 _ _).trans (le_of_eq ?_)
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 (T x) h0]
  simp only [routeUp, dist_self, add_zero]

/-! ### The downstream case lemma -/

/-- **Case lemma (lower bound).** If the Bowen–Walters distance between two classes is `< δ`, then
at least one of the five routes between the canonical representatives is `< δ`. Downstream this
extracts a same-strip / floor / seam / seam-up / seam-down alternative from a small distance. -/
theorem suspensionDist_lt_cases {p q : SuspensionSpace T hτ} {δ : ℝ}
    (h : suspensionDist T hτ hτ1 p q < δ) :
    routeDirect T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) < δ ∨
      routeLow T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) < δ ∨
      routeHigh T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) < δ ∨
      routeUp T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) < δ ∨
      routeDown T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q) < δ := by
  have h' : min (routeDirect T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q))
      (min (routeLow T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q))
        (min (routeHigh T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q))
          (min (routeUp T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q))
            (routeDown T (suspensionRep T hτ hτ1 p) (suspensionRep T hτ hτ1 q))))) < δ := h
  rcases min_lt_iff.mp h' with hd | h1
  · exact Or.inl hd
  rcases min_lt_iff.mp h1 with hl | h2
  · exact Or.inr (Or.inl hl)
  rcases min_lt_iff.mp h2 with hh | h3
  · exact Or.inr (Or.inr (Or.inl hh))
  rcases min_lt_iff.mp h3 with hu | hdn
  · exact Or.inr (Or.inr (Or.inr (Or.inl hu)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hdn)))

/-- From a small direct route, the height gap is small. -/
theorem abs_height_lt_of_routeDirect_lt {a b : X × ℝ} {δ : ℝ}
    (ha0 : 0 ≤ a.2) (ha1 : a.2 ≤ 1) (hb0 : 0 ≤ b.2) (hb1 : b.2 ≤ 1)
    (h : routeDirect T a b < δ) : |a.2 - b.2| < δ := by
  have hmnn : 0 ≤ min (hlen T a.2 a.1 b.1) (hlen T b.2 a.1 b.1) :=
    le_min (hlen_nonneg T ha0 ha1 _ _) (hlen_nonneg T hb0 hb1 _ _)
  simp only [routeDirect] at h
  linarith

/-- From a small direct route, the minimal horizontal length is small. -/
theorem min_hlen_lt_of_routeDirect_lt {a b : X × ℝ} {δ : ℝ}
    (h : routeDirect T a b < δ) :
    min (hlen T a.2 a.1 b.1) (hlen T b.2 a.1 b.1) < δ := by
  have habs : 0 ≤ |a.2 - b.2| := abs_nonneg _
  simp only [routeDirect] at h
  linarith

/-- On the lower half of the fibre, the base distance is controlled by the horizontal length. -/
theorem dist_le_two_mul_hlen_of_height_le_half {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (x y : X) : dist x y ≤ 2 * hlen T r x y := by
  have h2 : 0 ≤ r * dist (T x) (T y) := mul_nonneg hr0 dist_nonneg
  have h1 : (1 / 2 : ℝ) * dist x y ≤ (1 - r) * dist x y :=
    mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  simp only [hlen]
  nlinarith

/-! ### The quotient topology and compactness -/

/-- The canonical **quotient topology** on the suspension space (the coinduced topology from
`X × ℝ` along the projection), mirroring the canonical `MeasurableSpace` instance. -/
instance instTopologicalSpaceSuspensionSpace :
    TopologicalSpace (SuspensionSpace T hτ) := by
  unfold SuspensionSpace
  infer_instance

/-- The quotient projection `suspensionMk` is continuous for the quotient topology. -/
theorem continuous_suspensionMk : Continuous (suspensionMk T hτ) :=
  continuous_quotient_mk'

include hτ1 in
/-- **Compactness.** For a compact base `X`, the constant-roof suspension space is compact: it is
the continuous image of the compact set `X × [0, 1]` under the projection `(x, t) ↦ [x, t]`, which
is surjective because every class has a representative with height in `[0, 1) ⊆ [0, 1]`. -/
theorem compactSpace_suspensionSpace [CompactSpace X] :
    CompactSpace (SuspensionSpace T hτ) := by
  haveI : CompactSpace ↥(Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hcont : Continuous (fun p : X × ↥(Set.Icc (0 : ℝ) 1) =>
      suspensionMk T hτ (p.1, (p.2 : ℝ))) :=
    (continuous_suspensionMk T hτ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hsurj : Function.Surjective (fun p : X × ↥(Set.Icc (0 : ℝ) 1) =>
      suspensionMk T hτ (p.1, (p.2 : ℝ))) := by
    intro z
    refine Quotient.inductionOn z (fun p => ?_)
    obtain ⟨x, s⟩ := p
    refine ⟨(baseIter T hτ ⌊s⌋ x,
      ⟨Int.fract s, ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩⟩), ?_⟩
    change suspensionMk T hτ (baseIter T hτ ⌊s⌋ x, Int.fract s) = suspensionMk T hτ (x, s)
    exact suspensionMk_unitCoord T hτ hτ1 x s
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (SuspensionSpace T hτ))
      = (fun p : X × ↥(Set.Icc (0 : ℝ) 1) => suspensionMk T hτ (p.1, (p.2 : ℝ))) '' Set.univ := by
    rw [Set.image_univ, Set.range_eq_univ.mpr hsurj]
  rw [huniv]
  exact isCompact_univ.image hcont

/-! ### The circle-height distance

The vertical coordinate of the mapping torus lives on the circle `ℝ / ℤ` (the roof is `1`). Its
geodesic distance, expressed on canonical `[0, 1)`-representatives, is `hgt s t = min |s − t|
(1 − |s − t|)`. It is a genuine metric (the quotient metric of `ℝ / ℤ`), whose triangle inequality
we prove by the "nearest lattice point" argument. -/

/-- The **circle-height distance** between two heights, the geodesic distance on `ℝ / ℤ` written on
`[0, 1)`-representatives: `hgt s t = min |s − t| (1 − |s − t|)`. -/
def hgt (s t : ℝ) : ℝ := min |s - t| (1 - |s - t|)

theorem hgt_comm (s t : ℝ) : hgt s t = hgt t s := by
  simp only [hgt, abs_sub_comm s t]

@[simp] theorem hgt_self (s : ℝ) : hgt s s = 0 := by simp [hgt]

/-- The circle-height distance is nonnegative once the height gap is at most `1`. -/
theorem hgt_nonneg {s t : ℝ} (h : |s - t| ≤ 1) : 0 ≤ hgt s t :=
  le_min (abs_nonneg _) (by linarith)

/-- The circle-height distance is bounded by the naive height gap. -/
theorem hgt_le_abs (s t : ℝ) : hgt s t ≤ |s - t| := min_le_left _ _

/-- The circle-height distance is bounded by `1 − |s − t|`. -/
theorem hgt_le_one_sub (s t : ℝ) : hgt s t ≤ 1 - |s - t| := min_le_right _ _

/-- **Nearest-lattice-point bound.** If `|u| ≤ 1` then `min |u| (1 − |u|)` is at most the distance
`|u − N|` from `u` to *any* integer `N`. -/
theorem hgt_le_sub_int {u : ℝ} (N : ℤ) : min |u| (1 - |u|) ≤ |u - N| := by
  rcases eq_or_ne N 0 with hN | hN
  · subst hN
    simp only [Int.cast_zero, sub_zero]
    exact min_le_left _ _
  · have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by
      have : (1 : ℤ) ≤ |N| := by
        rcases lt_or_gt_of_ne hN with h | h
        · rw [abs_of_neg h]; omega
        · rw [abs_of_pos h]; omega
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|N| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(N : ℝ)| := by rw [Int.cast_abs]
    have hge : |(N : ℝ)| - |u| ≤ |u - N| := by
      have := abs_sub_abs_le_abs_sub (N : ℝ) u
      calc |(N : ℝ)| - |u| ≤ |(N : ℝ) - u| := this
        _ = |u - N| := by rw [abs_sub_comm]
    calc min |u| (1 - |u|) ≤ 1 - |u| := min_le_right _ _
      _ ≤ |(N : ℝ)| - |u| := by linarith
      _ ≤ |u - N| := hge

/-- Each circle-height distance is realised as the distance from the height gap to a specific
integer: `hgt s t = |(s − t) − k|` for some `k ∈ {−1, 0, 1}`. -/
theorem exists_int_hgt {s t : ℝ} (h : |s - t| ≤ 1) : ∃ k : ℤ, hgt s t = |(s - t) - (k : ℝ)| := by
  rcases min_cases |s - t| (1 - |s - t|) with ⟨he, _⟩ | ⟨he, _⟩
  · exact ⟨0, by rw [hgt, he]; simp⟩
  · rcases le_total 0 (s - t) with hpos | hneg
    · refine ⟨1, ?_⟩
      rw [hgt, he, abs_of_nonneg hpos]
      rw [show ((1 : ℤ) : ℝ) = 1 by norm_num,
        abs_of_nonpos (by linarith [le_abs_self (s - t), h])]; ring
    · refine ⟨-1, ?_⟩
      rw [hgt, he, abs_of_nonpos hneg]
      rw [show (((-1 : ℤ)) : ℝ) = -1 by norm_num,
        abs_of_nonneg (by linarith [neg_abs_le (s - t), h])]; ring

/-- **Triangle inequality for the circle-height distance** on heights in `[0, 1)`. Writing each
distance as `|gap − k|` for a nearest integer, the ordinary triangle inequality for `|·|` and the
nearest-lattice-point bound close the argument. -/
theorem hgt_triangle {s t r : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ico (0 : ℝ) 1) : hgt s r ≤ hgt s t + hgt t r := by
  have hst : |s - t| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  have htr : |t - r| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [ht.1, hr.2], by linarith [ht.2, hr.1]⟩
  obtain ⟨k, hk⟩ := exists_int_hgt hst
  obtain ⟨m, hm⟩ := exists_int_hgt htr
  rw [hk, hm]
  calc hgt s r ≤ |(s - r) - ((k + m : ℤ) : ℝ)| := hgt_le_sub_int (k + m)
    _ = |((s - t) - (k : ℝ)) + ((t - r) - (m : ℝ))| := by push_cast; ring_nf
    _ ≤ |(s - t) - (k : ℝ)| + |(t - r) - (m : ℝ)| := abs_add_le _ _

/-! ### The Kuratowski test functions

We realise the Bowen–Walters metric class through an explicit **Kuratowski-type embedding**. Under
`diam X ≤ 1` the map `a ↦ dist a (·)` is an isometry of `X` into the bounded continuous functions
`X →ᵇ ℝ`; the two test bundles `muFun`, `nuFun` interpolate the Kuratowski images of `x` and `T x`
with two *distinct* height weightings, so that the pair recovers both base points from a
common-height comparison. Their seam consistency (`muFun_seam`, `nuFun_seam`) is exactly what lets
the metric descend across the gluing `(x, 1) ∼ (T x, 0)`. -/

/-- The **Kuratowski image** `kur a = dist a (·)` of a base point, a bounded continuous function on
`X` (bounded by `diam X ≤ 1`). -/
def kur (hdiam : ∀ a b : X, dist a b ≤ 1) (a : X) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun w => dist a w, continuous_const.dist continuous_id⟩ 1
    (fun w w' => by
      rw [ContinuousMap.coe_mk, Real.dist_eq]
      calc |dist a w - dist a w'| = |dist w a - dist w' a| := by
            rw [dist_comm a w, dist_comm a w']
        _ ≤ dist w w' := abs_dist_sub_le w w' a
        _ ≤ 1 := hdiam w w')

@[simp] theorem kur_apply (hdiam : ∀ a b : X, dist a b ≤ 1) (a w : X) :
    (kur hdiam a) w = dist a w := rfl

/-- The Kuratowski embedding is a genuine **isometry**: `‖kur a − kur b‖ = dist a b`. -/
theorem dist_kur (hdiam : ∀ a b : X, dist a b ≤ 1) (a b : X) :
    dist (kur hdiam a) (kur hdiam b) = dist a b := by
  refine le_antisymm ?_ ?_
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).2 (fun w => ?_)
    rw [kur_apply, kur_apply, Real.dist_eq]
    exact abs_dist_sub_le a b w
  · have h := BoundedContinuousFunction.dist_coe_le_dist (f := kur hdiam a) (g := kur hdiam b) b
    rwa [kur_apply, kur_apply, dist_self, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at h

/-- The Kuratowski embedding is continuous (it is `1`-Lipschitz). -/
theorem continuous_kur (hdiam : ∀ a b : X, dist a b ≤ 1) : Continuous (kur hdiam) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun a b => by
    rw [dist_kur hdiam]; simp)).continuous

/-- The **first test bundle** `muFun (x, s) = (1 − s)·kur x + s·kur (T x)`: the height-`s`
interpolation of the Kuratowski images of the base point and its `T`-image. -/
def muFun (hdiam : ∀ a b : X, dist a b ≤ 1) (a : X × ℝ) : X →ᵇ ℝ :=
  (1 - a.2) • kur hdiam a.1 + a.2 • kur hdiam (T a.1)

/-- The **second test bundle** `nuFun (x, s) = (1 − s)²·kur x + (1 − (1 − s)²)·kur (T x)`, a second,
convex-but-*different* height weighting. Paired with `muFun` it recovers both base points. -/
def nuFun (hdiam : ∀ a b : X, dist a b ≤ 1) (a : X × ℝ) : X →ᵇ ℝ :=
  (1 - a.2) ^ 2 • kur hdiam a.1 + (1 - (1 - a.2) ^ 2) • kur hdiam (T a.1)

/-- **Seam consistency of `muFun`**: `muFun (x, 1) = muFun (T x, 0)`, both equal to `kur (T x)`.
This is the descent condition across the gluing `(x, 1) ∼ (T x, 0)`. -/
theorem muFun_seam (hdiam : ∀ a b : X, dist a b ≤ 1) (x : X) :
    muFun T hdiam (x, 1) = muFun T hdiam (T x, 0) := by
  simp [muFun]

/-- **Seam consistency of `nuFun`**: `nuFun (x, 1) = nuFun (T x, 0)`, both equal to `kur (T x)`. -/
theorem nuFun_seam (hdiam : ∀ a b : X, dist a b ≤ 1) (x : X) :
    nuFun T hdiam (x, 1) = nuFun T hdiam (T x, 0) := by
  simp [nuFun]

/-- The `muFun` bundle is jointly continuous in the base point and the height (needs `T`
continuous). -/
theorem continuous_muFun (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T) :
    Continuous (muFun T hdiam) := by
  refine Continuous.add ?_ ?_
  · exact (continuous_const.sub continuous_snd).smul ((continuous_kur hdiam).comp continuous_fst)
  · exact continuous_snd.smul ((continuous_kur hdiam).comp (hT.comp continuous_fst))

/-- The `nuFun` bundle is jointly continuous in the base point and the height. -/
theorem continuous_nuFun (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T) :
    Continuous (nuFun T hdiam) := by
  refine Continuous.add ?_ ?_
  · exact ((continuous_const.sub continuous_snd).pow 2).smul
      ((continuous_kur hdiam).comp continuous_fst)
  · exact (continuous_const.sub ((continuous_const.sub continuous_snd).pow 2)).smul
      ((continuous_kur hdiam).comp (hT.comp continuous_fst))

/-! ### The embedding metric

Comparing the two test bundles and the circle height at the canonical `[0, 1)`-representatives
yields the **embedding distance** `embDist`. Unlike the route gauge `suspensionDist` it satisfies
the genuine triangle inequality (the `muFun`/`nuFun` parts by the norm triangle inequality of
`X →ᵇ ℝ`, the height part by `hgt_triangle`), and it separates points (a `2 × 2` linear solve on the
two Kuratowski weightings recovers the base point). It is the explicit realization of the
Bowen–Walters metric class. -/

/-- The **embedding distance** on the suspension space: the sum of the sup-norm distances of the two
Kuratowski test bundles and the circle-height distance, evaluated at the canonical representatives.
-/
def embDist (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) : ℝ :=
  dist (muFun T hdiam (suspensionRep T hτ hτ1 p)) (muFun T hdiam (suspensionRep T hτ hτ1 q))
    + dist (nuFun T hdiam (suspensionRep T hτ hτ1 p)) (nuFun T hdiam (suspensionRep T hτ hτ1 q))
    + hgt (suspensionRep T hτ hτ1 p).2 (suspensionRep T hτ hτ1 q).2

/-- The height gap between two canonical representatives has absolute value at most `1`. -/
theorem abs_rep_height_le (p q : SuspensionSpace T hτ) :
    |(suspensionRep T hτ hτ1 p).2 - (suspensionRep T hτ hτ1 q).2| ≤ 1 := by
  have hp0 := suspensionRep_nonneg T hτ hτ1 p
  have hp1 := suspensionRep_lt_one T hτ hτ1 p
  have hq0 := suspensionRep_nonneg T hτ hτ1 q
  have hq1 := suspensionRep_lt_one T hτ hτ1 q
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- The embedding distance is nonnegative. -/
theorem embDist_nonneg (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    0 ≤ embDist T hτ hτ1 hdiam p q := by
  have h := hgt_nonneg (abs_rep_height_le T hτ hτ1 p q)
  have := dist_nonneg (x := muFun T hdiam (suspensionRep T hτ hτ1 p))
    (y := muFun T hdiam (suspensionRep T hτ hτ1 q))
  have := dist_nonneg (x := nuFun T hdiam (suspensionRep T hτ hτ1 p))
    (y := nuFun T hdiam (suspensionRep T hτ hτ1 q))
  unfold embDist; linarith

/-- The embedding distance to self is zero. -/
@[simp] theorem embDist_self (hdiam : ∀ a b : X, dist a b ≤ 1) (p : SuspensionSpace T hτ) :
    embDist T hτ hτ1 hdiam p p = 0 := by
  unfold embDist; simp

/-- The embedding distance is symmetric. -/
theorem embDist_comm (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    embDist T hτ hτ1 hdiam p q = embDist T hτ hτ1 hdiam q p := by
  unfold embDist; rw [dist_comm (muFun T hdiam _), dist_comm (nuFun T hdiam _),
    hgt_comm (suspensionRep T hτ hτ1 p).2]

/-- **Triangle inequality** for the embedding distance. The two Kuratowski parts descend from the
norm triangle inequality of `X →ᵇ ℝ`; the height part from `hgt_triangle`. -/
theorem embDist_triangle (hdiam : ∀ a b : X, dist a b ≤ 1) (p q r : SuspensionSpace T hτ) :
    embDist T hτ hτ1 hdiam p r ≤ embDist T hτ hτ1 hdiam p q + embDist T hτ hτ1 hdiam q r := by
  have hμ := dist_triangle (muFun T hdiam (suspensionRep T hτ hτ1 p))
    (muFun T hdiam (suspensionRep T hτ hτ1 q)) (muFun T hdiam (suspensionRep T hτ hτ1 r))
  have hν := dist_triangle (nuFun T hdiam (suspensionRep T hτ hτ1 p))
    (nuFun T hdiam (suspensionRep T hτ hτ1 q)) (nuFun T hdiam (suspensionRep T hτ hτ1 r))
  have hh := hgt_triangle (suspensionRep_mem_Ico T hτ hτ1 p) (suspensionRep_mem_Ico T hτ hτ1 q)
    (suspensionRep_mem_Ico T hτ hτ1 r)
  unfold embDist; linarith

/-- **Separation.** A zero embedding distance forces the two classes to coincide. From the height
part, the canonical heights agree; from the two Kuratowski parts (with a common height) a linear
elimination of the weightings shows `kur x = kur y`, hence `x = y` by the Kuratowski isometry. -/
theorem embDist_eq_zero (hdiam : ∀ a b : X, dist a b ≤ 1) {p q : SuspensionSpace T hτ}
    (h : embDist T hτ hτ1 hdiam p q = 0) : p = q := by
  set a := suspensionRep T hτ hτ1 p with ha
  set b := suspensionRep T hτ hτ1 q with hb
  have ha0 : 0 ≤ a.2 := suspensionRep_nonneg T hτ hτ1 p
  have ha1 : a.2 < 1 := suspensionRep_lt_one T hτ hτ1 p
  have hb0 : 0 ≤ b.2 := suspensionRep_nonneg T hτ hτ1 q
  have hb1 : b.2 < 1 := suspensionRep_lt_one T hτ hτ1 q
  have habs : |a.2 - b.2| ≤ 1 := abs_rep_height_le T hτ hτ1 p q
  have hμnn : 0 ≤ dist (muFun T hdiam a) (muFun T hdiam b) := dist_nonneg
  have hνnn : 0 ≤ dist (nuFun T hdiam a) (nuFun T hdiam b) := dist_nonneg
  have hhnn : 0 ≤ hgt a.2 b.2 := hgt_nonneg habs
  have hsum : dist (muFun T hdiam a) (muFun T hdiam b)
      + dist (nuFun T hdiam a) (nuFun T hdiam b) + hgt a.2 b.2 = 0 := h
  have hμ0 : dist (muFun T hdiam a) (muFun T hdiam b) = 0 := by linarith
  have hν0 : dist (nuFun T hdiam a) (nuFun T hdiam b) = 0 := by linarith
  have hh0 : hgt a.2 b.2 = 0 := by linarith
  -- heights agree
  have hheq : a.2 = b.2 := by
    have hpos : (0 : ℝ) < 1 - |a.2 - b.2| := by
      have : |a.2 - b.2| < 1 := by rw [abs_lt]; constructor <;> linarith
      linarith
    rw [hgt] at hh0
    have habs0 : |a.2 - b.2| = 0 := by
      rcases min_eq_iff.mp hh0 with ⟨e, _⟩ | ⟨e, _⟩
      · exact e
      · linarith
    have := abs_eq_zero.mp habs0; linarith
  -- Kuratowski equalities at the common height
  have hmu' : muFun T hdiam a = muFun T hdiam b := dist_eq_zero.mp hμ0
  have hnu' : nuFun T hdiam a = nuFun T hdiam b := dist_eq_zero.mp hν0
  simp only [muFun, nuFun] at hmu' hnu'
  rw [← hheq] at hmu' hnu'
  set s := a.2 with hs
  set x := a.1 with hx
  set y := b.1 with hy
  -- recover the base equality kur x = kur y
  have hbase : kur hdiam x = kur hdiam y := by
    rcases eq_or_lt_of_le ha0 with hs0 | hspos
    · -- s = 0
      rw [← hs0] at hmu'
      simpa using hmu'
    · -- 0 < s < 1
      have hspos' : (0 : ℝ) < s := hspos
      have hs1 : s < 1 := ha1
      have expand : ((1 - s) * s) • kur hdiam x
          = (1 - (1 - s) ^ 2) • ((1 - s) • kur hdiam x + s • kur hdiam (T x))
            - s • ((1 - s) ^ 2 • kur hdiam x + (1 - (1 - s) ^ 2) • kur hdiam (T x)) := by
        module
      have expand2 : ((1 - s) * s) • kur hdiam y
          = (1 - (1 - s) ^ 2) • ((1 - s) • kur hdiam y + s • kur hdiam (T y))
            - s • ((1 - s) ^ 2 • kur hdiam y + (1 - (1 - s) ^ 2) • kur hdiam (T y)) := by
        module
      have key : ((1 - s) * s) • kur hdiam x = ((1 - s) * s) • kur hdiam y := by
        rw [expand, expand2, hmu', hnu']
      have key0 : ((1 - s) * s) • (kur hdiam x - kur hdiam y) = 0 := by
        rw [smul_sub, key, sub_self]
      have hcne : (1 - s) * s ≠ 0 := ne_of_gt (mul_pos (by linarith) hspos')
      rcases smul_eq_zero.mp key0 with hc | hxy
      · exact absurd hc hcne
      · exact sub_eq_zero.mp hxy
  have hxy : x = y := by
    have := (dist_kur hdiam x y).symm
    rw [hbase, dist_self] at this
    exact dist_eq_zero.mp this
  have hrep : a = b := Prod.ext hxy hheq
  apply suspensionRep_injective T hτ hτ1
  rw [← ha, ← hb]; exact hrep

/-! ### Bi-Lipschitz comparison with the route gauge

The embedding metric is bi-Lipschitz to the route gauge `suspensionDist`. We record the two
directions as elementary "move" bounds, the shape consumed downstream (Bowen–Walters
`α`-Hölder gluing): upper bounds `embDist ≤ C · (elementary route cost)` for the horizontal,
vertical and seam moves (composed through `embDist_triangle`), and the lower-bound primitives
extracting the height gap and the two Kuratowski parts from a small embedding distance. -/

/-- The Kuratowski difference has sup-norm exactly the base distance. -/
theorem norm_kur_sub (hdiam : ∀ a b : X, dist a b ≤ 1) (x y : X) :
    ‖kur hdiam x - kur hdiam y‖ = dist x y := by
  rw [← dist_eq_norm, dist_kur]

/-- **Same-base vertical bound for `muFun`.** The `muFun` Kuratowski bundle over a fixed base point
moves by at most the height gap: `dist (muFun (x, s)) (muFun (x, t)) ≤ |s − t|`. Roof independent
(point-level, not class-level); reused at raw heights (constant roof) and normalized heights
(variable roof). -/
theorem dist_muFun_sameBase_le (hdiam : ∀ a b : X, dist a b ≤ 1) (x : X) (s t : ℝ) :
    dist (muFun T hdiam (x, s)) (muFun T hdiam (x, t)) ≤ |s - t| := by
  have hsub : muFun T hdiam (x, s) - muFun T hdiam (x, t)
      = (s - t) • (kur hdiam (T x) - kur hdiam x) := by simp only [muFun]; module
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub]
  calc |s - t| * dist (T x) x ≤ |s - t| * 1 :=
        mul_le_mul_of_nonneg_left (hdiam _ _) (abs_nonneg _)
    _ = |s - t| := mul_one _

/-- **Same-base vertical bound for `nuFun`** (at heights in `[0, 1]`):
`dist (nuFun (x, s)) (nuFun (x, t)) ≤ 2 · |s − t|`. Roof independent; reused at raw and normalized
heights. -/
theorem dist_nuFun_sameBase_le (hdiam : ∀ a b : X, dist a b ≤ 1) (x : X) {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist (nuFun T hdiam (x, s)) (nuFun T hdiam (x, t)) ≤ 2 * |s - t| := by
  have hsub : nuFun T hdiam (x, s) - nuFun T hdiam (x, t)
      = ((1 - s) ^ 2 - (1 - t) ^ 2) • (kur hdiam x - kur hdiam (T x)) := by
    simp only [nuFun]; module
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub]
  have hfac : |(1 - s) ^ 2 - (1 - t) ^ 2| ≤ 2 * |s - t| := by
    have hid : (1 - s) ^ 2 - (1 - t) ^ 2 = (t - s) * (2 - s - t) := by ring
    rw [hid, abs_mul, abs_sub_comm t s]
    have h2 : |2 - s - t| ≤ 2 := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
    calc |s - t| * |2 - s - t| ≤ |s - t| * 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = 2 * |s - t| := by ring
  calc |(1 - s) ^ 2 - (1 - t) ^ 2| * dist x (T x) ≤ 2 * |s - t| * 1 :=
        mul_le_mul hfac (hdiam _ _) dist_nonneg (by positivity)
    _ = 2 * |s - t| := by ring

/-- **Horizontal move bound.** The `muFun` part of the embedding distance at a common height is at
most the interpolated horizontal length `hlen s x y`. -/
theorem dist_muFun_le_hlen (hdiam : ∀ a b : X, dist a b ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x y : X) : dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s)) ≤ hlen T s x y := by
  have hsub : muFun T hdiam (x, s) - muFun T hdiam (y, s)
      = (1 - s) • (kur hdiam x - kur hdiam y) + s • (kur hdiam (T x) - kur hdiam (T y)) := by
    simp only [muFun]; module
  rw [dist_eq_norm, hsub]
  calc ‖(1 - s) • (kur hdiam x - kur hdiam y) + s • (kur hdiam (T x) - kur hdiam (T y))‖
      ≤ ‖(1 - s) • (kur hdiam x - kur hdiam y)‖ + ‖s • (kur hdiam (T x) - kur hdiam (T y))‖ :=
        norm_add_le _ _
    _ = |1 - s| * dist x y + |s| * dist (T x) (T y) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_kur_sub, norm_kur_sub]
    _ = hlen T s x y := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg hs0]; rfl

/-- The `nuFun` part of the embedding distance at a common height, with its explicit weightings. -/
theorem dist_nuFun_le (hdiam : ∀ a b : X, dist a b ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x y : X) : dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s))
      ≤ (1 - s) ^ 2 * dist x y + (1 - (1 - s) ^ 2) * dist (T x) (T y) := by
  have hsub : nuFun T hdiam (x, s) - nuFun T hdiam (y, s)
      = (1 - s) ^ 2 • (kur hdiam x - kur hdiam y)
        + (1 - (1 - s) ^ 2) • (kur hdiam (T x) - kur hdiam (T y)) := by
    simp only [nuFun]; module
  have hc1 : (0 : ℝ) ≤ (1 - s) ^ 2 := sq_nonneg _
  have hc2 : (0 : ℝ) ≤ 1 - (1 - s) ^ 2 := by nlinarith
  rw [dist_eq_norm, hsub]
  calc ‖(1 - s) ^ 2 • (kur hdiam x - kur hdiam y)
        + (1 - (1 - s) ^ 2) • (kur hdiam (T x) - kur hdiam (T y))‖
      ≤ ‖(1 - s) ^ 2 • (kur hdiam x - kur hdiam y)‖
        + ‖(1 - (1 - s) ^ 2) • (kur hdiam (T x) - kur hdiam (T y))‖ := norm_add_le _ _
    _ = |(1 - s) ^ 2| * dist x y + |1 - (1 - s) ^ 2| * dist (T x) (T y) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_kur_sub, norm_kur_sub]
    _ = (1 - s) ^ 2 * dist x y + (1 - (1 - s) ^ 2) * dist (T x) (T y) := by
        rw [abs_of_nonneg hc1, abs_of_nonneg hc2]

/-- **Horizontal upper bound** for the embedding distance: two classes at a common height `s` are
at embedding distance at most `3 · hlen s x y`. -/
theorem embDist_le_three_hlen (hdiam : ∀ a b : X, dist a b ≤ 1) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (x y : X) :
    embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, s))
      ≤ 3 * hlen T s x y := by
  unfold embDist
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 y hs]
  have hmu := dist_muFun_le_hlen T hdiam hs.1 hs.2.le x y
  have hnu := dist_nuFun_le T hdiam hs.1 hs.2.le x y
  have hdxy : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hdT : (0 : ℝ) ≤ dist (T x) (T y) := dist_nonneg
  have hnu2 : (1 - s) ^ 2 * dist x y + (1 - (1 - s) ^ 2) * dist (T x) (T y)
      ≤ 2 * hlen T s x y := by
    simp only [hlen]
    have e1 : (1 - s) ^ 2 * dist x y ≤ (1 - s) * dist x y := by
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - s by linarith [hs.2.le]) hs.1) hdxy]
    have e2 : (1 - (1 - s) ^ 2) * dist (T x) (T y) ≤ 2 * (s * dist (T x) (T y)) := by
      nlinarith [mul_nonneg (sq_nonneg s) hdT]
    have e3 : (0 : ℝ) ≤ (1 - s) * dist x y := mul_nonneg (by linarith [hs.2.le]) hdxy
    linarith
  have hz : hgt (x, s).2 (y, s).2 = 0 := hgt_self s
  linarith

/-- **Vertical upper bound** for the embedding distance: two classes on a common fibre at heights
`s, u` are at embedding distance at most `4 · |s − u|`. -/
theorem embDist_vertical_le (hdiam : ∀ a b : X, dist a b ≤ 1) {s u : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hu : u ∈ Set.Ico (0 : ℝ) 1) (x : X) :
    embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (x, u))
      ≤ 4 * |s - u| := by
  unfold embDist
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 x hu]
  have hmu : dist (muFun T hdiam (x, s)) (muFun T hdiam (x, u)) ≤ |s - u| := by
    have hsub : muFun T hdiam (x, s) - muFun T hdiam (x, u)
        = (s - u) • (kur hdiam (T x) - kur hdiam x) := by simp only [muFun]; module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub]
    calc |s - u| * dist (T x) x ≤ |s - u| * 1 :=
          mul_le_mul_of_nonneg_left (hdiam _ _) (abs_nonneg _)
      _ = |s - u| := mul_one _
  have hnu : dist (nuFun T hdiam (x, s)) (nuFun T hdiam (x, u)) ≤ 2 * |s - u| := by
    have hsub : nuFun T hdiam (x, s) - nuFun T hdiam (x, u)
        = ((1 - s) ^ 2 - (1 - u) ^ 2) • (kur hdiam x - kur hdiam (T x)) := by
      simp only [nuFun]; module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub]
    have hfac : |(1 - s) ^ 2 - (1 - u) ^ 2| ≤ 2 * |s - u| := by
      have hid : (1 - s) ^ 2 - (1 - u) ^ 2 = (u - s) * (2 - s - u) := by ring
      rw [hid, abs_mul, abs_sub_comm u s]
      have h2 : |2 - s - u| ≤ 2 := by
        rw [abs_le]; exact ⟨by linarith [hs.2.le, hu.2.le], by linarith [hs.1, hu.1]⟩
      calc |s - u| * |2 - s - u| ≤ |s - u| * 2 :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = 2 * |s - u| := by ring
    calc |(1 - s) ^ 2 - (1 - u) ^ 2| * dist x (T x) ≤ 2 * |s - u| * 1 :=
          mul_le_mul hfac (hdiam _ _) dist_nonneg (by positivity)
      _ = 2 * |s - u| := by ring
  have hh : hgt (x, s).2 (x, u).2 ≤ |s - u| := hgt_le_abs _ _
  linarith

/-- **Seam upper bound** for the embedding distance: a class `[x, s]` is within `3 · (1 − s)` of the
seam image `[T x, 0]`. -/
theorem embDist_seam_le (hdiam : ∀ a b : X, dist a b ≤ 1) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (x : X) :
    embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (T x, 0))
      ≤ 3 * (1 - s) := by
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl 0, one_pos⟩
  unfold embDist
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 (T x) h0]
  have hmu : dist (muFun T hdiam (x, s)) (muFun T hdiam (T x, 0)) ≤ 1 - s := by
    have hsub : muFun T hdiam (x, s) - muFun T hdiam (T x, 0)
        = (1 - s) • (kur hdiam x - kur hdiam (T x)) := by simp only [muFun]; module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub,
      abs_of_nonneg (by linarith [hs.2.le])]
    calc (1 - s) * dist x (T x) ≤ (1 - s) * 1 :=
          mul_le_mul_of_nonneg_left (hdiam _ _) (by linarith [hs.2.le])
      _ = 1 - s := mul_one _
  have hnu : dist (nuFun T hdiam (x, s)) (nuFun T hdiam (T x, 0)) ≤ 1 - s := by
    have hsub : nuFun T hdiam (x, s) - nuFun T hdiam (T x, 0)
        = (1 - s) ^ 2 • (kur hdiam x - kur hdiam (T x)) := by simp only [nuFun]; module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, norm_kur_sub, abs_of_nonneg (sq_nonneg _)]
    have hsq : (1 - s) ^ 2 ≤ 1 - s := by nlinarith [hs.1, hs.2.le]
    calc (1 - s) ^ 2 * dist x (T x) ≤ (1 - s) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hdiam _ _) (sq_nonneg _)
      _ = (1 - s) ^ 2 := mul_one _
      _ ≤ 1 - s := hsq
  have hh : hgt (x, s).2 (T x, 0).2 ≤ 1 - s := by
    change hgt s 0 ≤ 1 - s
    calc hgt s 0 ≤ 1 - |s - 0| := hgt_le_one_sub _ _
      _ = 1 - s := by rw [sub_zero, abs_of_nonneg hs.1]
  linarith

/-- **Quantitative separation / lower comparison at a common height.** For a mid-range height
`s ∈ [1/4, 3/4]` the base distance is controlled by the embedding distance: `dist x y ≤
(16/3) · embDist [x,s] [y,s]`. The `2 × 2` elimination of the two Kuratowski weightings recovers
`((1 − s)·s)·(kur x − kur y)` from the two test parts, with `(1 − s)·s ≥ 3/16`. -/
theorem dist_base_le_embDist (hdiam : ∀ a b : X, dist a b ≤ 1) {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)) (x y : X) :
    dist x y ≤ (16 / 3) *
      embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, s)) := by
  have hs01 : s ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hs0 : (0 : ℝ) ≤ s := by linarith [hs.1]
  have hs1 : s ≤ 1 := by linarith [hs.2]
  set E := embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, s))
    with hEdef
  -- the sum of the two parts is exactly `E` (the height part vanishes)
  have hsum : dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s))
      + dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s)) = E := by
    rw [hEdef]; unfold embDist
    rw [suspensionRep_mk T hτ hτ1 x hs01, suspensionRep_mk T hτ hτ1 y hs01]
    have hz : hgt (x, s).2 (y, s).2 = 0 := hgt_self s
    rw [hz, add_zero]
  -- eliminate the second weighting
  have hkey : ((1 - s) * s) • (kur hdiam x - kur hdiam y)
      = (1 - (1 - s) ^ 2) • (muFun T hdiam (x, s) - muFun T hdiam (y, s))
        - s • (nuFun T hdiam (x, s) - nuFun T hdiam (y, s)) := by
    simp only [muFun, nuFun]; module
  have hc1 : (0 : ℝ) ≤ 1 - (1 - s) ^ 2 := by nlinarith
  have hnorm : ((1 - s) * s) * dist x y
      ≤ (1 - (1 - s) ^ 2) * dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s))
        + s * dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s)) := by
    have hlhs : ((1 - s) * s) * dist x y = ‖((1 - s) * s) • (kur hdiam x - kur hdiam y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, norm_kur_sub,
        abs_of_nonneg (mul_nonneg (by linarith) hs0)]
    rw [hlhs, hkey]
    calc ‖(1 - (1 - s) ^ 2) • (muFun T hdiam (x, s) - muFun T hdiam (y, s))
          - s • (nuFun T hdiam (x, s) - nuFun T hdiam (y, s))‖
        ≤ ‖(1 - (1 - s) ^ 2) • (muFun T hdiam (x, s) - muFun T hdiam (y, s))‖
          + ‖s • (nuFun T hdiam (x, s) - nuFun T hdiam (y, s))‖ := norm_sub_le _ _
      _ = (1 - (1 - s) ^ 2) * dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s))
          + s * dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s)) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc1,
            abs_of_nonneg hs0, ← dist_eq_norm, ← dist_eq_norm]
  -- combine: (1-s)*s ≥ 3/16, and the weighted sum is ≤ E
  have hcoeff : (3 : ℝ) / 16 ≤ (1 - s) * s := by nlinarith [hs.1, hs.2]
  have hdxy : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hμnn : (0 : ℝ) ≤ dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s)) := dist_nonneg
  have hνnn : (0 : ℝ) ≤ dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s)) := dist_nonneg
  -- weighted sum ≤ μpart + νpart = E
  have hwle : (1 - (1 - s) ^ 2) * dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s))
      + s * dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s)) ≤ E := by
    have h1 : (1 - (1 - s) ^ 2) * dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s))
        ≤ dist (muFun T hdiam (x, s)) (muFun T hdiam (y, s)) := by nlinarith
    have h2 : s * dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s))
        ≤ dist (nuFun T hdiam (x, s)) (nuFun T hdiam (y, s)) := by nlinarith
    linarith [hsum]
  have hfin : ((1 - s) * s) * dist x y ≤ E := le_trans hnorm hwle
  have hstep : (3 / 16 : ℝ) * dist x y ≤ E :=
    le_trans (mul_le_mul_of_nonneg_right hcoeff hdxy) hfin
  linarith

/-- **Lower-bound primitive.** The height gap is controlled by the embedding distance. -/
theorem hgt_le_embDist (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    hgt (suspensionRep T hτ hτ1 p).2 (suspensionRep T hτ hτ1 q).2 ≤ embDist T hτ hτ1 hdiam p q := by
  have h1 : (0 : ℝ) ≤ dist (muFun T hdiam (suspensionRep T hτ hτ1 p))
    (muFun T hdiam (suspensionRep T hτ hτ1 q)) := dist_nonneg
  have h2 : (0 : ℝ) ≤ dist (nuFun T hdiam (suspensionRep T hτ hτ1 p))
    (nuFun T hdiam (suspensionRep T hτ hτ1 q)) := dist_nonneg
  unfold embDist; linarith

/-- **Lower-bound primitive.** The `muFun` Kuratowski part is controlled by the embedding
distance. -/
theorem dist_muFun_le_embDist (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    dist (muFun T hdiam (suspensionRep T hτ hτ1 p)) (muFun T hdiam (suspensionRep T hτ hτ1 q))
      ≤ embDist T hτ hτ1 hdiam p q := by
  have h2 : (0 : ℝ) ≤ dist (nuFun T hdiam (suspensionRep T hτ hτ1 p))
    (nuFun T hdiam (suspensionRep T hτ hτ1 q)) := dist_nonneg
  have h3 : (0 : ℝ) ≤ hgt (suspensionRep T hτ hτ1 p).2 (suspensionRep T hτ hτ1 q).2 :=
    hgt_nonneg (abs_rep_height_le T hτ hτ1 p q)
  unfold embDist; linarith

/-- **Lower-bound primitive.** The `nuFun` Kuratowski part is controlled by the embedding
distance. -/
theorem dist_nuFun_le_embDist (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    dist (nuFun T hdiam (suspensionRep T hτ hτ1 p)) (nuFun T hdiam (suspensionRep T hτ hτ1 q))
      ≤ embDist T hτ hτ1 hdiam p q := by
  have h1 : (0 : ℝ) ≤ dist (muFun T hdiam (suspensionRep T hτ hτ1 p))
    (muFun T hdiam (suspensionRep T hτ hτ1 q)) := dist_nonneg
  have h3 : (0 : ℝ) ≤ hgt (suspensionRep T hτ hτ1 p).2 (suspensionRep T hτ hτ1 q).2 :=
    hgt_nonneg (abs_rep_height_le T hτ hτ1 p q)
  unfold embDist; linarith

/-! ### Quotient-continuity of the embedding distance

The one substantial topological ingredient: `embDist (·) q` is continuous for the canonical
quotient topology. The map `suspensionMk` is a topological quotient map, so continuity reduces to
that of the composite `(x, s) ↦ embDist [x, s] q` on `X × ℝ`. On the open strip `s ∈ (n, n+1)` this
composite equals a manifestly continuous "strip formula" built from the raw `muFun`/`nuFun`/`hgt`
data at `(Tⁿ x, s − n)`; the seam consistency `muFun_seam`, `nuFun_seam` and the circle-height
identity `hgt 1 = hgt 0` glue the strips across the integer seams. Concretely, near any point the
composite agrees with a single `Continuous.if_le` gluing of the two adjacent strip formulas. -/

/-- One-step recursion for the integer base iterate: `T^{n+1} x = T (T^n x)`, valid for every
integer `n` (the natural-index case is `baseIter_natCast`; this is the `ℤ`-indexed step). -/
theorem baseIter_add_one (n : ℤ) (x : X) :
    baseIter T hτ (n + 1) x = T (baseIter T hτ n x) := by
  have h : suspensionAct T hτ (n + 1) (x, (0 : ℝ))
      = suspensionGen T hτ (suspensionAct T hτ n (x, (0 : ℝ))) := by
    rw [add_comm, suspensionAct_add, suspensionAct_one]
  simp only [baseIter, h, suspensionGen_apply]

/-- The integer base iterate `x ↦ Tⁿ x` is continuous when both `T` and `T⁻¹` are continuous
(forward iterates use `T`, backward iterates use `T⁻¹`). -/
theorem continuous_baseIter (hT : Continuous ⇑T) (hTs : Continuous ⇑T.symm) (n : ℤ) :
    Continuous (baseIter T hτ n) := by
  induction n using Int.induction_on with
  | zero =>
    have h0 : (baseIter T hτ (0 : ℤ)) = fun x => x := by
      funext x; simp [baseIter, suspensionAct_zero]
    rw [h0]; exact continuous_id
  | succ k ih =>
    have hcont : Continuous (fun x => T (baseIter T hτ (k : ℤ) x)) := hT.comp ih
    exact hcont.congr (fun x => (baseIter_add_one T hτ (k : ℤ) x).symm)
  | pred k ih =>
    have hcont : Continuous (fun x => T.symm (baseIter T hτ (-(k : ℤ)) x)) := hTs.comp ih
    refine hcont.congr (fun x => ?_)
    have h := baseIter_add_one T hτ (-(k : ℤ) - 1) x
    rw [show (-(k : ℤ) - 1 + 1) = -(k : ℤ) by ring] at h
    rw [h, MeasurableEquiv.symm_apply_apply]

/-- The circle-height distance, as a function of its first argument (the height), is continuous. -/
theorem continuous_hgt_left (c : ℝ) : Continuous (fun u : ℝ => hgt u c) := by
  have habs : Continuous (fun u : ℝ => |u - c|) :=
    _root_.continuous_abs.comp (continuous_id.sub continuous_const)
  exact habs.min (continuous_const.sub habs)

/-- The seam identity for the circle-height distance: at heights `c ∈ [0, 1)` the value at height
`1` equals the value at height `0` (the endpoints of the fundamental interval are glued). -/
theorem hgt_one_eq_zero_height {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) : hgt 1 c = hgt 0 c := by
  unfold hgt
  have h1 : |(1 : ℝ) - c| = 1 - c := abs_of_nonneg (by linarith)
  have h0 : |(0 : ℝ) - c| = c := by rw [zero_sub, abs_neg, abs_of_nonneg hc0]
  rw [h1, h0, show (1 : ℝ) - (1 - c) = c by ring]
  exact min_comm _ _

/-- The canonical representative of a class `[x, s]` at *arbitrary* height `s ∈ ℝ` is
`(T^{⌊s⌋} x, {s})` (integer base iterate at the floor, fractional part as the new height). -/
theorem suspensionRep_mk' (x : X) (s : ℝ) :
    suspensionRep T hτ hτ1 (suspensionMk T hτ (x, s))
      = (baseIter T hτ ⌊s⌋ x, Int.fract s) := by
  rw [← suspensionMk_unitCoord T hτ hτ1 x s]
  exact suspensionRep_mk T hτ hτ1 (baseIter T hτ ⌊s⌋ x)
    ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩

/-- **Quotient-continuity of the embedding distance.** For the canonical quotient topology on the
suspension space, `p ↦ embDist p q` is continuous. This is the seam-continuity across the integer
gluings of the mapping torus, and it is the ingredient that identifies the `embDist`-metric topology
with the quotient topology (see `suspensionMetricSpace`). -/
theorem embDist_continuous (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T)
    (hTs : Continuous ⇑T.symm) (q : SuspensionSpace T hτ) :
    Continuous (fun p => embDist T hτ hτ1 hdiam p q) := by
  have hqm : Topology.IsQuotientMap (suspensionMk T hτ) := isQuotientMap_quotient_mk'
  rw [hqm.continuous_iff]
  change Continuous (fun a : X × ℝ => embDist T hτ hτ1 hdiam (suspensionMk T hτ a) q)
  set Mq := muFun T hdiam (suspensionRep T hτ hτ1 q) with hMq
  set Nq := nuFun T hdiam (suspensionRep T hτ hτ1 q) with hNq
  set hq := (suspensionRep T hτ hτ1 q).2 with hhq
  have hq0 : 0 ≤ hq := suspensionRep_nonneg T hτ hτ1 q
  have hq1 : hq < 1 := suspensionRep_lt_one T hτ hτ1 q
  -- continuity of the strip formula at each integer index `m`
  have hcontg : ∀ m : ℤ, Continuous (fun a : X × ℝ =>
      dist (muFun T hdiam (baseIter T hτ m a.1, a.2 - (m : ℝ))) Mq
        + dist (nuFun T hdiam (baseIter T hτ m a.1, a.2 - (m : ℝ))) Nq
        + hgt (a.2 - (m : ℝ)) hq) := by
    intro m
    have hmap : Continuous (fun a : X × ℝ => (baseIter T hτ m a.1, a.2 - (m : ℝ))) :=
      ((continuous_baseIter T hτ hT hTs m).comp continuous_fst).prodMk
        (continuous_snd.sub continuous_const)
    have hmu : Continuous
        (fun a : X × ℝ => dist (muFun T hdiam (baseIter T hτ m a.1, a.2 - (m : ℝ))) Mq) :=
      ((continuous_muFun T hdiam hT).comp hmap).dist continuous_const
    have hnu : Continuous
        (fun a : X × ℝ => dist (nuFun T hdiam (baseIter T hτ m a.1, a.2 - (m : ℝ))) Nq) :=
      ((continuous_nuFun T hdiam hT).comp hmap).dist continuous_const
    have hht : Continuous (fun a : X × ℝ => hgt (a.2 - (m : ℝ)) hq) :=
      (continuous_hgt_left hq).comp (continuous_snd.sub continuous_const)
    exact (hmu.add hnu).add hht
  -- reduce to continuity at each point
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, s₀⟩
  set n : ℤ := ⌊s₀⌋ with hn
  -- seam agreement of the two adjacent strip formulas at the integer `n`
  have hagree : ∀ a : X × ℝ, a.2 = (n : ℝ) →
      dist (muFun T hdiam (baseIter T hτ (n - 1) a.1, a.2 - ((n - 1 : ℤ) : ℝ))) Mq
          + dist (nuFun T hdiam (baseIter T hτ (n - 1) a.1, a.2 - ((n - 1 : ℤ) : ℝ))) Nq
          + hgt (a.2 - ((n - 1 : ℤ) : ℝ)) hq
        = dist (muFun T hdiam (baseIter T hτ n a.1, a.2 - (n : ℝ))) Mq
          + dist (nuFun T hdiam (baseIter T hτ n a.1, a.2 - (n : ℝ))) Nq
          + hgt (a.2 - (n : ℝ)) hq := by
    intro a ha
    have e1 : a.2 - ((n - 1 : ℤ) : ℝ) = 1 := by push_cast; rw [ha]; ring
    have e0 : a.2 - (n : ℝ) = 0 := by rw [ha]; ring
    have hb : T (baseIter T hτ (n - 1) a.1) = baseIter T hτ n a.1 := by
      have h := baseIter_add_one T hτ (n - 1) a.1
      rw [show (n - 1) + 1 = n by ring] at h
      exact h.symm
    rw [e1, e0, muFun_seam, nuFun_seam, hb, hgt_one_eq_zero_height hq0 hq1]
  -- the two-strip gluing is continuous
  have hH : Continuous (fun a : X × ℝ =>
      if a.2 ≤ (n : ℝ) then
        dist (muFun T hdiam (baseIter T hτ (n - 1) a.1, a.2 - ((n - 1 : ℤ) : ℝ))) Mq
          + dist (nuFun T hdiam (baseIter T hτ (n - 1) a.1, a.2 - ((n - 1 : ℤ) : ℝ))) Nq
          + hgt (a.2 - ((n - 1 : ℤ) : ℝ)) hq
      else
        dist (muFun T hdiam (baseIter T hτ n a.1, a.2 - (n : ℝ))) Mq
          + dist (nuFun T hdiam (baseIter T hτ n a.1, a.2 - (n : ℝ))) Nq
          + hgt (a.2 - (n : ℝ)) hq) :=
    Continuous.if_le (hcontg (n - 1)) (hcontg n) continuous_snd continuous_const hagree
  -- near `(x₀, s₀)` the composite agrees with this gluing
  have hUmem : {a : X × ℝ | (n : ℝ) - 1 < a.2 ∧ a.2 < (n : ℝ) + 1} ∈ nhds ((x₀, s₀) : X × ℝ) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)
    · refine ⟨?_, ?_⟩
      · have h := Int.floor_le s₀; rw [← hn] at h; change (n : ℝ) - 1 < s₀; linarith
      · have h := Int.lt_floor_add_one s₀; rw [← hn] at h; change s₀ < (n : ℝ) + 1; linarith
  refine (hH.continuousAt).congr (Filter.eventuallyEq_of_mem hUmem ?_)
  rintro ⟨x, s⟩ ⟨hlo, hhi⟩
  dsimp only
  have key : embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) q
      = dist (muFun T hdiam (baseIter T hτ ⌊s⌋ x, Int.fract s)) Mq
        + dist (nuFun T hdiam (baseIter T hτ ⌊s⌋ x, Int.fract s)) Nq
        + hgt (Int.fract s) hq := by
    unfold embDist
    rw [suspensionRep_mk' T hτ hτ1 x s, ← hMq, ← hNq, ← hhq]
  rcases lt_or_ge s (n : ℝ) with hsn | hsn
  · -- left strip: ⌊s⌋ = n − 1
    have hfl : ⌊s⌋ = n - 1 := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨by linarith, by linarith⟩
    have hfr : Int.fract s = s - ((n - 1 : ℤ) : ℝ) := by
      rw [show Int.fract s = s - ((⌊s⌋ : ℤ) : ℝ) from rfl, hfl]
    rw [if_pos hsn.le, key, hfl, hfr]
  · -- right strip: ⌊s⌋ = n
    have hfl : ⌊s⌋ = n := by
      rw [Int.floor_eq_iff]; exact ⟨hsn, by linarith⟩
    have hfr : Int.fract s = s - (n : ℝ) := by
      rw [show Int.fract s = s - ((⌊s⌋ : ℤ) : ℝ) from rfl, hfl]
    rcases eq_or_lt_of_le hsn with hse | hslt
    · -- s = n : both `if` and the floor formula use the seam agreement
      rw [if_pos hse.ge, key, hfl, hfr]
      exact hagree (x, s) hse.symm
    · rw [if_neg (not_le.mpr hslt), key, hfl, hfr]

/-! ### The metric-space packaging

With the quotient-continuity in hand, we identify the `embDist` metric topology with the canonical
quotient topology (`embDist_isOpen_iff`) and package `embDist` as a genuine `MetricSpace` instance
on the suspension space whose topology is *definitionally* the quotient one (no diamond), following
`MetricSpace.ofDistTopology` idiom. For a compact base this then makes the suspension space a Polish
space. -/

/-- Continuity of the embedding distance in its **second** argument, from the first by symmetry. -/
theorem continuous_embDist_right (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T)
    (hTs : Continuous ⇑T.symm) (p : SuspensionSpace T hτ) :
    Continuous (fun r => embDist T hτ hτ1 hdiam p r) :=
  (embDist_continuous T hτ hτ1 hdiam hT hTs p).congr
    (fun r => embDist_comm T hτ hτ1 hdiam r p)

/-- **The embedding-distance openness criterion equals the quotient topology.** A set is open in the
canonical quotient topology iff it contains an `embDist`-ball around each of its points. Backward:
each ball is open by continuity of `embDist`. Forward (uses compactness of the base): the complement
is compact, `embDist p (·)` is continuous and strictly positive on it (separation), so it attains a
positive minimum which is a valid ball radius. -/
theorem embDist_isOpen_iff (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T)
    (hTs : Continuous ⇑T.symm) [CompactSpace X] (s : Set (SuspensionSpace T hτ)) :
    IsOpen s ↔ ∀ p ∈ s, ∃ ε > 0, ∀ r, embDist T hτ hτ1 hdiam p r < ε → r ∈ s := by
  haveI : CompactSpace (SuspensionSpace T hτ) := compactSpace_suspensionSpace T hτ hτ1
  constructor
  · intro hs p hp
    have hcont : Continuous (fun r => embDist T hτ hτ1 hdiam p r) :=
      continuous_embDist_right T hτ hτ1 hdiam hT hTs p
    rcases Set.eq_empty_or_nonempty sᶜ with hce | hne
    · refine ⟨1, one_pos, fun r _ => ?_⟩
      have hsu : s = Set.univ := by rwa [compl_empty_iff] at hce
      rw [hsu]; exact Set.mem_univ r
    · have hcpt : IsCompact sᶜ := hs.isClosed_compl.isCompact
      obtain ⟨r₀, hr₀, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
      have hmpos : 0 < embDist T hτ hτ1 hdiam p r₀ := by
        rcases (embDist_nonneg T hτ hτ1 hdiam p r₀).lt_or_eq with h | h
        · exact h
        · have hpr : p = r₀ := embDist_eq_zero T hτ hτ1 hdiam h.symm
          exact absurd (hpr ▸ hp) hr₀
      refine ⟨embDist T hτ hτ1 hdiam p r₀, hmpos, fun r hr => ?_⟩
      by_contra hrs
      exact absurd (isMinOn_iff.mp hmin r hrs) (not_le.mpr hr)
  · intro h
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨ε, hε, hball⟩ := h p hp
    refine ⟨{r | embDist T hτ hτ1 hdiam p r < ε}, fun r hr => hball r hr,
      isOpen_lt (continuous_embDist_right T hτ hτ1 hdiam hT hTs p) continuous_const, ?_⟩
    change embDist T hτ hτ1 hdiam p p < ε
    rw [embDist_self]; exact hε

include hτ1 in
/-- **The Bowen–Walters metric space.** `embDist` packaged as a genuine `MetricSpace` instance on
the constant-roof suspension space, built with `MetricSpace.ofDistTopology` against the pre-existing
canonical quotient topology, so the metric topology is definitionally the quotient topology and
inherited structure (`CompactSpace`, `BorelSpace`, …) carries over with no diamond. Hypotheses
(`diam X ≤ 1`, continuity of `T`/`T⁻¹`, `CompactSpace X`) live on the `def`, mirroring
`biShiftMetricSpace`. -/
@[implicit_reducible]
noncomputable def suspensionMetricSpace (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T)
    (hTs : Continuous ⇑T.symm) [CompactSpace X] : MetricSpace (SuspensionSpace T hτ) :=
  MetricSpace.ofDistTopology (embDist T hτ hτ1 hdiam)
    (embDist_self T hτ hτ1 hdiam) (embDist_comm T hτ hτ1 hdiam)
    (embDist_triangle T hτ hτ1 hdiam) (embDist_isOpen_iff T hτ hτ1 hdiam hT hTs)
    (fun _ _ h => embDist_eq_zero T hτ hτ1 hdiam h)

include hτ1 in
/-- **The constant-roof suspension space is Polish** for a compact base: a compact metric space is
second-countable (hence separable) and complete, so it is Polish. Stated for the canonical quotient
topology, which the `embDist` metric induces. -/
theorem suspensionPolish (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T)
    (hTs : Continuous ⇑T.symm) [CompactSpace X] : PolishSpace (SuspensionSpace T hτ) := by
  letI := suspensionMetricSpace T hτ hτ1 hdiam hT hTs
  haveI : CompactSpace (SuspensionSpace T hτ) := compactSpace_suspensionSpace T hτ hτ1
  haveI : CompleteSpace (SuspensionSpace T hτ) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  infer_instance

/-! ### The flow-Lipschitz estimate

The suspension flow moves points along the fibres at unit speed, and under `diam X ≤ 1` this is an
(almost) isometry: `embDist (ζ_a q) (ζ_b q) ≤ 5 · |a − b|`. For a unit step the estimate follows
from the vertical and seam move bounds (a single seam is crossed); for a large step the global bound
`embDist ≤ 5` (the Kuratowski parts are `≤ 1` in norm, the height part `≤ 1`) closes it. -/

/-- The Kuratowski image has sup-norm at most `1` (the base has diameter `≤ 1`). -/
theorem norm_kur_le_one (hdiam : ∀ a b : X, dist a b ≤ 1) (a : X) : ‖kur hdiam a‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le (by norm_num)).2 fun w => by
    rw [kur_apply, Real.norm_eq_abs, abs_of_nonneg dist_nonneg]; exact hdiam a w

/-- A nonnegative sub-convex combination of two Kuratowski images has sup-norm at most `1`. -/
theorem norm_kur_comb_le (hdiam : ∀ a b : X, dist a b ≤ 1) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β ≤ 1) (u v : X) : ‖α • kur hdiam u + β • kur hdiam v‖ ≤ 1 := by
  have hu := norm_kur_le_one hdiam u
  have hv := norm_kur_le_one hdiam v
  calc ‖α • kur hdiam u + β • kur hdiam v‖
      ≤ ‖α • kur hdiam u‖ + ‖β • kur hdiam v‖ := norm_add_le _ _
    _ = α * ‖kur hdiam u‖ + β * ‖kur hdiam v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα,
          abs_of_nonneg hβ]
    _ ≤ α * 1 + β * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hu hα) (mul_le_mul_of_nonneg_left hv hβ)
    _ ≤ 1 := by linarith

/-- The `muFun` test bundle has sup-norm at most `1` at heights `s ∈ [0, 1]`. -/
theorem norm_muFun_le (hdiam : ∀ a b : X, dist a b ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x : X) : ‖muFun T hdiam (x, s)‖ ≤ 1 := by
  unfold muFun
  exact norm_kur_comb_le hdiam (by linarith) hs0 (by linarith) x (T x)

/-- The `nuFun` test bundle has sup-norm at most `1` at heights `s ∈ [0, 1]`. -/
theorem norm_nuFun_le (hdiam : ∀ a b : X, dist a b ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (x : X) : ‖nuFun T hdiam (x, s)‖ ≤ 1 := by
  unfold nuFun
  have hsq : (1 - s) ^ 2 ≤ 1 := by nlinarith
  exact norm_kur_comb_le hdiam (sq_nonneg _) (by nlinarith) (by linarith) x (T x)

/-- **Global bound.** The embedding distance never exceeds `5` (Kuratowski parts `≤ 2` each by the
sup-norm triangle inequality with `‖muFun‖, ‖nuFun‖ ≤ 1`, height part `≤ 1`). -/
theorem embDist_le_five (hdiam : ∀ a b : X, dist a b ≤ 1) (p q : SuspensionSpace T hτ) :
    embDist T hτ hτ1 hdiam p q ≤ 5 := by
  set a := suspensionRep T hτ hτ1 p with ha
  set b := suspensionRep T hτ hτ1 q with hb
  have ha0 : 0 ≤ a.2 := suspensionRep_nonneg T hτ hτ1 p
  have ha1 : a.2 ≤ 1 := (suspensionRep_lt_one T hτ hτ1 p).le
  have hb0 : 0 ≤ b.2 := suspensionRep_nonneg T hτ hτ1 q
  have hb1 : b.2 ≤ 1 := (suspensionRep_lt_one T hτ hτ1 q).le
  have hμ : dist (muFun T hdiam a) (muFun T hdiam b) ≤ 2 := by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have := norm_muFun_le T hdiam ha0 ha1 a.1
      have := norm_muFun_le T hdiam hb0 hb1 b.1
      linarith)
  have hν : dist (nuFun T hdiam a) (nuFun T hdiam b) ≤ 2 := by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have := norm_nuFun_le T hdiam ha0 ha1 a.1
      have := norm_nuFun_le T hdiam hb0 hb1 b.1
      linarith)
  have hh : hgt a.2 b.2 ≤ 1 :=
    (hgt_le_one_sub _ _).trans (by linarith [abs_nonneg (a.2 - b.2)])
  unfold embDist; linarith

/-- **Unit-step vertical bound.** Two points on a common base fibre whose heights differ by `< 1`
are at embedding distance at most `4 · (r − p)`. If the two heights share a floor this is the
vertical bound; otherwise exactly one seam is crossed and the seam + vertical bounds combine. -/
theorem embDist_step_le (hdiam : ∀ a b : X, dist a b ≤ 1) (x : X) {p r : ℝ} (hpr : p ≤ r)
    (hlt : r - p < 1) :
    embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, p)) (suspensionMk T hτ (x, r))
      ≤ 4 * (r - p) := by
  rw [← suspensionMk_unitCoord T hτ hτ1 x p, ← suspensionMk_unitCoord T hτ hτ1 x r]
  have hfp : Int.fract p ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg p, Int.fract_lt_one p⟩
  have hfr : Int.fract r ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩
  have h1 : ⌊p⌋ ≤ ⌊r⌋ := Int.floor_le_floor hpr
  have h2 : ⌊r⌋ ≤ ⌊p⌋ + 1 := by
    rw [Int.floor_le_iff]; push_cast; have := Int.lt_floor_add_one p; linarith
  have hfloor : ⌊r⌋ = ⌊p⌋ ∨ ⌊r⌋ = ⌊p⌋ + 1 := by omega
  rcases hfloor with heq | heq
  · rw [heq]
    have hv := embDist_vertical_le T hτ hτ1 hdiam hfp hfr (baseIter T hτ ⌊p⌋ x)
    refine hv.trans (le_of_eq ?_)
    have hval : |Int.fract p - Int.fract r| = r - p := by
      rw [show Int.fract p - Int.fract r = -(r - p) by
        rw [show Int.fract p = p - (⌊p⌋ : ℝ) from rfl,
          show Int.fract r = r - (⌊r⌋ : ℝ) from rfl, heq]; ring, abs_neg,
        abs_of_nonneg (by linarith)]
    rw [hval]
  · rw [heq]
    set y := baseIter T hτ ⌊p⌋ x with hy
    have hTy : T y = baseIter T hτ (⌊p⌋ + 1) x := (baseIter_add_one T hτ ⌊p⌋ x).symm
    rw [← hTy]
    have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl 0, one_pos⟩
    have hp1 : (p : ℝ) < ⌊p⌋ + 1 := Int.lt_floor_add_one p
    calc embDist T hτ hτ1 hdiam (suspensionMk T hτ (y, Int.fract p))
          (suspensionMk T hτ (T y, Int.fract r))
        ≤ embDist T hτ hτ1 hdiam (suspensionMk T hτ (y, Int.fract p))
            (suspensionMk T hτ (T y, 0))
          + embDist T hτ hτ1 hdiam (suspensionMk T hτ (T y, 0))
            (suspensionMk T hτ (T y, Int.fract r)) := embDist_triangle T hτ hτ1 hdiam _ _ _
      _ ≤ 3 * (1 - Int.fract p) + 4 * Int.fract r := by
          refine add_le_add (embDist_seam_le T hτ hτ1 hdiam hfp y) ?_
          have hv := embDist_vertical_le T hτ hτ1 hdiam h0 hfr (T y)
          rwa [show |(0 : ℝ) - Int.fract r| = Int.fract r by
            rw [zero_sub, abs_neg, abs_of_nonneg (Int.fract_nonneg r)]] at hv
      _ ≤ 4 * (r - p) := by
          rw [show Int.fract p = p - (⌊p⌋ : ℝ) from rfl,
            show Int.fract r = r - ((⌊p⌋ : ℝ) + 1) by
              rw [show Int.fract r = r - (⌊r⌋ : ℝ) from rfl, heq]; push_cast; ring]
          linarith

/-- **Flow-Lipschitz estimate.** The suspension flow is `5`-Lipschitz in time on each orbit:
`embDist (ζ_a q) (ζ_b q) ≤ 5 · |a − b|`. Unit steps use `embDist_step_le`; large steps the global
bound `embDist_le_five`. -/
theorem embDist_flow_le (hdiam : ∀ a b : X, dist a b ≤ 1) (a b : ℝ) (q : SuspensionSpace T hτ) :
    embDist T hτ hτ1 hdiam (suspensionFlowMap T hτ a q) (suspensionFlowMap T hτ b q)
      ≤ 5 * |a - b| := by
  set r := suspensionRep T hτ hτ1 q with hr
  have hqmk : suspensionMk T hτ r = q := suspensionMk_suspensionRep T hτ hτ1 q
  have hfa : suspensionFlowMap T hτ a q = suspensionMk T hτ (r.1, r.2 + a) := by
    rw [← hqmk, suspensionFlowMap_mk, suspensionTranslate_apply]
  have hfb : suspensionFlowMap T hτ b q = suspensionMk T hτ (r.1, r.2 + b) := by
    rw [← hqmk, suspensionFlowMap_mk, suspensionTranslate_apply]
  rw [hfa, hfb]
  have hab : |a - b| = |(r.2 + a) - (r.2 + b)| := by rw [show (r.2 + a) - (r.2 + b) = a - b by ring]
  rcases lt_or_ge |a - b| 1 with hsmall | hbig
  · rcases le_total (r.2 + a) (r.2 + b) with hle | hle
    · have hlt : (r.2 + b) - (r.2 + a) < 1 := by
        rw [show (r.2 + b) - (r.2 + a) = b - a by ring]
        calc b - a ≤ |b - a| := le_abs_self _
          _ = |a - b| := abs_sub_comm b a
          _ < 1 := hsmall
      have hstep := embDist_step_le T hτ hτ1 hdiam r.1 hle hlt
      refine hstep.trans ?_
      have hle' : b - a ≤ |a - b| := by
        calc b - a ≤ |b - a| := le_abs_self _
          _ = |a - b| := abs_sub_comm b a
      rw [show (r.2 + b) - (r.2 + a) = b - a by ring]
      nlinarith [abs_nonneg (a - b)]
    · have hlt : (r.2 + a) - (r.2 + b) < 1 := by
        rw [show (r.2 + a) - (r.2 + b) = a - b by ring]
        exact (le_abs_self _).trans_lt hsmall
      have hstep := embDist_step_le T hτ hτ1 hdiam r.1 hle hlt
      rw [embDist_comm T hτ hτ1 hdiam (suspensionMk T hτ (r.1, r.2 + a))]
      refine hstep.trans ?_
      have hle' : a - b ≤ |a - b| := le_abs_self _
      rw [show (r.2 + a) - (r.2 + b) = a - b by ring]
      nlinarith [abs_nonneg (a - b)]
  · refine (embDist_le_five T hτ hτ1 hdiam _ _).trans ?_
    nlinarith [hbig]

/-- **Seam-wrap lower comparison.** For representatives `(x, s)`, `(y, t)` with `s, t ∈ [0, 1)` the
`T`-image distance is controlled by the embedding distance up to the seam slack `(1 − s) + t`
(sharp in the wrap regime `s → 1`, `t → 0`): `dist (T x) y ≤ embDist [x,s] [y,t] + (1 − s) + t`. The
`muFun` part recovers `kur (T x) − kur y` up to two boundary corrections, each `≤ 1` under
`diam X ≤ 1`. -/
theorem dist_map_le_embDist_wrap (hdiam : ∀ a b : X, dist a b ≤ 1) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) (x y : X) :
    dist (T x) y ≤ embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
      + (1 - s) + t := by
  have hmu : dist (muFun T hdiam (x, s)) (muFun T hdiam (y, t))
      ≤ embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t)) := by
    have h := dist_muFun_le_embDist T hτ hτ1 hdiam
      (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
    rwa [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 y ht] at h
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
    _ ≤ embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
        + (1 - s) + t := by
        have hA : (1 - s) * dist (T x) x ≤ (1 - s) :=
          mul_le_of_le_one_right (by linarith [hs.2.le]) (hdiam _ _)
        have hB : t * dist (T y) y ≤ t := mul_le_of_le_one_right ht.1 (hdiam _ _)
        linarith [hmu]

/-! ### Sanity: the metric layer under the local instance -/

/-- **Sanity certificate.** Under the `embDist` metric instance `suspensionMetricSpace`, the bundled
`dist` is *definitionally* `embDist` (mirrors `BiShiftMetric.dist_eq_distZ`). Because
`suspensionMetricSpace` carries the geometric hypotheses `hdiam`/`hT`/`hTs` (and `CompactSpace X`)
as explicit arguments rather than as instances, the instance is threaded with `letI` in the
statement instead of a bare `attribute [local instance]`. -/
theorem dist_eq_embDist (hdiam : ∀ a b : X, dist a b ≤ 1) (hT : Continuous ⇑T)
    (hTs : Continuous ⇑T.symm) [CompactSpace X] (p q : SuspensionSpace T hτ) :
    letI := suspensionMetricSpace T hτ hτ1 hdiam hT hTs
    dist p q = embDist T hτ hτ1 hdiam p q := rfl

end

end ErgodicTheory
