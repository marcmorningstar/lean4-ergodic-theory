/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapAWContraction
import ErgodicTheory.Examples.CatMapAdlerWeissMeasure
import ErgodicTheory.Krieger.GeneratingOfSeparating

/-!
# The Adler–Weiss partition is a two-sided generator for the cat map

This module closes the generator argument for the Adler–Weiss Markov partition
`catAWPartition` of the Arnold cat map `catTorus` on the sup-metric torus
`T2 = Fin 2 → UnitAddCircle`.  It has three layers.

**Exact cover.**  The two golden rectangles `R₁ = [0,φ)×[0,φ)` and `R₂ = [φ,φ²)×[0,1)` (in the
eigen-coordinates `pC, qC`) tile the plane under the golden image `{(φm+n, m−φn)}` of the integer
lattice: every point of the torus lies in *some* projected branch, so the junk cell of
`catAWPartition` is empty — not merely null (`exists_awCell_succ`, `awUnion_eq_univ`,
`awCell_zero_eq_empty`).  The reduction is a four-case skew-lattice division: with a lift in the
unit square, the eigen-coordinates satisfy `p ∈ [0, φ+1)` and `q ∈ (−φ, 1)`, and subtracting one
of the four lattice vectors `(0,0), (0,1), (−1,0), (−1,1)` (chosen by the signs of `q`, `q+1` and
the position of `p` relative to `1`) lands the point in `R₁ ∪ R₂`.

**Unique admissible itinerary.**  Each toral point `x` has, at every time `k : ℤ`, a branch cell
containing `ziter catTorusEquiv k x` (`awSymb`), and consecutive symbols are admissible:
`tgt (awSymb x k) = src (awSymb x (k+1))` (`awSymb_admissible`), because one dynamical step maps a
branch representative into the target rectangle (`branch_step`) while the covering projection is
injective on `R₁ ∪ R₂`.

**Separation and the generator.**  Two points sharing every cell along the two-sided itinerary
carry branch representatives whose difference propagates *linearly* (`awRep_step`, offsets cancel),
so the two-sided contraction estimate `dist_le_of_coordDiff` gives `dist x y ≤ 2·φ·μ^m` for every
window half-length `m`; letting `m → ∞` forces `x = y` (`eq_of_matching_awCells`).  Hence the
two-sided cell itinerary separates points (`separating_catAWPartition`), and the Blackwell bridge
`isGeneratingTwoSided_of_separating` yields the prize:

* `ErgodicTheory.CatMapToral.isGeneratingTwoSided_catAWPartition` —
  `IsGeneratingTwoSided catTorusEquiv catAWPartition`.
-/

open Matrix

noncomputable section

namespace ErgodicTheory.CatMapToral

/-! ## Membership normal forms for the golden rectangles -/

/-- Membership in the first golden rectangle `R₁ = [0,φ)×[0,φ)`, unfolded. -/
lemma mem_awBox_zero {v : Fin 2 → ℝ} :
    v ∈ awBox 0 ↔ (0 ≤ pC v ∧ pC v < phiAW) ∧ 0 ≤ qC v ∧ qC v < phiAW := by
  simp [awBox, Set.mem_Ico]

/-- Membership in the second golden rectangle `R₂ = [φ,φ²)×[0,1)`, unfolded. -/
lemma mem_awBox_one {v : Fin 2 → ℝ} :
    v ∈ awBox 1 ↔ (phiAW ≤ pC v ∧ pC v < phiAW ^ 2) ∧ 0 ≤ qC v ∧ qC v < 1 := by
  simp [awBox, Set.mem_Ico]

/-- Constructor for membership in a branch. -/
lemma mem_branchBox {e : Fin 5} {v : Fin 2 → ℝ} (h1 : pa e ≤ pC v) (h2 : pC v < pb e)
    (h3 : 0 ≤ qC v) (h4 : qC v < qHeight (src e)) : v ∈ branchBox e :=
  ⟨⟨h1, h2⟩, h3, h4⟩

/-! ## The exact cover -/

/-- An integer pair projects to `0` on the torus. -/
lemma catProj_intPair (m n : ℤ) : catProj ![(m : ℝ), (n : ℝ)] = 0 := by
  funext i
  fin_cases i <;>
    · simp only [catProj, Pi.zero_apply]
      exact coe_intCast_eq_zero _

/-- **The skew-lattice division step.**  Every vector `v` with coordinates in `[0,1)` has an
integer translate in `R₁ ∪ R₂`.  In eigen-coordinates `p = pC v ∈ [0, φ+1)` and
`q = qC v ∈ (−φ, 1)`, and one of the four lattice vectors `(0,0), (0,1), (−1,0), (−1,1)` —
selected by the position of `q` relative to `0` and `−1` and of `p` relative to `1` — moves
`(p, q)` into `([0,φ)×[0,φ)) ∪ ([φ,φ²)×[0,1))`. -/
lemma exists_intPair_mem_awUnion {v : Fin 2 → ℝ} (h00 : 0 ≤ v 0) (h01 : v 0 < 1)
    (h10 : 0 ≤ v 1) (h11 : v 1 < 1) :
    ∃ m n : ℤ, v - ![(m : ℝ), (n : ℝ)] ∈ awBox 0 ∪ awBox 1 := by
  have hφ1 := one_lt_phiAW
  have hφ2 := phiAW_lt_two
  have hsq := phiAW_sq
  have hp0 : 0 ≤ pC v := by
    simp only [pC]; nlinarith [mul_nonneg phiAW_pos.le h00]
  have hpu : pC v < phiAW + 1 := by
    simp only [pC]; nlinarith [mul_lt_mul_of_pos_left h01 phiAW_pos]
  have hql : -phiAW < qC v := by
    simp only [qC]; nlinarith [mul_lt_mul_of_pos_left h11 phiAW_pos]
  have hqu : qC v < 1 := by
    simp only [qC]; nlinarith [mul_nonneg phiAW_pos.le h10]
  rcases le_or_gt 0 (qC v) with hq | hq
  · -- `q ∈ [0, 1)`: no translation needed; the box is decided by `p` against `φ`.
    refine ⟨0, 0, ?_⟩
    have hpw : pC (v - ![((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ)]) = pC v := by
      rw [pC_sub, pC_cons]; push_cast; ring
    have hqw : qC (v - ![((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ)]) = qC v := by
      rw [qC_sub, qC_cons]; push_cast; ring
    rcases lt_or_ge (pC v) phiAW with hpφ | hpφ
    · left
      rw [mem_awBox_zero, hpw, hqw]
      exact ⟨⟨hp0, hpφ⟩, hq, by linarith⟩
    · right
      rw [mem_awBox_one, hpw, hqw]
      exact ⟨⟨hpφ, by linarith⟩, hq, hqu⟩
  · rcases le_or_gt 1 (pC v) with hp1 | hp1
    · -- `q < 0 ≤ p − 1`: translate by `(0, 1)`; lands in `R₁`.
      refine ⟨0, 1, ?_⟩
      have hpw : pC (v - ![((0 : ℤ) : ℝ), ((1 : ℤ) : ℝ)]) = pC v - 1 := by
        rw [pC_sub, pC_cons]; push_cast; ring
      have hqw : qC (v - ![((0 : ℤ) : ℝ), ((1 : ℤ) : ℝ)]) = qC v + phiAW := by
        rw [qC_sub, qC_cons]; push_cast; ring
      left
      rw [mem_awBox_zero, hpw, hqw]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rcases le_or_gt (-1) (qC v) with hqm | hqm
      · -- `p < 1`, `q ∈ [−1, 0)`: translate by `(−1, 0)`; lands in `R₂`.
        refine ⟨-1, 0, ?_⟩
        have hpw : pC (v - ![((-1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)]) = pC v + phiAW := by
          rw [pC_sub, pC_cons]; push_cast; ring
        have hqw : qC (v - ![((-1 : ℤ) : ℝ), ((0 : ℤ) : ℝ)]) = qC v + 1 := by
          rw [qC_sub, qC_cons]; push_cast; ring
        right
        rw [mem_awBox_one, hpw, hqw]
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      · -- `p < 1`, `q < −1`: translate by `(−1, 1)`; lands in `R₁`.
        refine ⟨-1, 1, ?_⟩
        have hpw : pC (v - ![((-1 : ℤ) : ℝ), ((1 : ℤ) : ℝ)]) = pC v + phiAW - 1 := by
          rw [pC_sub, pC_cons]; push_cast; ring
        have hqw : qC (v - ![((-1 : ℤ) : ℝ), ((1 : ℤ) : ℝ)]) = qC v + phiAW + 1 := by
          rw [qC_sub, qC_cons]; push_cast; ring
        left
        rw [mem_awBox_zero, hpw, hqw]
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Inside `R₁ ∪ R₂` the five branch windows are exhaustive: every point of the union lies in
some branch.  The windows `[0,φ−1), [φ−1,1), [1,φ)` split `R₁`'s unstable interval and
`[φ,2), [2,φ²)` split `R₂`'s. -/
lemma exists_branchBox_of_mem_awUnion {v : Fin 2 → ℝ} (hv : v ∈ awBox 0 ∪ awBox 1) :
    ∃ e : Fin 5, v ∈ branchBox e := by
  rcases hv with hv | hv
  · rw [mem_awBox_zero] at hv
    obtain ⟨⟨hp0, hp1⟩, hq0, hq1⟩ := hv
    rcases lt_or_ge (pC v) (phiAW - 1) with h | h
    · exact ⟨0, mem_branchBox hp0 h hq0 hq1⟩
    · rcases lt_or_ge (pC v) 1 with h' | h'
      · exact ⟨1, mem_branchBox h h' hq0 hq1⟩
      · exact ⟨2, mem_branchBox h' hp1 hq0 hq1⟩
  · rw [mem_awBox_one] at hv
    obtain ⟨⟨hp0, hp1⟩, hq0, hq1⟩ := hv
    rcases lt_or_ge (pC v) 2 with h | h
    · exact ⟨3, mem_branchBox hp0 h hq0 hq1⟩
    · exact ⟨4, mem_branchBox h hp1 hq0 hq1⟩

/-- **Exact cover, torus version.**  Every toral point lies in one of the five projected
branches: reduce a lift into the unit square with `Int.fract`, apply the skew-lattice division,
and select the branch window. -/
theorem exists_awCell_succ (x : T2) : ∃ e : Fin 5, x ∈ awCell e.succ := by
  obtain ⟨u, hu⟩ := catProj_surjective x
  have hproj : catProj (fun i => Int.fract (u i)) = x := by
    rw [← hu]
    funext i
    simp only [catProj]
    rw [show Int.fract (u i) = u i - (⌊u i⌋ : ℝ) from rfl, AddCircle.coe_sub,
      coe_intCast_eq_zero, sub_zero]
  obtain ⟨m, n, hmn⟩ := exists_intPair_mem_awUnion (v := fun i => Int.fract (u i))
    (Int.fract_nonneg _) (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _)
  obtain ⟨e, he⟩ := exists_branchBox_of_mem_awUnion hmn
  refine ⟨e, ?_⟩
  rw [awCell_succ]
  exact ⟨(fun i => Int.fract (u i)) - ![(m : ℝ), (n : ℝ)], he,
    by rw [catProj_sub, catProj_intPair, sub_zero, hproj]⟩

/-- **The five projected branches cover the torus exactly.** -/
theorem awUnion_eq_univ : (⋃ e : Fin 5, catProj '' branchBox e) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨e, he⟩ := exists_awCell_succ x
  rw [awCell_succ] at he
  exact Set.mem_iUnion.2 ⟨e, he⟩

/-- **The junk cell is empty** — not merely null: the Adler–Weiss tiling is exact. -/
theorem awCell_zero_eq_empty : awCell 0 = (∅ : Set T2) := by
  rw [awCell_zero, awUnion_eq_univ, Set.compl_univ]

/-! ## The unique admissible itinerary -/

/-- The two golden rectangles are disjoint in the plane (their unstable windows
`[0,φ)` and `[φ,φ²)` are).  Kept `private` to avoid a name clash with the general
`awBox_disjoint` proved (for arbitrary distinct box indices) in `CatMapAdlerWeissCount`;
both files are imported together by the entropy-assembly module. -/
private lemma awBox_disjoint : Disjoint (awBox 0) (awBox 1) := by
  rw [Set.disjoint_left]
  intro v h0 h1
  rw [mem_awBox_zero] at h0
  rw [mem_awBox_one] at h1
  exact absurd h1.1.1 (not_le.mpr h0.1.2)

/-- **One-step forcing at the level of lifts.**  If `r` lifts a point in branch `e` and `r'`
lifts its `catTorus`-image in branch `e'`, the transition is admissible: `tgt e = src e'`.
Indeed `catℝ *ᵥ r − off e` lies in `awBox (tgt e)` and projects to the same toral point as
`r' ∈ awBox (src e')`; injectivity of `catProj` on `R₁ ∪ R₂` identifies the two lifts, and the
plane-disjointness of the rectangles forces the box indices to agree. -/
theorem tgt_eq_src_of_step {e e' : Fin 5} {r r' : Fin 2 → ℝ}
    (hr : r ∈ branchBox e) (hr' : r' ∈ branchBox e')
    (hrr' : catProj r' = catTorus (catProj r)) : tgt e = src e' := by
  by_contra hne
  have h1 : catℝ *ᵥ r - off e ∈ awBox (tgt e) := branch_step e hr
  have h2 : catProj (catℝ *ᵥ r - off e) = catTorus (catProj r) := by
    rw [catProj_sub, catProj_off, sub_zero, catProj_mulVec]
  have hbox' : r' ∈ awBox (src e') := branchBox_subset_awBox_src e' hr'
  have hequ : r' = catℝ *ᵥ r - off e :=
    catProj_injOn_awUnion (awBox_subset_awUnion _ hbox') (awBox_subset_awUnion _ h1)
      (by rw [hrr', h2])
  rw [hequ] at hbox'
  have h01 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  rcases h01 (tgt e) with ht | ht <;> rcases h01 (src e') with hs | hs
  · exact hne (ht.trans hs.symm)
  · rw [ht] at h1; rw [hs] at hbox'
    exact Set.disjoint_left.mp awBox_disjoint h1 hbox'
  · rw [ht] at h1; rw [hs] at hbox'
    exact Set.disjoint_left.mp awBox_disjoint hbox' h1
  · exact hne (ht.trans hs.symm)

/-- **One-step forcing on the torus.**  Consecutive branch cells along an orbit are admissible. -/
theorem tgt_eq_src_of_awCell_step {e e' : Fin 5} {p : T2}
    (hp : p ∈ awCell e.succ) (hp' : catTorus p ∈ awCell e'.succ) : tgt e = src e' := by
  rw [awCell_succ] at hp hp'
  obtain ⟨r, hr, hrp⟩ := hp
  obtain ⟨r', hr', hrp'⟩ := hp'
  exact tgt_eq_src_of_step hr hr' (by rw [hrp]; exact hrp')

/-- The two-sided iterate advances one step of the cat map at a time. -/
lemma ziter_succ_apply (k : ℤ) (x : T2) :
    Krieger.ziter catTorusEquiv (k + 1) x = catTorus (Krieger.ziter catTorusEquiv k x) := by
  rw [add_comm k 1, Krieger.ziter_add, Function.comp_apply, Krieger.ziter_one,
    catTorusEquiv_apply]

/-- **The Adler–Weiss symbol** of `x` at time `k`: the branch whose projected cell contains
`ziter catTorusEquiv k x` (well defined by the exact cover; unique by cell disjointness). -/
def awSymb (x : T2) (k : ℤ) : Fin 5 :=
  (exists_awCell_succ (Krieger.ziter catTorusEquiv k x)).choose

/-- The defining membership of the Adler–Weiss symbol. -/
lemma awSymb_mem (x : T2) (k : ℤ) :
    Krieger.ziter catTorusEquiv k x ∈ awCell (awSymb x k).succ :=
  (exists_awCell_succ (Krieger.ziter catTorusEquiv k x)).choose_spec

/-- **Admissibility of the itinerary:** consecutive Adler–Weiss symbols are compatible,
`tgt (awSymb x k) = src (awSymb x (k+1))`. -/
theorem awSymb_admissible (x : T2) (k : ℤ) :
    tgt (awSymb x k) = src (awSymb x (k + 1)) := by
  refine tgt_eq_src_of_awCell_step (awSymb_mem x k) ?_
  rw [← ziter_succ_apply]
  exact awSymb_mem x (k + 1)

/-! ## Matching itineraries contract -/

/-- Two lifts in one branch have unstable coordinates within `φ` of each other. -/
lemma abs_pC_sub_lt_of_mem_branchBox {e : Fin 5} {u w : Fin 2 → ℝ}
    (hu : u ∈ branchBox e) (hw : w ∈ branchBox e) : |pC (u - w)| < phiAW := by
  obtain ⟨hup, _⟩ := hu
  obtain ⟨hwp, _⟩ := hw
  rw [Set.mem_Ico] at hup hwp
  have hwidth := pWidth_le e
  have h1 := one_lt_phiAW
  rw [pC_sub, abs_lt]
  constructor <;> linarith [hup.1, hup.2, hwp.1, hwp.2]

/-- Two lifts in one branch have stable coordinates within `φ` of each other. -/
lemma abs_qC_sub_lt_of_mem_branchBox {e : Fin 5} {u w : Fin 2 → ℝ}
    (hu : u ∈ branchBox e) (hw : w ∈ branchBox e) : |qC (u - w)| < phiAW := by
  obtain ⟨_, huq⟩ := hu
  obtain ⟨_, hwq⟩ := hw
  rw [Set.mem_Ico] at huq hwq
  have hh := qHeight_src_le e
  rw [qC_sub, abs_lt]
  constructor <;> linarith [huq.1, huq.2, hwq.1, hwq.2]

/-- **Matching itineraries contract.**  If `y` follows `x` through every Adler–Weiss cell along
the whole two-sided orbit, then `dist x y ≤ 2·φ·μ^m` for every window half-length `m`.  Branch
representatives of the two orbits satisfy the same affine recursion (`awRep_step`; the offsets
cancel in differences), so the difference of lifts propagates linearly and the two-sided
contraction estimate `dist_le_of_coordDiff` applies. -/
theorem dist_le_of_matching_awCells {x y : T2}
    (h : ∀ (k : ℤ) (e : Fin 5), Krieger.ziter catTorusEquiv k x ∈ awCell e.succ →
      Krieger.ziter catTorusEquiv k y ∈ awCell e.succ) (m : ℕ) :
    dist x y ≤ 2 * phiAW * mu ^ m := by
  -- Choose, at every time, a common branch and lifts of the two orbit points.
  have H : ∀ k : ℤ, ∃ (e : Fin 5) (r s : Fin 2 → ℝ),
      r ∈ branchBox e ∧ s ∈ branchBox e ∧
      catProj r = Krieger.ziter catTorusEquiv k x ∧
      catProj s = Krieger.ziter catTorusEquiv k y := by
    intro k
    obtain ⟨e, he⟩ := exists_awCell_succ (Krieger.ziter catTorusEquiv k x)
    have hy := h k e he
    rw [awCell_succ] at he hy
    obtain ⟨r, hr, hrp⟩ := he
    obtain ⟨s, hs, hsp⟩ := hy
    exact ⟨e, r, s, hr, hs, hrp, hsp⟩
  choose e r s hr hs hrx hsy using H
  -- The one-step affine identities for both representative sequences.
  have hadm : ∀ k : ℤ, tgt (e k) = src (e (k + 1)) := by
    intro k
    refine tgt_eq_src_of_step (hr k) (hr (k + 1)) ?_
    rw [hrx, hrx]
    exact ziter_succ_apply k x
  have hstepr : ∀ k : ℤ, r (k + 1) = catℝ *ᵥ r k - off (e k) := by
    intro k
    refine awRep_step (hadm k) (hr k) (hr (k + 1)) ?_
    rw [hrx, hrx]
    exact ziter_succ_apply k x
  have hsteps : ∀ k : ℤ, s (k + 1) = catℝ *ᵥ s k - off (e k) := by
    intro k
    refine awRep_step (hadm k) (hs k) (hs (k + 1)) ?_
    rw [hsy, hsy]
    exact ziter_succ_apply k y
  -- Differences propagate linearly: the integer offsets cancel.
  have hiter : ∀ (j : ℕ) (k : ℤ), r (k + j) - s (k + j) = (catℝ ^ j) *ᵥ (r k - s k) := by
    intro j
    induction j with
    | zero => intro k; simp [Matrix.one_mulVec]
    | succ i ih =>
      intro k
      have hidx : (k + ((i + 1 : ℕ) : ℤ)) = (k + (i : ℕ)) + 1 := by push_cast; ring
      rw [hidx, hstepr, hsteps, sub_sub_sub_cancel_right, ← Matrix.mulVec_sub, ih,
        Matrix.mulVec_mulVec, pow_succ']
  -- The time-0 difference lifts `x − y`.
  have hx0 : catProj (r 0) = x := by rw [hrx 0, Krieger.ziter_zero, id_eq]
  have hy0 : catProj (s 0) = y := by rw [hsy 0, Krieger.ziter_zero, id_eq]
  have hxy : catProj (r 0 - s 0) = x - y := by rw [catProj_sub, hx0, hy0]
  -- Unstable control at the forward end of the window.
  have hfor := hiter m 0
  rw [zero_add] at hfor
  have hpm : |pC ((catℝ ^ m) *ᵥ (r 0 - s 0))| < phiAW := by
    rw [← hfor]
    exact abs_pC_sub_lt_of_mem_branchBox (hr _) (hs _)
  -- Stable control at the backward end of the window.
  have hbwd := hiter m (-(m : ℤ))
  rw [neg_add_cancel] at hbwd
  have hqm : |qC (r (-(m : ℤ)) - s (-(m : ℤ)))| < phiAW :=
    abs_qC_sub_lt_of_mem_branchBox (hr _) (hs _)
  exact dist_le_of_coordDiff x y m (r 0 - s 0) hxy hpm
    (r (-(m : ℤ)) - s (-(m : ℤ))) hbwd.symm hqm

/-- **Points with matching two-sided itineraries coincide:** the contraction bound `2·φ·μ^m`
tends to `0` as the window grows. -/
theorem eq_of_matching_awCells {x y : T2}
    (h : ∀ (k : ℤ) (e : Fin 5), Krieger.ziter catTorusEquiv k x ∈ awCell e.succ →
      Krieger.ziter catTorusEquiv k y ∈ awCell e.succ) : x = y := by
  have hlim : Filter.Tendsto (fun m : ℕ => 2 * phiAW * mu ^ m) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun m : ℕ => mu ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one mu_pos.le mu_lt_one
    have h1 := h0.const_mul (2 * phiAW)
    simpa using h1
  have hle : dist x y ≤ 0 := ge_of_tendsto' hlim (dist_le_of_matching_awCells h)
  exact eq_of_dist_eq_zero (le_antisymm hle dist_nonneg)

/-! ## The partition separates points and generates -/

/-- The cells of the assembled measure partition are the Adler–Weiss cells. -/
lemma catAWPartition_cells (i : Fin 6) : catAWPartition.cells i = awCell i := rfl

/-- **The two-sided Adler–Weiss itinerary separates points:** distinct toral points are told
apart by some cell of `catAWPartition` at some time `n : ℤ`. -/
theorem separating_catAWPartition (x y : T2) (hxy : x ≠ y) :
    ∃ (n : ℤ) (i : Fin 6), Krieger.ziter catTorusEquiv n x ∈ catAWPartition.cells i ∧
      Krieger.ziter catTorusEquiv n y ∉ catAWPartition.cells i := by
  by_contra hcon
  push Not at hcon
  refine hxy (eq_of_matching_awCells fun k e hke => ?_)
  have := hcon k e.succ
  rw [catAWPartition_cells] at this
  exact this hke

/-- **THE PRIZE: the Adler–Weiss partition is a two-sided generator for the cat map.**
The exact golden tiling separates points along the two-sided orbit, and the Blackwell bridge
converts pointwise separation into σ-algebra saturation. -/
theorem isGeneratingTwoSided_catAWPartition :
    Krieger.IsGeneratingTwoSided catTorusEquiv catAWPartition :=
  Krieger.isGeneratingTwoSided_of_separating catTorusEquiv catAWPartition
    separating_catAWPartition

end ErgodicTheory.CatMapToral

end
