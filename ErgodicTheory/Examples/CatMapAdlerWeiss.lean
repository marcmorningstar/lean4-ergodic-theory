/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapCover
import ErgodicTheory.Examples.CatMapOrbit
import ErgodicTheory.Examples.CatMapEigenShadow

/-!
# The Adler–Weiss golden two-box geometry for the Arnold cat map

This module builds the **geometric skeleton** of the classical Adler–Weiss Markov partition of the
Arnold cat map `catTorus = torusMap !![2,1;1,1]` on the sup-metric torus
`T2 = Fin 2 → UnitAddCircle` (the plain product torus).
It is *pure geometry*: the two golden rectangles, the five affine branches of the induced map, the
keystone "one step of the dynamics maps each branch onto a target rectangle" identities, and the
injectivity of the covering projection on each branch.  No measure computations appear here; those
are layered on top with the measure toolkit elsewhere.

The eigen-coordinates are the two linear functionals
`pC v = φ·v₀ + v₁` (the unstable/expanding coordinate) and `qC v = v₀ − φ·v₁` (the stable
coordinate), where `φ = λ − 1 = (1+√5)/2` is the golden ratio (`phiAW`).  Under one step of the
real matrix action they scale multiplicatively, `pC (catℝ *ᵥ v) = λ·pC v` and
`qC (catℝ *ᵥ v) = μ·qC v`, and since `λ = φ²`, `μ = φ⁻²` all the interval arithmetic closes in the
golden field `ℚ[φ]`.

## Main results

* `ErgodicTheory.CatMapToral.phiAW` — the golden ratio `φ = λ − 1`, with `phiAW_sq : φ² = φ + 1`.
* `ErgodicTheory.CatMapToral.pC`, `qC` — the unstable/stable eigen-coordinates and their
  multiplicativity `pC_mulVec`, `qC_mulVec`.
* `ErgodicTheory.CatMapToral.awBox` — the two golden rectangles `R₁, R₂`.
* `ErgodicTheory.CatMapToral.branchBox` — the five affine branches, with
  `branchBox_subset_awBox_src` (each branch sits inside its source rectangle).
* `ErgodicTheory.CatMapToral.branch_step` — the **keystone**: `catℝ *ᵥ v − offset` lands in the
  target rectangle for every point of a branch.
* `ErgodicTheory.CatMapToral.catProj_injOn_branchBox` — the covering projection is injective on each
  branch (a golden-lattice exclusion argument).
* `ErgodicTheory.CatMapToral.awCell`, `awCell_image_step` — the six partition cells on `T2` and the
  set-level image-step `catTorus '' cell(e) ⊆ catProj '' targetRectangle`.
-/

open Matrix

noncomputable section

namespace ErgodicTheory.CatMapToral

/-! ## The golden ratio `φ = λ − 1` -/

/-- The golden ratio `φ = λ − 1 = (1+√5)/2`, the aspect constant of the Adler–Weiss rectangles. -/
def phiAW : ℝ := lam - 1

/-- The defining golden identity `φ² = φ + 1`. -/
lemma phiAW_sq : phiAW ^ 2 = phiAW + 1 := by
  unfold phiAW; have := lam_sq; nlinarith [this]

/-- `φ = (1+√5)/2`. -/
lemma phiAW_val : phiAW = (1 + Real.sqrt 5) / 2 := by unfold phiAW lam; ring

/-- `1 < φ`. -/
lemma one_lt_phiAW : 1 < phiAW := by
  unfold phiAW; have := two_lt_sqrt5; unfold lam; linarith

/-- `φ < 2`. -/
lemma phiAW_lt_two : phiAW < 2 := by
  unfold phiAW; have := sqrt5_lt_three; unfold lam; linarith

/-- `0 < φ`. -/
lemma phiAW_pos : 0 < phiAW := by linarith [one_lt_phiAW]

/-- `λ = φ + 1` (`= φ²`). -/
lemma lam_eq : lam = phiAW + 1 := by unfold phiAW; ring

/-- `μ = 2 − φ` (`= φ⁻²`). -/
lemma mu_eq : mu = 2 - phiAW := by unfold phiAW lam mu; ring

/-! ## The unstable/stable eigen-coordinates

(`lam_pos : 0 < lam` is proved once in `ErgodicTheory.Examples.CatMapOrbit`.) -/

/-- The **unstable (expanding) coordinate** `pC v = φ·v₀ + v₁`. -/
def pC (v : Fin 2 → ℝ) : ℝ := phiAW * v 0 + v 1

/-- The **stable (contracting) coordinate** `qC v = v₀ − φ·v₁`. -/
def qC (v : Fin 2 → ℝ) : ℝ := v 0 - phiAW * v 1

/-- `pC` is additive on differences. -/
lemma pC_sub (u w : Fin 2 → ℝ) : pC (u - w) = pC u - pC w := by
  simp only [pC, Pi.sub_apply]; ring

/-- `qC` is additive on differences. -/
lemma qC_sub (u w : Fin 2 → ℝ) : qC (u - w) = qC u - qC w := by
  simp only [qC, Pi.sub_apply]; ring

/-- Value of `pC` on an explicit pair `![a, b]`. -/
lemma pC_cons (a b : ℝ) : pC ![a, b] = phiAW * a + b := by
  simp only [pC, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Value of `qC` on an explicit pair `![a, b]`. -/
lemma qC_cons (a b : ℝ) : qC ![a, b] = a - phiAW * b := by
  simp only [qC, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Unstable multiplicativity:** `pC (catℝ *ᵥ v) = λ·pC v`.  One step of the dynamics expands the
unstable coordinate by `λ`. -/
lemma pC_mulVec (v : Fin 2 → ℝ) : pC (catℝ *ᵥ v) = lam * pC v := by
  rw [catℝ_mulVec_apply]
  simp only [pC, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [lam_eq]; linear_combination (-(v 0)) * phiAW_sq

/-- **Stable multiplicativity:** `qC (catℝ *ᵥ v) = μ·qC v`.  One step of the dynamics contracts the
stable coordinate by `μ`. -/
lemma qC_mulVec (v : Fin 2 → ℝ) : qC (catℝ *ᵥ v) = mu * qC v := by
  rw [catℝ_mulVec_apply]
  simp only [qC, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mu_eq]; linear_combination (-(v 1)) * phiAW_sq

/-! ## The two golden rectangles and the five branches -/

/-- The two Adler–Weiss rectangles in eigen-coordinates: `R₁` (index `0`) is `[0,φ)×[0,φ)` and
`R₂` (index `1`) is `[φ,φ²)×[0,1)`. -/
def awBox : Fin 2 → Set (Fin 2 → ℝ)
  | 0 => {v | pC v ∈ Set.Ico 0 phiAW ∧ qC v ∈ Set.Ico 0 phiAW}
  | 1 => {v | pC v ∈ Set.Ico phiAW (phiAW ^ 2) ∧ qC v ∈ Set.Ico 0 1}

/-- The stable height of each rectangle: `φ` for `R₁`, `1` for `R₂`. -/
def qHeight : Fin 2 → ℝ
  | 0 => phiAW
  | 1 => 1

/-- Source rectangle of each of the five branches: `R₁,R₁,R₁,R₂,R₂`. -/
def src : Fin 5 → Fin 2 := ![0, 0, 0, 1, 1]

/-- Target rectangle of each branch: `R₁,R₂,R₁,R₂,R₁`. -/
def tgt : Fin 5 → Fin 2 := ![0, 1, 0, 1, 0]

/-- Left endpoint of each branch's unstable window. -/
def pa : Fin 5 → ℝ := ![0, phiAW - 1, 1, phiAW, 2]

/-- Right endpoint of each branch's unstable window. -/
def pb : Fin 5 → ℝ := ![phiAW - 1, 1, phiAW, 2, phiAW ^ 2]

/-- Integer translation subtracted after applying `catℝ` on each branch. -/
def off : Fin 5 → (Fin 2 → ℝ) := ![![0, 0], ![0, 0], ![1, 1], ![1, 1], ![2, 2]]

/-- The `e`-th affine branch: the sub-rectangle of the source box whose unstable coordinate lies in
the window `[pa e, pb e)` and whose stable coordinate fills the full height. -/
def branchBox (e : Fin 5) : Set (Fin 2 → ℝ) :=
  {v | pC v ∈ Set.Ico (pa e) (pb e) ∧ qC v ∈ Set.Ico 0 (qHeight (src e))}

/-- Each branch sits inside its source rectangle: the five unstable windows partition the source
box's unstable interval and the heights agree. -/
lemma branchBox_subset_awBox_src (e : Fin 5) : branchBox e ⊆ awBox (src e) := by
  intro v hv
  obtain ⟨hpv, hqv⟩ := hv
  rw [Set.mem_Ico] at hpv hqv
  obtain ⟨hp0, hp1⟩ := hpv
  obtain ⟨hq0, hq1⟩ := hqv
  fin_cases e <;>
    norm_num [src, pa, pb, qHeight, awBox, Set.mem_setOf_eq, Set.mem_Ico] at hp0 hp1 hq0 hq1 ⊢ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    nlinarith [hp0, hp1, hq0, hq1, phiAW_sq, phiAW_pos, phiAW_lt_two, one_lt_phiAW, phiAW_val,
      two_lt_sqrt5]

/-! ## The keystone: one step maps each branch onto its target rectangle -/

set_option maxHeartbeats 400000 in
-- The five golden-field interval computations (one per branch) exhaust the default budget.
/-- **Keystone identity.**  For every point `v` of the `e`-th branch, one step of the real dynamics
followed by the integer translation, `catℝ *ᵥ v − off e`, lands in the target rectangle
`awBox (tgt e)`.  Each of the five branches is a short interval computation in the golden field:
`pC` expands by `λ = φ²` and `qC` contracts by `μ = φ⁻²`, and the affine windows were chosen so the
image intervals reassemble exactly into the target box. -/
theorem branch_step (e : Fin 5) {v : Fin 2 → ℝ} (hv : v ∈ branchBox e) :
    catℝ *ᵥ v - off e ∈ awBox (tgt e) := by
  obtain ⟨hpv, hqv⟩ := hv
  rw [Set.mem_Ico] at hpv hqv
  obtain ⟨hp0, hp1⟩ := hpv
  obtain ⟨hq0, hq1⟩ := hqv
  have hpw : pC (catℝ *ᵥ v - off e) = lam * pC v - pC (off e) := by rw [pC_sub, pC_mulVec]
  have hqw : qC (catℝ *ᵥ v - off e) = mu * qC v - qC (off e) := by rw [qC_sub, qC_mulVec]
  have hlp0 := mul_le_mul_of_nonneg_left hp0 lam_pos.le
  have hlp1 := mul_lt_mul_of_pos_left hp1 lam_pos
  have hmq0 := mul_le_mul_of_nonneg_left hq0 mu_pos.le
  have hmq1 := mul_lt_mul_of_pos_left hq1 mu_pos
  fin_cases e <;>
  · norm_num [tgt, awBox, Set.mem_setOf_eq, Set.mem_Ico] at hpw hqw ⊢
    rw [hpw, hqw]
    norm_num [off, pa, pb, src, qHeight, pC_cons, qC_cons, lam_eq, mu_eq] at *
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    nlinarith [hp0, hp1, hq0, hq1, hlp0, hlp1, hmq0, hmq1, phiAW_sq, phiAW_pos, phiAW_lt_two,
      one_lt_phiAW]

/-! ## Injectivity of the covering projection on each branch -/

/-- Each branch's unstable window is narrower than `φ − 1`. -/
lemma pWidth_le (e : Fin 5) : pb e - pa e ≤ phiAW - 1 := by
  fin_cases e <;>
    norm_num [pa, pb] <;>
    nlinarith [phiAW_sq, phiAW_val, two_lt_sqrt5, sqrt5_lt_three]

/-- Each branch's stable height is at most `φ`. -/
lemma qHeight_src_le (e : Fin 5) : qHeight (src e) ≤ phiAW := by
  fin_cases e <;>
    norm_num [src, qHeight] <;>
    linarith [one_lt_phiAW]

/-- `awBox 0` and `awBox 1` are the two pieces of the union `R₁ ∪ R₂`. -/
lemma awBox_subset_awUnion (b : Fin 2) : awBox b ⊆ awBox 0 ∪ awBox 1 := by
  fin_cases b
  · exact Set.subset_union_left
  · exact Set.subset_union_right

set_option maxHeartbeats 1600000 in
-- The final exclusion runs `nlinarith` across `4 regions × 9 lattice candidates`.
/-- **Injectivity on the fundamental domain.**  The covering projection `catProj` is injective on
`R₁ ∪ R₂ = awBox 0 ∪ awBox 1`.  Two points with equal projection differ by an integer vector
`(m,n)`; the golden identity `(φ+2)m = φ(φm+n) + (m−φn)` bounds `|m|,|n| < 2`, and the eight nonzero
lattice candidates each violate a strict half-open endpoint of one of the two rectangles. -/
theorem catProj_injOn_awUnion : Set.InjOn catProj (awBox 0 ∪ awBox 1) := by
  intro x hx y hy hxy
  have hpos := phiAW_pos
  have ho := one_lt_phiAW
  have ht := phiAW_lt_two
  have hsq := phiAW_sq
  -- The difference has integer coordinates `(m,n)`.
  have hcoe : ∀ i, ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
    intro i
    have h := congrFun hxy i
    simp only [catProj] at h
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).mp (hcoe 0)
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp (hcoe 1)
  rw [zsmul_eq_mul, mul_one] at hm hn
  have hpd : phiAW * (m : ℝ) + (n : ℝ) = pC x - pC y := by rw [hm, hn]; simp only [pC]; ring
  have hqd : (m : ℝ) - phiAW * (n : ℝ) = qC x - qC y := by rw [hm, hn]; simp only [qC]; ring
  have hid : (phiAW + 2) * (m : ℝ)
      = phiAW * (phiAW * (m : ℝ) + (n : ℝ)) + ((m : ℝ) - phiAW * (n : ℝ)) := by
    linear_combination (-(m : ℝ)) * phiAW_sq
  have hidn : (phiAW + 2) * (n : ℝ)
      = (phiAW * (m : ℝ) + (n : ℝ)) - phiAW * ((m : ℝ) - phiAW * (n : ℝ)) := by
    linear_combination -(n : ℝ) * phiAW_sq
  -- Loose bounds valid throughout `R₁ ∪ R₂`.
  have hloose : ∀ z ∈ awBox 0 ∪ awBox 1,
      0 ≤ pC z ∧ pC z < phiAW + 1 ∧ 0 ≤ qC z ∧ qC z < phiAW := by
    rintro z (hz | hz) <;>
      simp only [awBox, Set.mem_setOf_eq, Set.mem_Ico] at hz <;>
      obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hz <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [hsq, ho, ht, hpos, ha, hb, hc, hd]
  obtain ⟨hxp0, hxp1, hxq0, hxq1⟩ := hloose x hx
  obtain ⟨hyp0, hyp1, hyq0, hyq1⟩ := hloose y hy
  rw [hpd, hqd] at hid hidn
  -- `|m| < 2` and `|n| < 2` from the loose bounds and the golden identities (linear once the
  -- `φ`-scaled products are supplied explicitly).
  have key_m : (phiAW + 2) * (m : ℝ) = phiAW * pC x - phiAW * pC y + (qC x - qC y) := by
    rw [hid]; ring
  have key_n : (phiAW + 2) * (n : ℝ)
      = pC x - pC y - (phiAW * qC x - phiAW * qC y) := by
    rw [hidn]; ring
  have hax : phiAW * pC x ≤ phiAW * (phiAW + 1) := mul_le_mul_of_nonneg_left hxp1.le hpos.le
  have hay : phiAW * pC y ≤ phiAW * (phiAW + 1) := mul_le_mul_of_nonneg_left hyp1.le hpos.le
  have hax0 : 0 ≤ phiAW * pC x := mul_nonneg hpos.le hxp0
  have hay0 : 0 ≤ phiAW * pC y := mul_nonneg hpos.le hyp0
  have hcx : phiAW * qC x ≤ phiAW * phiAW := mul_le_mul_of_nonneg_left hxq1.le hpos.le
  have hcy : phiAW * qC y ≤ phiAW * phiAW := mul_le_mul_of_nonneg_left hyq1.le hpos.le
  have hcx0 : 0 ≤ phiAW * qC x := mul_nonneg hpos.le hxq0
  have hcy0 : 0 ≤ phiAW * qC y := mul_nonneg hpos.le hyq0
  have hmi : m < 2 ∧ (-2 : ℤ) < m := by
    have hr : (m : ℝ) < 2 ∧ (-2 : ℝ) < (m : ℝ) :=
      ⟨by nlinarith [key_m, hax, hay0, hxq1, hyq0, hsq, ht, hpos],
       by nlinarith [key_m, hax0, hay, hxq0, hyq1, hsq, ht, hpos]⟩
    exact_mod_cast hr
  have hni : n < 2 ∧ (-2 : ℤ) < n := by
    have hr : (n : ℝ) < 2 ∧ (-2 : ℝ) < (n : ℝ) :=
      ⟨by nlinarith [key_n, hxp1, hyp0, hcx0, hcy, hsq, ht, hpos],
       by nlinarith [key_n, hxp0, hyp1, hcx, hcy0, hsq, ht, hpos]⟩
    exact_mod_cast hr
  obtain ⟨hmu, hml⟩ := hmi
  obtain ⟨hnu, hnl⟩ := hni
  -- Reduce to `m = 0 ∧ n = 0`.
  suffices hmn : m = 0 ∧ n = 0 by
    obtain ⟨hm0, hn0⟩ := hmn
    rw [hm0] at hm; rw [hn0] at hn
    push_cast at hm hn
    funext i
    fin_cases i
    · change x 0 = y 0; linarith
    · change x 1 = y 1; linarith
  -- Region-specific tight bounds exclude the eight nonzero lattice candidates.
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    (simp only [awBox, Set.mem_setOf_eq, Set.mem_Ico] at hx hy;
     obtain ⟨⟨hxp0', hxp1'⟩, hxq0', hxq1'⟩ := hx;
     obtain ⟨⟨hyp0', hyp1'⟩, hyq0', hyq1'⟩ := hy;
     interval_cases m <;> interval_cases n <;>
       first
       | exact ⟨rfl, rfl⟩
       | (exfalso; push_cast at hpd hqd; ring_nf at hpd hqd;
          linarith [hpd, hqd, hxp0', hxp1', hxq0', hxq1', hyp0', hyp1', hyq0', hyq1', hsq]))

/-- **Injectivity on branches.**  The covering projection `catProj` is injective on each branch
`branchBox e`.  The branch sits inside its source rectangle, which is one of the two pieces of the
fundamental domain `R₁ ∪ R₂`; injectivity therefore restricts from `catProj_injOn_awUnion`. -/
theorem catProj_injOn_branchBox (e : Fin 5) : Set.InjOn catProj (branchBox e) :=
  catProj_injOn_awUnion.mono ((branchBox_subset_awBox_src e).trans (awBox_subset_awUnion (src e)))

/-! ## The six partition cells on the torus and the image-step -/

/-- The six Adler–Weiss cells on `T2`: cell `0` is the (measure-zero) junk complement of the images
of the five branches; cell `e+1` is the projected `e`-th branch. -/
def awCell : Fin 6 → Set T2 :=
  Fin.cases ((⋃ e, catProj '' branchBox e)ᶜ) (fun e => catProj '' branchBox e)

/-- The junk cell is the complement of the union of the projected branches. -/
lemma awCell_zero : awCell 0 = (⋃ e, catProj '' branchBox e)ᶜ := rfl

/-- Cell `e+1` is the projected `e`-th branch. -/
lemma awCell_succ (e : Fin 5) : awCell e.succ = catProj '' branchBox e := rfl

/-- The integer translation of each branch is invisible to the covering projection. -/
lemma catProj_off (e : Fin 5) : catProj (off e) = 0 := by
  have h1 : ((1 : ℝ) : UnitAddCircle) = 0 := by exact_mod_cast coe_intCast_eq_zero 1
  have h2 : ((2 : ℝ) : UnitAddCircle) = 0 := by exact_mod_cast coe_intCast_eq_zero 2
  funext i
  fin_cases e <;> fin_cases i <;>
    norm_num [catProj, off, Pi.zero_apply, AddCircle.coe_zero, h1, h2]

/-- **Image-step.**  One step of the cat map carries the projected `e`-th branch into the projected
target rectangle: `catTorus '' (awCell (e+1)) ⊆ catProj '' (awBox (tgt e))`.  This is the keystone
`branch_step` pushed down through the covering projection, the integer translation being killed by
`catProj`. -/
theorem awCell_image_step (e : Fin 5) :
    catTorus '' awCell e.succ ⊆ catProj '' awBox (tgt e) := by
  rw [awCell_succ]
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  refine ⟨catℝ *ᵥ v - off e, branch_step e hv, ?_⟩
  rw [catProj_sub, catProj_off, sub_zero, catProj_mulVec]

end ErgodicTheory.CatMapToral

end
