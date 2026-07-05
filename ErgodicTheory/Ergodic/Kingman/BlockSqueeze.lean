/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Ergodic.Kingman.Companion

/-!
# The M-block subsequence squeeze and additive assembly

The `M`-block subsequence squeeze of the `EReal` `limsup`/`liminf` envelopes and the additive
assembly via the `T^[M]`-Birkhoff average, combining the non-positive companion estimates back into
a statement about the original cocycle.

Internal infrastructure for Kingman's theorem (the `ErgodicTheory.Kingman` namespace); the public
statement is in `ErgodicTheory.Ergodic.Kingman.Core`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ErgodicTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-! ### The `M`-block subsequence squeeze

For a non-positive subadditive cocycle and `M ≥ 1`, the full `EReal` `limsup`/`liminf` of the
normalized cocycle equal the `limsup`/`liminf` along the `M`-subsequence
`k ↦ g (k*M) x / (k*M)`. The hard direction (`full ≤ subseq`) combines the pointwise
`block_sandwich` with the `c ≤ 1` ratio squeeze (`ereal_ratio_le_limsup`/`_liminf`); the easy
direction is `Tendsto.limsup_comp_le_limsup` along `Tendsto (·*M) atTop atTop`. -/

/-- The raw normalized cocycle `↑(g j x / j)` (with `g 0 x / 0 = 0`), indexed so that
`ecdiv g n x = usub g x (n+1)`. -/
noncomputable def usub (g : ℕ → X → ℝ) (x : X) (j : ℕ) : EReal :=
  ((g j x / j : ℝ) : EReal)

omit [MeasurableSpace X] in
/-- `(fun n => ecdiv g n x) = fun n => usub g x (n+1)`. -/
theorem ecdiv_eq_usub_succ (g : ℕ → X → ℝ) (x : X) :
    (fun n => ecdiv g n x) = fun n => usub g x (n + 1) := by
  funext n
  simp only [ecdiv, cdiv, usub]
  norm_num

omit [MeasurableSpace X] in
/-- `limsup_n (ecdiv g n x) = limsup_j (usub g x j)`. -/
theorem limsup_ecdiv_eq_usub (g : ℕ → X → ℝ) (x : X) :
    Filter.limsup (fun n => ecdiv g n x) atTop
      = Filter.limsup (fun j => usub g x j) atTop := by
  rw [ecdiv_eq_usub_succ]
  exact Filter.limsup_nat_add (fun j => usub g x j) 1

omit [MeasurableSpace X] in
/-- `liminf_n (ecdiv g n x) = liminf_j (usub g x j)`. -/
theorem liminf_ecdiv_eq_usub (g : ℕ → X → ℝ) (x : X) :
    Filter.liminf (fun n => ecdiv g n x) atTop
      = Filter.liminf (fun j => usub g x j) atTop := by
  rw [ecdiv_eq_usub_succ]
  exact Filter.liminf_nat_add (fun j => usub g x j) 1

omit [MeasurableSpace X] in
/-- `Tendsto (·*M) atTop atTop` for `M ≥ 1`. -/
theorem tendsto_mul_const_atTop_nat {M : ℕ} (hM : 1 ≤ M) :
    Tendsto (fun k : ℕ => k * M) atTop atTop :=
  tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right k hM) tendsto_id

omit [MeasurableSpace X] in
/-- `Tendsto (·/M) atTop atTop` for `M ≥ 1`. -/
theorem tendsto_div_const_atTop_nat {M : ℕ} (hM : 1 ≤ M) :
    Tendsto (fun j : ℕ => j / M) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b * M, fun j hj => ?_⟩
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact le_trans (by rw [mul_comm]) hj

omit [MeasurableSpace X] in
/-- Strict block upper bound: `j < (j/M + 1) * M` for `M ≥ 1`. -/
theorem lt_div_add_one_mul {M : ℕ} (hM : 1 ≤ M) (j : ℕ) : j < (j / M + 1) * M := by
  have h1 := Nat.div_add_mod j M
  have h2 := Nat.mod_lt j (show 0 < M by omega)
  nlinarith [h1, h2]

omit [MeasurableSpace X] in
/-- **Block subsequence squeeze (`limsup`).** For `M ≥ 1`, the full `limsup` of `ecdiv g`
equals the `limsup` along the `M`-block subsequence `k ↦ usub g x (k*M)`. -/
theorem limsup_ecdiv_eq_block {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) {M : ℕ} (hM : 1 ≤ M) (x : X) :
    Filter.limsup (fun n => ecdiv g n x) atTop
      = Filter.limsup (fun k => usub g x (k * M)) atTop := by
  rw [limsup_ecdiv_eq_usub]
  apply le_antisymm
  · -- `full ≤ subseq` via block_sandwich + the `c ≤ 1` ratio squeeze.
    -- `c j := (j/M)*M / j ≤ 1`, `z j := usub g x ((j/M)*M)`.
    set c : ℕ → ℝ := fun j => (((j / M) * M : ℕ) : ℝ) / (j : ℝ) with hcdef
    set z : ℕ → ℝ := fun j => g ((j / M) * M) x / (((j / M) * M : ℕ) : ℝ) with hzdef
    have hnp : ∀ i, 1 ≤ i → g i x ≤ 0 := by
      intro i hi; obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩; exact hnonpos p x
    -- `z j ≤ 0` for `j ≥ M` (so `j/M ≥ 1`, hence `(j/M)*M ≥ M ≥ 1`).
    have hzle : ∀ j, z j ≤ 0 := by
      intro j
      simp only [hzdef]
      rcases Nat.eq_zero_or_pos (j / M) with h0 | hpos
      · simp [h0]
      · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        exact hnp _ (by
          have : 1 ≤ j / M := hpos
          nlinarith [Nat.one_le_iff_ne_zero.2 (by omega : M ≠ 0)])
    have hc1 : ∀ j, c j ≤ 1 := by
      intro j
      simp only [hcdef]
      rcases Nat.eq_zero_or_pos j with h0 | hjpos
      · simp [h0]
      · rw [div_le_one (by positivity)]
        exact_mod_cast Nat.div_mul_le_self j M
    -- `c j → 1`.
    have hctend : Tendsto c atTop (𝓝 1) := by
      -- squeeze: `(j/M)/((j/M)+1) ≤ c j ≤ 1`, and `j/M → ∞`.
      have hkdiv : Tendsto (fun j : ℕ => j / M) atTop atTop := tendsto_div_const_atTop_nat hM
      have hlow : Tendsto (fun j : ℕ ↦ ((j / M : ℕ) : ℝ) / (((j / M : ℕ) : ℝ) + 1)) atTop
          (𝓝 1) := by
        have hform : (fun j : ℕ => ((j / M : ℕ) : ℝ) / (((j / M : ℕ) : ℝ) + 1))
            = (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1)) ∘ (fun j => j / M) := rfl
        rw [hform]
        have hbase : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 1) := by
          have hform2 : (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1))
              = fun k : ℕ => 1 - ((k : ℝ) + 1)⁻¹ := by
            funext k; have : ((k : ℝ) + 1) ≠ 0 := by positivity
            field_simp; ring
          rw [hform2]
          have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp
              (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
          simpa using tendsto_const_nhds.sub hinv
        exact hbase.comp hkdiv
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ hc1
      intro j
      simp only [hcdef]
      rcases Nat.eq_zero_or_pos j with h0 | hjpos
      · simp [h0]
      · have hjbound : j < (j / M + 1) * M := lt_div_add_one_mul hM j
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        have h1 : ((j / M : ℕ) : ℝ) * (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.div_mul_le_self j M
        have h2 : (j : ℝ) < (((j / M : ℕ) : ℝ) + 1) * (M : ℝ) := by exact_mod_cast hjbound
        nlinarith [Nat.cast_nonneg (α := ℝ) (j / M), (by positivity : (0:ℝ) < (M:ℝ)),
          (Nat.cast_pos (α := ℝ)).2 hjpos]
    -- chain.
    calc Filter.limsup (fun j => usub g x j) atTop
        ≤ Filter.limsup (fun j => ((c j * z j : ℝ) : EReal)) atTop := by
          refine Filter.limsup_le_limsup ?_ (Filter.isCobounded_le_of_bot)
            (Filter.isBounded_le_of_top)
          filter_upwards [eventually_ge_atTop M] with j hj
          have hjpos : 0 < j := by omega
          have hkpos : 1 ≤ j / M := by rw [Nat.le_div_iff_mul_le (by omega)]; omega
          have hsand := (block_sandwich hsub hnonpos M (j / M) j
            (Nat.div_mul_le_self j M) (le_of_lt (lt_div_add_one_mul hM j)) x).2
          simp only [usub]
          refine EReal.coe_le_coe_iff.2 ?_
          have hcz : c j * z j = g ((j / M) * M) x / (j : ℝ) := by
            simp only [hcdef, hzdef]
            have hden : (((j / M) * M : ℕ) : ℝ) ≠ 0 := by
              have : 1 ≤ (j / M) * M := by nlinarith [hkpos, hM]
              positivity
            field_simp
          rw [hcz]
          exact div_le_div_of_nonneg_right hsand (by positivity) |>.trans_eq (by ring)
      _ ≤ Filter.limsup (fun j => ((z j : ℝ) : EReal)) atTop :=
          ereal_ratio_le_limsup hzle hctend
      _ ≤ Filter.limsup (fun k => usub g x (k * M)) atTop := by
          have hkdiv : Tendsto (fun j : ℕ => j / M) atTop atTop := tendsto_div_const_atTop_nat hM
          have hzeq : (fun j => ((z j : ℝ) : EReal))
              = (fun k => usub g x (k * M)) ∘ (fun j => j / M) := by
            funext j; simp only [hzdef, usub, Function.comp]
          rw [hzeq]
          exact hkdiv.limsup_comp_le_limsup
  · -- `subseq ≤ full`.
    have hmul : Tendsto (fun k : ℕ => k * M) atTop atTop := tendsto_mul_const_atTop_nat hM
    exact hmul.limsup_comp_le_limsup (u := fun j => usub g x j)
      (Filter.isCobounded_le_of_bot) (Filter.isBounded_le_of_top)

omit [MeasurableSpace X] in
/-- **Block subsequence squeeze (`liminf`).** For `M ≥ 1`, the full `liminf` of `ecdiv g`
equals the `liminf` along the `M`-block subsequence `k ↦ usub g x (k*M)`. -/
theorem liminf_ecdiv_eq_block {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) {M : ℕ} (hM : 1 ≤ M) (x : X) :
    Filter.liminf (fun n => ecdiv g n x) atTop
      = Filter.liminf (fun k => usub g x (k * M)) atTop := by
  rw [liminf_ecdiv_eq_usub]
  apply le_antisymm
  · -- `full ≤ subseq` (easy): `liminf` along the subsequence `(·*M)`.
    have hmul : Tendsto (fun k : ℕ => k * M) atTop atTop := tendsto_mul_const_atTop_nat hM
    exact hmul.liminf_le_liminf_comp (u := fun j => usub g x j)
      (Filter.isCobounded_ge_of_top) (Filter.isBounded_ge_of_bot)
  · -- `subseq ≤ full` (hard): lower sandwich `g ((k+1)M) x ≤ g j x` + the `c ≥ 1` ratio squeeze.
    set c' : ℕ → ℝ := fun j => if j = 0 then 1 else (((j / M + 1) * M : ℕ) : ℝ) / (j : ℝ)
      with hc'def
    set w' : ℕ → ℝ := fun j => g ((j / M + 1) * M) x / (((j / M + 1) * M : ℕ) : ℝ) with hw'def
    have hMpos : 0 < M := by omega
    have hblkpos : ∀ j, 1 ≤ (j / M + 1) * M := fun j =>
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.succ_ne_zero _) hMpos.ne')
    have hw'le : ∀ j, w' j ≤ 0 := by
      intro j
      simp only [hw'def]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      obtain ⟨p, hp⟩ : ∃ p, (j / M + 1) * M = p + 1 :=
        ⟨(j / M + 1) * M - 1, by have := hblkpos j; omega⟩
      rw [hp]; exact hnonpos p x
    have hc'1 : ∀ j, 1 ≤ c' j := by
      intro j
      simp only [hc'def]
      rcases Nat.eq_zero_or_pos j with h0 | hjpos
      · simp [h0]
      · rw [if_neg (by omega), le_div_iff₀ (by positivity)]
        have := lt_div_add_one_mul hM j
        push_cast
        rw [one_mul]
        exact_mod_cast this.le
    have hc'tend : Tendsto c' atTop (𝓝 1) := by
      -- `1 ≤ c' j ≤ ((j/M)+1)/(j/M)` (for `j ≥ M`), and `j/M → ∞`.
      have hkdiv : Tendsto (fun j : ℕ => j / M) atTop atTop := tendsto_div_const_atTop_nat hM
      have hupp : Tendsto (fun j : ℕ ↦ (((j / M : ℕ) : ℝ) + 1) / ((j / M : ℕ) : ℝ)) atTop
          (𝓝 1) := by
        have hform : (fun j : ℕ => (((j / M : ℕ) : ℝ) + 1) / ((j / M : ℕ) : ℝ))
            = (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) ∘ (fun j => j / M) := rfl
        rw [hform]
        have hbase : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 1) := by
          have heq : (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ))
              =ᶠ[atTop] fun k : ℕ => 1 + (k : ℝ)⁻¹ := by
            filter_upwards [eventually_gt_atTop 0] with k hk
            have hk0 : (k : ℝ) ≠ 0 := by positivity
            field_simp
          rw [tendsto_congr' heq]
          have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
          simpa using tendsto_const_nhds.add hinv
        exact hbase.comp hkdiv
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupp
        (Eventually.of_forall hc'1) ?_
      filter_upwards [eventually_ge_atTop M] with j hj
      have hjpos : 0 < j := by omega
      simp only [hc'def, if_neg (show j ≠ 0 by omega)]
      have hkpos : 1 ≤ j / M := by rw [Nat.le_div_iff_mul_le (by omega)]; omega
      have hjbd : ((j / M : ℕ) : ℝ) * (M : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self j M
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      have hkpos' : (1 : ℝ) ≤ ((j / M : ℕ) : ℝ) := by exact_mod_cast hkpos
      nlinarith [hjbd, (by positivity : (0:ℝ) < (M:ℝ)), hkpos',
        (Nat.cast_pos (α := ℝ)).2 hjpos]
    -- `liminf(subseq) ≤ liminf ↑w' ≤ liminf ↑(c'·w') ≤ liminf(full)`.
    calc Filter.liminf (fun k => usub g x (k * M)) atTop
        ≤ Filter.liminf (fun j => ((w' j : ℝ) : EReal)) atTop := by
          have hφ : Tendsto (fun j : ℕ => j / M + 1) atTop atTop :=
            tendsto_atTop_mono (fun j => Nat.le_succ _) (tendsto_div_const_atTop_nat hM)
          have hweq : (fun k => usub g x (k * M)) ∘ (fun j => j / M + 1)
              = (fun j => ((w' j : ℝ) : EReal)) := by
            funext j; simp only [hw'def, usub, Function.comp]
          have hstep := hφ.liminf_le_liminf_comp (u := fun k => usub g x (k * M))
            (Filter.isCobounded_ge_of_top) (Filter.isBounded_ge_of_bot)
          rw [hweq] at hstep
          exact hstep
      _ ≤ Filter.liminf (fun j => ((c' j * w' j : ℝ) : EReal)) atTop :=
          ereal_liminf_le_ratio hw'le hc'tend
      _ ≤ Filter.liminf (fun j => usub g x j) atTop := by
          refine Filter.liminf_le_liminf ?_ (Filter.isBounded_ge_of_bot)
            (Filter.isCobounded_ge_of_top)
          filter_upwards [eventually_ge_atTop M] with j hj
          have hjpos : 0 < j := by omega
          have hsand := (block_sandwich hsub hnonpos M (j / M) j
            (Nat.div_mul_le_self j M) (le_of_lt (lt_div_add_one_mul hM j)) x).1
          simp only [usub]
          refine EReal.coe_le_coe_iff.2 ?_
          have hcw : c' j * w' j = g ((j / M + 1) * M) x / (j : ℝ) := by
            simp only [hc'def, hw'def, if_neg (show j ≠ 0 by omega)]
            have hden : (((j / M + 1) * M : ℕ) : ℝ) ≠ 0 := by
              have := hblkpos j
              positivity
            field_simp
          rw [hcw]
          exact div_le_div_of_nonneg_right hsand (by positivity) |>.trans_eq (by ring)

/-! ### Additive assembly via the `T^[M]`-Birkhoff average

The `M`-block subsequence value decomposes pointwise (for `n ≥ 1`) as
`g (n*M) x / (n*M) = (1/M)·(vM g M n x / n) + (1/M)·birkhoffAverage (T^[M]) (g M) n x`,
where the Birkhoff average converges a.e. to the finite `μ[g M | invariants (T^[M])] x`.
Feeding this into the `EReal` additive/scaling laws gives the envelopes of the block subsequence
as `(1/M)·(envelope of usub (vM g M)) + ↑((1/M)·c x)`. -/

omit [MeasurableSpace X] in
/-- The **block decomposition identity** (pointwise, `n ≥ 1`):
`g (n*M) x / (n*M) = (1/M)·(vM g M n x / n) + (1/M)·birkhoffAverage (T^[M]) (g M) n x`. -/
theorem block_decomp {g : ℕ → X → ℝ} {M : ℕ} (hM : 1 ≤ M) (n : ℕ) (hn : 1 ≤ n) (x : X) :
    g (n * M) x / ((n * M : ℕ) : ℝ)
      = (1 / (M : ℝ)) * (vM (T := T) g M n x / (n : ℝ))
        + (1 / (M : ℝ)) * birkhoffAverage ℝ (T^[M]) (g M) n x := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- `∑_{i<n} g M (T^[i*M] x) = n · birkhoffAverage`.
  have hsumeq : ∑ i ∈ Finset.range n, g M (T^[i * M] x)
      = ∑ i ∈ Finset.range n, g M ((T^[M])^[i] x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    rw [← Function.iterate_mul]; congr 1; ring
  have hsum : ∑ i ∈ Finset.range n, g M (T^[i * M] x)
      = (n : ℝ) * birkhoffAverage ℝ (T^[M]) (g M) n x := by
    rw [hsumeq, birkhoffAverage, birkhoffSum, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hnpos), one_mul]
  -- `g (n*M) x = vM g M n x + ∑`.
  have hvM : g (n * M) x = vM (T := T) g M n x + ∑ i ∈ Finset.range n, g M (T^[i * M] x) := by
    simp only [vM]; ring
  rw [hvM, hsum]
  push_cast
  field_simp

omit [MeasurableSpace X] in
/-- `usub (vM g M) x n = vM g M n x / n` (the normalized companion subsequence). -/
theorem usub_vM (g : ℕ → X → ℝ) (M : ℕ) (x : X) (n : ℕ) :
    usub (vM (T := T) g M) x n = ((vM (T := T) g M n x / (n : ℝ) : ℝ) : EReal) := rfl

omit [MeasurableSpace X] in
/-- **Block-envelope assembly (`limsup`).** A.e. (where the `T^[M]`-Birkhoff average of
`g M` converges to `c x`),
`limsup_k (usub g x (k*M)) = ↑(1/M)·limsup_n (usub (vM g M) x n) + ↑((1/M)·c x)`. -/
theorem limsup_block_eq {g : ℕ → X → ℝ} {M : ℕ} (hM : 1 ≤ M) (x : X) {c : ℝ}
    (hc : Tendsto (fun n => birkhoffAverage ℝ (T^[M]) (g M) n x) atTop (𝓝 c)) :
    Filter.limsup (fun k => usub g x (k * M)) atTop
      = ((1 / (M : ℝ) : ℝ) : EReal) * Filter.limsup (fun n => usub (vM (T := T) g M) x n) atTop
        + (((1 / (M : ℝ)) * c : ℝ) : EReal) := by
  set b : ℕ → ℝ := fun n => (1 / (M : ℝ)) * (vM (T := T) g M n x / (n : ℝ)) with hbdef
  set s : ℕ → ℝ := fun n => (1 / (M : ℝ)) * birkhoffAverage ℝ (T^[M]) (g M) n x with hsdef
  -- Eventually `usub g x (k*M) = ↑(b k + s k)`.
  have hev : (fun k => usub g x (k * M)) =ᶠ[atTop] fun k => ((b k + s k : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp only [usub, hbdef, hsdef]
    rw [block_decomp (T := T) hM k hk x]
  rw [Filter.limsup_congr hev]
  -- `s n → (1/M)·c`.
  have hstend : Tendsto s atTop (𝓝 ((1 / (M : ℝ)) * c)) := by
    simp only [hsdef]; exact hc.const_mul _
  rw [ereal_limsup_add_tendsto hstend]
  -- `limsup ↑(b n) = ↑(1/M)·limsup ↑(vM/n)`.
  have hbeq : Filter.limsup (fun n => ((b n : ℝ) : EReal)) atTop
      = ((1 / (M : ℝ) : ℝ) : EReal)
        * Filter.limsup (fun n ↦ usub (vM (T := T) g M) x n) atTop := by
    simp only [hbdef]
    rw [ereal_limsup_const_mul (by positivity)]
    rfl
  rw [hbeq]

omit [MeasurableSpace X] in
/-- **Block-envelope assembly (`liminf`).** A.e.,
`liminf_k (usub g x (k*M)) = ↑(1/M)·liminf_n (usub (vM g M) x n) + ↑((1/M)·c x)`. -/
theorem liminf_block_eq {g : ℕ → X → ℝ} {M : ℕ} (hM : 1 ≤ M) (x : X) {c : ℝ}
    (hc : Tendsto (fun n => birkhoffAverage ℝ (T^[M]) (g M) n x) atTop (𝓝 c)) :
    Filter.liminf (fun k => usub g x (k * M)) atTop
      = ((1 / (M : ℝ) : ℝ) : EReal) * Filter.liminf (fun n => usub (vM (T := T) g M) x n) atTop
        + (((1 / (M : ℝ)) * c : ℝ) : EReal) := by
  set b : ℕ → ℝ := fun n => (1 / (M : ℝ)) * (vM (T := T) g M n x / (n : ℝ)) with hbdef
  set s : ℕ → ℝ := fun n => (1 / (M : ℝ)) * birkhoffAverage ℝ (T^[M]) (g M) n x with hsdef
  have hev : (fun k => usub g x (k * M)) =ᶠ[atTop] fun k => ((b k + s k : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp only [usub, hbdef, hsdef]
    rw [block_decomp (T := T) hM k hk x]
  rw [Filter.liminf_congr hev]
  have hstend : Tendsto s atTop (𝓝 ((1 / (M : ℝ)) * c)) := by
    simp only [hsdef]; exact hc.const_mul _
  rw [ereal_liminf_add_tendsto hstend]
  have hbeq : Filter.liminf (fun n => ((b n : ℝ) : EReal)) atTop
      = ((1 / (M : ℝ) : ℝ) : EReal)
        * Filter.liminf (fun n ↦ usub (vM (T := T) g M) x n) atTop := by
    simp only [hbdef]
    rw [ereal_liminf_const_mul (by positivity)]
    rfl
  rw [hbeq]

/-- **Gap algebra.** From the block-envelope identities, the strict gap on `E` forces the
companion `liminf` strictly below `↑(−M·α)`. For `r > 0`, finite `c`, `α > 0`, and `Lp ≤ 0`,
if `↑r·Lm + ↑c + ↑α < ↑r·Lp + ↑c` then `Lm < ↑(−α/r)`. -/
theorem ereal_gap_to_liminf {r c α : ℝ} (hr : 0 < r) (_hα : 0 < α) {Lm Lp : EReal}
    (hLp : Lp ≤ 0) (h : (r : EReal) * Lm + (c : EReal) + (α : EReal)
      < (r : EReal) * Lp + (c : EReal)) : Lm < ((-α / r : ℝ) : EReal) := by
  -- `↑r·Lp ≤ 0`.
  have hrLp : (r : EReal) * Lp ≤ 0 := by
    calc (r : EReal) * Lp ≤ (r : EReal) * 0 :=
          mul_le_mul_of_nonneg_left hLp (le_of_lt (EReal.coe_pos.2 hr))
      _ = 0 := by rw [mul_zero]
  -- iso `· + ↑c` reflects order.
  have hisoc : ∀ a b : EReal, a + (c : EReal) < b + (c : EReal) ↔ a < b := by
    intro a b
    have h := (erealAddCoeIso c).lt_iff_lt (x := a) (y := b)
    simpa only [erealAddCoeIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk] using h
  -- RHS `↑r·Lp + ↑c ≤ ↑c`, hence `↑r·Lm + ↑α + ↑c < ↑c`.
  have hrhs : (r : EReal) * Lp + (c : EReal) ≤ (c : EReal) := by
    have : (r : EReal) * Lp + (c : EReal) ≤ (0 : EReal) + (c : EReal) := by
      have hh := (erealAddCoeIso c).le_iff_le (x := (r : EReal) * Lp) (y := (0 : EReal))
      simpa only [erealAddCoeIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk] using hh.2 hrLp
    rwa [zero_add] at this
  have h2 : (r : EReal) * Lm + (α : EReal) + (c : EReal) < (c : EReal) := by
    have heq : (r : EReal) * Lm + (α : EReal) + (c : EReal)
        = (r : EReal) * Lm + (c : EReal) + (α : EReal) := by
      rw [add_right_comm]
    rw [heq]; exact lt_of_lt_of_le h hrhs
  -- cancel `↑c`.
  have h3 : (r : EReal) * Lm + (α : EReal) < 0 := by
    have := (hisoc ((r : EReal) * Lm + (α : EReal)) 0).1
    rw [zero_add] at this
    exact this h2
  -- subtract `↑α`: `↑r·Lm < ↑(−α)`.
  have h5 : (r : EReal) * Lm < ((-α : ℝ) : EReal) := by
    have hisoα : ∀ a b : EReal, a + (α : EReal) < b + (α : EReal) ↔ a < b := by
      intro a b
      have hh := (erealAddCoeIso α).lt_iff_lt (x := a) (y := b)
      simpa only [erealAddCoeIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk] using hh
    have hgoal : (r : EReal) * Lm + (α : EReal) < ((-α : ℝ) : EReal) + (α : EReal) := by
      rw [← EReal.coe_add, neg_add_cancel, EReal.coe_zero]
      exact h3
    exact (hisoα _ _).1 hgoal
  -- divide by `↑r`.
  rw [EReal.coe_div, EReal.lt_div_iff (EReal.coe_pos.2 hr) (EReal.coe_ne_top r), mul_comm]
  exact h5

/-- **The `E_α` contradiction** (Karlsson §3.3). For a non-positive subadditive cocycle
and any `α > 0`, the gap set `Bα := {x | liminf (ecdiv g · x) + ↑α < limsup (ecdiv g · x)}` is
null. The argument:

* Extract a genuinely `T`-invariant measurable `E =ᵐ Bα` (both envelopes are a.e. `T`-invariant,
  `liminf_ecdiv_comp_ae` / `limsup_ecdiv_comp_ae`); then `(T^[M])⁻¹ E = E` for every `M`.
* Fix `ε > 0`; pick `M ≥ 1` with `(∫ g M)/M ≤ Λ + ε` (Fekete). On `E`, the block squeeze
  (`limsup_ecdiv_eq_block` / `liminf_ecdiv_eq_block`) and the assembly (`limsup_block_eq` /
  `liminf_block_eq`) reduce the `g`-gap to the companion `usub (vM g M)` envelopes; the strict
  gap and `limsup (usub (vM g M)) ≤ 0` force `liminf_n (vM g M n x / n) < ↑(−M·α)`
  (`ereal_gap_to_liminf`), hence `∃ k, vM g M (k+1) x < (k+1)·(−M·α)` (the `hBneg` input).
* `setIntegral_div_le_level` over `T^[M]` gives
  `limsup_n ↑((∫_E vM g M (n+1))/(n+1)) ≤ ↑((−Mα)·(μ E).toReal)`, while the `X`-integral ratio
  `(∫_X vM g M (n+1))/(n+1) → M·Λ − ∫ g M ≥ −Mε` and `vM ≤ 0` (so `∫_E ≥ ∫_X`) give the matching
  lower bound `↑(−Mε)`. Hence `α·(μ E).toReal ≤ ε`; letting `ε → 0` forces `μ E = 0 = μ Bα`. -/
theorem measure_gap_set_eq_zero [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) {Λ : ℝ}
    (hΛ : Tendsto (fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1)) atTop (𝓝 Λ))
    {α : ℝ} (hα : 0 < α) :
    μ {x | Filter.liminf (fun n => ecdiv g n x) atTop + (α : EReal)
      < Filter.limsup (fun n => ecdiv g n x) atTop} = 0 := by
  classical
  set Bα : Set X := {x | Filter.liminf (fun n => ecdiv g n x) atTop + (α : EReal)
    < Filter.limsup (fun n => ecdiv g n x) atTop} with hBαdef
  -- `Bα` is null-measurable and a.e. `T`-invariant; extract a genuinely invariant `E =ᵐ Bα`.
  have hBαnull : NullMeasurableSet Bα μ := by
    have h1 := aemeasurable_ereal_liminf (μ := μ) hint
    have h2 := aemeasurable_ereal_limsup (μ := μ) hint
    exact nullMeasurableSet_lt (h1.add_const _) h2
  have hBαinv : T ⁻¹' Bα =ᵐ[μ] Bα := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [liminf_ecdiv_comp_ae hT hsub hint hnonpos,
      limsup_ecdiv_comp_ae hT hsub hint hnonpos] with x hLx hUx
    simp only [Function.comp] at hLx hUx
    simp only [Set.mem_preimage, hBαdef, Set.mem_setOf_eq, hLx, hUx]
  obtain ⟨E, hEm, hEeq, hEinv⟩ :=
    hT.quasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hBαnull hBαinv
  have hμEB : μ E = μ Bα := measure_congr hEeq
  rw [← hμEB]
  -- `T^[M]`-invariance of `E`.
  have hEinvM : ∀ M : ℕ, (T^[M]) ⁻¹' E = E := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Function.iterate_succ, Set.preimage_comp, ih, hEinv]
  -- Birkhoff convergence of `g M` along `T^[M]`, finite limit `cM x`.
  set I : ∀ M : ℕ, MeasurableSpace X := fun M => MeasurableSpace.invariants (T^[M]) with hIdef
  have hbirk : ∀ M : ℕ, ∀ᵐ x ∂μ, Tendsto
      (fun n => birkhoffAverage ℝ (T^[M]) (g M) n x) atTop
      (𝓝 ((μ[g M | MeasurableSpace.invariants (T^[M])]) x)) :=
    fun M => tendsto_birkhoffAverage_ae (vM_measurePreserving hT M) (hint M)
  -- `(μ E).toReal`.
  set m : ℝ := (μ E).toReal with hmdef
  have hmnn : 0 ≤ m := ENNReal.toReal_nonneg
  -- The key bound: for every `ε > 0`, `α · m ≤ ε`.
  have hkey : ∀ ε : ℝ, 0 < ε → α * m ≤ ε := by
    intro ε hε
    -- Choose `M ≥ 1` with `(∫ g M)/M ≤ Λ + ε`.
    have hMexists : ∃ M : ℕ, 1 ≤ M ∧ (∫ x, g M x ∂μ) / (M : ℝ) ≤ Λ + ε := by
      have := (hΛ.eventually (eventually_lt_nhds (show Λ < Λ + ε by linarith))).exists
      obtain ⟨m₀, hm₀⟩ := this
      exact ⟨m₀ + 1, by omega, by
        have : (∫ x, g (m₀ + 1) x ∂μ) / ((m₀ : ℝ) + 1) ≤ Λ + ε := le_of_lt hm₀
        rwa [show ((m₀ + 1 : ℕ) : ℝ) = (m₀ : ℝ) + 1 by push_cast; ring]⟩
    obtain ⟨M, hM1, hMle⟩ := hMexists
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    -- `hBneg` for `setIntegral_div_le_level`: on `E`, `∃ k, vM g M (k+1) x < (k+1)·(−Mα)`.
    have hBneg : ∀ᵐ x ∂μ, x ∈ E →
        ∃ k, vM (T := T) g M (k + 1) x < (k + 1 : ℝ) * (-(M : ℝ) * α) := by
      filter_upwards [hbirk M, Filter.eventuallyEq_set.1 hEeq] with x hxbirk hxmem
      intro hxE
      -- Block envelopes via the squeeze and assembly identities.
      set cM : ℝ := (μ[g M | MeasurableSpace.invariants (T^[M])]) x with hcMdef
      have hLU : Filter.liminf (fun n => ecdiv g n x) atTop + (α : EReal)
          < Filter.limsup (fun n => ecdiv g n x) atTop := by
        have : x ∈ Bα := hxmem.1 hxE
        simpa only [hBαdef, Set.mem_setOf_eq] using this
      rw [limsup_ecdiv_eq_block hsub hnonpos hM1 x,
        liminf_ecdiv_eq_block hsub hnonpos hM1 x,
        limsup_block_eq (T := T) hM1 x hxbirk, liminf_block_eq (T := T) hM1 x hxbirk] at hLU
      -- Companion envelopes `L⁻ ≤ L⁺ ≤ 0`.
      set Lm : EReal := Filter.liminf (fun n => usub (vM (T := T) g M) x n) atTop with hLmdef
      set Lp : EReal := Filter.limsup (fun n => usub (vM (T := T) g M) x n) atTop with hLpdef
      have husubnp : ∀ n, usub (vM (T := T) g M) x n ≤ ((0 : ℝ) : EReal) := by
        intro n
        rw [usub_vM]
        refine EReal.coe_le_coe_iff.2 ?_
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · simp [h0]
        · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
          exact vM_nonpos hsub M n hpos x
      have hLp0 : Lp ≤ 0 := by
        rw [hLpdef]
        have hmono : Filter.limsup (fun n => usub (vM (T := T) g M) x n) atTop
            ≤ Filter.limsup (fun _ : ℕ => ((0 : ℝ) : EReal)) atTop :=
          Filter.limsup_le_limsup (Eventually.of_forall husubnp)
            (by isBoundedDefault) (by isBoundedDefault)
        refine hmono.trans ?_
        simp [Filter.limsup_const]
      -- Apply the gap-algebra lemma with `r = 1/M`, `c = (1/M)·cM`.
      have hgap := ereal_gap_to_liminf (r := 1 / (M : ℝ)) (c := (1 / (M : ℝ)) * cM)
        (α := α) (by positivity) hα hLp0 hLU
      -- `−α / (1/M) = −Mα`.
      have hrw : ((-α / (1 / (M : ℝ)) : ℝ) : EReal) = (((-(M : ℝ)) * α : ℝ) : EReal) := by
        congr 1
        rw [div_div_eq_mul_div, div_one]
        ring
      rw [hrw] at hgap
      -- `liminf (usub vM) < ↑(−Mα)` ⟹ frequently a real term below ⟹ pick `n ≥ 1`.
      have hfreq : ∃ᶠ n in atTop, usub (vM (T := T) g M) x n < (((-(M : ℝ)) * α : ℝ) : EReal) :=
        Filter.frequently_lt_of_liminf_lt (Filter.isCobounded_ge_of_top) hgap
      obtain ⟨n, hn1, hnlt⟩ := ((hfreq.and_eventually (eventually_ge_atTop 1)).exists)
      refine ⟨n - 1, ?_⟩
      have hn1' : 1 ≤ n := hnlt
      rw [show n - 1 + 1 = n by omega]
      rw [usub_vM] at hn1
      have hncast : ((n : ℝ)) ≠ 0 := by positivity
      have : vM (T := T) g M n x / (n : ℝ) < (-(M : ℝ)) * α := by
        exact_mod_cast hn1
      rw [show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by
        rw [Nat.cast_sub hn1']; push_cast; ring]
      rw [div_lt_iff₀ (by positivity)] at this
      linarith [this]
    -- The `β`-maximal inequality (Prop 3.5): `limsup ↑((∫_E vM(n+1))/(n+1)) ≤ ↑((−Mα)·m)`.
    have hUpper := setIntegral_div_le_level (vM_measurePreserving hT M)
      (vM_subadditive hsub M) (vM_integrable hT hint M) hEm (hEinvM M) (-(M : ℝ) * α) hBneg
    -- Lower bound: `(∫_X vM(n+1))/(n+1) → M·Λ − ∫ g M ≥ −Mε`, and `∫_E ≥ ∫_X` (since `vM ≤ 0`).
    have hlower_tendsto : Tendsto (fun n : ℕ => (∫ x, vM (T := T) g M (n + 1) x ∂μ) / (n + 1))
        atTop (𝓝 ((M : ℝ) * Λ - ∫ x, g M x ∂μ)) := by
      -- `(∫ vM(n+1))/(n+1) = M·(∫ g((n+1)M))/((n+1)M) − ∫ g M`.
      have hform : ∀ n : ℕ, (∫ x, vM (T := T) g M (n + 1) x ∂μ) / ((n : ℝ) + 1)
          = (M : ℝ) * ((∫ x, g ((n + 1) * M) x ∂μ) / (((n + 1) * M : ℕ) : ℝ)) - ∫ x, g M x ∂μ := by
        intro n
        rw [integral_vM hT hint M (n + 1)]
        have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMpos
        have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp
      rw [tendsto_congr hform]
      -- `(∫ g((n+1)M))/((n+1)M) → Λ` (Fekete subsequence).
      have hsubseq : Tendsto (fun n : ℕ => (∫ x, g ((n + 1) * M) x ∂μ) / (((n + 1) * M : ℕ) : ℝ))
          atTop (𝓝 Λ) := by
        have hcomp : (fun n : ℕ => (∫ x, g ((n + 1) * M) x ∂μ) / (((n + 1) * M : ℕ) : ℝ))
            = (fun k : ℕ ↦ (∫ x, g (k + 1) x ∂μ) / ((k : ℝ) + 1))
              ∘ (fun n ↦ (n + 1) * M - 1) := by
          funext n
          simp only [Function.comp]
          rw [show (n + 1) * M - 1 + 1 = (n + 1) * M by
            have : 1 ≤ (n + 1) * M := by nlinarith [hM1]
            omega]
          congr 1
          rw [Nat.cast_sub (by nlinarith [hM1] : 1 ≤ (n + 1) * M)]
          push_cast; ring
        rw [hcomp]
        refine hΛ.comp ?_
        apply tendsto_atTop_mono (fun n => ?_) tendsto_id
        have h1 : n + 1 ≤ (n + 1) * M := Nat.le_mul_of_pos_right _ (by omega)
        change n ≤ (n + 1) * M - 1
        omega
      have := (hsubseq.const_mul (M : ℝ)).sub_const (∫ x, g M x ∂μ)
      convert this using 2
    have hlower_lim : (M : ℝ) * Λ - ∫ x, g M x ∂μ ≥ -((M : ℝ) * ε) := by
      have : (∫ x, g M x ∂μ) ≤ (M : ℝ) * (Λ + ε) := by
        rw [div_le_iff₀ hMpos] at hMle; linarith [hMle]
      nlinarith [this]
    -- `∫_E vM(n+1) ≥ ∫_X vM(n+1)` (since `vM ≤ 0` and `E ⊆ univ`).
    have hsetint_ge : ∀ n : ℕ, (∫ x, vM (T := T) g M (n + 1) x ∂μ)
        ≤ ∫ x in E, vM (T := T) g M (n + 1) x ∂μ := by
      intro n
      have hvMnp : ∀ x, vM (T := T) g M (n + 1) x ≤ 0 :=
        fun x ↦ vM_nonpos hsub M (n + 1) (by omega) x
      have hintEc : Integrable (vM (T := T) g M (n + 1)) (μ.restrict Eᶜ) :=
        (vM_integrable hT hint M (n + 1)).restrict
      have hsplit : ∫ x, vM (T := T) g M (n + 1) x ∂μ
          = (∫ x in E, vM (T := T) g M (n + 1) x ∂μ) + ∫ x in Eᶜ, vM (T := T) g M (n + 1) x ∂μ :=
        (integral_add_compl hEm (vM_integrable hT hint M (n + 1))).symm
      have hEcle : ∫ x in Eᶜ, vM (T := T) g M (n + 1) x ∂μ ≤ 0 :=
        integral_nonpos (fun x => hvMnp x)
      rw [hsplit]; linarith
    -- Combine into an `EReal` `limsup` lower bound `≥ ↑(−Mε)`.
    have hlimsup_ge : ((-(M : ℝ) * ε : ℝ) : EReal)
        ≤ Filter.limsup (fun n : ℕ =>
          (((∫ x in E, vM (T := T) g M (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop := by
      -- `liminf ↑((∫_X)/(n+1)) = ↑(MΛ − ∫gM)` (convergent).
      have hXtend : Tendsto (fun n : ℕ =>
          (((∫ x, vM (T := T) g M (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop
          (𝓝 (((M : ℝ) * Λ - ∫ x, g M x ∂μ : ℝ) : EReal)) := by
        refine (continuous_coe_real_ereal.tendsto _).comp ?_
        have := hlower_tendsto
        simpa only [Nat.cast_add, Nat.cast_one] using this
      have hXliminf : Filter.liminf (fun n : ℕ =>
          (((∫ x, vM (T := T) g M (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop
          = (((M : ℝ) * Λ - ∫ x, g M x ∂μ : ℝ) : EReal) := hXtend.liminf_eq
      -- `liminf ↑((∫_X)/(n+1)) ≤ liminf ↑((∫_E)/(n+1)) ≤ limsup ↑((∫_E)/(n+1))`.
      have hmono : Filter.liminf (fun n : ℕ =>
          (((∫ x, vM (T := T) g M (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop
          ≤ Filter.liminf (fun n : ℕ =>
          (((∫ x in E, vM (T := T) g M (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop := by
        refine Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)
          (by isBoundedDefault) (by isBoundedDefault)
        exact EReal.coe_le_coe_iff.2
          (div_le_div_of_nonneg_right (hsetint_ge n) (by positivity))
      have hLELS : Filter.liminf (fun n : ℕ =>
          (((∫ x in E, vM (T := T) g M (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop
          ≤ Filter.limsup (fun n : ℕ =>
          (((∫ x in E, vM (T := T) g M (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop :=
        Filter.liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
      calc ((-(M : ℝ) * ε : ℝ) : EReal)
          ≤ (((M : ℝ) * Λ - ∫ x, g M x ∂μ : ℝ) : EReal) :=
            EReal.coe_le_coe_iff.2 (by linarith [hlower_lim])
        _ = _ := hXliminf.symm
        _ ≤ _ := hmono
        _ ≤ _ := hLELS
    -- `↑(−Mε) ≤ limsup(∫_E …) ≤ ↑((−Mα)·m)`, hence `α·m ≤ ε`.
    have hchain : ((-(M : ℝ) * ε : ℝ) : EReal) ≤ ((((-(M : ℝ)) * α) * m : ℝ) : EReal) :=
      le_trans hlimsup_ge hUpper
    have hreal : -(M : ℝ) * ε ≤ ((-(M : ℝ)) * α) * m := by exact_mod_cast hchain
    nlinarith [hreal, hMpos]
  -- Let `ε → 0`: `α·m ≤ 0`, so `m = 0`, so `μ E = 0`.
  have hαm0 : α * m ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    have := hkey (α * m / 2) (by linarith)
    linarith
  have hm0 : m = 0 := le_antisymm (by nlinarith [hmnn, hα]) hmnn
  -- `μ E = 0` from `(μ E).toReal = 0` and finiteness.
  rwa [hmdef, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top μ E)] at hm0

/-- **Stopping-time direction (the hard core of Kingman), non-positive case.** A.e. the `EReal`
`liminf` of the normalized non-positive subadditive cocycle equals its `EReal` `limsup`.

The unconditional `liminf ≤ limsup` reduces this to `μ {liminf < limsup} = 0`, and that bad set is
the countable union over `ℚ⁺` of the gap sets `Bα`, each null by `measure_gap_set_eq_zero`
(Karlsson §3.3, the `E_α` contradiction). -/
theorem ae_ereal_liminf_eq_limsup_nonpos [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.liminf (fun n => ecdiv g n x) atTop
      = Filter.limsup (fun n => ecdiv g n x) atTop := by
  classical
  -- Fekete constant `Λ`.
  obtain ⟨Λ, hΛ⟩ := exists_fekete hT hsub hint hbdd
  -- The gap set for `α > 0` has measure zero (the `E_α` contradiction).
  have hgap : ∀ α : ℝ, 0 < α →
      μ {x | Filter.liminf (fun n => ecdiv g n x) atTop + (α : EReal)
        < Filter.limsup (fun n => ecdiv g n x) atTop} = 0 :=
    fun α hα => measure_gap_set_eq_zero hT hsub hint hnonpos hΛ hα
  -- The bad set `{liminf < limsup}` is a countable union of null gap sets over `ℚ⁺`.
  set L : X → EReal := fun x => Filter.liminf (fun n => ecdiv g n x) atTop with hLdef
  set U : X → EReal := fun x => Filter.limsup (fun n => ecdiv g n x) atTop with hUdef
  have hmem : ∀ x, L x < U x → ∃ q : ℚ, 0 < q ∧ L x + ((q : ℝ) : EReal) < U x := by
    intro x hx
    rcases eq_or_ne (L x) ⊥ with hLbot | hLbot
    · -- `L x = ⊥`: `⊥ + ↑1 = ⊥ < U x`.
      refine ⟨1, by norm_num, ?_⟩
      rw [hLbot, EReal.bot_add]
      rw [hLbot] at hx; exact hx
    · -- `L x` finite: `L x < ↑c < U x`; pick rational `q ∈ (0, c − a)`.
      have hLtop : L x ≠ ⊤ := by
        intro htop; rw [htop] at hx; exact absurd hx (not_top_lt)
      obtain ⟨c, hc1, hc2⟩ := EReal.exists_rat_btwn_of_lt hx
      set a : ℝ := (L x).toReal with hadef
      have ha : ((a : ℝ) : EReal) = L x := EReal.coe_toReal hLtop hLbot
      have hac : a < (c : ℝ) := by
        have : ((a : ℝ) : EReal) < ((c : ℝ) : EReal) := by rw [ha]; exact hc1
        exact_mod_cast this
      obtain ⟨q, hq0, hqlt⟩ := exists_rat_btwn (sub_pos.2 hac)
      refine ⟨q, by exact_mod_cast hq0, ?_⟩
      have hstep : L x + ((q : ℝ) : EReal) < ((c : ℝ) : EReal) := by
        rw [← ha, ← EReal.coe_add]
        exact EReal.coe_lt_coe_iff.2 (by linarith)
      exact lt_trans hstep hc2
  -- The bad set is contained in the countable union over `ℚ⁺` of the (null) gap sets.
  have hbad : μ {x | L x < U x} = 0 := by
    have hsub_union : {x | L x < U x}
        ⊆ ⋃ q : {q : ℚ // 0 < q}, {x | L x + (((q : ℚ) : ℝ) : EReal) < U x} := by
      intro x hx
      obtain ⟨q, hq0, hqlt⟩ := hmem x hx
      exact Set.mem_iUnion.2 ⟨⟨q, hq0⟩, hqlt⟩
    refine measure_mono_null hsub_union ?_
    rw [measure_iUnion_null_iff]
    rintro ⟨q, hq0⟩
    exact hgap (q : ℝ) (by exact_mod_cast hq0)
  -- Conclude `liminf = limsup` a.e.: the bad set `{L ≠ U}` equals `{L < U}` (null).
  have hle : ∀ x, L x ≤ U x := fun x =>
    Filter.liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
  rw [ae_iff]
  have hset : {x | ¬ L x = U x} = {x | L x < U x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => lt_of_le_of_ne (hle x) h, fun h => ne_of_lt h⟩
  rw [hset]
  exact hbad

/-- **Stopping-time direction (the hard core of Kingman).** A.e. the `EReal` `liminf` of the
normalized cocycle equals its `EReal` `limsup`, proved by the Riesz/Derriennic "leaders" route
(Karlsson, *A proof of the subadditive ergodic theorem*).

Reduced here to the non-positive case `ae_ereal_liminf_eq_limsup_nonpos` applied to the
companion `vcoc g` (`vcoc_subadditive`, `vcoc_nonpos`, `vcoc_integrable`, `vcoc_bddBelow`): the
normalized gap `ecdiv g − ecdiv (vcoc g) = ↑(birkhoffAverage (g 1) (·+1))` converges a.e.
(Birkhoff) to the *finite* `μ[g 1 | invariants T]`, and adding an a.e.-convergent
finite-valued real sequence preserves the `liminf`/`limsup` (both become `e + ↑(limit)`).

Ingredients:
* `sum_leaders_nonpos` — Riesz's combinatorial leader lemma (Karlsson Lemma 3.2).
* `sum_leaders_cocycle_nonpos` / `sum_psiCoc_comp_nonpos` — pointwise leader inequality.
* `limsup_setIntegral_div_nonpos` — *Derriennic's maximal inequality* (Karlsson Lemma 3.4). -/
theorem ae_ereal_liminf_eq_limsup [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.liminf (fun n => ecdiv g n x) atTop
      = Filter.limsup (fun n => ecdiv g n x) atTop := by
  -- Non-positive companion `v := vcoc g` and its `liminf = limsup`.
  set v : ℕ → X → ℝ := vcoc (T := T) g with hvdef
  have hvsub : IsSubadditiveCocycle T v := vcoc_subadditive hsub
  have hvint : ∀ n, Integrable (v n) μ := fun n => vcoc_integrable hT hint n
  have hvnonpos : ∀ n x, v (n + 1) x ≤ 0 := fun n x => vcoc_nonpos hsub n x
  have hvbdd : BddBelow (Set.range fun n : ℕ => (∫ x, v (n + 1) x ∂μ) / (n + 1)) :=
    vcoc_bddBelow hT hint hbdd
  have hveq := ae_ereal_liminf_eq_limsup_nonpos hT hvsub hvint hvnonpos hvbdd
  -- Birkhoff: `birkhoffAverage (g 1) (·+1) x → B x := μ[g 1 | I] x` a.e. (reindexed).
  have hbirk : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop
      (𝓝 ((μ[g 1 | MeasurableSpace.invariants T]) x)) := by
    filter_upwards [tendsto_birkhoffAverage_ae hT (hint 1)] with x hx
    exact hx.comp (tendsto_add_atTop_nat 1)
  filter_upwards [hveq, hbirk] with x hxeq hxbirk
  -- Common EReal limit of `ecdiv v`.
  set e : EReal := Filter.limsup (fun n => ecdiv v n x) atTop with hedef
  have htend_v : Tendsto (fun n => ecdiv v n x) atTop (𝓝 e) :=
    tendsto_of_liminf_eq_limsup hxeq rfl
  -- `↑birkhoffAverage → ↑(B x)` in EReal.
  set c : ℝ := (μ[g 1 | MeasurableSpace.invariants T]) x with hcdef
  have htend_b : Tendsto (fun n : ℕ => ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal))
      atTop (𝓝 ((c : ℝ) : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hxbirk
  -- Sum tends to `e + ↑c` (addition by a finite EReal is continuous).
  have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (e, ((c : ℝ) : EReal)) :=
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot c)) (Or.inr (EReal.coe_ne_top c))
  have htend_g : Tendsto (fun n => ecdiv g n x) atTop (𝓝 (e + ((c : ℝ) : EReal))) := by
    have hsum : Tendsto
        (fun n ↦ (ecdiv v n x, ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal)))
        atTop (𝓝 (e, ((c : ℝ) : EReal))) := htend_v.prodMk_nhds htend_b
    have := hcont.tendsto.comp hsum
    refine this.congr (fun n => ?_)
    simp only [Function.comp]
    exact (ecdiv_eq_ecdiv_vcoc_add n x).symm
  rw [htend_g.liminf_eq, htend_g.limsup_eq]


end ErgodicTheory.Kingman
