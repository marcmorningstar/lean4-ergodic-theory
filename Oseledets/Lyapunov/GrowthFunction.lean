import Oseledets.Cocycle.Basic
import Oseledets.Cocycle.Norm
import Oseledets.Cocycle.FurstenbergKesten
import Oseledets.Ergodic.Birkhoff
import Oseledets.Lyapunov.Ultrametric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The upper Lyapunov growth function

This module (blueprint `lyapunov-to-target.md` §2, layers `L4.1`–`L4.2`) introduces the
**upper Lyapunov growth function**

`lambdaBar A T x v = limsup_n (1/n) · log ‖A⁽ⁿ⁾(x) · v‖`,

the per-vector growth rate of the linear cocycle `A` over `T`. Here `A⁽ⁿ⁾(x) · v` is the
action `Matrix.toEuclideanCLM (cocycle A T n x) v` of the cocycle iterate on the Euclidean
vector `v`.

The key structural facts proved here, feeding the ultrametric machinery of
`Oseledets.Lyapunov.Ultrametric`:

* `lambdaBar_smul` — `lambdaBar` is invariant under nonzero scaling of the vector
  (unconditional);
* `lambdaBar_equivariant` — `A`-equivariance `lambdaBar A T x v = lambdaBar A T (T x) (A x·v)`;
* `lambdaBar_mem_Icc` — finiteness: a.e. `x`, `lambdaBar A T x v` lies in a fixed interval
  `[lamBot, lamTop]` (the extremal Lyapunov exponents from Furstenberg–Kesten);
* `lambdaBar_add_le` / `isUltrametricGrowth_lambdaBar` — the non-Archimedean inequality and
  the packaged statement that a.e. `lambdaBar A T x` is an `IsUltrametricGrowth` function.

The non-Archimedean step (and the equivariance reindexing) needs the defining sequence
`(1/n)·log‖A⁽ⁿ⁾(x)·v‖` to be bounded; boundedness holds a.e. by the Furstenberg–Kesten
sandwich. Accordingly `lambdaBar_add_le` and `lambdaBar_equivariant` carry explicit
`IsBoundedUnder` hypotheses on that sequence, while the primary a.e. deliverable
`isUltrametricGrowth_lambdaBar` discharges them from the FK limits (via the private
`growthSeq_bounded`). `lambdaBar_smul` is fully unconditional (the perturbation `(1/n)·log|c|`
is uniformly bounded), proved through the robust helper `limsup_eq_of_tendsto_sub_zero`.

Reference: Oseledets MET, upper growth function, blueprint §2.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X} {d : ℕ}

/-- The image vector `A⁽ⁿ⁾(x) · v` of the cocycle action on `v`. -/
private noncomputable def cocycleVec (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v

/-- The defining sequence of `lambdaBar`: `(1/n)·log‖A⁽ⁿ⁾(x)·v‖`. -/
private noncomputable def growthSeq (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (v : EuclideanSpace ℝ (Fin d)) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖

/-- The **upper Lyapunov growth function**
`lambdaBar A T x v = limsup_n (1/n) log‖A⁽ⁿ⁾(x) v‖`. -/
noncomputable def lambdaBar (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ *
    Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖) atTop

theorem lambdaBar_eq_limsup_growthSeq (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    lambdaBar A T x v = Filter.limsup (growthSeq A T x v) atTop := rfl

/-! ### Nonzeroness and norm bridges -/

/-- If `det (cocycle) ≠ 0` and `v ≠ 0`, the image vector `A⁽ⁿ⁾(x)·v` is nonzero. -/
private theorem cocycleVec_ne_zero {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (n : ℕ) (x : X) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v ≠ 0 := by
  intro h
  -- `toEuclideanCLM` of an invertible matrix is injective (it is a ring iso composed with a
  -- linear equiv); we argue via the inverse.
  have hinv : Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ (Ne.isUnit (det_cocycle_ne_zero hA n x)), map_one,
      ContinuousLinearMap.one_apply]
  rw [h, map_zero] at hinv
  exact hv hinv.symm

/-! ### The per-`n` sandwich inequalities -/

/-- Upper bound on the defining sequence: `(1/n)log‖M·v‖ ≤ (1/n)log‖M‖ + (1/n)log‖v‖`. -/
private theorem growthSeq_le {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) [NeZero d] (x : X) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (n : ℕ) :
    growthSeq A T x v n ≤
      (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖ := by
  have hMpos : 0 < ‖cocycle A T n x‖ := norm_cocycle_pos hA n x
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hMvpos : 0 < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ :=
    norm_pos_iff.mpr (cocycleVec_ne_zero hA n x hv)
  have hle : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ ≤
      ‖cocycle A T n x‖ * ‖v‖ := by
    have := (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x)).le_opNorm v
    rwa [Matrix.l2_opNorm_toEuclideanCLM] at this
  have hlogle : Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ ≤
      Real.log ‖cocycle A T n x‖ + Real.log ‖v‖ := by
    rw [← Real.log_mul (ne_of_gt hMpos) (ne_of_gt hvpos)]
    exact Real.log_le_log hMvpos hle
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  calc growthSeq A T x v n
      = (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ := rfl
    _ ≤ (n : ℝ)⁻¹ * (Real.log ‖cocycle A T n x‖ + Real.log ‖v‖) := by
        exact mul_le_mul_of_nonneg_left hlogle hninv
    _ = (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖ := by ring

/-- Lower bound on the defining sequence:
`-(1/n)log‖M⁻¹‖ + (1/n)log‖v‖ ≤ (1/n)log‖M·v‖`. -/
private theorem le_growthSeq {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) [NeZero d] (x : X) {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (n : ℕ) :
    -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) + (n : ℝ)⁻¹ * Real.log ‖v‖ ≤
      growthSeq A T x v n := by
  have hMipos : 0 < ‖(cocycle A T n x)⁻¹‖ := norm_inv_cocycle_pos hA n x
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hMvpos : 0 < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ :=
    norm_pos_iff.mpr (cocycleVec_ne_zero hA n x hv)
  -- `v = M⁻¹·(M·v)`, so `‖v‖ ≤ ‖M⁻¹‖·‖M·v‖`.
  have hveq : Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ (Ne.isUnit (det_cocycle_ne_zero hA n x)), map_one,
      ContinuousLinearMap.one_apply]
  have hle : ‖v‖ ≤ ‖(cocycle A T n x)⁻¹‖ *
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ := by
    conv_lhs => rw [← hveq]
    have := (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x)⁻¹).le_opNorm
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v)
    rwa [Matrix.l2_opNorm_toEuclideanCLM] at this
  have hlogle : Real.log ‖v‖ ≤ Real.log ‖(cocycle A T n x)⁻¹‖ +
      Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ := by
    rw [← Real.log_mul (ne_of_gt hMipos) (ne_of_gt hMvpos)]
    exact Real.log_le_log hvpos hle
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hmul : (n : ℝ)⁻¹ * Real.log ‖v‖ ≤ (n : ℝ)⁻¹ *
      (Real.log ‖(cocycle A T n x)⁻¹‖ +
        Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖) :=
    mul_le_mul_of_nonneg_left hlogle hninv
  show -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) + (n : ℝ)⁻¹ * Real.log ‖v‖ ≤
    (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖
  nlinarith [hmul]

/-! ### Boundedness of the defining sequence (a.e., from Furstenberg–Kesten) -/

/-- If both Furstenberg–Kesten sequences converge at `x`, then for every `v ≠ 0` the
defining sequence `growthSeq A T x v` has range bounded above and below. -/
private theorem growthSeq_bounded {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) [NeZero d] (x : X) {lam₁ lamk' : ℝ}
    (htop : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖) atTop (𝓝 lam₁))
    (hbot : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) atTop
      (𝓝 lamk'))
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    IsBoundedUnder (· ≤ ·) atTop (growthSeq A T x v) ∧
      IsBoundedUnder (· ≥ ·) atTop (growthSeq A T x v) := by
  -- Upper bounding sequence `hi n = (1/n)log‖M‖ + (1/n)log‖v‖ → lam₁ + 0`.
  have hlogv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    simpa using this.mul_const (Real.log ‖v‖)
  have hhi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ +
      (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 (lam₁ + 0)) := htop.add hlogv
  have hlo : Tendsto (fun n : ℕ => -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) +
      (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 (-lamk' + 0)) := hbot.neg.add hlogv
  refine ⟨?_, ?_⟩
  · -- bounded above: `growthSeq ≤ hi`, `hi` convergent hence bounded above.
    refine IsBoundedUnder.mono_le hhi.isBoundedUnder_le ?_
    exact Eventually.of_forall fun n => growthSeq_le hA x hv n
  · -- bounded below: `lo ≤ growthSeq`, `lo` convergent hence bounded below.
    refine IsBoundedUnder.mono_ge hlo.isBoundedUnder_ge ?_
    exact Eventually.of_forall fun n => le_growthSeq hA x hv n

/-! ### A robust `limsup`-invariance helper

`limsup` (along `atTop` in `ℝ`) is unchanged when the sequence is perturbed by a term that
tends to `0`, **without** any boundedness hypothesis. The proof works directly on the
defining sets `{a | ∀ᶠ n, u n ≤ a}`: the vanishing perturbation makes these two sets have
equal `sInf` (handling the empty/unbounded "junk-value" cases uniformly). -/
private theorem limsup_eq_of_tendsto_sub_zero {u w : ℕ → ℝ}
    (h : Tendsto (fun n => u n - w n) atTop (𝓝 0)) :
    Filter.limsup u atTop = Filter.limsup w atTop := by
  -- It suffices to prove `≤`; the reverse follows by symmetry (`w - u → 0`).
  suffices key : ∀ p q : ℕ → ℝ, Tendsto (fun n => p n - q n) atTop (𝓝 0) →
      Filter.limsup p atTop ≤ Filter.limsup q atTop by
    refine le_antisymm (key u w h) (key w u ?_)
    have : (fun n => w n - u n) = fun n => -(u n - w n) := by funext n; ring
    rw [this]; simpa using h.neg
  intro p q hpq
  rw [Filter.limsup_eq, Filter.limsup_eq]
  -- `Sp = {a | ∀ᶠ p n ≤ a}`, `Sq = {a | ∀ᶠ q n ≤ a}`.
  set Sp := {a : ℝ | ∀ᶠ n in atTop, p n ≤ a} with hSp
  set Sq := {a : ℝ | ∀ᶠ n in atTop, q n ≤ a} with hSq
  -- Generic transfer between the two defining sets, in either direction.
  have htrans_gen : ∀ r s : ℕ → ℝ, Tendsto (fun n => r n - s n) atTop (𝓝 0) →
      ∀ a ∈ {b : ℝ | ∀ᶠ n in atTop, s n ≤ b}, ∀ ε : ℝ, 0 < ε →
        (a + ε) ∈ {b : ℝ | ∀ᶠ n in atTop, r n ≤ b} := by
    intro r s hrs a ha ε hε
    have hev : ∀ᶠ n in atTop, |r n - s n| < ε := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hrs ε hε
      filter_upwards [eventually_ge_atTop N] with n hn
      simpa [Real.dist_eq, sub_zero] using hN n hn
    simp only [Set.mem_setOf_eq]
    filter_upwards [ha, hev] with n hsn hdn
    have : r n - s n < ε := (abs_lt.mp hdn).2
    linarith
  -- `hqp : (fun n => q n - p n) → 0`, the reverse perturbation.
  have hqp : Tendsto (fun n => q n - p n) atTop (𝓝 0) := by
    have : (fun n => q n - p n) = fun n => -(p n - q n) := by funext n; ring
    rw [this]; simpa using hpq.neg
  -- Transfer instances.
  have htrans : ∀ a ∈ Sq, ∀ ε : ℝ, 0 < ε → a + ε ∈ Sp := htrans_gen p q hpq
  have htrans' : ∀ a ∈ Sp, ∀ ε : ℝ, 0 < ε → a + ε ∈ Sq := htrans_gen q p hqp
  rcases Sq.eq_empty_or_nonempty with hSqe | hSqne
  · -- `Sq` empty ⟹ `Sp` empty (else `htrans'` would populate `Sq`).
    have hSpe : Sp = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro b hb
      exact (Set.eq_empty_iff_forall_notMem.mp hSqe _) (htrans' b hb 1 one_pos)
    rw [hSpe, hSqe]
  · obtain ⟨a₀, ha₀⟩ := hSqne
    have hSpne : Sp.Nonempty := ⟨a₀ + 1, htrans a₀ ha₀ 1 one_pos⟩
    -- An up-set is bounded below iff it is not all of `ℝ`; the two sets are simultaneously so.
    by_cases hbddSq : BddBelow Sq
    · -- `Sp` is then bounded below too (otherwise `Sp = univ`, forcing `Sq = univ`).
      have hbddSp : BddBelow Sp := by
        by_contra hSpunb
        -- `Sp` unbounded below: for any `m`, some element `< m`; transfer to `Sq`.
        obtain ⟨L, hL⟩ := hbddSq
        rw [not_bddBelow_iff] at hSpunb
        obtain ⟨c, hcSp, hcL⟩ := hSpunb (L - 1)
        have : c + 1 ∈ Sq := htrans' c hcSp 1 one_pos
        have := hL this
        linarith
      -- `sInf Sp ≤ a` for every `a ∈ Sq` via `a + ε ∈ Sp`.
      apply le_csInf ⟨a₀, ha₀⟩
      intro a ha
      refine le_of_forall_pos_le_add fun ε hε => ?_
      exact csInf_le hbddSp (htrans a ha ε hε)
    · -- `Sq` unbounded below ⟹ `Sp` unbounded below ⟹ both `sInf = 0`.
      have hSpunb : ¬ BddBelow Sp := by
        intro hSpbdd
        apply hbddSq
        obtain ⟨L, hL⟩ := hSpbdd
        refine ⟨L - 1, fun a ha => ?_⟩
        have : a + 1 ∈ Sp := htrans a ha 1 one_pos
        have := hL this
        linarith
      rw [Real.sInf_of_not_bddBelow hSpunb, Real.sInf_of_not_bddBelow hbddSq]

/-! ### L4.2 scaling -/

/-- **L4.2 scaling.** `lambdaBar` is invariant under nonzero scaling of the vector. -/
theorem lambdaBar_smul (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    {c : ℝ} (hc : c ≠ 0) (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) :
    lambdaBar A T x (c • v) = lambdaBar A T x v := by
  -- The two defining sequences differ by `(1/n)·(log‖M(c•v)‖ - log‖Mv‖)`, which tends to `0`.
  refine limsup_eq_of_tendsto_sub_zero ?_
  -- Show the difference sequence tends to `0`: it is bounded by `(1/n)·|log|c|| → 0`.
  have hcb : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * abs (Real.log |c|)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    simpa using this.mul_const (abs (Real.log |c|))
  refine squeeze_zero_norm ?_ hcb
  intro n
  -- `‖M(c•v)‖ = |c| · ‖Mv‖` (CLM linearity + `norm_smul`).
  have hsmul : Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) (c • v)
      = c • Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v := map_smul _ _ _
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) (c • v)‖
      = |c| * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ := by
    rw [hsmul, norm_smul, Real.norm_eq_abs]
  -- The difference of the two `log` terms is `log|c|` (when `‖Mv‖ > 0`) or `0`.
  set s := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖ with hs
  have hsnn : 0 ≤ s := norm_nonneg _
  have hlogdiff : Real.log (|c| * s) - Real.log s = if s = 0 then 0 else Real.log |c| := by
    by_cases hs0 : s = 0
    · simp [hs0]
    · rw [Real.log_mul (by positivity) hs0, if_neg hs0]; ring
  have hbound : |Real.log (|c| * s) - Real.log s| ≤ abs (Real.log |c|) := by
    rw [hlogdiff]
    by_cases hs0 : s = 0 <;> simp [hs0, abs_nonneg]
  -- Assemble: difference of `growthSeq`s is `(1/n)·(that difference)`.
  show ‖(n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) (c • v)‖ -
    (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖‖ ≤
    (n : ℝ)⁻¹ * abs (Real.log |c|)
  rw [hnorm, ← hs, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-! ### L4.2 `A`-equivariance -/

/-- The `(n+1)`-th `growthSeq` term at `(x, v)` equals `(n+1)⁻¹ · log‖A⁽ⁿ⁾(Tx)·(A x·v)‖`:
the cocycle identity peels off the newest factor `A x`. -/
private theorem growthSeq_succ (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    growthSeq A T x v (n + 1) =
      ((n : ℝ) + 1)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n (T x))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v)‖ := by
  unfold growthSeq
  rw [cocycle_succ, map_mul]
  push_cast
  rfl

/-- **L4.2 `A`-equivariance.** `lambdaBar A T x v = lambdaBar A T (T x) (A x · v)`.

Boundedness of the target sequence `growthSeq A T (T x) (A x·v)` is required: the limsup of
the `(x,v)` sequence is the limsup of the same log-data scaled by `(n+1)⁻¹` instead of
`n⁻¹`, and the two scalings differ by `(1/(n+1) - 1/n)·log‖·‖ = -(n+1)⁻¹·(n⁻¹·log‖·‖)`,
which tends to `0` exactly because `n⁻¹·log‖·‖` is bounded. This boundedness holds a.e. by
Furstenberg–Kesten and is supplied from `growthSeq_bounded`. -/
theorem lambdaBar_equivariant (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (hA : (A x).det ≠ 0) (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0)
    (hbddA : IsBoundedUnder (· ≤ ·) atTop
      (growthSeq A T (T x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v)))
    (hbddB : IsBoundedUnder (· ≥ ·) atTop
      (growthSeq A T (T x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v))) :
    lambdaBar A T x v
      = lambdaBar A T (T x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v) := by
  set w := Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v with hw
  -- The shared log-data sequence, with `a n = n⁻¹·L n = growthSeq A T (Tx) w n`.
  set L : ℕ → ℝ := fun n =>
    Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n (T x)) w‖ with hL
  set a : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * L n with ha
  have haeq : a = growthSeq A T (T x) w := rfl
  -- `lambdaBar A T x v = limsup_n (n+1)⁻¹·L n` (reindex by `+1`).
  have hxshift : lambdaBar A T x v
      = Filter.limsup (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * L n) atTop := by
    rw [lambdaBar_eq_limsup_growthSeq, ← Filter.limsup_nat_add (growthSeq A T x v) 1]
    congr 1
    funext n
    rw [growthSeq_succ]
  -- `lambdaBar A T (Tx) w = limsup_n a n`.
  have htgt : lambdaBar A T (T x) w = Filter.limsup a atTop := by
    rw [lambdaBar_eq_limsup_growthSeq, haeq]
  rw [hxshift, htgt]
  -- `a` is bounded, hence `‖a‖` is bounded above.
  have habdd : IsBoundedUnder (· ≤ ·) atTop a := haeq ▸ hbddA
  have habdd' : IsBoundedUnder (· ≥ ·) atTop a := haeq ▸ hbddB
  have hnormbdd : IsBoundedUnder (· ≤ ·) atTop ((‖·‖) ∘ a) := by
    obtain ⟨U, hU⟩ := habdd
    obtain ⟨Lo, hLo⟩ := habdd'
    rw [eventually_map] at hU hLo
    refine ⟨max |U| |Lo|, ?_⟩
    rw [eventually_map]
    filter_upwards [hU, hLo] with n hUn hLon
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · calc -max |U| |Lo| ≤ -|Lo| := neg_le_neg (le_max_right _ _)
        _ ≤ Lo := neg_abs_le _
        _ ≤ a n := hLon
    · calc a n ≤ U := hUn
        _ ≤ |U| := le_abs_self _
        _ ≤ max |U| |Lo| := le_max_left _ _
  -- The difference `(n+1)⁻¹ L n - a n` equals `-(n+1)⁻¹ · a n` eventually (`n ≥ 1`), → 0.
  refine limsup_eq_of_tendsto_sub_zero ?_
  have hsucc : Tendsto (fun n : ℕ => -(((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := h1.inv_tendsto_atTop.neg
    simpa using this
  -- `a n * (-(n+1)⁻¹) → 0` since `‖a‖` bounded and `-(n+1)⁻¹ → 0`.
  have hprod : Tendsto (fun n : ℕ => a n * -(((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hnormbdd hsucc
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : 1 ≤ n := hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  simp only [ha]
  -- `(n+1)⁻¹ L n - n⁻¹ L n = -(n+1)⁻¹·(n⁻¹ L n)` ⟺ `((n+1)⁻¹ - n⁻¹)L n = -(n+1)⁻¹ n⁻¹ L n`.
  field_simp
  ring

/-! ### L4.1 finiteness (Furstenberg–Kesten sandwich) -/

/-- **L4.1 finiteness.** For a.e. `x`, every nonzero `v` has `lambdaBar A T x v` in a fixed
interval `[lamBot, lamTop]` whose endpoints are the extremal (bottom/top) Lyapunov
exponents from Furstenberg–Kesten. -/
theorem lambdaBar_mem_Icc
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ lamBot lamTop : ℝ, lamBot ≤ lamTop ∧ ∀ᵐ x ∂μ,
      ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 → lambdaBar A T x v ∈ Set.Icc lamBot lamTop := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: every `v = 0`, so the statement is vacuous.
    subst hd
    exact ⟨0, 0, le_refl _, Filter.Eventually.of_forall fun x v hv =>
      absurd (Subsingleton.elim v 0) hv⟩
  · haveI : NeZero d := ⟨hd.ne'⟩
    obtain ⟨lamTop, htop⟩ := furstenbergKesten_top hT hA hAmeas hint hint'
    obtain ⟨lamk', hbot⟩ := furstenbergKesten_bot hT hA hAmeas hint hint'
    refine ⟨-lamk', lamTop, ?_, ?_⟩
    · -- `-lamk' ≤ lamTop`: `0 ≤ lamTop + lamk'` from `log‖M‖ + log‖M⁻¹‖ ≥ log 1 = 0`.
      -- Take any `x` in both a.e. sets; the two limits add to a nonnegative quantity.
      obtain ⟨x, hx1, hx2⟩ := (htop.and hbot).exists
      have hsum : Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ +
            (n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) atTop (𝓝 (lamTop + lamk')) :=
        hx1.add hx2
      have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ +
          (n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖ := by
        intro n
        have hposc : 0 < ‖cocycle A T n x‖ := norm_cocycle_pos hA n x
        have hposi : 0 < ‖(cocycle A T n x)⁻¹‖ := norm_inv_cocycle_pos hA n x
        have hmulinv : cocycle A T n x * (cocycle A T n x)⁻¹ = 1 :=
          Matrix.mul_nonsing_inv _ (Ne.isUnit (det_cocycle_ne_zero hA n x))
        have h1 : (1 : ℝ) ≤ ‖cocycle A T n x‖ * ‖(cocycle A T n x)⁻¹‖ := by
          have := Matrix.l2_opNorm_mul (cocycle A T n x) (cocycle A T n x)⁻¹
          rw [hmulinv, norm_one_matrix] at this; exact this
        have hlog : 0 ≤ Real.log ‖cocycle A T n x‖ + Real.log ‖(cocycle A T n x)⁻¹‖ := by
          rw [← Real.log_mul (ne_of_gt hposc) (ne_of_gt hposi)]; exact Real.log_nonneg h1
        have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hlog hninv]
      have : 0 ≤ lamTop + lamk' :=
        ge_of_tendsto' hsum hnn
      linarith
    · -- The a.e. sandwich. Work on the intersection of the two FK a.e. sets.
      filter_upwards [htop, hbot] with x hx1 hx2
      intro v hv
      -- Boundedness of `growthSeq A T x v` from both FK limits.
      obtain ⟨hba, hbb⟩ := growthSeq_bounded hA x hx1 hx2 hv
      have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (growthSeq A T x v) :=
        hbb.isCoboundedUnder_le
      constructor
      · -- Lower bound: `lambdaBar = limsup ≥ liminf ≥ liminf lo = -lamk'`.
        have hlo : Tendsto (fun n : ℕ =>
            -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) +
              (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 (-lamk' + 0)) := by
          have hlogv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0) := by
            simpa using (tendsto_inv_atTop_nhds_zero_nat).mul_const (Real.log ‖v‖)
          exact hx2.neg.add hlogv
        have hliminf : -lamk' ≤ Filter.liminf (growthSeq A T x v) atTop := by
          have hmono : Filter.liminf (fun n : ℕ =>
              -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) +
                (n : ℝ)⁻¹ * Real.log ‖v‖) atTop ≤ Filter.liminf (growthSeq A T x v) atTop :=
            Filter.liminf_le_liminf (Eventually.of_forall fun n => le_growthSeq hA x hv n)
              hlo.isBoundedUnder_ge hba.isCoboundedUnder_ge
          calc -lamk' = -lamk' + 0 := by ring
            _ = Filter.liminf (fun n : ℕ =>
                -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) +
                  (n : ℝ)⁻¹ * Real.log ‖v‖) atTop := hlo.liminf_eq.symm
            _ ≤ _ := hmono
        calc -lamk' ≤ Filter.liminf (growthSeq A T x v) atTop := hliminf
          _ ≤ Filter.limsup (growthSeq A T x v) atTop := liminf_le_limsup hba hbb
          _ = lambdaBar A T x v := rfl
      · -- Upper bound: `lambdaBar ≤ lamTop`.
        have hub : ∀ n : ℕ, growthSeq A T x v n ≤
            ((n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖) :=
          fun n => growthSeq_le hA x hv n
        have hbddRHS : IsBoundedUnder (· ≤ ·) atTop
            (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖) := by
          have hlogv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0) := by
            simpa using (tendsto_inv_atTop_nhds_zero_nat).mul_const (Real.log ‖v‖)
          exact (hx1.add hlogv).isBoundedUnder_le
        calc lambdaBar A T x v
            = Filter.limsup (growthSeq A T x v) atTop := rfl
          _ ≤ Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ +
                (n : ℝ)⁻¹ * Real.log ‖v‖) atTop :=
              Filter.limsup_le_limsup (Eventually.of_forall hub) hcobdd hbddRHS
          _ = lamTop + 0 := by
              refine Filter.Tendsto.limsup_eq ?_
              have hlogv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0) := by
                simpa using (tendsto_inv_atTop_nhds_zero_nat).mul_const (Real.log ‖v‖)
              exact hx1.add hlogv
          _ = lamTop := by ring

/-! ### L4.2 ultrametric (non-Archimedean) inequality -/

/-- Per-`n` non-Archimedean bound: `growthSeq (v+w) n ≤ (1/n)log 2 + max (growthSeq v n)
(growthSeq w n)`, from `‖M(v+w)‖ ≤ ‖Mv‖ + ‖Mw‖ ≤ 2·max(‖Mv‖, ‖Mw‖)`. -/
private theorem growthSeq_add_le {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) [NeZero d] (x : X) {v w : EuclideanSpace ℝ (Fin d)}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) (n : ℕ) :
    growthSeq A T x (v + w) n ≤
      (n : ℝ)⁻¹ * Real.log 2 + max (growthSeq A T x v n) (growthSeq A T x w n) := by
  set M := Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) with hM
  have hMvw : 0 < ‖M (v + w)‖ := norm_pos_iff.mpr (cocycleVec_ne_zero hA n x hvw)
  have hMv : 0 < ‖M v‖ := norm_pos_iff.mpr (cocycleVec_ne_zero hA n x hv)
  have hMw : 0 < ‖M w‖ := norm_pos_iff.mpr (cocycleVec_ne_zero hA n x hw)
  -- `‖M(v+w)‖ ≤ ‖Mv‖ + ‖Mw‖ ≤ 2·max(‖Mv‖,‖Mw‖)`.
  have htri : ‖M (v + w)‖ ≤ 2 * max (‖M v‖) (‖M w‖) := by
    have h1 : ‖M (v + w)‖ ≤ ‖M v‖ + ‖M w‖ := by rw [map_add]; exact norm_add_le _ _
    have h2 : ‖M v‖ + ‖M w‖ ≤ 2 * max (‖M v‖) (‖M w‖) := by
      rcases le_total (‖M v‖) (‖M w‖) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    linarith
  have hmaxpos : 0 < max (‖M v‖) (‖M w‖) := lt_max_of_lt_left hMv
  -- Take logs: `log‖M(v+w)‖ ≤ log 2 + max(log‖Mv‖, log‖Mw‖)`.
  have hlog : Real.log ‖M (v + w)‖ ≤
      Real.log 2 + max (Real.log ‖M v‖) (Real.log ‖M w‖) := by
    have hstep : Real.log ‖M (v + w)‖ ≤ Real.log (2 * max (‖M v‖) (‖M w‖)) :=
      Real.log_le_log hMvw htri
    rw [Real.log_mul (by norm_num) (ne_of_gt hmaxpos)] at hstep
    have hlogmax : Real.log (max (‖M v‖) (‖M w‖)) = max (Real.log ‖M v‖) (Real.log ‖M w‖) := by
      rcases le_total (‖M v‖) (‖M w‖) with h | h
      · rw [max_eq_right h, max_eq_right (Real.log_le_log hMv h)]
      · rw [max_eq_left h, max_eq_left (Real.log_le_log hMw h)]
    rw [hlogmax] at hstep; exact hstep
  -- Multiply by `(1/n) ≥ 0` and distribute over `max`.
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  calc growthSeq A T x (v + w) n
      = (n : ℝ)⁻¹ * Real.log ‖M (v + w)‖ := rfl
    _ ≤ (n : ℝ)⁻¹ * (Real.log 2 + max (Real.log ‖M v‖) (Real.log ‖M w‖)) :=
        mul_le_mul_of_nonneg_left hlog hninv
    _ = (n : ℝ)⁻¹ * Real.log 2 +
          max ((n : ℝ)⁻¹ * Real.log ‖M v‖) ((n : ℝ)⁻¹ * Real.log ‖M w‖) := by
        rw [mul_add, mul_max_of_nonneg _ _ hninv]
    _ = (n : ℝ)⁻¹ * Real.log 2 + max (growthSeq A T x v n) (growthSeq A T x w n) := rfl

/-- **L4.2 ultrametric.** The non-Archimedean inequality, with boundedness of the three
defining sequences (which holds a.e. by Furstenberg–Kesten; supplied via `growthSeq_bounded`
in `isUltrametricGrowth_lambdaBar`). -/
theorem lambdaBar_add_le {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) [NeZero d] (x : X) {v w : EuclideanSpace ℝ (Fin d)}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0)
    (hbv : IsBoundedUnder (· ≤ ·) atTop (growthSeq A T x v))
    (hbv' : IsBoundedUnder (· ≥ ·) atTop (growthSeq A T x v))
    (hbw : IsBoundedUnder (· ≤ ·) atTop (growthSeq A T x w))
    (hbw' : IsBoundedUnder (· ≥ ·) atTop (growthSeq A T x w))
    (hbvw' : IsBoundedUnder (· ≥ ·) atTop (growthSeq A T x (v + w))) :
    lambdaBar A T x (v + w) ≤ max (lambdaBar A T x v) (lambdaBar A T x w) := by
  -- `growthSeq (v+w) ≤ (1/n)log2 + max(growthSeq v, growthSeq w)`.
  have hcobvw : IsCoboundedUnder (· ≤ ·) atTop (growthSeq A T x (v + w)) :=
    hbvw'.isCoboundedUnder_le
  -- Upper bound the limsup by the limsup of the RHS.
  have hRHSbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2 +
        max (growthSeq A T x v n) (growthSeq A T x w n)) := by
    have hlog2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat).mul_const (Real.log 2)
    have hmaxbdd : IsBoundedUnder (· ≤ ·) atTop
        (fun n : ℕ => max (growthSeq A T x v n) (growthSeq A T x w n)) := hbv.sup hbw
    exact isBoundedUnder_le_add hlog2.isBoundedUnder_le hmaxbdd
  calc lambdaBar A T x (v + w)
      = Filter.limsup (growthSeq A T x (v + w)) atTop := rfl
    _ ≤ Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2 +
          max (growthSeq A T x v n) (growthSeq A T x w n)) atTop :=
        Filter.limsup_le_limsup
          (Eventually.of_forall fun n => growthSeq_add_le hA x hv hw hvw n) hcobvw hRHSbdd
    _ = max (lambdaBar A T x v) (lambdaBar A T x w) := by
        -- `(1/n)log2 → 0` drops out; then `limsup max = max limsup`.
        have hdrop : Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2 +
            max (growthSeq A T x v n) (growthSeq A T x w n)) atTop =
            Filter.limsup (fun n : ℕ => max (growthSeq A T x v n) (growthSeq A T x w n)) atTop := by
          refine limsup_eq_of_tendsto_sub_zero ?_
          have hlog2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
            simpa using (tendsto_inv_atTop_nhds_zero_nat).mul_const (Real.log 2)
          refine hlog2.congr' ?_
          filter_upwards with n
          ring
        rw [hdrop, limsup_max hbv'.isCoboundedUnder_le hbw'.isCoboundedUnder_le hbv hbw]
        rfl

/-! ### Packaged ultrametric growth function (a.e.) -/

/-- **Packaged L4.1–4.2.** For a.e. `x`, the upper Lyapunov growth function
`lambdaBar A T x` is an `IsUltrametricGrowth` function: scaling-invariant (`lambdaBar_smul`)
and non-Archimedean (`lambdaBar_add_le`, with the required boundedness discharged from the
Furstenberg–Kesten sandwich `growthSeq_bounded`). -/
theorem isUltrametricGrowth_lambdaBar
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, IsUltrametricGrowth (lambdaBar A T x) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: `lambdaBar` is constant on the trivial space; the predicate holds for every `x`.
    subst hd
    refine Filter.Eventually.of_forall fun x => ⟨?_, ?_⟩
    · intro c v hc
      rw [Subsingleton.elim (c • v) v]
    · intro v w hv _ _
      exact absurd (Subsingleton.elim v 0) hv
  · haveI : NeZero d := ⟨hd.ne'⟩
    obtain ⟨lamTop, htop⟩ := furstenbergKesten_top hT hA hAmeas hint hint'
    obtain ⟨lamk', hbot⟩ := furstenbergKesten_bot hT hA hAmeas hint hint'
    -- Off the intersection of the two FK a.e. sets, both FK sequences converge.
    filter_upwards [htop, hbot] with x hx1 hx2
    refine ⟨?_, ?_⟩
    · -- `scaling`: `lambdaBar_smul` (trivial on `v = 0`).
      intro c v hc
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact lambdaBar_smul A T x hc v hv
    · -- `ultra`: `lambdaBar_add_le`, boundedness from `growthSeq_bounded`.
      intro v w hv hw hvw
      obtain ⟨hbv, hbv'⟩ := growthSeq_bounded hA x hx1 hx2 hv
      obtain ⟨hbw, hbw'⟩ := growthSeq_bounded hA x hx1 hx2 hw
      obtain ⟨_, hbvw'⟩ := growthSeq_bounded hA x hx1 hx2 hvw
      exact lambdaBar_add_le hA x hv hw hvw hbv hbv' hbw hbw' hbvw'

end Oseledets
