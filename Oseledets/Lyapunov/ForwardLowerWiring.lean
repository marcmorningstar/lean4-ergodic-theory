import Oseledets.Lyapunov.FiltrationAssembly
import Oseledets.Lyapunov.FiltrationAssemblyBridge
import Oseledets.Lyapunov.ForwardAngle
import Oseledets.Cocycle.FurstenbergKesten

/-!
# `ForwardLowerWiring` — discharging `hlb`/`hbdd` for `hgrowth_of_upper_lower`

This scratch file supplies the two remaining hypotheses of the committed
`Oseledets.hgrowth_of_upper_lower` (in `FiltrationAssemblyBridge.lean`):

* `hbdd_of_fk` — the two-sided `IsBoundedUnder` side-conditions on the normalized log-growth
  sequence `(1/n) log‖A⁽ⁿ⁾ v‖`, discharged *unconditionally* from the standing hypotheses by the
  Furstenberg–Kesten extremal exponents (top and bottom).

* `hlb_of_bandProjector` — the per-vector liminf lower bound, reduced to the band-projector
  convergence datum (the L11 connection of `Vflag` membership to the spectral band structure),
  taken here as the minimal cleanly-typed hypothesis and forwarded to the committed analytic core
  `log_le_liminf_log_cocycle_apply`.
-/

open MeasureTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

set_option linter.deprecated false
set_option linter.unusedSectionVars false

/-! ## Helper norm bounds (apply-norm sandwiched by operator norm) -/

/-- `‖A⁽ⁿ⁾ v‖ ≤ ‖A⁽ⁿ⁾‖ * ‖v‖` (apply-norm bounded above by the operator norm). -/
theorem norm_toEuclideanLin_cocycle_le {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ≤ ‖cocycle A T n x‖ * ‖v‖ := by
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (𝕜 := ℝ),
    ← Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ)]
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x)).le_opNorm v

/-- The inverse cocycle is a left inverse of the cocycle on `EuclideanSpace`. -/
theorem toEuclideanLin_inv_cocycle_apply {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0) (n : ℕ) (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanLin (cocycle A T n x)⁻¹
      (Matrix.toEuclideanLin (cocycle A T n x) v) = v := by
  rw [Matrix.toEuclideanLin_apply, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit (det_cocycle_ne_zero hA n x)),
    Matrix.one_mulVec]

/-- `‖v‖ ≤ ‖(A⁽ⁿ⁾)⁻¹‖ * ‖A⁽ⁿ⁾ v‖` (apply-norm bounded below via the inverse operator norm). -/
theorem norm_le_norm_inv_cocycle_mul {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0) (n : ℕ) (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ ‖(cocycle A T n x)⁻¹‖ * ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
  calc ‖v‖ = ‖Matrix.toEuclideanLin (cocycle A T n x)⁻¹
        (Matrix.toEuclideanLin (cocycle A T n x) v)‖ := by
        rw [toEuclideanLin_inv_cocycle_apply A hA n x v]
    _ ≤ ‖(cocycle A T n x)⁻¹‖ * ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
        rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (𝕜 := ℝ),
          ← Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ)]
        exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x)⁻¹).le_opNorm _

/-! ## The two-sided boundedness from Furstenberg–Kesten -/

/-- The normalized log-norm of `v` along the cocycle is eventually `≤` the convergent envelope
`(1/n) log‖A⁽ⁿ⁾‖ + (1/n) log‖v‖` and eventually `≥` the convergent envelope
`-(1/n) log‖(A⁽ⁿ⁾)⁻¹‖ + (1/n) log‖v‖`.  Both envelopes converge (Furstenberg–Kesten), so the middle
sequence is bounded on both sides. -/
theorem isBoundedUnder_log_norm_cocycle_apply {T : X → X}
    {μ : Measure X} [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 →
      (IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) ∧
      (IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: every space is trivial and there is no nonzero `v`.
    subst hd
    filter_upwards with x v hv
    exact absurd (Subsingleton.elim v 0) hv
  · haveI : NeZero d := ⟨hd.ne'⟩
    obtain ⟨lamT, hlamT⟩ := furstenbergKesten_top hT hA hAmeas hint hint'
    obtain ⟨lamB, hlamB⟩ := furstenbergKesten_bot hT hA hAmeas hint hint'
    filter_upwards [hlamT, hlamB] with x hxT hxB v hv
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    -- The `(1/n) log‖v‖` correction tends to `0`.
    have hcorr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
      simpa using this.mul_const (Real.log ‖v‖)
    constructor
    · -- Upper envelope: `(1/n) log‖A⁽ⁿ⁾ v‖ ≤ (1/n) log‖A⁽ⁿ⁾‖ + (1/n) log‖v‖`.
      have henv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖
          + (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 (lamT + 0)) := hxT.add hcorr
      refine (henv.isBoundedUnder_le).mono_le ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hposc : 0 < ‖cocycle A T n x‖ := norm_cocycle_pos hA n x
      have hposv : (0 : ℝ) < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
        rw [norm_pos_iff]
        intro hzero
        have : v = 0 := by
          have := congrArg (Matrix.toEuclideanLin (cocycle A T n x)⁻¹) hzero
          rwa [toEuclideanLin_inv_cocycle_apply A hA n x v, map_zero] at this
        exact hv this
      have hle : Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
          ≤ Real.log ‖cocycle A T n x‖ + Real.log ‖v‖ := by
        rw [← Real.log_mul (ne_of_gt hposc) (ne_of_gt hvpos)]
        exact Real.log_le_log hposv (norm_toEuclideanLin_cocycle_le A n x v)
      have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      calc (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
          ≤ (n : ℝ)⁻¹ * (Real.log ‖cocycle A T n x‖ + Real.log ‖v‖) :=
            mul_le_mul_of_nonneg_left hle hninv
        _ = (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖ := by ring
    · -- Lower envelope: `(1/n) log‖A⁽ⁿ⁾ v‖ ≥ -(1/n) log‖(A⁽ⁿ⁾)⁻¹‖ + (1/n) log‖v‖`.
      have henv : Tendsto (fun n : ℕ => -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖)
          + (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 (-lamB + 0)) := hxB.neg.add hcorr
      refine (henv.isBoundedUnder_ge).mono_ge ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hposi : 0 < ‖(cocycle A T n x)⁻¹‖ := norm_inv_cocycle_pos hA n x
      have hposv : (0 : ℝ) < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
        rw [norm_pos_iff]
        intro hzero
        have : v = 0 := by
          have := congrArg (Matrix.toEuclideanLin (cocycle A T n x)⁻¹) hzero
          rwa [toEuclideanLin_inv_cocycle_apply A hA n x v, map_zero] at this
        exact hv this
      -- `log‖v‖ ≤ log‖(A⁽ⁿ⁾)⁻¹‖ + log‖A⁽ⁿ⁾ v‖`, i.e. `-log‖(A⁽ⁿ⁾)⁻¹‖ + log‖v‖ ≤ log‖A⁽ⁿ⁾ v‖`.
      have hge : -Real.log ‖(cocycle A T n x)⁻¹‖ + Real.log ‖v‖
          ≤ Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
        have hlogle : Real.log ‖v‖
            ≤ Real.log ‖(cocycle A T n x)⁻¹‖ + Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
          rw [← Real.log_mul (ne_of_gt hposi) (ne_of_gt hposv)]
          exact Real.log_le_log hvpos (norm_le_norm_inv_cocycle_mul A hA n x v)
        linarith
      have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      calc -((n : ℝ)⁻¹ * Real.log ‖(cocycle A T n x)⁻¹‖) + (n : ℝ)⁻¹ * Real.log ‖v‖
          = (n : ℝ)⁻¹ * (-Real.log ‖(cocycle A T n x)⁻¹‖ + Real.log ‖v‖) := by ring
        _ ≤ (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ :=
            mul_le_mul_of_nonneg_left hge hninv

/-! ## Deliverable A — `hbdd` -/

/-- **`hbdd` from Furstenberg–Kesten.**  Discharges the two-sided `IsBoundedUnder` side-conditions
of `hgrowth_of_upper_lower` *unconditionally* from the standing hypotheses.  On each stratum the
vector is nonzero (`0` lies in every flag level, so `v ∉ Vflag i.succ ⟹ v ≠ 0`), and the
log-growth sequence is squeezed between the two convergent Furstenberg–Kesten envelopes. -/
theorem hbdd_of_fk {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        (IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) ∧
        (IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) := by
  filter_upwards [isBoundedUnder_log_norm_cocycle_apply hT A hA hAmeas hint hint']
    with x hx i v _ hvnot
  -- `0 ∈ Vflag i.succ` (submodules contain `0`), so `v ∉ Vflag i.succ ⟹ v ≠ 0`.
  have hv : v ≠ 0 := fun h => hvnot (h ▸ Submodule.zero_mem _)
  exact hx v hv

/-! ## Deliverable B — `hlb`

The per-vector liminf lower bound is the committed analytic core
`log_le_liminf_log_cocycle_apply`: at threshold `c = e^{specList i} > 0`, if the band projectors
for `(c, ∞)` converge to a limit `P` with `P v ≠ 0`, then `specList i = log c ≤ liminf …`.  The
remaining `IsCoboundedUnder (· ≥ ·)` side-condition is exactly the lower boundedness already
furnished by `hbdd_of_fk` (a bounded-below sequence is cobounded-below).

The band-projector convergence datum (`hP`, `hPv`) is the L11 spectral-band identification of
`Vflag` membership — `v ∉ Vflag i.succ` says `v` has a nonzero component in the band at level
`≥ specList i`, i.e. `P v ≠ 0` for the limit projector at threshold `e^{specList i}`.  That
identification is not yet committed in the repo, so it is taken here as the minimal cleanly-typed
hypothesis `hband`; once a committed `Vflag`-to-band lemma exists it discharges `hband` directly. -/

/-- **`hlb` from band-projector convergence.**  Given, a.e. and per stratum-vector, the band
projector convergence datum at threshold `e^{specList i}` (`hband`) and the lower boundedness of the
log-growth sequence (from `hbdd_of_fk`), the per-vector lower bound `specList i ≤ liminf …` holds.

The cobounded-below side-condition of `log_le_liminf_log_cocycle_apply` is supplied by the same
`IsBoundedUnder (· ≥ ·)` already proved in `hbdd_of_fk` (`IsBoundedUnder.isCoboundedUnder_ge`,
using that `atTop` is `NeBot`). -/
theorem hlb_of_bandProjector [NeZero d] {μ : Measure X} {T : X → X}
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ x, (A x).det ≠ 0)
    (hband : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        ∃ P : Matrix (Fin d) (Fin d) ℝ,
          Tendsto (fun n => bandProjector A T
            (Set.indicator (Set.Ioi (Real.exp (specList A T x i))) 1) n x) atTop (𝓝 P) ∧
          Matrix.toEuclideanLin P v ≠ 0)
    (hbdd : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        (IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) ∧
        (IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))) :
    ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        specList A T x i ≤ liminf (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop := by
  filter_upwards [hband, hbdd] with x hbandx hbddx i v hv hvnot
  obtain ⟨P, hP, hPv⟩ := hbandx i v hv hvnot
  obtain ⟨hba, _⟩ := hbddx i v hv hvnot
  -- `IsCoboundedUnder (· ≥ ·)` from bounded-*above* (`isCoboundedUnder_ge` flips the order).
  have hcob : IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) :=
    hba.isCoboundedUnder_ge
  have hc : (0 : ℝ) < Real.exp (specList A T x i) := Real.exp_pos _
  have := log_le_liminf_log_cocycle_apply A T hA hc hP hPv hcob
  rwa [Real.log_exp] at this

/-! ## Type-compatibility check: feed both deliverables into `hgrowth_of_upper_lower` -/

/-- Sanity wiring: `hbdd_of_fk` and `hlb_of_bandProjector` have exactly the types consumed by the
committed `hgrowth_of_upper_lower`.  Given the (parallel-worker) upper bound `hub` and the
band-projector datum `hband`, the per-vector exact growth interface `hgrowth` follows. -/
theorem hgrowth_of_fk_and_band [NeZero d] {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (hub : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        limsup (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ specList A T x i)
    (hband : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        ∃ P : Matrix (Fin d) (Fin d) ℝ,
          Tendsto (fun n => bandProjector A T
            (Set.indicator (Set.Ioi (Real.exp (specList A T x i))) 1) n x) atTop (𝓝 P) ∧
          Matrix.toEuclideanLin P v ≠ 0) :
    ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
          atTop (𝓝 (specList A T x i)) :=
  have hbdd := hbdd_of_fk hT A hA hAmeas hint hint'
  hgrowth_of_upper_lower A hub (hlb_of_bandProjector A hA hband hbdd) hbdd

/-! ## Axiom audit -/

#print axioms hbdd_of_fk
#print axioms hlb_of_bandProjector
#print axioms hgrowth_of_fk_and_band

end Oseledets
