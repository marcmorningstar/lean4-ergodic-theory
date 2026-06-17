/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.SlowFlagBridge
import Oseledets.Lyapunov.SpectrumConstancy
import Oseledets.Lyapunov.ForwardLowerWiring

/-!
# The Oseledets filtration theorem from the spectral upper bound

This file assembles the Oseledets filtration theorem `oseledets_filtration_of_upper` from a
single analytic input `hupper` — the per-vector spectral upper bound: every nonzero vector of
the slow space `vslow A T (Real.exp t) x` has upper growth exponent at most `t` — together
with a minimized set of precisely typed residual hypotheses capturing the spectral
identification of the Oseledets limit operator.

The assembly proceeds through `Oseledets.oseledets_filtration_of_slowflag`, which consumes
three almost-everywhere interfaces: `hspec`, `hslowflag`, and `hgrowth`.  Each is discharged
as far as `hupper` allows, isolating the remaining content into named residual hypotheses:

* **`hslowflag`** (`vslow (exp t) = lambdaSublevel t`).  The forward inclusion
  `vslow (exp t) ≤ lambdaSublevel t` is derived from `hupper`: a vector in the slow space grows
  slowly, hence lies in the growth sublevel (`vslow_subset_lambdaSublevel_of_upper`).  The
  reverse inclusion is taken as the typed residual hypothesis `hslowrev`.

* **`hgrowth`** via `Oseledets.tendsto_inv_mul_log_norm_cocycle_apply_of_upper_lower`.  The upper half `hub` holds
  unconditionally on the `IsUltrametricGrowth` good set (`limsup_log_norm_cocycle_apply_le_specList_of_mem_stratum`); the
  boundedness `hbdd` comes from the Furstenberg–Kesten layer (`Oseledets.isBoundedUnder_inv_mul_log_norm_cocycle_apply_of_mem_stratum`); the
  lower bound `hlb` comes from the band-projector layer (`Oseledets.specList_le_liminf_inv_mul_log_norm_cocycle_apply_of_bandProjector`),
  fed the residual band-projector convergence datum `hband`.

* **`hspec`** via `Oseledets.specList_eq_expEnum_of_subsets_standing`.  The two `Finset` inclusions between the
  realized exponent set `spectrum` and the deterministic exponent set `distinctExp lam0 d`
  are taken as the typed residuals `hub_spec` and `hlb_spec`.

The residual hypotheses `hslowrev`, `hband`, `hub_spec`, `hlb_spec` are each the minimal
cleanly typed shape of a single spectral fact about the Oseledets limit operator; none is
derivable from `hupper` alone.

## Main results

* `Oseledets.vslow_subset_lambdaSublevel_of_upper`: the forward slow-flag inclusion
  `vslow (exp t) ≤ lambdaSublevel t` from the spectral upper bound.
* `Oseledets.limsup_log_norm_cocycle_apply_le_specList_of_mem_stratum`: the per-stratum `limsup` upper bound, almost everywhere.
* `Oseledets.vslow_eq_lambdaSublevel_of_upper`: the slow-flag identification
  `vslow (exp t) = lambdaSublevel t` from the spectral upper bound and the reverse inclusion.
* `Oseledets.oseledets_filtration_of_upper`: the Oseledets filtration theorem, assembled from
  the spectral upper bound and the residual spectral-identification hypotheses.
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]

/-! ## Forward inclusion of `hslowflag` from `hupper` -/

omit [MeasurableSpace X] [NeZero d] in
/-- **`vslow (exp t) ⊆ lambdaSublevel t` from `hupper`.**  A nonzero vector in the Λ-slow band
at level `e^t` has, by `hupper`, `limsup (1/n) log‖A⁽ⁿ⁾ v‖ ≤ t`; that `limsup` *is*
`lambdaBar A T x v` (`limsup_log_norm_cocycle_eq_lambdaBar`), so `lambdaBar A T x v ≤ t`, i.e.
`v ∈ lambdaSublevel t`.  The zero vector lies in every submodule.  Requires only the
`IsUltrametricGrowth` good set (to use the sublevel membership criterion `mem_lambdaSublevel`). -/
theorem vslow_subset_lambdaSublevel_of_upper
    {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {x : X}
    (hx : IsUltrametricGrowth (lambdaBar A T x))
    (hupperx : ∀ t : ℝ, ∀ v ∈ vslow A T (Real.exp t) x, v ≠ 0 →
      limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ t) :
    ∀ t : ℝ, vslow A T (Real.exp t) x ≤ lambdaSublevel A T x t := by
  intro t v hv
  rw [mem_lambdaSublevel hx]
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  · refine Or.inr ?_
    have := hupperx t v hv hv0
    rwa [limsup_log_norm_cocycle_eq_lambdaBar] at this

/-! ## The `hgrowth` upper half from `vflag` membership

The upper half `hub` of `Oseledets.tendsto_inv_mul_log_norm_cocycle_apply_of_upper_lower` is, in fact, *unconditional* given
the `IsUltrametricGrowth` good set: a vector in the stratum `vflag i.castSucc \ vflag i.succ`
has `lambdaBar = specList i` exactly (`lambdaBar_eq_on_stratum`), and that `lambdaBar` is the
`limsup` (`limsup_log_norm_cocycle_eq_lambdaBar`).  So `limsup ≤ specList i` holds (with
equality) and `hub` needs no separate analytic input. -/

omit [NeZero d] in
/-- **`hub` from `vflag` membership (a.e.).**  On the `IsUltrametricGrowth` good set the
per-stratum `limsup` equals the exact exponent `specList i`, so in particular
`limsup ≤ specList i` — the upper half consumed by `Oseledets.tendsto_inv_mul_log_norm_cocycle_apply_of_upper_lower`. -/
theorem limsup_log_norm_cocycle_apply_le_specList_of_mem_stratum
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ vflag A T x i.succ →
        limsup (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ specList A T x i := by
  filter_upwards [isUltrametricGrowth_lambdaBar hT hA hAmeas hint hint'] with x hx i v hv hvnot
  rw [limsup_log_norm_cocycle_eq_lambdaBar]
  exact le_of_eq (lambdaBar_eq_on_stratum hx i hv hvnot)

/-! ## Assembling `hslowflag` from the forward (`hupper`) and reverse inclusions -/

omit [NeZero d] in
/-- **`hslowflag` from `hupper` and the reverse inclusion.**  Combines the forward inclusion
`vslow (exp t) ⊆ lambdaSublevel t` (derived from `hupper` via
`vslow_subset_lambdaSublevel_of_upper`) with the reverse inclusion `hslowrev`
(`lambdaSublevel t ⊆ vslow (exp t)`) into the per-point identification
`vslow (exp t) = lambdaSublevel t` consumed by `oseledets_filtration_of_slowflag`. -/
theorem vslow_eq_lambdaSublevel_of_upper
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (hupper : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ vslow A T (Real.exp t) x, v ≠ 0 →
      limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ t)
    (hslowrev : ∀ᵐ x ∂μ, ∀ t : ℝ, lambdaSublevel A T x t ≤ vslow A T (Real.exp t) x) :
    ∀ᵐ x ∂μ, ∀ t : ℝ, vslow A T (Real.exp t) x = lambdaSublevel A T x t := by
  filter_upwards [isUltrametricGrowth_lambdaBar hT hA hAmeas hint hint', hupper, hslowrev]
    with x hx hupperx hrevx
  intro t
  exact le_antisymm (vslow_subset_lambdaSublevel_of_upper hx (hupperx) t) (hrevx t)

/-! ## The composed filtration theorem -/

/-- **Oseledets filtration theorem, composed from the spectral upper bound `hupper`.**

The complete Oseledets measurable-filtration conclusion, assembled through
`oseledets_filtration_of_slowflag` from the per-vector spectral upper bound `hupper`.  The
deterministic exponent data `lam0` is taken from `exists_lam_tendsto_singularValue`.  The
three a.e. interfaces are discharged as follows:

* `hslowflag` — forward inclusion derived from `hupper` (`vslow_eq_lambdaSublevel_of_upper`), reverse
  inclusion the residual `hslowrev`;
* `hgrowth` — `hub` derived from `vflag` membership (`limsup_log_norm_cocycle_apply_le_specList_of_mem_stratum`), `hbdd` from
  `isBoundedUnder_inv_mul_log_norm_cocycle_apply_of_mem_stratum`, `hlb` from `specList_le_liminf_inv_mul_log_norm_cocycle_apply_of_bandProjector` fed the residual band datum `hband`;
* `hspec` — `specList_eq_expEnum_of_subsets_standing` fed the two residual `Finset` spectrum inclusions
  `hub_spec` / `hlb_spec`.

The residual hypotheses `hslowrev`, `hband`, `hub_spec`, `hlb_spec` capture exactly the
spectral identification of the Oseledets limit operator; see the module docstring. -/
theorem oseledets_filtration_of_upper
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hTmeas : Measurable T)
    {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    -- The per-vector spectral upper bound.
    (hupper : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ vslow A T (Real.exp t) x, v ≠ 0 →
      Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) Filter.atTop ≤ t)
    -- Residual 1: the reverse slow-flag inclusion (slow growth implies slow-space membership).
    (hslowrev : ∀ᵐ x ∂μ, ∀ t : ℝ, lambdaSublevel A T x t ≤ vslow A T (Real.exp t) x)
    -- Residual 2: spectrum upper Finset inclusion (every realized exponent is deterministic).
    (hub_spec : ∀ lam0 : ℕ → ℝ,
      (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam0 i))) →
      ∀ᵐ x ∂μ, lyapunovSpectrum A T x ⊆ distinctExp lam0 d)
    -- Residual 3: spectrum lower Finset inclusion (every deterministic exponent is attained).
    (hlb_spec : ∀ lam0 : ℕ → ℝ,
      (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam0 i))) →
      ∀ᵐ x ∂μ, distinctExp lam0 d ⊆ lyapunovSpectrum A T x)
    -- Residual 4: the band-projector convergence datum feeding the liminf lower bound.
    (hband : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ vflag A T x i.succ →
        ∃ P : Matrix (Fin d) (Fin d) ℝ,
          Tendsto (fun n => bandProjector A T
            (Set.indicator (Set.Ioi (Real.exp (specList A T x i))) 1) n x) atTop (𝓝 P) ∧
          Matrix.toEuclideanLin P v ≠ 0) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (V i x) =
            V i (T x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
              atTop (𝓝 (lam i))) := by
  classical
  -- The deterministic singular-value exponents.
  obtain ⟨lam0, _hmono, hlam0⟩ :=
    exists_lam_tendsto_singularValue hT hA hAmeas hint hint'
  -- `hspec` from the two residual spectrum inclusions.
  have hspec := specList_eq_expEnum_of_subsets_standing hT A hA hAmeas hint hint' lam0
    (hub_spec lam0 hlam0) (hlb_spec lam0 hlam0)
  -- `hslowflag` from `hupper` and the reverse inclusion.
  have hslowflag := vslow_eq_lambdaSublevel_of_upper hT hA hAmeas hint hint' hupper hslowrev
  -- `hgrowth` from upper (`vflag`) + lower (band) + boundedness (Furstenberg–Kesten).
  have hbdd := isBoundedUnder_inv_mul_log_norm_cocycle_apply_of_mem_stratum hT A hA hAmeas hint hint'
  have hub := limsup_log_norm_cocycle_apply_le_specList_of_mem_stratum hT hA hAmeas hint hint'
  have hlb := specList_le_liminf_inv_mul_log_norm_cocycle_apply_of_bandProjector A hA hband hbdd
  have hgrowth := tendsto_inv_mul_log_norm_cocycle_apply_of_upper_lower A hub hlb hbdd
  -- Assemble through `oseledets_filtration_of_slowflag`.
  exact oseledets_filtration_of_slowflag hT A hA hAmeas hTmeas hint hint' lam0
    hspec hslowflag hgrowth

end Oseledets
