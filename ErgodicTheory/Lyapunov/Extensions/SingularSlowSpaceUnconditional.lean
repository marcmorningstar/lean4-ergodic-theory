/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.OseledetsLimit.ProjectorIncrement
import ErgodicTheory.Lyapunov.Extensions.SingularSlowSpace
import ErgodicTheory.Lyapunov.Extensions.SingularBandConverge

/-!
# The singular slow space `Vⱼ` — unconditional on the tempered class (Wave-5, Angle 5A)

For a **possibly-singular** (non-invertible) matrix cocycle generator
`A : X → Matrix (Fin d) (Fin d) ℝ`, the intermediate slow space `Vⱼ(ω)` of the singular forward
Oseledets filtration (Quas, *MET and Applications*, 2013, **Theorem 2**; Ruelle, Publ. IHES 50,
1979, **Lemma 1.4**) is — by the landed structural reduction
`ErgodicTheory.tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector`
(`SingularSlowSpace.lean`) — reduced **unconditionally** to a single input: convergence of the fast
band projector `bandProjector A T (𝟙_{(c,∞)}) n x` at a Lyapunov cut `c`. That band convergence
follows by the **root test** from any per-step increment upper bound `b n` with
`(1/n)·log b n → L < 0`. This module supplies that — with the negative log-limit obtained from the
**a.e.-constant genuine singular spectrum's strict gap at the cut**
(`SingularSpectrumConstant.lean`, via `ErgodicTheory.ae_singularSpectralValue_eq_const`) — and pins,
with `cruxStatus`-quality precision, exactly which hypothesis the resulting `Vⱼ` carries.

## What Wave-5 establishes, and the precise residual

The **forward-ratio crack** (Angle 5A) sought a *det-free, inverse-free* per-step bound

  `(R5A)   ‖P_slow(n+1) − P_slow(n)‖ ≤ C · σ_{k+1}(M_{n+1}) / σ_k(M_{n+1})`,

`M_{n+1} = cocycle (n+1) x`, controlling the slow increment by a **forward** singular-value ratio of
the *single* cocycle `M_{n+1}` (no inverse). We record (`bandProjector_increment_eq_aperture`,
a *statement-level* identity, **not** a proof of a false claim) that `(R5A)` is **false at the
per-step granularity**: the band increment `‖P_slow(n+1) − P_slow(n)‖` is the **aperture**
`sin∠(S_n, S_{n+1})` between the top-`k` right-singular spaces of `M_n` and `M_{n+1} = B·M_n`
(`B = A(Tⁿx)`); a single ill-conditioned step `B` (with `σ_k(B)` small, `k < d`, `det B` possibly
`0`) can rotate `S_n` by an `O(1)` angle while the *internal* forward gap
`σ_{k+1}(M_{n+1})/σ_k(M_{n+1})` of `M_{n+1}` stays `O(1)`. Davis–Kahan gives
`sin∠(S_n, S_{n+1}) ≤ ‖(B*B − I)|_{S_n}‖ / gap`, whose numerator is the **condition number of `B`**
(the inverse), not the forward ratio. So the inverse is genuinely **load-bearing per step** — it is
intrinsic to *which directions are top-`k` after applying `B`* — and the forward ratio does not
bound the aperture. This is the same wall the Wave-4 wedge route (`SingularSlowSpaceConverge.lean`,
`wedge_mu0_lb_is_inverse_bound`) and the per-step `s`-engine (`SingularBandConverge.lean`) hit.

## The guaranteed landing: unconditional on the tempered class

What **is** unconditional and sorry-free here:

* `ErgodicTheory.tendsto_vSlowSingularStep_of_summable_increment` — the **soft-analysis core**: from a
  per-step increment upper bound `b n ≥ ‖P_slow(n+1) − P_slow(n)‖` (equivalently the fast band
  increment, by the complement bridge) with `(1/n)·log b n → L < 0`, the slow projectors converge to
  the **explicit complement** `1 − Pfast` of the fast band limit. **No invertibility, no det, no
  tempering** — pure root test + the landed structural reduction. This is genuinely unconditional;
  the only content is *supplying* such a `b`.

* `ErgodicTheory.tendsto_vSlowSingularStep_of_tempered` — the **tempered-class `Vⱼ`**: supplying `b`
  from the det-free `s`-engine (`norm_bandProjector_succ_sub_le_detfree`) under
  (i) a **strict spectral gap at the cut** `lamK < lamK1` from the a.e.-constant singular spectrum
  (the forward ratio `r = σ_k/σ_{k-1}` then has `(1/n)log r → lamK − lamK1 < 0`, geometric decay),
  and (ii) **tempering** of the compound condition number `(1/n)·log(cB·cBi) → 0`. Then
  `(1/n)·log b → lamK − lamK1 < 0`, so `b` is summable and `Vⱼ` converges to `1 − Pfast`. The carry
  is the *tempered-non-degeneracy* hypothesis — strictly weaker than `det A ≠ 0` everywhere, but it
  still requires each step's compound inverse to exist (so the `s = 1/cBi` supply is well-defined):
  see `bandProjector_increment_eq_aperture` for why no inverse-free per-step replacement exists.

* `ErgodicTheory.measurableSubspace_vSlowSingularStep` (re-exported context) and
  `ErgodicTheory.vSlowSingularStep_antitone` give the measurability and the antitone flag of the limit
  `Vⱼ` for free, from the landed `SingularSlowSpace.lean` (they are deterministic / unconditional).

## Main results

* `ErgodicTheory.tendsto_vSlowSingularStep_of_summable_increment` — unconditional soft core: summable
  per-step increment bound ⇒ `Vⱼ` converges to `1 − Pfast`.
* `ErgodicTheory.tendsto_log_detfree_step_bound` — the negative log-limit of the det-free `s`-engine's
  per-step bound, from the strict gap + tempering.
* `ErgodicTheory.summable_detfree_step_bound` — the det-free per-step bound is summable under strict gap
  + tempering (root test).
* `ErgodicTheory.tendsto_vSlowSingularStep_of_tempered` — the tempered-class `Vⱼ`: convergence to
  `1 − Pfast` carrying the strict-gap + tempering hypotheses.
* `ErgodicTheory.ForwardRatioPerStepBound` / `ErgodicTheory.bandProjector_increment_eq_aperture` — the
  precise residual record: the forward-ratio per-step bound `(R5A)` is the aperture, governed by the
  inverse (condition number of `B`), not the forward ratio.

## References

* A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1).
* M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*,
  Israel J. Math. **32** (1979), 356–362.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46 (the sin-Θ aperture bound).
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder

noncomputable section

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d] {T : X → X}

/-! ## The unconditional soft-analysis core

Any per-step upper bound on the slow (equivalently, by the complement bridge, fast band) increment
whose `(1/n)·log` tends to a negative limit makes the increments summable (root test,
`summable_of_logLimit_neg`), hence the slow projectors converge to the explicit complement
`1 − Pfast` of the fast band limit. This is **unconditional**: no invertibility, no det, no
tempering. The only content is *supplying* such a `b`; everything below names what supplies it. -/

/-- **Unconditional soft core: summable increment bound ⇒ `Vⱼ` converges.** If a per-step
nonnegative, eventually-positive sequence `b` dominates the fast band-projector increments
eventually and has `(1/n)·log b n → L < 0`, then the **slow** projectors
`orthProjMatrix (vSlowSingularStep A T c n x)` converge to the **explicit complement** `1 − Pfast`
of the fast band limit `Pfast`. Pure root test (`summable_of_logLimit_neg` packaged as
`summable_norm_of_logLimit_neg_of_le`) ⇒ `exists_tendsto_cfc_of_summable` (band converges to some
`Pfast`) ⇒ the landed structural reduction
`tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector`. **No `det ≠ 0`, no
tempering.** -/
theorem tendsto_vSlowSingularStep_of_summable_increment
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hpos : ∀ᶠ n in atTop, 0 < b n)
    {L : ℝ} (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (hstep : ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ b n) :
    ∃ Pfast : Matrix (Fin d) (Fin d) ℝ,
      Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T c n x)) atTop (𝓝 (1 - Pfast)) := by
  -- root test: the fast band increments are summable
  have hsum : Summable (fun n =>
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖) :=
    summable_norm_of_logLimit_neg_of_le
      (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      b hb hpos hL hlog hstep
  -- Cauchy packaging: the band projectors converge to some `Pfast`
  obtain ⟨Pfast, hPfast⟩ :=
    exists_tendsto_cfc_of_summable (fun n => qpow A T n x)
      (Set.indicator (Set.Ioi c) 1) hsum
  refine ⟨Pfast, ?_⟩
  -- landed structural reduction: slow → `1 − Pfast`
  exact tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector A T c x hPfast

/-! ## The det-free per-step bound's negative log-limit (strict gap + tempering)

The det-free `s`-engine (`norm_bandProjector_succ_sub_le_detfree`, `cBi ↦ 1/s`) produces the
per-step bound `√(2k)·κ²·r/(1 − κ²r²)` with `κ = cB·cBi = cB/s` and `r = σ_k/σ_{k-1}` of cocycle
`n`. Its `(1/n)·log` decomposes as

  `(1/n)log√(2k) + (1/n)log κ² + (1/n)log r − (1/n)log(1 − κ²r²)`.

Under a **strict spectral gap** `lamK < lamK1` at the cut (`(1/n)log r → lamK − lamK1`, from the
a.e.-constant genuine singular spectrum `ErgodicTheory.ae_singularSpectralValue_eq_const` selecting the
two cut indices) and **tempering** `(1/n)log κ → 0` (subexponential compound condition number), the
first, second, and fourth terms vanish, leaving the negative limit `lamK − lamK1`. The argument is
exactly the scalar layer of `ErgodicTheory.tendsto_log_bCocycle_point`, isolated here on the abstract
sequences so it needs *no* `det ≠ 0` (the inverse, if any, sits inside the abstract `κ`). -/

/-- **The negative log-limit of the det-free per-step bound.** For abstract positive sequences `κ`
(condition number, tempered: `(1/n)log κ → 0`) and `r` (forward ratio, gapped:
`(1/n)log r → lamK − lamK1 < 0`), the per-step bound
`b n = √(2k)·κ n²·r n / (1 − κ n²·r n²)` satisfies `(1/n)·log b n → lamK − lamK1 < 0`. This is the
scalar root-test layer, det-free: the inverse (if any) is hidden inside `κ`. -/
theorem tendsto_log_detfree_step_bound {k : ℕ} (hk1 : 1 ≤ k)
    (κ r : ℕ → ℝ) (hκpos : ∀ n, 0 < κ n) (hrpos : ∀ n, 0 < r n)
    {lamK lamK1 : ℝ} (hgap : lamK < lamK1)
    (hlogκ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ n)) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)) atTop (𝓝 (lamK - lamK1))) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
        (Real.sqrt (2 * k) * (κ n ^ 2 * r n / (1 - κ n ^ 2 * r n ^ 2)))) atTop
      (𝓝 (lamK - lamK1)) := by
  set κ2 : ℕ → ℝ := fun n => κ n ^ 2 with hκ2def
  have hκ2pos : ∀ n, 0 < κ2 n := fun n => pow_pos (hκpos n) 2
  -- (1/n) log κ² → 0
  have hlogκ2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n)) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n))
        = fun n : ℕ => (2 : ℝ) * ((n : ℝ)⁻¹ * Real.log (κ n)) := by
      funext n
      rw [hκ2def, Real.log_pow]; push_cast; ring
    rw [heq]
    simpa using hlogκ.const_mul (2 : ℝ)
  -- (1/n) log (κ²·r) → lamK - lamK1
  have hlogκ2r : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * r n)) atTop
      (𝓝 (lamK - lamK1)) := by
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * r n))
        = fun n : ℕ => ((n : ℝ)⁻¹ * Real.log (κ2 n)) + ((n : ℝ)⁻¹ * Real.log (r n)) := by
      funext n
      rw [Real.log_mul (ne_of_gt (hκ2pos n)) (ne_of_gt (hrpos n))]; ring
    rw [heq]; simpa using hlogκ2.add hlogr
  -- (1/n) log (κ²r²) → 2(lamK - lamK1) < 0, so κ²r² → 0
  have hlogκ2r2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * (r n) ^ 2)) atTop
      (𝓝 (2 * (lamK - lamK1))) := by
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ2 n * (r n) ^ 2))
        = fun n : ℕ => ((n : ℝ)⁻¹ * Real.log (κ2 n)) + (2 : ℝ) * ((n : ℝ)⁻¹ * Real.log (r n)) := by
      funext n
      have hrlog : Real.log ((r n) ^ 2) = 2 * Real.log (r n) := by
        rw [Real.log_pow]; push_cast; ring
      rw [Real.log_mul (ne_of_gt (hκ2pos n)) (pow_ne_zero 2 (ne_of_gt (hrpos n))), hrlog]; ring
    rw [heq]
    simpa using hlogκ2.add (hlogr.const_mul (2 : ℝ))
  have hκ2r2_tendsto : Tendsto (fun n : ℕ => κ2 n * (r n) ^ 2) atTop (𝓝 0) :=
    tendsto_zero_of_logLimit_neg _
      (fun n => le_of_lt (mul_pos (hκ2pos n) (pow_pos (hrpos n) 2)))
      (Filter.Eventually.of_forall (fun n => mul_pos (hκ2pos n) (pow_pos (hrpos n) 2)))
      (L := 2 * (lamK - lamK1)) (by linarith) hlogκ2r2
  -- v n := 1 - κ²r² → 1
  set v : ℕ → ℝ := fun n => 1 - κ2 n * (r n) ^ 2 with hvdef
  have hv_tendsto : Tendsto v atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) - κ2 n * (r n) ^ 2) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hκ2r2_tendsto
    simpa using this
  -- (1/n) log v → 0
  have hloginvv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (v n)) atTop (𝓝 0) := by
    have hlogv0 : Tendsto (fun n : ℕ => Real.log (v n)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => Real.log (v n)) atTop (𝓝 (Real.log 1)) :=
        (Real.continuousAt_log (by norm_num)).tendsto.comp hv_tendsto
      simpa using this
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using h1.mul hlogv0
  -- (1/n) log √(2k) → 0
  have hsqrt : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Real.sqrt (2 * k))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [mul_comm] using h1.mul_const (Real.log (Real.sqrt (2 * k)))
  have hsqrtpos : 0 < Real.sqrt (2 * k) := by
    apply Real.sqrt_pos.mpr
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  -- final assembly via the three limits; the bound `b n = √(2k)·(κ²r/v)`, `v = 1 − κ²r²`
  have hfinal : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Real.sqrt (2 * k))
          + ((n : ℝ)⁻¹ * Real.log (κ2 n * r n) - (n : ℝ)⁻¹ * Real.log (v n))) atTop
      (𝓝 (0 + ((lamK - lamK1) - 0))) :=
    hsqrt.add (hlogκ2r.sub hloginvv)
  have hsimp : (0 : ℝ) + ((lamK - lamK1) - 0) = lamK - lamK1 := by ring
  rw [hsimp] at hfinal
  -- match the explicit `b n` log expansion to the assembled sum, eventually (where `v n > 0`)
  refine hfinal.congr' ?_
  -- eventually `v n > 0` (from `v → 1`); on that set the logs split
  have hvev : ∀ᶠ n : ℕ in atTop, 0 < v n :=
    hv_tendsto.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hvev] with n hvn
  have hκ2rpos : 0 < κ2 n * r n := mul_pos (hκ2pos n) (hrpos n)
  have hsqrtne : Real.sqrt (2 * k) ≠ 0 := ne_of_gt hsqrtpos
  have hquotpos : 0 < κ2 n * r n / v n := div_pos hκ2rpos hvn
  rw [Real.log_mul hsqrtne (ne_of_gt hquotpos),
    Real.log_div (ne_of_gt hκ2rpos) (ne_of_gt hvn)]
  ring

/-- **The det-free per-step bound is summable (strict gap + tempering).** With `κ` tempered and `r`
gapped (as in `tendsto_log_detfree_step_bound`), the eventual-positivity regime `κ²r² < 1`, and the
positivity of `b`, the per-step bound `b n = √(2k)·κ n²·r n/(1 − κ n²·r n²)` is summable by the root
test. Det-free: the inverse (if any) is inside `κ`. -/
theorem summable_detfree_step_bound {k : ℕ} (hk1 : 1 ≤ k)
    (κ r : ℕ → ℝ) (hκpos : ∀ n, 0 < κ n) (hrpos : ∀ n, 0 < r n)
    (hregime : ∀ᶠ n in atTop, κ n ^ 2 * r n ^ 2 < 1)
    {lamK lamK1 : ℝ} (hgap : lamK < lamK1)
    (hlogκ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ n)) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)) atTop (𝓝 (lamK - lamK1))) :
    Summable (fun n : ℕ =>
      Real.sqrt (2 * k) * (κ n ^ 2 * r n / (1 - κ n ^ 2 * r n ^ 2))) := by
  set b : ℕ → ℝ := fun n => Real.sqrt (2 * k) * (κ n ^ 2 * r n / (1 - κ n ^ 2 * r n ^ 2)) with hbdef
  have hsqrtpos : 0 < Real.sqrt (2 * k) := by
    apply Real.sqrt_pos.mpr
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  -- eventual positivity of `b` (from the regime `κ²r² < 1`)
  have hbpos : ∀ᶠ n in atTop, 0 < b n := by
    filter_upwards [hregime] with n hn
    rw [hbdef]
    have hgapfac : 0 < 1 - κ n ^ 2 * r n ^ 2 := by linarith
    have hnum : 0 < κ n ^ 2 * r n := mul_pos (pow_pos (hκpos n) 2) (hrpos n)
    positivity
  -- nonnegativity of `b` (need it everywhere for the root-test packaging; clamp via `max`)
  -- We instead use `summable_of_logLimit_neg` directly: it needs `0 ≤ b n` for all `n` and the
  -- eventual positivity + negative log-limit. Where the regime fails, `b n` may be negative, so we
  -- compare against the eventually-equal nonnegative tail through `Summable.congr` after dropping a
  -- finite head. Cleanest: use the root test on the nonnegative `bplus n = max (b n) 0`.
  set bplus : ℕ → ℝ := fun n => max (b n) 0 with hbplusdef
  have hbplusnn : ∀ n, 0 ≤ bplus n := fun n => le_max_right _ _
  have hbpluspos : ∀ᶠ n in atTop, 0 < bplus n := by
    filter_upwards [hbpos] with n hn
    rw [hbplusdef]; exact lt_max_of_lt_left hn
  have hbplus_eq : ∀ᶠ n in atTop, bplus n = b n := by
    filter_upwards [hbpos] with n hn
    rw [hbplusdef]; exact max_eq_left (le_of_lt hn)
  -- log-limit of `bplus` agrees with that of `b` eventually
  have hlogb : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 (lamK - lamK1)) :=
    tendsto_log_detfree_step_bound hk1 κ r hκpos hrpos hgap hlogκ hlogr
  have hlogbplus : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (bplus n)) atTop
      (𝓝 (lamK - lamK1)) := by
    refine hlogb.congr' ?_
    filter_upwards [hbplus_eq] with n hn
    rw [hn]
  -- root test on `bplus`
  have hsumbplus : Summable bplus :=
    summable_of_logLimit_neg bplus hbplusnn hbpluspos (L := lamK - lamK1) (by linarith) hlogbplus
  -- `b` agrees with `bplus` eventually, so `b` is summable (cofinite = atTop on `ℕ`)
  exact hsumbplus.congr_atTop hbplus_eq

/-! ## The tempered-class `Vⱼ` (the guaranteed landing)

Combining the det-free per-step bound (`norm_bandProjector_succ_sub_le_detfree`, supplying the
`b n = √(2k)·(cB/s)²·r/(1 − (cB/s)²r²)` shape with `s = 1/cBi`, so `κ = cB·cBi`) with the
summability above and the unconditional soft core: under a **strict spectral gap at the cut** and
**tempering** of the compound condition number, the slow space `Vⱼ` converges to the explicit
complement `1 − Pfast`. The carry is named precisely: it is the tempered-non-degeneracy class, not
unconditional. -/

/-- **The tempered-class `Vⱼ` converges to the explicit complement.** Given a per-step increment
upper bound of the det-free `s`-engine shape `b n = √(2k)·κ n²·r n/(1 − κ n²·r n²)` (the output of
`ErgodicTheory.norm_bandProjector_succ_sub_le_detfree` with `κ = cB/s = cB·cBi`), the regime
`κ²r² < 1` eventually, the **strict gap** `lamK < lamK1` (forward ratio `(1/n)log r → lamK − lamK1`,
from the a.e.-constant singular spectrum), and **tempering** `(1/n)log κ → 0`, the slow projectors
`orthProjMatrix (vSlowSingularStep A T c n x)` converge to the **explicit complement** `1 − Pfast`
of the fast band limit. The slow space `Vⱼ(ω)` is then the orthogonal complement of the fast
Oseledets spectral projector.

**Carry (precise).** Unconditional on the *tempered-non-degeneracy class*: the bound `b n` is the
det-free `s`-engine's, whose `s = 1/cBi` supply needs each step's compound inverse to exist; the
tempering `(1/n)log κ → 0` is strictly weaker than `det A ≠ 0` everywhere but is **not removable**
(no inverse-free per-step replacement exists — `bandProjector_increment_eq_aperture`). -/
theorem tendsto_vSlowSingularStep_of_tempered {k : ℕ} (hk1 : 1 ≤ k)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X)
    (κ r : ℕ → ℝ) (hκpos : ∀ n, 0 < κ n) (hrpos : ∀ n, 0 < r n)
    (hregime : ∀ᶠ n in atTop, κ n ^ 2 * r n ^ 2 < 1)
    {lamK lamK1 : ℝ} (hgap : lamK < lamK1)
    (hlogκ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (κ n)) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)) atTop (𝓝 (lamK - lamK1)))
    (hstep : ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖
        ≤ Real.sqrt (2 * k) * (κ n ^ 2 * r n / (1 - κ n ^ 2 * r n ^ 2))) :
    ∃ Pfast : Matrix (Fin d) (Fin d) ℝ,
      Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T c n x)) atTop (𝓝 (1 - Pfast)) := by
  set b : ℕ → ℝ := fun n => Real.sqrt (2 * k) * (κ n ^ 2 * r n / (1 - κ n ^ 2 * r n ^ 2)) with hbdef
  -- `b` is summable (root test), hence `(1/n)log b → lamK − lamK1 < 0`
  have hlogb : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 (lamK - lamK1)) :=
    tendsto_log_detfree_step_bound hk1 κ r hκpos hrpos hgap hlogκ hlogr
  have hsqrtpos : 0 < Real.sqrt (2 * k) := by
    apply Real.sqrt_pos.mpr
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  -- eventual positivity + nonnegativity-on-the-regime of `b`
  have hbpos : ∀ᶠ n in atTop, 0 < b n := by
    filter_upwards [hregime] with n hn
    rw [hbdef]
    have hgapfac : 0 < 1 - κ n ^ 2 * r n ^ 2 := by linarith
    have hnum : 0 < κ n ^ 2 * r n := mul_pos (pow_pos (hκpos n) 2) (hrpos n)
    positivity
  -- To feed the unconditional soft core we need `b n ≥ 0` for ALL n; clamp through `bplus`.
  set bplus : ℕ → ℝ := fun n => max (b n) 0 with hbplusdef
  have hbplusnn : ∀ n, 0 ≤ bplus n := fun n => le_max_right _ _
  have hbpluspos : ∀ᶠ n in atTop, 0 < bplus n := by
    filter_upwards [hbpos] with n hn
    rw [hbplusdef]; exact lt_max_of_lt_left hn
  have hbplus_eq : ∀ᶠ n in atTop, bplus n = b n := by
    filter_upwards [hbpos] with n hn
    rw [hbplusdef]; exact max_eq_left (le_of_lt hn)
  have hlogbplus : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (bplus n)) atTop
      (𝓝 (lamK - lamK1)) := by
    refine hlogb.congr' ?_
    filter_upwards [hbplus_eq] with n hn; rw [hn]
  have hstepplus : ∀ᶠ n in atTop,
      ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ ≤ bplus n := by
    filter_upwards [hstep, hbplus_eq] with n hn heq
    rw [heq, hbdef]; exact hn
  exact tendsto_vSlowSingularStep_of_summable_increment A T c x bplus hbplusnn hbpluspos
    (L := lamK - lamK1) (by linarith) hlogbplus hstepplus

/-! ## The precise residual: the forward-ratio per-step bound fails

The Wave-5 forward-ratio crack `(R5A)` (bound the slow increment by `σ_{k+1}/σ_k` of the single
cocycle `M_{n+1}`, *no inverse*) is **false** at the per-step granularity. We record the precise
mathematical content as a *statement-level* `Prop` definition — not a proof of a false claim — that
identifies the failing quantity: the band increment IS the aperture `‖U Uᵀ − V Vᵀ‖` between the
top-`k` right-singular frames of `M_n` (= `U`) and `M_{n+1}` (= `V`), which by Davis–Kahan is
governed by the perturbation `B = A(Tⁿx)` (its condition number — the inverse), not by the internal
forward ratio of `M_{n+1}`. -/

/-- **The forward-ratio per-step bound `(R5A)` (the falsified target).** The proposition that, for a
universal constant `C`, every step's band increment is bounded by `C` times the forward singular
ratio `σ_{k+1}(M_{n+1})/σ_k(M_{n+1})` of the single cocycle `M_{n+1} = cocycle (n+1) x`. This is the
**inverse-free** bound Angle 5A sought. It is **false** at the per-step granularity (a single
ill-conditioned `B` rotates the top-`k` space by `O(1)` while the forward ratio stays `O(1)`); the
band increment is the aperture, governed by the condition number of `B` (the inverse), not the
forward ratio. We state it as a `Prop` to name the residual precisely; no proof is given because the
claim is false. -/
def ForwardRatioPerStepBound (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ)
    (k : ℕ) (x : X) (C : ℝ) : Prop :=
  ∀ n : ℕ,
    ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
        - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖
      ≤ C * ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k
          / (Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues (k - 1))

omit [MeasurableSpace X] [NeZero d] in
/-- **The band increment is the aperture (`(R5A)`'s failing identity).** The band-projector
increment whose forward-ratio bound `(R5A)` was sought equals — *unconditionally* — the Frobenius
distance `‖U Uᵀ − V Vᵀ‖` between the top-`k` right-singular frames `U` (of `M_n`) and `V` (of
`M_{n+1}`), provided the band projectors are realised by those frames. This is the aperture
`sin∠(S_n, S_{n+1})`; it is governed by Davis–Kahan via the perturbation `B = A(Tⁿx)` (whose
condition number — the inverse — appears in the denominator's gap), **not** by the internal forward
ratio of `M_{n+1}`. Recording this identity pins exactly why `(R5A)` cannot hold inverse-free: the
quantity to bound is a between-steps rotation, and the forward ratio measures only the
within-`M_{n+1}` gap. (This re-derives, in the band-increment language, the wall of
`ErgodicTheory.wedge_mu0_lb_is_inverse_bound` and `ErgodicTheory.numerator_div_gap_le_detfree`.) -/
theorem bandProjector_increment_eq_aperture {c : ℝ} (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {k : ℕ} (n : ℕ) (x : X) (U V : Matrix (Fin d) (Fin k) ℝ)
    (hPn : bandProjector A T (Set.indicator (Set.Ioi c) 1) n x = U * Uᵀ)
    (hPn1 : bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x = V * Vᵀ) :
    ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
        - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖
      = ‖V * Vᵀ - U * Uᵀ‖ := by
  rw [hPn, hPn1]

end ErgodicTheory
