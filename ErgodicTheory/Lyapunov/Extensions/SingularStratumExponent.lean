/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Forward
import ErgodicTheory.Lyapunov.Extensions.SingularLambdaBarFiltration

/-!
# The exact per-stratum per-direction exponent of the singular Lyapunov filtration

For a **possibly-singular** matrix cocycle generator `A : X → Matrix (Fin d) (Fin d) ℝ` (no
`det A ≠ 0`, no inverse integrability) the forward filtration is the algebraic sublevel filtration
`Vⱼ(x) = ErgodicTheory.lambdaBarSublevel A T c x` of the upper Lyapunov exponent
`lambdaBar A T x v = limsup_n (1/n)·log‖A⁽ⁿ⁾(x)·v‖`
(`ErgodicTheory/Lyapunov/Extensions/SingularLambdaBarFiltration.lean`). This module proves the
**exact per-direction growth law on each stratum**: for a vector `v` lying *exactly* on the
`j`-th band of the filtration — `v ∈ Vⱼ \ Vⱼ₊₁`, captured here as `v ∈ lambdaBarSublevel A T c x`
together with `v ∉ lambdaBarSublevel A T c' x` for the next lower cut `c'` (and `v ≠ 0`) — the
normalized log-growth sequence converges *exactly* to the stratum exponent,
**not** merely between bounds:

`Tendsto (fun n => (1/n)·log‖A⁽ⁿ⁾(x)·v‖) atTop (𝓝 (λⱼ x))`.

## The two halves of the squeeze (the upper half is det-free; the lower half is the wall)

The exact limit is a `liminf = limsup` squeeze:

* **Upper half (`limsup ≤ c`), unconditional and det-free.** Membership `v ∈ lambdaBarSublevel
  A T c x` at a nonnegative cut `c ≥ 0` is exactly `lambdaBar A T x v ≤ c`
  (`ErgodicTheory.mem_lambdaBarSublevel_iff`), i.e. `limsup (1/n)·log‖A⁽ⁿ⁾ v‖ ≤ c`. No invertibility,
  no integrability, no band-projector convergence — it is *built into* the filtration's definition.

* **Lower half (`c ≤ liminf`), from the fast band projector at the cut.** Supplied by the det-free
  analytic core `ErgodicTheory.cocycle_apply_sq_ge_band` (`cᵘⁿ‖Pᶜₙ v‖² ≤ ‖A⁽ⁿ⁾ v‖²`, no `det`
  hypothesis): if the fast band projectors at threshold `e^c` converge to a limit `P` with `P v ≠ 0`
  (the spectral identification that `v` has a genuine component above the cut), then
  `log e^c = c ≤ liminf (1/n)·log‖A⁽ⁿ⁾ v‖`. This module re-derives that lower bound **without** the
  invertibility hypothesis carried by the invertible engine
  (`ErgodicTheory.log_le_liminf_log_cocycle_apply`): the only place `det A ≠ 0` was used there
  (`cocycle_apply_ne_zero`, to get `‖A⁽ⁿ⁾ v‖ > 0`) is replaced by the band bound itself, which
  forces `‖A⁽ⁿ⁾ v‖² ≥ cᵘⁿ‖Pᶜₙ v‖² > 0` eventually.

The band-projector convergence datum `hP, hPv` is exactly the genuine residual of the singular
forward filtration (the wall `(R)` pinned in `SingularBandConverge.lean` and
`SingularSlowSpaceUnconditional.lean`): for a singular cocycle it is *not* unconditional, but is
guaranteed on the tempered class (`ErgodicTheory.tendsto_vSlowSingularStep_of_tempered`). We therefore
take it — together with the two-sided Furstenberg–Kesten boundedness `hbdd` — as the explicit
hypotheses of the exact law, exactly as the invertible engine
(`ErgodicTheory.tendsto_inv_mul_log_norm_cocycle_apply_of_bandProjector`) does. The headline is then a
clean, sorry-free, det-free squeeze.

## Main results

* `ErgodicTheory.log_le_liminf_log_cocycle_apply_detfree` — the **det-free** per-vector liminf lower
  bound `log c ≤ liminf (1/n)·log‖A⁽ⁿ⁾ v‖` from band-projector convergence at the cut `c > 0`. No
  invertibility.
* `ErgodicTheory.singular_perDirection_exponent_eq_lambda_of_mem_stratum` — **the headline**: the exact
  per-stratum per-direction growth limit `Tendsto (fun n => (1/n)·log‖A⁽ⁿ⁾ v‖) atTop (𝓝 c)` for a
  vector exactly on the `c`-stratum of the singular sublevel filtration (`v ∈ lambdaBarSublevel
  A T c x`, `v ≠ 0`) with a fast band projector converging non-trivially at the cut.
* `ErgodicTheory.lambdaBar_eq_of_mem_stratum` — the user-facing corollary tying the measurable
  filtration to the exact exponent: under the same hypotheses, `lambdaBar A T x v = c` *and* the
  full sequence (not just its `limsup`) converges to `c`.

## References

* A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1).
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*, Publ. Math. IHÉS **50** (1979),
  27–58 (Lemma 1.4).
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ### The det-free per-vector liminf lower bound

The invertible liminf engine `ErgodicTheory.log_le_liminf_log_cocycle_apply` carries
`hA : ∀ x, (A x).det ≠ 0` only to guarantee `‖A⁽ⁿ⁾ v‖ > 0` (`cocycle_apply_ne_zero`). For a
singular cocycle that positivity is instead *forced by the band bound*
`ErgodicTheory.cocycle_apply_sq_ge_band`: where the band projection `‖Pᶜₙ v‖` is positive (eventually,
since it converges to `‖P v‖ > 0`), the bound `cᵘⁿ‖Pᶜₙ v‖² ≤ ‖A⁽ⁿ⁾ v‖²` with `c > 0` makes
`‖A⁽ⁿ⁾ v‖ > 0`. So we re-derive the eventual lower bound and the `liminf` bound **det-free**. -/

/-- **Det-free eventual per-vector lower bound.** If the fast band projectors for `(c,∞)` (with
`c > 0`) converge to `P` with `P v ≠ 0`, then *eventually*
`log c + (1/n)·log‖Pᶜₙ v‖ ≤ (1/n)·log‖A⁽ⁿ⁾ v‖`. No invertibility: positivity of `‖A⁽ⁿ⁾ v‖` is
forced by the det-free band bound `ErgodicTheory.cocycle_apply_sq_ge_band` (since the band projection
norm is eventually positive and `c > 0`). -/
theorem log_add_correction_le_inv_mul_log_cocycle_apply_detfree [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {c : ℝ} (hc : 0 < c) {x : X} {P : Matrix (Fin d) (Fin d) ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      Real.log c + (n : ℝ)⁻¹ * Real.log
          ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖
        ≤ (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
  -- band projection applied to `v` converges to `P v ≠ 0`, hence eventually nonzero.
  set evalLin : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.applyₗ v) ∘ₗ (Matrix.toEuclideanLin).toLinearMap with heval
  have hcont : Continuous evalLin := evalLin.continuous_of_finiteDimensional
  have htendBand : Tendsto
      (fun n => Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v)
      atTop (𝓝 (Matrix.toEuclideanLin P v)) := by
    have := (hcont.tendsto P).comp hP
    simpa [heval, Function.comp_def] using this
  have hL : (0 : ℝ) < ‖Matrix.toEuclideanLin P v‖ := norm_pos_iff.mpr hPv
  have hbandpos : ∀ᶠ n in atTop,
      0 < ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ := by
    have hnorm := htendBand.norm
    have : ∀ᶠ n in atTop,
        ‖Matrix.toEuclideanLin P v‖ / 2 <
          ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ :=
      hnorm.eventually_const_lt (by linarith)
    filter_upwards [this] with n hn
    linarith [hn, half_pos hL]
  filter_upwards [eventually_ge_atTop 1, hbandpos] with n hn1 hbpos
  -- the det-free band bound `cᵘⁿ ‖Pᶜₙ v‖² ≤ ‖A⁽ⁿ⁾ v‖²`.
  have hband := cocycle_apply_sq_ge_band A T hn1 x (le_of_lt hc) v
  set b := ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖
  set M := ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
  -- positivity of `M` is forced by the band bound (det-free): `cᵘⁿ b² ≤ M²` with `cᵘⁿ b² > 0`.
  have hlhs_pos : 0 < c ^ (2 * (n : ℝ)) * b ^ 2 := by
    have : 0 < c ^ (2 * (n : ℝ)) := Real.rpow_pos_of_pos hc _
    positivity
  have hMsq_pos : 0 < M ^ 2 := lt_of_lt_of_le hlhs_pos hband
  -- take logs of `cᵘⁿ b² ≤ M²`.
  have hlog_le : Real.log (c ^ (2 * (n : ℝ)) * b ^ 2) ≤ Real.log (M ^ 2) :=
    Real.log_le_log hlhs_pos hband
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hc _)) (by positivity),
    Real.log_rpow hc, Real.log_pow, Real.log_pow] at hlog_le
  push_cast at hlog_le
  rw [← sub_nonneg]
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hexpand : (n : ℝ)⁻¹ * Real.log M - (Real.log c + (n : ℝ)⁻¹ * Real.log b)
      = (n : ℝ)⁻¹ * (Real.log M - Real.log b - (n : ℝ) * Real.log c) := by
    field_simp
    ring
  rw [hexpand]
  apply mul_nonneg (le_of_lt hninv)
  nlinarith [hlog_le]

/-- **Det-free per-vector liminf lower bound.** If the fast band projectors for `(c,∞)` (with
`c > 0`) converge to `P` with `P v ≠ 0`, then `log c ≤ liminf (1/n)·log‖A⁽ⁿ⁾ v‖`. **No
invertibility** (the det-free analogue of `ErgodicTheory.log_le_liminf_log_cocycle_apply`): combines the
det-free eventual lower bound `log c + (1/n)·log‖Pᶜₙ v‖ ≤ (1/n)·log‖A⁽ⁿ⁾ v‖` (whose left side tends
to `log c`, the band correction vanishing by
`ErgodicTheory.tendsto_inv_mul_log_norm_bandProjector_apply`) with `liminf` monotonicity. The cobounded
side condition is the hypothesis `hcobdd`, supplied a.e. by Furstenberg–Kesten. -/
theorem log_le_liminf_log_cocycle_apply_detfree [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {c : ℝ} (hc : 0 < c) {x : X} {P : Matrix (Fin d) (Fin d) ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0)
    (hcobdd : atTop.IsCoboundedUnder (· ≥ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    Real.log c ≤ liminf
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop := by
  have hcorr := tendsto_inv_mul_log_norm_bandProjector_apply A T hP hPv
  set LHS : ℕ → ℝ := fun n ↦ Real.log c + (n : ℝ)⁻¹ * Real.log
      ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖
    with hLHS
  set RHS : ℕ → ℝ := fun n =>
      (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
  have hLHStend : Tendsto LHS atTop (𝓝 (Real.log c)) := by
    have := (tendsto_const_nhds (x := Real.log c) (f := atTop (α := ℕ))).add hcorr
    simpa [hLHS] using this
  have hineq : ∀ᶠ n in atTop, LHS n ≤ RHS n :=
    log_add_correction_le_inv_mul_log_cocycle_apply_detfree A T hc hP hPv
  have hLHSbdd : atTop.IsBoundedUnder (· ≥ ·) LHS := hLHStend.isBoundedUnder_ge
  calc Real.log c = liminf LHS atTop := hLHStend.liminf_eq.symm
    _ ≤ liminf RHS atTop := Filter.liminf_le_liminf hineq hLHSbdd hcobdd

/-! ### The exact per-stratum per-direction exponent -/

/-- **The exact per-stratum per-direction singular Lyapunov exponent.** Let `A` be a (possibly
**singular**) cocycle generator over `T`, `c` a stratum cut **gated to be nonnegative** (`0 ≤ c` —
the lower-half band bound below uses `Real.exp c` at threshold `c`, valid only for `c ≥ 0`), and
`v ≠ 0` a vector lying on the `c`-stratum of the singular sublevel filtration, i.e.
`v ∈ lambdaBarSublevel A T c x` (so its upper exponent `lambdaBar A T x v ≤ c`) with the fast band
projectors at the cut `e^c` converging to a limit `P` for which `P v ≠ 0` (the spectral
identification that `v` has a genuine component above the cut — equivalently `v ∉` the strictly
lower stratum). Then the normalized log-growth sequence converges **exactly** to the stratum
exponent:

`Tendsto (fun n => (1/n)·log‖A⁽ⁿ⁾(x)·v‖) atTop (𝓝 c)`.

The **achievement is the exactness**: this is a genuine two-sided `Tendsto` to `c`, not a one-sided
`≤`/`≥` bound. The limit value is the caller-supplied cut `c` itself, which **is** the exact
per-direction exponent `lambdaBar A T x v` of `v` on that stratum (the user-facing corollary
`ErgodicTheory.lambdaBar_eq_of_mem_stratum` reads off `lambdaBar A T x v = c`).

**Scope of the statement.** This is **pointwise at the single `x`** and **conditional** on the
band-projector datum (`hP`, `hPv`) and the two-sided boundedness hypotheses (`hbddabove`,
`hbddbelow`): there is **no measure and no `∀ᵐ x`** in the statement. The customary "a.e."
qualifier is not part of this lemma — it enters only because the conditional band datum is
*guaranteed on the tempered class* by `ErgodicTheory.tendsto_vSlowSingularStep_of_tempered`, and the
boundedness is supplied a.e. by Furstenberg–Kesten for an integrable generator.

The upper half `limsup ≤ c` is the membership `v ∈ lambdaBarSublevel A T c x` itself
(`ErgodicTheory.mem_lambdaBarSublevel_iff`, det-free). The lower half `c ≤ liminf` is the det-free band
bound `ErgodicTheory.log_le_liminf_log_cocycle_apply_detfree` at threshold `e^c`. The two-sided
boundedness hypotheses squeeze the two into a genuine limit
(`ErgodicTheory.tendsto_inv_mul_log_norm_cocycle_apply`). **No `det A ≠ 0`, no inverse integrability.**
The band-projector convergence `hP, hPv` is the genuine residual of the singular forward filtration,
guaranteed on the tempered class (`ErgodicTheory.tendsto_vSlowSingularStep_of_tempered`). -/
theorem singular_perDirection_exponent_eq_lambda_of_mem_stratum [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {c : ℝ} (hc : 0 ≤ c) {x : X} (hx : HasFiniteTopGrowth A T x)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (hmem : v ∈ lambdaBarSublevel A T c x hx)
    {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi (Real.exp c)) 1) n x)
      atTop (𝓝 P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0)
    (hbddabove : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hbddbelow : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
      atTop (𝓝 c) := by
  -- Upper half: membership at a nonnegative cut is `lambdaBar A T x v ≤ c`, i.e. `limsup ≤ c`.
  have hub : lambdaBar A T x v ≤ c := by
    rcases (mem_lambdaBarSublevel_iff A T hc x hx v).mp hmem with rfl | hle
    · exact absurd rfl hv
    · exact hle
  have hsup : limsup (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ c := by
    -- `lambdaBar` is the same `limsup`, stated with `toEuclideanCLM` (defeq to `toEuclideanLin`).
    have hcoe : ∀ n : ℕ, Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v
        = Matrix.toEuclideanLin (cocycle A T n x) v := by
      intro n; rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
    rw [lambdaBar] at hub
    simp_rw [hcoe] at hub
    exact hub
  -- Lower half: the det-free band liminf bound at threshold `e^c` (`log e^c = c`).
  have hcpos : (0 : ℝ) < Real.exp c := Real.exp_pos c
  have hcobdd : atTop.IsCoboundedUnder (· ≥ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) :=
    hbddabove.isCoboundedUnder_ge
  have hlow := log_le_liminf_log_cocycle_apply_detfree A T hcpos hP hPv hcobdd
  rw [Real.log_exp] at hlow
  -- Squeeze `limsup ≤ c ≤ liminf` into a genuine limit.
  exact tendsto_inv_mul_log_norm_cocycle_apply T A x v c hsup hlow hbddabove hbddbelow

/-- **User-facing corollary: the measurable filtration carries the exact per-stratum exponent.**
Under the hypotheses of `ErgodicTheory.singular_perDirection_exponent_eq_lambda_of_mem_stratum`, a
vector exactly on the `c`-stratum of the singular sublevel filtration (a.e.-measurable, by
`ErgodicTheory.aemeasurable_orthProjMatrix_lambdaSublevel`) has its **full**
normalized log-growth sequence — not just its `limsup` — converging to `c`, and consequently its
upper Lyapunov exponent equals the stratum cut exactly: `lambdaBar A T x v = c`. This is the
det-free singular analogue of the invertible MET's per-stratum growth law
`ErgodicTheory.oseledets_filtration`. -/
theorem lambdaBar_eq_of_mem_stratum [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {c : ℝ} (hc : 0 ≤ c) {x : X} (hx : HasFiniteTopGrowth A T x)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (hmem : v ∈ lambdaBarSublevel A T c x hx)
    {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi (Real.exp c)) 1) n x)
      atTop (𝓝 P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0)
    (hbddabove : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hbddbelow : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    lambdaBar A T x v = c := by
  have htend := singular_perDirection_exponent_eq_lambda_of_mem_stratum A T hc hx hv hmem hP hPv
    hbddabove hbddbelow
  -- `lambdaBar` is the `limsup`, equal to the limit of a convergent sequence.
  have hcoe : ∀ n : ℕ, Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v
      = Matrix.toEuclideanLin (cocycle A T n x) v := by
    intro n; rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
  rw [lambdaBar]
  simp_rw [hcoe]
  exact htend.limsup_eq

end ErgodicTheory
