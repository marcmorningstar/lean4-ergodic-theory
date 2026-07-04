/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.OseledetsLimit.ProjectorIncrement
import Oseledets.Lyapunov.Extensions.SingularSubspaceDist
import Oseledets.Lyapunov.SpectralMeasurable

/-!
# The intermediate slow space `Vⱼ` of the singular forward flag — det-free structural reduction

This module constructs the finite-step approximants of an intermediate **slow space** `Vⱼ(ω)` of the
singular (non-invertible) Oseledets forward filtration (Quas, *Multiplicative Ergodic Theorems and
Applications*, 2013, **Theorem 2**; Ruelle, Publ. IHES 50, 1979, **Lemma 1.4**), and reduces its
convergence — **det-free, unconditionally** — to the convergence of the *fast* band projector
`Oseledets.bandProjector`.

It promotes the reusable structural lemmas of the Wave-2 de-risk scratch
(`Oseledets.Lyapunov.Extensions.SingularSlowSpaceCauchyScratch`) from the **fixed raw-Gram
threshold** (which is *not* Cauchy — threshold-scale mismatch) to the **`qpow` / Lyapunov-scale
cut** (the cut at which the existing fast engine actually converges), defining the slow space as the
orthogonal **complement** of the fast band at a Lyapunov gap value `c`.

## The construction

The `n`-step slow approximant at a Lyapunov gap value `c` is

  `vSlowSingularStep A T c n x` := the range of `1 − bandProjector A T (𝟙_{(c,∞)}) n x`,

the orthogonal complement of the **fast** band (the span of `qpow` eigenvectors with eigenvalue
`> c`). Equivalently it is the span of the `qpow` eigenvectors with eigenvalue `≤ c`, i.e. the
singular directions with `σᵢ(cocycle n x)^{1/n} ≤ exp c` (the *slow / Lyapunov-subthreshold* side).

## The structural finding (det-free, unconditional)

Because `bandProjector` is a self-adjoint idempotent (`bandProjector_isSelfAdjoint`,
`bandProjector_indicator_mul_self`), its complement `1 − bandProjector` is again a self-adjoint
idempotent, and `orthProjMatrix (vSlowSingularStep …) = 1 − bandProjector …`
(`orthProjMatrix_vSlowSingularStep`). The two `1`s then cancel in the consecutive-step difference,
so the **slow** projector increments equal — *in operator norm* — the **fast** band increments:

  `‖P_slow(n+1) − P_slow(n)‖ = ‖bandProjector(n+1) − bandProjector(n)‖`
    (`norm_vSlowSingularStep_proj_succ_sub_eq_band`).

Hence summability of the slow increments is **definitionally** the summability of the fast
increments (`summable_vSlowSingularStep_increment_iff_band`), and feeding it through Wave-1's
`exists_tendsto_orthProjMatrix_of_summable` produces the limit slow projector
(`exists_tendsto_orthProjMatrix_vSlowSingularStep_of_summable`). No invertibility, no separate
small-σ leakage bound: the det-free `norm_proj_sub_le_wedge` engine that bounds the *fast* band
increments controls the *slow* projector increments verbatim.

This is the genuine advance over the scratch: the cut is now the **moving** Lyapunov cut, at which
the fast band increments are the very increments the existing engine
(`norm_bandProjector_succ_sub_le` ⇒ `exists_tendsto_bandProjector`) makes summable — so the slow
space converges along exactly the same a.e. set.

## The wall (precisely pinned; the honest stopping point of Track 3B)

The structural reduction above is **unconditional**. What it reduces *to* — the summable fast-band
increments — is supplied by `exists_tendsto_bandProjector` (which takes the per-step bound as a
hypothesis) only after the per-step bound is *discharged*, and the unconditional cocycle discharge
`exists_tendsto_bandProjector_cocycle` (via `norm_bandProjector_succ_sub_le_cocycle`) **requires
invertibility** `hA : ∀ x, (A x).det ≠ 0`.

The invertibility is load-bearing in **exactly one** estimate, the *rank-1 lower bound on the
perturbed top eigenvalue* `μ̃₀ ≥ cM²/cBi²`
(`Oseledets.ExteriorNorm.norm_sq_compound_mul_ge` / `…rayleigh_deficit_le`), whose only route uses
the compound *inverse* `cBi = ‖compound k (A(Tⁿx))⁻¹‖` through the factorisation
`compound k M = compound k B⁻¹ · compound k (B·M)` (`compoundMatrix_eq_inv_mul`). That bound is
what makes the spectral-gap denominator `μ̃₀ − ν` of the Davis–Kahan sin-Θ step positive and large
enough for the increment to decay. The det-free `RuelleCore` engine (`SVDData.oneStep_sandwich`,
the leakage chain) only delivers a one-sided **upper** mass envelope (a `limsup` spectral bound on
a *fixed* slow space, e.g. `Oseledets.limsup_le_of_mem_vslow`); it does **not** lower-bound the
perturbed top eigenvalue, hence cannot, by itself, bound the *projector increment* / aperture
distance that the Cauchy construction of `Vⱼ` consumes. See the `cruxStatus` of the report.

So this module lands the full unconditional structural reduction (definition, complement bridge,
increment identity, summability transfer, conditional limit, measurability, antitone flag) and names
the single remaining input — and its single invertibility-using estimate — precisely.

## Main definitions

* `Oseledets.vSlowSingularStep` — the `n`-step slow approximant (range of `1 − bandProjector`).

## Main results (all sorry-free, all det-free / unconditional)

* `Oseledets.orthProjMatrix_vSlowSingularStep` — the complement bridge
  `orthProjMatrix (vSlowSingularStep …) = 1 − bandProjector …`.
* `Oseledets.norm_vSlowSingularStep_proj_succ_sub_eq_band` — slow increment = fast band increment
  in norm.
* `Oseledets.summable_vSlowSingularStep_increment_iff_band` — summability transfer (definitional).
* `Oseledets.exists_tendsto_orthProjMatrix_vSlowSingularStep_of_summable` — the limit slow projector
  from summable fast-band increments (the `Vⱼ` construction crux, *given* the fast summability).
* `Oseledets.measurableSubspace_vSlowSingularStep` — measurability of each `n`-step slow space.
* `Oseledets.vSlowSingularStep_antitone` — the `n`-step slow spaces are **antitone** in the cut `c`
  (a larger Lyapunov threshold admits more slow directions): the finite-step flag.
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder

noncomputable section

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]

/-! ## The complement-projector algebra at the `qpow` (Lyapunov) cut

The fast band `bandProjector A T (𝟙_{(c,∞)}) n x = cfc (𝟙_{(c,∞)}) (qpow A T n x)` is a self-adjoint
idempotent (unconditionally — `bandProjector_isSelfAdjoint`, `bandProjector_indicator_mul_self`). We
record that its complement `1 − bandProjector` is one too; this is the `qpow`-scale analogue of the
scratch's raw-Gram `cfc_indicator_Iic_eq_one_sub_Ioi`, but stated directly on the band projector so
it composes with the existing convergence engine. -/

/-- The complement `1 − bandProjector A T (𝟙_{(c,∞)}) n x` of the fast band is **self-adjoint**: the
difference of the self-adjoint identity and the self-adjoint band projector. -/
theorem isSelfAdjoint_one_sub_bandProjector (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ)
    (n : ℕ) (x : X) :
    IsSelfAdjoint (1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) :=
  (IsSelfAdjoint.one (R := Matrix (Fin d) (Fin d) ℝ)).sub
    (bandProjector_isSelfAdjoint A T (Set.indicator (Set.Ioi c) 1) n x)

/-- The complement `1 − bandProjector A T (𝟙_{(c,∞)}) n x` of the fast band is **idempotent**:
`(1 − P)² = 1 − 2P + P² = 1 − P` since `P² = P` (`bandProjector_indicator_mul_self`). -/
theorem one_sub_bandProjector_mul_self (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ)
    (n : ℕ) (x : X) :
    (1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
        * (1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      = 1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x := by
  set P := bandProjector A T (Set.indicator (Set.Ioi c) 1) n x with hP
  have hPP : P * P = P := bandProjector_indicator_mul_self A T n x
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hPP]
  abel

/-! ## The `n`-step slow approximant and the complement bridge -/

/-- The **`n`-step slow approximant** at the Lyapunov gap value `c`: the range of the complement
`1 − bandProjector A T (𝟙_{(c,∞)}) n x` of the fast band, transported to a subspace of
`EuclideanSpace ℝ (Fin d)`. It is the orthogonal complement of the span of the `qpow` eigenvectors
with eigenvalue `> c`, i.e. the span of the singular directions with `σᵢ^{1/n} ≤ exp c` — the
finite-step approximant of an intermediate slow space `Vⱼ(ω)` of the singular Oseledets flag (Quas,
*MET and Applications*, 2013, Theorem 2). -/
noncomputable def vSlowSingularStep (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (n : ℕ)
    (x : X) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ)
    (1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)).toLinearMap

/-- **The complement bridge.** The orthogonal-projection matrix onto the `n`-step slow space equals
`1 − bandProjector A T (𝟙_{(c,∞)}) n x`, the complement of the fast band projector. Direct from the
projector/range bridge `orthProjMatrix_range_toEuclideanCLM` and the complement-projector algebra
(`isSelfAdjoint_one_sub_bandProjector`, `one_sub_bandProjector_mul_self`). -/
theorem orthProjMatrix_vSlowSingularStep (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ)
    (n : ℕ) (x : X) :
    orthProjMatrix (vSlowSingularStep A T c n x)
      = 1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x :=
  orthProjMatrix_range_toEuclideanCLM _ (isSelfAdjoint_one_sub_bandProjector A T c n x)
    (one_sub_bandProjector_mul_self A T c n x)

/-! ## Slow increment = fast (band) increment in norm

The complement bridge turns the consecutive **slow** projector increment into the consecutive
**fast** band increment: the `1`s cancel and the difference flips sign, which is norm-invariant.
This is the det-free structural heart — the slow-side increment estimate IS the fast-side increment
estimate, verbatim, with no invertibility and no new small-σ leakage bound. -/

/-- **Slow increment equals fast (band) increment in norm.** The consecutive slow-projector
increment has the same operator norm as the consecutive fast band-projector increment at the same
Lyapunov cut `c`:

  `‖P_slow(n+1) − P_slow(n)‖ = ‖bandProjector(n+1) − bandProjector(n)‖`.

Proof: the complement bridge writes each slow projector as `1 − bandProjector`; the `1`s cancel in
the difference, the sign flips, and `‖−M‖ = ‖M‖`. -/
theorem norm_vSlowSingularStep_proj_succ_sub_eq_band (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (c : ℝ) (n : ℕ) (x : X) :
    ‖orthProjMatrix (vSlowSingularStep A T c (n + 1) x)
        - orthProjMatrix (vSlowSingularStep A T c n x)‖
      = ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖ := by
  rw [orthProjMatrix_vSlowSingularStep, orthProjMatrix_vSlowSingularStep]
  rw [show (1 : Matrix (Fin d) (Fin d) ℝ)
        - bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
      - (1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      = -(bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) by abel]
  rw [norm_neg]

/-! ## Summability transfer and the limit slow projector

The norm identity makes summability of the slow increments **literally the same proposition** as
summability of the fast band increments. Feeding it through Wave-1's
`exists_tendsto_orthProjMatrix_of_summable` produces the limit slow projector — the analytic crux of
the `Vⱼ` construction, *given* the summable fast-band increments (which the existing engine supplies
under the named invertibility hypothesis; see the module docstring's wall). -/

/-- **Summability transfer.** The slow-projector increments are summable iff the fast band-projector
increments are. Immediate from the per-step norm identity
`norm_vSlowSingularStep_proj_succ_sub_eq_band`. -/
theorem summable_vSlowSingularStep_increment_iff_band (A : X → Matrix (Fin d) (Fin d) ℝ)
    (T : X → X) (c : ℝ) (x : X) :
    Summable (fun n => ‖orthProjMatrix (vSlowSingularStep A T c (n + 1) x)
        - orthProjMatrix (vSlowSingularStep A T c n x)‖)
      ↔ Summable (fun n =>
          ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
            - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖) := by
  apply summable_congr
  intro n
  exact norm_vSlowSingularStep_proj_succ_sub_eq_band A T c n x

/-- **The limit slow projector (the `Vⱼ` construction crux).** If the **fast** band-projector
increments are summable, then the **slow** orthogonal projectors
`orthProjMatrix (vSlowSingularStep A T c n x)` converge to a matrix `P` that is again an orthogonal
projector (self-adjoint and idempotent, `P * P = P`) — the candidate limit slow projector encoding
`Vⱼ(ω) = limₙ vSlowSingularStep A T c n x`.

This is the assembly of the det-free reduction: the summability transfer
(`summable_vSlowSingularStep_increment_iff_band`) feeds Wave-1's
`exists_tendsto_orthProjMatrix_of_summable`. The only remaining input is the **fast-band increment
summability** — supplied by the existing det-free leakage engine
(`norm_bandProjector_succ_sub_le` ⇒ `exists_tendsto_bandProjector`), whose UNCONDITIONAL cocycle
discharge requires invertibility in exactly one rank-1 lower bound; see the module docstring. -/
theorem exists_tendsto_orthProjMatrix_vSlowSingularStep_of_summable
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X)
    (hsum : Summable (fun n =>
        ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖)) :
    ∃ P, Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T c n x)) atTop (𝓝 P)
      ∧ IsSelfAdjoint P ∧ P * P = P := by
  have hsum' : Summable (fun n => ‖orthProjMatrix (vSlowSingularStep A T c (n + 1) x)
      - orthProjMatrix (vSlowSingularStep A T c n x)‖) :=
    (summable_vSlowSingularStep_increment_iff_band A T c x).mpr hsum
  exact exists_tendsto_orthProjMatrix_of_summable hsum'

/-! ## Convergence of the slow projector to a concrete limit (the band-limit complement)

Beyond mere existence of a limit projector, the slow projector converges to the **explicit**
complement `1 − P_fast` of the fast band limit `P_fast`. This is the cleanest packaging of the
reduction: the slow space limit is *literally* the orthogonal complement of the fast Oseledets
spectral projector, with no extra analysis once `bandProjector` converges. -/

/-- **Slow projector → complement of the fast limit.** If the fast band projectors converge to
`P_fast`, then the slow projectors `orthProjMatrix (vSlowSingularStep A T c n x)` converge to the
complement `1 − P_fast`. Continuity of `M ↦ 1 − M` applied to the complement bridge
`orthProjMatrix_vSlowSingularStep`. -/
theorem tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X)
    {Pfast : Matrix (Fin d) (Fin d) ℝ}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) atTop (𝓝 Pfast)) :
    Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T c n x)) atTop (𝓝 (1 - Pfast)) := by
  have hcompl : (fun n => orthProjMatrix (vSlowSingularStep A T c n x))
      = (fun n => 1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) := by
    funext n; exact orthProjMatrix_vSlowSingularStep A T c n x
  rw [hcompl]
  exact tendsto_const_nhds.sub hP

/-! ## Measurability of the `n`-step slow space

Each `n`-step slow space is a `MeasurableSubspace` (in `x`), unconditionally. The complement of the
fast band is the **slow** spectral projector `cfc (𝟙_{(-∞,c]}) (qpow)`, which is measurable by
`measurable_spectralProjector` applied to the measurable, self-adjoint `qpow` family. -/

/-- The complement `1 − bandProjector A T (𝟙_{(c,∞)}) n x` equals the slow spectral projector
`cfc (𝟙_{(-∞,c]} 1) (qpow A T n x)` — the `qpow`-scale orthogonal-complement `cfc` identity (the
`qpow` analogue of the scratch's raw-Gram `cfc_indicator_Iic_eq_one_sub_Ioi`). The `{0,1}`
indicators of `(-∞,c]` and `(c,∞)` sum to `1` and `cfc` is additive, so the slow projector is `1`
minus the fast projector at the same `qpow` cut. -/
theorem one_sub_bandProjector_eq_cfc_Iic (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ)
    (n : ℕ) (x : X) :
    1 - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
      = cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (qpow A T n x) := by
  set S := qpow A T n x with hS
  have hfin := S.finite_real_spectrum
  have hcontIic : ContinuousOn (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    hfin.continuousOn _
  have hcontIoi : ContinuousOn (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    hfin.continuousOn _
  have hsum : cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) S
        + cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) S
      = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [← cfc_add (a := S) (Set.indicator (Set.Iic c) (1 : ℝ → ℝ))
      (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) hcontIic hcontIoi]
    rw [show (fun s => Set.indicator (Set.Iic c) (1 : ℝ → ℝ) s
        + Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) s) = (1 : ℝ → ℝ) from ?_]
    · exact cfc_one (a := S) ℝ (ha := qpow_isSelfAdjoint A T n x)
    · funext s
      by_cases hs : s ≤ c
      · have h1 : s ∈ Set.Iic c := hs
        have h2 : s ∉ Set.Ioi c := by simp only [Set.mem_Ioi, not_lt]; exact hs
        rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]; simp
      · have h1 : s ∉ Set.Iic c := by simp only [Set.mem_Iic, not_le]; exact lt_of_not_ge hs
        have h2 : s ∈ Set.Ioi c := lt_of_not_ge hs
        rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]; simp
  rw [bandProjector, ← hS, eq_comm]
  exact eq_sub_of_add_eq hsum

/-- **The slow space is the range of the slow `qpow` spectral projector.** `vSlowSingularStep A T c
n x` equals the range of `cfc (𝟙_{(-∞,c]} 1) (qpow A T n x)`, the orthogonal projector onto the span
of the `qpow` eigenvectors with eigenvalue `≤ c`. Rewriting the defining complement via the
orthogonal-complement `cfc` identity `one_sub_bandProjector_eq_cfc_Iic`. -/
theorem vSlowSingularStep_eq_range_cfc (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ)
    (n : ℕ) (x : X) :
    vSlowSingularStep A T c n x
      = LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (qpow A T n x))).toLinearMap := by
  rw [vSlowSingularStep, one_sub_bandProjector_eq_cfc_Iic]

/-- **Measurability of the `n`-step slow space.** For each fixed step `n` and Lyapunov cut `c`, the
family `x ↦ vSlowSingularStep A T c n x` is a `MeasurableSubspace`. The defining matrix is the slow
`qpow` spectral projector `cfc (𝟙_{(-∞,c]} 1) (qpow A T n x)`
(`vSlowSingularStep_eq_range_cfc`), a measurable (`measurable_spectralProjector` on the measurable,
self-adjoint `qpow` family `measurable_qpow` / `qpow_isSelfAdjoint`) self-adjoint idempotent; the
projector/range bridge `measurableSubspace_range_of_measurable` closes it. Unconditional. -/
theorem measurableSubspace_vSlowSingularStep {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A)
    {T : X → X} (hT : Measurable T) (c : ℝ) (n : ℕ) :
    MeasurableSubspace (fun x => vSlowSingularStep A T c n x) := by
  have heq : (fun x => vSlowSingularStep A T c n x)
      = fun x => LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (qpow A T n x))).toLinearMap := by
    funext x; exact vSlowSingularStep_eq_range_cfc A T c n x
  rw [heq]
  refine measurableSubspace_range_of_measurable
    (fun x => cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (qpow A T n x)) ?_ ?_ ?_
  · exact measurable_spectralProjector c (fun x => qpow A T n x) (measurable_qpow hA hT n)
      (fun x => (qpow_isSelfAdjoint A T n x))
  · intro x; exact cfc_predicate _ _
  · intro x
    -- The `{0,1}`-indicator squares to itself on the (finite) spectrum; `cfc` is multiplicative.
    have hfin := (qpow A T n x).finite_real_spectrum
    have hcont : ContinuousOn (Set.indicator (Set.Iic c) (1 : ℝ → ℝ))
        (spectrum ℝ (qpow A T n x)) := hfin.continuousOn _
    have hidem : (fun s : ℝ => Set.indicator (Set.Iic c) (1 : ℝ → ℝ) s
        * Set.indicator (Set.Iic c) 1 s) = Set.indicator (Set.Iic c) (1 : ℝ → ℝ) := by
      funext s
      by_cases hs : s ∈ Set.Iic c
      · simp [Set.indicator_of_mem hs]
      · simp [Set.indicator_of_notMem hs]
    rw [← cfc_mul _ _ _ hcont hcont, hidem]

/-! ## The antitone finite-step flag

The `n`-step slow spaces are **antitone** in the Lyapunov cut `c`: a larger threshold admits *more*
slow (subthreshold) singular directions, so `c ≤ c'` gives `vSlowSingularStep … c … ≤
vSlowSingularStep … c' …`. This is the finite-step incarnation of the nested slow flag
`V₁ ⊆ V₂ ⊆ ⋯` of Oseledets' filtration. The range of a spectral `≤ c` projector is the `≤ c`
eigenspace, and `≤ c` eigenspaces nest as `c` grows. -/

omit [MeasurableSpace X] [NeZero d] in
/-- The slow `qpow` spectral projector fixes every slow eigenvector at a smaller cut: if `c ≤ c'`,
then `cfc (𝟙_{(-∞,c']}) (qpow) ∘ cfc (𝟙_{(-∞,c]}) (qpow) = cfc (𝟙_{(-∞,c]}) (qpow)`, because on the
spectrum the larger indicator dominates the smaller (`𝟙_{(-∞,c']}·𝟙_{(-∞,c]} = 𝟙_{(-∞,c]}`). This is
the projector-nesting that yields the subspace inclusion. -/
theorem cfc_Iic_mul_Iic_of_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) {c c' : ℝ}
    (hcc : c ≤ c') (n : ℕ) (x : X) :
    cfc (Set.indicator (Set.Iic c') (1 : ℝ → ℝ)) (qpow A T n x)
        * cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (qpow A T n x)
      = cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (qpow A T n x) := by
  set S := qpow A T n x with hS
  have hfin := S.finite_real_spectrum
  have hcontc' : ContinuousOn (Set.indicator (Set.Iic c') (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    hfin.continuousOn _
  have hcontc : ContinuousOn (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    hfin.continuousOn _
  have hmul : (fun s : ℝ => Set.indicator (Set.Iic c') (1 : ℝ → ℝ) s
      * Set.indicator (Set.Iic c) (1 : ℝ → ℝ) s) = Set.indicator (Set.Iic c) (1 : ℝ → ℝ) := by
    funext s
    by_cases hs : s ∈ Set.Iic c
    · have hs' : s ∈ Set.Iic c' := le_trans hs hcc
      rw [Set.indicator_of_mem hs', Set.indicator_of_mem hs]; simp
    · rw [Set.indicator_of_notMem hs]; simp
  rw [← cfc_mul _ _ _ hcontc' hcontc, hmul]

/-- **The antitone finite-step slow flag.** For `c ≤ c'`, the `n`-step slow space at cut `c` is
contained in the one at cut `c'`: `vSlowSingularStep A T c n x ≤ vSlowSingularStep A T c' n x`. The
smaller-cut slow projector factors through the larger-cut one (`cfc_Iic_mul_Iic_of_le`), so each
vector of the smaller range lies in the larger range. This is the nested slow flag of the singular
forward filtration at finite step `n`. -/
theorem vSlowSingularStep_antitone (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) {c c' : ℝ}
    (hcc : c ≤ c') (n : ℕ) (x : X) :
    vSlowSingularStep A T c n x ≤ vSlowSingularStep A T c' n x := by
  rw [vSlowSingularStep_eq_range_cfc, vSlowSingularStep_eq_range_cfc]
  set Pc := cfc (Set.indicator (Set.Iic c) (1 : ℝ → ℝ)) (qpow A T n x) with hPc
  set Pc' := cfc (Set.indicator (Set.Iic c') (1 : ℝ → ℝ)) (qpow A T n x) with hPc'
  rintro y ⟨w, rfl⟩
  -- `y = (toEuclideanCLM Pc) w`; exhibit it in the larger range via `Pc' * Pc = Pc`
  -- (so `toEuclideanCLM Pc' (toEuclideanCLM Pc w) = toEuclideanCLM Pc w`).
  refine ⟨(Matrix.toEuclideanCLM (𝕜 := ℝ) Pc).toLinearMap w, ?_⟩
  have hmul : Pc' * Pc = Pc := cfc_Iic_mul_Iic_of_le A T hcc n x
  have hcomp : (Matrix.toEuclideanCLM (𝕜 := ℝ) Pc')
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) Pc) w)
      = (Matrix.toEuclideanCLM (𝕜 := ℝ) Pc) w := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, hmul]
  simpa using hcomp

end Oseledets
