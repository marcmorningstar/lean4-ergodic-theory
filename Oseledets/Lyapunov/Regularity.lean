/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.DetIdentity
import Oseledets.Ergodic.Birkhoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Regularity of the Lyapunov exponents in the generating cocycle (item #4)

This module is purely *additive* on top of the spectrum object
`Oseledets.exponents : Fin d → ℝ`, the telescoping growth rate `Oseledets.gammaK`
(`Oseledets/Lyapunov/ExponentSums.lean`), and the determinant identity
`Oseledets.sumAllExp_eq_integral_log_abs_det` (`Oseledets/Lyapunov/DetIdentity.lean`). It
records the **regularity** of the exponents as functions of the generator `A`.

This is the genuinely subtle requested extension. The honest summary is:

* **The Fekete infimum representation** `Γ_k = ⨅ n, (∫ log Sprod_k(n+1))/(n+1)`
  (`GammaK_eq_iInf`). The normalized integral sequence is the average of a *subadditive*
  cocycle (`isSubadditiveCocycle_logSprod` integrated over the measure-preserving base), so by
  Fekete's lemma it converges to the **infimum** of its values. The ergodic a.e.-constant limit
  `gammaK` coincides with this infimum; the non-trivial direction of that coincidence is a
  two-sided Fatou argument (`gammaK_eq_GammaKInf`).

* **Per-`n` integral continuity under a uniform log-integrable envelope** (regime 1,
  `tendsto_integral_logSprod_of_dominated`). If a family of generators `Aₘ → A` converges
  entrywise a.e. with `‖Aₘ‖, ‖Aₘ⁻¹‖` dominated by *fixed* `L¹`-log functions, then by dominated
  convergence `∫ log Sprod_k(Aₘ, n) → ∫ log Sprod_k(A, n)` for each fixed `n`. Pointwise
  generator convergence *alone is insufficient*: the dominated-convergence theorem needs a fixed
  integrable envelope, which is exactly what the uniform `L¹`-log hypothesis supplies.

* **Upper semicontinuity of the partial sums and the top exponent**
  (`GammaK_upperSemicontinuous`, `topExponent_upperSemicontinuous`). An infimum of functions each
  *continuous* in the generator is **upper semicontinuous**; hence each `Γ_k` (the sum of the
  top-`k` exponents) and the top exponent `λ₁ = Γ_1` are USC: `limsup_m Γ_k(Aₘ) ≤ Γ_k(A)`. The
  positive-exponent sum `max_k Γ_k` is then USC as a finite maximum of USC functions (a finite
  `max` of `limsup`s), which we leave to the consumer to assemble from `GammaK_upperSemicontinuous`.

* **Lower semicontinuity of the bottom exponent** (`botExp_lowerSemicontinuous`). Because
  `Γ_d = ∫ log|det|` is *continuous* (in fact linear in `log|det|`, see the determinant
  identity), and the bottom exponent is `λ_d = Γ_d − Γ_{d-1}` with `Γ_{d-1}` USC, the difference
  is **lower** semicontinuous.

## Honest caveats (these are mandatory and stated in the relevant docstrings)

* **USC, not continuity.** The partial sums `Γ_k` and the positive-exponent sum are only *upper*
  semicontinuous, not continuous, in the generator. Full continuity of individual exponents
  *fails* in general: the spectrum can jump as a spectral gap closes.
* **Individual interior exponents have no semicontinuity.** An interior exponent
  `λᵢ = Γ_{i+1} − Γ_i` is a *difference* of two USC functions, hence is in general neither USC
  nor LSC. The bottom exponent is the exception: it is LSC because `Γ_d` is continuous.
* **The convergence hypothesis is essential.** The semicontinuity statements are stated for the
  uniform or `L¹`-log convergence regime with a *fixed integrable envelope* dominating
  `‖Aₘ‖, ‖Aₘ⁻¹‖`. Pointwise generator convergence alone does not suffice (the per-`n` integral
  continuity step is a dominated-convergence argument that requires domination).

## Main definitions / results

* `Oseledets.GammaKInf` — the Fekete infimum `⨅ n, (∫ log Sprod_k(n+1))/(n+1)`.
* `Oseledets.integral_logSprod_subadditive` — the integral sequence is subadditive.
* `Oseledets.tendsto_integral_logSprod` — Fekete: the normalized integral sequence converges to
  `GammaKInf`.
* `Oseledets.gammaK_eq_GammaKInf`, `Oseledets.GammaK_eq_iInf` — the ergodic constant is the
  Fekete infimum.
* `Oseledets.tendsto_integral_logSprod_of_dominated` — per-`n` integral continuity under a fixed
  log-integrable envelope (regime 1).
* `Oseledets.GammaK_upperSemicontinuous` — USC of the top-`k` partial-sum growth rate `Γ_k`.
* `Oseledets.topExponent_upperSemicontinuous` — USC of the top exponent `λ₁ = Γ_1`.
* `Oseledets.botExp`, `Oseledets.botExp_eq_exponents_last`,
  `Oseledets.botExp_lowerSemicontinuous` — the bottom exponent `λ_d = Γ_d − Γ_{d-1}` and its LSC.
-/

open MeasureTheory Filter Topology ENNReal
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]
variable {μ : Measure X} {T : X → X}

/-! ## A Bochner–Fatou helper for nonnegative a.e.-convergent sequences

If `h n ≥ 0` (a.e.) is integrable, `h n → H` a.e. with `H` integrable, and the *integral*
sequence converges to `b`, then `∫ H ≤ b`. This is Fatou's lemma in the convenient convergent
form; it powers the non-trivial direction of `gammaK_eq_GammaKInf`. -/

omit [NeZero d] in
private theorem integral_le_of_nonneg_tendsto {h : ℕ → X → ℝ} {H : X → ℝ} {b : ℝ}
    (hint : ∀ n, Integrable (h n) μ) (hnn : ∀ n, 0 ≤ᵐ[μ] h n)
    (hHnn : 0 ≤ᵐ[μ] H) (hHint : Integrable H μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 (H x)))
    (hbconv : Tendsto (fun n => ∫ x, h n x ∂μ) atTop (𝓝 b)) :
    (∫ x, H x ∂μ) ≤ b := by
  have hbnn : 0 ≤ b :=
    ge_of_tendsto' hbconv (fun n => integral_nonneg_of_ae (hnn n))
  have key : ENNReal.ofReal (∫ x, H x ∂μ) ≤ ENNReal.ofReal b := by
    rw [ofReal_integral_eq_lintegral_ofReal hHint hHnn]
    have hHeq : (fun x => ENNReal.ofReal (H x)) =ᵐ[μ]
        (fun x => liminf (fun n => ENNReal.ofReal (h n x)) atTop) := by
      filter_upwards [hconv] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
    rw [lintegral_congr_ae hHeq]
    refine le_trans (lintegral_liminf_le' (fun n => (hint n).aemeasurable.ennreal_ofReal)) ?_
    have hbconv' : Tendsto (fun n => ENNReal.ofReal (∫ x, h n x ∂μ)) atTop
        (𝓝 (ENNReal.ofReal b)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hbconv
    rw [← hbconv'.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards with n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (hnn n)]
  exact (ENNReal.ofReal_le_ofReal_iff hbnn).mp key

/-! ## The Fekete infimum representation of `Γ_k` -/

section Fekete

variable [IsProbabilityMeasure μ]

/-- The integral of a measure-preserving composition equals the integral:
`∫ g (T^[m] x) ∂μ = ∫ g x ∂μ`. (A local copy of the Kingman-file helper, which is private.) -/
private theorem integral_comp_iterate_logSprod {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A) (hT : MeasurePreserving T μ μ)
    (hTmeas : Measurable T) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) {k : ℕ} (hk : k ≤ d) (m n : ℕ) :
    ∫ x, Real.log (Sprod A T k n (T^[m] x)) ∂μ = ∫ x, Real.log (Sprod A T k n x) ∂μ := by
  have hg : Integrable (fun x => Real.log (Sprod A T k n x)) μ :=
    integrable_logSprod hT hA hAmeas hTmeas hint hint' hk n
  have hmp : MeasurePreserving (T^[m]) μ μ := hT.iterate m
  have haesm : AEStronglyMeasurable (fun x => Real.log (Sprod A T k n x))
      (Measure.map (T^[m]) μ) := by
    rw [hmp.map_eq]; exact hg.aestronglyMeasurable
  have hmap := integral_map (μ := μ) (φ := T^[m]) hmp.aemeasurable
    (f := fun x => Real.log (Sprod A T k n x)) haesm
  rw [hmp.map_eq] at hmap
  exact hmap.symm

/-- **Subadditivity of the integral sequence.** The sequence `aₙ = ∫ log Sprod_k(n)` is
subadditive (`a (m+n) ≤ a m + a n`): integrate the subadditive-cocycle inequality
(`isSubadditiveCocycle_logSprod`) over the measure-preserving base. This is the Fekete input. -/
theorem integral_logSprod_subadditive {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A) (hT : MeasurePreserving T μ μ)
    (hTmeas : Measurable T) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) {k : ℕ} (hk : k ≤ d) :
    Subadditive (fun n => ∫ x, Real.log (Sprod A T k n x) ∂μ) := by
  intro m n
  simp only
  have hsub := (isSubadditiveCocycle_logSprod (T := T) A k
    (fun j y => Sprod_pos hA hk j y)).apply_add_le
  have hgm : Integrable (fun x => Real.log (Sprod A T k m x)) μ :=
    integrable_logSprod hT hA hAmeas hTmeas hint hint' hk m
  have hgn : Integrable (fun x => Real.log (Sprod A T k n x)) μ :=
    integrable_logSprod hT hA hAmeas hTmeas hint hint' hk n
  have hgmn : Integrable (fun x => Real.log (Sprod A T k (m + n) x)) μ :=
    integrable_logSprod hT hA hAmeas hTmeas hint hint' hk (m + n)
  have hcomp : Integrable (fun x => Real.log (Sprod A T k n (T^[m] x))) μ :=
    (hT.iterate m).integrable_comp_of_integrable hgn
  calc ∫ x, Real.log (Sprod A T k (m + n) x) ∂μ
      ≤ ∫ x, (Real.log (Sprod A T k m x) + Real.log (Sprod A T k n (T^[m] x))) ∂μ :=
        integral_mono hgmn (hgm.add hcomp) (fun x => hsub m n x)
    _ = (∫ x, Real.log (Sprod A T k m x) ∂μ)
          + ∫ x, Real.log (Sprod A T k n (T^[m] x)) ∂μ := integral_add hgm hcomp
    _ = (∫ x, Real.log (Sprod A T k m x) ∂μ)
          + ∫ x, Real.log (Sprod A T k n x) ∂μ := by
        rw [integral_comp_iterate_logSprod hA hAmeas hT hTmeas hint hint' hk m n]

/-- **The Fekete infimum** `Γ_k = ⨅ n, (∫ log Sprod_k(n+1))/(n+1)`. By Fekete's lemma the
normalized integral sequence of a subadditive sequence decreases to its infimum; this packages
that infimum as a plain real. (It is identified with the ergodic constant `gammaK` in
`gammaK_eq_GammaKInf`.) -/
noncomputable def GammaKInf {A : X → Matrix (Fin d) (Fin d) ℝ} {k : ℕ} (_hk : k ≤ d) : ℝ :=
  ⨅ n : ℕ, (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1)

/-- The range of the normalized shifted integral sequence equals the image of `Ici 1` under
`u · / ·`, i.e. `GammaKInf` is the `sInf` over `n ≥ 1` of `(∫ log Sprod_k(n))/n`. -/
private theorem range_div_succ_eq {u : ℕ → ℝ} :
    Set.range (fun n : ℕ => u (n + 1) / (n + 1))
      = (fun n : ℕ => u n / n) '' Set.Ici 1 := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, Nat.le_add_left 1 n, by push_cast; ring_nf⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
    exact ⟨n, by push_cast; ring_nf⟩

/-- `GammaKInf` is the `Subadditive.lim` of the integral sequence. Both are `sInf` of the same
set (the image of `Ici 1` under `u · / ·`); `range_div_succ_eq` reconciles the `⨅`-over-`ℕ`
shifted indexing with the `Subadditive.lim` `Ici 1` indexing. -/
theorem GammaKInf_eq_lim {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) (hT : MeasurePreserving T μ μ)
    (hTmeas : Measurable T) {k : ℕ} (hk : k ≤ d) :
    GammaKInf (T := T) (μ := μ) (A := A) hk
      = (integral_logSprod_subadditive hA hAmeas hT hTmeas hint hint' hk).lim := by
  rw [GammaKInf, Subadditive.lim, iInf, ← range_div_succ_eq
    (u := fun n => ∫ x, Real.log (Sprod A T k n x) ∂μ)]

/-- **Fekete's lemma.** The normalized integral sequence `(∫ log Sprod_k(n+1))/(n+1)` converges
to the Fekete infimum `GammaKInf`. -/
theorem tendsto_integral_logSprod {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) (hT : MeasurePreserving T μ μ)
    (hTmeas : Measurable T) {k : ℕ} (hk : k ≤ d) :
    Tendsto (fun n : ℕ => (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1)) atTop
      (𝓝 (GammaKInf (T := T) (μ := μ) (A := A) hk)) := by
  set u : ℕ → ℝ := fun n => ∫ x, Real.log (Sprod A T k n x) ∂μ with hudef
  have hsa : Subadditive u := integral_logSprod_subadditive hA hAmeas hT hTmeas hint hint' hk
  have hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ)
      / (n + 1)) := bddBelow_logSprod hT hA hAmeas hTmeas hint hint' hk
  have hbdd' : BddBelow (Set.range fun n : ℕ => u n / n) := by
    obtain ⟨lb, hlb⟩ := hbdd
    refine ⟨min lb 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases n with _ | m
    · simp only [Nat.cast_zero, _root_.div_zero]; exact min_le_right lb 0
    · have hmem : u (m + 1) / ((m : ℝ) + 1)
          ∈ Set.range fun n : ℕ => (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1) :=
        ⟨m, by simp only [hudef]⟩
      have heq : (fun n : ℕ => u n / n) (m + 1) = u (m + 1) / ((m : ℝ) + 1) := by
        push_cast; ring
      rw [heq]
      exact le_trans (min_le_left lb 0) (hlb hmem)
  have hlim := hsa.tendsto_lim hbdd'
  rw [← tendsto_add_atTop_iff_nat (f := fun n : ℕ => u n / n) 1] at hlim
  rw [GammaKInf_eq_lim hA hAmeas hint hint' hT hTmeas hk]
  refine hlim.congr (fun n => ?_)
  show u (n + 1) / ((n + 1 : ℕ) : ℝ) = (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / ((n : ℝ) + 1)
  simp only [hudef, Nat.cast_add, Nat.cast_one]

end Fekete

/-! ## The ergodic constant equals the Fekete infimum (the crux) -/

section Crux

variable [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

omit [IsProbabilityMeasure μ] in
/-- The integral of `birkhoffAverage` over the iterate count `n+1` is just `∫ g`, on a
probability space with measure-preserving `T`. -/
private theorem integral_birkhoffAverage_succ (hmp : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : Integrable g μ) (n : ℕ) :
    ∫ x, birkhoffAverage ℝ T g (n + 1) x ∂μ = ∫ x, g x ∂μ := by
  have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [birkhoffAverage, smul_eq_mul]
  rw [integral_const_mul, integral_birkhoffSum hmp hg, nsmul_eq_mul]
  push_cast
  field_simp

/-- **The crux: the ergodic constant is the Fekete infimum.** `gammaK = GammaKInf`. The
inequality `gammaK ≤ GammaKInf` is a Fatou estimate on `f_n − L_n ≥ 0` where
`L_n = −k·birkhoffAverage(log⁺‖A⁻¹‖)` converges a.e. (Birkhoff) to a constant; the reverse
`GammaKInf ≤ gammaK` is the symmetric Fatou estimate on `U_n − f_n ≥ 0` with
`U_n = k·birkhoffAverage(log⁺‖A‖)`. The integral sequence converges to `GammaKInf` by Fekete
(`tendsto_integral_logSprod`), the integrands converge a.e. to `gammaK` (`gammaK_tendsto`), and
the dominating-Birkhoff integrals are constant by measure preservation. -/
theorem gammaK_eq_GammaKInf {k : ℕ} (hk : k ≤ d) :
    gammaK hT hA hAmeas hint hint' hk
      = GammaKInf (T := T) (μ := μ) (A := A) hk := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  set c := gammaK hT hA hAmeas hint hint' hk with hcdef
  set G := GammaKInf (T := T) (μ := μ) (A := A) hk with hGdef
  -- normalized integrand `f_n x = log Sprod_k(n+1, x)/(n+1)`.
  set f : ℕ → X → ℝ := fun n x => Real.log (Sprod A T k (n + 1) x) / (n + 1) with hfdef
  -- a.e. `f_n → c`.
  have hfconv : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 c) := by
    filter_upwards [gammaK_tendsto hT hA hAmeas hint hint' hk] with x hx
    rw [← tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Sprod A T k n x)) 1]
      at hx
    refine hx.congr (fun n => ?_)
    rw [hfdef]
    push_cast
    rw [div_eq_inv_mul]
  -- `∫ f_n = (∫ log Sprod_k(n+1))/(n+1)`.
  have hint_f : ∀ n, Integrable (f n) μ := by
    intro n
    exact (integrable_logSprod hmp hA hAmeas hTmeas hint hint' hk (n + 1)).div_const _
  have hf_integral : ∀ n, (∫ x, f n x ∂μ)
      = (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1) := by
    intro n
    rw [hfdef]
    exact integral_div _ _
  have hf_tendsto : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 G) := by
    rw [hGdef]
    refine (tendsto_integral_logSprod hA hAmeas hint hint' hmp hTmeas hk).congr (fun n => ?_)
    rw [hf_integral n]
  -- The two dominating Birkhoff averages.
  set Q := ∫ x, Real.posLog ‖A x‖ ∂μ with hQdef
  set P := ∫ x, Real.posLog ‖(A x)⁻¹‖ ∂μ with hPdef
  have hQint : Integrable (fun x => Real.posLog ‖A x‖) μ := hint
  have hPint : Integrable (fun x => Real.posLog ‖(A x)⁻¹‖) μ := hint'
  set U : ℕ → X → ℝ := fun n x =>
    (k : ℝ) * birkhoffAverage ℝ T (fun y => Real.posLog ‖A y‖) (n + 1) x with hUdef
  set L : ℕ → X → ℝ := fun n x =>
    - ((k : ℝ) * birkhoffAverage ℝ T (fun y => Real.posLog ‖(A y)⁻¹‖) (n + 1) x) with hLdef
  -- a.e. convergence of the envelopes.
  have hUconv : ∀ᵐ x ∂μ, Tendsto (fun n => U n x) atTop (𝓝 ((k : ℝ) * Q)) := by
    filter_upwards [tendsto_birkhoffAverage_ae_integral hT hQint] with x hx
    rw [hUdef]
    rw [← tendsto_add_atTop_iff_nat
      (f := fun n => birkhoffAverage ℝ T (fun y => Real.posLog ‖A y‖) n x) 1] at hx
    exact (tendsto_const_nhds.mul hx)
  have hLconv : ∀ᵐ x ∂μ, Tendsto (fun n => L n x) atTop (𝓝 (-((k : ℝ) * P))) := by
    filter_upwards [tendsto_birkhoffAverage_ae_integral hT hPint] with x hx
    rw [hLdef]
    rw [← tendsto_add_atTop_iff_nat
      (f := fun n => birkhoffAverage ℝ T (fun y => Real.posLog ‖(A y)⁻¹‖) n x) 1] at hx
    exact (tendsto_const_nhds.mul hx).neg
  -- integrability of birkhoffAverages.
  have hbaQ : ∀ n, Integrable (fun x => birkhoffAverage ℝ T (fun y => Real.posLog ‖A y‖)
      (n + 1) x) μ := fun n => by
    simp only [birkhoffAverage, smul_eq_mul]
    exact (integrable_birkhoffSum hmp hQint (n + 1)).const_mul _
  have hbaP : ∀ n, Integrable (fun x => birkhoffAverage ℝ T (fun y => Real.posLog ‖(A y)⁻¹‖)
      (n + 1) x) μ := fun n => by
    simp only [birkhoffAverage, smul_eq_mul]
    exact (integrable_birkhoffSum hmp hPint (n + 1)).const_mul _
  -- integrability of envelopes.
  have hUint : ∀ n, Integrable (U n) μ := fun n => (hbaQ n).const_mul _
  have hLint : ∀ n, Integrable (L n) μ := fun n => ((hbaP n).const_mul _).neg
  -- integral of envelopes.
  have hU_integral : ∀ n, (∫ x, U n x ∂μ) = (k : ℝ) * Q := by
    intro n
    rw [hUdef, integral_const_mul, integral_birkhoffAverage_succ hmp hQint n]
  have hL_integral : ∀ n, (∫ x, L n x ∂μ) = -((k : ℝ) * P) := by
    intro n
    rw [hLdef, integral_neg, integral_const_mul, integral_birkhoffAverage_succ hmp hPint n]
  -- pointwise bounds `L_n ≤ f_n ≤ U_n`.
  have hLf : ∀ n, ∀ x, L n x ≤ f n x := by
    intro n x
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- `log Sprod_k(n+1) ≥ -k·log‖(A⁽ⁿ⁺¹⁾)⁻¹‖ ≥ -k·birkhoffSum(log⁺‖A⁻¹‖)(n+1)`.
    have hlb := neg_le_logSprod (T := T) hA hk (n + 1) x
    have hbk := logNorm_inv_cocycle_le_birkhoffSum (T := T) hA (n + 1) x
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hstep : - ((k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖(A y)⁻¹‖) (n + 1) x)
        ≤ Real.log (Sprod A T k (n + 1) x) := by
      have : (k : ℝ) * Real.log ‖(cocycle A T (n + 1) x)⁻¹‖
          ≤ (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖(A y)⁻¹‖) (n + 1) x :=
        mul_le_mul_of_nonneg_left hbk hknn
      linarith [hlb, this]
    simp only [hLdef, hfdef, birkhoffAverage, smul_eq_mul]
    rw [show (((n + 1 : ℕ) : ℝ))⁻¹ = ((n : ℝ) + 1)⁻¹ by rw [hcast], le_div_iff₀ hpos]
    rw [show -((k : ℝ) * (((n : ℝ) + 1)⁻¹ * birkhoffSum T
        (fun y => Real.posLog ‖(A y)⁻¹‖) (n + 1) x)) * ((n : ℝ) + 1)
        = -((k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖(A y)⁻¹‖) (n + 1) x) by
      field_simp]
    linarith [hstep]
  have hfU : ∀ n, ∀ x, f n x ≤ U n x := by
    intro n x
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hub := logSprod_le (T := T) hA hk (n + 1) x
    have hbk := logNorm_cocycle_le_birkhoffSum (T := T) hA (n + 1) x
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hstep : Real.log (Sprod A T k (n + 1) x)
        ≤ (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) (n + 1) x := by
      have : (k : ℝ) * Real.log ‖cocycle A T (n + 1) x‖
          ≤ (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) (n + 1) x :=
        mul_le_mul_of_nonneg_left hbk hknn
      linarith [hub, this]
    simp only [hfdef, hUdef, birkhoffAverage, smul_eq_mul]
    rw [show (((n + 1 : ℕ) : ℝ))⁻¹ = ((n : ℝ) + 1)⁻¹ by rw [hcast], div_le_iff₀ hpos]
    rw [show (k : ℝ) * (((n : ℝ) + 1)⁻¹ * birkhoffSum T
        (fun y => Real.posLog ‖A y‖) (n + 1) x) * ((n : ℝ) + 1)
        = (k : ℝ) * birkhoffSum T (fun y => Real.posLog ‖A y‖) (n + 1) x by
      field_simp]
    linarith [hstep]
  -- ===== Lower direction: `c ≤ G` via Fatou on `h_n = f_n - L_n ≥ 0 → c + kP`. =====
  have hlower : c ≤ G := by
    set h : ℕ → X → ℝ := fun n x => f n x - L n x with hhdef
    have hhint : ∀ n, Integrable (h n) μ := fun n => (hint_f n).sub (hLint n)
    have hhnn : ∀ n, 0 ≤ᵐ[μ] h n := by
      intro n; filter_upwards with x; exact sub_nonneg.mpr (hLf n x)
    have hHval : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 (c + (k : ℝ) * P)) := by
      filter_upwards [hfconv, hLconv] with x hfx hLx
      have := hfx.sub hLx
      simpa only [hhdef, sub_neg_eq_add] using this
    have hHnn : 0 ≤ᵐ[μ] (fun _ : X => c + (k : ℝ) * P) := by
      filter_upwards [hHval] with x hx
      exact ge_of_tendsto' hx (fun n => sub_nonneg.mpr (hLf n x))
    have hbconv : Tendsto (fun n => ∫ x, h n x ∂μ) atTop (𝓝 (G + (k : ℝ) * P)) := by
      have heq : (fun n => ∫ x, h n x ∂μ) = fun n => (∫ x, f n x ∂μ) + (k : ℝ) * P := by
        funext n
        rw [show (∫ x, h n x ∂μ) = (∫ x, f n x ∂μ) - ∫ x, L n x ∂μ from
          integral_sub (hint_f n) (hLint n), hL_integral n, sub_neg_eq_add]
      rw [heq]
      exact hf_tendsto.add_const _
    have hfatou := integral_le_of_nonneg_tendsto hhint hhnn hHnn (integrable_const _)
      hHval hbconv
    rw [integral_const, probReal_univ, one_smul] at hfatou
    linarith [hfatou]
  -- ===== Upper direction: `G ≤ c` via Fatou on `h'_n = U_n - f_n ≥ 0 → kQ - c`. =====
  have hupper : G ≤ c := by
    set h : ℕ → X → ℝ := fun n x => U n x - f n x with hhdef
    have hhint : ∀ n, Integrable (h n) μ := fun n => (hUint n).sub (hint_f n)
    have hhnn : ∀ n, 0 ≤ᵐ[μ] h n := by
      intro n; filter_upwards with x; exact sub_nonneg.mpr (hfU n x)
    have hHval : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 ((k : ℝ) * Q - c)) := by
      filter_upwards [hfconv, hUconv] with x hfx hUx
      simpa only [hhdef] using hUx.sub hfx
    have hHnn : 0 ≤ᵐ[μ] (fun _ : X => (k : ℝ) * Q - c) := by
      filter_upwards [hHval] with x hx
      exact ge_of_tendsto' hx (fun n => sub_nonneg.mpr (hfU n x))
    have hbconv : Tendsto (fun n => ∫ x, h n x ∂μ) atTop (𝓝 ((k : ℝ) * Q - G)) := by
      have heq : (fun n => ∫ x, h n x ∂μ) = fun n => (k : ℝ) * Q - ∫ x, f n x ∂μ := by
        funext n
        rw [show (∫ x, h n x ∂μ) = (∫ x, U n x ∂μ) - ∫ x, f n x ∂μ from
          integral_sub (hUint n) (hint_f n), hU_integral n]
      rw [heq]
      exact tendsto_const_nhds.sub hf_tendsto
    have hfatou := integral_le_of_nonneg_tendsto hhint hhnn hHnn (integrable_const _)
      hHval hbconv
    rw [integral_const, probReal_univ, one_smul] at hfatou
    linarith [hfatou]
  linarith [hlower, hupper]

/-- **The Fekete infimum representation of `Γ_k`** (item #4 foundation). The ergodic growth
rate equals the infimum, over `n`, of the normalized integrals:
`Γ_k = ⨅ n, (∫ log Sprod_k(n+1))/(n+1)`. This is the representation that makes `Γ_k` an
infimum of functions *continuous* in the generator, hence upper semicontinuous. -/
theorem GammaK_eq_iInf {k : ℕ} (hk : k ≤ d) :
    gammaK hT hA hAmeas hint hint' hk
      = ⨅ n : ℕ, (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1) :=
  gammaK_eq_GammaKInf hT hA hAmeas hint hint' hk

end Crux

/-! ## Per-`n` integral continuity under a fixed log-integrable envelope (regime 1) -/

section PerNContinuity

variable {B : ℕ → X → Matrix (Fin d) (Fin d) ℝ}
    {A : X → Matrix (Fin d) (Fin d) ℝ}

omit [NeZero d] in
/-- **Per-`n` integral continuity (dominated convergence, regime 1).** Suppose a sequence of
generators `B m → A` is such that, for a *fixed* iterate count `n` and `μ`-a.e. `x`, the
integrand `log Sprod_k(B m, n, x) → log Sprod_k(A, n, x)` converges, and is dominated by a
*fixed* integrable function `bound`. Then `∫ log Sprod_k(B m, n) → ∫ log Sprod_k(A, n)`.

The a.e. integrand convergence is supplied, e.g., by entrywise a.e. convergence `B m → A`
through the continuity of the singular-value product `Sprod` in the matrix entries; the fixed
`bound` (e.g. `k·(log⁺‖·‖ + log⁺‖·⁻¹‖)` for a uniform envelope) is the mandatory `L¹`-log
domination. **Pointwise generator convergence alone is insufficient**: the dominated-convergence
theorem requires a fixed integrable envelope. -/
theorem tendsto_integral_logSprod_of_dominated {k n : ℕ} {bound : X → ℝ}
    (hmeas : ∀ m, AEStronglyMeasurable (fun x => Real.log (Sprod (B m) T k n x)) μ)
    (hbound_int : Integrable bound μ)
    (hbound : ∀ m, ∀ᵐ x ∂μ, ‖Real.log (Sprod (B m) T k n x)‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => Real.log (Sprod (B m) T k n x)) atTop
      (𝓝 (Real.log (Sprod A T k n x)))) :
    Tendsto (fun m => ∫ x, Real.log (Sprod (B m) T k n x) ∂μ) atTop
      (𝓝 (∫ x, Real.log (Sprod A T k n x) ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hbound_int hbound hlim

end PerNContinuity

/-! ## Upper semicontinuity of the partial sums, top exponent, and positive-exponent sum -/

section USC

variable [IsProbabilityMeasure μ] {ι : Type*} {l : Filter ι}
    {B : ι → X → Matrix (Fin d) (Fin d) ℝ}
    (hB : ∀ i, (∀ x, (B i x).det ≠ 0) ∧ Measurable (B i) ∧ IntegrableLogNorm (B i) μ
      ∧ IntegrableLogNorm (fun x => (B i x)⁻¹) μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

/-- **Upper semicontinuity of the partial sums in the generator.** Let `B i` be a family of
generators (each satisfying the standing hypotheses, via `hB`) and `A` a limiting generator,
such that for *every fixed* `n` the per-`n` integral is continuous along the filter `l`
(`hcont`, the conclusion of `tendsto_integral_logSprod_of_dominated`). Then the partial-sum
growth rate `Γ_k` is **upper semicontinuous**: `limsup_i Γ_k(B i) ≤ Γ_k(A)`.

CAVEAT (honest): this is *upper* semicontinuity, **not continuity**. `Γ_k` is an infimum of the
per-`n` continuous normalized integrals (`GammaK_eq_iInf`); an infimum of continuous functions is
USC, and the inequality can be strict — full continuity of the partial sums (and a fortiori of
individual exponents) fails in general when a spectral gap closes. The per-`n` continuity
hypothesis is the dominated-convergence conclusion and itself requires a fixed integrable
envelope (pointwise generator convergence alone does not suffice). -/
theorem GammaK_upperSemicontinuous (hT : Ergodic T μ) [l.IsCountablyGenerated] [l.NeBot] {k : ℕ}
    (hk : k ≤ d)
    (hcobdd : IsCoboundedUnder (· ≤ ·) l
      (fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 hk))
    (hcont : ∀ n : ℕ, Tendsto (fun i => ∫ x, Real.log (Sprod (B i) T k (n + 1) x) ∂μ) l
      (𝓝 (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ))) :
    limsup (fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 hk) l
      ≤ gammaK hT hA hAmeas hint hint' hk := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  -- `Γ_k(A) = ⨅ n, a_n(A)`; for each `n`, `limsup_i Γ_k(B i) ≤ a_n(A)`.
  rw [GammaK_eq_iInf hT hA hAmeas hint hint' hk]
  refine le_ciInf (fun n => ?_)
  -- `Γ_k(B i) ≤ a_n(B i)` for each `i` (infimum lower bound), then take `limsup`.
  set a : ι → ℝ := fun i => (∫ x, Real.log (Sprod (B i) T k (n + 1) x) ∂μ) / (n + 1) with hadef
  have hle : ∀ i, gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 hk ≤ a i := by
    intro i
    rw [GammaK_eq_iInf hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 hk]
    exact ciInf_le (bddBelow_logSprod hmp (hB i).1 (hB i).2.1 hTmeas
      (hB i).2.2.1 (hB i).2.2.2 hk) n
  -- `a i → a_n(A)`, so `limsup a = a_n(A)`.
  have haconv : Tendsto a l (𝓝 ((∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1))) :=
    (hcont n).div_const _
  have hgbdd : IsBoundedUnder (· ≤ ·) l a := haconv.isBoundedUnder_le
  calc limsup (fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 hk) l
      ≤ limsup a l := limsup_le_limsup (Filter.Eventually.of_forall hle) hcobdd hgbdd
    _ = (∫ x, Real.log (Sprod A T k (n + 1) x) ∂μ) / (n + 1) := haconv.limsup_eq

/-- `gammaK` at `k = 1` is the top Lyapunov exponent `topExponent = exponents 0`.
(Local copy with this argument order; the public form is `Oseledets.gammaK_one_eq_topExponent`
in `ExteriorCocycle`.) -/
private theorem gammaK_one_eq_topExponent (hT : Ergodic T μ) :
    gammaK hT hA hAmeas hint hint' (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
      = topExponent hT hA hAmeas hint hint' := by
  rw [gammaK_eq_sum_top_exponents hT hA hAmeas hint hint'
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Finset.univ_unique, Finset.sum_singleton,
    topExponent]
  rfl

/-- **Upper semicontinuity of the top Lyapunov exponent.** Specializing
`GammaK_upperSemicontinuous` to `k = 1` (`λ₁ = Γ_1`): the top exponent is USC in the generator,
`limsup_i λ₁(B i) ≤ λ₁(A)`. As for the partial sums, this is USC, **not** continuity. -/
theorem topExponent_upperSemicontinuous (hT : Ergodic T μ) [l.IsCountablyGenerated] [l.NeBot]
    (hcobdd : IsCoboundedUnder (· ≤ ·) l
      (fun i => topExponent hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2))
    (hcont : ∀ n : ℕ, Tendsto (fun i => ∫ x, Real.log (Sprod (B i) T 1 (n + 1) x) ∂μ) l
      (𝓝 (∫ x, Real.log (Sprod A T 1 (n + 1) x) ∂μ))) :
    limsup (fun i => topExponent hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2) l
      ≤ topExponent hT hA hAmeas hint hint' := by
  have h1 : (1 : ℕ) ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hgeq : ∀ i, gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 h1
      = topExponent hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 :=
    fun i => gammaK_one_eq_topExponent (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 hT
  have hco : IsCoboundedUnder (· ≤ ·) l
      (fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 h1) := by
    have : (fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 h1)
        = fun i => topExponent hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 :=
      funext hgeq
    rw [this]; exact hcobdd
  rw [← gammaK_one_eq_topExponent hA hAmeas hint hint' hT]
  refine le_trans (le_of_eq ?_) (GammaK_upperSemicontinuous hB hA hAmeas hint hint' hT h1 hco hcont)
  exact (limsup_congr (Filter.Eventually.of_forall (fun i => (hgeq i).symm)))

end USC

/-! ## Lower semicontinuity of the bottom exponent

The bottom (smallest) Lyapunov exponent is `λ_d = Γ_d − Γ_{d-1}`. Since `Γ_d = ∫ log|det|` is
*continuous* (linear in `log|det|`, the determinant identity), while `Γ_{d-1}` is only USC, the
difference is **lower** semicontinuous — the opposite asymmetry to the top exponent. -/

section BotLSC

variable [IsProbabilityMeasure μ] {ι : Type*} {l : Filter ι}
    {B : ι → X → Matrix (Fin d) (Fin d) ℝ}
    (hB : ∀ i, (∀ x, (B i x).det ≠ 0) ∧ Measurable (B i) ∧ IntegrableLogNorm (B i) μ
      ∧ IntegrableLogNorm (fun x => (B i x)⁻¹) μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

/-- The bottom Lyapunov exponent, as the telescoping difference `Γ_d − Γ_{d-1}`. By the
telescoping identity (`gammaK_eq_sum_top_exponents`) this equals the smallest entry of the
sorted spectrum `exponents ⟨d-1, …⟩` (recorded in `botExp_eq_exponents_last`). -/
noncomputable def botExp (hT : Ergodic T μ) (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) : ℝ :=
  gammaK hT hA hAmeas hint hint' (le_refl d)
    - gammaK hT hA hAmeas hint hint' (Nat.sub_le d 1)

/-- **The bottom exponent is the smallest entry of the sorted spectrum.** `Γ_d − Γ_{d-1}`
telescopes to the last (smallest) spectral value `exponents ⟨d-1, …⟩`. -/
theorem botExp_eq_exponents_last (hT : Ergodic T μ) :
    botExp hT hA hAmeas hint hint'
      = exponents hT hA hAmeas hint hint' ⟨d - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne d))
          Nat.one_pos⟩ := by
  have hd : d = (d - 1) + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne d))).symm
  -- Express both growth rates as `Finset.range` sums of `chosenLam` and difference off the top.
  rw [botExp, gammaK_eq_sum_top_exponents hT hA hAmeas hint hint' (le_refl d),
    gammaK_eq_sum_top_exponents hT hA hAmeas hint hint' (Nat.sub_le d 1)]
  have hcast : ∀ (k : ℕ) (hk : k ≤ d),
      ∑ i : Fin k, exponents hT hA hAmeas hint hint' (Fin.castLE hk i)
        = ∑ i ∈ Finset.range k, chosenLam hT hA hAmeas hint hint' i := by
    intro k hk
    rw [← Fin.sum_univ_eq_sum_range (fun i => chosenLam hT hA hAmeas hint hint' i) k]
    rfl
  rw [hcast d (le_refl d), hcast (d - 1) (Nat.sub_le d 1)]
  have hsplit : ∑ i ∈ Finset.range d, chosenLam hT hA hAmeas hint hint' i
      = (∑ i ∈ Finset.range (d - 1), chosenLam hT hA hAmeas hint hint' i)
        + chosenLam hT hA hAmeas hint hint' (d - 1) := by
    have hrange : Finset.range d = Finset.range ((d - 1) + 1) := by rw [← hd]
    rw [hrange, Finset.sum_range_succ]
  rw [hsplit, add_sub_cancel_left, exponents]

/-- **Lower semicontinuity of the bottom exponent in the generator.** Under the per-`n` integral
continuity for the top-`(d-1)` sum (`hcont`, supplying USC of `Γ_{d-1}`) and continuity of the
determinant growth `Γ_d = ∫ log|det|` (`hdet`), the bottom exponent is **lower** semicontinuous:
`botExp(A) ≤ liminf_i botExp(B i)`.

CAVEAT (honest): this LSC is the *opposite* asymmetry to the top exponent's USC, and is special
to the bottom exponent: it holds precisely because `Γ_d = ∫ log|det|` is continuous (indeed
linear) in the generator, whereas a generic *interior* exponent `λᵢ = Γ_{i+1} − Γ_i` is a
difference of two USC functions and has **no** semicontinuity in either direction. -/
theorem botExp_lowerSemicontinuous (hT : Ergodic T μ) [l.IsCountablyGenerated] [l.NeBot]
    (hwbelow : IsBoundedUnder (· ≥ ·) l
      (fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 (Nat.sub_le d 1)))
    (hcont : ∀ n : ℕ, Tendsto
      (fun i => ∫ x, Real.log (Sprod (B i) T (d - 1) (n + 1) x) ∂μ) l
      (𝓝 (∫ x, Real.log (Sprod A T (d - 1) (n + 1) x) ∂μ)))
    (hdet : Tendsto (fun i => ∫ x, Real.log |(B i x).det| ∂μ) l
      (𝓝 (∫ x, Real.log |(A x).det| ∂μ))) :
    botExp hT hA hAmeas hint hint'
      ≤ liminf (fun i => botExp hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2) l := by
  -- `Γ_d(·) = sumAllExp(·) = ∫ log|det(·)|` (the determinant identity).
  have hΓd : ∀ j : ι, gammaK hT (hB j).1 (hB j).2.1 (hB j).2.2.1 (hB j).2.2.2 (le_refl d)
      = ∫ x, Real.log |(B j x).det| ∂μ := fun j => by
    rw [gammaK_eq_sum_top_exponents hT (hB j).1 (hB j).2.1 (hB j).2.2.1 (hB j).2.2.2 (le_refl d),
      ← sumAllExp_eq_integral_log_abs_det hT (hB j).1 (hB j).2.1 (hB j).2.2.1 (hB j).2.2.2,
      sumAllExp]
    exact Finset.sum_congr rfl (fun i _ => by rw [Fin.castLE_rfl, id])
  have hΓdA : gammaK hT hA hAmeas hint hint' (le_refl d) = ∫ x, Real.log |(A x).det| ∂μ := by
    rw [gammaK_eq_sum_top_exponents hT hA hAmeas hint hint' (le_refl d),
      ← sumAllExp_eq_integral_log_abs_det hT hA hAmeas hint hint', sumAllExp]
    exact Finset.sum_congr rfl (fun i _ => by rw [Fin.castLE_rfl, id])
  -- continuity of `Γ_d`.
  have hΓd_cont : Tendsto (fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2
      (le_refl d)) l (𝓝 (gammaK hT hA hAmeas hint hint' (le_refl d))) := by
    rw [hΓdA]
    exact hdet.congr (fun i => (hΓd i).symm)
  -- Abbreviations for the two families.
  set u : ι → ℝ := fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 (le_refl d)
    with hudef
  set w : ι → ℝ := fun i => gammaK hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2
    (Nat.sub_le d 1) with hwdef
  set v : ι → ℝ := fun i => - w i with hvdef
  -- `w = Γ_{d-1}(B·)` is bounded below by `hwbelow` and bounded above by the `n = 0` inf term.
  have hw_bddge : IsBoundedUnder (· ≥ ·) l w := hwbelow
  have hw_cobdd_le : IsCoboundedUnder (· ≤ ·) l w := hwbelow.isCoboundedUnder_le
  have hw_bddle : IsBoundedUnder (· ≤ ·) l w := by
    have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
    have hTmeas : Measurable T := hmp.measurable
    -- `w i ≤ a_0(B i)`, and `a_0(B i) → a_0(A)` (the `n = 0` per-`n` continuity).
    have hle0 : ∀ i, w i
        ≤ (∫ x, Real.log (Sprod (B i) T (d - 1) (0 + 1) x) ∂μ) / ((0 : ℕ) + 1) := by
      intro i
      simp only [hwdef]
      rw [GammaK_eq_iInf hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2 (Nat.sub_le d 1)]
      exact ciInf_le (bddBelow_logSprod hmp (hB i).1 (hB i).2.1 hTmeas
        (hB i).2.2.1 (hB i).2.2.2 (Nat.sub_le d 1)) 0
    exact ((hcont 0).div_const ((0 : ℕ) + 1)).isBoundedUnder_le.mono_le
      (Filter.Eventually.of_forall hle0)
  -- USC of `Γ_{d-1}`.
  have hΓdm1_usc : limsup w l ≤ gammaK hT hA hAmeas hint hint' (Nat.sub_le d 1) :=
    GammaK_upperSemicontinuous hB hA hAmeas hint hint' hT (Nat.sub_le d 1)
      hwbelow.isCoboundedUnder_le hcont
  -- `botExp(B i) = u i + v i`.
  have hbot : (fun i => botExp hT (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2) = u + v := by
    funext i; rw [botExp]; simp only [hudef, hwdef, hvdef, Pi.add_apply, sub_eq_add_neg]
  -- `u` converges to `Γ_d(A)` (bounded both ways).
  have hu_bddge : IsBoundedUnder (· ≥ ·) l u := hΓd_cont.isBoundedUnder_ge
  have hu_bddle : IsBoundedUnder (· ≤ ·) l u := hΓd_cont.isBoundedUnder_le
  -- `v = -w` bounded both ways and cobounded below.
  have hv_bddge : IsBoundedUnder (· ≥ ·) l v := by
    obtain ⟨b, hb⟩ := hw_bddle
    exact ⟨-b, by simpa only [hvdef, eventually_map, neg_le_neg_iff] using hb⟩
  have hv_bddle : IsBoundedUnder (· ≤ ·) l v := by
    obtain ⟨b, hb⟩ := hw_bddge
    exact ⟨-b, by simpa only [hvdef, eventually_map, neg_le_neg_iff] using hb⟩
  have hv_cobdd : IsCoboundedUnder (· ≥ ·) l v := hv_bddle.isCoboundedUnder_ge
  -- `liminf u + liminf v ≤ liminf (u+v)`.
  have hkey : liminf u l + liminf v l ≤ liminf (u + v) l :=
    le_liminf_add hu_bddge hu_bddle hv_bddge hv_cobdd
  have hliminf_u : liminf u l = gammaK hT hA hAmeas hint hint' (le_refl d) := hΓd_cont.liminf_eq
  -- `-Γ_{d-1}(A) ≤ liminf v` because `limsup w ≤ Γ_{d-1}(A)`.
  have hliminf_v : - gammaK hT hA hAmeas hint hint' (Nat.sub_le d 1) ≤ liminf v l := by
    refine (le_liminf_iff hv_cobdd hv_bddge).2 (fun y hy => ?_)
    have hwlt : limsup w l < -y := lt_of_le_of_lt hΓdm1_usc (lt_neg.mp hy)
    filter_upwards [eventually_lt_of_limsup_lt hwlt hw_bddle] with i hi
    simpa only [hvdef] using lt_neg.mpr (by linarith [hi] : w i < -y)
  rw [botExp, hbot]
  calc gammaK hT hA hAmeas hint hint' (le_refl d)
        - gammaK hT hA hAmeas hint hint' (Nat.sub_le d 1)
      = gammaK hT hA hAmeas hint hint' (le_refl d)
        + (- gammaK hT hA hAmeas hint hint' (Nat.sub_le d 1)) := by ring
    _ ≤ liminf u l + liminf v l := by rw [hliminf_u]; linarith [hliminf_v]
    _ ≤ liminf (u + v) l := hkey

end BotLSC

/-! ## Per-`n` integral continuity under a.e. generator convergence + uniform integrability
(regime 2, the Vitali route)

The second per-`n` continuity regime replaces the *fixed integrable envelope* of regime 1
(`tendsto_integral_logSprod_of_dominated`) by the honest `L¹`-log control hypothesis of **uniform
integrability** of the integrand family `log Sprod_k(B m, n, ·)`, together with `μ`-a.e.
convergence of the *generators* `B m → A`. The latter is purely analytic: it propagates through
the cocycle (a finite matrix product / orbit composition), the Gram matrix, its sorted
eigenvalues (Weyl perturbation, `tendsto_eigenvalues₀`), the singular values
(`gram_eigenvalues₀_eq_sq_singularValues`), and finally `Sprod = ∏ σ` and `Real.log`. This is the
`HELPER` `ae_tendsto_logSprod_of_ae_tendsto_generator`. The integral continuity is then Vitali's
convergence theorem (`tendsto_Lp_finite_of_tendsto_ae` + `tendsto_integral_of_L1'`), packaged in
the `PRIMARY` theorem `tendsto_integral_logSprod_of_unifIntegrable` and combined with the helper in
the `WRAPPER` `tendsto_integral_logSprod_of_ae_unifIntegrable`.

**Honest caveat (mandatory).** Uniform integrability is an *explicit hypothesis*, not something
derived from pure `L¹`-log convergence of the generators: `log Sprod` is **not** `L¹`-continuous in
`posLog‖·‖`, so pure `L¹`-log convergence of the generators does **not** imply integral continuity.
Uniform integrability is the correct `L¹`-log control that, together with a.e. convergence, makes
the Vitali theorem applicable. Note also that the a.e. *generator*-convergence helper genuinely
needs `T` to be measure-preserving: the integrand at `x` samples the generator along the finite
orbit `x, Tx, …, T^{n-1}x`, so propagating an a.e. statement from `x` to its orbit requires
quasi-measure-preservation of `T`. (At the wrapper's call site this is supplied by `Ergodic.T`.) -/

section RegimeTwo

variable {B : ℕ → X → Matrix (Fin d) (Fin d) ℝ}
    {A : X → Matrix (Fin d) (Fin d) ℝ}

omit [NeZero d] [MeasurableSpace X] μ in
/-- **Cocycle continuity along a convergent orbit.** If, at every orbit point `T^[j] x`, the
generators converge `B m (T^[j] x) → A (T^[j] x)`, then the cocycle iterate converges
`cocycle (B m) T n x → cocycle A T n x`. The cocycle is a finite matrix product over the orbit
(`cocycle_succ`), so this is continuity of multiplication (`Tendsto.mul`, the matrix
`ContinuousMul`) by induction on `n`. -/
private theorem tendsto_cocycle_of_tendsto_orbit {x : X}
    (horb : ∀ j : ℕ, Tendsto (fun m => B m (T^[j] x)) atTop (𝓝 (A (T^[j] x)))) (n : ℕ) :
    Tendsto (fun m => cocycle (B m) T n x) atTop (𝓝 (cocycle A T n x)) := by
  induction n generalizing x with
  | zero => simp only [cocycle_zero]; exact tendsto_const_nhds
  | succ n ih =>
    simp only [cocycle_succ]
    -- IH at the shifted base `T x`: the orbit of `T x` is the tail of the orbit of `x`.
    have horbT : ∀ j : ℕ, Tendsto (fun m => B m (T^[j] (T x))) atTop (𝓝 (A (T^[j] (T x)))) := by
      intro j
      rw [← Function.iterate_succ_apply]
      exact horb (j + 1)
    exact (ih horbT).mul (horb 0)

omit [NeZero d] in
/-- **A.e. cocycle continuity from a.e. generator convergence.** Promotes the a.e. generator
convergence `B m → A` to a.e. convergence of the cocycle iterate `cocycle (B m) T n x →
cocycle A T n x`, using quasi-measure-preservation of `T` to push the a.e. statement along the
finite forward orbit sampled by the cocycle. -/
private theorem ae_tendsto_cocycle_of_ae_tendsto_generator
    (hT : MeasurePreserving T μ μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun m => B m x) atTop (𝓝 (A x))) (n : ℕ) :
    ∀ᵐ x ∂μ, Tendsto (fun m => cocycle (B m) T n x) atTop (𝓝 (cocycle A T n x)) := by
  -- For each `j`, the a.e. statement holds along `T^[j]`.
  have horb : ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun m => B m (T^[j] x)) atTop (𝓝 (A (T^[j] x))) := by
    rw [ae_all_iff]
    intro j
    exact (hT.iterate j).quasiMeasurePreserving.tendsto_ae hconv
  filter_upwards [horb] with x hx
  exact tendsto_cocycle_of_tendsto_orbit hx n

/-- **HELPER — a.e. continuity of `log Sprod` from a.e. generator convergence.** If the
generators converge `μ`-a.e. `B m → A`, then for each fixed iterate count `n` and `k ≤ d`,
`μ`-a.e. the integrand converges `log Sprod_k(B m, n, x) → log Sprod_k(A, n, x)`.

This is the analytic core of regime 2. The chain is: a.e. `B m → A` propagates to the cocycle
(`ae_tendsto_cocycle_of_ae_tendsto_generator`); the Gram matrix `Qₙ = cocycleᵀ · cocycle`
converges (continuity of transpose and matrix multiplication); its sorted eigenvalues converge
(Weyl perturbation, `tendsto_eigenvalues₀`); the squared singular values equal the Gram
eigenvalues (`gram_eigenvalues₀_eq_sq_singularValues`), so each `σᵢ(B m)² → σᵢ(A)²`, hence
`σᵢ(B m) → σᵢ(A)` (`Real.sqrt` continuity, `σᵢ ≥ 0`); the finite product
`Sprod = ∏_{i<k} σᵢ` converges (`tendsto_finsetProd`); and `Real.log` is continuous at the strictly
positive limit `Sprod_k(A, n, x) > 0` (`Sprod_pos`).

The measure-preserving hypothesis `hT` is genuinely required: `log Sprod_k(·, n, x)` samples the
generator along the finite orbit `x, Tx, …, T^{n-1}x`, so an a.e. statement at `x` propagates to
its orbit only through quasi-measure-preservation of `T`. -/
theorem ae_tendsto_logSprod_of_ae_tendsto_generator (hA : ∀ x, (A x).det ≠ 0) {k : ℕ}
    (hk : k ≤ d) {n : ℕ} (hT : MeasurePreserving T μ μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun m => B m x) atTop (𝓝 (A x))) :
    ∀ᵐ x ∂μ, Tendsto (fun m => Real.log (Sprod (B m) T k n x)) atTop
      (𝓝 (Real.log (Sprod A T k n x))) := by
  filter_upwards [ae_tendsto_cocycle_of_ae_tendsto_generator hT hconv n] with x hcoc
  -- The Gram matrix converges (transpose and matrix multiplication are continuous).
  have htr : Tendsto (fun m => Matrix.transpose (cocycle (B m) T n x)) atTop
      (𝓝 (Matrix.transpose (cocycle A T n x))) :=
    ((Continuous.matrix_transpose continuous_id).tendsto (cocycle A T n x)).comp hcoc
  have hgram : Tendsto (fun m => gram (B m) T n x) atTop (𝓝 (gram A T n x)) := by
    simpa only [gram, Matrix.transpose] using htr.mul hcoc
  -- Each (top-`k`) squared singular value converges, via the Gram eigenvalues (Weyl perturbation).
  have hsq : ∀ i : ℕ, i < d →
      Tendsto (fun m => (Matrix.toEuclideanLin (cocycle (B m) T n x)).singularValues i)
        atTop (𝓝 ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i)) := by
    intro i hi
    have hic : i < Fintype.card (Fin d) := by rwa [Fintype.card_fin]
    -- Sorted Gram eigenvalues converge (Weyl).
    have heig := Weyl.tendsto_eigenvalues₀ (M := fun m => gram (B m) T n x) (M₀ := gram A T n x)
      (fun m => (gram_posSemidef (B m) T n x).isHermitian) (gram_posSemidef A T n x).isHermitian
      hgram ⟨i, hic⟩
    -- Rewrite eigenvalues as `σᵢ²` on both sides.
    simp only [gram_eigenvalues₀_eq_sq_singularValues] at heig
    -- `σᵢ = √(σᵢ²)`, so `√` continuity transports the convergence.
    have hAnn : 0 ≤ (Matrix.toEuclideanLin (cocycle A T n x)).singularValues i :=
      (Matrix.toEuclideanLin (cocycle A T n x)).singularValues_nonneg i
    have hsqrt := heig.sqrt
    rwa [Real.sqrt_sq hAnn,
      funext (fun m => Real.sqrt_sq
        ((Matrix.toEuclideanLin (cocycle (B m) T n x)).singularValues_nonneg i))] at hsqrt
  -- The finite product `Sprod = ∏_{i<k} σᵢ` converges.
  have hprod : Tendsto (fun m => Sprod (B m) T k n x) atTop (𝓝 (Sprod A T k n x)) := by
    simp only [Sprod]
    exact tendsto_finsetProd (Finset.range k)
      (fun i hi => hsq i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
  -- `Real.log` is continuous at the strictly positive limit `Sprod_k(A, n, x) > 0`.
  exact hprod.log (ne_of_gt (Sprod_pos hA hk n x))

omit [NeZero d] in
/-- **PRIMARY — per-`n` integral continuity via uniform integrability (Vitali, regime 2).**
For a fixed iterate count `n` and `k ≤ d`, if the integrand family `log Sprod_k(B m, n, ·)` is
uniformly integrable (`hui`), `μ`-a.e.-strongly-measurable (`hBmeas`), and converges `μ`-a.e. to
`log Sprod_k(A, n, ·)` (`hlim`, with the limit `L¹`, `hAmemLp`), then the integrals converge:
`∫ log Sprod_k(B m, n) → ∫ log Sprod_k(A, n)`.

This is Vitali's convergence theorem: a.e. convergence with uniform integrability yields
`L¹`-convergence (`tendsto_Lp_finite_of_tendsto_ae`), which gives integral convergence
(`tendsto_integral_of_L1'`). Uniform integrability is the honest `L¹`-log control replacing the
fixed envelope of regime 1; it is **not** derivable from pure `L¹`-log convergence of the
generators (`log Sprod` is not `L¹`-continuous in `posLog‖·‖`) and is kept as a hypothesis. -/
theorem tendsto_integral_logSprod_of_unifIntegrable [IsFiniteMeasure μ] {k n : ℕ}
    (hBmeas : ∀ m, AEStronglyMeasurable (fun x => Real.log (Sprod (B m) T k n x)) μ)
    (hAmemLp : MemLp (fun x => Real.log (Sprod A T k n x)) 1 μ)
    (hui : UnifIntegrable (fun m x => Real.log (Sprod (B m) T k n x)) 1 μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => Real.log (Sprod (B m) T k n x)) atTop
      (𝓝 (Real.log (Sprod A T k n x)))) :
    Tendsto (fun m => ∫ x, Real.log (Sprod (B m) T k n x) ∂μ) atTop
      (𝓝 (∫ x, Real.log (Sprod A T k n x) ∂μ)) := by
  set f : ℕ → X → ℝ := fun m x => Real.log (Sprod (B m) T k n x) with hfdef
  set g : X → ℝ := fun x => Real.log (Sprod A T k n x) with hgdef
  -- Vitali: a.e. convergence + uniform integrability ⟹ `L¹`-convergence.
  have hL1 : Tendsto (fun m => eLpNorm (f m - g) 1 μ) atTop (𝓝 0) :=
    MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (le_refl 1) one_ne_top hBmeas hAmemLp hui hlim
  -- Eventually each `f m` is integrable: `eLpNorm (f m - g) 1 μ` is eventually finite, and
  -- `f m = (f m - g) + g` with `g ∈ L¹`.
  have hFi : ∀ᶠ m in atTop, Integrable (f m) μ := by
    have hev : ∀ᶠ m in atTop, eLpNorm (f m - g) 1 μ < ⊤ := by
      have := (ENNReal.tendsto_atTop_zero.mp hL1) 1 (by norm_num)
      obtain ⟨N, hN⟩ := this
      filter_upwards [eventually_ge_atTop N] with m hm
      exact lt_of_le_of_lt (hN m hm) (by norm_num)
    filter_upwards [hev] with m hm
    have hsub : MemLp (f m - g) 1 μ :=
      ⟨(hBmeas m).sub hAmemLp.aestronglyMeasurable, hm⟩
    have hfm : MemLp (f m) 1 μ := by
      have heq : f m = (f m - g) + g := by
        funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [heq]; exact hsub.add hAmemLp
    exact (memLp_one_iff_integrable.mp hfm)
  -- Integral convergence from `L¹`-convergence.
  exact MeasureTheory.tendsto_integral_of_L1' g (memLp_one_iff_integrable.mp hAmemLp) hFi hL1

/-- **WRAPPER — per-`n` integral continuity from a.e. generator convergence + uniform
integrability.** Combines the `HELPER` (a.e. generator convergence `B m → A` ⟹ a.e. integrand
convergence) with the `PRIMARY` Vitali theorem. The output is exactly the per-`n` continuity
hypothesis `hcont` consumed by `GammaK_upperSemicontinuous`, `topExponent_upperSemicontinuous`,
and `botExp_lowerSemicontinuous` (those take `hcont` over any countably-generated `NeBot` filter,
and `atTop` on `ℕ` qualifies). It thus delivers regime-2 semicontinuity with no change to those
theorems — see `GammaK_upperSemicontinuous_of_ae_unifIntegrable`.

The measure-preserving hypothesis is supplied at the USC call site by `Ergodic.toMeasurePreserving`.
Uniform integrability remains an explicit hypothesis (the honest `L¹`-log control), not derived
from pure `L¹`-log convergence of the generators. -/
theorem tendsto_integral_logSprod_of_ae_unifIntegrable [IsProbabilityMeasure μ]
    (hA : ∀ x, (A x).det ≠ 0) {k : ℕ} (hk : k ≤ d) {n : ℕ} (hT : MeasurePreserving T μ μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun m => B m x) atTop (𝓝 (A x)))
    (hBmeas : ∀ m, AEStronglyMeasurable (fun x => Real.log (Sprod (B m) T k n x)) μ)
    (hAmemLp : MemLp (fun x => Real.log (Sprod A T k n x)) 1 μ)
    (hui : UnifIntegrable (fun m x => Real.log (Sprod (B m) T k n x)) 1 μ) :
    Tendsto (fun m => ∫ x, Real.log (Sprod (B m) T k n x) ∂μ) atTop
      (𝓝 (∫ x, Real.log (Sprod A T k n x) ∂μ)) :=
  tendsto_integral_logSprod_of_unifIntegrable hBmeas hAmemLp hui
    (ae_tendsto_logSprod_of_ae_tendsto_generator hA hk hT hconv)

/-- **Regime-2 upper semicontinuity of the partial sums.** Specializing `GammaK_upperSemicontinuous`
to the filter `atTop` on `ℕ` with the regime-2 per-`n` continuity from the `WRAPPER`: under a.e.
generator convergence `B m → A` (`hconv`) and, for each fixed iterate count, a.e.-strong
measurability (`hBmeas`), an `L¹` limit (`hAmemLp`), and uniform integrability (`hui`) of the
integrand family, the partial-sum growth rate `Γ_k` is upper semicontinuous:
`limsup_m Γ_k(B m) ≤ Γ_k(A)`. This shows regime 2 feeds the existing USC machinery with **no change**
to `GammaK_upperSemicontinuous`.

As always, this is *upper* semicontinuity, not continuity, and uniform integrability is an explicit
`L¹`-log hypothesis, not a consequence of pure `L¹`-log generator convergence. -/
theorem GammaK_upperSemicontinuous_of_ae_unifIntegrable [IsProbabilityMeasure μ]
    (hB : ∀ m, (∀ x, (B m x).det ≠ 0) ∧ Measurable (B m) ∧ IntegrableLogNorm (B m) μ
      ∧ IntegrableLogNorm (fun x => (B m x)⁻¹) μ)
    (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A) (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) (hT : Ergodic T μ) {k : ℕ} (hk : k ≤ d)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun m => gammaK hT (hB m).1 (hB m).2.1 (hB m).2.2.1 (hB m).2.2.2 hk))
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun m => B m x) atTop (𝓝 (A x)))
    (hBmeas : ∀ n m, AEStronglyMeasurable (fun x => Real.log (Sprod (B m) T k (n + 1) x)) μ)
    (hAmemLp : ∀ n, MemLp (fun x => Real.log (Sprod A T k (n + 1) x)) 1 μ)
    (hui : ∀ n, UnifIntegrable (fun m x => Real.log (Sprod (B m) T k (n + 1) x)) 1 μ) :
    limsup (fun m => gammaK hT (hB m).1 (hB m).2.1 (hB m).2.2.1 (hB m).2.2.2 hk) atTop
      ≤ gammaK hT hA hAmeas hint hint' hk :=
  GammaK_upperSemicontinuous hB hA hAmeas hint hint' hT hk hcobdd
    (fun n => tendsto_integral_logSprod_of_ae_unifIntegrable hA hk hT.toMeasurePreserving hconv
      (hBmeas n) (hAmemLp n) (hui n))

end RegimeTwo

end Oseledets
