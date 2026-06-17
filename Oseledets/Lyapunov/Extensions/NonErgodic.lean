/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.OseledetsLimit.Limit
import Oseledets.Lyapunov.Extensions.Spectrum

/-!
# The non-ergodic Lyapunov spectrum (exponents as invariant functions)

This module is the **non-ergodic relaxation** of the singular-value layer. In the ergodic
theory (`Oseledets.tendsto_gammaK`, `Oseledets.exists_lam_tendsto_singularValue`,
`Oseledets.exponents`) the partial-sum limits `Γ_k` and the per-`σ` Lyapunov exponents
`λᵢ = Γ_{i+1} − Γ_i` are almost-everywhere **constants**. Without ergodicity these limits
still exist almost everywhere, but they are now `T`-**invariant measurable functions**
rather than constants. (Heuristically the limit is the conditional expectation
`μ[log sprod_k(·, 1) | invariants T]`; the theorems below prove only its existence,
`T`-invariance, and integrability — not that identification.)

The whole development is a *mechanical re-derivation* swapping the ergodic Kingman theorem
(`Oseledets.tendsto_kingman_ergodic`) for the non-ergodic one (`Oseledets.tendsto_kingman`):
the latter produces a `T`-invariant integrable limit `G` instead of a constant `c`. Every
integrability / positivity / subadditivity fact about `log sprod_k` that the ergodic proof
discharged (`integrable_logSprod`, `bddBelow_logSprod`, `sprod_pos`,
`isSubadditiveCocycle_logSprod`) is reused verbatim — only the `Ergodic` hypothesis is
dropped in favour of bare `MeasurePreserving`. The pointwise telescoping that turns the
`Γ_k` limits into per-`σ` exponents (`tendsto_log_singularValue`) is unchanged.

The ergodic results are recovered as the special case where the σ-algebra of `T`-invariants
is trivial (so each invariant function is a.e. constant): see
`Oseledets.tendsto_gammaK_of_integrableLogNorm` and
`Oseledets.exists_lam_tendsto_singularValue`.

## Main results

* `Oseledets.tendsto_gammaK_nonergodic` — the partial-sum limit `Γ_k` as a `T`-invariant
  integrable function `G : X → ℝ`, with `(1/n) log sprod_k → G` almost everywhere.
* `Oseledets.exists_exponents_nonergodic` — the full Lyapunov spectrum as a family of
  `T`-invariant integrable functions `lam : ℕ → X → ℝ`, each the a.e. limit of
  `(1/n) log σᵢ(A⁽ⁿ⁾)`.
* `Oseledets.exists_sumPosExp_nonergodic` — the sum of the positive exponents, as a
  `T`-invariant integrable function obtained by summing the positive part of the spectrum.

## References

* L. Arnold, *Random Dynamical Systems*, Springer Monographs in Mathematics, 1998.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
variable {μ : Measure X} {T : X → X}

section NonErgodic

variable [IsFiniteMeasure μ] [NeZero d]

/-- **The non-ergodic partial-sum limit `Γ_k`.** For a measure-preserving `T`, an
everywhere-invertible measurable cocycle generator with `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹`, and
`k ≤ d`, the normalized `log sprod_k` converges `μ`-a.e. to a `T`-invariant integrable
function `G` (no ergodicity assumed). This is the
non-ergodic analogue of `tendsto_gammaK_of_integrableLogNorm`: the constant `Γ_k` is
replaced by the invariant function `G`. -/
theorem tendsto_gammaK_nonergodic (hmp : MeasurePreserving T μ μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    {k : ℕ} (hk : k ≤ d) :
    ∃ G : X → ℝ, (G ∘ T =ᵐ[μ] G) ∧ Integrable G μ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (sprod A T k n x))
        atTop (𝓝 (G x)) := by
  classical
  have hTmeas : Measurable T := hmp.measurable
  -- The non-ergodic Kingman theorem applied to the subadditive cocycle `log sprod_k`,
  -- reusing the same integrability / bounded-below / positivity facts as the ergodic case.
  obtain ⟨G, hGinv, hGint, hGconv⟩ := tendsto_kingman hmp
    (isSubadditiveCocycle_logSprod A k (fun j y => sprod_pos hA hk j y))
    (fun n => integrable_logSprod hmp hA hAmeas hTmeas hint hint' hk n)
    (bddBelow_logSprod hmp hA hAmeas hTmeas hint hint' hk)
  exact ⟨G, hGinv, hGint, hGconv⟩

/-- **The non-ergodic Lyapunov spectrum.** For a measure-preserving `T`, an
everywhere-invertible measurable cocycle generator with `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹`, there is
a family of `T`-invariant integrable functions `lam : ℕ → X → ℝ` (supported on `[0, d)`)
such that, for each `i < d` and `μ`-a.e. `x`, the normalized log of the `i`-th singular
value of `A⁽ⁿ⁾` converges to `lam i x`. Without ergodicity the exponents are invariant
measurable functions instead of the constants of `exists_lam_tendsto_singularValue`.

The functions are built as σ-differences `lam i = G_{i+1} − G_i` of the partial-sum limits
of `tendsto_gammaK_nonergodic`; the per-`σ` telescoping (`tendsto_log_singularValue`) is the
same pointwise argument used in the ergodic case. -/
theorem exists_exponents_nonergodic (hmp : MeasurePreserving T μ μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ lam : ℕ → X → ℝ, (∀ i : ℕ, (lam i ∘ T =ᵐ[μ] lam i)) ∧ (∀ i : ℕ, Integrable (lam i) μ) ∧
      ∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam i x)) := by
  classical
  -- The non-ergodic partial-sum functions `G_k`, for `0 ≤ k ≤ d`, packaged for ALL `k` by
  -- using the genuine limit when `k ≤ d` and the constant `0` otherwise.
  have hG : ∀ k : ℕ, ∃ G : X → ℝ, (k ≤ d → (G ∘ T =ᵐ[μ] G) ∧ Integrable G μ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (sprod A T k n x))
        atTop (𝓝 (G x))) ∧ (d < k → G = 0) := by
    intro k
    by_cases hk : k ≤ d
    · obtain ⟨G, hG⟩ := tendsto_gammaK_nonergodic hmp hA hAmeas hint hint' hk
      exact ⟨G, fun _ => hG, fun hkd => absurd hkd (by omega)⟩
    · exact ⟨0, fun hkd => absurd hkd (by omega), fun _ => rfl⟩
  choose G hG using hG
  -- The exponent functions: `lam i = G_{i+1} − G_i`.
  refine ⟨fun i => fun x => G (i + 1) x - G i x, ?_, ?_, ?_⟩
  · -- invariance: difference of two invariant functions
    intro i
    change (fun x => G (i + 1) x - G i x) ∘ T =ᵐ[μ] fun x => G (i + 1) x - G i x
    by_cases hi : i + 1 ≤ d
    · filter_upwards [(hG (i + 1)).1 hi |>.1, (hG i).1 (by omega) |>.1] with x hx1 hx2
      simp only [Function.comp_apply] at hx1 hx2 ⊢
      rw [hx1, hx2]
    · -- `G (i+1) = 0`; so the difference equals `- G i`, whose invariance we get when `i ≤ d`
      have hGi1 : G (i + 1) = 0 := (hG (i + 1)).2 (by omega)
      by_cases hi' : i ≤ d
      · filter_upwards [(hG i).1 hi' |>.1] with x hx2
        simp only [Function.comp_apply, hGi1, Pi.zero_apply] at hx2 ⊢
        rw [hx2]
      · have hGi : G i = 0 := (hG i).2 (by omega)
        simp only [hGi1, hGi, Pi.zero_apply, sub_self, Function.comp_def]
        rfl
  · -- integrability: difference of two integrable functions (constant `0` is integrable)
    intro i
    change Integrable (fun x => G (i + 1) x - G i x) μ
    by_cases hi : i + 1 ≤ d
    · exact ((hG (i + 1)).1 hi |>.2.1).sub ((hG i).1 (by omega) |>.2.1)
    · have hGi1 : G (i + 1) = 0 := (hG (i + 1)).2 (by omega)
      by_cases hi' : i ≤ d
      · have heq : (fun x => G (i + 1) x - G i x) = fun x => - G i x := by
          funext x; rw [hGi1]; simp
        rw [heq]; exact ((hG i).1 hi' |>.2.1).neg
      · have hGi : G i = 0 := (hG i).2 (by omega)
        have heq : (fun x => G (i + 1) x - G i x) = fun _ => (0 : ℝ) := by
          funext x; rw [hGi1, hGi]; simp
        rw [heq]; exact integrable_zero X ℝ μ
  · -- σ-limit: telescoping difference of the two partial-sum limits
    intro i hi
    filter_upwards [(hG (i + 1)).1 (by omega) |>.2.2, (hG i).1 (by omega) |>.2.2]
      with x hax hbx
    exact tendsto_log_singularValue hA hi hax hbx

/-- **The non-ergodic sum of positive exponents.** Summing the positive parts `max (lam i x) 0`
of the non-ergodic spectrum over `i < d` yields a single `T`-invariant integrable function
`G₊ : X → ℝ`, the non-ergodic analogue of `lyapPosSum`. (Without ergodicity this is an
invariant function, not a constant.) -/
theorem exists_sumPosExp_nonergodic (hmp : MeasurePreserving T μ μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ (lam : ℕ → X → ℝ) (Gpos : X → ℝ),
      (Gpos ∘ T =ᵐ[μ] Gpos) ∧ Integrable Gpos μ ∧
      (∀ x, Gpos x = ∑ i ∈ Finset.range d, max (lam i x) 0) ∧
      (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        atTop (𝓝 (lam i x))) := by
  obtain ⟨lam, hinv, hintlam, hlim⟩ :=
    exists_exponents_nonergodic hmp hA hAmeas hint hint'
  refine ⟨lam, fun x => ∑ i ∈ Finset.range d, max (lam i x) 0, ?_, ?_, fun _ => rfl, hlim⟩
  · -- invariance of a finite sum of positive parts of invariant functions
    have hall : ∀ᵐ x ∂μ, ∀ i ∈ Finset.range d, lam i (T x) = lam i x := by
      rw [eventually_all_finset]
      intro i _
      filter_upwards [hinv i] with x hx using hx
    filter_upwards [hall] with x hx
    simp only [Function.comp_apply]
    exact Finset.sum_congr rfl fun i hi => by rw [hx i hi]
  · -- integrability of a finite sum of positive parts of integrable functions
    refine integrable_finsetSum _ fun i _ => ?_
    have heq : (fun x => max (lam i x) 0) = fun x => (lam i x)⁺ := by
      funext x; rw [posPart_def]
    rw [heq]
    exact (hintlam i).pos_part

end NonErgodic

end Oseledets
