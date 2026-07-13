/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapFourierDecay
import ErgodicTheory.Examples.CatMapNormForm
import ErgodicTheory.Examples.CatMapCorrExpansion
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exponential decay of correlations for the Arnold cat map

This module proves the **repository's first quantitative-rate mixing statement** for the Arnold
cat map `catTorus` on the `2`-torus `𝕋²`, upgrading the qualitative `tendsto_catCorr` to an
explicit geometric rate.  For observables in the Fourier-decay class `FourierDecay s` (`s > 2`)
the centred correlation decays exponentially:

`‖∫ conj f · (g ∘ Tᵏ) − (∫ conj f)(∫ g)‖ ≤ C · θᵏ`,  with  `θ = λ^(-(s-2)/4) < 1`,

`λ = (3 + √5)/2` the expanding eigenvalue.  A real-observable corollary (feeding Green–Kubo
sums downstream) records `|∫ f · (f ∘ Tᵏ) − (∫ f)²| ≤ C θᵏ`.

## Mechanism

The proof is the Fourier / character proof of exponential mixing for hyperbolic toral
automorphisms (Einsiedler–Ward, *Ergodic Theory with a View Towards Number Theory*, Ch. 2; see
Katok–Hasselblatt §17–18 for the Anosov decay context).  Parseval expands the correlation as a
bilinear character sum (`hasSum_correlation_fourier_ne_zero`); the Koopman action shifts one index
by the matrix power `Aᵏ`, and the quantitative expansion of the invariant norm form on the dual
lattice (discriminant `5`, `lemma_beta`) forces geometric decay of the shifted coefficient.  The
frequency lattice `{b ≠ 0}` splits at radius `⟨b⟩ = λ^(k/2)`: on the near part the `Aᵏ`-expansion
gives `⟨Aᵏ b⟩ ≥ (√5-2)λ^(k/2)`, on the far part the tail sum `tsum_bracket_rpow_tail_le` supplies
the decay `λ^(-k(s-2)/4)`.

## Main results

* `ErgodicTheory.CatMapToral.lam_rpow_lt_one` — `θ = λ^(-(s-2)/4) < 1` for `s > 2`.
* `ErgodicTheory.CatMapToral.catCorr_tsum_norm_le` — the geometric tail estimate on the centred
  character sum, with an explicit constant.
* `ErgodicTheory.CatMapToral.catCorr_decay` — **the headline**: exponential decay of the complex
  correlation.
* `ErgodicTheory.CatMapToral.catCorr_decay_real₂`,
  `ErgodicTheory.CatMapToral.catCorr_decay_real` — real-observable corollaries.
-/

open MeasureTheory UnitAddTorus Matrix
open scoped ComplexConjugate ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
sibling cat-map Fourier modules: with this instance `volume` on `𝕋²` is the product Haar
probability measure used by the Fourier API.  Local instances do not cross files, so the trio is
repeated here. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catDecay :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catDecay :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catDecay :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## Glue between the Japanese bracket and the sup-norm form -/

/-- The Japanese bracket is the `max 1` of the sup-norm of the real cast. -/
lemma bracket_eq_max_one_nr (n : Fin 2 → ℤ) : bracket n = max 1 (nr (toR n)) := rfl

/-- The sup-norm of the real cast is dominated by the Japanese bracket. -/
lemma nr_toR_le_bracket (n : Fin 2 → ℤ) : nr (toR n) ≤ bracket n := by
  rw [bracket_eq_max_one_nr]; exact le_max_right _ _

/-! ## The decay base `θ = λ^(-(s-2)/4)` -/

/-- The explicit decay base is `< 1` for `s > 2` (since `λ > 1` and the exponent is negative). -/
lemma lam_rpow_lt_one {s : ℝ} (hs : 2 < s) : lam ^ (-(s - 2) / 4 : ℝ) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg one_lt_lam
  linarith

/-! ## The geometric tail estimate on the centred character sum -/

set_option maxHeartbeats 1600000 in
-- The near/far lattice split assembles many `tsum` comparisons, subtype reindexings and `rpow`
-- exponent rewrites into a single elaboration that exceeds the default heartbeat budget.
/-- **Geometric tail estimate.**  For `f g` in the Fourier-decay class `FourierDecay s` (`s > 2`),
the centred character sum over `{b ≠ 0}` is summable and bounded by `C · θᵏ` with the explicit
decay base `θ = λ^(-(s-2)/4)` and an explicit constant `C`.  This is the analytic heart of the
exponential-mixing statement; the near/far split of the frequency lattice at radius `λ^(k/2)` is
carried out in the proof. -/
theorem catCorr_tsum_norm_le {s : ℝ} (hs : 2 < s) {f g : T2 → ℂ}
    (hf : FourierDecay s f) (hg : FourierDecay s g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      (Summable (fun b : {b : Fin 2 → ℤ // b ≠ 0} =>
          ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖
            * ‖mFourierCoeff g (b : Fin 2 → ℤ)‖)) ∧
      (∑' b : {b : Fin 2 → ℤ // b ≠ 0},
          ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖
            * ‖mFourierCoeff g (b : Fin 2 → ℤ)‖)
        ≤ C * (lam ^ (-(s - 2) / 4 : ℝ)) ^ k := by
  obtain ⟨K, hK, hKb⟩ := hf
  obtain ⟨L, hL, hLb⟩ := hg
  have hlam0 : (0 : ℝ) < lam := by linarith [one_lt_lam]
  have hlam1 : (1 : ℝ) ≤ lam := (one_lt_lam).le
  have ht5 : (0 : ℝ) < Real.sqrt 5 - 2 := by linarith [two_lt_sqrt5]
  set θ : ℝ := lam ^ (-(s - 2) / 4 : ℝ) with hθ
  refine ⟨K * L * (Real.sqrt 5 - 2) ^ (-s) * (∑' n, bracket n ^ (-s))
      + K * L * (∑' n, bracket n ^ (-((s + 2) / 2))), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑' n : Fin 2 → ℤ, bracket n ^ (-s) :=
      tsum_nonneg (fun n => Real.rpow_nonneg (bracket_nonneg n) _)
    have h2 : (0 : ℝ) ≤ ∑' n : Fin 2 → ℤ, bracket n ^ (-((s + 2) / 2)) :=
      tsum_nonneg (fun n => Real.rpow_nonneg (bracket_nonneg n) _)
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hK hL) (Real.rpow_nonneg ht5.le _)) h1)
      (mul_nonneg (mul_nonneg hK hL) h2)
  intro k
  -- The radius `R = λ^(k/2)` and its algebra.
  set R : ℝ := lam ^ ((k : ℝ) / 2) with hR_def
  have hRpos : 0 < R := by rw [hR_def]; exact Real.rpow_pos_of_pos hlam0 _
  have hR1 : 1 ≤ R := by rw [hR_def]; exact Real.one_le_rpow hlam1 (by positivity)
  have hRsq : R * R = lam ^ k := by
    rw [hR_def, ← Real.rpow_add hlam0, show (k : ℝ) / 2 + (k : ℝ) / 2 = (k : ℝ) by ring,
      Real.rpow_natCast]
  have hθk : θ ^ k = lam ^ ((-(s - 2) / 4) * (k : ℝ)) := by
    rw [hθ, ← Real.rpow_natCast (lam ^ (-(s - 2) / 4 : ℝ)) k, ← Real.rpow_mul hlam0.le]
  have hRtail : R ^ (-((s - 2) / 2)) = θ ^ k := by
    rw [hθk, hR_def, ← Real.rpow_mul hlam0.le]; congr 1; ring
  have hRs_le : R ^ (-s) ≤ θ ^ k := by
    rw [hR_def, ← Real.rpow_mul hlam0.le, hθk]
    apply Real.rpow_le_rpow_of_exponent_le hlam1
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))
      (by linarith : (0 : ℝ) ≤ s + 2)]
  -- The correlation term function and its dominating bound.
  set term : {b : Fin 2 → ℤ // b ≠ 0} → ℝ :=
    fun b => ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖ * ‖mFourierCoeff g (b : Fin 2 → ℤ)‖
    with hterm_def
  have hbrT_sum : Summable (fun b : {b : Fin 2 → ℤ // b ≠ 0} => bracket (b : Fin 2 → ℤ) ^ (-s)) :=
    (summable_bracket_rpow hs).subtype (· ≠ 0)
  have hdom_sum : Summable
      (fun b : {b : Fin 2 → ℤ // b ≠ 0} => (K * L) * bracket (b : Fin 2 → ℤ) ^ (-s)) :=
    ((summable_bracket_rpow hs).mul_left (K * L)).subtype (· ≠ 0)
  -- Uniform bound `‖ĉ_f(Aᵏ b)‖ ≤ K`, hence `term b ≤ K·L·⟨b⟩^(-s)`.
  have hdom : ∀ b : {b : Fin 2 → ℤ // b ≠ 0},
      term b ≤ (K * L) * bracket (b : Fin 2 → ℤ) ^ (-s) := by
    intro b
    have hfb : ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖ ≤ K := by
      refine (hKb _).trans ?_
      calc K * bracket (catℤ ^ k *ᵥ (b : Fin 2 → ℤ)) ^ (-s)
          ≤ K * 1 := mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos (one_le_bracket _) (by linarith)) hK
        _ = K := mul_one K
    calc term b ≤ K * (L * bracket (b : Fin 2 → ℤ) ^ (-s)) :=
          mul_le_mul hfb (hLb _) (norm_nonneg _) hK
      _ = (K * L) * bracket (b : Fin 2 → ℤ) ^ (-s) := by ring
  have hterm_sum : Summable term :=
    Summable.of_nonneg_of_le
      (fun b => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hdom hdom_sum
  -- Near-region pointwise bound via the norm-form expansion `lemma_beta`.
  have key_small : ∀ b : {b : Fin 2 → ℤ // b ≠ 0}, bracket (b : Fin 2 → ℤ) ≤ R →
      term b ≤ (K * L * ((Real.sqrt 5 - 2) * R) ^ (-s)) * bracket (b : Fin 2 → ℤ) ^ (-s) := by
    intro b hbR
    have hn : (b : Fin 2 → ℤ) ≠ 0 := b.2
    have hnrpos : 0 < nr (toR (b : Fin 2 → ℤ)) := nr_toR_pos hn
    have hnr_le : nr (toR (b : Fin 2 → ℤ)) ≤ R := (nr_toR_le_bracket _).trans hbR
    have hbeta := lemma_beta hn k
    have hprod : (Real.sqrt 5 - 2) * R * nr (toR (b : Fin 2 → ℤ))
        ≤ (Real.sqrt 5 - 2) * lam ^ k := by
      calc (Real.sqrt 5 - 2) * R * nr (toR (b : Fin 2 → ℤ))
          ≤ (Real.sqrt 5 - 2) * R * R :=
            mul_le_mul_of_nonneg_left hnr_le (mul_nonneg ht5.le hRpos.le)
        _ = (Real.sqrt 5 - 2) * (R * R) := by ring
        _ = (Real.sqrt 5 - 2) * lam ^ k := by rw [hRsq]
    have ht5R_le : (Real.sqrt 5 - 2) * R ≤ nr (toR (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))) :=
      ((le_div_iff₀ hnrpos).mpr hprod).trans hbeta
    have hbrAk : (Real.sqrt 5 - 2) * R ≤ bracket (catℤ ^ k *ᵥ (b : Fin 2 → ℤ)) :=
      ht5R_le.trans (nr_toR_le_bracket _)
    have ht5R_pos : 0 < (Real.sqrt 5 - 2) * R := mul_pos ht5 hRpos
    have hf_rpow : bracket (catℤ ^ k *ᵥ (b : Fin 2 → ℤ)) ^ (-s)
        ≤ ((Real.sqrt 5 - 2) * R) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos ht5R_pos hbrAk (by linarith)
    have hff : ‖mFourierCoeff f (catℤ ^ k *ᵥ (b : Fin 2 → ℤ))‖
        ≤ K * ((Real.sqrt 5 - 2) * R) ^ (-s) :=
      (hKb _).trans (mul_le_mul_of_nonneg_left hf_rpow hK)
    calc term b ≤ (K * ((Real.sqrt 5 - 2) * R) ^ (-s)) * (L * bracket (b : Fin 2 → ℤ) ^ (-s)) :=
          mul_le_mul hff (hLb _) (norm_nonneg _)
            (mul_nonneg hK (Real.rpow_nonneg ht5R_pos.le _))
      _ = (K * L * ((Real.sqrt 5 - 2) * R) ^ (-s)) * bracket (b : Fin 2 → ℤ) ^ (-s) := by ring
  -- The near/far split of `{b ≠ 0}` at radius `R`.
  set A : Set {b : Fin 2 → ℤ // b ≠ 0} := {x | bracket (x : Fin 2 → ℤ) ≤ R} with hA_def
  -- Injections collapsing the double subtypes to the base lattice.
  have hinjA : Function.Injective
      (fun x : ↥A => ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ)) := by
    intro x y h; exact Subtype.ext (Subtype.ext h)
  have hAsum_le : ∑' x : ↥A, bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ^ (-s)
      ≤ ∑' n : Fin 2 → ℤ, bracket n ^ (-s) :=
    tsum_comp_le_tsum_of_inj (summable_bracket_rpow hs)
      (fun n => Real.rpow_nonneg (bracket_nonneg n) _) hinjA
  -- Near part.
  have hAle : ∑' x : ↥A, term (x : {b : Fin 2 → ℤ // b ≠ 0})
      ≤ (K * L * (Real.sqrt 5 - 2) ^ (-s) * (∑' n, bracket n ^ (-s))) * θ ^ k := by
    have hconst_nonneg : (0 : ℝ) ≤ K * L * ((Real.sqrt 5 - 2) * R) ^ (-s) :=
      mul_nonneg (mul_nonneg hK hL) (Real.rpow_nonneg (mul_pos ht5 hRpos).le _)
    have hcoeff_nonneg : (0 : ℝ)
        ≤ K * L * (Real.sqrt 5 - 2) ^ (-s) * (∑' n, bracket n ^ (-s)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hK hL) (Real.rpow_nonneg ht5.le _))
        (tsum_nonneg (fun n => Real.rpow_nonneg (bracket_nonneg n) _))
    calc ∑' x : ↥A, term (x : {b : Fin 2 → ℤ // b ≠ 0})
        ≤ ∑' x : ↥A, (K * L * ((Real.sqrt 5 - 2) * R) ^ (-s))
            * bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ^ (-s) :=
          (hterm_sum.subtype (· ∈ A)).tsum_le_tsum
            (fun x => key_small (x : {b : Fin 2 → ℤ // b ≠ 0}) x.2)
            ((hbrT_sum.subtype (· ∈ A)).mul_left _)
      _ = (K * L * ((Real.sqrt 5 - 2) * R) ^ (-s))
            * ∑' x : ↥A, bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ^ (-s) :=
          tsum_mul_left
      _ ≤ (K * L * ((Real.sqrt 5 - 2) * R) ^ (-s)) * (∑' n, bracket n ^ (-s)) :=
          mul_le_mul_of_nonneg_left hAsum_le hconst_nonneg
      _ = (K * L * (Real.sqrt 5 - 2) ^ (-s) * (∑' n, bracket n ^ (-s))) * R ^ (-s) := by
          rw [Real.mul_rpow ht5.le hRpos.le]; ring
      _ ≤ (K * L * (Real.sqrt 5 - 2) ^ (-s) * (∑' n, bracket n ^ (-s))) * θ ^ k :=
          mul_le_mul_of_nonneg_left hRs_le hcoeff_nonneg
  -- Far part.
  have hSmem : ∀ n ∈ {n : Fin 2 → ℤ | R ≤ bracket n}, R ≤ bracket n := fun _ hn => hn
  have hmemS : ∀ x : ↥(Aᶜ), R ≤ bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) := by
    intro x
    have hx : (x : {b : Fin 2 → ℤ // b ≠ 0}) ∉ A := (Set.mem_compl_iff _ _).mp x.2
    have hx' : ¬ (bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ≤ R) := hx
    exact (not_le.mp hx').le
  have hinjB : Function.Injective
      (fun x : ↥(Aᶜ) => (⟨((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ),
        hmemS x⟩ : ↥{n : Fin 2 → ℤ | R ≤ bracket n})) := by
    intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.coe_injective (Subtype.coe_injective h)
  have hBsum_le : ∑' x : ↥(Aᶜ), bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ^ (-s)
      ≤ ∑' m : ↥{n : Fin 2 → ℤ | R ≤ bracket n}, bracket (m : Fin 2 → ℤ) ^ (-s) :=
    tsum_comp_le_tsum_of_inj ((summable_bracket_rpow hs).subtype (· ∈ {n | R ≤ bracket n}))
      (fun m => Real.rpow_nonneg (bracket_nonneg _) _) hinjB
  have hBtail : ∑' x : ↥(Aᶜ), bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ^ (-s)
      ≤ (∑' n, bracket n ^ (-((s + 2) / 2))) * R ^ (-((s - 2) / 2)) :=
    hBsum_le.trans (tsum_bracket_rpow_tail_le hs hR1 hSmem)
  have hBle : ∑' x : ↥(Aᶜ), term (x : {b : Fin 2 → ℤ // b ≠ 0})
      ≤ (K * L * (∑' n, bracket n ^ (-((s + 2) / 2)))) * θ ^ k := by
    calc ∑' x : ↥(Aᶜ), term (x : {b : Fin 2 → ℤ // b ≠ 0})
        ≤ ∑' x : ↥(Aᶜ), (K * L)
            * bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ^ (-s) :=
          (hterm_sum.subtype (· ∈ Aᶜ)).tsum_le_tsum
            (fun x => hdom (x : {b : Fin 2 → ℤ // b ≠ 0})) (hdom_sum.subtype (· ∈ Aᶜ))
      _ = (K * L) * ∑' x : ↥(Aᶜ), bracket ((x : {b : Fin 2 → ℤ // b ≠ 0}) : Fin 2 → ℤ) ^ (-s) :=
          tsum_mul_left
      _ ≤ (K * L) * ((∑' n, bracket n ^ (-((s + 2) / 2))) * R ^ (-((s - 2) / 2))) :=
          mul_le_mul_of_nonneg_left hBtail (mul_nonneg hK hL)
      _ = (K * L * (∑' n, bracket n ^ (-((s + 2) / 2)))) * θ ^ k := by rw [hRtail]; ring
  -- Assemble.
  refine ⟨hterm_sum, ?_⟩
  have hsplit := hterm_sum.tsum_subtype_add_tsum_subtype_compl A
  calc (∑' b : {b : Fin 2 → ℤ // b ≠ 0}, term b)
      = (∑' x : ↥A, term (x : {b : Fin 2 → ℤ // b ≠ 0}))
        + ∑' x : ↥(Aᶜ), term (x : {b : Fin 2 → ℤ // b ≠ 0}) := hsplit.symm
    _ ≤ (K * L * (Real.sqrt 5 - 2) ^ (-s) * (∑' n, bracket n ^ (-s))) * θ ^ k
        + (K * L * (∑' n, bracket n ^ (-((s + 2) / 2)))) * θ ^ k := add_le_add hAle hBle
    _ = (K * L * (Real.sqrt 5 - 2) ^ (-s) * (∑' n, bracket n ^ (-s))
          + K * L * (∑' n, bracket n ^ (-((s + 2) / 2)))) * θ ^ k := by ring

/-! ## The headline: exponential decay of the complex correlation -/

/-- **Exponential decay of correlations (complex observables).**  For `f g : C(𝕋², ℂ)` in the
Fourier-decay class `FourierDecay s` with `s > 2`, the centred correlation under the `k`-fold cat
map decays geometrically with explicit base `θ = λ^(-(s-2)/4) < 1`:
`‖∫ conj f · (g ∘ Tᵏ) − (∫ conj f)(∫ g)‖ ≤ C · θᵏ`.  This is the repository's first
quantitative-rate mixing statement for the cat map (an upgrade of `tendsto_catCorr`). -/
theorem catCorr_decay {s : ℝ} (hs : 2 < s) (f g : C(T2, ℂ))
    (hf : FourierDecay s (f : T2 → ℂ)) (hg : FourierDecay s (g : T2 → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ‖(∫ t : T2, (starRingEnd ℂ) (f t) * g (catTorus^[k] t))
          - (∫ t : T2, (starRingEnd ℂ) (f t)) * (∫ t : T2, g t)‖
        ≤ C * (lam ^ (-(s - 2) / 4 : ℝ)) ^ k := by
  obtain ⟨C, hC, hbound⟩ := catCorr_tsum_norm_le hs hf hg
  refine ⟨C, hC, fun k => ?_⟩
  obtain ⟨hsum, hle⟩ := hbound k
  exact (norm_correlation_sub_le f g k hsum).trans hle

/-! ## Real-observable corollaries (Green–Kubo input) -/

/-- **Exponential decay of correlations (two real observables).**  For `f g : C(𝕋², ℝ)` whose
complexifications lie in `FourierDecay s` (`s > 2`), the real centred correlation decays
geometrically:  `|∫ f · (g ∘ Tᵏ) − (∫ f)(∫ g)| ≤ C · θᵏ`. -/
theorem catCorr_decay_real₂ {s : ℝ} (hs : 2 < s) (f g : C(T2, ℝ))
    (hf : FourierDecay s (fun t => (f t : ℂ)))
    (hg : FourierDecay s (fun t => (g t : ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |(∫ t : T2, f t * g (catTorus^[k] t)) - (∫ t : T2, f t) * (∫ t : T2, g t)|
        ≤ C * (lam ^ (-(s - 2) / 4 : ℝ)) ^ k := by
  set F : C(T2, ℂ) := ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  set G : C(T2, ℂ) := ⟨fun t => (g t : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ with hG
  have hfF : FourierDecay s (F : T2 → ℂ) := hf
  have hgG : FourierDecay s (G : T2 → ℂ) := hg
  obtain ⟨C, hC, hbound⟩ := catCorr_decay hs F G hfF hgG
  refine ⟨C, hC, fun k => ?_⟩
  have hbk := hbound k
  -- Rewrite the complex centred correlation as the real cast of the real one.
  have hcorr : (∫ t : T2, (starRingEnd ℂ) (F t) * G (catTorus^[k] t))
      = ((∫ t : T2, f t * g (catTorus^[k] t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, hG, ContinuousMap.coe_mk, Complex.conj_ofReal, Complex.ofReal_mul]
  have hmf : (∫ t : T2, (starRingEnd ℂ) (F t)) = ((∫ t : T2, f t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, ContinuousMap.coe_mk, Complex.conj_ofReal]
  have hmg : (∫ t : T2, G t) = ((∫ t : T2, g t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hG, ContinuousMap.coe_mk]
  rw [hcorr, hmf, hmg, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hbk
  exact hbk

/-- **Exponential decay of the auto-correlation (single real observable).**  For `f : C(𝕋², ℝ)`
whose complexification lies in `FourierDecay s` (`s > 2`), the variance-centred auto-correlation
decays geometrically:  `|∫ f · (f ∘ Tᵏ) − (∫ f)²| ≤ C · θᵏ`.  This is the input to a downstream
Green–Kubo sum. -/
theorem catCorr_decay_real {s : ℝ} (hs : 2 < s) (f : C(T2, ℝ))
    (hf : FourierDecay s (fun t => (f t : ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |(∫ t : T2, f t * f (catTorus^[k] t)) - (∫ t : T2, f t) ^ 2|
        ≤ C * (lam ^ (-(s - 2) / 4 : ℝ)) ^ k := by
  obtain ⟨C, hC, hbound⟩ := catCorr_decay_real₂ hs f f hf hf
  exact ⟨C, hC, fun k => by rw [sq]; exact hbound k⟩

/-! ## Non-vacuity: characters and trigonometric polynomials -/

/-- The exponential-decay estimate is non-vacuous: every character `mFourier m` lies in every
Fourier-decay class, so `catCorr_decay` applies to it (compile-time inhabitation check). -/
example {s : ℝ} (hs : 2 < s) (m : Fin 2 → ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ‖(∫ t : T2, (starRingEnd ℂ) (mFourier m t) * mFourier m (catTorus^[k] t))
          - (∫ t : T2, (starRingEnd ℂ) (mFourier m t)) * (∫ t : T2, mFourier m t)‖
        ≤ C * (lam ^ (-(s - 2) / 4 : ℝ)) ^ k :=
  catCorr_decay hs (mFourier m) (mFourier m)
    (fourierDecay_mFourier s m) (fourierDecay_mFourier s m)

end ErgodicTheory.CatMapToral
