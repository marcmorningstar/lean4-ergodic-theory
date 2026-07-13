/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionMetricVar
import ErgodicTheory.Livsic.HolderFlowCoboundary

/-!
# Hölder-regularity Livšic theorem for variable-roof suspension flows

This module generalises the constant-roof Hölder-Livšic equivalence
(`ErgodicTheory.livsic_holderFlow_constRoof`) to a **variable roof** `τ` bounded below by a positive
constant and **Lipschitz** (issue #63, tier 3). Working on the variable-roof Bowen–Walters metric
`ErgodicTheory.embDistVar` of `ErgodicTheory.Continuous.SuspensionMetricVar`, we introduce
`IsHolderFlowCoboundaryVar`: a flow observable `F` whose flow transfer function is Hölder for the
variable-roof embedding metric. We then prove the equivalence

`IsHolderFlowCoboundaryVar Φ F ↔ HasVanishingPeriodicSums T (inducedBaseCocycle T hτ F)`

for an `embDistVar`-`r`-Hölder, bounded observable `F`, under the discrete Hölder-Livšic hypotheses
on the base.

## The roof hypotheses

The roof `τ` is assumed:

* bounded below (`hρpos : 0 < ρmin`, `hρ0 : ∀ x, ρmin ≤ τ x`) — the metric substrate needs it;
* bounded above (`hρub : ∀ x, τ x ≤ ρmax`) — to control the fibre integrals;
* **Lipschitz** (`hρLip : LipschitzWith Cρ τ`) — the *classical* Bowen–Walters hypothesis (roofs
  are `C¹`/Lipschitz, Barreira–Radu–Wolf §2.1). This is essential and cannot be relaxed to a merely
  `r`-Hölder roof without exponent loss: the fibre-comparison change of variables `σ = τ x · w`
  produces a roof-difference factor `|τ x − τ y|`, which the Lipschitz bound keeps at exponent `1`
  (so the assembled transfer stays `r`-Hölder); a roof only `r`-Hölder would degrade the exponent to
  `r²` (disclosed, not delivered).

## The seam-gluing estimate at variable heights

As in the constant-roof case the transfer function is the descent `suspTransfer T hτ F u₀` of the
fundamental-strip candidate `uCover (x, s) = u₀ x + ∫₀ˢ F [x, σ] dσ`, glued across the seam by the
**general-roof** descent identity `uCover_gen_var` (seam at height `τ x`). The substantive content
is the cross-seam Hölder gluing: the transfer function is Hölder for `embDistVar`. The metric
compares points at their *normalized* heights `u = s / τ x ∈ [0, 1)`, while the transfer integrates
raw heights; the bridge is the change of variables `σ = τ x · w`
(`intervalIntegral.mul_integral_comp_mul_left`), which puts both fibre integrands at a *common
normalized height* `w` and lets `embDistVar_le_three_hlen` bound the fibre difference by the
horizontal length `hlen`.

## The rescale-to-constant trap

Rescaling a variable roof to a constant roof (a time change) is bi-Lipschitz only when `τ` is
cohomologous to a constant, `τ = c + φ ∘ T − φ` — precisely the hypothesis one wants to avoid. So
the metric and this theory are built directly on the normalized fibre coordinate.

## Main definitions

* `ErgodicTheory.IsHolderFlowCoboundaryVar` — `F` has an `embDistVar`-Hölder flow transfer function.

## Main results

* `ErgodicTheory.IsHolderFlowCoboundaryVar.isFlowCoboundary` — a Hölder flow coboundary is a flow
  coboundary.
* `ErgodicTheory.suspensionMk_Tvar`, `ErgodicTheory.uCover_gen_var` — the general-roof seam identity
  and generator descent (seam at height `τ x`).
* `ErgodicTheory.holderWith_inducedBaseCocycle_var` — the induced base observable is Hölder
  (Lemma A-var).
* `ErgodicTheory.holderWith_suspTransfer_var` — the cross-seam Hölder gluing (the keystone).
* `ErgodicTheory.livsic_holderFlow_varRoof` — the tier-3 equivalence.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972) 1278–1301.
* R. Bowen, P. Walters, *Expansive one-parameter flows*, J. Diff. Eq. **12** (1972) 180–193.
* L. Barreira, C. Radu, C. Wolf, *Dimension of measures for suspension flows*, Dyn. Syst. **19**
  (2004) §2.1.
-/

open MeasureTheory Function
open scoped NNReal

namespace ErgodicTheory

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)
  {ρmin ρmax : ℝ} {Cρ : ℝ≥0}
  (hρpos : 0 < ρmin) (hρ0 : ∀ x, ρmin ≤ τ x)

/-! ### The definition -/

/-- `F` is a **variable-roof Hölder flow coboundary** for the flow `Φ` on the variable-roof
suspension space if it is a flow coboundary whose transfer function `u` is Hölder continuous for the
variable-roof Bowen–Walters embedding metric `embDistVar`. -/
def IsHolderFlowCoboundaryVar (hdiam : ∀ a b : X, dist a b ≤ 1)
    (Φ : ℝ → SuspensionSpace T hτ → SuspensionSpace T hτ) (F : SuspensionSpace T hτ → ℝ) : Prop :=
  ∃ (C rr : ℝ≥0) (u : SuspensionSpace T hτ → ℝ), 0 < rr ∧ rr ≤ 1 ∧
    (∀ p q, |u p - u q| ≤ (C : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ)) ∧
    (∀ (q : SuspensionSpace T hτ) (t : ℝ), u (Φ t q) - u q = ∫ s in (0 : ℝ)..t, F (Φ s q))

/-- **A variable-roof Hölder flow coboundary is a flow coboundary** (forget the modulus). -/
theorem IsHolderFlowCoboundaryVar.isFlowCoboundary {hdiam : ∀ a b : X, dist a b ≤ 1}
    {Φ : ℝ → SuspensionSpace T hτ → SuspensionSpace T hτ} {F : SuspensionSpace T hτ → ℝ}
    (h : IsHolderFlowCoboundaryVar T hτ hρpos hρ0 hdiam Φ F) : IsFlowCoboundary Φ F := by
  obtain ⟨_, _, u, _, _, _, hcob⟩ := h
  exact ⟨u, hcob⟩

/-! ### The general-roof seam identity and generator descent -/

/-- **General-roof seam identity.** In the variable-roof suspension quotient the seam sits at height
`τ x`: `[T x, σ] = [x, σ + τ x]`, since the generator `G (x, σ + τ x) = (T x, σ)`. -/
theorem suspensionMk_Tvar (x : X) (σ : ℝ) :
    suspensionMk T hτ (T x, σ) = suspensionMk T hτ (x, σ + τ x) := by
  have hgen : suspensionGen T hτ (x, σ + τ x) = (T x, σ) := by
    rw [suspensionGen_apply]; simp
  rw [← hgen, ← suspensionAct_one T hτ (x, σ + τ x), suspensionMk_act' T hτ 1 (x, σ + τ x)]

/-- **General-roof generator descent.** For a base transfer `u₀` cobounding the induced base
observable, the fundamental-domain candidate is invariant under the suspension generator:
`uCover (T x, s − τ x) = uCover (x, s)`. The base jump `u₀ (T x) − u₀ x` is exactly the one-lap
integral `∫₀^{τ x} F [x, σ] dσ`. -/
theorem uCover_gen_var (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hu₀ : ∀ x, inducedBaseCocycle T hτ F x = u₀ (T x) - u₀ x)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x : X) (s : ℝ) :
    uCover T hτ F u₀ (T x, s - τ x) = uCover T hτ F u₀ (x, s) := by
  simp only [uCover]
  have hInt : (∫ σ in (0 : ℝ)..(s - τ x), F (suspensionMk T hτ (T x, σ)))
      = ∫ σ in (τ x)..s, F (suspensionMk T hτ (x, σ)) := by
    have hshift : (fun σ => F (suspensionMk T hτ (T x, σ)))
        = fun σ => F (suspensionMk T hτ (x, σ + τ x)) := by
      funext σ; rw [suspensionMk_Tvar T hτ]
    rw [hshift,
      intervalIntegral.integral_comp_add_right
        (fun σ => F (suspensionMk T hτ (x, σ))) (τ x)]
    congr 1 <;> ring
  rw [hInt]
  have hu : u₀ (T x) = u₀ x + ∫ σ in (0 : ℝ)..(τ x), F (suspensionMk T hτ (x, σ)) := by
    have hval := hu₀ x
    rw [inducedBaseCocycle] at hval; linarith [hval]
  rw [hu]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint x 0 (τ x)) (hint x (τ x) s)
  have : (∫ σ in (0 : ℝ)..(τ x), F (suspensionMk T hτ (x, σ)))
      + ∫ σ in (τ x)..s, F (suspensionMk T hτ (x, σ))
      = ∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)) := hadd
  linarith [this]

/-- The generator-invariance hypothesis `hg` for the variable roof, from the base cohomology. -/
theorem uCover_gen_hg_var (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hu₀ : ∀ x, inducedBaseCocycle T hτ F x = u₀ (T x) - u₀ x)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b) :
    ∀ p, uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p := by
  rintro ⟨x, s⟩
  rw [suspensionGen_apply]
  exact uCover_gen_var T hτ F u₀ hu₀ hint x s

/-! ### The Lipschitz roof in absolute-value form -/

/-- The Lipschitz roof bound in absolute-value form. -/
theorem roof_lip_abs (hρLip : LipschitzWith Cρ τ) (x y : X) :
    |τ x - τ y| ≤ (Cρ : ℝ) * dist x y := by
  have h := hρLip.dist_le_mul x y
  rwa [Real.dist_eq] at h

/-! ### The change-of-variables fibre bridge

The fibre integrals are in *raw* height, whereas `embDistVar` compares points at *normalized*
height; the bridge is `σ = τ x · w`. -/

/-- **Fibre change of variables.** `∫ σ in (τ x · a)..(τ x · b), F [x, σ] = τ x · ∫ w in a..b,
F [x, τ x · w]`. -/
theorem fibre_scaled_eq (F : SuspensionSpace T hτ → ℝ) (x : X) (a b : ℝ) :
    (∫ σ in (τ x * a)..(τ x * b), F (suspensionMk T hτ (x, σ)))
      = τ x * ∫ w in a..b, F (suspensionMk T hτ (x, τ x * w)) :=
  (intervalIntegral.mul_integral_comp_mul_left
    (f := fun σ => F (suspensionMk T hτ (x, σ))) (a := a) (b := b) (τ x)).symm

include hρpos hρ0 in
/-- Interval integrability of the scaled fibre integrand `w ↦ F [x, τ x · w]`. -/
theorem intervalIntegrable_scaled (F : SuspensionSpace T hτ → ℝ)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x : X) (a b : ℝ) :
    IntervalIntegrable (fun w => F (suspensionMk T hτ (x, τ x * w))) volume a b := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have h := (hint x (τ x * a) (τ x * b)).comp_mul_left (c := τ x)
  rwa [mul_div_cancel_left₀ _ (ne_of_gt hxpos), mul_div_cancel_left₀ _ (ne_of_gt hxpos)] at h

/-! ### The matched-height fibre-difference modulus -/

/-- **Matched-height fibre difference.** At a *common normalized height* `w ∈ [0, 1]`, the
`embDistVar`-Hölder modulus of `F` controls the difference of the two fibre integrand values by the
horizontal length: `|F [x, τ x · w] − F [y, τ y · w]| ≤ CF · (3 · hlen w x y) ^ r`. The interior
`w < 1` uses `embDistVar_le_three_hlen`; the top `w = 1` uses the seam identity. -/
theorem absF_matched_le (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0}
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    (x y : X) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |F (suspensionMk T hτ (x, τ x * w)) - F (suspensionMk T hτ (y, τ y * w))|
      ≤ (CF : ℝ) * (3 * hlen T w x y) ^ (rr : ℝ) := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hkey : embDistVar T hτ hρpos hρ0 hdiam
      (suspensionMk T hτ (x, τ x * w)) (suspensionMk T hτ (y, τ y * w)) ≤ 3 * hlen T w x y := by
    rcases lt_or_eq_of_le hw1 with hlt | heq
    · have hwI : w ∈ Set.Ico (0 : ℝ) 1 := ⟨hw0, hlt⟩
      have h := embDistVar_le_three_hlen T hτ hρpos hρ0 hdiam hwI x y
      rwa [mul_comm w (τ x), mul_comm w (τ y)] at h
    · have hx1 : suspensionMk T hτ (x, τ x * w) = suspensionMk T hτ (T x, 0) := by
        rw [heq, mul_one, suspensionMk_Tvar T hτ x 0, zero_add]
      have hy1 : suspensionMk T hτ (y, τ y * w) = suspensionMk T hτ (T y, 0) := by
        rw [heq, mul_one, suspensionMk_Tvar T hτ y 0, zero_add]
      have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl 0, one_pos⟩
      rw [hx1, hy1]
      have h := embDistVar_le_three_hlen T hτ hρpos hρ0 hdiam h0 (T x) (T y)
      rw [zero_mul, zero_mul] at h
      refine h.trans (le_of_eq ?_)
      rw [heq, hlen_one, hlen_zero]
  have hcf : (0 : ℝ) ≤ (CF : ℝ) := CF.coe_nonneg
  calc |F (suspensionMk T hτ (x, τ x * w)) - F (suspensionMk T hτ (y, τ y * w))|
      ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam
          (suspensionMk T hτ (x, τ x * w)) (suspensionMk T hτ (y, τ y * w)) ^ (rr : ℝ) := hF _ _
    _ ≤ (CF : ℝ) * (3 * hlen T w x y) ^ (rr : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (embDistVar_nonneg T hτ hρpos hρ0 hdiam _ _) hkey rr.coe_nonneg) hcf

/-! ### The master matched-range fibre-difference bound -/

/-- **Master matched-range fibre-difference bound.** For a normalized range `[a, b] ⊆ [0, 1]` on
which the horizontal length is bounded by `H`, the difference of the two raw fibre integrals over
`[τ x · a, τ x · b]` and `[τ y · a, τ y · b]` splits into a Hölder part (matched normalized heights)
and a roof-difference part (the Lipschitz roof keeps its exponent at `1`):
`|∫_{τx·a}^{τx·b} F[x] − ∫_{τy·a}^{τy·b} F[y]| ≤ ρmax · CF · (3 · H) ^ r · (b − a) + Cρ · dist x y ·
M · (b − a)`. -/
theorem absJ_matched_le (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0}
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (hρub : ∀ x, τ x ≤ ρmax) (hρLip : LipschitzWith Cρ τ)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x y : X) {a b H : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (hH0 : 0 ≤ H)
    (hH : ∀ w, a ≤ w → w ≤ b → hlen T w x y ≤ H) :
    |(∫ σ in (τ x * a)..(τ x * b), F (suspensionMk T hτ (x, σ)))
        - ∫ σ in (τ y * a)..(τ y * b), F (suspensionMk T hτ (y, σ))|
      ≤ ρmax * ((CF : ℝ) * (3 * H) ^ (rr : ℝ)) * (b - a)
        + (Cρ : ℝ) * dist x y * (M * (b - a)) := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM (suspensionMk T hτ (x, 0)))
  have hba0 : (0 : ℝ) ≤ b - a := by linarith
  set A := ∫ w in a..b, F (suspensionMk T hτ (x, τ x * w)) with hAdef
  set B := ∫ w in a..b, F (suspensionMk T hτ (y, τ y * w)) with hBdef
  rw [fibre_scaled_eq T hτ F x a b, fibre_scaled_eq T hτ F y a b, ← hAdef, ← hBdef]
  have hintx := intervalIntegrable_scaled T hτ hρpos hρ0 F hint x a b
  have hinty := intervalIntegrable_scaled T hτ hρpos hρ0 F hint y a b
  -- regroup τx·A − τy·B = τx·(A − B) + (τx − τy)·B
  have hsplit : τ x * A - τ y * B = τ x * (A - B) + (τ x - τ y) * B := by ring
  rw [hsplit]
  -- bound A − B by the matched-height Hölder modulus
  have hAB : |A - B| ≤ (CF : ℝ) * (3 * H) ^ (rr : ℝ) * (b - a) := by
    rw [hAdef, hBdef, ← intervalIntegral.integral_sub hintx hinty, ← Real.norm_eq_abs]
    have hbnd : ∀ w ∈ Set.uIoc a b,
        ‖F (suspensionMk T hτ (x, τ x * w)) - F (suspensionMk T hτ (y, τ y * w))‖
          ≤ (CF : ℝ) * (3 * H) ^ (rr : ℝ) := by
      intro w hw
      rw [Set.uIoc_of_le hab] at hw
      have hw0 : (0 : ℝ) ≤ w := le_trans ha0 hw.1.le
      have hw1 : w ≤ 1 := le_trans hw.2 hb1
      rw [Real.norm_eq_abs]
      refine (absF_matched_le T hτ hρpos hρ0 hdiam F hF x y hw0 hw1).trans ?_
      have h3nn : (0 : ℝ) ≤ 3 * hlen T w x y := by
        have := hlen_nonneg T hw0 hw1 x y; linarith
      have h3 : 3 * hlen T w x y ≤ 3 * H := by have := hH w hw.1.le hw.2; linarith
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h3nn h3 rr.coe_nonneg) CF.coe_nonneg
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbnd).trans_eq ?_
    rw [abs_of_nonneg hba0]
  -- bound B by M·(b − a)
  have hB : |B| ≤ M * (b - a) := by
    rw [hBdef, ← Real.norm_eq_abs]
    have hBbnd : ∀ w ∈ Set.uIoc a b, ‖F (suspensionMk T hτ (y, τ y * w))‖ ≤ M :=
      fun w _ => by rw [Real.norm_eq_abs]; exact hM _
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hBbnd).trans_eq ?_
    rw [abs_of_nonneg hba0]
  -- combine
  have hτxnn : (0 : ℝ) ≤ τ x := hxpos.le
  have hτub : τ x ≤ ρmax := hρub x
  have h1 : |τ x * (A - B)| ≤ ρmax * ((CF : ℝ) * (3 * H) ^ (rr : ℝ)) * (b - a) := by
    rw [abs_mul, abs_of_nonneg hτxnn]
    have hpow : (0 : ℝ) ≤ (CF : ℝ) * (3 * H) ^ (rr : ℝ) := by positivity
    calc τ x * |A - B| ≤ τ x * ((CF : ℝ) * (3 * H) ^ (rr : ℝ) * (b - a)) :=
          mul_le_mul_of_nonneg_left hAB hτxnn
      _ ≤ ρmax * ((CF : ℝ) * (3 * H) ^ (rr : ℝ) * (b - a)) :=
          mul_le_mul_of_nonneg_right hτub (by positivity)
      _ = ρmax * ((CF : ℝ) * (3 * H) ^ (rr : ℝ)) * (b - a) := by ring
  have h2 : |(τ x - τ y) * B| ≤ (Cρ : ℝ) * dist x y * (M * (b - a)) := by
    rw [abs_mul]
    have hlip := roof_lip_abs hρLip x y
    calc |τ x - τ y| * |B| ≤ ((Cρ : ℝ) * dist x y) * (M * (b - a)) :=
          mul_le_mul hlip hB (abs_nonneg _) (by positivity)
      _ = (Cρ : ℝ) * dist x y * (M * (b - a)) := by ring
  calc |τ x * (A - B) + (τ x - τ y) * B|
      ≤ |τ x * (A - B)| + |(τ x - τ y) * B| := abs_add_le _ _
    _ ≤ ρmax * ((CF : ℝ) * (3 * H) ^ (rr : ℝ)) * (b - a)
        + (Cρ : ℝ) * dist x y * (M * (b - a)) := by linarith [h1, h2]

/-! ### Lemma A: the induced base observable is Hölder -/

/-- **Lemma A-var: the induced base observable is Hölder.** If `F` is `embDistVar`-`r`-Hölder,
bounded by `M`, `T` is `L`-Lipschitz and the roof is bounded (`ρmax`) and `Cρ`-Lipschitz, the base
observable `inducedBaseCocycle T hτ F` is `r`-Hölder with constant
`ρmax · CF · (3 · max 1 L) ^ r + Cρ · M`. Route: the master matched-range bound at `[0, 1]`, with
`hlen w x y ≤ max 1 L · dist x y`, then fold the Lipschitz-roof first-power term into `dist ^ r`
using `dist ≤ 1`. -/
theorem holderWith_inducedBaseCocycle_var (hdiam : ∀ a b : X, dist a b ≤ 1)
    (F : SuspensionSpace T hτ → ℝ) {CF rr : ℝ≥0} (_hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (hρub : ∀ x, τ x ≤ ρmax) (hρLip : LipschitzWith Cρ τ)
    {L : ℝ≥0} (hTL : LipschitzWith L ⇑T)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b) :
    HolderWith (ρmax * (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) + (Cρ : ℝ) * M).toNNReal rr
      (inducedBaseCocycle T hτ F) := by
  have hrr1' : (rr : ℝ) ≤ 1 := by exact_mod_cast hrr1
  refine holderWith_of_dist_le fun x y => ?_
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hd0 : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM (suspensionMk T hτ (x, 0)))
  have hρmax0 : (0 : ℝ) ≤ ρmax := le_trans hxpos.le (hρub x)
  have hCnn : (0 : ℝ) ≤ ρmax * (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) + (Cρ : ℝ) * M := by
    positivity
  rw [Real.coe_toNNReal _ hCnn, Real.dist_eq]
  -- rewrite the induced cocycle as the master integral at [0, 1]
  have hfx : inducedBaseCocycle T hτ F x
      = ∫ σ in (τ x * 0)..(τ x * 1), F (suspensionMk T hτ (x, σ)) := by
    rw [inducedBaseCocycle, mul_zero, mul_one]
  have hfy : inducedBaseCocycle T hτ F y
      = ∫ σ in (τ y * 0)..(τ y * 1), F (suspensionMk T hτ (y, σ)) := by
    rw [inducedBaseCocycle, mul_zero, mul_one]
  rw [hfx, hfy]
  -- horizontal-length bound
  have hHle : ∀ w, (0 : ℝ) ≤ w → w ≤ 1 → hlen T w x y ≤ max 1 (L : ℝ) * dist x y := by
    intro w hw0 hw1
    have hd2 : dist (T x) (T y) ≤ (L : ℝ) * dist x y := by
      have := hTL.dist_le_mul x y; simpa using this
    have h1 : (1 - w) * dist x y ≤ (1 - w) * (max 1 (L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left dist_nonneg (le_max_left _ _)) (by linarith)
    have h2 : w * dist (T x) (T y) ≤ w * (max 1 (L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hd2.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)) hw0
    simp only [hlen]; nlinarith [h1, h2]
  have hHnn : (0 : ℝ) ≤ max 1 (L : ℝ) * dist x y :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hd0
  have hmaster := absJ_matched_le T hτ hρpos hρ0 hdiam F hF hM hρub hρLip hint x y
    (le_refl 0) (by norm_num : (0 : ℝ) ≤ 1) (le_refl 1) hHnn (fun w hw0 hw1 => hHle w hw0 hw1)
  refine hmaster.trans ?_
  simp only [sub_zero, mul_one]
  -- fold the two terms into C · dist ^ r
  have hpoweq : (3 * (max 1 (L : ℝ) * dist x y)) ^ (rr : ℝ)
      = (3 * max 1 (L : ℝ)) ^ (rr : ℝ) * dist x y ^ (rr : ℝ) := by
    rw [show 3 * (max 1 (L : ℝ) * dist x y) = (3 * max 1 (L : ℝ)) * dist x y from by ring,
      Real.mul_rpow (by positivity) hd0]
  have hdr : dist x y ≤ dist x y ^ (rr : ℝ) :=
    Real.self_le_rpow_of_le_one hd0 (hdiam x y) hrr1'
  have hdrnn : (0 : ℝ) ≤ dist x y ^ (rr : ℝ) := Real.rpow_nonneg hd0 _
  have hterm1 : ρmax * ((CF : ℝ) * (3 * (max 1 (L : ℝ) * dist x y)) ^ (rr : ℝ))
      = ρmax * (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) * dist x y ^ (rr : ℝ) := by
    rw [hpoweq]; ring
  have hterm2 : (Cρ : ℝ) * dist x y * M ≤ (Cρ : ℝ) * M * dist x y ^ (rr : ℝ) := by
    have := mul_le_mul_of_nonneg_left hdr (by positivity : (0 : ℝ) ≤ (Cρ : ℝ) * M)
    nlinarith [this, Cρ.coe_nonneg, hM0]
  calc ρmax * ((CF : ℝ) * (3 * (max 1 (L : ℝ) * dist x y)) ^ (rr : ℝ))
        + (Cρ : ℝ) * dist x y * M
      = ρmax * (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) * dist x y ^ (rr : ℝ)
        + (Cρ : ℝ) * dist x y * M := by rw [hterm1]
    _ ≤ ρmax * (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) * dist x y ^ (rr : ℝ)
        + (Cρ : ℝ) * M * dist x y ^ (rr : ℝ) := by linarith [hterm2]
    _ = (ρmax * (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) + (Cρ : ℝ) * M)
          * dist x y ^ (rr : ℝ) := by ring

/-! ### Common-height Kuratowski reductions for the variable roof -/

/-- The `muFun` bundle distance at the two normalized heights `s/τx`, `t/τy` is bounded by the
embedding distance between the box classes. -/
theorem dist_muFun_le_embDistVar_box (hdiam : ∀ a b : X, dist a b ≤ 1) {x : X} {s : ℝ} {y : X}
    {t : ℝ} (hd : (x, s) ∈ suspensionDomain τ) (hd' : (y, t) ∈ suspensionDomain τ) :
    dist (muFun T hdiam (x, s / τ x)) (muFun T hdiam (y, t / τ y))
      ≤ embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t)) := by
  rw [embDistVar_box T hτ hρpos hρ0 hdiam hd hd']
  have hνnn : (0 : ℝ) ≤ dist (nuFun T hdiam (x, s / τ x)) (nuFun T hdiam (y, t / τ y)) :=
    dist_nonneg
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hu : s / τ x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hd.1 hxpos.le, (div_lt_one hxpos).mpr hd.2⟩
  have hu' : t / τ y ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hd'.1 hypos.le, (div_lt_one hypos).mpr hd'.2⟩
  have hhnn : 0 ≤ hgt (s / τ x) (t / τ y) := by
    apply hgt_nonneg; rw [abs_le]; exact ⟨by linarith [hu.1, hu'.2], by linarith [hu.2, hu'.1]⟩
  linarith

/-- The `nuFun` bundle distance at the two normalized heights is bounded by the embedding
distance. -/
theorem dist_nuFun_le_embDistVar_box (hdiam : ∀ a b : X, dist a b ≤ 1) {x : X} {s : ℝ} {y : X}
    {t : ℝ} (hd : (x, s) ∈ suspensionDomain τ) (hd' : (y, t) ∈ suspensionDomain τ) :
    dist (nuFun T hdiam (x, s / τ x)) (nuFun T hdiam (y, t / τ y))
      ≤ embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t)) := by
  rw [embDistVar_box T hτ hρpos hρ0 hdiam hd hd']
  have hμnn : (0 : ℝ) ≤ dist (muFun T hdiam (x, s / τ x)) (muFun T hdiam (y, t / τ y)) :=
    dist_nonneg
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hu : s / τ x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hd.1 hxpos.le, (div_lt_one hxpos).mpr hd.2⟩
  have hu' : t / τ y ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hd'.1 hypos.le, (div_lt_one hypos).mpr hd'.2⟩
  have hhnn : 0 ≤ hgt (s / τ x) (t / τ y) := by
    apply hgt_nonneg; rw [abs_le]; exact ⟨by linarith [hu.1, hu'.2], by linarith [hu.2, hu'.1]⟩
  linarith

/-- **Common-height `muFun` bound (Var).** At the common normalized height `v = t/τy`, the two
`muFun` bundles are within `ε + |u − v|` (`u = s/τx`), by pushing `x`'s bundle from `u` to `v`. -/
theorem dist_muFun_common_le_var (hdiam : ∀ a b : X, dist a b ≤ 1) {x : X} {s : ℝ} {y : X} {t : ℝ}
    (hd : (x, s) ∈ suspensionDomain τ) (hd' : (y, t) ∈ suspensionDomain τ) :
    dist (muFun T hdiam (x, t / τ y)) (muFun T hdiam (y, t / τ y))
      ≤ embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
        + |s / τ x - t / τ y| := by
  have h := dist_muFun_le_embDistVar_box T hτ hρpos hρ0 hdiam hd hd'
  have hvert : dist (muFun T hdiam (x, t / τ y)) (muFun T hdiam (x, s / τ x))
      ≤ |s / τ x - t / τ y| :=
    (dist_muFun_sameBase_le T hdiam x (t / τ y) (s / τ x)).trans_eq (abs_sub_comm _ _)
  have htri := dist_triangle (muFun T hdiam (x, t / τ y)) (muFun T hdiam (x, s / τ x))
    (muFun T hdiam (y, t / τ y))
  linarith

/-- **Common-height `nuFun` bound (Var).** At the common normalized height `v = t/τy`, the two
`nuFun` bundles are within `ε + 2·|u − v|`. -/
theorem dist_nuFun_common_le_var (hdiam : ∀ a b : X, dist a b ≤ 1) {x : X} {s : ℝ} {y : X} {t : ℝ}
    (hd : (x, s) ∈ suspensionDomain τ) (hd' : (y, t) ∈ suspensionDomain τ) :
    dist (nuFun T hdiam (x, t / τ y)) (nuFun T hdiam (y, t / τ y))
      ≤ embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
        + 2 * |s / τ x - t / τ y| := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hu : s / τ x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hd.1 hxpos.le, (div_lt_one hxpos).mpr hd.2⟩
  have hu' : t / τ y ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hd'.1 hypos.le, (div_lt_one hypos).mpr hd'.2⟩
  have h := dist_nuFun_le_embDistVar_box T hτ hρpos hρ0 hdiam hd hd'
  have hvert : dist (nuFun T hdiam (x, t / τ y)) (nuFun T hdiam (x, s / τ x))
      ≤ 2 * |s / τ x - t / τ y| := by
    refine (dist_nuFun_sameBase_le T hdiam x hu'.1 hu'.2.le hu.1 hu.2.le).trans ?_
    rw [abs_sub_comm (t / τ y) (s / τ x)]
  have htri := dist_triangle (nuFun T hdiam (x, t / τ y)) (nuFun T hdiam (x, s / τ x))
    (nuFun T hdiam (y, t / τ y))
  linarith

/-! ### The from-above representation of the transfer candidate (variable roof) -/

/-- **From-above representation (Var).** Using `inducedBaseCocycle F x = u₀ (T x) − u₀ x`, the
fundamental-strip candidate is `uCover (x, s) = u₀ (T x) − ∫_s^{τ x} F [x, σ] dσ`. -/
theorem uCover_fromAbove_var (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hu₀ : ∀ x, inducedBaseCocycle T hτ F x = u₀ (T x) - u₀ x)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x : X) (s : ℝ) :
    uCover T hτ F u₀ (x, s) = u₀ (T x) - ∫ σ in s..(τ x), F (suspensionMk T hτ (x, σ)) := by
  have hval : u₀ (T x) = u₀ x + ∫ σ in (0 : ℝ)..(τ x), F (suspensionMk T hτ (x, σ)) := by
    have h := hu₀ x
    rw [inducedBaseCocycle] at h; linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hint x 0 s) (hint x s (τ x))
  simp only [uCover]
  rw [hval]; linarith [hadd]

/-! ### The keystone: the ordered seam-gluing estimate (variable roof) -/

set_option maxHeartbeats 3200000 in -- long four-way case analysis with change-of-variables
/-- **Ordered seam-gluing estimate (variable roof).** For canonical box representatives `(x, s)`,
`(y, t)` ordered by normalized height `s/τx ≤ t/τy`, the transfer candidate `uCover` is
`embDistVar`-Hölder. The proof splits on `ε = embDistVar [x,s] [y,t]`: large `ε` uses a crude
oscillation bound; small `ε` uses the normalized-height gap `hgt u v ≤ ε` to branch into no-wrap
(from-below `v ≤ 7/8` or from-above `v > 7/8`) and wrap, with the fibre integrals compared at
matched normalized heights via `absJ_matched_le` (change of variables) and the roof-difference term
kept `O(ε)` by the Lipschitz roof together with `(1−v)·dist x y ≤ 7ε`. -/
theorem holder_uCover_core_var (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0} (_hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (hρub : ∀ x, τ x ≤ ρmax) (hρLip : LipschitzWith Cρ τ)
    (u₀ : X → ℝ) {Cu : ℝ} (hCu0 : 0 ≤ Cu)
    (hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ Cu * dist a b ^ (rr : ℝ))
    (hu₀ : ∀ a, inducedBaseCocycle T hτ F a = u₀ (T a) - u₀ a)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x y : X) {s t : ℝ} (hd : (x, s) ∈ suspensionDomain τ) (hd' : (y, t) ∈ suspensionDomain τ)
    (huv : s / τ x ≤ t / τ y) :
    |uCover T hτ F u₀ (x, s) - uCover T hτ F u₀ (y, t)|
      ≤ 300 * (Cu + ρmax * M + ρmax * (CF : ℝ) + (Cρ : ℝ) * M + 1)
        * embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s))
          (suspensionMk T hτ (y, t)) ^ (rr : ℝ) := by
  have hxpos : 0 < τ x := lt_of_lt_of_le hρpos (hρ0 x)
  have hypos : 0 < τ y := lt_of_lt_of_le hρpos (hρ0 y)
  have hρmax0 : (0 : ℝ) ≤ ρmax := le_trans hxpos.le (hρub x)
  set u := s / τ x with hu_def
  set v := t / τ y with hv_def
  have huI : u ∈ Set.Ico (0 : ℝ) 1 := ⟨div_nonneg hd.1 hxpos.le, (div_lt_one hxpos).mpr hd.2⟩
  have hvI : v ∈ Set.Ico (0 : ℝ) 1 := ⟨div_nonneg hd'.1 hypos.le, (div_lt_one hypos).mpr hd'.2⟩
  have hsu : τ x * u = s := by rw [hu_def]; field_simp
  have htv : τ y * v = t := by rw [hv_def]; field_simp
  set ε := embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s))
    (suspensionMk T hτ (y, t)) with hεdef
  have hε0 : 0 ≤ ε := embDistVar_nonneg T hτ hρpos hρ0 hdiam _ _
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM (suspensionMk T hτ (x, 0)))
  have hrr1' : (rr : ℝ) ≤ 1 := by exact_mod_cast hrr1
  have hεrnn : 0 ≤ ε ^ (rr : ℝ) := Real.rpow_nonneg hε0 _
  have hd0 : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hD0 : (0 : ℝ) ≤ dist (T x) (T y) := dist_nonneg
  have habs_uv : |u - v| = v - u := by rw [abs_of_nonpos (by linarith [huv] : u - v ≤ 0)]; ring
  set K := 300 * (Cu + ρmax * M + ρmax * (CF : ℝ) + (Cρ : ℝ) * M + 1) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  -- final coefficient-domination step
  have hfin : ∀ c : ℝ, c ≤ K → c * ε ^ (rr : ℝ) ≤ K * ε ^ (rr : ℝ) :=
    fun c hc => mul_le_mul_of_nonneg_right hc hεrnn
  -- representations of the two candidate values
  have hucx : uCover T hτ F u₀ (x, s)
      = u₀ x + ∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)) := rfl
  have hucy : uCover T hτ F u₀ (y, t)
      = u₀ y + ∫ σ in (0 : ℝ)..t, F (suspensionMk T hτ (y, σ)) := rfl
  rcases le_or_gt (1 / 8 : ℝ) ε with hbig | hsmall
  · -- Large ε: crude oscillation bound.
    have hεr18 : (1 / 8 : ℝ) ≤ ε ^ (rr : ℝ) := by
      have h1 : (1 / 8 : ℝ) ≤ (1 / 8 : ℝ) ^ (rr : ℝ) :=
        Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) hrr1'
      have h2 : (1 / 8 : ℝ) ^ (rr : ℝ) ≤ ε ^ (rr : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hbig rr.coe_nonneg
      linarith
    have hcrude : |uCover T hτ F u₀ (x, s) - uCover T hτ F u₀ (y, t)| ≤ Cu + 2 * (ρmax * M) := by
      rw [hucx, hucy]
      have hA : |u₀ x - u₀ y| ≤ Cu := by
        refine (hu₀hol x y).trans ?_
        have : dist x y ^ (rr : ℝ) ≤ 1 := Real.rpow_le_one hd0 (hdiam x y) rr.coe_nonneg
        nlinarith [hCu0]
      have hBx := abs_integral_fibre_le T hτ F hM x 0 s
      have hBy := abs_integral_fibre_le T hτ F hM y 0 t
      rw [abs_of_nonneg (by linarith [hd.1] : (0 : ℝ) ≤ s - 0)] at hBx
      rw [abs_of_nonneg (by linarith [hd'.1] : (0 : ℝ) ≤ t - 0)] at hBy
      have hs1 : M * (s - 0) ≤ ρmax * M := by
        have : s ≤ ρmax := le_trans hd.2.le (hρub x); nlinarith [hM0]
      have ht1 : M * (t - 0) ≤ ρmax * M := by
        have : t ≤ ρmax := le_trans hd'.2.le (hρub y); nlinarith [hM0]
      calc |u₀ x + _ - (u₀ y + _)|
          ≤ |u₀ x - u₀ y| + |∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ))|
            + |∫ σ in (0 : ℝ)..t, F (suspensionMk T hτ (y, σ))| := by
            rw [show u₀ x + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
                - (u₀ y + ∫ σ in (0 : ℝ)..t, F (suspensionMk T hτ (y, σ)))
              = (u₀ x - u₀ y) + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
                - ∫ σ in (0 : ℝ)..t, F (suspensionMk T hτ (y, σ)) from by ring]
            refine (abs_sub_le_abs_add _ _).trans ?_
            linarith [abs_add_le (u₀ x - u₀ y)
              (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))]
        _ ≤ Cu + 2 * (ρmax * M) := by linarith
    refine hcrude.trans ?_
    have hstep : Cu + 2 * (ρmax * M) ≤ (Cu + 2 * (ρmax * M)) * (8 * ε ^ (rr : ℝ)) :=
      le_mul_of_one_le_right (by positivity) (by linarith [hεr18])
    refine hstep.trans (le_trans (le_of_eq (by ring)) (hfin (8 * Cu + 16 * (ρmax * M)) ?_))
    rw [hKdef]; nlinarith [hCu0, hM0, CF.coe_nonneg, Cρ.coe_nonneg, hρmax0]
  · -- Small ε: split on the normalized-height gap.
    have hε1 : ε ≤ 1 := by linarith
    have hεr : ε ≤ ε ^ (rr : ℝ) := Real.self_le_rpow_of_le_one hε0 hε1 hrr1'
    have hHGT : hgt u v ≤ ε := by
      have h := hgtVar_le_embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s))
        (suspensionMk T hτ (y, t))
      rwa [normHeightVar_mk T hτ hρpos hρ0 hd, normHeightVar_mk T hτ hρpos hρ0 hd', ← hu_def,
        ← hv_def, ← hεdef] at h
    have hmin : min |u - v| (1 - |u - v|) < 1 / 8 := lt_of_le_of_lt hHGT hsmall
    rcases min_lt_iff.mp hmin with hnw | hw
    · -- No-wrap: v − u ≤ ε.
      have habsε : v - u ≤ ε := by
        have : hgt u v = |u - v| := by
          rw [hgt, min_eq_left (by rw [habs_uv]; linarith [hnw, habs_uv])]
        rw [this, habs_uv] at hHGT; linarith
      -- common-height Kuratowski parts and recoveries
      have hMμ : dist (muFun T hdiam (x, v)) (muFun T hdiam (y, v)) ≤ 2 * ε := by
        have := dist_muFun_common_le_var T hτ hρpos hρ0 hdiam hd hd'
        rw [← hu_def, ← hv_def, ← hεdef, habs_uv] at this; linarith
      have hMν : dist (nuFun T hdiam (x, v)) (nuFun T hdiam (y, v)) ≤ 3 * ε := by
        have := dist_nuFun_common_le_var T hτ hρpos hρ0 hdiam hd hd'
        rw [← hu_def, ← hv_def, ← hεdef, habs_uv] at this; linarith
      have hμnn : (0 : ℝ) ≤ dist (muFun T hdiam (x, v)) (muFun T hdiam (y, v)) := dist_nonneg
      have hrecD := embHeight_recover_map T hdiam hvI.1 hvI.2.le x y
      have hrecd := embHeight_recover_base T hdiam hvI.1 hvI.2.le x y
      have htD : v * dist (T x) (T y) ≤ 5 * ε := by
        have hp : (1 - v) * dist (muFun T hdiam (x, v)) (muFun T hdiam (y, v))
            ≤ dist (muFun T hdiam (x, v)) (muFun T hdiam (y, v)) :=
          mul_le_of_le_one_left hμnn (by linarith [hvI.1])
        linarith
      have htd : (1 - v) * dist x y ≤ 7 * ε := by linarith
      rcases le_or_gt v (7 / 8) with hlow | hhigh
      · -- From-below representation.
        have hd56 : dist x y ≤ 56 * ε := by
          have h18 : (1 : ℝ) / 8 ≤ 1 - v := by linarith
          nlinarith [htd, mul_le_mul_of_nonneg_right h18 hd0, hd0]
        have hHfb : ∀ w, (0 : ℝ) ≤ w → w ≤ u → hlen T w x y ≤ 61 * ε := by
          intro w hw0 hwu
          have hwv : w ≤ v := le_trans hwu huv
          have h2 : w * dist (T x) (T y) ≤ v * dist (T x) (T y) :=
            mul_le_mul_of_nonneg_right hwv hD0
          simp only [hlen]
          nlinarith [hd56, htD, h2, mul_nonneg hw0 hd0]
        -- match at normalized u: uCover(y,t) split at sy = τy·u
        set sy := τ y * u with hsy_def
        have hsy0 : 0 ≤ sy := mul_nonneg hypos.le huI.1
        have hsy_t : t - sy = τ y * (v - u) := by rw [hsy_def, ← htv]; ring
        have hadd_y := intervalIntegral.integral_add_adjacent_intervals
          (hint y 0 sy) (hint y sy t)
        have hAle : |u₀ x - u₀ y| ≤ 56 * Cu * ε ^ (rr : ℝ) := by
          refine (hu₀hol x y).trans ?_
          have h2 := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 56) hd0 hd56 hε0
          calc Cu * dist x y ^ (rr : ℝ) ≤ Cu * (56 * ε ^ (rr : ℝ)) :=
                mul_le_mul_of_nonneg_left h2 hCu0
            _ = 56 * Cu * ε ^ (rr : ℝ) := by ring
        -- the matched fibre difference J₀ = ∫₀ˢF[x] − ∫₀^{sy}F[y]
        have hJ0 : |(∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            - ∫ σ in (0 : ℝ)..sy, F (suspensionMk T hτ (y, σ))|
            ≤ (ρmax * (CF : ℝ) * 183 + 56 * ((Cρ : ℝ) * M)) * ε ^ (rr : ℝ) := by
          have hmaster := absJ_matched_le T hτ hρpos hρ0 hdiam F hF hM hρub hρLip hint x y
            (a := 0) (b := u) (H := 61 * ε) (le_refl 0) huI.1 huI.2.le (by linarith [hε0]) hHfb
          rw [mul_zero, mul_zero, hsu, ← hsy_def] at hmaster
          refine hmaster.trans ?_
          have hpow := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 183)
            (by positivity) (by nlinarith [hε0] : 3 * (61 * ε) ≤ 183 * ε) hε0
          have hT1 : ρmax * ((CF : ℝ) * (3 * (61 * ε)) ^ (rr : ℝ)) * (u - 0)
              ≤ ρmax * (CF : ℝ) * 183 * ε ^ (rr : ℝ) := by
            have hfac : (0 : ℝ) ≤ ρmax * (CF : ℝ) := by positivity
            have hu1 : u - 0 ≤ 1 := by linarith [huI.2.le]
            calc ρmax * ((CF : ℝ) * (3 * (61 * ε)) ^ (rr : ℝ)) * (u - 0)
                ≤ ρmax * ((CF : ℝ) * (183 * ε ^ (rr : ℝ))) * 1 := by
                  apply mul_le_mul _ hu1 (by linarith [huI.1]) (by positivity)
                  apply mul_le_mul_of_nonneg_left _ hρmax0
                  exact mul_le_mul_of_nonneg_left hpow CF.coe_nonneg
              _ = ρmax * (CF : ℝ) * 183 * ε ^ (rr : ℝ) := by ring
          have hT2 : (Cρ : ℝ) * dist x y * (M * (u - 0))
              ≤ 56 * ((Cρ : ℝ) * M) * ε ^ (rr : ℝ) := by
            have hu1 : u - 0 ≤ 1 := by linarith [huI.2.le]
            have hstep : (Cρ : ℝ) * dist x y * (M * (u - 0)) ≤ (Cρ : ℝ) * (56 * ε) * (M * 1) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hd56 Cρ.coe_nonneg)
                (mul_le_mul_of_nonneg_left hu1 hM0)
                (mul_nonneg hM0 (by linarith [huI.1]))
                (mul_nonneg Cρ.coe_nonneg (by linarith [hε0]))
            refine hstep.trans ?_
            have : (Cρ : ℝ) * (56 * ε) * (M * 1) = 56 * ((Cρ : ℝ) * M) * ε := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_left hεr (by positivity)
          linarith [hT1, hT2]
        -- the small vertical correction ∫_{sy}^t F[y]
        have hCle : |∫ σ in sy..t, F (suspensionMk T hτ (y, σ))| ≤ ρmax * M * ε ^ (rr : ℝ) := by
          refine (abs_integral_fibre_le T hτ F hM y sy t).trans ?_
          rw [hsy_t, abs_of_nonneg (by nlinarith [habsε, hypos.le, sub_nonneg.mpr huv] :
            (0 : ℝ) ≤ τ y * (v - u))]
          have hle : τ y * (v - u) ≤ ρmax * ε := by
            have h1 : τ y * (v - u) ≤ ρmax * (v - u) :=
              mul_le_mul_of_nonneg_right (hρub y) (by linarith [huv])
            have h2 : ρmax * (v - u) ≤ ρmax * ε := mul_le_mul_of_nonneg_left habsε hρmax0
            linarith
          calc M * (τ y * (v - u)) ≤ M * (ρmax * ε) := mul_le_mul_of_nonneg_left hle hM0
            _ = ρmax * M * ε := by ring
            _ ≤ ρmax * M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr (by positivity)
        rw [hucx, hucy, ← hadd_y]
        rw [show u₀ x + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
              - (u₀ y + ((∫ σ in (0 : ℝ)..sy, F (suspensionMk T hτ (y, σ)))
                + ∫ σ in sy..t, F (suspensionMk T hτ (y, σ))))
            = (u₀ x - u₀ y) + ((∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
                - ∫ σ in (0 : ℝ)..sy, F (suspensionMk T hτ (y, σ)))
              - ∫ σ in sy..t, F (suspensionMk T hτ (y, σ)) from by ring]
        refine le_trans ?_ (hfin
          (56 * Cu + (ρmax * (CF : ℝ) * 183 + 56 * ((Cρ : ℝ) * M)) + ρmax * M)
          (by rw [hKdef]; nlinarith [hCu0, hM0, CF.coe_nonneg, Cρ.coe_nonneg, hρmax0]))
        rw [add_mul, add_mul]
        refine (abs_sub_le_abs_add _ _).trans ?_
        have htri := abs_add_le (u₀ x - u₀ y)
          ((∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            - ∫ σ in (0 : ℝ)..sy, F (suspensionMk T hτ (y, σ)))
        linarith [hAle, hJ0, hCle, htri]
      · -- From-above representation.
        have hD6 : dist (T x) (T y) ≤ 6 * ε := by
          nlinarith [htD, mul_le_mul_of_nonneg_right (by linarith : (7 : ℝ) / 8 ≤ v) hD0, hε0]
        have hHfa : ∀ w, v ≤ w → w ≤ 1 → hlen T w x y ≤ 13 * ε := by
          intro w hvw hw1
          have h1 : (1 - w) * dist x y ≤ (1 - v) * dist x y :=
            mul_le_mul_of_nonneg_right (by linarith) hd0
          have h2 : w * dist (T x) (T y) ≤ dist (T x) (T y) :=
            mul_le_of_le_one_left hD0 hw1
          simp only [hlen]; nlinarith [htd, hD6, h1, h2]
        have hucax := uCover_fromAbove_var T hτ F u₀ hu₀ hint x s
        have hucay := uCover_fromAbove_var T hτ F u₀ hu₀ hint y t
        -- match at normalized v: split x's upper integral at vx = τx·v
        set vx := τ x * v with hvx_def
        have hs_vx : vx - s = τ x * (v - u) := by rw [hvx_def, ← hsu]; ring
        have hadd_x := intervalIntegral.integral_add_adjacent_intervals
          (hint x s vx) (hint x vx (τ x))
        have hAle : |u₀ (T x) - u₀ (T y)| ≤ 6 * Cu * ε ^ (rr : ℝ) := by
          refine (hu₀hol (T x) (T y)).trans ?_
          have h2 := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 6) hD0 hD6 hε0
          calc Cu * dist (T x) (T y) ^ (rr : ℝ) ≤ Cu * (6 * ε ^ (rr : ℝ)) :=
                mul_le_mul_of_nonneg_left h2 hCu0
            _ = 6 * Cu * ε ^ (rr : ℝ) := by ring
        -- the matched upper fibre difference J₁ = ∫_{vx}^{τx}F[x] − ∫_t^{τy}F[y]
        have hJ1 : |(∫ σ in vx..(τ x), F (suspensionMk T hτ (x, σ)))
            - ∫ σ in t..(τ y), F (suspensionMk T hτ (y, σ))|
            ≤ (ρmax * (CF : ℝ) * 39 + 7 * ((Cρ : ℝ) * M)) * ε ^ (rr : ℝ) := by
          have hmaster := absJ_matched_le T hτ hρpos hρ0 hdiam F hF hM hρub hρLip hint x y
            (a := v) (b := 1) (H := 13 * ε) hvI.1 hvI.2.le (le_refl 1) (by linarith [hε0]) hHfa
          rw [mul_one, mul_one, ← hvx_def, htv] at hmaster
          refine hmaster.trans ?_
          have hpow := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 39)
            (by positivity) (by nlinarith [hε0] : 3 * (13 * ε) ≤ 39 * ε) hε0
          have h1v : (0 : ℝ) ≤ 1 - v := by linarith [hvI.2.le]
          have hT1 : ρmax * ((CF : ℝ) * (3 * (13 * ε)) ^ (rr : ℝ)) * (1 - v)
              ≤ ρmax * (CF : ℝ) * 39 * ε ^ (rr : ℝ) := by
            have hfac : (0 : ℝ) ≤ ρmax * (CF : ℝ) := by positivity
            have hv1 : (1 : ℝ) - v ≤ 1 := by linarith [hvI.1]
            calc ρmax * ((CF : ℝ) * (3 * (13 * ε)) ^ (rr : ℝ)) * (1 - v)
                ≤ ρmax * ((CF : ℝ) * (39 * ε ^ (rr : ℝ))) * 1 := by
                  apply mul_le_mul _ hv1 h1v (by positivity)
                  apply mul_le_mul_of_nonneg_left _ hρmax0
                  exact mul_le_mul_of_nonneg_left hpow CF.coe_nonneg
              _ = ρmax * (CF : ℝ) * 39 * ε ^ (rr : ℝ) := by ring
          have hT2 : (Cρ : ℝ) * dist x y * (M * (1 - v))
              ≤ 7 * ((Cρ : ℝ) * M) * ε ^ (rr : ℝ) := by
            have hkey : dist x y * (M * (1 - v)) = M * ((1 - v) * dist x y) := by ring
            rw [mul_assoc, hkey]
            have hstep : (Cρ : ℝ) * (M * ((1 - v) * dist x y)) ≤ (Cρ : ℝ) * (M * (7 * ε)) := by
              apply mul_le_mul_of_nonneg_left _ Cρ.coe_nonneg
              exact mul_le_mul_of_nonneg_left htd hM0
            refine hstep.trans ?_
            have : (Cρ : ℝ) * (M * (7 * ε)) = 7 * ((Cρ : ℝ) * M) * ε := by ring
            rw [this]; exact mul_le_mul_of_nonneg_left hεr (by positivity)
          linarith [hT1, hT2]
        -- the small vertical correction ∫_s^{vx}F[x]
        have hCle : |∫ σ in s..vx, F (suspensionMk T hτ (x, σ))| ≤ ρmax * M * ε ^ (rr : ℝ) := by
          refine (abs_integral_fibre_le T hτ F hM x s vx).trans ?_
          rw [hs_vx, abs_of_nonneg (by nlinarith [habsε, hxpos.le, sub_nonneg.mpr huv] :
            (0 : ℝ) ≤ τ x * (v - u))]
          have hle : τ x * (v - u) ≤ ρmax * ε := by
            have h1 : τ x * (v - u) ≤ ρmax * (v - u) :=
              mul_le_mul_of_nonneg_right (hρub x) (by linarith [huv])
            have h2 : ρmax * (v - u) ≤ ρmax * ε := mul_le_mul_of_nonneg_left habsε hρmax0
            linarith
          calc M * (τ x * (v - u)) ≤ M * (ρmax * ε) := mul_le_mul_of_nonneg_left hle hM0
            _ = ρmax * M * ε := by ring
            _ ≤ ρmax * M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr (by positivity)
        rw [hucax, hucay, ← hadd_x]
        rw [show u₀ (T x) - ((∫ σ in s..vx, F (suspensionMk T hτ (x, σ)))
                + ∫ σ in vx..(τ x), F (suspensionMk T hτ (x, σ)))
              - (u₀ (T y) - ∫ σ in t..(τ y), F (suspensionMk T hτ (y, σ)))
            = (u₀ (T x) - u₀ (T y)) - (∫ σ in s..vx, F (suspensionMk T hτ (x, σ)))
              - ((∫ σ in vx..(τ x), F (suspensionMk T hτ (x, σ)))
                - ∫ σ in t..(τ y), F (suspensionMk T hτ (y, σ))) from by ring]
        refine le_trans ?_ (hfin (6 * Cu + (ρmax * (CF : ℝ) * 39 + 7 * ((Cρ : ℝ) * M)) + ρmax * M)
          (by rw [hKdef]; nlinarith [hCu0, hM0, CF.coe_nonneg, Cρ.coe_nonneg, hρmax0]))
        rw [add_mul, add_mul]
        refine (abs_sub_le_abs_add _ _).trans ?_
        have htri := abs_sub_le_abs_add (u₀ (T x) - u₀ (T y))
          (∫ σ in s..vx, F (suspensionMk T hτ (x, σ)))
        linarith [hAle, hJ1, hCle, htri]
    · -- Wrap regime: (1 − v) + u ≤ ε.
      have hmin_eq : min |u - v| (1 - |u - v|) = 1 - |u - v| :=
        min_eq_right (by linarith [hw])
      have hsum : (1 - v) + u ≤ ε := by
        have h := hHGT
        simp only [hgt] at h
        rw [hmin_eq, habs_uv] at h; linarith
      have h1vnn : (0 : ℝ) ≤ 1 - v := by linarith [hvI.2.le]
      have hu_ε : u ≤ ε := by linarith [h1vnn]
      have h1v_ε : 1 - v ≤ ε := by linarith [huI.1]
      have hw2 : dist x (T y) ≤ 2 * ε := by
        have hwrapd := dist_map_le_embDistVar_wrap T hτ hρpos hρ0 hdiam hd' hd
        rw [embDistVar_comm T hτ hρpos hρ0 hdiam (suspensionMk T hτ (y, t))
          (suspensionMk T hτ (x, s)), ← hεdef, ← hu_def, ← hv_def] at hwrapd
        rw [dist_comm x (T y)]; linarith
      have hucay := uCover_fromAbove_var T hτ F u₀ hu₀ hint y t
      have hAle : |u₀ x - u₀ (T y)| ≤ 2 * Cu * ε ^ (rr : ℝ) := by
        refine (hu₀hol x (T y)).trans ?_
        have h2 := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 2) dist_nonneg hw2 hε0
        calc Cu * dist x (T y) ^ (rr : ℝ) ≤ Cu * (2 * ε ^ (rr : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 hCu0
          _ = 2 * Cu * ε ^ (rr : ℝ) := by ring
      have hBle : |∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ))| ≤ ρmax * M * ε ^ (rr : ℝ) := by
        refine (abs_integral_fibre_le T hτ F hM x 0 s).trans ?_
        rw [abs_of_nonneg (by linarith [hd.1] : (0 : ℝ) ≤ s - 0)]
        have hsε : s ≤ ρmax * ε := by
          have : s = τ x * u := hsu.symm
          rw [this]
          calc τ x * u ≤ ρmax * u := mul_le_mul_of_nonneg_right (hρub x) huI.1
            _ ≤ ρmax * ε := mul_le_mul_of_nonneg_left hu_ε hρmax0
        calc M * (s - 0) ≤ M * (ρmax * ε) := by
              rw [sub_zero]; exact mul_le_mul_of_nonneg_left hsε hM0
          _ = ρmax * M * ε := by ring
          _ ≤ ρmax * M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr (by positivity)
      have hCle : |∫ σ in t..(τ y), F (suspensionMk T hτ (y, σ))| ≤ ρmax * M * ε ^ (rr : ℝ) := by
        refine (abs_integral_fibre_le T hτ F hM y t (τ y)).trans ?_
        rw [abs_of_nonneg (by linarith [hd'.2.le] : (0 : ℝ) ≤ τ y - t)]
        have htε : τ y - t ≤ ρmax * ε := by
          have heq : τ y - t = τ y * (1 - v) := by rw [← htv]; ring
          rw [heq]
          calc τ y * (1 - v) ≤ ρmax * (1 - v) := mul_le_mul_of_nonneg_right (hρub y) h1vnn
            _ ≤ ρmax * ε := mul_le_mul_of_nonneg_left h1v_ε hρmax0
        calc M * (τ y - t) ≤ M * (ρmax * ε) := mul_le_mul_of_nonneg_left htε hM0
          _ = ρmax * M * ε := by ring
          _ ≤ ρmax * M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr (by positivity)
      rw [hucx, hucay]
      rw [show u₀ x + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            - (u₀ (T y) - ∫ σ in t..(τ y), F (suspensionMk T hτ (y, σ)))
          = (u₀ x - u₀ (T y)) + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            + ∫ σ in t..(τ y), F (suspensionMk T hτ (y, σ)) from by ring]
      refine le_trans ?_ (hfin (2 * Cu + ρmax * M + ρmax * M)
        (by rw [hKdef]; nlinarith [hCu0, hM0, CF.coe_nonneg, Cρ.coe_nonneg, hρmax0]))
      rw [show (2 * Cu + ρmax * M + ρmax * M) * ε ^ (rr : ℝ)
          = 2 * Cu * ε ^ (rr : ℝ) + ρmax * M * ε ^ (rr : ℝ) + ρmax * M * ε ^ (rr : ℝ) from by ring]
      refine (abs_add_le _ _).trans ?_
      have htri := abs_add_le (u₀ x - u₀ (T y))
        (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
      linarith [hAle, hBle, hCle, htri]

/-- **Unordered seam-gluing estimate (variable roof).** The ordered core symmetrised over the two
normalized-height orderings. -/
theorem holder_uCover_symm_var (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (hρub : ∀ x, τ x ≤ ρmax) (hρLip : LipschitzWith Cρ τ)
    (u₀ : X → ℝ) {Cu : ℝ} (hCu0 : 0 ≤ Cu)
    (hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ Cu * dist a b ^ (rr : ℝ))
    (hu₀ : ∀ a, inducedBaseCocycle T hτ F a = u₀ (T a) - u₀ a)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x y : X) {s t : ℝ} (hd : (x, s) ∈ suspensionDomain τ) (hd' : (y, t) ∈ suspensionDomain τ) :
    |uCover T hτ F u₀ (x, s) - uCover T hτ F u₀ (y, t)|
      ≤ 300 * (Cu + ρmax * M + ρmax * (CF : ℝ) + (Cρ : ℝ) * M + 1)
        * embDistVar T hτ hρpos hρ0 hdiam (suspensionMk T hτ (x, s))
          (suspensionMk T hτ (y, t)) ^ (rr : ℝ) := by
  rcases le_total (s / τ x) (t / τ y) with huv | hvu
  · exact holder_uCover_core_var T hτ hρpos hρ0 hdiam F hrr0 hrr1 hF hM hρub hρLip u₀ hCu0
      hu₀hol hu₀ hint x y hd hd' huv
  · have h := holder_uCover_core_var T hτ hρpos hρ0 hdiam F hrr0 hrr1 hF hM hρub hρLip u₀ hCu0
      hu₀hol hu₀ hint y x hd' hd hvu
    rw [abs_sub_comm,
      embDistVar_comm T hτ hρpos hρ0 hdiam (suspensionMk T hτ (y, t))
        (suspensionMk T hτ (x, s))] at h
    exact h

/-- **The keystone: the cross-seam Hölder gluing (variable roof).** The descended transfer function
`suspTransfer` is `embDistVar`-Hölder. Reducing `p, q` to their canonical representatives
(`suspensionRepVar`) reduces to the unordered gluing bound. -/
theorem holderWith_suspTransfer_var (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (hρub : ∀ x, τ x ≤ ρmax) (hρLip : LipschitzWith Cρ τ)
    (u₀ : X → ℝ) {Cu : ℝ} (hCu0 : 0 ≤ Cu)
    (hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ Cu * dist a b ^ (rr : ℝ))
    (hu₀ : ∀ a, inducedBaseCocycle T hτ F a = u₀ (T a) - u₀ a)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (hg : ∀ p, uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p)
    (p q : SuspensionSpace T hτ) :
    |suspTransfer T hτ F u₀ hg p - suspTransfer T hτ F u₀ hg q|
      ≤ 300 * (Cu + ρmax * M + ρmax * (CF : ℝ) + (Cρ : ℝ) * M + 1)
        * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ) := by
  have hval : ∀ z, suspTransfer T hτ F u₀ hg z
      = uCover T hτ F u₀ (suspensionRepVar T hτ hρpos hρ0 z) := by
    intro z
    conv_lhs => rw [← suspensionMk_suspensionRepVar T hτ hρpos hρ0 z]
    rw [suspTransfer_mk]
  have hemb : embDistVar T hτ hρpos hρ0 hdiam p q
      = embDistVar T hτ hρpos hρ0 hdiam
          (suspensionMk T hτ (suspensionRepVar T hτ hρpos hρ0 p))
          (suspensionMk T hτ (suspensionRepVar T hτ hρpos hρ0 q)) := by
    rw [suspensionMk_suspensionRepVar, suspensionMk_suspensionRepVar]
  rw [hval p, hval q, hemb]
  exact holder_uCover_symm_var T hτ hρpos hρ0 hdiam F hrr0 hrr1 hF hM hρub hρLip u₀ hCu0
    hu₀hol hu₀ hint (suspensionRepVar T hτ hρpos hρ0 p).1 (suspensionRepVar T hτ hρpos hρ0 q).1
    (suspensionRepVar_mem_domain T hτ hρpos hρ0 p) (suspensionRepVar_mem_domain T hτ hρpos hρ0 q)

/-! ### Theorem C: the variable-roof Hölder flow-Livšic equivalence -/

/-- **Hölder flow-Livšic equivalence for variable-roof suspension flows (issue #63, tier 3).** For a
base map `T` that is a compact-system Hölder-Livšic map (continuous, `L`-Lipschitz, a dense orbit,
the summed exponential closing property) and a bounded roof (`ρmin ≤ τ ≤ ρmax`) that is
`Cρ`-Lipschitz, an `embDistVar`-`r`-Hölder bounded flow observable `F` is a **variable-roof Hölder
flow coboundary iff** every periodic Birkhoff sum of the induced base observable vanishes.

The forward direction is the tier-I obstruction (`inducedBaseCocycle_isCoboundary`, general-roof).
The converse combines Lemma A-var (`holderWith_inducedBaseCocycle_var`), the discrete Hölder-Livšic
converse with an exposed exponent (`exists_baseTransfer_holder`), and the keystone cross-seam gluing
(`holderWith_suspTransfer_var`), with the coboundary equation from the general-roof
`suspTransfer_flow`. The classical Lipschitz-roof hypothesis is essential (see module docstring);
a rescale to a constant roof is *not* available unless `τ` is cohomologous to a constant. -/
theorem livsic_holderFlow_varRoof [CompactSpace X] (hdiam : ∀ a b : X, dist a b ≤ 1)
    (hT : Continuous ⇑T) {L : ℝ≥0} (hTL : LipschitzWith L ⇑T)
    (F : SuspensionSpace T hτ → ℝ) {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (hρub : ∀ x, τ x ≤ ρmax) (hρLip : LipschitzWith Cρ τ)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    {δ Kc : ℝ} (hδ : 0 < δ) (hKc : 0 ≤ Kc) (hclosing : ExpClosing (⇑T) (rr : ℝ) δ Kc)
    {x₀ : X} (hdense : DenseRange fun n : ℕ => (⇑T)^[n] x₀) :
    IsHolderFlowCoboundaryVar T hτ hρpos hρ0 hdiam (suspensionFlowMap T hτ) F ↔
      HasVanishingPeriodicSums (⇑T) (inducedBaseCocycle T hτ F) := by
  constructor
  · intro h
    exact (inducedBaseCocycle_isCoboundary T hτ F
      h.isFlowCoboundary).hasVanishingPeriodicSums
  · intro hvps
    have hfhol := holderWith_inducedBaseCocycle_var T hτ hρpos hρ0 hdiam F hrr0 hrr1 hF hM hρub
      hρLip hTL hint
    obtain ⟨Cu, u₀, hu₀hol', hu₀eq⟩ :=
      exists_baseTransfer_holder hT hrr0 hrr1 hfhol hδ hKc hclosing hvps hdense
    have hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ (Cu : ℝ) * dist a b ^ (rr : ℝ) := by
      intro a b
      have h := (hu₀hol'.holderOnWith Set.univ).dist_le (Set.mem_univ a) (Set.mem_univ b)
      rwa [Real.dist_eq] at h
    have hg := uCover_gen_hg_var T hτ F u₀ hu₀eq hint
    have hM0 : (0 : ℝ) ≤ M := (abs_nonneg _).trans (hM (suspensionMk T hτ (x₀, 0)))
    have hρmax0 : (0 : ℝ) ≤ ρmax := le_trans (lt_of_lt_of_le hρpos (hρ0 x₀)).le (hρub x₀)
    refine ⟨(300 * (((Cu : ℝ)) + ρmax * M + ρmax * (CF : ℝ) + (Cρ : ℝ) * M + 1)).toNNReal, rr,
      suspTransfer T hτ F u₀ hg, hrr0, hrr1, fun p q => ?_,
      fun q t => suspTransfer_flow T hτ F u₀ hg hint q t⟩
    rw [Real.coe_toNNReal _ (by positivity)]
    exact holderWith_suspTransfer_var T hτ hρpos hρ0 hdiam F hrr0 hrr1 hF hM hρub hρLip u₀
      Cu.coe_nonneg hu₀hol hu₀eq hint hg p q

/-- **Flow-native form of the variable-roof Hölder flow-Livšic equivalence.** Same hypotheses as
`livsic_holderFlow_varRoof`, with the obstruction phrased as the vanishing of every closed-orbit
integral of `F`, via the general-roof lap-decomposition bridge
`suspension_periodicOrbitIntegral_eq_birkhoffSum`. -/
theorem livsic_holderFlow_varRoof_orbitIntegral [CompactSpace X]
    (hdiam : ∀ a b : X, dist a b ≤ 1)
    (hT : Continuous ⇑T) {L : ℝ≥0} (hTL : LipschitzWith L ⇑T)
    (F : SuspensionSpace T hτ → ℝ) {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDistVar T hτ hρpos hρ0 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (hρub : ∀ x, τ x ≤ ρmax) (hρLip : LipschitzWith Cρ τ)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    {δ Kc : ℝ} (hδ : 0 < δ) (hKc : 0 ≤ Kc) (hclosing : ExpClosing (⇑T) (rr : ℝ) δ Kc)
    {x₀ : X} (hdense : DenseRange fun n : ℕ => (⇑T)^[n] x₀) :
    IsHolderFlowCoboundaryVar T hτ hρpos hρ0 hdiam (suspensionFlowMap T hτ) F ↔
      ∀ (n : ℕ) (p : X), (⇑T)^[n] p = p →
        ∫ s in (0 : ℝ)..(birkhoffSum (⇑T) τ n p),
          F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)) = 0 := by
  have hint' : ∀ (p : X) (a b : ℝ),
      IntervalIntegrable
        (fun s => F (suspensionFlowMap T hτ s (suspensionSection' T hτ p))) volume a b := by
    intro p a b
    have hdir : (fun s => F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)))
        = fun s => F (suspensionMk T hτ (p, s)) := by
      funext s
      simp only [suspensionSection', suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]
    rw [hdir]; exact hint p a b
  have hequiv : HasVanishingPeriodicSums (⇑T) (inducedBaseCocycle T hτ F) ↔
      ∀ (n : ℕ) (p : X), (⇑T)^[n] p = p →
        ∫ s in (0 : ℝ)..(birkhoffSum (⇑T) τ n p),
          F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)) = 0 := by
    constructor
    · intro hvps n p hp
      rw [suspension_periodicOrbitIntegral_eq_birkhoffSum T hτ F p n (fun k _ => hint' p _ _)]
      exact hvps n p hp
    · intro hflow n p hp
      rw [← suspension_periodicOrbitIntegral_eq_birkhoffSum T hτ F p n (fun k _ => hint' p _ _)]
      exact hflow n p hp
  exact (livsic_holderFlow_varRoof T hτ hρpos hρ0 hdiam hT hTL F hrr0 hrr1 hF hM hρub hρLip hint
    hδ hKc hclosing hdense).trans hequiv

end

end ErgodicTheory
