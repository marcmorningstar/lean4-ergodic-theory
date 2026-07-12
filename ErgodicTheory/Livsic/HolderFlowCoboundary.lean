/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionMetric
import ErgodicTheory.Continuous.SuspensionLivsic
import ErgodicTheory.Livsic.Abstract
import ErgodicTheory.Livsic.HolderExtend

/-!
# Hölder-regularity Livšic theorem for constant-roof suspension flows

This module upgrades the regularity-free tier-III Livšic equivalence
(`ErgodicTheory.livsic_suspensionFlow_constRoof`) to a **Hölder-regularity** statement, tiers 2 + 4
of issue #63. Working on the Bowen–Walters metric space `SuspensionSpace T hτ` (constant roof `1`,
`ErgodicTheory.embDist`), we introduce `IsHolderFlowCoboundary`: a flow observable `F` is a
*Hölder* flow coboundary if its flow transfer function `u` is Hölder continuous for the embedding
metric. We then prove the constant-roof equivalence

`IsHolderFlowCoboundary Φ F ↔ HasVanishingPeriodicSums T (inducedBaseCocycle T hτ F)`

for an embedding-`α`-Hölder, bounded observable `F`, under the discrete Hölder-Livšic hypotheses on
the base (compactness, a dense orbit, and the summed exponential closing property).

## The seam-gluing estimate

The transfer function is the descent `suspTransfer T hτ F u₀` of the fundamental-domain candidate
`uCover (x, s) = u₀ x + ∫₀ˢ F [x, σ] dσ` (`ErgodicTheory.SuspensionLivsic`). The **substantive
content** here is the cross-seam Hölder gluing (`holderWith_suspTransfer`): the transfer function is
Hölder for the embedding metric. Its proof follows the exact-seam-identity philosophy of
`uCover_gen`: on the fundamental strip the fibre integral is controlled by the embedding-Hölder
modulus of `F`, the base value by the discrete Hölder transfer `u₀`, and the seam is bridged by two
algebraically equivalent representations of `uCover` (from-below and from-above), matched by the
base cohomological identity `inducedBaseCocycle F x = u₀ (T x) − u₀ x`. The base-distance recoveries
use the two Kuratowski test bundles `muFun`/`nuFun` (a `2 × 2` elimination), and the seam-wrap
regime uses `dist_map_le_embDist_wrap`.

## Main definitions

* `ErgodicTheory.IsHolderFlowCoboundary` — `F` has an embedding-Hölder flow transfer function.

## Main results

* `ErgodicTheory.IsHolderFlowCoboundary.isFlowCoboundary` — a Hölder flow coboundary is a flow
  coboundary (forgets the modulus).
* `ErgodicTheory.holderWith_inducedBaseCocycle` — the induced base observable is Hölder (Lemma A).
* `ErgodicTheory.holderWith_suspTransfer` — the cross-seam Hölder gluing (the keystone).
* `ErgodicTheory.livsic_holderFlow_constRoof` — the tier 2 + 4 equivalence.
* `ErgodicTheory.livsic_holderFlow_constRoof_orbitIntegral` — its flow-native (closed-orbit) form.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972) 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §19.2.
* R. Bowen, P. Walters, *Expansive one-parameter flows*, J. Diff. Eq. **12** (1972) 180–193.
-/

open MeasureTheory Function
open scoped NNReal

namespace ErgodicTheory

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) (hτ1 : τ = fun _ => (1 : ℝ))

/-! ### The definition -/

/-- `F` is a **Hölder flow coboundary** for the flow `Φ` on the constant-roof suspension space if it
is a flow coboundary (`u (Φ t q) − u q = ∫₀ᵗ F (Φ s q) ds`) whose transfer function `u` is Hölder
continuous for the Bowen–Walters embedding metric `embDist`. This is the regularity upgrade of
`IsFlowCoboundary`, phrased `dist`-free through `embDist` to avoid metric-instance plumbing; under
`suspensionMetricSpace` (where `dist = embDist`) this is exactly `HolderWith`. -/
def IsHolderFlowCoboundary (hdiam : ∀ a b : X, dist a b ≤ 1)
    (Φ : ℝ → SuspensionSpace T hτ → SuspensionSpace T hτ) (F : SuspensionSpace T hτ → ℝ) : Prop :=
  ∃ (C rr : ℝ≥0) (u : SuspensionSpace T hτ → ℝ), 0 < rr ∧ rr ≤ 1 ∧
    (∀ p q, |u p - u q| ≤ (C : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ)) ∧
    (∀ (q : SuspensionSpace T hτ) (t : ℝ), u (Φ t q) - u q = ∫ s in (0 : ℝ)..t, F (Φ s q))

/-- **A Hölder flow coboundary is a flow coboundary** (forget the Hölder modulus). -/
theorem IsHolderFlowCoboundary.isFlowCoboundary {hdiam : ∀ a b : X, dist a b ≤ 1}
    {Φ : ℝ → SuspensionSpace T hτ → SuspensionSpace T hτ} {F : SuspensionSpace T hτ → ℝ}
    (h : IsHolderFlowCoboundary T hτ hτ1 hdiam Φ F) : IsFlowCoboundary Φ F := by
  obtain ⟨_, _, u, _, _, _, hcob⟩ := h
  exact ⟨u, hcob⟩

/-! ### Elementary `rpow` and Kuratowski recovery lemmas -/

/-- **Kuratowski recovery of the `T`-image base distance** at a common height `t ∈ [0, 1]`. A
`2 × 2` elimination of the two test weightings isolates `t · (kur (T x) − kur (T y))`, yielding a
bound on `t · dist (T x) (T y)` by the two Kuratowski parts at height `t`. -/
theorem embHeight_recover_map (hdiam : ∀ a b : X, dist a b ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x y : X) :
    t * dist (T x) (T y) ≤ dist (nuFun T hdiam (x, t)) (nuFun T hdiam (y, t))
      + (1 - t) * dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t)) := by
  have key : t • (kur hdiam (T x) - kur hdiam (T y))
      = (nuFun T hdiam (x, t) - nuFun T hdiam (y, t))
        - (1 - t) • (muFun T hdiam (x, t) - muFun T hdiam (y, t)) := by
    simp only [muFun, nuFun]; module
  have hlhs : ‖t • (kur hdiam (T x) - kur hdiam (T y))‖ = t * dist (T x) (T y) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, norm_kur_sub]
  rw [← hlhs, key]
  calc ‖(nuFun T hdiam (x, t) - nuFun T hdiam (y, t))
        - (1 - t) • (muFun T hdiam (x, t) - muFun T hdiam (y, t))‖
      ≤ ‖nuFun T hdiam (x, t) - nuFun T hdiam (y, t)‖
        + ‖(1 - t) • (muFun T hdiam (x, t) - muFun T hdiam (y, t))‖ := norm_sub_le _ _
    _ = dist (nuFun T hdiam (x, t)) (nuFun T hdiam (y, t))
        + (1 - t) * dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t)) := by
        rw [← dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          ← dist_eq_norm]

/-- **Kuratowski recovery of the base distance** at a common height `t ∈ [0, 1]`:
`(1 − t) · dist x y ≤ dist (muFun (x,t)) (muFun (y,t)) + t · dist (T x) (T y)`. -/
theorem embHeight_recover_base (hdiam : ∀ a b : X, dist a b ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x y : X) :
    (1 - t) * dist x y ≤ dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t))
      + t * dist (T x) (T y) := by
  have key : (1 - t) • (kur hdiam x - kur hdiam y)
      = (muFun T hdiam (x, t) - muFun T hdiam (y, t))
        - t • (kur hdiam (T x) - kur hdiam (T y)) := by simp only [muFun]; module
  have hlhs : ‖(1 - t) • (kur hdiam x - kur hdiam y)‖ = (1 - t) * dist x y := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_kur_sub]
  rw [← hlhs, key]
  calc ‖(muFun T hdiam (x, t) - muFun T hdiam (y, t)) - t • (kur hdiam (T x) - kur hdiam (T y))‖
      ≤ ‖muFun T hdiam (x, t) - muFun T hdiam (y, t)‖ + ‖t • (kur hdiam (T x) - kur hdiam (T y))‖ :=
        norm_sub_le _ _
    _ = dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t)) + t * dist (T x) (T y) := by
        rw [← dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, norm_kur_sub]

/-! ### The embedding-Hölder modulus of the fibre integrand -/

/-- **Fibre-difference bound.** For a common fibre height `σ ∈ [0, 1]`, the embedding-Hölder modulus
of `F` controls the fibre difference by the horizontal length: `|F [x, σ] − F [y, σ]|
≤ CF · (3 · hlen σ x y) ^ r`. The interior height `σ < 1` uses `embDist_le_three_hlen`; the top
`σ = 1` uses the seam identity `[x, 1] = [T x, 0]` and `hlen 1 x y = dist (T x) (T y)`. -/
theorem absF_fibre_diff_le (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0}
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    (x y : X) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |F (suspensionMk T hτ (x, σ)) - F (suspensionMk T hτ (y, σ))|
      ≤ (CF : ℝ) * (3 * hlen T σ x y) ^ (rr : ℝ) := by
  have hkey : embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, σ)) (suspensionMk T hτ (y, σ))
      ≤ 3 * hlen T σ x y := by
    rcases lt_or_eq_of_le hσ1 with hlt | heq
    · exact embDist_le_three_hlen T hτ hτ1 hdiam ⟨hσ0, hlt⟩ x y
    · have hx1 : suspensionMk T hτ (x, σ) = suspensionMk T hτ (T x, 0) := by
        rw [heq, ← zero_add (1 : ℝ), ← suspensionMk_T T hτ 1 hτ1 x 0]
      have hy1 : suspensionMk T hτ (y, σ) = suspensionMk T hτ (T y, 0) := by
        rw [heq, ← zero_add (1 : ℝ), ← suspensionMk_T T hτ 1 hτ1 y 0]
      have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl 0, one_pos⟩
      rw [hx1, hy1]
      refine (embDist_le_three_hlen T hτ hτ1 hdiam h0 (T x) (T y)).trans (le_of_eq ?_)
      rw [heq, hlen_one, hlen_zero]
  have hcf : (0 : ℝ) ≤ (CF : ℝ) := CF.coe_nonneg
  calc |F (suspensionMk T hτ (x, σ)) - F (suspensionMk T hτ (y, σ))|
      ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, σ))
          (suspensionMk T hτ (y, σ)) ^ (rr : ℝ) := hF _ _
    _ ≤ (CF : ℝ) * (3 * hlen T σ x y) ^ (rr : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (embDist_nonneg T hτ hτ1 hdiam _ _) hkey rr.coe_nonneg) hcf

/-! ### Lemma A: the induced base observable is Hölder -/

/-- **Lemma A: the induced base observable is Hölder.** If `F` is embedding-`r`-Hölder and `T` is
`L`-Lipschitz, the induced base observable `inducedBaseCocycle T hτ F` (the roof-`1` lap integral)
is `r`-Hölder with constant `CF · (3 · max 1 L) ^ r`: the fibre integrand is `r`-Hölder in the base
distance with modulus `CF · (3 · hlen σ) ^ r ≤ CF · (3 · max 1 L · dist x y) ^ r`, integrated over
the unit roof. -/
theorem holderWith_inducedBaseCocycle (hdiam : ∀ a b : X, dist a b ≤ 1)
    (F : SuspensionSpace T hτ → ℝ) {CF rr : ℝ≥0}
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    {L : ℝ≥0} (hTL : LipschitzWith L ⇑T)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b) :
    HolderWith ((CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ)).toNNReal rr
      (inducedBaseCocycle T hτ F) := by
  have hCnn : (0 : ℝ) ≤ (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) := by positivity
  refine holderWith_of_dist_le fun x y => ?_
  rw [Real.coe_toNNReal _ hCnn, Real.dist_eq]
  set B : ℝ := (CF : ℝ) * (3 * max 1 (L : ℝ)) ^ (rr : ℝ) * dist x y ^ (rr : ℝ) with hB
  have hτx : τ x = 1 := congrFun hτ1 x
  have hτy : τ y = 1 := congrFun hτ1 y
  have hfx : inducedBaseCocycle T hτ F x = ∫ σ in (0 : ℝ)..1, F (suspensionMk T hτ (x, σ)) := by
    rw [inducedBaseCocycle, hτx]
  have hfy : inducedBaseCocycle T hτ F y = ∫ σ in (0 : ℝ)..1, F (suspensionMk T hτ (y, σ)) := by
    rw [inducedBaseCocycle, hτy]
  rw [hfx, hfy, ← intervalIntegral.integral_sub (hint x 0 1) (hint y 0 1)]
  have hbd : ∀ σ ∈ Set.uIoc (0 : ℝ) 1,
      ‖F (suspensionMk T hτ (x, σ)) - F (suspensionMk T hτ (y, σ))‖ ≤ B := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hσ
    have hσ0 : (0 : ℝ) ≤ σ := hσ.1.le
    have hσ1 : σ ≤ 1 := hσ.2
    have hle := absF_fibre_diff_le T hτ hτ1 hdiam F hF x y hσ0 hσ1
    rw [Real.norm_eq_abs]
    refine hle.trans ?_
    have hhlen : hlen T σ x y ≤ max 1 (L : ℝ) * dist x y := by
      have hd2 : dist (T x) (T y) ≤ (L : ℝ) * dist x y := by
        have := hTL.dist_le_mul x y; simpa using this
      have h1 : (1 - σ) * dist x y ≤ (1 - σ) * (max 1 (L : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_left dist_nonneg (le_max_left _ _)) (by linarith)
      have h2 : σ * dist (T x) (T y) ≤ σ * (max 1 (L : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left (hd2.trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)) hσ0
      simp only [hlen]; nlinarith [h1, h2]
    have h3 : (3 : ℝ) * hlen T σ x y ≤ 3 * (max 1 (L : ℝ)) * dist x y := by nlinarith [hhlen]
    have h3nn : (0 : ℝ) ≤ 3 * hlen T σ x y := by
      have := hlen_nonneg T hσ0 hσ1 x y; linarith
    calc (CF : ℝ) * (3 * hlen T σ x y) ^ (rr : ℝ)
        ≤ (CF : ℝ) * (3 * (max 1 (L : ℝ)) * dist x y) ^ (rr : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h3nn h3 rr.coe_nonneg) CF.coe_nonneg
      _ = B := by
          rw [hB, Real.mul_rpow (by positivity) dist_nonneg]; ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans ?_
  rw [hB]; simp

/-! ### The base transfer function, with an explicit Hölder exponent -/

/-- **Exponent-exposing base Livšic converse.** The abstract Hölder-Livšic converse
(`exists_holderCoboundary_of_denseOrbit`) packaged so that the transfer function's Hölder exponent
is *exactly* the exponent `rr` of `φ` (the packed `IsHolderCoboundary` predicate hides it behind an
existential). Same construction: the Birkhoff-sum transfer on a dense orbit, its close-pair Hölder
modulus, the McShane extension, and density transport of the cohomology identity. -/
theorem exists_baseTransfer_holder [CompactSpace X] {S : X → X} (hS : Continuous S)
    {φ : X → ℝ} {Cφ rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1) (hφ : HolderWith Cφ rr φ)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hclosing : ExpClosing S (rr : ℝ) δ K)
    (hvps : HasVanishingPeriodicSums S φ)
    {x₀ : X} (hdense : DenseRange fun n : ℕ => S^[n] x₀) :
    ∃ (Cu : ℝ≥0) (u₀ : X → ℝ), HolderWith Cu rr u₀ ∧ ∀ x, φ x = u₀ (S x) - u₀ x := by
  classical
  set e : ℕ → X := fun n => S^[n] x₀ with he
  set w : ℕ → ℝ := fun n => birkhoffSum S φ n x₀ with hw
  set u₀ : X → ℝ := fun y => w (Function.invFun e y) with hu₀def
  have hu₀ : ∀ m, u₀ (e m) = w m := by
    intro m
    have hpre : e (Function.invFun e (e m)) = e m := Function.invFun_eq ⟨m, rfl⟩
    simp only [hu₀def]
    exact birkhoffSum_eq_of_orbit_eq' hvps hpre
  have he_succ : ∀ m, e (m + 1) = S (e m) := by
    intro m; simp only [he, Function.iterate_succ_apply']
  have hw_succ : ∀ m, w (m + 1) = w m + φ (e m) := by
    intro m; simp only [hw, he, birkhoffSum_succ]
  have hCK : (0 : ℝ) ≤ (Cφ : ℝ) * K := mul_nonneg Cφ.coe_nonneg hK
  have hclose_orbit : ∀ x ∈ Set.range e, ∀ y ∈ Set.range e, dist x y ≤ δ →
      |u₀ x - u₀ y| ≤ (Cφ : ℝ) * K * dist x y ^ (rr : ℝ) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hd
    rw [hu₀ a, hu₀ b]
    rcases le_total a b with hab | hba
    · rw [abs_sub_comm]
      exact abs_birkhoffSum_orbit_sub_le hφ hclosing hvps hab hd
    · have hd' : dist (e b) (e a) ≤ δ := by rw [dist_comm]; exact hd
      rw [dist_comm (e a) (e b)]
      exact abs_birkhoffSum_orbit_sub_le hφ hclosing hvps hba hd'
  obtain ⟨M, hM⟩ := exists_bound_of_closePairHolder hdense hδ hCK hclose_orbit
  have hM'0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hM' : ∀ x ∈ Set.range e, |u₀ x| ≤ max M 0 :=
    fun x hx => le_trans (hM x hx) (le_max_left _ _)
  obtain ⟨C', horbit_holder⟩ :=
    holderOnWith_of_closePairHolder_bounded hδ hCK hM'0 hclose_orbit hM'
  obtain ⟨v, hv_holder, hv_eqon⟩ := exists_holderWith_extension hrr0 hrr1 horbit_holder
  have hv_orbit : ∀ m, v (e m) = w m := fun m => (hv_eqon ⟨m, rfl⟩).symm.trans (hu₀ m)
  have hcohom_orbit : ∀ m, φ (e m) = v (S (e m)) - v (e m) := by
    intro m
    rw [← he_succ, hv_orbit (m + 1), hv_orbit m, hw_succ]; ring
  have hφc : Continuous φ := hφ.continuous hrr0
  have hvc : Continuous v := hv_holder.continuous hrr0
  have hgc : Continuous fun x => v (S x) - v x := (hvc.comp hS).sub hvc
  have hEq : φ = fun x => v (S x) - v x := by
    refine Continuous.ext_on hdense hφc hgc ?_
    rintro y ⟨m, rfl⟩
    exact hcohom_orbit m
  exact ⟨C', v, hv_holder, fun x => congrFun hEq x⟩

/-! ### Integral and representation helpers for the seam gluing -/

/-- A single fibre integral of `F` is bounded by `M · |b − a|` when `|F| ≤ M`. -/
theorem abs_integral_fibre_le (F : SuspensionSpace T hτ → ℝ) {M : ℝ} (hM : ∀ p, |F p| ≤ M)
    (x : X) (a b : ℝ) :
    |∫ σ in a..b, F (suspensionMk T hτ (x, σ))| ≤ M * |b - a| := by
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun σ _ => ?_)
  rw [Real.norm_eq_abs]; exact hM _

/-- **Fibre-difference integral bound.** Over `[a, b] ⊆ [0, 1]`, if the horizontal length is bounded
by `H`, the difference of the two fibre integrals is controlled by the embedding-Hölder modulus:
`|∫ₐᵇ F[x,σ] − ∫ₐᵇ F[y,σ]| ≤ CF · (3 · H) ^ r · (b − a)`. -/
theorem abs_integral_fibre_diff_le (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0} (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    (x y : X) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) {H : ℝ}
    (hH : ∀ σ, a ≤ σ → σ ≤ b → hlen T σ x y ≤ H)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b) :
    |(∫ σ in a..b, F (suspensionMk T hτ (x, σ))) - ∫ σ in a..b, F (suspensionMk T hτ (y, σ))|
      ≤ (CF : ℝ) * (3 * H) ^ (rr : ℝ) * (b - a) := by
  rw [← intervalIntegral.integral_sub (hint x a b) (hint y a b), ← Real.norm_eq_abs]
  have hbnd : ∀ σ ∈ Set.uIoc a b,
      ‖F (suspensionMk T hτ (x, σ)) - F (suspensionMk T hτ (y, σ))‖
        ≤ (CF : ℝ) * (3 * H) ^ (rr : ℝ) := by
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    have hσ0 : (0 : ℝ) ≤ σ := le_trans ha0 hσ.1.le
    have hσ1 : σ ≤ 1 := le_trans hσ.2 hb1
    rw [Real.norm_eq_abs]
    refine (absF_fibre_diff_le T hτ hτ1 hdiam F hF x y hσ0 hσ1).trans ?_
    have h3nn : (0 : ℝ) ≤ 3 * hlen T σ x y := by
      have := hlen_nonneg T hσ0 hσ1 x y; linarith
    have h3 : 3 * hlen T σ x y ≤ 3 * H := by
      have := hH σ hσ.1.le hσ.2; linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h3nn h3 rr.coe_nonneg) CF.coe_nonneg
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbnd).trans_eq ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]

include hτ1 in
/-- **From-above representation of the transfer candidate.** Using the base cohomological identity
`inducedBaseCocycle F x = u₀ (T x) − u₀ x` (roof `1`), the fundamental-strip candidate is also
`uCover (x, s) = u₀ (T x) − ∫ₛ¹ F [x, σ] dσ`, the "descend from the seam" form. -/
theorem uCover_fromAbove (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hu₀ : ∀ x, inducedBaseCocycle T hτ F x = u₀ (T x) - u₀ x)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x : X) (s : ℝ) :
    uCover T hτ F u₀ (x, s) = u₀ (T x) - ∫ σ in s..(1 : ℝ), F (suspensionMk T hτ (x, σ)) := by
  have hτx : τ x = 1 := congrFun hτ1 x
  have hval : u₀ (T x) = u₀ x + ∫ σ in (0 : ℝ)..1, F (suspensionMk T hτ (x, σ)) := by
    have h := hu₀ x
    rw [inducedBaseCocycle, hτx] at h; linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hint x 0 s) (hint x s 1)
  simp only [uCover]
  rw [hval]; linarith [hadd]

/-- The `muFun` part at a common height `t`, reduced from the embedding distance between the
canonical representatives `(x, s)`, `(y, t)`: `dist (muFun (x,t)) (muFun (y,t)) ≤ ε + |s − t|`. -/
theorem dist_muFun_common_le (hdiam : ∀ a b : X, dist a b ≤ 1) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) (x y : X) :
    dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t))
      ≤ embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t)) + |s - t| := by
  have h := dist_muFun_le_embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s))
    (suspensionMk T hτ (y, t))
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 y ht] at h
  have hvert : dist (muFun T hdiam (x, t)) (muFun T hdiam (x, s)) ≤ |s - t| :=
    (dist_muFun_sameBase_le T hdiam x t s).trans_eq (abs_sub_comm t s)
  have htri := dist_triangle (muFun T hdiam (x, t)) (muFun T hdiam (x, s)) (muFun T hdiam (y, t))
  linarith

/-- The `nuFun` part at a common height `t`, reduced from the embedding distance between the
canonical reps `(x, s)`, `(y, t)`: `dist (nuFun (x,t)) (nuFun (y,t)) ≤ ε + 2 · |s − t|`. -/
theorem dist_nuFun_common_le (hdiam : ∀ a b : X, dist a b ≤ 1) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) (x y : X) :
    dist (nuFun T hdiam (x, t)) (nuFun T hdiam (y, t))
      ≤ embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
        + 2 * |s - t| := by
  have h := dist_nuFun_le_embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s))
    (suspensionMk T hτ (y, t))
  rw [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 y ht] at h
  have hvert : dist (nuFun T hdiam (x, t)) (nuFun T hdiam (x, s)) ≤ 2 * |s - t| := by
    refine (dist_nuFun_sameBase_le T hdiam x ht.1 ht.2.le hs.1 hs.2.le).trans ?_
    rw [abs_sub_comm t s]
  have htri := dist_triangle (nuFun T hdiam (x, t)) (nuFun T hdiam (x, s)) (nuFun T hdiam (y, t))
  linarith

/-- Triangle inequality in the form `|a − b| ≤ |a| + |b|`. -/
theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])

/-- **`rpow` transfer of a linear bound.** If `0 ≤ v ≤ A · ε` with `1 ≤ A`, `0 ≤ ε` and `r ≤ 1`,
then `v ^ r ≤ A · ε ^ r`. This folds the multiplicative constant out of an `r`-power, converting
a base-distance bound `v ≤ A · ε` into the shape `A · ε ^ r` used throughout the seam gluing. -/
theorem rpow_le_mul_rpow {rr : ℝ≥0} (hrr1 : rr ≤ 1) {A ε v : ℝ} (hA : 1 ≤ A) (hv0 : 0 ≤ v)
    (hvA : v ≤ A * ε) (hε0 : 0 ≤ ε) : v ^ (rr : ℝ) ≤ A * ε ^ (rr : ℝ) := by
  calc v ^ (rr : ℝ) ≤ (A * ε) ^ (rr : ℝ) := Real.rpow_le_rpow hv0 hvA rr.coe_nonneg
    _ = A ^ (rr : ℝ) * ε ^ (rr : ℝ) := Real.mul_rpow (by linarith) hε0
    _ ≤ A * ε ^ (rr : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hA (by exact_mod_cast hrr1))
          (Real.rpow_nonneg hε0 _)

/-! ### The keystone: the ordered seam-gluing estimate -/

set_option maxHeartbeats 1600000 in -- long four-way case analysis
include hτ1 in
/-- **Ordered seam-gluing estimate (core of Lemma B).** For canonical representatives `(x, s)`,
`(y, t)` with `s ≤ t`, the transfer candidate `uCover` is embedding-Hölder:
`|uCover (x,s) − uCover (y,t)| ≤ 300 · (Cu + M + CF + 1) · ε ^ r`, where `ε = embDist [x,s] [y,t]`.
The proof splits on `ε`: for `ε ≥ 1/8` a crude oscillation bound suffices; for `ε < 1/8` the height
gap `hgt s t ≤ ε` forces a no-wrap (`|s−t| ≤ ε`) or a wrap (`(1−t)+s ≤ ε`) regime. No-wrap is closed
by the two Kuratowski recoveries (base distances `≤ Cε`) via a from-below (`t ≤ 7/8`) or from-above
(`t > 7/8`) representation; wrap uses `dist_map_le_embDist_wrap` and two small fibre integrals. -/
theorem holder_uCover_core (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0} (_hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (u₀ : X → ℝ) {Cu : ℝ} (hCu0 : 0 ≤ Cu)
    (hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ Cu * dist a b ^ (rr : ℝ))
    (hu₀ : ∀ a, inducedBaseCocycle T hτ F a = u₀ (T a) - u₀ a)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x y : X) {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) (hst : s ≤ t) :
    |uCover T hτ F u₀ (x, s) - uCover T hτ F u₀ (y, t)|
      ≤ 300 * (Cu + M + (CF : ℝ) + 1)
        * embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s))
          (suspensionMk T hτ (y, t)) ^ (rr : ℝ) := by
  set ε := embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t)) with hεdef
  have hε0 : 0 ≤ ε := embDist_nonneg T hτ hτ1 hdiam _ _
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM (suspensionMk T hτ (x, 0)))
  have hrr1' : (rr : ℝ) ≤ 1 := by exact_mod_cast hrr1
  have hεrnn : 0 ≤ ε ^ (rr : ℝ) := Real.rpow_nonneg hε0 _
  have hd0 : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hD0 : (0 : ℝ) ≤ dist (T x) (T y) := dist_nonneg
  have habs_ts : |s - t| = t - s := by rw [abs_of_nonpos (by linarith : s - t ≤ 0)]; ring
  have hucx : uCover T hτ F u₀ (x, s)
      = u₀ x + ∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)) := rfl
  have hucy : uCover T hτ F u₀ (y, t)
      = u₀ y + ∫ σ in (0 : ℝ)..t, F (suspensionMk T hτ (y, σ)) := rfl
  -- The final coefficient-domination step, shared by all branches.
  have hfin : ∀ c : ℝ, c ≤ 300 * (Cu + M + (CF : ℝ) + 1) →
      c * ε ^ (rr : ℝ) ≤ 300 * (Cu + M + (CF : ℝ) + 1) * ε ^ (rr : ℝ) :=
    fun c hc => mul_le_mul_of_nonneg_right hc hεrnn
  rcases le_or_gt (1 / 8 : ℝ) ε with hbig | hsmall
  · -- Crude oscillation bound for large ε.
    have hεr18 : (1 / 8 : ℝ) ≤ ε ^ (rr : ℝ) := by
      have h1 : (1 / 8 : ℝ) ≤ (1 / 8 : ℝ) ^ (rr : ℝ) :=
        Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) hrr1'
      have h2 : (1 / 8 : ℝ) ^ (rr : ℝ) ≤ ε ^ (rr : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hbig rr.coe_nonneg
      linarith
    have hcrude : |uCover T hτ F u₀ (x, s) - uCover T hτ F u₀ (y, t)| ≤ Cu + 2 * M := by
      rw [hucx, hucy]
      have hA : |u₀ x - u₀ y| ≤ Cu := by
        refine (hu₀hol x y).trans ?_
        have : dist x y ^ (rr : ℝ) ≤ 1 := Real.rpow_le_one hd0 (hdiam x y) rr.coe_nonneg
        nlinarith [hCu0]
      have hBx := abs_integral_fibre_le T hτ F hM x 0 s
      have hBy := abs_integral_fibre_le T hτ F hM y 0 t
      rw [abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - 0)] at hBx
      rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - 0)] at hBy
      have hs1 : M * (s - 0) ≤ M := by nlinarith [hs.2.le, hM0]
      have ht1 : M * (t - 0) ≤ M := by nlinarith [ht.2.le, hM0]
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
        _ ≤ Cu + 2 * M := by linarith
    refine hcrude.trans ?_
    have hstep : Cu + 2 * M ≤ (Cu + 2 * M) * (8 * ε ^ (rr : ℝ)) :=
      le_mul_of_one_le_right (by linarith) (by linarith [hεr18])
    have hstep2 : (Cu + 2 * M) * (8 * ε ^ (rr : ℝ)) = (8 * Cu + 16 * M) * ε ^ (rr : ℝ) := by ring
    refine hstep.trans (hstep2.le.trans ?_)
    exact hfin _ (by nlinarith [hCu0, hM0, CF.coe_nonneg])
  · -- Small ε: split on the height gap.
    have hε1 : ε ≤ 1 := by linarith
    have hεr : ε ≤ ε ^ (rr : ℝ) := Real.self_le_rpow_of_le_one hε0 hε1 hrr1'
    have hHGT : hgt s t ≤ ε := by
      have h := hgt_le_embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s)) (suspensionMk T hτ (y, t))
      rwa [suspensionRep_mk T hτ hτ1 x hs, suspensionRep_mk T hτ hτ1 y ht] at h
    have hmin : min |s - t| (1 - |s - t|) < 1 / 8 := lt_of_le_of_lt hHGT hsmall
    rcases min_lt_iff.mp hmin with hnw | hw
    · -- No-wrap: |s - t| ≤ ε.
      have habsε : t - s ≤ ε := by
        have : hgt s t = |s - t| := by
          rw [hgt, min_eq_left (by rw [habs_ts]; linarith [hnw, habs_ts])]
        rw [this, habs_ts] at hHGT; linarith
      -- Common-height Kuratowski parts, then the two recoveries.
      have hMμ : dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t)) ≤ 2 * ε := by
        have := dist_muFun_common_le T hτ hτ1 hdiam hs ht x y
        rw [habs_ts] at this; linarith
      have hMν : dist (nuFun T hdiam (x, t)) (nuFun T hdiam (y, t)) ≤ 3 * ε := by
        have := dist_nuFun_common_le T hτ hτ1 hdiam hs ht x y
        rw [habs_ts] at this; linarith
      have hμnn : (0 : ℝ) ≤ dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t)) := dist_nonneg
      have hrecD := embHeight_recover_map T hdiam ht.1 ht.2.le x y
      have hrecd := embHeight_recover_base T hdiam ht.1 ht.2.le x y
      have htD : t * dist (T x) (T y) ≤ 5 * ε := by
        have hp : (1 - t) * dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t))
            ≤ dist (muFun T hdiam (x, t)) (muFun T hdiam (y, t)) :=
          mul_le_of_le_one_left hμnn (by linarith [ht.1])
        linarith
      have htd : (1 - t) * dist x y ≤ 7 * ε := by linarith
      rcases le_or_gt t (7 / 8) with hlow | hhigh
      · -- From-below representation.
        have hd56 : dist x y ≤ 56 * ε := by
          have h18 : (1 : ℝ) / 8 ≤ 1 - t := by linarith
          nlinarith [htd, mul_le_mul_of_nonneg_right h18 hd0, hd0]
        have hHfb : ∀ σ, (0 : ℝ) ≤ σ → σ ≤ s → hlen T σ x y ≤ 61 * ε := by
          intro σ hσ0 hσs
          have hσt : σ ≤ t := le_trans hσs hst
          have h2 : σ * dist (T x) (T y) ≤ t * dist (T x) (T y) :=
            mul_le_mul_of_nonneg_right hσt hD0
          simp only [hlen]
          nlinarith [hd56, htD, h2, mul_nonneg hσ0 hd0]
        have hadd_y := intervalIntegral.integral_add_adjacent_intervals
          (hint y 0 s) (hint y s t)
        have hAle : |u₀ x - u₀ y| ≤ 56 * Cu * ε ^ (rr : ℝ) := by
          refine (hu₀hol x y).trans ?_
          have h2 := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 56) hd0 hd56 hε0
          calc Cu * dist x y ^ (rr : ℝ) ≤ Cu * (56 * ε ^ (rr : ℝ)) :=
                mul_le_mul_of_nonneg_left h2 hCu0
            _ = 56 * Cu * ε ^ (rr : ℝ) := by ring
        have hBle : |(∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            - ∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (y, σ))| ≤ (CF : ℝ) * 183 * ε ^ (rr : ℝ) := by
          refine (abs_integral_fibre_diff_le T hτ hτ1 hdiam F hF x y le_rfl hs.1
            hs.2.le hHfb hint).trans ?_
          have hpow := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 183)
            (by positivity) (by linarith : 3 * (61 * ε) ≤ 183 * ε) hε0
          have hfac : (0 : ℝ) ≤ (CF : ℝ) * (3 * (61 * ε)) ^ (rr : ℝ) := by positivity
          calc (CF : ℝ) * (3 * (61 * ε)) ^ (rr : ℝ) * (s - 0)
              ≤ (CF : ℝ) * (3 * (61 * ε)) ^ (rr : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left (by linarith [hs.2.le]) hfac
            _ = (CF : ℝ) * (3 * (61 * ε)) ^ (rr : ℝ) := mul_one _
            _ ≤ (CF : ℝ) * (183 * ε ^ (rr : ℝ)) := mul_le_mul_of_nonneg_left hpow CF.coe_nonneg
            _ = (CF : ℝ) * 183 * ε ^ (rr : ℝ) := by ring
        have hCle : |∫ σ in s..t, F (suspensionMk T hτ (y, σ))| ≤ M * ε ^ (rr : ℝ) := by
          refine (abs_integral_fibre_le T hτ F hM y s t).trans ?_
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)]
          calc M * (t - s) ≤ M * ε := mul_le_mul_of_nonneg_left habsε hM0
            _ ≤ M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr hM0
        rw [hucx, hucy, ← hadd_y]
        rw [show u₀ x + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
              - (u₀ y + ((∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (y, σ)))
                + ∫ σ in s..t, F (suspensionMk T hτ (y, σ))))
            = (u₀ x - u₀ y) + ((∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
                - ∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (y, σ)))
              - ∫ σ in s..t, F (suspensionMk T hτ (y, σ)) from by ring]
        refine le_trans ?_ (hfin (56 * Cu + (CF : ℝ) * 183 + M)
          (by nlinarith [hCu0, hM0, CF.coe_nonneg]))
        rw [add_mul, add_mul]
        refine (abs_sub_le_abs_add _ _).trans ?_
        have htri := abs_add_le (u₀ x - u₀ y)
          ((∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            - ∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (y, σ)))
        linarith [hAle, hBle, hCle, htri]
      · -- From-above representation.
        have hD6 : dist (T x) (T y) ≤ 6 * ε := by
          nlinarith [htD, mul_le_mul_of_nonneg_right (by linarith : (7 : ℝ) / 8 ≤ t) hD0, hε0]
        have hHfa : ∀ σ, t ≤ σ → σ ≤ 1 → hlen T σ x y ≤ 13 * ε := by
          intro σ hσt hσ1
          have h1 : (1 - σ) * dist x y ≤ (1 - t) * dist x y :=
            mul_le_mul_of_nonneg_right (by linarith) hd0
          have h2 : σ * dist (T x) (T y) ≤ dist (T x) (T y) :=
            mul_le_of_le_one_left hD0 hσ1
          simp only [hlen]
          nlinarith [htd, hD6, h1, h2]
        have hucax := uCover_fromAbove T hτ hτ1 F u₀ hu₀ hint x s
        have hucay := uCover_fromAbove T hτ hτ1 F u₀ hu₀ hint y t
        have hadd_x := intervalIntegral.integral_add_adjacent_intervals
          (hint x s t) (hint x t 1)
        have hAle : |u₀ (T x) - u₀ (T y)| ≤ 6 * Cu * ε ^ (rr : ℝ) := by
          refine (hu₀hol (T x) (T y)).trans ?_
          have h2 := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 6) hD0 hD6 hε0
          calc Cu * dist (T x) (T y) ^ (rr : ℝ) ≤ Cu * (6 * ε ^ (rr : ℝ)) :=
                mul_le_mul_of_nonneg_left h2 hCu0
            _ = 6 * Cu * ε ^ (rr : ℝ) := by ring
        have hBle : |(∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (x, σ)))
            - ∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (y, σ))| ≤ (CF : ℝ) * 39 * ε ^ (rr : ℝ) := by
          refine (abs_integral_fibre_diff_le T hτ hτ1 hdiam F hF x y ht.1 ht.2.le
            le_rfl hHfa hint).trans ?_
          have hpow := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 39)
            (by positivity) (by linarith : 3 * (13 * ε) ≤ 39 * ε) hε0
          have hfac : (0 : ℝ) ≤ (CF : ℝ) * (3 * (13 * ε)) ^ (rr : ℝ) := by positivity
          calc (CF : ℝ) * (3 * (13 * ε)) ^ (rr : ℝ) * (1 - t)
              ≤ (CF : ℝ) * (3 * (13 * ε)) ^ (rr : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left (by linarith [ht.1]) hfac
            _ = (CF : ℝ) * (3 * (13 * ε)) ^ (rr : ℝ) := mul_one _
            _ ≤ (CF : ℝ) * (39 * ε ^ (rr : ℝ)) := mul_le_mul_of_nonneg_left hpow CF.coe_nonneg
            _ = (CF : ℝ) * 39 * ε ^ (rr : ℝ) := by ring
        have hCle : |∫ σ in s..t, F (suspensionMk T hτ (x, σ))| ≤ M * ε ^ (rr : ℝ) := by
          refine (abs_integral_fibre_le T hτ F hM x s t).trans ?_
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)]
          calc M * (t - s) ≤ M * ε := mul_le_mul_of_nonneg_left habsε hM0
            _ ≤ M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr hM0
        rw [hucax, hucay, ← hadd_x]
        rw [show u₀ (T x) - ((∫ σ in s..t, F (suspensionMk T hτ (x, σ)))
                + ∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (x, σ)))
              - (u₀ (T y) - ∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (y, σ)))
            = (u₀ (T x) - u₀ (T y)) - (∫ σ in s..t, F (suspensionMk T hτ (x, σ)))
              - ((∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (x, σ)))
                - ∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (y, σ))) from by ring]
        refine le_trans ?_ (hfin (6 * Cu + (CF : ℝ) * 39 + M)
          (by nlinarith [hCu0, hM0, CF.coe_nonneg]))
        rw [add_mul, add_mul]
        refine (abs_sub_le_abs_add _ _).trans ?_
        have htri := abs_sub_le_abs_add (u₀ (T x) - u₀ (T y))
          (∫ σ in s..t, F (suspensionMk T hτ (x, σ)))
        linarith [hAle, hBle, hCle, htri]
    · -- Wrap regime: |s − t| ≥ 7/8, so (1 − t) + s ≤ ε.
      have hmin_eq : min |s - t| (1 - |s - t|) = 1 - |s - t| :=
        min_eq_right (by linarith [hw])
      have hsum : (1 - t) + s ≤ ε := by
        have h := hHGT
        simp only [hgt] at h
        rw [hmin_eq, habs_ts] at h; linarith
      have h1tnn : (0 : ℝ) ≤ 1 - t := by linarith [ht.2.le]
      have hs_ε : s ≤ ε := by linarith
      have h1t_ε : 1 - t ≤ ε := by linarith [hs.1]
      have hw2 : dist x (T y) ≤ 2 * ε := by
        have hwrapd := dist_map_le_embDist_wrap T hτ hτ1 hdiam ht hs y x
        rw [embDist_comm T hτ hτ1 hdiam (suspensionMk T hτ (y, t))
          (suspensionMk T hτ (x, s)), ← hεdef] at hwrapd
        rw [dist_comm x (T y)]; linarith
      have hucay := uCover_fromAbove T hτ hτ1 F u₀ hu₀ hint y t
      have hAle : |u₀ x - u₀ (T y)| ≤ 2 * Cu * ε ^ (rr : ℝ) := by
        refine (hu₀hol x (T y)).trans ?_
        have h2 := rpow_le_mul_rpow hrr1 (by norm_num : (1 : ℝ) ≤ 2) dist_nonneg hw2 hε0
        calc Cu * dist x (T y) ^ (rr : ℝ) ≤ Cu * (2 * ε ^ (rr : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 hCu0
          _ = 2 * Cu * ε ^ (rr : ℝ) := by ring
      have hBle : |∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ))| ≤ M * ε ^ (rr : ℝ) := by
        refine (abs_integral_fibre_le T hτ F hM x 0 s).trans ?_
        rw [abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - 0)]
        calc M * (s - 0) ≤ M * ε := mul_le_mul_of_nonneg_left (by linarith) hM0
          _ ≤ M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr hM0
      have hCle : |∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (y, σ))| ≤ M * ε ^ (rr : ℝ) := by
        refine (abs_integral_fibre_le T hτ F hM y t 1).trans ?_
        rw [abs_of_nonneg (by linarith [ht.2.le] : (0 : ℝ) ≤ 1 - t)]
        calc M * (1 - t) ≤ M * ε := mul_le_mul_of_nonneg_left h1t_ε hM0
          _ ≤ M * ε ^ (rr : ℝ) := mul_le_mul_of_nonneg_left hεr hM0
      rw [hucx, hucay]
      rw [show u₀ x + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            - (u₀ (T y) - ∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (y, σ)))
          = (u₀ x - u₀ (T y)) + (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
            + ∫ σ in t..(1 : ℝ), F (suspensionMk T hτ (y, σ)) from by ring]
      refine le_trans ?_ (hfin (2 * Cu + M + M) (by nlinarith [hCu0, hM0, CF.coe_nonneg]))
      rw [show (2 * Cu + M + M) * ε ^ (rr : ℝ)
          = 2 * Cu * ε ^ (rr : ℝ) + M * ε ^ (rr : ℝ) + M * ε ^ (rr : ℝ) from by ring]
      refine (abs_add_le _ _).trans ?_
      have htri := abs_add_le (u₀ x - u₀ (T y))
        (∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)))
      linarith [hAle, hBle, hCle, htri]

include hτ1 in
/-- **Unordered seam-gluing estimate.** The ordered core `holder_uCover_core` symmetrised: for any
canonical representatives, `|uCover (x,s) − uCover (y,t)| ≤ K · embDist [x,s] [y,t] ^ r`. -/
theorem holder_uCover_symm (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (u₀ : X → ℝ) {Cu : ℝ} (hCu0 : 0 ≤ Cu)
    (hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ Cu * dist a b ^ (rr : ℝ))
    (hu₀ : ∀ a, inducedBaseCocycle T hτ F a = u₀ (T a) - u₀ a)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x y : X) {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    |uCover T hτ F u₀ (x, s) - uCover T hτ F u₀ (y, t)|
      ≤ 300 * (Cu + M + (CF : ℝ) + 1)
        * embDist T hτ hτ1 hdiam (suspensionMk T hτ (x, s))
          (suspensionMk T hτ (y, t)) ^ (rr : ℝ) := by
  rcases le_total s t with hst | hts
  · exact holder_uCover_core T hτ hτ1 hdiam F hrr0 hrr1 hF hM u₀ hCu0 hu₀hol hu₀ hint x y hs ht hst
  · have h := holder_uCover_core T hτ hτ1 hdiam F hrr0 hrr1 hF hM u₀ hCu0 hu₀hol hu₀ hint
      y x ht hs hts
    rw [abs_sub_comm,
      embDist_comm T hτ hτ1 hdiam (suspensionMk T hτ (y, t)) (suspensionMk T hτ (x, s))] at h
    exact h

include hτ1 in
/-- **The keystone: the cross-seam Hölder gluing.** The descended transfer function `suspTransfer`
is embedding-Hölder: `|suspTransfer p − suspTransfer q| ≤ K · embDist p q ^ r`. Reducing `p, q` to
their canonical representatives (`suspTransfer_mk`) reduces this to the unordered gluing bound. -/
theorem holderWith_suspTransfer (hdiam : ∀ a b : X, dist a b ≤ 1) (F : SuspensionSpace T hτ → ℝ)
    {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M) (u₀ : X → ℝ) {Cu : ℝ} (hCu0 : 0 ≤ Cu)
    (hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ Cu * dist a b ^ (rr : ℝ))
    (hu₀ : ∀ a, inducedBaseCocycle T hτ F a = u₀ (T a) - u₀ a)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (hg : ∀ p, uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p)
    (p q : SuspensionSpace T hτ) :
    |suspTransfer T hτ F u₀ hg p - suspTransfer T hτ F u₀ hg q|
      ≤ 300 * (Cu + M + (CF : ℝ) + 1) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ) := by
  have hval : ∀ z, suspTransfer T hτ F u₀ hg z
      = uCover T hτ F u₀ (suspensionRep T hτ hτ1 z) := by
    intro z
    conv_lhs => rw [← suspensionMk_suspensionRep T hτ hτ1 z]
    rw [suspTransfer_mk]
  have hemb : embDist T hτ hτ1 hdiam p q
      = embDist T hτ hτ1 hdiam (suspensionMk T hτ (suspensionRep T hτ hτ1 p))
          (suspensionMk T hτ (suspensionRep T hτ hτ1 q)) := by
    rw [suspensionMk_suspensionRep, suspensionMk_suspensionRep]
  rw [hval p, hval q, hemb]
  exact holder_uCover_symm T hτ hτ1 hdiam F hrr0 hrr1 hF hM u₀ hCu0 hu₀hol hu₀ hint
    (suspensionRep T hτ hτ1 p).1 (suspensionRep T hτ hτ1 q).1
    (suspensionRep_mem_Ico T hτ hτ1 p) (suspensionRep_mem_Ico T hτ hτ1 q)

/-! ### Theorem C: the abstract Hölder flow-Livšic equivalence (constant roof `1`) -/

include hτ1 in
/-- **Hölder flow-Livšic equivalence for constant-roof suspension flows (issue #63, tiers 2 + 4).**
For a base map `T` that is a compact-system Hölder-Livšic map (continuous with continuous inverse,
`L`-Lipschitz, a dense orbit, and the summed exponential closing property), and an embedding-`r`-
Hölder, bounded flow observable `F`, the suspension flow observable `F` is a **Hölder flow
coboundary iff** every periodic Birkhoff sum of the induced base observable `inducedBaseCocycle F`
vanishes.

The forward direction is the tier-I obstruction (`inducedBaseCocycle_isCoboundary`). The converse
combines Lemma A (`holderWith_inducedBaseCocycle`: the induced observable is Hölder), the discrete
Hölder-Livšic converse with an exposed exponent (`exists_baseTransfer_holder`), and the keystone
cross-seam gluing (`holderWith_suspTransfer`), with the coboundary equation from
`suspTransfer_flow`. The metric statement is for roof `1`; a constant roof `c` normalises to `1` by
`suspensionRescale` at the measurable level. -/
theorem livsic_holderFlow_constRoof [CompactSpace X] (hdiam : ∀ a b : X, dist a b ≤ 1)
    (hT : Continuous ⇑T) {L : ℝ≥0} (hTL : LipschitzWith L ⇑T)
    (F : SuspensionSpace T hτ → ℝ) {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    {δ Kc : ℝ} (hδ : 0 < δ) (hKc : 0 ≤ Kc) (hclosing : ExpClosing (⇑T) (rr : ℝ) δ Kc)
    {x₀ : X} (hdense : DenseRange fun n : ℕ => (⇑T)^[n] x₀) :
    IsHolderFlowCoboundary T hτ hτ1 hdiam (suspensionFlowMap T hτ) F ↔
      HasVanishingPeriodicSums (⇑T) (inducedBaseCocycle T hτ F) := by
  constructor
  · intro h
    exact (inducedBaseCocycle_isCoboundary T hτ F
      h.isFlowCoboundary).hasVanishingPeriodicSums
  · intro hvps
    have hfhol := holderWith_inducedBaseCocycle T hτ hτ1 hdiam F hF hTL hint
    obtain ⟨Cu, u₀, hu₀hol', hu₀eq⟩ :=
      exists_baseTransfer_holder hT hrr0 hrr1 hfhol hδ hKc hclosing hvps hdense
    have hu₀hol : ∀ a b : X, |u₀ a - u₀ b| ≤ (Cu : ℝ) * dist a b ^ (rr : ℝ) := by
      intro a b
      have h := (hu₀hol'.holderOnWith Set.univ).dist_le (Set.mem_univ a) (Set.mem_univ b)
      rwa [Real.dist_eq] at h
    have hg : ∀ z, uCover T hτ F u₀ (suspensionGen T hτ z) = uCover T hτ F u₀ z := by
      rintro ⟨x, s⟩
      have hcx : τ x = 1 := congrFun hτ1 x
      have hgp : suspensionGen T hτ (x, s) = (T x, s - 1) := by rw [suspensionGen_apply, hcx]
      rw [hgp]
      exact uCover_gen T hτ F u₀ hu₀eq 1 hτ1 hint x s
    refine ⟨(300 * ((Cu : ℝ) + M + (CF : ℝ) + 1)).toNNReal, rr,
      suspTransfer T hτ F u₀ hg, hrr0, hrr1, fun p q => ?_,
      fun q t => suspTransfer_flow T hτ F u₀ hg hint q t⟩
    have hM0 : (0 : ℝ) ≤ M := (abs_nonneg _).trans (hM (suspensionMk T hτ (x₀, 0)))
    rw [Real.coe_toNNReal _ (by nlinarith [Cu.coe_nonneg, CF.coe_nonneg, hM0])]
    exact holderWith_suspTransfer T hτ hτ1 hdiam F hrr0 hrr1 hF hM u₀ Cu.coe_nonneg
      hu₀hol hu₀eq hint hg p q

include hτ1 in
/-- **Flow-native Hölder flow-Livšic equivalence.** Same hypotheses as `livsic_holderFlow_constRoof`
but with the obstruction phrased as the vanishing of every closed-orbit integral of `F`, obtained by
chaining through the lap-decomposition bridge `suspension_periodicOrbitIntegral_eq_birkhoffSum`. -/
theorem livsic_holderFlow_constRoof_orbitIntegral [CompactSpace X]
    (hdiam : ∀ a b : X, dist a b ≤ 1)
    (hT : Continuous ⇑T) {L : ℝ≥0} (hTL : LipschitzWith L ⇑T)
    (F : SuspensionSpace T hτ → ℝ) {CF rr : ℝ≥0} (hrr0 : 0 < rr) (hrr1 : rr ≤ 1)
    (hF : ∀ p q, |F p - F q| ≤ (CF : ℝ) * embDist T hτ hτ1 hdiam p q ^ (rr : ℝ))
    {M : ℝ} (hM : ∀ p, |F p| ≤ M)
    (hint : ∀ x a b, IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    {δ Kc : ℝ} (hδ : 0 < δ) (hKc : 0 ≤ Kc) (hclosing : ExpClosing (⇑T) (rr : ℝ) δ Kc)
    {x₀ : X} (hdense : DenseRange fun n : ℕ => (⇑T)^[n] x₀) :
    IsHolderFlowCoboundary T hτ hτ1 hdiam (suspensionFlowMap T hτ) F ↔
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
  exact (livsic_holderFlow_constRoof T hτ hτ1 hdiam hT hTL F hrr0 hrr1 hF hM hint
    hδ hKc hclosing hdense).trans hequiv

end

end ErgodicTheory
