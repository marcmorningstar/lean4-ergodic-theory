/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapToral
import ErgodicTheory.Ergodic.EigenvalueMixing
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Strong mixing of the Arnold cat map

This module proves that the genuine Arnold cat map `catTorus : 𝕋² → 𝕋²` (the hyperbolic toral
automorphism induced by `M = !![2,1;1,1]`, defined in `ErgodicTheory.Examples.CatMapToral`) is
**strongly mixing** for the Haar (`volume`) measure: for arbitrary measurable sets `A B`,

`volume.real (A ∩ catTorus^[k] ⁻¹' B) → volume.real A · volume.real B` as `k → ∞`.

## Strategy (Fourier / correlation decay)

The Koopman operator `U_k v = v ∘ catTorus^[k]` sends the character `mFourier n` to
`mFourier (Mᵏ ·ᵥ n)` (`mFourier_iterate_catTorus`).  The `L²` correlation
`Φ k u v = ⟪u, U_k v⟫` therefore *decorrelates exactly* on pairs of characters beyond a finite
shift: for `b ≠ 0` the index `Mᵏ ·ᵥ b` eventually escapes any fixed value
(`eventually_pow_mulVec_ne`, hyperbolicity), so orthonormality of the characters
(`integral_conj_mFourier_mul`) forces `Φ k (mFourier a) (mFourier b) = 0` eventually, matching the
product `(∫ conj (mFourier a)) · (∫ mFourier b) = 0`.  A finite-span approximation of arbitrary
`u v ∈ L²` (density of the character span, `span_mFourierLp_closure_eq_top`) together with the
Cauchy–Schwarz bound `‖Φ k u v‖ ≤ ‖u‖ ‖v‖` promotes this to

`Φ k u v → (∫ conj u) · (∫ v)`   (`tendsto_catCorr`),

the orthogonal projection onto the constants.  Feeding indicator functions gives the set-level
mixing statement.

## Main results

* `ErgodicTheory.CatMapToral.tendsto_catCorr` — `L²` correlation decay to the product of the means.
* `ErgodicTheory.CatMapToral.catTorus_mixing` — **strong mixing** of the Arnold cat map.
* `ErgodicTheory.CatMapToral.catTorus_eigenfunction_ae_zero_of_mixing` — spectral rigidity as a
  corollary of mixing (mixing has no nontrivial unimodular eigenvalues).

## References

* P. Walters, *An Introduction to Ergodic Theory*, Theorem 1.30 and §1.7 (mixing implies ergodicity
  and has no nontrivial eigenvalues).
* M. Einsiedler, T. Ward, *Ergodic Theory with a View Towards Number Theory*, Theorem 2.20
  (hyperbolic toral automorphisms are mixing via Fourier analysis).
-/

open MeasureTheory UnitAddTorus Matrix Filter Topology
open scoped ComplexConjugate InnerProductSpace

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching
`ErgodicTheory.Examples.CatMapToral`: with this `MeasureSpace` instance, `volume` on
`UnitAddTorus (Fin 2)` is the product Haar probability measure on `𝕋²`, the basis used by the
Fourier API. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catMixingB :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catMixingB :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catMixingB :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-! ## The Koopman action on characters under iteration -/

/-- **Iterated Koopman / character relation.**  Composing a character with the `k`-fold iterate of
the cat-map automorphism gives the character at the `k`-th matrix power of the index:
`mFourier n (catTorus^[k] y) = mFourier (Mᵏ ·ᵥ n) y`. -/
theorem mFourier_iterate_catTorus (k : ℕ) (n : Fin 2 → ℤ) (y : T2) :
    mFourier n (catTorus^[k] y) = mFourier (catℤ ^ k *ᵥ n) y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (catTorus y), mFourier_catTorus, vecMul_catℤ,
      mulVec_mulVec, ← pow_succ']

/-- **Escape of the index orbit.**  For a nonzero integer vector `m`, the forward orbit
`k ↦ Mᵏ ·ᵥ m` eventually avoids any fixed value `n`.  (The orbit is injective by
`orbit_injective`, so the preimage of `{n}` is finite.) -/
theorem eventually_pow_mulVec_ne {m : Fin 2 → ℤ} (hm : m ≠ 0) (n : Fin 2 → ℤ) :
    ∀ᶠ k in Filter.atTop, catℤ ^ k *ᵥ m ≠ n := by
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite]
  have hset : {k : ℕ | ¬ catℤ ^ k *ᵥ m ≠ n} = (fun k : ℕ => catℤ ^ k *ᵥ m) ⁻¹' {n} := by
    ext k; simp only [Set.mem_setOf_eq, not_not, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hset]
  exact Set.Finite.preimage (orbit_injective hm).injOn (Set.finite_singleton n)

/-! ## Orthonormality of the characters as an integral identity -/

/-- **Character orthogonality.**  The integral of the product of a conjugated character and a
character is `1` on the diagonal and `0` off it.  This is the orthonormality of the `L²` monomials
`mFourierLp 2` transported to a pointwise integral. -/
theorem integral_conj_mFourier_mul (a b : Fin 2 → ℤ) :
    ∫ t : T2, (starRingEnd ℂ) (mFourier a t) * mFourier b t = if a = b then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin 2))) a b
  rw [MeasureTheory.L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mFourierLp 2 a, coeFn_mFourierLp 2 b] with t ha hb
  rw [RCLike.inner_apply, ha, hb]
  ring

/-- **Mean of a character.**  The integral of a character is `1` at the trivial index and `0`
otherwise (a special case of `integral_conj_mFourier_mul` at `a = 0`). -/
theorem integral_mFourier (a : Fin 2 → ℤ) :
    ∫ t : T2, mFourier a t = if a = 0 then 1 else 0 := by
  have h := integral_conj_mFourier_mul (0 : Fin 2 → ℤ) a
  have heq : ∀ t : T2, (starRingEnd ℂ) (mFourier (0 : Fin 2 → ℤ) t) * mFourier a t
      = mFourier a t := by
    intro t; rw [mFourier_zero_apply]; simp
  simp_rw [heq] at h
  rw [h]
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha, if_neg (fun h : (0 : Fin 2 → ℤ) = a => ha h.symm)]

/-- The inner product of the constant monomial with a character: `1` at the trivial index, `0`
otherwise (orthonormality of `mFourierLp 2`). -/
theorem inner_mFourierLp0 (a : Fin 2 → ℤ) :
    ⟪mFourierLp 2 (0 : Fin 2 → ℤ), mFourierLp 2 a⟫_ℂ = if (0 : Fin 2 → ℤ) = a then 1 else 0 :=
  (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin 2))) 0 a

/-- The constant monomial `mFourierLp 2 0` is a unit vector. -/
theorem norm_mFourierLp0 : ‖mFourierLp (d := Fin 2) 2 (0 : Fin 2 → ℤ)‖ = 1 :=
  (orthonormal_mFourier (d := Fin 2)).norm_eq_one 0

/-! ## The integral as an inner product with the constant -/

/-- The integral of an `L²` function is its inner product with the constant monomial
`mFourierLp 2 0` (which represents the constant function `1`). -/
theorem integral_eq_inner_mFourierLp0 (u : Lp ℂ 2 (volume : Measure T2)) :
    (∫ t : T2, (u : T2 → ℂ) t) = ⟪mFourierLp 2 (0 : Fin 2 → ℤ), u⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mFourierLp 2 (0 : Fin 2 → ℤ)] with t ht
  rw [RCLike.inner_apply, ht, mFourier_zero_apply]
  simp

/-- Cauchy–Schwarz bound for the constant projection: `‖∫ u‖ ≤ ‖u‖` (probability space). -/
theorem norm_inner_mFourierLp0_le (u : Lp ℂ 2 (volume : Measure T2)) :
    ‖⟪mFourierLp 2 (0 : Fin 2 → ℤ), u⟫_ℂ‖ ≤ ‖u‖ :=
  (norm_inner_le_norm _ _).trans_eq (by rw [norm_mFourierLp0, one_mul])

/-! ## The `L²` correlation functional -/

/-- The `L²`-normalised Koopman operator of the `k`-th iterate of `catTorus`, packaged as a linear
isometry `L²(𝕋²) → L²(𝕋²)`. -/
def catComp (k : ℕ) : Lp ℂ 2 (volume : Measure T2) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure T2) :=
  Lp.compMeasurePreservingₗᵢ ℂ (catTorus^[k]) (measurePreserving_catTorus.iterate k)

/-- The correlation `Φ k u v = ⟪u, U_k v⟫` of `u` with the iterated Koopman image of `v`. -/
def catCorr (k : ℕ) (u v : Lp ℂ 2 (volume : Measure T2)) : ℂ := ⟪u, catComp k v⟫_ℂ

/-- The pointwise value of `catComp k v` is `v ∘ catTorus^[k]` almost everywhere. -/
theorem coeFn_catComp (k : ℕ) (v : Lp ℂ 2 (volume : Measure T2)) :
    (catComp k v : T2 → ℂ) =ᵐ[volume] (v : T2 → ℂ) ∘ (catTorus^[k]) :=
  Lp.coeFn_compMeasurePreserving v (measurePreserving_catTorus.iterate k)

/-- The correlation of two characters: `Φ k (mFourier a) (mFourier b) = 1` iff `a = Mᵏ ·ᵥ b`. -/
theorem catCorr_basis (k : ℕ) (a b : Fin 2 → ℤ) :
    catCorr k (mFourierLp 2 a) (mFourierLp 2 b) = if a = catℤ ^ k *ᵥ b then 1 else 0 := by
  have hmp := measurePreserving_catTorus.iterate k
  have hb_shift : (fun t => (mFourierLp (d := Fin 2) 2 b) (catTorus^[k] t))
      =ᵐ[volume] (fun t => mFourier b (catTorus^[k] t)) :=
    (coeFn_mFourierLp 2 b).comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
  simp only [catCorr, MeasureTheory.L2.inner_def]
  rw [← integral_conj_mFourier_mul a (catℤ ^ k *ᵥ b)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_catComp k (mFourierLp 2 b), coeFn_mFourierLp 2 a, hb_shift]
    with t hcomp ha hbs
  rw [RCLike.inner_apply, ha, hcomp, Function.comp_apply, hbs, mFourier_iterate_catTorus]
  ring

/-- **Eventual pairwise decorrelation.**  For each pair of characters the correlation `Φ k` is
eventually equal to the product of their means (in inner-product form).  For `b ≠ 0` this holds
because `Mᵏ ·ᵥ b` eventually escapes `a`; for `b = 0` it is exact for all `k`. -/
theorem catCorr_basis_eventually (a b : Fin 2 → ℤ) :
    ∀ᶠ k in atTop, catCorr k (mFourierLp 2 a) (mFourierLp 2 b)
      = (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), mFourierLp 2 a⟫_ℂ)
          * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), mFourierLp 2 b⟫_ℂ := by
  rw [inner_mFourierLp0, inner_mFourierLp0]
  by_cases hb : b = 0
  · refine Filter.Eventually.of_forall (fun k => ?_)
    rw [catCorr_basis, hb, mulVec_zero]
    rcases eq_or_ne a 0 with ha | ha
    · subst ha; simp
    · rw [if_neg ha, if_neg (fun h : (0 : Fin 2 → ℤ) = a => ha h.symm)]; simp
  · filter_upwards [eventually_pow_mulVec_ne hb a] with k hk
    rw [catCorr_basis, if_neg (fun h => hk h.symm),
      if_neg (fun h : (0 : Fin 2 → ℤ) = b => hb h.symm), mul_zero]

/-! ## Bilinear expansion over finite character sums -/

/-- Sesquilinear expansion of the correlation over finite character sums. -/
theorem catCorr_sum_eq (k : ℕ) (s t : Finset (Fin 2 → ℤ)) (c d : (Fin 2 → ℤ) → ℂ) :
    catCorr k (∑ a ∈ s, c a • mFourierLp 2 a) (∑ b ∈ t, d b • mFourierLp 2 b)
      = ∑ b ∈ t, d b * ∑ a ∈ s,
          (starRingEnd ℂ) (c a) * catCorr k (mFourierLp 2 a) (mFourierLp 2 b) := by
  simp only [catCorr]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, inner_smul_right]
  congr 1
  rw [sum_inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inner_smul_left]

/-- Sesquilinear expansion of the constant-projection product over finite character sums, matching
the shape of `catCorr_sum_eq`. -/
theorem target_sum_eq (s t : Finset (Fin 2 → ℤ)) (c d : (Fin 2 → ℤ) → ℂ) :
    (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), ∑ a ∈ s, c a • mFourierLp 2 a⟫_ℂ)
        * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), ∑ b ∈ t, d b • mFourierLp 2 b⟫_ℂ
      = ∑ b ∈ t, d b * ∑ a ∈ s, (starRingEnd ℂ) (c a)
          * ((starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), mFourierLp 2 a⟫_ℂ)
              * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), mFourierLp 2 b⟫_ℂ) := by
  rw [inner_sum, map_sum, inner_sum]
  simp only [inner_smul_right, map_mul]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ## Finite-span approximation -/

/-- Every `L²` function is approximated in norm by a finite linear combination of characters (the
character span is dense in `L²`). -/
theorem exists_span_approx (u : Lp ℂ 2 (volume : Measure T2)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ),
      ‖u - ∑ a ∈ s, c a • mFourierLp 2 a‖ < ε := by
  have hmem : u ∈ (Submodule.span ℂ
      (Set.range (mFourierLp (d := Fin 2) 2))).topologicalClosure := by
    rw [span_mFourierLp_closure_eq_top (by simp)]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨w, hw_mem, hw_dist⟩ := hmem ε hε
  rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at hw_mem
  obtain ⟨cf, hcf⟩ := hw_mem
  refine ⟨cf.support, cf, ?_⟩
  rw [Finsupp.sum] at hcf
  rw [dist_eq_norm, ← hcf] at hw_dist
  exact hw_dist

/-! ## The correlation-decay keystone -/

set_option maxHeartbeats 1600000 in
-- the density argument assembles the limit from the character case, whose Parseval bookkeeping (a
-- finite double sum over two character supports) elaborates past the default heartbeat budget.
/-- **`L²` correlation decay.**  For arbitrary `u v ∈ L²(𝕋²)`, the correlation `Φ k u v` converges
to the product of the means `(∫ conj u) · (∫ v)` (the orthogonal projection onto the constants).

Characters decorrelate exactly beyond a finite shift (`catCorr_basis_eventually`); the
Cauchy–Schwarz bound `‖Φ k u v‖ ≤ ‖u‖ ‖v‖` and density of the character span promote this to `L²`
functions by a triangle-inequality approximation. -/
theorem tendsto_catCorr (u v : Lp ℂ 2 (volume : Measure T2)) :
    Tendsto (fun k => catCorr k u v) atTop
      (𝓝 ((∫ t : T2, (starRingEnd ℂ) ((u : T2 → ℂ) t)) * (∫ t : T2, (v : T2 → ℂ) t))) := by
  rw [integral_conj, integral_eq_inner_mFourierLp0, integral_eq_inner_mFourierLp0]
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Approximation radius `η`, small relative to the norms of `u` and `v`.
  set M : ℝ := ‖u‖ + ‖v‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  set η : ℝ := min 1 (ε / (3 * M)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηM : η * M ≤ ε / 3 := by
    have h1 : η ≤ ε / (3 * M) := min_le_right _ _
    calc η * M ≤ (ε / (3 * M)) * M := by gcongr
      _ = ε / 3 := by field_simp
  -- Finite-span approximants.
  obtain ⟨s, c, hu'⟩ := exists_span_approx u hη0
  obtain ⟨tt, d, hv'⟩ := exists_span_approx v hη0
  set u' : Lp ℂ 2 (volume : Measure T2) := ∑ a ∈ s, c a • mFourierLp 2 a with hu'def
  set v' : Lp ℂ 2 (volume : Measure T2) := ∑ b ∈ tt, d b • mFourierLp 2 b with hv'def
  -- Correlation difference bound (bilinearity + Cauchy–Schwarz + isometry).
  have hcatCorrbound : ∀ k,
      ‖catCorr k u v - catCorr k u' v'‖ ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ := by
    intro k
    have e : catCorr k u v - catCorr k u' v'
        = ⟪u - u', catComp k v⟫_ℂ + ⟪u', catComp k (v - v')⟫_ℂ := by
      simp only [catCorr, map_sub, inner_sub_left, inner_sub_right]; ring
    have h1 : ‖⟪u - u', catComp k v⟫_ℂ‖ ≤ ‖u - u'‖ * ‖v‖ :=
      (norm_inner_le_norm _ _).trans_eq (by rw [LinearIsometry.norm_map])
    have h2 : ‖⟪u', catComp k (v - v')⟫_ℂ‖ ≤ ‖u'‖ * ‖v - v'‖ :=
      (norm_inner_le_norm _ _).trans_eq (by rw [LinearIsometry.norm_map])
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  -- Constant-projection difference bound.
  have hBbound : ‖(starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u⟫_ℂ)
        * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v⟫_ℂ
      - (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u'⟫_ℂ)
        * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v'⟫_ℂ‖
      ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ := by
    have e : (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u⟫_ℂ)
          * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v⟫_ℂ
        - (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u'⟫_ℂ)
          * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v'⟫_ℂ
        = (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u - u'⟫_ℂ)
            * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v⟫_ℂ
          + (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u'⟫_ℂ)
            * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v - v'⟫_ℂ := by
      simp only [inner_sub_right, map_sub]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (norm_inner_mFourierLp0_le _) (norm_inner_mFourierLp0_le _)
        (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (norm_inner_mFourierLp0_le _) (norm_inner_mFourierLp0_le _)
        (norm_nonneg _) (norm_nonneg _)
  -- Middle term: exact eventual equality of the approximants' correlation and projection.
  have hev : ∀ᶠ k in atTop, catCorr k u' v'
      = (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u'⟫_ℂ)
          * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v'⟫_ℂ := by
    have hall : ∀ᶠ k in atTop, ∀ a ∈ (s : Set (Fin 2 → ℤ)), ∀ b ∈ (tt : Set (Fin 2 → ℤ)),
        catCorr k (mFourierLp 2 a) (mFourierLp 2 b)
          = (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), mFourierLp 2 a⟫_ℂ)
              * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), mFourierLp 2 b⟫_ℂ := by
      rw [eventually_all_finite s.finite_toSet]
      intro a _
      rw [eventually_all_finite tt.finite_toSet]
      intro b _
      exact catCorr_basis_eventually a b
    filter_upwards [hall] with k hk
    rw [hu'def, hv'def, catCorr_sum_eq, target_sum_eq]
    refine Finset.sum_congr rfl fun b hb => ?_
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hk a (Finset.mem_coe.mpr ha) b (Finset.mem_coe.mpr hb)]
  -- Abbreviate the error budget `P` and the two constant projections `B`, `B'`.
  set P : ℝ := ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ with hPdef
  set B : ℂ := (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u⟫_ℂ)
    * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v⟫_ℂ with hBdef
  set B' : ℂ := (starRingEnd ℂ) (⟪mFourierLp 2 (0 : Fin 2 → ℤ), u'⟫_ℂ)
    * ⟪mFourierLp 2 (0 : Fin 2 → ℤ), v'⟫_ℂ with hB'def
  -- Norm-approximation facts.
  have ha : ‖u - u'‖ < η := hu'
  have hb : ‖v - v'‖ < η := hv'
  have hu'norm : ‖u'‖ ≤ ‖u‖ + η := by
    calc ‖u'‖ = ‖u - (u - u')‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - u'‖ := norm_sub_le _ _
      _ ≤ ‖u‖ + η := by linarith [ha.le]
  have hchain : P ≤ η * M := by
    rw [hPdef]
    have t1 : ‖u - u'‖ * ‖v‖ ≤ η * ‖v‖ := mul_le_mul_of_nonneg_right ha.le (norm_nonneg _)
    have t2 : ‖u'‖ * ‖v - v'‖ ≤ (‖u‖ + 1) * η := by
      refine mul_le_mul ?_ hb.le (norm_nonneg _) (by positivity)
      linarith [hu'norm, hη1]
    have hsum : η * ‖v‖ + (‖u‖ + 1) * η = η * M := by rw [hM]; ring
    linarith [t1, t2, hsum]
  -- Assemble the triangle inequality.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun k hk => ?_⟩
  have hkeq := hN k hk
  rw [dist_eq_norm]
  have hb2 : ‖catCorr k u' v' - B‖ ≤ P := by rw [hkeq, norm_sub_rev]; exact hBbound
  calc ‖catCorr k u v - B‖
      = ‖(catCorr k u v - catCorr k u' v') + (catCorr k u' v' - B)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖catCorr k u v - catCorr k u' v'‖ + ‖catCorr k u' v' - B‖ := norm_add_le _ _
    _ ≤ P + P := add_le_add (hcatCorrbound k) hb2
    _ < ε := by linarith [hchain, hηM]

/-! ## Strong mixing -/

/-- **Strong mixing of the Arnold cat map (GitHub issue #54).**  For arbitrary measurable sets
`A B`, the set correlation `volume.real (A ∩ catTorus^[k] ⁻¹' B)` converges to the product
`volume.real A · volume.real B`.

The indicator functions of `A` and `B` sit in `L²`; feeding them to the correlation-decay keystone
`tendsto_catCorr` and identifying `Φ k` with the set correlation and the limit with the measure
product gives the statement (Walters Thm 1.30; Einsiedler–Ward Thm 2.20). -/
theorem catTorus_mixing (A B : Set T2) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto (fun k => (volume : Measure T2).real (A ∩ catTorus^[k] ⁻¹' B))
      Filter.atTop (𝓝 ((volume : Measure T2).real A * (volume : Measure T2).real B)) := by
  set u : Lp ℂ 2 (volume : Measure T2) := indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ)
    with hu
  set v : Lp ℂ 2 (volume : Measure T2) := indicatorConstLp 2 hB (measure_ne_top _ _) (1 : ℂ)
    with hv
  have hcatCorr := tendsto_catCorr u v
  -- The mean integrals of the indicators are the real measures.
  have integral_u : (∫ t : T2, (u : T2 → ℂ) t) = ((volume : Measure T2).real A : ℂ) := by
    rw [hu, integral_congr_ae indicatorConstLp_coeFn, integral_indicator_const (1 : ℂ) hA,
      Complex.real_smul, mul_one]
  have integral_v : (∫ t : T2, (v : T2 → ℂ) t) = ((volume : Measure T2).real B : ℂ) := by
    rw [hv, integral_congr_ae indicatorConstLp_coeFn, integral_indicator_const (1 : ℂ) hB,
      Complex.real_smul, mul_one]
  have hIu : (∫ t : T2, (starRingEnd ℂ) ((u : T2 → ℂ) t)) = ((volume : Measure T2).real A : ℂ) := by
    rw [integral_conj, integral_u, Complex.conj_ofReal]
  have hlim : (∫ t : T2, (starRingEnd ℂ) ((u : T2 → ℂ) t)) * (∫ t : T2, (v : T2 → ℂ) t)
      = (((volume : Measure T2).real A * (volume : Measure T2).real B : ℝ) : ℂ) := by
    rw [hIu, integral_v]; push_cast; ring
  -- Identify the correlation with the set correlation.
  have hval : ∀ k,
      catCorr k u v = (((volume : Measure T2).real (A ∩ catTorus^[k] ⁻¹' B) : ℝ) : ℂ) := by
    intro k
    have hmp := measurePreserving_catTorus.iterate k
    have hv_shift : (fun t => (v : T2 → ℂ) (catTorus^[k] t))
        =ᵐ[volume] (fun t => (B.indicator (fun _ => (1 : ℂ))) (catTorus^[k] t)) := by
      rw [hv]; exact indicatorConstLp_coeFn.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
    have hu_ind : (u : T2 → ℂ) =ᵐ[volume] A.indicator (fun _ => (1 : ℂ)) := by
      rw [hu]; exact indicatorConstLp_coeFn
    have key : catCorr k u v
        = ∫ t : T2, ((A ∩ catTorus^[k] ⁻¹' B).indicator (fun _ => (1 : ℂ))) t := by
      simp only [catCorr, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_catComp k v, hu_ind, hv_shift] with t hcv hui hvs
      rw [RCLike.inner_apply, hcv, Function.comp_apply, hvs, hui]
      by_cases hAt : t ∈ A <;> by_cases hBt : catTorus^[k] t ∈ B <;>
        simp [Set.mem_inter_iff, Set.mem_preimage, hAt, hBt]
    rw [key, integral_indicator_const (1 : ℂ) (hA.inter (hB.preimage hmp.measurable)),
      Complex.real_smul, mul_one]
  rw [hlim] at hcatCorr
  simp only [hval] at hcatCorr
  have hre := (Complex.continuous_re.tendsto _).comp hcatCorr
  simpa only [Function.comp_def, Complex.ofReal_re] using hre

/-! ## Spectral rigidity as a corollary -/

/-- **Mixing kills eigenvalues (corollary).**  A measurable eigenfunction `g` of `catTorus` with a
unimodular eigenvalue `l ≠ 1` vanishes almost everywhere.  This re-derives the spectral rigidity of
`CatMapEigenfunction` from strong mixing (`catTorus_mixing`) via the abstract
`eigenfunction_ae_zero_of_mixing`. -/
theorem catTorus_eigenfunction_ae_zero_of_mixing {g : T2 → ℂ} {l : ℂ}
    (hg : Measurable g) (heig : ∀ x, g (catTorus x) = l * g x)
    (hl : ‖l‖ = 1) (hl1 : l ≠ 1) : g =ᵐ[volume] 0 :=
  eigenfunction_ae_zero_of_mixing
    (fun _ hAB => catTorus_mixing _ _ hAB hAB)
    continuous_catTorus.measurable hg heig hl hl1

end ErgodicTheory.CatMapToral
