/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapToral
import Mathlib.Dynamics.Ergodic.Function

/-!
# Eigenfunctions of the Arnold cat map are trivial

This module proves the **spectral rigidity** of the genuine Arnold cat map
`catTorus : 𝕋² → 𝕋²` (the hyperbolic toral automorphism induced by `M = !![2,1;1,1]`, defined in
`ErgodicTheory.Examples.CatMapToral`): the map has **no nontrivial unimodular eigenfunctions**.
Concretely, a measurable `g : 𝕋² → ℂ` satisfying the eigen-equation `g ∘ catTorus = l · g` with a
unimodular eigenvalue `l ≠ 1` must vanish almost everywhere.

This is **GitHub issue #47**. It supplies exactly the spectral input (`hspec`) that the abstract
time-`1` ergodicity theorem `ErgodicTheory.ergodic_suspensionFlowMap_one_const_roof` requires,
mirroring the Bernoulli-shift case handled by `eigenfunction_ae_zero_of_mixing`.

## Strategy (Fourier collapse)

The argument is the eigenfunction analogue of the invariant-function Fourier collapse used to prove
`ergodic_catTorus`:

* **Boundedness.** `‖l‖ = 1` makes `‖g‖` `catTorus`-invariant, so ergodicity forces `‖g‖` to be
  a.e. a constant `c`; hence `g` is a.e. bounded and lies in `L²`.  Let `F` be its `L²`
  representative, so the eigen-equation transports to `(F : 𝕋² → ℂ) ∘ catTorus =ᵐ l • F`.
* **Coefficient twist.** Changing variables through the measure-preserving `catTorus` shows each
  Fourier coefficient transforms as `mFourierCoeff F (n ᵥ* M) = l⁻¹ • mFourierCoeff F n`
  (`mFourierCoeff_vecMul_of_eigen`).
* **Off-origin vanishing.** Since `‖l⁻¹‖ = 1`, the coefficient norm is *constant* along the infinite
  index orbit `{Mᵖ ·ᵥ n}` (`n ≠ 0`); square-summability forces it to `0`
  (`mFourierCoeff_eq_zero_of_eigen`).
* **Zero mode.** At `n = 0` the twist reads `c₀ = l⁻¹ c₀`, and `l⁻¹ ≠ 1` forces `c₀ = 0`.
* **Collapse.** All Fourier coefficients vanish, so `F = 0` in `L²` and `g =ᵐ 0`.

Unlike the Bernoulli case there is no case split on a surviving constant: the Fourier argument kills
*every* mode, the constant mode included.

## Main results

* `ErgodicTheory.CatMapToral.catTorus_eigenfunction_ae_zero` — the headline: a measurable
  eigenfunction with a unimodular eigenvalue `≠ 1` vanishes a.e.
-/

open MeasureTheory UnitAddTorus Matrix

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching
`ErgodicTheory.Examples.CatMapToral`: with this `MeasureSpace` instance, `volume` on
`UnitAddTorus (Fin 2)` is the product Haar probability measure on `𝕋²`, the basis used by the
Fourier API. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catEigen :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catEigen :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catEigen :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- **Eigen-twist of the Fourier coefficients.**  If `F ∘ catTorus =ᵐ l • F` for a nonzero `l`, then
composing the character `mFourier (-n)` with `catTorus`, substituting `F = l⁻¹ • (F ∘ catTorus)`
a.e., and changing variables (measure preservation) shows the coefficient transforms as
`mFourierCoeff F (n ᵥ* M) = l⁻¹ • mFourierCoeff F n`.  (Eigen analogue of
`mFourierCoeff_vecMul_of_invariant`.) -/
theorem mFourierCoeff_vecMul_of_eigen {F : T2 → ℂ} {l : ℂ} (hl0 : l ≠ 0)
    (hF : F ∘ catTorus =ᵐ[volume] l • F) (n : Fin 2 → ℤ) :
    mFourierCoeff F (Matrix.vecMul n catℤ) = l⁻¹ • mFourierCoeff F n := by
  have hchar : (mFourier (-(Matrix.vecMul n catℤ)) : T2 → ℂ)
      = (mFourier (-n)) ∘ catTorus := by
    rw [← Matrix.neg_vecMul]; exact mFourier_vecMul_eq_comp (-n)
  -- From the eigen-relation: a.e. `F t = l⁻¹ * F (catTorus t)`.
  have hFinv : ∀ᵐ t ∂(volume : Measure T2), F t = l⁻¹ * F (catTorus t) := by
    filter_upwards [hF] with t ht
    have h1 : F (catTorus t) = l * F t := by
      simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using ht
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
  rw [mFourierCoeff, mFourierCoeff]
  calc ∫ t, mFourier (-(Matrix.vecMul n catℤ)) t • F t
      = ∫ t, (mFourier (-n)) (catTorus t) • (l⁻¹ * F (catTorus t)) := by
        refine integral_congr_ae ?_
        filter_upwards [hFinv] with t ht
        have hc : mFourier (-(Matrix.vecMul n catℤ)) t = (mFourier (-n)) (catTorus t) :=
          congrFun hchar t
        rw [hc, ht]
    _ = ∫ t, l⁻¹ • ((mFourier (-n)) (catTorus t) • F (catTorus t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [smul_eq_mul]; ring
    _ = l⁻¹ • ∫ t, (mFourier (-n)) (catTorus t) • F (catTorus t) := by rw [integral_smul]
    _ = l⁻¹ • ∫ s, (mFourier (-n)) s • F s := by
        refine congrArg (l⁻¹ • ·) ?_
        exact measurePreserving_catTorusEquiv.integral_comp' (fun s => (mFourier (-n)) s • F s)

/-- A complex sequence with **constant norm on an infinite set** and **square-summable** vanishes on
that set.  (Square-summability forces `‖·‖² → 0` cofinitely, but a nonzero constant norm on an
infinite set never does.)  Norm variant of `eq_zero_of_constant_on_infinite_of_summable`. -/
theorem eq_zero_of_constNorm_on_infinite_of_summable {ι : Type*} {c : ι → ℂ} {S : Set ι} {v : ℂ}
    (hS : S.Infinite) (hconst : ∀ i ∈ S, ‖c i‖ = ‖v‖)
    (hsum : Summable fun i => ‖c i‖ ^ 2) : v = 0 := by
  by_contra hv
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by
    have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  have htends : Filter.Tendsto (fun i => ‖c i‖ ^ 2) Filter.cofinite (nhds 0) :=
    hsum.tendsto_cofinite_zero
  have hev : ∀ᶠ i in Filter.cofinite, ‖c i‖ ^ 2 < ‖v‖ ^ 2 :=
    htends.eventually (eventually_lt_nhds hpos)
  have hfin : {i | ‖c i‖ ^ 2 < ‖v‖ ^ 2}ᶜ.Finite :=
    Filter.eventually_cofinite.mp hev
  refine hS (hfin.subset fun i hi => ?_)
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, hconst i hi, le_refl]

/-- **Off-origin Fourier coefficients of an `L²` eigenfunction vanish.**  If `(F : 𝕋² → ℂ)` obeys
`F ∘ catTorus =ᵐ l • F` with `‖l‖ = 1`, `l ≠ 0`, then `mFourierCoeff F n = 0` for every nonzero `n`.
The coefficient *norm* is constant along the infinite index orbit (`‖l⁻¹‖ = 1`) and the family is
square-summable, so `eq_zero_of_constNorm_on_infinite_of_summable` applies. -/
theorem mFourierCoeff_eq_zero_of_eigen {F : Lp ℂ 2 (volume : Measure T2)} {l : ℂ} (hl0 : l ≠ 0)
    (hl : ‖l‖ = 1) (hF : (F : T2 → ℂ) ∘ catTorus =ᵐ[volume] l • (F : T2 → ℂ)) {n : Fin 2 → ℤ}
    (hn : n ≠ 0) : mFourierCoeff (F : T2 → ℂ) n = 0 := by
  have hnorm_inv : ‖l⁻¹‖ = 1 := by rw [norm_inv, hl, inv_one]
  have hstep : ∀ m : Fin 2 → ℤ,
      ‖mFourierCoeff (F : T2 → ℂ) (Matrix.vecMul m catℤ)‖ = ‖mFourierCoeff (F : T2 → ℂ) m‖ := by
    intro m
    rw [mFourierCoeff_vecMul_of_eigen hl0 hF m, norm_smul, hnorm_inv, one_mul]
  have hconst : ∀ p : ℕ,
      ‖mFourierCoeff (F : T2 → ℂ) ((fun m => Matrix.vecMul m catℤ)^[p] n)‖
        = ‖mFourierCoeff (F : T2 → ℂ) n‖ := by
    intro p
    induction p with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', hstep, ih]
  refine eq_zero_of_constNorm_on_infinite_of_summable (index_orbit_infinite hn) ?_
    (summable_sq_mFourierCoeff F)
  rintro i ⟨p, rfl⟩
  exact hconst p

/-- **An `L²` eigenfunction with a unimodular eigenvalue `≠ 1` is a.e. zero.**  All off-origin
coefficients vanish (`mFourierCoeff_eq_zero_of_eigen`) and the zero mode satisfies `c₀ = l⁻¹ c₀`
with `l⁻¹ ≠ 1`, forcing `c₀ = 0`.  Hence the Fourier series collapses to `0` in `L²`. -/
theorem coe_ae_zero_of_eigen {F : Lp ℂ 2 (volume : Measure T2)} {l : ℂ} (hl0 : l ≠ 0)
    (hl : ‖l‖ = 1) (hl1 : l ≠ 1)
    (hF : (F : T2 → ℂ) ∘ catTorus =ᵐ[volume] l • (F : T2 → ℂ)) :
    (F : T2 → ℂ) =ᵐ[volume] 0 := by
  classical
  -- Zero mode vanishes: `c₀ = l⁻¹ • c₀` and `l⁻¹ ≠ 1`.
  have hzero_mode : mFourierCoeff (F : T2 → ℂ) 0 = 0 := by
    have h := mFourierCoeff_vecMul_of_eigen hl0 hF (0 : Fin 2 → ℤ)
    rw [Matrix.zero_vecMul, smul_eq_mul] at h
    have hli : l⁻¹ ≠ 1 := fun hc => hl1 (by rw [← inv_inv l, hc, inv_one])
    have hne : (1 - l⁻¹) ≠ 0 := sub_ne_zero.mpr (Ne.symm hli)
    have hmul : (1 - l⁻¹) * mFourierCoeff (F : T2 → ℂ) 0 = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left hne
  -- All Fourier coefficients vanish.
  have hrepr : ∀ n : Fin 2 → ℤ, mFourierBasis.repr F n = 0 := by
    intro n
    rw [mFourierBasis_repr]
    by_cases hn : n = 0
    · rw [hn]; exact hzero_mode
    · exact mFourierCoeff_eq_zero_of_eigen hl0 hl hF hn
  -- The Fourier series collapses to `0`.
  have hsum := mFourierBasis.hasSum_repr F
  have hzero : HasSum (fun n : Fin 2 → ℤ => mFourierBasis.repr F n • mFourierBasis n) 0 := by
    have heq : (fun n : Fin 2 → ℤ => mFourierBasis.repr F n • mFourierBasis n) = fun _ => 0 := by
      funext n; rw [hrepr n, zero_smul]
    rw [heq]; exact hasSum_zero
  have hF0 : F = 0 := hsum.unique hzero
  rw [hF0]; exact Lp.coeFn_zero ℂ 2 volume

/-- **Spectral rigidity of the Arnold cat map (GitHub issue #47).**  A measurable eigenfunction
`g : 𝕋² → ℂ` of `catTorus` with a unimodular eigenvalue `l ≠ 1` (i.e. `g (catTorus x) = l · g x` for
all `x`, `‖l‖ = 1`, `l ≠ 1`) vanishes almost everywhere.

Ergodicity makes `‖g‖` a.e. constant, so `g ∈ L²`; the eigen-twist of its Fourier coefficients then
forces every mode — the constant mode included — to vanish. -/
theorem catTorus_eigenfunction_ae_zero {g : T2 → ℂ} {l : ℂ}
    (hg : Measurable g) (heig : ∀ x, g (catTorus x) = l * g x)
    (hl : ‖l‖ = 1) (hl1 : l ≠ 1) : g =ᵐ[volume] 0 := by
  have hl0 : l ≠ 0 := by
    intro h; rw [h, norm_zero] at hl; exact zero_ne_one hl
  -- `‖g‖` is `catTorus`-invariant (`‖l‖ = 1`), hence a.e. constant by ergodicity.
  have hnorminv : (fun x => ‖g x‖) ∘ catTorus =ᵐ[volume] (fun x => ‖g x‖) :=
    Filter.Eventually.of_forall (fun x => by
      simp only [Function.comp_apply, heig, norm_mul, hl, one_mul])
  obtain ⟨cst, hcst⟩ := ergodic_catTorus.ae_eq_const_of_ae_eq_comp_ae
    hg.norm.aestronglyMeasurable hnorminv
  have hbound : ∀ᵐ x ∂(volume : Measure T2), ‖g x‖ ≤ cst := by
    filter_upwards [hcst] with x hx; exact le_of_eq hx
  -- `g` is a.e. bounded, hence in `L²`; pass to its `L²` representative `F`.
  have hmem : MemLp g 2 (volume : Measure T2) := MemLp.of_bound hg.aestronglyMeasurable cst hbound
  set F : Lp ℂ 2 (volume : Measure T2) := hmem.toLp g with hFdef
  have hFg : (F : T2 → ℂ) =ᵐ[volume] g := by rw [hFdef]; exact hmem.coeFn_toLp
  -- Transport the eigen-equation to `F`.
  have hFeig : (F : T2 → ℂ) ∘ catTorus =ᵐ[volume] l • (F : T2 → ℂ) := by
    have hgcomp : g ∘ catTorus = l • g := by
      funext x; simp only [Function.comp_apply, Pi.smul_apply, heig, smul_eq_mul]
    calc (F : T2 → ℂ) ∘ catTorus
        =ᵐ[volume] g ∘ catTorus :=
          hFg.comp_tendsto measurePreserving_catTorus.quasiMeasurePreserving.tendsto_ae
      _ = l • g := hgcomp
      _ =ᵐ[volume] l • (F : T2 → ℂ) := by
          filter_upwards [hFg] with x hx; simp only [Pi.smul_apply, hx]
  -- `F =ᵐ 0`, hence `g =ᵐ 0`.
  exact hFg.symm.trans (coe_ae_zero_of_eigen hl0 hl hl1 hFeig)

end ErgodicTheory.CatMapToral
