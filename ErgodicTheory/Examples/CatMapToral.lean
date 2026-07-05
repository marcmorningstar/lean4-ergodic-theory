/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapOrbit
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The genuine Arnold cat map as a hyperbolic toral automorphism

This module formalizes the **genuine** Arnold cat map: the automorphism of the 2-torus
`𝕋² = UnitAddTorus (Fin 2) = Fin 2 → UnitAddCircle` induced by the unimodular hyperbolic matrix
`M = !![2,1;1,1] ∈ SL₂(ℤ)`, and proves it is **measure-preserving** and **ergodic** for the Haar
(`volume`) measure.  This replaces the constant-cocycle realization in
`ErgodicTheory/Examples/Elementary.lean` (where the cat-map matrix is merely a constant cocycle over
the doubling map) with real toral dynamics.

## Strategy

* **Measure-preservation.**  `catTorus` is a continuous surjective additive automorphism of the
  compact group `𝕋²`.  Since `volume` is a Haar probability measure (product of Haar on the unit
  circle), `AddMonoidHom.measurePreserving` applies (a continuous surjective hom of compact groups
  with equal total mass is measure-preserving).

* **Ergodicity (Fourier / character argument).**  The Koopman operator sends the character
  `mFourier n` to `mFourier (catℤ ·ᵥ n)` (the matrix is symmetric, so the index action by `Mᵀ` is
  the action by `M`).  For a measurable invariant set `s`, the indicator `1_s ∈ L²` has Fourier
  coefficients constant along the orbit `p ↦ catℤᵖ ·ᵥ n`.  For `n ≠ 0` that orbit is **infinite**
  (`ErgodicTheory.CatMapToral.orbit_infinite`, the hyperbolicity input), and `ℓ²`-summability forces
  the coefficient to `0`. Hence only the `n = 0` coefficient survives, so `1_s` is a.e. constant and
  `s` is a.e. empty or full.

## Main results

* `ErgodicTheory.CatMapToral.catTorus` — the cat-map automorphism of `𝕋²`.
* `ErgodicTheory.CatMapToral.measurePreserving_catTorus` — `catTorus` preserves `volume`.
* `ErgodicTheory.CatMapToral.ergodic_catTorus` — `catTorus` is ergodic for `volume`.
-/

open MeasureTheory UnitAddTorus Matrix
open scoped ComplexConjugate ENNReal

noncomputable section

/-- Normalise the circle measure to total mass `1` (`AddCircle.haarAddCircle`), matching the
convention of `Mathlib.Analysis.Fourier.AddCircleMulti` (where `mFourierBasis` and the Fourier
coefficient API are stated).  With this `MeasureSpace` instance, `volume` on `UnitAddTorus (Fin 2)`
is the product Haar probability measure on `𝕋²`, which is exactly the basis the Fourier API uses. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory.CatMapToral

/-- The 2-torus `𝕋² = Fin 2 → UnitAddCircle`. -/
abbrev T2 : Type := UnitAddTorus (Fin 2)

/-- The inverse cat-map matrix `M⁻¹ = !![1,-1;-1,2]` (note `det M = 1`). -/
def catℤinv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; -1, 2]

/-- `M · M⁻¹ = 1`. -/
lemma catℤ_mul_inv : catℤ * catℤinv = 1 := by
  rw [catℤ, catℤinv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `M⁻¹ · M = 1`. -/
lemma catℤinv_mul : catℤinv * catℤ = 1 := by
  rw [catℤ, catℤinv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The cat-map automorphism of the torus -/

/-- The general toral endomorphism induced by an integer matrix `A`,
`(torusMap A y) i = ∑ j, A i j • y j`. -/
def torusMap (A : Matrix (Fin 2) (Fin 2) ℤ) : T2 → T2 := fun y i => ∑ j, A i j • y j

/-- The cat-map automorphism `T_M : 𝕋² → 𝕋²`, induced by `M = !![2,1;1,1]`. -/
def catTorus : T2 → T2 := torusMap catℤ

/-- `torusMap` of a matrix product is the composition of `torusMap`s.  (The `ℤ`-action on
`UnitAddCircle` makes each component additive, and matrix multiplication is the composition of the
index actions.) -/
lemma torusMap_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    torusMap (A * B) = torusMap A ∘ torusMap B := by
  funext y i
  simp only [torusMap, Function.comp_apply, Matrix.mul_apply]
  -- LHS = ∑ k (∑ j A i j * B j k) • y k,  RHS = ∑ j A i j • (∑ k B j k • y k).
  calc ∑ k, (∑ j, A i j * B j k) • y k
      = ∑ k, ∑ j, (A i j * B j k) • y k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ j, ∑ k, (A i j * B j k) • y k := Finset.sum_comm
    _ = ∑ j, A i j • ∑ k, B j k • y k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_smul]

/-- `torusMap 1 = id`. -/
lemma torusMap_one : torusMap (1 : Matrix (Fin 2) (Fin 2) ℤ) = id := by
  funext y i
  simp only [torusMap, Matrix.one_apply, id_eq]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg (by simpa [eq_comm] using hj), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `catTorus` is a bijection, with two-sided inverse `torusMap catℤinv`. -/
lemma catTorus_leftInverse : Function.LeftInverse (torusMap catℤinv) catTorus := by
  intro y
  rw [catTorus, ← Function.comp_apply (f := torusMap catℤinv), ← torusMap_mul, catℤinv_mul,
    torusMap_one, id]

lemma catTorus_rightInverse : Function.RightInverse (torusMap catℤinv) catTorus := by
  intro y
  rw [catTorus, ← Function.comp_apply (f := torusMap catℤ), ← torusMap_mul, catℤ_mul_inv,
    torusMap_one, id]

/-- `catTorus` is a bijection (it has the two-sided inverse `torusMap catℤinv`). -/
lemma catTorus_bijective : Function.Bijective catTorus :=
  ⟨catTorus_leftInverse.injective, catTorus_rightInverse.surjective⟩

/-- `catTorus` is surjective. -/
lemma catTorus_surjective : Function.Surjective catTorus := catTorus_bijective.2

/-- `catTorus` packaged as an additive monoid homomorphism of `𝕋²` (each component is a finite
sum of `ℤ`-scalings, hence additive). -/
def catTorusHom : T2 →+ T2 where
  toFun := catTorus
  map_zero' := by
    funext i; simp [catTorus, torusMap]
  map_add' x y := by
    funext i
    simp only [catTorus, torusMap, Pi.add_apply, smul_add, Finset.sum_add_distrib]

@[simp] lemma catTorusHom_apply (y : T2) : catTorusHom y = catTorus y := rfl

/-- Every `torusMap` is continuous. -/
lemma continuous_torusMap (A : Matrix (Fin 2) (Fin 2) ℤ) : Continuous (torusMap A) := by
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact (continuous_zsmul _).comp (continuous_apply j)

/-- `catTorus` is continuous. -/
lemma continuous_catTorus : Continuous catTorus := continuous_torusMap catℤ

/-! ## Measure preservation -/

/-- **The cat-map automorphism preserves Haar (`volume`).**  `catTorus` is a continuous surjective
additive automorphism of the compact group `𝕋²`, and `volume` is a Haar probability measure, so
`AddMonoidHom.measurePreserving` applies (equal total mass `1`). -/
theorem measurePreserving_catTorus :
    MeasurePreserving catTorus (volume : Measure T2) (volume : Measure T2) :=
  catTorusHom.measurePreserving (μ := (volume : Measure T2)) (ν := (volume : Measure T2))
    continuous_catTorus catTorus_surjective (by simp)

/-- `catTorus` as a measurable equivalence of `𝕋²` (continuous bijection with continuous inverse on
a compact Hausdorff space). -/
def catTorusEquiv : T2 ≃ᵐ T2 :=
  { toEquiv := Equiv.ofBijective catTorus catTorus_bijective
    measurable_toFun := continuous_catTorus.measurable
    measurable_invFun := by
      have hsymm : (Equiv.ofBijective catTorus catTorus_bijective).symm = torusMap catℤinv := by
        funext y
        rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
        exact (catTorus_rightInverse y).symm
      rw [hsymm]
      exact (continuous_torusMap catℤinv).measurable }

@[simp] lemma catTorusEquiv_apply (y : T2) : catTorusEquiv y = catTorus y := rfl

/-- The measurable-equivalence packaging `catTorusEquiv` also preserves Haar (`volume`). -/
lemma measurePreserving_catTorusEquiv :
    MeasurePreserving catTorusEquiv (volume : Measure T2) (volume : Measure T2) :=
  measurePreserving_catTorus

/-! ## The Koopman / character relation

The Koopman operator sends a character to a character, with the index transformed by the
(transpose of the) matrix.  Since `catℤ` is symmetric, `catℤᵀ = catℤ`, so the index action is just
`n ↦ catℤ ·ᵥ n`.
-/

/-- The character property in the point argument: `fourier k` is multiplicative under addition. -/
lemma fourier_add_point {k : ℤ} {x y : UnitAddCircle} :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp_rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- One `ℤ`-scaling inside `fourier`: `fourier k (a • x) = fourier (k * a) x`. -/
lemma fourier_zsmul_point {k a : ℤ} {x : UnitAddCircle} :
    fourier k (a • x) = fourier (k * a) x := by
  rw [fourier_apply, fourier_apply, smul_smul]

/-- `fourier` of a finite sum of scalings is the product of the scaled-index characters:
`fourier k (∑ j, a j • z j) = ∏ j, fourier (k * a j) (z j)`. -/
lemma fourier_sum_zsmul {k : ℤ} (a : Fin 2 → ℤ) (z : Fin 2 → UnitAddCircle) :
    fourier k (∑ j, a j • z j) = ∏ j, fourier (k * a j) (z j) := by
  induction (Finset.univ : Finset (Fin 2)) using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, fourier_add_point, fourier_zsmul_point, Finset.prod_insert hj, ih]

/-- Additivity of `fourier` in the **index** over a finite sum:
`fourier (∑ i, c i) x = ∏ i, fourier (c i) x`. -/
lemma fourier_sum_index (c : Fin 2 → ℤ) (x : UnitAddCircle) :
    fourier (∑ i, c i) x = ∏ i, fourier (c i) x := by
  induction (Finset.univ : Finset (Fin 2)) using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, fourier_add, Finset.prod_insert hi, ih]

/-- **Koopman / character relation.**  Composing a character with the cat-map automorphism gives
the character at the vecMul-transformed index:
`mFourier n (catTorus y) = mFourier (catℤ.vecMul n) y`.  Equivalently
`mFourier (catℤ.vecMul n) = mFourier n ∘ catTorus`. -/
theorem mFourier_catTorus (n : Fin 2 → ℤ) (y : T2) :
    mFourier n (catTorus y) = mFourier (Matrix.vecMul n catℤ) y := by
  simp only [mFourier, ContinuousMap.coe_mk, catTorus, torusMap]
  -- LHS = ∏ i, fourier (n i) (∑ j, catℤ i j • y j) = ∏ i ∏ j fourier (n i * catℤ i j) (y j).
  have hlhs : (∏ i, fourier (n i) (∑ j, catℤ i j • y j))
      = ∏ i, ∏ j, fourier (n i * catℤ i j) (y j) :=
    Finset.prod_congr rfl fun i _ => fourier_sum_zsmul _ _
  -- RHS = ∏ j, fourier ((vecMul n catℤ) j) (y j) = ∏ j ∏ i fourier (n i * catℤ i j) (y j).
  have hrhs : (∏ j, fourier (Matrix.vecMul n catℤ j) (y j))
      = ∏ j, ∏ i, fourier (n i * catℤ i j) (y j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show Matrix.vecMul n catℤ j = ∑ i, n i * catℤ i j from rfl, fourier_sum_index]
  rw [hlhs, hrhs, Finset.prod_comm]

/-- The Koopman relation as a functional identity:
`mFourier (catℤ.vecMul n) = (mFourier n) ∘ catTorus`. -/
theorem mFourier_vecMul_eq_comp (n : Fin 2 → ℤ) :
    (mFourier (Matrix.vecMul n catℤ) : T2 → ℂ) = (mFourier n) ∘ catTorus := by
  funext y; exact (mFourier_catTorus n y).symm

/-! ## Fourier coefficient invariance and the orbit-vanishing argument -/

/-- **Fourier coefficients of an invariant function are constant along the index orbit.**
If `f =ᵐ f ∘ catTorus`, then `mFourierCoeff f (catℤ.vecMul n) = mFourierCoeff f n`: composing the
character `mFourier (-n)` with `catTorus` and changing variables (measure preservation) shows the
two integrals agree. -/
theorem mFourierCoeff_vecMul_of_invariant {f : T2 → ℂ}
    (hf : f =ᵐ[volume] f ∘ catTorus) (n : Fin 2 → ℤ) :
    mFourierCoeff f (Matrix.vecMul n catℤ) = mFourierCoeff f n := by
  -- `mFourier (-(vecMul n catℤ)) = mFourier (vecMul (-n) catℤ) = mFourier (-n) ∘ catTorus`.
  have hchar : (mFourier (-(Matrix.vecMul n catℤ)) : T2 → ℂ)
      = (mFourier (-n)) ∘ catTorus := by
    rw [← Matrix.neg_vecMul]; exact mFourier_vecMul_eq_comp (-n)
  rw [mFourierCoeff, mFourierCoeff]
  -- `∫ t, mFourier (-(vecMul n catℤ)) t • f t = ∫ t, (mFourier (-n) (catTorus t)) • f t`.
  calc ∫ t, mFourier (-(Matrix.vecMul n catℤ)) t • f t
      = ∫ t, (mFourier (-n)) (catTorus t) • f (catTorus t) := by
        refine integral_congr_ae ?_
        filter_upwards [hf] with t ht
        have hc : mFourier (-(Matrix.vecMul n catℤ)) t = (mFourier (-n)) (catTorus t) :=
          congrFun hchar t
        have hft : f t = f (catTorus t) := ht
        rw [hc, hft]
    _ = ∫ s, (mFourier (-n)) s • f s :=
        measurePreserving_catTorusEquiv.integral_comp'
          (fun s => (mFourier (-n)) s • f s)

/-- A complex sequence that is **constant on an infinite set** and **square-summable** vanishes on
that set.  (Square-summability forces `‖·‖² → 0` along the cofinite filter, but a nonzero constant
on an infinite set never tends to `0`.) -/
theorem eq_zero_of_constant_on_infinite_of_summable {ι : Type*} {c : ι → ℂ} {S : Set ι} {v : ℂ}
    (hS : S.Infinite) (hconst : ∀ i ∈ S, c i = v) (hsum : Summable fun i => ‖c i‖ ^ 2) : v = 0 := by
  by_contra hv
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  -- `‖c ·‖² → 0` cofinitely, so eventually (cofinitely) `‖c i‖² < ‖v‖²`.
  have htends : Filter.Tendsto (fun i => ‖c i‖ ^ 2) Filter.cofinite (nhds 0) :=
    hsum.tendsto_cofinite_zero
  have hev : ∀ᶠ i in Filter.cofinite, ‖c i‖ ^ 2 < ‖v‖ ^ 2 :=
    htends.eventually (eventually_lt_nhds hpos)
  -- Hence `{i | ‖c i‖² < ‖v‖²}ᶜ` is finite.
  have hfin : {i | ‖c i‖ ^ 2 < ‖v‖ ^ 2}ᶜ.Finite :=
    Filter.eventually_cofinite.mp hev
  -- But `S` is contained in that finite set (since `c = v` on `S`), contradicting `S` infinite.
  refine hS (hfin.subset fun i hi => ?_)
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, hconst i hi, le_refl]

/-! ## Identifying the index action with the `mulVec` orbit -/

/-- `catℤ` is symmetric, so the `vecMul` index action coincides with the `mulVec` action. -/
lemma vecMul_catℤ (n : Fin 2 → ℤ) : Matrix.vecMul n catℤ = catℤ *ᵥ n := by
  rw [← Matrix.mulVec_transpose]
  congr 1
  rw [catℤ]; ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The `p`-fold iterate of the index action is the `p`-th matrix power applied by `mulVec`. -/
lemma iterate_vecMul (p : ℕ) (n : Fin 2 → ℤ) :
    (fun m => Matrix.vecMul m catℤ)^[p] n = catℤ ^ p *ᵥ n := by
  induction p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, vecMul_catℤ, mulVec_mulVec, ← pow_succ']

/-- The index orbit `{(vecMul · catℤ)ᵖ n}` is the `mulVec`-orbit, hence **infinite** for `n ≠ 0`. -/
theorem index_orbit_infinite {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    (Set.range (fun p : ℕ => (fun m => Matrix.vecMul m catℤ)^[p] n)).Infinite := by
  have : (fun p : ℕ => (fun m => Matrix.vecMul m catℤ)^[p] n) = fun p => catℤ ^ p *ᵥ n := by
    funext p; exact iterate_vecMul p n
  rw [this]; exact orbit_infinite hn

/-! ## Ergodicity -/

/-- The constant character `mFourier 0` is the constant function `1`. -/
lemma mFourier_zero_apply (y : T2) : mFourier (0 : Fin 2 → ℤ) y = 1 := by
  rw [mFourier_zero]; rfl

/-- For an `L²` function `f`, the Fourier coefficients are square-summable. -/
lemma summable_sq_mFourierCoeff (f : Lp ℂ 2 (volume : Measure T2)) :
    Summable fun n => ‖mFourierCoeff (f : T2 → ℂ) n‖ ^ 2 :=
  (hasSum_sq_mFourierCoeff (d := Fin 2) f).summable

/-- **Fourier coefficients of an invariant `L²` function vanish off the origin.**  If
`(f : T2 → ℂ)` is `=ᵐ f ∘ catTorus` and `f ∈ L²`, then `mFourierCoeff f n = 0` for every nonzero
index `n`.  (Constant along the infinite index orbit + square-summable ⇒ zero.) -/
theorem mFourierCoeff_eq_zero_of_invariant {f : Lp ℂ 2 (volume : Measure T2)}
    (hf : (f : T2 → ℂ) =ᵐ[volume] (f : T2 → ℂ) ∘ catTorus) {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    mFourierCoeff (f : T2 → ℂ) n = 0 := by
  -- The coefficient is constant along the index orbit.
  have hconst : ∀ p : ℕ,
      mFourierCoeff (f : T2 → ℂ) ((fun m => Matrix.vecMul m catℤ)^[p] n)
        = mFourierCoeff (f : T2 → ℂ) n := by
    intro p
    induction p with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', mFourierCoeff_vecMul_of_invariant hf, ih]
  -- Apply the infinite-orbit / summability collapse with `S` the orbit, `v` the value at `n`.
  refine eq_zero_of_constant_on_infinite_of_summable (index_orbit_infinite hn) ?_
    (summable_sq_mFourierCoeff f)
  rintro i ⟨p, rfl⟩
  exact hconst p

/-- **An invariant `L²` function is a.e. constant.**  If `f ∈ L²` and `(f : T2 → ℂ) =ᵐ f∘catTorus`,
then `f` is a.e. equal to its zeroth Fourier coefficient.  (All higher coefficients vanish by
`mFourierCoeff_eq_zero_of_invariant`, so the Fourier series collapses to the constant term.) -/
theorem ae_eq_const_of_invariant {f : Lp ℂ 2 (volume : Measure T2)}
    (hf : (f : T2 → ℂ) =ᵐ[volume] (f : T2 → ℂ) ∘ catTorus) :
    (f : T2 → ℂ) =ᵐ[volume] fun _ => mFourierCoeff (f : T2 → ℂ) 0 := by
  classical
  -- In the Hilbert basis, only the `0`-th coefficient survives.
  have hrepr : ∀ n : Fin 2 → ℤ, n ≠ 0 → mFourierBasis.repr f n = 0 := by
    intro n hn
    rw [mFourierBasis_repr]
    exact mFourierCoeff_eq_zero_of_invariant hf hn
  -- The Fourier series collapses to `c₀ • (basis 0)`.
  have hsum := mFourierBasis.hasSum_repr f
  have hcollapse : HasSum (fun n => mFourierBasis.repr f n • mFourierBasis n)
      (mFourierBasis.repr f 0 • mFourierBasis 0) := by
    have heq : (fun n : Fin 2 → ℤ => mFourierBasis.repr f n • mFourierBasis n)
        = fun n => if n = 0 then mFourierBasis.repr f 0 • mFourierBasis 0 else 0 := by
      funext n
      split_ifs with h
      · rw [h]
      · rw [hrepr n h, zero_smul]
    rw [heq]; exact hasSum_ite_eq 0 _
  -- Name the surviving coefficient `c₀` so the substitution does not recurse.
  set c₀ : ℂ := mFourierBasis.repr f 0 with hc₀
  have hF : f = c₀ • mFourierBasis 0 := hsum.unique hcollapse
  -- `basis 0 = mFourierLp 2 0 =ᵐ mFourier 0 = const 1`, so `f =ᵐ c₀ • 1`.
  have hbasis0 : (mFourierBasis (d := Fin 2) 0 : T2 → ℂ) =ᵐ[volume] fun _ => (1 : ℂ) := by
    rw [coe_mFourierBasis]
    filter_upwards [coeFn_mFourierLp 2 (0 : Fin 2 → ℤ)] with y hy
    rw [hy, mFourier_zero_apply]
  -- Combine.
  have hcoe : (f : T2 → ℂ) =ᵐ[volume] c₀ • (mFourierBasis (d := Fin 2) 0 : T2 → ℂ) := by
    rw [hF]
    exact Lp.coeFn_smul c₀ (mFourierBasis (d := Fin 2) 0)
  -- `c₀ = repr f 0 = mFourierCoeff f 0`, the constant in the statement.
  have hcc : c₀ = mFourierCoeff (f : T2 → ℂ) 0 := by rw [hc₀, mFourierBasis_repr]
  filter_upwards [hcoe, hbasis0] with y hy hy0
  rw [hy, Pi.smul_apply, hy0, smul_eq_mul, mul_one, hcc]

/-- **The Arnold cat map is ergodic.**  For a measurable `catTorus`-invariant set `s`, the
indicator `1_s ∈ L²` is `catTorus`-invariant, hence a.e. constant by `ae_eq_const_of_invariant`;
an indicator that is a.e. constant forces `s` to be a.e. empty or a.e. the whole torus.  Together
with `measurePreserving_catTorus` this gives ergodicity. -/
theorem ergodic_catTorus : Ergodic catTorus (volume : Measure T2) := by
  refine ⟨measurePreserving_catTorus, ?_⟩
  refine ⟨fun s hs hinv => ?_⟩
  -- The indicator of `s` as an `L²` element.
  have hμs : (volume : Measure T2) s ≠ ∞ := measure_ne_top _ _
  set F : Lp ℂ 2 (volume : Measure T2) := indicatorConstLp 2 hs hμs (1 : ℂ) with hFdef
  -- `F` is `catTorus`-invariant, because `s` is.
  have hFinv : (F : T2 → ℂ) =ᵐ[volume] (F : T2 → ℂ) ∘ catTorus := by
    have hcoe : (F : T2 → ℂ) =ᵐ[volume] s.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    -- `(1_s) ∘ catTorus = 1_{catTorus⁻¹ s} = 1_s`.
    have hmem : ∀ t : T2, catTorus t ∈ s ↔ t ∈ s := fun t => by
      conv_rhs => rw [← hinv]
      rfl
    have hind : (s.indicator (fun _ => (1 : ℂ))) ∘ catTorus
        = s.indicator (fun _ => (1 : ℂ)) := by
      funext t
      simp only [Function.comp_apply]
      by_cases ht : catTorus t ∈ s
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ((hmem t).mp ht)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun h => ht ((hmem t).mpr h))]
    calc (F : T2 → ℂ)
        =ᵐ[volume] s.indicator (fun _ => (1 : ℂ)) := hcoe
      _ = (s.indicator (fun _ => (1 : ℂ))) ∘ catTorus := hind.symm
      _ =ᵐ[volume] (F : T2 → ℂ) ∘ catTorus :=
          (hcoe.symm.comp_tendsto measurePreserving_catTorus.quasiMeasurePreserving.tendsto_ae)
  -- Hence `F` (and so `1_s`) is a.e. constant.
  have hconst : (F : T2 → ℂ) =ᵐ[volume] fun _ => mFourierCoeff (F : T2 → ℂ) 0 :=
    ae_eq_const_of_invariant hFinv
  set c : ℂ := mFourierCoeff (F : T2 → ℂ) 0 with hc
  -- `1_s =ᵐ c`.  An indicator a.e. equal to a constant: the constant is `0` or `1`, giving the
  -- measure-`0`-or-full dichotomy for `s`.
  have hind_const : s.indicator (fun _ => (1 : ℂ)) =ᵐ[volume] fun _ => c :=
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ))).symm.trans hconst
  rw [Filter.eventuallyConst_set']
  -- Split on whether `c = 0`.
  by_cases hc0 : c = 0
  · -- `1_s =ᵐ 0`, so `s` is a.e. empty.
    left
    have : s.indicator (fun _ => (1 : ℂ)) =ᵐ[volume] (fun _ => (0 : ℂ)) := by
      filter_upwards [hind_const] with x hx; rw [hx, hc0]
    rw [Filter.eventuallyEq_empty]
    filter_upwards [this] with x hx
    intro hxs
    rw [Set.indicator_of_mem hxs] at hx
    exact one_ne_zero hx
  · -- `c ≠ 0`.  On the complement `1_s = 0 = c` would force `c = 0`; so a.e. `x ∈ s`.
    right
    have huniv : ∀ᵐ x ∂(volume : Measure T2), x ∈ s := by
      filter_upwards [hind_const] with x hx
      by_contra hxs
      rw [Set.indicator_of_notMem hxs] at hx
      exact hc0 hx.symm
    rw [Filter.eventuallyEq_univ]
    filter_upwards [huniv] with x hx
    exact hx

end ErgodicTheory.CatMapToral
