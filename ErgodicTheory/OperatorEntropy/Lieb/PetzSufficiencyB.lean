/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Petz equality — sufficiency: the resolvent readoff (module M3, route B)

This module supplies the two crux analytic gaps of the **sufficiency (`⟹`) direction** of the
Petz equality theorem (issue #28), along the resolvent route (Petz 2003):

* **crux (5) — the Stone–Weierstrass readoff on a finite spectrum.** The resolvent functions
  `t ↦ (x + t)⁻¹` (`t > 0`) are *total* on any finite set of positive reals: they are linearly
  independent as functions of `t`, so (a `span`-`flip` duality) their evaluation vectors span the
  full function space on the finite point set.  Consequently any target function agrees on the
  finite set with a finite `ℂ`-linear combination of resolvents.  This is the step that upgrades
  "the channel intertwines every resolvent `(Δ + t)⁻¹`" to "the channel intertwines every
  continuous function of `Δ`", in particular the modular power `Δ^{it}`.

The linear-independence heart is a one-variable polynomial argument: if `∑ᵢ cᵢ/(xᵢ + t) = 0` for
all `t > 0`, then clearing denominators gives a polynomial vanishing on the infinite set `(0,∞)`,
hence the zero polynomial; evaluating at `t = -x₀` isolates `c₀ · ∏_{j≠0}(xⱼ - x₀) = 0`, forcing
`c₀ = 0`.

## Main results

* `ErgodicTheory.OperatorEntropy.Lieb.resolvent_linearIndependent`: the resolvent functions
  `x ↦ (t ↦ (x + t)⁻¹)` are `ℂ`-linearly independent over a finite set of distinct positive reals.
* `ErgodicTheory.OperatorEntropy.Lieb.resolvent_span_top`: their evaluation family spans the full
  finite-dimensional function space.
* `ErgodicTheory.OperatorEntropy.Lieb.exists_resolvent_combo`: every target function on the finite set
  is a finite `ℂ`-linear combination of resolvents (`t > 0`).
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

/-! ## crux (5): resolvent totality on a finite spectrum -/

/-- The resolvent function family `x ↦ (t ↦ (x + t)⁻¹ : ℂ)`, indexed by a finite type `ι` mapped
into the positive reals by an injection `x`, is **`ℂ`-linearly independent**.

The proof is the one-variable partial-fractions argument: a vanishing combination
`∑ᵢ cᵢ (xᵢ + t)⁻¹ = 0` (for all `t > 0`) clears to a polynomial with infinitely many roots, hence
the zero polynomial, and evaluating at `t = -x₀` isolates `c₀`. -/
theorem resolvent_linearIndependent {ι : Type*} [Finite ι] (x : ι → ℝ)
    (hxinj : Function.Injective x) (hxpos : ∀ i, 0 < x i) :
    LinearIndependent ℂ
      (fun (i : ι) => (fun (t : {t : ℝ // 0 < t}) => ((x i : ℂ) + (t : ℂ))⁻¹)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i0
  -- evaluate the vanishing combination at each `t > 0`
  have hpt : ∀ t : ℝ, 0 < t → ∑ i, c i * ((x i : ℂ) + (t : ℂ))⁻¹ = 0 := by
    intro t ht
    have hEval := congrFun hc ⟨t, ht⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hEval
  -- the "cleared" polynomial `Q(T) = ∑ᵢ cᵢ ∏_{j≠i} (T + xⱼ)`
  set Q : ℂ[X] := ∑ i, C (c i) * ∏ j ∈ Finset.univ.erase i, (X + C ((x j : ℂ))) with hQ
  -- `eval` of `Q` at any complex `z`
  have hevalQ : ∀ z : ℂ, Q.eval z = ∑ i, c i * ∏ j ∈ Finset.univ.erase i, (z + (x j : ℂ)) := by
    intro z
    rw [hQ]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
  -- `Q` vanishes at every `t > 0` (clear denominators against `hpt`)
  have hroot : ∀ t : ℝ, 0 < t → Q.eval ((t : ℂ)) = 0 := by
    intro t ht
    rw [hevalQ]
    have key : (∑ i, c i * ∏ j ∈ Finset.univ.erase i, ((t : ℂ) + (x j : ℂ)))
        = (∏ j, ((t : ℂ) + (x j : ℂ))) * (∑ i, c i * ((x i : ℂ) + (t : ℂ))⁻¹) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hxit : ((x i : ℂ) + (t : ℂ)) ≠ 0 := by
        have : (0 : ℝ) < x i + t := by have := hxpos i; linarith
        exact_mod_cast (by positivity : (0:ℝ) < x i + t).ne'
      have hprod : (∏ j, ((t : ℂ) + (x j : ℂ)))
          = ((t : ℂ) + (x i : ℂ)) * ∏ j ∈ Finset.univ.erase i, ((t : ℂ) + (x j : ℂ)) :=
        (Finset.mul_prod_erase Finset.univ (fun j => ((t : ℂ) + (x j : ℂ)))
          (Finset.mem_univ i)).symm
      rw [hprod]
      field_simp
      ring
    rw [key, hpt t ht, mul_zero]
  -- infinitely many roots ⇒ `Q = 0`
  have hinf : Set.Infinite {z : ℂ | Q.IsRoot z} := by
    have hsub : (fun r : ℝ => (r : ℂ)) '' Set.Ioi 0 ⊆ {z : ℂ | Q.IsRoot z} := by
      rintro z ⟨r, hr, rfl⟩
      exact hroot r hr
    have himg : ((fun r : ℝ => (r : ℂ)) '' Set.Ioi 0).Infinite :=
      (Set.infinite_image_iff (Complex.ofReal_injective.injOn)).mpr (Set.Ioi_infinite 0)
    exact Set.Infinite.mono hsub himg
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q hinf
  -- evaluate `Q` at `-(x i0)` : only the `i = i0` term survives
  have hz : Q.eval (-(x i0 : ℂ)) = 0 := by rw [hQ0]; simp
  rw [hevalQ] at hz
  have hcollapse : (∑ i, c i * ∏ j ∈ Finset.univ.erase i, (-(x i0 : ℂ) + (x j : ℂ)))
      = c i0 * ∏ j ∈ Finset.univ.erase i0, (-(x i0 : ℂ) + (x j : ℂ)) := by
    rw [Finset.sum_eq_single i0]
    · intro i _ hi
      have hmem : i0 ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ _⟩
      rw [Finset.prod_eq_zero hmem (by ring), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i0) h
  rw [hcollapse] at hz
  have hprodne : (∏ j ∈ Finset.univ.erase i0, (-(x i0 : ℂ) + (x j : ℂ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj hzero
    have hjne : j ≠ i0 := (Finset.mem_erase.mp hj).1
    have hxne : x j ≠ x i0 := fun h => hjne (hxinj h)
    apply hxne
    have : (x j : ℂ) = (x i0 : ℂ) := by linear_combination hzero
    exact_mod_cast this
  exact (mul_eq_zero.mp hz).resolve_right hprodne

/-- The evaluation family of the resolvents `{ t ↦ (fun i ↦ (xᵢ + t)⁻¹) : t > 0 }` **spans** the
full finite-dimensional function space `ι → ℂ`, for `x` an injection of the finite type `ι` into
the positive reals. -/
theorem resolvent_span_top {ι : Type*} [Finite ι] (x : ι → ℝ)
    (hxinj : Function.Injective x) (hxpos : ∀ i, 0 < x i) :
    Submodule.span ℂ
        (Set.range (flip (fun (i : ι) (t : {t : ℝ // 0 < t}) => ((x i : ℂ) + (t : ℂ))⁻¹))) = ⊤ :=
  span_flip_eq_top_iff_linearIndependent.mpr (resolvent_linearIndependent x hxinj hxpos)

/-- **Resolvent readoff (crux 5).** For an injection `x` of a finite type into the positive reals,
every target `g : ι → ℂ` is a finite `ℂ`-linear combination of resolvents `(xᵢ + t)⁻¹` with the
shifts `t > 0`.  This is the step reconstructing an arbitrary function of a finite-spectrum
operator from its resolvents. -/
theorem exists_resolvent_combo {ι : Type*} [Finite ι] (x : ι → ℝ)
    (hxinj : Function.Injective x) (hxpos : ∀ i, 0 < x i) (g : ι → ℂ) :
    ∃ c : {t : ℝ // 0 < t} →₀ ℂ,
      ∀ i, g i = ∑ t ∈ c.support, c t * ((x i : ℂ) + (t : ℂ))⁻¹ := by
  have hmem : g ∈ Submodule.span ℂ
      (Set.range (flip (fun (i : ι) (t : {t : ℝ // 0 < t}) => ((x i : ℂ) + (t : ℂ))⁻¹))) := by
    rw [resolvent_span_top x hxinj hxpos]; trivial
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, fun i => ?_⟩
  have happ : (c.sum fun t a => a • flip
      (fun (i : ι) (t : {t : ℝ // 0 < t}) => ((x i : ℂ) + (t : ℂ))⁻¹) t) i
      = ∑ t ∈ c.support, c t * ((x i : ℂ) + (t : ℂ))⁻¹ := by
    rw [Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [flip, Pi.smul_apply, smul_eq_mul]
  rw [← happ, hc]

end ErgodicTheory.OperatorEntropy.Lieb

end
