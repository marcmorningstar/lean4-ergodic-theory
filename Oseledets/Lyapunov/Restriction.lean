/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.Corollaries

/-!
# Restriction of the cocycle to an invariant subbundle

This module realizes the *restriction to invariant sub-cocycles* extension (item 5 of the
additive-extensions blueprint). Given a measurable, cocycle-invariant subbundle
`W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))` of the ambient bundle, the Lyapunov
spectrum realized inside `W` is a sub-object of the ambient limsup spectrum.

## What is delivered (Stage (i), guaranteed)

* `InvariantSubbundle` — a measurable, a.e. cocycle-invariant subbundle, with the
  equivariance shape `Submodule.map (toEuclideanCLM (A x)).toLinearMap (W x) = W (T x)`
  matching `Oseledets.IsOseledetsFiltration` / `Vflag_equivariant`.
* `restrictedSpectrum` — the exponents realized by nonzero vectors of `W x`, as a
  sub-`Finset` of `spectrum A T x`.
* `restrictedSpectrum_subset` / `restrictedSpectrum_subset_ae` — the restricted spectrum is
  a subset of the ambient spectrum (immediate from `lambdaBar_mem_spectrum`).
* `restricted_finrank_le` — the dimension interlacing
  `finrank (W x ⊓ Vflag A T x i) ≤ finrank (Vflag A T x i)` (a sub-multiplicity bound).
* `restricted_inf_lambdaSublevel_equivariant` — the intersections `W ⊓ Vflag` are themselves
  `A`-equivariant a.e., so the *restricted* multiplicities `finrank (W ⊓ Vflag i)` are a.e.
  `T`-invariant.

The honest meaning of "interlacing" here: the restricted exponents form a **sub-multiset of
the ambient exponent multiset** (with multiplicities bounded by `finrank` monotonicity of
`W ⊓ Vflag` inside `Vflag`). This is **not** classical Cauchy eigenvalue interlacing.

## What is scoped out (Stage (ii), deferred)

The *full restricted* `IsOseledetsFiltration` on `W` (via the flag `x ↦ Vflag A T x i ⊓ W x`)
is **not** delivered. The intersections are equivariant (`restricted_inf_lambdaSublevel_equivariant`,
proved here) but establishing that `x ↦ Vflag A T x i ⊓ W x` is a `MeasurableSubspace`
requires a closure-under-`⊓` lemma `MeasurableSubspace.inf` that is **absent** from the
current infrastructure (`Oseledets/Lyapunov/Measurable.lean` provides only `measurable_finrank`
and span/selection plumbing — no `⊓`/intersection measurability). Consequently the a.e.
*constancy* (by ergodicity, via `measurable_finrank` + `ae_eq_const_of_ae_eq_comp₀`) of the
restricted multiplicities is also deferred; only their a.e. `T`-*invariance* is established.

All standing hypotheses match the rest of the development
(`hT : Ergodic T μ`, `hA : ∀ x, (A x).det ≠ 0`, `hAmeas : Measurable A`,
`hint : IntegrableLogNorm A μ`, `hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ`,
`[IsProbabilityMeasure μ]`).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} {d : ℕ}

/-! ### The invariant subbundle structure -/

/-- A **measurable, cocycle-invariant subbundle** of the ambient bundle
`EuclideanSpace ℝ (Fin d)` over the base `X`, relative to a measure `μ`, dynamics `T`, and
linear cocycle generator `A`.

The invariance is the a.e. equivariance
`Submodule.map (toEuclideanCLM (A x)).toLinearMap (W x) = W (T x)`, the exact shape used by
`Oseledets.IsOseledetsFiltration` and `Vflag_equivariant`. -/
structure InvariantSubbundle [MeasurableSpace X] (μ : Measure X) (T : X → X)
    (A : X → Matrix (Fin d) (Fin d) ℝ) where
  /-- The fibre subspace at each base point. -/
  W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))
  /-- The fibre varies measurably in the base point. -/
  meas : MeasurableSubspace W
  /-- The subbundle is `A`-invariant almost everywhere. -/
  invariant_ae : ∀ᵐ x ∂μ,
    Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (W x) = W (T x)

/-! ### The restricted spectrum -/

/-- The **restricted limsup spectrum** at `x`: the sub-`Finset` of the ambient spectrum
`spectrum A T x` consisting of the exponents realized by some nonzero vector of `W x`. -/
noncomputable def restrictedSpectrum (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x : X) : Finset ℝ :=
  open Classical in
  (spectrum A T x).filter
    (fun r => ∃ v : EuclideanSpace ℝ (Fin d), v ∈ W x ∧ v ≠ 0 ∧ lambdaBar A T x v = r)

/-- A value lies in the restricted spectrum iff it is in the ambient spectrum and realized by
a nonzero vector of `W x`. -/
theorem mem_restrictedSpectrum {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    {W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {x : X} {r : ℝ} :
    r ∈ restrictedSpectrum A T W x ↔
      r ∈ spectrum A T x ∧
        ∃ v : EuclideanSpace ℝ (Fin d), v ∈ W x ∧ v ≠ 0 ∧ lambdaBar A T x v = r := by
  classical
  rw [restrictedSpectrum, Finset.mem_filter]

/-- **The restricted spectrum is a subset of the ambient spectrum** (pointwise, no
hypotheses): every exponent realized inside `W x` is realized in the ambient space. -/
theorem restrictedSpectrum_subset (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x : X) :
    restrictedSpectrum A T W x ⊆ spectrum A T x := by
  classical
  exact Finset.filter_subset _ _

/-- Every nonzero vector of `W x` realizes an exponent of the restricted spectrum (under the
`IsUltrametricGrowth` hypothesis that makes the ambient spectrum well-behaved). -/
theorem lambdaBar_mem_restrictedSpectrum {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    {W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {x : X}
    (hx : IsUltrametricGrowth (lambdaBar A T x)) {v : EuclideanSpace ℝ (Fin d)}
    (hvW : v ∈ W x) (hv : v ≠ 0) :
    lambdaBar A T x v ∈ restrictedSpectrum A T W x :=
  (mem_restrictedSpectrum).mpr ⟨lambdaBar_mem_spectrum hx hv, v, hvW, hv, rfl⟩

variable [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **The restricted spectrum is a.e. a subset of the ambient spectrum.** This is immediate
from the pointwise `restrictedSpectrum_subset`; it is the a.e. form requested by the
blueprint. -/
theorem restrictedSpectrum_subset_ae (A : X → Matrix (Fin d) (Fin d) ℝ)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    ∀ᵐ x ∂μ, restrictedSpectrum A T W x ⊆ spectrum A T x :=
  Filter.Eventually.of_forall fun x => restrictedSpectrum_subset A T W x

/-! ### Dimension interlacing (sub-multiplicity bound)

The restricted multiplicities are bounded by the ambient multiplicities: at each flag level
`Vflag A T x i`, the part captured by `W x` is the intersection `W x ⊓ Vflag A T x i`, whose
dimension is at most that of the ambient level by `finrank` monotonicity. The honest
"interlacing" is that the restricted exponents form a sub-multiset of the ambient exponent
multiset. -/

omit [MeasurableSpace X] in
/-- **Dimension interlacing.** At each ambient flag level, the dimension captured by the
subbundle is at most the ambient dimension. -/
theorem restricted_finrank_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x : X)
    (i : Fin (specCard A T x + 1)) :
    Module.finrank ℝ (W x ⊓ Vflag A T x i : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤
      Module.finrank ℝ (Vflag A T x i) :=
  Submodule.finrank_mono inf_le_right

omit [MeasurableSpace X] in
/-- The restricted multiplicity at a stratum is bounded by the ambient multiplicity:
`dim (W ⊓ V i) - dim (W ⊓ V (i+1)) ≤ dim (V i) - dim (V (i+1))`. This is the honest
sub-multiset interlacing of the exponent multisets (not Cauchy interlacing).

Mathematically: `(W ⊓ V i) / (W ⊓ V (i+1))` embeds into `(V i) / (V (i+1))`, so the restricted
stratum dimension is at most the ambient one. This is the modular-law identity
`dim ((W⊓Vᵢ) ⊔ Vₛ) + dim (W⊓Vₛ) = dim (W⊓Vᵢ) + dim Vₛ` combined with `(W⊓Vᵢ) ⊔ Vₛ ≤ Vᵢ`. -/
theorem restricted_multiplicity_le {A : X → Matrix (Fin d) (Fin d) ℝ}
    {W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {x : X}
    (hx : IsUltrametricGrowth (lambdaBar A T x)) (i : Fin (specCard A T x)) :
    Module.finrank ℝ (W x ⊓ Vflag A T x i.castSucc : Submodule ℝ (EuclideanSpace ℝ (Fin d))) -
        Module.finrank ℝ (W x ⊓ Vflag A T x i.succ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤
      Module.finrank ℝ (Vflag A T x i.castSucc) - Module.finrank ℝ (Vflag A T x i.succ) := by
  set Vc := Vflag A T x i.castSucc with hVc
  set Vs := Vflag A T x i.succ with hVs
  have hVle : Vs ≤ Vc := (Vflag_strictAnti hx i).le
  -- modular law for `A := W ⊓ Vc` and `B := Vs` inside the ambient space
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (W x ⊓ Vc) Vs
  -- `(W ⊓ Vc) ⊓ Vs = W ⊓ Vs` since `Vs ≤ Vc`
  have hinf : (W x ⊓ Vc) ⊓ Vs = W x ⊓ Vs := by
    rw [inf_assoc, inf_eq_right.mpr hVle]
  -- `(W ⊓ Vc) ⊔ Vs ≤ Vc`
  have hsup_le : (W x ⊓ Vc) ⊔ Vs ≤ Vc := sup_le inf_le_right hVle
  have hsup_dim : Module.finrank ℝ ((W x ⊓ Vc) ⊔ Vs
      : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤ Module.finrank ℝ Vc :=
    Submodule.finrank_mono hsup_le
  rw [hinf] at hmod
  -- ambient `dim Vs ≤ dim Vc`
  have hVmono : Module.finrank ℝ Vs ≤ Module.finrank ℝ Vc := Submodule.finrank_mono hVle
  -- restricted small ≤ restricted big (monotone along `Vs ≤ Vc`)
  have hWmono : Module.finrank ℝ (W x ⊓ Vs : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤
      Module.finrank ℝ (W x ⊓ Vc : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :=
    Submodule.finrank_mono (inf_le_inf_left _ hVle)
  omega

/-! ### Equivariance of the restricted sublevels

The intersections `W ⊓ lambdaSublevel … t` are themselves `A`-equivariant a.e.: the map `A x`
is injective (invertible matrix), so it commutes with `⊓` (`Submodule.map_inf`), and both `W`
(by `InvariantSubbundle.invariant_ae`) and the sublevels (by `Vflag_equivariant`) are
equivariant. Indexing by a real threshold `t` (rather than by `Fin (specCard …)`) sidesteps
the index-type transport `specCard A T x = specCard A T (T x)`; the flag levels `Vflag A T x i`
on the interior are exactly such sublevels (`Vflag_of_lt`).

Hence the restricted multiplicities `finrank (W ⊓ lambdaSublevel … t)` are a.e. `T`-invariant.
Their a.e. *constancy* by ergodicity is deferred — see the module docstring: it needs
`MeasurableSubspace.inf`, which is not yet available. -/

/-- **`A`-equivariance of the restricted sublevels (a.e.).** For a.e. `x` and every threshold
`t`, the action of `A x` maps the restricted sublevel `W x ⊓ lambdaSublevel A T x t` onto
`W (T x) ⊓ lambdaSublevel A T (T x) t`. Since interior flag levels are sublevels
(`Vflag_of_lt`), this is the equivariance of the restricted flag. -/
theorem restricted_inf_lambdaSublevel_equivariant [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (Wb : InvariantSubbundle μ T A) :
    ∀ᵐ x ∂μ, ∀ t : ℝ,
      Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap
          (Wb.W x ⊓ lambdaSublevel A T x t) =
        Wb.W (T x) ⊓ lambdaSublevel A T (T x) t := by
  filter_upwards [Vflag_equivariant hT hA hAmeas hint hint', Wb.invariant_ae] with x hflag hW
  intro t
  -- injectivity of the action of `A x`
  have hinj : Function.Injective
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
        = Matrix.toEuclideanLin (A x) :=
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (A x)
    rw [h1]; exact injective_toEuclideanLin (hA x)
  -- `map` distributes over `⊓` for injective maps; then rewrite both factors.
  -- (`hflag` is stated through the private `Aclm`, definitionally `toEuclideanCLM (A x)`,
  -- so we close the `lambdaSublevel` factor by `exact` up to that defeq.)
  rw [Submodule.map_inf _ hinj, hW]
  refine congrArg (Wb.W (T x) ⊓ ·) ?_
  exact hflag t

/-- **A.e. `T`-invariance of the restricted multiplicities.** For a.e. `x` and every threshold
`t`, the dimension of the restricted sublevel is preserved by `T`:
`finrank (W (T x) ⊓ lambdaSublevel A T (T x) t) = finrank (W x ⊓ lambdaSublevel A T x t)`.

This is the invariance underlying ergodic constancy; the constancy itself is deferred (it
needs `MeasurableSubspace.inf`; see the module docstring). -/
theorem restricted_finrank_invariant_ae [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (Wb : InvariantSubbundle μ T A) :
    ∀ᵐ x ∂μ, ∀ t : ℝ,
      Module.finrank ℝ (Wb.W (T x) ⊓ lambdaSublevel A T (T x) t
          : Submodule ℝ (EuclideanSpace ℝ (Fin d))) =
        Module.finrank ℝ (Wb.W x ⊓ lambdaSublevel A T x t
          : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
  filter_upwards [restricted_inf_lambdaSublevel_equivariant hT hA hAmeas hint hint' Wb]
    with x hx t
  -- injectivity of `A x` again, to read off `finrank (map K) = finrank K`
  have hinj : Function.Injective
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
        = Matrix.toEuclideanLin (A x) :=
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (A x)
    rw [h1]; exact injective_toEuclideanLin (hA x)
  have heq := (Submodule.equivMapOfInjective _ hinj (Wb.W x ⊓ lambdaSublevel A T x t)).finrank_eq
  rw [← hx t]
  exact heq.symm

end Oseledets
