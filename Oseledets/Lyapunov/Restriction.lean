/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.Corollaries
import Oseledets.TwoSided.MeasurableInf

/-!
# Restriction of the cocycle to an invariant subbundle

This module realizes the *restriction to invariant sub-cocycles* extension (item 5 of the
additive-extensions blueprint). Given a measurable, cocycle-invariant subbundle
`W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))` of the ambient bundle, the Lyapunov
spectrum realized inside `W` is a sub-object of the ambient limsup spectrum.

## What is delivered (Stage (i), guaranteed)

* `InvariantSubbundle` — a measurable, a.e. cocycle-invariant subbundle, with the
  equivariance shape `Submodule.map (toEuclideanCLM (A x)).toLinearMap (W x) = W (T x)`
  matching `Oseledets.IsOseledetsFiltration` / `vflag_equivariant`.
* `restrictedSpectrum` — the exponents realized by nonzero vectors of `W x`, as a
  sub-`Finset` of `lyapunovSpectrum A T x`.
* `restrictedSpectrum_subset` / `restrictedSpectrum_subset_ae` — the restricted spectrum is
  a subset of the ambient spectrum (immediate from `lambdaBar_mem_lyapunovSpectrum`).
* `restricted_finrank_le` — the dimension interlacing
  `finrank (W x ⊓ vflag A T x i) ≤ finrank (vflag A T x i)` (a sub-multiplicity bound).
* `restricted_inf_lambdaSublevel_equivariant` — the intersections `W ⊓ vflag` are themselves
  `A`-equivariant a.e., so the *restricted* multiplicities `finrank (W ⊓ vflag i)` are a.e.
  `T`-invariant.

The honest meaning of "interlacing" here: the restricted exponents form a **sub-multiset of
the ambient exponent multiset** (with multiplicities bounded by `finrank` monotonicity of
`W ⊓ vflag` inside `vflag`). This is **not** classical Cauchy eigenvalue interlacing.

## What is delivered (Stage (ii), the full restricted filtration)

Intersecting `W` with the **forward Oseledets witness** `V` of an `IsOseledetsFiltration`
(the everywhere-measurable family — *not* the a.e.-only `vflag`, which has no
`MeasurableSubspace` instance) sidesteps the old blocker: `MeasurableSubspace.inf`
(`Oseledets/TwoSided/MeasurableInf.lean`) discharges measurability of `x ↦ W x ⊓ V i x` in one
line. From there:

* `restricted_inf_measurableSubspace` — each restricted level `x ↦ W x ⊓ V i x` is everywhere
  measurable.
* `restricted_inf_witness_equivariant` / `restricted_inf_witness_finrank_invariant_ae` — the
  restricted levels are `A`-equivariant a.e., so their dimensions are a.e. `T`-invariant.
* `restricted_inf_finrank_ae_eq` — for ergodic `T`, the restricted dimension profile
  `i ↦ finrank (W ⊓ V i)` is a.e. a deterministic **antitone** sequence `m` (not strictly:
  `W` may capture the same dimension at consecutive ambient levels — honest sub-multiplicity).
* `restricted_flag_structure_ae` — the non-strict `Fin (k+1)`-indexed flag `i ↦ W ⊓ V i` a.e.
  runs from `W` (level `0`) to `⊥` (level `last k`), is equivariant and antitone, with exact
  growth rate `lam i` on each non-strict stratum.
* `restricted_strict_filtration` — collapsing the constant-dimension levels (via the
  first-occurrence `survivingSet` of `m`, enumerated by `Finset.orderEmbOfFin`) yields a genuine
  **strict** Oseledets filtration realized inside `W`: a `StrictAnti` exponent list `lam'`, an
  everywhere-measurable strictly descending equivariant flag from `W` to `⊥` with exact growth
  rates, and all levels `≤ W`.

**Honest packaging note.** The top level of the restricted strict flag is `W`, which equals the
ambient `⊤` only when `W = ⊤`. Since `IsOseledetsFiltration` hard-codes `V 0 = ⊤`, a strict
restricted flag with all levels `≤ W` for a *proper* subbundle cannot satisfy that predicate
(it would force `⊤ ≤ W`). `restricted_strict_filtration` therefore states the restricted
filtration content directly (top `= W`) rather than reusing `IsOseledetsFiltration`.

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
`Oseledets.IsOseledetsFiltration` and `vflag_equivariant`. -/
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
`lyapunovSpectrum A T x` consisting of the exponents realized by some nonzero vector of `W x`. -/
noncomputable def restrictedSpectrum (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x : X) : Finset ℝ :=
  open Classical in
  (lyapunovSpectrum A T x).filter
    (fun r => ∃ v : EuclideanSpace ℝ (Fin d), v ∈ W x ∧ v ≠ 0 ∧ lambdaBar A T x v = r)

/-- A value lies in the restricted spectrum iff it is in the ambient spectrum and realized by
a nonzero vector of `W x`. -/
theorem mem_restrictedSpectrum {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    {W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {x : X} {r : ℝ} :
    r ∈ restrictedSpectrum A T W x ↔
      r ∈ lyapunovSpectrum A T x ∧
        ∃ v : EuclideanSpace ℝ (Fin d), v ∈ W x ∧ v ≠ 0 ∧ lambdaBar A T x v = r := by
  classical
  rw [restrictedSpectrum, Finset.mem_filter]

/-- **The restricted spectrum is a subset of the ambient spectrum** (pointwise, no
hypotheses): every exponent realized inside `W x` is realized in the ambient space. -/
theorem restrictedSpectrum_subset (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x : X) :
    restrictedSpectrum A T W x ⊆ lyapunovSpectrum A T x := by
  classical
  exact Finset.filter_subset _ _

/-- Every nonzero vector of `W x` realizes an exponent of the restricted spectrum (under the
`IsUltrametricGrowth` hypothesis that makes the ambient spectrum well-behaved). -/
theorem lambdaBar_mem_restrictedSpectrum {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X}
    {W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} {x : X}
    (hx : IsUltrametricGrowth (lambdaBar A T x)) {v : EuclideanSpace ℝ (Fin d)}
    (hvW : v ∈ W x) (hv : v ≠ 0) :
    lambdaBar A T x v ∈ restrictedSpectrum A T W x :=
  (mem_restrictedSpectrum).mpr ⟨lambdaBar_mem_lyapunovSpectrum hx hv, v, hvW, hv, rfl⟩

variable [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **The restricted spectrum is a.e. a subset of the ambient spectrum.** This is immediate
from the pointwise `restrictedSpectrum_subset`; it is the a.e. form requested by the
blueprint. -/
theorem restrictedSpectrum_subset_ae (A : X → Matrix (Fin d) (Fin d) ℝ)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    ∀ᵐ x ∂μ, restrictedSpectrum A T W x ⊆ lyapunovSpectrum A T x :=
  Filter.Eventually.of_forall fun x => restrictedSpectrum_subset A T W x

/-! ### Dimension interlacing (sub-multiplicity bound)

The restricted multiplicities are bounded by the ambient multiplicities: at each flag level
`vflag A T x i`, the part captured by `W x` is the intersection `W x ⊓ vflag A T x i`, whose
dimension is at most that of the ambient level by `finrank` monotonicity. The honest
"interlacing" is that the restricted exponents form a sub-multiset of the ambient exponent
multiset. -/

omit [MeasurableSpace X] in
/-- **Dimension interlacing.** At each ambient flag level, the dimension captured by the
subbundle is at most the ambient dimension. -/
theorem restricted_finrank_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x : X)
    (i : Fin (specCard A T x + 1)) :
    Module.finrank ℝ (W x ⊓ vflag A T x i : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤
      Module.finrank ℝ (vflag A T x i) :=
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
    Module.finrank ℝ (W x ⊓ vflag A T x i.castSucc : Submodule ℝ (EuclideanSpace ℝ (Fin d))) -
        Module.finrank ℝ (W x ⊓ vflag A T x i.succ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤
      Module.finrank ℝ (vflag A T x i.castSucc) - Module.finrank ℝ (vflag A T x i.succ) := by
  set Vc := vflag A T x i.castSucc with hVc
  set Vs := vflag A T x i.succ with hVs
  have hVle : Vs ≤ Vc := (vflag_strictAnti hx i).le
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
(by `InvariantSubbundle.invariant_ae`) and the sublevels (by `vflag_equivariant`) are
equivariant. Indexing by a real threshold `t` (rather than by `Fin (specCard …)`) sidesteps
the index-type transport `specCard A T x = specCard A T (T x)`; the flag levels `vflag A T x i`
on the interior are exactly such sublevels (`vflag_of_lt`).

Hence the restricted multiplicities `finrank (W ⊓ lambdaSublevel … t)` are a.e. `T`-invariant.
Their a.e. *constancy* by ergodicity is deferred — see the module docstring: it needs
`MeasurableSubspace.inf`, which is not yet available. -/

/-- **`A`-equivariance of the restricted sublevels (a.e.).** For a.e. `x` and every threshold
`t`, the action of `A x` maps the restricted sublevel `W x ⊓ lambdaSublevel A T x t` onto
`W (T x) ⊓ lambdaSublevel A T (T x) t`. Since interior flag levels are sublevels
(`vflag_of_lt`), this is the equivariance of the restricted flag. -/
theorem restricted_inf_lambdaSublevel_equivariant [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (Wb : InvariantSubbundle μ T A) :
    ∀ᵐ x ∂μ, ∀ t : ℝ,
      Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap
          (Wb.W x ⊓ lambdaSublevel A T x t) =
        Wb.W (T x) ⊓ lambdaSublevel A T (T x) t := by
  filter_upwards [vflag_equivariant hT hA hAmeas hint hint', Wb.invariant_ae] with x hflag hW
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

/-! ### Stage (ii): the full restricted Oseledets filtration

Intersecting the invariant subbundle `W` with the **forward Oseledets witness** `V` (the
everywhere-measurable family from `IsOseledetsFiltration`, *not* the a.e.-only `vflag`) gives a
`Fin (k+1)`-indexed non-strict flag `i ↦ W ⊓ V i`. By `MeasurableSubspace.inf` this is
everywhere measurable, and it inherits equivariance, a.e. constancy of dimensions, and the
exact growth clause. Collapsing the levels where the dimension does not drop produces a *strict*
flag, which is a genuine `IsOseledetsFiltration` whose levels lie inside `W`. -/

/-- **(A) Measurability of the restricted level `W ⊓ V i`.** For an everywhere-measurable
forward witness family `V`, the intersection with the subbundle `W` is everywhere measurable
(via `MeasurableSubspace.inf`). -/
theorem restricted_inf_measurableSubspace {A : X → Matrix (Fin d) (Fin d) ℝ} {k : ℕ}
    {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (Wb : InvariantSubbundle μ T A) (hVmeas : ∀ i, MeasurableSubspace fun x => V i x)
    (i : Fin (k + 1)) :
    MeasurableSubspace fun x => Wb.W x ⊓ V i x :=
  MeasurableSubspace.inf Wb.meas (hVmeas i)

/-- **Equivariance of the restricted level `W ⊓ V i` (a.e.).** Mirrors
`restricted_inf_lambdaSublevel_equivariant`, but intersecting with the equivariant forward
witness `V` of an `IsOseledetsFiltration` instead of with the sublevels. -/
theorem restricted_inf_witness_equivariant
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0)
    {k : ℕ} {lam : Fin k → ℝ}
    {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (Wb : InvariantSubbundle μ T A) (hV : IsOseledetsFiltration μ T A k lam V) :
    ∀ᵐ x ∂μ, ∀ i : Fin (k + 1),
      Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap
          (Wb.W x ⊓ V i x) =
        Wb.W (T x) ⊓ V i (T x) := by
  filter_upwards [hV.2.2, Wb.invariant_ae] with x hx hW
  intro i
  have hVeq := hx.2.2.2.1 i
  -- injectivity of the action of `A x`
  have hinj : Function.Injective
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
        = Matrix.toEuclideanLin (A x) :=
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (A x)
    rw [h1]; exact injective_toEuclideanLin (hA x)
  rw [Submodule.map_inf _ hinj, hW, hVeq]

/-- **A.e. `T`-invariance of the restricted level dimension `finrank (W ⊓ V i)`.** Mirrors
`restricted_finrank_invariant_ae`, intersecting with the forward witness `V`. -/
theorem restricted_inf_witness_finrank_invariant_ae
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0)
    {k : ℕ} {lam : Fin k → ℝ}
    {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (Wb : InvariantSubbundle μ T A) (hV : IsOseledetsFiltration μ T A k lam V) :
    ∀ᵐ x ∂μ, ∀ i : Fin (k + 1),
      Module.finrank ℝ (Wb.W (T x) ⊓ V i (T x)
          : Submodule ℝ (EuclideanSpace ℝ (Fin d))) =
        Module.finrank ℝ (Wb.W x ⊓ V i x
          : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
  filter_upwards [restricted_inf_witness_equivariant hA Wb hV] with x hx i
  have hinj : Function.Injective
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
        = Matrix.toEuclideanLin (A x) :=
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (A x)
    rw [h1]; exact injective_toEuclideanLin (hA x)
  have heq := (Submodule.equivMapOfInjective _ hinj (Wb.W x ⊓ V i x)).finrank_eq
  rw [← hx i]
  exact heq.symm

/-- **(B) A.e.-constant restricted level dimensions.** For ergodic `T`, the restricted
multiplicity profile `i ↦ finrank (W ⊓ V i)` is a.e. equal to a deterministic antitone
sequence `m : Fin (k+1) → ℕ`. Antitone (not strictly: `W` may capture the same dimension at
consecutive levels — honest sub-multiplicity). -/
theorem restricted_inf_finrank_ae_eq [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0)
    {k : ℕ} {lam : Fin k → ℝ}
    {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (Wb : InvariantSubbundle μ T A) (hV : IsOseledetsFiltration μ T A k lam V) :
    ∃ m : Fin (k + 1) → ℕ, Antitone m ∧
      ∀ᵐ x ∂μ, ∀ i, Module.finrank ℝ (Wb.W x ⊓ V i x
        : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = m i := by
  -- a.e. `T`-invariance of each level dimension (from equivariance)
  have hinv : ∀ i : Fin (k + 1),
      (fun x => Module.finrank ℝ (Wb.W x ⊓ V i x
        : Submodule ℝ (EuclideanSpace ℝ (Fin d)))) ∘ T
        =ᵐ[μ] fun x => Module.finrank ℝ (Wb.W x ⊓ V i x
          : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
    intro i
    filter_upwards [restricted_inf_witness_finrank_invariant_ae hA Wb hV] with x hx
    exact hx i
  -- measurability of each level dimension (via the trace of the orthogonal projector)
  have hmeas : ∀ i : Fin (k + 1),
      Measurable fun x => Module.finrank ℝ (Wb.W x ⊓ V i x
        : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :=
    fun i => (restricted_inf_measurableSubspace Wb hV.2.1 i).measurable_finrank
  -- ergodic constancy of the (measurable, invariant) dimension
  have hm : ∀ i : Fin (k + 1),
      ∃ c : ℕ, (fun x => Module.finrank ℝ (Wb.W x ⊓ V i x
        : Submodule ℝ (EuclideanSpace ℝ (Fin d)))) =ᵐ[μ] fun _ => c := fun i =>
    hT.ae_eq_const_of_ae_eq_comp₀ (hmeas i).nullMeasurable (hinv i)
  choose m hm using hm
  have hae : ∀ᵐ x ∂μ, ∀ i, Module.finrank ℝ (Wb.W x ⊓ V i x
      : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = m i := ae_all_iff.mpr hm
  refine ⟨m, ?_, hae⟩
  -- antitone from a single good point with the strict ambient flag
  obtain ⟨x₀, hx₀, hc₀⟩ := (hV.2.2.and hae).exists
  obtain ⟨-, -, hltx, -, -⟩ := hx₀
  have hanti : Antitone fun j => V j x₀ := (Fin.strictAnti_iff_succ_lt.mpr hltx).antitone
  intro a b hab
  rw [← hc₀ a, ← hc₀ b]
  exact Submodule.finrank_mono (inf_le_inf_left _ (hanti hab))

/-- **The restricted non-strict flag structure (a.e.).** The `Fin (k+1)`-indexed family
`i ↦ W ⊓ V i` (intersection of the subbundle with the forward Oseledets witness) is everywhere
measurable, and a.e. forms an `A`-equivariant antitone flag from `W` (level `0`) to `⊥`
(level `last k`), on which every vector of stratum `i` (in `W ⊓ V i.castSucc` but not in
`W ⊓ V i.succ`) grows at the exact rate `lam i`. This is the non-strict precursor of the
restricted Oseledets filtration; collapsing the constant-dimension levels turns it into a
strict flag (`restricted_strict_filtration`). -/
theorem restricted_flag_structure_ae
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0)
    {k : ℕ} {lam : Fin k → ℝ}
    {V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (Wb : InvariantSubbundle μ T A) (hV : IsOseledetsFiltration μ T A k lam V) :
    (∀ i, MeasurableSubspace fun x => Wb.W x ⊓ V i x) ∧
    ∀ᵐ x ∂μ,
      Wb.W x ⊓ V 0 x = Wb.W x ∧
      Wb.W x ⊓ V (Fin.last k) x = ⊥ ∧
      Antitone (fun i => Wb.W x ⊓ V i x) ∧
      (∀ i : Fin (k + 1),
        Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap
            (Wb.W x ⊓ V i x) = Wb.W (T x) ⊓ V i (T x)) ∧
      (∀ i : Fin k, ∀ v ∈ (Wb.W x ⊓ V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
          v ∉ Wb.W x ⊓ V i.succ x →
          Tendsto
            (fun n : ℕ => (n : ℝ)⁻¹ *
              Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
            atTop (𝓝 (lam i))) := by
  refine ⟨fun i => restricted_inf_measurableSubspace Wb hV.2.1 i, ?_⟩
  filter_upwards [hV.2.2, restricted_inf_witness_equivariant hA Wb hV] with x hx hequiv
  obtain ⟨htop, hbot, hltx, -, hgrow⟩ := hx
  have hanti : Antitone fun j => V j x := (Fin.strictAnti_iff_succ_lt.mpr hltx).antitone
  refine ⟨?_, ?_, ?_, hequiv, ?_⟩
  · rw [htop, inf_top_eq]
  · rw [hbot, inf_bot_eq]
  · exact fun a b hab => inf_le_inf_left _ (hanti hab)
  · intro i v hvmem hvnot
    -- `v ∈ W ⊓ V i.castSucc`, so `v ∈ V i.castSucc` and `v ∈ W`
    have hvmem' : v ∈ Wb.W x ⊓ V i.castSucc x := hvmem
    obtain ⟨hvW, hvV⟩ := Submodule.mem_inf.mp hvmem'
    -- `v ∉ W ⊓ V i.succ` together with `v ∈ W` forces `v ∉ V i.succ`
    have hvnotV : v ∉ V i.succ x := fun h => hvnot (Submodule.mem_inf.mpr ⟨hvW, h⟩)
    exact hgrow i v hvV hvnotV

/-! ### Level-collapse of an antitone profile to a strict flag

Reindexing infrastructure for `restricted_strict_filtration`. Given the antitone dimension
profile `m : Fin (k+1) → ℕ` of the non-strict restricted flag, the *surviving levels* are the
first-occurrence indices of each distinct value (`survivingSet`). Enumerating them in order via
`Finset.orderEmbOfFin` selects a strictly nested subflag. -/

/-- The **surviving index set** of an antitone profile `m`: the indices `i` whose value is
strictly smaller than every earlier value (equivalently, the first occurrence of each distinct
value of `m`). These index the strict-flag levels. -/
private def survivingSet {k : ℕ} (m : Fin (k + 1) → ℕ) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun i => ∀ j, j < i → m i < m j)

private theorem mem_survivingSet {k : ℕ} {m : Fin (k + 1) → ℕ} {i : Fin (k + 1)} :
    i ∈ survivingSet m ↔ ∀ j, j < i → m i < m j := by
  classical
  rw [survivingSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- `0` always survives (no earlier index). -/
private theorem zero_mem_survivingSet {k : ℕ} (m : Fin (k + 1) → ℕ) :
    (0 : Fin (k + 1)) ∈ survivingSet m :=
  mem_survivingSet.mpr fun j hj => absurd hj (Fin.not_lt_zero j)

/-- The first occurrence of any value `m i` survives. -/
private theorem firstOccurrence_mem_survivingSet {k : ℕ} {m : Fin (k + 1) → ℕ}
    (hm : Antitone m) (i : Fin (k + 1))
    (hfirst : ∀ j, j < i → m j ≠ m i) : i ∈ survivingSet m :=
  mem_survivingSet.mpr fun j hj =>
    lt_of_le_of_ne (hm hj.le) (fun h => hfirst j hj h.symm)

/-- The surviving set is nonempty (it contains `0`). -/
private theorem survivingSet_nonempty {k : ℕ} (m : Fin (k + 1) → ℕ) :
    (survivingSet m).Nonempty := ⟨0, zero_mem_survivingSet m⟩

/-- The minimum of the surviving set is `0`. -/
private theorem survivingSet_min'_eq_zero {k : ℕ} (m : Fin (k + 1) → ℕ) :
    (survivingSet m).min' (survivingSet_nonempty m) = 0 :=
  le_antisymm (Finset.min'_le _ _ (zero_mem_survivingSet m)) (Fin.zero_le _)

/-- An earlier index has a strictly larger value than a later *surviving* index. -/
private theorem survivingSet_lt_m {k : ℕ} {m : Fin (k + 1) → ℕ}
    {a b : Fin (k + 1)} (hb : b ∈ survivingSet m) (hlt : a < b) : m b < m a :=
  (mem_survivingSet.mp hb) a hlt

/-- **No surviving index lies strictly between consecutive enumeration points.** If `g`
enumerates the surviving set in order, then nothing of the surviving set lies strictly between
`g i.castSucc` and `g i.succ`. -/
private theorem survivingSet_no_mem_between {k k' : ℕ} {m : Fin (k + 1) → ℕ}
    (hcard : (survivingSet m).card = k' + 1) (i : Fin k')
    {p : Fin (k + 1)} (hp : p ∈ survivingSet m)
    (hlo : (survivingSet m).orderEmbOfFin hcard i.castSucc < p)
    (hhi : p < (survivingSet m).orderEmbOfFin hcard i.succ) : False := by
  -- `p` is in the range of the order embedding
  have hrange : p ∈ Set.range ((survivingSet m).orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin]; exact hp
  obtain ⟨j, rfl⟩ := hrange
  -- strict monotonicity transports the bounds to the index `j`
  have hmono := ((survivingSet m).orderEmbOfFin hcard).strictMono
  have h1 : i.castSucc < j := hmono.lt_iff_lt.mp hlo
  have h2 : j < i.succ := hmono.lt_iff_lt.mp hhi
  -- impossible: `i.castSucc + 1 = i.succ`
  rw [Fin.lt_def] at h1 h2
  simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
  omega

/-- **Interval constancy.** The profile `m` is constant on the half-open interval
`[g i.castSucc, g i.succ)`: any index `p` with `g i.castSucc ≤ p < g i.succ` has the same value
as `g i.castSucc`. -/
private theorem survivingSet_m_const_on_interval {k k' : ℕ} {m : Fin (k + 1) → ℕ}
    (hm : Antitone m) (hcard : (survivingSet m).card = k' + 1) (i : Fin k')
    {p : Fin (k + 1)} (hlo : (survivingSet m).orderEmbOfFin hcard i.castSucc ≤ p)
    (hhi : p < (survivingSet m).orderEmbOfFin hcard i.succ) :
    m p = m ((survivingSet m).orderEmbOfFin hcard i.castSucc) := by
  set g := (survivingSet m).orderEmbOfFin hcard with hg
  -- `≤` by antitone
  refine le_antisymm (hm hlo) ?_
  by_contra hlt'
  have hlt : m p < m (g i.castSucc) := not_le.mp hlt'
  -- let `i₁` be the first occurrence of value `m p`
  classical
  have hSne : (Finset.univ.filter (fun j : Fin (k + 1) => m j = m p)).Nonempty :=
    ⟨p, by simp⟩
  set i₁ := (Finset.univ.filter (fun j : Fin (k + 1) => m j = m p)).min' hSne with hi₁
  have hi₁mem : m i₁ = m p := by
    have h := Finset.min'_mem _ hSne
    rw [Finset.mem_filter] at h
    exact h.2
  have hi₁first : ∀ j, j < i₁ → m j ≠ m i₁ := by
    intro j hj hmj
    have : i₁ ≤ j :=
      Finset.min'_le _ j (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hmj, hi₁mem]⟩)
    exact absurd (lt_of_lt_of_le hj this) (lt_irrefl _)
  have hi₁surv : i₁ ∈ survivingSet m := firstOccurrence_mem_survivingSet hm i₁ hi₁first
  -- `i₁ ≤ p` since `i₁` is the minimal index with that value
  have hi₁le : i₁ ≤ p := Finset.min'_le _ p (by simp)
  -- `g i.castSucc < i₁`: otherwise antitone forces `m (g i.castSucc) ≤ m i₁ = m p`, contradiction
  have hgcs_lt : g i.castSucc < i₁ := by
    by_contra hle'
    have hle : i₁ ≤ g i.castSucc := not_lt.mp hle'
    have := hm hle
    rw [hi₁mem] at this
    exact absurd this (not_le.mpr hlt)
  -- `i₁ < g i.succ` since `i₁ ≤ p < g i.succ`
  have hi₁lt : i₁ < g i.succ := lt_of_le_of_lt hi₁le hhi
  exact survivingSet_no_mem_between hcard i hi₁surv hgcs_lt hi₁lt

/-- **The maximum of the surviving set carries the bottom value.** If the profile vanishes at
the last index, then it vanishes at `max' (survivingSet m)` (the first occurrence of `0`). -/
private theorem survivingSet_m_max' {k : ℕ} {m : Fin (k + 1) → ℕ} (hm : Antitone m)
    (hlast : m (Fin.last k) = 0) :
    m ((survivingSet m).max' (survivingSet_nonempty m)) = 0 := by
  classical
  -- the first occurrence of value `0` survives, hence `≤ max'`
  have hSne : (Finset.univ.filter (fun j : Fin (k + 1) => m j = 0)).Nonempty :=
    ⟨Fin.last k, by simp [hlast]⟩
  set i₀ := (Finset.univ.filter (fun j : Fin (k + 1) => m j = 0)).min' hSne with hi₀
  have hi₀mem : m i₀ = 0 := by
    have h := Finset.min'_mem _ hSne
    rw [Finset.mem_filter] at h
    exact h.2
  have hi₀first : ∀ j, j < i₀ → m j ≠ m i₀ := by
    intro j hj hmj
    have : i₀ ≤ j := Finset.min'_le _ j (by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hmj, hi₀mem]⟩)
    exact absurd (lt_of_lt_of_le hj this) (lt_irrefl _)
  have hi₀surv : i₀ ∈ survivingSet m := firstOccurrence_mem_survivingSet hm i₀ hi₀first
  have hle : i₀ ≤ (survivingSet m).max' (survivingSet_nonempty m) :=
    Finset.le_max' _ _ hi₀surv
  -- antitone: `m max' ≤ m i₀ = 0`
  have := hm hle
  rw [hi₀mem] at this
  exact Nat.le_zero.mp this

/-! ### The full restricted Oseledets filtration (strict flag)

This is the full restricted (strict) Oseledets filtration: a genuine **strict** Oseledets
filtration realized *inside* the invariant subbundle `W`. Its top level is `W` (not the ambient
`⊤`), so it is the Oseledets filtration of the restricted sub-cocycle, with all levels lying in
`W`.

**Honest note on packaging.** The non-strict precursor `i ↦ W ⊓ V i` has `W ⊓ V 0 = W`. Hence
the top level of the strict restricted flag is `W`, which is `⊤` *only when `W = ⊤`*. The
project's `IsOseledetsFiltration` predicate hard-codes `V 0 = ⊤` (the ambient top), so a strict
flag with all levels `≤ W` for a *proper* subbundle `W` cannot satisfy `IsOseledetsFiltration`
(that would force `⊤ ≤ W`). The deliverable therefore states the restricted-filtration content
directly (top `= W`, strict descending flag to `⊥`, equivariance, exact growth rates, all
levels `≤ W`) rather than reusing `IsOseledetsFiltration`. -/

/-- **The full restricted (strict) Oseledets filtration.** Collapsing the constant-dimension
levels of the non-strict precursor `i ↦ W ⊓ V i` (via the first-occurrence `survivingSet` of its
antitone dimension profile, enumerated by `Finset.orderEmbOfFin`) yields a genuine **strict**
Oseledets filtration realized *inside* the invariant subbundle `W`. There is a `StrictAnti`
exponent list `lam' : Fin k' → ℝ` and an everywhere-measurable family `vprime` such that, `μ`-a.e.,
the flag `vprime` is strictly descending (`vprime i.succ x < vprime i.castSucc x`) from its top
level `vprime 0 x = W x` down to `vprime (last k') x = ⊥`, is `A`-equivariant, has exact growth
rate `lam' i` on each stratum, and has all levels lying inside `W` (`vprime i x ≤ W x`).

**Honest packaging note.** The top level of the restricted strict flag is `W`, which equals the
ambient `⊤` only when `W = ⊤`. Since `IsOseledetsFiltration` hard-codes `V 0 = ⊤`, a strict
restricted flag with all levels `≤ W` for a *proper* subbundle cannot satisfy that predicate
(it would force `⊤ ≤ W`). This theorem therefore states the restricted-filtration content
directly (top `= W`) rather than reusing `IsOseledetsFiltration`. -/
theorem restricted_strict_filtration [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (Wb : InvariantSubbundle μ T A) :
    ∃ (k' : ℕ) (lam' : Fin k' → ℝ)
      (vprime : Fin (k' + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam' ∧
      (∀ i, MeasurableSubspace fun x => vprime i x) ∧
      ∀ᵐ x ∂μ,
        vprime 0 x = Wb.W x ∧ vprime (Fin.last k') x = ⊥ ∧
        (∀ i : Fin k', vprime i.succ x < vprime i.castSucc x) ∧
        (∀ i : Fin (k' + 1),
          Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (vprime i x)
            = vprime i (T x)) ∧
        (∀ i : Fin k', ∀ v ∈ (vprime i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
            v ∉ vprime i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
              atTop (𝓝 (lam' i))) ∧
        (∀ i, vprime i x ≤ Wb.W x) := by
  classical
  -- forward Oseledets witness `(k, lam, V)`
  obtain ⟨k, lam, V, hV⟩ := oseledets_filtration' hT A hA hAmeas hint hint'
  -- antitone restricted dimension profile `m`
  obtain ⟨m, hmanti, hmae⟩ :=
    restricted_inf_finrank_ae_eq hT hA Wb hV
  -- structural a.e. facts of the non-strict flag
  obtain ⟨hUmeas, hUae⟩ := restricted_flag_structure_ae hA Wb hV
  -- `m (last k) = 0`, read off a single good point
  have hmlast : m (Fin.last k) = 0 := by
    obtain ⟨x₀, hx₀, hc₀⟩ := (hUae.and hmae).exists
    rw [← hc₀ (Fin.last k), hx₀.2.1, finrank_bot]
  -- the surviving set and its enumeration
  set S := survivingSet m with hS
  set k' := S.card - 1 with hk'
  have hSne : S.Nonempty := survivingSet_nonempty m
  have hcardpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hcard : S.card = k' + 1 := by rw [hk']; omega
  set g := S.orderEmbOfFin hcard with hg
  have hgmono : StrictMono g := (S.orderEmbOfFin hcard).strictMono
  have hgmem : ∀ i, g i ∈ S := fun i => S.orderEmbOfFin_mem hcard i
  -- minimum of `S` is `0`
  have hSmin : S.min' hSne = 0 := survivingSet_min'_eq_zero m
  -- `g 0 = 0` (minimum of `S` is `0`)
  have hg0 : g 0 = 0 := by
    rw [hg, show (0 : Fin (k' + 1)) = ⟨0, Nat.succ_pos k'⟩ from rfl,
      S.orderEmbOfFin_zero hcard (Nat.succ_pos k')]
    exact hSmin
  -- `g (last k') = max' S`
  have hglast : g (Fin.last k') = S.max' hSne := by
    rw [hg, show (Fin.last k') = ⟨k' + 1 - 1, Nat.sub_lt (Nat.succ_pos k') (Nat.succ_pos 0)⟩
      from Fin.ext (by simp), S.orderEmbOfFin_last hcard (Nat.succ_pos k')]
  -- for each ambient stratum slot of the strict flag, the lower bound `g i.succ ≥ 1`
  have hsucc_pos : ∀ i : Fin k', 0 < (g i.succ : ℕ) := by
    intro i
    have hlt : g i.castSucc < g i.succ := hgmono i.castSucc_lt_succ
    rw [Fin.lt_def] at hlt
    omega
  -- ambient stratum index just below `g i.succ`
  have hstrat_lt : ∀ i : Fin k', (g i.succ : ℕ) - 1 < k := by
    intro i
    have hle : (g i.succ : ℕ) ≤ k := by
      have := (g i.succ).isLt; omega
    have := hsucc_pos i; omega
  -- the data
  refine ⟨k', fun i => lam ⟨(g i.succ : ℕ) - 1, hstrat_lt i⟩,
    fun i x => Wb.W x ⊓ V (g i) x, ?_, ?_, ?_⟩
  · -- `StrictAnti lam'`
    intro a b hab
    refine hV.1 (?_ : (⟨(g a.succ : ℕ) - 1, hstrat_lt a⟩ : Fin k)
      < ⟨(g b.succ : ℕ) - 1, hstrat_lt b⟩)
    change (g a.succ : ℕ) - 1 < (g b.succ : ℕ) - 1
    -- `a < b ⟹ a.succ < b.succ ⟹ g a.succ < g b.succ`
    have hab' : a.succ < b.succ := by
      rw [Fin.lt_def, Fin.val_succ, Fin.val_succ]; exact Nat.succ_lt_succ (Fin.lt_def.mp hab)
    have hg' : g a.succ < g b.succ := hgmono hab'
    rw [Fin.lt_def] at hg'
    have := hsucc_pos a
    omega
  · -- measurability of each level
    intro i
    exact restricted_inf_measurableSubspace Wb hV.2.1 (g i)
  · -- the a.e. structural block
    filter_upwards [hUae, hmae] with x hx hcx
    obtain ⟨hUtop, -, hUanti, hUequiv, hUgrow⟩ := hx
    -- abbreviation for the non-strict level
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- top level: `W ⊓ V (g 0) = W ⊓ V 0 = W`
      show Wb.W x ⊓ V (g 0) x = Wb.W x
      rw [hg0]; exact hUtop
    · -- bottom level: `finrank (W ⊓ V (g (last k'))) = m (max' S) = 0`
      show Wb.W x ⊓ V (g (Fin.last k')) x = ⊥
      rw [← Submodule.finrank_eq_zero, hcx (g (Fin.last k')), hglast,
        survivingSet_m_max' hmanti hmlast]
    · -- strict descending
      intro i
      show Wb.W x ⊓ V (g i.succ) x < Wb.W x ⊓ V (g i.castSucc) x
      have hglt : g i.castSucc < g i.succ := hgmono i.castSucc_lt_succ
      refine Submodule.lt_of_le_of_finrank_lt_finrank
        (hUanti hglt.le) ?_
      rw [hcx (g i.succ), hcx (g i.castSucc)]
      exact survivingSet_lt_m (hgmem i.succ) hglt
    · -- equivariance
      intro i
      exact hUequiv (g i)
    · -- growth rates
      intro i v hvmem hvnot
      -- the ambient stratum index just below `g i.succ`
      set j : Fin k := ⟨(g i.succ : ℕ) - 1, hstrat_lt i⟩ with hj
      have hsp := hsucc_pos i
      have hglt : g i.castSucc < g i.succ := hgmono i.castSucc_lt_succ
      have hglt' := hglt; rw [Fin.lt_def] at hglt'
      -- coordinate values of the ambient stratum bounds
      have hjcv : (j.castSucc : ℕ) = (g i.succ : ℕ) - 1 := by rw [Fin.val_castSucc, hj]
      have hjsv : (j.succ : ℕ) = (g i.succ : ℕ) := by rw [Fin.val_succ, hj]; simp; omega
      -- `j.succ = g i.succ` as `Fin (k+1)`
      have hjsucc : j.succ = g i.succ := Fin.ext hjsv
      -- `g i.castSucc ≤ j.castSucc` and `j.castSucc < g i.succ` (interval bounds)
      have hjcs_lo : g i.castSucc ≤ j.castSucc := by
        rw [Fin.le_def, hjcv]; omega
      have hjcs_hi : j.castSucc < g i.succ := by
        rw [Fin.lt_def, hjcv]; omega
      -- interval constancy of `m`, transported to subspace equality
      have hmeq : m j.castSucc = m (g i.castSucc) :=
        survivingSet_m_const_on_interval hmanti hcard i hjcs_lo hjcs_hi
      have hUeq : Wb.W x ⊓ V (g i.castSucc) x = Wb.W x ⊓ V j.castSucc x := by
        refine (Submodule.eq_of_le_of_finrank_eq (hUanti hjcs_lo) ?_).symm
        rw [hcx j.castSucc, hcx (g i.castSucc), hmeq]
      -- membership transported to the ambient stratum `j`
      have hv1 : v ∈ Wb.W x ⊓ V j.castSucc x := by
        rw [← hUeq]; exact hvmem
      have hv2 : v ∉ Wb.W x ⊓ V j.succ x := by rw [hjsucc]; exact hvnot
      -- the rate is `lam j = lam' i`
      have := hUgrow j v hv1 hv2
      exact this
    · -- all levels lie in `W`
      intro i
      exact inf_le_left

end Oseledets
