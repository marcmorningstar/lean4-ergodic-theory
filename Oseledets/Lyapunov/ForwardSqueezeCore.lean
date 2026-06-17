/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ForwardSqueezeData

/-!
# Constructing `SqueezeData` for the Oseledets spectral upper bound

This file builds a constructor `SqueezeData.ofCore` that takes the analytic limit and
boundedness facts about the cocycle along the orbit of `x` as inputs, and discharges all
the remaining (arithmetic or boundedness-from-convergence) fields of `SqueezeData`. The
analytic inputs are thereby isolated as the only substantial obligations; everything
routine is closed here.

## Main results

* `Oseledets.SqueezeData.ofCore`: assemble a `SqueezeData` from the core analytic inputs
  (the volume/determinant limits, the tempered angle, the factorizations, the per-direction
  lower bounds, the restriction bound, and the boundedness facts).
* `Oseledets.spectral_upper_bound_of_core`: the per-vector spectral upper bound
  `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ`, obtained by composing `SqueezeData.ofCore` with
  `spectral_upper_bound_of_squeezeData`.
* `Oseledets.exists_dSum_tendsto_dExponent`: almost-everywhere convergence of the
  determinant exponent `(1/n) log |det A⁽ⁿ⁾|`, supplying the `hD` field of `SqueezeData`.
* `Oseledets.tendsto_angle_exponent_zero`: the tempered-angle input `hS`, derived from
  `L¹`-integrability of the positive log of the inverse splitting angle.

## References

* L. Arnold, *Random Dynamical Systems*, Springer, 1998, §3.4.
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS 50 (1979), 27–58.
* S. Filip, *Notes on the multiplicative ergodic theorem*,
  Ergodic Theory Dynam. Systems 39 (2019), 1153–1189.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- `IsCoboundedUnder (·≤·)` of a sequence follows from it being bounded below. -/
theorem isCoboundedUnder_le_of_boundedUnder_ge {f : ℕ → ℝ}
    (h : IsBoundedUnder (· ≥ ·) atTop f) : IsCoboundedUnder (· ≤ ·) atTop f :=
  h.isCoboundedUnder_le

/-! ## The determinant exponent `hD`

`sprod A T d n x = ∏_{i<d} σᵢ(A⁽ⁿ⁾) = |det A⁽ⁿ⁾|`, so the determinant exponent is the top
`Γ`-limit `Γ_d`. This is the cleanest concrete field: it follows directly from the ergodic
Kingman limit `tendsto_GammaK_of_integrableLogNorm` at `k = d`, with no frame geometry
involved. It is exposed here as `dExponent` and `exists_dSum_tendsto_dExponent`. -/

variable {μ : MeasureTheory.Measure X}

/-- The det-exponent sequence `D n = (1/n) log sprod_d` (= `(1/n) log|det A⁽ⁿ⁾|`). -/
noncomputable def dExponent (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) : ℕ → ℝ :=
  fun n => (n : ℝ)⁻¹ * Real.log (sprod A T d n x)

/-- For an ergodic `T` and an everywhere-invertible measurable cocycle generator with
integrable log-norms, the determinant exponent `(1/n) log sprod_d(A⁽ⁿ⁾) → Γ_d` for
`μ`-a.e. `x` (here `sprod_d = ∏ all σ = |det|`). This supplies the `hD` field of
`SqueezeData`, with `dSum := Γ_d`. -/
theorem exists_dSum_tendsto_dExponent [NeZero d] [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ dSum : ℝ, ∀ᵐ x ∂μ, Tendsto (dExponent A T x) atTop (𝓝 dSum) :=
  tendsto_GammaK_of_integrableLogNorm hT hA hAmeas hint hint' (le_refl d)

omit [MeasurableSpace X] in
/-- For `v ≠ 0` and an invertible cocycle (`det ≠ 0`), the per-vector growth `‖A⁽ⁿ⁾ v‖` is
strictly positive at every `n`. This supplies the `hMvpos` field of `SqueezeData`. -/
theorem norm_cocycle_apply_pos {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0)
    {x : X} {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) (n : ℕ) :
    0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
  rw [norm_pos_iff]
  have hdet : (cocycle A T n x).det ≠ 0 := det_cocycle_ne_zero hA n x
  intro h
  exact hv (injective_toEuclideanLin hdet (by rw [h, map_zero]))

/-! ## The tempered angle `hS` via `L¹`-temperedness

In general the image angle `sin∠(A⁽ⁿ⁾F, A⁽ⁿ⁾S)` between the fast and slow images converges
to a positive constant, not to `1`. In the autonomous case `S n = (1/n) log sin∠ → 0` simply
because `sin∠` is eventually bounded below by a positive constant. In the general ergodic
case, equivariance `A⁽ⁿ⁾S(x) = S(Tⁿx)` together with the forward fast limit `F` gives
`sin∠(A⁽ⁿ⁾F(x), A⁽ⁿ⁾S(x)) = θ(Tⁿx)` for a fixed splitting-angle function `θ : X → (0,1]`,
and `(1/n) log θ(Tⁿx) → 0` follows from the `L¹`-temperedness hypothesis `log(1/θ) ∈ L¹(μ)`
(see Arnold §3.4 and Ruelle), discharged by `tempering_posLog`. Fischer's inequality
`sin∠ ≤ 1` gives the upper side `θ ≤ 1`.

The lemma below derives `hS` from exactly this data: the equivariant representation
`S n = (1/n) log (θ(Tⁿx))`, the range `0 < θ ≤ 1`, and the temperedness `posLog(1/θ) ∈ L¹`. -/

/-- **The tempered angle from `L¹`-temperedness.** Suppose the angle sequence is the
orbit sample of a fixed splitting-angle function: `S n = (n)⁻¹ · log (θ (Tⁿ x))` with
`0 < θ y ≤ 1` for all `y`, and the temperedness `y ↦ posLog ((θ y)⁻¹) ∈ L¹(μ)`. Then for
`μ`-a.e. `x`, `S → 0`. This is the precise content of the tempered angle, the `hS` field
of `SqueezeData`. -/
theorem tendsto_angle_exponent_zero {μ : MeasureTheory.Measure X}
    (hT : MeasurePreserving T μ μ) {θ : X → ℝ}
    (hθpos : ∀ y, 0 < θ y) (hθle : ∀ y, θ y ≤ 1)
    (htemp : Integrable (fun y => Real.posLog ((θ y)⁻¹)) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (θ (T^[n] x))) atTop (𝓝 0) := by
  -- `tempering_posLog` on `g = 1/θ`: `(1/n) posLog((θ(Tⁿx))⁻¹) → 0`.
  have hbase := tempering_posLog hT htemp
  filter_upwards [hbase] with x hx
  -- `log (θ y) = - posLog ((θ y)⁻¹)` since `0 < θ y ≤ 1`.
  have hrep : ∀ n : ℕ, (n : ℝ)⁻¹ * Real.log (θ (T^[n] x))
      = - ((n : ℝ)⁻¹ * Real.posLog ((θ (T^[n] x))⁻¹)) := by
    intro n
    have hy : 0 < θ (T^[n] x) := hθpos _
    have hyle : θ (T^[n] x) ≤ 1 := hθle _
    have hlog_le : Real.log (θ (T^[n] x)) ≤ 0 := Real.log_nonpos hy.le hyle
    have : Real.posLog ((θ (T^[n] x))⁻¹) = - Real.log (θ (T^[n] x)) := by
      rw [Real.posLog, Real.log_inv]
      rw [max_eq_right (by linarith)]
    rw [this]; ring
  rw [show (0 : ℝ) = -0 from (neg_zero).symm]
  refine (Filter.Tendsto.neg ?_).congr (fun n => (hrep n).symm)
  exact hx

/-- **Core constructor for `SqueezeData`.**

Takes the analytic inputs (the volume/determinant limits, the tempered angle, the
factorizations, the per-direction lower bounds, the restriction bound, and the
Furstenberg–Kesten-type boundedness facts) and assembles them into a `SqueezeData`. Each
hypothesis is named after the field it supplies; the coboundedness field `hcobdd` is
derived from the lower-boundedness hypothesis `hMvlb`.

This constructor isolates exactly the analytic content of the spectral upper bound. -/
def SqueezeData.ofCore
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) (lamI : ℝ)
    (D VF VS S topS restS r : ℕ → ℝ) (dSum fSum restSum : ℝ)
    (hv : v ≠ 0)
    (hD : Tendsto D atTop (𝓝 dSum))
    (hVF : Tendsto VF atTop (𝓝 fSum))
    (hS : Tendsto S atTop (𝓝 0))
    (hfact : ∀ᶠ n in atTop, D n = VF n + VS n + S n)
    (hvolfact : ∀ᶠ n in atTop, VS n = topS n + restS n)
    (hsplit : dSum - fSum = lamI + restSum)
    (htop_lb : lamI ≤ liminf topS atTop)
    (hrest_lb : restSum ≤ liminf restS atTop)
    (htopS_eq : topS = fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n))
    (htopS_ub : IsBoundedUnder (· ≤ ·) atTop topS)
    (htopS_lb : IsBoundedUnder (· ≥ ·) atTop topS)
    (hrestS_ub : IsBoundedUnder (· ≤ ·) atTop restS)
    (hrestS_lb : IsBoundedUnder (· ≥ ·) atTop restS)
    (hrestrict : ∀ᶠ n in atTop,
      ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ≤ r n * ‖v‖)
    (hrnn : ∀ᶠ n in atTop, 0 ≤ r n)
    (hMvpos : ∀ᶠ n in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hMvlb : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    SqueezeData A T x v lamI where
  hv := hv
  D := D
  VF := VF
  VS := VS
  S := S
  topS := topS
  restS := restS
  r := r
  dSum := dSum
  fSum := fSum
  restSum := restSum
  hD := hD
  hVF := hVF
  hS := hS
  hfact := hfact
  hvolfact := hvolfact
  hsplit := hsplit
  htop_lb := htop_lb
  hrest_lb := hrest_lb
  htopS_eq := htopS_eq
  htopS_ub := htopS_ub
  htopS_lb := htopS_lb
  hrestS_ub := hrestS_ub
  hrestS_lb := hrestS_lb
  hrestrict := hrestrict
  hrnn := hrnn
  hMvpos := hMvpos
  hcobdd := isCoboundedUnder_le_of_boundedUnder_ge hMvlb

/-! ## The spectral upper bound from the core analytic inputs

Composing `SqueezeData.ofCore` with `spectral_upper_bound_of_squeezeData` gives the
spectral upper bound directly from the analytic inputs: once they are supplied, the
per-vector spectral upper bound `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ` follows with no
further work. -/

omit [MeasurableSpace X] in
/-- The per-vector spectral upper bound `limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ`, assembled from
the core analytic inputs via `SqueezeData.ofCore` and
`spectral_upper_bound_of_squeezeData`. -/
theorem spectral_upper_bound_of_core
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) (lamI : ℝ)
    (D VF VS S topS restS r : ℕ → ℝ) (dSum fSum restSum : ℝ)
    (hv : v ≠ 0)
    (hD : Tendsto D atTop (𝓝 dSum))
    (hVF : Tendsto VF atTop (𝓝 fSum))
    (hS : Tendsto S atTop (𝓝 0))
    (hfact : ∀ᶠ n in atTop, D n = VF n + VS n + S n)
    (hvolfact : ∀ᶠ n in atTop, VS n = topS n + restS n)
    (hsplit : dSum - fSum = lamI + restSum)
    (htop_lb : lamI ≤ liminf topS atTop)
    (hrest_lb : restSum ≤ liminf restS atTop)
    (htopS_eq : topS = fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n))
    (htopS_ub : IsBoundedUnder (· ≤ ·) atTop topS)
    (htopS_lb : IsBoundedUnder (· ≥ ·) atTop topS)
    (hrestS_ub : IsBoundedUnder (· ≤ ·) atTop restS)
    (hrestS_lb : IsBoundedUnder (· ≥ ·) atTop restS)
    (hrestrict : ∀ᶠ n in atTop,
      ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ≤ r n * ‖v‖)
    (hrnn : ∀ᶠ n in atTop, 0 ≤ r n)
    (hMvpos : ∀ᶠ n in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hMvlb : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lamI :=
  spectral_upper_bound_of_squeezeData
    (SqueezeData.ofCore A T x v lamI D VF VS S topS restS r dSum fSum restSum hv hD hVF hS
      hfact hvolfact hsplit htop_lb hrest_lb htopS_eq htopS_ub htopS_lb hrestS_ub hrestS_lb
      hrestrict hrnn hMvpos hMvlb)

end Oseledets
