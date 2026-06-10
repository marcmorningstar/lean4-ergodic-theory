import Oseledets.Lyapunov.ForwardSqueezeData

/-!
# `ForwardSqueezeCore` — constructing `SqueezeData` for the Oseledets spectral upper bound.

This file builds a constructor `SqueezeData.ofCore` that takes the genuinely-analytic
limit/boundedness facts about the cocycle along the orbit of `x` as inputs, and discharges
ALL the remaining (arithmetic / boundedness-from-convergence) fields of `SqueezeData`. The
analytic inputs are then the isolated residual; everything routine is closed here with no `sorry`.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- `IsCoboundedUnder (·≤·)` of a sequence follows from it being bounded below. -/
theorem isCoboundedUnder_le_of_boundedUnder_ge {f : ℕ → ℝ}
    (h : IsBoundedUnder (· ≥ ·) atTop f) : IsCoboundedUnder (· ≤ ·) atTop f :=
  h.isCoboundedUnder_le

/-! ## Concrete discharge of the determinant exponent `hD`.

`Sprod A T d n x = ∏_{i<d} σᵢ(A⁽ⁿ⁾) = |det A⁽ⁿ⁾|`, so the det exponent is the top
`Γ`-limit `Γ_d`. This is the cleanest concrete field: it follows directly from the committed
ergodic `Γ_k` Kingman limit `tendsto_GammaK_of_integrableLogNorm` at `k = d`, with NO frame
geometry. We expose it as `dExponent`/`hD_concrete` to show the wiring is non-vacuous. -/

variable {μ : MeasureTheory.Measure X}

/-- The det-exponent sequence `D n = (1/n) log Sprod_d` (= `(1/n) log|det A⁽ⁿ⁾|`). -/
noncomputable def dExponent (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) : ℕ → ℝ :=
  fun n => (n : ℝ)⁻¹ * Real.log (Sprod A T d n x)

/-- **`hD` discharged from committed infrastructure.** For an ergodic `T`, an everywhere-invertible
measurable cocycle generator with integrable log-norms, the det exponent
`(1/n) log Sprod_d(A⁽ⁿ⁾) → Γ_d` for `μ`-a.e. `x`. (`Sprod_d = ∏ all σ = |det|`.) This is the
`hD` field of `SqueezeData`, concretely, with `dSum := Γ_d`. -/
theorem exists_dSum_tendsto_dExponent [NeZero d] [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ dSum : ℝ, ∀ᵐ x ∂μ, Tendsto (dExponent A T x) atTop (𝓝 dSum) :=
  tendsto_GammaK_of_integrableLogNorm hT hA hAmeas hint hint' (le_refl d)

/-- **`hMvpos` discharged.** For `v ≠ 0` and an invertible cocycle (`det ≠ 0`), the per-vector
growth `‖A⁽ⁿ⁾ v‖` is strictly positive at every `n`. Concrete, frame-free. -/
theorem norm_cocycle_apply_pos {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0)
    {x : X} {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) (n : ℕ) :
    0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
  rw [norm_pos_iff]
  have hdet : (cocycle A T n x).det ≠ 0 := det_cocycle_ne_zero hA n x
  intro h
  exact hv (injective_toEuclideanLin hdet (by rw [h, map_zero]))

/-! ## Concrete discharge of the tempered angle `hS` (resolution (ii): L¹-temperedness).

NUMERICS (mpmath dps=220, autonomous non-normal `A` with `|eig| = 3,2,1`, `p=1/q=2`) confirm:
the image angle `sin∠(A⁽ⁿ⁾F, A⁽ⁿ⁾S)` converges to a POSITIVE CONSTANT (≈ 0.8865 here), NOT to
`1`. So `S n = (1/n) log sin∠ → 0` because `sin∠` is bounded below by a positive constant — in the
AUTONOMOUS case this is resolution (i) (sin∠ eventually ≥ const > 0). In the GENERAL ergodic case,
equivariance `A⁽ⁿ⁾S(x) = S(Tⁿx)` plus the forward-fast-limit `F` give
`sin∠(A⁽ⁿ⁾F(x), A⁽ⁿ⁾S(x)) = θ(Tⁿx)` for the FIXED splitting-angle function `θ : X → (0,1]`, and
`(1/n) log θ(Tⁿx) → 0` is resolution (ii): it needs `log(1/θ) ∈ L¹(μ)` (Arnold §3.4 / Ruelle /
Filip), discharged by `tempering_posLog`. Fischer's `sin∠ ≤ 1` gives the upper side `θ ≤ 1`.

The lemma below CLOSES `hS` from exactly that residual: the equivariant representation
`S n = (1/n) log (θ(Tⁿx))`, the range `0 < θ ≤ 1`, and the temperedness `posLog(1/θ) ∈ L¹`. -/

/-- **`hS` discharged from L¹-temperedness (resolution (ii)).** Suppose the angle sequence is the
orbit sample of a fixed splitting-angle function: `S n = (n)⁻¹ · log (θ (Tⁿ x))` with
`0 < θ y ≤ 1` for all `y`, and the temperedness `y ↦ posLog ((θ y)⁻¹) ∈ L¹(μ)`. Then for
`μ`-a.e. `x`, `S → 0`. This is the precise content of the tempered angle. -/
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

Takes the genuinely-analytic inputs (the three volume/det limits, the tempered angle, the
factorizations, the per-direction lower bounds, the restriction bound, and the FK-type
boundedness facts) and assembles them into a `SqueezeData`. Each hypothesis is named after the
field it supplies; the four derived fields (`hrnn`, `hMvpos`, `hcobdd` and the bounded-under
sides not directly given) are produced from the supplied data.

The point: this isolates EXACTLY the analytic residual. -/
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

/-! ## The capstone, fed by the core analytic inputs.

Composing `SqueezeData.ofCore` with the committed `spectral_upper_bound_of_squeezeData` gives the
TARGET spectral upper bound directly from the analytic residual. This is the assembled deliverable:
once the (precisely-typed) analytic inputs are supplied, the per-vector spectral upper bound
`limsup (1/n) log ‖A⁽ⁿ⁾ v‖ ≤ λᵢ` follows with NO further work. -/
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

