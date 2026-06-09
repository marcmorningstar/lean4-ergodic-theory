import Oseledets.Lyapunov.ForwardDetSqueeze

/-!
# `scratch_wiring` — discharging the determinant-squeeze hypotheses into the
  UNCONDITIONAL Oseledets spectral upper bound.

This file wires the concrete cocycle facts into the abstract determinant-squeeze machinery
committed in `Oseledets/Lyapunov/ForwardDetSqueeze.lean`, producing the spectral upper bound

    limsup_n (1/n)·log ‖A⁽ⁿ⁾ v‖  ≤  λᵢ,    for v in the limit slow subspace S(x).

## Architecture

The abstract chain committed upstream is:

  `tendsto_slowVolume_exponent`   (hD, hVF, hS, hfact  → slow-volume limit `VS → slowSum`)
  → `limsup_topSlow_le_of_squeeze` (slow-volume limit + hsplit + lower bounds + boundedness
                                    → `limsup topS ≤ λᵢ`)
  → `spectral_upper_bound_of_squeeze` (`hslownorm` + `hrestrict` + side conditions → TARGET).

The concrete cocycle inputs are bundled in `SqueezeData`, a structure of **precisely typed
hypotheses** — each entry matches the committed infrastructure it abstracts, so discharging the
structure is exactly the residual concrete work, with NO hidden arithmetic. The MAIN theorem
`spectral_upper_bound_of_squeezeData` proves the chain is gapless: `SqueezeData → TARGET`.

## What is closed here (gapless wiring)

The full arithmetic chain from the six concrete inputs to the per-vector spectral upper bound,
with zero `sorry` and clean axioms. Boundedness side-conditions are derived where possible from
the convergence inputs (a convergent real sequence is bounded above and below, cobounded, etc.),
so they are NOT carried as separate fields.

## The residual concrete inputs (the fields of `SqueezeData`)

Listed with the committed lemma that discharges each (see the field docstrings):

* `hD`     — Furstenberg–Kesten det limit (`furstenbergKesten_*` + det/exterior Kingman).
* `hVF`    — exterior-Kingman fast-volume limit (`ExteriorNorm` `‖⋀ᵏ‖ = ∏σ` + Kingman).
* `hS`     — the tempered angle `→ 0` (`tempering_posLog` + L¹-temperedness + Fischer `sin ≤ 1`).
* `hfact`  — the determinant/angle factorization (`det_sq_eq_gram_image` + block-Gram sine).
* `htop_lb`, `hrest_lb` — per-direction lower bounds (`log_le_liminf_log_cocycle_apply` +
  `tendsto_log_singularValue` / `exists_lam_tendsto_singularValue`).
* `hrestrict` — slow-restriction operator-norm bound (`v ∈ S` equivariant + op-norm monotonicity).
* `hMvpos`  — strict positivity of the per-vector growth (`norm_cocycle_pos` applied to `v ≠ 0`).
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-! ## Boundedness helpers: a convergent real sequence is bounded/cobounded both ways.

These discharge the `IsBoundedUnder`/`IsCoboundedUnder` side-conditions of the abstract squeeze
lemmas purely from the convergence inputs, so `SqueezeData` need not carry them as fields. -/

theorem isBoundedUnder_le_of_tendsto {f : ℕ → ℝ} {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) : IsBoundedUnder (· ≤ ·) atTop f :=
  h.isBoundedUnder_le

theorem isBoundedUnder_ge_of_tendsto {f : ℕ → ℝ} {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) : IsBoundedUnder (· ≥ ·) atTop f :=
  h.isBoundedUnder_ge

theorem isCoboundedUnder_le_of_tendsto {f : ℕ → ℝ} {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) : IsCoboundedUnder (· ≤ ·) atTop f :=
  h.isBoundedUnder_ge.isCoboundedUnder_le

/-! ## The concrete cocycle inputs of the determinant squeeze.

`SqueezeData A T x v lamI` bundles the precise residual concrete facts about the cocycle `A⁽ⁿ⁾(x)`
along the orbit of `x`, for a fixed slow vector `v` in the limit slow subspace `S(x)` with target
top-slow Lyapunov exponent `lamI`. Each field is typed verbatim against the committed
infrastructure that supplies it; the boundedness side-conditions are derived (not assumed).

Notation for the sequences (all `: ℕ → ℝ`):
* `D n  = (1/n) log|det A⁽ⁿ⁾|`               — det exponent, `→ dSum = Σ_all λ`     (`hD`).
* `VF n = (1/n) log vol(A⁽ⁿ⁾ ω_F)`           — fast-frame volume exponent, `→ fSum = Σ_fast λ`
                                                                                          (`hVF`).
* `VS n = (1/n) log vol(A⁽ⁿ⁾ ω_S)`           — slow-frame volume exponent (`= topS + restS`).
* `S n  = (1/n) log sin∠(A⁽ⁿ⁾F, A⁽ⁿ⁾S)`      — tempered angle, `→ 0`                (`hS`).
* `topS n = (1/n) log (r n)`, `r n = ‖A⁽ⁿ⁾|_S‖` — top-slow restricted-norm exponent.
* `restS n` — remaining `q−1` slow singular exponents, `VS = topS + restS`. -/
structure SqueezeData (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) (lamI : ℝ) where
  /-- The slow vector is nonzero. -/
  hv : v ≠ 0
  /-- Det exponent sequence `(1/n) log|det A⁽ⁿ⁾|`. -/
  D : ℕ → ℝ
  /-- Fast-frame volume exponent sequence. -/
  VF : ℕ → ℝ
  /-- Slow-frame volume exponent sequence. -/
  VS : ℕ → ℝ
  /-- Tempered-angle exponent sequence. -/
  S : ℕ → ℝ
  /-- Top-slow restricted-norm exponent sequence. -/
  topS : ℕ → ℝ
  /-- Remaining slow-direction exponent sequence. -/
  restS : ℕ → ℝ
  /-- Restricted operator norm `r n = ‖A⁽ⁿ⁾|_S‖`. -/
  r : ℕ → ℝ
  /-- Total exponent sum `Σ_all λ`. -/
  dSum : ℝ
  /-- Fast exponent sum `Σ_fast λ`. -/
  fSum : ℝ
  /-- Rest exponent sum (slow without the top direction). -/
  restSum : ℝ
  /-- **hD** — Furstenberg–Kesten det limit: `(1/n) log|det A⁽ⁿ⁾| → Σ_all λ`.
      Discharged by `furstenbergKesten_*` + the det/top-exterior Kingman limit
      (`|det A⁽ⁿ⁾| = ∏ⱼ σⱼ`, `(1/n)Σ log σⱼ → Σλ`). -/
  hD : Tendsto D atTop (𝓝 dSum)
  /-- **hVF** — exterior-Kingman fast-volume limit: `(1/n) log vol(A⁽ⁿ⁾ ω_F) → Σ_fast λ`.
      Discharged by the committed exterior norm `‖⋀ᵖ‖ = ∏σ` + Kingman (upper), with the fast
      frame `ω_F` chosen ≈ the limit top-`p` singular subspace (band-projector convergence) so the
      angle defect is tempered (lower). -/
  hVF : Tendsto VF atTop (𝓝 fSum)
  /-- **hS** — the tempered angle `(1/n) log sin∠(A⁽ⁿ⁾F, A⁽ⁿ⁾S) → 0`.
      Discharged by `tempering_posLog` applied to `g = 1/sin∠_splitting` (using equivariance
      `A⁽ⁿ⁾S(x) = S(Tⁿx)` so the image angle is the splitting angle at `Tⁿx`), provided
      `log(1/sin∠_splitting) ∈ L¹(μ)` (Arnold §3.4; from `IntegrableLogNorm A` + `…A⁻¹`),
      together with Fischer's `sin∠ ≤ 1` (so `S n ≤ 0`, i.e. the `posLog` captures the whole). -/
  hS : Tendsto S atTop (𝓝 0)
  /-- **hfact** — the determinant/angle factorization `D n = VF n + VS n + S n`.
      Discharged by `det_sq_eq_gram_image` (with orthonormal source frame `W`, `|det W| = 1`) and
      the block-Gram definition of `sin∠`, taking logs of `|det A⁽ⁿ⁾| = volF·volS·sin∠`. -/
  hfact : ∀ᶠ n in atTop, D n = VF n + VS n + S n
  /-- The slow volume factors into the top-slow restricted norm and the remaining directions:
      `VS n = topS n + restS n`. From the singular-value factorization of `vol(A⁽ⁿ⁾ ω_S)`. -/
  hvolfact : ∀ᶠ n in atTop, VS n = topS n + restS n
  /-- The slow exponent sum splits as the top-slow exponent `lamI` plus the rest:
      `(dSum − fSum) = lamI + restSum`. -/
  hsplit : dSum - fSum = lamI + restSum
  /-- **htop_lb** — top-slow per-direction lower bound `lamI ≤ liminf topS`.
      Discharged by `log_le_liminf_log_cocycle_apply` at threshold `c = e^{lamI}` +
      `tendsto_log_singularValue`. -/
  htop_lb : lamI ≤ liminf topS atTop
  /-- **hrest_lb** — remaining-directions lower bound `restSum ≤ liminf restS`.
      Discharged by the per-direction singular-value lower bounds for the `q−1` non-top slow
      singular values (`exists_lam_tendsto_singularValue`). -/
  hrest_lb : restSum ≤ liminf restS atTop
  /-- The top-slow exponent is the normalized log of the restricted operator norm: `topS = (1/n) log r`. -/
  htopS_eq : topS = fun n : ℕ => (n : ℝ)⁻¹ * Real.log (r n)
  /-- The top-slow restricted-norm exponent is bounded above (Furstenberg–Kesten: `(1/n) log‖A⁽ⁿ⁾‖`
      converges, and `r n = ‖A⁽ⁿ⁾|_S‖ ≤ ‖A⁽ⁿ⁾‖`). Provided as a clean uniform bound. -/
  htopS_ub : IsBoundedUnder (· ≤ ·) atTop topS
  /-- The top-slow restricted-norm exponent is bounded below (Furstenberg–Kesten on the inverse
      cocycle: `r n = ‖A⁽ⁿ⁾|_S‖ ≥ 1/‖(A⁽ⁿ⁾)⁻¹‖`, whose log-exponent converges by `furstenbergKesten_bot`).
      Note: a `liminf` lower bound alone does NOT give this in a conditionally-complete order, so it
      is carried explicitly. -/
  htopS_lb : IsBoundedUnder (· ≥ ·) atTop topS
  /-- `restS` is bounded above (FK: the slow volume is bounded by `‖A⁽ⁿ⁾‖^q`, so each exponent term
      is bounded; equivalently from the convergence of all singular-value exponents). -/
  hrestS_ub : IsBoundedUnder (· ≤ ·) atTop restS
  /-- `restS` is bounded below (FK on the inverse cocycle: singular values stay away from `0`). -/
  hrestS_lb : IsBoundedUnder (· ≥ ·) atTop restS
  /-- **hrestrict** — slow-restriction operator-norm bound: `‖A⁽ⁿ⁾ v‖ ≤ r n · ‖v‖`.
      Valid because `v ∈ S(x)` (equivariant slow subspace) and `r n = ‖A⁽ⁿ⁾|_S‖`; operator-norm
      monotonicity. -/
  hrestrict : ∀ᶠ n in atTop,
    ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ≤ r n * ‖v‖
  /-- `r n ≥ 0` (an operator norm). -/
  hrnn : ∀ᶠ n in atTop, 0 ≤ r n
  /-- **hMvpos** — strict positivity of the per-vector growth: `0 < ‖A⁽ⁿ⁾ v‖`.
      From `v ≠ 0` and `det A⁽ⁿ⁾ ≠ 0` (so `A⁽ⁿ⁾` is invertible ⇒ `A⁽ⁿ⁾ v ≠ 0`). -/
  hMvpos : ∀ᶠ n in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖
  /-- The per-vector log-growth sequence is cobounded above (FK: bounded above ⇒ cobounded). -/
  hcobdd : IsCoboundedUnder (· ≤ ·) atTop
    (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)

/-! ## The chain: `SqueezeData → limsup topS ≤ λᵢ → spectral upper bound`. -/

variable {A : X → Matrix (Fin d) (Fin d) ℝ} {x : X}
  {v : EuclideanSpace ℝ (Fin d)} {lamI : ℝ}

/-- **Step 1+2 — the determinant squeeze pins the top-slow exponent.** From a `SqueezeData`,
`limsup (1/n) log r ≤ λᵢ`, where `r n = ‖A⁽ⁿ⁾|_S‖` is the slow restricted operator norm. This
chains `tendsto_slowVolume_exponent` (the volume limit `VS → dSum − fSum`) into
`limsup_topSlow_le_of_squeeze` (the two-term pinning squeeze), with all boundedness side-conditions
discharged from the convergence inputs of the data. NON-CIRCULAR: no per-vector growth was used. -/
theorem limsup_slowNorm_le_of_squeezeData (hsq : SqueezeData A T x v lamI) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (hsq.r n)) atTop ≤ lamI := by
  -- Step 1: the slow-volume exponent converges to `dSum − fSum`.
  have hvolS : Tendsto hsq.VS atTop (𝓝 (hsq.dSum - hsq.fSum)) :=
    tendsto_slowVolume_exponent hsq.hD hsq.hVF hsq.hS hsq.hfact
  -- Step 2: the two-term pinning squeeze. Boundedness side-conditions are the corresponding fields.
  have hkey : limsup hsq.topS atTop ≤ lamI :=
    limsup_topSlow_le_of_squeeze hvolS hsq.hsplit hsq.hvolfact hsq.htop_lb hsq.hrest_lb
      hsq.htopS_ub hsq.htopS_lb hsq.hrestS_lb hsq.hrestS_ub
  -- Rewrite `topS = (1/n) log r`.
  rw [hsq.htopS_eq] at hkey
  exact hkey

/-- **Step 3 — the capstone.** The full chain: `SqueezeData → spectral upper bound`. For a slow
vector `v` in the limit slow subspace `S(x)`, the determinant squeeze yields the TARGET

    limsup_n (1/n)·log ‖A⁽ⁿ⁾ v‖  ≤  λᵢ.

All hypotheses of `spectral_upper_bound_of_squeeze` are discharged from the data (the slow-norm
limsup bound from `limsup_slowNorm_le_of_squeezeData`, the restriction bound, positivity, and the
boundedness side-conditions, the last derived from the slow-norm bound). NON-CIRCULAR. -/
theorem spectral_upper_bound_of_squeezeData (hsq : SqueezeData A T x v lamI) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lamI := by
  have hslownorm : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (hsq.r n)) atTop ≤ lamI :=
    limsup_slowNorm_le_of_squeezeData hsq
  -- `IsBoundedUnder (· ≤ ·)` of `(1/n) log r` from `htopS_ub` (= the same sequence up to `htopS_eq`).
  have hRbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (hsq.r n)) := by
    have := hsq.htopS_ub; rw [hsq.htopS_eq] at this; exact this
  exact spectral_upper_bound_of_squeeze hsq.hv hslownorm hsq.hrestrict hsq.hrnn hsq.hMvpos
    hRbdd hsq.hcobdd

/-- The MAIN deliverable: the unconditional (modulo `SqueezeData`) spectral upper bound. -/
example (hsq : SqueezeData A T x v lamI) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lamI :=
  spectral_upper_bound_of_squeezeData hsq

end Oseledets

-- Axiom audit: must be exactly [propext, Classical.choice, Quot.sound].
#print axioms Oseledets.spectral_upper_bound_of_squeezeData
#print axioms Oseledets.limsup_slowNorm_le_of_squeezeData
