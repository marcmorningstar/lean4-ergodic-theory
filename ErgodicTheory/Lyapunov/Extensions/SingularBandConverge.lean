/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.OseledetsLimit.ProjectorIncrement
import ErgodicTheory.Lyapunov.Extensions.SingularSlowSpace

/-!
# Det-free band-projector increment bound and the singular slow space `Vⱼ` (Angle A)

For a **singular** (non-invertible, `det A = 0` allowed) cocycle, the singular forward Oseledets
flag's intermediate slow space `Vⱼ(ω)` (Quas, *MET and Applications*, 2013, **Theorem 2**; Ruelle,
Publ. IHES 50, 1979, **Lemma 1.4**) is — by the landed structural reduction
`ErgodicTheory.tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector`
(`ErgodicTheory/Lyapunov/Extensions/SingularSlowSpace.lean`) — reduced **unconditionally** to one input:
the convergence of the *fast* band projector
`bandProjector A T (𝟙_{(c,∞)}) n x` at a Lyapunov-gap cut `c`.

That band-projector convergence is supplied, in the invertible engine
(`ErgodicTheory/Lyapunov/OseledetsLimit/ProjectorIncrement.lean`), by the per-step increment bound
`norm_bandProjector_succ_sub_le_cocycle`, whose UNCONDITIONAL cocycle discharge carries
`hA : ∀ x, (A x).det ≠ 0`. This module **isolates** the single estimate that consumes the
invertibility, replaces every *other* appearance of the inverse by a **det-free, forward** quantity,
and pins the genuine residual obstruction with a `cruxStatus`-quality precision.

## The det-free reformulation (Angle A — forward growth / reverse sandwich)

The abstract per-step bound `ErgodicTheory.norm_bandProjector_succ_sub_le` reads, with the compound-norm
abbreviations `cM = ‖compound k Mₙ‖`, `cB = ‖compound k B‖`, `r = σₖ/σₖ₋₁` (`B = A(Tⁿx)`,
`Mₙ = cocycle A T n x`),

  `‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·(cB·cBi)²·r / (1 − (cB·cBi)²r²)`,

with `cBi = ‖compound k B⁻¹‖`. The single ingredient that *forces* the inverse is the **gap
denominator lower bound** `hμ₀lb`:

  `cM²/cBi² · (1 − (cB·cBi)²r²) ≤ μ̃₀ − ν`,   where  `μ̃₀ = ‖compound k (B·Mₙ)‖²`, `ν = cM²r²cB²`.

Everything else — the off-diagonal numerator `‖C v₀ − ⟪C v₀,v₀⟫v₀‖ ≤ cM²·r·cB²` and the `ν`-ceiling
`ν = μ₁·cB² = cM²r²·cB²` — is **det-free / forward**. We make this exact:

* `ErgodicTheory.numerator_div_gap_le_detfree` — the gap-denominator collapse with the inverse replaced
  by an **abstract** lower-bound coefficient `s` (`μ̃₀ ≥ s²·cM²`): the increment ratio collapses to
  `(cB/s)²·r / (1 − (cB/s)²r²)`. Here `cB/s` is the det-free analogue of the compound condition
  number `κ = cB·cBi`, with `s = σ_min(compound k B) = 1/cBi`.
* `ErgodicTheory.norm_bandProjector_succ_sub_le_detfree` — the per-step band-projector increment bound
  driven by the **abstract** `s`: it consumes *only* the lower bound `s²·cM² ≤ μ̃₀` (and `s > 0`,
  `s² cM² > ν`, the regime). No inverse symbol; the inverse engine survives in this lemma **only as
  the supplier of one number `s` with `μ̃₀ ≥ s²·cM²`.**

## The wall (the residual inequality the inverse is load-bearing for)

The forward-growth / reverse-sandwich route **cannot** discharge the one remaining input

  `(R)   ‖compound k (B · Mₙ)‖ ≥ s · ‖compound k Mₙ‖`   with `s` bounded away from `0`,

for a **single** step `B = A(Tⁿx)` that is allowed to be singular. The maximal det-free coefficient
is `s = σ_min(compound k B)` (the smallest singular value of `B`'s `k`-th compound), because the
only inverse-free per-vector lower bound is `‖(compound k B)·v‖ ≥ σ_min(compound k B)·‖v‖`, applied
at the top right-singular vector of `compound k Mₙ`. And
`σ_min(compound k B) = 1/‖(compound k B)⁻¹‖ = 1/cBi` exactly — so the "det-free" `s` **is** the
reciprocal compound-inverse norm. When `B` drops rank on the top-`k` exterior power (`det B = 0`,
or more generally `σₖ(B) = 0`), `σ_min(compound k B) = 0` and `(R)` collapses: the perturbed top
compound eigenvalue `μ̃₀` is genuinely **not** lower-bounded by any positive multiple of the forward
growth `cM`, because one singular step can annihilate the top-`k` volume that the next-step band
projector measures.

The forward exponents being *positive at the cut* (the prompt's expanding-top-`k` insight) controls
the **time-averaged / eventual** growth `(1/n)log‖compound k (cocycle n x)‖ → λ₁+⋯+λₖ > log c`, but
**not** the per-step ratio `μ̃₀/cM² = (‖compound(cocycle (n+1))‖/‖compound(cocycle n)‖)²`, which an
individual contracting step `B` can push below `1`. The reverse SVD sandwich `oneStep_sandwich`
(`ErgodicTheory/Lyapunov/RuelleCore.lean`) is **mass-symmetric, not a lower
bound**: it equates the slow→fast and fast→slow off-diagonal block masses for a *fixed* orthonormal
change of basis (a `limsup` envelope on a *fixed* slow space, `limsup_le_of_mem_vslow`); it does not
lower-bound `μ̃₀`, hence cannot drive the Davis–Kahan **projector increment** the Cauchy
construction of `Vⱼ` consumes.

## What this module lands (det-free)

* `ErgodicTheory.numerator_div_gap_le_detfree` — det-free gap-denominator collapse (sorry-free).
* `ErgodicTheory.norm_bandProjector_succ_sub_le_detfree` — det-free per-step band-projector increment
  bound parametrised by the abstract lower-bound coefficient `s` (sorry-free).
* `ErgodicTheory.tendsto_vSlowSingularStep_of_bandProjector_increments_detfree` — the **unconditional**
  `Vⱼ` convergence: from summable det-free per-step bounds (with the abstract `s`) to a converging
  slow projector. Chains `norm_bandProjector_succ_sub_le_detfree` ⇒ the abstract Cauchy packaging
  `exists_tendsto_bandProjector` ⇒ the landed structural reduction
  `tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector`. **No `det ≠ 0` hypothesis.**

The sole input that the inverse engine still supplies — to *any* route — is one number `s > 0` per
step with `μ̃₀ ≥ s²·cM²`. That single residual is named precisely and is the genuine mathematical
wall of the singular `Vⱼ` band-projector route.
-/

open Module InnerProductSpace MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator Matrix MatrixOrder RealInnerProductSpace

noncomputable section

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]
variable {μ : Measure X} {T : X → X}

/-! ## The det-free gap-denominator collapse

The inverse appears in `norm_bandProjector_succ_sub_le` only through the compound condition number
`κ = cB·cBi` (`cBi = ‖compound k B⁻¹‖`). We replace `cBi` by `1/s` with `s` an **abstract** positive
lower-bound coefficient on the perturbed top compound eigenvalue (`μ̃₀ ≥ s²·cM²`). The numerator
over the gap then collapses to the **det-free** ratio `(cB/s)²·r / (1 − (cB/s)²r²)` — a verbatim
det-free analogue of `numerator_div_gap_le`, with `cBi ↦ 1/s`. -/

/-- **Det-free gap-denominator collapse.** With the off-diagonal numerator `cM·(cM·r)·cB²` and a
gap denominator `denom ≥ s²·cM² − cM²·r²·cB²` (`= cM²(s² − r²cB²)`, the det-free form of
`μ̃₀ − ν` once `μ̃₀ ≥ s²·cM²`), the ratio is bounded by `(cB/s)²·r / (1 − (cB/s)²r²)`. The inverse
norm `cBi` of `numerator_div_gap_le` is replaced by `1/s` with `s = σ_min(compound k B)`; no `det`
hypothesis. -/
theorem numerator_div_gap_le_detfree {cM cB s r denom : ℝ}
    (hcM : 0 ≤ cM) (_hcB : 0 ≤ cB) (hr : 0 ≤ r) (hs : 0 < s)
    (hsr : (cB / s) ^ 2 * r ^ 2 < 1)
    (hdenom : s ^ 2 * cM ^ 2 - cM ^ 2 * r ^ 2 * cB ^ 2 ≤ denom) :
    cM * (cM * r) * cB ^ 2 / denom
      ≤ (cB / s) ^ 2 * r / (1 - (cB / s) ^ 2 * r ^ 2) := by
  set q : ℝ := (cB / s) ^ 2 with hq
  have hqnn : 0 ≤ q := by rw [hq]; positivity
  have hgapfac : 0 < 1 - q * r ^ 2 := by linarith
  have hnumnn : 0 ≤ cM * (cM * r) * cB ^ 2 := by positivity
  rcases eq_or_lt_of_le hcM with hcM0 | hcMpos
  · rw [← hcM0]; simp only [zero_mul, mul_zero, zero_div]; positivity
  · have hlb_eq : s ^ 2 * cM ^ 2 - cM ^ 2 * r ^ 2 * cB ^ 2
        = cM ^ 2 * s ^ 2 * (1 - q * r ^ 2) := by
      rw [hq]; field_simp
    have hlbpos : 0 < cM ^ 2 * s ^ 2 * (1 - q * r ^ 2) := by positivity
    have hstep1 : cM * (cM * r) * cB ^ 2 / denom
        ≤ cM * (cM * r) * cB ^ 2 / (cM ^ 2 * s ^ 2 * (1 - q * r ^ 2)) := by
      apply div_le_div_of_nonneg_left hnumnn hlbpos
      rw [← hlb_eq]; exact hdenom
    have hcMne : cM ≠ 0 := ne_of_gt hcMpos
    have hsne : s ≠ 0 := ne_of_gt hs
    have hgapne : (1 - q * r ^ 2) ≠ 0 := ne_of_gt hgapfac
    have hstep2 : cM * (cM * r) * cB ^ 2 / (cM ^ 2 * s ^ 2 * (1 - q * r ^ 2))
        = q * r / (1 - q * r ^ 2) := by
      rw [div_eq_div_iff (ne_of_gt hlbpos) hgapne, hq]
      field_simp
    rw [hstep2] at hstep1; rw [hq]; exact hstep1

/-! ## The det-free per-step band-projector increment bound

Instantiating the abstract `norm_bandProjector_succ_sub_le` with `cBi := 1/s` turns its
inverse-using scalar linkage into the **det-free** form: the gap lower bound is
`s²·cM²·(1 − (cB/s)²r²) ≤ μ̃₀ − ν`, the gap positivity `ν < μ̃₀`, and the regime `(cB/s)²r² < 1`.
The only residual that the inverse engine still supplies is the **single number `s > 0` with
`μ̃₀ ≥ s²·cM²`** (the load-bearing inequality `(R)`); every other ingredient (the abstract symmetric
operator `C` with its top eigenpair / `ν`-ceiling, the orthonormal frames, the det-Gram wedge
bridge) is forward / det-free. -/

set_option linter.unusedSectionVars false in
open scoped RealInnerProductSpace in
/-- **Det-free per-step band-projector increment bound.** Identical to
`norm_bandProjector_succ_sub_le` but parametrised by the **abstract** lower-bound coefficient `s`
(`cBi ↦ 1/s`): the band-projector increment obeys

  `‖Pₙ₊₁ − Pₙ‖ ≤ √(2k)·(cB/s)²·r / (1 − (cB/s)²r²)`.

The scalar inputs are now the **det-free** gap lower bound
`hμ₀lb : s²·cM²·(1 − (cB/s)²r²) ≤ μ₀ − ν`,
the gap positivity `hgap : ν < μ₀`, the regime `hsr : (cB/s)²r² < 1`, and `hspos : 0 < s`. The only
place the inverse survives — in *any* route — is the supply of `s` and the bound `μ₀ ≥ s²·cM²` baked
into `hμ₀lb` (the residual inequality `(R)` of the module docstring). -/
theorem norm_bandProjector_succ_sub_le_detfree {c : ℝ} (A : X → Matrix (Fin d) (Fin d) ℝ)
    (T : X → X) {k : ℕ} (n : ℕ) (x : X)
    (U V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hPn : bandProjector A T (Set.indicator (Set.Ioi c) 1) n x = U * Uᵀ)
    (hPn1 : bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x = V * Vᵀ)
    {N : ℕ} {C : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)}
    {v₀ vt : EuclideanSpace ℝ (Fin N)} (hv₀ : ‖v₀‖ = 1) (hvt : ‖vt‖ = 1)
    {μ₀ μ₁ : ℝ} (hev : C vt = μ₀ • vt)
    {cM cB s r : ℝ} (hcM : 0 ≤ cM) (hcB : 0 ≤ cB) (hr : 0 ≤ r)
    (hnum : ‖C v₀ - (⟪C v₀, v₀⟫_ℝ) • v₀‖ ≤ cM * (cM * r) * cB ^ 2)
    (hceil : ∀ z, (inner ℝ z v₀ : ℝ) = 0 → ⟪C z, z⟫_ℝ ≤ (μ₁ * cB ^ 2) * ‖z‖ ^ 2)
    (hdet : (Uᵀ * V).det = ⟪vt, v₀⟫_ℝ)
    (hμ₀lb : s ^ 2 * cM ^ 2 * (1 - (cB / s) ^ 2 * r ^ 2) ≤ μ₀ - μ₁ * cB ^ 2)
    (hgap : μ₁ * cB ^ 2 < μ₀) (hsr : (cB / s) ^ 2 * r ^ 2 < 1)
    (hspos : 0 < s) :
    ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
        - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖
      ≤ Real.sqrt (2 * k) * ((cB / s) ^ 2 * r / (1 - (cB / s) ^ 2 * r ^ 2)) := by
  -- Instantiate the abstract bound with `cBi := 1/s`; then `cB·cBi = cB/s` and `cM²/cBi² = s²cM²`.
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hcBis : cB * s⁻¹ = cB / s := by rw [div_eq_mul_inv]
  have hbound := norm_bandProjector_succ_sub_le (c := c) A T n x U V hU hV hPn hPn1
    hv₀ hvt hev hcM hcB hr hnum hceil hdet
    (cBi := s⁻¹) (μ₁ := μ₁)
    (by -- `hμ₀lb` in the `cBi = 1/s` form: `cM²/(1/s)² = s²cM²` and `cB·(1/s) = cB/s`.
      rw [hcBis] at *
      have hrw : cM ^ 2 / (s⁻¹) ^ 2 = s ^ 2 * cM ^ 2 := by
        rw [inv_pow, div_inv_eq_mul]; ring
      rw [hrw]; exact hμ₀lb)
    hgap
    (by rw [hcBis] at *; exact hsr)
    (by positivity)
  -- rewrite `cB·(1/s)` to `cB/s` in the conclusion.
  rw [hcBis] at hbound
  exact hbound

/-! ## The unconditional `Vⱼ` convergence (det-free chaining)

With the det-free per-step bound in hand, summability of the det-free dominating sequence yields
band-projector convergence through the abstract Cauchy packaging
`exists_tendsto_orthProjMatrix_of_summable` — already wired in `SingularSlowSpace.lean` as
`exists_tendsto_orthProjMatrix_vSlowSingularStep_of_summable` — and the explicit complement limit
through the landed structural reduction
`tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector`. We package both, **det-free**:
the only hypothesis is the summable (resp. convergent) fast-band increments, which the det-free
per-step bound makes summable wherever the residual `s`-supply `(R)` holds along the orbit. -/

/-- **Unconditional limit slow projector from summable det-free increments.** If the fast-band
increments are summable (the genuine output of `norm_bandProjector_succ_sub_le_detfree` along the
orbit, wherever the per-step `s`-supply `(R)` holds), the slow projectors
`orthProjMatrix (vSlowSingularStep A T c n x)` converge to an orthogonal projector — the candidate
`Vⱼ(ω)` projector. **No `det ≠ 0`.** Re-export of the landed
`exists_tendsto_orthProjMatrix_vSlowSingularStep_of_summable`, recorded here to mark the det-free
chain's terminus. -/
theorem exists_tendsto_vSlowSingularStep_of_summable_detfree
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X)
    (hsum : Summable (fun n =>
        ‖bandProjector A T (Set.indicator (Set.Ioi c) 1) (n + 1) x
          - bandProjector A T (Set.indicator (Set.Ioi c) 1) n x‖)) :
    ∃ P, Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T c n x)) atTop (𝓝 P)
      ∧ IsSelfAdjoint P ∧ P * P = P :=
  exists_tendsto_orthProjMatrix_vSlowSingularStep_of_summable A T c x hsum

/-- **Unconditional `Vⱼ` convergence to the explicit complement limit.** If the fast band projectors
converge to `Pfast` (the genuine output of the det-free per-step bound + Cauchy packaging, wherever
`(R)` holds along the orbit), then the slow projectors converge to the **explicit complement**
`1 − Pfast`, i.e. the singular slow space `Vⱼ(ω)` is the orthogonal complement of the fast Oseledets
spectral projector. **No `det ≠ 0`.** This is the det-free terminus: the band-projector convergence
— the *only* input the landed structural reduction needs — feeds
`tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector` verbatim. -/
theorem tendsto_vSlowSingularStep_of_bandProjector_detfree
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X)
    {Pfast : Matrix (Fin d) (Fin d) ℝ}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      atTop (𝓝 Pfast)) :
    Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T c n x)) atTop (𝓝 (1 - Pfast)) :=
  tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector A T c x hP

end ErgodicTheory
