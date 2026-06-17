/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.OseledetsLimit
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.Measurable

/-!
# Forward exact growth and the measurable Oseledets filtration

This module connects the analytic core of the one-sided Oseledets multiplicative ergodic
theorem (the Oseledets limit `Λ = lim ((A⁽ⁿ⁾)ᵀA⁽ⁿ⁾)^{1/2n}` of `OseledetsLimit.lean`, its
band-projector convergence, and the limsup flag of `Filtration.lean`) to the target theorem
`oseledets_filtration`.

The mathematical content of this module is the **per-vector exact growth limit**
`(1/n) log‖A⁽ⁿ⁾(x) v‖ → λᵢ` for `v` in the stratum `Vᵢ \ Vᵢ₊₁`:

* **Lower bound** `liminf ≥ λᵢ`: the Gram quadratic-form band bound
  `⟪gramₙ v, v⟫ ≥ c^{2n} ‖Pᶜₙ v‖²` (`inner_cfc_ge_band`), the band-projector convergence
  `Pᶜₙ v → Pᶜ_∞ v ≠ 0`, and taking the threshold `c ↑ e^{λᵢ}`.
* **Upper bound** `limsup ≤ λᵢ`: a spectral decomposition over the sorted Gram eigenbasis,
  with each overlap term controlled by the tilt of the band projector at its
  straddling-gap rate, paired against the block's singular-value growth.

Together they upgrade the limsup flag's `lambdaBar = λᵢ` (`lambdaBar_eq_on_stratum`) to a
genuine limit, identify the Λ-spectral filtration with `lambdaSublevel` a.e. (so it inherits
strict antitonicity and `A`-equivariance), and — with the deterministic exponents from
`exists_lam_tendsto_singularValue` and the CFC measurability of `Measurable.lean` — yield
the target theorem.

## Main results

* `inner_cfc_ge_band`: the Gram quadratic-form band bound for a self-adjoint matrix.
* `log_le_liminf_log_cocycle_apply`: the per-vector liminf lower bound
  `log c ≤ liminf (1/n) log‖A⁽ⁿ⁾ v‖` from band-projector convergence.
* `limitBandProjector_apply_eq_zero_of_le`: kernel propagation between limit band
  projectors of nested thresholds.
* `norm_sq_bandProjector_apply_eq_sum`: the frame Parseval identity for the band
  projection in the straddled regime.
* `limsup_normLog_inner_le`: the per-overlap limsup bound via the handle identity and
  Cauchy–Schwarz.
* `limsup_inv_mul_log_norm_cocycle_apply_le`: the per-vector growth upper bound,
  conditional on per-index leakage envelopes.
* `tendsto_inv_mul_log_norm_cocycle_apply_of_bandProjector_envelope`: the assembled per-vector
  exact growth limit.
-/

open MeasureTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace Oseledets

variable {d : ℕ}

/-! ## Distinct descending exponent enumeration

The deterministic singular-value exponents `lam : ℕ → ℝ` (from
`exists_lam_tendsto_singularValue`) are antitone on `[0, d)`; their distinct values,
enumerated **descending**, are the `k` Lyapunov exponents `λ₀ > ⋯ > λ_{k-1}` of the target
theorem. This mirrors `Filtration.specList`. -/

/-- The finite set of distinct exponent values on `[0, d)`. -/
noncomputable def distinctExp (lam : ℕ → ℝ) (d : ℕ) : Finset ℝ :=
  (Finset.range d).image lam

/-- The number of distinct exponents. -/
noncomputable def numExp (lam : ℕ → ℝ) (d : ℕ) : ℕ := (distinctExp lam d).card

/-- The descending enumeration of the distinct exponents (index `0` = largest). -/
noncomputable def expEnum (lam : ℕ → ℝ) (d : ℕ) : Fin (numExp lam d) → ℝ :=
  fun i => (distinctExp lam d).orderEmbOfFin rfl i.rev

theorem expEnum_strictAnti (lam : ℕ → ℝ) (d : ℕ) : StrictAnti (expEnum lam d) :=
  fun _ _ hij => (distinctExp lam d).orderEmbOfFin rfl |>.strictMono (Fin.rev_lt_rev.mpr hij)

theorem expEnum_mem (lam : ℕ → ℝ) (d : ℕ) (i : Fin (numExp lam d)) :
    expEnum lam d i ∈ distinctExp lam d :=
  (distinctExp lam d).orderEmbOfFin_mem rfl i.rev

/-- Membership: `r` is an enumerated value iff `r = lam j` for some `j < d`. -/
theorem mem_distinctExp (lam : ℕ → ℝ) (d : ℕ) {r : ℝ} :
    r ∈ distinctExp lam d ↔ ∃ j : ℕ, j < d ∧ lam j = r := by
  rw [distinctExp, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hjr⟩; exact ⟨j, Finset.mem_range.mp hj, hjr⟩
  · rintro ⟨j, hj, hjr⟩; exact ⟨j, Finset.mem_range.mpr hj, hjr⟩

/-- Every exponent `lam j` (`j < d`) is one of the enumerated distinct values. -/
theorem exists_expEnum_eq (lam : ℕ → ℝ) {d : ℕ} {j : ℕ} (hj : j < d) :
    ∃ i : Fin (numExp lam d), expEnum lam d i = lam j := by
  have hr : lam j ∈ distinctExp lam d := (mem_distinctExp lam d).mpr ⟨j, hj, rfl⟩
  have hrange :
      lam j ∈ Set.range ⇑((distinctExp lam d).orderEmbOfFin (rfl : _ = numExp lam d)) := by
    rw [Finset.range_orderEmbOfFin]; exact hr
  obtain ⟨k, hk⟩ := hrange
  exact ⟨k.rev, by simpa [expEnum] using hk⟩

/-- Every enumerated value is realized by some `lam j`. -/
theorem expEnum_eq_lam (lam : ℕ → ℝ) (d : ℕ) (i : Fin (numExp lam d)) :
    ∃ j : ℕ, j < d ∧ expEnum lam d i = lam j := by
  obtain ⟨j, hj, hjr⟩ := (mem_distinctExp lam d).mp (expEnum_mem lam d i)
  exact ⟨j, hj, hjr.symm⟩

theorem numExp_pos (lam : ℕ → ℝ) {d : ℕ} (hd : 0 < d) : 0 < numExp lam d := by
  rw [numExp, Finset.card_pos]; exact ⟨lam 0, (mem_distinctExp lam d).mpr ⟨0, hd, rfl⟩⟩

theorem numExp_le (lam : ℕ → ℝ) (d : ℕ) : numExp lam d ≤ d := by
  rw [numExp, distinctExp]
  calc ((Finset.range d).image lam).card ≤ (Finset.range d).card := Finset.card_image_le
    _ = d := Finset.card_range d

/-! ## The Gram quadratic-form band bound (lower-bound foundation)

For a self-adjoint `Q` and a `0/1` band indicator `χ = 𝟙_{(c,∞)}`, a continuous shape
`f ≥ 0` with `f ≥ a` above `c` controls the band projection:
`a · ‖(cfc χ Q) v‖² ≤ ⟪(cfc f Q) v, v⟫`. Applied with `Q = qpow`, `f = (·)^{2n}`
(so `cfc f Q = gram`) and `a = c^{2n}` it gives the per-vector lower bound
`c^{2n} ‖Pᶜₙ v‖² ≤ ‖A⁽ⁿ⁾ v‖²`. -/

section QuadForm
open scoped InnerProductSpace
open ComplexOrder

/-- The norm identity `‖toEuclideanLin M v‖² = ⟪toEuclideanLin (Mᵀ * M) v, v⟫` (generic
real matrix; the cocycle specialization is `norm_sq_cocycle_apply_eq_inner_gram`). -/
theorem norm_sq_toEuclideanLin_eq_inner_gram
    (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin M v‖ ^ 2 = ⟪Matrix.toEuclideanLin (Mᵀ * M) v, v⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  have hadj : ⟪Matrix.toEuclideanLin M v, Matrix.toEuclideanLin M v⟫_ℝ
      = ⟪((Matrix.toEuclideanLin M).adjoint ∘ₗ (Matrix.toEuclideanLin M)) v, v⟫_ℝ := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [hadj]
  congr 1
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [LinearMap.comp_apply, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **Gram quadratic-form band bound.** For self-adjoint `Q`, a `0/1` band indicator
`χ = 𝟙_{(c,∞)}`, and a continuous `f ≥ 0` on the spectrum with `a ≤ f t` whenever
`c < t`: `a · ‖(cfc χ Q) v‖² ≤ ⟪(cfc f Q) v, v⟫`. The band projector is a self-adjoint
idempotent (`‖Pv‖² = ⟪Pv,v⟫`); the gap `cfc (f − a·χ) Q` is `PosSemidef` since
`f − a·χ ≥ 0` on the spectrum. -/
theorem inner_cfc_ge_band [NeZero d]
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSelfAdjoint Q)
    (c a : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (_root_.spectrum ℝ Q))
    (hfnn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ f t)
    (hfband : ∀ t ∈ _root_.spectrum ℝ Q, c < t → a ≤ f t)
    (v : EuclideanSpace ℝ (Fin d)) :
    a * ‖Matrix.toEuclideanLin (cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) Q) v‖ ^ 2
      ≤ inner ℝ (Matrix.toEuclideanLin (cfc f Q) v) v := by
  classical
  set χ : ℝ → ℝ := Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) with hχ
  have hspecfin : (_root_.spectrum ℝ Q).Finite := Matrix.finite_real_spectrum (A := Q)
  have hcontχ : ContinuousOn χ (_root_.spectrum ℝ Q) := hspecfin.continuousOn _
  have hPsa : IsSelfAdjoint (cfc χ Q) := cfc_predicate χ Q
  have hPherm : (cfc χ Q).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hPsa
  have hidem : (_root_.spectrum ℝ Q).EqOn (fun t => χ t * χ t) χ := by
    intro t _
    by_cases ht : t ∈ Set.Ioi c
    · simp [hχ, Set.indicator_of_mem ht]
    · simp [hχ, Set.indicator_of_notMem ht]
  have hPidem : cfc χ Q * cfc χ Q = cfc χ Q := by
    rw [← cfc_mul χ χ Q hcontχ hcontχ, cfc_congr hidem]
  have hPtranspose : (cfc χ Q)ᵀ = cfc χ Q := by
    have h := hPherm
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hstep1 : ‖Matrix.toEuclideanLin (cfc χ Q) v‖ ^ 2
      = ⟪Matrix.toEuclideanLin (cfc χ Q) v, v⟫_ℝ := by
    rw [norm_sq_toEuclideanLin_eq_inner_gram, hPtranspose, hPidem]
  set g : ℝ → ℝ := fun t => f t - a * χ t with hg
  have hgnn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ g t := by
    intro t ht
    by_cases hc : c < t
    · have h1 : χ t = 1 := by simp [hχ, Set.indicator_of_mem (Set.mem_Ioi.mpr hc)]
      rw [hg]; simp only [h1, mul_one]; linarith [hfband t ht hc]
    · have h0 : χ t = 0 := by
        rw [hχ, Set.indicator_of_notMem]; rw [Set.mem_Ioi]; exact hc
      rw [hg]; simp only [h0, mul_zero, sub_zero]; exact hfnn t ht
  have hgsplit : cfc g Q = cfc f Q - a • cfc χ Q := by
    have hca : ContinuousOn (fun t ↦ a * χ t) (_root_.spectrum ℝ Q) :=
      (continuousOn_const).mul hcontχ
    rw [hg, cfc_sub f (fun t ↦ a * χ t) Q hf hca, cfc_const_mul a χ Q hcontχ]
  have hgcont : ContinuousOn g (_root_.spectrum ℝ Q) := hf.sub ((continuousOn_const).mul hcontχ)
  have hgsa : IsSelfAdjoint (cfc g Q) := cfc_predicate g Q
  have hgherm : (cfc g Q).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hgsa
  have hgPSD : (cfc g Q).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨hgherm, ?_⟩
    rw [cfc_map_spectrum g Q hQ hgcont]
    rintro _ ⟨t, ht, rfl⟩
    exact hgnn t ht
  have hinner_dot : ⟪Matrix.toEuclideanLin (cfc g Q) v, v⟫_ℝ
      = star (v : Fin d → ℝ) ⬝ᵥ ((cfc g Q) *ᵥ (v : Fin d → ℝ)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    simp only [star_trivial]
  have hPSDnn : (0 : ℝ) ≤ ⟪Matrix.toEuclideanLin (cfc g Q) v, v⟫_ℝ := by
    rw [hinner_dot]; exact hgPSD.dotProduct_mulVec_nonneg _
  have hsplit_inner : ⟪Matrix.toEuclideanLin (cfc g Q) v, v⟫_ℝ
      = ⟪Matrix.toEuclideanLin (cfc f Q) v, v⟫_ℝ
        - a * ⟪Matrix.toEuclideanLin (cfc χ Q) v, v⟫_ℝ := by
    rw [hgsplit, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
  rw [show inner ℝ (Matrix.toEuclideanLin (cfc f Q) v) v
      = ⟪Matrix.toEuclideanLin (cfc f Q) v, v⟫_ℝ from rfl, hstep1]
  have hfin : (0 : ℝ) ≤ ⟪Matrix.toEuclideanLin (cfc f Q) v, v⟫_ℝ
      - a * ⟪Matrix.toEuclideanLin (cfc χ Q) v, v⟫_ℝ := by
    rw [← hsplit_inner]; exact hPSDnn
  linarith

end QuadForm

variable {X : Type*} [MeasurableSpace X]

/-! ## The per-vector lower bound: Gram–CFC identity, band bound, and liminf

The Gram matrix `gramₙ = (A⁽ⁿ⁾)ᵀA⁽ⁿ⁾` is recovered from `qpowₙ = (gramₙ)^{1/(2n)}` by
raising to the `2n`-th power (`gram_eq_cfc_qpow`). Feeding `qpowₙ` into the quadratic-form
band bound (`inner_cfc_ge_band`) with `f = (·)^{2n}` and threshold `c` then gives the
per-vector bound `c^{2n} ‖Pᶜₙ v‖² ≤ ‖A⁽ⁿ⁾ v‖²` (`cocycle_apply_sq_ge_band`). Taking logs,
dividing by `2n`, and sending the band-projector correction to `0`
(`tendsto_inv_mul_log_norm_bandProjector_apply`) yields the per-vector liminf lower bound
`log c ≤ liminf (1/n) log‖A⁽ⁿ⁾ v‖` (`log_le_liminf_log_cocycle_apply`). -/

section LowerBound
open scoped Matrix InnerProductSpace

/-- **Gram–CFC identity.** Raising `qpowₙ = (gramₙ)^{1/(2n)}` to the `2n`-th power (via the
CFC) recovers the Gram matrix `gramₙ`. -/
theorem gram_eq_cfc_qpow [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {n : ℕ} (hn : 1 ≤ n) (x : X) :
    cfc (fun t : ℝ => t ^ (2 * (n : ℝ))) (qpow A T n x) = gram A T n x := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have h2n : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hgsa : IsSelfAdjoint (gram A T n x) := gram_isSelfAdjoint A T n x
  -- spectrum of gram is nonnegative
  have hspec : _root_.spectrum ℝ (gram A T n x) ⊆ {a : ℝ | 0 ≤ a} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp (gram_posSemidef A T n x)).2
  -- global continuity of the two rpow shapes (exponents ≥ 0)
  have hcont_out : Continuous (fun t : ℝ => t ^ (2 * (n : ℝ))) :=
    Real.continuous_rpow_const (by positivity)
  have hcont_in : Continuous (fun t : ℝ => t ^ ((2 * (n : ℝ))⁻¹)) :=
    Real.continuous_rpow_const (by positivity)
  -- fold the two powers via `cfc_comp`
  have hfold :
      cfc (fun t : ℝ => t ^ (2 * (n : ℝ))) (qpow A T n x)
        = cfc (fun t : ℝ => (t ^ ((2 * (n : ℝ))⁻¹)) ^ (2 * (n : ℝ))) (gram A T n x) := by
    change cfc (fun t : ℝ ↦ t ^ (2 * (n : ℝ)))
        (cfc (fun t : ℝ ↦ t ^ ((2 * (n : ℝ))⁻¹)) (gram A T n x)) = _
    rw [← cfc_comp (fun t : ℝ ↦ t ^ (2 * (n : ℝ)))
      (fun t : ℝ ↦ t ^ ((2 * (n : ℝ))⁻¹)) (gram A T n x) hgsa hcont_out.continuousOn
      hcont_in.continuousOn]
    rfl
  rw [hfold]
  -- on the (nonneg) spectrum, the composed power is the identity
  have hid : (_root_.spectrum ℝ (gram A T n x)).EqOn
      (fun t : ℝ => (t ^ ((2 * (n : ℝ))⁻¹)) ^ (2 * (n : ℝ))) (id : ℝ → ℝ) := by
    intro t ht
    have ht0 : 0 ≤ t := hspec ht
    simp only [id]
    rw [← Real.rpow_mul ht0]
    rw [show ((2 * (n : ℝ))⁻¹ * (2 * (n : ℝ))) = 1 by field_simp]
    rw [Real.rpow_one]
  rw [cfc_congr hid, cfc_id ℝ (gram A T n x)]

/-- **Band lower bound.** For `c ≥ 0`, the band projection of `v` (for the band `(c,∞)` of
`qpowₙ`) is controlled by the cocycle growth:
`c^{2n} · ‖Pᶜₙ v‖² ≤ ‖A⁽ⁿ⁾ v‖²`. -/
theorem cocycle_apply_sq_ge_band [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {n : ℕ} (hn : 1 ≤ n) (x : X) {c : ℝ} (hc : 0 ≤ c) (v : EuclideanSpace ℝ (Fin d)) :
    c ^ (2 * (n : ℝ)) *
        ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ ^ 2
      ≤ ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2 := by
  set Q := qpow A T n x with hQ
  have hQsa : IsSelfAdjoint Q := qpow_isSelfAdjoint A T n x
  have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  -- spectrum of Q is nonnegative
  have hspec : _root_.spectrum ℝ Q ⊆ {a : ℝ | 0 ≤ a} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp (qpow_posSemidef A T n x)).2
  have hf : ContinuousOn (fun t : ℝ => t ^ (2 * (n : ℝ))) (_root_.spectrum ℝ Q) :=
    (Real.continuous_rpow_const h2n).continuousOn
  have hfnn : ∀ t ∈ _root_.spectrum ℝ Q, 0 ≤ (fun t : ℝ => t ^ (2 * (n : ℝ))) t := by
    intro t ht; exact Real.rpow_nonneg (hspec ht) _
  have hfband : ∀ t ∈ _root_.spectrum ℝ Q, c < t →
      c ^ (2 * (n : ℝ)) ≤ (fun t : ℝ => t ^ (2 * (n : ℝ))) t := by
    intro t _ hct
    exact Real.rpow_le_rpow hc (le_of_lt hct) h2n
  have hmain := inner_cfc_ge_band Q hQsa c (c ^ (2 * (n : ℝ)))
    (fun t : ℝ => t ^ (2 * (n : ℝ))) hf hfnn hfband v
  -- `cfc f Q = gram` by the Gram–CFC identity; the RHS inner product is `‖cocycle v‖²`
  rw [gram_eq_cfc_qpow A T hn x] at hmain
  rw [← norm_sq_cocycle_apply_eq_inner_gram A n x v] at hmain
  -- `cfc χ Q = bandProjector` by def
  exact hmain

omit [MeasurableSpace X] in
/-- **Band correction vanishes.** If the band projectors `Pᶜₙ` converge to `P` with
`P v ≠ 0`, then the normalized log of the band projection `‖Pᶜₙ v‖` tends to `0`: the norm
converges to a positive limit, so its log is bounded, and dividing by `n → ∞` kills it. -/
theorem tendsto_inv_mul_log_norm_bandProjector_apply [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) {c : ℝ} {x : X}
    {P : Matrix (Fin d) (Fin d) ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (hP : Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      Filter.atTop (nhds P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ)⁻¹ * Real.log
        ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖)
      Filter.atTop (nhds 0) := by
  -- the linear map `M ↦ toEuclideanLin M v` is continuous (finite-dimensional)
  set evalLin : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.applyₗ v) ∘ₗ (Matrix.toEuclideanLin).toLinearMap with heval
  have hcont : Continuous evalLin := evalLin.continuous_of_finiteDimensional
  have hevalP : evalLin P = Matrix.toEuclideanLin P v := rfl
  -- band projection applied to v converges to P v
  have htend : Filter.Tendsto
      (fun n => Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v)
      Filter.atTop (nhds (Matrix.toEuclideanLin P v)) := by
    have := (hcont.tendsto P).comp hP
    simpa [heval, Function.comp_def] using this
  -- norms converge to L = ‖P v‖ > 0
  have hL : (0 : ℝ) < ‖Matrix.toEuclideanLin P v‖ := norm_pos_iff.mpr hPv
  have hnorm : Filter.Tendsto
      (fun n => ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖)
      Filter.atTop (nhds ‖Matrix.toEuclideanLin P v‖) := htend.norm
  -- logs converge to log L (a finite number)
  have hlog : Filter.Tendsto
      (fun n ↦ Real.log
        ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖)
      Filter.atTop (nhds (Real.log ‖Matrix.toEuclideanLin P v‖)) :=
    (Real.continuousAt_log (ne_of_gt hL)).tendsto.comp hnorm
  -- (n)⁻¹ → 0, times bounded log → 0
  have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have := hinv.mul hlog
  simpa using this

/-- **Per-vector lower bound, eventual form (the analytic core of the liminf bound).** If
the band projectors for `(c,∞)` (with `c > 0`) converge to `P` with `P v ≠ 0`, then
*eventually* `log c + (1/n) log‖Pᶜₙ v‖ ≤ (1/n) log‖A⁽ⁿ⁾ v‖`, where the left band-correction
term tends to `0` (`tendsto_inv_mul_log_norm_bandProjector_apply`). Taking `n → ∞` (the
band correction vanishing) yields `log c ≤ liminf (1/n) log‖A⁽ⁿ⁾ v‖`, which is packaged as
`log_le_liminf_log_cocycle_apply` below. -/
theorem log_add_correction_le_inv_mul_log_cocycle_apply [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (hA : ∀ x, (A x).det ≠ 0)
    {c : ℝ} (hc : 0 < c) {x : X} {P : Matrix (Fin d) (Fin d) ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (hP : Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      Filter.atTop (nhds P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log c + (n : ℝ)⁻¹ * Real.log
          ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖
        ≤ (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
  -- v ≠ 0 since toEuclideanLin P v ≠ 0
  have hv : v ≠ 0 := by
    rintro rfl; exact hPv (by rw [map_zero])
  -- band projection applied to v converges to P v ≠ 0, hence eventually nonzero
  set evalLin : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.applyₗ v) ∘ₗ (Matrix.toEuclideanLin).toLinearMap with heval
  have hcont : Continuous evalLin := evalLin.continuous_of_finiteDimensional
  have htendBand : Filter.Tendsto
      (fun n => Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v)
      Filter.atTop (nhds (Matrix.toEuclideanLin P v)) := by
    have := (hcont.tendsto P).comp hP
    simpa [heval, Function.comp_def] using this
  have hL : (0 : ℝ) < ‖Matrix.toEuclideanLin P v‖ := norm_pos_iff.mpr hPv
  have hbandpos : ∀ᶠ n in Filter.atTop,
      0 < ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ := by
    have hnorm := htendBand.norm
    have : ∀ᶠ n in Filter.atTop,
        ‖Matrix.toEuclideanLin P v‖ / 2 <
          ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ :=
      hnorm.eventually_const_lt (by linarith)
    filter_upwards [this] with n hn
    linarith [hn, half_pos hL]
  -- the eventual inequality
  filter_upwards [eventually_ge_atTop 1, hbandpos] with n hn1 hbpos
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  -- the band bound `cocycle_apply_sq_ge_band`
  have hband := cocycle_apply_sq_ge_band A T hn1 x (le_of_lt hc) v
  set b := ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖
    with hb
  set M := ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ with hM
  have hMpos : 0 < M := norm_pos_iff.mpr (cocycle_apply_ne_zero (T := T) hA n x hv)
  -- take logs of `c^(2n) * b^2 ≤ M^2`
  have hlhs_pos : 0 < c ^ (2 * (n : ℝ)) * b ^ 2 := by
    have : 0 < c ^ (2 * (n : ℝ)) := Real.rpow_pos_of_pos hc _
    positivity
  have hlog_le : Real.log (c ^ (2 * (n : ℝ)) * b ^ 2) ≤ Real.log (M ^ 2) :=
    Real.log_le_log hlhs_pos hband
  -- expand the LHS log
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hc _)) (by positivity),
    Real.log_rpow hc, Real.log_pow, Real.log_pow] at hlog_le
  push_cast at hlog_le
  -- hlog_le : 2*n*log c + 2*log b ≤ 2*log M
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  rw [← sub_nonneg]
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hexpand : (n : ℝ)⁻¹ * Real.log M - (Real.log c + (n : ℝ)⁻¹ * Real.log b)
      = (n : ℝ)⁻¹ * (Real.log M - Real.log b - (n : ℝ) * Real.log c) := by
    field_simp
    ring
  rw [hexpand]
  apply mul_nonneg (le_of_lt hninv)
  nlinarith [hlog_le]

/-- **Per-vector liminf lower bound.** If the band projectors for `(c,∞)` (with `c > 0`)
converge to `P` with `P v ≠ 0`, then `log c ≤ liminf (1/n) log‖A⁽ⁿ⁾ v‖`.

The proof combines the eventual lower bound `log_add_correction_le_inv_mul_log_cocycle_apply`
(whose left side converges to `log c`, the band correction vanishing by
`tendsto_inv_mul_log_norm_bandProjector_apply`) with `liminf` monotonicity. The
`IsCoboundedUnder (· ≥ ·)` side-condition on the right-hand cocycle sequence — which fails
in general without an a-priori upper growth bound on `(1/n) log‖A⁽ⁿ⁾‖`, a Furstenberg–Kesten
input — is taken as a hypothesis `hcobdd`; at the application site it is supplied by the
integrability of the top Furstenberg–Kesten exponent. -/
theorem log_le_liminf_log_cocycle_apply [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (hA : ∀ x, (A x).det ≠ 0)
    {c : ℝ} (hc : 0 < c) {x : X} {P : Matrix (Fin d) (Fin d) ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (hP : Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      Filter.atTop (nhds P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0)
    (hcobdd : Filter.atTop.IsCoboundedUnder (· ≥ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    Real.log c ≤ Filter.liminf
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
      Filter.atTop := by
  have hcorr := tendsto_inv_mul_log_norm_bandProjector_apply A T hP hPv
  set LHS : ℕ → ℝ := fun n ↦ Real.log c + (n : ℝ)⁻¹ * Real.log
      ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖
    with hLHS
  set RHS : ℕ → ℝ := fun n =>
      (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ with hRHS
  have hLHStend : Filter.Tendsto LHS Filter.atTop (nhds (Real.log c)) := by
    have := (tendsto_const_nhds (x := Real.log c) (f := Filter.atTop (α := ℕ))).add hcorr
    simpa [hLHS] using this
  have hineq : ∀ᶠ n in Filter.atTop, LHS n ≤ RHS n :=
    log_add_correction_le_inv_mul_log_cocycle_apply A T hA hc hP hPv
  have hLHSbdd : Filter.atTop.IsBoundedUnder (· ≥ ·) LHS := hLHStend.isBoundedUnder_ge
  calc Real.log c = Filter.liminf LHS Filter.atTop := hLHStend.liminf_eq.symm
    _ ≤ Filter.liminf RHS Filter.atTop := Filter.liminf_le_liminf hineq hLHSbdd hcobdd

/-! ## Band-projector nesting

For `c ≤ c'`, the spectral bands satisfy `Ioi c' ⊆ Ioi c`, so the finer band projector
(threshold `c'`) has range contained in the coarser one (threshold `c`); algebraically
`Pᶜₙ · Pᶜ'ₙ = Pᶜ'ₙ`. Passing to the limit and applying to a vector gives the
kernel-propagation form consumed by the upper-bound proof: a vector killed by the coarser
(lower-threshold) limit projector is killed by every finer (higher-threshold) one above
it. -/

omit [MeasurableSpace X] in
/-- **Band-projector nesting (finite `n`, operator form).** For `c ≤ c'`, the band
projectors are nested: `cfc 𝟙_{(c,∞)} · cfc 𝟙_{(c',∞)} = cfc 𝟙_{(c',∞)}` on `qpow`. The
coarser band (threshold `c`) contains the finer one (threshold `c'`). -/
theorem bandProjector_mul_of_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (n : ℕ) (x : X) {c c' : ℝ} (h : c ≤ c') :
    bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
        * bandProjector A T (Set.indicator (Set.Ioi c') 1) n x
      = bandProjector A T (Set.indicator (Set.Ioi c') 1) n x := by
  -- On the spectrum, `𝟙_{(c,∞)} t · 𝟙_{(c',∞)} t = 𝟙_{(c',∞)} t` because `Ioi c' ⊆ Ioi c`.
  have hidem : (_root_.spectrum ℝ (qpow A T n x)).EqOn
      (fun t => Set.indicator (Set.Ioi c) (1 : ℝ → ℝ) t * Set.indicator (Set.Ioi c') (1 : ℝ → ℝ) t)
      (Set.indicator (Set.Ioi c') (1 : ℝ → ℝ)) := by
    intro t _
    by_cases ht' : t ∈ Set.Ioi c'
    · have ht : t ∈ Set.Ioi c := lt_of_le_of_lt h ht'
      simp [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    · simp [Set.indicator_of_notMem ht']
  have hcont : ContinuousOn (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ))
      (_root_.spectrum ℝ (qpow A T n x)) :=
    (Matrix.finite_real_spectrum (A := qpow A T n x)).continuousOn _
  have hcont' : ContinuousOn (Set.indicator (Set.Ioi c') (1 : ℝ → ℝ))
      (_root_.spectrum ℝ (qpow A T n x)) :=
    (Matrix.finite_real_spectrum (A := qpow A T n x)).continuousOn _
  simp only [bandProjector]
  rw [← cfc_mul _ _ _ hcont hcont', cfc_congr hidem]

omit [MeasurableSpace X] in
/-- **Band-projector nesting (limit, operator form).** Passing `bandProjector_mul_of_le`
through the two convergent band-projector sequences (matrix multiplication is continuous)
gives `P · P' = P'` for the limit projectors, where `c ≤ c'`. -/
theorem limitBandProjector_mul_of_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {x : X} {c c' : ℝ} (h : c ≤ c') {P P' : Matrix (Fin d) (Fin d) ℝ}
    (hP : Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      Filter.atTop (nhds P))
    (hP' : Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c') 1) n x)
      Filter.atTop (nhds P')) :
    P * P' = P' := by
  -- The product sequence converges both to `P * P'` (by continuity of multiplication)
  -- and, by band nesting, to `P'`.
  have hmul : Filter.Tendsto
      (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
          * bandProjector A T (Set.indicator (Set.Ioi c') 1) n x)
      Filter.atTop (nhds (P * P')) := hP.mul hP'
  have heq : (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x
          * bandProjector A T (Set.indicator (Set.Ioi c') 1) n x)
      = (fun n => bandProjector A T (Set.indicator (Set.Ioi c') 1) n x) := by
    funext m; exact bandProjector_mul_of_le A T m x h
  rw [heq] at hmul
  exact tendsto_nhds_unique hmul hP'

/-- **Band-projector nesting (limit, kernel-propagation form).** With `c ≤ c'`, a vector
with `P v = 0` for the coarser (threshold `c`) limit projector also has `P' v = 0` for the
finer (threshold `c'`) one: transposing `P · P' = P'` (both limit projectors are symmetric)
gives `P' · P = P'`, hence `P' v = P' (P v) = 0`. -/
theorem limitBandProjector_apply_eq_zero_of_le [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {x : X} {c c' : ℝ} (h : c ≤ c') {P P' : Matrix (Fin d) (Fin d) ℝ}
    (hP : Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
      Filter.atTop (nhds P))
    (hP' : Filter.Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi c') 1) n x)
      Filter.atTop (nhds P')) {v : EuclideanSpace ℝ (Fin d)}
    (hv : Matrix.toEuclideanLin P v = 0) :
    Matrix.toEuclideanLin P' v = 0 := by
  -- Since all band projectors are self-adjoint (hence the limits are symmetric),
  -- `P * P' = P'` transposes to `P' * P = P'`. Then `P' v = P' (P v) = P' 0 = 0`.
  have hPP' : P * P' = P' := limitBandProjector_mul_of_le A T h hP hP'
  -- symmetry of the limit projectors (limit of self-adjoint matrices is self-adjoint)
  have hPsym : Pᵀ = P := by
    have hsa : Filter.Tendsto
        (fun n => (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)ᵀ)
        Filter.atTop (nhds Pᵀ) := by
      have hcont : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => Mᵀ) := by fun_prop
      exact (hcont.continuousAt (x := P)).tendsto.comp hP
    have heqT : (fun n => (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)ᵀ)
        = (fun n => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) := by
      funext m
      have hsa : (bandProjector A T (Set.indicator (Set.Ioi c) 1) m x)ᴴ
          = bandProjector A T (Set.indicator (Set.Ioi c) 1) m x :=
        bandProjector_isSelfAdjoint A T (Set.indicator (Set.Ioi c) 1) m x
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hsa
    rw [heqT] at hsa
    exact tendsto_nhds_unique hsa hP
  have hP'sym : P'ᵀ = P' := by
    have hsa : Filter.Tendsto
        (fun n => (bandProjector A T (Set.indicator (Set.Ioi c') 1) n x)ᵀ)
        Filter.atTop (nhds P'ᵀ) := by
      have hcont : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => Mᵀ) := by fun_prop
      exact (hcont.continuousAt (x := P')).tendsto.comp hP'
    have heqT : (fun n => (bandProjector A T (Set.indicator (Set.Ioi c') 1) n x)ᵀ)
        = (fun n => bandProjector A T (Set.indicator (Set.Ioi c') 1) n x) := by
      funext m
      have hsa : (bandProjector A T (Set.indicator (Set.Ioi c') 1) m x)ᴴ
          = bandProjector A T (Set.indicator (Set.Ioi c') 1) m x :=
        bandProjector_isSelfAdjoint A T (Set.indicator (Set.Ioi c') 1) m x
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hsa
    rw [heqT] at hsa
    exact tendsto_nhds_unique hsa hP'
  -- transpose `P * P' = P'`: `(P * P')ᵀ = P'ᵀ`, i.e. `P'ᵀ * Pᵀ = P'ᵀ`, i.e. `P' * P = P'`.
  have hP'P : P' * P = P' := by
    have := congrArg Matrix.transpose hPP'
    rw [Matrix.transpose_mul, hPsym, hP'sym] at this
    exact this
  -- now `P' v = (P' * P) v = P' (P v) = P' 0 = 0`
  have hsplit : Matrix.toEuclideanLin (P' * P) v
      = Matrix.toEuclideanLin P' (Matrix.toEuclideanLin P v) := by
    simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  calc Matrix.toEuclideanLin P' v
      = Matrix.toEuclideanLin (P' * P) v := by rw [hP'P]
    _ = Matrix.toEuclideanLin P' (Matrix.toEuclideanLin P v) := hsplit
    _ = Matrix.toEuclideanLin P' 0 := by rw [hv]
    _ = 0 := map_zero _

/-! ## The exact frame Parseval identity

In the eventual straddled regime where exactly `k` `qpow`-eigenvalues exceed the cut `c`
and the top-`k` sorted ones all exceed it, `bandProjector_indicator_eq_sortedTopFrame`
gives `P = W Wᵀ` with `Wᵀ W = 1`, `W = sortedTopFrame`. The band projection applied to `v`
therefore has squared norm equal to the sum of squared overlaps with the top sorted Gram
eigenvectors. -/

/-- **Frame Parseval identity.** Under the eventual straddled-regime hypotheses (`htop`,
`hcount`) of `bandProjector_indicator_eq_sortedTopFrame`, the squared norm of the band
projection equals the sum of squared overlaps of `v` with the top-`k` sorted Gram
eigenvectors (the columns of `sortedTopFrame`, recovered by `colE_sortedTopFrame`). -/
theorem norm_sq_bandProjector_apply_eq_sum [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (n : ℕ) (x : X) (c : ℝ)
    {k : ℕ} (hk : k ≤ Fintype.card (Fin d))
    (htop : ∀ j : Fin k, c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues₀
      ⟨j, lt_of_lt_of_le j.2 hk⟩)
    (hcount : Fintype.card {i : Fin d // c < (qpow_isSelfAdjoint A T n x).isHermitian.eigenvalues i}
      = k) (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c) 1) n x) v‖ ^ 2
      = ∑ j : Fin k,
          (inner ℝ v (ExteriorNorm.colE (sortedTopFrame A T n x hk) j) : ℝ) ^ 2 := by
  obtain ⟨hPWW, hWW⟩ :=
    bandProjector_indicator_eq_sortedTopFrame A T n x c hk htop hcount
  set W := sortedTopFrame A T n x hk with hW
  rw [hPWW]
  -- Step 1: `toEuclideanLin (W Wᵀ) v = ∑ⱼ ⟪v, colE W j⟫ • colE W j`.
  have hdecomp : Matrix.toEuclideanLin (W * Wᵀ) v
      = ∑ j : Fin k, (inner ℝ v (ExteriorNorm.colE W j) : ℝ) • ExteriorNorm.colE W j := by
    apply (EuclideanSpace.equiv (Fin d) ℝ).injective
    rw [map_sum]
    funext a
    rw [Matrix.toLpLin_apply]
    -- LHS at `a`: `((W Wᵀ) *ᵥ v) a`; RHS: `∑ⱼ ⟪v,colEⱼ⟫ • (equiv colEⱼ) a`.
    change ((W * Wᵀ) *ᵥ ((EuclideanSpace.equiv (Fin d) ℝ) v)) a
      = (∑ j : Fin k, (EuclideanSpace.equiv (Fin d) ℝ)
          ((inner ℝ v (ExteriorNorm.colE W j) : ℝ) • ExteriorNorm.colE W j)) a
    rw [Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    -- LHS: `((W Wᵀ) *ᵥ equiv v) a = ∑ b, (∑ j, W a j * W b j) * (equiv v) b`.
    have hLHS : ((W * Wᵀ) *ᵥ ((EuclideanSpace.equiv (Fin d) ℝ) v)) a
        = ∑ b, (∑ j : Fin k, W a j * W b j) * (EuclideanSpace.equiv (Fin d) ℝ) v b := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Matrix.mul_apply]
      refine congrArg (· * _) ?_
      exact Finset.sum_congr rfl (fun j _ => by rw [Matrix.transpose_apply])
    rw [hLHS]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- RHS term `j`: `⟪v, colE W j⟫ * (equiv colE W j) a = ⟪v, colE W j⟫ * W a j`
    have hcolE : (EuclideanSpace.equiv (Fin d) ℝ) (ExteriorNorm.colE W j) a = W a j := by
      rw [ExteriorNorm.colE]; rfl
    have hcolEval : ∀ b, (ExteriorNorm.colE W j) b = W b j := fun b => rfl
    have hinner : (inner ℝ v (ExteriorNorm.colE W j) : ℝ) = ∑ b, W b j * v b := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [RCLike.inner_apply, conj_trivial, hcolEval, mul_comm]
    rw [hcolE, hinner, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hvb : (EuclideanSpace.equiv (Fin d) ℝ) v b = v.ofLp b := rfl
    rw [hvb]; ring
  rw [hdecomp]
  -- Step 2: the columns are orthonormal (`Wᵀ W = 1`), so the squared norm of the sum is `∑ aⱼ²`.
  have horth : ∀ i j : Fin k, (inner ℝ (ExteriorNorm.colE W i) (ExteriorNorm.colE W j) : ℝ)
      = if i = j then 1 else 0 := by
    intro i j
    rw [ExteriorNorm.inner_colE, hWW, Matrix.one_apply]
  rw [← real_inner_self_eq_norm_sq, inner_sum]
  simp only [sum_inner, inner_smul_left, inner_smul_right, conj_trivial, horth]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end LowerBound

/-! ## The per-overlap limsup bound

The handle identity `⟪v, uⱼ(n)⟫ = ⟪v, (Pₙ − Pinf) uⱼ(n)⟫` for slow `v`/fast `uⱼ`, its
Cauchy–Schwarz consequence `|⟪v,uⱼ⟫| ≤ ‖v‖ · ‖(Pₙ − Pinf) uⱼ‖`, the `k = 1` Gram residual
via Pythagoras, and the assembled normalized-log/limsup bounds. Everything is parametrized
over a tilt/overlap-rate hypothesis, supplied at the application site by the
band-projector convergence theory. -/

section OverlapBound
open scoped InnerProductSpace

/-- **Handle identity.** If `v` is slow (`toEuclideanLin Pinf v = 0`) and `uⱼ(n)` lies in
the step-`n` fast band (`toEuclideanLin Pₙ uⱼ = uⱼ`), then `⟪v, uⱼ⟫ = ⟪v, (Pₙ − Pinf) uⱼ⟫`.
Both `Pₙ` and `Pinf` are self-adjoint. -/
theorem inner_eq_inner_bandProjector_sub_limit [NeZero d]
    {Pn Pinf : Matrix (Fin d) (Fin d) ℝ}
    (_hPnsa : Pnᵀ = Pn) (hPinfsa : Pinfᵀ = Pinf)
    {v uj : EuclideanSpace ℝ (Fin d)}
    (hslow : Matrix.toEuclideanLin Pinf v = 0)
    (hfast : Matrix.toEuclideanLin Pn uj = uj) :
    (inner ℝ v uj : ℝ)
      = (inner ℝ v (Matrix.toEuclideanLin (Pn - Pinf) uj) : ℝ) := by
  have hsymPinf : (Matrix.toEuclideanLin Pinf).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hPinfsa])
  -- `⟪v, Pinf uj⟫ = ⟪Pinf v, uj⟫ = ⟪0, uj⟫ = 0`.
  have hPinfuj : (inner ℝ v (Matrix.toEuclideanLin Pinf uj) : ℝ) = 0 := by
    rw [← hsymPinf v uj, hslow, inner_zero_left]
  -- `Pn - Pinf` linear map splits.
  have hsplit : Matrix.toEuclideanLin (Pn - Pinf) uj
      = Matrix.toEuclideanLin Pn uj - Matrix.toEuclideanLin Pinf uj := by
    rw [map_sub, LinearMap.sub_apply]
  rw [hsplit, inner_sub_right, hPinfuj, sub_zero, hfast]

/-- **Handle + Cauchy–Schwarz (per-step bound).** For slow `v` and a step-`n` fast eigenvector
`uj` (`toEuclideanLin Pn uj = uj`), the overlap is controlled by the tilt of the band projector
on `uj`: `|⟪v, uj⟫| ≤ ‖v‖ · ‖(Pn − Pinf) uj‖`. -/
theorem abs_inner_le_norm_mul_bandProjector_tilt [NeZero d]
    {Pn Pinf : Matrix (Fin d) (Fin d) ℝ}
    (hPnsa : Pnᵀ = Pn) (hPinfsa : Pinfᵀ = Pinf)
    {v uj : EuclideanSpace ℝ (Fin d)}
    (hslow : Matrix.toEuclideanLin Pinf v = 0)
    (hfast : Matrix.toEuclideanLin Pn uj = uj) :
    |(inner ℝ v uj : ℝ)| ≤ ‖v‖ * ‖Matrix.toEuclideanLin (Pn - Pinf) uj‖ := by
  rw [inner_eq_inner_bandProjector_sub_limit hPnsa hPinfsa hslow hfast]
  exact abs_real_inner_le_norm v _

/-- **Off-diagonal residual (Pythagoras).** The off-diagonal residual numerator squared:
`‖C v₀ − ⟪C v₀, v₀⟫ v₀‖² = ‖C v₀‖² − ⟪C v₀, v₀⟫²` for a unit vector `v₀`. This is the
elementary `k = 1` Gram off-diagonal residual, requiring no exterior-power machinery. -/
theorem norm_sub_inner_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : E →ₗ[ℝ] E) {v₀ : E} (hv₀ : ‖v₀‖ = 1) :
    ‖C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀‖ ^ 2
      = ‖C v₀‖ ^ 2 - (inner ℝ (C v₀) v₀ : ℝ) ^ 2 := by
  have hv₀v₀ : (inner ℝ v₀ v₀ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₀]; norm_num
  set a : ℝ := (inner ℝ (C v₀) v₀ : ℝ) with ha
  have hcomm : (inner ℝ v₀ (C v₀) : ℝ) = a := by rw [ha, real_inner_comm]
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [real_inner_smul_left, real_inner_smul_right, hv₀v₀, hcomm]
  rw [← real_inner_self_eq_norm_sq]
  ring

/-- **Off-diagonal residual (bound form).** The off-diagonal residual numerator is at most
`‖C v₀‖`. -/
theorem norm_sub_inner_smul_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : E →ₗ[ℝ] E) {v₀ : E} (hv₀ : ‖v₀‖ = 1) :
    ‖C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀‖ ≤ ‖C v₀‖ := by
  have hsq := norm_sub_inner_smul_sq C hv₀
  have hle : ‖C v₀ - (inner ℝ (C v₀) v₀ : ℝ) • v₀‖ ^ 2 ≤ ‖C v₀‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg (inner ℝ (C v₀) v₀ : ℝ)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hle

/-- **Per-step log overlap bound.** With the per-step handle bound `|⟪v,uⱼₙ⟫| ≤ ‖v‖ · tₙ`
(`hbound`) and both sides positive, the normalized-log overlap exponent is dominated by the
tilt exponent plus a vanishing `(1/n) log ‖v‖` shift. -/
theorem normLog_overlap_le {a t : ℕ → ℝ} {nv : ℝ} {n : ℕ}
    (hbound : a n ≤ nv * t n) (hapos : 0 < a n) (hnvpos : 0 < nv) (htpos : 0 < t n) :
    (n : ℝ)⁻¹ * Real.log (a n)
      ≤ (n : ℝ)⁻¹ * Real.log nv + (n : ℝ)⁻¹ * Real.log (t n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hlog : Real.log (a n) ≤ Real.log nv + Real.log (t n) := by
    rw [← Real.log_mul (ne_of_gt hnvpos) (ne_of_gt htpos)]
    exact Real.log_le_log hapos hbound
  calc (n : ℝ)⁻¹ * Real.log (a n)
      ≤ (n : ℝ)⁻¹ * (Real.log nv + Real.log (t n)) :=
        mul_le_mul_of_nonneg_left hlog hninv
    _ = (n : ℝ)⁻¹ * Real.log nv + (n : ℝ)⁻¹ * Real.log (t n) := by ring

/-- **Limsup overlap bound.** Combining `normLog_overlap_le` over `n` with the vanishing of
`(1/n) log ‖v‖` and the supplied tilt-rate `limsup ((1/n) log tₙ) ≤ r`, the overlap
exponent has `limsup ≤ r`. -/
theorem limsup_normLog_overlap_le {a t : ℕ → ℝ} {nv r : ℝ}
    (hbound : ∀ᶠ n in atTop, a n ≤ nv * t n)
    (hapos : ∀ᶠ n in atTop, 0 < a n) (hnvpos : 0 < nv) (htpos : ∀ᶠ n in atTop, 0 < t n)
    (hnvvanish : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log nv) atTop (𝓝 0))
    (htilt : Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (t n)) atTop ≤ r)
    (hcob : Filter.atTop.IsCoboundedUnder (· ≤ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)))
    (hcobt : Filter.atTop.IsCoboundedUnder (· ≤ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (t n)))
    (hbddt : Filter.atTop.IsBoundedUnder (· ≤ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (t n))) :
    Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop ≤ r := by
  set u : ℕ → ℝ := fun n : ℕ => (n : ℝ)⁻¹ * Real.log nv with hu
  set tt : ℕ → ℝ := fun n : ℕ => (n : ℝ)⁻¹ * Real.log (t n) with htt
  have hubdd_le : Filter.atTop.IsBoundedUnder (· ≤ ·) u := hnvvanish.isBoundedUnder_le
  have hubdd_ge : Filter.atTop.IsBoundedUnder (· ≥ ·) u := hnvvanish.isBoundedUnder_ge
  have hulimsup : Filter.limsup u atTop = 0 := hnvvanish.limsup_eq
  have hev : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) ≤ᶠ[atTop] (u + tt) := by
    filter_upwards [hbound, hapos, htpos] with n hb ha ht
    exact normLog_overlap_le hb ha hnvpos ht
  have hsumbdd : Filter.atTop.IsBoundedUnder (· ≤ ·) (u + tt) :=
    isBoundedUnder_le_add hubdd_le hbddt
  have h1 := Filter.limsup_le_limsup hev hcob hsumbdd
  have h2 : Filter.limsup (u + tt) atTop ≤ Filter.limsup u atTop + Filter.limsup tt atTop :=
    limsup_add_le hubdd_ge hubdd_le hcobt hbddt
  rw [hulimsup, zero_add] at h2
  exact (h1.trans h2).trans htilt

/-- **Limsup overlap bound (band-projector form).** Ties the abstract limsup bound to the
genuine band projectors. Given, eventually in `n`, self-adjointness of `Pₙ`/`Pinf`, the
slow hypothesis `Pinf v = 0`, and fast-band membership `Pₙ uⱼ(n) = uⱼ(n)`, the handle +
Cauchy–Schwarz supply the per-step bound, and with the tilt rate `htilt` the overlap
exponent has `limsup ≤ r`. -/
theorem limsup_normLog_inner_le [NeZero d]
    {Pn : ℕ → Matrix (Fin d) (Fin d) ℝ} {Pinf : Matrix (Fin d) (Fin d) ℝ}
    {v : EuclideanSpace ℝ (Fin d)} {uj : ℕ → EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hvpos : 0 < ‖v‖)
    (hPnsa : ∀ᶠ n in atTop, (Pn n)ᵀ = Pn n) (hPinfsa : Pinfᵀ = Pinf)
    (hslow : Matrix.toEuclideanLin Pinf v = 0)
    (hfast : ∀ᶠ n in atTop, Matrix.toEuclideanLin (Pn n) (uj n) = uj n)
    (hapos : ∀ᶠ n in atTop, 0 < |(inner ℝ v (uj n) : ℝ)|)
    (htpos : ∀ᶠ n in atTop, 0 < ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖)
    (hnvvanish : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0))
    (htilt : Filter.limsup
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖) atTop ≤ r)
    (hcob : Filter.atTop.IsCoboundedUnder (· ≤ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log |(inner ℝ v (uj n) : ℝ)|))
    (hcobt : Filter.atTop.IsCoboundedUnder (· ≤ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖))
    (hbddt : Filter.atTop.IsBoundedUnder (· ≤ ·)
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖)) :
    Filter.limsup
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log |(inner ℝ v (uj n) : ℝ)|) atTop ≤ r := by
  have hbound : ∀ᶠ n in atTop,
      |(inner ℝ v (uj n) : ℝ)| ≤ ‖v‖ * ‖Matrix.toEuclideanLin (Pn n - Pinf) (uj n)‖ := by
    filter_upwards [hPnsa, hfast] with n hsa hf
    exact abs_inner_le_norm_mul_bandProjector_tilt hsa hPinfsa hslow hf
  exact limsup_normLog_overlap_le hbound hapos hvpos htpos hnvvanish htilt hcob hcobt hbddt

/-- **Band-projection leakage bound (per-step log form).** With `‖P v‖² = Σⱼ cⱼ`, `cⱼ ≥ 0`,
and a common per-step ceiling `cⱼ ≤ B`, the band-projection leakage exponent is bounded by
`(1/2n) log (k·B)`. -/
theorem normLog_bandProj_le {k : ℕ} {P : ℝ} {c : Fin k → ℝ} {B : ℝ} {n : ℕ}
    (hPpos : 0 < P) (hsum : P ^ 2 = ∑ j, c j) (hcB : ∀ j, c j ≤ B) :
    (n : ℝ)⁻¹ * Real.log P ≤ (n : ℝ)⁻¹ * (2⁻¹ * Real.log ((k : ℝ) * B)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hPsq_le : P ^ 2 ≤ (k : ℝ) * B := by
    rw [hsum]
    calc ∑ j, c j ≤ ∑ _j : Fin k, B := Finset.sum_le_sum (fun j _ => hcB j)
      _ = (k : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hlogP : Real.log P ≤ 2⁻¹ * Real.log ((k : ℝ) * B) := by
    have h2 : Real.log (P ^ 2) ≤ Real.log ((k : ℝ) * B) :=
      Real.log_le_log (by positivity) hPsq_le
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  exact mul_le_mul_of_nonneg_left hlogP hninv

end OverlapBound

/-! ## The per-vector growth upper bound and the per-vector limit

The per-vector upper bound `limsup (1/n) log‖A⁽ⁿ⁾v‖ ≤ λᵢ`, conditional on the per-index
leakage envelopes, and the assembled per-vector exact-growth limit. -/

section Upper
open scoped InnerProductSpace

variable (T : X → X)

/-- **Helper (log of a finite sum).** Let `s` be a finite index type and `t : s → ℕ → ℝ` with
`t m n ≥ 0`. If for every `m` and every `ε > 0`, eventually `t m n ≤ exp (n (L + ε))`, and the total
sum is eventually positive, then `limsup_n (1/n) log (∑_m t m n) ≤ L`. -/
theorem limsup_inv_mul_log_sum_le {s : Type*} [Fintype s] [Nonempty s]
    (t : s → ℕ → ℝ) (L : ℝ) (_htnn : ∀ m n, 0 ≤ t m n)
    (hbound : ∀ m, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, t m n ≤ Real.exp ((n : ℝ) * (L + ε)))
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < ∑ m, t m n)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑ m, t m n))) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑ m, t m n)) atTop ≤ L := by
  set u : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (∑ m, t m n) with hu
  have hkey : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, u n ≤ L + ε +
      (n : ℝ)⁻¹ * Real.log (Fintype.card s) := by
    intro ε hε
    have hall : ∀ᶠ n : ℕ in atTop, ∀ m, t m n ≤ Real.exp ((n : ℝ) * (L + ε)) :=
      eventually_all.mpr (fun m => hbound m ε hε)
    filter_upwards [hall, hpos, eventually_ge_atTop 1] with n hn hsum_pos hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hninv0 : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    have hsum_le : ∑ m, t m n ≤ (Fintype.card s : ℝ) * Real.exp ((n : ℝ) * (L + ε)) := by
      calc ∑ m, t m n ≤ ∑ _m : s, Real.exp ((n : ℝ) * (L + ε)) :=
            Finset.sum_le_sum (fun m _ => hn m)
        _ = (Fintype.card s : ℝ) * Real.exp ((n : ℝ) * (L + ε)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard_pos : (0 : ℝ) < (Fintype.card s : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hlog_le : Real.log (∑ m, t m n)
        ≤ Real.log ((Fintype.card s : ℝ) * Real.exp ((n : ℝ) * (L + ε))) :=
      Real.log_le_log hsum_pos hsum_le
    rw [Real.log_mul (ne_of_gt hcard_pos) (Real.exp_ne_zero _), Real.log_exp] at hlog_le
    rw [hu]
    have hmul : (n : ℝ)⁻¹ * Real.log (∑ m, t m n)
        ≤ (n : ℝ)⁻¹ * (Real.log (Fintype.card s) + (n : ℝ) * (L + ε)) :=
      mul_le_mul_of_nonneg_left hlog_le (le_of_lt hninv0)
    calc (n : ℝ)⁻¹ * Real.log (∑ m, t m n)
        ≤ (n : ℝ)⁻¹ * (Real.log (Fintype.card s) + (n : ℝ) * (L + ε)) := hmul
      _ = L + ε + (n : ℝ)⁻¹ * Real.log (Fintype.card s) := by
          field_simp; ring
  have hcorr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Fintype.card s)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa using hinv.mul_const (Real.log (Fintype.card s))
  have hbdd : IsBoundedUnder (· ≤ ·) atTop u := by
    obtain ⟨N, hN⟩ := (Filter.eventually_atTop.mp ((hkey 1 one_pos).and
      (hcorr.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num)))))
    refine ⟨L + 1 + 1, ?_⟩
    rw [Filter.eventually_map, Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN n hn
    have : (n : ℝ)⁻¹ * Real.log (Fintype.card s) < 1 := by
      simpa using h2
    linarith
  rw [limsup_le_iff' hcobdd hbdd]
  intro y hy
  set ε := (y - L) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  filter_upwards [hkey ε hεpos,
    hcorr.eventually (gt_mem_nhds (show (0:ℝ) < ε from hεpos))] with n h1 h2
  have hcorr_lt : (n : ℝ)⁻¹ * Real.log (Fintype.card s) < ε := by simpa using h2
  calc u n ≤ L + ε + (n : ℝ)⁻¹ * Real.log (Fintype.card s) := h1
    _ ≤ L + ε + ε := by linarith
    _ = y := by rw [hεdef]; ring

/-- **Helper (limsup ⟹ exp envelope).** If `a n ≥ 0` and `limsup_n (1/n) log (a n) ≤ M`, then for
every `ε > 0` eventually `a n ≤ exp (n (M + ε))`. -/
theorem eventually_le_exp_of_limsup_le {a : ℕ → ℝ} (hann : ∀ n, 0 ≤ a n) {M : ℝ}
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)))
    (hlim : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp ((n : ℝ) * (M + ε)) := by
  have hlt : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop < M + ε := by linarith
  have hev := eventually_lt_of_limsup_lt hlt hbdd
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  rcases eq_or_lt_of_le (hann n) with h0 | hpos
  · rw [← h0]; positivity
  · have hloglt : Real.log (a n) < (n : ℝ) * (M + ε) := by
      have hmul : (n : ℝ) * ((n : ℝ)⁻¹ * Real.log (a n)) < (n : ℝ) * (M + ε) :=
        mul_lt_mul_of_pos_left hn hnpos
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at hmul
    have : a n < Real.exp ((n : ℝ) * (M + ε)) := by
      rw [← Real.exp_log hpos]; exact Real.exp_lt_exp.mpr hloglt
    exact le_of_lt this

/-- **Spectral Parseval for the Gram quadratic form** against the sorted Gram eigenbasis:
`⟪gram v, v⟫ = ∑ⱼ (eigenvalues₀ (gram) j) · ⟪v, uⱼ⟫²`. -/
theorem inner_gram_apply_eq_sum_eigenvalues₀ [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanLin (gram A T n x) v, v⟫_ℝ
      = ∑ j : Fin (Fintype.card (Fin d)),
          (gram_posSemidef A T n x).isHermitian.eigenvalues₀ j *
            (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2 := by
  set b := sortedGramEigenbasis A T n x with hb
  set G := Matrix.toEuclideanLin (gram A T n x) with hG
  have hGsym : G.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (gram_posSemidef A T n x).isHermitian
  rw [← b.sum_inner_mul_inner (G v) v]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hGbj : G (b j) = (gram_posSemidef A T n x).isHermitian.eigenvalues₀ j • b j :=
    sortedGramEigenbasis_eigenpair A T n x j
  have h1 : (inner ℝ (G v) (b j) : ℝ) = (gram_posSemidef A T n x).isHermitian.eigenvalues₀ j *
      (inner ℝ v (b j) : ℝ) := by
    rw [hGsym v (b j), hGbj, inner_smul_right]
  have h2 : (inner ℝ (b j) v : ℝ) = (inner ℝ v (b j) : ℝ) := real_inner_comm _ _
  rw [h1, h2]; ring

/-- **Spectral Parseval (cocycle form).** The squared cocycle norm is the sum of squared singular
values times squared overlaps with the sorted Gram eigenbasis:
`‖A⁽ⁿ⁾ v‖² = ∑ⱼ σⱼ(n)² · ⟪v, uⱼ(n)⟫²`. -/
theorem norm_sq_cocycle_apply_eq_sum_singularValues [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2
      = ∑ j : Fin (Fintype.card (Fin d)),
          ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j) ^ 2 *
            (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2 := by
  rw [norm_sq_cocycle_apply_eq_inner_gram, inner_gram_apply_eq_sum_eigenvalues₀]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [gram_eigenvalues₀_eq_sq_singularValues]

/-- The `j`-th spectral term `σⱼ(n)² · ⟪v,uⱼ(n)⟫²`. -/
noncomputable def specTerm [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) (j : Fin (Fintype.card (Fin d))) : ℝ :=
  ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j) ^ 2 *
    (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2

/-- `∑ⱼ specTermⱼ = ‖A⁽ⁿ⁾ v‖²`. -/
theorem sum_specTerm_eq_norm_sq [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∑ j, specTerm T A n x v j = ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2 := by
  rw [norm_sq_cocycle_apply_eq_sum_singularValues]; rfl

theorem specTerm_nonneg [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) (j : Fin (Fintype.card (Fin d))) :
    0 ≤ specTerm T A n x v j := by
  rw [specTerm]; positivity

/-- **Conditional upper bound.** Given, for each spectral index `j`, the per-index exp-envelope
`tⱼ(n) ≤ exp(n(2λᵢ + ε))`, and eventual positivity of `‖A⁽ⁿ⁾ v‖`, the per-vector growth limsup is
`≤ λᵢ`. -/
theorem limsup_inv_mul_log_norm_cocycle_apply_le [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : EuclideanSpace ℝ (Fin d)) (lami : ℝ)
    (henv : ∀ j : Fin (Fintype.card (Fin d)), ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)))
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lami := by
  set g : ℕ → ℝ := fun n => (n : ℝ)⁻¹ *
    Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ with hg
  set N := Fintype.card (Fin (Fintype.card (Fin d))) with hN
  have hcardpos : (0 : ℝ) < (N : ℝ) := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hsumpos : ∀ᶠ n : ℕ in atTop, 0 < ∑ j, specTerm T A n x v j := by
    filter_upwards [hpos] with n hn
    rw [sum_specTerm_eq_norm_sq]; positivity
  have heq : ∀ᶠ n : ℕ in atTop, g n =
      (1/2 : ℝ) * ((n : ℝ)⁻¹ * Real.log (∑ j, specTerm T A n x v j)) := by
    filter_upwards [hpos] with n hn
    have hsq : ∑ j, specTerm T A n x v j
        = ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ ^ 2 := sum_specTerm_eq_norm_sq T A n x v
    have hlog : Real.log (∑ j, specTerm T A n x v j)
        = 2 * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖ := by
      rw [hsq, Real.log_pow]; push_cast; ring
    rw [hg, hlog]; ring
  have hcorr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log N) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa using hinv.mul_const (Real.log N)
  have hgkey : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      g n ≤ lami + ε / 2 + (1/2 : ℝ) * ((n : ℝ)⁻¹ * Real.log N) := by
    intro ε hε
    have hall : ∀ᶠ n : ℕ in atTop, ∀ j,
        specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) :=
      eventually_all.mpr (fun j => henv j ε hε)
    filter_upwards [hall, hsumpos, heq, eventually_ge_atTop 1] with n hn hsum_pos hen hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    have hsum_le : ∑ j, specTerm T A n x v j ≤ (N : ℝ) * Real.exp ((n : ℝ) * (2 * lami + ε)) := by
      calc ∑ j, specTerm T A n x v j ≤ ∑ _j : Fin (Fintype.card (Fin d)),
              Real.exp ((n : ℝ) * (2 * lami + ε)) := Finset.sum_le_sum (fun j _ => hn j)
        _ = (N : ℝ) * Real.exp ((n : ℝ) * (2 * lami + ε)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
    have hlog_le := Real.log_le_log hsum_pos hsum_le
    rw [Real.log_mul (ne_of_gt hcardpos) (Real.exp_ne_zero _), Real.log_exp] at hlog_le
    have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hninv)
    rw [hen]
    have hstep : (n : ℝ)⁻¹ * Real.log (∑ j, specTerm T A n x v j)
        ≤ (n : ℝ)⁻¹ * Real.log N + (2 * lami + ε) := by
      calc (n : ℝ)⁻¹ * Real.log (∑ j, specTerm T A n x v j)
          ≤ (n : ℝ)⁻¹ * (Real.log N + (n : ℝ) * (2 * lami + ε)) := hmul
        _ = (n : ℝ)⁻¹ * Real.log N + (2 * lami + ε) := by
            rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnpos), one_mul]
    nlinarith [hstep]
  have hgbdd : IsBoundedUnder (· ≤ ·) atTop g := by
    obtain ⟨M, hM⟩ := (Filter.eventually_atTop.mp ((hgkey 1 one_pos).and
      (hcorr.eventually (gt_mem_nhds (show (0:ℝ) < 2 by norm_num)))))
    refine ⟨lami + 1 / 2 + 1, ?_⟩
    rw [Filter.eventually_map, Filter.eventually_atTop]
    refine ⟨M, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hM n hn
    have h2' : (n : ℝ)⁻¹ * Real.log N < 2 := by simpa using h2
    nlinarith [h1, h2']
  rw [limsup_le_iff' hcobdd hgbdd]
  intro y hy
  set ε := y - lami with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  filter_upwards [hgkey ε hεpos,
    hcorr.eventually (gt_mem_nhds (show (0:ℝ) < ε from hεpos))] with n h1 h2
  have h2' : (n : ℝ)⁻¹ * Real.log N < ε := by simpa using h2
  calc g n ≤ lami + ε / 2 + (1/2 : ℝ) * ((n : ℝ)⁻¹ * Real.log N) := h1
    _ ≤ y := by rw [hεdef] at *; nlinarith [h2']

/-- **Product envelope.** If `a n ≤ exp(n·p)` and `b n ≤ exp(n·q)` eventually (`a, b ≥ 0`), then
`a n · b n ≤ exp(n·(p+q))` eventually. -/
theorem eventually_mul_le_exp {a b : ℕ → ℝ} (_hann : ∀ n, 0 ≤ a n) (hbnn : ∀ n, 0 ≤ b n)
    {p q : ℝ} (ha : ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp ((n : ℝ) * p))
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ Real.exp ((n : ℝ) * q)) :
    ∀ᶠ n : ℕ in atTop, a n * b n ≤ Real.exp ((n : ℝ) * (p + q)) := by
  filter_upwards [ha, hb] with n han hbn
  calc a n * b n ≤ Real.exp ((n : ℝ) * p) * Real.exp ((n : ℝ) * q) :=
        mul_le_mul han hbn (hbnn n) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * (p + q)) := by rw [← Real.exp_add]; ring_nf

omit [MeasurableSpace X] in
/-- **Singular-value square envelope.** If `(1/n) log σⱼ(n) → λⱼ` and each `σⱼ(n) > 0`, then
for every `δ > 0`, eventually `σⱼ(n)² ≤ exp(n(2λⱼ + δ))`. -/
theorem eventually_sq_singularValue_le_exp {A : X → Matrix (Fin d) (Fin d) ℝ} {x : X}
    (j : Fin (Fintype.card (Fin d)))
    (hσpos : ∀ n : ℕ, 1 ≤ n → 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    {lamj : ℝ}
    (hσ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 lamj))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j) ^ 2
        ≤ Real.exp ((n : ℝ) * (2 * lamj + δ)) := by
  have hev := hσ.eventually (gt_mem_nhds (show lamj < lamj + δ/2 by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  set σ := (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j with hσdef
  have hσp : 0 < σ := hσpos n hn1
  have hloglt : Real.log σ < (n : ℝ) * (lamj + δ/2) := by
    have hmul : (n : ℝ) * ((n : ℝ)⁻¹ * Real.log σ) < (n : ℝ) * (lamj + δ/2) :=
      mul_lt_mul_of_pos_left hn hnpos
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at hmul
  have hσsq : σ ^ 2 = Real.exp (2 * Real.log σ) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hσp]
    norm_num
  rw [hσsq]
  apply Real.exp_le_exp.mpr
  nlinarith [hloglt]

/-- **Per-index envelope (slow & fast unified).** If `(1/n) log σⱼ(n) → λⱼ`, each `σⱼ(n) > 0`, the
overlap satisfies the leakage bound `limsup (1/n) log ⟪v,uⱼ(n)⟫² ≤ 2 rⱼ` (with the boundedness
side-condition), and `λⱼ + rⱼ ≤ λᵢ`, then `specTermⱼ(n) ≤ exp(n(2λᵢ + ε))` for every `ε > 0`. -/
theorem specTerm_envelope_of_rate [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ} {x : X}
    {v : EuclideanSpace ℝ (Fin d)} {lami lamj rj : ℝ} (j : Fin (Fintype.card (Fin d)))
    (hσpos : ∀ n : ℕ, 1 ≤ n → 0 < (Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)
    (hσ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j)) atTop (𝓝 lamj))
    (hovbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)))
    (hov : limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)) atTop ≤ 2 * rj)
    (hrate : lamj + rj ≤ lami) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)) := by
  intro ε hε
  have hσenv := eventually_sq_singularValue_le_exp (T := T) j hσpos hσ (ε/2) (by linarith)
  have hovenv := eventually_le_exp_of_limsup_le
    (a := fun n : ℕ => (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)
    (fun n => by positivity) hovbdd hov (ε/2) (by linarith)
  have hprod := eventually_mul_le_exp
    (a := fun n : ℕ => ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues j) ^ 2)
    (b := fun n : ℕ => (inner ℝ v (sortedGramEigenbasis A T n x j) : ℝ) ^ 2)
    (fun n => by positivity) (fun n => by positivity) hσenv hovenv
  filter_upwards [hprod] with n hn
  rw [specTerm]
  refine hn.trans (Real.exp_le_exp.mpr ?_)
  have : (n : ℝ) * (2 * lamj + ε / 2 + (2 * rj + ε / 2)) ≤ (n : ℝ) * (2 * lami + ε) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [hrate]
  linarith [this]

omit [MeasurableSpace X] in
/-- **Per-vector exact growth limit (from limsup ≤ λᵢ and λᵢ ≤ liminf).** -/
theorem tendsto_inv_mul_log_norm_cocycle_apply
    (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : EuclideanSpace ℝ (Fin d)) (lami : ℝ)
    (hsup : limsup (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ lami)
    (hinf : lami ≤ liminf (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop)
    (hbddabove : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hbddbelow : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop (𝓝 lami) :=
  tendsto_of_le_liminf_of_limsup_le hinf hsup hbddabove hbddbelow

/-- **Per-vector exact growth limit (assembled).** The lower bound is
`log_le_liminf_log_cocycle_apply` at threshold `c = e^{λᵢ}`; the upper bound is
`limsup_inv_mul_log_norm_cocycle_apply_le`. Given band-projector convergence (`hP`, `hPv`),
the per-index leakage envelopes (`henv`), positivity (`hpos`), the cobounded inputs, and
the boundedness side-conditions, the per-vector growth converges to `λᵢ`. -/
theorem tendsto_inv_mul_log_norm_cocycle_apply_of_bandProjector_envelope [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) {x : X}
    {v : EuclideanSpace ℝ (Fin d)} {lami : ℝ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi (Real.exp lami)) 1) n x)
      atTop (𝓝 P))
    (hPv : Matrix.toEuclideanLin P v ≠ 0)
    (henv : ∀ j : Fin (Fintype.card (Fin d)), ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, specTerm T A n x v j ≤ Real.exp ((n : ℝ) * (2 * lami + ε)))
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hcobdd' : IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hbddabove : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))
    (hbddbelow : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop (𝓝 lami) := by
  have hsup := limsup_inv_mul_log_norm_cocycle_apply_le T A x v lami henv hpos hcobdd
  have hexp_pos : (0 : ℝ) < Real.exp lami := Real.exp_pos lami
  have hlow := log_le_liminf_log_cocycle_apply A T hA hexp_pos hP hPv hcobdd'
  rw [Real.log_exp] at hlow
  exact tendsto_inv_mul_log_norm_cocycle_apply T A x v lami hsup hlow hbddabove hbddbelow

end Upper

end Oseledets
