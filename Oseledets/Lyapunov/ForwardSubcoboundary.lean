import Oseledets.Ergodic.Birkhoff
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# ForwardSubcoboundary — the abstract tempering lemma via the in-measure trick.

Deliverable 2 (the crown jewel): a *sub-coboundary* tempering lemma. If `u ≥ 0` is
measurable and finite, `g ∈ L¹`, and `u (T x) ≤ u x + g x` a.e., together with the
reverse `u x ≤ u (T x) + g x` a.e. (so the *increment* `h := u∘T − u` is dominated by
`g`, hence integrable), then `(1/n) u (Tⁿ x) → 0` for `μ`-a.e. `x`.

This is strictly weaker than the L¹-temperedness premise `posLog (1/θ) ∈ L¹` used by the
committed `tempering_posLog`: we only need the *one-step increment* to be integrable, not
`u` itself.

## Proof (Arnold §3.4.7, in-measure version)

* `h := u∘T − u` is integrable (dominated by `g`, measurable).
* Telescoping: `u (Tⁿ x) = u x + birkhoffSum T h n x`.
* Birkhoff (`tendsto_birkhoffAverage_ae`): `(1/n)·birkhoffSum T h n x → ĥ x` a.e., hence
  `(1/n) u (Tⁿ x) → ĥ x` a.e.
* In-measure: `μ {x | ε < (1/n) u (Tⁿ x)} = μ {x | εn < u x} → 0` (measure preservation +
  `u` finite on a probability space), so `(1/n) u (Tⁿ x) → 0` in measure.
* Uniqueness (a.e. limit = in-measure limit via a subsequence): `ĥ = 0` a.e.
-/

open MeasureTheory Filter Topology

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **Telescoping identity.** For `h y = u (T y) − u y`, the Birkhoff sum telescopes:
`birkhoffSum T h n x = u (Tⁿ x) − u x`. -/
theorem birkhoffSum_sub_comp_self (u : X → ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun y => u (T y) - u y) n x = u (T^[n] x) - u x := by
  induction n with
  | zero => simp [birkhoffSum_zero]
  | succ n ih =>
      rw [birkhoffSum_succ, ih, Function.iterate_succ_apply']
      ring

/-- **Tail decay of the super-level measure.** For a measurable real-valued `u` on a finite
measure space and `δ > 0`, `μ {x | δ·n ≤ u x} → 0` as `n → ∞`: the super-level sets are
antitone with empty intersection (`u` is real-valued, hence finite). -/
theorem tendsto_measure_superlevel_atTop [IsFiniteMeasure μ] {u : X → ℝ} (hu : Measurable u)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => μ {x | δ * n ≤ u x}) atTop (𝓝 0) := by
  set s : ℕ → Set X := fun n => {x | δ * n ≤ u x} with hs
  have hmeas : ∀ n, NullMeasurableSet (s n) μ := fun n =>
    (measurableSet_le measurable_const hu).nullMeasurableSet
  have hanti : Antitone s := by
    intro m n hmn x hx
    simp only [hs, Set.mem_setOf_eq] at hx ⊢
    have : δ * m ≤ δ * n := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact_mod_cast hmn
    linarith
  have hinter : (⋂ n, s n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Set.mem_iInter, hs, Set.mem_setOf_eq] at hx
    -- δ·n ≤ u x for all n contradicts the Archimedean property.
    obtain ⟨n, hn⟩ := exists_nat_gt (u x / δ)
    have := hx n
    rw [div_lt_iff₀ hδ] at hn
    nlinarith [hx n]
  have hconv := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter, measure_empty] at hconv
  exact hconv

/-- **In-measure decay of the normalized orbit.** For measure-preserving `T`, a finite
measure, and a non-negative measurable `u`, the normalized orbit `n⁻¹ · u (Tⁿ x)` tends to
`0` in measure. (Measure preservation moves the super-level set back to `{δn ≤ u}`, which
shrinks to null by `tendsto_measure_superlevel_atTop`.) -/
theorem tendstoInMeasure_orbit_div [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    {u : X → ℝ} (hu : Measurable u) (hu0 : 0 ≤ u) :
    TendstoInMeasure μ (fun (n : ℕ) (x : X) => (n : ℝ)⁻¹ * u (T^[n] x)) atTop (0 : X → ℝ) := by
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  -- The super-level set for `n ≥ 1` equals `(T^[n])⁻¹' {δn ≤ u}`.
  have hset : ∀ n : ℕ, 1 ≤ n →
      {x | δ ≤ dist ((n : ℝ)⁻¹ * u (T^[n] x)) ((0 : X → ℝ) x)}
        = T^[n] ⁻¹' {x | δ * n ≤ u x} := by
    intro n hn
    ext x
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hux : 0 ≤ u (T^[n] x) := hu0 _
    have hinvnn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Pi.zero_apply, dist_zero_right,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hinvnn hux)]
    constructor
    · intro h
      rw [mul_comm δ]
      calc (n : ℝ) * δ
          ≤ n * ((n : ℝ)⁻¹ * u (T^[n] x)) := by
              apply mul_le_mul_of_nonneg_left h hnpos.le
        _ = u (T^[n] x) := by field_simp
    · intro h
      have : (n : ℝ)⁻¹ * (δ * n) ≤ (n : ℝ)⁻¹ * u (T^[n] x) :=
        mul_le_mul_of_nonneg_left h hinvnn
      rwa [show (n : ℝ)⁻¹ * (δ * n) = δ by field_simp] at this
  -- Bound the super-level measure by `μ {δn ≤ u}`, which decays.
  have hbound := tendsto_measure_superlevel_atTop (μ := μ) hu hδ
  refine hbound.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hset n hn]
  exact ((hT.iterate n).measure_preimage
    (measurableSet_le measurable_const hu).nullMeasurableSet).symm

/-- **Abstract tempering lemma (sub-coboundary form) — the crown jewel.**

If `u ≥ 0` is measurable, `g ∈ L¹`, and the one-step increment is dominated by `g` on
both sides — `u (T x) ≤ u x + g x` and `u x ≤ u (T x) + g x` a.e. — then the normalized
orbit tends to `0` a.e.:
`(1/n) · u (Tⁿ x) → 0` for `μ`-a.e. `x`.

Crucially this needs only the *one-step increment* `u∘T − u` to be integrable (dominated by
`g`), NOT `u` itself, and NOT `log⁺(1/θ) ∈ L¹`. This is the classical tempering trick of
Arnold (MET book, Lemma 3.4.7), formalized via the in-measure uniqueness argument. -/
theorem tempering_of_subadditive_step [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hTm : Measurable T) {u g : X → ℝ} (hu : Measurable u) (hu0 : 0 ≤ u)
    (hg : Integrable g μ)
    (hstep : ∀ᵐ x ∂μ, u (T x) ≤ u x + g x)
    (hstep' : ∀ᵐ x ∂μ, u x ≤ u (T x) + g x) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * u (T^[n] x)) atTop (𝓝 0) := by
  -- The increment `h := u∘T − u`, dominated by `g`, hence integrable.
  set h : X → ℝ := fun x => u (T x) - u x with hhdef
  have hhmeas : Measurable h := (hu.comp hTm).sub hu
  have hhle : ∀ᵐ x ∂μ, ‖h x‖ ≤ g x := by
    filter_upwards [hstep, hstep'] with x h1 h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> [linarith; linarith]
  have hhint : Integrable h μ :=
    Integrable.mono' hg hhmeas.aestronglyMeasurable hhle
  -- Birkhoff: `(1/n) Σ_{k<n} h(Tᵏx) → ĥ x` a.e.
  set hbar : X → ℝ := μ[h | MeasurableSpace.invariants T] with hbardef
  have hbirk : ∀ᵐ x ∂μ,
      Tendsto (fun n => birkhoffAverage ℝ T h n x) atTop (𝓝 (hbar x)) :=
    tendsto_birkhoffAverage_ae hT hhint
  -- Telescoping rewrites the Birkhoff average of `h` as `(1/n)(u(Tⁿx) − u x)`.
  have horbit : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * u (T^[n] x)) atTop (𝓝 (hbar x)) := by
    filter_upwards [hbirk] with x hx
    -- `birkhoffAverage ℝ T h n x = (1/n)·(u(Tⁿx) − u x)`, and `(1/n)·u x → 0`.
    have heq : ∀ n : ℕ, birkhoffAverage ℝ T h n x
        = (n : ℝ)⁻¹ * u (T^[n] x) - (n : ℝ)⁻¹ * u x := by
      intro n
      rw [birkhoffAverage, birkhoffSum_sub_comp_self, smul_eq_mul, mul_sub]
    have hconst : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * u x) atTop (𝓝 0) := by
      simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.mul_const (u x)
    have : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * u (T^[n] x)) atTop (𝓝 (hbar x + 0)) := by
      have hsum := hx.add hconst
      refine hsum.congr (fun n => ?_)
      rw [heq n]; ring
    simpa using this
  -- In-measure: the same sequence tends to `0` in measure.
  have hinmeas : TendstoInMeasure μ (fun (n : ℕ) (x : X) => (n : ℝ)⁻¹ * u (T^[n] x)) atTop 0 :=
    tendstoInMeasure_orbit_div hT hu hu0
  -- A subsequence converges a.e. to `0`; combined with a.e. convergence to `hbar`, get `hbar = 0`.
  obtain ⟨ns, hns_mono, hns_ae⟩ := hinmeas.exists_seq_tendsto_ae
  have hbar0 : ∀ᵐ x ∂μ, hbar x = 0 := by
    filter_upwards [horbit, hns_ae] with x hx hxsub
    -- `f (ns i) x → hbar x` (subsequence of a convergent sequence) and `→ 0`.
    have hsub : Tendsto (fun i => (ns i : ℝ)⁻¹ * u (T^[ns i] x)) atTop (𝓝 (hbar x)) :=
      hx.comp hns_mono.tendsto_atTop
    exact tendsto_nhds_unique hsub hxsub
  -- Conclude.
  filter_upwards [horbit, hbar0] with x hx hx0
  rwa [hx0] at hx

/-! ## Deliverable 3 — one-step angle distortion (exact algebraic core).

The squared det-Gram splitting angle of a square frame `W = [ω_F | ω_S]` under a map `M` is
`θ²(M) = det((MW)ᵀ(MW)) / (gF(MW) · gS(MW))`, where `gF, gS` extract the diagonal-block Gram
determinants. The decisive *exact* fact: the numerator transforms by `(det M)²` (Cauchy–Binet
on the full square frame), so the angle distortion is carried entirely by the block Gram
determinants in the denominator. We prove this exactly, then package the log-distortion bound
modulo singular-value sandwich bounds on the block Gram determinants (the residual analytic
input). -/

section AngleDistortion

open scoped Matrix

variable {d : ℕ}

/-- **Image Gram determinant (square frame).** `det((MW)ᵀ(MW)) = (det M)²·(det W)²`. The pure
algebraic core: `det_mul`, `det_transpose`, `det_mul`. (Restated locally for self-containment.) -/
theorem det_gram_image_sq (M W : Matrix (Fin d) (Fin d) ℝ) :
    ((M * W)ᵀ * (M * W)).det = (M.det) ^ 2 * (W.det) ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul]; ring

/-- **Source Gram determinant.** `det(WᵀW) = (det W)²`. -/
theorem det_gram_self_sq (W : Matrix (Fin d) (Fin d) ℝ) :
    (Wᵀ * W).det = (W.det) ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_transpose]; ring

/-- **Exact numerator distortion.** The full-frame Gram determinant of the image is the source
Gram determinant scaled exactly by `(det M)²`:
`det((MW)ᵀ(MW)) = (det M)² · det(WᵀW)`. This is the *only* exact transformation; the angle
distortion is then entirely in the block (denominator) Gram determinants. -/
theorem det_gram_image_eq_sq_mul_self (M W : Matrix (Fin d) (Fin d) ℝ) :
    ((M * W)ᵀ * (M * W)).det = (M.det) ^ 2 * (Wᵀ * W).det := by
  rw [det_gram_image_sq, det_gram_self_sq]

/-- The squared det-Gram splitting angle of frame `W` under map `M`, with block Gram
determinants supplied by `gF, gS`. -/
noncomputable def gramAngleSq (gF gS : Matrix (Fin d) (Fin d) ℝ → ℝ)
    (M W : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ((M * W)ᵀ * (M * W)).det / (gF (M * W) * gS (M * W))

/-- **Exact angle distortion ratio.** For an invertible `M` and a frame `W` with `det W ≠ 0`,
the angle distortion factors as the *exact* numerator factor `(det M)²` times the ratio of
block Gram determinants:
`θ²(M·W) = (det M)² · det(WᵀW) / (gF(MW)·gS(MW))`. Combined with the trivial identity
`θ²(I·W) = det(WᵀW)/(gF(W)·gS(W))`, this isolates the entire angle distortion in the *block*
Gram determinants `gF, gS` — the numerator distortion is exact. -/
theorem gramAngleSq_eq (gF gS : Matrix (Fin d) (Fin d) ℝ → ℝ)
    (M W : Matrix (Fin d) (Fin d) ℝ) (hden : gF (M * W) * gS (M * W) ≠ 0) :
    gramAngleSq gF gS M W
      = (M.det) ^ 2 * (Wᵀ * W).det / (gF (M * W) * gS (M * W)) := by
  rw [gramAngleSq, det_gram_image_eq_sq_mul_self]

/-- **Exact log decomposition of the angle.** With positive block Gram determinants and
`det M ≠ 0`, `det W ≠ 0`,
`log θ²(MW) = log((det M)²) + log(det(WᵀW)) − log gF(MW) − log gS(MW)`. The `(det M)²`
appears *exactly* (numerator) and additively in log scale — the distortion content is the
two block-Gram log terms. -/
theorem log_gramAngleSq_decomp
    (gF gS : Matrix (Fin d) (Fin d) ℝ → ℝ) (M W : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.det ≠ 0) (hW : W.det ≠ 0)
    (hgF : 0 < gF (M * W)) (hgS : 0 < gS (M * W)) :
    Real.log (gramAngleSq gF gS M W)
      = Real.log ((M.det) ^ 2) + Real.log ((Wᵀ * W).det)
        - Real.log (gF (M * W)) - Real.log (gS (M * W)) := by
  have hdetMsq : (0:ℝ) < (M.det) ^ 2 := by positivity
  have hWsq : (0:ℝ) < (Wᵀ * W).det := by rw [det_gram_self_sq]; positivity
  rw [gramAngleSq_eq gF gS M W (by positivity)]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul hdetMsq.ne' hWsq.ne', Real.log_mul hgF.ne' hgS.ne']
  ring

/-- **Exact angle-ratio identity.** `log θ²(MW) − log θ²(IW)` equals *exactly*
`log((det M)²) − [log gF(MW) − log gF(W)] − [log gS(MW) − log gS(W)]`. The source numerator
`det(WᵀW)` cancels and the whole distortion is the `(det M)²` factor plus the two block-Gram
log differences. This is the exact one-step distortion of the splitting angle. -/
theorem log_gramAngleSq_ratio
    (gF gS : Matrix (Fin d) (Fin d) ℝ → ℝ) (M W : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.det ≠ 0) (hW : W.det ≠ 0)
    (hgFMW : 0 < gF (M * W)) (hgSMW : 0 < gS (M * W))
    (hgFW : 0 < gF W) (hgSW : 0 < gS W) :
    Real.log (gramAngleSq gF gS M W) - Real.log (gramAngleSq gF gS 1 W)
      = Real.log ((M.det) ^ 2)
        - (Real.log (gF (M * W)) - Real.log (gF W))
        - (Real.log (gS (M * W)) - Real.log (gS W)) := by
  rw [log_gramAngleSq_decomp gF gS M W hM hW hgFMW hgSMW]
  have h1 : (1 : Matrix (Fin d) (Fin d) ℝ).det ≠ 0 := by simp
  rw [log_gramAngleSq_decomp gF gS 1 W h1 hW (by simpa using hgFW) (by simpa using hgSW)]
  simp only [one_mul, Matrix.det_one, one_pow, Real.log_one]
  ring

/-- **Log-distortion bound (the inequality feeding the sub-coboundary step).** Given the
block-Gram *upper* sandwich `gF(MW) ≤ N²ᵈ·gF(W)`, `gS(MW) ≤ N²ᵈ·gS(W)` — the analytic residual
(with `N = ‖M‖`), supplied as hypotheses — the per-step change in `log(1/θ²)` is bounded by
the log operator norm: with `c := log θ²(W)` the source angle,
`−log θ²(MW) ≤ −log θ²(W) − log((det M)²) + 4d·log N`.

Because `−log θ²` is `log(1/θ²) = log(1/sin²∠)`, this is exactly the sub-coboundary step
`log(1/θ(Tx)) ≤ log(1/θ(x)) + g(x)` (halved), with the L¹ control function
`g = 2d·log⁺‖M‖ + |log(det M)|` — precisely the increment that feeds
`tempering_of_subadditive_step`. The remaining content (deriving the `N²ᵈ` sandwich from
`ExteriorNorm`) is the analytic residual. -/
theorem neg_log_gramAngleSq_le
    (gF gS : Matrix (Fin d) (Fin d) ℝ → ℝ) (M W : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.det ≠ 0) (hW : W.det ≠ 0)
    (hgFMW : 0 < gF (M * W)) (hgSMW : 0 < gS (M * W))
    (hgFW : 0 < gF W) (hgSW : 0 < gS W)
    {N : ℝ} (hN : 0 < N)
    -- block-Gram *upper* sandwich (analytic residual): ‖M‖²ᵈ scaling.
    (hFub : gF (M * W) ≤ N ^ (2 * d) * gF W) (hSub : gS (M * W) ≤ N ^ (2 * d) * gS W) :
    - Real.log (gramAngleSq gF gS M W)
      ≤ - Real.log (gramAngleSq gF gS 1 W)
        - Real.log ((M.det) ^ 2) + 2 * ((2 * d : ℕ) * Real.log N) := by
  have hratio := log_gramAngleSq_ratio gF gS M W hM hW hgFMW hgSMW hgFW hgSW
  have hNd : (0:ℝ) < N ^ (2 * d) := by positivity
  -- From the upper sandwich: log gF(MW) − log gF(W) ≤ 2d·log N.
  have hFdiff : Real.log (gF (M * W)) - Real.log (gF W) ≤ (2 * d : ℕ) * Real.log N := by
    have h := Real.log_le_log hgFMW hFub
    rw [Real.log_mul hNd.ne' hgFW.ne', Real.log_pow] at h
    linarith
  have hSdiff : Real.log (gS (M * W)) - Real.log (gS W) ≤ (2 * d : ℕ) * Real.log N := by
    have h := Real.log_le_log hgSMW hSub
    rw [Real.log_mul hNd.ne' hgSW.ne', Real.log_pow] at h
    linarith
  -- Assemble: −logθ²(MW) = −logθ²(W) − log(detM)² + (loggF diff) + (loggS diff).
  have hkey : - Real.log (gramAngleSq gF gS M W)
      = - Real.log (gramAngleSq gF gS 1 W) - Real.log ((M.det) ^ 2)
        + (Real.log (gF (M * W)) - Real.log (gF W))
        + (Real.log (gS (M * W)) - Real.log (gS W)) := by
    linarith [hratio]
  rw [hkey]; linarith [hFdiff, hSdiff]

end AngleDistortion

end Oseledets

#print axioms Oseledets.tempering_of_subadditive_step
#print axioms Oseledets.tendstoInMeasure_orbit_div
#print axioms Oseledets.tendsto_measure_superlevel_atTop
#print axioms Oseledets.birkhoffSum_sub_comp_self
#print axioms Oseledets.det_gram_image_eq_sq_mul_self
#print axioms Oseledets.gramAngleSq_eq
#print axioms Oseledets.log_gramAngleSq_decomp
#print axioms Oseledets.log_gramAngleSq_ratio
#print axioms Oseledets.neg_log_gramAngleSq_le
