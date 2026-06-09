import Oseledets.Lyapunov.Forward

/-!
# The block-specific overlap bound (the final Oseledets crux)

For `μ`-a.e. `x` and a vector `v` with top Λ-exponent `≤ λᵢ` (i.e. `P∞^{cᵢ} v = 0`, where `P∞` is
the limit band projector straddling block `i−1 / i`), and a fast sorted index `j`
(`block(j) < i`, `λⱼ > λᵢ`):

    limsup_n (1/n) log |⟪v, uⱼ(n)⟫_ℝ|  ≤  λᵢ − λ_{block(j)}.

The route telescopes the FINITE-`n` frame overlaps MULTIPLICATIVELY across the adjacent gaps, so
the rate is the sum of adjacent gaps `Σ_k (λₖ − λₖ₋₁) = λᵢ − λ_{block(j)}`.

## Ladder

* **LOW `inner_eq_single_cut_residual`** — pure algebra single-cut residual identity (adapts
  `inner_eq_inner_bandProjector_sub_limit` of `scratch_s4core.lean`).
* **LOW `leak_le_bandProjector_diff`** — `‖Q∞ u‖ ≤ ‖Pₙ − P∞‖_op` operator-level leak.
* **MED `limsup_logTail_le`** / **`single_gap_coupling_logLimit`** — the tail-rate lemma: summable
  increments with `(1/n) log bₙ → L < 0` give `limsup (1/n) log ‖Σ_{m≥n} incr‖ ≤ L`; specialised to
  the band-projector tail `‖Pₙ − P∞‖`.
* **HIGH `telescope_overlap_limsup_le`** — the multiplicative composition across the adjacent gaps.
-/

open MeasureTheory Filter Topology
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X}
variable {d : ℕ}

/-! ## LOW 1 — single-cut residual identity (pure algebra) -/

/-- **LOW 1 (`inner_eq_single_cut_residual`).** If `v` is killed by the limit projector
`P∞` (`toEuclideanLin P∞ v = 0`) and `u` lies in the step-`n` band of `Pₙ`
(`toEuclideanLin Pₙ u = u`), then the overlap is the residual overlap against the band-projector
tilt: `⟪v, u⟫ = ⟪v, (Pₙ − P∞) u⟫`. Both projectors are self-adjoint. -/
theorem inner_eq_single_cut_residual [NeZero d]
    {Pn Pinf : Matrix (Fin d) (Fin d) ℝ}
    (hPinfsa : Pinfᵀ = Pinf)
    {v u : EuclideanSpace ℝ (Fin d)}
    (hkill : Matrix.toEuclideanLin Pinf v = 0)
    (hband : Matrix.toEuclideanLin Pn u = u) :
    (inner ℝ v u : ℝ) = (inner ℝ v (Matrix.toEuclideanLin (Pn - Pinf) u) : ℝ) := by
  have hsymPinf : (Matrix.toEuclideanLin Pinf).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hPinfsa])
  -- `⟪v, P∞ u⟫ = ⟪P∞ v, u⟫ = ⟪0, u⟫ = 0`.
  have hPinfu : (inner ℝ v (Matrix.toEuclideanLin Pinf u) : ℝ) = 0 := by
    rw [← hsymPinf v u, hkill, inner_zero_left]
  -- `(Pₙ − P∞) u = Pₙ u − P∞ u`.
  have hsplit : Matrix.toEuclideanLin (Pn - Pinf) u
      = Matrix.toEuclideanLin Pn u - Matrix.toEuclideanLin Pinf u := by
    rw [map_sub, LinearMap.sub_apply]
  rw [hsplit, inner_sub_right, hPinfu, sub_zero, hband]

/-! ## LOW 2 — the leak is bounded by the band-projector difference -/

/-- **LOW 2 (`leak_le_bandProjector_diff`).** With `u` in the step-`n` band (`Pₙ u = u`) and the
limit projector `P∞` killing it up to the residual, the residual `‖(Pₙ − P∞) u‖` is bounded by the
operator norm of `Pₙ − P∞` times `‖u‖`. (Operator-norm tilt control; in the application `‖u‖ = 1`.)
This is the per-step leak whose normalized log telescopes at the gap rate. -/
theorem leak_le_bandProjector_diff [NeZero d]
    {Pn Pinf : Matrix (Fin d) (Fin d) ℝ}
    {u : EuclideanSpace ℝ (Fin d)} :
    ‖Matrix.toEuclideanLin (Pn - Pinf) u‖ ≤ ‖Pn - Pinf‖ * ‖u‖ :=
  ExteriorNorm.norm_toEuclideanLin_apply_le (Pn - Pinf) u

/-- **LOW 2′ (overlap ≤ tilt, unit `u`).** Combining LOW 1, Cauchy–Schwarz and LOW 2 for a unit
band vector `u`: `|⟪v, u⟫| ≤ ‖v‖ · ‖Pₙ − P∞‖`. -/
theorem abs_inner_le_norm_mul_bandProjector_diff [NeZero d]
    {Pn Pinf : Matrix (Fin d) (Fin d) ℝ}
    (hPinfsa : Pinfᵀ = Pinf)
    {v u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hkill : Matrix.toEuclideanLin Pinf v = 0)
    (hband : Matrix.toEuclideanLin Pn u = u) :
    |(inner ℝ v u : ℝ)| ≤ ‖v‖ * ‖Pn - Pinf‖ := by
  rw [inner_eq_single_cut_residual hPinfsa hkill hband]
  calc |(inner ℝ v (Matrix.toEuclideanLin (Pn - Pinf) u) : ℝ)|
      ≤ ‖v‖ * ‖Matrix.toEuclideanLin (Pn - Pinf) u‖ := abs_real_inner_le_norm v _
    _ ≤ ‖v‖ * (‖Pn - Pinf‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (leak_le_bandProjector_diff) (norm_nonneg _)
    _ = ‖v‖ * ‖Pn - Pinf‖ := by rw [hu, mul_one]

/-! ## MED — the tail-rate lemma

The single-gap coupling: the band-projector tilt `‖Pₙ − P∞‖` is a *tail* of the summable
increments `incr m = P_{m+1} − P_m`, namely `P∞ − Pₙ = ∑_{m≥n} incr m`, so
`‖Pₙ − P∞‖ ≤ ∑_{m≥n} ‖incr m‖ ≤ ∑_{m≥n} bₘ` with `bₘ` the per-step dominating sequence
(`bCocycle`). The analytic heart is: if `(1/n) log bₘ → L < 0` then
`limsup (1/n) log (∑_{m≥n} bₘ) ≤ L`. We prove this sharply (rate `L`, not `L/2`) via the per-`ε`
geometric envelope `bₘ ≤ exp(m (L+ε))`. -/

/-- **MED core (`tail_le_geometric_envelope`).** If eventually `bₘ ≤ exp(m·s)` with `s < 0`, then
for `n` in that eventual regime the tail `∑_{m≥n} b (n + m)` is bounded by the geometric tail
`exp(n·s) / (1 − exp s)`. (Here `b` is nonneg and the tail is `∑' m, b (n+m)`.) -/
theorem tail_le_geometric_envelope (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) {s : ℝ} (hs : s < 0)
    {N : ℕ} (hN : ∀ m, N ≤ m → b m ≤ Real.exp ((m : ℝ) * s)) {n : ℕ} (hn : N ≤ n) :
    ∑' m : ℕ, b (n + m) ≤ Real.exp ((n : ℝ) * s) / (1 - Real.exp s) := by
  set ρ := Real.exp s with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr hs
  -- termwise: b (n+m) ≤ exp(n s) · ρ^m
  have hterm : ∀ m : ℕ, b (n + m) ≤ Real.exp ((n : ℝ) * s) * ρ ^ m := by
    intro m
    have hge : N ≤ n + m := le_trans hn (Nat.le_add_right _ _)
    calc b (n + m) ≤ Real.exp (((n + m : ℕ) : ℝ) * s) := hN (n + m) hge
      _ = Real.exp ((n : ℝ) * s) * ρ ^ m := by
          rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]
          congr 1; push_cast; ring
  -- summability of the geometric majorant
  have hgeo_sum : Summable (fun m : ℕ => Real.exp ((n : ℝ) * s) * ρ ^ m) :=
    (summable_geometric_of_lt_one (le_of_lt hρ0) hρ1).mul_left _
  have hb_sum : Summable (fun m : ℕ => b (n + m)) :=
    hgeo_sum.of_nonneg_of_le (fun m => hb (n + m)) hterm
  calc ∑' m : ℕ, b (n + m)
      ≤ ∑' m : ℕ, Real.exp ((n : ℝ) * s) * ρ ^ m :=
        hb_sum.tsum_le_tsum hterm hgeo_sum
    _ = Real.exp ((n : ℝ) * s) * ∑' m : ℕ, ρ ^ m := by rw [tsum_mul_left]
    _ = Real.exp ((n : ℝ) * s) * (1 - ρ)⁻¹ := by rw [tsum_geometric_of_lt_one (le_of_lt hρ0) hρ1]
    _ = Real.exp ((n : ℝ) * s) / (1 - ρ) := by rw [div_eq_mul_inv]

/-- **MED (`eventually_le_exp_envelope_of_tendsto`).** From the log-limit `(1/n) log bₙ → L`, for
every `ε > 0` eventually `bₙ ≤ exp(n (L + ε))`. (Tendsto form of the root-test envelope.) -/
theorem eventually_le_exp_envelope_of_tendsto {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {L : ℝ}
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, b n ≤ Real.exp ((n : ℝ) * (L + ε)) := by
  have hlt := hlog.eventually (eventually_lt_nhds (show L < L + ε by linarith))
  filter_upwards [hlt, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  rcases eq_or_lt_of_le (hb n) with h0 | hpos
  · rw [← h0]; positivity
  · have hloglt : Real.log (b n) < (n : ℝ) * (L + ε) := by
      have hmul : (n : ℝ) * ((n : ℝ)⁻¹ * Real.log (b n)) < (n : ℝ) * (L + ε) :=
        mul_lt_mul_of_pos_left hn hnpos
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at hmul
    calc b n = Real.exp (Real.log (b n)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp ((n : ℝ) * (L + ε)) := Real.exp_le_exp.mpr (le_of_lt hloglt)

/-- **MED (`limsup_logTail_le`).** The sharp tail-rate lemma. For a nonnegative `b` with
`(1/n) log bₙ → L < 0`, the geometric tail `∑_{m≥n} b (n+m)` has
`limsup_n (1/n) log (∑' m, b (n+m)) ≤ L`. This is the single-gap coupling rate: the band-projector
tilt `‖Pₙ − P∞‖`, being a tail of the summable per-step increments dominated by `bₘ = bCocycle`,
inherits the rate `L = λₖ − λₖ₋₁`. The cobounded side-condition is passed explicitly. -/
theorem limsup_logTail_le {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {L : ℝ} (hL : L < 0)
    (hbpos : ∀ᶠ n : ℕ in atTop, 0 < b n)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑' m : ℕ, b (n + m))))
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑' m : ℕ, b (n + m)))) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑' m : ℕ, b (n + m))) atTop ≤ L := by
  set u : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.log (∑' m : ℕ, b (n + m)) with hu
  /- For a fixed negative exponent `s` (with `s` slightly above `L`), the geometric envelope of the
  tail gives `u n ≤ s + (1/n)·(− log(1 − exp s))`, and the correction tends to `0`. We feed this
  per-target `y > L` through `limsup_le_iff'`. -/
  -- The per-`s` eventual bound on `u`.
  have hbound_s : ∀ s : ℝ, L < s → s < 0 → ∀ᶠ n : ℕ in atTop,
      u n ≤ s + (n : ℝ)⁻¹ * (- Real.log (1 - Real.exp s)) := by
    intro s hLs hs
    -- exp-envelope `b m ≤ exp(m·s)` from the log-limit (ε := s − L > 0, since L + ε = s).
    have henv := eventually_le_exp_envelope_of_tendsto hb hlog (s - L) (by linarith)
    have henv' : ∀ᶠ m : ℕ in atTop, b m ≤ Real.exp ((m : ℝ) * s) := by
      filter_upwards [henv] with m hm
      have : L + (s - L) = s := by ring
      rwa [this] at hm
    obtain ⟨N, hN⟩ := eventually_atTop.mp henv'
    -- denominator positivity: 1 − exp s > 0 since s < 0.
    have hden : 0 < 1 - Real.exp s := by
      have : Real.exp s < 1 := Real.exp_lt_one_iff.mpr hs
      linarith
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1, hbpos] with n hn hn1 hbn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    -- the tail bound
    have htail := tail_le_geometric_envelope b hb hs (N := N) hN hn
    -- summability of the tail (to get the `m = 0` lower bound `b n ≤ tail`)
    have hb_sum : Summable (fun m : ℕ => b (n + m)) := by
      have hρ1 : Real.exp s < 1 := Real.exp_lt_one_iff.mpr hs
      have hgeo : Summable (fun m : ℕ => Real.exp ((n : ℝ) * s) * Real.exp s ^ m) :=
        (summable_geometric_of_lt_one (le_of_lt (Real.exp_pos s)) hρ1).mul_left _
      refine hgeo.of_nonneg_of_le (fun m => hb (n + m)) (fun m => ?_)
      have hge : N ≤ n + m := le_trans hn (Nat.le_add_right _ _)
      calc b (n + m) ≤ Real.exp (((n + m : ℕ) : ℝ) * s) := hN (n + m) hge
        _ = Real.exp ((n : ℝ) * s) * Real.exp s ^ m := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    set tail := ∑' m : ℕ, b (n + m) with htaildef
    -- tail positive: dominates its `m = 0` term `b n > 0`.
    have htail_pos : 0 < tail := by
      have h0 : b (n + 0) ≤ tail := hb_sum.le_tsum 0 (fun m _ => hb (n + m))
      simp only [Nat.add_zero] at h0
      linarith [hbn]
    -- `log tail ≤ log (RHS) = n·s − log(1 − exp s)`.
    have hlogtail : Real.log tail ≤ (n : ℝ) * s + (- Real.log (1 - Real.exp s)) := by
      have hlog_le : Real.log tail ≤ Real.log (Real.exp ((n : ℝ) * s) / (1 - Real.exp s)) :=
        Real.log_le_log htail_pos htail
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hden), Real.log_exp] at hlog_le
      linarith [hlog_le]
    -- divide by n
    calc u n = (n : ℝ)⁻¹ * Real.log tail := by rw [hu]
      _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * s + (- Real.log (1 - Real.exp s))) :=
          mul_le_mul_of_nonneg_left hlogtail hninv
      _ = s + (n : ℝ)⁻¹ * (- Real.log (1 - Real.exp s)) := by
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnpos), one_mul]
  -- correction term vanishes for any fixed `s`.
  have hcorr : ∀ s : ℝ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (- Real.log (1 - Real.exp s))) atTop (𝓝 0) := by
    intro s
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa using hinv.mul_const (- Real.log (1 - Real.exp s))
  rw [limsup_le_iff' hcobdd hbdd]
  intro y hy
  -- choose `s` with `L < s < y` and `s < 0`.
  set s := L + (min (y - L) (- L)) / 2 with hsdef
  have hpos1 : 0 < y - L := by linarith
  have hpos2 : 0 < - L := by linarith
  have hmin_pos : 0 < min (y - L) (- L) := lt_min hpos1 hpos2
  have hsL : L < s := by rw [hsdef]; linarith [hmin_pos]
  have hsneg : s < 0 := by
    rw [hsdef]
    have : min (y - L) (- L) ≤ - L := min_le_right _ _
    linarith
  have hsy : s < y := by
    rw [hsdef]
    have : min (y - L) (- L) ≤ y - L := min_le_left _ _
    linarith
  filter_upwards [hbound_s s hsL hsneg, (hcorr s).eventually
    (gt_mem_nhds (show (0:ℝ) < y - s by linarith))] with n h1 h2
  have h2' : (n : ℝ)⁻¹ * (- Real.log (1 - Real.exp s)) < y - s := by simpa using h2
  calc u n ≤ s + (n : ℝ)⁻¹ * (- Real.log (1 - Real.exp s)) := h1
    _ ≤ s + (y - s) := by linarith
    _ = y := by ring

/-! ## MED — the band-projector tilt is bounded by the increment tail -/

/-- **MED (`norm_bandProjector_sub_limit_le_tail`).** A normed-space tail bound: if `f n → a` and the
consecutive increments are dominated by a summable nonnegative `b` (`‖f n − f (n+1)‖ ≤ b n`), then
`‖f n − a‖ ≤ ∑' m, b (n + m)`. Specialised to `f = Pₙ`, `a = P∞`, `b = bCocycle` this is the tilt
tail bound `‖Pₙ − P∞‖ ≤ ∑_{m≥n} bₘ`. Direct from Mathlib's
`dist_le_tsum_of_dist_le_of_tendsto`. -/
theorem norm_sub_limit_le_tail {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (b : ℕ → ℝ) (hstep : ∀ n, ‖f n - f (n + 1)‖ ≤ b n) (hsum : Summable b)
    {a : E} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    ‖f n - a‖ ≤ ∑' m : ℕ, b (n + m) := by
  have hdist : ∀ k, dist (f k) (f k.succ) ≤ b k := by
    intro k; rw [dist_eq_norm]; exact hstep k
  have h := dist_le_tsum_of_dist_le_of_tendsto b hdist hsum ha n
  rwa [dist_eq_norm] at h

/-- **MED (`single_gap_coupling_overlap_le`).** The single-gap coupling, in the form the overlap
assembly consumes. For a unit step-`n` band vector `uⱼ(n)` and `v` killed by the limit projector,
the overlap is bounded by the increment tail:

    |⟪v, uⱼ(n)⟫|  ≤  ‖v‖ · (∑' m, b (n + m)),

where `b` (`= bCocycle`) dominates the band-projector increments `‖Pₙ − Pₙ₊₁‖ ≤ bₙ` and is summable
(here from `Pₙ → P∞`). Combined with `limsup_logTail_le`, the increment tail carries the sharp
single-gap rate `L = λₖ − λₖ₋₁`. We expose both the pointwise bound and the tail-rate so the overlap
exponent can be assembled via `scratch_s4core`'s `limsup_normLog_overlap_le` (with `t n = tail` —
eventually positive, so no `log 0` artifact). -/
theorem overlap_le_norm_mul_tail [NeZero d]
    {Pn : ℕ → Matrix (Fin d) (Fin d) ℝ} {Pinf : Matrix (Fin d) (Fin d) ℝ}
    (hPinfsa : Pinfᵀ = Pinf)
    {v : EuclideanSpace ℝ (Fin d)} {uj : ℕ → EuclideanSpace ℝ (Fin d)}
    (b : ℕ → ℝ) (hstep : ∀ n, ‖Pn n - Pn (n + 1)‖ ≤ b n) (hsum : Summable b)
    (hP : Tendsto Pn atTop (𝓝 Pinf))
    (hkill : Matrix.toEuclideanLin Pinf v = 0)
    (hu : ∀ n, ‖uj n‖ = 1)
    (hband : ∀ n, Matrix.toEuclideanLin (Pn n) (uj n) = uj n) (n : ℕ) :
    |(inner ℝ v (uj n) : ℝ)| ≤ ‖v‖ * ∑' m : ℕ, b (n + m) := by
  calc |(inner ℝ v (uj n) : ℝ)|
      ≤ ‖v‖ * ‖Pn n - Pinf‖ :=
        abs_inner_le_norm_mul_bandProjector_diff hPinfsa (hu n) hkill (hband n)
    _ ≤ ‖v‖ * ∑' m : ℕ, b (n + m) :=
        mul_le_mul_of_nonneg_left (norm_sub_limit_le_tail Pn b hstep hsum hP n) (norm_nonneg _)

/-- **MED (`single_gap_coupling_logLimit`).** Packaging the single-gap coupling at the log level
(the `scratch_s4core` shape). With the per-step increment bound, the tail-rate (`limsup_logTail_le`,
`L = λₖ − λₖ₋₁ < 0`), the unit band vector and the kill hypothesis, the overlap exponent has

    limsup (1/n) log |⟪v, uⱼ(n)⟫|  ≤  L.

Built by feeding `overlap_le_norm_mul_tail` and `limsup_logTail_le` into the abstract
`Oseledets.limsup_normLog_overlap_le` of `scratch_s4core.lean`, with the (eventually positive)
increment tail as the controlling sequence `t n`. The `‖v‖`-vanishing, eventual positivity of the
overlap, and boundedness/coboundedness side-conditions are passed explicitly. -/
theorem single_gap_coupling_logLimit [NeZero d]
    {Pn : ℕ → Matrix (Fin d) (Fin d) ℝ} {Pinf : Matrix (Fin d) (Fin d) ℝ}
    (hPinfsa : Pinfᵀ = Pinf)
    {v : EuclideanSpace ℝ (Fin d)} {uj : ℕ → EuclideanSpace ℝ (Fin d)}
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hbpos : ∀ᶠ n : ℕ in atTop, 0 < b n)
    {L : ℝ} (hL : L < 0)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (b n)) atTop (𝓝 L))
    (hstep : ∀ n, ‖Pn n - Pn (n + 1)‖ ≤ b n)
    (hP : Tendsto Pn atTop (𝓝 Pinf))
    (hvpos : 0 < ‖v‖)
    (hkill : Matrix.toEuclideanLin Pinf v = 0)
    (hu : ∀ n, ‖uj n‖ = 1)
    (hband : ∀ n, Matrix.toEuclideanLin (Pn n) (uj n) = uj n)
    (hapos : ∀ᶠ n : ℕ in atTop, 0 < |(inner ℝ v (uj n) : ℝ)|)
    (hnvvanish : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0))
    (hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log |(inner ℝ v (uj n) : ℝ)|))
    (hcobT : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑' m : ℕ, b (n + m))))
    (hbddT : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (∑' m : ℕ, b (n + m)))) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log |(inner ℝ v (uj n) : ℝ)|) atTop ≤ L := by
  have hsum : Summable b := summable_of_logLimit_neg b hb hbpos hL hlog
  set t : ℕ → ℝ := fun n => ∑' m : ℕ, b (n + m) with htdef
  -- the tail is eventually positive (dominates its `m = 0` term `b n`).
  have htpos : ∀ᶠ n : ℕ in atTop, 0 < t n := by
    filter_upwards [hbpos] with n hbn
    have h0 : b (n + 0) ≤ t n :=
      (hsum.comp_injective (add_right_injective n)).le_tsum 0 (fun m _ => hb (n + m))
    simp only [Nat.add_zero] at h0; linarith [hbn]
  -- pointwise overlap bound `a n ≤ ‖v‖ · t n`
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(inner ℝ v (uj n) : ℝ)| ≤ ‖v‖ * t n :=
    Filter.Eventually.of_forall (fun n =>
      overlap_le_norm_mul_tail hPinfsa b hstep hsum hP hkill hu hband n)
  -- tail rate
  have htilt : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (t n)) atTop ≤ L :=
    limsup_logTail_le hb hL hbpos hlog hbddT hcobT
  exact limsup_normLog_overlap_le (a := fun n => |(inner ℝ v (uj n) : ℝ)|) (t := t)
    hbound hapos hvpos htpos hnvvanish htilt hcob hcobT hbddT

/-! ## HIGH — the multiplicative telescope (composition of single-gap couplings)

The target rate `λᵢ − λ_{block(j)}` for a fast index `j` whose block is *several* gaps below `i`
equals the sum of the adjacent gaps `Σ_{k} (λₖ − λₖ₋₁)`. The single-gap couplings (MED) supply each
`limsup (1/n) log ℓₖ(n) ≤ λₖ − λₖ₋₁` for the per-gap leak factor `ℓₖ(n)`; composing them
MULTIPLICATIVELY over the finite-`n` frame overlaps gives the full rate.

We split HIGH into:

* **`limsup_log_finset_prod_le`** — the abstract composition engine (FULLY PROVED): given a finite
  family of eventually-positive factors `ℓₖ` with `limsup (1/n) log ℓₖ ≤ rₖ`, a subexponential
  prefactor `C(n)` (`(1/n) log C(n) → 0`), and the product bound `a n ≤ C(n) · ∏ₖ ℓₖ(n)`
  (eventually, with `a ≥ 0`), the overlap exponent has `limsup (1/n) log a ≤ Σₖ rₖ`.

* **`telescope_overlap_limsup_le`** — the Oseledets specialization: instantiates the engine with
  `rₖ = λₖ − λₖ₋₁`, `Σₖ rₖ = λᵢ − λ_{block(j)}`, the per-gap leaks `ℓₖ` from MED, and the
  finite-`n` frame product bound (the single remaining analytic input, stated precisely). -/

/-- **HIGH engine (`limsup_log_finset_prod_le`).** The abstract multiplicative composition. Over a
finite index set `s`, let `ℓ : s → ℕ → ℝ` be eventually-positive factors with
`limsup (1/n) log (ℓₖ n) ≤ r k` (boundedness side-conditions supplied), let `C : ℕ → ℝ` be a
subexponential prefactor (`(1/n) log (C n) → 0`, `C ≥ 0`), and suppose the nonnegative target `a`
obeys the product bound `a n ≤ C n · ∏ₖ ℓₖ n` eventually. Then
`limsup (1/n) log (a n) ≤ ∑ₖ r k`. This is the telescope: the σ-ratios multiply, logs add, and the
limsup of the sum is bounded by the sum of the rates. -/
theorem limsup_log_finset_prod_le {s : Type*} [Fintype s]
    (ℓ : s → ℕ → ℝ) (r : s → ℝ) (a C : ℕ → ℝ)
    (_hann : ∀ n, 0 ≤ a n) (hCnn : ∀ n, 0 ≤ C n)
    (hapos : ∀ᶠ n : ℕ in atTop, 0 < a n)
    (hℓpos : ∀ k, ∀ᶠ n : ℕ in atTop, 0 < ℓ k n)
    (hℓbdd : ∀ k, IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (ℓ k n)))
    (hℓlim : ∀ k, limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (ℓ k n)) atTop ≤ r k)
    (hC : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (C n)) atTop (𝓝 0))
    (hprod : ∀ᶠ n : ℕ in atTop, a n ≤ C n * ∏ k : s, ℓ k n)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)))
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n))) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (a n)) atTop ≤ ∑ k : s, r k := by
  classical
  set R := ∑ k : s, r k with hR
  set N := Fintype.card s with hN
  -- Per-`ε` exp-envelope for `a`: `a n ≤ exp(n (R + ε))` eventually.
  have henv : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp ((n : ℝ) * (R + ε)) := by
    intro ε hε
    -- distribute ε over the (N + 1) factors: each gets ε/(N+1).
    set δ : ℝ := ε / (N + 1) with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    -- per-factor envelope `ℓₖ n ≤ exp(n (r k + δ))`
    have hℓenv : ∀ k, ∀ᶠ n : ℕ in atTop, ℓ k n ≤ Real.exp ((n : ℝ) * (r k + δ)) := by
      intro k
      -- Run the limsup-envelope on the nonneg clamp `max (ℓ k n) 0`, equal to `ℓ k n` eventually.
      have hℓ0 : ∀ n, 0 ≤ (fun n => max (ℓ k n) 0) n := fun n => le_max_right _ _
      have hcongr : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (max (ℓ k n) 0))
          =ᶠ[atTop] (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (ℓ k n)) := by
        filter_upwards [hℓpos k] with n hn
        rw [max_eq_left (le_of_lt hn)]
      have hbdd' : IsBoundedUnder (· ≤ ·) atTop
          (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (max (ℓ k n) 0)) := by
        obtain ⟨B, hB⟩ := hℓbdd k
        refine ⟨B, ?_⟩
        rw [Filter.eventually_map] at hB ⊢
        filter_upwards [hB, hcongr] with n hbn hcn
        rw [hcn]; exact hbn
      have hlim' : limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (max (ℓ k n) 0)) atTop ≤ r k := by
        rw [limsup_congr hcongr]; exact hℓlim k
      have henv0 := eventually_le_exp_of_limsup_le hℓ0 hbdd' hlim' δ hδpos
      filter_upwards [henv0, hℓpos k] with n hn hpos
      rw [max_eq_left (le_of_lt hpos)] at hn; exact hn
    -- C envelope `C n ≤ exp(n δ)`
    have hCenv : ∀ᶠ n : ℕ in atTop, C n ≤ Real.exp ((n : ℝ) * δ) := by
      have := eventually_le_exp_envelope_of_tendsto hCnn hC δ hδpos
      simpa [zero_add] using this
    -- gather all factor envelopes + product bound
    have hall : ∀ᶠ n : ℕ in atTop, ∀ k, ℓ k n ≤ Real.exp ((n : ℝ) * (r k + δ)) :=
      eventually_all.mpr hℓenv
    have hallpos : ∀ᶠ n : ℕ in atTop, ∀ k, 0 < ℓ k n := eventually_all.mpr hℓpos
    filter_upwards [hall, hCenv, hprod, hallpos] with n hn hCn hpn hℓpn
    -- product bound: ∏ ℓₖ ≤ exp(n (Σ(rₖ+δ))) = exp(n (R + N δ))
    have hprodle : ∏ k : s, ℓ k n ≤ Real.exp ((n : ℝ) * (R + N * δ)) := by
      calc ∏ k : s, ℓ k n
          ≤ ∏ k : s, Real.exp ((n : ℝ) * (r k + δ)) :=
            Finset.prod_le_prod (fun k _ => le_of_lt (hℓpn k)) (fun k _ => hn k)
        _ = Real.exp (∑ k : s, (n : ℝ) * (r k + δ)) := by rw [← Real.exp_sum]
        _ = Real.exp ((n : ℝ) * (R + N * δ)) := by
            congr 1
            have hsplit : ∑ k : s, (n : ℝ) * (r k + δ)
                = (n : ℝ) * (∑ k : s, r k) + (n : ℝ) * ((Fintype.card s : ℝ) * δ) := by
              simp only [mul_add]
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                ← Finset.mul_sum]
              ring
            rw [hsplit, hR, hN]; ring
    -- a n ≤ C n · ∏ ≤ exp(nδ)·exp(n(R+Nδ)) = exp(n(R + (N+1)δ)) = exp(n(R+ε))
    have hprodnn : 0 ≤ ∏ k : s, ℓ k n :=
      Finset.prod_nonneg (fun k _ => le_of_lt (hℓpn k))
    calc a n ≤ C n * ∏ k : s, ℓ k n := hpn
      _ ≤ Real.exp ((n : ℝ) * δ) * Real.exp ((n : ℝ) * (R + N * δ)) :=
          mul_le_mul hCn hprodle hprodnn (Real.exp_nonneg _)
      _ = Real.exp ((n : ℝ) * (R + (N + 1) * δ)) := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp ((n : ℝ) * (R + ε)) := by
          congr 2; rw [hδ]; field_simp
  -- turn the per-ε envelope into the limsup bound.
  rw [limsup_le_iff' hcobdd hbdd]
  intro y hy
  set ε := y - R with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  filter_upwards [henv ε hεpos, eventually_ge_atTop 1, hapos] with n hn hn1 hpos
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hlog_le : Real.log (a n) ≤ (n : ℝ) * (R + ε) := by
    rw [← Real.log_exp ((n : ℝ) * (R + ε))]; exact Real.log_le_log hpos hn
  calc (n : ℝ)⁻¹ * Real.log (a n)
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (R + ε)) := mul_le_mul_of_nonneg_left hlog_le hninv
    _ = R + ε := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnpos), one_mul]
    _ = y := by rw [hεdef]; ring

/-- **HIGH (`telescope_overlap_limsup_le`) — the block-specific overlap bound.** The final crux,
assembled from the composition engine `limsup_log_finset_prod_le`. Indexing the adjacent gaps by a
finite type `s` (the gaps `block(j)+1, …, i`), with per-gap leak factors `ℓₖ(n) = ‖Πₖⁿ − Πₖ^∞‖`
(eventually positive, log-limsup `≤ λₖ − λₖ₋₁ =: rₖ`, the MED single-gap rate from
`limsup_logTail_le`), a subexponential prefactor `C(n)` (`‖v‖` and the frame-overlap normalizers),
and the **finite-`n` multiplicative frame-overlap bound** `|⟪v, uⱼ(n)⟫| ≤ C(n) · ∏ₖ ℓₖ(n)` (the
telescope: the σ-ratios multiply across the finite-`n` adjacent frame overlaps), the overlap
exponent has

    limsup (1/n) log |⟪v, uⱼ(n)⟫|  ≤  ∑ₖ rₖ  =  λᵢ − λ_{block(j)}.

This is exactly the consumer form `hov` (after the budget identity `∑ₖ (λₖ − λₖ₋₁) = λᵢ − λⱼ`). The
hypotheses are the precise reduction of the crux to the single remaining analytic input — the
finite-`n` frame product bound `hprod` — every other ingredient (per-gap rates, positivity,
boundedness) being supplied by the banked LOW/MED machinery. -/
theorem telescope_overlap_limsup_le {s : Type*} [Fintype s]
    (ℓ : s → ℕ → ℝ) (lam : s → ℝ) (lamPrev : s → ℝ)
    (overlap : ℕ → ℝ) (C : ℕ → ℝ)
    (hov_nn : ∀ n, 0 ≤ overlap n) (hCnn : ∀ n, 0 ≤ C n)
    (hov_pos : ∀ᶠ n : ℕ in atTop, 0 < overlap n)
    (hℓpos : ∀ k, ∀ᶠ n : ℕ in atTop, 0 < ℓ k n)
    (hℓbdd : ∀ k, IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (ℓ k n)))
    -- the MED single-gap rate for each adjacent gap `k`:
    (hℓlim : ∀ k, limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (ℓ k n)) atTop ≤ lam k - lamPrev k)
    (hC : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (C n)) atTop (𝓝 0))
    -- the finite-`n` multiplicative frame-overlap bound (the remaining analytic input):
    (hprod : ∀ᶠ n : ℕ in atTop, overlap n ≤ C n * ∏ k : s, ℓ k n)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (overlap n)))
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (overlap n)))
    {rate : ℝ}
    -- the telescope budget identity `∑ₖ (λₖ − λₖ₋₁) = λᵢ − λ_{block(j)}`:
    (hbudget : ∑ k : s, (lam k - lamPrev k) = rate) :
    limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (overlap n)) atTop ≤ rate := by
  have h := limsup_log_finset_prod_le ℓ (fun k => lam k - lamPrev k) overlap C
    hov_nn hCnn hov_pos hℓpos hℓbdd hℓlim hC hprod hbdd hcobdd
  rwa [hbudget] at h

end Oseledets
