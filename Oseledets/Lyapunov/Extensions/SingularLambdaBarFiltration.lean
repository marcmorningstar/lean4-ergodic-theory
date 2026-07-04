/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.GrowthFunction
import Oseledets.Lyapunov.Ultrametric

/-!
# The algebraic forward filtration from the upper Lyapunov exponent `lambdaBar`

For a (possibly **singular**) matrix cocycle generator `A : X → Matrix (Fin d) (Fin d) ℝ` over
`T : X → X`, this module builds — purely algebraically, **det-free and inverse-free** — the forward
sublevel filtration of the pointwise upper Lyapunov exponent
`lambdaBar A T x v = limsup_n (1/n)·log‖A⁽ⁿ⁾(x)·v‖` (`Oseledets.lambdaBar`,
`Oseledets/Lyapunov/GrowthFunction.lean`).

## The origin/kernel subtlety (and why we floor at `0`)

`lambdaBar` is **`ℝ`-valued** with the convention `Real.log 0 = 0`, so `lambdaBar A T x 0 = 0`
(*not* `−∞`). More importantly, for a *singular* cocycle a nonzero vector can be eventually killed:
if `v + w ∈ ker (A⁽ⁿ⁾(x))` for infinitely many `n`, then `growthSeq (v+w) n = (1/n)·log 0 = 0`
along that subsequence, so `lambdaBar A T x (v + w) ≥ 0` even when `lambdaBar A T x v` and
`lambdaBar A T x w` are both strictly negative. Concretely, for the constant cocycle
`A x = diag(1/2, 0)` one has `lambdaBar (e₁ + e₂) = lambdaBar (−e₁) = log(1/2) < 0` while
`lambdaBar ((e₁ + e₂) + (−e₁)) = lambdaBar e₂ = 0`. Hence the **naive** sublevel set
`{v | lambdaBar A T x v ≤ c} ∪ {0}` is **not** a submodule for `c < 0`: closure under addition fails
at the kernel. This is the genuine `−∞`-vs-`0` obstruction of the singular forward filtration.

The honest, unconditional non-Archimedean inequality is therefore the **floored** one:

  `lambdaBar A T x (v + w) ≤ max (max (lambdaBar A T x v) (lambdaBar A T x w)) 0`

(`lambdaBar_add_le_max_zero`). Consequently the function `v ↦ max (lambdaBar A T x v) 0` *is* a
genuine `IsUltrametricGrowth` function (`isUltrametricGrowth_max_lambdaBar`), and its sublevel sets
are honest submodules. For thresholds `c ≥ 0` — the regime of the genuine nonnegative singular
spectrum — the floored sublevel set **coincides** with the intended set
`{v | lambdaBar A T x v ≤ c} ∪ {0}` (`mem_lambdaBarSublevel_iff`).

## The mild det-free finiteness hypothesis

Both the floored ultrametric inequality and the genuineness of `lambdaBar` (as opposed to the
`Real`-junk value of an unbounded `limsup`) need the top growth sequence
`n ↦ (1/n)·log‖A⁽ⁿ⁾(x)‖` to be bounded above at `x`. This is the **det-free, inverse-free**
finiteness hypothesis `HasFiniteTopGrowth A T x`; it holds a.e. by Furstenberg–Kesten, and holds
**everywhere** whenever `A` has uniformly bounded norm (e.g. `A` continuous on a compact base).
It is strictly weaker than `det A ≠ 0`.

## Main results

* `Oseledets.lambdaBar_step_le`: the **floored** det-free cocycle-step inequality
  `lambdaBar A T (T x) (A x · v) ≤ max (lambdaBar A T x v) 0` (the `(n+1)/n → 1` reindexing);
  fully elementary, carrying only the finiteness hypothesis `HasFiniteTopGrowth A T x`. The full
  identity `= lambdaBar A T x v` would need invertibility (see the section prose above).
* `Oseledets.lambdaBar_add_le_max_zero`: the floored non-Archimedean inequality.
* `Oseledets.isUltrametricGrowth_max_lambdaBar`: `v ↦ max (lambdaBar A T x v) 0` is an
  `IsUltrametricGrowth` function.
* `Oseledets.lambdaBarSublevel`: the sublevel **submodule** at threshold `c`.
* `Oseledets.lambdaBarSublevel_antitone`: monotonicity in `c`.
* `Oseledets.mem_lambdaBarSublevel_iff`: membership, `v = 0 ∨ lambdaBar A T x v ≤ c`, in the
  regime `0 ≤ c` (where the floor is invisible).
* `Oseledets.lambdaBarSublevel_equivariant`: the cocycle step maps the level-`c` space at `x` into
  the level-`c` space at `T x`.

## References

* A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1).
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*, Publ. IHÉS **50** (1979),
  27–58 (Lemma 1.4).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} {T : X → X} {d : ℕ}

/-- **Det-free top-growth finiteness at `x`.** The defining hypothesis of this module: the top
growth sequence `n ↦ (1/n)·log‖A⁽ⁿ⁾(x)‖` is bounded above at `x`. This is inverse-free and
det-free; it holds a.e. by Furstenberg–Kesten and everywhere when `A` has bounded norm. -/
def HasFiniteTopGrowth (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) : Prop :=
  IsBoundedUnder (· ≤ ·) atTop
    (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖)

/-! ### A robust floored `limsup` bound

The single soft-analysis fact that makes the floored non-Archimedean inequality unconditional:
an **eventual** upper bound by a **nonnegative constant** caps the `limsup`, with *no* boundedness
side condition — the nonnegativity of the cap absorbs the `Real`-junk value of an unbounded
`limsup`. -/

/-- If `u n ≤ a` eventually and `0 ≤ a`, then `limsup u ≤ a`. No coboundedness hypothesis: the
`bddBelow` case is `csInf_le`, and the unbounded case gives `limsup u = 0 ≤ a` via
`Real.sInf_of_not_bddBelow`. -/
private theorem limsup_le_of_eventually_le_nonneg {u : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ n in atTop, u n ≤ a) : Filter.limsup u atTop ≤ a := by
  rw [Filter.limsup_eq]
  set S := {b : ℝ | ∀ᶠ n in atTop, u n ≤ b} with hS
  have haS : a ∈ S := h
  by_cases hbdd : BddBelow S
  · exact csInf_le hbdd haS
  · rw [Real.sInf_of_not_bddBelow hbdd]; exact ha

/-! ### The floored non-Archimedean inequality -/

/-- Eventually, the defining sequence is bounded above by the (eventually finite, det-free) value
`(1/n)·log‖A⁽ⁿ⁾(x)‖ + (1/n)·log‖v‖`, *flooring at `0`* — robust to the cocycle killing `v`:
where `A⁽ⁿ⁾(x)·v = 0` the term is `0`, otherwise `‖A⁽ⁿ⁾(x)·v‖ ≤ ‖A⁽ⁿ⁾(x)‖·‖v‖`. -/
private theorem growthSeq_le_floor [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (v : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖
      ≤ max 0 ((n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖) := by
  set M := Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) with hM
  by_cases hMv : M v = 0
  · simp only [hMv, norm_zero, Real.log_zero, mul_zero]
    exact le_max_left _ _
  · refine le_trans ?_ (le_max_right _ _)
    have hMvpos : 0 < ‖M v‖ := norm_pos_iff.mpr hMv
    have hvpos : 0 < ‖v‖ := by
      rw [norm_pos_iff]; rintro rfl; exact hMv (by simp)
    have hMpos : 0 < ‖cocycle A T n x‖ := by
      rw [norm_pos_iff]; rintro h0
      apply hMv
      have : M = 0 := by rw [hM, h0, map_zero]
      rw [this]; rfl
    have hle : ‖M v‖ ≤ ‖cocycle A T n x‖ * ‖v‖ := by
      have := M.le_opNorm v
      rwa [hM, Matrix.l2_opNorm_toEuclideanCLM] at this
    have hlogle : Real.log ‖M v‖ ≤ Real.log ‖cocycle A T n x‖ + Real.log ‖v‖ := by
      rw [← Real.log_mul (ne_of_gt hMpos) (ne_of_gt hvpos)]
      exact Real.log_le_log hMvpos hle
    have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    calc (n : ℝ)⁻¹ * Real.log ‖M v‖
        ≤ (n : ℝ)⁻¹ * (Real.log ‖cocycle A T n x‖ + Real.log ‖v‖) :=
          mul_le_mul_of_nonneg_left hlogle hninv
      _ = (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖ := by ring

/-- **`lambdaBar` is bounded above by the top growth at every `v`** under `HasFiniteTopGrowth`.
Det-free: the upper bound `(1/n)·log‖A⁽ⁿ⁾(x)‖ + (1/n)·log‖v‖`, floored at `0`, is eventually finite
and convergent, so its `limsup` caps `lambdaBar`. -/
theorem lambdaBar_le_of_hasFiniteTopGrowth [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ)
    (T : X → X) (x : X) (hx : HasFiniteTopGrowth A T x) (v : EuclideanSpace ℝ (Fin d)) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖) := by
  obtain ⟨U, hU⟩ := hx
  rw [eventually_map] at hU
  -- `(1/n)·log‖v‖ → 0`, hence eventually `≤ 1`.
  have hlogv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖v‖) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat).mul_const (Real.log ‖v‖)
  have hlogvle : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * Real.log ‖v‖ ≤ 1 :=
    hlogv.eventually_le_const (by norm_num)
  refine ⟨max (U + 1) 0, ?_⟩
  rw [eventually_map]
  filter_upwards [hU, hlogvle] with n hUn hvn
  refine le_trans (growthSeq_le_floor A T x v n) ?_
  rw [max_le_iff]
  refine ⟨le_max_right _ _, ?_⟩
  calc (n : ℝ)⁻¹ * Real.log ‖cocycle A T n x‖ + (n : ℝ)⁻¹ * Real.log ‖v‖
      ≤ U + 1 := add_le_add hUn hvn
    _ ≤ max (U + 1) 0 := le_max_left _ _

/-- **The floored non-Archimedean inequality (unconditional given finite top growth).**
`lambdaBar A T x (v + w) ≤ max (max (lambdaBar A T x v) (lambdaBar A T x w)) 0`. The floor at `0` is
*necessary* (the kernel of a singular cocycle can make `lambdaBar (v + w) = 0` while
`lambdaBar v, lambdaBar w < 0`). -/
theorem lambdaBar_add_le_max_zero [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (hx : HasFiniteTopGrowth A T x) (v w : EuclideanSpace ℝ (Fin d)) :
    lambdaBar A T x (v + w)
      ≤ max (max (lambdaBar A T x v) (lambdaBar A T x w)) 0 := by
  -- Abbreviations for the two source exponents and the floored cap.
  have ha0 : (0 : ℝ) ≤ max (max (lambdaBar A T x v) (lambdaBar A T x w)) 0 := le_max_right _ _
  -- It suffices, for every `ε > 0`, to bound `lambdaBar (v+w) ≤ cap + ε`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- `lambdaBar v, lambdaBar w` are genuine (bounded-above sequences).
  have hbv := lambdaBar_le_of_hasFiniteTopGrowth A T x hx v
  have hbw := lambdaBar_le_of_hasFiniteTopGrowth A T x hx w
  -- Eventually `growthSeq v n < lambdaBar v + ε/2` and likewise for `w`.
  have hev : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖
        < lambdaBar A T x v + ε / 2 :=
    eventually_lt_of_limsup_lt
      (show lambdaBar A T x v < lambdaBar A T x v + ε / 2 by linarith) hbv
  have hew : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) w‖
        < lambdaBar A T x w + ε / 2 :=
    eventually_lt_of_limsup_lt
      (show lambdaBar A T x w < lambdaBar A T x w + ε / 2 by linarith) hbw
  -- Eventually `(1/n)·log 2 ≤ ε/2`.
  have hlog2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat).mul_const (Real.log 2)
  have hlog2le : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * Real.log 2 ≤ ε / 2 :=
    hlog2.eventually_le_const (by linarith)
  -- Assemble the eventual bound `growthSeq (v+w) n ≤ cap + ε`.
  set a := max (max (lambdaBar A T x v) (lambdaBar A T x w)) 0 with ha
  refine limsup_le_of_eventually_le_nonneg (by rw [ha]; positivity) ?_
  filter_upwards [hev, hew, hlog2le, eventually_ge_atTop 1] with n hvn hwn h2n hn1
  set Mvw := Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) (v + w) with hMvw
  have hnpos : (0 : ℝ) < (n : ℝ)⁻¹ := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    positivity
  have hlog2nn : 0 ≤ (n : ℝ)⁻¹ * Real.log 2 := by positivity
  -- Per-`n` triangle bound, robust to the cocycle killing `v + w`.
  set Av := Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v with hAv
  set Aw := Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) w with hAw
  have hsplit : Mvw = Av + Aw := by rw [hMvw, hAv, hAw, map_add]
  by_cases hz : Mvw = 0
  · rw [hz, norm_zero, Real.log_zero, mul_zero]; positivity
  · have hpos : 0 < ‖Mvw‖ := norm_pos_iff.mpr hz
    have htri : ‖Mvw‖ ≤ 2 * max ‖Av‖ ‖Aw‖ := by
      have h1 : ‖Mvw‖ ≤ ‖Av‖ + ‖Aw‖ := by rw [hsplit]; exact norm_add_le _ _
      have h2 : ‖Av‖ + ‖Aw‖ ≤ 2 * max ‖Av‖ ‖Aw‖ := by
        rcases le_total ‖Av‖ ‖Aw‖ with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith
      linarith
    -- `max ‖Av‖ ‖Aw‖ > 0` because `‖Mvw‖ > 0` and `‖Mvw‖ ≤ 2·max`.
    have hmaxpos : 0 < max ‖Av‖ ‖Aw‖ := by nlinarith [norm_nonneg Av, norm_nonneg Aw]
    have hlog : Real.log ‖Mvw‖ ≤ Real.log 2 + Real.log (max ‖Av‖ ‖Aw‖) := by
      have hstep : Real.log ‖Mvw‖ ≤ Real.log (2 * max ‖Av‖ ‖Aw‖) := Real.log_le_log hpos htri
      rwa [Real.log_mul (by norm_num) (ne_of_gt hmaxpos)] at hstep
    -- Multiply by `(1/n) ≥ 0`, and split the `log max`.
    have hgs : (n : ℝ)⁻¹ * Real.log ‖Mvw‖
        ≤ (n : ℝ)⁻¹ * Real.log 2
          + max ((n : ℝ)⁻¹ * Real.log ‖Av‖) ((n : ℝ)⁻¹ * Real.log ‖Aw‖) := by
      have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := le_of_lt hnpos
      -- `log (max ‖Av‖ ‖Aw‖) ≤ max (log ‖Av‖) (log ‖Aw‖)` (robust to a zero factor: the larger
      -- norm is positive, and its log is one of the two — hence `≤` their max).
      have hlogmax_le : Real.log (max ‖Av‖ ‖Aw‖) ≤ max (Real.log ‖Av‖) (Real.log ‖Aw‖) := by
        rcases le_total ‖Av‖ ‖Aw‖ with h | h
        · rw [max_eq_right h]; exact le_max_right _ _
        · rw [max_eq_left h]; exact le_max_left _ _
      calc (n : ℝ)⁻¹ * Real.log ‖Mvw‖
          ≤ (n : ℝ)⁻¹ * (Real.log 2 + Real.log (max ‖Av‖ ‖Aw‖)) :=
            mul_le_mul_of_nonneg_left hlog hninv
        _ = (n : ℝ)⁻¹ * Real.log 2 + (n : ℝ)⁻¹ * Real.log (max ‖Av‖ ‖Aw‖) := by ring
        _ ≤ (n : ℝ)⁻¹ * Real.log 2
              + (n : ℝ)⁻¹ * max (Real.log ‖Av‖) (Real.log ‖Aw‖) := by
            gcongr
        _ = (n : ℝ)⁻¹ * Real.log 2
              + max ((n : ℝ)⁻¹ * Real.log ‖Av‖) ((n : ℝ)⁻¹ * Real.log ‖Aw‖) := by
            rw [mul_max_of_nonneg _ _ hninv]
    -- Combine with `hvn, hwn, h2n` and `lambdaBar v, lambdaBar w ≤ a`.
    have hMvle : lambdaBar A T x v ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
    have hMwle : lambdaBar A T x w ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
    have hmaxlt : max ((n : ℝ)⁻¹ * Real.log ‖Av‖) ((n : ℝ)⁻¹ * Real.log ‖Aw‖)
        ≤ a + ε / 2 := by
      rw [max_le_iff]
      exact ⟨le_of_lt (lt_of_lt_of_le hvn (by linarith)),
        le_of_lt (lt_of_lt_of_le hwn (by linarith))⟩
    calc (n : ℝ)⁻¹ * Real.log ‖Mvw‖
        ≤ (n : ℝ)⁻¹ * Real.log 2
            + max ((n : ℝ)⁻¹ * Real.log ‖Av‖) ((n : ℝ)⁻¹ * Real.log ‖Aw‖) := hgs
      _ ≤ ε / 2 + (a + ε / 2) := add_le_add h2n hmaxlt
      _ = a + ε := by ring

/-! ### The genuine ultrametric growth function `max (lambdaBar ·) 0` -/

/-- **`v ↦ max (lambdaBar A T x v) 0` is an ultrametric growth function** (under finite top
growth). Scaling-invariance is the unconditional `lambdaBar_smul`; the non-Archimedean inequality is
the floored `lambdaBar_add_le_max_zero` (the floor at `0` is what makes `g` genuinely
non-Archimedean despite the singular kernel). -/
theorem isUltrametricGrowth_max_lambdaBar [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ)
    (T : X → X) (x : X) (hx : HasFiniteTopGrowth A T x) :
    IsUltrametricGrowth (fun v : EuclideanSpace ℝ (Fin d) => max (lambdaBar A T x v) 0) := by
  refine ⟨?_, ?_⟩
  · -- scaling: `lambdaBar (c • v) = lambdaBar v` for `c ≠ 0`.
    intro c v hc
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [lambdaBar_smul A T x hc v hv]
  · -- non-Archimedean: from `lambdaBar_add_le_max_zero`.
    intro v w _ _ _
    have h := lambdaBar_add_le_max_zero A T x hx v w
    -- `max (lambdaBar (v+w)) 0 ≤ max (max (lambdaBar v) 0) (max (lambdaBar w) 0)`.
    refine max_le (le_trans h ?_) (le_max_of_le_left (le_max_right _ _))
    refine max_le (max_le ?_ ?_) (le_max_of_le_left (le_max_right _ _))
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_right (le_max_left _ _)

/-! ### The sublevel submodule -/

/-- **The algebraic forward sublevel submodule** at threshold `c`: the sublevel set of the
ultrametric growth function `v ↦ max (lambdaBar A T x v) 0`. For `c ≥ 0` it is
`{v | lambdaBar A T x v ≤ c} ∪ {0}` (`mem_lambdaBarSublevel_iff`); for `c < 0` the floor
collapses it to `{0}`. Det-free and inverse-free. -/
noncomputable def lambdaBarSublevel [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (c : ℝ) (x : X) (hx : HasFiniteTopGrowth A T x) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (isUltrametricGrowth_max_lambdaBar A T x hx).sublevel c

@[simp]
theorem mem_lambdaBarSublevel [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (c : ℝ) (x : X) (hx : HasFiniteTopGrowth A T x) (v : EuclideanSpace ℝ (Fin d)) :
    v ∈ lambdaBarSublevel A T c x hx ↔ v = 0 ∨ max (lambdaBar A T x v) 0 ≤ c := Iff.rfl

/-- **Antitone in the threshold.** `c ≤ c'` makes the level-`c` space a subspace of the level-`c'`
space. -/
theorem lambdaBarSublevel_antitone [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (hx : HasFiniteTopGrowth A T x) {c c' : ℝ} (hcc : c ≤ c') :
    lambdaBarSublevel A T c x hx ≤ lambdaBarSublevel A T c' x hx :=
  (isUltrametricGrowth_max_lambdaBar A T x hx).sublevel_mono hcc

/-- **Membership in the genuine regime `0 ≤ c`.** For nonnegative thresholds the floor is invisible:
`v ∈ lambdaBarSublevel A T c x ↔ v = 0 ∨ lambdaBar A T x v ≤ c`. (For `c < 0` the right disjunct
would over-count kernel directions whose `lambdaBar` is `< 0`, which is exactly why the construction
floors at `0`.) -/
theorem mem_lambdaBarSublevel_iff [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    {c : ℝ} (hc : 0 ≤ c) (x : X) (hx : HasFiniteTopGrowth A T x)
    (v : EuclideanSpace ℝ (Fin d)) :
    v ∈ lambdaBarSublevel A T c x hx ↔ v = 0 ∨ lambdaBar A T x v ≤ c := by
  rw [mem_lambdaBarSublevel]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (le_trans (le_max_left _ _) h)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (max_le h hc)

/-! ### The cocycle-step inequality and equivariance

The cocycle reindexing `A⁽ⁿ⁾(Tx)·(A x·v) = A⁽ⁿ⁺¹⁾(x)·v` ties the image defining sequence at `T x`
to a one-shifted copy of the defining sequence at `x`. Writing
`L n = log‖A⁽ⁿ⁾(Tx)·(A x·v)‖`, the image sequence is `f n = n⁻¹·L n` (the defining sequence at
`T x`) and the shifted source sequence is `g n = (n+1)⁻¹·L n` (the source sequence at `n+1`). They
are related by `f n = ((n+1)/n)·g n` (for `n ≥ 1`). The **full identity** at the spectrum level
needs `f` bounded on *both* sides (lower boundedness is the invertible/det data, see
`Oseledets.lambdaBar_equivariant`). The **one-sided inequality** below — which is all the sublevel
filtration requires — is **det-free**: where `L n ≥ 0` we have `f n = g n + g n/n` with `g` bounded
above by `HasFiniteTopGrowth A T x`, and where `L n < 0` we have `f n < 0`, so the floor at `0`
absorbs it. -/

/-- The `(n+1)`-th source summand equals the `n`-th image summand of `w = A x · v`, by the cocycle
identity `A⁽ⁿ⁺¹⁾(x)·v = A⁽ⁿ⁾(Tx)·(A x·v)` — the elementary reindexing, det-free. -/
private theorem lambdaBarSummand_succ (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (v : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ((n : ℝ) + 1)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T (n + 1) x) v‖
      = ((n : ℝ) + 1)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n (T x))
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v)‖ := by
  rw [cocycle_succ, map_mul, ContinuousLinearMap.mul_apply]

/-- **The det-free cocycle-step inequality** `lambdaBar A T (T x) (A x · v)
≤ max (lambdaBar A T x v) 0`. No invertibility: the image exponent at `T x` is dominated by the
(floored) source exponent at `x`. The floor at `0` is what makes this hold without a lower bound on
the image sequence. -/
theorem lambdaBar_step_le [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (hx : HasFiniteTopGrowth A T x) (v : EuclideanSpace ℝ (Fin d)) :
    lambdaBar A T (T x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v)
      ≤ max (lambdaBar A T x v) 0 := by
  set w := Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v with hw
  -- The shared log-data `L n = log‖A⁽ⁿ⁾(Tx)·w‖`.
  set L : ℕ → ℝ := fun n =>
    Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n (T x)) w‖ with hL
  -- LHS = `limsup (n⁻¹·L n)`.
  change Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ * L n) atTop ≤ max (lambdaBar A T x v) 0
  -- `lambdaBar A T x v = limsup ((n+1)⁻¹·L n)` (reindex source by `+1` via the cocycle identity).
  have hgshift : lambdaBar A T x v
      = Filter.limsup (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * L n) atTop := by
    have hsrc : lambdaBar A T x v = Filter.limsup
        (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * Real.log
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T (n + 1) x) v‖) atTop := by
      rw [show lambdaBar A T x v = Filter.limsup (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖) atTop from rfl,
        ← Filter.limsup_nat_add (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖) 1]
      congr 1; funext n; push_cast; ring_nf
    rw [hsrc]
    congr 1; funext n; rw [lambdaBarSummand_succ]
  rw [hgshift]
  set g : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ * L n with hg
  -- `g` is bounded above: it equals the (bounded-above) source summand at `n + 1`.
  have hgbdd : IsBoundedUnder (· ≤ ·) atTop g := by
    obtain ⟨U, hU⟩ := lambdaBar_le_of_hasFiniteTopGrowth A T x hx v
    rw [eventually_map] at hU
    rw [eventually_atTop] at hU
    obtain ⟨N, hN⟩ := hU
    refine ⟨U, ?_⟩
    rw [eventually_map, eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hsum := hN (n + 1) (Nat.le_succ_of_le hn)
    change ((n : ℝ) + 1)⁻¹ * L n ≤ U
    -- `g n = source summand at (n+1)` via `lambdaBarSummand_succ`.
    have heq : ((n : ℝ) + 1)⁻¹ * L n
        = ((n : ℝ) + 1)⁻¹ * Real.log
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T (n + 1) x) v‖ := by
      rw [hL, lambdaBarSummand_succ]
    rw [heq]
    -- match `(n+1)⁻¹` with `((n+1 : ℕ) : ℝ)⁻¹`.
    have hcast : ((n : ℝ) + 1)⁻¹ = (((n + 1 : ℕ) : ℝ))⁻¹ := by push_cast; ring
    rw [hcast]; exact hsum
  set M := Filter.limsup g atTop with hM
  -- For each `ε > 0`, bound `limsup (n⁻¹·L n) ≤ max M 0 + ε`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine limsup_le_of_eventually_le_nonneg (by positivity) ?_
  -- Eventually `g n ≤ M + ε/2` (g bounded above) and `max (g n) 0 / n ≤ ε/2`.
  have hgev : ∀ᶠ n : ℕ in atTop, g n ≤ M + ε / 2 :=
    (eventually_lt_of_limsup_lt (by rw [hM]; linarith) hgbdd).mono fun n h => le_of_lt h
  -- `max (g n) 0` is bounded in `[0, max U 0]`; divided by `n` it → 0.
  obtain ⟨U, hU⟩ := hgbdd
  rw [eventually_map, eventually_atTop] at hU
  obtain ⟨N₀, hN₀⟩ := hU
  have hdiv : Tendsto (fun n : ℕ => max U 0 * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat).const_mul (max U 0)
  have hdivle : ∀ᶠ n : ℕ in atTop, max U 0 * (n : ℝ)⁻¹ ≤ ε / 2 :=
    hdiv.eventually_le_const (by linarith)
  filter_upwards [hgev, hdivle, Filter.eventually_atTop.2 ⟨N₀, fun n hn => hn⟩,
    eventually_ge_atTop 1] with n hgn hdn hn0 hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hUbnd : g n ≤ U := hN₀ n hn0
  -- Per-`n`: `n⁻¹·L n ≤ max (g n + g n / n) 0 = max (g n) 0 * (1 + 1/n)`.
  have hgL : g n = ((n : ℝ) + 1)⁻¹ * L n := rfl
  have hfg : (n : ℝ)⁻¹ * L n = g n + g n * (n : ℝ)⁻¹ := by
    rw [hgL]; field_simp
  have hsplit : (n : ℝ)⁻¹ * L n ≤ max (g n) 0 + max (g n) 0 * (n : ℝ)⁻¹ := by
    rcases le_or_gt 0 (L n) with hLnn | hLneg
    · -- `L n ≥ 0` ⟹ `g n ≥ 0`, so `max (g n) 0 = g n` and the two sides coincide.
      have hgnn : 0 ≤ g n := by rw [hgL]; positivity
      rw [hfg, max_eq_left hgnn]
    · -- `L n < 0` ⟹ `n⁻¹·L n < 0 ≤ RHS`.
      have hneg : (n : ℝ)⁻¹ * L n < 0 := mul_neg_of_pos_of_neg (by positivity) hLneg
      refine le_trans (le_of_lt hneg) ?_
      have : 0 ≤ max (g n) 0 := le_max_right _ _
      positivity
  -- Bound `max (g n) 0 ≤ M + ε/2` and `max (g n) 0 * n⁻¹ ≤ ε/2`.
  have hmaxle : max (g n) 0 ≤ max M 0 + ε / 2 := by
    rw [max_le_iff]
    exact ⟨le_trans hgn (by have := le_max_left M 0; linarith),
      le_trans (le_max_right M 0) (by linarith)⟩
  have hmaxU : max (g n) 0 ≤ max U 0 := max_le_max hUbnd (le_refl 0)
  have hmaxdiv : max (g n) 0 * (n : ℝ)⁻¹ ≤ ε / 2 := by
    refine le_trans ?_ hdn
    exact mul_le_mul_of_nonneg_right hmaxU (by positivity)
  calc (n : ℝ)⁻¹ * L n
      ≤ max (g n) 0 + max (g n) 0 * (n : ℝ)⁻¹ := hsplit
    _ ≤ (max M 0 + ε / 2) + ε / 2 := add_le_add hmaxle hmaxdiv
    _ = max M 0 + ε := by ring

/-- **Equivariance of the algebraic sublevel filtration.** The cocycle step `A x ·` maps the
level-`c` space at `x` into the level-`c` space at `T x`: if `v ∈ lambdaBarSublevel A T c x`, then
`A x · v ∈ lambdaBarSublevel A T c (T x)`. Det-free, from `lambdaBar_step_le`. -/
theorem lambdaBarSublevel_equivariant [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (c : ℝ) (x : X) (hx : HasFiniteTopGrowth A T x) (hTx : HasFiniteTopGrowth A T (T x))
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ lambdaBarSublevel A T c x hx) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v ∈ lambdaBarSublevel A T c (T x) hTx := by
  rw [mem_lambdaBarSublevel] at hv ⊢
  -- From `v ∈`: either `v = 0` (then the image is `0`), or `max (lambdaBar x v) 0 ≤ c`.
  rcases hv with rfl | hv
  · left; simp
  · right
    -- `max (lambdaBar (Tx)(A x·v)) 0 ≤ max (lambdaBar x v) 0 ≤ c`.
    have hstep := lambdaBar_step_le A T x hx v
    rw [max_le_iff]
    have hc : max (lambdaBar A T x v) 0 ≤ c := hv
    exact ⟨le_trans hstep hc, le_trans (le_max_right (lambdaBar A T x v) 0) hc⟩

end Oseledets
