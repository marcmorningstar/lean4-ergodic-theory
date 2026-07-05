/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.ExponentSums

/-!
# The exterior (wedge) cocycle and the growth-rate characterization

This module is purely *additive* on top of the spectrum object
`ErgodicTheory.exponents : Fin d → ℝ` and the partial sums `ErgodicTheory.gammaK` (`Γ_k`), under the
standing hypotheses (`hT : Ergodic T μ`, `hA : ∀ x, (A x).det ≠ 0`, `hAmeas : Measurable A`,
`hint : IntegrableLogNorm A μ`, `hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ`, together with
`[IsProbabilityMeasure μ]`).

It realizes the **exterior / wedge characterization** of the partial sums of Lyapunov
exponents. Three layers:

* **The exterior cocycle is a cocycle.** For each `k`, the `k`-th compound (exterior power)
  `ExteriorNorm.compoundMatrix k (A ·)` generates a matrix cocycle, and its iterate is the
  compound of the iterate: `cocycle (extGen k A) T n x = compoundMatrix k (cocycle A T n x)`
  (`cocycle_extGen_eq_compound`). This is precisely Cauchy–Binet
  (`ExteriorNorm.compoundMatrix_mul`) packaged dynamically.
* **The `k`-volume growth rate.** For `μ`-a.e. `x`,
  `(1/n) log ‖compoundMatrix k (cocycle A T n x)‖ → Γ_k` (`tendsto_log_opNorm_compound_cocycle`).
  The operator norm `‖compoundMatrix k (cocycle A T n x)‖` is exactly the product of the
  top-`k` singular values (`ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound`), i.e. the
  norm of the largest `k × k` minor block — the `k`-dimensional volume growth rate. We take
  the *scalar* route (rewriting through `sprod`), which avoids re-establishing
  Furstenberg–Kesten integrability for the compound generator.
* **The positive-exponent sum as a maximal partial sum.** Since the partial sums
  `Γ_k = ∑_{i<k} exponents i` are partial sums of the antitone sequence `exponents`, they are
  maximized exactly at `k₊ = #{i | 0 < exponents i}`, the number of positive exponents. Hence
  `sumPosExp = Γ_{k₊}` (`sumPosExp_eq_gammaK_card_pos`).

## Main definitions

* `ErgodicTheory.extGen` — the `k`-th exterior (compound) cocycle generator
  `x ↦ compoundMatrix k (A x)`.

## Main results

* `ErgodicTheory.cocycle_extGen_eq_compound` — the exterior power of the cocycle is the cocycle of
  the exterior power (Cauchy–Binet, packaged dynamically).
* `ErgodicTheory.tendsto_log_opNorm_compound_cocycle` — the `k`-volume / largest-minor growth rate
  equals `Γ_k`.
* `ErgodicTheory.gammaK_eq_sum_top_exponents` (re-exported from `ExponentSums`) — `Γ_k` is the sum
  of the top-`k` exponents.
* `ErgodicTheory.gammaK_one_eq_topExponent` — `Γ_1` is the top Lyapunov exponent.
* `ErgodicTheory.sumPosExp_eq_gammaK_card_pos` — the positive-exponent sum is the partial sum at
  the number of positive exponents, i.e. the maximal partial sum.

## Implementation notes

The compound generator `extGen k A` has values in the `⋀^k`-finrank-indexed square matrices
`Matrix (Fin (finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))) … ℝ`; the cocycle machinery
(`cocycle`, `cocycle_succ`, `cocycle_one`) is generic over the matrix index type, so it
applies verbatim.

The Furstenberg–Kesten-on-the-compound-generator route (feeding `extGen k A` to the top-exponent
FK theorem) is **not** used and **not** required: it would demand its own integrability bound
`log⁺‖C_k(A)‖ ≤ k · log⁺‖A‖ + C`. The scalar route through `sprod` is far cheaper and is what we
use here. The cocycle structure (`cocycle_extGen_eq_compound`) is nonetheless proved, since it is
the conceptual content of "the wedge of the cocycle is a cocycle".

## References

* M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*,
  Israel J. Math. **32** (1979), 356–362.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]
variable {μ : Measure X} {T : X → X}

/-! ## The exterior (compound) cocycle generator -/

section ExtGen

/-- **The `k`-th exterior (compound) cocycle generator.** It sends `x` to the `k`-th compound
matrix `C_k(A x)` (whose entries are the `k × k` minors of `A x`). Its iterated cocycle is the
compound of the iterated cocycle — see `cocycle_extGen_eq_compound`. -/
noncomputable def extGen (k : ℕ) (A : X → Matrix (Fin d) (Fin d) ℝ) :
    X → Matrix (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d)))))
      (Fin (Module.finrank ℝ (⋀[ℝ]^k (EuclideanSpace ℝ (Fin d))))) ℝ :=
  fun x => ExteriorNorm.compoundMatrix k (A x)

omit [MeasurableSpace X] [NeZero d] in
/-- **The exterior power of the cocycle is the cocycle of the exterior power.** The iterate of
the compound cocycle generator equals the compound of the cocycle iterate:
`cocycle (extGen k A) T n x = C_k(cocycle A T n x)`.

This is Cauchy–Binet (`ExteriorNorm.compoundMatrix_mul`) packaged dynamically: induction on `n`
with `compoundMatrix_one` for the base and `compoundMatrix_mul` for the step. It shows that the
`k`-th exterior power of a matrix cocycle is itself a matrix cocycle. -/
theorem cocycle_extGen_eq_compound (k : ℕ) (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X) :
    cocycle (extGen k A) T n x = ExteriorNorm.compoundMatrix k (cocycle A T n x) := by
  induction n generalizing x with
  | zero => simp [ExteriorNorm.compoundMatrix_one]
  | succ n ih =>
    rw [cocycle_succ, cocycle_succ, ih (T x), extGen, ExteriorNorm.compoundMatrix_mul]

end ExtGen

/-! ## The `k`-volume / largest-minor growth rate -/

section Growth

variable [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

/-- **The `k`-volume growth rate equals `Γ_k`.** For `μ`-a.e. `x`,
`(1/n) log ‖C_k(cocycle A T n x)‖ → Γ_k`. The operator norm of the compound matrix is the
product of the top-`k` singular values (`ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound`),
i.e. the largest `k × k` minor growth / `k`-dimensional volume growth; its growth rate is the
partial sum `Γ_k` of the top-`k` Lyapunov exponents.

We rewrite `‖C_k(cocycle A T n x)‖ = sprod_k` and apply `gammaK_tendsto` (the scalar route),
avoiding any Furstenberg–Kesten integrability bound for the compound generator. -/
theorem tendsto_log_opNorm_compound_cocycle {k : ℕ} (hk : k ≤ d) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖ExteriorNorm.compoundMatrix k (cocycle A T n x)‖) atTop
      (𝓝 (gammaK hT hA hAmeas hint hint' hk)) := by
  filter_upwards [gammaK_tendsto hT hA hAmeas hint hint' hk] with x hx
  refine hx.congr (fun n => ?_)
  rw [sprod, ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound]

/-- **`Γ_1` is the top Lyapunov exponent.** The first partial sum `Γ_1 = ∑_{i<1} exponents i`
equals `exponents 0 = topExponent`. -/
theorem gammaK_one_eq_topExponent (h1 : 1 ≤ d) :
    gammaK hT hA hAmeas hint hint' h1 = topExponent hT hA hAmeas hint hint' := by
  rw [gammaK_eq_sum_top_exponents hT hA hAmeas hint hint' h1, topExponent,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_one]
  simp only [Nat.lt_one_iff, dif_pos]
  rfl

end Growth

/-! ## The positive-exponent sum as a maximal partial sum -/

section PositiveSum

omit [NeZero d] in
/-- The number of indices `≤ (i:ℕ)` in `Fin d` is `(i:ℕ) + 1`. -/
private lemma card_filter_le_eq (i : Fin d) :
    (Finset.univ.filter (fun j : Fin d => (j : ℕ) ≤ (i : ℕ))).card = (i : ℕ) + 1 := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun m => if m ≤ (i : ℕ) then 1 else 0)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  rw [show ({x ∈ Finset.range d | x ≤ (i : ℕ)}) = Finset.range ((i : ℕ) + 1) from by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; have := i.2; omega]
  simp

omit [NeZero d] in
/-- The number of indices `< n` in `Fin d` (for `n ≤ d`) is `n`. -/
private lemma card_filter_lt_eq {n : ℕ} (hn : n ≤ d) :
    (Finset.univ.filter (fun j : Fin d => (j : ℕ) < n)).card = n := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun m => if m < n then 1 else 0)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  rw [show ({x ∈ Finset.range d | x < n}) = Finset.range n from by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  simp

omit [NeZero d] in
/-- **Arithmetic core: an antitone sequence's positive entries are the top prefix.**
For an antitone `lam : Fin d → ℝ` and `i : Fin d`, `lam i` is strictly positive iff its index
is below the count of positive entries. -/
private lemma pos_iff_lt_card_pos {lam : Fin d → ℝ} (hanti : Antitone lam) (i : Fin d) :
    0 < lam i ↔ (i : ℕ) < (Finset.univ.filter (fun j => 0 < lam j)).card := by
  classical
  set kp := (Finset.univ.filter (fun j => 0 < lam j)).card with hkp
  constructor
  · -- if `0 < lam i` then by antitonicity all `j ≤ i` are positive, so `i + 1 ≤ kp`.
    intro hi
    have hsub : (Finset.univ.filter (fun m : Fin d => (m : ℕ) ≤ (i : ℕ)))
        ⊆ Finset.univ.filter (fun m => 0 < lam m) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_univ m, lt_of_lt_of_le hi
        (hanti (by rw [Fin.le_iff_val_le_val]; exact hm.2))⟩
    have hcard := Finset.card_le_card hsub
    rw [card_filter_le_eq i] at hcard
    omega
  · -- if `(i:ℕ) < kp` but `lam i ≤ 0`, then all `j ≥ i` are non-positive, so the positive
    -- filter is contained in `{j | (j:ℕ) < i}`, giving `kp ≤ i`, a contradiction.
    intro hi
    by_contra hle
    rw [not_lt] at hle
    have hsub : Finset.univ.filter (fun m => 0 < lam m)
        ⊆ Finset.univ.filter (fun m : Fin d => (m : ℕ) < (i : ℕ)) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      refine ⟨Finset.mem_univ m, ?_⟩
      by_contra hmi
      rw [not_lt] at hmi
      exact absurd hm.2 (not_lt.mpr (le_trans (hanti (by rw [Fin.le_iff_val_le_val]; exact hmi))
        hle))
    have hcard := Finset.card_le_card hsub
    rw [card_filter_lt_eq (le_of_lt i.2)] at hcard
    omega

variable [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)

/-- **The positive-exponent sum is the maximal partial sum.** Writing
`k₊ = #{i | 0 < exponents i}` for the number of strictly positive Lyapunov exponents, the sum of
the positive exponents equals the partial sum `Γ_{k₊} = ∑_{i<k₊} exponents i`.

Since `exponents` is antitone, its strictly positive entries are exactly the top `k₊` indices, so
the filtered positive sum coincides with the top-`k₊` prefix sum, which is `Γ_{k₊}` by
`gammaK_eq_sum_top_exponents`. Equivalently, among all partial sums `Γ_k` of the antitone
sequence `exponents`, the maximum is attained exactly at `k = k₊` (adding any non-positive
exponent does not increase the sum). -/
theorem sumPosExp_eq_gammaK_card_pos
    (hk : (Finset.univ.filter (fun i => 0 < exponents hT hA hAmeas hint hint' i)).card ≤ d) :
    sumPosExp hT hA hAmeas hint hint' = gammaK hT hA hAmeas hint hint' hk := by
  classical
  set kp := (Finset.univ.filter (fun i => 0 < exponents hT hA hAmeas hint hint' i)).card with hkp
  rw [gammaK_eq_sum_top_exponents hT hA hAmeas hint hint' hk, sumPosExp]
  -- bijection `{i | 0 < exponents i} ↔ Fin kp`, `j ↦ (j:ℕ)`, inverse `i ↦ Fin.castLE hk i`.
  -- membership of a positive index in `Fin kp`:
  have hmem : ∀ j ∈ Finset.univ.filter (fun i => 0 < exponents hT hA hAmeas hint hint' i),
      (j : ℕ) < kp := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [hkp, ← pos_iff_lt_card_pos (exponents_antitone hT hA hAmeas hint hint')]
    exact hj.2
  refine Finset.sum_bij'
    (fun (j : Fin d) (hj : j ∈ _) => (⟨(j : ℕ), hmem j hj⟩ : Fin kp))
    (fun (i : Fin kp) (_ : i ∈ Finset.univ) => Fin.castLE hk i)
    (fun j _ => Finset.mem_univ _) ?_ (fun j _ => Fin.ext rfl) (fun i _ => rfl) (fun j _ => rfl)
  · -- the inverse map lands in the positive filter
    intro i _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [pos_iff_lt_card_pos (exponents_antitone hT hA hAmeas hint hint')]
    exact i.2

end PositiveSum

end ErgodicTheory
