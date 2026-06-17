/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Deterministic core of Ruelle's spectral upper bound

This file formalises, deterministically, the analytic heart of Ruelle's argument
(Publ. IHES 50, 1979, Lemma 1.4 / Prop 1.3) for the per-vector spectral upper bound

  `limsup (1/n) log ‖Mⁿ v‖ ≤ λ⁽ʳ⁾`   for `v` in the limit slow space.

We abstract the SVD data of a sequence of operators `f n : E →ₗ E` on a finite-dimensional
real inner product space `E` by:

* a per-time orthonormal right-singular basis `e n : OrthonormalBasis (Fin d) ℝ E`;
* per-time singular values `σ n : Fin d → ℝ` (`≥ 0`);
* the defining Parseval identity
    `‖f n u‖² = Σ_j (σ n j)² · ⟪e n j, u⟫²`.

From this single identity we derive both halves of Ruelle's one-step sandwich:

* `normSq_apply_le_of_mem_span` — restricted SVD upper bound on a "slow" right-singular span;
* `singularValue_norm_proj_le_norm_apply` — SVD lower bound via a "fast" right-singular projection.

The convention here matches Ruelle's (increasing): the index set is split by a *cut* into a
"slow / low" part (small indices, small singular values) and a "fast / high" part (large indices,
large singular values).

## Main results

* `oneStep_sandwich`: the one-step two-sided estimate.  For `u` in the slow span at time `n`,
  the fast projection of `f (n+1) u` decays at the full pairwise band gap
  (`t·‖fastProj‖ ≤ b·s·‖u‖`),
  combining the slow SVD upper bound at time `n` with the fast SVD lower bound at time `n+1` through
  the one-step operator bound `b`.
* The `k`-uniform forward leakage chain.  `geometric_recursion` solves the discrete linear
  recursion `a(i+1) ≤ q·a i + c i` exactly; `geometric_recursion_uniform` and `chain_leakage_exp`
  package it with a uniform source rate / explicit `exp` rates, giving the sub-exponential envelope
  `a k ≤ exp(-kγ)·a 0 + R·k·exp(-(k-1)·min γ γ')` at the full pairwise gap.  This is the analytic
  engine of Ruelle's Lemma 1.4 band-distance induction (his displayed geometric-series computation).
* `orthogonal_block_mass_symm`: the reverse-side block-norm symmetry.  For any orthonormal
  change of basis the off-diagonal block over `(A,Aᶜ)` carries the same squared (Frobenius) mass as
  the transposed block over `(Aᶜ,A)`, so the slow→fast and fast→slow leakages coincide.  This is
  pure orthogonality (Parseval in each basis), pinning the reverse side to the forward rate for the
  dominant gap.
* `normSq_apply_le_band_sum`: the band-grouped Parseval envelope (Ruelle's part b).  For a
  partition of the right-singular indices into bands with per-band singular-value caps,
  `‖f n v‖² ≤ Σ_r (cap r)²·‖fastProj n (band r) v‖²`; fed the leakage envelopes this yields the
  `λ⁽ᵖ⁾` growth.
-/

open Filter Topology
open scoped RealInnerProductSpace BigOperators

noncomputable section

namespace Oseledets.RuelleCofactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ}

/-- **SVD data** for a sequence of operators on a finite-dimensional real inner product space.

`e n` is the time-`n` orthonormal right-singular basis, `σ n j ≥ 0` the `j`-th singular value, and
`apply n u = f n u` the image, satisfying the Parseval identity
`‖apply n u‖² = Σ_j (σ n j)² ⟪e n j, u⟫²`. -/
structure SVDData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ) where
  /-- The (right-singular) orthonormal basis at time `n`. -/
  e : ℕ → OrthonormalBasis (Fin d) ℝ E
  /-- The singular values at time `n`. -/
  σ : ℕ → Fin d → ℝ
  /-- Singular values are nonnegative. -/
  σ_nonneg : ∀ n j, 0 ≤ σ n j
  /-- The image of `u` under the time-`n` operator. -/
  apply : ℕ → E → E
  /-- The Parseval / SVD identity for the squared norm of the image. -/
  normSq_apply : ∀ n u,
    ‖apply n u‖ ^ 2 = ∑ j, (σ n j) ^ 2 * ⟪e n j, u⟫ ^ 2

namespace SVDData

variable (S : SVDData E d)

/-- Parseval for the orthonormal basis: `‖u‖² = Σ_j ⟪e n j, u⟫²`. -/
lemma normSq_eq (n : ℕ) (u : E) : ‖u‖ ^ 2 = ∑ j, ⟪S.e n j, u⟫ ^ 2 := by
  have := (S.e n).sum_inner_mul_inner u u
  -- `(e n).sum_inner_mul_inner` : `∑ i, ⟪u, e i⟫ * ⟪e i, u⟫ = ⟪u, u⟫`
  rw [← real_inner_self_eq_norm_sq]
  rw [← (S.e n).sum_inner_mul_inner u u]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (S.e n j) u]
  ring

/-- **SVD upper bound on a slow span.**  If `u` lies in the span of the right-singular vectors
`e n j` with `j` in `lo` (the "slow / low" indices), and every such singular value is `≤ s`, then
`‖f n u‖ ≤ s · ‖u‖`.  Pure SVD: in the Parseval sum only the `lo`-terms survive, each bounded by
`s² ⟪e n j, u⟫²`. -/
lemma normSq_apply_le_of_mem_span (n : ℕ) (lo : Finset (Fin d)) (s : ℝ) (hs : 0 ≤ s)
    (hσ : ∀ j ∈ lo, S.σ n j ≤ s) (u : E)
    (hu : u ∈ Submodule.span ℝ (Set.range (fun j : lo => S.e n (j : Fin d)))) :
    ‖S.apply n u‖ ^ 2 ≤ s ^ 2 * ‖u‖ ^ 2 := by
  -- Components outside `lo` vanish.
  have hzero : ∀ j ∉ lo, ⟪S.e n j, u⟫ = 0 := by
    intro j hj
    -- `u` is in the span of `e n i, i ∈ lo`; `e n j` is orthogonal to each.
    refine Submodule.span_induction
      (p := fun w _ => ⟪S.e n j, w⟫ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨i, rfl⟩
      have hij : (i : Fin d) ≠ j := by
        rintro rfl; exact hj i.2
      exact (S.e n).orthonormal.2 (by simpa using hij.symm)
    · simp
    · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
    · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
  rw [S.normSq_apply, S.normSq_eq n u]
  rw [Finset.mul_sum]
  -- Split the LHS sum over `lo` and its complement; complement terms are 0.
  have hsplit : ∑ j, (S.σ n j) ^ 2 * ⟪S.e n j, u⟫ ^ 2
      = ∑ j ∈ lo, (S.σ n j) ^ 2 * ⟪S.e n j, u⟫ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ lo)]
    have : ∑ j ∈ Finset.univ.filter (fun j => j ∉ lo),
        (S.σ n j) ^ 2 * ⟪S.e n j, u⟫ ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter] at hj
      rw [hzero j hj.2]; ring
    rw [this, add_zero]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp
  rw [hsplit]
  -- Bound each `lo`-term, and embed RHS over univ ⊇ lo.
  have hsub : ∑ j ∈ lo, (S.σ n j) ^ 2 * ⟪S.e n j, u⟫ ^ 2
      ≤ ∑ j ∈ lo, s ^ 2 * ⟪S.e n j, u⟫ ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply sq_le_sq'
    · linarith [S.σ_nonneg n j, hσ j hj, hs]
    · exact hσ j hj
  refine hsub.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ lo)
  intro j _ _
  positivity

/-- **SVD lower bound via a fast projection.**  Fix a "fast / high" index set `hi` with every
singular value there `≥ t ≥ 0`.  Let `w = Σ_{j ∈ hi} ⟪e n j, u⟫ • e n j` be the orthogonal
projection of `u` onto the fast span.  Then `t · ‖w‖ ≤ ‖f n u‖`. -/
lemma singularValue_norm_proj_le_norm_apply (n : ℕ) (hi : Finset (Fin d)) (t : ℝ) (ht : 0 ≤ t)
    (hσ : ∀ j ∈ hi, t ≤ S.σ n j) (u : E) :
    (t * ‖∑ j ∈ hi, ⟪S.e n j, u⟫ • S.e n j‖) ^ 2 ≤ ‖S.apply n u‖ ^ 2 := by
  -- `‖w‖² = Σ_{j ∈ hi} ⟪e n j, u⟫²` (orthonormality).
  have hwSq : ‖∑ j ∈ hi, ⟪S.e n j, u⟫ • S.e n j‖ ^ 2
      = ∑ j ∈ hi, ⟪S.e n j, u⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi'
    rw [inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, (S.e n).orthonormal.1 i]
      ring
    · intro j hj hji
      rw [real_inner_smul_left, real_inner_smul_right,
        (S.e n).orthonormal.2 (by simpa using hji.symm)]
      ring
    · intro h; exact absurd hi' h
  -- Bound `t² ‖w‖²` against the `hi`-part of the Parseval sum, which is ≤ the full sum.
  rw [mul_pow, hwSq, S.normSq_apply]
  rw [Finset.mul_sum]
  calc ∑ j ∈ hi, t ^ 2 * ⟪S.e n j, u⟫ ^ 2
      ≤ ∑ j ∈ hi, (S.σ n j) ^ 2 * ⟪S.e n j, u⟫ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply sq_le_sq'
        · linarith [hσ j hj, ht]
        · exact hσ j hj
    _ ≤ ∑ j, (S.σ n j) ^ 2 * ⟪S.e n j, u⟫ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ hi)
        intro j _ _; positivity

/-! ## The one-step two-sided sandwich -/

/-- The orthogonal projection of `u` onto the span of the time-`n` right-singular vectors with
index in `hi` (the "fast" band at time `n`):  `Σ_{j ∈ hi} ⟪e n j, u⟫ • e n j`. -/
def fastProj (n : ℕ) (hi : Finset (Fin d)) (u : E) : E :=
  ∑ j ∈ hi, ⟪S.e n j, u⟫ • S.e n j

/-- `‖fastProj n hi u‖² = Σ_{j ∈ hi} ⟪e n j, u⟫²` (orthonormality of `e n`). -/
lemma normSq_fastProj (n : ℕ) (hi : Finset (Fin d)) (u : E) :
    ‖S.fastProj n hi u‖ ^ 2 = ∑ j ∈ hi, ⟪S.e n j, u⟫ ^ 2 := by
  rw [fastProj, ← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, (S.e n).orthonormal.1 i]
    ring
  · intro j hj hji
    rw [real_inner_smul_left, real_inner_smul_right,
      (S.e n).orthonormal.2 (by simpa using hji.symm)]
    ring
  · intro h; exact absurd hi' h

/-- Restated lower bound in terms of `fastProj`:  `t · ‖fastProj n hi u‖ ≤ ‖f n u‖`. -/
lemma singularValue_norm_fastProj_le_norm_apply (n : ℕ) (hi : Finset (Fin d)) (t : ℝ) (ht : 0 ≤ t)
    (hσ : ∀ j ∈ hi, t ≤ S.σ n j) (u : E) :
    (t * ‖S.fastProj n hi u‖) ^ 2 ≤ ‖S.apply n u‖ ^ 2 :=
  S.singularValue_norm_proj_le_norm_apply n hi t ht hσ u

/-- **Ruelle's one-step two-sided SVD sandwich.**

Fix consecutive times `n, n+1`.  Let `u` lie in the time-`n` *slow* span (indices `lo`, each
singular value `≤ s`), and let `hi` be a *fast* band at time `n+1` (each singular value `≥ t > 0`).
Suppose the one-step operator bound `‖f (n+1) u‖ ≤ b · ‖f n u‖` holds with `b ≥ 0`.  Then the
time-`(n+1)` fast projection of `u` satisfies

    t · ‖fastProj (n+1) hi u‖  ≤  b · s · ‖u‖ .

This is the leakage at the full pairwise band gap: combining the SVD lower bound at time `n+1`
(`fastProj` term) with the SVD upper bound on the slow span at time `n` (`s‖u‖`) through the
one-step step bound `b`. -/
theorem oneStep_sandwich (n : ℕ) (lo hi : Finset (Fin d)) (s t b : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hb : 0 ≤ b)
    (hσlo : ∀ j ∈ lo, S.σ n j ≤ s) (hσhi : ∀ j ∈ hi, t ≤ S.σ (n + 1) j)
    (u : E) (hu : u ∈ Submodule.span ℝ (Set.range (fun j : lo => S.e n (j : Fin d))))
    (hstep : ‖S.apply (n + 1) u‖ ≤ b * ‖S.apply n u‖) :
    t * ‖S.fastProj (n + 1) hi u‖ ≤ b * s * ‖u‖ := by
  -- The chain of squared inequalities:
  --   (t‖w‖)² ≤ ‖f(n+1)u‖² ≤ (b‖f n u‖)² ≤ (b·s·‖u‖)².
  have hlower : (t * ‖S.fastProj (n + 1) hi u‖) ^ 2 ≤ ‖S.apply (n + 1) u‖ ^ 2 :=
    S.singularValue_norm_fastProj_le_norm_apply (n + 1) hi t ht hσhi u
  have hstep2 : ‖S.apply (n + 1) u‖ ^ 2 ≤ (b * ‖S.apply n u‖) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [norm_nonneg (S.apply (n + 1) u), norm_nonneg (S.apply n u), hstep]
    · exact hstep
  have hupper : ‖S.apply n u‖ ^ 2 ≤ s ^ 2 * ‖u‖ ^ 2 :=
    S.normSq_apply_le_of_mem_span n lo s hs hσlo u hu
  have hchain : (t * ‖S.fastProj (n + 1) hi u‖) ^ 2 ≤ (b * s * ‖u‖) ^ 2 := by
    refine hlower.trans (hstep2.trans ?_)
    have : (b * ‖S.apply n u‖) ^ 2 = b ^ 2 * ‖S.apply n u‖ ^ 2 := by ring
    rw [this]
    calc b ^ 2 * ‖S.apply n u‖ ^ 2
        ≤ b ^ 2 * (s ^ 2 * ‖u‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left hupper (sq_nonneg b)
      _ = (b * s * ‖u‖) ^ 2 := by ring
  -- Take square roots: both sides nonneg.
  have hL : 0 ≤ t * ‖S.fastProj (n + 1) hi u‖ := by positivity
  have hR : 0 ≤ b * s * ‖u‖ := by positivity
  nlinarith [hchain, hL, hR]

/-! ## The band-grouped Parseval envelope -/

/-- **Band-restricted Parseval mass.**  The partial Parseval sum over a band `B` is exactly
`Σ_{j ∈ B} (σ n j)² ⟪e n j, v⟫²`, and is bounded by `Sr² · ‖fastProj n B v‖²` whenever every
singular value in `B` is `≤ Sr`.  (This is the per-band term that, with the leakage envelope on
`‖fastProj n B v‖`, yields the `λ⁽ᵖ⁾` growth.) -/
lemma band_partial_normSq_le (n : ℕ) (B : Finset (Fin d)) (Sr : ℝ) (hSr : 0 ≤ Sr)
    (hσ : ∀ j ∈ B, S.σ n j ≤ Sr) (v : E) :
    ∑ j ∈ B, (S.σ n j) ^ 2 * ⟪S.e n j, v⟫ ^ 2 ≤ Sr ^ 2 * ‖S.fastProj n B v‖ ^ 2 := by
  rw [S.normSq_fastProj, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply sq_le_sq'
  · linarith [S.σ_nonneg n j, hσ j hj, hSr]
  · exact hσ j hj

/-- **Band-grouped SVD envelope.**  Let `bands : Finset ι` index a partition of `Fin d` into
bands via `B : ι → Finset (Fin d)` (covering all indices: `Finset.univ ⊆ ⋃_{r ∈ bands} B r`), with a
per-band singular-value cap `Sr : ι → ℝ` (`σ n j ≤ Sr r` for `j ∈ B r`, `0 ≤ Sr r`).  Then

    ‖f n v‖²  ≤  Σ_{r ∈ bands} (Sr r)² · ‖fastProj n (B r) v‖² .

This sums the band-restricted Parseval masses (`band_partial_normSq_le`).  With the leakage
envelopes on each `‖fastProj n (B r) v‖`, the right side is `≤ (#bands)·K²·exp(2n(λ⁽ᵖ⁾+δ))·‖v‖²`,
giving
`limsup (1/n) log‖f n v‖ ≤ λ⁽ᵖ⁾` (Ruelle's part b). -/
theorem normSq_apply_le_band_sum {ι : Type*} (n : ℕ) (bands : Finset ι)
    (B : ι → Finset (Fin d)) (Sr : ι → ℝ) (hSr : ∀ r ∈ bands, 0 ≤ Sr r)
    (hσ : ∀ r ∈ bands, ∀ j ∈ B r, S.σ n j ≤ Sr r)
    (hdisj : Set.PairwiseDisjoint (↑bands) B)
    (hcover : (Finset.univ : Finset (Fin d)) ⊆ bands.biUnion B) (v : E) :
    ‖S.apply n v‖ ^ 2 ≤ ∑ r ∈ bands, (Sr r) ^ 2 * ‖S.fastProj n (B r) v‖ ^ 2 := by
  classical
  rw [S.normSq_apply]
  set f : Fin d → ℝ := fun j => (S.σ n j) ^ 2 * ⟪S.e n j, v⟫ ^ 2 with hf
  have hfnn : ∀ j, 0 ≤ f j := fun j => by rw [hf]; positivity
  -- Step 1: full sum ≤ sum over the cover `bands.biUnion B` (extra nonneg terms only help).
  have hstep1 : ∑ j, f j ≤ ∑ j ∈ bands.biUnion B, f j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hcover
    intro j _ _; exact hfnn j
  -- Step 2: disjoint bands ⟹ sum over biUnion = Σ_r Σ_{j∈B r}.
  have hstep2 : ∑ j ∈ bands.biUnion B, f j = ∑ r ∈ bands, ∑ j ∈ B r, f j :=
    Finset.sum_biUnion hdisj
  -- Step 3: each band bounded by its cap.
  have hstep3 : ∑ r ∈ bands, ∑ j ∈ B r, f j
      ≤ ∑ r ∈ bands, (Sr r) ^ 2 * ‖S.fastProj n (B r) v‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro r hr
    exact S.band_partial_normSq_le n (B r) (Sr r) (hSr r hr) (hσ r hr) v
  rw [hstep2] at hstep1
  exact hstep1.trans hstep3

/-! ## The `k`-uniform forward chain (geometric recursion)

Ruelle's Lemma 1.4 controls the leakage of *slow* mass into the *fast* bands accumulated over the
window `n, n+1, …, n+k`.  Iterating the one-step sandwich along the window produces, for the
mass arriving in a fixed fast band, a *discrete linear recursion*

    a (i+1)  ≤  q · a i  +  R · ρ^i ,

whose solution is the geometric envelope below.  Here `a i` is the band-leakage budget at time
`n+i`, `q ∈ [0,1)` the one-step survival/decay factor of the gap, `R·ρ^i` the fresh mass injected at
step `i` (itself decaying at the source rate `ρ`).  This is the core analytic engine of Lemma 1.4:
the band-distance induction reduces to iterating exactly this recursion, and the resulting
geometric sum is Ruelle's displayed computation.  It is stated and proved abstractly so it can be
driven by the sandwich factors at each step. -/

/-- **Discrete geometric recursion (Grönwall-type).**  If `a (i+1) ≤ q · a i + c i` for all `i`,
with `0 ≤ q`, then for every `k`,

    a k  ≤  q^k · a 0  +  Σ_{i<k} q^{k-1-i} · c i .

This is the exact solution of Ruelle's per-step leakage recursion; the second term is the
accumulated freshly-injected mass, each contribution surviving `k-1-i` further steps at factor
`q`. -/
theorem geometric_recursion (a c : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hrec : ∀ i, a (i + 1) ≤ q * a i + c i) (k : ℕ) :
    a k ≤ q ^ k * a 0 + ∑ i ∈ Finset.range k, q ^ (k - 1 - i) * c i := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- a (k+1) ≤ q·a k + c k ≤ q·(envelope k) + c k = envelope (k+1).
    refine (hrec k).trans ?_
    have hstep : q * a k + c k
        ≤ q * (q ^ k * a 0 + ∑ i ∈ Finset.range k, q ^ (k - 1 - i) * c i) + c k := by
      have := mul_le_mul_of_nonneg_left ih hq
      linarith
    refine hstep.trans (le_of_eq ?_)
    rw [Finset.sum_range_succ]
    -- Reindex the surviving terms: each `q^{k-1-i}` gains one factor of `q`, becoming
    -- `q^{(k+1)-1-i}`.
    have hpow : ∀ i ∈ Finset.range k,
        q * (q ^ (k - 1 - i) * c i) = q ^ (k + 1 - 1 - i) * c i := by
      intro i hi
      rw [Finset.mem_range] at hi
      have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl hpow]
    have hck : q ^ (k + 1 - 1 - k) * c k = c k := by
      have : k + 1 - 1 - k = 0 := by omega
      rw [this, pow_zero, one_mul]
    rw [hck]
    ring

/-- **Geometric envelope with a uniform source rate.**  Specialising `geometric_recursion` to the
source `c i = R · ρ^i` with `0 ≤ ρ`, `0 ≤ R`, the accumulated sum collapses (each surviving term has
total exponent `(k-1-i)+i = k-1`) to the sub-exponential envelope

    a k  ≤  q^k · a 0  +  R · k · (max q ρ)^(k-1) .

The `k·M^(k-1)` envelope suffices for the Lyapunov application: it is sub-exponential in `k` and is
killed by the strictly-positive band gap in the exponent.  This is the form consumed by the
band-distance induction. -/
theorem geometric_recursion_uniform (a : ℕ → ℝ) (q ρ R : ℝ)
    (hq : 0 ≤ q) (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hrec : ∀ i, a (i + 1) ≤ q * a i + R * ρ ^ i) (k : ℕ) :
    a k ≤ q ^ k * a 0 + R * (k : ℝ) * (max q ρ) ^ (k - 1) := by
  have hmain := geometric_recursion a (fun i => R * ρ ^ i) q hq hrec k
  refine hmain.trans ?_
  gcongr
  -- bound each term `q^{k-1-i}·R·ρ^i ≤ R·M^{k-1}` (M = max q ρ), then sum over `range k`.
  have hbound : ∀ i ∈ Finset.range k,
      q ^ (k - 1 - i) * (R * ρ ^ i) ≤ R * (max q ρ) ^ (k - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : q ^ (k - 1 - i) ≤ (max q ρ) ^ (k - 1 - i) :=
      pow_le_pow_left₀ hq (le_max_left _ _) _
    have h2 : ρ ^ i ≤ (max q ρ) ^ i :=
      pow_le_pow_left₀ hρ (le_max_right _ _) _
    have h3 : q ^ (k - 1 - i) * ρ ^ i ≤ (max q ρ) ^ (k - 1 - i) * (max q ρ) ^ i := by
      apply mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : (max q ρ) ^ (k - 1 - i) * (max q ρ) ^ i = (max q ρ) ^ (k - 1) := by
      rw [← pow_add]; congr 1; omega
    calc q ^ (k - 1 - i) * (R * ρ ^ i)
        = R * (q ^ (k - 1 - i) * ρ ^ i) := by ring
      _ ≤ R * ((max q ρ) ^ (k - 1 - i) * (max q ρ) ^ i) := by
          apply mul_le_mul_of_nonneg_left h3 hR
      _ = R * (max q ρ) ^ (k - 1) := by rw [h4]
  calc ∑ i ∈ Finset.range k, q ^ (k - 1 - i) * (R * ρ ^ i)
      ≤ ∑ _i ∈ Finset.range k, R * (max q ρ) ^ (k - 1) :=
        Finset.sum_le_sum hbound
    _ = (k : ℝ) * (R * (max q ρ) ^ (k - 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = R * (k : ℝ) * (max q ρ) ^ (k - 1) := by ring

/-- **`k`-uniform forward leakage envelope (exponential form).**

This is Ruelle's Lemma 1.4 leakage bound in its application-facing form.  Model the band-leakage
budget `a i` over the window `n, n+1, …` by the recursion `a (i+1) ≤ q·a i + R·ρ^i`, where:

* `a 0` is the initial slow mass (`= ‖u‖`, taken `≤ 1` for a unit vector);
* `q = exp(-(γ))` is the one-step gap survival factor, `γ ≥ 0` the per-step band gap;
* `R·ρ^i` is the freshly injected leakage at step `i`, with source rate `ρ = exp(-γ') ≤ exp(-γ)`.

Then, writing `M = max q ρ = exp(-(min γ γ'))`, the time-`(n+k)` leakage obeys

    a k  ≤  exp(-k·γ)·a 0  +  R·k·exp(-(k-1)·min γ γ') ,

an envelope decaying at the full pairwise gap `min γ γ'` (up to the harmless polynomial `k` and
boundary factor).  This packages `geometric_recursion_uniform` with explicit `exp` rates so it
composes directly with the SVD sandwich factors. -/
theorem chain_leakage_exp (a : ℕ → ℝ) (γ γ' R : ℝ) (hR : 0 ≤ R)
    (hrec : ∀ i, a (i + 1) ≤ Real.exp (-γ) * a i + R * Real.exp (-γ') ^ i) (k : ℕ) :
    a k ≤ Real.exp (-(k : ℝ) * γ) * a 0
        + R * (k : ℝ) * Real.exp (-((k : ℝ) - 1) * min γ γ') := by
  have hq : (0:ℝ) ≤ Real.exp (-γ) := (Real.exp_pos _).le
  have hρ : (0:ℝ) ≤ Real.exp (-γ') := (Real.exp_pos _).le
  have hmain := geometric_recursion_uniform a (Real.exp (-γ)) (Real.exp (-γ')) R hq hρ hR hrec k
  refine hmain.trans (le_of_eq ?_)
  congr 1
  · -- q^k = exp(-k γ)
    rw [← Real.exp_nat_mul]; congr 1; ring_nf
  · -- M^{k-1} = exp(-(k-1)·min γ γ'), where M = max(exp(-γ), exp(-γ')) = exp(-min γ γ')
    have hmax : max (Real.exp (-γ)) (Real.exp (-γ')) = Real.exp (-min γ γ') := by
      rw [← Real.exp_monotone.map_max]; congr 1; rw [max_neg_neg]
    rw [hmax]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [← Real.exp_nat_mul]; congr 1
      rw [Nat.cast_sub hk]; push_cast; ring_nf

/-! ## The reverse side (orthogonal block-norm symmetry)

Ruelle's reverse-side estimate bounds the entries of the orthogonal change-of-basis matrix
`S_{ij} = ⟪e_n j, e_m i⟫` on the *other* side of the band diagonal (slow `i` at time `m`, fast `j`
at time `n`) at the full pairwise rate.  The deep route is the cofactor/permutation expansion.
Here we
record the elementary structural fact that already pins the reverse-side block to the same Frobenius
mass as the forward-side block, which is the quantitative heart of the rate transfer for the
dominant gap: for *any* orthonormal change of basis, the off-diagonal block over `(A, Aᶜ)` carries
the same squared mass as the transposed block over `(Aᶜ, A)`.

This is purely orthogonality (`SᵀS = I = SSᵀ`, realised as Parseval in each basis): no permutation
combinatorics.  It gives the reverse-side leakage `Σ_{j∈Aᶜ}⟪e_m i, e_n j⟫²` (summed over slow `i∈A`)
exactly in terms of the forward-side leakage, hence at the forward rate. -/

/-- Parseval in an orthonormal basis `b`: `‖u‖² = Σ_i ⟪b i, u⟫²`. -/
lemma orthonormalBasis_normSq_eq (b : OrthonormalBasis (Fin d) ℝ E) (u : E) :
    ‖u‖ ^ 2 = ∑ i, ⟪b i, u⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner u u]
  apply Finset.sum_congr rfl
  intro j _; rw [real_inner_comm (b j) u]; ring

/-- **Orthogonal off-diagonal block-norm symmetry.**  For two orthonormal bases `b, b'` of a
finite-dimensional real inner product space and any index set `A`, the cross-overlap mass of
"`A`-rows against `Aᶜ`-columns" equals that of "`Aᶜ`-rows against `A`-columns":

    Σ_{i∈A} Σ_{j∈Aᶜ} ⟪b' i, b j⟫²  =  Σ_{i∈Aᶜ} Σ_{j∈A} ⟪b' i, b j⟫² .

Equivalently the slow→fast leakage equals the fast→slow leakage.  Proof: each side equals
`|A| − Σ_{i∈A}Σ_{j∈A} ⟪b' i, b j⟫²`, using that every row sums to `1` (Parseval of `b' i` in basis
`b`) and every column sums to `1` (Parseval of `b j` in basis `b'`). -/
theorem orthogonal_block_mass_symm (b b' : OrthonormalBasis (Fin d) ℝ E) (A : Finset (Fin d)) :
    ∑ i ∈ A, ∑ j ∈ Aᶜ, ⟪b' i, b j⟫ ^ 2 = ∑ i ∈ Aᶜ, ∑ j ∈ A, ⟪b' i, b j⟫ ^ 2 := by
  classical
  -- Row sums: `Σ_j ⟪b' i, b j⟫² = ‖b' i‖² = 1`.
  have hrow : ∀ i, ∑ j, ⟪b' i, b j⟫ ^ 2 = 1 := by
    intro i
    have hcomm : ∀ j, ⟪b' i, b j⟫ ^ 2 = ⟪b j, b' i⟫ ^ 2 := by
      intro j; rw [real_inner_comm (b' i) (b j)]
    simp_rw [hcomm]
    rw [← orthonormalBasis_normSq_eq b (b' i), b'.orthonormal.1 i]; norm_num
  -- Column sums: `Σ_i ⟪b' i, b j⟫² = ‖b j‖² = 1`.
  have hcol : ∀ j, ∑ i, ⟪b' i, b j⟫ ^ 2 = 1 := by
    intro j
    rw [← orthonormalBasis_normSq_eq b' (b j), b.orthonormal.1 j]; norm_num
  -- Split each row over `A ∪ Aᶜ`.  Let `T i = Σ_{j∈A} ⟪b' i, b j⟫²`.
  set M : Fin d → Fin d → ℝ := fun i j => ⟪b' i, b j⟫ ^ 2 with hM
  have hrowsplit : ∀ i, ∑ j ∈ A, M i j + ∑ j ∈ Aᶜ, M i j = 1 := by
    intro i
    rw [Finset.sum_add_sum_compl A (M i)]; exact hrow i
  have hcolsplit : ∀ j, ∑ i ∈ A, M i j + ∑ i ∈ Aᶜ, M i j = 1 := by
    intro j
    rw [Finset.sum_add_sum_compl A (fun i => M i j)]; exact hcol j
  -- Σ_{i∈A} Σ_{j∈Aᶜ} M = Σ_{i∈A}(1 - Σ_{j∈A} M) = |A| - Σ_{i∈A,j∈A} M.
  have hL : ∑ i ∈ A, ∑ j ∈ Aᶜ, M i j
      = (A.card : ℝ) - ∑ i ∈ A, ∑ j ∈ A, M i j := by
    have hcongr : ∑ i ∈ A, ∑ j ∈ Aᶜ, M i j
        = ∑ i ∈ A, (1 - ∑ j ∈ A, M i j) :=
      Finset.sum_congr rfl (fun i _ => by linarith [hrowsplit i])
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Σ_{i∈Aᶜ} Σ_{j∈A} M = Σ_{j∈A}(1 - Σ_{i∈A} M) = |A| - Σ_{i∈A,j∈A} M  (after swapping order).
  have hR : ∑ i ∈ Aᶜ, ∑ j ∈ A, M i j
      = (A.card : ℝ) - ∑ i ∈ A, ∑ j ∈ A, M i j := by
    rw [Finset.sum_comm]
    have hcongr : ∑ j ∈ A, ∑ i ∈ Aᶜ, M i j
        = ∑ j ∈ A, (1 - ∑ i ∈ A, M i j) :=
      Finset.sum_congr rfl (fun j _ => by linarith [hcolsplit j])
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.sum_comm]
  rw [hL, hR]

end SVDData

end Oseledets.RuelleCofactor
