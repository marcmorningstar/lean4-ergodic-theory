/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.ExteriorNorm.Basic
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Positive-part volume distortion: the singular-value product the covering count consumes

This module proves the **algebraic identity** at the heart of the positive-part volume distortion
appearing in the Margulis–Ruelle covering-count estimate (Liao–Qiu,
*Margulis–Ruelle inequality for general manifolds*, §3, Lemmas 3.2–3.3): the local volume
expansion factor counting only the **expanding** directions of a linear map is

$$\prod_{i} \max(1, \sigma_i) \;=\; \sup_{0 \le k \le d} \prod_{i < k} \sigma_i
  \;=\; \sup_{0 \le k \le d} \lVert C_k(M) \rVert,$$

where `σ₀ ≥ σ₁ ≥ ⋯` are the singular values and `C_k(M)` is the `k`-th compound matrix.

Geometrically, the cthickening of a thin box `M '' B` is covered by a number of unit cells
comparable to `∏ᵢ max(1, σᵢ M)` (Lemma 3.2 bounds the cover of a box with sides `aᵢ` by
`c · ∏ᵢ max(aᵢ, 1)`; for a thickened image the relevant sides are `σᵢ`), and Lemma 3.3 packages
this as the operator norm of the **exterior power** `‖(D_x g)^∧‖ = max_κ ‖(D_x g)^{∧κ}‖`, i.e. the
maximal compound operator norm. This is exactly the form `(b)` requested: it bridges
`|det M| = ∏ σᵢ` (the full product, the `k = d` term) with the `∏ max(1, σᵢ)` that the count
needs, by selecting the *optimal truncation* `k` of the singular-value product.

## Main results

* `Oseledets.prod_max_one_eq_sup_prod_range` — the **abstract algebraic identity** for any
  antitone, nonnegative sequence: `∏_{i<d} max(1, σᵢ) = ⨆_{k≤d} ∏_{i<k} σᵢ` (`Finset.sup'`).
* `Oseledets.prod_max_one_singularValues_eq_sup_prod_range` — its specialization to the singular
  values of a linear map between finite-dimensional inner product spaces.
* `Oseledets.prod_max_one_singularValues_eq_sup_opNorm_compound` — the **compound bridge**: for a
  square matrix `M`, `∏_{i<d} max(1, σᵢ(M)) = ⨆_{k≤d} ‖C_k(M)‖`, the maximal compound operator
  norm that the covering count consumes.

## Implementation notes

The abstract identity is proved by an *antichain/prefix* argument. Antitonicity makes the index set
`{i < d : 1 ≤ σ i}` an initial segment `range k*`, where `k* := #{i < d : 1 ≤ σ i}`. The partial
product `∏_{i<k*} σ i` then equals `∏_{i<d} max(1, σ i)` (the truncated factors `σ i < 1` contribute
`max(1, σ i) = 1`), and it dominates every other partial product `∏_{i<k} σ i` by monotonicity of
products over `[0,1]`-padded factors. The compound bridge is then immediate from the repository
identity `Oseledets.ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound`.
-/

open Finset
open scoped Matrix.Norms.L2Operator

namespace Oseledets

/-! ## The abstract algebraic identity for an antitone nonnegative sequence -/

section Abstract

variable {σ : ℕ → ℝ} (hanti : Antitone σ) (hpos : ∀ i, 0 ≤ σ i)

/-- The prefix `{i < d : 1 ≤ σ i}` of an antitone sequence is an initial segment `range k`. Its
cardinality `k = #{i < d : 1 ≤ σ i}` is the number of singular values that are `≥ 1`, i.e. the
expanding directions. -/
theorem range_filter_one_le_eq_range (hanti : Antitone σ) (d : ℕ) :
    (range d).filter (fun i => 1 ≤ σ i)
      = range ((range d).filter (fun i => 1 ≤ σ i)).card := by
  classical
  set k := ((range d).filter (fun i => 1 ≤ σ i)).card with hk
  apply Finset.eq_of_subset_of_card_le
  · -- every member `i` of the filter is `< k`: there is no gap, by antitonicity.
    intro i hi
    rw [mem_filter, mem_range] at hi
    rw [mem_range]
    by_contra hik
    push Not at hik
    -- `range (i+1) ⊆ filter`, since `j ≤ i ⇒ σ j ≥ σ i ≥ 1` and `j < i+1 ≤ d`.
    have hsub : range (i + 1) ⊆ (range d).filter (fun j => 1 ≤ σ j) := by
      intro j hj
      rw [mem_range, Nat.lt_succ_iff] at hj
      rw [mem_filter, mem_range]
      exact ⟨lt_of_le_of_lt hj hi.1, le_trans hi.2 (hanti hj)⟩
    have := Finset.card_le_card hsub
    rw [card_range] at this
    omega
  · rw [card_range]
end Abstract

/-- **The positive-part singular-value product as a supremum of partial products (abstract).**
For an antitone nonnegative sequence `σ` and a horizon `d`, the product of the positive parts
`∏_{i<d} max(1, σ i)` equals the supremum over truncations `0 ≤ k ≤ d` of the partial products
`∏_{i<k} σ i`. The optimal truncation `k* = #{i < d : 1 ≤ σ i}` keeps exactly the expanding
factors. -/
theorem prod_max_one_eq_sup_prod_range {σ : ℕ → ℝ} (hanti : Antitone σ) (hpos : ∀ i, 0 ≤ σ i)
    (d : ℕ) :
    ∏ i ∈ range d, max 1 (σ i)
      = (range (d + 1)).sup' (nonempty_range_iff.2 (Nat.succ_ne_zero d))
          (fun k => ∏ i ∈ range k, σ i) := by
  classical
  set H := nonempty_range_iff.2 (Nat.succ_ne_zero d)
  set k := ((range d).filter (fun i => 1 ≤ σ i)).card with hk
  -- `k ≤ d`, so `k ∈ range (d+1)`.
  have hkd : k ≤ d := by
    rw [hk]
    calc ((range d).filter (fun i => 1 ≤ σ i)).card ≤ (range d).card :=
          card_filter_le _ _
      _ = d := card_range d
  have hkmem : k ∈ range (d + 1) := by rw [mem_range]; omega
  -- The optimal partial product equals the positive-part product.
  have hpartial : ∏ i ∈ range k, σ i = ∏ i ∈ range d, max 1 (σ i) := by
    -- Rewrite the positive-part product by splitting `range d` along the threshold filter.
    have hfilter : (range d).filter (fun i => 1 ≤ σ i) = range k :=
      range_filter_one_le_eq_range hanti d
    rw [← Finset.prod_filter_mul_prod_filter_not (range d) (fun i => 1 ≤ σ i)
      (fun i => max 1 (σ i))]
    rw [hfilter]
    -- On `range k` the factor `max 1 (σ i) = σ i`; off it `max 1 (σ i) = 1`.
    have hon : ∏ i ∈ range k, max 1 (σ i) = ∏ i ∈ range k, σ i := by
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have : 1 ≤ σ i := by
        have := hfilter ▸ hi
        rw [mem_filter] at this; exact this.2
      exact max_eq_right this
    have hoff : ∏ i ∈ (range d).filter (fun i => ¬ 1 ≤ σ i), max 1 (σ i) = 1 := by
      refine Finset.prod_eq_one (fun i hi => ?_)
      rw [mem_filter] at hi
      push Not at hi
      exact max_eq_left (le_of_lt hi.2)
    rw [hon, hoff, mul_one]
  -- Equality by antisymmetry on the supremum.
  apply le_antisymm
  · -- `∏ max ≤ sup'`: realized at `k`.
    rw [← hpartial]
    exact Finset.le_sup'_of_le _ hkmem (le_refl _)
  · -- `sup' ≤ ∏ max`: every partial product is `≤` the positive-part product.
    rw [Finset.sup'_le_iff]
    intro j hj
    rw [mem_range, Nat.lt_succ_iff] at hj
    calc ∏ i ∈ range j, σ i
        ≤ ∏ i ∈ range j, max 1 (σ i) :=
          Finset.prod_le_prod (fun i _ => hpos i) (fun i _ => le_max_right _ _)
      _ ≤ ∏ i ∈ range d, max 1 (σ i) :=
          Finset.prod_le_prod_of_subset_of_one_le
            (Finset.range_subset_range.2 hj)
            (fun i _ => le_trans zero_le_one (le_max_left _ _))
            (fun i _ _ => le_max_left _ _)

/-! ## Specialization to singular values -/

section SingularValues

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The positive-part singular-value product as a supremum of partial products.** For a linear map
`f` between finite-dimensional real inner product spaces, the positive-part product
`∏_{i<d} max(1, σᵢ(f))` equals the supremum over truncations `0 ≤ k ≤ d` of the top-`k` singular
value products `∏_{i<k} σᵢ(f)`. This is the local volume-expansion factor counting only the
expanding directions, written in the truncated-product form the covering count uses. -/
theorem prod_max_one_singularValues_eq_sup_prod_range (f : E →ₗ[ℝ] F) (d : ℕ) :
    ∏ i ∈ range d, max 1 (f.singularValues i)
      = (range (d + 1)).sup' (nonempty_range_iff.2 (Nat.succ_ne_zero d))
          (fun k => ∏ i ∈ range k, f.singularValues i) :=
  prod_max_one_eq_sup_prod_range f.singularValues_antitone f.singularValues_nonneg d

end SingularValues

/-! ## The compound bridge -/

section Compound

variable {d : ℕ}

/-- **The positive-part volume distortion as the maximal compound operator norm.** For a square
matrix `M`, the positive-part singular-value product `∏_{i<n} max(1, σᵢ(M))` equals the supremum
over `0 ≤ k ≤ n` of the operator norms of the compound matrices `‖C_k(M)‖`. This is the form the
Margulis–Ruelle covering count consumes (Liao–Qiu §3, Lemma 3.3): the cover of the thickened image
is controlled by `‖(toEuclideanLin M)^∧‖ = max_κ ‖C_κ(M)‖`, the maximal exterior-power operator
norm. It bridges `|det M| = ∏ σᵢ` (the `k = n` term) with the truncated `∏ max(1, σᵢ)` the count
needs. -/
theorem prod_max_one_singularValues_eq_sup_opNorm_compound (M : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    ∏ i ∈ range n, max 1 ((Matrix.toEuclideanLin M).singularValues i)
      = (range (n + 1)).sup' (nonempty_range_iff.2 (Nat.succ_ne_zero n))
          (fun k => ‖Oseledets.ExteriorNorm.compoundMatrix k M‖) := by
  rw [prod_max_one_singularValues_eq_sup_prod_range (Matrix.toEuclideanLin M) n]
  refine Finset.sup'_congr _ rfl (fun k _ => ?_)
  exact Oseledets.ExteriorNorm.prod_singularValues_eq_l2_opNorm_compound k M

end Compound

end Oseledets
