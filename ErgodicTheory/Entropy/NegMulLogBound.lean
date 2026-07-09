/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The uniform-weight Jensen bound for `negMulLog`

The concave function `negMulLog x = -x * log x` satisfies the maximum-entropy inequality: for a
finite probability vector `p` supported on a nonempty finite set `s`, the Shannon-type sum
`∑ i ∈ s, negMulLog (p i)` is bounded above by `log |s|`, with equality at the uniform
distribution.  This is the finite-dimensional maximum-entropy principle, extracted here as a
standalone `Finset` lemma so that both the classical entropy layer and the operator-entropy
layer (`ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_rank`) can share the single Jensen
argument rather than each inlining it.

The proof applies the concave Jensen inequality (`ConcaveOn.le_map_sum`) to `negMulLog` with the
uniform weights `1 / |s|` and evaluates `negMulLog (1 / |s|) = (1 / |s|) · log |s|`.

## Main results

* `ErgodicTheory.sum_negMulLog_le_log_card`
-/

open Real

namespace ErgodicTheory

/-- **Maximum-entropy bound (uniform-weight Jensen).** For a probability vector `p` supported on a
nonempty finite set `s` (`0 ≤ p i` and `∑ i ∈ s, p i = 1`), the entropy sum
`∑ i ∈ s, negMulLog (p i)` is at most `log |s|`.  Equality holds at the uniform distribution
`p ≡ 1 / |s|`. -/
theorem sum_negMulLog_le_log_card {ι : Type*} {s : Finset ι} {p : ι → ℝ}
    (hs : s.Nonempty) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤ Real.log s.card := by
  have hKpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  -- concave Jensen inequality with uniform weights `1 / |s|`
  have hjensen := concaveOn_negMulLog.le_map_sum (t := s)
    (w := fun _ => (s.card : ℝ)⁻¹) (p := p)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; exact mul_inv_cancel₀ hKpos.ne')
    (fun i hi => Set.mem_Ici.mpr (hp i hi))
  simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one] at hjensen
  -- evaluate `negMulLog (1 / |s|)`
  have hval : Real.negMulLog ((s.card : ℝ)⁻¹) = (s.card : ℝ)⁻¹ * Real.log (s.card : ℝ) := by
    unfold Real.negMulLog
    rw [Real.log_inv]; ring
  rw [hval] at hjensen
  have hcpos : (0 : ℝ) < (s.card : ℝ)⁻¹ := inv_pos.mpr hKpos
  exact le_of_mul_le_mul_left hjensen hcpos

end ErgodicTheory
