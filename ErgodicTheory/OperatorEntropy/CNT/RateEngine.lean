import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A generic cumulative-bounded ⟹ per-step-rate-zero engine

This tiny, domain-neutral module records the pigeonhole face of the finiteness doctrine: if a
nonnegative sequence `a : ℕ → ℝ` is bounded above by a fixed constant `C` (a *reservoir*), then the
per-step rate `a n / n` tends to `0`.  This is the quantitative core behind the vanishing of a
dynamical-entropy rate in a finite-dimensional (finite-reservoir) system: the cumulative entropy
`H(N₁, …, Nₙ)` never exceeds the reservoir, so its rate is squeezed to `0`.

The intended quantum instantiation is in `ErgodicTheory.OperatorEntropy.CNT.FiniteDimZero`, where
`a n = S(corrMatrix Φ ρ X n)` and `C = log(d²)`; the engine is kept generic (namespace
`ErgodicTheory`, not `CNT`) so future classical instantiations can reuse it.

The CNT dynamical-entropy context is that of A. Connes, H. Narnhofer, W. Thirring, *Dynamical
entropy of C\*-algebras and von Neumann algebras*, Comm. Math. Phys. **112** (1987) 691–719.
-/

open Filter

namespace ErgodicTheory

/-- **Cumulative-bounded ⟹ per-step rate → 0.**  If `a` is nonnegative and uniformly bounded above
by `C`, then `a n / n → 0`.  Squeeze between `0 ≤ a n / n` and `a n / n ≤ C / n → 0`. -/
theorem rate_to_zero_of_cumulative_bounded {a : ℕ → ℝ} {C : ℝ}
    (hnn : ∀ n, 0 ≤ a n) (hb : ∀ n, a n ≤ C) :
    Filter.Tendsto (fun n => a n / (n : ℝ)) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun n => div_nonneg (hnn n) n.cast_nonneg) (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat C)
  gcongr
  exact hb n

end ErgodicTheory
