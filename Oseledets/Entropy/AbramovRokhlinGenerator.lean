/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Entropy.AbramovRokhlin
import Oseledets.Entropy.CondKSMovingLimit
import Oseledets.Entropy.JoinSigmaAlgebra
import Oseledets.Entropy.FactorGeneratorSaturate

/-!
# The Abramov–Rokhlin addition formula under a base generator (issue #13)

This is the **headline** of the issue-#13 conditional/relative entropy layer: the Abramov–Rokhlin
addition formula

`h(T) = h(S) + h(T | comap π 𝓑_Y)`

for a factor map `π : (α, T, μ) → (β, S, ν)`, with the genuinely analytic partition-level input
*discharged* rather than supplied. The previous form `Oseledets.Entropy.abramov_rokhlin` took the
partition-level identity (B6a) as a hypothesis `hBA`; the form here replaces it with the natural
structural hypothesis `IsGenerating ν S R` (the partition `R` generates the base system), which is
exactly the saturation needed for the moving-index Cesàro/martingale limit to converge.

The bridge is `Oseledets.Entropy.abramovRokhlin_partition` (the unconditional partition-level
identity, proved sorry-free in `CondKSMovingLimit` via the blocking/Cesàro–Toeplitz argument), whose
saturation hypothesis `⨆ n, σ(B_n) = 𝒜` is produced here from `IsGenerating ν S R` by composing
`iSup_generatedSigmaAlgebra_ksJoin_eq` (the join σ-algebra ladder `⨆ n σ(⋁_{k<n}T⁻ᵏ Q) =
⨆ k comap(T^[k]) σ(Q)`) with `factor_iSup_comap_eq` (`⨆ k comap(T^[k]) σ(π⁻¹R) = comap π 𝓑_Y`, the
forward saturation of a base generator pulled back through the factor map).

## Main results

* `Oseledets.Entropy.abramov_rokhlin_of_generator`: the addition formula
  `h(T) = h(S) + h(T | comap π 𝓑_Y)`, under the factor map, the generator/relative-generator
  reductions, and `IsGenerating ν S R` (in place of the supplied partition-level identity). This is
  the analytic crux W3 fully discharged.

## References

* L. M. Abramov, V. A. Rokhlin, *The entropy of a skew product of measure-preserving
  transformations*, Vestnik Leningrad Univ. **17** (1962).
* M. Einsiedler, E. Lindenstrauss, T. Ward, *Entropy in Ergodic Theory and Topological Dynamics*,
  Ch. 2 (the conditional Kolmogorov–Sinai / future formula and the Abramov–Rokhlin corollary).
* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), §§4.3–4.5.
-/

open MeasureTheory Function Filter Topology

namespace Oseledets.Entropy

variable {α β : Type*} {n m : ℕ}
variable [mα : MeasurableSpace α] [mβ : MeasurableSpace β] [StandardBorelSpace α]

/-- **The Abramov–Rokhlin addition formula under a base generator** for a factor map
`π : (α, T, μ) → (β, S, ν)`:
`h(T) = h(S) + h(T | comap π 𝓑_Y)`.

This is the sharpest form: instead of supplying the partition-level identity (B6a) as the
hypothesis `hBA` of `abramov_rokhlin`, it consumes the natural structural hypothesis
`hgenR : IsGenerating ν S R` (the base partition `R` generates `(β, S, ν)`). The saturation
`⨆ n, σ(B_n) = comap π 𝓑_Y` it implies — produced here by composing
`iSup_generatedSigmaAlgebra_ksJoin_eq` with `factor_iSup_comap_eq` — is exactly what drives the
moving-index Cesàro/martingale convergence
(`abramovRokhlin_partition`), so the partition-level identity is **proved**, not assumed. Every
input is now either a generator reduction (`hredT`, `hredS`, `hredRel`), the structural refinement
(`g`, `hrefine`), or the generator hypothesis `hgenR`; the analytic residual W3 is discharged. -/
theorem abramov_rokhlin_of_generator
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : α → α} {S : β → β} {π : α → β} [Nonempty (Fin n)]
    (hfac : IsFactorMap π T S μ ν)
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (P : MeasurePartition μ (Fin n)) (R : MeasurePartition ν (Fin m))
    (hm : MeasurableSpace.comap π mβ ≤ mα)
    (hinv : MeasurableSpace.comap T (MeasurableSpace.comap π mβ) ≤ MeasurableSpace.comap π mβ)
    (hredT : ksEntropy hT = ((ksEntropyPartition hT P : ℝ) : EReal))
    (hredS : ksEntropy hS = ((ksEntropyPartition hS R : ℝ) : EReal))
    (hredRel : condKsEntropy hm hT hinv
        = ((condKsEntropyPartition hm hT hinv P : ℝ) : EReal))
    (hgenR : IsGenerating ν S R)
    (g : ∀ k, (Fin k → Fin n) → (Fin k → Fin m))
    (hrefine : ∀ k f, (ksJoin hT P k).cells f ≤ᵐ[μ]
        (ksJoin hT (R.pulledBack hfac.1) k).cells (g k f)) :
    ksEntropy hT = ksEntropy hS + condKsEntropy hm hT hinv := by
  -- Saturation: the forward `T`-iterates of the pulled-back base generator recover the factor
  -- σ-algebra `comap π 𝓑_Y`. Compose the join-σ-algebra ladder with the generator saturation.
  have hsat : (⨆ k, generatedSigmaAlgebra μ (ksJoin hT (R.pulledBack hfac.1) k))
      = MeasurableSpace.comap π mβ := by
    rw [iSup_generatedSigmaAlgebra_ksJoin_eq]
    exact factor_iSup_comap_eq hfac.1 hfac.2.2 R hgenR
  -- The partition-level identity is now proved (not supplied) via the moving-index limit.
  exact abramov_rokhlin hfac hT hS P R hm hinv hredT hredS hredRel
    (abramovRokhlin_partition hm hT hinv (R.pulledBack hfac.1) P g hrefine hsat)

end Oseledets.Entropy
