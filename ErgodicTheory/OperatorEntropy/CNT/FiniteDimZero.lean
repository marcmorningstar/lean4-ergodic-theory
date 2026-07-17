/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.CNT.Construction
import ErgodicTheory.OperatorEntropy.CNT.GramFactorization
import ErgodicTheory.Entropy.RateEngine
import ErgodicTheory.OperatorEntropy.EntropyRank
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing of the CNT/ALF entropy rate in finite dimension

In a finite-dimensional quantum system the Connes–Narnhofer–Thirring / Alicki–Fannes dynamical
entropy is `0`: for every operational partition `X` the correlation density matrix
`corrMatrix Φ ρ X n` factorises as a product through the `d²`-dimensional matrix space
`Fin d × Fin d`, so its rank is at most `d²` **uniformly in `n`**.  A density matrix of rank
`≤ d²` has von Neumann entropy `≤ log(d²)`, and the entropy *rate* `S(corrMatrix n)/n` is therefore
squeezed to `0`.

This is the well-known finite-dimensional degeneracy of quantum dynamical entropy: Alicki–Fannes,
*Quantum Dynamical Systems* (OUP 2001), observe that the AF entropy of a finite-dimensional system
vanishes precisely because `rank(ρ[X⁽ⁿ⁾]) ≤ (dim H)²`; Neshveyev–Størmer, *Dynamical Entropy in
Operator Algebras* (Springer 2006), record that the CNT entropy of a finite-dimensional algebra is
`0`.  The main results here are:

* `vonNeumannEntropy_corrMatrix_le_log`: `S(corrMatrix Φ ρ X n) ≤ log(d²)` for all `n`, obtained by
  chaining the maximum-entropy bound `vonNeumannEntropy_le_log_rank` (`EntropyRank`) with the
  Gram-factorisation rank bound `rank_corrVal_le` (`CNT.GramFactorization`); both the concavity /
  Jensen entropy bound and the rank-`≤ d²` factorisation live in those imported modules.
* `cntCumulativeEntropy_le_reservoir`: the uniform reservoir cap `S(corrMatrix n) ≤ 2·log d` for
  every `n`, tight at `d = 2` (saturated by the Pauli partition, see `ReservoirSaturation`) (issue
  #69).
* `cntEntropySeq_bddAbove`: the cumulative sequence `n ↦ S(corrMatrix n)` is bounded above by the
  fixed reservoir `log(d²)`; monotonicity in `n` is deliberately not claimed.
* `cntEntropyPartition_eq_zero` and `tendsto_cntEntropySeq_div`: the entropy rate is a genuine
  limit and equals `0` for **every** operational partition.
* `cntDynamicalEntropy_eq_zero`: the full CNT/ALF dynamical entropy is `0`.

The system-level equalities are `0 = 0` collapses forced by finite-dimensional degeneracy (mirroring
the disclosure in `AbelianCorner`); the substantive content is the per-resolution rank/entropy bound
`vonNeumannEntropy_corrMatrix_le_log`, uniform in `n`.
-/

open Matrix Real Filter
open scoped ComplexOrder Topology

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

variable {d : ℕ}

/-- The trivial one-cell operational partition: its single operator is the identity `1`.  It
witnesses that `OperationalPartition d 1` is inhabited, so the supremum defining the CNT dynamical
entropy ranges over a nonempty family. -/
def trivialPartition (d : ℕ) : OperationalPartition d 1 where
  op _ := 1
  partUnity := by simp

@[simp] theorem trivialPartition_op (i : Fin 1) : (trivialPartition d).op i = 1 := rfl

/-- **Uniform entropy bound.**  The von Neumann entropy of the CNT correlation matrix is at most
`log(d²)` at every resolution `n`, since its rank is `≤ d²`.  The bound chains the maximum-entropy
inequality `vonNeumannEntropy_le_log_rank` (`S ≤ log(rank)`) with the Gram-factorisation rank bound
`rank_corrVal_le` (`rank(corrVal) ≤ d²`); rank positivity comes from `DensityMatrix.rank_pos`. -/
theorem vonNeumannEntropy_corrMatrix_le_log (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    vonNeumannEntropy (corrMatrix Φ ρ X n) ≤ Real.log ((d : ℝ) ^ 2) := by
  have hrank : (corrMatrix Φ ρ X n).val.rank ≤ d ^ 2 := by
    rw [corrMatrix_val]; exact rank_corrVal_le Φ ρ X n
  refine (vonNeumannEntropy_le_log_rank (corrMatrix Φ ρ X n)).trans (Real.log_le_log ?_ ?_)
  · exact_mod_cast (corrMatrix Φ ρ X n).rank_pos
  · calc ((corrMatrix Φ ρ X n).val.rank : ℝ)
        ≤ ((d ^ 2 : ℕ) : ℝ) := by exact_mod_cast hrank
      _ = (d : ℝ) ^ 2 := by push_cast; ring

/-- **Reservoir cap for the cumulative entropy, in the `2·log d` form.**  This is the uniform-in-`n`
reservoir ceiling for the *iterated-refinement* cumulative entropy of a single operational partition
(the API's honest reading of `H(N₁, …, Nₙ)`): `S(corrMatrix Φ ρ X n) ≤ 2·log d` for every `n`.

The reservoir is `log(d²) = 2·log d`, **not** the naive single-copy ceiling `log d`: the
correlation-matrix construction lives on a `d²`-dimensional Gram factorization, so the honest cap is
`log(d²)`.  This bound is tight at `d = 2`: it is saturated by the Pauli operational partition at
the maximally mixed state (`vonNeumannEntropy_corrMatrix_pauliPartition_eq`, `ReservoirSaturation`).
The analogous Weyl-partition saturation for general `d` is standard but not formalized here.
Restated from `vonNeumannEntropy_corrMatrix_le_log` via `Real.log_pow` (`log (d²) = 2·log d`, valid
also at `d = 0` since `log 0 = 0`). -/
theorem cntCumulativeEntropy_le_reservoir (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) (n : ℕ) :
    vonNeumannEntropy (corrMatrix Φ ρ X n) ≤ 2 * Real.log (d : ℝ) := by
  have h := vonNeumannEntropy_corrMatrix_le_log Φ ρ X n
  rwa [Real.log_pow, Nat.cast_ofNat] at h

/-- **The cumulative entropy sequence is bounded.**  The saturation statement: the cumulative
sequence `n ↦ S(corrMatrix Φ ρ X n)` is bounded above by the fixed reservoir `log(d²)` uniformly in
the step count `n`.  Monotonicity in `n` is deliberately NOT claimed — it is unproven in general and
forced flat in the saturated regime — only this uniform reservoir cap is asserted. -/
theorem cntEntropySeq_bddAbove (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) :
    BddAbove (Set.range fun n => vonNeumannEntropy (corrMatrix Φ ρ X n)) := by
  refine ⟨Real.log ((d : ℝ) ^ 2), ?_⟩
  rintro x ⟨n, rfl⟩
  exact vonNeumannEntropy_corrMatrix_le_log Φ ρ X n

/-- **The entropy rate vanishes for every operational partition.**  The CNT entropy of a partition
is the infimum rate `inf_{n ≥ 1} S(corrMatrix n)/n`; since `S(corrMatrix n) ≤ log(d²)` uniformly,
the rate is squeezed to `0`. -/
theorem cntEntropyPartition_eq_zero (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) :
    cntEntropyPartition Φ ρ X = 0 := by
  classical
  rw [cntEntropyPartition_eq]
  set f : ℕ → ℝ := fun n => vonNeumannEntropy (corrMatrix Φ ρ X n) / (n : ℝ) with hf
  set S : Set ℝ := f '' Set.Ici 1 with hSdef
  have hlb : ∀ x ∈ S, 0 ≤ x := by
    rintro x ⟨n, _, rfl⟩
    exact div_nonneg (vonNeumannEntropy_nonneg _) (Nat.cast_nonneg n)
  have hne : S.Nonempty := ⟨f 1, 1, Set.mem_Ici.mpr le_rfl, rfl⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hlb x hx⟩
  refine le_antisymm ?_ (le_csInf hne hlb)
  refine ge_of_tendsto (ErgodicTheory.rate_to_zero_of_cumulative_bounded
    (fun n => vonNeumannEntropy_nonneg _) (vonNeumannEntropy_corrMatrix_le_log Φ ρ X)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hmem : f n ∈ S := ⟨n, Set.mem_Ici.mpr hn, rfl⟩
  exact csInf_le hbdd hmem

/-- **The sInf-rate is a genuine limit.**  For every operational partition, the entropy rate
`S(corrMatrix n)/n` converges (to the CNT partition entropy, which equals `0`).  This is the
well-definedness the sInf-definition captures: `0 ≤ S(corrMatrix n)/n ≤ log(d²)/n → 0`. -/
theorem tendsto_cntEntropySeq_div (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d))
    {k : ℕ} (X : OperationalPartition d k) :
    Filter.Tendsto (fun n => vonNeumannEntropy (corrMatrix Φ ρ X n) / (n : ℝ))
      Filter.atTop (nhds (cntEntropyPartition Φ ρ X)) := by
  rw [cntEntropyPartition_eq_zero]
  exact ErgodicTheory.rate_to_zero_of_cumulative_bounded
    (fun n => vonNeumannEntropy_nonneg _) (vonNeumannEntropy_corrMatrix_le_log Φ ρ X)

/-- **The CNT/ALF dynamical entropy vanishes in finite dimension.**  Taking the supremum of the
partition entropy rate over all operational partitions, every term is `0` (by
`cntEntropyPartition_eq_zero`); the trivial partition witnesses nonemptiness at `k = 1`, so the
supremum is `0`.  (The inner supremum over the empty partition type at `k = 0` is `⊥` and never
affects the outer supremum.)  This now visibly factors through the generic rate engine — the quantum
pigeonhole: the cumulative reservoir cap `S(corrMatrix n) ≤ log(d²)` plus the generic
`ErgodicTheory.rate_to_zero_of_cumulative_bounded` force the rate to `0`. -/
theorem cntDynamicalEntropy_eq_zero (Φ : UnitalStarEndo d) (ρ : DensityMatrix (Fin d)) :
    cntDynamicalEntropy Φ ρ = 0 := by
  unfold cntDynamicalEntropy
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => iSup_le fun X => ?_
    rw [cntEntropyPartition_eq_zero]
    exact le_of_eq EReal.coe_zero
  · refine le_iSup_of_le 1 (le_iSup_of_le (trivialPartition d) ?_)
    rw [cntEntropyPartition_eq_zero]
    exact le_of_eq EReal.coe_zero.symm

end ErgodicTheory.OperatorEntropy.CNT
