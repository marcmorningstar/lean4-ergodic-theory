/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Basic
import ErgodicTheory.OperatorEntropy.PartialTrace
import ErgodicTheory.OperatorEntropy.KroneckerSpectrum
import ErgodicTheory.OperatorEntropy.Klein
import ErgodicTheory.OperatorEntropy.Additivity
import ErgodicTheory.OperatorEntropy.Subadditivity
import ErgodicTheory.OperatorEntropy.DiagonalSpectrum
import ErgodicTheory.OperatorEntropy.EntropyRank
import ErgodicTheory.OperatorEntropy.EntropyStrictPos
import ErgodicTheory.OperatorEntropy.PartialTraceKraus
import ErgodicTheory.OperatorEntropy.CNT.Refinement
import ErgodicTheory.OperatorEntropy.CNT.Construction
import ErgodicTheory.OperatorEntropy.CNT.AbelianCorner
import ErgodicTheory.OperatorEntropy.CNT.GramFactorization
import ErgodicTheory.OperatorEntropy.CNT.FiniteDimZero
import ErgodicTheory.OperatorEntropy.CNT.ReservoirSaturation
import ErgodicTheory.OperatorEntropy.CNT.AbelianCornerFull
import ErgodicTheory.OperatorEntropy.CNT.AbelianFekete
import ErgodicTheory.OperatorEntropy.CNT.SubadditivityCounterexample
import ErgodicTheory.OperatorEntropy.CNT.AbelianRestriction
import ErgodicTheory.OperatorEntropy.CNT.NonCommutativeCertificate
import ErgodicTheory.OperatorEntropy.EntropyPure
import ErgodicTheory.OperatorEntropy.QuantumSeal
import ErgodicTheory.OperatorEntropy.RelativeEntropy
import ErgodicTheory.OperatorEntropy.RelEntropyAdditivity
import ErgodicTheory.OperatorEntropy.StinespringReduction
import ErgodicTheory.OperatorEntropy.PetzRecovery
import ErgodicTheory.OperatorEntropy.Lieb.OperatorConvex
import ErgodicTheory.OperatorEntropy.Lieb.StrictLog
import ErgodicTheory.OperatorEntropy.Lieb.Step0Dilation
import ErgodicTheory.OperatorEntropy.Lieb.DilationProto
import ErgodicTheory.OperatorEntropy.Lieb.Dilation
import ErgodicTheory.OperatorEntropy.Lieb.Perspective
import ErgodicTheory.OperatorEntropy.Lieb.JointConvexity
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessing
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessingGeneral
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessingCPTP
import ErgodicTheory.OperatorEntropy.Lieb.ModularOperator
import ErgodicTheory.OperatorEntropy.Lieb.ChoiLoewner
import ErgodicTheory.OperatorEntropy.Lieb.RectOperatorJensen
import ErgodicTheory.OperatorEntropy.Lieb.PetzVecBridge
import ErgodicTheory.OperatorEntropy.Lieb.PetzKadison
import ErgodicTheory.OperatorEntropy.Lieb.PetzReconciliation
import ErgodicTheory.OperatorEntropy.Lieb.PetzChannelContraction
import ErgodicTheory.OperatorEntropy.Lieb.PetzAnalyticContinuation
import ErgodicTheory.OperatorEntropy.Lieb.PetzSufficiencyB
import ErgodicTheory.OperatorEntropy.Lieb.RigidityTail
import ErgodicTheory.OperatorEntropy.Lieb.ContractionRigiditySkeleton
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityM3sc
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityIntertwine
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityRecovery28
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualitySufficiency
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityGeneral
import ErgodicTheory.OperatorEntropy.GrowingTower.Tower
import ErgodicTheory.OperatorEntropy.GrowingTower.SealLift
import ErgodicTheory.OperatorEntropy.GrowingTower.World
import ErgodicTheory.OperatorEntropy.GrowingTower.ChainAlgebra
import ErgodicTheory.OperatorEntropy.GrowingTower.ChainState
import ErgodicTheory.OperatorEntropy.GrowingTower.ModularClock
import ErgodicTheory.OperatorEntropy.GrowingTower.QuantumBernoulli

/-!
# Finite-dimensional operator entropy

Self-contained finite-dimensional operator-entropy primitives over complex matrices: the
`DensityMatrix` of a finite quantum system (a positive-semidefinite, unit-trace matrix), its
`vonNeumannEntropy`, the partial trace as a positive trace-preserving (and completely positive,
in Kraus/compression form) coarse-graining, the Kronecker spectrum, and the additivity and
subadditivity of the von Neumann entropy.

The mathematical content mirrors the standard quantum-information references
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, §11.3; Carlen,
*Trace Inequalities and Quantum Entropy*, §2.3). In particular **subadditivity** rests only on
the elementary **Klein inequality** (Carlen Thm 2.11), not on the deeper joint-convexity /
Lieb-concavity layer.

Beyond that foundational layer, this umbrella re-exports the full finite-dimensional
relative-entropy development built on the same matrix infrastructure: the Umegaki relative
entropy, Lieb's joint-convexity theorem, the data-processing inequality under a Stinespring
dilation, and both directions of Petz's equality theorem.

## Principal results

* `ErgodicTheory.OperatorEntropy.vonNeumannEntropy` — `S(ρ) = ∑ᵢ negMulLog(λᵢ)`.
* `ErgodicTheory.OperatorEntropy.partialTraceRight` / `partialTraceLeft` — the partial trace,
  trace-preserving and positivity-preserving (`PosSemidef.partialTraceRight`), packaged as a
  `DensityMatrix.partialTraceRight : DensityMatrix (nA × nB) → DensityMatrix nA`.
* `ErgodicTheory.OperatorEntropy.eigenvalues_kronecker_multiset` — the spectrum of `A ⊗ₖ B`.
* `ErgodicTheory.OperatorEntropy.vonNeumannEntropy_additive_kronecker` — `S(ρ ⊗ σ) = S(ρ) + S(σ)`.
* `ErgodicTheory.OperatorEntropy.vonNeumannEntropy_subadditive` — `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`.
* `ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropy` / `cntDynamicalEntropyAbelian` — the
  Connes–Narnhofer–Thirring / Alicki–Fannes quantum dynamical entropy (supremum of the
  per-partition entropy rate over all, resp. all projection, operational partitions).
* `ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropyAbelian_eq_ksEntropy` — on the abelian
  (diagonal-subalgebra) corner the CNT dynamical entropy of `adPerm σ` equals the classical
  Kolmogorov–Sinai entropy `h(⇑σ)`. A permutation of a finite set has KS entropy `0`, so this
  system-level identity is `0 = 0`; the substantive content is the per-resolution identity below.
* `ErgodicTheory.OperatorEntropy.CNT.vonNeumannEntropy_corrMatrix_eq_ksEntropySeq` — the substantive
  per-resolution identity `S(corrMatrix n) = ksEntropySeq n` underlying that collapse.
* `ErgodicTheory.OperatorEntropy.partialTraceRight_eq_kraus` / `partialTraceLeft_eq_kraus` — the
  literal explicit-Kraus (block-inclusion) presentation of the partial traces,
  `Tr_B M = ∑ⱼ Eⱼ M Eⱼᴴ`, with the Kraus operators named as honest `Matrix` `def`s (issue #25).
* `ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_rank` — the maximum-entropy bound
  `S(ρ) ≤ log(rank ρ)`; `vonNeumannEntropy_pos_of_sq_ne` — strict positivity of the entropy for a
  non-idempotent (mixed) state.
* `ErgodicTheory.OperatorEntropy.CNT.corrVal_eq_conjTranspose_mul_self` / `rank_corrVal_le` — the
  CNT correlation matrix is a Gram matrix `Vᴴ V`, so its rank is `≤ d²` uniformly in the resolution.
* `ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropy_eq_zero` and `cntEntropyPartition_eq_zero`
  — the finite-dimensional collapse: the CNT/ALF entropy rate is `≡ 0` for every operational
  partition, with `tendsto_cntEntropySeq_div` the accompanying well-definedness (the rate is a
  genuine limit) (issue #26).
* `ErgodicTheory.OperatorEntropy.CNT.ksEntropy_eq_cntDynamicalEntropy` and
  `cntDynamicalEntropyAbelianFull_eq_ksEntropy` — the classical KS entropy equals the full (resp.
  full-diagonal) CNT dynamical entropy of `adPerm σ`, upgrading the one-sided abelian-corner bound
  (both sides `0` in finite dimension).
* `ErgodicTheory.OperatorEntropy.CNT.subadditive_vonNeumannEntropy_corrMatrix_abelian` and
  `tendsto_cntEntropyPartition_abelian` — on the abelian corner the entropy sequence is
  `Subadditive` (Fekete), so the CNT rate is a genuine limit there; `not_subadditive_cnt_entropySeq`
  exhibits an explicit two-element operational partition (identity dynamics, pure state) for which
  subadditivity **fails**, explaining why the CNT rate must be defined as an infimum, not a Fekete
  limit (issue #26).
* `ErgodicTheory.OperatorEntropy.relEntropy_nonneg` — nonnegativity of the Umegaki relative
  entropy `D(ρ‖σ) ≥ 0` (Klein's inequality).
* `ErgodicTheory.OperatorEntropy.Lieb.relEntropyMat_jointly_convex` — Lieb's joint convexity of
  the matrix relative entropy.
* `ErgodicTheory.OperatorEntropy.monotonicity_relEntropy_under_stinespring` — the data-processing
  inequality: relative entropy is monotone under a Stinespring-dilated channel.
* `ErgodicTheory.OperatorEntropy.petz_recovery` and
  `ErgodicTheory.OperatorEntropy.Lieb.petz_equality_recovery_general` — the two directions of
  Petz's equality theorem (Petz recovery ⟺ saturation of the data-processing inequality).
* `ErgodicTheory.OperatorEntropy.CNT.vonNeumannEntropy_corrMatrix_pauliPartition_eq` — the reservoir
  saturation: for the four-element Pauli partition the one-step CNT correlation entropy hits its
  `log(d²)` cap exactly, so the cumulative-entropy cap `cntCumulativeEntropy_le_reservoir`
  (`S(corrMatrix n) ≤ 2·log d`, with `cntEntropySeq_bddAbove` the bounded sequence) is tight by
  saturation, not zero (issue #69).
* `ErgodicTheory.OperatorEntropy.blockEntropy_eq` / `tendsto_blockEntropy_div` — the growing tower:
  the `n`-block von Neumann entropy is `n · S(ρ)`, so block entropy grows linearly with a positive
  per-site spatial rate `S(ρ) > 0` for any mixed single-site state `ρ` (issue #70).
* `ErgodicTheory.OperatorEntropy.growingQuantumWorld_exists` — the bundled world: one growing object
  that is simultaneously alive (positive block-entropy rate), sealed (strict relative-entropy drop),
  and non-commutative at its base (issue #70).
* `ErgodicTheory.OperatorEntropy.quantumBernoulliShift_exists` — the quantum Bernoulli shift: a
  fixed directed system with a shift-invariant tracial state, a temporal-window entropy rate
  `log 2`, and a per-stage strict relative-entropy seal under dephasing (issue #71).
* `ErgodicTheory.OperatorEntropy.modAut_maximallyMixed_eq_id` / `modAut_diagState_ne_id` — the
  finite modular clock: the modular automorphism is trivial exactly at the maximally mixed state
  and moves a non-flat diagonal state, an intrinsic-clock dichotomy (issue #71).
-/
