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
import ErgodicTheory.OperatorEntropy.CNT.Refinement
import ErgodicTheory.OperatorEntropy.CNT.Construction
import ErgodicTheory.OperatorEntropy.CNT.AbelianCorner

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
-/
