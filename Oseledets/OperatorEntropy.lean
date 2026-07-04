/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.OperatorEntropy.Basic
import Oseledets.OperatorEntropy.PartialTrace
import Oseledets.OperatorEntropy.KroneckerSpectrum
import Oseledets.OperatorEntropy.Klein
import Oseledets.OperatorEntropy.Additivity
import Oseledets.OperatorEntropy.Subadditivity
import Oseledets.OperatorEntropy.DiagonalSpectrum
import Oseledets.OperatorEntropy.CNT.Refinement
import Oseledets.OperatorEntropy.CNT.Construction
import Oseledets.OperatorEntropy.CNT.AbelianCorner

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

* `Oseledets.OperatorEntropy.vonNeumannEntropy` — `S(ρ) = ∑ᵢ negMulLog(λᵢ)`.
* `Oseledets.OperatorEntropy.partialTraceRight` / `partialTraceLeft` — the partial trace,
  trace-preserving and positivity-preserving (`PosSemidef.partialTraceRight`), packaged as a
  `DensityMatrix.partialTraceRight : DensityMatrix (nA × nB) → DensityMatrix nA`.
* `Oseledets.OperatorEntropy.eigenvalues_kronecker_multiset` — the spectrum of `A ⊗ₖ B`.
* `Oseledets.OperatorEntropy.vonNeumannEntropy_additive_kronecker` — `S(ρ ⊗ σ) = S(ρ) + S(σ)`.
* `Oseledets.OperatorEntropy.vonNeumannEntropy_subadditive` — `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`.
* `Oseledets.OperatorEntropy.CNT.cntDynamicalEntropy` / `cntDynamicalEntropyAbelian` — the
  Connes–Narnhofer–Thirring / Alicki–Fannes quantum dynamical entropy (supremum of the
  per-partition entropy rate over all, resp. all projection, operational partitions).
* `Oseledets.OperatorEntropy.CNT.cntDynamicalEntropyAbelian_eq_ksEntropy` — on the abelian
  (diagonal-subalgebra) corner the CNT dynamical entropy of `adPerm σ` equals the classical
  Kolmogorov–Sinai entropy `h(⇑σ)`. A permutation of a finite set has KS entropy `0`, so this
  system-level identity is `0 = 0`; the substantive content is the per-resolution identity below.
* `Oseledets.OperatorEntropy.CNT.vonNeumannEntropy_corrMatrix_eq_ksEntropySeq` — the substantive
  per-resolution identity `S(corrMatrix n) = ksEntropySeq n` underlying that collapse.
-/
