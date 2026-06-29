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
-/
