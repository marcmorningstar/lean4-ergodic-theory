/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.MultiplicativeErgodic
import ErgodicTheory.Lyapunov.Extensions.Corollaries
import ErgodicTheory.Lyapunov.Extensions.Spectrum
import ErgodicTheory.Lyapunov.Extensions.ExponentSums
import ErgodicTheory.Lyapunov.Extensions.ExteriorCocycle
import ErgodicTheory.Lyapunov.Extensions.DetIdentity
import ErgodicTheory.Lyapunov.Extensions.Inverse
import ErgodicTheory.Lyapunov.Extensions.Restriction
import ErgodicTheory.Lyapunov.Extensions.NonErgodic
import ErgodicTheory.Lyapunov.Extensions.Regularity
import ErgodicTheory.Lyapunov.Extensions.Singular
import ErgodicTheory.Lyapunov.Extensions.SingularExponent
import ErgodicTheory.Lyapunov.Extensions.SingularExponentBounds
import ErgodicTheory.Lyapunov.Extensions.SingularExponentTop
import ErgodicTheory.Lyapunov.Extensions.SingularDet
import ErgodicTheory.Lyapunov.Extensions.SingularDetGrowth
import ErgodicTheory.Lyapunov.Extensions.SingularExponentGenLog
import ErgodicTheory.Lyapunov.Extensions.SingularKernelStratum
import ErgodicTheory.Lyapunov.Extensions.SingularRank
import ErgodicTheory.Lyapunov.Extensions.SingularKernelSubmodule
import ErgodicTheory.Lyapunov.Extensions.SingularEventualKernel
import ErgodicTheory.Lyapunov.Extensions.SingularKernelEquivariant
import ErgodicTheory.Lyapunov.Extensions.SingularRankMeasurable
import ErgodicTheory.Lyapunov.Extensions.SingularRankMeasurable2
import ErgodicTheory.Lyapunov.Extensions.SingularRankMinor
import ErgodicTheory.Lyapunov.Extensions.SingularDimMeasurable
import ErgodicTheory.Lyapunov.Extensions.SingularKernelMeasurableGraph
import ErgodicTheory.Lyapunov.Extensions.SingularKernelProjector
import ErgodicTheory.Lyapunov.Extensions.SingularEventualKernelProjector
import ErgodicTheory.Lyapunov.Extensions.SingularSublevelProjector
import ErgodicTheory.Lyapunov.Extensions.SingularSublevelEventual
import ErgodicTheory.Lyapunov.Extensions.SingularSubspaceDist
import ErgodicTheory.Lyapunov.Extensions.SingularPerDirectionExponent
import ErgodicTheory.Lyapunov.Extensions.SingularSpectralValues
import ErgodicTheory.Lyapunov.Extensions.SingularSpectrumConstant
import ErgodicTheory.Lyapunov.Extensions.SingularSlowSpace
import ErgodicTheory.Lyapunov.Extensions.SingularBandConverge
import ErgodicTheory.Lyapunov.Extensions.SingularSlowSpaceUnconditional
import ErgodicTheory.Lyapunov.Extensions.SingularLambdaBarFiltration
import ErgodicTheory.Lyapunov.Extensions.SingularLambdaBarMeasurable
import ErgodicTheory.Lyapunov.Extensions.ConstantCocycle
import ErgodicTheory.TwoSided.Invertible
import ErgodicTheory.TwoSided.SpectralRank
import ErgodicTheory.TwoSided.MeasurableInf
import ErgodicTheory.TwoSided.StrongExport
import ErgodicTheory.TwoSided.KingmanMeans
import ErgodicTheory.TwoSided.Reflection
import ErgodicTheory.TwoSided.RestrictedCocycle
import ErgodicTheory.TwoSided.RestrictedExponent
import ErgodicTheory.TwoSided.Transversality
import ErgodicTheory.TwoSided.SplittingAssembly
import ErgodicTheory.Continuous.Flow
import ErgodicTheory.Continuous.Reduction
import ErgodicTheory.Continuous.BetweenTimes
import ErgodicTheory.Continuous.Equivariance
import ErgodicTheory.Continuous.MultiplicativeErgodicFlow
import ErgodicTheory.Continuous.Suspension
import ErgodicTheory.Continuous.SuspensionMeasure
import ErgodicTheory.Continuous.SuspensionSpace
import ErgodicTheory.Continuous.SuspensionFlow
import ErgodicTheory.Continuous.SuspensionFlowMP
import ErgodicTheory.Continuous.ReturnTimeExponent
import ErgodicTheory.Continuous.ReturnTimeTopExponent
import ErgodicTheory.Continuous.SuspensionCocycle
import ErgodicTheory.Continuous.SuspensionLapCount
import ErgodicTheory.Continuous.SuspensionFlowCocycle
import ErgodicTheory.Continuous.SuspensionCoverCocycle
import ErgodicTheory.Continuous.SuspensionCoverFlow
import ErgodicTheory.Continuous.SuspensionDescent
import ErgodicTheory.Continuous.SuspensionNlap
import ErgodicTheory.Continuous.SuspensionFlowExponent
import ErgodicTheory.Continuous.SuspensionBetweenReturns
import ErgodicTheory.Continuous.SuspensionFullTimeExponent
import ErgodicTheory.Continuous.SuspensionBddRoofExponent
import ErgodicTheory.Continuous.SuspensionMeasureTransfer
import ErgodicTheory.Continuous.SuspensionDisintegration
import ErgodicTheory.Continuous.SuspensionGrowthDescent
import ErgodicTheory.Continuous.SuspensionExponentDescent
import ErgodicTheory.Continuous.SuspensionSpaceExponent
import ErgodicTheory.Continuous.SuspensionSpaceExponentValue
import ErgodicTheory.Continuous.SuspensionQuotientImage
import ErgodicTheory.Continuous.SuspensionFlowExponentValue
import ErgodicTheory.Continuous.SuspensionReturnTimeMeasurable
import ErgodicTheory.Continuous.SuspensionExponentSetEquiv
import ErgodicTheory.Continuous.SuspensionExponentSetMeasurable
import ErgodicTheory.Continuous.SuspensionFlowExponentFinal
import ErgodicTheory.Smooth.DerivativeCocycle
import ErgodicTheory.Smooth.Expanding
import ErgodicTheory.Smooth.RokhlinExpanding
import ErgodicTheory.Smooth.Pesin.SRBData
import ErgodicTheory.Smooth.Pesin.ManeLowerBound
import ErgodicTheory.Smooth.Pesin.PesinFormula
import ErgodicTheory.Examples.Elementary
import ErgodicTheory.Entropy.Partition
import ErgodicTheory.Entropy.Join
import ErgodicTheory.Entropy.Subadditive
import ErgodicTheory.Entropy.Subadditive2
import ErgodicTheory.Entropy.Fekete
import ErgodicTheory.Entropy.KSEntropy
import ErgodicTheory.Entropy.KSEntropyBounds
import ErgodicTheory.Entropy.KSEntropySystem
import ErgodicTheory.Entropy.KSEntropyProps
import ErgodicTheory.Entropy.KSEntropyJoin
import ErgodicTheory.Entropy.KSEntropyMono
import ErgodicTheory.Entropy.MargulisRuelleAbstract
import ErgodicTheory.Entropy.MargulisRuelleSharpened
import ErgodicTheory.MeasureTheory.CoveringFromVolume
import ErgodicTheory.MeasureTheory.AnalyticUniversallyMeasurable
import ErgodicTheory.Entropy.Ruelle.Count
import ErgodicTheory.Entropy.Ruelle.SharpCovering
import ErgodicTheory.Entropy.Ruelle.MargulisRuelleSharp
import ErgodicTheory.Singular.SingularFiltrationMeasurable
import ErgodicTheory.Lyapunov.Extensions.ConstantCocycleSpectralRadius
import ErgodicTheory.Lyapunov.Extensions.SingularStratumExponent
import ErgodicTheory.Continuous.SuspensionPartialSumExponent
import ErgodicTheory.Examples.RuelleDoubling
import ErgodicTheory.Examples.CatMapOrbit
import ErgodicTheory.Examples.CatMapToral
import ErgodicTheory.Examples.CatMapDerivativeCocycle
import ErgodicTheory.Examples.CatMapPerPartition
import ErgodicTheory.Examples.Rokhlin.AbstractEqui
import ErgodicTheory.Examples.Rokhlin.DoublingCrux
import ErgodicTheory.Examples.Rokhlin.DoublingEquality
import ErgodicTheory.Examples.Rokhlin.DoublingPesin
import ErgodicTheory.Entropy.CondChainRule
import ErgodicTheory.Entropy.CondPullback
import ErgodicTheory.Entropy.CondJointPullback
import ErgodicTheory.Entropy.CondMono
import ErgodicTheory.Entropy.CondEntropyContinuous
import ErgodicTheory.Entropy.CondKSEntropySystem
import ErgodicTheory.Entropy.FactorEntropy
import ErgodicTheory.Entropy.FactorGeneratorSaturate
import ErgodicTheory.Entropy.CondGivenPartitionBridge
import ErgodicTheory.Entropy.AbramovRokhlin
import ErgodicTheory.Entropy.AbramovRokhlinPartition
import ErgodicTheory.Entropy.CondKSMovingLimit
import ErgodicTheory.Entropy.AbramovRokhlinGenerator
import ErgodicTheory.Entropy.GeneratorTheorem
import ErgodicTheory.Krieger.ZIterate
import ErgodicTheory.Krieger.InfoFunction
import ErgodicTheory.Krieger.NameCount
import ErgodicTheory.Krieger.RokhlinTower
import ErgodicTheory.Krieger.Coding
import ErgodicTheory.Krieger.Krieger
import ErgodicTheory.Krieger.CountableEntropy
import ErgodicTheory.Krieger.SMB
import ErgodicTheory.Krieger.Generator
import ErgodicTheory.Krieger.PrefixCode
import ErgodicTheory.Krieger.SMBSharp
import ErgodicTheory.Krieger.CodeMap
import ErgodicTheory.Krieger.NameCountSharp
import ErgodicTheory.Krieger.KeaneSerafin
import ErgodicTheory.Krieger.Recovery
import ErgodicTheory.Krieger.SMBPointwise
import ErgodicTheory.Krieger.ColumnCode
import ErgodicTheory.Krieger.TowerCode
import ErgodicTheory.Krieger.SMBLeaves
import ErgodicTheory.Krieger.CodeTerm
import ErgodicTheory.Krieger.UpperSMB
import ErgodicTheory.Krieger.Interleave
import ErgodicTheory.Krieger.RefTower
import ErgodicTheory.Krieger.StageBuild
import ErgodicTheory.Krieger.Weave
import ErgodicTheory.Krieger.Bracket
import ErgodicTheory.Multifractal
-- Direct imports of the `Multifractal` guarded modules (the `ErgodicTheory.Multifractal` umbrella
-- above still re-exports them; these keep each guarded declaration's defining module imported
-- directly, so the axiom guards below cannot silently narrow if the umbrella is ever pruned).
import ErgodicTheory.Multifractal.BernoulliDimension
import ErgodicTheory.Multifractal.BernoulliEntropy
import ErgodicTheory.Multifractal.BernoulliErgodic
import ErgodicTheory.Multifractal.BernoulliHeterogeneous
import ErgodicTheory.Multifractal.BernoulliSuspensionFlow
import ErgodicTheory.Multifractal.BernoulliSuspensionFlowErgodic
import ErgodicTheory.Multifractal.BernoulliSuspensionWitness
import ErgodicTheory.Multifractal.BernoulliTwoSidedErgodic
import ErgodicTheory.Multifractal.BernoulliTwoSidedGenerating
import ErgodicTheory.Multifractal.BernoulliTwoSidedSystemEntropy
import ErgodicTheory.Multifractal.Degeneracy
import ErgodicTheory.Multifractal.HausdorffDimension
import ErgodicTheory.Multifractal.LocalDimension
import ErgodicTheory.Multifractal.LogConvex
import ErgodicTheory.Multifractal.Measure
import ErgodicTheory.Multifractal.Monotone
import ErgodicTheory.Multifractal.RefiningLimit
import ErgodicTheory.Multifractal.Source.FlowEmpirical
import ErgodicTheory.Multifractal.Source.FlowPartition
import ErgodicTheory.Multifractal.SymbolicDimension
import ErgodicTheory.Entropy.GeneratorTheoremTwoSided
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Entropy.ProductIdEntropy
import ErgodicTheory.Multifractal.BernoulliSuspensionEntropy
import ErgodicTheory.Multifractal.BernoulliSuspensionCondEntropy
import ErgodicTheory.Entropy.CondProductIdEntropy
import ErgodicTheory.Entropy.CondChainRuleSup
import ErgodicTheory.Entropy.CondKSEntropyConjugacy
import ErgodicTheory.OperatorEntropy
-- Direct imports of the `OperatorEntropy` guarded corner modules (the `ErgodicTheory.OperatorEntropy`
-- umbrella above still re-exports them; these keep each guarded declaration's defining module
-- imported directly, so the axiom guards below cannot silently narrow if the umbrella is pruned).
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
import ErgodicTheory.OperatorEntropy.CNT.AbelianCornerFull
import ErgodicTheory.OperatorEntropy.CNT.AbelianFekete
import ErgodicTheory.OperatorEntropy.CNT.SubadditivityCounterexample
import ErgodicTheory.OperatorEntropy.RelativeEntropy
import ErgodicTheory.OperatorEntropy.PetzRecovery
import ErgodicTheory.OperatorEntropy.Lieb.OperatorConvex
import ErgodicTheory.OperatorEntropy.RelEntropyAdditivity
import ErgodicTheory.OperatorEntropy.StinespringReduction
import ErgodicTheory.OperatorEntropy.Lieb.DilationProto
import ErgodicTheory.OperatorEntropy.Lieb.Dilation
import ErgodicTheory.OperatorEntropy.Lieb.Perspective
import ErgodicTheory.OperatorEntropy.Lieb.JointConvexity
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessing
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessingGeneral
import ErgodicTheory.OperatorEntropy.Lieb.DataProcessingCPTP
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityRecovery28
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualitySufficiency
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityGeneral
-- Direct imports of the issue #30 cat-map suspension-flow witness and the issue #29 Livšic modules
-- whose declarations are guarded below (keeping each guarded declaration's defining module imported
-- directly, so the axiom guards cannot silently narrow if an umbrella is ever pruned).
import ErgodicTheory.Examples.CatMapSuspensionFlow
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.HolderExtend
import ErgodicTheory.Livsic.Abstract
import ErgodicTheory.Livsic.FullShiftClosing
import ErgodicTheory.Livsic.DenseOrbit
import ErgodicTheory.Livsic.ContinuousRigidity
import ErgodicTheory.Livsic.BoundedRigidity
import ErgodicTheory.Livsic.FullShift
-- Direct imports of the issue #32 (two-sided shift, SFTs, cat map) + issue #33 (doubling map)
-- Livšic-II modules whose declarations are guarded below.
import ErgodicTheory.Livsic.ErgodicDenseOrbit
import ErgodicTheory.Livsic.DoublingClosing
import ErgodicTheory.Livsic.Doubling
import ErgodicTheory.Livsic.SubshiftFiniteType
import ErgodicTheory.Livsic.SubshiftDenseOrbit
import ErgodicTheory.Livsic.BiShiftMetric
import ErgodicTheory.Livsic.BiShiftClosing
import ErgodicTheory.Livsic.BiShiftDenseOrbit
import ErgodicTheory.Livsic.BiShiftFull
import ErgodicTheory.Examples.CatMapCover
import ErgodicTheory.Examples.CatMapEigenShadow
import ErgodicTheory.Examples.CatMapClosing
-- Direct imports of the issue #37 representative-free flow-exponent modules whose declarations are
-- guarded below (the descended `flowExponentAt` quotient and its cat-suspension instantiation).
import ErgodicTheory.Continuous.SuspensionFlowExponentQuotient
import ErgodicTheory.Examples.CatMapSuspensionFlowQuotient
-- Direct imports of the issue #36 Livšic flow tier: the regularity-free flow coboundary and its
-- periodic-orbit obstruction, and the suspension-flow landing whose declarations are guarded below.
import ErgodicTheory.Livsic.FlowCoboundary
import ErgodicTheory.Continuous.SuspensionCoboundary
import ErgodicTheory.Examples.CatMapFlowCoboundary
import ErgodicTheory.Multifractal.BernoulliTwoSidedMixing
import ErgodicTheory.Ergodic.EigenvalueMixing
import ErgodicTheory.Continuous.SuspensionTimeOneCoeff
import ErgodicTheory.Continuous.SuspensionTimeOneParseval
import ErgodicTheory.Continuous.SuspensionTimeOneErgodic
import ErgodicTheory.Multifractal.BernoulliSuspensionTimeOneErgodic
-- Direct imports of the issue #47 cat-map spectral-rigidity modules whose declarations are guarded
-- below (the eigenfunction-vanishing headline and the constant-irrational-roof time-`1` ergodicity).
import ErgodicTheory.Examples.CatMapEigenfunction
import ErgodicTheory.Examples.CatMapSuspensionTimeOneErgodic
import ErgodicTheory.Entropy.KSEntropyPow
import ErgodicTheory.Continuous.SuspensionRescale
import ErgodicTheory.Continuous.SuspensionEntropyDescent
-- Direct imports of the issue #34 unbounded measurable Livšic rigidity tier (Katok–Hasselblatt
-- 19.2.4): the classical Lusin theorem, the two-sided natural-extension factor + past ⊗ future
-- product structure, the stable/unstable essential-oscillation bounds, the Fubini glue, and the full
-- measurable-rigidity equivalence — all guarded below.
import ErgodicTheory.MeasureTheory.LusinContinuousOn
import ErgodicTheory.Livsic.MeasurableRigidity
import ErgodicTheory.Livsic.BiShiftFactor
import ErgodicTheory.Livsic.BiShiftProductStructure
import ErgodicTheory.Livsic.BiShiftStableOscillation
import ErgodicTheory.Livsic.BiShiftUnstableOscillation
import ErgodicTheory.Livsic.BiShiftMeasurableRigidity
import ErgodicTheory.Livsic.MeasurableRigidityFull

-- Direct imports of the issue #11 Arsenin–Kunugui tier: the analytic-set closure lemmas, the
-- generalized first separation and coanalytic weak-reduction theorems, the Saint Raymond /
-- Kunugui–Novikov section theorems, the compact-section projection (Novikov, Srivastava 4.7.11),
-- and the everywhere-Borel singular filtration converter — all guarded below.
import ErgodicTheory.MeasureTheory.AnalyticSetLemmas
import ErgodicTheory.MeasureTheory.NovikovSeparation
import ErgodicTheory.MeasureTheory.CoanalyticReduction
import ErgodicTheory.MeasureTheory.KunuguiNovikov
import ErgodicTheory.MeasureTheory.CompactSectionProjection
import ErgodicTheory.Singular.SingularFiltrationBorel
import ErgodicTheory.Entropy.FinJoin
import ErgodicTheory.Entropy.JoinEntropyCompare
import ErgodicTheory.Continuous.FlowCondEntropyShift
import ErgodicTheory.Continuous.FlowEntropyContinuity
import ErgodicTheory.Continuous.SuspensionMeasureContinuity
import ErgodicTheory.Continuous.FlowAbramov

/-!
# Axiom audit

A guarded audit that the target theorem `ErgodicTheory.oseledets_filtration` and every other
headline of the formalization depend only on Lean/Mathlib's standard axioms — in particular on
no `sorryAx` and no extra axioms. The audited declarations now span the whole development: the
Oseledets filtration and its companion corollaries, the additive/exterior/inverse/singular
Lyapunov extensions, the two-sided splitting and continuous-flow MET, and the entropy,
Krieger-generator, multifractal and finite-dimensional quantum operator-entropy layers (von
Neumann/Umegaki relative entropy, Klein/Lieb joint convexity, the CPTP data-processing
inequality, CNT dynamical entropy, and both directions of Petz's equality theorem).

Each `#guard_msgs in #print axioms` block below pins a declaration's axiom set and **fails the
build if it ever differs**. Almost every block expects `[propext, Classical.choice, Quot.sound]`;
a few (e.g. `ErgodicTheory.Krieger.sentinelEncodeList_injective`, and `ErgodicTheory.goldenMean_proper`,
a decidable non-membership fact, needing only `[propext]`) honestly expect a smaller set. This
`AxiomAudit` library is a `defaultTargets` entry (see `lakefile.toml`), so the check runs on every
`lake build` as a continuously-enforced regression test rather than an informational dump (it
produces no output on success).

Scope caveat: `#print axioms` certifies axiom cleanliness only. It does **not** certify that a
guarded declaration states what its name suggests, nor that its hypotheses are satisfiable — a
number of audited headlines are honestly hypothesis-carrying (documented at their definition
sites).
-/

/-- info: 'ErgodicTheory.oseledets_filtration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_filtration

/-- info: 'ErgodicTheory.oseledets_filtration'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_filtration'

/-- info: 'ErgodicTheory.oseledets_top_exponent_eq_furstenbergKesten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_top_exponent_eq_furstenbergKesten

/-- info: 'ErgodicTheory.oseledets_filtration_with_multiplicities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_filtration_with_multiplicities

/-- info: 'ErgodicTheory.IsOseledetsFiltration.ae_mem_iff_limsup_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.ae_mem_iff_limsup_le

/-- info: 'ErgodicTheory.IsOseledetsFiltration.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.unique

/-- info: 'ErgodicTheory.IsOseledetsFiltration.tendsto_log_opNorm_cocycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.tendsto_log_opNorm_cocycle

/-- info: 'ErgodicTheory.IsOseledetsFiltration.exists_finrank_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.exists_finrank_ae_eq

/-- info: 'ErgodicTheory.IsOseledetsFiltration.exists_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.exists_multiplicity

/-- info: 'ErgodicTheory.IsOseledetsFiltration.k_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.k_pos

-- Additive extensions: the full Lyapunov spectrum object.

/-- info: 'ErgodicTheory.exponents_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exponents_antitone

/-- info: 'ErgodicTheory.exponents_tendsto_log_singularValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exponents_tendsto_log_singularValue

/-- info: 'ErgodicTheory.exp_exponents_eq_eigenvalues₀_oseledetsLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exp_exponents_eq_eigenvalues₀_oseledetsLimit

-- Exponent sums, sign/vanishing, and the top-k telescoping (items 1, 3).

/-- info: 'ErgodicTheory.sumPosExp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumPosExp_nonneg

/-- info: 'ErgodicTheory.sumPosExp_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumPosExp_eq_zero_iff

/-- info: 'ErgodicTheory.sumPosExp_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumPosExp_pos_iff

/-- info: 'ErgodicTheory.sumNegExp_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumNegExp_nonpos

/-- info: 'ErgodicTheory.sumNegExp_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumNegExp_eq_zero_iff

/-- info: 'ErgodicTheory.sumNegExp_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumNegExp_neg_iff

/-- info: 'ErgodicTheory.gammaK_eq_sum_top_exponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.gammaK_eq_sum_top_exponents

-- Exterior/wedge growth (item 2) and the trace/determinant identity (item 7).

/-- info: 'ErgodicTheory.cocycle_extGen_eq_compound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycle_extGen_eq_compound

/-- info: 'ErgodicTheory.tendsto_log_opNorm_compound_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_log_opNorm_compound_cocycle

/-- info: 'ErgodicTheory.sumPosExp_eq_gammaK_card_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumPosExp_eq_gammaK_card_pos

/-- info: 'ErgodicTheory.sumAllExp_eq_integral_log_abs_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sumAllExp_eq_integral_log_abs_det

/-- info: 'ErgodicTheory.tendsto_log_abs_det_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_log_abs_det_cocycle

/-- info: 'ErgodicTheory.tendsto_abs_det_cocycle_atTop_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_abs_det_cocycle_atTop_zero

-- Inverse / time reversal (item 8).

/-- info: 'ErgodicTheory.singularValues_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.singularValues_inv

/-- info: 'ErgodicTheory.tendsto_log_singularValue_inv_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_log_singularValue_inv_cocycle

/-- info: 'ErgodicTheory.topExponent_inv_eq_neg_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.topExponent_inv_eq_neg_bot

-- Restriction to an invariant subbundle (item 5).

/-- info: 'ErgodicTheory.restrictedSpectrum_subset_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restrictedSpectrum_subset_ae

/-- info: 'ErgodicTheory.restricted_multiplicity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_multiplicity_le

/-- info: 'ErgodicTheory.restricted_finrank_invariant_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_finrank_invariant_ae

-- Restriction Stage (ii): the full restricted (strict) Oseledets filtration (item 5, deferred part).

/-- info: 'ErgodicTheory.restricted_inf_measurableSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_inf_measurableSubspace

/-- info: 'ErgodicTheory.restricted_inf_witness_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_inf_witness_equivariant

/-- info: 'ErgodicTheory.restricted_inf_witness_finrank_invariant_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_inf_witness_finrank_invariant_ae

/-- info: 'ErgodicTheory.restricted_inf_finrank_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_inf_finrank_ae_eq

/-- info: 'ErgodicTheory.restricted_flag_structure_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_flag_structure_ae

/-- info: 'ErgodicTheory.restricted_strict_filtration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_strict_filtration

-- Non-ergodic version (item 9A).

/-- info: 'ErgodicTheory.tendsto_gammaK_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_gammaK_nonergodic

/-- info: 'ErgodicTheory.exists_exponents_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exists_exponents_nonergodic

/-- info: 'ErgodicTheory.exists_sumPosExp_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exists_sumPosExp_nonergodic

-- Regularity in the generator: Fekete inf + USC/LSC (item 4).

/-- info: 'ErgodicTheory.gammaK_eq_gammaKInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.gammaK_eq_gammaKInf

/-- info: 'ErgodicTheory.gammaK_eq_iInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.gammaK_eq_iInf

/-- info: 'ErgodicTheory.gammaK_upperSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.gammaK_upperSemicontinuous

/-- info: 'ErgodicTheory.topExponent_upperSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.topExponent_upperSemicontinuous

/-- info: 'ErgodicTheory.botExp_lowerSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.botExp_lowerSemicontinuous

/-- info: 'ErgodicTheory.botExp_eq_exponents_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.botExp_eq_exponents_last

-- Regularity regime 2: a.e.-convergence + uniform integrability (Vitali) continuity (item 4, deferred part).

/-- info: 'ErgodicTheory.ae_tendsto_logSprod_of_ae_tendsto_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_tendsto_logSprod_of_ae_tendsto_generator

/-- info: 'ErgodicTheory.tendsto_integral_logSprod_of_unifIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_integral_logSprod_of_unifIntegrable

/-- info: 'ErgodicTheory.tendsto_integral_logSprod_of_ae_unifIntegrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_integral_logSprod_of_ae_unifIntegrable

/-- info: 'ErgodicTheory.gammaK_upperSemicontinuous_of_ae_unifIntegrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.gammaK_upperSemicontinuous_of_ae_unifIntegrable

-- Singular / one-sided upper bounds without invertibility (item 9B).

/-- info: 'ErgodicTheory.limsup_logNorm_le_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.limsup_logNorm_le_top

/-- info: 'ErgodicTheory.limsup_logSprod_le_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.limsup_logSprod_le_top

-- Singular / one-sided: EReal lift of the log⁺ limits + the limsup = exponent sharpening (item 9B).

/-- info: 'ErgodicTheory.tendsto_top_posLogNorm_ereal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_top_posLogNorm_ereal

/-- info: 'ErgodicTheory.limsup_eq_liminf_posLogNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.limsup_eq_liminf_posLogNorm

/-- info: 'ErgodicTheory.limsup_logNorm_eq_top_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.limsup_logNorm_eq_top_of_pos

/-- info: 'ErgodicTheory.tendsto_top_posLogSprod_ereal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_top_posLogSprod_ereal

/-- info: 'ErgodicTheory.limsup_logSprod_eq_top_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.limsup_logSprod_eq_top_of_pos

-- Singular: the EReal-valued forward singular exponent γ_k (item 9B, invertibility-free).

/-- info: 'ErgodicTheory.measurable_forwardSingularExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_forwardSingularExponent

/-- info: 'ErgodicTheory.forwardSingularExponent_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardSingularExponent_nonneg

/-- info: 'ErgodicTheory.forwardSingularExponent_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardSingularExponent_zero

/-- info: 'ErgodicTheory.ae_forwardSingularExponent_eq_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_forwardSingularExponent_eq_coe

/-- info: 'ErgodicTheory.ae_forwardSingularExponent_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_forwardSingularExponent_lt_top

/-- info: 'ErgodicTheory.ae_forwardSingularExponent_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_forwardSingularExponent_ne_bot

-- Issue #6 (EReal exponent tie-in): the cumulative exponent γ_k is bounded by k · γ_1.

/-- info: 'ErgodicTheory.forwardPosLogNormLimsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardPosLogNormLimsup

/-- info: 'ErgodicTheory.forwardSingularExponent_le_natCast_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardSingularExponent_le_natCast_mul

-- Issue #6 (EReal exponent tie-in): top singular value = L2 opNorm, hence γ_1 = top exponent.

/-- info: 'ErgodicTheory.top_singularValue_eq_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.top_singularValue_eq_opNorm

/-- info: 'ErgodicTheory.sprod_one_eq_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sprod_one_eq_opNorm

/-- info: 'ErgodicTheory.forwardSingularExponent_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardSingularExponent_one_eq

/-- info: 'ErgodicTheory.ae_forwardSingularExponent_one_eq_topExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_forwardSingularExponent_one_eq_topExponent

-- Issue #6 (top cumulative exponent): the full singular product is |det|, hence γ_d via log⁺|det|.

/-- info: 'ErgodicTheory.forwardSingularExponent_full_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardSingularExponent_full_eq

-- Issue #6 (γ_d det-growth tie): a.e. γ_d = ↑Γ_d⁺, and the genuine log⁺|det| growth when positive.

/-- info: 'ErgodicTheory.ae_forwardSingularExponent_full_eq_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_forwardSingularExponent_full_eq_coe

/-- info: 'ErgodicTheory.ae_forwardSingularExponent_full_eq_det_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_forwardSingularExponent_full_eq_det_growth

-- Issue #6 (genuine-log EReal exponent): the kernel/volume-collapse −∞ stratum hook (Quas/Raghunathan).

/-- info: 'ErgodicTheory.measurable_forwardSingularExponentLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_forwardSingularExponentLog

/-- info: 'ErgodicTheory.forwardSingularExponentLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardSingularExponentLog_le

/-- info: 'ErgodicTheory.forwardSingularExponentLog_eq_bot_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.forwardSingularExponentLog_eq_bot_of_tendsto

-- Issue #6 (kernel stratum): the measurable −∞ volume-collapse set {x | γ_d^log = ⊥}.

/-- info: 'ErgodicTheory.singularKernelSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.singularKernelSet

/-- info: 'ErgodicTheory.measurableSet_singularKernelSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_singularKernelSet

/-- info: 'ErgodicTheory.measurableSet_finiteSingularExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_finiteSingularExponent

/-- info: 'ErgodicTheory.sprod_zero_imp_logTerm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sprod_zero_imp_logTerm_zero

/-- info: 'ErgodicTheory.singularKernelSet_compl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.singularKernelSet_compl_eq

-- Issue #6 (rank filtration data): the cocycle rank and its non-increasing rank-drop.

/-- info: 'ErgodicTheory.cocycleRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycleRank

/-- info: 'ErgodicTheory.cocycleRank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycleRank_le

/-- info: 'ErgodicTheory.cocycleRank_add_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycleRank_add_le_min

-- Issue #6 (filtration flag): the cocycle kernel submodule grows monotonically along the orbit.

/-- info: 'ErgodicTheory.cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycleKer

/-- info: 'ErgodicTheory.cocycleKer_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycleKer_le_add

/-- info: 'ErgodicTheory.finrank_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.finrank_cocycleKer

/-- info: 'ErgodicTheory.mem_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.mem_cocycleKer

-- Issue #6 (filtration flag bottom): the eventual (stabilized) cocycle kernel.

/-- info: 'ErgodicTheory.cocycleKer_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycleKer_mono

/-- info: 'ErgodicTheory.eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.eventualKer

/-- info: 'ErgodicTheory.finrank_eventualKer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.finrank_eventualKer_le

-- Issue #6 (filtration flag equivariance): A_x maps the eventual kernel forward along T.

/-- info: 'ErgodicTheory.mapsTo_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.mapsTo_cocycleKer

/-- info: 'ErgodicTheory.eventualKer_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.eventualKer_equivariant

-- Issue #6 (measurable flag): determinantal rank measurability — the full-rank stratum.

/-- info: 'Matrix.rank_eq_card_iff_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.rank_eq_card_iff_det_ne_zero

/-- info: 'ErgodicTheory.measurable_minor_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_minor_det

/-- info: 'ErgodicTheory.measurableSet_cocycleRank_eq_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_cocycleRank_eq_full

-- Issue #6 (rank measurability): minor-nonsingular ⟹ rank ≥ r (easy direction).

/-- info: 'Matrix.le_rank_of_submatrix_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.le_rank_of_submatrix_det_ne_zero

-- Issue #6 (measurable flag CLOSURE): rank = max nonsingular minor ⟹ the rank function is measurable.

/-- info: 'Matrix.le_rank_iff_exists_submatrix_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.le_rank_iff_exists_submatrix_det_ne_zero

/-- info: 'ErgodicTheory.measurableSet_le_cocycleRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_le_cocycleRank

/-- info: 'ErgodicTheory.measurable_cocycleRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_cocycleRank

-- Issue #6 (measurable dimension data — CLOSED): eventual rank + eventual-kernel dimension measurable.

/-- info: 'ErgodicTheory.measurable_eventualRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_eventualRank

/-- info: 'ErgodicTheory.eventualKerDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.eventualKerDim

/-- info: 'ErgodicTheory.measurable_eventualKerDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_eventualKerDim

-- Issue #6 (singular kernel graph): measurable graph of the eventual-kernel subspace family.

/-- info: 'ErgodicTheory.mem_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.mem_eventualKer

/-- info: 'ErgodicTheory.measurable_cocycleMulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_cocycleMulVec

/-- info: 'ErgodicTheory.measurableSet_graph_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_graph_cocycleKer

/-- info: 'ErgodicTheory.measurableSet_graph_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_graph_eventualKer

/-- info: 'ErgodicTheory.measurableSet_mem_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_mem_eventualKer

-- Issue #6 (singular kernel projector): Euclidean Gram spectral projector onto the cocycle kernel.

/-- info: 'ErgodicTheory.orthProjMatrix_cocycleKerEuclid_eq_spectralProjector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.orthProjMatrix_cocycleKerEuclid_eq_spectralProjector

/-- info: 'ErgodicTheory.measurable_orthProjMatrix_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_orthProjMatrix_cocycleKer

-- Issue #6 (singular eventual-kernel projector): limit projector onto the eventual kernel.

/-- info: 'ErgodicTheory.measurable_orthProjMatrix_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_orthProjMatrix_eventualKer

/-- info: 'ErgodicTheory.measurableSubspace_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSubspace_eventualKer

-- Issue #6 (sublevel slow-space stratum): the per-step, per-threshold Gram sublevel spectral
-- subspace (the threshold-`t` generalization of the kernel stratum), and its measurability.

/-- info: 'ErgodicTheory.cocycleSublevelEuclid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycleSublevelEuclid

/-- info: 'ErgodicTheory.measurableSubspace_cocycleSublevelEuclid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSubspace_cocycleSublevelEuclid

/-- info: 'ErgodicTheory.measurableSubspace_cocycleSublevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSubspace_cocycleSublevel

-- Two-sided splitting, Phase 0 (backward generator / cocycle infrastructure).

/-- info: 'ErgodicTheory.cocycle_backwardGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycle_backwardGen

-- Two-sided splitting, P1 (forward dimension formula) and P7 (intersection measurability).

/-- info: 'ErgodicTheory.ae_finrank_vslow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_finrank_vslow

/-- info: 'ErgodicTheory.MeasurableSubspace.inf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.MeasurableSubspace.inf

/-- info: 'ErgodicTheory.tendsto_pow_orthProj_inf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_pow_orthProj_inf

-- Two-sided splitting, P2 (strong one-sided export with the dimension formula).

/-- info: 'ErgodicTheory.oseledets_filtration_dims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_filtration_dims

-- Two-sided splitting, P3 (Kingman means identification — load-bearing new analytic lemma).

/-- info: 'ErgodicTheory.tendsto_kingman_ergodic_means' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_kingman_ergodic_means

-- Two-sided splitting, P6 (exponent reflection: backward spectrum = -forward reversed).

/-- info: 'ErgodicTheory.sum_mu0_eq_neg_sum_lam0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.sum_mu0_eq_neg_sum_lam0

/-- info: 'ErgodicTheory.reflect_of_counting_and_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.reflect_of_counting_and_sum

/-- info: 'ErgodicTheory.expEnum_eq_neg_rev_of_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.expEnum_eq_neg_rev_of_counting

-- Two-sided splitting, P4a (backward-orbit restricted envelope; analytic heart).

/-- info: 'ErgodicTheory.isSubadditiveCocycle_restLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.isSubadditiveCocycle_restLog

/-- info: 'ErgodicTheory.restLog_eq_on_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restLog_eq_on_good

/-- info: 'ErgodicTheory.restLog_backward_kingman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restLog_backward_kingman

-- Two-sided splitting, P4b (restricted Kingman constant = λᵢ; backward envelope).

/-- info: 'ErgodicTheory.restricted_const_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.restricted_const_eq

-- Two-sided splitting, P5 (transversality crux + counting bound).

/-- info: 'ErgodicTheory.ae_crux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_crux

/-- info: 'ErgodicTheory.ae_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_counting

/-- info: 'ErgodicTheory.inf_eq_bot_of_neg_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.inf_eq_bot_of_neg_sum

-- Two-sided splitting, P8 (the headline theorem: invariant direct-sum decomposition).

/-- info: 'ErgodicTheory.oseledets_splitting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_splitting

-- Continuous-flow MET, P0 (flow + cocycle reduction identity).

/-- info: 'ErgodicTheory.MeasurePreservingFlow.natCast_eq_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.MeasurePreservingFlow.natCast_eq_iterate

/-- info: 'ErgodicTheory.FlowCocycle.toCocycle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.FlowCocycle.toCocycle_eq

-- Continuous-flow MET, P2 (reduction to the discrete theorem at the time-1 map).

/-- info: 'ErgodicTheory.exists_isOseledetsFiltration_timeOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exists_isOseledetsFiltration_timeOne

-- Continuous-flow MET, P1 (between-times sandwich: integer-time → continuous-time growth).

/-- info: 'ErgodicTheory.ae_tendsto_flowError_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_tendsto_flowError_zero

/-- info: 'ErgodicTheory.tendsto_log_norm_atTop_of_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_log_norm_atTop_of_discrete

-- Continuous-flow MET, P3a (flow-equivariance machinery: fixed-time sublinearity, limsup shift).

/-- info: 'ErgodicTheory.ae_tendsto_logNorm_fixedTime_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_tendsto_logNorm_fixedTime_zero

/-- info: 'ErgodicTheory.glim_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.glim_shift

/-- info: 'ErgodicTheory.ae_flow_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_flow_equivariant

-- Continuous-flow MET, P3b (the headline theorem: flow-equivariant filtration, continuous-time growth).

/-- info: 'ErgodicTheory.oseledets_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_flow

-- Issue #1: constant-cocycle Lyapunov exponents (specialization to a constant generator `A ≡ M`).

/-- info: 'ErgodicTheory.cocycle_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cocycle_const

/-- info: 'ErgodicTheory.qpow_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.qpow_const

/-- info: 'ErgodicTheory.oseledetsLimit_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.oseledetsLimit_const

/--
info: 'ErgodicTheory.exp_exponents_const_eq_eigenvalues₀_absMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.exp_exponents_const_eq_eigenvalues₀_absMatrix

/-- info: 'ErgodicTheory.exponents_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exponents_const

-- Issue #2: derivative (tangent) cocycle of a differentiable self-map.

/-- info: 'ErgodicTheory.chainRule_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.chainRule_cocycle

/--
info: 'ErgodicTheory.oseledets_filtration_derivativeCocycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.oseledets_filtration_derivativeCocycle

-- Issue #3: concrete worked examples (doubling map, irrational rotation, Arnold cat-map matrix).

/-- info: 'ErgodicTheory.doublingMap_topExponent_eq_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.doublingMap_topExponent_eq_log_two

/-- info: 'ErgodicTheory.irrationalRotation_exponents_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.irrationalRotation_exponents_eq_zero

/-- info: 'ErgodicTheory.catMapMatrix_exponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.catMapMatrix_exponents

/-- info: 'ErgodicTheory.catMapMatrix_exponents_sum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.catMapMatrix_exponents_sum_eq_zero

-- Issue #4 (foundation): Shannon entropy of a finite measurable partition (toward KS entropy).

/-- info: 'ErgodicTheory.Entropy.entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_nonneg

/-- info: 'ErgodicTheory.Entropy.entropy_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_le_log_card

/--
info: 'ErgodicTheory.Entropy.MeasurePartition.sum_toReal_measure_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.MeasurePartition.sum_toReal_measure_eq_one

/-- info: 'ErgodicTheory.Entropy.entropy_le_log_card_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_le_log_card_partition

/-- info: 'ErgodicTheory.isAddFundamentalDomain_suspensionDomain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.isAddFundamentalDomain_suspensionDomain

/-- info: 'ErgodicTheory.suspension_exists_unique_act_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspension_exists_unique_act_mem

/-- info: 'ErgodicTheory.exists_unique_lt_of_strictMono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exists_unique_lt_of_strictMono

/-- info: 'ErgodicTheory.roofSum_add_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.roofSum_add_one

-- Issue #5 (measure layer): the suspension invariant-measure foundation.

/-- info: 'ErgodicTheory.measurePreserving_shear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurePreserving_shear

/-- info: 'ErgodicTheory.measurePreserving_suspensionGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurePreserving_suspensionGen

/-- info: 'ErgodicTheory.measure_suspensionDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measure_suspensionDomain

-- Issue #4 (entropy layer): T-invariance of partition entropy (toward the Fekete h(α,T) limit).

/-- info: 'ErgodicTheory.Entropy.entropy_comp_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_comp_preimage

-- Issue #4 (entropy subadditivity): H(α∨β) ≤ H(α)+H(β) — the gate to the Fekete h(α,T) limit.

/-- info: 'ErgodicTheory.Entropy.MeasurePartition.measure_eq_sum_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.MeasurePartition.measure_eq_sum_inter

/-- info: 'ErgodicTheory.Entropy.sum_negMulLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.sum_negMulLog_le

/-- info: 'ErgodicTheory.Entropy.entropy_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_join_le

-- Issue #4 (pullback partition): the T⁻¹ partition and the T-invariance of its entropy.

/-- info: 'ErgodicTheory.Entropy.entropy_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_pullback

-- Issue #4 (Fekete limit): the flat Fin-indexed KS join, its subadditive entropy sequence, and
-- the Kolmogorov–Sinai entropy as the Fekete limit.

/-- info: 'ErgodicTheory.Entropy.ksJoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksJoin

/-- info: 'ErgodicTheory.Entropy.ksEntropySeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropySeq

/-- info: 'ErgodicTheory.Entropy.ksEntropySeq_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropySeq_subadditive

/-- info: 'ErgodicTheory.Entropy.ksEntropyPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropyPartition

/-- info: 'ErgodicTheory.Entropy.tendsto_ksEntropySeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.tendsto_ksEntropySeq

-- Issue #4 (KS entropy bounds): h(α,T) ≥ 0 and h(α,T) ≤ H(α).

/-- info: 'ErgodicTheory.Entropy.ksEntropySeq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropySeq_one

/-- info: 'ErgodicTheory.Entropy.ksEntropySeq_le_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropySeq_le_nsmul

/-- info: 'ErgodicTheory.Entropy.ksEntropyPartition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropyPartition_nonneg

/-- info: 'ErgodicTheory.Entropy.ksEntropyPartition_le_entropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropyPartition_le_entropy

-- Issue #4 (KS entropy of the system): h(T) = ⨆_α h(α,T) as an EReal supremum.

/-- info: 'ErgodicTheory.Entropy.ksEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropy

/-- info: 'ErgodicTheory.Entropy.le_ksEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.le_ksEntropy

/-- info: 'ErgodicTheory.Entropy.ksEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropy_nonneg

-- Issue #4 (KS entropy property): the Fekete inf bound h(α,T) ≤ ksEntropySeq n / n.

/-- info: 'ErgodicTheory.Entropy.bddBelow_ksEntropySeq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.bddBelow_ksEntropySeq_div

/-- info: 'ErgodicTheory.Entropy.ksEntropyPartition_le_ksEntropySeq_div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropyPartition_le_ksEntropySeq_div

-- Issue #4 (dynamical subadditivity): h(α∨β,T) ≤ h(α,T) + h(β,T).

/-- info: 'ErgodicTheory.Entropy.joinPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.joinPartition

/-- info: 'ErgodicTheory.Entropy.ksEntropySeq_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropySeq_join_le

/-- info: 'ErgodicTheory.Entropy.ksEntropyPartition_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropyPartition_join_le

-- Issue #4 (entropy refinement-monotonicity): h(α,T) ≤ h(α∨β,T).

/-- info: 'ErgodicTheory.Entropy.entropy_le_entropy_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_le_entropy_join

/-- info: 'ErgodicTheory.Entropy.ksEntropyPartition_le_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.ksEntropyPartition_le_join

-- Issue #5 (quotient layer): the suspension space and its invariant probability measure.

/-- info: 'ErgodicTheory.measurable_suspensionMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_suspensionMk

/-- info: 'ErgodicTheory.suspensionMeasure₀_univ_eq_measure_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionMeasure₀_univ_eq_measure_box

/-- info: 'ErgodicTheory.suspensionMeasure_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionMeasure_univ

/-- info: 'ErgodicTheory.isProbabilityMeasure_suspensionMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.isProbabilityMeasure_suspensionMeasure

-- Issue #5 (flow layer): the suspension flow ζ_t (descent of the vertical translation) on Xᵗ.

/-- info: 'ErgodicTheory.measurePreserving_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurePreserving_translate

/-- info: 'ErgodicTheory.suspensionFlowMap_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionFlowMap_zero

/-- info: 'ErgodicTheory.suspensionFlowMap_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionFlowMap_add

/-- info: 'ErgodicTheory.measurable_suspensionFlowMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_suspensionFlowMap

-- Issue #5 (flow measure-preservation): the suspension flow is a measure-preserving flow.

/-- info: 'ErgodicTheory.measurePreserving_suspensionFlowMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurePreserving_suspensionFlowMap

/-- info: 'ErgodicTheory.suspensionFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionFlow

-- Issue #5 (transfer core): the return-time exponent log‖A⁽ⁿ⁾‖ / τ⁽ⁿ⁾ → λ / ∫τ.

/-- info: 'ErgodicTheory.tendsto_div_of_tendsto_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_div_of_tendsto_div

/-- info: 'ErgodicTheory.roofSum_natCast_eq_birkhoffSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.roofSum_natCast_eq_birkhoffSum

/-- info: 'ErgodicTheory.tendsto_roofAverage_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_roofAverage_ae

/-- info: 'ErgodicTheory.integral_roof_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.integral_roof_pos

/-- info: 'ErgodicTheory.returnTime_tendsto_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.returnTime_tendsto_exponent

-- Issue #5 (top-exponent transfer): the MET top exponent transfers as λ_top / ∫τ.

/-- info: 'ErgodicTheory.IsOseledetsFiltration.returnTime_tendsto_topExponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.returnTime_tendsto_topExponent

-- Issue #5 (flow cocycle core): the return-indexed suspension cocycle and its multiplicativity.

/-- info: 'ErgodicTheory.suspensionCocycleReturn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionCocycleReturn_add

/-- info: 'ErgodicTheory.measurable_suspensionCocycleReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_suspensionCocycleReturn

/-- info: 'ErgodicTheory.returnTime_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.returnTime_add

/-- info: 'ErgodicTheory.suspensionCocycleReturn_returnTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionCocycleReturn_returnTime

-- Issue #5 (special-flow lap counter): return times diverge, and the first-passage lap count N(t,x).

/-- info: 'ErgodicTheory.returnTime_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.returnTime_strictMono

/-- info: 'ErgodicTheory.returnTime_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.returnTime_tendsto_atTop

/-- info: 'ErgodicTheory.lapCount_returnTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_returnTime_le

/-- info: 'ErgodicTheory.lapCount_lt_returnTime_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_lt_returnTime_succ

-- Issue #5 (flow cocycle on the section): Ψ_t = A^(lapCount t) and the return identity.

/-- info: 'ErgodicTheory.flowCocycleSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.flowCocycleSection

/-- info: 'ErgodicTheory.lapCount_returnTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_returnTime_eq

/-- info: 'ErgodicTheory.flowCocycleSection_returnTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.flowCocycleSection_returnTime

/-- info: 'ErgodicTheory.flowCocycleSection_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.flowCocycleSection_zero

-- Issue #5 (cover extension): lapCount monotone + the off-section lap-count additivity.

/-- info: 'ErgodicTheory.lapCount_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_mono

/-- info: 'ErgodicTheory.lapCount_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_unique

/-- info: 'ErgodicTheory.lapCount_returnTime_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_returnTime_add

-- Issue #5 (cover flow cocycle): the X×ℝ cover cocycle + its section return-boundary identity.

/-- info: 'ErgodicTheory.coverCocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle

/-- info: 'ErgodicTheory.coverCocycle_section_returnTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_section_returnTime

-- Issue #5 (descent): the one-lap height reduction and its operator-norm bound.

/-- info: 'ErgodicTheory.coverCocycle_one_lap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_one_lap

-- Issue #5 (flow exponent bridge): cover-cocycle norm = base norm at return times.

/-- info: 'ErgodicTheory.coverCocycle_returnTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_returnTime_eq

/-- info: 'ErgodicTheory.coverCocycle_returnTime_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_returnTime_opNorm_le

-- Issue #5 (HEADLINE): the special-flow Lyapunov exponent along returns = λ_base / ∫τ.

/-- info: 'ErgodicTheory.coverCocycle_returnTime_tendsto_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_returnTime_tendsto_exponent

/-- info: 'ErgodicTheory.IsOseledetsFiltration.coverCocycle_returnTime_tendsto_topExponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.IsOseledetsFiltration.coverCocycle_returnTime_tendsto_topExponent

-- Issue #5 (special-flow structure): the flow cocycle is constant = A^(n) between returns.

/-- info: 'ErgodicTheory.coverCocycle_const_between_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_const_between_returns

-- Issue #5 (full-time reduction): flow-cocycle norm = base norm at the lap count + the sandwich.

/-- info: 'ErgodicTheory.coverCocycle_norm_eq_lapCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_norm_eq_lapCount

/-- info: 'ErgodicTheory.log_coverCocycle_div_eq_lapCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.log_coverCocycle_div_eq_lapCount

-- Issue #5 (HEADLINE closure): full-time special-flow exponent = λ_base/∫τ under a bounded roof.

/-- info: 'ErgodicTheory.lapCount_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_tendsto_atTop

/-- info: 'ErgodicTheory.lapCount_returnTime_div_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lapCount_returnTime_div_tendsto_one

/-- info: 'ErgodicTheory.coverCocycle_tendsto_exponent_of_bddRoof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_tendsto_exponent_of_bddRoof

-- Issue #5 (suspension bridge): the cross-section embedding + gluing + section-image exponent.

/-- info: 'ErgodicTheory.suspensionMk_roof_eq_section_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionMk_roof_eq_section_base

/-- info: 'ErgodicTheory.measurable_suspensionSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_suspensionSection

/-- info: 'ErgodicTheory.coverCocycle_tendsto_exponent_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_tendsto_exponent_section

-- Issue #5 (suspension disintegration): base-a.e. → μ̂-a.e. transfer to the suspension measure.

/-- info: 'ErgodicTheory.suspensionMeasure_ae_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionMeasure_ae_iff

/-- info: 'ErgodicTheory.ae_suspensionMeasure_of_ae_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_of_ae_restrict

/-- info: 'ErgodicTheory.ae_restrict_suspensionDomain_of_ae_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_restrict_suspensionDomain_of_ae_base

/-- info: 'ErgodicTheory.ae_suspensionMeasure_of_ae_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_of_ae_base

/-- info: 'ErgodicTheory.ae_suspensionMeasure_section_exponent_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_section_exponent_set

-- Issue #5 (suspension growth-rate descent): orbit re-basing + two-sided bounded op-norm discrepancy.

/-- info: 'ErgodicTheory.coverCocycle_suspensionAct_rebasing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_suspensionAct_rebasing

/-- info: 'ErgodicTheory.coverCocycle_suspensionAct_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_suspensionAct_opNorm_le

/-- info: 'ErgodicTheory.coverCocycle_suspensionAct_rebasing_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_suspensionAct_rebasing_inv

/-- info: 'ErgodicTheory.coverCocycle_suspensionAct_opNorm_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_suspensionAct_opNorm_ge

-- Issue #5 (exponent descent): orbit re-basing has bounded log-norm discrepancy ⟹ same exponent.

/-- info: 'ErgodicTheory.norm_pos_of_isUnit_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.norm_pos_of_isUnit_det

/-- info: 'ErgodicTheory.coverCocycle_suspensionAct_log_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_suspensionAct_log_discrepancy

/-- info: 'ErgodicTheory.coverCocycle_suspensionAct_tendsto_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coverCocycle_suspensionAct_tendsto_exponent

-- Issue #5 (flow exponent on the space): the well-defined suspension-space flow exponent predicate.

/-- info: 'ErgodicTheory.HasFlowExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.HasFlowExponent

/-- info: 'ErgodicTheory.tendsto_exponent_iff_of_suspensionAct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_exponent_iff_of_suspensionAct

/-- info: 'ErgodicTheory.hasFlowExponent_of_suspensionAct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.hasFlowExponent_of_suspensionAct

-- Issue #5 (flow exponent value): the section flow exponent + the μ̂-a.e. flow-exponent statement.

/-- info: 'ErgodicTheory.tendsto_coverCocycle_exponent_of_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_coverCocycle_exponent_of_section

/-- info: 'ErgodicTheory.ae_suspensionMeasure_hasFlowExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_hasFlowExponent

-- Issue #4 (Margulis–Ruelle inequality): h(T) ≤ ∑ λᵢ⁺ reduced to the geometric atom-counting bound.

/-- info: 'ErgodicTheory.margulisRuelle_le_sumPosExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.margulisRuelle_le_sumPosExp

-- Issue #5 (quotient-image measurability): discharge the `hmeas` quotient-image hypothesis.

/-- info: 'ErgodicTheory.suspensionActEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionActEquiv

/-- info: 'ErgodicTheory.suspensionActEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspensionActEquiv_apply

/-- info: 'ErgodicTheory.measurableSet_suspensionAct_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_suspensionAct_image

/-- info: 'ErgodicTheory.preimage_image_suspensionMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.preimage_image_suspensionMk

/-- info: 'ErgodicTheory.measurableSet_suspensionMk_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_suspensionMk_image

/-- info: 'ErgodicTheory.measurableSet_suspensionMk_exponent_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_suspensionMk_exponent_image

-- Issue #5 (unconditional space-level exponent): `hmeas` discharged + tied to the genuine flow.

/-- info: 'ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_unconditional

/-- info: 'ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_flowOrbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_flowOrbit

-- Issue #5 (hPmeas discharged): cover-cocycle convergence-set measurability ⇒ fully unconditional
-- space-level special-flow exponent (only `Measurable A` assumed, no convergence-set hypothesis).

/-- info: 'ErgodicTheory.measurableSet_coverCocycle_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSet_coverCocycle_exponent

/-- info: 'ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_of_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_of_measurable

/-- info: 'ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_flowOrbit_of_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_flowOrbit_of_measurable

-- Issue #6 (det-free singular infra): subspace-convergence tool + per-direction EReal exponent.

/-- info: 'ErgodicTheory.cauchySeq_of_summable_subspaceDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.cauchySeq_of_summable_subspaceDist

/-- info: 'ErgodicTheory.exists_tendsto_orthProjMatrix_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exists_tendsto_orthProjMatrix_of_summable

/-- info: 'ErgodicTheory.measurable_singularDirExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_singularDirExponent

/-- info: 'ErgodicTheory.ae_singularDirExponent_eq_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_singularDirExponent_eq_coe

-- Issue #4 (honest sharpening): positive-part singular-value product identity + minimal atom-count
-- restatement of the Margulis–Ruelle reduction. The geometric `hgeo`/`hcount` input stays an explicit
-- open hypothesis (smooth-ergodic-theory wall); nothing axiomatized.

/-- info: 'ErgodicTheory.Entropy.sum_posLog_singularValues_toEuclideanLin_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.sum_posLog_singularValues_toEuclideanLin_eq

-- Issue #6 (det-free genuine singular Lyapunov spectrum): the −∞-aware per-direction exponent is
-- deterministically antitone + measurable + a.e. finite; cut-threshold ladder for the slow-space flag.

/-- info: 'ErgodicTheory.singularSpectralValue_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.singularSpectralValue_antitone

/-- info: 'ErgodicTheory.measurable_singularSpectralValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_singularSpectralValue

/-- info: 'ErgodicTheory.ae_singularSpectralValue_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_singularSpectralValue_lt_top

/-- info: 'ErgodicTheory.exists_cutThresholds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.exists_cutThresholds

-- Issue #6 (genuine singular spectrum is a.e. CONSTANT, det-free) + the missing Horn singular-value
-- inequality σ_k(g∘f) ≤ σ_k(g)·‖f‖ built en route.

/-- info: 'ErgodicTheory.singularValues_comp_le_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.singularValues_comp_le_opNorm

/-- info: 'ErgodicTheory.singularSpectralValue_invariant_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.singularSpectralValue_invariant_ae

/-- info: 'ErgodicTheory.ae_singularSpectralValue_eq_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_singularSpectralValue_eq_const

-- Issue #6 (singular slow-space step + structural reduction of V_j convergence to one summability input).

/-- info: 'ErgodicTheory.measurableSubspace_vSlowSingularStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSubspace_vSlowSingularStep

/-- info: 'ErgodicTheory.vSlowSingularStep_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.vSlowSingularStep_antitone

/-- info: 'ErgodicTheory.tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector

-- Issue #6 (det-free band route): the V_j band-increment bound with the inverse isolated to a single
-- per-step coefficient hypothesis; the complement reduction band-convergence ⇒ slow-space convergence.

/-- info: 'ErgodicTheory.numerator_div_gap_le_detfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.numerator_div_gap_le_detfree

/-- info: 'ErgodicTheory.tendsto_vSlowSingularStep_of_bandProjector_detfree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_vSlowSingularStep_of_bandProjector_detfree

-- Issue #6 (tempered-class V_j + the wall identity): unconditional soft-analysis core (any summable band
-- increment ⇒ V_j converges), the tempered-non-degeneracy V_j, and the proof the increment IS an aperture.

/-- info: 'ErgodicTheory.tendsto_vSlowSingularStep_of_summable_increment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_vSlowSingularStep_of_summable_increment

/-- info: 'ErgodicTheory.tendsto_vSlowSingularStep_of_tempered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_vSlowSingularStep_of_tempered

/-- info: 'ErgodicTheory.bandProjector_increment_eq_aperture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.bandProjector_increment_eq_aperture

-- Issue #6 (algebraic forward filtration): the lambdaBar sublevel as a submodule, antitone + equivariant
-- (floored growth + the det-free HasFiniteTopGrowth finiteness hypothesis).

/-- info: 'ErgodicTheory.lambdaBarSublevel_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lambdaBarSublevel_antitone

/-- info: 'ErgodicTheory.lambdaBarSublevel_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lambdaBarSublevel_equivariant

-- Issue #6 (measurability reduction): {v : lambdaBar ≤ c} is a MeasurableSubspace given the projector
-- convergence — which provably reduces to the same band/aperture convergence (the pinned inverse wall).

/-- info: 'ErgodicTheory.measurableSubspace_of_tendsto_orthProjMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSubspace_of_tendsto_orthProjMatrix

/-- info: 'ErgodicTheory.measurableSubspace_lambdaSublevel_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurableSubspace_lambdaSublevel_of_tendsto

-- Issue #6 (migrated headline): the a.e.-measurable forward Lyapunov projector of the singular
-- MET, from the measurable graph via universal measurability of analytic sets (Lusin/Choquet).

/-- info: 'ErgodicTheory.aemeasurable_orthProjMatrix_lambdaSublevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.aemeasurable_orthProjMatrix_lambdaSublevel

-- Issue #6 upstream candidate: every analytic set in a standard Borel space is universally
-- measurable (NullMeasurableSet for every s-finite measure), via Choquet capacitability.

/-- info: 'MeasureTheory.AnalyticSet.nullMeasurableSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MeasureTheory.AnalyticSet.nullMeasurableSet

-- Issue #4 (migrated headline): the sharp Margulis–Ruelle inequality h(T) ≤ ∑ λᵢ⁺ for a smooth
-- ergodic self-map of Euclidean space (modulo the honest non-compactness atom-count input).

/-- info: 'ErgodicTheory.margulisRuelle_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.margulisRuelle_sharp

-- Issue #4 upstream candidate: Mañé's Lemma 12.5, the covering number bounded by Haar volume of
-- the closed thickening on Euclidean space.

/-- info: 'Metric.coveringNumber_le_addHaar_div_of_addHaar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Metric.coveringNumber_le_addHaar_div_of_addHaar_le

-- Issue #4: the sharp anisotropic one-step covering count of a linear image of a ball, by the
-- positive-part singular-value product (the geometric heart of the sharp track).

/-- info: 'ErgodicTheory.coveringCount_image_ball_le_volProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.coveringCount_image_ball_le_volProd

-- Issue #4: the orbit growth rate (1/n) log (volProd …) → ∑ λᵢ⁺, a.e., driving the count.

/-- info: 'ErgodicTheory.tendsto_log_volProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.tendsto_log_volProd

-- MET enhancements campaign: #1-#6 closures

/-- info: 'ErgodicTheory.topExponent_constantCocycle_eq_log_spectralRadius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.topExponent_constantCocycle_eq_log_spectralRadius

/-- info: 'ErgodicTheory.doublingMap_sumPosExp_eq_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.doublingMap_sumPosExp_eq_log_two

/-- info: 'ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.doublingMap_ksEntropyPartition_le_sumPosExp

/--
info: 'ErgodicTheory.singular_perDirection_exponent_eq_lambda_of_mem_stratum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.singular_perDirection_exponent_eq_lambda_of_mem_stratum

/-- info: 'ErgodicTheory.lambdaBar_eq_of_mem_stratum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.lambdaBar_eq_of_mem_stratum

/-- info: 'ErgodicTheory.log_le_liminf_log_cocycle_apply_detfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.log_le_liminf_log_cocycle_apply_detfree

/-- info: 'ErgodicTheory.CatMapToral.ergodic_catTorus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.CatMapToral.ergodic_catTorus

/-- info: 'ErgodicTheory.CatMapToral.measurePreserving_catTorus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.CatMapToral.measurePreserving_catTorus

/-- info: 'ErgodicTheory.CatMapToral.orbit_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.CatMapToral.orbit_infinite

/-- info: 'ErgodicTheory.CatMapToral.catTorus_constCocycle_topExponent_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.CatMapToral.catTorus_constCocycle_topExponent_pos

/-- info: 'ErgodicTheory.CatMapToral.derivativeCocycle_catLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.CatMapToral.derivativeCocycle_catLift

/--
info: 'ErgodicTheory.CatMapToral.catLift_derivativeCocycle_topExponent_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.CatMapToral.catLift_derivativeCocycle_topExponent_pos

/--
info: 'ErgodicTheory.CatMapToral.catTorus_ksEntropyPartition_le_logLambda' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.CatMapToral.catTorus_ksEntropyPartition_le_logLambda

/-- info: 'ErgodicTheory.suspension_perExponent_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspension_perExponent_scaling

/-- info: 'ErgodicTheory.suspension_gammaK_flow_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.suspension_gammaK_flow_scaling

/-- info: 'ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_extGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.ae_suspensionMeasure_hasFlowExponent_extGen

/-- info: 'ErgodicTheory.measurable_extGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.measurable_extGen

/-- info: 'ErgodicTheory.Examples.Rokhlin.rokhlin_equality_doublingMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Examples.Rokhlin.rokhlin_equality_doublingMap

/--
info: 'ErgodicTheory.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two

/-- info: 'ErgodicTheory.Examples.Rokhlin.volume_binJoinCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Examples.Rokhlin.volume_binJoinCell

-- Conditional / relative entropy + Abramov–Rokhlin (issue #13).

/-- info: 'ErgodicTheory.Entropy.condEntropy_join_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.condEntropy_join_eq

/-- info: 'ErgodicTheory.Entropy.condEntropy_comap_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.condEntropy_comap_pullback

/-- info: 'ErgodicTheory.Entropy.condEntropy_mono_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.condEntropy_mono_of_le

/-- info: 'ErgodicTheory.Entropy.condKsEntropy_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.condKsEntropy_bot

/-- info: 'ErgodicTheory.Entropy.factor_relative_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.factor_relative_eq

/-- info: 'ErgodicTheory.Entropy.abramov_rokhlin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.abramov_rokhlin

-- Issue #13 §5b: the partition-level Abramov–Rokhlin skeleton (B6a reduced to the W3 limit).

/-- info: 'ErgodicTheory.Entropy.entropy_joinCells_of_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.entropy_joinCells_of_refines

/-- info: 'ErgodicTheory.Entropy.abramovRokhlin_partition_of_W3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.abramovRokhlin_partition_of_W3

/-- info: 'ErgodicTheory.Entropy.abramov_rokhlin_of_W3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.abramov_rokhlin_of_W3

/-- info: 'ErgodicTheory.Entropy.condEntropy_tendsto_iSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.condEntropy_tendsto_iSup

/-- info: 'ErgodicTheory.Entropy.factor_iSup_comap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.factor_iSup_comap_eq

/--
info: 'ErgodicTheory.Entropy.condEntropyGivenPartition_eq_condEntropy_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.condEntropyGivenPartition_eq_condEntropy_generated

-- Issue #13: W3 DISCHARGED — the moving-index Cesàro/martingale limit (blocking + the fixed-partition
-- Lévy theorem) and the resulting UNCONDITIONAL Abramov–Rokhlin addition formula under a base generator.

/-- info: 'ErgodicTheory.Entropy.tendsto_condEntropy_genJoin_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.tendsto_condEntropy_genJoin_div

/-- info: 'ErgodicTheory.Entropy.tendsto_condCellSeq_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.tendsto_condCellSeq_div

/-- info: 'ErgodicTheory.Entropy.abramovRokhlin_partition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.abramovRokhlin_partition

/-- info: 'ErgodicTheory.Entropy.abramov_rokhlin_of_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Entropy.abramov_rokhlin_of_generator

-- Issue #15: Krieger's finite generator theorem. The full M0–M3 infrastructure is sorry-free and
-- axiom-clean: two-sided generation (M0), the Rokhlin tower (M1), the information function + the
-- martingale-free name-count engine (M2), and the σ-algebra recovery core + the faithful headline
-- `krieger_finite_generator` modulo the supplied finite coding `KriegerCodingData` (M3). The one
-- residual to make the headline unconditional — constructing `KriegerCodingData` (a two-sided SMB +
-- a finite-entropy countable generator + a symbolic block-code) — is a genuine multi-layer wall,
-- not in Mathlib; it is NOT discharged here and carries no `sorry` (it is a hypothesis).

/-- info: 'ErgodicTheory.Krieger.isGeneratingOneSided_le_twoSided' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.isGeneratingOneSided_le_twoSided

/-- info: 'ErgodicTheory.Krieger.rokhlin_tower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.rokhlin_tower

/-- info: 'ErgodicTheory.Krieger.rokhlin_tower_aux' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.rokhlin_tower_aux

/-- info: 'ErgodicTheory.Krieger.integral_infoFun_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.integral_infoFun_eq

/-- info: 'ErgodicTheory.Krieger.ae_forall_eventually_div_infoFun_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.ae_forall_eventually_div_infoFun_le

/-- info: 'ErgodicTheory.Krieger.comap_twoSidedSat_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.comap_twoSidedSat_le

/-- info: 'ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0.of_codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0.of_codes

/-- info: 'ErgodicTheory.Krieger.isGeneratingTwoSidedMod0_of_literal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.isGeneratingTwoSidedMod0_of_literal

/-- info: 'ErgodicTheory.Krieger.krieger_finite_generator_of_coding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.krieger_finite_generator_of_coding

/-- info: 'ErgodicTheory.Krieger.krieger_finite_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.krieger_finite_generator

-- Issue #15 (unconditional drive, Wave 0): countable-partition Shannon entropy + the
-- finite-static-entropy criterion (Downarowicz Fact 1.1.4), infrastructure for the
-- finite-entropy countable generator (sub-problem A).

/-- info: 'ErgodicTheory.Krieger.cHμ_summable_of_summable_index_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErgodicTheory.Krieger.cHμ_summable_of_summable_index_mul

-- Issue #15 (unconditional drive, Wave 0): SMB infrastructure — the uniform partition-function
-- bound and the crude-rate name-count limsup (Birkhoff-free, Markov + Borel–Cantelli). The sharp
-- rate (1/n)·infoFun → h is the residual (Chung L¹ maximal domination + the lower-half assembly).

/-- info: 'ErgodicTheory.Krieger.lintegral_exp_infoFun_sub_log_card_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.lintegral_exp_infoFun_sub_log_card_le_one

/-- info: 'ErgodicTheory.Krieger.ae_limsup_div_infoFun_le_log_card' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ae_limsup_div_infoFun_le_log_card

-- Issue #15 (unconditional drive, Wave 1): the finite-entropy countable two-sided generator
-- (Keane–Serafin / Downarowicz Thm 4.2.3 first half) — the structural reduction is unconditional;
-- the dynamical KeaneSerafinData (per-step SMB + Rokhlin recovery) is the isolated residual.

/-- info: 'ErgodicTheory.Krieger.exists_countable_twoSided_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.exists_countable_twoSided_generator

/-- info: 'ErgodicTheory.Krieger.exists_countable_twoSided_generator_of_keaneSerafinData' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.exists_countable_twoSided_generator_of_keaneSerafinData

-- Issue #15 (unconditional drive, Wave 1): the cross-layer coding bridge — a *countable* mod-0
-- two-sided generator (Generator layer) coded by a *Fintype* `Fin k` partition (Coding layer). The
-- recovery `IsGeneratingTwoSidedMod0c.of_codesc` is what the refactored `KriegerCodingData`/headline
-- now consume; `codesTwoSidedMod0c_of_aeRecovery` is the sufficient condition the C3 wave discharges.

/-- info: 'ErgodicTheory.Krieger.ctwoSidedSat_mono_of_codesc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ctwoSidedSat_mono_of_codesc

/-- info: 'ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0c.of_codesc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.IsGeneratingTwoSidedMod0c.of_codesc

/-- info: 'ErgodicTheory.Krieger.CodesTwoSidedMod0c.isGeneratingTwoSidedMod0' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.CodesTwoSidedMod0c.isGeneratingTwoSidedMod0

/-- info: 'ErgodicTheory.Krieger.codesTwoSidedMod0c_of_aeRecovery' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.codesTwoSidedMod0c_of_aeRecovery

-- Issue #15 (unconditional drive, Wave 1): the sentinel/comma-free prefix-code counting (C1) —
-- the self-contained combinatorial core of the symbolic coding, fully closed (no residual).

/-- info: 'ErgodicTheory.Krieger.exists_sentinelEncoding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.exists_sentinelEncoding

/-- info: 'ErgodicTheory.Krieger.sentinelEncodeList_injective' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.sentinelEncodeList_injective

/-- info: 'ErgodicTheory.Krieger.pow_le_pow_iff_log' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.pow_le_pow_iff_log

-- Issue #15 (unconditional drive): sharp SMB integral-level identity h = H(P | strict future)
-- via Breiman telescoping + the #13 Lévy theorem (unconditional; pointwise residual = R5).

/-- info: 'ErgodicTheory.Krieger.ksEntropySeq_eq_sum_condEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ksEntropySeq_eq_sum_condEntropy

/-- info: 'ErgodicTheory.Krieger.ksEntropyPartition_eq_condEntropy_iSup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ksEntropyPartition_eq_condEntropy_iSup

-- Issue #15 (unconditional drive): the symbolic code-map measurable backbone — the itinerary map
-- x ↦ (n ↦ code(eⁿx)) is twoSidedSat-measurable (automatic, no new symbolic-dynamics infra), so a
-- measurable decoder with a.e. recovery discharges the mod-0 coding hypothesis (measurable_itin).

/-- info: 'ErgodicTheory.Krieger.measurable_itin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.measurable_itin

-- Issue #15 (unconditional drive): asymptotic-equipartition name count (C2) — the pigeonhole +
-- covering content are unconditional; the C3-facing cover ≤ exp(N(h+ε)) names ≥ 1-ε is modulo the
-- in-measure upper-SMB hypothesis UpperSMBInMeasure (strictly lighter than the pointwise R5).

/-- info: 'ErgodicTheory.Krieger.card_goodNames_le_exp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.card_goodNames_le_exp

/-- info: 'ErgodicTheory.Krieger.measure_iUnion_goodNames_ge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.measure_iUnion_goodNames_ge

/-- info: 'ErgodicTheory.Krieger.exists_cover_names_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.exists_cover_names_card_le

-- Issue #15 (unconditional drive): Keane–Serafin generator construction (sub-problem A) — the
-- structural reduction to a per-level KeaneSerafinLevels bundle is unconditional; the dynamical
-- per-step lemma is blocked by the SAME in-probability SMB equipartition as the SMBSharp R5 leaf.

/-- info: 'ErgodicTheory.Krieger.exists_countable_twoSided_generator_of_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.exists_countable_twoSided_generator_of_step

/-- info: 'ErgodicTheory.Krieger.exists_countable_twoSided_generator_of_levels' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.exists_countable_twoSided_generator_of_levels

-- Issue #15 (unconditional drive): the refining-tower recovery (sub-problem B). The two-sided
-- recurrence tiling + Borel–Cantelli scaffolding are unconditional + sorry-free (the feared crux
-- was cheap via Mathlib's Conservative API); the residual is the existence of a ColumnCodeData
-- (the code symbol + the measurable bi-infinite sentinel parser — symbolic-dynamics infra Mathlib lacks).

/-- info: 'ErgodicTheory.Krieger.twoSided_recurrence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.twoSided_recurrence

/-- info: 'ErgodicTheory.Krieger.codesTwoSidedMod0c_of_columnCode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.codesTwoSidedMod0c_of_columnCode

/-- info: 'ErgodicTheory.Krieger.ColumnCodeData.codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ColumnCodeData.codes

-- Issue #15 (unconditional drive): pointwise SMB R3/R4 closed + R5 reduced. The conditional
-- information function, the keystone ∫ g_𝒜 = H(P|𝒜), and the R4 Birkhoff main term are proved
-- unconditionally; the full pointwise (1/n)infoFun → h is reduced to two named analytic leaves
-- (the Chung Doob stopping-time tail + the Maker dominated-Cesàro), carried as hypotheses.

/-- info: 'ErgodicTheory.Krieger.integral_condInfoFun_eq_condEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.integral_condInfoFun_eq_condEntropy

/-- info: 'ErgodicTheory.Krieger.ae_tendsto_birkhoffAverage_condInfoFun_futureSigma' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ae_tendsto_birkhoffAverage_condInfoFun_futureSigma

/-- info: 'ErgodicTheory.Krieger.lintegral_condInfoMaxFun_le_of_layer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.lintegral_condInfoMaxFun_le_of_layer

/-- info: 'ErgodicTheory.Krieger.ae_tendsto_div_infoFun_of_tail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ae_tendsto_div_infoFun_of_tail

-- Issue #15 (unconditional drive): the measurable bi-infinite sentinel parser — the gap diagnosed
-- as "multi-week, no Mathlib analogue" is CLOSED (measurable_find of a totalized forward search +
-- measurable_to_countable'). The decoder is constructed, not hypothesized; sub-problem B's residual
-- reduces to the (moderate, no-Mathlib-gap) tower-column code symbol + a.e. recovery.

/-- info: 'ErgodicTheory.Krieger.measurable_fwdSentinel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.measurable_fwdSentinel

-- Issue #15 (unconditional drive): the OFFSET-AWARE tower code. Adversarial catch: a bare
-- position-blind sentinelParse gives the same label at x and e·x (parse_event_cannot_separate), so a
-- naive sentinel-column recovery field is unsatisfiable. Fixed with blockOffset / sentinelParseAt
-- (offset increases by 1 under the shift ⟹ can separate floors) + the floor-address map.

/-- info: 'ErgodicTheory.Krieger.parse_event_cannot_separate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.parse_event_cannot_separate

/-- info: 'ErgodicTheory.Krieger.measurable_sentinelParseAt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.measurable_sentinelParseAt

/-- info: 'ErgodicTheory.Krieger.measurable_floorAddr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.measurable_floorAddr

/-- info: 'ErgodicTheory.Krieger.SentinelColumnCodeAt.codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.SentinelColumnCodeAt.codes

-- Issue #15 (unconditional drive): BOTH analytic leaves of the pointwise SMB closed — the Chung
-- Doob stopping-time tail (g* ∈ L¹) and the Maker/Breiman dominated-Cesàro. The pointwise SMB
-- ae_tendsto_div_infoFun + the in-measure tendsto_measure_div_infoFun_gt (⟹ UpperSMBInMeasure) are
-- unconditional given only the R2 Breiman telescoping (mechanical measure-algebra, not analytic).

/-- info: 'ErgodicTheory.Krieger.chungTail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.chungTail

/-- info: 'ErgodicTheory.Krieger.lintegral_condInfoMaxFun_lt_top' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.lintegral_condInfoMaxFun_lt_top

/-- info: 'ErgodicTheory.Krieger.makerTail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.makerTail

/-- info: 'ErgodicTheory.Krieger.ae_tendsto_div_infoFun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ae_tendsto_div_infoFun

/-- info: 'ErgodicTheory.Krieger.tendsto_measure_div_infoFun_gt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.tendsto_measure_div_infoFun_gt

-- Issue #15 (unconditional drive): the offset/floor alignment — the heart of the tower code. On a
-- column-tiled stream the offset-aware parser reads dec(column-block)(floorAddr), so sub-problem B's
-- entire symbolic side reduces (sorry-free) to ONE field: ColumnLayoutData.recovers_tiled = the a.e.
-- two-sided column tiling of one fixed interleaving code (the refining-tower / Borel–Cantelli limit;
-- a single tower closes only mod-ε, not mod-0 — adversarially caught).

/-- info: 'ErgodicTheory.Krieger.sentinelParseAt_column' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.sentinelParseAt_column

/-- info: 'ErgodicTheory.Krieger.sentinelParseAt_itin_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.sentinelParseAt_itin_eq

/-- info: 'ErgodicTheory.Krieger.ColumnLayoutData.codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ColumnLayoutData.codes

-- Issue #15 (unconditional drive): the analytic side CLOSED. Adversarial catch: the literal hbreiman
-- is off-by-one for infoFun (conditions on 𝒞₀..𝒞ₙ₋₁, not 𝒞₁..𝒞ₙ); resolved via the true edge-form
-- telescoping + orbital decay. ae_tendsto_div_infoFun_self = the UNCONDITIONAL pointwise SMB; and
-- UpperSMBInMeasure is now a THEOREM (upperSMBInMeasure_of_ergodic), discharging C2's hypothesis.

/-- info: 'ErgodicTheory.Krieger.ae_tendsto_div_infoFun_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.ae_tendsto_div_infoFun_self

/-- info: 'ErgodicTheory.Krieger.upperSMBInMeasure_of_ergodic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.upperSMBInMeasure_of_ergodic

-- Issue #15 (unconditional drive): the refining-tower interleaving core. The Borel–Cantelli m→∞
-- reduction + the parser/encode bridge are unconditional + sorry-free, reducing sub-problem B to ONE
-- bundle RefiningTowerCode whose only genuine field is stage_tiled (the escape-symbol multi-stage
-- construction repairing the hprev bottom-block defect — adversarially caught, 5th of the campaign).

/-- info: 'ErgodicTheory.Krieger.aeParse_of_aeStageTiled' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.aeParse_of_aeStageTiled

/-- info: 'ErgodicTheory.Krieger.sentinelParseAt_itin_of_encode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.sentinelParseAt_itin_of_encode

/-- info: 'ErgodicTheory.Krieger.RefiningTowerCode.codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.RefiningTowerCode.codes

-- Issue #15 (unconditional drive): the escape-symbol StageCode interface (the W7 hprev repair). The
-- StageCode bracketing (s at every column predecessor) discharges hprev ⟹ per-stage alignment
-- (StageCode.tiled), and a sequence of StageCodes assembles to CodesTwoSidedMod0c
-- (RefiningTowerCode.codes_ofStages). The residual is the measurable interleaving code spelling
-- sentinelEncode + bracketing (StageCode's spells/brackets fields).

/-- info: 'ErgodicTheory.Krieger.StageCode.tiled' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.StageCode.tiled

/-- info: 'ErgodicTheory.Krieger.RefiningTowerCode.codes_ofStages' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.RefiningTowerCode.codes_ofStages

-- Issue #15 (unconditional drive): the CONCRETE escape-symbol code. stageCode (one measurable code
-- via getD…s, the escape symbol doubling as off-tower default AND column terminator) +
-- measurable_stageCode + stageCode_predecessor (the W7/W8 bracketing proved UNCONDITIONALLY over the
-- whole towerBase) + stageCode_of_tower (the full per-stage StageCode). Residual = cross-stage
-- interleaving (one fixed code agreeing with each stageCode), carried in StageInput.

/-- info: 'ErgodicTheory.Krieger.measurable_stageCode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.measurable_stageCode

/-- info: 'ErgodicTheory.Krieger.stageCode_predecessor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.stageCode_predecessor

/-- info: 'ErgodicTheory.Krieger.stageCode_of_tower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.stageCode_of_tower

/-- info: 'ErgodicTheory.Krieger.StageInput.codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.StageInput.codes

-- Issue #15 (unconditional drive): the cross-stage WEAVE. The derived-name trick (weaveName = read
-- the master code off the column + invert through emb) makes code_floor/code_pred DEFINITIONAL
-- (stageCode_weaveName_eq), so the overlap consistency is automatic — there is literally one code.
-- Sub-problem B is reduced to ONE leaf: the existence of a BracketedTowerSystem (nested towers + one
-- self-bracketed master code), the genuine Keane–Serafin nested-marker construction.

/-- info: 'ErgodicTheory.Krieger.stageCode_weaveName_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.stageCode_weaveName_eq

/-- info: 'ErgodicTheory.Krieger.BracketedTowerSystem.codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.BracketedTowerSystem.codes

-- Issue #15 (unconditional drive): the marker-set factoring. markerCode M emb dataLetter (s on M,
-- data letters off M) is measurable (measurable_markerCode); AlignedTowerCastle reduces the three
-- self-bracketing conditions to set-membership on ONE coherent marker set M. Sub-problem B's entire
-- residual is now the EXISTENCE of M + nested towers — the Kakutani–Rokhlin nested aligned castle.

/-- info: 'ErgodicTheory.Krieger.measurable_markerCode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.measurable_markerCode

/-- info: 'ErgodicTheory.Krieger.AlignedTowerCastle.codes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Krieger.AlignedTowerCastle.codes

-- Issue #16 — coarse-grained multifractal analysis. The finite-resolution core (generalized
-- partition function `Z_q`, Rényi dimensions `D_q`, the singularity spectrum `f(α)`) and its
-- measure / flow layer, all sorry-free and depending only on the standard axioms.

/-- info: 'ErgodicTheory.Multifractal.logPartitionFunction_convexOn' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.logPartitionFunction_convexOn

/-- info: 'ErgodicTheory.Multifractal.massExponent_concaveOn' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.massExponent_concaveOn

/-- info: 'ErgodicTheory.Multifractal.renyiDim_antitone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDim_antitone

/-- info: 'ErgodicTheory.Multifractal.partitionFunction_equalMeasure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.partitionFunction_equalMeasure

/-- info: 'ErgodicTheory.Multifractal.renyiDimMeasure_antitone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDimMeasure_antitone

/-- info: 'ErgodicTheory.Multifractal.renyiDimMeasure_one_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDimMeasure_one_eq

/-- info: 'ErgodicTheory.Multifractal.renyiDimFlow_antitone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDimFlow_antitone

/-- info: 'ErgodicTheory.Multifractal.renyiDim_uniform_eq_dim' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDim_uniform_eq_dim

/-- info: 'ErgodicTheory.Multifractal.renyiDim_uniform_seq_tendsto_dim' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDim_uniform_seq_tendsto_dim

/-- info: 'ErgodicTheory.Multifractal.ae_tendsto_localDimension_of_absolutelyContinuous' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ae_tendsto_localDimension_of_absolutelyContinuous

/-- info: 'ErgodicTheory.Multifractal.ae_localDimension_eq_finrank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ae_localDimension_eq_finrank

/-- info: 'ErgodicTheory.Multifractal.dimH_eq_finrank_of_ae_full_of_absolutelyContinuous' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.dimH_eq_finrank_of_ae_full_of_absolutelyContinuous

/-- info: 'ErgodicTheory.sumPosExp_eq_integral_log_abs_det_of_expanding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.sumPosExp_eq_integral_log_abs_det_of_expanding

/-- info: 'ErgodicTheory.Entropy.ksEntropy_eq_ksEntropyPartition_of_generating' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.ksEntropy_eq_ksEntropyPartition_of_generating

/-- info: 'ErgodicTheory.Multifractal.dimH_le_of_fine_cover_mass_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.dimH_le_of_fine_cover_mass_lower

/-- info: 'ErgodicTheory.Multifractal.dimH_eq_of_localDimension_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.dimH_eq_of_localDimension_eq

/-- info: 'ErgodicTheory.Multifractal.dimH_eq_finrank_carrier_of_absolutelyContinuous' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.dimH_eq_finrank_carrier_of_absolutelyContinuous

/-- info: 'ErgodicTheory.condEntropy_comap_eq_integral_log_abs_det' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.condEntropy_comap_eq_integral_log_abs_det

/-- info: 'ErgodicTheory.ksEntropyPartition_eq_integral_log_abs_det' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropyPartition_eq_integral_log_abs_det

/-- info: 'ErgodicTheory.pesin_formula_expanding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.pesin_formula_expanding

/-- info: 'ErgodicTheory.sumPosExp_eq_sumAllExp_of_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.sumPosExp_eq_sumAllExp_of_nonneg

/-- info: 'ErgodicTheory.strictFuture_le_comap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.strictFuture_le_comap

/-- info: 'ErgodicTheory.integral_log_abs_det_le_ksEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.integral_log_abs_det_le_ksEntropy

/-- info: 'ErgodicTheory.sumPosExp_le_ksEntropy_of_SRB' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.sumPosExp_le_ksEntropy_of_SRB

/-- info: 'ErgodicTheory.pesin_entropy_formula_spectral' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.pesin_entropy_formula_spectral

/-- info: 'ErgodicTheory.pesin_entropy_formula' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.pesin_entropy_formula

/-- info: 'ErgodicTheory.Examples.Rokhlin.pesin_identity_doublingMap_perPartition' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Examples.Rokhlin.pesin_identity_doublingMap_perPartition

/-- info: 'ErgodicTheory.Examples.Rokhlin.borel_le_generateFrom_dyadicArcs' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Examples.Rokhlin.borel_le_generateFrom_dyadicArcs

/-- info: 'ErgodicTheory.Examples.Rokhlin.binPartition_isGenerating' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Examples.Rokhlin.binPartition_isGenerating

/-- info: 'ErgodicTheory.Examples.Rokhlin.ksEntropy_doublingMap_eq_log_two' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Examples.Rokhlin.ksEntropy_doublingMap_eq_log_two

/-- info: 'ErgodicTheory.Examples.Rokhlin.pesin_formula_doublingMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Examples.Rokhlin.pesin_formula_doublingMap

/-- info: 'ErgodicTheory.Multifractal.dimH_eq_ksEntropyPartition_div_log_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.dimH_eq_ksEntropyPartition_div_log_two

/-- info: 'ErgodicTheory.Multifractal.dimH_eq_ksEntropy_div_log_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.dimH_eq_ksEntropy_div_log_two

/-- info: 'ErgodicTheory.Multifractal.integral_empiricalCellMass_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.integral_empiricalCellMass_eq

/-- info: 'ErgodicTheory.Multifractal.tendsto_empiricalCellMass_ae' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.tendsto_empiricalCellMass_ae

/-- info: 'ErgodicTheory.Multifractal.cellMassFamily_sum_eq_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.cellMassFamily_sum_eq_one

/-- info: 'ErgodicTheory.Multifractal.not_isHeterogeneous_iff_equalMeasure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.not_isHeterogeneous_iff_equalMeasure

/-- info: 'ErgodicTheory.Multifractal.refiningLimitConvergesSeqProp_of_uniform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.refiningLimitConvergesSeqProp_of_uniform

/-! ### Issue #19 — the chaotic Bernoulli-suspension flow object
(positive metric entropy + a non-uniform ergodic invariant measure on which `D_q` is `q`-dependent) -/

/-- info: 'ErgodicTheory.Multifractal.suspensionFlow_bernZ_ksEntropy_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.suspensionFlow_bernZ_ksEntropy_pos

/-- info: 'ErgodicTheory.Multifractal.renyiDimFlow_bernSuspension_q_dependent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDimFlow_bernSuspension_q_dependent

/-- info: 'ErgodicTheory.Multifractal.renyiDimMeasure_zero_ne_one_bern' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDimMeasure_zero_ne_one_bern

/-- info: 'ErgodicTheory.Multifractal.renyiDimFlow_bernSuspension_zero_ne_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.renyiDimFlow_bernSuspension_zero_ne_one

/-- info: 'ErgodicTheory.Multifractal.dimH_bern_eq_Hnu_div_log_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.dimH_bern_eq_Hnu_div_log_two

/-- info: 'ErgodicTheory.Multifractal.hasFlowExponent_of_tendsto_finiteTimeFlowExponent' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.hasFlowExponent_of_tendsto_finiteTimeFlowExponent

/-- info: 'ErgodicTheory.Multifractal.isHeterogeneous_bernSuspensionWitness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.isHeterogeneous_bernSuspensionWitness

/-- info: 'ErgodicTheory.Multifractal.measurePreserving_suspensionBaseProj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.measurePreserving_suspensionBaseProj

/-- info: 'ErgodicTheory.Multifractal.ergodic_shiftMap_bern' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ergodic_shiftMap_bern

/-- info: 'ErgodicTheory.Multifractal.ksEntropy_bern_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ksEntropy_bern_eq

/-! ### Issue #19 — ergodicity of the constant-roof Bernoulli suspension flow
(the full `ℝ`-flow is ergodic iff the base shift is; its time-`1` map is honestly NOT ergodic) -/

/-- info: 'ErgodicTheory.Multifractal.ergodic_bernSuspensionFlow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ergodic_bernSuspensionFlow

/-- info: 'ErgodicTheory.Multifractal.not_ergodic_bernSuspensionFlow_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.not_ergodic_bernSuspensionFlow_one

/-- info: 'ErgodicTheory.Multifractal.suspensionMeasure_eq_bernZ_base_of_flowInvariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.suspensionMeasure_eq_bernZ_base_of_flowInvariant

/-- info: 'ErgodicTheory.Multifractal.suspensionMeasure_sectionHalf' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.suspensionMeasure_sectionHalf

/-! ### Issue #19 ext — two-sided Bernoulli ergodicity (keystone) + UNCONDITIONAL flow ergodicity -/

/-- info: 'ErgodicTheory.Multifractal.ergodic_biShiftEquiv_bernZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ergodic_biShiftEquiv_bernZ

/-- info: 'ErgodicTheory.Multifractal.ergodic_bernSuspensionFlow_uncond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ergodic_bernSuspensionFlow_uncond

/-! ### Issue #20 — two-sided / invertible Kolmogorov–Sinai generator theorem
(keystone), the two-sided-generating Bernoulli partition, the system-entropy unlock
`ksEntropy(bernZ) = Hnu`, and the constant-roof suspension `StandardBorelSpace`. -/

/-- info: 'ErgodicTheory.Entropy.ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.ksEntropy_eq_ksEntropyPartition_of_isGeneratingTwoSided

/-- info: 'ErgodicTheory.Multifractal.coordPartitionZFin_isGeneratingTwoSided' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.coordPartitionZFin_isGeneratingTwoSided

/-- info: 'ErgodicTheory.Multifractal.ksEntropy_biShiftEquiv_bernZ_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ksEntropy_biShiftEquiv_bernZ_eq

/-- info: 'ErgodicTheory.standardBorelSpace_suspensionSpace_const_roof' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.standardBorelSpace_suspensionSpace_const_roof

/-- info: 'ErgodicTheory.Multifractal.instStandardBorelSpace_suspensionSpace_bern' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.instStandardBorelSpace_suspensionSpace_bern

/-! ### Issue #20 fibre — product/skew entropy `h(T×id)=h(T)` (Walters Thm 4.23) and the
unconditional Category-C unlock: the constant-roof Bernoulli suspension time-`1` map has
metric entropy `Hnu`. -/

/-- info: 'ErgodicTheory.Entropy.ksEntropy_prod_id_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.ksEntropy_prod_id_eq

/-- info: 'ErgodicTheory.Multifractal.ksEntropy_bernSuspensionFlow_one_eq_Hnu' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ksEntropy_bernSuspensionFlow_one_eq_Hnu

/-- info: 'ErgodicTheory.Multifractal.bernSuspensionFlow_ksEntropy_eq_Hnu' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.bernSuspensionFlow_ksEntropy_eq_Hnu

/-! ### Issue #21 — the literal conditional-fibre entropy of the constant-roof Bernoulli
suspension vanishes (`condKsEntropy(time-1 | base factor) = 0`), via the conditional Le Maître
chain: the A0 chain-rule keystone, the conditional frozen-product vanishing `h(T×id | fst) = 0`
(D), and conjugacy invariance of the conditional KS entropy (E2). -/

/-- info: 'ErgodicTheory.Multifractal.condKsEntropy_bernSuspensionFlow_one_baseProj_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.condKsEntropy_bernSuspensionFlow_one_baseProj_eq_zero

/-- info: 'ErgodicTheory.Entropy.condKsEntropy_prod_id_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.condKsEntropy_prod_id_eq_zero

/-- info: 'ErgodicTheory.Entropy.condEntropyGivenPartitionCond_eq_condEntropy_sup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.condEntropyGivenPartitionCond_eq_condEntropy_sup

/-- info: 'ErgodicTheory.Entropy.condKsEntropy_congr_of_conjugacy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.condKsEntropy_congr_of_conjugacy

/-! ### Issue #23 — finite-dimensional operator entropy (foundations)
`DensityMatrix` / `vonNeumannEntropy`, the partial trace as a positive trace-preserving map,
the Kronecker spectrum, and the scalar Klein inequality. -/

/-- info: 'ErgodicTheory.OperatorEntropy.vonNeumannEntropy_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.vonNeumannEntropy_nonneg

/-- info: 'ErgodicTheory.OperatorEntropy.trace_partialTraceRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.trace_partialTraceRight

/-- info: 'ErgodicTheory.OperatorEntropy.PosSemidef.partialTraceRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.PosSemidef.partialTraceRight

/-- info: 'ErgodicTheory.OperatorEntropy.eigenvalues_kronecker_multiset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.eigenvalues_kronecker_multiset

/-- info: 'ErgodicTheory.OperatorEntropy.klein_scalar' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.klein_scalar

/-! Issue #23 assembly — von Neumann entropy additivity & subadditivity, and the
`DensityMatrix`-level Kronecker / partial-trace maps. -/

/-- info: 'ErgodicTheory.OperatorEntropy.DensityMatrix.kron' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.DensityMatrix.kron

/-- info: 'ErgodicTheory.OperatorEntropy.DensityMatrix.partialTraceRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.DensityMatrix.partialTraceRight

/-- info: 'ErgodicTheory.OperatorEntropy.vonNeumannEntropy_additive_kronecker' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.vonNeumannEntropy_additive_kronecker

/-- info: 'ErgodicTheory.OperatorEntropy.vonNeumannEntropy_subadditive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.vonNeumannEntropy_subadditive

/-! Issue #23 — Left-handed partial-trace mirror guards (symmetry with the Right-handed ones). -/

/-- info: 'ErgodicTheory.OperatorEntropy.trace_partialTraceLeft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.trace_partialTraceLeft

/-- info: 'ErgodicTheory.OperatorEntropy.PosSemidef.partialTraceLeft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.PosSemidef.partialTraceLeft

/-- info: 'ErgodicTheory.OperatorEntropy.DensityMatrix.partialTraceLeft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.DensityMatrix.partialTraceLeft

/-! ### Issue #24 — CNT/ALF quantum dynamical entropy (construction)
Diagonal von Neumann entropy bridge, the partition-of-unity telescoping, the correlation
density matrix, and the `cntDynamicalEntropy` itself. -/

/-- info: 'ErgodicTheory.OperatorEntropy.vonNeumannEntropy_diagonal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.vonNeumannEntropy_diagonal

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.sum_refine_conjTranspose_mul_refine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.sum_refine_conjTranspose_mul_refine

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.corrMatrix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.corrMatrix

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropy

/-! ### Issue #24 — CNT/ALF abelian-corner theorem (the headline)
The quantum dynamical entropy restricted to the abelian (diagonal) corner equals the classical
Kolmogorov–Sinai entropy of the induced measure-preserving permutation system. -/

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.cntEntropyPartition_eq_ksEntropyPartition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.cntEntropyPartition_eq_ksEntropyPartition

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropyAbelian_eq_ksEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropyAbelian_eq_ksEntropy

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.ksEntropy_le_cntDynamicalEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.ksEntropy_le_cntDynamicalEntropy

-- The substantive per-resolution identity behind the abelian-corner collapse (non-vacuous:
-- positive at finite `n`, unlike the rate equality which is `0` for a finite permutation).
/-- info: 'ErgodicTheory.OperatorEntropy.CNT.vonNeumannEntropy_corrMatrix_eq_ksEntropySeq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.vonNeumannEntropy_corrMatrix_eq_ksEntropySeq

/-! ### Issue #22 — Umegaki relative entropy (feasible foundations layer)
Klein-inequality nonnegativity of the relative entropy, its vanishing on the diagonal,
unitary-conjugation invariance, and the DPI/no-recovery-section corollary (whose
data-processing input is an explicit hypothesis, the Lieb-gated piece staying out). -/

/-- info: 'ErgodicTheory.OperatorEntropy.relEntropy_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.relEntropy_nonneg

/-- info: 'ErgodicTheory.OperatorEntropy.relEntropy_self_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.relEntropy_self_eq_zero

/-- info: 'ErgodicTheory.OperatorEntropy.relEntropy_conj_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.relEntropy_conj_invariant

/-- info: 'ErgodicTheory.OperatorEntropy.no_monotone_section_of_strict_drop' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.no_monotone_section_of_strict_drop

/-- info: 'ErgodicTheory.OperatorEntropy.petz_recovery' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.petz_recovery

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.operatorConvexOn_neg_log' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.operatorConvexOn_neg_log

/-- info: 'ErgodicTheory.OperatorEntropy.relEntropy_additive_kronecker' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.relEntropy_additive_kronecker

/-- info: 'ErgodicTheory.OperatorEntropy.relEntropy_ancilla_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.relEntropy_ancilla_invariant

/-- info: 'ErgodicTheory.OperatorEntropy.relEntropy_embed_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.relEntropy_embed_invariant

/-- info: 'ErgodicTheory.OperatorEntropy.stinespring_relEntropy_monotone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.stinespring_relEntropy_monotone

/-- info: 'ErgodicTheory.OperatorEntropy.relEntropy_eq_traceLog' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.relEntropy_eq_traceLog

/-- info: 'ErgodicTheory.OperatorEntropy.KrausChannel.adj_hsAdjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.KrausChannel.adj_hsAdjoint

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.exists_unitary_firstBlockCol' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.exists_unitary_firstBlockCol

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.hpj_affine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.hpj_affine

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.hpj_isometry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.hpj_isometry

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.operatorPerspective_jointly_convex' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.operatorPerspective_jointly_convex

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.relEntropyMat_jointly_convex' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.relEntropyMat_jointly_convex

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.relEntropyMonotone_partialTrace_faithful' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.relEntropyMonotone_partialTrace_faithful

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.twirl_sum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.twirl_sum

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.relEntropyMonotone_partialTrace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.relEntropyMonotone_partialTrace

/-- info: 'ErgodicTheory.OperatorEntropy.monotonicity_relEntropy_under_stinespring' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.monotonicity_relEntropy_under_stinespring

/-- info: 'ErgodicTheory.OperatorEntropy.no_section_of_strict_relEntropy_drop' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.no_section_of_strict_relEntropy_drop

/-- info: 'ErgodicTheory.OperatorEntropy.no_stinespring_section_of_strict_relEntropy_drop' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.no_stinespring_section_of_strict_relEntropy_drop

/-- info: 'ErgodicTheory.OperatorEntropy.petz_recovery_implies_equality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.petz_recovery_implies_equality

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.petz_equality_recovery' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.petz_equality_recovery

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.petz_equality_recovery_general' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.petz_equality_recovery_general

/-- info: 'ErgodicTheory.OperatorEntropy.Lieb.partialTrace_equality_imp_intertwinesIt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.Lieb.partialTrace_equality_imp_intertwinesIt

/-! ### Issues #25 + #26 — literal-Kraus partial traces and the finite-dimensional CNT collapse
The explicit block-inclusion Kraus form of the partial traces (#25); the entropy-rank maximum-entropy
bound and the non-idempotent strict positivity; the Gram-factorisation rank bound of the CNT
correlation matrix; the finite-dimensional vanishing of the CNT/ALF entropy rate with its
abelian-corner / KS-entropy consequences; the abelian Fekete well-definedness; and the explicit
counterexample to subadditivity of the CNT entropy sequence (#26). -/

/-- info: 'ErgodicTheory.OperatorEntropy.partialTraceRight_eq_kraus' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.partialTraceRight_eq_kraus

/-- info: 'ErgodicTheory.OperatorEntropy.partialTraceLeft_eq_kraus' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.partialTraceLeft_eq_kraus

/-- info: 'ErgodicTheory.OperatorEntropy.sum_conjTranspose_mul_krausInclusionRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.sum_conjTranspose_mul_krausInclusionRight

/-- info: 'ErgodicTheory.OperatorEntropy.krausInclusionRight_mul_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.krausInclusionRight_mul_conjTranspose

/-- info: 'ErgodicTheory.OperatorEntropy.krausInclusionLeft_mul_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.krausInclusionLeft_mul_conjTranspose

/-- info: 'ErgodicTheory.OperatorEntropy.sum_conjTranspose_mul_krausInclusionLeft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.sum_conjTranspose_mul_krausInclusionLeft

/-- info: 'ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_rank

/-- info: 'ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_card' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.vonNeumannEntropy_le_log_card

/-- info: 'ErgodicTheory.OperatorEntropy.vonNeumannEntropy_pos_of_sq_ne' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.vonNeumannEntropy_pos_of_sq_ne

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.corrVal_eq_conjTranspose_mul_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.corrVal_eq_conjTranspose_mul_self

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.rank_corrVal_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.rank_corrVal_le

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.vonNeumannEntropy_corrMatrix_le_log' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.vonNeumannEntropy_corrMatrix_le_log

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.cntEntropyPartition_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.cntEntropyPartition_eq_zero

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.tendsto_cntEntropySeq_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.tendsto_cntEntropySeq_div

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropy_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropy_eq_zero

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropyAbelianFull_eq_ksEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropyAbelianFull_eq_ksEntropy

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropyAbelian_le_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.cntDynamicalEntropyAbelian_le_full

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.ksEntropy_eq_cntDynamicalEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.ksEntropy_eq_cntDynamicalEntropy

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.tendsto_cntEntropyPartition_abelian' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.tendsto_cntEntropyPartition_abelian

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.subadditive_vonNeumannEntropy_corrMatrix_abelian' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.subadditive_vonNeumannEntropy_corrMatrix_abelian

/-- info: 'ErgodicTheory.OperatorEntropy.CNT.not_subadditive_cnt_entropySeq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.OperatorEntropy.CNT.not_subadditive_cnt_entropySeq

-- Issue #30 (cat-map suspension flow carries the base's derivative cocycle): the four headlines of
-- `ErgodicTheory.Examples.CatMapSuspensionFlow`.

/-- info: 'ErgodicTheory.CatMapToral.catSuspension_ae_hasFlowExponent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catSuspension_ae_hasFlowExponent

/-- info: 'ErgodicTheory.CatMapToral.catSuspension_ae_hasFlowExponent_flowOrbit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catSuspension_ae_hasFlowExponent_flowOrbit

/-- info: 'ErgodicTheory.CatMapToral.catSuspensionFlow_ownExponent_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catSuspensionFlow_ownExponent_pos

/-- info: 'ErgodicTheory.CatMapToral.catSuspension_flowExponent_eq_base_div_roof' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catSuspension_flowExponent_eq_base_div_roof

-- Issue #29 (Livšic cohomological rigidity): the abstract equivalence and its supporting steps.

/-- info: 'ErgodicTheory.isHolderCoboundary_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.isHolderCoboundary_iff

/-- info: 'ErgodicTheory.exists_holderCoboundary_of_denseOrbit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.exists_holderCoboundary_of_denseOrbit

/-- info: 'ErgodicTheory.exists_holderWith_extension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.exists_holderWith_extension

/-- info: 'ErgodicTheory.IsCoboundary.hasVanishingPeriodicSums' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.IsCoboundary.hasVanishingPeriodicSums

/-- info: 'ErgodicTheory.not_isCoboundary_of_periodicSum_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.not_isCoboundary_of_periodicSum_ne_zero

-- Issue #29 (full-shift instance): the closing property, the dense orbit, and the rigidity tiers.

/-- info: 'ErgodicTheory.Livsic.expClosing_shiftMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.expClosing_shiftMap

/-- info: 'ErgodicTheory.Livsic.exists_denseRange_shiftMap_orbit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.exists_denseRange_shiftMap_orbit

/-- info: 'ErgodicTheory.Livsic.hasVanishingPeriodicSums_of_continuous_coboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.hasVanishingPeriodicSums_of_continuous_coboundary

/-- info: 'ErgodicTheory.Livsic.hasVanishingPeriodicSums_of_bounded_aeCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.hasVanishingPeriodicSums_of_bounded_aeCoboundary

-- Issue #29 (headline full-shift Livšic equivalence, its `Fin m` form, and the corollaries).

/-- info: 'ErgodicTheory.Livsic.livsic_fullShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.livsic_fullShift

/-- info: 'ErgodicTheory.Livsic.livsic_fullShift_fin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.livsic_fullShift_fin

/-- info: 'ErgodicTheory.Livsic.phi_not_isCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.phi_not_isCoboundary

/-- info: 'ErgodicTheory.Livsic.phi_not_isHolderCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.phi_not_isHolderCoboundary

/-- info: 'ErgodicTheory.Livsic.psi_isHolderCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.psi_isHolderCoboundary

/-- info: 'ErgodicTheory.Livsic.psi_hasVanishingPeriodicSums' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.psi_hasVanishingPeriodicSums

/-- info: 'ErgodicTheory.Livsic.psi_isHolderCoboundary_via_livsic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.psi_isHolderCoboundary_via_livsic

/-- info: 'ErgodicTheory.Livsic.isOpenPosMeasure_bern' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.isOpenPosMeasure_bern

/-- info: 'ErgodicTheory.Livsic.isHolderCoboundary_of_continuous_aeCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.isHolderCoboundary_of_continuous_aeCoboundary

/-- info: 'ErgodicTheory.Livsic.isHolderCoboundary_of_bounded_aeCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.isHolderCoboundary_of_bounded_aeCoboundary

/-! ### Issue #37 — representative-free flow exponent as a genuine `SuspensionSpace → ℝ` function -/

-- Issue #37 (signed-step closure + `Quotient.lift` descent of the special-flow exponent): the
-- cover-cocycle positivity, signed-step uniqueness, the descended `flowExponentAt`, its readoff and
-- a.e. identification, and the three cat-suspension instantiations.

/-- info: 'ErgodicTheory.coverCocycle_norm_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.coverCocycle_norm_pos

/-- info: 'ErgodicTheory.tendsto_exponent_iff_of_orbitRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.tendsto_exponent_iff_of_orbitRel

/-- info: 'ErgodicTheory.flowExponentAt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.flowExponentAt

/-- info: 'ErgodicTheory.flowExponentAt_eq_of_hasFlowExponent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.flowExponentAt_eq_of_hasFlowExponent

/-- info: 'ErgodicTheory.ae_flowExponentAt_eq_base_div_roof' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ae_flowExponentAt_eq_base_div_roof

/-- info: 'ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_eq_log' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_eq_log

/-- info: 'ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_eq_base_div_roof' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_eq_base_div_roof

/-- info: 'ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catSuspension_flowExponentAt_pos

/-! ### Issues #32 + #33 — Livšic II (two-sided shift, SFTs, cat map) + doubling instance -/

-- Issue #33 (smooth expanding doubling-map instance): the generic ergodic dense orbit, the rounding
-- closing property, the headline equivalence, and its obstruction/positive witnesses.

/-- info: 'ErgodicTheory.ergodic_exists_denseRange_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ergodic_exists_denseRange_iterate

/-- info: 'ErgodicTheory.expClosing_doublingMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.expClosing_doublingMap

/-- info: 'ErgodicTheory.livsic_doublingMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.livsic_doublingMap

/-- info: 'ErgodicTheory.doublingMap_periodic_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.doublingMap_periodic_iff

/-- info: 'ErgodicTheory.const_one_not_isCoboundary_doublingMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.const_one_not_isCoboundary_doublingMap

/-- info: 'ErgodicTheory.norm_coboundary_isHolderCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.norm_coboundary_isHolderCoboundary

-- Issue #32 (one-sided subshift-of-finite-type tier): the unconditional `δ = 1/2` closing property,
-- the conditional equivalence, the safe-symbol dense orbit, and the golden-mean instance.

/-- info: 'ErgodicTheory.expClosing_sftShiftMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.expClosing_sftShiftMap

/-- info: 'ErgodicTheory.livsic_sft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.livsic_sft

/-- info: 'ErgodicTheory.exists_denseRange_sftShiftMap_orbit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.exists_denseRange_sftShiftMap_orbit

/-- info: 'ErgodicTheory.livsic_goldenMean' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.livsic_goldenMean

-- `goldenMean_proper` is a decidable non-membership fact, so it honestly needs only `[propext]`
-- (a strict subset of the standard set — no `Classical.choice`, no `Quot.sound`, no `sorryAx`).
/-- info: 'ErgodicTheory.goldenMean_proper' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.goldenMean_proper

-- Issue #32 (two-sided full-shift tier): the min-regime closing property, the bilateral dense orbit,
-- the headline equivalence, and the fully-supported-measure rigidity corollaries.

/-- info: 'ErgodicTheory.expClosing_biShiftMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.expClosing_biShiftMap

/-- info: 'ErgodicTheory.exists_denseRange_biShiftMap_orbit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.exists_denseRange_biShiftMap_orbit

/-- info: 'ErgodicTheory.livsic_biShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.livsic_biShift

/-- info: 'ErgodicTheory.livsic_biShift_fin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.livsic_biShift_fin

/-- info: 'ErgodicTheory.isOpenPosMeasure_bernZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.isOpenPosMeasure_bernZ

/-- info: 'ErgodicTheory.isHolderCoboundary_of_continuous_aeCoboundary_biShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.isHolderCoboundary_of_continuous_aeCoboundary_biShift

/-- info: 'ErgodicTheory.isHolderCoboundary_of_bounded_aeCoboundary_biShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.isHolderCoboundary_of_bounded_aeCoboundary_biShift

-- Issue #32 (cat-map instance): the summed exponential closing property, the headline Livšic
-- equivalence, and the constant-observable obstruction witness for Arnold's cat map on `T²`.

/-- info: 'ErgodicTheory.CatMapToral.expClosing_catTorus' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.expClosing_catTorus

/-- info: 'ErgodicTheory.CatMapToral.livsic_catTorus' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.livsic_catTorus

/-- info: 'ErgodicTheory.CatMapToral.const_one_not_isCoboundary_catTorus' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.const_one_not_isCoboundary_catTorus

/-! ### Issue #36 — Livšic flow tier: periodic-orbit obstruction for suspension flows -/

-- The regularity-free flow coboundary and its generic periodic-orbit obstruction.

/-- info: 'ErgodicTheory.not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.not_isFlowCoboundary_of_periodicOrbitIntegral_ne_zero

-- The suspension-flow landing: cross-section return, induced base coboundary, and both obstruction
-- tiers (induced periodic sum and flow-native closed-orbit integral) plus the bridge identity.

/-- info: 'ErgodicTheory.suspensionFlowMap_roof' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.suspensionFlowMap_roof

/-- info: 'ErgodicTheory.inducedBaseCocycle_isCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.inducedBaseCocycle_isCoboundary

/-- info: 'ErgodicTheory.not_isFlowCoboundary_of_inducedPeriodicSum_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.not_isFlowCoboundary_of_inducedPeriodicSum_ne_zero

/-- info: 'ErgodicTheory.suspensionFlow_orbit_periodic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.suspensionFlow_orbit_periodic

/-- info: 'ErgodicTheory.not_isFlowCoboundary_suspensionFlowMap_of_periodicOrbitIntegral_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.not_isFlowCoboundary_suspensionFlowMap_of_periodicOrbitIntegral_ne_zero

/-- info: 'ErgodicTheory.suspension_periodicOrbitIntegral_eq_birkhoffSum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.suspension_periodicOrbitIntegral_eq_birkhoffSum

/-- info: 'ErgodicTheory.not_isFlowCoboundary_suspensionFlow_of_inducedPeriodicSum_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.not_isFlowCoboundary_suspensionFlow_of_inducedPeriodicSum_ne_zero

/-- info: 'ErgodicTheory.not_isFlowCoboundary_suspensionFlow_of_periodicOrbitIntegral_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.not_isFlowCoboundary_suspensionFlow_of_periodicOrbitIntegral_ne_zero

-- The per-lap identity feeding the bridge.

/-- info: 'ErgodicTheory.suspensionCoboundary_lap_integral' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.suspensionCoboundary_lap_integral

-- The trivial inhabitant (zero observable is a flow coboundary) and the concrete non-vacuity
-- witness (the constant `1` is not a flow coboundary of the cat-map suspension flow).

/-- info: 'ErgodicTheory.isFlowCoboundary_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.isFlowCoboundary_zero

/-- info: 'ErgodicTheory.CatMapToral.const_one_not_isFlowCoboundary_catSuspension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.const_one_not_isFlowCoboundary_catSuspension
/-! ### Issues #35 + #38 — time-1 ergodicity (irrational constant roof) + suspension entropy descent -/

-- Issue #35 (time-1 ergodicity): strong mixing of the two-sided Bernoulli shift and the
-- eigenfunction-vanishing criterion feeding the Fourier/Parseval fibre argument, the twisted
-- eigenfunction relations, the per-fibre Parseval bridge and dichotomy, the abstract constant-roof
-- time-1 ergodicity, and its Bernoulli instantiation with the concrete `r := √2` non-vacuity witness.

/-- info: 'ErgodicTheory.Multifractal.tendsto_measureReal_inter_preimage_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.tendsto_measureReal_inter_preimage_iterate

/-- info: 'ErgodicTheory.eigenfunction_ae_zero_of_mixing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.eigenfunction_ae_zero_of_mixing

/-- info: 'ErgodicTheory.coeffFn_twist' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.coeffFn_twist

/-- info: 'ErgodicTheory.coeffFn_liftedIndicator_twist' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.coeffFn_liftedIndicator_twist

/-- info: 'ErgodicTheory.parseval_bridge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.parseval_bridge

/-- info: 'ErgodicTheory.fibre_indicator_dichotomy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.fibre_indicator_dichotomy

/-- info: 'ErgodicTheory.ergodic_suspensionFlowMap_one_const_roof' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ergodic_suspensionFlowMap_one_const_roof

/-- info: 'ErgodicTheory.Multifractal.ergodic_suspensionFlow_timeOne_const_irrational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ergodic_suspensionFlow_timeOne_const_irrational

/-- info: 'ErgodicTheory.Multifractal.ergodic_suspensionFlow_packaged_timeOne_const_irrational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ergodic_suspensionFlow_packaged_timeOne_const_irrational

/-- info: 'ErgodicTheory.Multifractal.ergodic_suspensionFlow_timeOne_sqrtTwo' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Multifractal.ergodic_suspensionFlow_timeOne_sqrtTwo

-- Issue #47 (cat-map spectral rigidity): a measurable eigenfunction of the Arnold cat map with a
-- unimodular eigenvalue `≠ 1` vanishes a.e., and the time-`1` map of the constant-irrational-roof
-- cat-map suspension flow is ergodic (with the `r = √2` non-vacuity witness).

/-- info: 'ErgodicTheory.CatMapToral.catTorus_eigenfunction_ae_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.catTorus_eigenfunction_ae_zero

/-- info: 'ErgodicTheory.CatMapToral.ergodic_catSuspension_timeOne_const_irrational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.ergodic_catSuspension_timeOne_const_irrational

/-- info: 'ErgodicTheory.CatMapToral.ergodic_catSuspension_timeOne_sqrtTwo' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.CatMapToral.ergodic_catSuspension_timeOne_sqrtTwo

-- Issue #38 (suspension entropy descent): the entropy power rule `h(Tⁿ) = n·h(T)`, the time-`r`
-- rescaling conjugacy of the constant-roof suspension (its measurable equivalence, invariant-measure
-- transport, and the `h(ζ^{(r)}_r) = Hnu` seal), and the flow-homogeneity descent giving the
-- time-1 entropy `h(ζ^{(r)}_1) = Hnu / r` for rational `r`.

/-- info: 'ErgodicTheory.Entropy.ksEntropy_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.ksEntropy_iterate

/-- info: 'ErgodicTheory.suspensionRescale' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.suspensionRescale

/-- info: 'ErgodicTheory.map_suspensionRescale_suspensionMeasure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.map_suspensionRescale_suspensionMeasure

/-- info: 'ErgodicTheory.ksEntropy_suspensionFlowMap_const_eq_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_suspensionFlowMap_const_eq_unit

/-- info: 'ErgodicTheory.ksEntropy_bernConstSuspension_time_r' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_bernConstSuspension_time_r

/-- info: 'ErgodicTheory.flow_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.flow_iterate

/-- info: 'ErgodicTheory.nsmul_ksEntropy_flow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.nsmul_ksEntropy_flow

/-- info: 'ErgodicTheory.nsmul_ksEntropy_bernSuspensionFlow_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.nsmul_ksEntropy_bernSuspensionFlow_inv

/-- info: 'ErgodicTheory.ksEntropy_bernSuspensionFlow_frac' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_bernSuspensionFlow_frac

/-- info: 'ErgodicTheory.ksEntropy_bernConstSuspension_time_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_bernConstSuspension_time_one

/-- info: 'ErgodicTheory.ksEntropy_bernConstSuspension_time_one_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_bernConstSuspension_time_one_mul

/-! ### Issue #34 — measurable Livšic rigidity (unbounded tier) via the two-sided extension -/

-- The classical Lusin theorem (continuous-on-a-compact form), the consumer of the measurable tier.

/-- info: 'ErgodicTheory.lusin_continuousOn' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.lusin_continuousOn

-- The one-sided measurable-solution tier: uniqueness modulo constants and conditional regularity.

/-- info: 'ErgodicTheory.Livsic.aeCoboundary_unique_mod_const' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.aeCoboundary_unique_mod_const

/-- info: 'ErgodicTheory.Livsic.measurable_solution_ae_eq_holder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.measurable_solution_ae_eq_holder

-- The two-sided natural-extension factor map and its transport properties (W1).

/-- info: 'ErgodicTheory.toShift' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.toShift

/-- info: 'ErgodicTheory.toShift_comp_biShiftMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.toShift_comp_biShiftMap

/-- info: 'ErgodicTheory.map_toShift_bernZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.map_toShift_bernZ

/-- info: 'ErgodicTheory.measurePreserving_toShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.measurePreserving_toShift

/-- info: 'ErgodicTheory.holderWith_comp_toShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.holderWith_comp_toShift

/-- info: 'ErgodicTheory.isAeCoboundaryOf_comp_toShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.isAeCoboundaryOf_comp_toShift

-- The past ⊗ future product structure of the two-sided Bernoulli measure (W2).

/-- info: 'ErgodicTheory.map_joinPF_bernZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.map_joinPF_bernZ

-- The two symmetric essential-oscillation bounds (W3 stable, W4 unstable): Lusin + reverse Fatou.

/-- info: 'ErgodicTheory.stable_pair_osc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.stable_pair_osc

/-- info: 'ErgodicTheory.unstable_pair_osc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.unstable_pair_osc

-- The Fubini glue and the two-sided headline (W5): essential boundedness + clamp.

/-- info: 'ErgodicTheory.essBounded_of_measurable_aeCoboundary_biShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.essBounded_of_measurable_aeCoboundary_biShift

/-- info: 'ErgodicTheory.hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.hasVanishingPeriodicSums_of_measurable_aeCoboundary_biShift

-- The one-sided descent and the full Katok–Hasselblatt 19.2.4 equivalence (W6).

/-- info: 'ErgodicTheory.Livsic.hasVanishingPeriodicSums_of_measurable_aeCoboundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.hasVanishingPeriodicSums_of_measurable_aeCoboundary

/-- info: 'ErgodicTheory.Livsic.livsic_measurable_rigidity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.livsic_measurable_rigidity

/-- info: 'ErgodicTheory.Livsic.measurable_aeCoboundary_ae_eq_holder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Livsic.measurable_aeCoboundary_ae_eq_holder

/-! ### Issue #11 — Arsenin–Kunugui: compact-section projection + everywhere-Borel singular filtration -/

-- The descriptive-set-theory infrastructure: analytic-set closure lemmas (finite intersections,
-- unions, products), the generalized first separation theorem (Srivastava 4.6.1), and the
-- coanalytic weak-reduction theorem.

/-- info: 'MeasureTheory.AnalyticSet.inter'' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.AnalyticSet.inter'

/-- info: 'MeasureTheory.AnalyticSet.union'' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.AnalyticSet.union'

/-- info: 'MeasureTheory.AnalyticSet.prod'' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.AnalyticSet.prod'

/-- info: 'ErgodicTheory.sepFam_ranges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.sepFam_ranges

/-- info: 'ErgodicTheory.generalized_first_separation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.generalized_first_separation

/-- info: 'ErgodicTheory.weak_reduction_coanalytic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.weak_reduction_coanalytic

-- The Saint Raymond disjoint-closed-sections and Kunugui–Novikov open-sections theorems
-- (Srivastava 4.7.1, 4.7.2).

/-- info: 'ErgodicTheory.saintRaymond_closedSections' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.saintRaymond_closedSections

/-- info: 'ErgodicTheory.kunuguiNovikov_openSections' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.kunuguiNovikov_openSections

-- The finer-Polish-topology reduction (Srivastava 4.7.4) and the compact-section projection
-- theorem (Novikov, Srivastava 4.7.11): the image of a Borel set with compact sections is Borel.

/-- info: 'ErgodicTheory.exists_finer_polish_isClosed_of_closedSections' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.exists_finer_polish_isClosed_of_closedSections

/-- info: 'ErgodicTheory.measurableSet_image_fst_of_isCompact_sections_of_compactSpace' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.measurableSet_image_fst_of_isCompact_sections_of_compactSpace

/-- info: 'ErgodicTheory.measurableSet_image_fst_of_isCompact_sections' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.measurableSet_image_fst_of_isCompact_sections

-- The issue #11 headline consumers: a measurable graph yields a measurable distance-to-fibre map,
-- the general measurable-graph → measurable-orthogonal-projection converter, and its specialization
-- to the singular λ̄-sublevel filtration (the everywhere-Borel singular filtration).

/-- info: 'ErgodicTheory.measurable_infDist_of_measurableGraph' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.measurable_infDist_of_measurableGraph

/-- info: 'ErgodicTheory.measurable_orthProjMatrix_of_measurableGraph' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.measurable_orthProjMatrix_of_measurableGraph

/-- info: 'ErgodicTheory.measurable_orthProjMatrix_lambdaSublevel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.measurable_orthProjMatrix_lambdaSublevel

-- Issue #48: Ito's elementary proof of Abramov flow-entropy homogeneity, the finite-family join
-- comparison (Ito's Lemma, L2), the keystone suspension-flow measure-continuity, the per-partition
-- LUB Proposition, and the unconditional (irrational-roof allowed) Bernoulli time-1 entropy value.

/-- info: 'ErgodicTheory.Entropy.entropy_finJoin_le_add_sum_condEntropy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.Entropy.entropy_finJoin_le_add_sum_condEntropy

/-- info: 'ErgodicTheory.tendsto_measureReal_symmDiff_suspensionFlowMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.tendsto_measureReal_symmDiff_suspensionFlowMap

/-- info: 'ErgodicTheory.exists_isLUB_ksEntropyPartition_flow_ratio' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.exists_isLUB_ksEntropyPartition_flow_ratio

/-- info: 'ErgodicTheory.ksEntropy_flow_eq_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_flow_eq_mul

/-- info: 'ErgodicTheory.ksEntropy_bernSuspensionFlow_time_s_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_bernSuspensionFlow_time_s_eq

/-- info: 'ErgodicTheory.ksEntropy_bernConstSuspension_time_one_irrational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ErgodicTheory.ksEntropy_bernConstSuspension_time_one_irrational
