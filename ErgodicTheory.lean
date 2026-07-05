import ErgodicTheory.Cocycle.Basic
import ErgodicTheory.Cocycle.Norm
import ErgodicTheory.Cocycle.FurstenbergKesten
import ErgodicTheory.Ergodic.MaximalErgodic
import ErgodicTheory.Ergodic.Birkhoff
import ErgodicTheory.Ergodic.Kingman.Core
import ErgodicTheory.Lyapunov.ExteriorNorm.Weyl
import ErgodicTheory.Lyapunov.MeasurableSubspace
import ErgodicTheory.Lyapunov.Measurable
import ErgodicTheory.Lyapunov.Ultrametric
import ErgodicTheory.Lyapunov.GrowthFunction
import ErgodicTheory.Lyapunov.Filtration
import ErgodicTheory.Lyapunov.OseledetsLimit.Limit
import ErgodicTheory.Lyapunov.Forward
import ErgodicTheory.Lyapunov.ForwardAngle
import ErgodicTheory.Lyapunov.ForwardUpperBound
import ErgodicTheory.Lyapunov.ForwardMeasurable
import ErgodicTheory.Lyapunov.ForwardV
import ErgodicTheory.Lyapunov.SpectralMeasurable
import ErgodicTheory.MultiplicativeErgodic
import ErgodicTheory.Lyapunov.FiltrationFromInterfaces
import ErgodicTheory.Lyapunov.FiltrationInterfaceReduction
import ErgodicTheory.Lyapunov.SlowFiltrationMeasurable
import ErgodicTheory.Lyapunov.SpectrumConstancy
import ErgodicTheory.Lyapunov.RuelleCore
import ErgodicTheory.Lyapunov.StratumLogGrowthBounds
import ErgodicTheory.Lyapunov.FiltrationFromSpectralUpper
import ErgodicTheory.Lyapunov.SpectrumResiduals
import ErgodicTheory.Lyapunov.RuelleReverse
import ErgodicTheory.Lyapunov.LimitSlowSpaceSpectralBound
import ErgodicTheory.Lyapunov.LimitEigenbasis
import ErgodicTheory.Lyapunov.FiltrationFromSpectralIdent
import ErgodicTheory.Lyapunov.SpectralIdentification
import ErgodicTheory.Lyapunov.ForwardGradedOverlap
import ErgodicTheory.Lyapunov.FastIndexSpectralEnvelope
import ErgodicTheory.Lyapunov.DimZero
import ErgodicTheory.Lyapunov.ChainRecursion
import ErgodicTheory.Lyapunov.ForwardGradedOverlapTopGap
import ErgodicTheory.Lyapunov.FiltrationFromTopGapEnvelope
import ErgodicTheory.Lyapunov.TopGapEnvelope
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
import ErgodicTheory.Continuous.SuspensionFlowCocycleMul
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
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Smooth.DerivativeCocycle
import ErgodicTheory.Smooth.Expanding
import ErgodicTheory.Smooth.RokhlinExpanding
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
-- Conditional / relative entropy + Abramov–Rokhlin (issue #13)
import ErgodicTheory.Entropy.CondPartition
import ErgodicTheory.Entropy.CondExpEquivariant
import ErgodicTheory.Entropy.CondPullback
import ErgodicTheory.Entropy.CondMono
import ErgodicTheory.Entropy.CondEntropyContinuous
import ErgodicTheory.Entropy.CondChainRule
import ErgodicTheory.Entropy.CondJointPullback
import ErgodicTheory.Entropy.CondKSEntropy
import ErgodicTheory.Entropy.CondKSEntropySystem
import ErgodicTheory.Entropy.FactorMap
import ErgodicTheory.Entropy.Generator
import ErgodicTheory.Entropy.FactorEntropy
import ErgodicTheory.Entropy.FactorGeneratorSaturate
import ErgodicTheory.Entropy.CondGivenPartitionBridge
import ErgodicTheory.Entropy.AbramovRokhlinPartition
import ErgodicTheory.Entropy.AbramovRokhlin
import ErgodicTheory.Entropy.AbramovRokhlinDefect
import ErgodicTheory.Entropy.CondBlockSubadditive
import ErgodicTheory.Entropy.JoinSigmaAlgebra
import ErgodicTheory.Entropy.CondKSMovingLimit
import ErgodicTheory.Entropy.AbramovRokhlinGenerator
import ErgodicTheory.Entropy.GeneratorTheorem
import ErgodicTheory.Entropy.GeneratorTheoremTwoSided
import ErgodicTheory.Entropy.KSEntropyCondBound
import ErgodicTheory.Entropy.ProductRectangleEntropy
import ErgodicTheory.Entropy.ProductFactorEntropy
import ErgodicTheory.Entropy.CondEntropyRefineZero
import ErgodicTheory.Entropy.KSEntropyConjugacy
import ErgodicTheory.Entropy.ProductIdEntropy
import ErgodicTheory.MeasureTheory.CoveringFromVolume
import ErgodicTheory.MeasureTheory.AnalyticUniversallyMeasurable
import ErgodicTheory.Entropy.Ruelle.AtomCount
import ErgodicTheory.Entropy.Ruelle.VolumeDistortion
import ErgodicTheory.Entropy.Ruelle.Crude
import ErgodicTheory.Entropy.Ruelle.LocalCovering
import ErgodicTheory.Entropy.Ruelle.Count
import ErgodicTheory.Entropy.Ruelle.SharpCovering
import ErgodicTheory.Entropy.Ruelle.MargulisRuelleSharp
import ErgodicTheory.Singular.StarProjectionPolar
import ErgodicTheory.Singular.JointMeasurableLambdaBar
import ErgodicTheory.Singular.GraphAndDim
import ErgodicTheory.Singular.MeasurableProjection
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
import ErgodicTheory.Krieger.ZIterate
import ErgodicTheory.Krieger.SmallSet
import ErgodicTheory.Krieger.FirstReturn
import ErgodicTheory.Krieger.InfoFunction
import ErgodicTheory.Krieger.NameCount
import ErgodicTheory.Krieger.Skyscraper
import ErgodicTheory.Krieger.TowerBase
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
import ErgodicTheory.OperatorEntropy
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

/-!
# Oseledets

Root module of the `ErgodicTheory` library: a Lean 4 + Mathlib formalization of the
**Oseledets multiplicative ergodic theorem (MET)** and a broad layer of results built on the same
cocycle/matrix infrastructure. It covers the discrete forward filtration MET
(`ErgodicTheory.oseledets_filtration`) with its additive/geometric extensions (Lyapunov spectrum,
exponent sums, exterior-power growth, trace–det identity, inverse/time-reversal, restriction,
non-ergodic and singular forms), the **two-sided splitting** (`ErgodicTheory.oseledets_splitting`),
the **continuous-flow MET** (`ErgodicTheory.oseledets_flow`), and a finite-dimensional
**quantum-information layer** (`ErgodicTheory.OperatorEntropy.*`: von Neumann and Umegaki relative
entropy, Klein/Lieb joint convexity, the CPTP data-processing inequality, CNT dynamical entropy,
and Petz's recovery/equality theorem). It also includes the entropy layer (Kolmogorov–Sinai,
Abramov–Rokhlin, Margulis–Ruelle), Krieger's generator theorem, and multifractal/smooth-dynamics
modules.

This module imports the whole development.

## Layout (principal entry points)

* `ErgodicTheory.Cocycle.Basic` — the iterated linear cocycle and its basic API.
* `ErgodicTheory.Cocycle.Norm` — measurability of the L2 operator norm and matrix inverse.
* `ErgodicTheory.Cocycle.FurstenbergKesten` — the extremal Lyapunov exponents.
* `ErgodicTheory.Ergodic.MaximalErgodic` — the maximal ergodic inequality.
* `ErgodicTheory.Ergodic.Birkhoff` — the pointwise Birkhoff ergodic theorem.
* `ErgodicTheory.Ergodic.Kingman.Core` — Kingman's subadditive ergodic theorem.
* `ErgodicTheory.Lyapunov.MeasurableSubspace` — measurably-varying subspaces.
* `ErgodicTheory.Lyapunov.*` — the Lyapunov-exponent / filtration layers and the
  final assembly chain (`OseledetsLimit`, `TopGapEnvelope`, `FiltrationFromTopGapEnvelope`, …).
* `ErgodicTheory.MultiplicativeErgodic` — the target theorem `oseledets_filtration`.
* `ErgodicTheory.Lyapunov.Extensions.*` — companion results and additive extensions (multiplicities,
  spectrum uniqueness, top-exponent norm growth, exponent sums, exterior/singular forms).
* `ErgodicTheory.TwoSided.*` — the two-sided splitting `oseledets_splitting`.
* `ErgodicTheory.Continuous.*` — the continuous-flow MET `oseledets_flow` and its special-flow
  (suspension) layer.
* `ErgodicTheory.OperatorEntropy.*` — the finite-dimensional quantum-information layer.

The target theorem `ErgodicTheory.oseledets_filtration`, the two-sided `oseledets_splitting`, the flow
`oseledets_flow`, and each quantum-information headline are proved using only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. This is **enforced**: `test/AxiomAudit.lean` is a
default `lake` build target (`defaultTargets` in `lakefile.toml`), so every `lake build` re-checks
these axiom sets via `#guard_msgs in #print axioms` and fails the build on any drift.
-/
