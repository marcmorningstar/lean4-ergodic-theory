/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.MultiplicativeErgodic
import Oseledets.Lyapunov.Extensions.Corollaries
import Oseledets.Lyapunov.Extensions.Spectrum
import Oseledets.Lyapunov.Extensions.ExponentSums
import Oseledets.Lyapunov.Extensions.ExteriorCocycle
import Oseledets.Lyapunov.Extensions.DetIdentity
import Oseledets.Lyapunov.Extensions.Inverse
import Oseledets.Lyapunov.Extensions.Restriction
import Oseledets.Lyapunov.Extensions.NonErgodic
import Oseledets.Lyapunov.Extensions.Regularity
import Oseledets.Lyapunov.Extensions.Singular
import Oseledets.Lyapunov.Extensions.SingularExponent
import Oseledets.Lyapunov.Extensions.SingularExponentBounds
import Oseledets.Lyapunov.Extensions.SingularExponentTop
import Oseledets.Lyapunov.Extensions.SingularDet
import Oseledets.Lyapunov.Extensions.SingularDetGrowth
import Oseledets.Lyapunov.Extensions.SingularExponentGenLog
import Oseledets.Lyapunov.Extensions.SingularKernelStratum
import Oseledets.Lyapunov.Extensions.SingularRank
import Oseledets.Lyapunov.Extensions.SingularKernelSubmodule
import Oseledets.Lyapunov.Extensions.SingularEventualKernel
import Oseledets.Lyapunov.Extensions.SingularKernelEquivariant
import Oseledets.Lyapunov.Extensions.SingularRankMeasurable
import Oseledets.Lyapunov.Extensions.SingularRankMeasurable2
import Oseledets.Lyapunov.Extensions.SingularRankMinor
import Oseledets.Lyapunov.Extensions.SingularDimMeasurable
import Oseledets.Lyapunov.Extensions.SingularKernelMeasurableGraph
import Oseledets.Lyapunov.Extensions.SingularKernelProjector
import Oseledets.Lyapunov.Extensions.SingularEventualKernelProjector
import Oseledets.Lyapunov.Extensions.SingularSublevelProjector
import Oseledets.Lyapunov.Extensions.SingularSublevelEventual
import Oseledets.Lyapunov.Extensions.SingularSubspaceDist
import Oseledets.Lyapunov.Extensions.SingularPerDirectionExponent
import Oseledets.Lyapunov.Extensions.SingularSpectralValues
import Oseledets.Lyapunov.Extensions.SingularSpectrumConstant
import Oseledets.Lyapunov.Extensions.SingularSlowSpace
import Oseledets.Lyapunov.Extensions.SingularBandConverge
import Oseledets.Lyapunov.Extensions.SingularSlowSpaceUnconditional
import Oseledets.Lyapunov.Extensions.SingularLambdaBarFiltration
import Oseledets.Lyapunov.Extensions.SingularLambdaBarMeasurable
import Oseledets.Lyapunov.Extensions.ConstantCocycle
import Oseledets.TwoSided.Invertible
import Oseledets.TwoSided.SpectralRank
import Oseledets.TwoSided.MeasurableInf
import Oseledets.TwoSided.StrongExport
import Oseledets.TwoSided.KingmanMeans
import Oseledets.TwoSided.Reflection
import Oseledets.TwoSided.RestrictedCocycle
import Oseledets.TwoSided.RestrictedExponent
import Oseledets.TwoSided.Transversality
import Oseledets.TwoSided.SplittingAssembly
import Oseledets.Continuous.Flow
import Oseledets.Continuous.Reduction
import Oseledets.Continuous.BetweenTimes
import Oseledets.Continuous.Equivariance
import Oseledets.Continuous.MultiplicativeErgodicFlow
import Oseledets.Continuous.Suspension
import Oseledets.Continuous.SuspensionMeasure
import Oseledets.Continuous.SuspensionSpace
import Oseledets.Continuous.SuspensionFlow
import Oseledets.Continuous.SuspensionFlowMP
import Oseledets.Continuous.ReturnTimeExponent
import Oseledets.Continuous.ReturnTimeTopExponent
import Oseledets.Continuous.SuspensionCocycle
import Oseledets.Continuous.SuspensionLapCount
import Oseledets.Continuous.SuspensionFlowCocycle
import Oseledets.Continuous.SuspensionFlowCocycleMul
import Oseledets.Continuous.SuspensionCoverCocycle
import Oseledets.Continuous.SuspensionCoverFlow
import Oseledets.Continuous.SuspensionDescent
import Oseledets.Continuous.SuspensionNlap
import Oseledets.Continuous.SuspensionFlowExponent
import Oseledets.Continuous.SuspensionBetweenReturns
import Oseledets.Continuous.SuspensionFullTimeExponent
import Oseledets.Continuous.SuspensionBddRoofExponent
import Oseledets.Continuous.SuspensionMeasureTransfer
import Oseledets.Continuous.SuspensionDisintegration
import Oseledets.Continuous.SuspensionGrowthDescent
import Oseledets.Continuous.SuspensionExponentDescent
import Oseledets.Continuous.SuspensionSpaceExponent
import Oseledets.Continuous.SuspensionSpaceExponentValue
import Oseledets.Continuous.SuspensionQuotientImage
import Oseledets.Continuous.SuspensionFlowExponentValue
import Oseledets.Continuous.SuspensionReturnTimeMeasurable
import Oseledets.Continuous.SuspensionExponentSetEquiv
import Oseledets.Continuous.SuspensionExponentSetMeasurable
import Oseledets.Continuous.SuspensionFlowExponentFinal
import Oseledets.Smooth.DerivativeCocycle
import Oseledets.Examples.Elementary
import Oseledets.Entropy.Partition
import Oseledets.Entropy.Join
import Oseledets.Entropy.Subadditive
import Oseledets.Entropy.Subadditive2
import Oseledets.Entropy.Fekete
import Oseledets.Entropy.KSEntropy
import Oseledets.Entropy.KSEntropyBounds
import Oseledets.Entropy.KSEntropySystem
import Oseledets.Entropy.KSEntropyProps
import Oseledets.Entropy.KSEntropyJoin
import Oseledets.Entropy.KSEntropyMono
import Oseledets.Entropy.MargulisRuelleAbstract
import Oseledets.Entropy.MargulisRuelleSharpened
import Oseledets.MeasureTheory.CoveringFromVolume
import Oseledets.MeasureTheory.AnalyticUniversallyMeasurable
import Oseledets.Entropy.Ruelle.Count
import Oseledets.Entropy.Ruelle.SharpCovering
import Oseledets.Entropy.Ruelle.MargulisRuelleSharp
import Oseledets.Singular.SingularFiltrationMeasurable
import Oseledets.Fourier.Torus2
import Oseledets.Lyapunov.Extensions.ConstantCocycleSpectralRadius
import Oseledets.Lyapunov.Extensions.SingularStratumExponent
import Oseledets.Continuous.SuspensionPartialSumExponent
import Oseledets.Examples.RuelleDoubling
import Oseledets.Examples.CatMapOrbit
import Oseledets.Examples.CatMapToral
import Oseledets.Examples.Rokhlin.AbstractEqui
import Oseledets.Examples.Rokhlin.DoublingCrux
import Oseledets.Examples.Rokhlin.DoublingEquality
import Oseledets.Entropy.CondChainRule
import Oseledets.Entropy.CondPullback
import Oseledets.Entropy.CondJointPullback
import Oseledets.Entropy.CondMono
import Oseledets.Entropy.CondEntropyContinuous
import Oseledets.Entropy.CondKSEntropySystem
import Oseledets.Entropy.FactorEntropy
import Oseledets.Entropy.FactorGeneratorSaturate
import Oseledets.Entropy.CondGivenPartitionBridge
import Oseledets.Entropy.AbramovRokhlin
import Oseledets.Entropy.CondKSMovingLimit
import Oseledets.Entropy.AbramovRokhlinGenerator

/-!
# Axiom audit

A guarded audit that the target theorem `Oseledets.oseledets_filtration` and its companion
corollaries depend only on Lean/Mathlib's three standard axioms `propext`, `Classical.choice`,
`Quot.sound` — in particular on no `sorryAx` and no extra axioms.

Each `#guard_msgs in #print axioms` block below compares the declaration's axiom set against
the expected `[propext, Classical.choice, Quot.sound]` and **fails the build if it ever
differs**, so this module is a continuously-checked regression test rather than an
informational dump (it produces no output on success).
-/

/-- info: 'Oseledets.oseledets_filtration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration

/-- info: 'Oseledets.oseledets_filtration'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration'

/-- info: 'Oseledets.oseledets_top_exponent_eq_furstenbergKesten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_top_exponent_eq_furstenbergKesten

/-- info: 'Oseledets.oseledets_filtration_with_multiplicities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration_with_multiplicities

/-- info: 'Oseledets.IsOseledetsFiltration.ae_mem_iff_limsup_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.ae_mem_iff_limsup_le

/-- info: 'Oseledets.IsOseledetsFiltration.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.unique

/-- info: 'Oseledets.IsOseledetsFiltration.tendsto_log_opNorm_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.tendsto_log_opNorm_cocycle

/-- info: 'Oseledets.IsOseledetsFiltration.exists_finrank_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.exists_finrank_ae_eq

/-- info: 'Oseledets.IsOseledetsFiltration.exists_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.exists_multiplicity

/-- info: 'Oseledets.IsOseledetsFiltration.k_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.k_pos

-- Additive extensions: the full Lyapunov spectrum object.

/-- info: 'Oseledets.exponents_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exponents_antitone

/-- info: 'Oseledets.exponents_tendsto_log_singularValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exponents_tendsto_log_singularValue

/-- info: 'Oseledets.exp_exponents_eq_eigenvalues₀_oseledetsLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exp_exponents_eq_eigenvalues₀_oseledetsLimit

-- Exponent sums, sign/vanishing, and the top-k telescoping (items 1, 3).

/-- info: 'Oseledets.sumPosExp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumPosExp_nonneg

/-- info: 'Oseledets.sumPosExp_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumPosExp_eq_zero_iff

/-- info: 'Oseledets.sumPosExp_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumPosExp_pos_iff

/-- info: 'Oseledets.sumNegExp_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumNegExp_nonpos

/-- info: 'Oseledets.sumNegExp_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumNegExp_eq_zero_iff

/-- info: 'Oseledets.sumNegExp_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumNegExp_neg_iff

/-- info: 'Oseledets.gammaK_eq_sum_top_exponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.gammaK_eq_sum_top_exponents

-- Exterior/wedge growth (item 2) and the trace/determinant identity (item 7).

/-- info: 'Oseledets.cocycle_extGen_eq_compound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycle_extGen_eq_compound

/-- info: 'Oseledets.tendsto_log_opNorm_compound_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_log_opNorm_compound_cocycle

/-- info: 'Oseledets.sumPosExp_eq_gammaK_card_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumPosExp_eq_gammaK_card_pos

/-- info: 'Oseledets.sumAllExp_eq_integral_log_abs_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sumAllExp_eq_integral_log_abs_det

/-- info: 'Oseledets.tendsto_log_abs_det_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_log_abs_det_cocycle

/-- info: 'Oseledets.tendsto_abs_det_cocycle_atTop_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_abs_det_cocycle_atTop_zero

-- Inverse / time reversal (item 8).

/-- info: 'Oseledets.singularValues_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.singularValues_inv

/-- info: 'Oseledets.tendsto_log_singularValue_inv_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_log_singularValue_inv_cocycle

/-- info: 'Oseledets.topExponent_inv_eq_neg_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.topExponent_inv_eq_neg_bot

-- Restriction to an invariant subbundle (item 5).

/-- info: 'Oseledets.restrictedSpectrum_subset_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restrictedSpectrum_subset_ae

/-- info: 'Oseledets.restricted_multiplicity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_multiplicity_le

/-- info: 'Oseledets.restricted_finrank_invariant_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_finrank_invariant_ae

-- Restriction Stage (ii): the full restricted (strict) Oseledets filtration (item 5, deferred part).

/-- info: 'Oseledets.restricted_inf_measurableSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_inf_measurableSubspace

/-- info: 'Oseledets.restricted_inf_witness_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_inf_witness_equivariant

/-- info: 'Oseledets.restricted_inf_witness_finrank_invariant_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_inf_witness_finrank_invariant_ae

/-- info: 'Oseledets.restricted_inf_finrank_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_inf_finrank_ae_eq

/-- info: 'Oseledets.restricted_flag_structure_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_flag_structure_ae

/-- info: 'Oseledets.restricted_strict_filtration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_strict_filtration

-- Non-ergodic version (item 9A).

/-- info: 'Oseledets.tendsto_gammaK_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_gammaK_nonergodic

/-- info: 'Oseledets.exists_exponents_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_exponents_nonergodic

/-- info: 'Oseledets.exists_sumPosExp_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_sumPosExp_nonergodic

-- Regularity in the generator: Fekete inf + USC/LSC (item 4).

/-- info: 'Oseledets.gammaK_eq_gammaKInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.gammaK_eq_gammaKInf

/-- info: 'Oseledets.gammaK_eq_iInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.gammaK_eq_iInf

/-- info: 'Oseledets.gammaK_upperSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.gammaK_upperSemicontinuous

/-- info: 'Oseledets.topExponent_upperSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.topExponent_upperSemicontinuous

/-- info: 'Oseledets.botExp_lowerSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.botExp_lowerSemicontinuous

/-- info: 'Oseledets.botExp_eq_exponents_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.botExp_eq_exponents_last

-- Regularity regime 2: a.e.-convergence + uniform integrability (Vitali) continuity (item 4, deferred part).

/-- info: 'Oseledets.ae_tendsto_logSprod_of_ae_tendsto_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_tendsto_logSprod_of_ae_tendsto_generator

/-- info: 'Oseledets.tendsto_integral_logSprod_of_unifIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_integral_logSprod_of_unifIntegrable

/-- info: 'Oseledets.tendsto_integral_logSprod_of_ae_unifIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_integral_logSprod_of_ae_unifIntegrable

/-- info: 'Oseledets.gammaK_upperSemicontinuous_of_ae_unifIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.gammaK_upperSemicontinuous_of_ae_unifIntegrable

-- Singular / one-sided upper bounds without invertibility (item 9B).

/-- info: 'Oseledets.limsup_logNorm_le_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.limsup_logNorm_le_top

/-- info: 'Oseledets.limsup_logSprod_le_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.limsup_logSprod_le_top

-- Singular / one-sided: EReal lift of the log⁺ limits + the limsup = exponent sharpening (item 9B).

/-- info: 'Oseledets.tendsto_top_posLogNorm_ereal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_top_posLogNorm_ereal

/-- info: 'Oseledets.limsup_eq_liminf_posLogNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.limsup_eq_liminf_posLogNorm

/-- info: 'Oseledets.limsup_logNorm_eq_top_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.limsup_logNorm_eq_top_of_pos

/-- info: 'Oseledets.tendsto_top_posLogSprod_ereal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_top_posLogSprod_ereal

/-- info: 'Oseledets.limsup_logSprod_eq_top_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.limsup_logSprod_eq_top_of_pos

-- Singular: the EReal-valued forward singular exponent γ_k (item 9B, invertibility-free).

/-- info: 'Oseledets.measurable_forwardSingularExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_forwardSingularExponent

/-- info: 'Oseledets.forwardSingularExponent_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardSingularExponent_nonneg

/-- info: 'Oseledets.forwardSingularExponent_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardSingularExponent_zero

/-- info: 'Oseledets.ae_forwardSingularExponent_eq_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_forwardSingularExponent_eq_coe

/-- info: 'Oseledets.ae_forwardSingularExponent_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_forwardSingularExponent_lt_top

/-- info: 'Oseledets.ae_forwardSingularExponent_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_forwardSingularExponent_ne_bot

-- Issue #6 (EReal exponent tie-in): the cumulative exponent γ_k is bounded by k · γ_1.

/-- info: 'Oseledets.forwardPosLogNormLimsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardPosLogNormLimsup

/-- info: 'Oseledets.forwardSingularExponent_le_natCast_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardSingularExponent_le_natCast_mul

-- Issue #6 (EReal exponent tie-in): top singular value = L2 opNorm, hence γ_1 = top exponent.

/-- info: 'Oseledets.top_singularValue_eq_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.top_singularValue_eq_opNorm

/-- info: 'Oseledets.sprod_one_eq_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sprod_one_eq_opNorm

/-- info: 'Oseledets.forwardSingularExponent_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardSingularExponent_one_eq

/-- info: 'Oseledets.ae_forwardSingularExponent_one_eq_topExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_forwardSingularExponent_one_eq_topExponent

-- Issue #6 (top cumulative exponent): the full singular product is |det|, hence γ_d via log⁺|det|.

/-- info: 'Oseledets.forwardSingularExponent_full_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardSingularExponent_full_eq

-- Issue #6 (γ_d det-growth tie): a.e. γ_d = ↑Γ_d⁺, and the genuine log⁺|det| growth when positive.

/-- info: 'Oseledets.ae_forwardSingularExponent_full_eq_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_forwardSingularExponent_full_eq_coe

/-- info: 'Oseledets.ae_forwardSingularExponent_full_eq_det_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_forwardSingularExponent_full_eq_det_growth

-- Issue #6 (genuine-log EReal exponent): the kernel/volume-collapse −∞ stratum hook (Quas/Raghunathan).

/-- info: 'Oseledets.measurable_forwardSingularExponentLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_forwardSingularExponentLog

/-- info: 'Oseledets.forwardSingularExponentLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardSingularExponentLog_le

/-- info: 'Oseledets.forwardSingularExponentLog_eq_bot_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.forwardSingularExponentLog_eq_bot_of_tendsto

-- Issue #6 (kernel stratum): the measurable −∞ volume-collapse set {x | γ_d^log = ⊥}.

/-- info: 'Oseledets.singularKernelSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.singularKernelSet

/-- info: 'Oseledets.measurableSet_singularKernelSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_singularKernelSet

/-- info: 'Oseledets.measurableSet_finiteSingularExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_finiteSingularExponent

/-- info: 'Oseledets.sprod_zero_imp_logTerm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sprod_zero_imp_logTerm_zero

/-- info: 'Oseledets.singularKernelSet_compl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.singularKernelSet_compl_eq

-- Issue #6 (rank filtration data): the cocycle rank and its non-increasing rank-drop.

/-- info: 'Oseledets.cocycleRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycleRank

/-- info: 'Oseledets.cocycleRank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycleRank_le

/-- info: 'Oseledets.cocycleRank_add_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycleRank_add_le_min

-- Issue #6 (filtration flag): the cocycle kernel submodule grows monotonically along the orbit.

/-- info: 'Oseledets.cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycleKer

/-- info: 'Oseledets.cocycleKer_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycleKer_le_add

/-- info: 'Oseledets.finrank_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.finrank_cocycleKer

/-- info: 'Oseledets.mem_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.mem_cocycleKer

-- Issue #6 (filtration flag bottom): the eventual (stabilized) cocycle kernel.

/-- info: 'Oseledets.cocycleKer_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycleKer_mono

/-- info: 'Oseledets.eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.eventualKer

/-- info: 'Oseledets.finrank_eventualKer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.finrank_eventualKer_le

-- Issue #6 (filtration flag equivariance): A_x maps the eventual kernel forward along T.

/-- info: 'Oseledets.mapsTo_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.mapsTo_cocycleKer

/-- info: 'Oseledets.eventualKer_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.eventualKer_equivariant

-- Issue #6 (measurable flag): determinantal rank measurability — the full-rank stratum.

/-- info: 'Matrix.rank_eq_card_iff_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.rank_eq_card_iff_det_ne_zero

/-- info: 'Oseledets.measurable_minor_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_minor_det

/-- info: 'Oseledets.measurableSet_cocycleRank_eq_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_cocycleRank_eq_full

-- Issue #6 (rank measurability): minor-nonsingular ⟹ rank ≥ r (easy direction) + the measurable subset.

/-- info: 'Matrix.le_rank_of_submatrix_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.le_rank_of_submatrix_det_ne_zero

/-- info: 'Oseledets.measurableSet_minors_subset_le_cocycleRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_minors_subset_le_cocycleRank

-- Issue #6 (measurable flag CLOSURE): rank = max nonsingular minor ⟹ the rank function is measurable.

/-- info: 'Matrix.le_rank_iff_exists_submatrix_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.le_rank_iff_exists_submatrix_det_ne_zero

/-- info: 'Oseledets.measurableSet_le_cocycleRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_le_cocycleRank

/-- info: 'Oseledets.measurable_cocycleRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_cocycleRank

-- Issue #6 (measurable dimension data — CLOSED): eventual rank + eventual-kernel dimension measurable.

/-- info: 'Oseledets.measurable_eventualRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_eventualRank

/-- info: 'Oseledets.eventualKerDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.eventualKerDim

/-- info: 'Oseledets.measurable_eventualKerDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_eventualKerDim

-- Issue #6 (singular kernel graph): measurable graph of the eventual-kernel subspace family.

/-- info: 'Oseledets.mem_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.mem_eventualKer

/-- info: 'Oseledets.measurable_cocycleMulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_cocycleMulVec

/-- info: 'Oseledets.measurableSet_graph_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_graph_cocycleKer

/-- info: 'Oseledets.measurableSet_graph_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_graph_eventualKer

/-- info: 'Oseledets.measurableSet_mem_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_mem_eventualKer

-- Issue #6 (singular kernel projector): Euclidean Gram spectral projector onto the cocycle kernel.

/-- info: 'Oseledets.orthProjMatrix_cocycleKerEuclid_eq_spectralProjector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.orthProjMatrix_cocycleKerEuclid_eq_spectralProjector

/-- info: 'Oseledets.measurable_orthProjMatrix_cocycleKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_orthProjMatrix_cocycleKer

-- Issue #6 (singular eventual-kernel projector): limit projector onto the eventual kernel.

/-- info: 'Oseledets.measurable_orthProjMatrix_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_orthProjMatrix_eventualKer

/-- info: 'Oseledets.measurableSubspace_eventualKer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSubspace_eventualKer

-- Issue #6 (sublevel slow-space stratum): the per-step, per-threshold Gram sublevel spectral
-- subspace (the threshold-`t` generalization of the kernel stratum), and its measurability.

/-- info: 'Oseledets.cocycleSublevelEuclid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycleSublevelEuclid

/-- info: 'Oseledets.measurableSubspace_cocycleSublevelEuclid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSubspace_cocycleSublevelEuclid

/-- info: 'Oseledets.measurableSubspace_cocycleSublevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSubspace_cocycleSublevel

-- Two-sided splitting, Phase 0 (backward generator / cocycle infrastructure).

/-- info: 'Oseledets.cocycle_backwardGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycle_backwardGen

/-- info: 'Oseledets.exists_conull_biinvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_conull_biinvariant

-- Two-sided splitting, P1 (forward dimension formula) and P7 (intersection measurability).

/-- info: 'Oseledets.ae_finrank_vslow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_finrank_vslow

/-- info: 'Oseledets.MeasurableSubspace.inf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.MeasurableSubspace.inf

/-- info: 'Oseledets.tendsto_pow_orthProj_inf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_pow_orthProj_inf

-- Two-sided splitting, P2 (strong one-sided export with the dimension formula).

/-- info: 'Oseledets.oseledets_filtration_dims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration_dims

-- Two-sided splitting, P3 (Kingman means identification — load-bearing new analytic lemma).

/-- info: 'Oseledets.tendsto_kingman_ergodic_means' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_kingman_ergodic_means

-- Two-sided splitting, P6 (exponent reflection: backward spectrum = -forward reversed).

/-- info: 'Oseledets.sum_mu0_eq_neg_sum_lam0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.sum_mu0_eq_neg_sum_lam0

/-- info: 'Oseledets.reflect_of_counting_and_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.reflect_of_counting_and_sum

/-- info: 'Oseledets.expEnum_eq_neg_rev_of_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.expEnum_eq_neg_rev_of_counting

-- Two-sided splitting, P4a (backward-orbit restricted envelope; analytic heart).

/-- info: 'Oseledets.isSubadditiveCocycle_restLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.isSubadditiveCocycle_restLog

/-- info: 'Oseledets.restLog_eq_on_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restLog_eq_on_good

/-- info: 'Oseledets.restLog_backward_kingman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restLog_backward_kingman

-- Two-sided splitting, P4b (restricted Kingman constant = λᵢ; backward envelope).

/-- info: 'Oseledets.restricted_const_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.restricted_const_eq

/-- info: 'Oseledets.ae_limsup_restricted_backward_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_limsup_restricted_backward_le

-- Two-sided splitting, P5 (transversality crux + counting bound).

/-- info: 'Oseledets.ae_crux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_crux

/-- info: 'Oseledets.ae_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_counting

/-- info: 'Oseledets.inf_eq_bot_of_neg_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.inf_eq_bot_of_neg_sum

-- Two-sided splitting, P8 (the headline theorem: invariant direct-sum decomposition).

/-- info: 'Oseledets.oseledets_splitting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_splitting

-- Continuous-flow MET, P0 (flow + cocycle reduction identity).

/-- info: 'Oseledets.MeasurePreservingFlow.natCast_eq_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.MeasurePreservingFlow.natCast_eq_iterate

/-- info: 'Oseledets.FlowCocycle.toCocycle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.FlowCocycle.toCocycle_eq

-- Continuous-flow MET, P2 (reduction to the discrete theorem at the time-1 map).

/-- info: 'Oseledets.exists_isOseledetsFiltration_timeOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_isOseledetsFiltration_timeOne

-- Continuous-flow MET, P1 (between-times sandwich: integer-time → continuous-time growth).

/-- info: 'Oseledets.ae_tendsto_flowError_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_tendsto_flowError_zero

/-- info: 'Oseledets.tendsto_log_norm_atTop_of_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_log_norm_atTop_of_discrete

-- Continuous-flow MET, P3a (flow-equivariance machinery: fixed-time sublinearity, limsup shift).

/-- info: 'Oseledets.ae_tendsto_logNorm_fixedTime_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_tendsto_logNorm_fixedTime_zero

/-- info: 'Oseledets.glim_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.glim_shift

/-- info: 'Oseledets.ae_flow_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_flow_equivariant

-- Continuous-flow MET, P3b (the headline theorem: flow-equivariant filtration, continuous-time growth).

/-- info: 'Oseledets.oseledets_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_flow

-- Issue #1: constant-cocycle Lyapunov exponents (specialization to a constant generator `A ≡ M`).

/-- info: 'Oseledets.cocycle_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycle_const

/-- info: 'Oseledets.qpow_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.qpow_const

/-- info: 'Oseledets.oseledetsLimit_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledetsLimit_const

/--
info: 'Oseledets.exp_exponents_const_eq_eigenvalues₀_absMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Oseledets.exp_exponents_const_eq_eigenvalues₀_absMatrix

/-- info: 'Oseledets.exponents_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exponents_const

-- Issue #2: derivative (tangent) cocycle of a differentiable self-map.

/-- info: 'Oseledets.chainRule_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.chainRule_cocycle

/--
info: 'Oseledets.oseledets_filtration_derivativeCocycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration_derivativeCocycle

-- Issue #3: concrete worked examples (doubling map, irrational rotation, Arnold cat-map matrix).

/-- info: 'Oseledets.doublingMap_topExponent_eq_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.doublingMap_topExponent_eq_log_two

/-- info: 'Oseledets.irrationalRotation_exponents_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.irrationalRotation_exponents_eq_zero

/-- info: 'Oseledets.catMapMatrix_exponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.catMapMatrix_exponents

/-- info: 'Oseledets.catMapMatrix_exponents_sum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.catMapMatrix_exponents_sum_eq_zero

-- Issue #4 (foundation): Shannon entropy of a finite measurable partition (toward KS entropy).

/-- info: 'Oseledets.Entropy.entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_nonneg

/-- info: 'Oseledets.Entropy.entropy_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_le_log_card

/--
info: 'Oseledets.Entropy.MeasurePartition.sum_toReal_measure_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Oseledets.Entropy.MeasurePartition.sum_toReal_measure_eq_one

/-- info: 'Oseledets.Entropy.entropy_le_log_card_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_le_log_card_partition

/-- info: 'Oseledets.isAddFundamentalDomain_suspensionDomain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.isAddFundamentalDomain_suspensionDomain

/-- info: 'Oseledets.suspension_exists_unique_act_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspension_exists_unique_act_mem

/-- info: 'Oseledets.exists_unique_lt_of_strictMono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_unique_lt_of_strictMono

/-- info: 'Oseledets.roofSum_add_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.roofSum_add_one

-- Issue #5 (measure layer): the suspension invariant-measure foundation.

/-- info: 'Oseledets.measurePreserving_shear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurePreserving_shear

/-- info: 'Oseledets.measurePreserving_suspensionGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurePreserving_suspensionGen

/-- info: 'Oseledets.measure_suspensionDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measure_suspensionDomain

-- Issue #4 (entropy layer): T-invariance of partition entropy (toward the Fekete h(α,T) limit).

/-- info: 'Oseledets.Entropy.entropy_comp_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_comp_preimage

-- Issue #4 (entropy subadditivity): H(α∨β) ≤ H(α)+H(β) — the gate to the Fekete h(α,T) limit.

/-- info: 'Oseledets.Entropy.MeasurePartition.measure_eq_sum_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.MeasurePartition.measure_eq_sum_inter

/-- info: 'Oseledets.Entropy.sum_negMulLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.sum_negMulLog_le

/-- info: 'Oseledets.Entropy.entropy_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_join_le

-- Issue #4 (pullback partition): the T⁻¹ partition and the T-invariance of its entropy.

/-- info: 'Oseledets.Entropy.entropy_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_pullback

-- Issue #4 (Fekete limit): the flat Fin-indexed KS join, its subadditive entropy sequence, and
-- the Kolmogorov–Sinai entropy as the Fekete limit.

/-- info: 'Oseledets.Entropy.ksJoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksJoin

/-- info: 'Oseledets.Entropy.ksEntropySeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropySeq

/-- info: 'Oseledets.Entropy.ksEntropySeq_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropySeq_subadditive

/-- info: 'Oseledets.Entropy.ksEntropyPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropyPartition

/-- info: 'Oseledets.Entropy.tendsto_ksEntropySeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.tendsto_ksEntropySeq

-- Issue #4 (KS entropy bounds): h(α,T) ≥ 0 and h(α,T) ≤ H(α).

/-- info: 'Oseledets.Entropy.ksEntropySeq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropySeq_one

/-- info: 'Oseledets.Entropy.ksEntropySeq_le_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropySeq_le_nsmul

/-- info: 'Oseledets.Entropy.ksEntropyPartition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropyPartition_nonneg

/-- info: 'Oseledets.Entropy.ksEntropyPartition_le_entropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropyPartition_le_entropy

-- Issue #4 (KS entropy of the system): h(T) = ⨆_α h(α,T) as an EReal supremum.

/-- info: 'Oseledets.Entropy.ksEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropy

/-- info: 'Oseledets.Entropy.le_ksEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.le_ksEntropy

/-- info: 'Oseledets.Entropy.ksEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropy_nonneg

-- Issue #4 (KS entropy property): the Fekete inf bound h(α,T) ≤ ksEntropySeq n / n.

/-- info: 'Oseledets.Entropy.bddBelow_ksEntropySeq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.bddBelow_ksEntropySeq_div

/-- info: 'Oseledets.Entropy.ksEntropyPartition_le_ksEntropySeq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropyPartition_le_ksEntropySeq_div

-- Issue #4 (dynamical subadditivity): h(α∨β,T) ≤ h(α,T) + h(β,T).

/-- info: 'Oseledets.Entropy.joinPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.joinPartition

/-- info: 'Oseledets.Entropy.ksEntropySeq_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropySeq_join_le

/-- info: 'Oseledets.Entropy.ksEntropyPartition_join_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropyPartition_join_le

-- Issue #4 (entropy refinement-monotonicity): h(α,T) ≤ h(α∨β,T).

/-- info: 'Oseledets.Entropy.entropy_le_entropy_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_le_entropy_join

/-- info: 'Oseledets.Entropy.ksEntropyPartition_le_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.ksEntropyPartition_le_join

-- Issue #5 (quotient layer): the suspension space and its invariant probability measure.

/-- info: 'Oseledets.measurable_suspensionMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_suspensionMk

/-- info: 'Oseledets.suspensionMeasure₀_univ_eq_measure_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionMeasure₀_univ_eq_measure_box

/-- info: 'Oseledets.suspensionMeasure_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionMeasure_univ

/-- info: 'Oseledets.isProbabilityMeasure_suspensionMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.isProbabilityMeasure_suspensionMeasure

-- Issue #5 (flow layer): the suspension flow ζ_t (descent of the vertical translation) on Xᵗ.

/-- info: 'Oseledets.measurePreserving_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurePreserving_translate

/-- info: 'Oseledets.suspensionFlowMap_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionFlowMap_zero

/-- info: 'Oseledets.suspensionFlowMap_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionFlowMap_add

/-- info: 'Oseledets.measurable_suspensionFlowMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_suspensionFlowMap

-- Issue #5 (flow measure-preservation): the suspension flow is a measure-preserving flow.

/-- info: 'Oseledets.measurePreserving_suspensionFlowMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurePreserving_suspensionFlowMap

/-- info: 'Oseledets.suspensionFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionFlow

-- Issue #5 (transfer core): the return-time exponent log‖A⁽ⁿ⁾‖ / τ⁽ⁿ⁾ → λ / ∫τ.

/-- info: 'Oseledets.tendsto_div_of_tendsto_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_div_of_tendsto_div

/-- info: 'Oseledets.roofSum_natCast_eq_birkhoffSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.roofSum_natCast_eq_birkhoffSum

/-- info: 'Oseledets.tendsto_roofAverage_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_roofAverage_ae

/-- info: 'Oseledets.integral_roof_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.integral_roof_pos

/-- info: 'Oseledets.returnTime_tendsto_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.returnTime_tendsto_exponent

-- Issue #5 (top-exponent transfer): the MET top exponent transfers as λ_top / ∫τ.

/-- info: 'Oseledets.IsOseledetsFiltration.returnTime_tendsto_topExponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.returnTime_tendsto_topExponent

-- Issue #5 (flow cocycle core): the return-indexed suspension cocycle and its multiplicativity.

/-- info: 'Oseledets.suspensionCocycleReturn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionCocycleReturn_add

/-- info: 'Oseledets.measurable_suspensionCocycleReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_suspensionCocycleReturn

/-- info: 'Oseledets.returnTime_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.returnTime_add

/-- info: 'Oseledets.suspensionCocycleReturn_returnTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionCocycleReturn_returnTime

-- Issue #5 (special-flow lap counter): return times diverge, and the first-passage lap count N(t,x).

/-- info: 'Oseledets.returnTime_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.returnTime_strictMono

/-- info: 'Oseledets.returnTime_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.returnTime_tendsto_atTop

/-- info: 'Oseledets.lapCount_returnTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_returnTime_le

/-- info: 'Oseledets.lapCount_lt_returnTime_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_lt_returnTime_succ

-- Issue #5 (flow cocycle on the section): Ψ_t = A^(lapCount t) and the return identity.

/-- info: 'Oseledets.flowCocycleSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.flowCocycleSection

/-- info: 'Oseledets.lapCount_returnTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_returnTime_eq

/-- info: 'Oseledets.flowCocycleSection_returnTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.flowCocycleSection_returnTime

/-- info: 'Oseledets.flowCocycleSection_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.flowCocycleSection_zero

-- Issue #5 (flow cocycle multiplicativity): the base-cocycle identity at return times.

/-- info: 'Oseledets.flowCocycleSection_returnTime_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.flowCocycleSection_returnTime_add

/-- info: 'Oseledets.flowCocycleSection_returnTime_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.flowCocycleSection_returnTime_succ

-- Issue #5 (cover extension): lapCount monotone + the off-section lap-count additivity.

/-- info: 'Oseledets.lapCount_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_mono

/-- info: 'Oseledets.lapCount_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_unique

/-- info: 'Oseledets.lapCount_returnTime_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_returnTime_add

-- Issue #5 (cover flow cocycle): the X×ℝ cover cocycle + its section return-boundary identity.

/-- info: 'Oseledets.coverCocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle

/-- info: 'Oseledets.coverCocycle_section_returnTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_section_returnTime

-- Issue #5 (descent): the one-lap height reduction and its operator-norm bound.

/-- info: 'Oseledets.coverCocycle_one_lap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_one_lap

/-- info: 'Oseledets.coverCocycle_one_lap_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_one_lap_opNorm_le

-- Issue #5 (flow exponent bridge): cover-cocycle norm = base norm at return times.

/-- info: 'Oseledets.coverCocycle_returnTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_returnTime_eq

/-- info: 'Oseledets.coverCocycle_returnTime_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_returnTime_opNorm_le

-- Issue #5 (HEADLINE): the special-flow Lyapunov exponent along returns = λ_base / ∫τ.

/-- info: 'Oseledets.coverCocycle_returnTime_tendsto_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_returnTime_tendsto_exponent

/-- info: 'Oseledets.IsOseledetsFiltration.coverCocycle_returnTime_tendsto_topExponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.coverCocycle_returnTime_tendsto_topExponent

-- Issue #5 (special-flow structure): the flow cocycle is constant = A^(n) between returns.

/-- info: 'Oseledets.coverCocycle_const_between_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_const_between_returns

-- Issue #5 (full-time reduction): flow-cocycle norm = base norm at the lap count + the sandwich.

/-- info: 'Oseledets.coverCocycle_norm_eq_lapCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_norm_eq_lapCount

/-- info: 'Oseledets.log_coverCocycle_div_eq_lapCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.log_coverCocycle_div_eq_lapCount

-- Issue #5 (HEADLINE closure): full-time special-flow exponent = λ_base/∫τ under a bounded roof.

/-- info: 'Oseledets.lapCount_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_tendsto_atTop

/-- info: 'Oseledets.lapCount_returnTime_div_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lapCount_returnTime_div_tendsto_one

/-- info: 'Oseledets.coverCocycle_tendsto_exponent_of_bddRoof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_tendsto_exponent_of_bddRoof

-- Issue #5 (suspension bridge): the cross-section embedding + gluing + section-image exponent.

/-- info: 'Oseledets.suspensionMk_roof_eq_section_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionMk_roof_eq_section_base

/-- info: 'Oseledets.measurable_suspensionSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_suspensionSection

/-- info: 'Oseledets.coverCocycle_tendsto_exponent_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_tendsto_exponent_section

-- Issue #5 (suspension disintegration): base-a.e. → μ̂-a.e. transfer to the suspension measure.

/-- info: 'Oseledets.suspensionMeasure_ae_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionMeasure_ae_iff

/-- info: 'Oseledets.ae_suspensionMeasure_of_ae_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_of_ae_restrict

/-- info: 'Oseledets.ae_restrict_suspensionDomain_of_ae_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_restrict_suspensionDomain_of_ae_base

/-- info: 'Oseledets.ae_suspensionMeasure_of_ae_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_of_ae_base

/-- info: 'Oseledets.ae_suspensionMeasure_section_exponent_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_section_exponent_set

-- Issue #5 (suspension growth-rate descent): orbit re-basing + two-sided bounded op-norm discrepancy.

/-- info: 'Oseledets.coverCocycle_suspensionAct_rebasing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_suspensionAct_rebasing

/-- info: 'Oseledets.coverCocycle_suspensionAct_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_suspensionAct_opNorm_le

/-- info: 'Oseledets.coverCocycle_suspensionAct_rebasing_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_suspensionAct_rebasing_inv

/-- info: 'Oseledets.coverCocycle_suspensionAct_opNorm_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_suspensionAct_opNorm_ge

-- Issue #5 (exponent descent): orbit re-basing has bounded log-norm discrepancy ⟹ same exponent.

/-- info: 'Oseledets.norm_pos_of_isUnit_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.norm_pos_of_isUnit_det

/-- info: 'Oseledets.coverCocycle_suspensionAct_log_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_suspensionAct_log_discrepancy

/-- info: 'Oseledets.coverCocycle_suspensionAct_tendsto_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coverCocycle_suspensionAct_tendsto_exponent

-- Issue #5 (flow exponent on the space): the well-defined suspension-space flow exponent predicate.

/-- info: 'Oseledets.HasFlowExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.HasFlowExponent

/-- info: 'Oseledets.tendsto_exponent_iff_of_suspensionAct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_exponent_iff_of_suspensionAct

/-- info: 'Oseledets.hasFlowExponent_of_suspensionAct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.hasFlowExponent_of_suspensionAct

-- Issue #5 (flow exponent value): the section flow exponent + the μ̂-a.e. flow-exponent statement.

/-- info: 'Oseledets.tendsto_coverCocycle_exponent_of_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_coverCocycle_exponent_of_section

/-- info: 'Oseledets.ae_suspensionMeasure_hasFlowExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_hasFlowExponent

-- Issue #4 (Margulis–Ruelle inequality): h(T) ≤ ∑ λᵢ⁺ reduced to the geometric atom-counting bound.

/-- info: 'Oseledets.margulisRuelle_le_sumPosExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.margulisRuelle_le_sumPosExp

-- Issue #5 (quotient-image measurability): discharge the `hmeas` quotient-image hypothesis.

/-- info: 'Oseledets.suspensionActEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionActEquiv

/-- info: 'Oseledets.suspensionActEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspensionActEquiv_apply

/-- info: 'Oseledets.measurableSet_suspensionAct_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_suspensionAct_image

/-- info: 'Oseledets.preimage_image_suspensionMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.preimage_image_suspensionMk

/-- info: 'Oseledets.measurableSet_suspensionMk_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_suspensionMk_image

/-- info: 'Oseledets.measurableSet_suspensionMk_exponent_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_suspensionMk_exponent_image

-- Issue #5 (unconditional space-level exponent): `hmeas` discharged + tied to the genuine flow.

/-- info: 'Oseledets.ae_suspensionMeasure_hasFlowExponent_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_hasFlowExponent_unconditional

/-- info: 'Oseledets.ae_suspensionMeasure_hasFlowExponent_flowOrbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_hasFlowExponent_flowOrbit

-- Issue #5 (hPmeas discharged): cover-cocycle convergence-set measurability ⇒ fully unconditional
-- space-level special-flow exponent (only `Measurable A` assumed, no convergence-set hypothesis).

/-- info: 'Oseledets.measurableSet_coverCocycle_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSet_coverCocycle_exponent

/-- info: 'Oseledets.ae_suspensionMeasure_hasFlowExponent_of_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_hasFlowExponent_of_measurable

/-- info: 'Oseledets.ae_suspensionMeasure_hasFlowExponent_flowOrbit_of_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_hasFlowExponent_flowOrbit_of_measurable

-- Issue #6 (det-free singular infra): subspace-convergence tool + per-direction EReal exponent.

/-- info: 'Oseledets.cauchySeq_of_summable_subspaceDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cauchySeq_of_summable_subspaceDist

/-- info: 'Oseledets.exists_tendsto_orthProjMatrix_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_tendsto_orthProjMatrix_of_summable

/-- info: 'Oseledets.measurable_singularDirExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_singularDirExponent

/-- info: 'Oseledets.ae_singularDirExponent_eq_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_singularDirExponent_eq_coe

-- Issue #4 (honest sharpening): positive-part singular-value product identity + minimal atom-count
-- restatement of the Margulis–Ruelle reduction. The geometric `hgeo`/`hcount` input stays an explicit
-- open hypothesis (smooth-ergodic-theory wall); nothing axiomatized.

/-- info: 'Oseledets.Entropy.sum_posLog_singularValues_toEuclideanLin_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.sum_posLog_singularValues_toEuclideanLin_eq

/-- info: 'Oseledets.margulisRuelle_le_sumPosExp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.margulisRuelle_le_sumPosExp'

-- Issue #6 (det-free genuine singular Lyapunov spectrum): the −∞-aware per-direction exponent is
-- deterministically antitone + measurable + a.e. finite; cut-threshold ladder for the slow-space flag.

/-- info: 'Oseledets.singularSpectralValue_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.singularSpectralValue_antitone

/-- info: 'Oseledets.measurable_singularSpectralValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_singularSpectralValue

/-- info: 'Oseledets.ae_singularSpectralValue_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_singularSpectralValue_lt_top

/-- info: 'Oseledets.exists_cutThresholds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_cutThresholds

-- Issue #6 (genuine singular spectrum is a.e. CONSTANT, det-free) + the missing Horn singular-value
-- inequality σ_k(g∘f) ≤ σ_k(g)·‖f‖ built en route.

/-- info: 'Oseledets.singularValues_comp_le_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.singularValues_comp_le_opNorm

/-- info: 'Oseledets.singularSpectralValue_invariant_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.singularSpectralValue_invariant_ae

/-- info: 'Oseledets.ae_singularSpectralValue_eq_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_singularSpectralValue_eq_const

-- Issue #6 (singular slow-space step + structural reduction of V_j convergence to one summability input).

/-- info: 'Oseledets.measurableSubspace_vSlowSingularStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSubspace_vSlowSingularStep

/-- info: 'Oseledets.vSlowSingularStep_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.vSlowSingularStep_antitone

/-- info: 'Oseledets.tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_orthProjMatrix_vSlowSingularStep_of_tendsto_bandProjector

-- Issue #6 (det-free band route): the V_j band-increment bound with the inverse isolated to a single
-- per-step coefficient hypothesis; the complement reduction band-convergence ⇒ slow-space convergence.

/-- info: 'Oseledets.numerator_div_gap_le_detfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.numerator_div_gap_le_detfree

/-- info: 'Oseledets.tendsto_vSlowSingularStep_of_bandProjector_detfree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_vSlowSingularStep_of_bandProjector_detfree

-- Issue #6 (tempered-class V_j + the wall identity): unconditional soft-analysis core (any summable band
-- increment ⇒ V_j converges), the tempered-non-degeneracy V_j, and the proof the increment IS an aperture.

/-- info: 'Oseledets.tendsto_vSlowSingularStep_of_summable_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_vSlowSingularStep_of_summable_increment

/-- info: 'Oseledets.tendsto_vSlowSingularStep_of_tempered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_vSlowSingularStep_of_tempered

/-- info: 'Oseledets.bandProjector_increment_eq_aperture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.bandProjector_increment_eq_aperture

-- Issue #6 (algebraic forward filtration): the lambdaBar sublevel as a submodule, antitone + equivariant
-- (floored growth + the det-free HasFiniteTopGrowth finiteness hypothesis).

/-- info: 'Oseledets.lambdaBarSublevel_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lambdaBarSublevel_antitone

/-- info: 'Oseledets.lambdaBarSublevel_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lambdaBarSublevel_equivariant

-- Issue #6 (measurability reduction): {v : lambdaBar ≤ c} is a MeasurableSubspace given the projector
-- convergence — which provably reduces to the same band/aperture convergence (the pinned inverse wall).

/-- info: 'Oseledets.measurableSubspace_of_tendsto_orthProjMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSubspace_of_tendsto_orthProjMatrix

/-- info: 'Oseledets.measurableSubspace_lambdaSublevel_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurableSubspace_lambdaSublevel_of_tendsto

-- Issue #6 (migrated headline): the a.e.-measurable forward Lyapunov projector of the singular
-- MET, from the measurable graph via universal measurability of analytic sets (Lusin/Choquet).

/-- info: 'Oseledets.aemeasurable_orthProjMatrix_lambdaSublevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.aemeasurable_orthProjMatrix_lambdaSublevel

-- Issue #6 upstream candidate: every analytic set in a standard Borel space is universally
-- measurable (NullMeasurableSet for every s-finite measure), via Choquet capacitability.

/-- info: 'MeasureTheory.AnalyticSet.nullMeasurableSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MeasureTheory.AnalyticSet.nullMeasurableSet

-- Issue #4 (migrated headline): the sharp Margulis–Ruelle inequality h(T) ≤ ∑ λᵢ⁺ for a smooth
-- ergodic self-map of Euclidean space (modulo the honest non-compactness atom-count input).

/-- info: 'Oseledets.margulisRuelle_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.margulisRuelle_sharp

-- Issue #4 upstream candidate: Mañé's Lemma 12.5, the covering number bounded by Haar volume of
-- the closed thickening on Euclidean space.

/-- info: 'Metric.coveringNumber_le_addHaar_div_of_addHaar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Metric.coveringNumber_le_addHaar_div_of_addHaar_le

-- Issue #4: the sharp anisotropic one-step covering count of a linear image of a ball, by the
-- positive-part singular-value product (the geometric heart of the sharp track).

/-- info: 'Oseledets.coveringCount_image_ball_le_volProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.coveringCount_image_ball_le_volProd

-- Issue #4: the orbit growth rate (1/n) log (volProd …) → ∑ λᵢ⁺, a.e., driving the count.

/-- info: 'Oseledets.tendsto_log_volProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_log_volProd

-- MET enhancements campaign: #1-#6 closures

/-- info: 'Oseledets.topExponent_constantCocycle_eq_log_spectralRadius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.topExponent_constantCocycle_eq_log_spectralRadius

/-- info: 'Oseledets.doublingMap_sumPosExp_eq_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.doublingMap_sumPosExp_eq_log_two

/-- info: 'Oseledets.doublingMap_ksEntropyPartition_le_sumPosExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.doublingMap_ksEntropyPartition_le_sumPosExp

/--
info: 'Oseledets.singular_perDirection_exponent_eq_lambda_of_mem_stratum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Oseledets.singular_perDirection_exponent_eq_lambda_of_mem_stratum

/-- info: 'Oseledets.lambdaBar_eq_of_mem_stratum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.lambdaBar_eq_of_mem_stratum

/-- info: 'Oseledets.log_le_liminf_log_cocycle_apply_detfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.log_le_liminf_log_cocycle_apply_detfree

/-- info: 'Oseledets.CatMapToral.ergodic_catTorus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.CatMapToral.ergodic_catTorus

/-- info: 'Oseledets.CatMapToral.measurePreserving_catTorus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.CatMapToral.measurePreserving_catTorus

/-- info: 'Oseledets.CatMapToral.orbit_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.CatMapToral.orbit_infinite

/-- info: 'Oseledets.suspension_perExponent_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspension_perExponent_scaling

/-- info: 'Oseledets.suspension_gammaK_flow_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.suspension_gammaK_flow_scaling

/-- info: 'Oseledets.ae_suspensionMeasure_hasFlowExponent_extGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_suspensionMeasure_hasFlowExponent_extGen

/-- info: 'Oseledets.measurable_extGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.measurable_extGen

/-- info: 'Oseledets.Fourier.eq_zero_of_forall_char_inner_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Fourier.eq_zero_of_forall_char_inner_eq_zero

/-- info: 'Oseledets.Fourier.orthonormal_torusChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Fourier.orthonormal_torusChar

/-- info: 'Oseledets.Fourier.hasSum_sq_torusFourierCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Fourier.hasSum_sq_torusFourierCoeff

/-- info: 'Oseledets.Fourier.torusChar_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Fourier.torusChar_apply

/-- info: 'Oseledets.Examples.Rokhlin.rokhlin_equality_doublingMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Examples.Rokhlin.rokhlin_equality_doublingMap

/--
info: 'Oseledets.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Oseledets.Examples.Rokhlin.ksEntropyPartition_doublingMap_eq_log_two

/-- info: 'Oseledets.Examples.Rokhlin.volume_binJoinCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Examples.Rokhlin.volume_binJoinCell

-- Conditional / relative entropy + Abramov–Rokhlin (issue #13).

/-- info: 'Oseledets.Entropy.condEntropy_join_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.condEntropy_join_eq

/-- info: 'Oseledets.Entropy.condEntropy_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.condEntropy_pullback

/-- info: 'Oseledets.Entropy.condEntropy_comap_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.condEntropy_comap_pullback

/-- info: 'Oseledets.Entropy.condEntropy_mono_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.condEntropy_mono_of_le

/-- info: 'Oseledets.Entropy.condKsEntropy_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.condKsEntropy_bot

/-- info: 'Oseledets.Entropy.factor_relative_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.factor_relative_eq

/-- info: 'Oseledets.Entropy.abramov_rokhlin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.abramov_rokhlin

-- Issue #13 §5b: the partition-level Abramov–Rokhlin skeleton (B6a reduced to the W3 limit).

/-- info: 'Oseledets.Entropy.entropy_joinCells_of_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.entropy_joinCells_of_refines

/-- info: 'Oseledets.Entropy.abramovRokhlin_partition_of_W3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.abramovRokhlin_partition_of_W3

/-- info: 'Oseledets.Entropy.abramov_rokhlin_of_W3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.abramov_rokhlin_of_W3

/-- info: 'Oseledets.Entropy.condEntropy_tendsto_iSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.condEntropy_tendsto_iSup

/-- info: 'Oseledets.Entropy.factor_iSup_comap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.factor_iSup_comap_eq

/--
info: 'Oseledets.Entropy.condEntropyGivenPartition_eq_condEntropy_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Oseledets.Entropy.condEntropyGivenPartition_eq_condEntropy_generated

-- Issue #13: W3 DISCHARGED — the moving-index Cesàro/martingale limit (blocking + the fixed-partition
-- Lévy theorem) and the resulting UNCONDITIONAL Abramov–Rokhlin addition formula under a base generator.

/-- info: 'Oseledets.Entropy.tendsto_condEntropy_genJoin_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.tendsto_condEntropy_genJoin_div

/-- info: 'Oseledets.Entropy.tendsto_condCellSeq_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.tendsto_condCellSeq_div

/-- info: 'Oseledets.Entropy.abramovRokhlin_partition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.abramovRokhlin_partition

/-- info: 'Oseledets.Entropy.abramov_rokhlin_of_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.Entropy.abramov_rokhlin_of_generator
