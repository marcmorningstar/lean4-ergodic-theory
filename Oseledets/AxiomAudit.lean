/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.MultiplicativeErgodic
import Oseledets.Lyapunov.Corollaries
import Oseledets.Lyapunov.Spectrum
import Oseledets.Lyapunov.ExponentSums
import Oseledets.Lyapunov.ExteriorCocycle
import Oseledets.Lyapunov.DetIdentity
import Oseledets.Lyapunov.Inverse
import Oseledets.Lyapunov.Restriction
import Oseledets.Lyapunov.NonErgodic
import Oseledets.Lyapunov.Regularity
import Oseledets.Lyapunov.Singular
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

-- Additive extensions (request_prompt.md): the full spectrum object (item 6).

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

-- Non-ergodic version (item 9A).

/-- info: 'Oseledets.tendsto_GammaK_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.tendsto_GammaK_nonergodic

/-- info: 'Oseledets.exists_exponents_nonergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_exponents_nonergodic

-- Regularity in the generator: Fekete inf + USC/LSC (item 4).

/-- info: 'Oseledets.gammaK_eq_GammaKInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.gammaK_eq_GammaKInf

/-- info: 'Oseledets.GammaK_eq_iInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.GammaK_eq_iInf

/-- info: 'Oseledets.GammaK_upperSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.GammaK_upperSemicontinuous

/-- info: 'Oseledets.topExponent_upperSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.topExponent_upperSemicontinuous

/-- info: 'Oseledets.botExp_lowerSemicontinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.botExp_lowerSemicontinuous

-- Singular / one-sided upper bounds without invertibility (item 9B).

/-- info: 'Oseledets.limsup_logNorm_le_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.limsup_logNorm_le_top

/-- info: 'Oseledets.limsup_logSprod_le_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.limsup_logSprod_le_top

-- Two-sided splitting, Phase 0 (backward generator / cocycle infrastructure).

/-- info: 'Oseledets.cocycle_backwardGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.cocycle_backwardGen

/-- info: 'Oseledets.exists_conull_biinvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.exists_conull_biinvariant

-- Two-sided splitting, P1 (forward dimension formula) and P7 (intersection measurability).

/-- info: 'Oseledets.ae_finrank_Vslow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.ae_finrank_Vslow

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
