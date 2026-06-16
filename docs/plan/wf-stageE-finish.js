export const meta = {
  name: 'stageE-finish',
  description: 'Adversarially audit the 3 verified extension files (#8 inverse, #5 restriction, #9A non-ergodic) and implement+adversarially-verify the two hard extensions (#4 regularity/USC, #9B singular upper bounds)',
  phases: [
    { title: 'Audit-E3', detail: 'adversarial faithfulness audit of the 3 clean extension files' },
    { title: 'Implement-hard', detail: 'implement #4 regularity and #9B singular (lean-worker)' },
    { title: 'Audit-hard', detail: 'adversarial audit of #4 and #9B' },
  ],
}

const VERIFY = 'lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true -Dlinter.unusedSectionVars=true -Dlinter.unusedVariables=true -Dlinter.style.longFile=1500'

const AUDIT_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    file: { type: 'string' },
    compilesSorryFree: { type: 'boolean' },
    faithful: { type: 'boolean' },
    vacuityRisk: { type: 'string' },
    issues: { type: 'array', items: { type: 'string' } },
    verdict: { type: 'string' },
  },
  required: ['file', 'compilesSorryFree', 'faithful', 'vacuityRisk', 'issues', 'verdict'],
}

const IMPL_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    file: { type: 'string' },
    decls: { type: 'array', items: { type: 'string' } },
    sorryFree: { type: 'boolean' },
    verifierClean: { type: 'boolean' },
    scopedOut: { type: 'string' },
    notes: { type: 'string' },
  },
  required: ['file', 'decls', 'sorryFree', 'verifierClean', 'scopedOut', 'notes'],
}

const auditPrompt = (file, item, claim) => `
You are an ADVERSARIAL reviewer. A worker produced \`${file}\` realizing ${item} of the
additive-extensions plan (\`/workspaces/lean4-oseledets/docs/plan/blueprints/request-extensions.md\`).
Intended mathematical content: ${claim}

Your job is to find FLAWS, not to confirm. Specifically check:
1. **Compiles sorry-free**: run \`${VERIFY} ${file}\` — confirm zero errors, zero warnings, and grep the file for \`sorry\`/\`sorryAx\`/\`admit\`/\`native_decide\`. Report compilesSorryFree.
2. **Non-vacuity**: are the hypotheses SATISFIABLE / not contradictory? A theorem with contradictory or impossible hypotheses is vacuously true and worthless. For each main theorem, argue whether the hypotheses can actually hold (e.g. is the standing hypothesis set the genuine one used elsewhere — Ergodic T μ, det≠0, IntegrableLogNorm — not a stronger fake one?). Flag any \`True\`-like or trivially-discharged conclusion.
3. **Faithfulness**: does each theorem's STATEMENT actually express the intended math (read the claim above), with the correct quantifiers, the right limit/target, and no weakening that makes it trivial? E.g. for #8, that the singular-value reciprocity is the real σᵢ(M⁻¹)=σ_{rev i}(M)⁻¹ (or an honestly-reported weaker form), not something vacuous; for #5, that "subset" is the genuine spectrum subset; for #9A, that the limit is a genuine T-invariant function (not just restated as a constant).
4. **Definitions**: do the \`def\`s mean what they claim (e.g. the filtered sums, the invariant-subbundle structure)?

You MAY write a scratch probe file in /tmp (NOT in the repo) with \`example\`s to test non-vacuity (e.g. exhibit a concrete instance, or derive \`False\` from the hypotheses to prove vacuity). Do NOT edit the repo file. You cannot run git.

Return the structured verdict: compilesSorryFree, faithful (true only if statements genuinely capture the intended math and are non-vacuous), vacuityRisk (one line), issues (concrete problems found, empty if none), verdict (one-paragraph summary).
`

phase('Audit-E3')
const E3 = [
  { file: 'Oseledets/Lyapunov/Inverse.lean', item: 'item #8 (inverse / time reversal)',
    claim: 'For invertible M the singular values of M-inverse are the reciprocals of those of M in reversed order; the inverse-cocycle Lyapunov exponents are the negatives of the exponents in reversed order; positive vs negative spectra are tied. Honest caveat: one-sided base map gives the inverse-matrix-cocycle statement, not the full two-sided time-reversed flow.' },
  { file: 'Oseledets/Lyapunov/Restriction.lean', item: 'item #5 (restriction to an invariant subbundle)',
    claim: 'For a measurable cocycle-invariant subbundle W, the restricted Lyapunov spectrum is a subset (sub-multiset with multiplicity / interlacing) of the ambient spectrum, a.e. The full restricted Oseledets filtration may be honestly scoped out if MeasurableSubspace ⊓-closure is unavailable.' },
  { file: 'Oseledets/Lyapunov/NonErgodic.lean', item: 'item #9A (non-ergodic version)',
    claim: 'Without ergodicity (MeasurePreserving only), the partial sums Γ_k and the full spectrum exist as T-invariant measurable (integrable) FUNCTIONS (= conditional expectation on the invariant σ-algebra), via the non-ergodic Kingman theorem; the ergodic constants are the special case.' },
]
const e3audits = await parallel(E3.map(e => () =>
  agent(auditPrompt(e.file, e.item, e.claim),
    { agentType: 'mathematician', model: 'opus', phase: 'Audit-E3', schema: AUDIT_SCHEMA,
      label: `audit:${e.file.split('/').pop()}` })))

const NOGIT = 'You cannot run git (blocked). Do NOT edit Oseledets.lean or AxiomAudit.lean (the orchestrator wires imports). `omit ... in` goes BEFORE the docstring, and omit ALL unused section variables. Sorry-free: NEVER use sorry/admit — if you cannot prove something, do not state it (scope it out and report).'

const HARD = [
  { key: '#4', file: 'Oseledets/Lyapunov/Regularity.lean',
    impl: `Implement \`Oseledets/Lyapunov/Regularity.lean\` realizing item #4 (regularity of exponents in the generator — the HIGHEST-VALUE, hardest item). Read blueprint section "## 4" (it is detailed and precise) and "## 0". Build on committed files: Spectrum.lean (exponents, topExponent), ExponentSums.lean (gammaK, sumPosExp, gammaK_eq_sum_top_exponents), DetIdentity.lean (sumAllExp_eq_integral_log_abs_det ⇒ Γ_d continuous), OseledetsLimit.lean (Sprod, integrable_logSprod, the Fekete/subadditive structure, logSprod bounds), Ergodic/Kingman.lean (the lim=inf Fekete fact, Subadditive API).
    DELIVER, strongest-provable-first, ALL sorry-free:
    - \`GammaK_eq_iInf\` (Fekete): Γ_k = ⨅ n, (∫ log Sprod_k(n+1))/(n+1). Prove lim=inf from subadditivity of n ↦ ∫ log Sprod_k(n) (use the existing subadditive-cocycle witness + measure preservation; Mathlib Subadditive.tendsto_lim / direct monotone-ratio inf).
    - Per-n integral continuity under a CONCRETE convergence hypothesis. Start with REGIME 1 (uniform/entrywise a.e. convergence Aₘ→A with a fixed L¹-log envelope dominating ‖Aₘ‖,‖Aₘ⁻¹‖): DCT (MeasureTheory.tendsto_integral_of_dominated_convergence) ⇒ ∫ log Sprod_k(Aₘ,n) → ∫ log Sprod_k(A,n) for each fixed n.
    - \`GammaK_upperSemicontinuous\`: limsup_m Γ_k(Aₘ) ≤ Γ_k(A) (inf of continuous ⇒ USC). Hence topExponent USC and sumPosExp (= max_k Γ_k) USC.
    - \`botExp_lowerSemicontinuous\`: bottom exponent is LSC because Γ_d = ∫log|det| is continuous (linear), and λ_d = Γ_d − Γ_{d-1} (use DetIdentity).
    CAVEATS IN DOCSTRINGS (mandatory, honest): USC not continuity; individual interior exponents are differences of USC ⇒ no semicontinuity in general; bottom exp LSC; hypothesis is uniform-/L¹-log convergence with a fixed integrable envelope (pointwise alone is insufficient — DCT needs domination). If the L¹ regime (regime 2) stalls, deliver regime 1 only and report. If even regime 1's DCT stalls for full USC, deliver \`GammaK_eq_iInf\` + per-n continuity + the bottom-exp LSC and clearly scope out the USC limsup step — but do NOT sorry anything.
    ${NOGIT}
    Verify to zero warnings, sorry-free, error-free with: ${VERIFY} Oseledets/Lyapunov/Regularity.lean
    Report decls + signatures, sorryFree, verifierClean, what you scoped out (and why), notes.` },
  { key: '#9B', file: 'Oseledets/Lyapunov/Singular.lean',
    impl: `Implement \`Oseledets/Lyapunov/Singular.lean\` realizing item #9B (singular / one-sided cocycles WITHOUT the det≠0 and inverse-integrability hypotheses — possibly-singular matrix cocycles). Read blueprint section "## 9" subsection "(B)". Build on: OseledetsLimit.lean (Sprod, Sprod_submul — submultiplicativity holds with NO invertibility), Cocycle/FurstenbergKesten.lean (the FK/Kingman skeleton), Ergodic/Kingman.lean (incl. any EReal Kingman machinery).
    DELIVER (scoped, honest — ONLY one-sided UPPER bounds; NO full spectrum for singular cocycles), ALL sorry-free:
    - A top-exponent UPPER bound for a possibly-singular A using ONLY \`hint : IntegrableLogNorm A μ\` (NO hint', NO det≠0): e.g. \`∀ᵐ x, limsup (fun n => (n:ℝ)⁻¹ * Real.log ‖cocycle A T n x‖) ≤ λ₁\` where λ₁ is the (forward) top Lyapunov value (Furstenberg–Kesten top, which only needs forward integrability + subadditivity). Use posLog / handle ‖·‖ possibly small; the subadditive cocycle log⁺‖A⁽ⁿ⁾‖ gives Kingman's upper conclusion.
    - Optionally a top-k volume UPPER bound via Sprod_submul (still no invertibility) if cheap.
    DOCSTRING CAVEATS (mandatory): one-sided UPPER statements only; no filtration, no exact exponents, no lower bound for singular cocycles; the limit may live in [-∞,∞); ergodicity (or non-ergodic Kingman) still used for the a.e.-constant/invariant value. Be explicit that this DROPS det≠0 and hint'.
    If the EReal-valued / log 0 = -∞ handling proves too hard, deliver the cleanest upper bound you can prove sorry-free (even if under a mild extra hypothesis like ‖cocycle‖ ≥ 1 eventually, clearly stated) and scope out the rest. Do NOT sorry.
    ${NOGIT}
    Verify to zero warnings, sorry-free, error-free with: ${VERIFY} Oseledets/Lyapunov/Singular.lean
    Report decls + signatures, sorryFree, verifierClean, what you scoped out (and why), notes.` },
]

const hardResults = await pipeline(HARD,
  h => agent(h.impl, { agentType: 'lean-worker', model: 'opus', phase: 'Implement-hard', schema: IMPL_SCHEMA, label: `impl:${h.key}` }),
  (impl, h) => impl == null ? null :
    agent(auditPrompt(h.file, `item ${h.key}`,
      h.key === '#4'
        ? 'Upper-semicontinuity of the top exponent / top-k partial sums / positive-exponent sum in the generator (USC, NOT continuity), bottom exponent LSC, Fekete Γ_k=inf; honest caveats about non-continuity and the convergence hypothesis.'
        : 'One-sided UPPER bounds on the top exponent (and top-k volume) for possibly-singular cocycles WITHOUT det≠0 / inverse-integrability; honest caveat that only upper bounds hold, no full spectrum.'),
      { agentType: 'mathematician', model: 'opus', phase: 'Audit-hard', schema: AUDIT_SCHEMA, label: `audit:${h.key}` })
      .then(a => ({ key: h.key, file: h.file, impl, audit: a })))

log(`E3 audits: ${e3audits.filter(Boolean).filter(a => a.faithful).length}/${E3.length} faithful; hard: ${hardResults.filter(Boolean).length}/${HARD.length} implemented`)
return { e3audits, hardResults }
