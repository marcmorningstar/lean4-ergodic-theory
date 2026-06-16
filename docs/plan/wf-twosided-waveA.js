export const meta = {
  name: 'twosided-waveA',
  description: 'Two-sided splitting wave A: implement + adversarially audit the three independent phases P1 (SpectralRank), P3 (KingmanMeans), P7 (MeasurableInf)',
  phases: [
    { title: 'Implement', detail: 'P1, P3, P7 via lean-worker' },
    { title: 'Audit', detail: 'adversarial audit of each' },
  ],
}

const VERIFY = 'lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true -Dlinter.unusedSectionVars=true -Dlinter.unusedVariables=true -Dlinter.style.longFile=1500'
const BP = '/workspaces/lean4-oseledets/docs/plan/blueprints/two-sided-met.md'
const NOGIT = 'You cannot run git (blocked). Do NOT edit Oseledets.lean or AxiomAudit.lean (orchestrator wires imports). Never use sorry/admit: if you cannot prove a listed item, omit it and report the precise reason. `omit ... in` goes BEFORE the docstring; omit ALL unused section variables. Add the 4-line Mathlib copyright header + a neutral module docstring.'

const IMPL_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: { file: { type: 'string' }, decls: { type: 'array', items: { type: 'string' } },
    sorryFree: { type: 'boolean' }, verifierClean: { type: 'boolean' }, scopedOut: { type: 'string' }, notes: { type: 'string' } },
  required: ['file', 'decls', 'sorryFree', 'verifierClean', 'scopedOut', 'notes'],
}
const AUDIT_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: { file: { type: 'string' }, compilesSorryFree: { type: 'boolean' }, faithful: { type: 'boolean' },
    vacuityRisk: { type: 'string' }, issues: { type: 'array', items: { type: 'string' } }, verdict: { type: 'string' } },
  required: ['file', 'compilesSorryFree', 'faithful', 'vacuityRisk', 'issues', 'verdict'],
}

const PHASES = [
  { key: 'P1', file: 'Oseledets/TwoSided/SpectralRank.lean',
    spec: `Phase P1 (forward spectral-rank / dimension formula). Read ${BP} section "### P1" for the exact deliverables, and "## 0"/"## 2" for context. Imports: Oseledets.Lyapunov.ForwardV, Oseledets.Lyapunov.LimitEigenbasis, Oseledets.Lyapunov.OseledetsLimit, Mathlib.LinearAlgebra.Lagrange. Deliver: cfc_apply_of_eigenvector (per-point CFC on an eigenvector via Lagrange interpolation on the finite spectrum; no measurability); finrank_range_of_orthonormal_diag (rank of a diagonalised projection = count of unit eigenvalues); ae_finrank_Vslow (the validated a.e. statement: finrank (Vslow A T (exp t) x) = card {j in range d | lam0 j <= t}) via limitEigenbasis_eigenpair_exp + a.e. lamSing = lam0 + exp-monotonicity. Match real signatures from ForwardV/LimitEigenbasis/OseledetsLimit. Fallback for finrank if CFC-eigenvector fights the API: compute via trace of the projection (documented in the blueprint).` },
  { key: 'P3', file: 'Oseledets/TwoSided/KingmanMeans.lean',
    spec: `Phase P3 (Kingman means identification — NEW analytic content, the load-bearing new lemma). Read ${BP} section "### P3" for the exact statement + the two-direction proof plan. Imports: Oseledets.Ergodic.Kingman, Oseledets.Ergodic.Birkhoff. Deliver: tendsto_kingman_ergodic_means — under the hypotheses of tendsto_kingman_ergodic, there is c with (∫ g(n+1))/(n+1) → c AND a.e. (1/n) g n x → c (the a.e. Kingman limit and the mean limit coincide). Proof: means converge by Fekete (Subadditive.tendsto_lim); c ≤ L via iterated subadditivity g(m*n) ≤ Σ_{j<m} g n (T^[jn]·) + Birkhoff for T^[n]; c ≥ L via Fatou on the nonnegative sequence Aₙ − cdivₙ (Aₙ = birkhoffAverage of g 1). Mirror the ENNReal.ofReal-Fatou pattern of int_limsup_div_integrable_aux in Kingman.lean. Match the real tendsto_kingman_ergodic signature.` },
  { key: 'P7', file: 'Oseledets/TwoSided/MeasurableInf.lean',
    spec: `Phase P7 (measurability of the intersection subbundle — PARALLELIZABLE, independent). Read ${BP} section "### P7". Imports: Oseledets.Lyapunov.Measurable (only). Deliver: inner_projComp_eq / one_eigenspace_projComp (for orthogonal projections P_K,P_L: (P_K P_L P_K) v = v iff v in K ⊓ L); tendsto_pow_orthProj_inf (validated statement: (orthProjMatrix K * orthProjMatrix L * orthProjMatrix K)^n → orthProjMatrix (K ⊓ L), via the spectral theorem for the self-adjoint contraction, eigenvalues in [0,1], c^n → indicator c=1); MeasurableSubspace.inf (x ↦ K x ⊓ L x is a MeasurableSubspace when K,L are: powers measurable + measurable_of_tendsto_metrizable, entrywise). Match real MeasurableSubspace/orthProjMatrix API from Measurable.lean / MeasurableSubspace.lean. If the spectral-theorem API resists, diagonalize via Matrix.IsHermitian.spectral_theorem as LimitEigenbasis.lean does.` },
]

phase('Implement')
const results = await pipeline(PHASES,
  p => agent(
    `Implement a NEW file ${p.file} of the two-sided Oseledets splitting. PURELY ADDITIVE; sorry-free; linter-clean.\n\n${p.spec}\n\n${NOGIT}\n\nVERIFY to zero warnings, sorry-free, error-free:\n  ${VERIFY} ${p.file}\nReport (FINAL message only, once truly done and re-verified): exact public decl names + signatures; sorryFree + verifierClean; anything scoped out with the precise reason.`,
    { agentType: 'lean-worker', model: 'opus', phase: 'Implement', schema: IMPL_SCHEMA, label: `impl:${p.key}` }),
  (impl, p) => impl == null ? null :
    agent(
      `ADVERSARIAL audit of ${p.file} (two-sided splitting phase ${p.key}). Read ${BP} section "### ${p.key}" for the intended deliverables. Find FLAWS: (1) run \`${VERIFY} ${p.file}\` — confirm 0 errors/0 warnings, grep for sorry/admit/native_decide. (2) Non-vacuity: are hypotheses satisfiable, conclusions non-trivial? (3) Faithfulness: do the statements express the intended math (the blueprint deliverables) with correct quantifiers, not a weakened/vacuous form? Especially P3: that the mean-limit and a.e.-limit genuinely coincide (the load-bearing identification). You MAY write a /tmp scratch probe (not in repo). Do NOT edit the repo file; no git.\nReturn the structured verdict.`,
      { agentType: 'mathematician', model: 'opus', phase: 'Audit', schema: AUDIT_SCHEMA, label: `audit:${p.key}` })
      .then(a => ({ key: p.key, file: p.file, impl, audit: a })))

log(`wave A: ${results.filter(Boolean).length}/${PHASES.length} phases returned`)
return { results }
