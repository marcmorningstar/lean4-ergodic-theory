# Workflow templates

Two copy-adaptable `Workflow` scripts that have driven real campaigns. Pass them inline to the
`Workflow` tool (or write to a file and pass `{scriptPath}`). Edit the prompts/lenses for your
issue. Both rely on agents provisioning their own warm `lwt` worktree — `Workflow`'s
`isolation:'worktree'` is NOT warm and would rebuild Mathlib, so the worker boilerplate uses
`lwt` explicitly.

Reminders that apply to both:
- Scripts are plain JS (no TypeScript, no `Date.now()`/`Math.random()`).
- `agent(prompt, {schema, label, phase, agentType})` — with `schema` it returns a validated object.
- `parallel(thunks)` is a barrier (awaits all; failures become `null` — `.filter(Boolean)`).
- Keep each `parallel()` batch ≤ ~6–8 for RAM when the agents run cold Lean builds.

---

## Template A — research → parallel sub-lemma fan-out

For a decomposable formalization target: one research/scout agent verifies the route and emits a
list of **independent** sub-lemmas (each buildable on plain `main`), then a worker grinds each in
parallel. The orchestrator assembles the pieces afterward (cross-tree integration is yours, not
the workflow's). This is the shape that proved `h(T×id)=h(T)` for issue #20.

```js
export const meta = {
  name: 'issue-N-assault',
  description: 'Research-decompose <target> into independent lemmas, then prove each in parallel',
  phases: [
    { title: 'Research', detail: 'verify route + emit independent sub-lemma decomposition' },
    { title: 'SubLemmas', detail: 'parallel proof of each independent lemma on its own lwt worktree' },
  ],
}

const SCHEMA = {
  type: 'object', additionalProperties: false,
  required: ['viable', 'verdict', 'sublemmas', 'assemblyPlan'],
  properties: {
    viable: { type: 'boolean' },                 // false ⇒ stop; orchestrator documents the wall
    verdict: { type: 'string' },                 // SMALL/MEDIUM/LARGE + justification
    assemblyPlan: { type: 'string' },            // how the orchestrator combines the lemmas
    sublemmas: { type: 'array', items: {
      type: 'object', additionalProperties: false,
      required: ['key', 'statement', 'targetModule', 'existingLemmas', 'size'],
      properties: {
        key: { type: 'string' }, statement: { type: 'string' },
        targetModule: { type: 'string' },        // DISTINCT path per lemma (avoid collisions!)
        existingLemmas: { type: 'string' }, size: { type: 'string' },
      } } },
  },
}

// Worker boilerplate — every Lean worker gets this.
const INV = [
  'You are a Lean 4 + Mathlib worker on /workspaces/lean4-oseledets. Read CLAUDE.md.',
  'Provision your OWN warm worktree: WT=$(.claude/scripts/lwt add <branch> | tail -1) (NEVER --no-warm).',
  'Edit only under $WT (absolute paths). Iterate with warm leancheck; if confirmed broken this session, fall back to cold `lake build`.',
  'You may NOT run git. NEVER sorry/admit/axiom. Lint=errors: <=100 codepoints/line; no show/push_neg;',
  'set_option/omit go BEFORE the docstring. Create a NEW self-contained module; do NOT edit aggregators.',
  'FINAL GATE: cd "$WT" && lake build <YourModule> (zero errors/warnings). REPORT: exact final',
  'signature; branch; files (absolute); cold-build tail; `grep -nE "sorry|admit|axiom"` is empty; blockers.',
].join('\n')

phase('Research')
const research = await agent(
  '<research prompt: verify the cleanest route to <target> against the codebase + firecrawl the ' +
  'standard reference; decompose into INDEPENDENT abstract sub-lemmas each buildable on plain main; ' +
  'for each give key, exact Lean statement (codebase types), DISTINCT targetModule path, existing ' +
  'lemmas to use (name + file:line), size. Set viable=false with a verdict if it is a genuine wall.>',
  { schema: SCHEMA, phase: 'Research', agentType: 'mathematician' })
log('viable=' + research.viable + ' : ' + research.verdict)
if (!research.viable) return { viable: false, verdict: research.verdict, results: [] }

phase('SubLemmas')
const results = await parallel(research.sublemmas.map(function (sl) {
  return function () {
    return agent([INV, '', '## SUB-LEMMA `' + sl.key + '` (independent; builds on plain main)',
      'Branch `sl-' + sl.key + '`. New module `' + sl.targetModule + '`.',
      'PROVE sorry-free: ' + sl.statement,
      'Use: ' + sl.existingLemmas + '   Size: ' + sl.size,
      'If the stated form is slightly off, fix to the closest TRUE+USEFUL form and report it.',
    ].join('\n'), { label: 'sl:' + sl.key, phase: 'SubLemmas', agentType: 'lean-worker' })
      .then(function (r) { return { key: sl.key, module: sl.targetModule, report: r } })
  }
}))
return { viable: true, verdict: research.verdict, assemblyPlan: research.assemblyPlan,
         sublemmas: research.sublemmas, results: results.filter(Boolean) }
```

After it returns: stage the green sub-lemma modules into your integration tree, dispatch an
assembly worker (and a transport/specialization worker if needed), then run Template B (QA).

---

## Template B — multi-lens adversarial QA (with auto-fix downstream)

Reviews the new modules through five independent lenses in parallel, then an adversarial
synthesis-verifier confirms/rejects each finding against the actual code. Point `REPO` at wherever
the modules live (the integration worktree if not yet on `main`). After it returns, the
orchestrator auto-applies the `isReal` findings, rebuilds, and commits.

```js
export const meta = {
  name: 'issue-N-qa',
  description: 'Multi-lens adversarial QA over <modules> -> deduped confirmed fix list',
  phases: [{ title: 'Lenses' }, { title: 'Verify' }],
}
const REPO = '/workspaces/lean4-oseledets'          // or the integration worktree path
const FILES = ['Oseledets/.../A.lean (what it proves)', 'Oseledets/.../B.lean (…)']  // the new modules
const PREAMBLE = [
  'READ-ONLY QA reviewer for the Oseledets project (code under review in ' + REPO + '). Read its CLAUDE.md.',
  'Modules under review (with one-line purpose):', FILES.map(function (f) { return '  - ' + f }).join('\n'),
  '<one-paragraph context: what the result is, the route, and any deliberate rescope NOT to flag>',
  'Read the files in full + cited lemmas. Do NOT edit. Report findings ONLY for your lens:',
  'file, location, severity (blocker|major|minor|nit), category, description, suggestedFix.',
  'Prefer few high-signal findings. Empty list if clean.',
].join('\n')
const FSCHEMA = { type: 'object', additionalProperties: false, required: ['findings'], properties: {
  findings: { type: 'array', items: { type: 'object', additionalProperties: false,
    required: ['file', 'location', 'severity', 'category', 'description', 'suggestedFix'],
    properties: { file: {type:'string'}, location: {type:'string'},
      severity: {type:'string', enum:['blocker','major','minor','nit']},
      category: {type:'string'}, description: {type:'string'}, suggestedFix: {type:'string'} } } } } }
const LENSES = [
  { key: 'math-faithfulness', agentType: 'mathematician', focus: 'Do the STATEMENTS faithfully capture the intended results with NO weakening? Spot-check the load-bearing proof steps for soundness.' },
  { key: 'vacuity-honesty', agentType: 'mathematician', focus: 'Is the result NON-VACUOUS (the hypotheses satisfiable, the measures/spaces non-degenerate)? Any hypothesis secretly trivializing it?' },
  { key: 'soundness', agentType: 'general-purpose', focus: 'No sorry/admit/axiom/unsafe/native_decide; no Eq.mpr/cast/defeq abuse. Do the axiom-audit guards cover every headline result?' },
  { key: 'reuse', agentType: 'general-purpose', focus: 'Duplicated/ reinvented Mathlib or Oseledets API? Redundant hypotheses? Name the existing lemma that could replace each.' },
  { key: 'style', agentType: 'general-purpose', focus: 'Naming/convention consistency (incl. set_option/omit before docstrings, codepoint line length), doc-comments with SOURCE attribution.' },
]

phase('Lenses')
const lens = await parallel(LENSES.map(function (L) { return function () {
  return agent(PREAMBLE + '\n\n## LENS: ' + L.focus, { schema: FSCHEMA, label: 'qa:' + L.key, phase: 'Lenses', agentType: L.agentType })
    .then(function (r) { return (r && r.findings) ? r.findings.map(function (f){ return Object.assign({lens: L.key}, f) }) : [] })
}}))
const all = lens.filter(Boolean).flat()
if (all.length === 0) return { confirmed: [], real: [], summary: 'All lenses clean.' }

phase('Verify')
const VSCHEMA = { type: 'object', additionalProperties: false, required: ['confirmed','summary'], properties: {
  summary: {type:'string'}, confirmed: { type:'array', items: { type:'object', additionalProperties:false,
    required: ['file','location','severity','category','description','fix','isReal','reasoning'],
    properties: { file:{type:'string'}, location:{type:'string'}, severity:{type:'string'}, category:{type:'string'},
      description:{type:'string'}, fix:{type:'string'}, isReal:{type:'boolean'}, reasoning:{type:'string'} } } } } }
const verified = await agent([
  'ADVERSARIAL QA synthesis-verifier. Code in ' + REPO + '. For EACH raw finding below, READ THE CODE and',
  'decide isReal (true = real+actionable now) vs false (false positive/taste/scope). Default skeptical:',
  'isReal=false unless the code confirms it. DEDUPLICATE. Never weaken a statement to satisfy a lint.',
  'Give a fair severity, precise location, CONCRETE minimal fix (preserve statements, keep build green +',
  'axiom-clean), and reasoning citing code. Also a one-paragraph `summary` overall verdict.',
  '', 'RAW FINDINGS:', JSON.stringify(all, null, 2),
].join('\n'), { schema: VSCHEMA, phase: 'Verify', agentType: 'mathematician' })
const real = (verified.confirmed || []).filter(function (f) { return f.isReal })
log('verdict: ' + verified.summary); log('real findings: ' + real.length)
return { confirmed: verified.confirmed || [], real: real, summary: verified.summary }
```

After it returns: apply the `real` findings (cheap/local ones yourself; an invasive cross-module
refactor via a dedicated worker off `main` after the rest is pushed, to isolate its risk),
rebuild full (lib + AxiomAudit), then commit. Re-run on the next chunk of new modules.
