# Issue #22 — full implementation plan (LIVING DOC — update continuously)

**Goal (full acceptance):** `monotonicity_relEntropy_under_CPTP` (DPI) + `petz_equality_recovery`
sorry-free, axiom-clean, on `main`; consumer corollary `no_section_of_strict_relEntropy_drop`
UNCONDITIONAL. Finite-dim density operators over ℂ. Build on #23 `ErgodicTheory/OperatorEntropy/`.

**Strategy:** research-first (don't reinvent — formalize the cleanest documented proof), grind
piece by piece, commit each green module, update this plan after every phase.

## Phases & status

- **Phase 0 — relEntropy foundations** [IN PROGRESS; de-risk scout a0ca18b74ae518089]
  - relEntropy (Umegaki), relEntropy_nonneg (Klein via klein_scalar + eigenbasis overlap),
    relEntropy_eq_zero_iff (faithful), additivity, unitary invariance, conditional no-section.
  - FEASIBLE NOW (reuses #23 Klein). Lands real value regardless of the Lieb route.
- **Phase 1 — operator-convexity toolkit** [PENDING research]
  - op convex/concave of t·log t, log, t^s (s∈[0,1]); left/right mult superoperators L_A,R_B
    (commute) + functional calculus; the perspective scaffolding. Inventory Mathlib CFC op-convex API.
- **Phase 2 — joint convexity / Lieb (KEYSTONE)** [PENDING research]
  - Effros operator-perspective route: P_f(A,B) jointly op-convex for op-convex f; f=t log t ⇒
    joint convexity of Umegaki relative entropy. THE Mathlib-scale core.
- **Phase 3 — DPI** [PENDING]
  - unitary invariance (easy) + monotonicity under partial trace (from Phase 2) + Stinespring
    (CPTP = isometry + partial trace) ⇒ monotonicity_relEntropy_under_CPTP. Then discharge the
    Phase-0 conditional corollary ⇒ unconditional no_section_of_strict_relEntropy_drop.
- **Phase 4 — Petz recovery / equality** [PENDING; hardest]
  - Petz map + HS adjoint + equality case of DPI. Sits atop Phase 3.

## Known facts (from feasibility recons)
- DPI ⟺ joint convexity of rel. entropy ⟺ Lieb concavity (Ruskai/Carlen–Lieb). No elementary
  finite-dim shortcut (non-commutativity of ρ,σ,Λρ,Λσ blocks klein_scalar). Effros perspective =
  cleanest formalization target.
- Mathlib HAS: cfc Real.log on PosDef, single-var operator-monotone/concave log (CFC.concaveOn_log,
  CFC.log_le_log), generic CompletelyPositiveMap, PosSemidef/PosDef, IsHermitian.cfc, CFC.sqrt.
  ABSENT: Lieb, two-var/joint operator convexity, operator perspective, L/R mult superoperators,
  relative entropy, SSA, Petz map. [VERIFY depth in research Phase 1.]
- Consumer corollary needs DPI-for-ONE-map (the section R), still the full Lieb wall — so Phase 0
  delivers it CONDITIONED on an explicit monotonicity hyp; Phase 3 discharges that hyp.

## Open route questions for research (resolve before grinding Phase 1-4)
1. Effros perspective vs Lieb-analytic vs variational (Petz/Sutter-Berta) — which is MOST
   Lean-tractable given Mathlib's CFC depth?
2. Exact Mathlib op-convex API depth (is there ANY two-variable / Loewner-order / operator-mean
   theory to build on?).
3. DPI-from-joint-convexity: cleanest finite-dim reduction (Stinespring form available in Mathlib?).
4. Petz equality: how hard; is a scoped "DPI + recovery-map-defined, equality-conditional" honest
   partial acceptable if full equality is too deep?

## Commits / modules (update as landed)
- (none yet)

## === RESEARCH RESULT (2026-06-29): FRENKEL ROUTE chosen — REPLACES the Lieb/operator-convexity plan ===
Route: Frenkel integral formula `D(ρ‖σ)=Tr(ρ−σ)+∫_ℝ (|t|(t−1)²)⁻¹·tr₋((1−t)ρ+tσ)dt` (Frenkel,
Quantum 2023). DPI ⟸ tr₋ monotone under positive-TP maps (Lemma 9, elementary) + integral monotone.
NO operator convexity / Lieb / Stinespring / Choi–Kraus / CStarMatrix bridge needed. Single keystone
= the integral formula (F), classical analysis (Mathlib-strong).

### Phases (Frenkel)
- A [relEntropy def (cfc-trace form, bridged to spectral) + matrix Klein nonneg/eq-zero] — IN FLIGHT
  (worker aa9e0cb2796558bda on the spectral skeleton; ENSURE the cfc-trace bridge `relEntropy_eq_traceLog`
  lands — now load-bearing for F). module RelativeEntropy.lean (or RelativeEntropy/Defs.lean).
- B [trNeg/trPos + Frenkel Lemma 9 monotonicity under positive-TP] — INDEPENDENT, dispatch now.
  module RelativeEntropy/TrNeg.lean.
- C [unitary/isometry invariance + tensor cancellation] — needs A. RelativeEntropy/Invariance.lean.
- D [Petz map (concrete Kraus form) + petzMap_isCPTP + recovery R(Λσ)=σ] — needs A. PetzMap.lean.
- E [hDPI interface + no_section_of_strict_relEntropy_drop + easy Petz direction, CONDITIONAL on hDPI]
  — needs A,C,D statements. DataProcessing.lean (interface). (The old skeleton's conditional corollary
  already covers most of E.)
- F [KEYSTONE: F1 matrixLog_hasDerivAt/Adler integral (cfc fderiv, ABSENT — DE-RISK FIRST) → F2 deriv-in-r
  + r→∞ limit → F3 Frenkel Thm 7 residue assembly + dominated convergence]. LARGE, single complex-analysis
  worker, long pole. MatrixLogDeriv.lean + IntegralFormula.lean.
- G [monotonicity_relEntropy_under_positiveTP ⇒ _under_CPTP from F+B; discharge E ⇒ unconditional
  no-section]. needs F,B,E. DataProcessing.lean (proof).
- H [DEFER to follow-up: full petz_equality_recovery iff + Lieb/SSA].

### Grind order: wave1 = A(flight)+B+F1-derisk-scout; wave2 = C,D,E + dedicated F worker; wave3 = G.
### Honest scoping: A–E+D UNCONDITIONAL/CONDITIONAL ship now; F attempted (may not close); H deferred.
### Keystone risk: F1 (matrix-log Fréchet derivative, no cfcDeriv in Mathlib) — DE-RISK before committing F3.

## === F1 DE-RISK RESULT (2026-06-29): the Frenkel keystone F is ALSO a wall (at F3, not F1) ===
- F1 (Frenkel's actual derivative) is COMMUTING (along identity) ⇒ scalar log-sum derivative — PROVED by scout (no sorry). NOT the Adler integral (that's unused).
- F3 = complex RESIDUE THEOREM + real-algebraic-curve change of variables. Mathlib has NO residue theorem (only ResidueField algebra). Multi-month to build. => Frenkel route WALLED at F3.
- Combined with the Effros/Lieb route (walled at Hansen–Pedersen–Jensen operator-Jensen, no OperatorConvex theory), BOTH clean routes to the UNCONDITIONAL DPI are multi-month Mathlib-scale. CONFIRMED WALL (5-route research + 2 de-risk scouts).
- Resolvent rep `D=∫₀^∞ tr[ρ((σ+r)⁻¹−(ρ+r)⁻¹)]dr` does NOT give DPI cheaply (integrand not tr₋-style monotone; "DPI via op-monotone log" was a conflation — op-monotonicity ≠ the joint convexity DPI needs).
- DELIVERABLE NOW (unconditional/conditional): A relEntropy+Klein, B trNeg+Lemma9, C invariances, D Petz map+recovery, E no-section CONDITIONAL on explicit DPI hyp. Optional standalone: F1a (matrix-log deriv + tr log=log det + Jacobi) = genuine Mathlib-gap PR but does NOT unblock DPI (F3 still walled).
- DECISION PENDING (user): ship foundations+follow-up vs commit multi-month keystone (operator-Jensen OR residue theorem).

## === KEYSTONE GREENLIT (user chose Lieb/operator-Jensen). Verified skeleton: issue22_lieb_skeleton.lean ===
Route: Effros/HPJ. ~3-5 worker-weeks, 6 modules under ErgodicTheory/OperatorEntropy/Lieb/. ONE hard thm (HPJ K1 via dilation S1-S5) + ONE wrinkle (Matrix↔CStarMatrix cfc bridge: CStarAlgebra(Matrix) does NOT exist; state over Matrix native cfc, transport −log convexity via CStarMatrix ofMatrix defeq).
Modules: 1 Lieb/OperatorConvex.lean [K0 OperatorConvexOn + K2 −log op-convex(via CFC.concaveOn_log)+bridge] · 2 Lieb/Dilation.lean [S1-S5 + hpj_affine + hpj_isometry, HPJ keystone, riskiest=S1] · 3 Lieb/Perspective.lean [K3 perspective joint op-convexity] · 4 Lieb/RelEntropy.lean [canonical relEntropy=cfc-trace form + leftMul/rightMul + K5 realization] · 5 Lieb/JointConvexity.lean [K6 joint convexity of relEntropy] · 6 Lieb/DPI.lean [K7 + finite-dim Stinespring + twirl].
CANONICAL relEntropy = (trace(ρ*(cfc Real.log ρ − cfc Real.log σ))).re — UNIFY with Phase A (spectral form becomes a proved-equal bridge lemma for the Klein proof).
S1 = ∃ U unitary 2N×2N with first block-col (A,B) given star A*A+star B*B=1 (Orthonormal.exists_orthonormalBasis_extension). ROUTE B fallback if S1 stalls: convexOn_ringInverse (Mathlib HAS) + Schur complement + −log integral rep + scalar trace inside.
Waves: W1={M1 OperatorConvex, S1-prototype, M4-defs}; W2={M2 Dilation, M4 realization}; W3=M3; W4=M5; W5=M6.
