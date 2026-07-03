# Issue #22 — continuation handoff (DPI + Petz ⇒ no-section)

> **Start here for a new session.** This branch (`wip/issue-22`) is a checkpoint: the **Phase-A
> foundations** for issue #22 are landed and green; the **Lieb/operator-Jensen keystone** is fully
> researched and de-risked (a *verified* skeleton is committed under `docs/issue22/`), but **not yet
> ground**. Everything below is what you need to resume.

GitHub issue: <https://github.com/marcmorningstar/lean4-oseledets/issues/22>

---

## 0. TL;DR / where we are

- **3 sibling issues already CLOSED on `main`** (#23 operator entropy, #24 CNT/ALF, #21 conditional
  fibre). This branch is `wip/issue-22` off `main`.
- **Phase A (relEntropy foundations) — DONE, green, axiom-clean** in
  `Oseledets/OperatorEntropy/RelativeEntropy.lean` (committed here, **un-wired** — not yet imported by
  `Oseledets.lean`; see §6).
- **The unconditional DPI is a genuine multi-month Mathlib-scale keystone.** Confirmed by 5-route deep
  research + 3 de-risk scouts: every route to the *unconditional* `monotonicity_relEntropy_under_CPTP`
  funnels through a theorem **absent from Mathlib** (operator-Jensen / Lieb concavity, OR the complex
  residue theorem). The user chose to **grind the Lieb/operator-Jensen route**.
- **The keystone IS formalizable** (~3–5 focused worker-weeks, 6 modules). A **verified K0–K7 skeleton**
  (elaborates against Mathlib with only `sorry`s) is at `docs/issue22/lieb_keystone_skeleton.lean`.

**Next concrete action (Wave 1):** grind module 1 (`Lieb/OperatorConvex.lean`) and prototype S1 (the
unitary dilation) in isolation — see §5.

---

## 1. The target (issue #22 acceptance)

Finite-dim density operators over ℂ (PSD, unit-trace matrices). Deliver sorry-free:
- `monotonicity_relEntropy_under_CPTP` — the **data-processing inequality**: `S(Λρ‖Λσ) ≤ S(ρ‖σ)` for
  any CPTP `Λ`, where `S(ρ‖σ) = Tr ρ(log ρ − log σ)` (Umegaki relative entropy).
- `petz_equality_recovery` — equality ⟺ the Petz recovery map inverts `Λ` on `ρ`; hence a **strict**
  drop ⟹ no CP trace-preserving section.
- consumer corollary `no_section_of_strict_relEntropy_drop`: a CP coarse-graining with a strict
  relative-entropy drop has no CP trace-preserving section.

Builds on the **#23 `Oseledets/OperatorEntropy/` library** (`DensityMatrix`, `vonNeumannEntropy`,
`klein_scalar`, `partialTrace`, `eigenvalues_kronecker_multiset`, …). The downstream consumer
`AutonomousDynamics.OperatorEntropy.FiniteDimEntropy` lives in a **separate repo not checked out here**;
these are the **upstream primitives**.

---

## 2. What is DONE (Phase A) — `Oseledets/OperatorEntropy/RelativeEntropy.lean`

Green (`lake build Oseledets.OperatorEntropy.RelativeEntropy` → 8447 jobs, 0 sorry); every headline
axiom-clean `[propext, Classical.choice, Quot.sound]`.

Canonical objects (spectral/overlap form; `relEntropy_eq_traceLog` bridges to the textbook cfc-trace
form `Tr ρ(log ρ − log σ)`):
- `relEntropy ρ σ := (∑ k, ρ.eig k * log(ρ.eig k)) − ∑ k m, crossOverlap ρ σ k m * ρ.eig k * log(σ.eig m)`
  where `crossOverlap ρ σ k m = ‖(ρ.eigVecᴴ · σ.eigVec) k m‖²` (the doubly-stochastic eigenbasis overlap).

Proven (sorry-free, axiom-clean):
- **`relEntropy_nonneg (ρ σ) (hσ : σ.val.PosDef)`** — Klein/Gibbs, a *direct* `klein_scalar`
  instantiation (overlap matrix doubly-stochastic via the `Subadditivity.lean` `hrow`/`hcol` pattern;
  `hsupp` vacuous from `Matrix.PosDef.eigenvalues_pos`).
- `relEntropy_self_eq_zero` (`Q = 1` collapse).
- `relEntropy_conj_invariant` (unitary invariance, via the trace form + `StarAlgHomClass.map_cfc`).
- `relEntropy_eq_traceLog` (recognizability bridge to `Tr ρ(log ρ − log σ)`; uses `Matrix.IsHermitian.cfc Real.log` — **NOT** `CFC.log`, which needs an absent `NormedRing (Matrix …)` instance).
- `IsRelEntropyMonotone Λ := ∀ ρ σ, relEntropy (Λρ)(Λσ) ≤ relEntropy ρ σ`; `isRelEntropyMonotone_id`.
- **`no_monotone_section_of_strict_drop`** — the consumer corollary, CONDITIONAL on an explicit
  monotonicity hypothesis `hRmono : IsRelEntropyMonotone R`. This is the honest no-section obstruction;
  the DPI gap is localized to this one hypothesis, auto-discharged when the keystone lands (§4 K7/G).

### DEFERRED in Phase A (two findings — read these):
1. **`relEntropy_additive_kronecker` is FALSE as stated** (no faithfulness hyp). Counterexample
   (qubits): `σ=diag(½,½)`, `ω=diag(1,0)`, `ρ=τ=diag(½,½)` ⇒ `D(ρ⊗τ‖σ⊗ω)−[D(ρ‖σ)+D(τ‖ω)] = ½·log½ ≠ 0`,
   because `log(σ⊗ω) ≠ log σ⊗1 + 1⊗log ω` at a zero eigenvalue paired with a nonzero one. **Re-file with
   `PosDef σ, ω` added.**
2. **`relEntropy_eq_zero_iff`** — TRUE but blocked on the **Klein equality case** (`klein_scalar` gives
   only the inequality; need `log x ≤ x−1` tight ⟺ `x=1`, propagated through the overlap matrix to force
   matching spectra + aligned eigenbases ⇒ `ρ=σ`). A substantial standalone argument; defer or do as a
   small follow-up.

---

## 3. Why the unconditional DPI is a keystone (route analysis — don't re-derive)

Deep research (5 routes) + de-risk scouts converged: **there is no elementary finite-dim shortcut to
DPI**. The `#23` `klein_scalar` trick works for *subadditivity* (one fixed change of basis) but NOT for
relative-entropy DPI (four distinct eigenbases ρ,σ,Λρ,Λσ, no common diagonalization). Every clean route
hits a *different* Mathlib-absent, multi-month theorem:

| Route | Keystone needed | Mathlib status |
|---|---|---|
| **Effros operator-perspective / Lieb** (CHOSEN) | Hansen–Pedersen–Jensen operator-Jensen → joint operator convexity | ABSENT (no `OperatorConvex` theory) |
| Frenkel integral formula | the complex **residue theorem** + real-algebraic-curve change of variables | ABSENT (only `ResidueField` *algebra*; no analytic residue theorem) |
| Petz variational | Golden–Thompson + operator Jensen | ABSENT (+ a documented flaw in Petz's Jensen step, arXiv:2509.11221) |

Frenkel sub-finding: F1 (his actual derivative) is *commuting* (along the identity) ⇒ a scalar log-sum
derivative (provable); the wall is F3 (residues). The Adler/non-commuting matrix-log derivative is NOT
used by Frenkel. `x log x` operator convexity is a Mathlib **TODO**, so the Effros route MUST use
`−log` (which IS available — see §4 K2).

---

## 4. The CHOSEN route — Effros/HPJ, verified skeleton in `docs/issue22/lieb_keystone_skeleton.lean`

Chain: **OperatorConvex framework → HPJ operator-Jensen → Effros perspective joint convexity → joint
convexity of relative entropy → DPI.** All K0–K7 statements below ELABORATE against Mathlib (the
skeleton file; `leftMul_rightMul_commute` even proves outright). References: Hansen–Pedersen *Jensen's
operator inequality* (Bull. LMS 35, 2003); Carlen *Trace Inequalities and Quantum Entropy* (2010) §5–6;
Effros (PNAS 106, 2009 / arXiv:0802.0006); Frenkel (Quantum 7, 2023, for the rejected route).

- **K0** `OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) := ∀ m, ConvexOn ℝ {a : Matrix (Fin m) (Fin m) ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (fun a => cfc f a)` (matrix-convex of all orders; native `Matrix` cfc + scoped `MatrixOrder`).
- **K2** `operatorConvexOn_neg_log : OperatorConvexOn (Set.Ioi 0) (fun x => -Real.log x)` — FREE from Mathlib's `CFC.concaveOn_log` (`…/ExpLog/Order.lean:20`), transported through `CStarMatrix` (see the wrinkle in §4a).
- **K1 (KEYSTONE)** HPJ, two forms — affine `f(A⋆XA+B⋆YB) ≤ A⋆f(X)A+B⋆f(Y)B` for `A⋆A+B⋆B=1`, and isometry `f(V⋆xV) ≤ V⋆f(x)V` for `V⋆V=1, f(0)≤0`. **Via the unitary-dilation trick (S1–S5, §5).**
- **K3** `operatorPerspective f L R := CFC.rpow R (1/2) * cfc f (CFC.rpow R (-(1/2)) * L * CFC.rpow R (-(1/2))) * CFC.rpow R (1/2)`; `operatorPerspective_jointly_convex` (~15 lines given K1; `CFC.conjugate_rpow_neg_one_half` gives `A⋆A+B⋆B=1`).
- **K4/K5 (realization)** `leftMul ρ X = ρ*X`, `rightMul σ X = X*σ` (commuting positive `→ₗ[ℂ]` on the HS space `Matrix n n ℂ`; `leftMul_rightMul_commute` PROVED), and `relEntropy ρ σ = ⟨P_{−log}(L_ρ,R_σ)(1), 1⟩_HS`. The repo's `eigenvalues_kronecker_multiset` realizes `L_ρ⊗R_σ` as `ρ⊗σᵀ` — turns K5 into a finite eigenvalue computation (`log(ρ⊗I)=(log ρ)⊗I` via `map_cfc`; `⟨vec I, vec M⟩ = Tr M`).
- **K6** `relEntropy_jointly_convex` — the #22 CORE (transfer K3 via linearity of `ρ↦L_ρ`, `σ↦R_σ` + the commuting bracket).
- **K7** DPI: unitary invariance (have it) + monotonicity-under-partial-trace (from K6, twirl/average) + Stinespring (`CPTP = isometry + partialTrace`). `monotonicity_relEntropy_partialTrace` is the consumer-facing form; full CPTP needs finite-dim Stinespring (overlaps #23). Discharging K7 makes `no_section_of_strict_relEntropy_drop` unconditional.

### 4a. The load-bearing wrinkle (don't get stuck here)
`CStarAlgebra (Matrix n n ℂ)` does **NOT** exist even with `Matrix.Norms.L2Operator` open (the scoped
norm yields only `CStarRing`, not a bundled `CStarAlgebra`). And the **ℝ-cfc on `CStarMatrix` does not
auto-synthesize**. Resolution (in the skeleton): state the whole convexity layer over **`Matrix`**
(native cfc, no friction); confine `CStarMatrix` to K2's one-time transport of `CFC.concaveOn_log` via a
`haveI` built from the ℂ-cfc + `SpectrumRestricts.cfc`, using `CStarMatrix.ofMatrix = Equiv.refl` (defeq
carrier!) / `ofMatrixStarAlgEquiv` / `map_nonneg` / `map_cfc`. A naive "Matrix-as-C\*-algebra" worker
dies on line 1 — this is the gating task of module 1.

### 4b. ROUTE B (live fallback if S1 stalls)
Mathlib **already proves** `convexOn_ringInverse` (operator convexity of `x↦(t+x)⁻¹`) and has
`LinearAlgebra/Matrix/SchurComplement.lean`. Via `−log x = ∫₀^∞ (1/(x+s) − 1/(1+s)) ds` + pushing the
*scalar* trace inside the integral, joint convexity of `relEntropy` follows from the (Schur-complement /
inverse-perspective) joint convexity of `(L,R)↦R(R+sL)⁻¹R`-type integrands — **bypassing the HPJ
unitary-dilation keystone S1 entirely.** Trades S1's risk for (a) a PSD Schur-complement lemma (partly
to build) and (b) an *elementary scalar* integral-of-convex-functions argument (no operator-valued
integral). Keep this as the fallback.

---

## 5. Module decomposition + grind order (the plan)

New modules under `Oseledets/OperatorEntropy/Lieb/`:

| # | Module | Content | Effort | Deps |
|---|---|---|---|---|
| 1 | `Lieb/OperatorConvex.lean` | K0 + K2 + the `Matrix↔CStarMatrix` cfc/order bridge (§4a) | S–M | #23 |
| 2 | `Lieb/Dilation.lean` | **S1–S5 + `hpj_affine` + `hpj_isometry`** (the HPJ keystone) | **L** | 1 |
| 3 | `Lieb/Perspective.lean` | K3 (perspective + joint convexity) | M | 2 |
| 4 | `Lieb/RelEntropy.lean` | canonical `relEntropy` (cfc-trace) + `leftMul`/`rightMul` + K5 realization | M–L | #23 |
| 5 | `Lieb/JointConvexity.lean` | K6 (joint convexity of relEntropy) | M | 3,4 |
| 6 | `Lieb/DPI.lean` | K7 + finite-dim Stinespring + twirl; discharge the conditional consumer | L | 5 |

**HPJ (K1) sub-lemmas — module 2** (Carlen Thm 4.20 / Hansen–Pedersen dilation route; realize
`M₂(Matrix N) ≅ Matrix (Fin 2 × Fin N)`):
- **S1 (HIGHEST RISK).** `∃ U` unitary on `ℂ^{2N}` with first block-column `(A,B)` (given
  `A⋆A+B⋆B=1`): the `N` columns of `[A;B]` are orthonormal in `ℂ^{2N}` ⇒ extend via
  `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` (`…/PiL2.lean:1032`). Fallback: HP's
  explicit defect `√(1−AA⋆)`.
- **S2.** `cfc f (U⋆ M U) = U⋆ (cfc f M) U` via `Unitary.conjStarAlgAut` + `StarAlgHomClass.map_cfc` (probe-verified).
- **S3.** `cfc f (block-diag a b) = block-diag (cfc f a) (cfc f b)` via `cfc_map_prod` (`…/ContinuousFunctionalCalculus/Pi.lean`).
- **S4.** 2-pt convexity in `M₂` from `OperatorConvexOn … (2N)`, `V = diag(1,−1)` (involutive unitary).
- **S5.** Block arithmetic: `(U⋆ diag(X,Y) U)₁₁ = A⋆XA + B⋆YB`; pinch `diag(M₁₁,M₂₂) = (M + V M V)/2`;
  compare (1,1)-corners. (Affine form needs no `f(0)≤0`.)

**Grind waves:** W1 = {module 1, **S1 prototype in isolation**, module-4 defs} (independent) →
W2 = {module 2 (HPJ), module-4 realization} → W3 = module 3 → W4 = module 5 → W5 = module 6.
First two de-risking targets: **module 1 (the bridge)** and **S1**.

**Note — unify `relEntropy`:** Phase A uses the spectral/overlap form; the keystone (K5/K6) wants the
cfc-trace form `(Tr(ρ·(cfc log ρ − cfc log σ))).re`. `relEntropy_eq_traceLog` already bridges them — pick
the cfc-trace form as canonical and keep the spectral form as the proved-equal lemma for the Klein proof.

---

## 6. Wiring / build (when resuming)

Phase A's `RelativeEntropy.lean` is committed **un-wired** (not imported by `Oseledets.lean`, so a full
`lake build` ignores it). To build it: `lake build Oseledets.OperatorEntropy.RelativeEntropy`. When the
layer is ready to integrate, an **integration worker** (not the orchestrator) should add the import to
`Oseledets.lean` + the `#guard_msgs in #print axioms` guards to `test/AxiomAudit.lean`, then the full
`lake build Oseledets AxiomAudit` gate.

---

## 7. Campaign mechanics (so the method survives the session boundary)

- **Orchestrator delegates ALL Lean/test edits to `lean-worker` subagents**; the orchestrator does only
  git, build gates, `gh`, and memory. (User correction — see the `orchestrator-never-edits-files` memory.)
- **Every Lean worker gets its OWN warm `lwt` worktree:** `WT=$(.claude/scripts/lwt add <branch> | tail -1)`
  (never `--no-warm`); edits only under `$WT`; **NEVER runs git**; never `sorry`/`axiom`. Final gate =
  one cold `lake build <Module>`.
- **Warm leancheck is BROKEN this session** (leanclient absent) → workers **cold-iterate** (`lake build`);
  `lwt` still gives per-worktree isolation + the Mathlib-cache symlink.
- Workers **idle-notify after kicking off a background build** — the orchestrator takes over and runs the
  authoritative build itself.
- Subagents have **died on a 64000 output-token limit** when pasting whole files/logs — tell them to keep
  reports SHORT (the file survives on disk; take over and build it).
- **De-risk pattern that worked repeatedly:** a `mathematician` scout emits a *verified skeleton*
  (statements elaborating with `sorry` against the built lib) + the proof plan; workers then grind from
  the skeleton (copy statements verbatim). Race a single-point-of-failure keystone ×2.
- The verified keystone skeleton is `docs/issue22/lieb_keystone_skeleton.lean` — re-elaborate it with
  `lake env lean docs/issue22/lieb_keystone_skeleton.lean` to confirm it still type-checks on resume.

---

## 8. Other open issues (status, for context)

- **#25** (follow-up): literal explicit-Kraus partial-trace form `∑ⱼ Eⱼ M Eⱼᴴ` — blocked by a Mathlib
  `CStarMatrix`/`Matrix` `HMul` default-instance ambiguity; the CP content is already delivered in #23 via
  the submatrix-compression form. Bounded.
- **#26** (follow-up): CNT operator-Fekete well-definedness + soft-POVM ≥ projection monotonicity. Bounded.
- **#11** (WALL, partial): the two BLOCKED leaves are unequal — **Leaf 2** (Saint-Raymond σ-compact) is a
  genuine Effros-Borel-hyperspace/Π¹₁ wall (months); **Leaf 1** (Novikov compact-sections) is bounded
  Chapter-4 DST (~2–5 weeks). **Closed-ball shortcut**: the Oseledets sections are *subspaces* so
  `V∩closedBall` is COMPACT — route `measurableInfDist…` via `measurable_of_Iic` ⇒ the everywhere-Borel
  MET upgrade needs only Leaf 1, never Leaf 2.
- **#10** (WALL): `sumPosExp_le_ksEntropy_of_SRB` — (a) `ACConditionalsUnstable` is `opaque` ⇒ the leaf is
  unprovable/unrefutable as worded (needs an interface redesign), AND (b) the keystone (unstable-foliation
  absolute continuity / Brin–Katok) is multi-year, Mathlib-absent. Volume/expanding case already done
  (`pesin_formula_expanding`).

---

## 9. Artifacts in this commit
- `Oseledets/OperatorEntropy/RelativeEntropy.lean` — Phase A foundations (green, un-wired).
- `docs/issue22/lieb_keystone_skeleton.lean` — the verified K0–K7 keystone skeleton (re-elaborate to confirm).
- `docs/issue22/research_plan_log.md` — the full living research/plan log (route analysis, the Frenkel
  detour, the keystone greenlight).
- `ISSUE22_CONTINUATION.md` — this file.
