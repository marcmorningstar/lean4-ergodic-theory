# Decision record — target statement & proof route (self-approved)

> The charter (`PROMPT.md`) puts two **human checkpoints** before implementation:
> approval of the target statement, and approval of the plan. The user is away and
> explicitly authorized autonomous decisions ("decide on your own"). This file is
> the standing record of those decisions and their rationale, made in lieu of the
> human checkpoints. Date: 2026-06-04.

## Decision 1 — Target theorem (checkpoint 1: APPROVED, self)

**Adopt the one-sided Oseledets MET in filtration form for a real matrix cocycle
over an ergodic measure-preserving system** as the target (`docs/research/target-and-milestones.md`,
milestone **M10** / `understanding.md` **L6.1**).

Informally: for an ergodic m.p. `T : X → X` on a probability space and a measurable
`A : X → GL(d,ℝ)` with `log⁺‖A‖, log⁺‖A⁻¹‖ ∈ L¹(μ)`, there exist
`λ₁ > ⋯ > λ_k ∈ ℝ` and, a.e., a strictly decreasing `A`-equivariant measurable flag
`ℝᵈ = V¹ₓ ⊋ ⋯ ⊋ V_kₓ ⊋ {0}` with `lim (1/n) log‖A⁽ⁿ⁾(x)v‖ = λᵢ` for `v ∈ Vⁱₓ ∖ V^{i+1}ₓ`.

**Why this and not the alternatives** (full analysis in `target-and-milestones.md §a,c`):
- It is unmistakably *the Oseledets theorem* — all distinct exponents + the
  equivariant measurable filtration + the honest forward limit on each stratum.
  Not a triviality (Furstenberg–Kesten alone is too weak) and not padded.
- It needs only one-sided hypotheses, so its whole dependency chain is classical and
  rests on a Mathlib substrate that demonstrably exists.
- Every intermediate result (pointwise Birkhoff, Kingman, Furstenberg–Kesten) is an
  independently high-value, upstreamable Mathlib target.
- The two-sided splitting (M12), exterior-power multiplicities (M11), and the
  non-ergodic version (M13) are **faithful future milestones**, not dropped — they
  reuse M10 as a black box, so M10 is the correct first deliverable.

## Decision 2 — Proof route (part of checkpoint 2)

**Route B — classical: maximal ergodic inequality → pointwise Birkhoff → Kingman →
Furstenberg–Kesten → induction-on-dimension peeling (limsup flag, then limsup→lim).**
Rationale in `understanding.md §2` and `target-and-milestones.md §b`. In short: both
serious routes need pointwise Birkhoff (absent), so that cost is shared; Route B's
distinctive dependency (Kingman) has a single self-contained classical proof (Steele
1989) and is independently valuable, whereas Route A's distinctive machinery (fibered
Krylov–Bogoliubov + Krein–Milman + measurable subbundles on the projective bundle) is
a bespoke gadget essentially unpackaged in Mathlib. Karlsson–Margulis (NPC geometry)
and Filip's symmetric-space route are rejected (huge theories, little reuse).

**Refinement noted for the implementer:** Kingman can be proved either via Steele
(needs pointwise Birkhoff first) or via Katznelson–Weiss (directly from the maximal
ergodic inequality, with Birkhoff as the additive special case). Decide at M4 which is
cleaner in Lean; the Katznelson–Weiss order could let Kingman *subsume* Birkhoff and
save a layer. Both still require the maximal ergodic inequality (M1).

## Decision 3 — Conventions pinned once (apply project-wide)

- **Cocycle**: `A⁽⁰⁾ = 1`, `A⁽ⁿ⁺¹⁾(x) = A⁽ⁿ⁾(T x) * A x` (newest factor on the
  **left**; matches Bochi/Viana/Filip and `birkhoffSum`'s `f^[k]` indexing). Identity
  `A⁽ᵐ⁺ⁿ⁾(x) = A⁽ᵐ⁾(Tⁿ x) * A⁽ⁿ⁾(x)`.
- **Matrix norm**: the **scoped L2 operator norm** — `open scoped Matrix.Norms.L2Operator`
  — to get submultiplicativity (`Matrix.l2_opNorm_mul`) and the C*-identity, avoiding
  clashes with the default entrywise-sup norm.
- **`GL` encoding**: `A : X → Matrix (Fin d) (Fin d) ℝ` with the hypothesis
  `∀ x, (A x).det ≠ 0` (keeps `A` a plain measurable matrix-valued function; bridge to
  `Matrix.GeneralLinearGroup` only where group structure is needed, e.g. inverse cocycle).
- **`log⁺`**: `Real.posLog = fun r ↦ max 0 (log r)`, notation `log⁺` (exists, rich API).
- **`−∞` / `EReal`**: state **Kingman in `EReal`** (the subadditive limit can be `−∞`)
  to keep it Mathlib-worthy; the *target's* bottom exponent is finite under
  `log⁺‖A⁻¹‖ ∈ L¹`, so the MET-facing corollaries land back in `ℝ`.
- **Exponents decreasing** `λ₁ > ⋯ > λ_k`; flag `V¹ ⊋ ⋯ ⊋ V_k ⊋ 0`,
  `Vⁱ = {v : λ̄(x,v) ≤ λᵢ}` where `λ̄(x,v) = limsup (1/n) log‖A⁽ⁿ⁾(x)v‖`.

## Decision 4 — Mathlib-style layout & namespaces

Develop mirroring where this would live in Mathlib (`Mathlib/Dynamics/Ergodic/…`),
rooted in our lib under `ErgodicTheory/`. Declarations in the natural Mathlib namespaces
(`MeasureTheory`, `Ergodic`, `Dynamics`). Lint-clean, docstringed, one result per
concept (no parallel proofs). Concrete file layout in `implementation-plan.md`.

## Substrate spot-check (done before committing to the plan)

Verified by grep against pinned Mathlib source that the load-bearing M0 substrate
exists by name: `Real.posLog` (+API), `Matrix.l2_opNorm_mul` & scope
`Matrix.Norms.L2Operator`, `Ergodic.ae_eq_const_of_ae_eq_comp_ae`,
`MeasurableSpace.invariants` (`MeasureTheory/MeasurableSpace/Invariants.lean` — the
invariant σ-algebra, takes `(f : α → α)`), `birkhoffAverage`/`birkhoffSum_add`,
`MeasureTheory.condExp` (notation `μ[f | m]`), `setIntegral_condExp`,
`LinearMap.singularValues`, `Flag`, `Subadditive.tendsto_lim` (Fekete). Confirmed the
**pointwise** Birkhoff theorem is absent (only the L² von Neumann mean theorem
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` exists). Exact
import paths are pinned during the skeleton phase against the green build.
