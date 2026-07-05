# Implementation plan — Oseledets MET (checkpoint 2: self-approved)

Companion to `decision-record.md`, `../research/understanding.md` (layer ladder
L0–L7), and `../research/target-and-milestones.md` (milestones M0–M13). This file
fixes the **module layout**, the **phase breakdown** (one phase = one QA-gated
commit), and the **gate definition**. The dependency graph is not duplicated here —
it lives in `understanding.md §3` (the canonical "bottom→top" diagram).

## Scope realism (read this first)

The target M10 sits on a tower of theorems **none of which exist in Mathlib**:
maximal ergodic inequality → pointwise Birkhoff → Kingman → Furstenberg–Kesten →
limsup flag → measurable-subspace layer → limsup→lim induction. Pointwise Birkhoff
and Kingman are each, on their own, substantial formalizations (genuine Mathlib
contributions). A fully `sorry`-free M10 is a multi-stage effort spanning many
sessions. This plan is therefore built so that **every phase is independently
valuable, lands green with strictly fewer `sorry`s, and is committed** — progress is
monotone and resumable, and we never claim more than is proved. Honest status always
lives in `../progress/STATE.md`.

## Module layout (mirrors `Mathlib/Dynamics/Ergodic/…`)

```
ErgodicTheory.lean                         -- root: imports every module below
ErgodicTheory/
  Ergodic/
    MaximalErgodic.lean        -- L1.1  maximal ergodic inequality (Hopf/Garsia)
    CondExpComp.lean           -- L1.2  condExp commutes with m.p. composition
    Birkhoff.lean              -- L1.3  pointwise (Birkhoff) ergodic theorem
    Subadditive.lean           -- L2.1–2.2  subadditive cocycle predicate + block lemma
    Kingman.lean               -- L2.3–2.6  Kingman subadditive ergodic theorem (EReal)
    Tempering.lean             -- L5.1  (1/n)φ(Tⁿx)→0 tempering corollary of Birkhoff
  Cocycle/
    Basic.lean                 -- L3.1  iterated cocycle, identity, measurability, integrability
    FurstenbergKesten.lean     -- L3.2–3.4  log‖A⁽ⁿ⁾‖ subadditive ⇒ top & bottom exponents
  Lyapunov/
    GrowthFunction.lean        -- L4.1–4.2  λ̄(x,v): finiteness + ultrametric axioms + equivariance
    Ultrametric.lean           -- L4.3  pure ultrametric linear algebra (≤ d values, level subspaces)
    Filtration.lean            -- L4.4  the limsup flag + equivariance
    MeasurableSubspace.lean    -- L4.5 infra  measurable structure on subspaces / selection
    Measurable.lean            -- L4.5  measurability of k, λᵢ, x ↦ Vⁱₓ
    Subbundle.lean             -- L5.2  extremes on an invariant subbundle are genuine limits
    Limit.lean                 -- L5.3–5.5  block-triangular + peel + induction ⇒ genuine lim
  MultiplicativeErgodic.lean   -- L6.1  TARGET: one-sided MET (filtration)
```

(Future, not in the initial target: `Lyapunov/ExteriorPower.lean` = M11,
`MultiplicativeErgodic/Splitting.lean` = M12, non-ergodic = M13. Created only when
reached.) File names/splits may be refined during the skeleton phase as the API firms
up — the layout, not the exact file boundaries, is the commitment.

## Phase breakdown (one phase → one commit, gated)

Phases are ordered so each is buildable on its predecessors. Statement scaffolding is
**top-down** (Phase 0 writes the target + every milestone statement as `sorry`);
filling is then **bottom-up** (you cannot prove Birkhoff before the maximal
inequality). "Closeable now" = no dependency on an unproved hard theorem.

| Phase | Content (layers) | Depends | Difficulty / closeable this run? |
|---|---|---|---|
| **0 Skeleton** | All statements (L1.1–L6.1) as `sorry` theorems in the layout above; conventions pinned; target's proof cites the milestones; green build | green build | **Yes** — scaffold only |
| **1 Cocycle infra** | L3.1: `cocycle`, cocycle identity, measurability, `Integrable (log⁺‖A·‖)` predicate + basic posLog/integrability lemmas | P0 | **Yes** — self-contained |
| **2 condExp∘MP** | L1.2 (`CondExpComp`) | P0 | **Yes** — builds on existing condExp API |
| **3 Ultrametric LA** | L4.3 (`Ultrametric`): function with ultrametric growth axioms ⇒ ≤ d values, level sets are subspaces | P0 | **Yes** — pure linear algebra, no dynamics |
| **4 Maximal ergodic ineq** | L1.1 (`MaximalErgodic`) | P0 | Hard but self-contained (Garsia's proof is short) — **attempt to close** |
| **5 Pointwise Birkhoff** | L1.3 (`Birkhoff`) + L5.1 (`Tempering`) | P2,P4 | Hard — **stretch**; classical, gated by P4 |
| **6 Kingman** | L2.1–2.6 (`Subadditive`,`Kingman`) | P5 | Hardest analytic piece (greedy covering) — **stretch** |
| **7 Furstenberg–Kesten** | L3.2–3.4 (`FurstenbergKesten`) | P1,P6 | Moderate once Kingman lands |
| **8 limsup spectrum/flag** | L4.1,4.2,4.4 (`GrowthFunction`,`Filtration`) | P3,P7 | Moderate |
| **9 Measurability** | L4.5 (`MeasurableSubspace`,`Measurable`) | P8 | Infra-heavy (no Borel structure on subspaces) |
| **10 limsup→lim** | L5.2–5.5 (`Subbundle`,`Limit`) | P5,P8 | Hard (induction-on-dimension) |
| **11 Assemble target** | L6.1 (`MultiplicativeErgodic`) | P8,P9,P10 | Glue |

Realistic ambition for the current autonomous run: **close Phases 0–3 fully**, push
hard on **Phase 4 (maximal ergodic inequality)** and **Phase 5 (Birkhoff)** — both are
classical and tractable — and leave Phases 6–11 as well-structured `sorry`s with the
statements locked. Each closed phase is committed; the deep theorems advance as far as
focused agent work allows without ever breaking the build or hiding a `sorry`.

## The hard gate (every phase, before the next begins)

A phase is **done** only when ALL of:
1. `lake build` is green.
2. The only remaining `sorry`s are intended, *planned* gaps, and there are
   **strictly fewer** than before the phase (skeleton phase: it introduces the
   planned `sorry`s and proves none — that is its defined deliverable). Every `sorry`
   is flagged in `STATE.md`.
3. No new axioms (`#print axioms <target>` shows only Mathlib's standard axioms:
   `propext`, `Classical.choice`, `Quot.sound`).
4. An **independent checker agent** (fresh context, did not write the code) confirms
   1–3, reviews Mathlib-style + mathematical correctness, and verifies the phase
   closed the gaps it claimed. Sign-off required.
5. On sign-off: a single **git commit** (Mathlib-style message, one phase per commit,
   ending with the repo `Co-Authored-By` line) that includes the code **and** the
   updated `../progress/STATE.md`.

On failure: fix or re-plan; never advance.

## Tooling

- `lean-worker` agent for direct proof/definition implementation.
- `mathematician` agent for adversarial exploration, counterexample-hunting on tricky
  lemmas, and proof-strategy verification before committing to a Lean attempt.
- Dynamic **workflows** for fan-out (parallel lemma implementation within a phase,
  parallel independent checkers, completeness critics).
- Build is incremental; after the first green build, `lake build` is the inner loop.
- `firecrawl` for any further source lookups (Steele's Kingman proof, Garsia's lemma).
