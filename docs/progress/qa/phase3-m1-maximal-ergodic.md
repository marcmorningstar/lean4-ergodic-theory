# QA sign-off — Phase 3 (M1: maximal ergodic inequality)

_Date: 2026-06-05. Independent checker (fresh context, did not write the code) +
orchestrator mechanical re-verification._

## Verdict: PASS — committable

Independent checker ran build, axiom audit, sorry grep, an **adversarial faithfulness
check** (headline statement vs the QA'd skeleton), and a soundness spot-check of all 14
auxiliary declarations.

## Hard-gate items (independently confirmed)

- `lake build` exit 0; the only `sorry` warnings are the 7 intended foreign gaps
  (MultiplicativeErgodic, Birkhoff×2, Kingman×2, FurstenbergKesten×2). MaximalErgodic
  is sorry-free.
- `#print axioms setIntegral_birkhoffSum_pos_nonneg` = `[propext, Classical.choice,
  Quot.sound]` — no `sorryAx`, no custom axioms (grep empty).
- **Faithfulness:** the headline `setIntegral_birkhoffSum_pos_nonneg` is **byte-identical**
  to the skeleton — takes only `MeasurePreserving T μ μ` + `Integrable f μ`, concludes
  `0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T f (n+1) x}, f x ∂μ` (the faithful Hopf/Garsia
  statement, `n+1` shift correctly excluding the trivial `birkhoffSum 0`). Not weakened;
  no `Measurable` hypothesis snuck into the general theorem (the separate `_of_measurable`
  helper legitimately carries it).
- All 14 auxiliary lemmas (`maxBirkhoff` + nonneg/succ/measurable/integrable,
  `add_sup'_eq`, the Garsia inequality `maxBirkhoff_le_add`, `birkhoffSum_congr_ae`, the
  crux `setIntegral_maxBirkhoff_pos_nonneg`, monotone/iUnion of the positivity sets,
  `_of_measurable`) are mathematically true, non-vacuous, non-circular. Mathlib-style
  names + docstrings; specific imports (no `import Mathlib`).

## Non-blocking notes

- `add_sup'_eq` (constant-pull for `Finset.sup'`) is genuinely missing from Mathlib and a
  clean upstream candidate.
- Minor cosmetic redundancy in `integrable_birkhoffSum` (`have … ; exact this`).
