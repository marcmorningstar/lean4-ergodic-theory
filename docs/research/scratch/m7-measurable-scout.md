# M7 (Lyapunov/Measurable.lean) — Mathlib availability scout

Scouted 2026-06-06 while the Filtration worker built. Confirms the blueprint §4.3/§7
**fixed-threshold mitigation** is the route (raw analytic projection is NOT available as a
Borel statement).

## Available (use directly)

- `Measurable.limsup {f : ℕ → δ → α} (hf : ∀ i, Measurable (f i)) : Measurable (fun x => limsup (fun n => f n x) atTop)`
  — `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:1065`. Gives
  `Measurable (fun x => lambdaBar A T x v)` for fixed `v` (compose `measurable_cocycle`,
  `toEuclideanCLM` continuous, `Real.log` measurable).
- `Ergodic.ae_eq_const_of_ae_eq_comp_ae (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ)
  (h_eq : g ∘ f =ᵐ g) : ∃ c, g =ᵐ const` — `Mathlib/Dynamics/Ergodic/Function.lean:103`.
  This is the a.e.-constancy engine (needs `AEStronglyMeasurable g`, so still need SOME
  measurability of the exponent functions first).
- FK extremes are **already a.e. constant for free**: `furstenbergKesten_top`/`_bot` return
  `∃ lamTop, ∀ᵐ x, Tendsto … (𝓝 lamTop)` — `lamTop`/`lamBot` are single ℝ constants. So
  `specList … 0` (= top) and `specList … (last)` (= bottom) need NO peeling.

## NOT available (the gap / the real work)

- **Measurable projection** of a product-measurable set onto `x` is only in
  `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean` (analytic/Suslin; Borel→analytic,
  universally measurable, NOT Borel). ⇒ Do NOT define `specCard`/`specList` via projection.
  Use **fixed thresholds** under ergodicity: prove `specList` a.e. constant `lam : Fin k → ℝ`,
  then `Vflag x i = sublevel (lambdaBar A T x) (lam i)`; membership
  `lambdaBar A T x (e j) ≤ lam i` is measurable in `x` (limsup of measurables).
- **`gramSchmidt` measurability**: no prepackaged lemma in `GramSchmidtOrtho.lean`. Must build
  it (algebraic in inner products ⇒ `fun_prop`/`Measurable.inner`-amenable, but real work) for
  the measurable orthonormal frame → `orthProjMatrix` → `MeasurableSubspace`.

## Recursion caveat

`Ergodic.ae_eq_const_of_ae_eq_comp_ae` needs `AEStronglyMeasurable specList`, so a.e.-constancy
is not entirely free of the measurability work. Plan: (a) measurability of `x ↦ lambdaBar A T x v`
(easy); (b) measurability of `specCard`/`specList` via thresholding against the basis — may
itself lean on a.e.-constant `lam`, so structure as: extremes constant from FK → peel interior
via measurable sublevel-dimension `trace (orthProjMatrix …)` (integer-valued measurable) rather
than projection. Consider splitting M7 into two sub-phases (measurability-of-exponents, then
measurable-frame) if one worker stalls.
