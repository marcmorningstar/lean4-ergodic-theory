# Plan: Analytic sets are universally measurable (Frontier/Issue6/AnalyticUnivMeasMeasure.lean)

## Target (must MATCH MeasurableProjection.lean line ~139)
```
theorem MeasureTheory.AnalyticSet.nullMeasurableSet
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {s : Set X} (hs : AnalyticSet s) (μ : Measure X) : NullMeasurableSet s μ
```

## Mathlib facts confirmed PRESENT
- `MeasureTheory.AnalyticSet` = `s = ∅ ∨ ∃ f : (ℕ→ℕ)→X, Continuous f ∧ range f = s`.
- `analyticSet_iff_exists_polishSpace_range`.
- `instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace`: any measure on a
  Polish/BorelSpace is `InnerRegularCompactLTTop` — inner regular by compacts for
  finite-measure measurable sets. So Borel sets of finite measure are approx from inside
  by compacts. (RegularityCompacts.lean)
- `Measure.InnerRegularCompactLTTop` instance ⇒ measurable finite-measure sets inner regular.
- `ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : NullMeasurableSet s μ)
   (ht : μ t ≠ ∞) : s =ᵐ[μ] t`.
- `NullMeasurableSet.congr`, `MeasurableSet.nullMeasurableSet`.
- For a `Measure`, `μ s` is already the OUTER measure value on arbitrary `s`.

## Mathlib facts confirmed ABSENT
- No `AnalyticSet.nullMeasurableSet` / universal measurability.
- No capacity / Choquet framework.

## Reduction chain (top → core)
1. **Reduce to finite μ.** A measure on a Polish (hence σ-compact-ish? no — but) standard Borel
   space. Actually: reduce to PROBABILITY/finite. For the MET μ is a probability measure, but
   target is for ALL μ. General σ-finite reduction: NullMeasurable is local; use the
   `Measure.toFinite`/exhaustion. SIMPLER first pass: prove for finite μ, then handle general μ
   by `nullMeasurableSet` being checkable against a finite equivalent? Investigate
   `restrict`/`sigmaFinite` exhaustion. For now target finite μ then extend.

2. **Core (CAPACITABILITY): for finite μ and analytic A, ∃ Borel B ⊆ A with μ B = μ A.**
   Then `ae_eq_of_subset_of_measure_ge B⊆A, μA ≤ μB (from = and B⊆A gives ≤ both ways),
   NullMeasurableSet B (Borel), μ A ≠ ∞ (finite)` ⇒ `B =ᵐ A` ⇒ A NullMeasurable via congr.

3. **Capacitability core proof.** A = range f, f : (ℕ→ℕ)→X continuous.
   For r < μ A want compact K ⊆ A with r < μ K; equivalently μ A = sup over compact K ⊆ A.
   Then choose Kₙ ⊆ A compact with μ Kₙ → μ A, B = ⋃ Kₙ Borel (compacts are closed in metric),
   μ B = μ A, B ⊆ A. Done.

   Inner-approx core: define for finite sequences the closed "Souslin cells"
   `f '' cylinder ...`. The Choquet argument (Pollard §3, §5; Kechris 17.A): for ε>0 build
   nested closed sets with compact-closure whose images stay within ε of μ A and intersect to a
   compact subset of A. THIS is the genuinely hard inductive step.

## Risk / residual
The capacitability induction is the substantial part. If it cannot be fully discharged in time,
isolate it as ONE named sorry `capacitability_core` with precise statement, everything else
sorry-free, and report Pollard §5 as the missing step.
