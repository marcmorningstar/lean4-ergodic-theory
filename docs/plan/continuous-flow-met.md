# Blueprint — Continuous-flow Oseledets MET

*Status: in implementation (2026-06-16). Phase-by-phase via warm-REPL `lean-worker`s,
adversarially audited, cold-build gated, axiom guarded — the same workflow that produced
the two-sided splitting (#10).*

## Goal

A **continuous-time** Oseledets multiplicative ergodic theorem: replace the single
measure-preserving map `T : X → X` and its iterates by a one-parameter
**measure-preserving flow** `φ : ℝ → X → X` and a **continuous-time linear cocycle**
`A : ℝ → X → Matrix (Fin d) (Fin d) ℝ`, and conclude with finitely many Lyapunov
exponents `λ₁ > ⋯ > λ_k`, a measurable **flow-equivariant** filtration, and the exact
**continuous-parameter** growth `(1/t) log‖A(t,x) v‖ → λᵢ` as `t → ∞` over `ℝ`.

Motivation (recorded, out of scope to pursue here): a clock-free / relational-time
formulation — the conclusion is a statement about the continuous parameter `t ∈ ℝ`, with
no privileged unit step; the integer clock appears only as a technical reduction device.

## Strategy — reduce to the proved discrete theorem via the time-1 map

We do **not** redevelop the ergodic machinery for ℝ. Instead set `T := φ 1`,
`Ã := A(1, ·)`, observe that the discrete iterated cocycle of `Ã` over `T` *equals* the
flow cocycle sampled at integer times, apply the completed
`Oseledets.oseledets_filtration'`, and lift the integer-time conclusion to the continuous
parameter with a **between-times** estimate. This avoids a continuous-time Kingman
theorem entirely (Mathlib has only the discrete Fekete `Subadditive.tendsto_lim`).

### Two pivotal repo lemmas already exist (collapse the two hardest nodes)

* **Between-times sublinearity engine** — `Oseledets.ae_tendsto_orbit_div_atTop_zero`
  (`Oseledets/Ergodic/Birkhoff.lean:203`):
  `(hT : MeasurePreserving T μ μ) (hg : Integrable g μ) → ∀ᵐ x, Tendsto (n ↦ n⁻¹ · g (T^[n] x)) atTop (𝓝 0)`.
* **Intrinsic growth characterization** (⇒ flow-invariance) —
  `Oseledets.IsOseledetsFiltration.ae_mem_iff_limsup_le` (`Oseledets/Lyapunov/Corollaries.lean:266`):
  a.e. `v ∈ Vⁱ_x ↔ v = 0 ∨ limsup (n⁻¹ · log‖A⁽ⁿ⁾(x) v‖) ≤ λᵢ`.

### Mathlib pieces used (from the scout survey)

* Discrete hypothesis plumbing: `Ergodic`, `MeasurePreserving`, `MeasurePreserving.iterate`.
* Floor sandwich: `tendsto_nat_floor_atTop`, `tendsto_natCast_atTop_atTop`,
  `tendsto_nat_floor_div_atTop` (`(⌊t⌋₊ : ℝ)/t → 1`), all for ℝ.
* `Real.posLog` (= `log⁺`), L2 operator norm (`Matrix.Norms.L2Operator`), `Matrix.toEuclideanCLM`.

### Design decisions

* **Bespoke `MeasurePreservingFlow`** (no topology on `X`): bundles `toFun : ℝ → X → X`,
  `map_zero'`, `map_add'`, `measurePreserving'`. `Flow ℝ X` is rejected — it forces a
  `TopologicalSpace X` and joint continuity we neither have nor want.
* **Ergodicity is a *separate* hypothesis `Ergodic (φ 1) μ`** (the time-1 map). Flow
  ergodicity does *not* imply time-1 ergodicity (Mathlib has no such lemma, and it is
  false in general). Requiring the time-1 map ergodic is the standard, honest input that
  lets the discrete theorem deliver *constant* exponents.
* **Integrability in dominated form.** Hypotheses `g, g' : X → ℝ` integrable with
  `∀ s ∈ [0,1], ∀ x, log⁺‖A(s,x)‖ ≤ g x` and `… ‖A(s,x)⁻¹‖ ≤ g' x`. Equivalent to (and
  slightly more general than) `sup_{s∈[0,1]} log⁺‖A(s,·)^±1‖ ∈ L¹`; avoids the
  compact-interval-sup measurability infra Mathlib lacks. Feeds **both** the discrete
  `IntegrableLogNorm (A 1)` / `IntegrableLogNorm (A 1)⁻¹` inputs (take `s = 1`) and the
  between-times error bound `|log‖A(s,φₙx)^{±1}‖| ≤ (g + g')(φₙx)`.
* **Per-time equivariance.** State flow-equivariance as `∀ t, ∀ᵐ x, …` (not `∀ᵐ x, ∀ t`),
  the standard measurable-cocycle-over-a-flow form; the latter hides an uncountable
  null-set union. Provable from the growth characterization + `φ t` measure-preserving.

## The orientation / reduction identity (verified on paper)

Cocycle identity `A(t+s, x) = A(t, φ_s x) · A(s, x)`, `A(0,·) = 1`. Newest factor on the
left, matching `Oseledets.cocycle` (`cocycle A T (n+1) x = cocycle A T n (T x) · A x`).

* **Integer sampling:** `A((n:ℝ), x) = cocycle (A 1) (φ 1) n x` by induction on `n`.
  Step: `A((n+1:ℝ),x) = A((n:ℝ)+1,x) = A(n, φ₁ x)·A(1,x) = cocycle … n (φ₁ x) · Ã x`.
  Needs `φ (n:ℝ) = (φ 1)^[n]` (induction from `map_zero'`/`map_add'`).
* **Between-times sandwich:** write `t = n + s`, `n = ⌊t⌋₊`, `s ∈ [0,1)`. Then
  `A(t,x) = A(s, φₙ x)·A(n,x)`, so
  `log‖A(n,x)v‖ − log‖A(s,φₙx)⁻¹‖ ≤ log‖A(t,x)v‖ ≤ log‖A(s,φₙx)‖ + log‖A(n,x)v‖`.
  Both error terms are `≤ (g+g')(φₙ x)` in absolute value (using `‖M‖‖M⁻¹‖ ≥ 1`), and
  `n⁻¹·(g+g')((φ 1)^[n] x) → 0` a.e. by `ae_tendsto_orbit_div_atTop_zero`; together with
  `⌊t⌋₊/t → 1` this gives `(1/t) log‖A(t,x)v‖ → λᵢ` from the discrete limit.

## Modules & phases (under `Oseledets/Continuous/`)

| Phase | Module | Content |
|---|---|---|
| **P0** | `Flow.lean` | `structure MeasurePreservingFlow` (+ `CoeFun`, `map_zero`, `map_add`, `apply_add`, `measurePreserving`, `measurable`, `natCast_eq_iterate`); `structure FlowCocycle φ d` (+ `CoeFun`, `map_zero`, `cocycle_apply`, `det_ne_zero`, `measurable`); the **reduction identity** `toCocycle_eq : A ((n:ℝ)) x = cocycle (A 1 ·) (φ 1) n x`. |
| **P1** | `BetweenTimes.lean` | The sandwich estimate ⇒ for a.e. `x`, if `n⁻¹ log‖A(n,x)v‖ → L` (discrete) then `t⁻¹ log‖A(t,x)v‖ → L` over `atTop ℝ`. Uses `ae_tendsto_orbit_div_atTop_zero`, `tendsto_nat_floor_div_atTop`. |
| **P2** | `Reduction.lean` | Derive `IntegrableLogNorm (A 1 ·)` and `… (A 1 ·)⁻¹` from `g,g'`; apply `oseledets_filtration'` to `(φ 1, A 1)`; expose the discrete `IsOseledetsFiltration` datum + a "discrete→continuous growth" wrapper (P1) on each stratum. |
| **P3** | `MultiplicativeErgodicFlow.lean` | Headline **`oseledets_flow`**: `∃ k lam V`, `StrictAnti lam`, `MeasurableSubspace`, per-time flow-equivariance `∀ t, ∀ᵐ x, map (A t x) (Vⁱ x) = Vⁱ (φ t x)` (via `ae_mem_iff_limsup_le` + same-growth under time-shift), and `∀ᵐ x`, the flag + continuous-time exact growth. |
| **P4** | wiring | Import the four modules from `Oseledets.lean` and `AxiomAudit.lean`; add `#guard_msgs in #print axioms` for `oseledets_flow` (+ exported lemmas), expect `[propext, Classical.choice, Quot.sound]`. Authoritative cold umbrella `lake build` + per-file linter QA. Mathlib-style commit. |

## Headline statement (target)

```
theorem oseledets_flow {X} [MeasurableSpace X] {d : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (φ : MeasurePreservingFlow μ) (herg : Ergodic (φ 1) μ)
    (A : FlowCocycle φ d)
    (g g' : X → ℝ) (hg : Integrable g μ) (hg' : Integrable g' μ)
    (hgb  : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ x, Real.posLog ‖A s x‖     ≤ g x)
    (hg'b : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ x, Real.posLog ‖(A s x)⁻¹‖ ≤ g' x) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => V i x) ∧
      (∀ t : ℝ, ∀ᵐ x ∂μ, ∀ i : Fin (k + 1),
        Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x)).toLinearMap (V i x)
          = V i (φ t x)) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
          v ∉ V i.succ x →
          Tendsto (fun t : ℝ => t⁻¹ *
            Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A t x) v‖) atTop (𝓝 (lam i)))
```

## Invariants

* Strictly **additive**: nothing in the existing development is renamed/weakened/removed.
* **Sorry-free**; toolchain unchanged (`v4.30.0-rc2`, pinned Mathlib).
* Authoritative gate is the **cold umbrella `lake build`** + guarded `AxiomAudit`
  (`[propext, Classical.choice, Quot.sound]`); warm REPL is an inner-loop accelerator only.

## Recorded follow-ups (out of scope for this pass)

* Strengthen integrability hypothesis to the `sup`-form by building the missing
  compact-interval-sup measurability lemma (continuity-in-`t` + `Rat.denseRange_cast` +
  countable `Measurable.iSup`).
* Upgrade per-time equivariance to `∀ᵐ x, ∀ t` via joint measurability of `(t,x) ↦ φ t x`
  + Fubini on `ℝ × X`.
* Flow-ergodic ⇒ time-1-ergodic descent lemma (when it holds).
```
