# API notes — exact Mathlib signatures + framing decisions

Grounding for the skeleton/implementation phases. Signatures read from the pinned
Mathlib source (`v4.30.0-rc2`). **Verify against the green build before relying on a
proof; statements below are for getting types right.**

## Framing decision (project-wide) — cocycle, vectors, norms

- **Generator**: `A : X → Matrix (Fin d) (Fin d) ℝ`, measurable, with `∀ x, (A x).det ≠ 0`
  (the `GL(d,ℝ)` encoding). Matrices give the Pi/Borel measurable structure for free
  and `det`/inverse are measurable.
- **Vectors**: `EuclideanSpace ℝ (Fin d)` (= `PiLp 2 (fun _ : Fin d => ℝ)`), so `‖v‖`
  is the **L2** norm. *Not* `Fin d → ℝ` (that carries the sup norm).
- **Matrix norm**: `open scoped Matrix.Norms.L2Operator` → the L2 operator norm
  instances on `Matrix (Fin d) (Fin d) ℝ`. Gives submultiplicativity.
- **Action / bridge to operators**: `Matrix.toEuclideanCLM` :
  `Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)` (a star-algebra
  equiv, hence multiplicative: `toEuclideanCLM (M*N) = toEuclideanCLM M ∘L toEuclideanCLM N`).
  - `‖toEuclideanCLM M‖ = ‖M‖` : `Matrix.l2_opNorm_toEuclideanCLM` (`rfl`).
  - Action on a vector: `Matrix.toEuclideanCLM M v : EuclideanSpace ℝ (Fin d)`, so
    `‖toEuclideanCLM M v‖` is the L2 norm. Use **this** for the growth rate
    `(1/n)·log‖A⁽ⁿ⁾(x) v‖`, i.e. `Real.log ‖Matrix.toEuclideanCLM (cocycle A T n x) v‖`.
  - `‖toEuclideanCLM M v‖ ≤ ‖M‖ * ‖v‖` from `ContinuousLinearMap.le_opNorm` + the norm
    equality; submultiplicativity `‖M*N‖ ≤ ‖M‖*‖N‖` is `Matrix.l2_opNorm_mul`.
  - (Raw `*ᵥ` alternative — avoid in statements: `l2_opNorm_mulVec` is phrased
    `‖(EuclideanSpace.equiv m 𝕜).symm (A *ᵥ x)‖ ≤ ‖A‖ * ‖x‖`; the `equiv.symm` wrapper
    is needed because `A *ᵥ x : m → 𝕜` defaults to the sup norm.)
- **Equivariance**: `Submodule.map (Matrix.toEuclideanCLM (A x)).toLinearMap (V i x) = V i (T x)`
  (or via `LinearEquiv`; `toEuclideanCLM (A x)` is invertible when `det (A x) ≠ 0`).
- **Flag**: do NOT use the order-theoretic `Flag` (maximal chain). Use an explicit
  family `V : Fin (k+1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))`, strictly
  decreasing via `V i.succ x < V i.castSucc x`.

## Exact signatures (verified)

```
-- Dynamics/Ergodic/MeasurePreserving.lean
structure MeasurePreserving (f : α → β) (μ : Measure α) (ν : Measure β) : Prop
-- Dynamics/Ergodic/Ergodic.lean
structure PreErgodic (f : α → α) (μ : Measure α) : Prop
structure Ergodic (f : α → α) (μ : Measure α) : Prop extends MeasurePreserving f μ μ, PreErgodic f μ
-- Dynamics/Ergodic/Function.lean
theorem Ergodic.ae_eq_const_of_ae_eq_comp_ae {g : α → X} (h : Ergodic f μ)
    (hgm : AEStronglyMeasurable g μ) (hg : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] fun _ => c
  -- NOTE: needs an AEStronglyMeasurable hypothesis.

-- MeasureTheory/MeasurableSpace/Invariants.lean
def MeasurableSpace.invariants [m : MeasurableSpace α] (f : α → α) : MeasurableSpace α
theorem measurableSet_invariants {f s} : MeasurableSet[invariants f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s
theorem invariants_le (f) : invariants f ≤ ‹MeasurableSpace α›
theorem le_invariants_iterate (f) (n) : invariants f ≤ invariants (f^[n])

-- MeasureTheory/Function/ConditionalExpectation/Basic.lean
noncomputable irreducible_def condExp (m : MeasurableSpace α) (μ : Measure α) (f : α → E) : α → E
notation  μ[f | m]  := condExp m μ f      -- needs hm : m ≤ m₀ for the defining property
theorem setIntegral_condExp ... : ∫ x in s, (μ[f|m]) x ∂μ = ∫ x in s, f x ∂μ   -- (m-measurable s)

-- Dynamics/BirkhoffSum/{Basic,Average}.lean
def birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := ∑ k ∈ range n, g (f^[k] x)
theorem birkhoffSum_add (f g m n x) : birkhoffSum f g (m+n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x)
def birkhoffAverage (R) (f) (g) (n) (x) : M := (n : R)⁻¹ • birkhoffSum f g n x

-- Analysis/Subadditive.lean  (Fekete — DETERMINISTIC, the model for our cocycle limit object)
def Subadditive (u : ℕ → ℝ) : Prop := ∀ m n, u (m + n) ≤ u m + u n
protected def Subadditive.lim (h : Subadditive u) : ℝ          -- = ⨅ n, u n / n  (informally)
theorem Subadditive.tendsto_lim (h : Subadditive u) (hbdd : BddBelow (Set.range fun n => u n / n)) :
    Tendsto (fun n => u n / n) atTop (𝓝 h.lim)

-- Analysis/SpecialFunctions/Log/PosLog.lean   (notation  log⁺ )
noncomputable def Real.posLog : ℝ → ℝ := fun r => max 0 (log r)
theorem Real.posLog_mul : log⁺ (x*y) ≤ log⁺ x + log⁺ y
theorem Real.posLog_sub_posLog_inv : log⁺ x - log⁺ x⁻¹ = log x
-- + monotoneOn_posLog, posLog_nonneg, posLog_pow, posLog_prod/_sum, posLog_norm_add_le, ...

-- Analysis/CStarAlgebra/Matrix.lean   (open scoped Matrix.Norms.L2Operator)
lemma Matrix.l2_opNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) : ‖A * B‖ ≤ ‖A‖ * ‖B‖
lemma Matrix.l2_opNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(EuclideanSpace.equiv m 𝕜).symm (A *ᵥ x)‖ ≤ ‖A‖ * ‖x‖
lemma Matrix.l2_opNorm_toEuclideanCLM (A : Matrix n n 𝕜) : ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ = ‖A‖ := rfl

-- Analysis/InnerProductSpace/SingularValues.lean   (for multiplicities / two-sided cross-check; M11)
noncomputable def LinearMap.singularValues (T : E →ₗ[𝕜] F) : ℕ →₀ ℝ
theorem LinearMap.singularValues_antitone : Antitone T.singularValues
theorem LinearMap.singularValues_fin {n} (hn : finrank 𝕜 E = n) (i : Fin n) : ...
```

## Confirmed ABSENT (must build)

Pointwise Birkhoff (only L² von Neumann
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`); maximal ergodic
inequality / Hopf / Garsia; Kingman (only Fekete `Subadditive.tendsto_lim`);
`condExp` ∘ measure-preserving composition; cocycle / Lyapunov / Furstenberg–Kesten /
Oseledets; measurable structure on subspaces/flags.

## EReal

`EReal` is a `CompleteLinearOrder`; `Filter.limsup`/`liminf` (Order/LiminfLimsup.lean)
apply. State Kingman's limit in `EReal` (can be `−∞`); the MET-facing corollaries land
in `ℝ` under `log⁺‖A⁻¹‖ ∈ L¹`.
