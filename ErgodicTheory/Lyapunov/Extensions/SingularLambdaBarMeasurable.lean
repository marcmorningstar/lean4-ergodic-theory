/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.SingularSlowSpaceUnconditional
import ErgodicTheory.Lyapunov.Filtration
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Measurability of the `lambdaBar`-sublevel slow space for singular cocycles

For a **possibly-singular** (non-invertible, `det A = 0` allowed) matrix cocycle generator
`A : X → Matrix (Fin d) (Fin d) ℝ`, the intermediate slow space of the singular forward Oseledets
filtration at a Lyapunov cut `c` is the `lambdaBar`-sublevel

  `lambdaSublevel A T x c = {v : lambdaBar A T x v ≤ c}`   (det-free; `lambdaBar` is det-free,

`ErgodicTheory/Lyapunov/GrowthFunction.lean`). Track 6B asks the **last open** measurability question of
the unconditional singular flag: is `x ↦ {v : lambdaBar A T x v ≤ c}` a `MeasurableSubspace`?

This module **resolves the measurability question to a single, precisely-named convergence input**
and lands the reduction sorry-free and det-free, then pins exactly why the input cannot be supplied
unconditionally for singular cocycles.

## The reduction (sorry-free, det-free)

The finite-step slow approximants `vSlowSingularStep A T s n x` — the range of the slow `qpow`
spectral projector `cfc (𝟙_{(-∞,s]}) (qpow A T n x)`, where `qpow A T n x = (Gₙ)^{1/(2n)}` is the
renormalized Gram (`SingularSlowSpace.lean`) — are **everywhere measurable in `x`**, per fixed `n`
(`measurableSubspace_vSlowSingularStep`), unconditionally. Here the multiplier threshold `s` cuts
the `qpow` eigenvalues `σᵢ(cocycle n x)^{1/n}` (limits `e^{λᵢ}`), so to converge to the **exponent**
sublevel `{v : lambdaBar A T x v ≤ c}` the finite-step cut must sit at `s = Real.exp c`
(`σᵢ^{1/n} ≤ exp c ⟺ (1/n) log σᵢ ≤ c ⟶ λᵢ ≤ c`). If those finite-step *projector matrices*
converge — for every `x` — to the projector matrix of the `lambdaBar`-sublevel, then the limit is
measurable as a pointwise limit of measurable matrix-valued maps
(`measurable_of_tendsto_metrizable`, entrywise). We package:

* `ErgodicTheory.measurableSubspace_of_tendsto_orthProjMatrix` — the **fully general** soft lemma: a
  family `V` whose `orthProjMatrix` is, for every `x`, the pointwise (in `n`) limit of a sequence of
  *measurable* matrix families is a `MeasurableSubspace`. (The same
  `measurable_of_tendsto_metrizable` template as `ErgodicTheory.MeasurableSubspace.inf` and
  `ErgodicTheory.measurable_orthProjMatrix_eventualKer`.)

* `ErgodicTheory.measurableSubspace_lambdaSublevel_of_tendsto` — the **det-free reduction**: if for
  every `x` the slow projectors `orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x)` (the
  multiplier cut at `Real.exp c`, the honest scale for the exponent sublevel at `c`) converge to
  `orthProjMatrix (lambdaSublevel A T x c)`, then
  `MeasurableSubspace (fun x => lambdaSublevel A T x c)`. No `det ≠ 0`. The measurability of
  `{v : lambdaBar A T x v ≤ c}` is thereby reduced **exactly** to the convergence-to-the-right-limit
  hypothesis `hconv`.

## The wall (precisely pinned — why `hconv` is not unconditional)

`hconv` is the conjunction of two facts, **both** of which fail det-free for singular cocycles:

1. **The slow projectors converge at all.** `orthProjMatrix (vSlowSingularStep A T c n x) =
   1 − bandProjector A T (𝟙_{(c,∞)}) n x` (`orthProjMatrix_vSlowSingularStep`), so their convergence
   is *exactly* the fast band-projector convergence. By
   `ErgodicTheory.bandProjector_increment_eq_aperture` (`SingularSlowSpaceUnconditional.lean`) the
   per-step band increment `‖Pₙ₊₁ − Pₙ‖` is the **aperture** `‖V Vᵀ − U Uᵀ‖` between the top-`k`
   right-singular frames of `cocycle n x` and `cocycle (n+1) x = B·(cocycle n x)`, `B = A(Tⁿx)`;
   Davis–Kahan governs it by the **condition number of the single step `B`** (the inverse
   `‖(compound k B)⁻¹‖`), not by any forward singular ratio. A single rank-dropping step
   (`σ_k(B) = 0`, allowed when `det B = 0`) makes the increment `O(1)`, breaking summability.
   This is the Cauchy/aperture wall, already proved walled (`bandProjector_increment_eq_aperture`).

2. **The limit is the `lambdaBar`-sublevel.** Even granting convergence, identifying the limit slow
   space with `{lambdaBar ≤ c}` is the per-vector *spectral upper bound*
   `ErgodicTheory.limsup_le_of_mem_vslow` (`vslow ⊆ lambdaSublevel`,
   `ErgodicTheory/Lyapunov/LimitSlowSpaceSpectralBound.lean`), whose only route is the full Ruelle Lemma
   1.4 cofactor chain on the orthogonal change of basis between the time-`n` Gram eigenbasis and the
   **limit eigenbasis of `Λ = oseledetsLimit`** — and `Λ` itself exists only for invertible cocycles
   (`tendsto_oseledetsLimit` carries `hA : ∀ x, (A x).det ≠ 0`), because the per-`σ` exponent limit
   `tendsto_log_singularValue` needs every `σ_i > 0` (`singularValues_cocycle_pos hA`, `sprod_pos
   hA`). A singular cocycle's bottom singular values hit `0`, `log 0` is junk, and the renormalized
   eigenvalues at the bottom do not converge.

So `hconv` is supplied — and `{v : lambdaBar ≤ c}` is measurable — exactly on the **tempered class**
where the compound condition number is subexponential (`tendsto_vSlowSingularStep_of_tempered`,
`SingularSlowSpaceUnconditional.lean`, which delivers the convergence half of `hconv`, modulo the
limit-identification half), and the unconditional case stays walled at the aperture
(`bandProjector_increment_eq_aperture`) and at the `Λ`-eigenbasis (the missing Mathlib fact:
**continuity of sorted Hermitian eigenvalues/eigenvectors** and a normalized renormalized-Gram limit
for singular matrices — neither in Mathlib, and the latter mathematically false at the kernel
stratum where the limsup growth is `0`, not `−∞`).

## Main results

* `ErgodicTheory.measurableSubspace_of_tendsto_orthProjMatrix` — soft pointwise-limit measurability of a
  subspace family (general, reusable).
* `ErgodicTheory.measurableSubspace_lambdaSublevel_of_tendsto` — the det-free reduction of
  `{v : lambdaBar ≤ c}` measurability to the slow-projector convergence-to-the-sublevel `hconv` (the
  finite-step multiplier cut at `Real.exp c`, matching the exponent sublevel at `c`).
* `ErgodicTheory.orthProjMatrix_vSlowSingularStep_tendsto_iff_bandProjector` — `hconv` is equivalent to
  the convergence of the finite-step slow projectors to `orthProjMatrix (lambdaSublevel A T x c)`,
  re-stated through the complement bridge `1 − bandProjector` to expose the aperture wall.

## References

* A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1).
* D. Ruelle, *Ergodic theory of differentiable dynamical systems*, Publ. Math. IHÉS **50** (1979),
  Lemma 1.4.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
-/

open MeasureTheory Filter Topology Matrix

noncomputable section

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## The general soft lemma: pointwise-limit measurability of a subspace family

A subspace family is a `MeasurableSubspace` whenever its `orthProjMatrix` is, for every base point,
the pointwise (in the sequence index) limit of a sequence of measurable matrix-valued families. This
is the entrywise `measurable_of_tendsto_metrizable` template, identical in shape to
`ErgodicTheory.MeasurableSubspace.inf` and `ErgodicTheory.measurable_orthProjMatrix_eventualKer`; we isolate
it so any convergent measurable projector sequence yields measurability of its limit subspace. -/

/-- **Pointwise-limit measurability of a subspace family.** If `V : X → Submodule …` and there is a
sequence `P : ℕ → X → Matrix (Fin d) (Fin d) ℝ` of measurable matrix families with, for every `x`,
`P n x → orthProjMatrix (V x)` along `atTop`, then `MeasurableSubspace V`. The projector matrix of
each `V x` is the pointwise limit of the measurable `P n`, so it is measurable entrywise
(`measurable_of_tendsto_metrizable`). -/
theorem measurableSubspace_of_tendsto_orthProjMatrix
    (V : X → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (P : ℕ → X → Matrix (Fin d) (Fin d) ℝ) (hP : ∀ n, Measurable (P n))
    (hconv : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 (orthProjMatrix (V x)))) :
    MeasurableSubspace V := by
  unfold MeasurableSubspace
  -- reduce to entrywise measurability of the limit matrix
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  -- each entry of `P n` is measurable
  have hentry : ∀ n : ℕ, Measurable fun x => P n x i j :=
    fun n => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hP n))
  -- and the `i j` entry converges pointwise to the limit's `i j` entry
  refine measurable_of_tendsto_metrizable hentry ?_
  refine tendsto_pi_nhds.2 fun x => ?_
  have hx := hconv x
  exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hx i) j)

/-! ## The det-free reduction for the `lambdaBar`-sublevel slow space

The finite-step slow approximants `vSlowSingularStep A T (Real.exp c) n x` — the multiplier cut at
`Real.exp c`, whose `qpow` eigenvalues `σᵢ^{1/n}` limit to `e^{λᵢ}`, so that the cut matches the
**exponent** sublevel at `c` — have everywhere-measurable projector matrices
(`measurableSubspace_vSlowSingularStep`, unconditional). Feeding them into the soft lemma reduces
measurability of `{v : lambdaBar A T x v ≤ c} = lambdaSublevel A T x c` to a **single** hypothesis:
that those finite-step projectors converge, for every `x`, to the projector of the sublevel. -/

/-- **Det-free reduction of `{lambdaBar ≤ c}` measurability.** If, for every `x`, the finite-step
slow projectors `orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x)` converge to
`orthProjMatrix (lambdaSublevel A T x c)`, then `x ↦ lambdaSublevel A T x c` — the
`lambdaBar`-sublevel slow space `{v : lambdaBar A T x v ≤ c}` — is a `MeasurableSubspace`. **No
`det ≠ 0`.**

**The scales match honestly.** `vSlowSingularStep A T s` cuts the `qpow` eigenvalues
`σᵢ(cocycle n x)^{1/n}` (the *multiplier* scale, whose limits are `e^{λᵢ}`) at the threshold `s`,
whereas `lambdaSublevel A T x c` cuts the *exponents* `λ = lambdaBar A T x` at `c`. The finite-step
multiplier cut therefore has to sit at `s = Real.exp c` to converge to the exponent sublevel at `c`:
`σᵢ^{1/n} ≤ Real.exp c ⟺ (1/n) log σᵢ ≤ c ⟶ λᵢ ≤ c`. Hence `hconv` pairs
`vSlowSingularStep A T (Real.exp c)` with `lambdaSublevel A T x c`.

The finite-step projectors are measurable per `n` unconditionally
(`measurableSubspace_vSlowSingularStep`), so the conclusion follows from the pointwise-limit soft
lemma `measurableSubspace_of_tendsto_orthProjMatrix`. The convergence hypothesis `hconv` is the
genuine residual: it is the band-projector convergence (the aperture wall,
`bandProjector_increment_eq_aperture`) together with the limit being the sublevel (the spectral
upper bound `limsup_le_of_mem_vslow`); both are supplied only on the tempered class. -/
theorem measurableSubspace_lambdaSublevel_of_tendsto [NeZero d]
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) {T : X → X} (hT : Measurable T) (c : ℝ)
    (hconv : ∀ x, Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x)) atTop
      (𝓝 (orthProjMatrix (lambdaSublevel A T x c)))) :
    MeasurableSubspace (fun x => lambdaSublevel A T x c) := by
  refine measurableSubspace_of_tendsto_orthProjMatrix _
    (fun n x => orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x)) (fun n => ?_) hconv
  exact measurableSubspace_vSlowSingularStep hA hT (Real.exp c) n

/-! ## Exposing the aperture wall inside `hconv`

The complement bridge `orthProjMatrix (vSlowSingularStep A T c n x) = 1 − bandProjector …`
(`orthProjMatrix_vSlowSingularStep`) re-states `hconv` as the convergence of `1 − bandProjector` to
the sublevel projector, equivalently of the **fast** band projector to its complement. This makes
visible that the convergence half of `hconv` is the band-projector convergence whose per-step
increment is the aperture between consecutive top-`k` singular frames
(`bandProjector_increment_eq_aperture`), the precise quantity the inverse (condition number of the
single step) is load-bearing for. -/

/-- **`hconv` through the complement bridge.** For every `x`, the finite-step slow projectors
`orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x)` converge to
`orthProjMatrix (lambdaSublevel A T x c)` iff the complements
`1 − bandProjector A T (𝟙_{(exp c,∞)}) n x` do — i.e. iff the fast band projectors converge to
`1 − orthProjMatrix (lambdaSublevel A T x c)`. This re-expresses the residual convergence input of
`measurableSubspace_lambdaSublevel_of_tendsto` directly on the fast band (at the matching multiplier
threshold `Real.exp c`, the honest scale for the exponent sublevel at `c`; see that theorem), where
its per-step increment is the aperture `bandProjector_increment_eq_aperture` governed by the
condition number of the step `B = A(Tⁿx)` (the inverse), pinning why it is not summable for a
singular step. -/
theorem orthProjMatrix_vSlowSingularStep_tendsto_iff_bandProjector [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (c : ℝ) (x : X) :
    Tendsto (fun n => orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x)) atTop
        (𝓝 (orthProjMatrix (lambdaSublevel A T x c)))
      ↔ Tendsto (fun n => bandProjector A T (Set.indicator (Set.Ioi (Real.exp c)) 1) n x) atTop
          (𝓝 (1 - orthProjMatrix (lambdaSublevel A T x c))) := by
  constructor
  · intro h
    -- `bandProjector = 1 − (1 − bandProjector) = 1 − orthProjMatrix (vSlow …)`.
    have hcompl : (fun n => bandProjector A T (Set.indicator (Set.Ioi (Real.exp c)) 1) n x)
        = fun n => 1 - orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x) := by
      funext n
      rw [orthProjMatrix_vSlowSingularStep]; abel
    rw [hcompl]
    exact tendsto_const_nhds.sub h
  · intro h
    have hcompl : (fun n => orthProjMatrix (vSlowSingularStep A T (Real.exp c) n x))
        = fun n => 1 - bandProjector A T (Set.indicator (Set.Ioi (Real.exp c)) 1) n x := by
      funext n; exact orthProjMatrix_vSlowSingularStep A T (Real.exp c) n x
    rw [hcompl]
    -- `1 − band → 1 − (1 − orthProj) = orthProj`.
    have hsub : Tendsto (fun n => (1 : Matrix (Fin d) (Fin d) ℝ)
        - bandProjector A T (Set.indicator (Set.Ioi (Real.exp c)) 1) n x) atTop
        (𝓝 (1 - (1 - orthProjMatrix (lambdaSublevel A T x c)))) :=
      tendsto_const_nhds.sub h
    have hsimp : (1 : Matrix (Fin d) (Fin d) ℝ) - (1 - orthProjMatrix (lambdaSublevel A T x c))
        = orthProjMatrix (lambdaSublevel A T x c) := by abel
    rwa [hsimp] at hsub

end ErgodicTheory
