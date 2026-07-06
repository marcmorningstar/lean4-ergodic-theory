/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.RuelleCore
import ErgodicTheory.Lyapunov.OseledetsLimit.Limit
import ErgodicTheory.Lyapunov.Forward
import ErgodicTheory.Lyapunov.ForwardAngle
import ErgodicTheory.Lyapunov.SpectrumResiduals

/-!
# Chain recursion for the fast-band-mass envelope

Deterministic engine for the uniform-in-`m` fast-band-mass envelope appearing in Ruelle's
proof of the multiplicative ergodic theorem (the proof of Lemma 1.4 in [Ruelle, *Ergodic
theory of differentiable dynamical systems*]): the slow/fast orthogonal decomposition over
an `SVDData`, the one-step band-leakage recursion (`oneStep_recursion`, an application of
`oneStep_sandwich`), and the band↔SVD adapter identifying `bandProjector` with the explicit
fast projection (`toEuclideanLin_bandProjector_eq_fastProj`).

## Main results

* `ErgodicTheory.RuelleCofactor.SVDData.oneStep_recursion`: the deterministic one-step band-leakage
  recursion for the fast-band mass along an SVD chain.
* `ErgodicTheory.toEuclideanLin_bandProjector_eq_fastProj`: the band projector equals the
  explicit fast projection over the SVD chain `ErgodicTheory.chainSVD`.

## Implementation notes

Fix `x` in the a.e.-good set.  Write
`σ_j(t) = (toEuclideanLin (cocycle A T t x)).singularValues j` (antitone in `j`),
`u_a(n) = sortedGramEigenbasis A T n x ⟨a⟩` (a unit right-singular vector of
`cocycle A T n x`), `λ_j = lam0 j`.

We are given a *gap pair* `λ_a < λ_e`, a cut `c₀` with `exp λ_a < c₀ < exp λ_e`, and we
must bound, uniformly in `m ≥ n`,
  `‖P^{>c₀}_m u_a(n)‖ ≤ C·exp(−n(λ_e − λ_a − δ))`,
where `P^{>c₀}_m = bandProjector A T (indicator (Ioi c₀) 1) m x` is the orthogonal
projector onto the span of the time-`m` Gram eigenvectors `u_j(m)` whose exp-scale
eigenvalue `σ_j(m)^{1/m}` exceeds `c₀`.

### The deterministic SVD chain (`ErgodicTheory.RuelleCofactor.SVDData`)

Instantiate `ErgodicTheory.RuelleCofactor.SVDData (EuclideanSpace ℝ (Fin d)) (card (Fin d))` at the
point `x` by:
* `e t := sortedGramEigenbasis A T t x` — the time-`t` Gram eigenbasis (right-singular
  basis);
* `σ t j := σ_j(t)` — the time-`t` singular values;
* `apply t u := toEuclideanLin (cocycle A T t x) u`.
The Parseval field is `norm_sq_cocycle_apply_eq_sum_singularValues` (with
`real_inner_comm` to flip the inner-product order to the `⟪e j, u⟫` convention of
`ErgodicTheory.Lyapunov.RuelleCore`).

For this `S`:
* `S.fastProj m hi u = Σ_{j∈hi} ⟪e m j, u⟫ • e m j` and, when
  `hi = hiBand m := {j : c₀ < σ_j(m)^{1/m}}`,
  `‖S.fastProj m hi u‖ = ‖toEuclideanLin (P^{>c₀}_m) u‖` (the band projector is the
  orthogonal projection onto exactly this span — proved in
  `toEuclideanLin_bandProjector_eq_fastProj`).

### The recursion

`u := u_a(n)` lies in the time-`n` slow span `loBand n := {j : σ_j(n)^{1/n} ≤ c₀}` (it
equals the single basis vector `u_a(n)`, and eventually `σ_a(n)^{1/n} < c₀` so
`a ∈ loBand n`).  For each step `t = n+k → t+1`:
* the slow cap at time `t` for the slow span is `s_t := c₀^t` (every slow eigenvalue
  `σ_j(t) ≤ c₀^t`);
* the fast floor at time `t+1` for the fast band is `tt_{t+1} := c₀^{t+1}`;
* the one-step bound is `‖A⁽ᵗ⁺¹⁾u‖ ≤ b_t ‖A⁽ᵗ⁾u‖` with `b_t := ‖A(Tᵗx)‖`.
`oneStep_sandwich` then gives
  `c₀^{t+1}·‖fastProj(t+1) u‖ ≤ b_t · c₀^t · ‖u‖`  i.e.
  `‖fastProj(t+1) u‖ ≤ (b_t/c₀)·‖u‖`.
This is too lossy on its own (the `b_t` are only tempered, `b_t ≤ exp(tη)`).  Ruelle's
improvement: the *slow part of `u` at time `t`* — not all of `u` — feeds the fast band at
`t+1`, and the slow part's mass is what `fastProj(t) u` already controls.  The correct
one-step recursion (his displayed computation) is, with `a_k := ‖fastProj(n+k) u‖`:
  `a_{k+1} ≤ exp(−γ̄)·a_k + R·exp(−k γ')`,
where `γ̄ = λ_e − λ_a − δ*` is the per-step gap survival and `R·exp(−kγ')` the
freshly-injected slow leakage.  The leakage chain solves this:
  `a_k ≤ exp(−kγ̄)·a_0 + R·k·exp(−(k−1)·min γ̄ γ')`.
With `a_0 = 0` (at `m = n`, `u_a(n)` is orthogonal to the fast band, since eventually
`σ_a(n)^{1/n} < c₀`), `a_k ≤ R·k·exp(−(k−1)·min γ̄ γ')`, and since `a_k` is measured
at absolute time `m = n+k`, this carries the `exp(−n γ)` prefactor.  The polynomial `k` and
the `exp(−kγ̄)` tail give a constant uniform in `k = m − n`.

The `δ*`/stratum-gap and `c₀`-endpoint subtleties are handled where this engine is
consumed.  The deterministic recursion engine itself (`oneStep_sandwich`,
`geometric_recursion`) is proved in `ErgodicTheory.Lyapunov.RuelleCore`; this file builds the
band / SVDData adapter on top of it.

## References

* D. Ruelle, *Ergodic theory of differentiable dynamical systems*,
  Publ. Math. IHÉS **50** (1979), 27–58 (the proof of Lemma 1.4).
-/

open Filter Topology MeasureTheory
open scoped RealInnerProductSpace BigOperators

noncomputable section
namespace ErgodicTheory.RuelleCofactor
namespace SVDData

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {D : ℕ}
variable (S : SVDData E D)

/-- The slow projection onto the complement of `hi`. -/
def slowProj (t : ℕ) (hi : Finset (Fin D)) (u : E) : E :=
  ∑ j ∈ hiᶜ, ⟪S.e t j, u⟫ • S.e t j

/-- `u` reconstructs as fast + slow. -/
lemma fastProj_add_slowProj (t : ℕ) (hi : Finset (Fin D)) (u : E) :
    S.fastProj t hi u + S.slowProj t hi u = u := by
  classical
  rw [fastProj, slowProj]
  rw [Finset.sum_add_sum_compl hi (fun j => ⟪S.e t j, u⟫ • S.e t j)]
  exact (S.e t).sum_repr' u

/-- The slow projection lies in the slow span (the span of `e t j`, `j ∈ hiᶜ`). -/
lemma slowProj_mem_span (t : ℕ) (hi : Finset (Fin D)) (u : E) :
    S.slowProj t hi u
      ∈ Submodule.span ℝ
        (Set.range (fun j : (hiᶜ : Finset (Fin D)) => S.e t (j : Fin D))) := by
  classical
  rw [slowProj]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨j, hj⟩, rfl⟩

/-- The fast projection is contractive: `‖fastProj t hi u‖ ≤ ‖u‖`. -/
lemma norm_fastProj_le (t : ℕ) (hi : Finset (Fin D)) (u : E) :
    ‖S.fastProj t hi u‖ ≤ ‖u‖ := by
  classical
  have h1 : ‖S.fastProj t hi u‖ ^ 2 = ∑ j ∈ hi, ⟪S.e t j, u⟫ ^ 2 :=
    S.normSq_fastProj t hi u
  have h2 : ‖u‖ ^ 2 = ∑ j, ⟪S.e t j, u⟫ ^ 2 := S.normSq_eq t u
  have hle : ∑ j ∈ hi, ⟪S.e t j, u⟫ ^ 2 ≤ ∑ j, ⟪S.e t j, u⟫ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ hi)
    intro j _ _; positivity
  have hsq : ‖S.fastProj t hi u‖ ^ 2 ≤ ‖u‖ ^ 2 := by rw [h1, h2]; exact hle
  nlinarith [norm_nonneg (S.fastProj t hi u), norm_nonneg u, hsq]

/-- `fastProj t hi` is additive. -/
lemma fastProj_add (t : ℕ) (hi : Finset (Fin D)) (u v : E) :
    S.fastProj t hi (u + v) = S.fastProj t hi u + S.fastProj t hi v := by
  classical
  simp only [fastProj, inner_add_right, add_smul]
  rw [Finset.sum_add_distrib]

/-- **One-step recursion (deterministic).**  Fix consecutive times `t, t+1` with fast
bands `hi t`, `hi (t+1)`.  Assume the slow cap `s` at time `t` (every `σ t j ≤ s` for
`j ∈ (hi t)ᶜ`), the fast floor `tt > 0` at time `t+1` (every `σ (t+1) j ≥ tt` for
`j ∈ hi (t+1)`), and the step bound `‖apply (t+1) w‖ ≤ b·‖apply t w‖` for the slow part
`w = slowProj t (hi t) u`.  Then

    ‖fastProj (t+1) (hi (t+1)) u‖
      ≤ ‖fastProj t (hi t) u‖ + (b·s/tt)·‖slowProj t (hi t) u‖. -/
theorem oneStep_recursion (t : ℕ) (hiT hiT1 : Finset (Fin D)) (s tt b : ℝ)
    (hs : 0 ≤ s) (htt : 0 < tt) (hb : 0 ≤ b)
    (hσlo : ∀ j ∈ hiTᶜ, S.σ t j ≤ s) (hσhi : ∀ j ∈ hiT1, tt ≤ S.σ (t + 1) j)
    (u : E)
    (hstep : ‖S.apply (t + 1) (S.slowProj t hiT u)‖
      ≤ b * ‖S.apply t (S.slowProj t hiT u)‖) :
    ‖S.fastProj (t + 1) hiT1 u‖
      ≤ ‖S.fastProj t hiT u‖ + (b * s / tt) * ‖S.slowProj t hiT u‖ := by
  classical
  set w := S.slowProj t hiT u with hw
  set z := S.fastProj t hiT u with hz
  -- u = z + w
  have hdecomp : u = z + w := (S.fastProj_add_slowProj t hiT u).symm
  -- fastProj(t+1) u = fastProj(t+1) z + fastProj(t+1) w
  have hsplit : S.fastProj (t + 1) hiT1 u
      = S.fastProj (t + 1) hiT1 z + S.fastProj (t + 1) hiT1 w := by
    conv_lhs => rw [hdecomp]
    rw [S.fastProj_add]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · -- ‖fastProj(t+1) z‖ ≤ ‖z‖
    exact S.norm_fastProj_le (t + 1) hiT1 z
  · -- ‖fastProj(t+1) w‖ ≤ (b s / tt) ‖w‖ via oneStep_sandwich
    have hsand : tt * ‖S.fastProj (t + 1) hiT1 w‖ ≤ b * s * ‖w‖ :=
      S.oneStep_sandwich t hiTᶜ hiT1 s tt b hs htt.le hb hσlo hσhi w
        (S.slowProj_mem_span t hiT u) hstep
    rw [div_mul_eq_mul_div, le_div_iff₀ htt]
    calc ‖S.fastProj (t + 1) hiT1 w‖ * tt
        = tt * ‖S.fastProj (t + 1) hiT1 w‖ := by ring
      _ ≤ b * s * ‖w‖ := hsand

end SVDData
end ErgodicTheory.RuelleCofactor

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : ℕ} {T : X → X}

/-! ## The band / SVDData adapter

`bandProjector A T χ m x = cfc χ (qpow A T m x)`, and `qpow = cfc (·^{1/2m}) (gram)`, so by
CFC composition `bandProjector A T χ m x = cfc (χ ∘ (·^{1/2m})) (gram A T m x)`.  Hence it
acts on the
sorted Gram eigenbasis `u_j(m) = sortedGramEigenbasis A T m x j` diagonally, with eigenvalue
`χ (σ_j(m)^{1/m})` (the indicator of the exp-scale band). -/

/-- The band projector acts diagonally on the sorted Gram eigenbasis with eigenvalue
`χ (qpow-eigenvalue)`. -/
theorem toEuclideanLin_bandProjector_sortedGramEigenbasis [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (m : ℕ) (x : X) (χ : ℝ → ℝ)
    (j : Fin (Fintype.card (Fin d))) :
    Matrix.toEuclideanLin (bandProjector A T χ m x) (sortedGramEigenbasis A T m x j)
      = χ ((qpow_isSelfAdjoint A T m x).isHermitian.eigenvalues₀ j)
          • sortedGramEigenbasis A T m x j := by
  classical
  -- `sortedGramEigenbasis = (gram).eigenvectorBasis.reindex e.symm`; unfold to gram eigenbasis.
  set hG := (gram_posSemidef A T m x).isHermitian with hGdef
  set e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))).symm with he
  have hbase : sortedGramEigenbasis A T m x j = hG.eigenvectorBasis (e.symm j) := by
    rw [sortedGramEigenbasis, OrthonormalBasis.reindex_apply]
  -- bandProjector = cfc (χ ∘ (·^{1/2m})) (gram)
  set p : ℝ → ℝ := fun t : ℝ => t ^ ((2 * (m : ℝ))⁻¹) with hp
  have hgsa : IsSelfAdjoint (gram A T m x) := gram_isSelfAdjoint A T m x
  have hcontp : ContinuousOn p (_root_.spectrum ℝ (gram A T m x)) :=
    (Real.continuous_rpow_const (by positivity)).continuousOn
  -- χ is continuous on the (finite) image `p '' spectrum(gram) = spectrum(qpow)`.
  have hcontχ : ContinuousOn χ (p '' _root_.spectrum ℝ (gram A T m x)) :=
    ((Matrix.finite_real_spectrum (A := gram A T m x)).image p).continuousOn _
  -- bandProjector = cfc χ (qpow) = cfc χ (cfc p gram) = cfc (χ ∘ p) gram.
  have hbp : bandProjector A T χ m x = cfc (χ ∘ p) (gram A T m x) := by
    rw [bandProjector, qpow, cfc_comp χ p (gram A T m x) hgsa hcontχ hcontp]
  rw [hbp, hbase, toEuclideanLin_cfc_eigenvectorBasis (gram A T m x) hG (χ ∘ p) (e.symm j)]
  -- (χ∘p)(gram_eig (e.symm j)) = χ(p(eigenvalues₀ j)) = χ(qpow_eigenvalues₀ j).
  have heval : (χ ∘ p) (hG.eigenvalues (e.symm j))
      = χ ((qpow_isSelfAdjoint A T m x).isHermitian.eigenvalues₀ j) := by
    simp only [Function.comp_apply]
    congr 1
    -- p(gram_eigenvalues (e.symm j)) = p(gram_eigenvalues₀ j) = qpow_eigenvalues₀ j
    have h1 : hG.eigenvalues (e.symm j) = hG.eigenvalues₀ j := by
      rw [Matrix.IsHermitian.eigenvalues, he]
      congr 1
      change (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))) j) = j
      simp [Equiv.symm_apply_apply]
    rw [hp, h1]
    exact rpow_gram_eigenvalues₀_eq_qpow_eigenvalues₀ A T m x j
  rw [heval]

/-- The SVD chain data at a point `x`: time-`t` Gram eigenbasis, singular values, and the cocycle
action.  The Parseval field is `norm_sq_cocycle_apply_eq_sum_singularValues`. -/
def chainSVD [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    ErgodicTheory.RuelleCofactor.SVDData (EuclideanSpace ℝ (Fin d)) (Fintype.card (Fin d)) where
  e t := sortedGramEigenbasis A T t x
  σ t j := (Matrix.toEuclideanLin (cocycle A T t x)).singularValues j
  σ_nonneg t j := (Matrix.toEuclideanLin (cocycle A T t x)).singularValues_nonneg j
  apply t u := Matrix.toEuclideanLin (cocycle A T t x) u
  normSq_apply t u := by
    rw [norm_sq_cocycle_apply_eq_sum_singularValues]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_comm (sortedGramEigenbasis A T t x j) u]

@[simp] lemma chainSVD_apply [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (t : ℕ) (u : EuclideanSpace ℝ (Fin d)) :
    (chainSVD A T x).apply t u = Matrix.toEuclideanLin (cocycle A T t x) u := rfl

@[simp] lemma chainSVD_e [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (t : ℕ) :
    (chainSVD A T x).e t = sortedGramEigenbasis A T t x := rfl

@[simp] lemma chainSVD_σ [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (t : ℕ) (j : Fin (Fintype.card (Fin d))) :
    (chainSVD A T x).σ t j = (Matrix.toEuclideanLin (cocycle A T t x)).singularValues j := rfl

/-- The "fast band" finset at time `m`: indices whose exp-scale (qpow) eigenvalue exceeds `c₀`. -/
def hiBand [NeZero d] (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (m : ℕ) (x : X)
    (c₀ : ℝ) :
    Finset (Fin (Fintype.card (Fin d))) :=
  Finset.univ.filter (fun j => c₀ < (qpow_isSelfAdjoint A T m x).isHermitian.eigenvalues₀ j)

/-- The band projector applied to `u` equals the explicit fast projection
`S.fastProj m (hiBand …) u` onto the time-`m` Gram eigenvectors above the cut. -/
theorem toEuclideanLin_bandProjector_eq_fastProj [NeZero d]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (m : ℕ) (x : X) (c₀ : ℝ)
    (u : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c₀) 1) m x) u
      = (chainSVD A T x).fastProj m (hiBand A T m x c₀) u := by
  classical
  set χ : ℝ → ℝ := Set.indicator (Set.Ioi c₀) (1 : ℝ → ℝ) with hχ
  set b := sortedGramEigenbasis A T m x with hb
  set ev : Fin (Fintype.card (Fin d)) → ℝ :=
    fun j => (qpow_isSelfAdjoint A T m x).isHermitian.eigenvalues₀ j with hev
  -- Expand `u` in the orthonormal basis `b` and apply the diagonal action.
  have hu : u = ∑ j, (inner ℝ (b j) u : ℝ) • b j := by
    conv_lhs => rw [← b.sum_repr u]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [b.repr_apply_apply]
  -- `bandProjector u = Σ_j χ(ev j) • (⟪b j, u⟫ • b j)`.
  have hLHS : Matrix.toEuclideanLin (bandProjector A T χ m x) u
      = ∑ j, χ (ev j) • ((inner ℝ (b j) u : ℝ) • b j) := by
    conv_lhs => rw [hu]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, toEuclideanLin_bandProjector_sortedGramEigenbasis A m x χ j, smul_comm]
  rw [hLHS, ErgodicTheory.RuelleCofactor.SVDData.fastProj, hiBand]
  simp only [chainSVD_e]
  -- Split univ into fast / slow and discard slow.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => c₀ < ev j)]
  have hslow : ∑ j ∈ Finset.univ.filter (fun j => ¬ c₀ < ev j),
        χ (ev j) • ((inner ℝ (b j) u : ℝ) • b j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter] at hj
    have hχ0 : χ (ev j) = 0 := by rw [hχ, Set.indicator_of_notMem (by exact hj.2)]
    rw [hχ0, zero_smul]
  rw [hslow, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_filter] at hj
  have hχ1 : χ (ev j) = 1 := by
    rw [hχ, Set.indicator_of_mem (show ev j ∈ Set.Ioi c₀ from hj.2) 1, Pi.one_apply]
  rw [hχ1, one_smul, hb]

end ErgodicTheory
