import Oseledets.Lyapunov.RuelleCore
import Oseledets.Lyapunov.OseledetsLimit
import Oseledets.Lyapunov.Forward
import Oseledets.Lyapunov.ForwardAngle
import Oseledets.Lyapunov.ForwardV
import Oseledets.Lyapunov.SpectrumResiduals

/-!
# The n-scaled forward graded overlap bound (Ruelle Lemma 1.4 a.e. wiring)

This module proves `forward_graded_overlap`: a.e., for every `δ > 0` there is `c ≥ 1` such that
eventually in `n`, for all sorted-eigenbasis indices `a` and limit-eigenbasis indices `e`,

    |⟪b' x e, u_a(n)⟫| ≤ c · exp(−n·(max(λ_e − λ_a, 0) − δ)).

where `u_a(n) = sortedGramEigenbasis A T n x a` and `b' x e` is the limit eigenbasis vector at
eigenvalue `exp(λ_e)`.

## Paper proof (Ruelle Lemma 1.4 / Prop 1.3, a.e. layer)

Fix `x` in the a.e. good set (intersection of the committed a.e. facts: `hb'`, `hident`,
`ae_lamSing_eq_lam0`, the two tempering limits, and the `hlam0` convergence for each `i < d`).
Write `σ_a(n) = singularValues a` (genuine SVD values of `A⁽ⁿ⁾`, antitone in `a`),
`u_a(n) = sortedGramEigenbasis A T n x a`, `λ_a = lam0 a`.

**Trivial case.** If `λ_e ≤ λ_a` then `max(λ_e − λ_a, 0) = 0`, so the RHS is
`c · exp(nδ) ≥ 1 ≥ |⟪b'_e, u_a(n)⟫|` by Cauchy–Schwarz (both unit vectors). So with `c = 1` the
bound holds for all `n` (no eventuality needed) in the trivial pairs. The content is the gap pairs.

**Gap pairs.** Suppose `λ_e > λ_a`. Fix `δ > 0`, WLOG `δ < (λ_e − λ_a)/3`. The claim is the
time-`n` slow vector `u_a(n)` has overlap with the LIMIT fast band (eigenvectors at level ≥ λ_e)
decaying like `exp(−n(λ_e − λ_a − δ))`.

Route (Ruelle two-time chain + limit transfer):

1. **Gap cut.** The finitely many values `{exp(λ_j) : j < d}` are finite; choose a cut `c₀` with
   `exp(λ_a) < c₀ < exp(λ_e)` avoiding all `exp(λ_j)` (e.g. strictly between two consecutive
   level values straddling the gap). `hident` then applies at this cut.

2. **Two-time chain (deterministic core).** Instantiate `Ruelle13.SVDData` with
   `σ n j := σ_{a-reindexed}(n)`, `e n := sortedGramEigenbasis` (reindexed `Fin (card (Fin d)) ≃ Fin d`),
   `apply n u := toEuclideanLin (cocycle A T n x) u`. The Parseval field is
   `norm_sq_cocycle_apply_eq_sum_singularValues` (after `real_inner_comm`).
   Then for the time-`n` slow vector `u_a(n)` (it lies in the slow span `{u_j(n) : j ≤ a}` —
   trivially, it is `u_a(n)` itself), run the chain `m = n, n+1, …` and obtain, for the time-`m`
   fast band `hi_m = {j : σ_j(m)^{1/m} > c₀}` = `{j : σ_j(m) > c₀^m}`:

       ‖fastProj(m, hi_m) u_a(n)‖ ≤ C(x,δ) · exp(−n·(λ_e − λ_a − Kδ))   UNIFORMLY in m ≥ n.

   The per-step inputs (all eventual in m, uniform on the finitely many indices):
   - tempered step: `‖A(Tᵐx)‖ ≤ exp(mδ')` (from `tendsto_logNorm_orbit_div_atTop_zero`), giving the
     one-step operator bound `‖A⁽ᵐ⁺¹⁾u‖ ≤ ‖A(Tᵐx)‖·‖A⁽ᵐ⁾u‖`;
   - singular-value envelope: `exp(m(λ_j − δ')) ≤ σ_j(m) ≤ exp(m(λ_j + δ'))` eventually
     (from `hlam0`, intersected over the finitely many j).
   The recursion `chain_leakage_exp` packages the imbalance at gap `γ ≈ λ_e − λ_a − 2δ'`.

   NOTE on the cut value: `bandProjector A T (indicator (Ioi c₀)) m x` is the orthogonal projector
   onto `span{u_j(m) : σ_j(m)^{1/m} > c₀}` = `S.fastProj m hi_m` applied (after frame identity).
   The bandProjector is the cfc-projector; `fastProj` is the explicit sum. They coincide on the
   relevant band.

3. **Limit transfer (m → ∞ at fixed n).** `⟪b'_e, u_a(n)⟫`: by `hb'`, `b'_e` is a `lambdaHat`
   eigenvector at `exp(λ_e) > c₀`, hence FIXED by `Pinf = cfc (indicator (Ioi c₀)) lambdaHat`.
   So `⟪b'_e, u_a(n)⟫ = ⟪Pinf b'_e, u_a(n)⟫ = ⟪b'_e, Pinf u_a(n)⟫` (self-adjointness). Write
   `Pinf = P_m + (Pinf − P_m)`. `‖P_m u_a(n)‖` is the time-`m` fast-band mass ≤ step-2 bound uniformly
   in m; `‖(Pinf − P_m) u_a(n)‖ ≤ ‖Pinf − P_m‖ → 0` by `hident`. Let `m → ∞` at fixed `n`:
   `|⟪b'_e, Pinf u_a(n)⟫| = |⟪b'_e, P_m u_a(n)⟫ + ⟪b'_e, (Pinf−P_m) u_a(n)⟫|`
   `≤ ‖P_m u_a(n)‖ + ‖(Pinf−P_m) u_a(n)‖ → step-2 bound + 0`.
   No rate needed for the vanishing term.

4. **Assemble.** Combine the finitely many a.e. sets and the gap/trivial dichotomy; `c` is the max
   over the finitely many gap pairs of the step-2 constants (`≥ 1`), independent of `n, a, e`. `N` in
   the `∀ᶠ` is the max of the finitely many eventual thresholds.

**Quantifier audit.** `c` depends on `x, δ` (not on `n, a, e`): take max over pairs. `N` depends on
`x, δ`. `m` is the free recursion index sent to `∞` AT FIXED `n` — so the chain bound must be
uniform in `m ≥ n`, which `geometric_recursion_uniform` provides (the `q^k a₀ + R·k·M^{k-1}` envelope
is bounded uniformly in `k = m − n` because `M < 1` and the polynomial `k` is dominated).

## What is proved vs. isolated

FULLY PROVED here (zero `sorry`, axioms `[propext, Classical.choice, Quot.sound]`):
* `toEuclideanLin_cfc_fix_eigenvector` — the cfc fixes an arbitrary eigenvector at an eigenvalue
  where the cutoff is `1` (general spectral fact);
* `tendsto_toEuclideanLin_apply` — continuity of `M ↦ toEuclideanLin M u`;
* `abs_inner_le_of_bandProjector_mass_bound` — the LIMIT-TRANSFER reduction (Ruelle step 3): the
  overlap `|⟪w,u⟫|` is bounded by any eventual fast-band-mass bound, transferred through the
  projector limit (no rate needed for the vanishing term);
* `exists_spectral_cut` — the GAP-CUT selection (Ruelle step 1): a spectrum-avoiding cut strictly
  between two `exp`-levels exists;
* `forward_graded_overlap` — the a.e. wrapper: the trivial pairs (`λ_e ≤ λ_a`) are closed by
  Cauchy–Schwarz; the gap pairs are reduced, via the cut + limit-transfer, to the chain envelope;
  the finitely many pairs are combined by `eventually_all`.

ISOLATED as the single analytic hypothesis `hchain` (Ruelle step 2, the two-time chain): the
uniform-in-`m` fast-band-mass envelope
`‖bandProjector(c₀,m) · u_a(n)‖ ≤ C·exp(−n(λ_e−λ_a−δ))` at an ARBITRARY cut `c₀` between the levels.
This is exactly the wiring of `Ruelle13.oneStep_sandwich` into `Ruelle13.chain_leakage_exp`, which
the deterministic core `RuelleCore.lean` deliberately leaves out (its docstring: "the a.e. wiring
(M5) … is what is not in this deterministic core").  A single deterministic operator-norm step over
`[n,m]` is provably too lossy (it gives `exp((m−n)λ₀ − mλ_e)`, which DIVERGES as `m→∞` for the gap
direction), so the per-step recursion that keeps the vector in the slow cone is genuinely required.
-/

open MeasureTheory Filter Topology Matrix
open scoped RealInnerProductSpace BigOperators

noncomputable section

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} {d : ℕ} {T : X → X}

set_option linter.unusedSectionVars false

/-! ## Deterministic helper lemmas -/

/-- **CFC fixes an arbitrary eigenvector at an eigenvalue where `f = 1`.** If `M` is Hermitian,
`toEuclideanLin M v = lam • v`, and `f lam = 1`, then `toEuclideanLin (cfc f M) v = v`.
Proof: expand `v` in the (orthonormal) eigenvector basis; the component `⟪b_j, v⟫` is nonzero only
for eigenvalues `eigenvalues j = lam` (eigenvectors at distinct eigenvalues are orthogonal because
`M` is self-adjoint), and there `f (eigenvalues j) = f lam = 1`. -/
theorem toEuclideanLin_cfc_fix_eigenvector {d : ℕ} [NeZero d] (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.IsHermitian) (f : ℝ → ℝ) (v : EuclideanSpace ℝ (Fin d)) {lam : ℝ}
    (hev : Matrix.toEuclideanLin M v = lam • v) (hf : f lam = 1) :
    Matrix.toEuclideanLin (cfc f M) v = v := by
  classical
  -- expand v in the eigenbasis: v = ∑ i, ⟪b i, v⟫ • b i
  have hexp : ∑ i, (inner ℝ (hM.eigenvectorBasis i) v : ℝ) • hM.eigenvectorBasis i = v :=
    hM.eigenvectorBasis.sum_repr' v
  -- componentwise: if ⟪b j, v⟫ ≠ 0 then eigenvalues j = lam.
  have hcomp : ∀ j, (inner ℝ (hM.eigenvectorBasis j) v : ℝ) ≠ 0 → hM.eigenvalues j = lam := by
    intro j hj
    have hMbj : Matrix.toEuclideanLin M (hM.eigenvectorBasis j)
        = hM.eigenvalues j • (hM.eigenvectorBasis j) := by
      rw [Matrix.toEuclideanLin_apply, hM.mulVec_eigenvectorBasis j]; rfl
    have hsa : (Matrix.toEuclideanLin M).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
    have e1 : (inner ℝ (hM.eigenvectorBasis j) (Matrix.toEuclideanLin M v) : ℝ)
        = lam * (inner ℝ (hM.eigenvectorBasis j) v : ℝ) := by rw [hev, inner_smul_right]
    have e2 : (inner ℝ (Matrix.toEuclideanLin M (hM.eigenvectorBasis j)) v : ℝ)
        = hM.eigenvalues j * (inner ℝ (hM.eigenvectorBasis j) v : ℝ) := by
      rw [hMbj, inner_smul_left]; simp
    have e3 : (inner ℝ (hM.eigenvectorBasis j) (Matrix.toEuclideanLin M v) : ℝ)
        = (inner ℝ (Matrix.toEuclideanLin M (hM.eigenvectorBasis j)) v : ℝ) :=
      (hsa (hM.eigenvectorBasis j) v).symm
    have heq : lam * (inner ℝ (hM.eigenvectorBasis j) v : ℝ)
        = hM.eigenvalues j * (inner ℝ (hM.eigenvectorBasis j) v : ℝ) := by rw [← e1, e3, e2]
    exact (mul_right_cancel₀ hj heq).symm
  -- now compute cfc f M applied to v
  calc Matrix.toEuclideanLin (cfc f M) v
      = Matrix.toEuclideanLin (cfc f M)
          (∑ i, (inner ℝ (hM.eigenvectorBasis i) v : ℝ) • hM.eigenvectorBasis i) := by rw [hexp]
    _ = ∑ i, (inner ℝ (hM.eigenvectorBasis i) v : ℝ)
          • Matrix.toEuclideanLin (cfc f M) (hM.eigenvectorBasis i) := by
        rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
    _ = ∑ i, (inner ℝ (hM.eigenvectorBasis i) v : ℝ) • hM.eigenvectorBasis i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [toEuclideanLin_cfc_eigenvectorBasis M hM f j]
        by_cases hj : (inner ℝ (hM.eigenvectorBasis j) v : ℝ) = 0
        · rw [hj, zero_smul, zero_smul]
        · rw [hcomp j hj, hf, one_smul]
    _ = v := hexp

/-- **Continuity of matrix→vector application.** If `P_m → Pinf` (in the finite-dim matrix norm) then
`toEuclideanLin (P_m) u → toEuclideanLin Pinf u`. -/
theorem tendsto_toEuclideanLin_apply {d : ℕ} {P : ℕ → Matrix (Fin d) (Fin d) ℝ}
    {Pinf : Matrix (Fin d) (Fin d) ℝ} (hP : Filter.Tendsto P Filter.atTop (𝓝 Pinf))
    (u : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun m => Matrix.toEuclideanLin (P m) u) Filter.atTop
      (𝓝 (Matrix.toEuclideanLin Pinf u)) := by
  -- `M ↦ toEuclideanLin M u` is linear in `M` over a finite-dimensional domain, hence continuous.
  let L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    { toFun := fun M => Matrix.toEuclideanLin M u
      map_add' := by intro M N; simp only [map_add, LinearMap.add_apply]
      map_smul' := by intro c M; simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hcont : Continuous fun M : Matrix (Fin d) (Fin d) ℝ => Matrix.toEuclideanLin M u :=
    L.continuous_of_finiteDimensional
  exact (hcont.tendsto Pinf).comp hP

/-- **Limit-transfer reduction (Ruelle Lemma 1.4, step 3).** Let `w` be a unit vector that is fixed
by the limit band projector `Pinf` (`toEuclideanLin Pinf w = w`), with `Pinf` self-adjoint, and suppose
the time-`m` band projectors `P m` converge to `Pinf`. If the fast-band mass `‖toEuclideanLin (P m) u‖`
is eventually bounded by `B`, then `|⟪w, u⟫| ≤ B`. (No rate is needed for the vanishing of
`Pinf − P m`.) -/
theorem abs_inner_le_of_bandProjector_mass_bound {d : ℕ}
    {P : ℕ → Matrix (Fin d) (Fin d) ℝ} {Pinf : Matrix (Fin d) (Fin d) ℝ}
    (hP : Filter.Tendsto P Filter.atTop (𝓝 Pinf)) (hPinfsa : IsSelfAdjoint Pinf)
    (w u : EuclideanSpace ℝ (Fin d)) (hwnorm : ‖w‖ ≤ 1)
    (hfix : Matrix.toEuclideanLin Pinf w = w) {B : ℝ}
    (hbound : ∀ᶠ m : ℕ in Filter.atTop, ‖Matrix.toEuclideanLin (P m) u‖ ≤ B) :
    |(inner ℝ w u : ℝ)| ≤ B := by
  -- Pinf self-adjoint ⟹ ⟪w, Pinf u⟫ = ⟪Pinf w, u⟫ = ⟪w, u⟫.
  have hPinfsym : (Matrix.toEuclideanLin Pinf).IsSymmetric := by
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    rwa [Matrix.isHermitian_iff_isSelfAdjoint]
  have hkey : (inner ℝ w u : ℝ) = (inner ℝ w (Matrix.toEuclideanLin Pinf u) : ℝ) := by
    rw [← hPinfsym w u, hfix]
  -- ⟪w, toEuclideanLin (P m) u⟫ → ⟪w, toEuclideanLin Pinf u⟫
  have htend : Filter.Tendsto
      (fun m => (inner ℝ w (Matrix.toEuclideanLin (P m) u) : ℝ)) Filter.atTop
      (𝓝 (inner ℝ w (Matrix.toEuclideanLin Pinf u) : ℝ)) :=
    Filter.Tendsto.inner tendsto_const_nhds (tendsto_toEuclideanLin_apply hP u)
  -- |⟪w, P m u⟫| ≤ ‖P m u‖ ≤ B eventually, so the limit ⟪w, Pinf u⟫ has |·| ≤ B.
  have habs : ∀ᶠ m : ℕ in Filter.atTop,
      |(inner ℝ w (Matrix.toEuclideanLin (P m) u) : ℝ)| ≤ B := by
    filter_upwards [hbound] with m hm
    calc |(inner ℝ w (Matrix.toEuclideanLin (P m) u) : ℝ)|
        ≤ ‖w‖ * ‖Matrix.toEuclideanLin (P m) u‖ := abs_real_inner_le_norm w _
      _ ≤ 1 * B := by
          apply mul_le_mul hwnorm hm (norm_nonneg _) (by norm_num)
      _ = B := one_mul B
  have hlim : |(inner ℝ w (Matrix.toEuclideanLin Pinf u) : ℝ)| ≤ B :=
    le_of_tendsto (htend.abs) habs
  rw [hkey]; exact hlim

/-- **Gap-cut selection (Ruelle Lemma 1.4, step 1).** For two levels `lo < hi`, the open interval
`(exp lo, exp hi)` is infinite, so it contains a point `c₀` avoiding the finite spectrum
`{exp (g i) : i}`.  This supplies a spectral cut strictly between the two `exp`-levels at which the
band projector and `hident` may be evaluated. -/
theorem exists_spectral_cut {d : ℕ} (g : Fin d → ℝ) {lo hi : ℝ} (hlohi : lo < hi) :
    ∃ c₀ : ℝ, Real.exp lo < c₀ ∧ c₀ < Real.exp hi ∧ (∀ i : Fin d, Real.exp (g i) ≠ c₀) := by
  have hexp : Real.exp lo < Real.exp hi := Real.exp_lt_exp.mpr hlohi
  have hinf : (Set.Ioo (Real.exp lo) (Real.exp hi)).Infinite := Set.Ioo_infinite hexp
  have hfin : (Set.range (fun i : Fin d => Real.exp (g i))).Finite := Set.finite_range _
  obtain ⟨c₀, hc₀mem⟩ := (hinf.diff hfin).nonempty
  rw [Set.mem_diff, Set.mem_Ioo, Set.mem_range, not_exists] at hc₀mem
  exact ⟨c₀, hc₀mem.1.1, hc₀mem.1.2, hc₀mem.2⟩

end Oseledets

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} {d : ℕ} {T : X → X}

set_option linter.unusedSectionVars false

theorem forward_graded_overlap [MeasureTheory.IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (lam0 : ℕ → ℝ)
    (hlam0 : ∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
      Filter.atTop (𝓝 (lam0 i)))
    (b' : X → OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (hb' : ∀ᵐ x ∂μ, ∀ e : Fin d,
      Matrix.toEuclideanLin (lambdaHat A T x) (b' x e)
        = Real.exp (lamSing A T x (e : ℕ)) • b' x e)
    (hident : ∀ᵐ x ∂μ, ∀ c : ℝ, 0 < c → (∀ i : Fin d, Real.exp (lamSing A T x (i : ℕ)) ≠ c) →
      Filter.Tendsto (fun n : ℕ => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
        Filter.atTop (𝓝 (cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) (lambdaHat A T x))))
    -- ISOLATED OBSTRUCTION (Ruelle Lemma 1.4 step 2: the uniform-in-`m` fast-band-mass chain
    -- envelope) — stated at an ARBITRARY spectral cut `c₀` strictly between the two `exp`-levels.
    -- For a gap pair `λ_a < λ_e` and any such `c₀`, the fast-band mass of the time-`n` slow
    -- eigenvector `u_a(n)`, measured by the time-`m` band projector at cut `c₀`, decays like
    -- `exp(−n(λ_e−λ_a−δ))` UNIFORMLY in `m ≥ n`.  This is the genuine remaining analytic content
    -- (the deterministic core `Ruelle13` supplies the abstract recursion engine `chain_leakage_exp`
    -- but not the wiring of `oneStep_sandwich` into it).  The cut SELECTION (step 1) is discharged
    -- in the proof via `exists_spectral_cut`; only the envelope is assumed here.  See report.
    (hchain : ∀ᵐ x ∂μ, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 ≤ C ∧ ∀ a e : Fin d,
      lam0 (a : ℕ) < lam0 (e : ℕ) →
      ∀ c₀ : ℝ, Real.exp (lam0 (a : ℕ)) < c₀ → c₀ < Real.exp (lam0 (e : ℕ)) →
        ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ, n ≤ m →
          ‖Matrix.toEuclideanLin (bandProjector A T (Set.indicator (Set.Ioi c₀) 1) m x)
              (sortedGramEigenbasis A T n x
                ⟨(a : ℕ), lt_of_lt_of_eq a.isLt (Fintype.card_fin d).symm⟩)‖
            ≤ C * Real.exp (-(n : ℝ) * (lam0 (e : ℕ) - lam0 (a : ℕ) - δ))) :
    ∀ᵐ x ∂μ, ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ a e : Fin d,
        |(inner ℝ (b' x e) (sortedGramEigenbasis A T n x
            ⟨(a : ℕ), lt_of_lt_of_eq a.isLt (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ c * Real.exp (-(n : ℝ) * (max (lam0 (e : ℕ) - lam0 (a : ℕ)) 0 - δ)) := by
  filter_upwards [hb', hident, hchain,
    ae_lamSing_eq_lam0 lam0 hlam0] with x hb'x hidentx hchainx hlameq
  intro δ hδ
  obtain ⟨C, hC1, hCpair⟩ := hchainx δ hδ
  refine ⟨C, hC1, ?_⟩
  -- Prove the bound for each pair `(a, e)` separately, eventually in `n`; then combine over the
  -- finitely many pairs via `eventually_all`.  Trivial pairs (`λ_e ≤ λ_a`) are free by
  -- Cauchy–Schwarz; gap pairs (`λ_a < λ_e`) use the chain + limit-transfer.
  have hpair : ∀ p : Fin d × Fin d, ∀ᶠ n : ℕ in Filter.atTop,
      |(inner ℝ (b' x p.2) (sortedGramEigenbasis A T n x
          ⟨(p.1 : ℕ), lt_of_lt_of_eq p.1.isLt (Fintype.card_fin d).symm⟩) : ℝ)|
        ≤ C * Real.exp (-(n : ℝ) * (max (lam0 (p.2 : ℕ) - lam0 (p.1 : ℕ)) 0 - δ)) := by
    rintro ⟨a, e⟩
    by_cases hgap : lam0 (a : ℕ) < lam0 (e : ℕ)
    · -- GAP pair: pick a spectral cut, then chain + limit transfer.
      obtain ⟨c₀, hc₀lo, hc₀hi, hc₀avoid⟩ :=
        exists_spectral_cut (fun i : Fin d => lam0 (i : ℕ)) hgap
      have hc₀pos : 0 < c₀ := lt_trans (Real.exp_pos _) hc₀lo
      have hc₀spec : ∀ i : Fin d, Real.exp (lamSing A T x (i : ℕ)) ≠ c₀ := by
        intro i; rw [hlameq i]; exact hc₀avoid i
      have hc₀lt : c₀ < Real.exp (lamSing A T x (e : ℕ)) := by rw [hlameq e]; exact hc₀hi
      have hmass := hCpair a e hgap c₀ hc₀lo hc₀hi
      set Pinf := cfc (Set.indicator (Set.Ioi c₀) (1 : ℝ → ℝ)) (lambdaHat A T x) with hPinf
      have hfix : Matrix.toEuclideanLin Pinf (b' x e) = b' x e := by
        apply toEuclideanLin_cfc_fix_eigenvector (lambdaHat A T x)
          (lambdaHat_isSelfAdjoint A T x).isHermitian
          (Set.indicator (Set.Ioi c₀) (1 : ℝ → ℝ)) (b' x e) (hb'x e)
        rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hc₀lt), Pi.one_apply]
      have hPinfsa : IsSelfAdjoint Pinf := cfc_predicate _ _
      have htend := hidentx c₀ hc₀pos hc₀spec
      have hmaxeq : max (lam0 (e : ℕ) - lam0 (a : ℕ)) 0 = lam0 (e : ℕ) - lam0 (a : ℕ) :=
        max_eq_left (by linarith)
      filter_upwards [hmass] with n hmassn
      rw [hmaxeq]
      exact abs_inner_le_of_bandProjector_mass_bound htend hPinfsa (b' x e)
        (sortedGramEigenbasis A T n x ⟨(a : ℕ), lt_of_lt_of_eq a.isLt (Fintype.card_fin d).symm⟩)
        (le_of_eq ((b' x).orthonormal.1 e)) hfix
        (Filter.eventually_atTop.2 ⟨n, hmassn⟩)
    · -- TRIVIAL pair: `λ_e ≤ λ_a`, so `max(λ_e − λ_a, 0) = 0`, RHS `= C·exp(nδ) ≥ 1 ≥ |⟪·,·⟫|`.
      have hmaxeq : max (lam0 (e : ℕ) - lam0 (a : ℕ)) 0 = 0 :=
        max_eq_right (by linarith [not_lt.mp hgap])
      filter_upwards with n
      rw [hmaxeq]
      have hCS : |(inner ℝ (b' x e) (sortedGramEigenbasis A T n x
          ⟨(a : ℕ), lt_of_lt_of_eq a.isLt (Fintype.card_fin d).symm⟩) : ℝ)| ≤ 1 := by
        calc |(inner ℝ (b' x e) (sortedGramEigenbasis A T n x
            ⟨(a : ℕ), lt_of_lt_of_eq a.isLt (Fintype.card_fin d).symm⟩) : ℝ)|
            ≤ ‖b' x e‖ * ‖sortedGramEigenbasis A T n x
                ⟨(a : ℕ), lt_of_lt_of_eq a.isLt (Fintype.card_fin d).symm⟩‖ :=
              abs_real_inner_le_norm _ _
          _ = 1 := by
              rw [(b' x).orthonormal.1 e,
                (sortedGramEigenbasis A T n x).orthonormal.1
                  ⟨(a : ℕ), lt_of_lt_of_eq a.isLt (Fintype.card_fin d).symm⟩, one_mul]
      refine hCS.trans ?_
      have hexp1 : (1 : ℝ) ≤ Real.exp (-(n : ℝ) * (0 - δ)) :=
        Real.one_le_exp (by nlinarith [Nat.cast_nonneg (α := ℝ) n, hδ.le])
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ C * Real.exp (-(n : ℝ) * (0 - δ)) :=
            mul_le_mul hC1 hexp1 (by norm_num) (le_trans (by norm_num) hC1)
  -- combine over the finitely many pairs `(a, e) : Fin d × Fin d`
  have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ p : Fin d × Fin d,
      |(inner ℝ (b' x p.2) (sortedGramEigenbasis A T n x
          ⟨(p.1 : ℕ), lt_of_lt_of_eq p.1.isLt (Fintype.card_fin d).symm⟩) : ℝ)|
        ≤ C * Real.exp (-(n : ℝ) * (max (lam0 (p.2 : ℕ) - lam0 (p.1 : ℕ)) 0 - δ)) :=
    Filter.eventually_all.2 hpair
  filter_upwards [hall] with n hn a e
  exact hn (a, e)

end Oseledets

/-! ## Axiom audit -/

#print axioms Oseledets.toEuclideanLin_cfc_fix_eigenvector
#print axioms Oseledets.tendsto_toEuclideanLin_apply
#print axioms Oseledets.abs_inner_le_of_bandProjector_mass_bound
#print axioms Oseledets.exists_spectral_cut
#print axioms Oseledets.forward_graded_overlap
