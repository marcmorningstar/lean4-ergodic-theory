/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Lyapunov.Extensions.SingularSpectralValues
import ErgodicTheory.Lyapunov.ExteriorNorm.Weyl
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The genuine singular Lyapunov spectrum is `μ`-a.e. constant (det-free)

For a **possibly-singular** matrix cocycle generator `A : X → Matrix (Fin d) (Fin d) ℝ` — no
`det A ≠ 0`, no inverse integrability, only forward integrability `log⁺‖A‖ ∈ L¹` — this module
proves that the **genuine** (`−∞`-aware) per-direction forward singular Lyapunov exponent
`λ_k^gen = ErgodicTheory.singularSpectralValue A T k` is `μ`-**a.e. constant** under an ergodic
measure-preserving `T`:

`∃ c : EReal, ∀ᵐ x ∂μ, singularSpectralValue A T k x = c`.

## The route (integrability-free sub-invariance)

The standard Kingman path to a.e.-constant exponents needs the cocycle bounded below, a proviso the
genuine `−∞`-aware exponent lacks (it can fall to `⊥` on the kernel / volume-collapse stratum). We
sidestep integrability entirely:

1. **Per-direction singular-value submultiplicativity** `σ_k(g ∘ f) ≤ σ_k(g) · ‖f‖`
   (`ErgodicTheory.singularValues_comp_le_opNorm`). This is a Courant–Fischer dimension count
   built on
   `ErgodicTheory.Weyl` (`spanP`, `quad_ge_on_top`, `quad_le_on_bot`, `finrank_spanP`):
   the top-`(k+1)`
   eigenspace of `(g ∘ f)*(g ∘ f)` (dim `k+1`) and the `f`-preimage of the bottom-`(n-k)` eigenspace
   of `g*g` (dim `≥ n-k`) sum to dimension `> n`, hence meet nonzero, pinning the squared singular
   value. It is the genuine Horn inequality that Mathlib lacks.

2. **Sub-invariance** `λ_k^gen(x) ≤ λ_k^gen(T x)` for **every** `x`
   (`ErgodicTheory.singularSpectralValue_le_comp`). From `cocycle (n+1) x = cocycle n (T x) · A x`
   and
   step 1, `σ_k(A⁽ⁿ⁺¹⁾ x) ≤ σ_k(A⁽ⁿ⁾(T x)) · ‖A x‖`. After `(1/n) log` and `limsup`, the fixed
   single-step factor `log ‖A x‖` washes out (`(1/n) · c → 0`), giving the bound. The reverse
   genuinely needs the **smallest** singular value of `A x` (invertibility), so only sub-invariance
   is claimed.

3. **Sub-invariant ⟹ invariant** without integrability
   (`ErgodicTheory.singularSpectralValue_invariant_ae`). Compose with the bounded strictly-monotone
   transform `EReal.exp : EReal → ℝ≥0∞` (an order-iso, so injective). `h := exp ∘ λ_k^gen` is `≤`
   a finite constant `exp λ₁⁺` a.e. (the forward top value, via
   `ErgodicTheory.ae_singularSpectralValue_lt_top`), so `∫⁻ h < ∞`; `h ≤ h ∘ T` a.e. and
   `∫⁻ (h ∘ T) = ∫⁻ h` (measure-preserving) give `h =ᵐ h ∘ T`
   (`MeasureTheory.ae_eq_of_ae_le_of_lintegral_le`); injectivity of `exp` lifts back to
   `λ_k^gen =ᵐ λ_k^gen ∘ T`.

4. **Invariant ⟹ a.e. constant** under ergodicity
   (`ErgodicTheory.ae_singularSpectralValue_eq_const`), via `Ergodic.ae_eq_const_of_ae_eq_comp₀`
   (`EReal` is Polish, hence has a countably-separated Borel structure).

## Main results

* `ErgodicTheory.singularValues_comp_le_opNorm` — the per-direction Horn submultiplicativity
  `σ_k(g ∘ f) ≤ σ_k(g) · ‖f‖`.
* `ErgodicTheory.singularSpectralValue_le_comp` — deterministic sub-invariance
  `λ_k^gen(x) ≤ λ_k^gen(T x)`.
* `ErgodicTheory.singularSpectralValue_invariant_ae` — `λ_k^gen =ᵐ λ_k^gen ∘ T`
  (integrability-free).
* `ErgodicTheory.ae_singularSpectralValue_eq_const` — **the headline**: `λ_k^gen` is `μ`-a.e.
  constant.

## References

* A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1).
* M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*,
  Israel J. Math. **32** (1979), 356–362.
* R. A. Horn, C. R. Johnson, *Topics in Matrix Analysis* (Thm 3.3.16, singular-value
  submultiplicativity).
-/

open MeasureTheory Filter Topology Module
open scoped Matrix.Norms.L2Operator RealInnerProductSpace ENNReal

namespace ErgodicTheory

/-! ## Per-direction singular-value submultiplicativity (Horn inequality)

The genuine Horn inequality `σ_k(g ∘ f) ≤ σ_k(g) · ‖f‖` is built from the Courant–Fischer
dimension-count infrastructure of `ErgodicTheory.Weyl`. Mathlib provides only `σ_k ≤ ‖·‖`
(`LinearMap.singularValues_le_opNorm`) and the product submultiplicativity of `ErgodicTheory.sprod`;
the per-index bound is new. -/

section Horn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Gram quadratic form: `⟪(adjoint T ∘ₗ T) v, v⟫ = ‖T v‖²`. -/
private theorem gram_quad (T : E →ₗ[ℝ] E) (v : E) :
    ⟪(LinearMap.adjoint T ∘ₗ T) v, v⟫ = ‖T v‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- **Per-direction singular-value submultiplicativity (Horn).** For `f g : E →ₗ[ℝ] E` on a
finite-dimensional inner product space and any `i`, the `i`-th singular value of the composition is
bounded by `σ_i(g) · ‖f‖` (`‖f‖` the operator norm `‖toContinuousLinearMap f‖`):
`σ_i(g ∘ₗ f) ≤ σ_i(g) · ‖f‖`.

Proof by the Courant–Fischer dimension count. Write `n = finrank ℝ E`. For `i < n`,
`σ_i(g ∘ₗ f)² = μ_i(S')` and `σ_i(g)² = μ_i(S)` are sorted eigenvalues of the Gram operators
`S' = (g ∘ₗ f)*(g ∘ₗ f)` and `S = g* g`. The top-`(i+1)` eigenspace `V` of `S'` (dim `i+1`) and
`W := f⁻¹(`bottom-`(n-i)` eigenspace of `S`)` (dim `≥ n-i`) have `dim V + dim W ≥ n+1`, so meet at a
nonzero `v`. There `σ_i(g ∘ₗ f)²‖v‖² ≤ ‖g(f v)‖²` (top bound for `S'`) and, since `f v` lies in the
bottom eigenspace of `S`, `‖g(f v)‖² ≤ σ_i(g)²‖f v‖² ≤ σ_i(g)²‖f‖²‖v‖²` (bottom bound for `S` plus
`‖f v‖ ≤ ‖f‖‖v‖`). For `i ≥ n` the left side is `0`. -/
theorem singularValues_comp_le_opNorm (f g : E →ₗ[ℝ] E) (i : ℕ) :
    (g ∘ₗ f).singularValues i ≤ g.singularValues i * ‖LinearMap.toContinuousLinearMap f‖ := by
  classical
  set n := finrank ℝ E with hn
  set nf : ℝ := ‖LinearMap.toContinuousLinearMap f‖ with hnf
  have hnf0 : 0 ≤ nf := norm_nonneg _
  by_cases hi : i < n
  · -- the genuine regime: dimension count
    set S' := LinearMap.adjoint (g ∘ₗ f) ∘ₗ (g ∘ₗ f) with hS'
    set S := LinearMap.adjoint g ∘ₗ g with hS
    have hS'sym : S'.IsSymmetric := (g ∘ₗ f).isSymmetric_adjoint_comp_self
    have hSsym : S.IsSymmetric := g.isSymmetric_adjoint_comp_self
    -- the eigenspaces
    set V := Weyl.spanP hS'sym hn (· ≤ (⟨i, hi⟩ : Fin n)) with hV
    -- `W` = `f`-preimage of the bottom-`(n-i)` eigenspace of `S`
    set W0 := Weyl.spanP hSsym hn ((⟨i, hi⟩ : Fin n) ≤ ·) with hW0
    set ψ : E →ₗ[ℝ] (E ⧸ W0) := W0.mkQ ∘ₗ f with hψ
    set W := LinearMap.ker ψ with hW
    -- dimensions
    have hdimV : finrank ℝ V = i + 1 := by
      rw [hV, Weyl.finrank_spanP]
      rw [show (Finset.univ.filter (· ≤ (⟨i, hi⟩ : Fin n))) = Finset.Iic ⟨i, hi⟩ from
        Finset.filter_ge_eq_Iic]
      exact Fin.card_Iic _
    have hdimW0 : finrank ℝ W0 = n - i := by
      rw [hW0, Weyl.finrank_spanP]
      rw [show (Finset.univ.filter ((⟨i, hi⟩ : Fin n) ≤ ·)) = Finset.Ici ⟨i, hi⟩ from
        Finset.filter_le_eq_Ici]
      exact Fin.card_Ici _
    -- `finrank W ≥ n - i` from rank-nullity for `ψ`
    have hdimW : n - i ≤ finrank ℝ W := by
      have hrk := ψ.finrank_range_add_finrank_ker
      have hrange : finrank ℝ (LinearMap.range ψ) ≤ finrank ℝ (E ⧸ W0) := Submodule.finrank_le _
      have hquot : finrank ℝ (E ⧸ W0) + finrank ℝ W0 = n := by
        rw [W0.finrank_quotient_add_finrank, hn]
      rw [hW]
      omega
    -- the two eigenspaces meet nonzero
    have hsum : finrank ℝ (V ⊔ W : Submodule ℝ E) + finrank ℝ (V ⊓ W : Submodule ℝ E)
        = finrank ℝ V + finrank ℝ W := Submodule.finrank_sup_add_finrank_inf_eq V W
    have hle : finrank ℝ (V ⊔ W : Submodule ℝ E) ≤ n := hn ▸ Submodule.finrank_le _
    have hinf : 0 < finrank ℝ (V ⊓ W : Submodule ℝ E) := by omega
    have hne : (V ⊓ W : Submodule ℝ E) ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hinf; omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hvV : v ∈ V := (Submodule.mem_inf.mp hv).1
    have hvW : v ∈ W := (Submodule.mem_inf.mp hv).2
    have hnormpos : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    -- top bound for `S'`
    have h1 : (hS'sym.eigenvalues hn ⟨i, hi⟩) * ‖v‖ ^ 2 ≤ ⟪S' v, v⟫ :=
      Weyl.quad_ge_on_top hS'sym hn ⟨i, hi⟩ hvV
    -- `f v` lies in the bottom eigenspace of `S`
    have hfvW0 : f v ∈ W0 := by
      have hψv : ψ v = 0 := LinearMap.mem_ker.mp hvW
      rwa [hψ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hψv
    have h2 : ⟪S (f v), f v⟫ ≤ (hSsym.eigenvalues hn ⟨i, hi⟩) * ‖f v‖ ^ 2 :=
      Weyl.quad_le_on_bot hSsym hn ⟨i, hi⟩ hfvW0
    -- turn the quadratic forms into norms
    have hq1 : ⟪S' v, v⟫ = ‖g (f v)‖ ^ 2 := by
      rw [hS', gram_quad, LinearMap.comp_apply]
    have hq2 : ⟪S (f v), f v⟫ = ‖g (f v)‖ ^ 2 := by rw [hS, gram_quad]
    -- `σ_i(g ∘ₗ f)² = μ_i(S')`, `σ_i(g)² = μ_i(S)`
    have hsv1 : (g ∘ₗ f).singularValues i ^ 2 = hS'sym.eigenvalues hn ⟨i, hi⟩ :=
      (g ∘ₗ f).sq_singularValues_of_lt hn hi
    have hsv2 : g.singularValues i ^ 2 = hSsym.eigenvalues hn ⟨i, hi⟩ :=
      g.sq_singularValues_of_lt hn hi
    -- `‖f v‖ ≤ ‖f‖ ‖v‖`
    have hfv : ‖f v‖ ≤ nf * ‖v‖ := by
      have := (LinearMap.toContinuousLinearMap f).le_opNorm v
      rwa [LinearMap.coe_toContinuousLinearMap'] at this
    -- assemble: `σ_i(g∘f)² ‖v‖² ≤ ‖g(fv)‖² ≤ σ_i(g)² ‖fv‖² ≤ σ_i(g)² nf² ‖v‖²`
    have hsvnn1 : 0 ≤ (g ∘ₗ f).singularValues i := (g ∘ₗ f).singularValues_nonneg i
    have hsvnn2 : 0 ≤ g.singularValues i := g.singularValues_nonneg i
    have hfvnn : 0 ≤ ‖f v‖ := norm_nonneg _
    have hchain : (g ∘ₗ f).singularValues i ^ 2 * ‖v‖ ^ 2
        ≤ g.singularValues i ^ 2 * (nf * ‖v‖) ^ 2 := by
      have ha : (g ∘ₗ f).singularValues i ^ 2 * ‖v‖ ^ 2 ≤ ‖g (f v)‖ ^ 2 := by
        rw [hsv1]; rw [← hq1]; exact h1
      have hb : ‖g (f v)‖ ^ 2 ≤ g.singularValues i ^ 2 * ‖f v‖ ^ 2 := by
        rw [hsv2, ← hq2]; exact h2
      have hc : g.singularValues i ^ 2 * ‖f v‖ ^ 2 ≤ g.singularValues i ^ 2 * (nf * ‖v‖) ^ 2 := by
        gcongr
      exact ha.trans (hb.trans hc)
    -- cancel `‖v‖² > 0` and take square roots
    have hsq : (g ∘ₗ f).singularValues i ^ 2 ≤ (g.singularValues i * nf) ^ 2 := by
      have hvne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hnormpos
      have hrw : g.singularValues i ^ 2 * (nf * ‖v‖) ^ 2
          = (g.singularValues i * nf) ^ 2 * ‖v‖ ^ 2 := by ring
      rw [hrw] at hchain
      exact le_of_mul_le_mul_right (by linarith [hchain]) hnormpos
    have hprodnn : 0 ≤ g.singularValues i * nf := mul_nonneg hsvnn2 hnf0
    exact le_of_sq_le_sq hsq hprodnn
  · -- `i ≥ n`: `σ_i(g ∘ₗ f) = 0`
    have hge : finrank ℝ E ≤ i := by omega
    rw [(g ∘ₗ f).singularValues_of_finrank_le hge]
    exact mul_nonneg (g.singularValues_nonneg i) (norm_nonneg _)

end Horn

/-! ## The `(n+1)⁻¹` → `n⁻¹` reindexing of the `EReal`-`limsup`

Sub-invariance compares `cocycle (n+1) x` (at `x`) with `cocycle n (T x)` (at `T x`), so the
defining `limsup` of `λ_k^gen(x)` (normalized by `(n+1)⁻¹` after the `+1` shift) must be compared
with that of `λ_k^gen(T x)` (normalized by `n⁻¹`). The two normalizations are asymptotically
equivalent, but because the genuine exponent is **unbounded below** (it can fall to `⊥`), the
standard "perturbation tends to `0`" lemma (which needs two-sided boundedness, à la
`ErgodicTheory.lambdaBar_equivariant`) does **not** apply. The bound `limsup ((n+1)⁻¹ Bₙ) ≤ limsup
(n⁻¹ Bₙ)` is still true and proved here directly via `Filter.limsup_le_iff`, using only that the
target `limsup` is `< ⊤`: for any threshold `y` above it, `n⁻¹ Bₙ < y'` eventually for some
`y' < y`, and then `(n+1)⁻¹ Bₙ = (n⁻¹ Bₙ) · (n/(n+1))` is `≤ y'` (if `n⁻¹ Bₙ ≥ 0`) or `≤ y' ·
n/(n+1) → y' < y` (if `n⁻¹ Bₙ < 0`); either way `< y` eventually. -/

/-- **Reindexing the `EReal`-`limsup` from `(n+1)⁻¹` to `n⁻¹`.** For `B : ℕ → EReal` and a finite
real additive perturbation `cr : ℝ`,

`limsup_n ((n+1)⁻¹ · (Bₙ + cr)) ≤ limsup_n (n⁻¹ · Bₙ)`.

The `(n+1)⁻¹` normalization (after the `+1` shift of the defining sequence) is dominated by the
`n⁻¹` one even though `Bₙ` may be unbounded below; the perturbation washes out (`(n+1)⁻¹ · cr → 0`).
The bound is proved via `Filter.limsup_le_iff`: for `y` above the target `limsup`, pick a finite
real `z` with the target `< z < y`; then `n⁻¹ Bₙ < z` eventually, so `Bₙ ≤ n · z`, and
`(n+1)⁻¹ (Bₙ + cr) ≤ (n·z + cr)/(n+1) → z < y`. -/
theorem limsup_inv_succ_mul_add_le (B : ℕ → EReal) (cr : ℝ) :
    Filter.limsup (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : EReal) * (B n + (cr : EReal))) atTop
      ≤ Filter.limsup (fun n : ℕ => ((n : ℝ)⁻¹ : EReal) * B n) atTop := by
  set lam : EReal := Filter.limsup (fun n : ℕ => ((n : ℝ)⁻¹ : EReal) * B n) atTop with hlam
  rw [Filter.limsup_le_iff]
  intro y hy
  -- a finite real `z` with `lam < z < y`; `z` is neither `⊥` nor `⊤`, so `z = (zr : EReal)`
  obtain ⟨z, hlamz, hzy⟩ := exists_between hy
  have hzne_top : z ≠ ⊤ := ne_top_of_lt hzy
  have hzne_bot : z ≠ ⊥ := ne_bot_of_gt hlamz
  obtain ⟨zr, hzr⟩ : ∃ zr : ℝ, z = (zr : EReal) :=
    ⟨z.toReal, (EReal.coe_toReal hzne_top hzne_bot).symm⟩
  have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ)⁻¹ : EReal) * B n < z :=
    Filter.eventually_lt_of_limsup_lt (hlam ▸ hlamz)
  -- the eventual upper bound `(n·z + cr)/(n+1) < y` (it tends to `z < y`)
  have htend : Filter.Tendsto
      (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : EReal) * ((n : ℝ) * z + (cr : EReal))) atTop (𝓝 z) := by
    subst hzr
    have hreal : Filter.Tendsto
        (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * zr + cr)) atTop (𝓝 zr) := by
      have heq : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * zr + cr)
          = zr + (cr - zr) * ((n : ℝ) + 1)⁻¹ := by
        intro n
        have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      refine (Filter.Tendsto.congr (fun n => (heq n).symm) ?_)
      have htz : Filter.Tendsto (fun n : ℕ => (cr - zr) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        have hden : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        simpa using hden.inv_tendsto_atTop.const_mul (cr - zr)
      simpa using (tendsto_const_nhds (x := zr)).add htz
    have hcoe : ∀ n : ℕ, (((n : ℝ) + 1)⁻¹ : EReal) * ((n : ℝ) * (zr : EReal) + (cr : EReal))
        = ((((n : ℝ) + 1)⁻¹ * ((n : ℝ) * zr + cr) : ℝ) : EReal) := by
      intro n
      rw [EReal.coe_mul, EReal.coe_add, EReal.coe_mul, EReal.coe_inv, EReal.coe_add, EReal.coe_one,
        EReal.coe_natCast]
    refine (Filter.Tendsto.congr (fun n => (hcoe n).symm) ?_)
    exact (continuous_coe_real_ereal.tendsto zr).comp hreal
  have hyev : ∀ᶠ n : ℕ in atTop,
      (((n : ℝ) + 1)⁻¹ : EReal) * ((n : ℝ) * z + (cr : EReal)) < y :=
    htend.eventually (eventually_lt_nhds hzy)
  filter_upwards [hev, hyev, Filter.eventually_ge_atTop 1] with n hn hyn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hncoe_pos : (0 : EReal) < ((n : ℝ) : EReal) := EReal.coe_pos.2 hnpos
  have hncoe_top : ((n : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  -- `B n ≤ z · n` from `n⁻¹ · B n < z`
  have hBle : B n ≤ z * ((n : ℝ) : EReal) := by
    have hkey : ((n : ℝ)⁻¹ : EReal) * B n < z := hn
    rw [show ((n : ℝ)⁻¹ : EReal) = ((n : ℝ) : EReal)⁻¹ from (EReal.coe_inv _).symm,
      ← EReal.div_eq_inv_mul] at hkey
    exact le_of_lt ((EReal.div_lt_iff hncoe_pos hncoe_top).1 hkey)
  have hadd : B n + (cr : EReal) ≤ ((n : ℝ) : EReal) * z + (cr : EReal) := by
    rw [mul_comm]; gcongr
  have hmono : (((n : ℝ) + 1)⁻¹ : EReal) * (B n + (cr : EReal))
      ≤ (((n : ℝ) + 1)⁻¹ : EReal) * (((n : ℝ) : EReal) * z + (cr : EReal)) :=
    mul_le_mul_of_nonneg_left hadd (EReal.coe_pos.2 (by positivity)).le
  exact lt_of_le_of_lt hmono hyn

/-! ## Deterministic sub-invariance of `λ_k^gen` -/

section SubInvariance

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

open scoped Matrix.Norms.L2Operator

/-- `toEuclideanLin` of a matrix product is the composition of the linear maps. -/
private theorem toEuclideanLin_mul (M N : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.toEuclideanLin (M * N)
      = (Matrix.toEuclideanLin M) ∘ₗ (Matrix.toEuclideanLin N) := by
  ext v i
  simp only [Matrix.toLpLin_apply, LinearMap.comp_apply, Matrix.mulVec_mulVec]

omit [MeasurableSpace X] in
/-- **The single-step Horn bound for the cocycle.** From `cocycle (n+1) x = cocycle n (T x) · A x`
and the per-direction submultiplicativity `ErgodicTheory.singularValues_comp_le_opNorm`,

`σ_k(A⁽ⁿ⁺¹⁾ x) ≤ σ_k(A⁽ⁿ⁾(T x)) · ‖A x‖`. -/
theorem singularValue_cocycle_succ_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k n : ℕ) (x : X) :
    (Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k
      ≤ (Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues k * ‖A x‖ := by
  rw [cocycle_succ, toEuclideanLin_mul]
  have hnorm : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A x))‖ = ‖A x‖ := rfl
  rw [← hnorm]
  exact singularValues_comp_le_opNorm (Matrix.toEuclideanLin (A x))
    (Matrix.toEuclideanLin (cocycle A T n (T x))) k

omit [MeasurableSpace X] in
/-- **The single-step Horn bound in `−∞`-aware log form.** Applying `ENNReal.log ∘ ofReal` to
`ErgodicTheory.singularValue_cocycle_succ_le` (with `log` monotone and `ENNReal.log_mul_add`),

`log σ_k(A⁽ⁿ⁺¹⁾ x) ≤ log σ_k(A⁽ⁿ⁾(T x)) + log ‖A x‖` (in `EReal`, `log = ENNReal.log`). -/
theorem logSingularValue_cocycle_succ_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k n : ℕ) (x : X) :
    ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k))
      ≤ ENNReal.log (ENNReal.ofReal
          ((Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues k))
        + ENNReal.log (ENNReal.ofReal ‖A x‖) := by
  have hle := singularValue_cocycle_succ_le A T k n x
  have hnn : (0 : ℝ) ≤ (Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues k :=
    (Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues_nonneg k
  calc ENNReal.log (ENNReal.ofReal
        ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k))
      ≤ ENNReal.log (ENNReal.ofReal
          ((Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues k * ‖A x‖)) :=
        ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hle)
    _ = ENNReal.log (ENNReal.ofReal
          ((Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues k)
          * ENNReal.ofReal ‖A x‖) := by rw [ENNReal.ofReal_mul hnn]
    _ = ENNReal.log (ENNReal.ofReal
          ((Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues k))
        + ENNReal.log (ENNReal.ofReal ‖A x‖) := ENNReal.log_mul_add

omit [MeasurableSpace X] in
/-- **Deterministic sub-invariance of the genuine per-direction exponent.** For **every** `x` (no
invertibility, no integrability, no ergodicity), `λ_k^gen(x) ≤ λ_k^gen(T x)`. From the single-step
Horn log bound `log σ_k(A⁽ⁿ⁺¹⁾ x) ≤ log σ_k(A⁽ⁿ⁾(T x)) + log ‖A x‖`
(`ErgodicTheory.logSingularValue_cocycle_succ_le`), the defining `limsup` of `λ_k^gen(x)`
shifts by `+1`
(`Filter.limsup_nat_add`) and is dominated by the `n⁻¹`-normalized `limsup` at `T x` plus the fixed
single-step term `log ‖A x‖` that washes out, via the reindexing
`ErgodicTheory.limsup_inv_succ_mul_add_le`. The reverse inequality genuinely needs the **smallest**
singular value of `A x` (invertibility), so only the sub-invariant direction is established. -/
theorem singularSpectralValue_le_comp (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k : ℕ) (x : X) :
    singularSpectralValue A T k x ≤ singularSpectralValue A T k (T x) := by
  set B : ℕ → EReal := fun n => ENNReal.log (ENNReal.ofReal
    ((Matrix.toEuclideanLin (cocycle A T n (T x))).singularValues k)) with hB
  set cr : ℝ := (ENNReal.log (ENNReal.ofReal ‖A x‖)).toReal with hcr
  -- the defining `limsup` of `λ_k^gen(x)`, shifted by `+1`
  have hshift : singularSpectralValue A T k x
      = Filter.limsup (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : EReal) *
          ENNReal.log (ENNReal.ofReal
            ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k))) atTop := by
    rw [singularSpectralValue, ← Filter.limsup_nat_add _ 1]
    congr 1
    funext n
    norm_num
  -- bound the shifted terms by `(n+1)⁻¹ · (B n + cr')` where `cr' = log ‖A x‖`
  rw [hshift]
  by_cases hAx : ‖A x‖ = 0
  · -- `A x = 0`: `σ_k(A⁽ⁿ⁺¹⁾ x) = 0` (`log = ⊥`), so the shifted `limsup` is `⊥`
    have hbot : ∀ n : ℕ, (((n : ℝ) + 1)⁻¹ : EReal) *
        ENNReal.log (ENNReal.ofReal
          ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k)) = ⊥ := by
      intro n
      have hσ0 : (Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k = 0 := by
        have hle := singularValue_cocycle_succ_le A T k n x
        rw [hAx, mul_zero] at hle
        exact le_antisymm hle
          ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues_nonneg k)
      rw [hσ0]
      simp only [ENNReal.ofReal_zero, ENNReal.log_zero]
      exact EReal.mul_bot_of_pos (EReal.coe_pos.2 (by positivity))
    simp only [hbot]
    rw [Filter.limsup_const]
    exact bot_le
  · -- `A x ≠ 0`: `cr = log ‖A x‖` (finite); use the per-term bound and the reindexing helper
    have hAxpos : (0 : ℝ) < ‖A x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hAx)
    have hcreq : ENNReal.log (ENNReal.ofReal ‖A x‖) = (cr : EReal) := by
      rw [hcr, ENNReal.log_ofReal_of_pos hAxpos]
      simp
    have hterm : ∀ n : ℕ, (((n : ℝ) + 1)⁻¹ : EReal) *
        ENNReal.log (ENNReal.ofReal
          ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k))
        ≤ (((n : ℝ) + 1)⁻¹ : EReal) * (B n + (cr : EReal)) := by
      intro n
      refine mul_le_mul_of_nonneg_left ?_ (EReal.coe_pos.2 (by positivity)).le
      rw [hB, ← hcreq]
      exact logSingularValue_cocycle_succ_le A T k n x
    calc Filter.limsup (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : EReal) *
          ENNReal.log (ENNReal.ofReal
            ((Matrix.toEuclideanLin (cocycle A T (n + 1) x)).singularValues k))) atTop
        ≤ Filter.limsup (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : EReal) * (B n + (cr : EReal))) atTop :=
          Filter.limsup_le_limsup (Filter.Eventually.of_forall hterm)
      _ ≤ Filter.limsup (fun n : ℕ => ((n : ℝ)⁻¹ : EReal) * B n) atTop :=
          limsup_inv_succ_mul_add_le B cr
      _ = singularSpectralValue A T k (T x) := rfl

end SubInvariance

/-! ## Sub-invariant ⟹ invariant ⟹ a.e. constant -/

section Constant

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ} {μ : Measure X}

open scoped Matrix.Norms.L2Operator

/-- **An a.e. finite upper bound on `λ_k^gen`.** For an ergodic measure-preserving `T` and a
possibly-singular generator with `log⁺‖A‖ ∈ L¹`, there is a finite real constant `lam` (the forward
top value `λ₁⁺`) with `λ_k^gen(x) ≤ lam` for `μ`-a.e. `x`. Each defining term is
`≤ (1/n) log⁺‖A⁽ⁿ⁾‖` (`ErgodicTheory.singularSpectralValue_term_le_posLogNorm`), whose `limsup`
is the
a.e. limit `lam` of `tendsto_top_posLogNorm`. -/
theorem ae_singularSpectralValue_le [IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (k : ℕ) :
    ∃ lam : ℝ, ∀ᵐ x ∂μ, singularSpectralValue A T k x ≤ (lam : EReal) := by
  obtain ⟨lam, hlam⟩ := tendsto_top_posLogNorm hT hAmeas hint
  refine ⟨lam, ?_⟩
  filter_upwards [hlam] with x hx
  have hxE : Tendsto
      (fun n : ℕ => (((n : ℝ)⁻¹ * Real.posLog ‖cocycle A T n x‖ : ℝ) : EReal)) atTop
      (𝓝 (lam : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hx
  rw [← hxE.limsup_eq]
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
  exact singularSpectralValue_term_le_posLogNorm A T k n x

/-- **Integrability-free invariance of `λ_k^gen`.** For an ergodic measure-preserving `T` and a
possibly-singular generator with `log⁺‖A‖ ∈ L¹`, the genuine per-direction exponent is `μ`-a.e.
`T`-invariant: `λ_k^gen =ᵐ λ_k^gen ∘ T`. From the deterministic sub-invariance
`λ_k^gen ≤ λ_k^gen ∘ T` (`ErgodicTheory.singularSpectralValue_le_comp`), the bounded
strictly-monotone
transform `EReal.exp : EReal → ℝ≥0∞` gives `h := exp ∘ λ_k^gen` with `h ≤ h ∘ T` and `∫⁻ h < ∞`
(since `λ_k^gen ≤ λ₁⁺` a.e., `ErgodicTheory.ae_singularSpectralValue_le`, and `μ` is a probability
measure). As `T` is measure-preserving `∫⁻ (h ∘ T) = ∫⁻ h`, so `h =ᵐ h ∘ T`
(`MeasureTheory.ae_eq_of_ae_le_of_lintegral_le`); injectivity of `exp` lifts back. -/
theorem singularSpectralValue_invariant_ae [IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (k : ℕ) :
    singularSpectralValue A T k ∘ T =ᵐ[μ] singularSpectralValue A T k := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  have hTmeas : Measurable T := hmp.measurable
  set g : X → EReal := singularSpectralValue A T k with hg
  set h : X → ℝ≥0∞ := fun x => EReal.exp (g x) with hh
  have hgmeas : Measurable g := measurable_singularSpectralValue hAmeas hTmeas k
  have hhmeas : Measurable h := EReal.measurable_exp.comp hgmeas
  -- `h ≤ h ∘ T` (deterministic, from sub-invariance)
  have hle : h ≤ h ∘ T := fun x =>
    EReal.exp_monotone (singularSpectralValue_le_comp A T k x)
  -- `∫⁻ h < ∞` from the a.e. upper bound `g ≤ lam`
  obtain ⟨lam, hlam⟩ := ae_singularSpectralValue_le hT hAmeas hint k
  have hbound : ∀ᵐ x ∂μ, h x ≤ ENNReal.ofReal (Real.exp lam) := by
    filter_upwards [hlam] with x hx
    have : EReal.exp (g x) ≤ EReal.exp (lam : EReal) := EReal.exp_monotone hx
    rwa [EReal.exp_coe] at this
  have hint_fin : ∫⁻ x, h x ∂μ ≠ ∞ := by
    have hle_int : ∫⁻ x, h x ∂μ ≤ ∫⁻ _, ENNReal.ofReal (Real.exp lam) ∂μ :=
      lintegral_mono_ae hbound
    rw [lintegral_const] at hle_int
    refine ne_top_of_le_ne_top ?_ hle_int
    simp [measure_univ]
  -- `∫⁻ (h ∘ T) = ∫⁻ h` (measure-preserving)
  have hcomp : ∫⁻ x, (h ∘ T) x ∂μ = ∫⁻ x, h x ∂μ := by
    rw [Function.comp_def, ← lintegral_map hhmeas hTmeas, hmp.map_eq]
  -- `h =ᵐ h ∘ T`
  have hhT_meas : Measurable (h ∘ T) := hhmeas.comp hTmeas
  have heq : h =ᵐ[μ] h ∘ T :=
    ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hle) hint_fin
      hhT_meas.aemeasurable hcomp.le
  -- lift through injective `exp`
  filter_upwards [heq] with x hx
  have : EReal.exp (g (T x)) = EReal.exp (g x) := hx.symm
  exact EReal.exp_strictMono.injective this

/-- **The genuine singular Lyapunov spectrum is `μ`-a.e. constant (det-free).** For an ergodic
measure-preserving `T` and a **possibly-singular** measurable generator with `log⁺‖A‖ ∈ L¹` (and
*no* `det A ≠ 0`, *no* inverse integrability), the genuine `−∞`-aware per-direction singular
exponent `λ_k^gen = ErgodicTheory.singularSpectralValue A T k` is `μ`-a.e. equal to a single
constant
`c : EReal`:

`∃ c : EReal, ∀ᵐ x ∂μ, singularSpectralValue A T k x = c`.

From the integrability-free a.e. `T`-invariance `ErgodicTheory.singularSpectralValue_invariant_ae`,
the
exponent is a.e. constant by ergodicity (`Ergodic.ae_eq_const_of_ae_eq_comp₀`; `EReal` is Polish,
hence has a countably-separated Borel structure). The value `c` can be `⊥` on the kernel /
volume-collapse stratum — that is the whole point of the genuine `−∞`-aware exponent. -/
theorem ae_singularSpectralValue_eq_const [IsProbabilityMeasure μ] [NeZero d]
    (hT : Ergodic T μ) {A : X → Matrix (Fin d) (Fin d) ℝ} (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (k : ℕ) :
    ∃ c : EReal, ∀ᵐ x ∂μ, singularSpectralValue A T k x = c := by
  have hTmeas : Measurable T := hT.toMeasurePreserving.measurable
  have hgmeas : Measurable (singularSpectralValue A T k) :=
    measurable_singularSpectralValue hAmeas hTmeas k
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp₀ hgmeas.nullMeasurable
    (singularSpectralValue_invariant_ae hT hAmeas hint k)
  exact ⟨c, hc⟩

end Constant

end ErgodicTheory
