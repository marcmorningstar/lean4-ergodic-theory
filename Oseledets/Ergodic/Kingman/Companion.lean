/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Ergodic.Kingman.Derriennic

/-!
# Reduction to the non-positive companion cocycle

Karlsson's §3.3 reduction running the argument on the *non-positive* companion cocycle: the
`T^[M]`-subsequence cocycle algebra and the `EReal`-envelope `T`-invariance in the non-positive
case.

Internal infrastructure for Kingman's theorem (the `Oseledets.Kingman` namespace); the public
statement is in `Oseledets.Ergodic.Kingman.Core`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Oseledets.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-! ### Reduction to the non-positive companion cocycle

Karlsson's §3.3 argument is run on the *non-positive* companion
`vcoc g n := g n − birkhoffSum T (g 1) n`. Since `birkhoffSum (g 1)` is an additive cocycle,
`vcoc g` is again subadditive, and `le_birkhoffSum_one` gives `vcoc g (n+1) ≤ 0`.
The normalized gap is unchanged: `cdiv g − cdiv (vcoc g) = birkhoffAverage (g 1) (·+1)`, which
converges a.e. (Birkhoff) to the *finite* `μ[g 1 | invariants T]`, so `liminf = limsup` for
`ecdiv g`
follows from the same statement for `ecdiv (vcoc g)`. -/

/-- The **non-positive companion cocycle** `vcoc g n x := g n x − birkhoffSum T (g 1) n x`. -/
noncomputable def vcoc (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ :=
  g n x - birkhoffSum T (g 1) n x

omit [MeasurableSpace X] in
/-- `vcoc g` is a subadditive cocycle: subtracting the *additive* cocycle `birkhoffSum (g 1)`
from the subadditive `g` preserves subadditivity. -/
theorem vcoc_subadditive {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) :
    IsSubadditiveCocycle T (vcoc (T := T) g) := by
  refine ⟨fun m n x => ?_⟩
  simp only [vcoc]
  have hadd : birkhoffSum T (g 1) (m + n) x
      = birkhoffSum T (g 1) m x + birkhoffSum T (g 1) n (T^[m] x) := birkhoffSum_add T (g 1) m n x
  have hg := hsub.apply_add_le m n x
  rw [hadd]
  linarith

omit [MeasurableSpace X] in
/-- `vcoc g (n+1) x ≤ 0`: exactly `le_birkhoffSum_one`. -/
theorem vcoc_nonpos {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    vcoc (T := T) g (n + 1) x ≤ 0 := by
  simp only [vcoc, sub_nonpos]
  exact IsSubadditiveCocycle.le_birkhoffSum_one hsub n x

/-- Each level of `vcoc g` is integrable (a difference of integrable `g n` and `birkhoffSum`). -/
theorem vcoc_integrable (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (vcoc (T := T) g n) μ := by
  have heq : vcoc (T := T) g n = fun x => g n x - birkhoffSum T (g 1) n x := rfl
  rw [heq]
  exact (hint n).sub (integrable_birkhoffSum hT (hint 1) n)

/-- The integral of `vcoc g (n+1)` is `(∫ g (n+1)) − (n+1)·(∫ g 1)`: the additive cocycle
`birkhoffSum (g 1)` integrates to `(n+1)·∫ g 1` by measure preservation. -/
theorem integral_vcoc (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    ∫ x, vcoc (T := T) g (n + 1) x ∂μ
      = (∫ x, g (n + 1) x ∂μ) - ((n : ℝ) + 1) * ∫ x, g 1 x ∂μ := by
  simp only [vcoc]
  rw [integral_sub (hint (n + 1)) (integrable_birkhoffSum hT (hint 1) (n + 1))]
  congr 1
  -- `∫ birkhoffSum T (g 1) (n+1) = (n+1) * ∫ g 1`.
  simp only [birkhoffSum]
  rw [integral_finsetSum (f := fun k x => g 1 (T^[k] x)) _
    (fun j _ => (hT.iterate j).integrable_comp_of_integrable (hint 1))]
  have : ∀ j ∈ Finset.range (n + 1), ∫ x, g 1 (T^[j] x) ∂μ = ∫ x, g 1 x ∂μ :=
    fun j _ => integral_comp_iterate hT hint j 1
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- The normalized integrals of `vcoc g` are bounded below: `(∫ vcoc(n+1))/(n+1)
= (∫ g(n+1))/(n+1) − ∫ g 1`, a shift of the bounded-below sequence `hbdd`. -/
theorem vcoc_bddBelow (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    BddBelow (Set.range fun n : ℕ => (∫ x, vcoc (T := T) g (n + 1) x ∂μ) / (n + 1)) := by
  obtain ⟨c, hc⟩ := hbdd
  refine ⟨c - ∫ x, g 1 x ∂μ, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp only
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcn : c ≤ (∫ x, g (n + 1) x ∂μ) / (n + 1) := hc ⟨n, rfl⟩
  have hval : (∫ x, vcoc (T := T) g (n + 1) x ∂μ) / ((n : ℝ) + 1)
      = (∫ x, g (n + 1) x ∂μ) / ((n : ℝ) + 1) - ∫ x, g 1 x ∂μ := by
    rw [integral_vcoc hT hint n, sub_div]
    congr 1
    rw [mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]
  rw [hval]
  linarith

omit [MeasurableSpace X] in
/-- **Gap-transfer identity.** Pointwise in `EReal`, the normalized `g`-cocycle is the
normalized companion plus the Birkhoff average of `g 1`:
`ecdiv g n x = ecdiv (vcoc g) n x + ↑(birkhoffAverage ℝ T (g 1) (n+1) x)`. -/
theorem ecdiv_eq_ecdiv_vcoc_add {g : ℕ → X → ℝ} (n : ℕ) (x : X) :
    ecdiv g n x
      = ecdiv (vcoc (T := T) g) n x + ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal) := by
  simp only [ecdiv, ← EReal.coe_add]
  congr 1
  simp only [cdiv, vcoc, birkhoffAverage, smul_eq_mul, sub_div]
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, div_eq_inv_mul]
  ring

omit [MeasurableSpace X] in
/-- **Block subadditivity.** For a subadditive cocycle and any consecutive block
decomposition of `[0, n)` into `k+1` blocks of lengths `ℓ 0, …, ℓ k` (with
`n = ∑_{i ≤ k} ℓ i`), the cocycle is dominated by the sum of the block cocycle values along
the orbit, evaluated at the partial-sum frontiers `T^[∑_{j < i} ℓ j] x`. (Used by
the `Tᴹ`-subsequence cocycle algebra below; stated for `k+1` blocks since the empty
decomposition would force the false `g 0 x ≤ 0`.) -/
theorem IsSubadditiveCocycle.le_sum_blocks {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (ℓ : ℕ → ℕ) (k : ℕ) (x : X) :
    g (∑ i ∈ Finset.range (k + 1), ℓ i) x
      ≤ ∑ i ∈ Finset.range (k + 1), g (ℓ i) (T^[∑ j ∈ Finset.range i, ℓ j] x) := by
  induction k with
  | zero =>
      rw [Finset.range_one, Finset.sum_singleton, Finset.sum_singleton, Finset.range_zero,
        Finset.sum_empty, Function.iterate_zero, id_eq]
  | succ k ih =>
      rw [Finset.sum_range_succ (n := k + 1), Finset.sum_range_succ (n := k + 1)]
      set s : ℕ := ∑ j ∈ Finset.range (k + 1), ℓ j with hs
      calc g (s + ℓ (k + 1)) x
          ≤ g s x + g (ℓ (k + 1)) (T^[s] x) := hsub.apply_add_le s (ℓ (k + 1)) x
        _ ≤ (∑ i ∈ Finset.range (k + 1), g (ℓ i) (T^[∑ j ∈ Finset.range i, ℓ j] x))
              + g (ℓ (k + 1)) (T^[s] x) := by linarith [ih]

/-! ### The `Tᴹ`-subsequence cocycle algebra

For a non-positive subadditive cocycle `g` over `T` and a block length `M`, the
`Tᴹ`-subsequence cocycle `vM g M n x := g (n*M) x − ∑_{i<n} g M (T^[i*M] x)` is a non-positive
subadditive cocycle for `T^[M]`. This is a pure-algebra layer; no measure theory is used. -/

/-- The **`Tᴹ`-subsequence cocycle** `vM g M n x := g (n*M) x − ∑_{i<n} g M (T^[i*M] x)`. -/
noncomputable def vM (g : ℕ → X → ℝ) (M n : ℕ) (x : X) : ℝ :=
  g (n * M) x - ∑ i ∈ Finset.range n, g M (T^[i * M] x)

omit [MeasurableSpace X] in
/-- `vM g M` is a subadditive cocycle for `T^[M]`. Block subadditivity of `g` over the split
`(n+p)·M = n·M + p·M` gives the `g`-term bound; the sum splits as `range (n+p) = range n ∪ tail`,
and reindexing the tail `i = n+j` lines up `T^[i*M] = (T^[M])^[n] (T^[j*M])`. -/
theorem vM_subadditive {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (M : ℕ) :
    IsSubadditiveCocycle (T^[M]) (vM (T := T) g M) := by
  refine ⟨fun n p x => ?_⟩
  simp only [vM]
  -- frontier identity `T^[n*M] x = (T^[M])^[n] x`.
  have hfront : T^[n * M] x = (T^[M])^[n] x := by
    rw [← Function.iterate_mul]; congr 1; ring
  -- `g`-term: `g ((n+p)*M) x ≤ g (n*M) x + g (p*M) ((T^[M])^[n] x)`.
  have hgsplit : g ((n + p) * M) x ≤ g (n * M) x + g (p * M) ((T^[M])^[n] x) := by
    have := hsub.apply_add_le (n * M) (p * M) x
    rw [← Nat.add_mul, hfront] at this
    exact this
  -- sum split: `range (n+p) = range n ∪ (shifted range p)`, tail reindexed to the orbit frontier.
  have hsum : ∑ i ∈ Finset.range (n + p), g M (T^[i * M] x)
      = (∑ i ∈ Finset.range n, g M (T^[i * M] x))
        + ∑ i ∈ Finset.range p, g M (T^[i * M] ((T^[M])^[n] x)) := by
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [← hfront, ← Function.iterate_add_apply]
    congr 1
    ring
  rw [hsum]
  -- linear arithmetic on the three sums.
  set Sn := ∑ i ∈ Finset.range n, g M (T^[i * M] x)
  set Sp := ∑ i ∈ Finset.range p, g M (T^[i * M] ((T^[M])^[n] x))
  linarith

omit [MeasurableSpace X] in
/-- `vM g M n ≤ 0` for `n ≥ 1` when `g` is non-positive subadditive: block subadditivity
(`le_sum_blocks` with all `n` blocks equal to `M`) gives `g (n*M) ≤ ∑_{i<n} g M (T^[i*M])`. -/
theorem vM_nonpos {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (M n : ℕ)
    (hn : 1 ≤ n) (x : X) : vM (T := T) g M n x ≤ 0 := by
  simp only [vM, sub_nonpos]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- `le_sum_blocks` with constant block-length `ℓ = fun _ => M` and `k+1` blocks.
  have hblk := IsSubadditiveCocycle.le_sum_blocks hsub (fun _ => M) k x
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hblk
  exact hblk

/-- Each level `vM g M n` is integrable for measure-preserving `T` (a finite difference of
integrable terms; each `g M (T^[i*M] ·)` is integrable since `T^[i*M]` is measure-preserving). -/
theorem vM_integrable (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (M n : ℕ) :
    Integrable (vM (T := T) g M n) μ := by
  have heq : vM (T := T) g M n
      = fun x => g (n * M) x - ∑ i ∈ Finset.range n, g M (T^[i * M] x) := rfl
  rw [heq]
  refine (hint (n * M)).sub ?_
  exact integrable_finsetSum _
    (fun i _ => (hT.iterate (i * M)).integrable_comp_of_integrable (hint M))

/-- `T^[M]` is measure-preserving for measure-preserving `T` (stated for downstream use). -/
theorem vM_measurePreserving (hT : MeasurePreserving T μ μ) (M : ℕ) :
    MeasurePreserving (T^[M]) μ μ := hT.iterate M

/-- The integral of `vM g M n` is `(∫ g (n*M)) − n·(∫ g M)`: the orbit-sum integrates to
`n·∫ g M` by measure preservation. -/
theorem integral_vM (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (M n : ℕ) :
    ∫ x, vM (T := T) g M n x ∂μ = (∫ x, g (n * M) x ∂μ) - (n : ℝ) * ∫ x, g M x ∂μ := by
  have hintsum : Integrable (fun x => ∑ i ∈ Finset.range n, g M (T^[i * M] x)) μ :=
    integrable_finsetSum _ (fun i _ => (hT.iterate (i * M)).integrable_comp_of_integrable (hint M))
  have hsplit : ∫ x, vM (T := T) g M n x ∂μ
      = (∫ x, g (n * M) x ∂μ) - ∫ x, ∑ i ∈ Finset.range n, g M (T^[i * M] x) ∂μ := by
    rw [show (fun x => vM (T := T) g M n x)
      = fun x => g (n * M) x - ∑ i ∈ Finset.range n, g M (T^[i * M] x) from rfl]
    exact integral_sub (hint (n * M)) hintsum
  rw [hsplit]
  congr 1
  rw [integral_finsetSum (f := fun i x => g M (T^[i * M] x)) _
    (fun i _ => (hT.iterate (i * M)).integrable_comp_of_integrable (hint M))]
  have : ∀ i ∈ Finset.range n, ∫ x, g M (T^[i * M] x) ∂μ = ∫ x, g M x ∂μ :=
    fun i _ => integral_comp_iterate hT hint (i * M) M
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [MeasurableSpace X] in
/-- **Block sandwich (non-positive case).** For a non-positive subadditive cocycle and a block
length `M`, when `k*M ≤ m ≤ (k+1)*M` the cocycle value `g m x` is sandwiched:
`g ((k+1)*M) x ≤ g m x ≤ g (k*M) x`. (Upper bound: `g m = g (kM + (m−kM)) ≤ g (kM) + g (m−kM)(…) ≤
g (kM)` since `g (m−kM) ≤ 0`; the offset `0` case is equality. Lower bound symmetric using
`(k+1)M = m + ((k+1)M − m)`.) -/
theorem block_sandwich {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) (M k m : ℕ) (hkm : k * M ≤ m) (hmk : m ≤ (k + 1) * M)
    (x : X) : g ((k + 1) * M) x ≤ g m x ∧ g m x ≤ g (k * M) x := by
  have hnp : ∀ j, 1 ≤ j → ∀ y, g j y ≤ 0 := by
    intro j hj y; obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩; exact hnonpos i y
  constructor
  · -- `g ((k+1)*M) x ≤ g m x`: split `(k+1)*M = m + s`, `s = (k+1)*M − m`.
    set s : ℕ := (k + 1) * M - m with hs
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · have : (k + 1) * M = m := by omega
      rw [this]
    · have hsplit : (k + 1) * M = m + s := by omega
      calc g ((k + 1) * M) x = g (m + s) x := by rw [hsplit]
        _ ≤ g m x + g s (T^[m] x) := hsub.apply_add_le m s x
        _ ≤ g m x := by linarith [hnp s hspos (T^[m] x)]
  · -- `g m x ≤ g (k*M) x`: split `m = k*M + r`, `r = m − k*M`.
    set r : ℕ := m - k * M with hr
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · have : m = k * M := by omega
      rw [this]
    · have hsplit : m = k * M + r := by omega
      calc g m x = g (k * M + r) x := by rw [hsplit]
        _ ≤ g (k * M) x + g r (T^[k * M] x) := hsub.apply_add_le (k * M) r x
        _ ≤ g (k * M) x := by linarith [hnp r hrpos (T^[k * M] x)]

omit [MeasurableSpace X] in
/-- The pointwise subadditivity bound, normalized:
`cdiv g n x ≤ g 1 x / (n+1) + g n (T x)/(n+1)`. -/
theorem cdiv_le_shift {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    cdiv g n x ≤ g 1 x / (n + 1) + g n (T x) / (n + 1) := by
  have h := hsub.apply_add_le 1 n x
  rw [show (1 + n) = n + 1 from by ring] at h
  rw [cdiv, ← add_div]
  apply div_le_div_of_nonneg_right h (by positivity) |>.trans_eq
  simp only [Function.iterate_one]

/-! ### `EReal`-envelope `T`-invariance (non-positive case)

The `ℝ`-valued envelope invariance (`liminf_div_comp_ae`) requires the normalized cocycle to be
bounded below a.e. — a fact available only *after* `ae_tendsto_cdiv`. For the non-positive case
we need the envelope invariance *before* convergence, so we work directly in `EReal`, where the
`liminf`/`limsup` are total and no boundedness is needed. -/

omit [MeasurableSpace X] in
/-- **EReal `liminf` of a finite shift.** Liminf analogue of `ereal_limsup_add_coe`. -/
theorem ereal_liminf_add_coe (u : ℕ → ℝ) (c : ℝ) :
    Filter.liminf (fun n => ((u n : ℝ) : EReal) + (c : EReal)) atTop
      = Filter.liminf (fun n => ((u n : ℝ) : EReal)) atTop + (c : EReal) := by
  have h := (erealAddCoeIso c).liminf_apply (u := fun n => ((u n : ℝ) : EReal))
    (f := atTop) (by isBoundedDefault) (by isBoundedDefault)
    (by isBoundedDefault) (by isBoundedDefault)
  simp only [erealAddCoeIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk] at h
  exact h.symm

omit [MeasurableSpace X] in
/-- **EReal perturbation (`liminf`), one-sided.** If `a n − b n → 0` then
`liminf ↑b ≤ liminf ↑a` in `EReal`. Via `EReal.le_liminf_add` with the vanishing perturbation
`↑(a − b)`, whose `liminf` is `0`. No boundedness is required (`EReal` is a complete lattice). -/
theorem ereal_liminf_le_of_sub_tendsto_zero {a b : ℕ → ℝ}
    (hab : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    Filter.liminf (fun n => ((b n : ℝ) : EReal)) atTop
      ≤ Filter.liminf (fun n => ((a n : ℝ) : EReal)) atTop := by
  -- The perturbation `e n := ↑(a n − b n)` tends to `0`, so `liminf e = 0`.
  have hetend : Tendsto (fun n => ((a n - b n : ℝ) : EReal)) atTop (𝓝 ((0 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hab
  have heliminf : Filter.liminf (fun n => ((a n - b n : ℝ) : EReal)) atTop = 0 := by
    rw [hetend.liminf_eq]; norm_num
  -- `↑a = ↑b + ↑(a − b)` pointwise.
  have hsplit : (fun n => ((a n : ℝ) : EReal))
      = (fun n => ((b n : ℝ) : EReal)) + (fun n => ((a n - b n : ℝ) : EReal)) := by
    funext n
    simp only [Pi.add_apply]
    rw [← EReal.coe_add]
    congr 1
    ring
  -- `liminf ↑b + liminf e ≤ liminf (↑b + e) = liminf ↑a`.
  have hadd := EReal.le_liminf_add (f := atTop)
    (u := fun n => ((b n : ℝ) : EReal)) (v := fun n => ((a n - b n : ℝ) : EReal))
  rw [heliminf, add_zero] at hadd
  rwa [hsplit]

omit [MeasurableSpace X] in
/-- **EReal perturbation (`liminf`).** If two real sequences differ by a sequence tending to `0`,
their `EReal`-coerced `liminf`s coincide. -/
theorem ereal_liminf_eq_of_sub_tendsto_zero {u v : ℕ → ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    Filter.liminf (fun n => ((u n : ℝ) : EReal)) atTop
      = Filter.liminf (fun n => ((v n : ℝ) : EReal)) atTop := by
  refine le_antisymm ?_ (ereal_liminf_le_of_sub_tendsto_zero h)
  refine ereal_liminf_le_of_sub_tendsto_zero ?_
  have : (fun n => v n - u n) = (fun n => -(u n - v n)) := by funext n; ring
  rw [this]; simpa using h.neg

omit [MeasurableSpace X] in
/-- **EReal perturbation (`limsup`).** If two real sequences differ by a sequence tending to `0`,
their `EReal`-coerced `limsup`s coincide. Via `limsup_neg` and `ereal_liminf_eq_of_sub_tendsto_zero`
on the negated sequences. -/
theorem ereal_limsup_eq_of_sub_tendsto_zero {u v : ℕ → ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    Filter.limsup (fun n => ((u n : ℝ) : EReal)) atTop
      = Filter.limsup (fun n => ((v n : ℝ) : EReal)) atTop := by
  -- `limsup ↑u = -liminf (-↑u) = -liminf ↑(-u)`, and `(-u) − (-v) = -(u − v) → 0`.
  have hneg : Tendsto (fun n => (-u n) - (-v n)) atTop (𝓝 0) := by
    have : (fun n => (-u n) - (-v n)) = (fun n => -(u n - v n)) := by funext n; ring
    rw [this]; simpa using h.neg
  have key := ereal_liminf_eq_of_sub_tendsto_zero hneg
  have hrw : ∀ w : ℕ → ℝ, Filter.limsup (fun n => ((w n : ℝ) : EReal)) atTop
      = -Filter.liminf (fun n => ((-w n : ℝ) : EReal)) atTop := by
    intro w
    have hfun : (fun n => ((-w n : ℝ) : EReal)) = -(fun n => ((w n : ℝ) : EReal)) := by
      funext n; rw [Pi.neg_apply, EReal.coe_neg]
    rw [hfun, EReal.liminf_neg, neg_neg]
  rw [hrw u, hrw v, key]

omit [MeasurableSpace X] in
/-- **EReal ratio squeeze (`liminf`), one-sided.** If `z n ≤ 0`, `c n → 1`, `1 ≤ c n`, then the
nonpositive `EReal`-coerced products `↑(c n · z n)` (which are `≤ ↑(z n)`) have `liminf` no smaller
than that of `↑z`: `liminf ↑z ≤ liminf ↑(c · z)`. (The reverse is monotonicity.) For each `ε > 0`,
eventually `(1+ε)·z n ≤ c n · z n` (as `z ≤ 0`), and
`liminf ↑((1+ε)·z) = (1+ε)·liminf ↑z → liminf ↑z`
as `ε → 0`; the `EReal` scalar law `EReal.liminf_const_mul_of_nonneg_of_ne_top` handles the `−∞`
case uniformly. -/
theorem ereal_liminf_le_ratio {c z : ℕ → ℝ} (hz : ∀ n, z n ≤ 0)
    (_hc1 : ∀ n, 1 ≤ c n) (hctend : Tendsto c atTop (𝓝 1)) :
    Filter.liminf (fun n => ((z n : ℝ) : EReal)) atTop
      ≤ Filter.liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop := by
  set Lz : EReal := Filter.liminf (fun n => ((z n : ℝ) : EReal)) atTop with hLz
  set Lcz : EReal := Filter.liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop with hLcz
  -- `Lz ≤ 0`.
  have hLz0 : Lz ≤ 0 := by
    rw [hLz]
    refine le_trans (Filter.liminf_le_liminf (Eventually.of_forall fun n =>
      (EReal.coe_le_coe_iff.2 (hz n) : ((z n : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)))) ?_
    simp [Filter.liminf_const]
  -- For every real `ε > 0`: `↑(1+ε) * Lz ≤ Lcz`.
  have hkey : ∀ ε : ℝ, 0 < ε → (((1 + ε : ℝ) : EReal)) * Lz ≤ Lcz := by
    intro ε hε
    -- eventually `c n ≤ 1 + ε`, hence `(1+ε) * z n ≤ c n * z n` (as `z n ≤ 0`).
    have hev : ∀ᶠ n in atTop, ((((1 + ε) * z n : ℝ)) : EReal) ≤ ((c n * z n : ℝ) : EReal) := by
      have : ∀ᶠ n in atTop, c n ≤ 1 + ε := by
        have := (Metric.tendsto_atTop.1 hctend) ε hε
        obtain ⟨N, hN⟩ := this
        filter_upwards [eventually_ge_atTop N] with n hn
        have := hN n hn
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.2]
      filter_upwards [this] with n hcn
      refine EReal.coe_le_coe_iff.2 ?_
      exact mul_le_mul_of_nonpos_right hcn (hz n)
    have hmono : Filter.liminf (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) atTop ≤ Lcz :=
      Filter.liminf_le_liminf hev
    -- `liminf ↑((1+ε)·z) = ↑(1+ε) * liminf ↑z = ↑(1+ε) * Lz`.
    have hscalar : Filter.liminf (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) atTop
        = (((1 + ε : ℝ) : EReal)) * Lz := by
      have hfun : (fun n => ((((1 + ε) * z n : ℝ)) : EReal))
          = fun n => (((1 + ε : ℝ) : EReal)) * ((z n : ℝ) : EReal) := by
        funext n; rw [EReal.coe_mul]
      rw [hfun, hLz, EReal.liminf_const_mul_of_nonneg_of_ne_top (by positivity)
        (EReal.coe_ne_top _)]
    rwa [hscalar] at hmono
  -- Pass `ε → 0⁺`.  `Lz ≤ 0`, so either `Lz = ⊥` or `Lz` is finite.
  rcases eq_bot_or_bot_lt Lz with hbot | hfin
  · rw [hbot]; exact bot_le
  · -- finite case: `Lz = ↑a` with `a := Lz.toReal`.
    have hne_bot : Lz ≠ ⊥ := hfin.ne'
    have hne_top : Lz ≠ ⊤ := (hLz0.trans_lt (by norm_num : (0 : EReal) < ⊤)).ne
    set a : ℝ := Lz.toReal with hadef
    have ha : ((a : ℝ) : EReal) = Lz := EReal.coe_toReal hne_top hne_bot
    rw [← ha]
    -- `↑((1+ε)·a) ≤ Lcz` for all `ε > 0`; `(1+ε)·a → a`; conclude `↑a ≤ Lcz`.
    have hreal : ∀ ε : ℝ, 0 < ε → ((((1 + ε) * a : ℝ)) : EReal) ≤ Lcz := by
      intro ε hε
      have := hkey ε hε
      rw [← ha, ← EReal.coe_mul] at this
      exact this
    -- `Tendsto (fun ε => ↑((1+ε)·a)) (𝓝[>] 0) (𝓝 ↑a)`, and `Lcz` closed-above bound.
    have htend : Tendsto (fun ε : ℝ => ((((1 + ε) * a : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 ((a : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have : Tendsto (fun ε : ℝ => (1 + ε) * a) (𝓝 0) (𝓝 ((1 + 0) * a)) :=
        ((continuous_const.add continuous_id).mul continuous_const).tendsto 0
      simp only [add_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hreal ε hε

omit [MeasurableSpace X] in
/-- **EReal ratio squeeze (`limsup`), one-sided.** Dual of `ereal_liminf_le_ratio`:
`limsup ↑z ≤ limsup ↑(c · z)` when `z n ≤ 0`, `c n → 1`, `1 ≤ c n`. -/
theorem ereal_limsup_le_ratio {c z : ℕ → ℝ} (hz : ∀ n, z n ≤ 0)
    (_hc1 : ∀ n, 1 ≤ c n) (hctend : Tendsto c atTop (𝓝 1)) :
    Filter.limsup (fun n => ((z n : ℝ) : EReal)) atTop
      ≤ Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) atTop := by
  set Lz : EReal := Filter.limsup (fun n => ((z n : ℝ) : EReal)) atTop with hLz
  set Lcz : EReal := Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) atTop with hLcz
  have hLz0 : Lz ≤ 0 := by
    rw [hLz]
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall fun n =>
      (EReal.coe_le_coe_iff.2 (hz n) : ((z n : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)))) ?_
    simp [Filter.limsup_const]
  have hkey : ∀ ε : ℝ, 0 < ε → (((1 + ε : ℝ) : EReal)) * Lz ≤ Lcz := by
    intro ε hε
    have hev : ∀ᶠ n in atTop, ((((1 + ε) * z n : ℝ)) : EReal) ≤ ((c n * z n : ℝ) : EReal) := by
      have : ∀ᶠ n in atTop, c n ≤ 1 + ε := by
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hctend) ε hε
        filter_upwards [eventually_ge_atTop N] with n hn
        have := hN n hn
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.2]
      filter_upwards [this] with n hcn
      exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonpos_right hcn (hz n))
    have hmono : Filter.limsup (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) atTop ≤ Lcz :=
      Filter.limsup_le_limsup hev
    have hscalar : Filter.limsup (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) atTop
        = (((1 + ε : ℝ) : EReal)) * Lz := by
      have hfun : (fun n => ((((1 + ε) * z n : ℝ)) : EReal))
          = fun n => (((1 + ε : ℝ) : EReal)) * ((z n : ℝ) : EReal) := by
        funext n; rw [EReal.coe_mul]
      rw [hfun, hLz, EReal.limsup_const_mul_of_nonneg_of_ne_top (by positivity)
        (EReal.coe_ne_top _)]
    rwa [hscalar] at hmono
  rcases eq_bot_or_bot_lt Lz with hbot | hfin
  · rw [hbot]; exact bot_le
  · have hne_bot : Lz ≠ ⊥ := hfin.ne'
    have hne_top : Lz ≠ ⊤ := (hLz0.trans_lt (by norm_num : (0 : EReal) < ⊤)).ne
    set a : ℝ := Lz.toReal with hadef
    have ha : ((a : ℝ) : EReal) = Lz := EReal.coe_toReal hne_top hne_bot
    rw [← ha]
    have hreal : ∀ ε : ℝ, 0 < ε → ((((1 + ε) * a : ℝ)) : EReal) ≤ Lcz := by
      intro ε hε
      have := hkey ε hε
      rw [← ha, ← EReal.coe_mul] at this
      exact this
    have htend : Tendsto (fun ε : ℝ => ((((1 + ε) * a : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 ((a : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have : Tendsto (fun ε : ℝ => (1 + ε) * a) (𝓝 0) (𝓝 ((1 + 0) * a)) :=
        ((continuous_const.add continuous_id).mul continuous_const).tendsto 0
      simp only [add_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hreal ε hε

omit [MeasurableSpace X] in
/-- **EReal ratio squeeze (`limsup`), `c ≤ 1` companion.** If `z n ≤ 0`, `0 ≤ c n ≤ 1`, `c n → 1`,
then `limsup ↑(c · z) ≤ limsup ↑z`. (The reverse is monotonicity, since `c ≤ 1, z ≤ 0 ⟹ z ≤ c·z`.)
For each `ε ∈ (0,1)`, eventually `1 − ε ≤ c n`, so `c n · z n ≤ (1−ε)·z n` (as `z ≤ 0`), and
`limsup ↑((1−ε)·z) = (1−ε)·limsup ↑z → limsup ↑z` as `ε → 0`. -/
theorem ereal_ratio_le_limsup {c z : ℕ → ℝ} (hz : ∀ n, z n ≤ 0)
    (_hc1 : ∀ n, c n ≤ 1) (hctend : Tendsto c atTop (𝓝 1)) :
    Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) atTop
      ≤ Filter.limsup (fun n => ((z n : ℝ) : EReal)) atTop := by
  set Lz : EReal := Filter.limsup (fun n => ((z n : ℝ) : EReal)) atTop with hLz
  set Lcz : EReal := Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) atTop with hLcz
  have hLz0 : Lz ≤ 0 := by
    rw [hLz]
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall fun n =>
      (EReal.coe_le_coe_iff.2 (hz n) : ((z n : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)))) ?_
    simp [Filter.limsup_const]
  -- For every `ε ∈ (0,1)`: `Lcz ≤ ↑(1−ε) * Lz`.
  have hkey : ∀ ε : ℝ, 0 < ε → ε < 1 → Lcz ≤ (((1 - ε : ℝ) : EReal)) * Lz := by
    intro ε hε hε1
    have hev : ∀ᶠ n in atTop, ((c n * z n : ℝ) : EReal) ≤ ((((1 - ε) * z n : ℝ)) : EReal) := by
      have : ∀ᶠ n in atTop, 1 - ε ≤ c n := by
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hctend) ε hε
        filter_upwards [eventually_ge_atTop N] with n hn
        have := hN n hn
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.1]
      filter_upwards [this] with n hcn
      exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonpos_right hcn (hz n))
    have hmono : Lcz ≤ Filter.limsup (fun n => ((((1 - ε) * z n : ℝ)) : EReal)) atTop :=
      Filter.limsup_le_limsup hev
    have hscalar : Filter.limsup (fun n => ((((1 - ε) * z n : ℝ)) : EReal)) atTop
        = (((1 - ε : ℝ) : EReal)) * Lz := by
      have hfun : (fun n => ((((1 - ε) * z n : ℝ)) : EReal))
          = fun n => (((1 - ε : ℝ) : EReal)) * ((z n : ℝ) : EReal) := by
        funext n; rw [EReal.coe_mul]
      rw [hfun, hLz, EReal.limsup_const_mul_of_nonneg_of_ne_top
        (EReal.coe_nonneg.2 (by linarith)) (EReal.coe_ne_top _)]
    rwa [hscalar] at hmono
  rcases eq_bot_or_bot_lt Lz with hbot | hfin
  · -- `Lz = ⊥`: then `↑(1−ε)·⊥ = ⊥` for `1−ε > 0`, so `Lcz ≤ ⊥ = Lz`.
    rw [hbot]
    have := hkey (1/2) (by norm_num) (by norm_num)
    rw [hbot] at this
    rwa [EReal.mul_bot_of_pos
      (EReal.coe_pos.2 (by norm_num : (0 : ℝ) < 1 - 1/2))] at this
  · have hne_bot : Lz ≠ ⊥ := hfin.ne'
    have hne_top : Lz ≠ ⊤ := (hLz0.trans_lt (by norm_num : (0 : EReal) < ⊤)).ne
    set a : ℝ := Lz.toReal with hadef
    have ha : ((a : ℝ) : EReal) = Lz := EReal.coe_toReal hne_top hne_bot
    rw [← ha]
    have hreal : ∀ ε : ℝ, 0 < ε → ε < 1 → Lcz ≤ ((((1 - ε) * a : ℝ)) : EReal) := by
      intro ε hε hε1
      have := hkey ε hε hε1
      rw [← ha, ← EReal.coe_mul] at this
      exact this
    have htend : Tendsto (fun ε : ℝ => ((((1 - ε) * a : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 ((a : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have : Tendsto (fun ε : ℝ => (1 - ε) * a) (𝓝 0) (𝓝 ((1 - 0) * a)) :=
        ((continuous_const.sub continuous_id).mul continuous_const).tendsto 0
      simp only [sub_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε hε1
    exact hreal ε hε hε1

omit [MeasurableSpace X] in
/-- **EReal ratio squeeze (`liminf`), `c ≤ 1` companion.** Dual of `ereal_ratio_le_limsup`:
`liminf ↑(c · z) ≤ liminf ↑z` when `z n ≤ 0`, `0 ≤ c n ≤ 1`, `c n → 1`. -/
theorem ereal_ratio_le_liminf {c z : ℕ → ℝ} (hz : ∀ n, z n ≤ 0)
    (_hc1 : ∀ n, c n ≤ 1) (hctend : Tendsto c atTop (𝓝 1)) :
    Filter.liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop
      ≤ Filter.liminf (fun n => ((z n : ℝ) : EReal)) atTop := by
  set Lz : EReal := Filter.liminf (fun n => ((z n : ℝ) : EReal)) atTop with hLz
  set Lcz : EReal := Filter.liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop with hLcz
  have hLz0 : Lz ≤ 0 := by
    rw [hLz]
    refine le_trans (Filter.liminf_le_liminf (Eventually.of_forall fun n =>
      (EReal.coe_le_coe_iff.2 (hz n) : ((z n : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)))) ?_
    simp [Filter.liminf_const]
  have hkey : ∀ ε : ℝ, 0 < ε → ε < 1 → Lcz ≤ (((1 - ε : ℝ) : EReal)) * Lz := by
    intro ε hε hε1
    have hev : ∀ᶠ n in atTop, ((c n * z n : ℝ) : EReal) ≤ ((((1 - ε) * z n : ℝ)) : EReal) := by
      have : ∀ᶠ n in atTop, 1 - ε ≤ c n := by
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hctend) ε hε
        filter_upwards [eventually_ge_atTop N] with n hn
        have := hN n hn
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.1]
      filter_upwards [this] with n hcn
      exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonpos_right hcn (hz n))
    have hmono : Lcz ≤ Filter.liminf (fun n => ((((1 - ε) * z n : ℝ)) : EReal)) atTop :=
      Filter.liminf_le_liminf hev
    have hscalar : Filter.liminf (fun n => ((((1 - ε) * z n : ℝ)) : EReal)) atTop
        = (((1 - ε : ℝ) : EReal)) * Lz := by
      have hfun : (fun n => ((((1 - ε) * z n : ℝ)) : EReal))
          = fun n => (((1 - ε : ℝ) : EReal)) * ((z n : ℝ) : EReal) := by
        funext n; rw [EReal.coe_mul]
      rw [hfun, hLz, EReal.liminf_const_mul_of_nonneg_of_ne_top
        (EReal.coe_nonneg.2 (by linarith)) (EReal.coe_ne_top _)]
    rwa [hscalar] at hmono
  rcases eq_bot_or_bot_lt Lz with hbot | hfin
  · rw [hbot]
    have := hkey (1/2) (by norm_num) (by norm_num)
    rw [hbot] at this
    rwa [EReal.mul_bot_of_pos
      (EReal.coe_pos.2 (by norm_num : (0 : ℝ) < 1 - 1/2))] at this
  · have hne_bot : Lz ≠ ⊥ := hfin.ne'
    have hne_top : Lz ≠ ⊤ := (hLz0.trans_lt (by norm_num : (0 : EReal) < ⊤)).ne
    set a : ℝ := Lz.toReal with hadef
    have ha : ((a : ℝ) : EReal) = Lz := EReal.coe_toReal hne_top hne_bot
    rw [← ha]
    have hreal : ∀ ε : ℝ, 0 < ε → ε < 1 → Lcz ≤ ((((1 - ε) * a : ℝ)) : EReal) := by
      intro ε hε hε1
      have := hkey ε hε hε1
      rw [← ha, ← EReal.coe_mul] at this
      exact this
    have htend : Tendsto (fun ε : ℝ => ((((1 - ε) * a : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 ((a : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have : Tendsto (fun ε : ℝ => (1 - ε) * a) (𝓝 0) (𝓝 ((1 - 0) * a)) :=
        ((continuous_const.sub continuous_id).mul continuous_const).tendsto 0
      simp only [sub_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε hε1
    exact hreal ε hε hε1

omit [MeasurableSpace X] in
/-- **EReal `limsup` with a convergent real shift.** If `s n → σ` then
`limsup ↑(b n + s n) = limsup ↑(b n) + ↑σ`. -/
theorem ereal_limsup_add_tendsto {b s : ℕ → ℝ} {σ : ℝ}
    (hs : Tendsto s atTop (𝓝 σ)) :
    Filter.limsup (fun n => ((b n + s n : ℝ) : EReal)) atTop
      = Filter.limsup (fun n => ((b n : ℝ) : EReal)) atTop + (σ : EReal) := by
  have hperturb : Tendsto (fun n => (b n + s n) - (b n + σ)) atTop (𝓝 0) := by
    have : (fun n => (b n + s n) - (b n + σ)) = fun n => s n - σ := by funext n; ring
    rw [this]; have := hs.sub (tendsto_const_nhds (x := σ)); rwa [sub_self] at this
  rw [ereal_limsup_eq_of_sub_tendsto_zero hperturb]
  have hsplit : (fun n => ((b n + σ : ℝ) : EReal))
      = fun n => ((b n : ℝ) : EReal) + (σ : EReal) := by
    funext n; rw [EReal.coe_add]
  rw [hsplit, ereal_limsup_add_coe]

omit [MeasurableSpace X] in
/-- **EReal `liminf` with a convergent real shift.** If `s n → σ` then
`liminf ↑(b n + s n) = liminf ↑(b n) + ↑σ`. -/
theorem ereal_liminf_add_tendsto {b s : ℕ → ℝ} {σ : ℝ}
    (hs : Tendsto s atTop (𝓝 σ)) :
    Filter.liminf (fun n => ((b n + s n : ℝ) : EReal)) atTop
      = Filter.liminf (fun n => ((b n : ℝ) : EReal)) atTop + (σ : EReal) := by
  have hperturb : Tendsto (fun n => (b n + s n) - (b n + σ)) atTop (𝓝 0) := by
    have : (fun n => (b n + s n) - (b n + σ)) = fun n => s n - σ := by funext n; ring
    rw [this]; have := hs.sub (tendsto_const_nhds (x := σ)); rwa [sub_self] at this
  rw [ereal_liminf_eq_of_sub_tendsto_zero hperturb]
  have hsplit : (fun n => ((b n + σ : ℝ) : EReal))
      = fun n => ((b n : ℝ) : EReal) + (σ : EReal) := by
    funext n; rw [EReal.coe_add]
  rw [hsplit, ereal_liminf_add_coe]

omit [MeasurableSpace X] in
/-- **EReal `limsup` under positive real scaling.** For `0 ≤ r`,
`limsup ↑(r * b n) = ↑r * limsup ↑(b n)`. -/
theorem ereal_limsup_const_mul {r : ℝ} (hr : 0 ≤ r) (b : ℕ → ℝ) :
    Filter.limsup (fun n => ((r * b n : ℝ) : EReal)) atTop
      = (r : EReal) * Filter.limsup (fun n => ((b n : ℝ) : EReal)) atTop := by
  have hfun : (fun n => ((r * b n : ℝ) : EReal))
      = fun n => (r : EReal) * ((b n : ℝ) : EReal) := by funext n; rw [EReal.coe_mul]
  rw [hfun, EReal.limsup_const_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hr) (EReal.coe_ne_top _)]

omit [MeasurableSpace X] in
/-- **EReal `liminf` under positive real scaling.** For `0 ≤ r`,
`liminf ↑(r * b n) = ↑r * liminf ↑(b n)`. -/
theorem ereal_liminf_const_mul {r : ℝ} (hr : 0 ≤ r) (b : ℕ → ℝ) :
    Filter.liminf (fun n => ((r * b n : ℝ) : EReal)) atTop
      = (r : EReal) * Filter.liminf (fun n => ((b n : ℝ) : EReal)) atTop := by
  have hfun : (fun n => ((r * b n : ℝ) : EReal))
      = fun n => (r : EReal) * ((b n : ℝ) : EReal) := by funext n; rw [EReal.coe_mul]
  rw [hfun, EReal.liminf_const_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hr) (EReal.coe_ne_top _)]

/-- The `EReal` `liminf` envelope `x ↦ liminf (ecdiv g · x)` is a.e. measurable: it agrees a.e.
with the `EReal` liminf of measurable representatives of each level. -/
theorem aemeasurable_ereal_liminf {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.liminf (fun n => ecdiv g n x) atTop) μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.liminf (fun n => ((g₀ (n + 1) x / (n + 1) : ℝ) : EReal)) atTop, ?_, ?_⟩
  · exact Measurable.liminf (fun n => ((hg₀m (n + 1)).div_const _).coe_real_ereal)
  · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [ecdiv, cdiv]
    congr 1
    funext n
    rw [hx n]

/-- The `EReal` `limsup` envelope `x ↦ limsup (ecdiv g · x)` is a.e. measurable. -/
theorem aemeasurable_ereal_limsup {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.limsup (fun n => ecdiv g n x) atTop) μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.limsup (fun n => ((g₀ (n + 1) x / (n + 1) : ℝ) : EReal)) atTop, ?_, ?_⟩
  · exact Measurable.limsup (fun n => ((hg₀m (n + 1)).div_const _).coe_real_ereal)
  · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [ecdiv, cdiv]
    congr 1
    funext n
    rw [hx n]

omit [MeasurableSpace X] in
/-- The shift-and-ratio lower bound on the cocycle at `T x` (non-positive case): for every `k`,
`cdiv g k (T x) ≥ c k · z k − g 1 x/(k+1)`, where `z k := cdiv g (k+1) x ≤ 0` and
`c k := (k+2)/(k+1) ≥ 1`. From `g (k+2) x ≤ g 1 x + g (k+1) (T x)` (subadditivity, first block of
length `1`), so `g (k+1) (T x) ≥ g (k+2) x − g 1 x`; dividing by `k+1` and rewriting
`g (k+2) x/(k+1) = (k+2)/(k+1) · cdiv g (k+1) x`. -/
theorem cdiv_comp_ge_ratio {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (k : ℕ)
    (x : X) :
    ((k : ℝ) + 2) / ((k : ℝ) + 1) * cdiv g (k + 1) x - g 1 x / ((k : ℝ) + 1)
      ≤ cdiv g k (T x) := by
  have h := hsub.apply_add_le 1 (k + 1) x
  rw [show (1 + (k + 1)) = k + 2 from by ring, Function.iterate_one] at h
  -- `g (k+2) x ≤ g 1 x + g (k+1) (T x)`, so `g (k+1) (T x) ≥ g (k+2) x − g 1 x`.
  have hge : g (k + 2) x - g 1 x ≤ g (k + 1) (T x) := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  -- Divide by `k+1`.
  have hdiv : (g (k + 2) x - g 1 x) / ((k : ℝ) + 1) ≤ g (k + 1) (T x) / ((k : ℝ) + 1) :=
    div_le_div_of_nonneg_right hge hk1.le
  -- Rewrite both sides to the target form.
  have hlhs : ((k : ℝ) + 2) / ((k : ℝ) + 1) * cdiv g (k + 1) x - g 1 x / ((k : ℝ) + 1)
      = (g (k + 2) x - g 1 x) / ((k : ℝ) + 1) := by
    simp only [cdiv]
    rw [show (((k : ℕ) + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring]
    field_simp
  rw [hlhs]
  change (g (k + 2) x - g 1 x) / ((k : ℝ) + 1) ≤ g (k + 1) (T x) / ((k : ℝ) + 1)
  exact hdiv

omit [MeasurableSpace X] in
/-- The ratio sequence `c k := (k+2)/(k+1)` is `≥ 1` and tends to `1`. -/
theorem ratio_succ_tendsto_one :
    Tendsto (fun k : ℕ => ((k : ℝ) + 2) / ((k : ℝ) + 1)) atTop (𝓝 1) := by
  have hform : (fun k : ℕ => ((k : ℝ) + 2) / ((k : ℝ) + 1))
      = fun k : ℕ => 1 + ((k : ℝ) + 1)⁻¹ := by
    funext k
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hform]
  have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp this
  simpa using tendsto_const_nhds.add hinv

omit [MeasurableSpace X] in
/-- **EReal `liminf` comparison (non-positive case).** For every `x`,
`liminf (ecdiv g · x) ≤ liminf (ecdiv g · (T x))`. From the shift-and-ratio lower bound
`cdiv_comp_ge_ratio`, the ratio squeeze `ereal_liminf_le_ratio` (using `cdiv g (k+1) x ≤ 0`), the
vanishing perturbation `g 1 x/(k+1) → 0`, and the index shift `liminf (cdiv g · x) =
liminf (cdiv g (·+1) x)`. -/
theorem ereal_liminf_le_comp {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) (x : X) :
    Filter.liminf (fun n => ecdiv g n x) atTop
      ≤ Filter.liminf (fun n => ecdiv g n (T x)) atTop := by
  -- `z k := cdiv g (k+1) x ≤ 0`, `c k := (k+2)/(k+1)`, lower bound `y k := c k · z k − g1x/(k+1)`.
  set z : ℕ → ℝ := fun k => cdiv g (k + 1) x with hzdef
  set c : ℕ → ℝ := fun k => ((k : ℝ) + 2) / ((k : ℝ) + 1) with hcdef
  have hz : ∀ k, z k ≤ 0 := fun k => by
    simp only [hzdef, cdiv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [show (k + 1 + 1) = (k + 1) + 1 from rfl]; exact hnonpos (k + 1) x
  have hc1 : ∀ k, 1 ≤ c k := fun k => by
    simp only [hcdef]
    rw [le_div_iff₀ (by positivity)]; linarith
  -- bound `cdiv g k (T x) ≥ c k · z k − g1x/(k+1)`.
  have hbound : ∀ k, c k * z k - g 1 x / ((k : ℝ) + 1) ≤ cdiv g k (T x) :=
    fun k => cdiv_comp_ge_ratio hsub k x
  -- chain of EReal inequalities.
  calc Filter.liminf (fun n => ecdiv g n x) atTop
      = Filter.liminf (fun k => ((z k : ℝ) : EReal)) atTop := by
        rw [hzdef]
        exact (Filter.liminf_nat_add (fun n => ((cdiv g n x : ℝ) : EReal)) 1).symm
    _ ≤ Filter.liminf (fun k => ((c k * z k : ℝ) : EReal)) atTop := by
        have hct : Tendsto c atTop (𝓝 1) := by rw [hcdef]; exact ratio_succ_tendsto_one
        exact ereal_liminf_le_ratio hz hc1 hct
    _ = Filter.liminf (fun k => ((c k * z k - g 1 x / ((k : ℝ) + 1) : ℝ) : EReal)) atTop := by
        refine ereal_liminf_eq_of_sub_tendsto_zero ?_
        have : (fun k => c k * z k - (c k * z k - g 1 x / ((k : ℝ) + 1)))
            = fun k : ℕ => g 1 x / ((k : ℝ) + 1) := by funext k; ring
        rw [this]
        simp only [div_eq_mul_inv]
        have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          have : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
            tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
          exact tendsto_inv_atTop_zero.comp this
        simpa using hinv.const_mul (g 1 x)
    _ ≤ Filter.liminf (fun k => ((cdiv g k (T x) : ℝ) : EReal)) atTop := by
        refine Filter.liminf_le_liminf (Eventually.of_forall fun k =>
          EReal.coe_le_coe_iff.2 (hbound k)) ?_ ?_
        · exact Filter.isBounded_ge_of_bot
        · exact Filter.isCobounded_ge_of_top
    _ = Filter.liminf (fun n => ecdiv g n (T x)) atTop := rfl

omit [MeasurableSpace X] in
/-- **EReal `limsup` comparison (non-positive case).** For every `x`,
`limsup (ecdiv g · x) ≤ limsup (ecdiv g · (T x))`. Same route as `ereal_liminf_le_comp` with
`ereal_limsup_le_ratio` and `ereal_limsup_eq_of_sub_tendsto_zero`. -/
theorem ereal_limsup_le_comp {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) (x : X) :
    Filter.limsup (fun n => ecdiv g n x) atTop
      ≤ Filter.limsup (fun n => ecdiv g n (T x)) atTop := by
  set z : ℕ → ℝ := fun k => cdiv g (k + 1) x with hzdef
  set c : ℕ → ℝ := fun k => ((k : ℝ) + 2) / ((k : ℝ) + 1) with hcdef
  have hz : ∀ k, z k ≤ 0 := fun k => by
    simp only [hzdef, cdiv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [show (k + 1 + 1) = (k + 1) + 1 from rfl]; exact hnonpos (k + 1) x
  have hc1 : ∀ k, 1 ≤ c k := fun k => by
    simp only [hcdef]
    rw [le_div_iff₀ (by positivity)]; linarith
  have hbound : ∀ k, c k * z k - g 1 x / ((k : ℝ) + 1) ≤ cdiv g k (T x) :=
    fun k => cdiv_comp_ge_ratio hsub k x
  calc Filter.limsup (fun n => ecdiv g n x) atTop
      = Filter.limsup (fun k => ((z k : ℝ) : EReal)) atTop := by
        rw [hzdef]
        exact (Filter.limsup_nat_add (fun n => ((cdiv g n x : ℝ) : EReal)) 1).symm
    _ ≤ Filter.limsup (fun k => ((c k * z k : ℝ) : EReal)) atTop := by
        have hct : Tendsto c atTop (𝓝 1) := by rw [hcdef]; exact ratio_succ_tendsto_one
        exact ereal_limsup_le_ratio hz hc1 hct
    _ = Filter.limsup (fun k => ((c k * z k - g 1 x / ((k : ℝ) + 1) : ℝ) : EReal)) atTop := by
        refine ereal_limsup_eq_of_sub_tendsto_zero ?_
        have : (fun k => c k * z k - (c k * z k - g 1 x / ((k : ℝ) + 1)))
            = fun k : ℕ => g 1 x / ((k : ℝ) + 1) := by funext k; ring
        rw [this]
        simp only [div_eq_mul_inv]
        have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          have : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
            tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
          exact tendsto_inv_atTop_zero.comp this
        simpa using hinv.const_mul (g 1 x)
    _ ≤ Filter.limsup (fun k => ((cdiv g k (T x) : ℝ) : EReal)) atTop := by
        refine Filter.limsup_le_limsup (Eventually.of_forall fun k =>
          EReal.coe_le_coe_iff.2 (hbound k)) ?_ ?_
        · exact Filter.isCobounded_le_of_bot
        · exact Filter.isBounded_le_of_top
    _ = Filter.limsup (fun n => ecdiv g n (T x)) atTop := rfl

/-- **EReal version of `ae_eq_comp_of_le_comp`.** For an a.e.-measurable `EReal`-valued `F`
with `F x ≤ F (T x)` a.e., `F ∘ T =ᵐ[μ] F`. Verbatim adaptation of the `ℝ` proof, with rational
levels `↑(c : ℚ) : EReal` and `EReal.exists_rat_btwn_of_lt` for the separation step. -/
theorem ereal_ae_eq_comp_of_le_comp [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {F : X → EReal} (hF : AEMeasurable F μ)
    (hle : ∀ᵐ x ∂μ, F x ≤ F (T x)) : F ∘ T =ᵐ[μ] F := by
  set F0 : X → EReal := hF.mk F with hF0def
  have hF0m : Measurable F0 := hF.measurable_mk
  have hFF0 : F =ᵐ[μ] F0 := hF.ae_eq_mk
  have hkey : ∀ c : ℚ,
      T ⁻¹' {x | (((c : ℝ) : EReal)) ≤ F x} =ᵐ[μ] {x | (((c : ℝ) : EReal)) ≤ F x} := by
    intro c
    set s : Set X := {x | (((c : ℝ) : EReal)) ≤ F x} with hs
    have hsmeas : NullMeasurableSet s μ := by
      have hseq : s =ᵐ[μ] {x | (((c : ℝ) : EReal)) ≤ F0 x} := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [hFF0] with x hx
        simp only [hs, Set.mem_setOf_eq, hx]
      exact (measurableSet_le measurable_const hF0m).nullMeasurableSet.congr hseq.symm
    have hsub : s ≤ᵐ[μ] T ⁻¹' s := by
      filter_upwards [hle] with x hx hxs
      have hxs' : (((c : ℝ) : EReal)) ≤ F x := hxs
      exact le_trans hxs' hx
    have hmeq : μ (T ⁻¹' s) = μ s := hT.measure_preimage hsmeas
    have : s =ᵐ[μ] T ⁻¹' s :=
      ae_eq_of_ae_subset_of_measure_ge hsub (le_of_eq hmeq) hsmeas (measure_ne_top μ _)
    exact this.symm
  have hall : ∀ᵐ x ∂μ, ∀ c : ℚ,
      (x ∈ T ⁻¹' {x | (((c : ℝ) : EReal)) ≤ F x}) ↔ (x ∈ {x | (((c : ℝ) : EReal)) ≤ F x}) := by
    rw [ae_all_iff]
    intro c
    exact Filter.eventuallyEq_set.1 (hkey c)
  filter_upwards [hall] with x hx
  change F (T x) = F x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `F (T x) < F x`: pick rational `c` with `F (T x) < ↑c < F x`.
    obtain ⟨c, hc1, hc2⟩ := EReal.exists_rat_btwn_of_lt hlt
    have := (hx c).symm
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at this
    exact absurd (this.1 hc2.le) (not_le.2 hc1)
  · -- `F x < F (T x)`: pick rational `c` with `F x < ↑c < F (T x)`.
    obtain ⟨c, hc1, hc2⟩ := EReal.exists_rat_btwn_of_lt hgt
    have := hx c
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at this
    exact absurd (this.1 hc2.le) (not_le.2 hc1)

/-- **EReal `liminf`-envelope `T`-invariance (non-positive case).**
`(fun x => liminf (ecdiv g · x)) ∘ T =ᵐ[μ] …`. -/
theorem liminf_ecdiv_comp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) :
    (fun x => Filter.liminf (fun n => ecdiv g n x) atTop) ∘ T
      =ᵐ[μ] fun x => Filter.liminf (fun n => ecdiv g n x) atTop :=
  ereal_ae_eq_comp_of_le_comp hT (aemeasurable_ereal_liminf hint)
    (Eventually.of_forall (fun x => ereal_liminf_le_comp hsub hnonpos x))

/-- **EReal `limsup`-envelope `T`-invariance (non-positive case).**
`(fun x => limsup (ecdiv g · x)) ∘ T =ᵐ[μ] …`. -/
theorem limsup_ecdiv_comp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) :
    (fun x => Filter.limsup (fun n => ecdiv g n x) atTop) ∘ T
      =ᵐ[μ] fun x => Filter.limsup (fun n => ecdiv g n x) atTop :=
  ereal_ae_eq_comp_of_le_comp hT (aemeasurable_ereal_limsup hint)
    (Eventually.of_forall (fun x => ereal_limsup_le_comp hsub hnonpos x))


end Oseledets.Kingman
