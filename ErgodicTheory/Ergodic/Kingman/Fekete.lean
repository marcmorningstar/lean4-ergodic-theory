/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Ergodic.Birkhoff
import Mathlib.Analysis.Subadditive
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Subadditive cocycles: Fekete's lemma and the EReal envelope setup

The definition of a subadditive cocycle and the first layer of Kingman's subadditive ergodic
theorem: Fekete's lemma giving the limit `γ` of the normalized integrals, the `EReal`-valued
`limsup`/`liminf` envelopes of the normalized cocycle, their a.e. measurability and boundedness,
and the Fatou step bounding the limsup envelope and the integrability of its positive part.

The public statement of the theorem lives in `ErgodicTheory.Ergodic.Kingman.Core`; the intermediate
constructions are internal infrastructure and live in the `ErgodicTheory.Kingman` namespace.

## Main definitions

* `ErgodicTheory.IsSubadditiveCocycle` — a sequence `g : ℕ → X → ℝ` with
  `g (m + n) x ≤ g m x + g n (T^[m] x)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- A sequence `g : ℕ → X → ℝ` is a **subadditive cocycle** over `T` when
`g (m + n) x ≤ g m x + g n (T^[m] x)` for all `m, n, x`. (For `gₙ = log‖A⁽ⁿ⁾‖` this
follows from submultiplicativity of the operator norm and the cocycle identity.) -/
structure IsSubadditiveCocycle (T : X → X) (g : ℕ → X → ℝ) : Prop where
  apply_add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)

omit [MeasurableSpace X] in
/-- **Singleton partition subadditivity.** For `n ≥ 1`, a subadditive cocycle is
dominated by the Birkhoff sum of its first level: `g (n+1) x ≤ birkhoffSum T (g 1) (n+1) x`.
(The statement fails at `n = 0`: subadditivity only forces `0 ≤ g 0 x`, not `g 0 x ≤ 0`.) -/
theorem IsSubadditiveCocycle.le_birkhoffSum_one {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    g (n + 1) x ≤ birkhoffSum T (g 1) (n + 1) x := by
  induction n with
  | zero => simp only [Nat.zero_add, birkhoffSum_one]; exact le_refl _
  | succ n ih =>
      rw [birkhoffSum_succ]
      calc g (n + 1 + 1) x ≤ g (n + 1) x + g 1 (T^[n + 1] x) := hsub.apply_add_le (n + 1) 1 x
        _ ≤ birkhoffSum T (g 1) (n + 1) x + g 1 (T^[n + 1] x) := by linarith [ih]

omit [MeasurableSpace X] in
/-- **Block subadditivity.** For a subadditive cocycle and any consecutive block
decomposition of `[0, n)` into `k+1` blocks of lengths `ℓ 0, …, ℓ k` (with
`n = ∑_{i ≤ k} ℓ i`), the cocycle is dominated by the sum of the block cocycle values along
the orbit, evaluated at the partial-sum frontiers `T^[∑_{j < i} ℓ j] x`. (Used by the
`Tᴹ`-subsequence cocycle algebra; stated for `k+1` blocks since the empty decomposition
would force the false `g 0 x ≤ 0`.) -/
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

end ErgodicTheory

namespace ErgodicTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-! ### Reindexing the normalized sequence -/

omit [MeasurableSpace X] in
/-- **Reindexing.** The Kingman sequence `(n : ℝ)⁻¹ * g n x` converges to `L` iff the
shifted sequence `g (n+1) x / (n+1)` converges to `L`. The `n = 0` term of the original
sequence is `0⁻¹ * g 0 x = 0`, so dropping it is harmless. -/
theorem tendsto_kingman_reindex {g : ℕ → X → ℝ} {x : X} {L : ℝ} :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 L) ↔
      Tendsto (fun n : ℕ => g (n + 1) x / (n + 1)) atTop (𝓝 L) := by
  rw [← tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ)⁻¹ * g n x) 1]
  refine tendsto_congr (fun n => ?_)
  push_cast
  rw [div_eq_inv_mul]

/-! ### Integral of a measure-preserving composition -/

/-- The integral of a measure-preserving composition equals the integral:
`∫ g n (T^[m] x) ∂μ = ∫ g n x ∂μ`. -/
theorem integral_comp_iterate (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (m n : ℕ) :
    ∫ x, g n (T^[m] x) ∂μ = ∫ x, g n x ∂μ := by
  have hmp : MeasurePreserving (T^[m]) μ μ := hT.iterate m
  have haesm : AEStronglyMeasurable (g n) (Measure.map (T^[m]) μ) := by
    rw [hmp.map_eq]; exact (hint n).aestronglyMeasurable
  have hmap := integral_map (μ := μ) (φ := T^[m]) hmp.aemeasurable (f := g n) haesm
  rw [hmp.map_eq] at hmap
  exact hmap.symm

/-- **Integral subadditivity.** The integral sequence `aₙ = ∫ gₙ` is subadditive
in Mathlib's sense (`a (m+n) ≤ a m + a n`), the Fekete input. -/
theorem integral_subadditive (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
    Subadditive (fun n => ∫ x, g n x ∂μ) := by
  intro m n
  simp only
  have hcomp : Integrable (fun x => g n (T^[m] x)) μ :=
    (hT.iterate m).integrable_comp_of_integrable (hint n)
  calc ∫ x, g (m + n) x ∂μ
      ≤ ∫ x, (g m x + g n (T^[m] x)) ∂μ :=
        integral_mono (hint _) ((hint m).add hcomp) (fun x => hsub.apply_add_le m n x)
    _ = (∫ x, g m x ∂μ) + ∫ x, g n (T^[m] x) ∂μ := integral_add (hint m) hcomp
    _ = (∫ x, g m x ∂μ) + ∫ x, g n x ∂μ := by rw [integral_comp_iterate hT hint m n]

/-! ### Fekete: the limit `γ` of the normalized integrals -/

/-- **Fekete.** The normalized integral sequence `(∫ g (n+1)) / (n+1)` converges to
the Fekete constant `γ := (integral_subadditive …).lim`. The `n+1`-indexed bounded-below
hypothesis is bridged to the `n`-indexed Fekete input by hand (the `n = 0` term is
`(∫ g 0)/0 = 0`). -/
theorem exists_fekete (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ γ : ℝ, Tendsto (fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1)) atTop (𝓝 γ) := by
  set a : ℕ → ℝ := fun n => ∫ x, g n x ∂μ with hadef
  have hsa : Subadditive a := integral_subadditive hT hsub hint
  -- Bridge the `n+1`-indexed bound to a bound on `{a n / n}` over all `n`.
  have hbdd' : BddBelow (Set.range fun n : ℕ => a n / n) := by
    obtain ⟨lb, hlb⟩ := hbdd
    refine ⟨min lb 0, ?_⟩
    rintro y ⟨n, rfl⟩
    rcases n with _ | m
    · -- `n = 0`: `a 0 / 0 = 0 ≥ min lb 0`.
      simp only [Nat.cast_zero, div_zero]
      exact min_le_right lb 0
    · -- `n = m + 1`: bounded by `lb` from `hbdd`.
      have hmem : a (m + 1) / ((m : ℝ) + 1)
          ∈ Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1) :=
        ⟨m, by simp only [hadef]⟩
      have : (fun n : ℕ => a n / n) (m + 1) = a (m + 1) / ((m : ℝ) + 1) := by push_cast; ring
      rw [this]
      exact le_trans (min_le_left lb 0) (hlb hmem)
  -- Fekete: `a n / n → γ`, and the shifted sequence shares the limit.
  refine ⟨hsa.lim, ?_⟩
  have hlim := hsa.tendsto_lim hbdd'
  rw [← tendsto_add_atTop_iff_nat (f := fun n : ℕ => a n / n) 1] at hlim
  refine hlim.congr (fun n => ?_)
  show a (n + 1) / ((n + 1 : ℕ) : ℝ) = (∫ x, g (n + 1) x ∂μ) / ((n : ℝ) + 1)
  simp only [hadef, Nat.cast_add, Nat.cast_one]

/-! ### A.e. `T`-invariance from monotonicity under `T` -/

/-- **Invariance from `F ≤ F ∘ T`.** If `F` is a.e. measurable, `T` is
measure-preserving on a finite measure, and `F x ≤ F (T x)` for a.e. `x`, then
`F ∘ T =ᵐ[μ] F`. The upper level sets `{c ≤ F}` satisfy `{c ≤ F} ⊆ᵐ T⁻¹ {c ≤ F}` with
equal (finite) measure, hence agree a.e.; ranging over rational `c` gives invariance. -/
theorem ae_eq_comp_of_le_comp [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {F : X → ℝ} (hF : AEMeasurable F μ)
    (hle : ∀ᵐ x ∂μ, F x ≤ F (T x)) : F ∘ T =ᵐ[μ] F := by
  -- A measurable representative for the level-set null-measurability.
  set F0 : X → ℝ := hF.mk F with hF0def
  have hF0m : Measurable F0 := hF.measurable_mk
  have hFF0 : F =ᵐ[μ] F0 := hF.ae_eq_mk
  -- For each rational `c`, `{c ≤ F}` and its preimage agree a.e.
  have hkey : ∀ c : ℚ, T ⁻¹' {x | (c : ℝ) ≤ F x} =ᵐ[μ] {x | (c : ℝ) ≤ F x} := by
    intro c
    set s : Set X := {x | (c : ℝ) ≤ F x} with hs
    -- `s` is null-measurable via the representative `F0`.
    have hsmeas : NullMeasurableSet s μ := by
      have hseq : s =ᵐ[μ] {x | (c : ℝ) ≤ F0 x} := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [hFF0] with x hx
        simp only [hs, Set.mem_setOf_eq, hx]
      exact (measurableSet_le measurable_const hF0m).nullMeasurableSet.congr hseq.symm
    -- `s ⊆ᵐ T⁻¹ s` because a.e. `F x ≤ F (T x)`.
    have hsub : s ≤ᵐ[μ] T ⁻¹' s := by
      filter_upwards [hle] with x hx hxs
      have hxs' : (c : ℝ) ≤ F x := hxs
      exact le_trans hxs' hx
    -- equal measures.
    have hmeq : μ (T ⁻¹' s) = μ s := hT.measure_preimage hsmeas
    -- `s =ᵐ T⁻¹ s` (a.e. subset of equal finite measure).
    have : s =ᵐ[μ] T ⁻¹' s :=
      ae_eq_of_ae_subset_of_measure_ge hsub (le_of_eq hmeq) hsmeas (measure_ne_top μ _)
    exact this.symm
  -- Collect over rationals: a.e. `x` satisfies the equivalence for all `c`.
  have hall : ∀ᵐ x ∂μ, ∀ c : ℚ,
      (x ∈ T ⁻¹' {x | (c : ℝ) ≤ F x}) ↔ (x ∈ {x | (c : ℝ) ≤ F x}) := by
    rw [ae_all_iff]
    intro c
    exact Filter.eventuallyEq_set.1 (hkey c)
  filter_upwards [hall] with x hx
  -- From `∀ c, (c ≤ F (T x)) ↔ (c ≤ F x)`, deduce `F (T x) = F x`.
  change F (T x) = F x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `F (T x) < F x`: pick rational `c` in between, contradict via `hx`.
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hlt
    have := (hx c).symm
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at this
    exact absurd (this.1 hc2.le) (not_le.2 hc1)
  · -- `F x < F (T x)`: pick rational `c` with `F x < c < F (T x)`, contradict via `hx`.
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hgt
    have := hx c
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at this
    exact absurd (this.1 hc2.le) (not_le.2 hc1)

/-! ### Notation for the normalized cocycle and its envelopes

`cdiv g n x := g (n+1) x / (n+1)` is the normalized sequence whose limit Kingman's theorem
identifies; `f₊ = limsup`, `f₋ = liminf`. -/

/-- The normalized cocycle `g (n+1) x / (n+1)` — the sequence whose a.e. limit is the
content of Kingman's theorem. -/
noncomputable def cdiv (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ := g (n + 1) x / (n + 1)

omit [MeasurableSpace X] in
/-- `cdiv g n x` is dominated by the Birkhoff average of `g 1`: an immediate rephrasing of
`le_birkhoffSum_one`. -/
theorem cdiv_le_birkhoffAverage {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (n : ℕ) (x : X) : cdiv g n x ≤ birkhoffAverage ℝ T (g 1) (n + 1) x := by
  have h := hsub.le_birkhoffSum_one n x
  rw [cdiv, birkhoffAverage, smul_eq_mul]
  rw [div_eq_inv_mul]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  apply mul_le_mul_of_nonneg_left h (le_of_lt (by positivity))

/-! ### A.e. measurability of the limsup/liminf envelopes -/

/-- The pointwise `limsup` of `cdiv g · x` is a.e. measurable: it agrees a.e.
with the limsup of measurable representatives of each level `g (n+1)`. -/
theorem aemeasurable_limsup_div {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.limsup (fun n => cdiv g n x) atTop) μ := by
  -- Measurable representatives of each level.
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.limsup (fun n => g₀ (n + 1) x / (n + 1)) atTop, ?_, ?_⟩
  · exact Measurable.limsup (fun n => (hg₀m (n + 1)).div_const _)
  · -- The two sequences agree a.e. for all `n` simultaneously.
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [cdiv]
    congr 1
    funext n
    rw [hx n]

/-- The pointwise `liminf` of `cdiv g · x` is a.e. measurable. -/
theorem aemeasurable_liminf_div {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.liminf (fun n => cdiv g n x) atTop) μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.liminf (fun n => g₀ (n + 1) x / (n + 1)) atTop, ?_, ?_⟩
  · exact Measurable.liminf (fun n => (hg₀m (n + 1)).div_const _)
  · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [cdiv]
    congr 1
    funext n
    rw [hx n]

/-! ### Boundedness of the normalized cocycle

A.e., the range of `cdiv g · x` is bounded above (immediate from `le_birkhoffSum_one` and
a.e. boundedness of
the Birkhoff averages of `g 1`). The bounded-below direction is the subtle one: subadditivity
gives only upper bounds, so a.e. finiteness of the liminf holds only once a.e. convergence is
known. Accordingly it is derived from the core lemma `ae_tendsto_cdiv` (a convergent sequence
is bounded), defined below. -/

/-- A.e. the range of `cdiv g · x` is bounded above (`le_birkhoffSum_one` +
`ae_bddAbove_birkhoffAverage`). -/
theorem ae_bddAbove_cdiv [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
    ∀ᵐ x ∂μ, BddAbove (Set.range fun n : ℕ => cdiv g n x) := by
  filter_upwards [ae_bddAbove_birkhoffAverage hT (hint 1)] with x hx
  obtain ⟨M, hM⟩ := hx
  refine ⟨M, ?_⟩
  rintro y ⟨n, rfl⟩
  exact le_trans (cdiv_le_birkhoffAverage hsub n x) (hM (Set.mem_range_self n))

/-! ### EReal envelopes (avoiding the `ℝ` junk value at `−∞`)

The normalized cocycle may a priori tend to `−∞` on a positive-measure set, where the
`ℝ`-valued `Filter.liminf`/`limsup` return the junk value `0`. To control the relevant
extrema before finiteness is established we coerce the sequence into `EReal`, a
`CompleteLinearOrder` where `Filter.limsup`/`liminf` are total and `liminf ≤ limsup` is
unconditional. The two facts produced here — `limsup < ⊤` (envelope, from
`le_birkhoffSum_one` and Birkhoff convergence) and
`limsup > ⊥` (Fatou) — together with the hard `limsup ≤ liminf` (`ae_ereal_liminf_eq_limsup`)
pin the `EReal` `limsup`/`liminf` to a common finite value, from which the `ℝ` convergence
follows. -/

/-- The `EReal`-coerced normalized cocycle. -/
noncomputable def ecdiv (g : ℕ → X → ℝ) (n : ℕ) (x : X) : EReal := (cdiv g n x : EReal)

/-- **Envelope.** A.e. the `EReal` `limsup` of the normalized cocycle is bounded above by the
(finite) conditional expectation `μ[g 1 | invariants T]`, hence is `< ⊤`. From
`cdiv_le_birkhoffAverage` and the Birkhoff convergence `birkhoffAverage g₁ (n+1) → μ[g₁|I]`. -/
theorem ae_ereal_limsup_le_condExp [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
    ∀ᵐ x ∂μ, Filter.limsup (fun n => ecdiv g n x) atTop
      ≤ ((μ[g 1 | MeasurableSpace.invariants T] x : ℝ) : EReal) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT (hint 1)] with x hBconv
  -- `A_{n+1}(g₁) x → B x`, so the shifted `EReal` sequence converges to `↑(B x)`.
  set B : ℝ := (μ[g 1 | MeasurableSpace.invariants T]) x with hBdef
  have hshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop (𝓝 B) :=
    hBconv.comp (tendsto_add_atTop_nat 1)
  have heshift : Tendsto (fun n : ℕ => ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal))
      atTop (𝓝 ((B : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hshift
  -- `limsup (ecdiv) ≤ limsup (↑A_{n+1}) = ↑B`.
  have hle : Filter.limsup (fun n => ecdiv g n x) atTop
      ≤ Filter.limsup (fun n : ℕ => ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal)) atTop := by
    refine Filter.limsup_le_limsup ?_ ?_ ?_
    · filter_upwards with n
      exact EReal.coe_le_coe_iff.2 (cdiv_le_birkhoffAverage hsub n x)
    · exact Filter.isCobounded_le_of_bot
    · exact Filter.isBounded_le_of_top
  rw [heshift.limsup_eq] at hle
  exact hle

/-! ### The Fatou step: finiteness of the limsup and integrability of `f₊`

The normalized cocycle satisfies `cdiv g n x ≤ birkhoffAverage ℝ T (g 1) (n+1) x`
(`le_birkhoffSum_one`), so the
nonnegative defect `d n x := birkhoffAverage ℝ T (g 1) (n+1) x − cdiv g n x ≥ 0` controls how
far `cdiv` can drop. A single `ℝ≥0∞` Fatou pass (`lintegral_liminf_le`) on `ENNReal.ofReal (d n)`
shows `liminf_n (d n x) < ∞` a.e., which (since the Birkhoff average converges) is exactly
`limsup_n (cdiv g n x) > −∞` a.e. (i.e. `⊥ < EReal limsup`), and also yields that the limsup
envelope `f₊` is integrable. -/

/-- The nonnegative Fatou defect `birkhoffAverage ℝ T (g 1) (n+1) x − cdiv g n x ≥ 0`. -/
noncomputable def fdefect (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ :=
  birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x

omit [MeasurableSpace X] in
/-- The Fatou defect is nonnegative, by `cdiv_le_birkhoffAverage`. -/
theorem fdefect_nonneg {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    0 ≤ fdefect (T := T) g n x :=
  sub_nonneg.2 (cdiv_le_birkhoffAverage hsub n x)

/-- The integral of `birkhoffAverage ℝ T (g 1) (n+1)` is `∫ g 1`: the Birkhoff average is an
average of measure-preserving compositions of `g 1`, each with integral `∫ g 1`. -/
theorem integral_birkhoffAverage_eq (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    ∫ x, birkhoffAverage ℝ T (g 1) (n + 1) x ∂μ = ∫ x, g 1 x ∂μ := by
  have hsum : ∫ x, birkhoffSum T (g 1) (n + 1) x ∂μ = ((n : ℝ) + 1) * ∫ x, g 1 x ∂μ := by
    simp only [birkhoffSum]
    rw [integral_finsetSum (f := fun k x => g 1 (T^[k] x)) _
      (fun j _ => (hT.iterate j).integrable_comp_of_integrable (hint 1))]
    have : ∀ j ∈ Finset.range (n + 1), ∫ x, g 1 (T^[j] x) ∂μ = ∫ x, g 1 x ∂μ :=
      fun j _ => integral_comp_iterate hT hint j 1
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  have hbeq : (fun x => birkhoffAverage ℝ T (g 1) (n + 1) x)
      = fun x => ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g 1) (n + 1) x := rfl
  have hba : ∫ x, birkhoffAverage ℝ T (g 1) (n + 1) x ∂μ
      = ((n + 1 : ℕ) : ℝ)⁻¹ * ∫ x, birkhoffSum T (g 1) (n + 1) x ∂μ := by
    rw [show (∫ x, birkhoffAverage ℝ T (g 1) (n + 1) x ∂μ)
        = ∫ x, ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g 1) (n + 1) x ∂μ from by rw [hbeq],
      integral_const_mul]
  rw [hba, hsum, show (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- `cdiv g n` is integrable (`g (n+1)` divided by a constant). -/
theorem integrable_cdiv {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (cdiv g n) μ := by
  have : cdiv g n = fun x => g (n + 1) x / ((n : ℝ) + 1) := rfl
  rw [this]
  exact (hint (n + 1)).div_const _

/-- `birkhoffAverage ℝ T (g 1) (n+1)` is integrable. -/
theorem integrable_birkhoffAverage_one (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (fun x => birkhoffAverage ℝ T (g 1) (n + 1) x) μ := by
  have : (fun x => birkhoffAverage ℝ T (g 1) (n + 1) x)
      = fun x => ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g 1) (n + 1) x := rfl
  rw [this]
  exact (integrable_birkhoffSum hT (hint 1) (n + 1)).const_mul _

/-- The Fatou defect `d n` is integrable. -/
theorem integrable_fdefect (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (fdefect (T := T) g n) μ :=
  (integrable_birkhoffAverage_one hT hint n).sub (integrable_cdiv hint n)

/-- The integral of the Fatou defect: `∫ d n = ∫ g 1 − a_{n+1}/(n+1)`. -/
theorem integral_fdefect (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    ∫ x, fdefect (T := T) g n x ∂μ
      = (∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1) := by
  have hba := integrable_birkhoffAverage_one hT hint n
  have hcdiv := integrable_cdiv hint n
  have hfeq : (∫ x, fdefect (T := T) g n x ∂μ)
      = ∫ x, (birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x) ∂μ := rfl
  rw [hfeq, integral_sub hba hcdiv, integral_birkhoffAverage_eq hT hint]
  congr 1
  have hcd : (∫ x, cdiv g n x ∂μ) = ∫ x, g (n + 1) x / ((n : ℝ) + 1) ∂μ := rfl
  rw [hcd, integral_div]

/-- **Fatou core.** A.e. the `ℝ≥0∞`-`liminf` of `ENNReal.ofReal (d n x)` is finite. From this
finiteness both `⊥ < limsup (ecdiv)` and `Integrable f₊` follow. -/
theorem ae_liminf_ofReal_fdefect_lt_top [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop ∂μ < ⊤ := by
  -- Measurable representatives for `fdefect n`, used in Fatou.
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  -- A measurable model of `ofReal (fdefect g n)`.
  set F : ℕ → X → ℝ := fun n x =>
    birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / (n + 1) with hFdef
  have hFm : ∀ n, Measurable (fun x => ENNReal.ofReal (F n x)) := by
    intro n
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.sub ?_ ((hg₀m (n + 1)).div_const _)
    change Measurable (fun x ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g₀ 1) (n + 1) x)
    exact (measurable_birkhoffSum hTm (hg₀m 1) (n + 1)).const_mul _
  -- `F n =ᵐ fdefect g n` for all `n` simultaneously.
  have hFeq : ∀ᵐ x ∂μ, ∀ n, ENNReal.ofReal (F n x) = ENNReal.ofReal (fdefect (T := T) g n x) := by
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g n x = g₀ n x := ae_all_iff.2 hgg₀
    have hbs : ∀ᵐ x ∂μ, ∀ n : ℕ,
        birkhoffSum T (g 1) (n + 1) x = birkhoffSum T (g₀ 1) (n + 1) x :=
      ae_all_iff.2 (fun n => birkhoffSum_congr_ae hT (hgg₀ 1) (n + 1))
    filter_upwards [hall, hbs] with x hx hxbs
    intro n
    congr 1
    have hba : birkhoffAverage ℝ T (g₀ 1) (n + 1) x = birkhoffAverage ℝ T (g 1) (n + 1) x := by
      simp only [birkhoffAverage, smul_eq_mul]
      rw [hxbs n]
    change birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / ((n : ℝ) + 1)
      = birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x
    rw [hba]
    simp only [cdiv]
    rw [hx (n + 1)]
  -- Fatou for the measurable model.
  have hFatou : ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ
      ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
    lintegral_liminf_le hFm
  -- The `liminf` integrand agrees a.e. with the one we want.
  have hlhs : ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ
      = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hFeq] with x hx
    exact congrArg (fun s => Filter.liminf s atTop) (funext hx)
  rw [hlhs] at hFatou
  -- Compute `∫⁻ ofReal (F n) = ofReal (∫ d n) = ofReal (∫ g 1 − a_{n+1}/(n+1))`.
  have hintF : ∀ n, ∫⁻ x, ENNReal.ofReal (F n x) ∂μ
      = ENNReal.ofReal ((∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1)) := by
    intro n
    have heq : (fun x => ENNReal.ofReal (F n x)) =ᵐ[μ]
        fun x => ENNReal.ofReal (fdefect (T := T) g n x) := by
      filter_upwards [hFeq] with x hx; exact hx n
    rw [lintegral_congr_ae heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_fdefect hT hint n)
        (Filter.Eventually.of_forall (fdefect_nonneg hsub n)),
      integral_fdefect hT hint n]
  simp only [hintF] at hFatou
  -- The `liminf` of the RHS is `ofReal (∫ g 1 − γ) < ∞`.
  obtain ⟨γ, hγ⟩ := exists_fekete hT hsub hint hbdd
  have hconv : Tendsto (fun n => ENNReal.ofReal
      ((∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1))) atTop
      (𝓝 (ENNReal.ofReal ((∫ x, g 1 x ∂μ) - γ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hγ)
  have hrhs : Filter.liminf (fun n => ENNReal.ofReal
      ((∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1))) atTop
      = ENNReal.ofReal ((∫ x, g 1 x ∂μ) - γ) := hconv.liminf_eq
  rw [hrhs] at hFatou
  exact lt_of_le_of_lt hFatou ENNReal.ofReal_lt_top

/-- A.e. measurability of the `ℝ≥0∞`-`liminf` of the Fatou defect (for `ae_lt_top'`). -/
theorem aemeasurable_liminf_ofReal_fdefect [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop)
      μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  set F : ℕ → X → ℝ := fun n x =>
    birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / (n + 1) with hFdef
  have hFm : ∀ n, Measurable (fun x => ENNReal.ofReal (F n x)) := by
    intro n
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.sub ?_ ((hg₀m (n + 1)).div_const _)
    change Measurable (fun x ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g₀ 1) (n + 1) x)
    exact (measurable_birkhoffSum hTm (hg₀m 1) (n + 1)).const_mul _
  refine ⟨fun x => Filter.liminf (fun n => ENNReal.ofReal (F n x)) atTop,
    Measurable.liminf hFm, ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g n x = g₀ n x := ae_all_iff.2 hgg₀
  have hbs : ∀ᵐ x ∂μ, ∀ n : ℕ,
      birkhoffSum T (g 1) (n + 1) x = birkhoffSum T (g₀ 1) (n + 1) x :=
    ae_all_iff.2 (fun n => birkhoffSum_congr_ae hT (hgg₀ 1) (n + 1))
  filter_upwards [hall, hbs] with x hx hxbs
  refine congrArg (fun s => Filter.liminf s atTop) (funext fun n => ?_)
  have hFval : F n x = fdefect (T := T) g n x := by
    have hba : birkhoffAverage ℝ T (g₀ 1) (n + 1) x = birkhoffAverage ℝ T (g 1) (n + 1) x := by
      simp only [birkhoffAverage, smul_eq_mul]; rw [hxbs n]
    change birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / ((n : ℕ) + 1 : ℝ)
      = birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x
    rw [hba]
    simp only [cdiv]
    rw [hx (n + 1)]
  rw [hFval]

/-- **Fatou step, pointwise.** A.e. the `ℝ≥0∞`-`liminf` of the Fatou defect is finite. -/
theorem ae_liminf_fdefect_lt_top [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop < ⊤ :=
  ae_lt_top' (aemeasurable_liminf_ofReal_fdefect hT hTm hint)
    (ae_liminf_ofReal_fdefect_lt_top hT hTm hsub hint hbdd).ne

/-- A.e. the `EReal` limsup of the normalized cocycle is bounded below by
`⊥`: the Fatou defect cannot tend to `+∞`, so the cocycle cannot tend to `−∞`. -/
theorem ae_bot_lt_ereal_limsup [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, (⊥ : EReal) < Filter.limsup (fun n => ecdiv g n x) atTop := by
  filter_upwards [ae_liminf_fdefect_lt_top hT hTm hsub hint hbdd,
    tendsto_birkhoffAverage_ae hT (hint 1)] with x hfin hBconv
  -- `liminf (ofReal d_n) < ⊤`: choose a finite ceiling `C` with `liminf < C`.
  obtain ⟨C, hC1, hC2⟩ := exists_between hfin
  -- Frequently `ofReal (d_n) < C`.
  have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal (fdefect (T := T) g n x) < C :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hC1
  -- Hence frequently `d_n < C.toReal`, i.e. `cdiv ≥ A_{n+1} − C.toReal`.
  have hBshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop
      (𝓝 ((μ[g 1 | MeasurableSpace.invariants T]) x)) :=
    hBconv.comp (tendsto_add_atTop_nat 1)
  set B : ℝ := (μ[g 1 | MeasurableSpace.invariants T]) x with hBdef
  -- Eventually `A_{n+1} x > B − 1`.
  have hev : ∀ᶠ n in atTop, B - 1 < birkhoffAverage ℝ T (g 1) (n + 1) x := by
    have := hBshift.eventually (eventually_gt_nhds (show B - 1 < B by linarith))
    exact this
  -- Frequently `cdiv g n x > B − 1 − C.toReal`.
  set K : ℝ := B - 1 - C.toReal with hKdef
  have hKfreq : ∃ᶠ n in atTop, K ≤ cdiv g n x := by
    refine (hfreq.and_eventually hev).mono ?_
    rintro n ⟨hlt, hgt⟩
    -- `ofReal (d_n) < C ⟹ d_n < C.toReal` (since `d_n ≥ 0`).
    have hdlt : fdefect (T := T) g n x < C.toReal := by
      by_contra hge
      rw [not_lt] at hge
      have : C ≤ ENNReal.ofReal (fdefect (T := T) g n x) := by
        rw [← ENNReal.ofReal_toReal hC2.ne]
        exact ENNReal.ofReal_le_ofReal hge
      exact absurd hlt (not_lt.2 this)
    -- `cdiv = A_{n+1} − d_n`.
    have hcd : cdiv g n x = birkhoffAverage ℝ T (g 1) (n + 1) x - fdefect (T := T) g n x := by
      simp only [fdefect]; ring
    rw [hcd, hKdef]; linarith
  -- Lift to `EReal`: frequently `↑K ≤ ecdiv`, so `↑K ≤ limsup (ecdiv)`, and `⊥ < ↑K`.
  have hKle : ((K : ℝ) : EReal) ≤ Filter.limsup (fun n => ecdiv g n x) atTop := by
    refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    exact hKfreq.mono fun n hn => by simpa only [ecdiv] using EReal.coe_le_coe_iff.2 hn
  exact lt_of_lt_of_le (EReal.bot_lt_coe K) hKle

/-- The `ℝ`-valued limsup envelope `f₊` is integrable, by the Fatou step.
Set `B := μ[g 1 | invariants T]` (integrable) and `Δ := B − f₊`. Then a.e. `0 ≤ Δ` (the
envelope `f₊ ≤ B`) and `Δ ≤ liminf_n (d n) =: D` (by `le_liminf_add` applied to
`A_{n+1} + (−cdiv)`, using only that `cdiv` is bounded *above*). Since `d n ≥ 0`,
`ENNReal.ofReal D = liminf_n (ENNReal.ofReal (d n))` (`Monotone.map_liminf_of_continuousAt`),
so `∫⁻ ofReal Δ ≤ ∫⁻ liminf (ofReal d_n) < ∞` (the Fatou core
`ae_liminf_ofReal_fdefect_lt_top`). Hence `Δ` is integrable and `f₊ = B − Δ` is integrable.
This is a *direct* Fatou proof, independent of `ae_tendsto_cdiv` (no circularity), and — crucially
— it never assumes `cdiv` is bounded below (which only follows after the stopping-time lemma). -/
theorem int_limsup_div_integrable_aux [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    Integrable (fun x => Filter.limsup (fun n => cdiv g n x) atTop) μ := by
  set B : X → ℝ := fun x => (μ[g 1 | MeasurableSpace.invariants T]) x with hBdef
  have hBint : Integrable B μ := integrable_condExp
  set fp : X → ℝ := fun x => Filter.limsup (fun n => cdiv g n x) atTop with hfpdef
  -- `Δ x := B x − f₊ x`. It suffices to show `Δ` is integrable, since `f₊ = B − Δ`.
  set Δ : X → ℝ := fun x => B x - fp x with hΔdef
  suffices hΔ : Integrable Δ μ by
    have : (fun x => fp x) = fun x => B x - Δ x := by funext x; simp only [hΔdef]; ring
    rw [hfpdef] at this ⊢
    rw [this]; exact hBint.sub hΔ
  -- `Δ` is AEMeasurable.
  have hfpm : AEMeasurable fp μ := aemeasurable_limsup_div (μ := μ) hint
  have hΔm : AEMeasurable Δ μ := hBint.aestronglyMeasurable.aemeasurable.sub hfpm
  -- Pointwise on a good set: `0 ≤ Δ x ≤ liminf (defect)` and `ofReal (Δ x) ≤ liminf (ofReal d)`.
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (Δ x)
      ≤ Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop := by
    filter_upwards [tendsto_birkhoffAverage_ae hT (hint 1),
      ae_bddAbove_cdiv hT hsub hint,
      ae_liminf_fdefect_lt_top hT hTm hsub hint hbdd] with x hBconv hba hfdlt
    have hBshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop (𝓝 (B x)) :=
      hBconv.comp (tendsto_add_atTop_nat 1)
    -- boundedness of `cdiv` (above, from `hba`) and of `A_{n+1}` (converges).
    have hbA : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) :=
      hba.isBoundedUnder_of_range
    -- bounded below of `fdefect` (it is `≥ 0`).
    have hbdef : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => fdefect (T := T) g n x) := by
      refine ⟨0, ?_⟩
      simp only [eventually_map]
      exact Eventually.of_forall fun n => fdefect_nonneg hsub n x
    -- cobounded `(· ≥ ·)`: from `liminf (ofReal d) < ⊤`, frequently `d n ≤ C.toReal`.
    have hcobdef : Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n => fdefect (T := T) g n x) := by
      obtain ⟨C, hC1, hC2⟩ := exists_between hfdlt
      refine IsCoboundedUnder.of_frequently_le (a := C.toReal) ?_
      have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal (fdefect (T := T) g n x) < C :=
        frequently_lt_of_liminf_lt (by isBoundedDefault) hC1
      refine hfreq.mono fun n hn => ?_
      by_contra hge
      rw [not_le] at hge
      exact absurd hn (not_lt.2 (le_trans (by
        rw [← ENNReal.ofReal_toReal hC2.ne]
        exact ENNReal.ofReal_le_ofReal hge.le) (le_refl _)))
    -- `D := liminf fdefect`; `B − f₊ ≤ D` via the eventual bound `fdefect ≥ B − f₊ − 2δ`.
    set D : ℝ := Filter.liminf (fun n => fdefect (T := T) g n x) atTop with hDdef
    have hkey : B x - fp x ≤ D := by
      have hstep : ∀ δ : ℝ, 0 < δ → B x - fp x - 2 * δ ≤ D := by
        intro δ hδ
        refine le_liminf_of_le hcobdef ?_
        -- Eventually `A_{n+1} > B x − δ` and `cdiv n < f₊ x + δ`.
        have hev1 : ∀ᶠ n in atTop, B x - δ < birkhoffAverage ℝ T (g 1) (n + 1) x :=
          hBshift.eventually (eventually_gt_nhds (by linarith))
        have hev2 : ∀ᶠ n in atTop, cdiv g n x < fp x + δ :=
          eventually_lt_of_limsup_lt (show Filter.limsup (fun n => cdiv g n x) atTop < fp x + δ
            from by have : Filter.limsup (fun n => cdiv g n x) atTop = fp x := rfl; linarith) hbA
        filter_upwards [hev1, hev2] with n h1 h2
        have : fdefect (T := T) g n x = birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x := rfl
        rw [this]; linarith
      by_contra hlt
      rw [not_le] at hlt
      have := hstep ((B x - fp x - D) / 4) (by linarith)
      linarith
    have hmap : ENNReal.ofReal D
        = Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop := by
      have := ENNReal.ofReal_mono.map_liminf_of_continuousAt
        (a := fun n => fdefect (T := T) g n x)
        (ENNReal.continuous_ofReal.continuousAt) hcobdef hbdef
      simpa only [hDdef, Function.comp] using this
    calc ENNReal.ofReal (Δ x) = ENNReal.ofReal (B x - fp x) := rfl
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal hkey
      _ = _ := hmap
  -- `Δ ≥ 0` a.e. (envelope `f₊ ≤ B`).
  have hΔnn : 0 ≤ᵐ[μ] Δ := by
    filter_upwards [tendsto_birkhoffAverage_ae hT (hint 1),
      ae_bot_lt_ereal_limsup hT hTm hsub hint hbdd] with x hBconv hbot
    have hBshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop (𝓝 (B x)) :=
      hBconv.comp (tendsto_add_atTop_nat 1)
    -- cobounded `(· ≤ ·)` of `cdiv` from `⊥ < limsup (ecdiv)` (frequently `cdiv ≥ K`).
    have hcob : Filter.IsCoboundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) := by
      obtain ⟨K, _, hK2⟩ := EReal.lt_iff_exists_real_btwn.1 hbot
      refine IsCoboundedUnder.of_frequently_ge (a := K) ?_
      have hfreq : ∃ᶠ n in atTop, (K : EReal) < ecdiv g n x :=
        frequently_lt_of_lt_limsup (by isBoundedDefault) hK2
      refine hfreq.mono fun n hn => ?_
      simpa only [ecdiv] using (EReal.coe_lt_coe_iff.1 hn).le
    have hle : fp x ≤ B x := by
      have hstep : ∀ δ : ℝ, 0 < δ → fp x ≤ B x + δ := by
        intro δ hδ
        refine limsup_le_of_le hcob ?_
        have hAle : ∀ᶠ n in atTop, birkhoffAverage ℝ T (g 1) (n + 1) x < B x + δ :=
          hBshift.eventually (eventually_lt_nhds (by linarith))
        filter_upwards [hAle] with n hn
        exact le_of_lt (lt_of_le_of_lt (cdiv_le_birkhoffAverage hsub n x) hn)
      by_contra hlt
      rw [not_le] at hlt
      have := hstep ((fp x - B x) / 2) (by linarith)
      linarith
    change (0 : ℝ) ≤ Δ x
    simp only [hΔdef]
    linarith
  -- Finite lintegral: `∫⁻ ofReal Δ ≤ ∫⁻ liminf (ofReal d) < ∞`.
  have hfin : ∫⁻ x, ENNReal.ofReal (Δ x) ∂μ < ⊤ := by
    calc ∫⁻ x, ENNReal.ofReal (Δ x) ∂μ
        ≤ ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop ∂μ :=
          lintegral_mono_ae hpt
      _ < ⊤ := ae_liminf_ofReal_fdefect_lt_top hT hTm hsub hint hbdd
  -- Conclude `Integrable Δ`.
  rw [Integrable, hasFiniteIntegral_iff_ofReal hΔnn]
  exact ⟨hΔm.aestronglyMeasurable, hfin⟩


end ErgodicTheory.Kingman
