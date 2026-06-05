import Oseledets.Ergodic.Birkhoff
import Mathlib.Analysis.Subadditive
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Kingman's subadditive ergodic theorem

Kingman's theorem (layer `L2` / milestone `M4`) is the analytic engine of the
multiplicative ergodic theorem. Mathlib has only the *deterministic* Fekete lemma
(`Subadditive.tendsto_lim`); the measure-theoretic a.e.-convergence statement for a
**subadditive cocycle** over a measure-preserving system is absent.

We record the subadditive-cocycle predicate and the theorem. The statement here is in
`ℝ` under the boundedness proviso `BddBelow {(∫ gₙ)/n}` (which keeps the limit finite —
exactly the case used by Furstenberg–Kesten under the `log⁺‖A⁻¹‖ ∈ L¹` hypothesis); the
fully general `EReal`-valued version (limit possibly `−∞`) is a planned refinement.

## Strategy (pointwise Katznelson–Weiss / Steele)

The a.e. convergence is closed by a *pointwise* sandwich, exactly mirroring the existing
`M3` Birkhoff proof. Write `c n x := g (n+1) x / (n+1)`, `f₊ x := limsup_n (c n x)`,
`f₋ x := liminf_n (c n x)`. The target limit is `G := f₋`. The convergence
`Tendsto (c · x) atTop (𝓝 (f₋ x))` follows pointwise from
`tendsto_of_le_liminf_of_limsup_le` once we know, a.e.,

* (S1) `f₊ x ≤ f₋ x`  [hard, `ae_limsup_le_liminf_div` / `L9`]; and
* (S2) `f₋ x ≤ f₊ x`  [trivial, `liminf_le_limsup`].

No integral of `f₊`/`f₋` enters the convergence proof. The integral facts are needed only
to certify `Integrable G`, via a single Fatou step (`int_limsup_div_integrable` / `L8`).

All of this — the pointwise squeeze, the boundedness facts, the envelope integrability, and
the `T`-invariance — is derived (soft arguments) from the core lemma `ae_tendsto_cdiv`
(*for `μ`-a.e. `x`, `c n x` converges to the value `G x` of some integrable `G`*). The Fatou
integrability step and the finiteness/envelope facts are now proved; `ae_tendsto_cdiv` is
sorry-free, depending only on a **single remaining `sorry`** — the stopping-time / greedy block
partition `ae_ereal_limsup_le_liminf` (`limsup ≤ liminf` a.e.), the irreducible hard core of
`M4`; see `docs/plan/blueprints/m4-kingman-v2.md` §4 and `docs/research/scratch/m4-L9-notes.md`.

## Finiteness hypothesis

`tendsto_kingman` carries `[IsFiniteMeasure μ]`. As with `M3` Birkhoff, the maximal-
inequality machinery needs a finite measure; the Oseledets MET only ever calls Kingman
for probability measures, where this is automatic.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- A sequence `g : ℕ → X → ℝ` is a **subadditive cocycle** over `T` when
`g (m + n) x ≤ g m x + g n (T^[m] x)` for all `m, n, x`. (For `gₙ = log‖A⁽ⁿ⁾‖` this
follows from submultiplicativity of the operator norm and the cocycle identity.) -/
structure IsSubadditiveCocycle (T : X → X) (g : ℕ → X → ℝ) : Prop where
  apply_add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)

/-! ### L0: reindexing the normalized sequence -/

omit [MeasurableSpace X] in
/-- **L0 — reindex.** The Kingman sequence `(n : ℝ)⁻¹ * g n x` converges to `L` iff the
shifted sequence `g (n+1) x / (n+1)` converges to `L`. The `n = 0` term of the original
sequence is `0⁻¹ * g 0 x = 0`, so dropping it is harmless. -/
private theorem tendsto_kingman_reindex {g : ℕ → X → ℝ} {x : X} {L : ℝ} :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 L) ↔
      Tendsto (fun n : ℕ => g (n + 1) x / (n + 1)) atTop (𝓝 L) := by
  rw [← tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ)⁻¹ * g n x) 1]
  refine tendsto_congr (fun n => ?_)
  push_cast
  rw [div_eq_inv_mul]

/-! ### L1 / A1': singleton (Birkhoff-sum) subadditivity -/

omit [MeasurableSpace X] in
/-- **A1' — singleton partition subadditivity.** For `n ≥ 1`, a subadditive cocycle is
dominated by the Birkhoff sum of its first level: `g (n+1) x ≤ birkhoffSum T (g 1) (n+1) x`.
(The statement fails at `n = 0`: subadditivity only forces `0 ≤ g 0 x`, not `g 0 x ≤ 0`.) -/
private theorem IsSubadditiveCocycle.le_birkhoffSum_one {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    g (n + 1) x ≤ birkhoffSum T (g 1) (n + 1) x := by
  induction n with
  | zero => simp only [Nat.zero_add, birkhoffSum_one]; exact le_refl _
  | succ n ih =>
      rw [birkhoffSum_succ]
      calc g (n + 1 + 1) x ≤ g (n + 1) x + g 1 (T^[n + 1] x) := hsub.apply_add_le (n + 1) 1 x
        _ ≤ birkhoffSum T (g 1) (n + 1) x + g 1 (T^[n + 1] x) := by linarith [ih]

/-! ### L2 / A2: integral of a measure-preserving composition -/

/-- **L2.** The integral of a measure-preserving composition equals the integral:
`∫ g n (T^[m] x) ∂μ = ∫ g n x ∂μ`. -/
private theorem integral_comp_iterate (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (m n : ℕ) :
    ∫ x, g n (T^[m] x) ∂μ = ∫ x, g n x ∂μ := by
  have hmp : MeasurePreserving (T^[m]) μ μ := hT.iterate m
  have haesm : AEStronglyMeasurable (g n) (Measure.map (T^[m]) μ) := by
    rw [hmp.map_eq]; exact (hint n).aestronglyMeasurable
  have hmap := integral_map (μ := μ) (φ := T^[m]) hmp.aemeasurable (f := g n) haesm
  rw [hmp.map_eq] at hmap
  exact hmap.symm

/-- **A2 — integral subadditivity.** The integral sequence `aₙ = ∫ gₙ` is subadditive
in Mathlib's sense (`a (m+n) ≤ a m + a n`), the Fekete input. -/
private theorem integral_subadditive (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
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

/-! ### L4 / Fekete: the limit `γ` of the normalized integrals -/

/-- **L4 — Fekete.** The normalized integral sequence `(∫ g (n+1)) / (n+1)` converges to
the Fekete constant `γ := (integral_subadditive …).lim`. The `n+1`-indexed bounded-below
hypothesis is bridged to the `n`-indexed Fekete input by hand (the `n = 0` term is
`(∫ g 0)/0 = 0`). -/
private theorem exists_fekete (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
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

/-! ### L5 / A3: a.e. `T`-invariance from monotonicity under `T` -/

/-- **L5 / A3 — invariance from `F ≤ F ∘ T`.** If `F` is a.e. measurable, `T` is
measure-preserving on a finite measure, and `F x ≤ F (T x)` for a.e. `x`, then
`F ∘ T =ᵐ[μ] F`. The upper level sets `{c ≤ F}` satisfy `{c ≤ F} ⊆ᵐ T⁻¹ {c ≤ F}` with
equal (finite) measure, hence agree a.e.; ranging over rational `c` gives invariance. -/
private theorem ae_eq_comp_of_le_comp [IsFiniteMeasure μ]
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
  show F (T x) = F x
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
private noncomputable def cdiv (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ := g (n + 1) x / (n + 1)

omit [MeasurableSpace X] in
/-- `cdiv g n x` is dominated by the Birkhoff average of `g 1`: an immediate rephrasing of
A1' (`le_birkhoffSum_one`). -/
private theorem cdiv_le_birkhoffAverage {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (n : ℕ) (x : X) : cdiv g n x ≤ birkhoffAverage ℝ T (g 1) (n + 1) x := by
  have h := hsub.le_birkhoffSum_one n x
  rw [cdiv, birkhoffAverage, smul_eq_mul]
  rw [div_eq_inv_mul]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  apply mul_le_mul_of_nonneg_left h (le_of_lt (by positivity))

/-! ### L6: a.e. measurability of the limsup/liminf envelopes -/

/-- **L6 (limsup).** The pointwise `limsup` of `cdiv g · x` is a.e. measurable: it agrees a.e.
with the limsup of measurable representatives of each level `g (n+1)`. -/
private theorem aemeasurable_limsup_div {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
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

/-- **L6 (liminf).** The pointwise `liminf` of `cdiv g · x` is a.e. measurable. -/
private theorem aemeasurable_liminf_div {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
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

A.e., the range of `cdiv g · x` is bounded above (immediate from A1' and a.e. boundedness of
the Birkhoff averages of `g 1`). The bounded-below direction is the subtle one: subadditivity
gives only upper bounds, so a.e. finiteness of the liminf holds only once a.e. convergence is
known. Accordingly it is derived from the core lemma `ae_tendsto_cdiv` (a convergent sequence
is bounded), defined below. -/

/-- A.e. the range of `cdiv g · x` is bounded above (A1' + `ae_bddAbove_birkhoffAverage`). -/
private theorem ae_bddAbove_cdiv [IsFiniteMeasure μ]
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
unconditional. The two facts produced here — `limsup < ⊤` (envelope, from A1' + `M3`) and
`limsup > ⊥` (Fatou) — together with the hard `limsup ≤ liminf` (`ae_ereal_limsup_le_liminf`)
pin the `EReal` `limsup`/`liminf` to a common finite value, from which the `ℝ` convergence
follows. -/

/-- The `EReal`-coerced normalized cocycle. -/
private noncomputable def ecdiv (g : ℕ → X → ℝ) (n : ℕ) (x : X) : EReal := (cdiv g n x : EReal)

/-- **Envelope.** A.e. the `EReal` `limsup` of the normalized cocycle is bounded above by the
(finite) conditional expectation `μ[g 1 | invariants T]`, hence is `< ⊤`. From A1'
(`cdiv ≤ birkhoffAverage g₁ (n+1)`) and `M3` (`birkhoffAverage g₁ (n+1) → μ[g₁|I]`). -/
private theorem ae_ereal_limsup_le_condExp [IsFiniteMeasure μ]
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

/-! ### STEP 2: the Fatou step — finiteness of the limsup and integrability of `f₊`

The normalized cocycle satisfies `cdiv g n x ≤ birkhoffAverage ℝ T (g 1) (n+1) x` (A1'), so the
nonnegative defect `d n x := birkhoffAverage ℝ T (g 1) (n+1) x − cdiv g n x ≥ 0` controls how
far `cdiv` can drop. A single `ℝ≥0∞` Fatou pass (`lintegral_liminf_le`) on `ENNReal.ofReal (d n)`
shows `liminf_n (d n x) < ∞` a.e., which (since the Birkhoff average converges) is exactly
`limsup_n (cdiv g n x) > −∞` a.e. (i.e. `⊥ < EReal limsup`), and also yields that the limsup
envelope `f₊` is integrable. -/

/-- The nonnegative Fatou defect `birkhoffAverage ℝ T (g 1) (n+1) x − cdiv g n x ≥ 0`. -/
private noncomputable def fdefect (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ :=
  birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x

omit [MeasurableSpace X] in
/-- The Fatou defect is nonnegative, by A1' (`cdiv_le_birkhoffAverage`). -/
private theorem fdefect_nonneg {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    0 ≤ fdefect (T := T) g n x :=
  sub_nonneg.2 (cdiv_le_birkhoffAverage hsub n x)

/-- The integral of `birkhoffAverage ℝ T (g 1) (n+1)` is `∫ g 1`: the Birkhoff average is an
average of measure-preserving compositions of `g 1`, each with integral `∫ g 1`. -/
private theorem integral_birkhoffAverage_eq (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
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
private theorem integrable_cdiv {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (cdiv g n) μ := by
  have : cdiv g n = fun x => g (n + 1) x / ((n : ℝ) + 1) := rfl
  rw [this]
  exact (hint (n + 1)).div_const _

/-- `birkhoffAverage ℝ T (g 1) (n+1)` is integrable. -/
private theorem integrable_birkhoffAverage_one (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (fun x => birkhoffAverage ℝ T (g 1) (n + 1) x) μ := by
  have : (fun x => birkhoffAverage ℝ T (g 1) (n + 1) x)
      = fun x => ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g 1) (n + 1) x := rfl
  rw [this]
  exact (integrable_birkhoffSum hT (hint 1) (n + 1)).const_mul _

/-- The Fatou defect `d n` is integrable. -/
private theorem integrable_fdefect (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (fdefect (T := T) g n) μ :=
  (integrable_birkhoffAverage_one hT hint n).sub (integrable_cdiv hint n)

/-- The integral of the Fatou defect: `∫ d n = ∫ g 1 − a_{n+1}/(n+1)`. -/
private theorem integral_fdefect (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
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
private theorem ae_liminf_ofReal_fdefect_lt_top [IsFiniteMeasure μ]
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
    show Measurable (fun x => ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g₀ 1) (n + 1) x)
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
    show birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / ((n : ℝ) + 1)
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
private theorem aemeasurable_liminf_ofReal_fdefect [IsFiniteMeasure μ]
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
    show Measurable (fun x => ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g₀ 1) (n + 1) x)
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
    show birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / ((n : ℕ) + 1 : ℝ)
      = birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x
    rw [hba]
    simp only [cdiv]
    rw [hx (n + 1)]
  rw [hFval]

/-- **STEP 2 pointwise.** A.e. the `ℝ≥0∞`-`liminf` of the Fatou defect is finite. -/
private theorem ae_liminf_fdefect_lt_top [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop < ⊤ :=
  ae_lt_top' (aemeasurable_liminf_ofReal_fdefect hT hTm hint)
    (ae_liminf_ofReal_fdefect_lt_top hT hTm hsub hint hbdd).ne

/-- **STEP 2 (A1).** A.e. the `EReal` limsup of the normalized cocycle is bounded below by
`⊥`: the Fatou defect cannot tend to `+∞`, so the cocycle cannot tend to `−∞`. -/
private theorem ae_bot_lt_ereal_limsup [IsFiniteMeasure μ]
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

/-- **STEP 2 (A2).** The `ℝ`-valued limsup envelope `f₊` is integrable, by the Fatou step.
Set `B := μ[g 1 | invariants T]` (integrable) and `Δ := B − f₊`. Then a.e. `0 ≤ Δ` (the
envelope `f₊ ≤ B`) and `Δ ≤ liminf_n (d n) =: D` (by `le_liminf_add` applied to
`A_{n+1} + (−cdiv)`, using only that `cdiv` is bounded *above*). Since `d n ≥ 0`,
`ENNReal.ofReal D = liminf_n (ENNReal.ofReal (d n))` (`Monotone.map_liminf_of_continuousAt`),
so `∫⁻ ofReal Δ ≤ ∫⁻ liminf (ofReal d_n) < ∞` (the Fatou core
`ae_liminf_ofReal_fdefect_lt_top`). Hence `Δ` is integrable and `f₊ = B − Δ` is integrable.
This is a *direct* Fatou proof, independent of `ae_tendsto_cdiv` (no circularity), and — crucially
— it never assumes `cdiv` is bounded below (which only follows after the stopping-time lemma). -/
private theorem int_limsup_div_integrable_aux [IsFiniteMeasure μ]
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
    show (0 : ℝ) ≤ Δ x
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

/-! ### STEP 3: the Derriennic "leaders" route to `limsup ≤ liminf` a.e.

We follow Karlsson, *A proof of the subadditive ergodic theorem* (Riesz/Derriennic route).
The four ingredients are:

* **L-A** (`sum_leaders_nonpos`): Riesz's combinatorial "leader" lemma (Karlsson Lemma 3.2),
  pure finite induction, no measure theory.
* **L-B** (`telescope_sub`): the telescoping identity `a n x − a (n−k) (T^[k] x) = ∑ bₙ₋ᵢ(T^[i]x)`.
* **L-C** (`limsup_setIntegral_div_le`): Derriennic's maximal inequality (Karlsson Lemma 3.4 /
  Prop 3.5): for a `T`-invariant set `B` on which `liminf (aₙ/n) < α`, one has
  `limsup (1/n) ∫_B aₙ ≤ α·μ(B)`.
* **L-D**: the `E_{α,β}` two-bound contradiction (Karlsson §3.3), mirroring the additive
  `measure_setOf_lt_limsup_eq_zero` in `Birkhoff.lean`. -/

open Classical in
/-- The set of leaders of length `n` for partial sums `S`. -/
private noncomputable def leaderSet (S : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun u => ∃ j, u < j ∧ j ≤ n ∧ S j < S u)

/-- A leader `u ≥ s` of length `n` (with `s ≤ n`) is, after shifting indices down by `s`, a
leader of the shifted partial sums `S (· + s)` of length `n − s`, and conversely. (The leader
condition only inspects partial sums strictly after `u`, so dropping the prefix `[0, s)` is
harmless.) This is the reindexing engine of the leader-lemma induction. -/
private theorem mem_leaderSet_shift (S : ℕ → ℝ) (s n u : ℕ) (hsn : s ≤ n) :
    (u + s ∈ leaderSet S n ∧ s ≤ u + s) ↔ u ∈ leaderSet (fun j => S (j + s)) (n - s) := by
  classical
  simp only [leaderSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, j, hj1, hj2, hj3⟩, _⟩
    refine ⟨by omega, j - s, by omega, by omega, ?_⟩
    rwa [Nat.sub_add_cancel (by omega)]
  · rintro ⟨hu, j, hj1, hj2, hj3⟩
    refine ⟨⟨by omega, j + s, by omega, by omega, hj3⟩, by omega⟩

/-- **L-A — Riesz's leader lemma** (Karlsson, Lemma 3.2), in partial-sum form. Given a
sequence of partial sums `S : ℕ → ℝ` (think `S j = c 0 + … + c (j−1)`, `S 0 = 0`), call an
index `u < n` a *leader* (of length `n`) if some later partial sum drops strictly below `S u`,
i.e. `∃ j, u < j ≤ n ∧ S j < S u`. (This matches Karlsson's "a forward partial sum
`c u + … + c (j−1) = S j − S u` is negative".) Then the sum of the increments `S (u+1) − S u`
over the leaders is non-positive. Strong induction on `n`. -/
private theorem sum_leaders_nonpos :
    ∀ (n : ℕ) (S : ℕ → ℝ), ∑ u ∈ leaderSet S n, (S (u + 1) - S u) ≤ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S
    match n with
    | 0 => simp [leaderSet]
    | (n + 1) =>
      classical
      by_cases h0 : (0 : ℕ) ∈ leaderSet S (n + 1)
      · -- `0` is a leader: take the least partial-sum index `k` with `S k < S 0`.
        simp only [leaderSet, Finset.mem_filter, Finset.mem_range] at h0
        obtain ⟨_, j0, hj01, hj02, hj03⟩ := h0
        set P : ℕ → Prop := fun j => j ≤ n + 1 ∧ S j < S 0 with hP
        have hPex : ∃ j, P j := ⟨j0, hj02, hj03⟩
        set k : ℕ := Nat.find hPex with hk
        have hkP : P k := Nat.find_spec hPex
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · exfalso; rw [h] at hkP; exact lt_irrefl _ hkP.2
          · exact h
        have hkle : k ≤ n + 1 := hkP.1
        have hkmin : ∀ m, m < k → ¬ P m := fun m hm => Nat.find_min hPex hm
        -- For each `i < k`, `S k < S i`: `S i ≥ S 0` (minimality) and `S k < S 0`.
        have hbeat : ∀ i, i < k → S k < S i := by
          intro i hik
          rcases Nat.eq_zero_or_pos i with hi0 | _
          · subst hi0; exact hkP.2
          · have hSi : S 0 ≤ S i := by
              by_contra hlt; rw [not_le] at hlt; exact hkmin i hik ⟨by omega, hlt⟩
            linarith [hkP.2]
        -- Split the leader set as the prefix `range k` together with the leaders `≥ k`.
        have hprefix : ∀ i, i < k → i ∈ leaderSet S (n + 1) := by
          intro i hik
          simp only [leaderSet, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, k, hik, hkle, hbeat i hik⟩
        -- Split the leader sum into the prefix `{u < k}` and the tail `{¬ u < k}`.
        rw [← Finset.sum_filter_add_sum_filter_not (leaderSet S (n + 1)) (fun u => u < k)
          (fun u => S (u + 1) - S u)]
        -- The prefix filter is exactly `range k`; its increment sum telescopes to `S k - S 0 < 0`.
        have hpref_eq : (leaderSet S (n + 1)).filter (fun u => u < k) = Finset.range k := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
          intro hu; exact hprefix u hu
        rw [hpref_eq, Finset.sum_range_sub S k]
        -- The tail filter reindexes to the leaders of the shifted partial sums of length `n+1-k`.
        have htail : ∑ u ∈ (leaderSet S (n + 1)).filter (fun u => ¬ u < k), (S (u + 1) - S u)
            ≤ 0 := by
          set S' : ℕ → ℝ := fun j => S (j + k) with hS'
          have hmap : (leaderSet S (n + 1)).filter (fun u => ¬ u < k)
              = (leaderSet S' (n + 1 - k)).map ⟨fun u => u + k, fun a b h => Nat.add_right_cancel h⟩ := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk, not_lt]
            constructor
            · rintro ⟨hmem, hku⟩
              refine ⟨u - k, ?_, by omega⟩
              have := (mem_leaderSet_shift S k (n + 1) (u - k) hkle).1
              rw [Nat.sub_add_cancel hku] at this
              exact (this ⟨hmem, by omega⟩)
            · rintro ⟨v, hv, rfl⟩
              refine ⟨?_, by omega⟩
              exact ((mem_leaderSet_shift S k (n + 1) v hkle).2 hv).1
          rw [hmap, Finset.sum_map]
          simp only [Function.Embedding.coeFn_mk]
          have hval : ∀ v, S (v + k + 1) - S (v + k) = S' (v + 1) - S' v := by
            intro v; simp only [hS']; ring_nf
          simp_rw [hval]
          exact ih (n + 1 - k) (by omega) S'
        have := hkP.2; linarith [htail]
      · -- `0` is not a leader: every leader lies in `{1,…,n}`; shift down by 1 and apply IH.
        set S' : ℕ → ℝ := fun j => S (j + 1) with hS'
        have hmap : leaderSet S (n + 1)
            = (leaderSet S' n).map ⟨fun u => u + 1, fun a b h => Nat.add_right_cancel h⟩ := by
          ext u
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
          constructor
          · intro hmem
            have hu0 : u ≠ 0 := by rintro rfl; exact h0 hmem
            refine ⟨u - 1, ?_, by omega⟩
            have := (mem_leaderSet_shift S 1 (n + 1) (u - 1) (by omega)).1
            rw [Nat.sub_add_cancel (by omega)] at this
            exact this ⟨hmem, by omega⟩
          · rintro ⟨v, hv, rfl⟩
            exact ((mem_leaderSet_shift S 1 (n + 1) v (by omega)).2 hv).1
        rw [hmap, Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk]
        have hval : ∀ v, S (v + 1 + 1) - S (v + 1) = S' (v + 1) - S' v := fun v => rfl
        simp_rw [hval]
        exact ih n (by omega) S'

omit [MeasurableSpace X] in
/-- **L-B — leader inequality for the cocycle** (Karlsson, §3.2, the pointwise input of his
Lemma 3.4). Fix `x` and length `n`, and consider the partial sums
`S j := g n x − g (n−j) (T^[j] x)` (so `S 0 = 0`, and the increment `S (k+1) − S k` equals
`g (n−k) (T^[k] x) − g (n−k−1) (T^[k+1] x)`). With these partial sums an index `k` is a
*leader* exactly when `T^[k] x` lies in Karlsson's set `Λ_{n−k}`. The leader lemma `L-A`
(`sum_leaders_nonpos`) then bounds the sum of the increments over the leaders by `0`. This is
the purely pointwise/combinatorial heart of Derriennic's maximal inequality (the measure
theory enters only when one integrates this inequality over a `T`-invariant set). -/
private theorem sum_leaders_cocycle_nonpos (g : ℕ → X → ℝ) (n : ℕ) (x : X) :
    ∑ k ∈ leaderSet (fun j => g n x - g (n - j) (T^[j] x)) n,
        (g (n - k) (T^[k] x) - g (n - (k + 1)) (T^[k + 1] x)) ≤ 0 := by
  have h := sum_leaders_nonpos n (fun j => g n x - g (n - j) (T^[j] x))
  refine le_of_eq_of_le (Finset.sum_congr rfl (fun k _ => ?_)) h
  ring

/-! ### L-C: Derriennic's maximal inequality (Karlsson Lemma 3.4 / Prop 3.5)

Karlsson's Λ-set and A-set, and the integral telescoping of `sum_leaders_cocycle_nonpos`
(L-B) over a `T`-invariant set `B`. -/

/-- The increment of the cocycle: `bcoc g i x = g i x − g (i−1) (T x)`. (Karlsson's `b_i`.) -/
private def bcoc (g : ℕ → X → ℝ) (i : ℕ) (x : X) : ℝ := g i x - g (i - 1) (T x)

/-- Karlsson's set `Λ_m = {y | inf_{1≤k≤m} (g m y − g (m−k)(T^[k] y)) < 0}`. -/
private def LambdaSet (g : ℕ → X → ℝ) (m : ℕ) : Set X :=
  {y | ∃ k, 1 ≤ k ∧ k ≤ m ∧ g m y - g (m - k) (T^[k] y) < 0}

/-- Karlsson's set `A_m = {y | inf_{1≤k≤m} g k y < 0} ⊆ Λ_m`. -/
private def ASet (g : ℕ → X → ℝ) (m : ℕ) : Set X :=
  {y | ∃ k, 1 ≤ k ∧ k ≤ m ∧ g k y < 0}

omit [MeasurableSpace X] in
/-- `A_m ⊆ Λ_m` by subadditivity: `g m y ≤ g (m−k) y + g k (T^[m−k] y)`… actually the
inclusion uses `g m y ≤ g (m−k) (·)`; we prove it via `g m y − g (m−k)(T^[k] y) ≤ g k y` when
`k ≤ m`. Indeed `g m y = g (k + (m−k)) y ≤ g k y + g (m−k) (T^[k] y)`. -/
private theorem ASet_subset_LambdaSet {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (m : ℕ) :
    ASet g m ⊆ LambdaSet (T := T) g m := by
  rintro y ⟨k, hk1, hkm, hk⟩
  refine ⟨k, hk1, hkm, ?_⟩
  have hdecomp : g m y ≤ g k y + g (m - k) (T^[k] y) := by
    have := hsub.apply_add_le k (m - k) y
    rwa [Nat.add_sub_cancel' hkm] at this
  linarith

omit [MeasurableSpace X] in
/-- The leader-membership identification (Karlsson, §3.2): an index `k` is a leader of the
partial sums `S j = g n x − g (n−j)(T^[j] x)` of length `n` exactly when `k < n` and
`T^[k] x ∈ Λ_{n−k}`. -/
private theorem mem_leaderSet_iff_mem_LambdaSet (g : ℕ → X → ℝ) (n k : ℕ) (x : X) :
    k ∈ leaderSet (fun j => g n x - g (n - j) (T^[j] x)) n ↔
      k < n ∧ T^[k] x ∈ LambdaSet (T := T) g (n - k) := by
  classical
  simp only [leaderSet, Finset.mem_filter, Finset.mem_range, LambdaSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hkn, j, hkj, hjn, hlt⟩
    refine ⟨hkn, j - k, by omega, by omega, ?_⟩
    have h1 : T^[j - k] (T^[k] x) = T^[j] x := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    have h2 : n - k - (j - k) = n - j := by omega
    rw [h1, h2]
    linarith
  · rintro ⟨hkn, m, hm1, hmnk, hlt⟩
    refine ⟨hkn, k + m, by omega, by omega, ?_⟩
    have h1 : T^[m] (T^[k] x) = T^[k + m] x := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    have h2 : n - k - m = n - (k + m) := by omega
    rw [h1, h2] at hlt
    linarith

omit [MeasurableSpace X] in
/-- **Telescoping** (Karlsson §3.2): `∑_{k<n} bcoc g (n−k) (T^[k] x) = g n x − g 0 (T^[n] x)`. -/
private theorem sum_bcoc_telescope (g : ℕ → X → ℝ) (n : ℕ) (x : X) :
    ∑ k ∈ Finset.range n, bcoc (T := T) g (n - k) (T^[k] x)
      = g n x - g 0 (T^[n] x) := by
  set h : ℕ → ℝ := fun k => g (n - k) (T^[k] x) with hh
  have hterm : ∀ k ∈ Finset.range n, bcoc (T := T) g (n - k) (T^[k] x) = h k - h (k + 1) := by
    intro k _
    simp only [hh, bcoc]
    rw [Function.iterate_succ_apply', show n - k - 1 = n - (k + 1) by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' h n]
  simp only [hh, Nat.sub_zero, Function.iterate_zero, id_eq, Nat.sub_self]

open Classical in
omit [MeasurableSpace X] in
/-- **L-B′ — pointwise leader inequality, Λ-form.** Summing the increments `bcoc g (n−k)`
along the orbit over the indices `k < n` with `T^[k] x ∈ Λ_{n−k}` gives a non-positive number.
(Recast of `sum_leaders_cocycle_nonpos` via the membership identification.) -/
private theorem sum_bcoc_lambda_nonpos (g : ℕ → X → ℝ) (n : ℕ) (x : X) :
    ∑ k ∈ (Finset.range n).filter (fun k => T^[k] x ∈ LambdaSet (T := T) g (n - k)),
        bcoc (T := T) g (n - k) (T^[k] x) ≤ 0 := by
  classical
  have hset : (Finset.range n).filter (fun k => T^[k] x ∈ LambdaSet (T := T) g (n - k))
      = leaderSet (fun j => g n x - g (n - j) (T^[j] x)) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, mem_leaderSet_iff_mem_LambdaSet]
  rw [hset]
  refine le_of_eq_of_le (Finset.sum_congr rfl (fun k _ => ?_)) (sum_leaders_cocycle_nonpos g n x)
  simp only [bcoc]
  rw [Function.iterate_succ_apply', show n - k - 1 = n - (k + 1) by omega]

/-- Karlsson's localized increment `ψ_i = 1_{Λ_i} · bcoc g i`. -/
private noncomputable def psiCoc (g : ℕ → X → ℝ) (i : ℕ) : X → ℝ :=
  (LambdaSet (T := T) g i).indicator (bcoc (T := T) g i)

open Classical in
omit [MeasurableSpace X] in
/-- **L-B″ — indicator form of the pointwise leader inequality.** The full-range orbit sum of
the localized increments `ψ_{n−k} ∘ T^[k]` is non-positive (it equals the filtered leader sum
of `sum_bcoc_lambda_nonpos`, the extra terms being zero off `Λ`). -/
private theorem sum_psiCoc_comp_nonpos (g : ℕ → X → ℝ) (n : ℕ) (x : X) :
    ∑ k ∈ Finset.range n, psiCoc (T := T) g (n - k) (T^[k] x) ≤ 0 := by
  classical
  have hrw : ∑ k ∈ Finset.range n, psiCoc (T := T) g (n - k) (T^[k] x)
      = ∑ k ∈ (Finset.range n).filter (fun k => T^[k] x ∈ LambdaSet (T := T) g (n - k)),
          bcoc (T := T) g (n - k) (T^[k] x) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [psiCoc, Set.indicator_apply]
  rw [hrw]
  exact sum_bcoc_lambda_nonpos g n x

/-- `bcoc g i = g i − g (i−1) ∘ T` is integrable. -/
private theorem integrable_bcoc (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (i : ℕ) : Integrable (bcoc (T := T) g i) μ := by
  have hcomp : Integrable (fun x => g (i - 1) (T x)) μ :=
    hT.integrable_comp_of_integrable (hint (i - 1))
  exact (hint i).sub hcomp

/-- `LambdaSet g m` is null-measurable: a finite union over `1 ≤ k ≤ m` of the null-measurable
sets `{g m − g (m−k) ∘ T^[k] < 0}`. -/
private theorem nullMeasurableSet_LambdaSet (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (m : ℕ) :
    NullMeasurableSet (LambdaSet (T := T) g m) μ := by
  classical
  have hrw : LambdaSet (T := T) g m
      = ⋃ k ∈ (Finset.Icc 1 m : Finset ℕ), {y | g m y - g (m - k) (T^[k] y) < 0} := by
    ext y
    simp only [LambdaSet, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk1, hkm, hlt⟩; exact ⟨k, ⟨hk1, hkm⟩, hlt⟩
    · rintro ⟨k, ⟨hk1, hkm⟩, hlt⟩; exact ⟨k, hk1, hkm, hlt⟩
  rw [hrw]
  refine NullMeasurableSet.biUnion (Finset.Icc 1 m).countable_toSet (fun k _ => ?_)
  have hg1 : AEMeasurable (g m) μ := (hint m).aemeasurable
  have hg2 : AEMeasurable (fun y => g (m - k) (T^[k] y)) μ :=
    (hT.iterate k).integrable_comp_of_integrable (hint (m - k)) |>.aemeasurable
  exact nullMeasurableSet_lt (hg1.sub hg2) aemeasurable_const

/-- `psiCoc g i` is integrable (indicator of a null-measurable set of an integrable function). -/
private theorem integrable_psiCoc (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (i : ℕ) : Integrable (psiCoc (T := T) g i) μ :=
  (integrable_bcoc hT hint i).indicator₀ (nullMeasurableSet_LambdaSet hT hint i)

/-- Set-integral invariance under `T^[k]` for a measurable `T`-invariant set `s`:
`∫_s (h ∘ T^[k]) = ∫_s h`. -/
private theorem setIntegral_comp_iterate_of_invariants
    (hT : MeasurePreserving T μ μ) {h : X → ℝ} (hh : AEStronglyMeasurable h μ)
    {s : Set X} (hs : MeasurableSet s) (hsinv : T ⁻¹' s = s) (k : ℕ) :
    ∫ x in s, h (T^[k] x) ∂μ = ∫ x in s, h x ∂μ := by
  have hmp : MeasurePreserving (T^[k]) μ μ := hT.iterate k
  have hsinvk : T^[k] ⁻¹' s = s := by
    clear hh hs hmp
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ', Set.preimage_comp, hsinv, ih]
  have hmap : Measure.map (T^[k]) μ = μ := hmp.map_eq
  have hhmap : AEStronglyMeasurable h (Measure.map (T^[k]) μ) := by rw [hmap]; exact hh
  calc ∫ x in s, h (T^[k] x) ∂μ
      = ∫ x in T^[k] ⁻¹' s, h (T^[k] x) ∂μ := by rw [hsinvk]
    _ = ∫ y in s, h y ∂(Measure.map (T^[k]) μ) := (setIntegral_map hs hhmap hmp.aemeasurable).symm
    _ = ∫ y in s, h y ∂μ := by rw [hmap]

/-- **(★) — integrated leader inequality** (Karlsson Lemma 3.4, the telescoped integral). For a
measurable `T`-invariant set `B`, the partial sum of localized increment integrals is
non-positive: `∑_{i=1}^n ∫_{B} ψ_i ≤ 0`, where `ψ_i = 1_{Λ_i} bcoc g i`. -/
private theorem sum_setIntegral_psiCoc_nonpos
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ)
    {B : Set X} (hB : MeasurableSet B) (hBinv : T ⁻¹' B = B) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∫ x in B, psiCoc (T := T) g i x ∂μ ≤ 0 := by
  classical
  -- Integrate the pointwise inequality `∑_{k<n} ψ_{n-k}(T^[k] x) ≤ 0` over `B`.
  have hpt : ∫ x in B, (∑ k ∈ Finset.range n, psiCoc (T := T) g (n - k) (T^[k] x)) ∂μ ≤ 0 :=
    integral_nonpos_of_ae (Filter.Eventually.of_forall (fun x => sum_psiCoc_comp_nonpos g n x))
  -- Pull the finite sum out and apply the change of variables for `T^[k]`.
  rw [integral_finsetSum (μ := μ.restrict B) (Finset.range n)
    (f := fun k x => psiCoc (T := T) g (n - k) (T^[k] x))
    (fun k _ => ((hT.iterate k).integrable_comp_of_integrable
      (integrable_psiCoc hT hint (n - k))).restrict)] at hpt
  -- `∫_B ψ_{n-k} ∘ T^[k] = ∫_B ψ_{n-k}`.
  have hcv : ∀ k ∈ Finset.range n,
      ∫ x in B, psiCoc (T := T) g (n - k) (T^[k] x) ∂μ
        = ∫ x in B, psiCoc (T := T) g (n - k) x ∂μ := fun k _ =>
    setIntegral_comp_iterate_of_invariants hT
      (integrable_psiCoc hT hint (n - k)).aestronglyMeasurable hB hBinv k
  rw [Finset.sum_congr rfl hcv] at hpt
  -- Reindex `i = n - k` over `range n` to `Icc 1 n`.
  have hreindex : ∑ k ∈ Finset.range n, ∫ x in B, psiCoc (T := T) g (n - k) x ∂μ
      = ∑ i ∈ Finset.Icc 1 n, ∫ x in B, psiCoc (T := T) g i x ∂μ := by
    refine Finset.sum_nbij' (fun k => n - k) (fun i => n - i) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; dsimp only; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; dsimp only; omega
    · intro k _; rfl
  rw [hreindex] at hpt
  exact hpt

/-- **Integrated telescoping** over an invariant set `B`:
`∑_{i=1}^m ∫_B bcoc g i = ∫_B g m − ∫_B g 0`. -/
private theorem sum_setIntegral_bcoc_eq
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ)
    {B : Set X} (hB : MeasurableSet B) (hBinv : T ⁻¹' B = B) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, ∫ x in B, bcoc (T := T) g i x ∂μ
      = (∫ x in B, g m x ∂μ) - ∫ x in B, g 0 x ∂μ := by
  classical
  have hcv : ∀ k ∈ Finset.range m,
      ∫ x in B, bcoc (T := T) g (m - k) (T^[k] x) ∂μ
        = ∫ x in B, bcoc (T := T) g (m - k) x ∂μ := fun k _ =>
    setIntegral_comp_iterate_of_invariants hT
      (integrable_bcoc hT hint (m - k)).aestronglyMeasurable hB hBinv k
  have hreindex : ∑ k ∈ Finset.range m, ∫ x in B, bcoc (T := T) g (m - k) x ∂μ
      = ∑ i ∈ Finset.Icc 1 m, ∫ x in B, bcoc (T := T) g i x ∂μ := by
    refine Finset.sum_nbij' (fun k => m - k) (fun i => m - i) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; dsimp only; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; dsimp only; omega
    · intro k _; rfl
  calc ∑ i ∈ Finset.Icc 1 m, ∫ x in B, bcoc (T := T) g i x ∂μ
      = ∑ k ∈ Finset.range m, ∫ x in B, bcoc (T := T) g (m - k) x ∂μ := hreindex.symm
    _ = ∑ k ∈ Finset.range m, ∫ x in B, bcoc (T := T) g (m - k) (T^[k] x) ∂μ :=
        (Finset.sum_congr rfl hcv).symm
    _ = ∫ x in B, (∑ k ∈ Finset.range m, bcoc (T := T) g (m - k) (T^[k] x)) ∂μ :=
        (integral_finsetSum (μ := μ.restrict B) (Finset.range m)
          (f := fun k x => bcoc (T := T) g (m - k) (T^[k] x))
          (fun k _ => ((hT.iterate k).integrable_comp_of_integrable
            (integrable_bcoc hT hint (m - k))).restrict)).symm
    _ = ∫ x in B, (g m x - g 0 (T^[m] x)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => sum_bcoc_telescope g m x))
    _ = (∫ x in B, g m x ∂μ) - ∫ x in B, g 0 (T^[m] x) ∂μ :=
        integral_sub (hint m).restrict
          ((hT.iterate m).integrable_comp_of_integrable (hint 0)).restrict
    _ = (∫ x in B, g m x ∂μ) - ∫ x in B, g 0 x ∂μ := by
        rw [setIntegral_comp_iterate_of_invariants hT (hint 0).aestronglyMeasurable hB hBinv m]

omit [MeasurableSpace X] in
/-- `ASet g` is monotone in the length. -/
private theorem ASet_mono {g : ℕ → X → ℝ} : Monotone (ASet g) := by
  intro a b hab y hy
  obtain ⟨k, hk1, hka, hk⟩ := hy
  exact ⟨k, hk1, le_trans hka hab, hk⟩

/-- `ASet g m` is null-measurable. -/
private theorem nullMeasurableSet_ASet {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) (m : ℕ) :
    NullMeasurableSet (ASet g m) μ := by
  classical
  have hrw : ASet g m = ⋃ k ∈ (Finset.Icc 1 m : Finset ℕ), {y | g k y < 0} := by
    ext y; simp only [ASet, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk1, hkm, hlt⟩; exact ⟨k, ⟨hk1, hkm⟩, hlt⟩
    · rintro ⟨k, ⟨hk1, hkm⟩, hlt⟩; exact ⟨k, hk1, hkm, hlt⟩
  rw [hrw]
  exact NullMeasurableSet.biUnion (Finset.Icc 1 m).countable_toSet
    (fun k _ => nullMeasurableSet_lt (hint k).aemeasurable aemeasurable_const)

/-- **L-C — Derriennic's maximal inequality** (Karlsson Lemma 3.4). For a measurable
`T`-invariant set `B` on which (a.e.) `liminf (cdiv g · x) < 0`, the normalized integral
`(∫_B g (n+1))/(n+1)` has non-positive `limsup`. -/
private theorem limsup_setIntegral_div_nonpos [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    {B : Set X} (hB : MeasurableSet B) (hBinv : T ⁻¹' B = B)
    (hBneg : ∀ᵐ x ∂μ, x ∈ B → ∃ k, g (k + 1) x < 0) :
    Filter.limsup
      (fun n : ℕ => (((∫ x in B, g (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop ≤ 0 := by
  classical
  -- The positive part `p := (g 1)⁺`, integrable and nonnegative.
  set p : X → ℝ := fun y => max (g 1 y) 0 with hpdef
  have hpint : Integrable p μ := (hint 1).pos_part
  have hpnn : ∀ y, 0 ≤ p y := fun y => le_max_right _ _
  -- The tail integrals `dseq i = ∫_{B \ A_i} p`.
  set dseq : ℕ → ℝ := fun i => ∫ x in B, ((ASet g i)ᶜ).indicator p x ∂μ with hdseqdef
  -- (1) `B ⊆ᵐ ⋃ A_i`: on `B`, some level is `< 0`.
  have hBsub : ∀ᵐ x ∂μ, x ∈ B → x ∈ ⋃ i, ASet g i := by
    filter_upwards [hBneg] with x hx hxB
    obtain ⟨k, hk⟩ := hx hxB
    refine Set.mem_iUnion.2 ⟨k + 1, ?_⟩
    exact ⟨k + 1, by omega, le_refl _, hk⟩
  -- (2) `dseq i → 0` by dominated convergence on the antitone indicators.
  have hdseq0 : Tendsto dseq atTop (𝓝 0) := by
    set F : ℕ → X → ℝ := fun i x => (B ∩ (ASet g i)ᶜ).indicator p x with hFdef
    have hFnm : ∀ i, NullMeasurableSet (B ∩ (ASet g i)ᶜ) μ := fun i =>
      hB.nullMeasurableSet.inter (nullMeasurableSet_ASet hint i).compl
    have hFint : ∀ i, ∫ a, F i a ∂μ = dseq i := by
      intro i
      simp only [hFdef, hdseqdef]
      rw [← Set.indicator_indicator, integral_indicator₀ hB.nullMeasurableSet]
    have hFm : ∀ i, AEStronglyMeasurable (F i) μ :=
      fun i => (hpint.aestronglyMeasurable.indicator₀ (hFnm i))
    have hbound : ∀ i, ∀ᵐ a ∂μ, ‖F i a‖ ≤ p a := by
      intro i
      filter_upwards with a
      simp only [hFdef, Set.indicator_apply, Real.norm_eq_abs]
      by_cases h : a ∈ B ∩ (ASet g i)ᶜ
      · simp only [h, if_true, abs_of_nonneg (hpnn a), le_refl]
      · simp only [h, if_false, abs_zero]; exact hpnn a
    have hlim : ∀ᵐ a ∂μ, Tendsto (fun i => F i a) atTop (𝓝 0) := by
      filter_upwards [hBsub] with a hBa
      by_cases haB : a ∈ B
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hBa haB)
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop j] with i hij
        simp only [hFdef, Set.indicator_apply]
        have : a ∈ ASet g i := ASet_mono hij hj
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, this, not_true, and_false, if_false]
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards with i
        simp only [hFdef, Set.indicator_apply]
        simp only [Set.mem_inter_iff, haB, false_and, if_false]
    have hconv : Tendsto (fun i => ∫ a, F i a ∂μ) atTop (𝓝 (∫ a, (0 : ℝ) ∂μ)) :=
      tendsto_integral_of_dominated_convergence p hFm hpint hbound hlim
    simp only [integral_zero] at hconv
    exact (funext hFint) ▸ hconv
  -- (3) Per-level bound: `∫_B bcoc g i ≤ ∫_B ψ_i + dseq i` for `i ≥ 1`.
  have hpoint : ∀ i, 1 ≤ i → ∀ x,
      bcoc (T := T) g i x - psiCoc (T := T) g i x ≤ ((ASet g i)ᶜ).indicator p x := by
    intro i hi1 x
    -- `bcoc g i x ≤ p x` by subadditivity (i ≥ 1).
    have hble : bcoc (T := T) g i x ≤ p x := by
      have hdec : g i x ≤ g 1 x + g (i - 1) (T x) := by
        have := hsub.apply_add_le 1 (i - 1) x
        rw [show 1 + (i - 1) = i by omega, Function.iterate_one] at this
        exact this
      simp only [bcoc, hpdef]
      have : g i x - g (i - 1) (T x) ≤ g 1 x := by linarith
      exact le_trans this (le_max_left _ _)
    by_cases hΛ : x ∈ LambdaSet (T := T) g i
    · -- on `Λ_i`: `psiCoc = bcoc`, so LHS = 0 ≤ RHS.
      simp only [psiCoc, Set.indicator_of_mem hΛ, sub_self]
      exact Set.indicator_nonneg (fun y _ => hpnn y) x
    · -- off `Λ_i` (⟹ off `A_i`): `psiCoc = 0`, LHS = bcoc ≤ p = RHS.
      have hA : x ∉ ASet g i := fun h => hΛ (ASet_subset_LambdaSet hsub i h)
      simp only [psiCoc, Set.indicator_of_notMem hΛ, sub_zero,
        Set.indicator_of_mem (Set.mem_compl hA)]
      exact hble
  -- (4) The main inequality: `∫_B g (n+1) ≤ ∫_B g 0 + ∑_{i∈Icc 1 (n+1)} dseq i`.
  have hmain : ∀ n : ℕ, ∫ x in B, g (n + 1) x ∂μ
      ≤ (∫ x in B, g 0 x ∂μ) + ∑ i ∈ Finset.Icc 1 (n + 1), dseq i := by
    intro n
    -- telescoping: `∫_B g(n+1) - ∫_B g 0 = ∑_{Icc 1 (n+1)} ∫_B bcoc g i`.
    have htel := sum_setIntegral_bcoc_eq hT hint hB hBinv (n + 1)
    -- per-level: `∫_B bcoc g i ≤ ∫_B ψ_i + dseq i`.
    have hlevel : ∀ i ∈ Finset.Icc 1 (n + 1),
        ∫ x in B, bcoc (T := T) g i x ∂μ
          ≤ (∫ x in B, psiCoc (T := T) g i x ∂μ) + dseq i := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have hsub_int : ∫ x in B, (bcoc (T := T) g i x - psiCoc (T := T) g i x) ∂μ ≤ dseq i := by
        rw [hdseqdef]
        refine setIntegral_mono_on ?_ ?_ hB (fun x _ => hpoint i hi.1 x)
        · exact ((integrable_bcoc hT hint i).sub (integrable_psiCoc hT hint i)).restrict
        · exact (hpint.indicator₀ (nullMeasurableSet_ASet hint i).compl).restrict
      rw [integral_sub (integrable_bcoc hT hint i).restrict
        (integrable_psiCoc hT hint i).restrict] at hsub_int
      linarith
    -- sum the per-level bounds; use ★ for `∑ ∫_B ψ_i ≤ 0`.
    have hsumlevel : ∑ i ∈ Finset.Icc 1 (n + 1), ∫ x in B, bcoc (T := T) g i x ∂μ
        ≤ (∑ i ∈ Finset.Icc 1 (n + 1), ∫ x in B, psiCoc (T := T) g i x ∂μ)
          + ∑ i ∈ Finset.Icc 1 (n + 1), dseq i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hlevel
    have hstar := sum_setIntegral_psiCoc_nonpos hT hint hB hBinv (n + 1)
    have : ∑ i ∈ Finset.Icc 1 (n + 1), ∫ x in B, bcoc (T := T) g i x ∂μ
        ≤ ∑ i ∈ Finset.Icc 1 (n + 1), dseq i := by linarith
    rw [htel] at this
    linarith
  -- (5) Conclude: `(∫_B g(n+1))/(n+1) ≤ r n → 0`, so the EReal limsup is `≤ 0`.
  set r : ℕ → ℝ := fun n =>
    (∫ x in B, g 0 x ∂μ) / (n + 1) + (∑ i ∈ Finset.Icc 1 (n + 1), dseq i) / (n + 1) with hrdef
  -- `∑_{Icc 1 (n+1)} dseq = ∑_{range (n+1)} dseq (·+1)`.
  have hIccrange : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 (n + 1), dseq i
      = ∑ j ∈ Finset.range (n + 1), dseq (j + 1) := by
    intro n
    refine Finset.sum_nbij' (fun i => i - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Icc] at hi; simp only [Finset.mem_range]; omega
    · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; dsimp only; omega
    · intro j hj; dsimp only; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; dsimp only; congr 1; omega
  have hle : ∀ n : ℕ, (∫ x in B, g (n + 1) x ∂μ) / (n + 1) ≤ r n := by
    intro n
    rw [hrdef]
    simp only
    rw [← add_div]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact (div_le_div_iff_of_pos_right hpos).2 (hmain n)
  have hr0 : Tendsto r atTop (𝓝 0) := by
    rw [hrdef]
    have h1 : Tendsto (fun n : ℕ => (∫ x in B, g 0 x ∂μ) / (n + 1)) atTop (𝓝 0) := by
      simp only [div_eq_mul_inv]
      have : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa using this.const_mul (∫ x in B, g 0 x ∂μ)
    have h2 : Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc 1 (n + 1), dseq i) / (n + 1)) atTop (𝓝 0) := by
      -- Cesàro: `(m⁻¹) ∑_{j<m} dseq (j+1) → 0`, evaluated at `m = n+1`.
      have hces : Tendsto (fun m : ℕ => ((m : ℝ))⁻¹ * ∑ j ∈ Finset.range m, dseq (j + 1))
          atTop (𝓝 0) := Filter.Tendsto.cesaro (hdseq0.comp (tendsto_add_atTop_nat 1))
      have hshift := hces.comp (tendsto_add_atTop_nat 1)
      refine hshift.congr (fun n => ?_)
      simp only [Function.comp]
      rw [hIccrange n, div_eq_inv_mul,
        show ((n : ℝ) + 1) = (((n + 1 : ℕ)) : ℝ) by push_cast; ring]
    simpa using h1.add h2
  -- limsup in EReal of a sequence dominated by `r → 0`.
  have hcoe : Tendsto (fun n : ℕ => ((r n : ℝ) : EReal)) atTop (𝓝 ((0 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hr0
  calc Filter.limsup
        (fun n : ℕ => (((∫ x in B, g (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop
      ≤ Filter.limsup (fun n : ℕ => ((r n : ℝ) : EReal)) atTop := by
        refine Filter.limsup_le_limsup ?_ ?_ ?_
        · filter_upwards with n; exact EReal.coe_le_coe_iff.2 (hle n)
        · exact Filter.isCobounded_le_of_bot
        · exact Filter.isBounded_le_of_top
    _ = ((0 : ℝ) : EReal) := hcoe.limsup_eq
    _ = 0 := by norm_num

/-- **Stopping-time direction (the hard core of Kingman).** A.e. the `EReal` `liminf` of the
normalized cocycle equals its `EReal` `limsup`, proved by the Riesz/Derriennic "leaders" route
(Karlsson, *A proof of the subadditive ergodic theorem*).

Ingredients now in place sorry-free above:
* **L-A** `sum_leaders_nonpos` — Riesz's combinatorial leader lemma (Lemma 3.2).
* **L-B** `sum_leaders_cocycle_nonpos` / `sum_psiCoc_comp_nonpos` — pointwise leader inequality.
* **L-C** `limsup_setIntegral_div_nonpos` — *Derriennic's maximal inequality* (Lemma 3.4):
  for a measurable `T`-invariant `B` on which a.e. some level `g (k+1) < 0`,
  `limsup_n (∫_B g (n+1))/(n+1) ≤ 0` in `EReal`. (This is the substantive measure-theoretic
  step — the telescoped integral `sum_setIntegral_psiCoc_nonpos`, the per-level positive-part
  bound, and the Cesàro tail `dseq i → 0`.)

Remaining (**L-D**, Karlsson §3.3, *not yet formalized*): the `E_{α,β}` contradiction. For the
non-positive companion `v n := g n − birkhoffSum T (g 1) n` (subadditive, `v (n+1) ≤ 0`; and
`ecdiv g − ecdiv v = birkhoffAverage (g 1) (n+1) → μ[g 1 | I]` by M3, so the gap
`limsup − liminf` is the same for `g` and `v`), Karlsson shows `μ{f − g > α} = 0` for all
`α > 0` via the **`Tᴹ`-subsequence cocycle** `vᴹ_n := v_{nM} − ∑_{i<n} v_M(Tⁱᴹ)`:
applying **L-C with `T := T^[M]`** to `vᴹ` (non-positive subadditive for `T^[M]`) and using
`f_M = f`, `g_M = g` plus the `T^[M]`-Birkhoff convergence of `(1/n)∑ v_M(Tⁱᴹ)` (M3) gives
`Mα·μ(E) ≤ lim (1/n)∫_E vᴹ_n ≤ Mε`, hence `μ(E) ≤ ε/α → 0`. -/
private theorem ae_ereal_limsup_le_liminf [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.liminf (fun n => ecdiv g n x) atTop
      = Filter.limsup (fun n => ecdiv g n x) atTop := by
  sorry -- BLOCKED: L-D (Karlsson §3.3 `E_{α,β}` contradiction via the `Tᴹ`-subsequence
  -- cocycle `vᴹ`). L-A/L-B/L-C are proven above; this is the remaining reduction.

/-! ### The Kingman core: a.e. existence of an integrable limit (the single deep gap) -/

/-- **Kingman core (the single deep gap of M4).** The normalized cocycle `g (n+1) x / (n+1)`
converges, for `μ`-a.e. `x`, to the value `G x` of some integrable `G`. This packages the
entire analytic content of Kingman's theorem that is *not* generic measure theory:

* a.e. **convergence** (the stopping-time / greedy block partition, Katznelson–Weiss); and
* **integrability** of the limit (the Fatou step).

Everything else in this file — a.e. boundedness (`ae_bddBelow_cdiv`), `limsup ≤ liminf`
(`ae_limsup_le_liminf_div`), integrability of the envelope (`int_limsup_div_integrable`),
`T`-invariance, and the ergodic collapse — is derived from this one lemma by soft arguments,
so closing `M4` reduces exactly to this proof.

The proof is now sorry-free given the isolated stopping-time lemma `ae_ereal_limsup_le_liminf`.
It follows `docs/plan/blueprints/m4-kingman-v2.md` §4 and `docs/research/scratch/m4-L9-notes.md`:
work with the `EReal`-valued `limsup`/`liminf` to avoid the `ℝ` junk value at `−∞`; the `ℝ≥0∞`
Fatou step (`ae_bot_lt_ereal_limsup`, `int_limsup_div_integrable_aux`) gives `limsup > ⊥` a.e.
and the integrability; the stopping-time lemma gives `liminf = limsup`; together with the
envelope `limsup ≤ ↑B < ⊤` they force a finite a.e. limit `e.toReal`. -/
private theorem ae_tendsto_cdiv [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, Integrable G μ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => cdiv g n x) atTop (𝓝 (G x)) := by
  -- `G := f₊` (the `ℝ`-valued limsup), integrable by the Fatou step.
  refine ⟨fun x => Filter.limsup (fun n => cdiv g n x) atTop,
    int_limsup_div_integrable_aux hT hTm hsub hint hbdd, ?_⟩
  -- On the good set: `⊥ < e ≤ ↑B < ⊤` and `liminf = limsup = e`, so `cdiv → e.toReal = f₊ x`.
  filter_upwards [ae_ereal_limsup_le_condExp hT hsub hint,
    ae_bot_lt_ereal_limsup hT hTm hsub hint hbdd,
    ae_ereal_limsup_le_liminf hT hTm hsub hint hbdd] with x hupper hbot heq
  set e : EReal := Filter.limsup (fun n => ecdiv g n x) atTop with hedef
  -- Finiteness of `e`.
  have hetop : e ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_lt_top _).ne hupper
  have hebot : e ≠ ⊥ := hbot.ne'
  -- `ecdiv → e` from `liminf = limsup = e` (EReal is a complete linear order).
  have htend_e : Tendsto (fun n => ecdiv g n x) atTop (𝓝 e) :=
    tendsto_of_liminf_eq_limsup heq rfl
  -- Transfer to `ℝ`: `cdiv → e.toReal`.
  have hcoe : e = ((e.toReal : ℝ) : EReal) := (EReal.coe_toReal hetop hebot).symm
  have htend_r : Tendsto (fun n => cdiv g n x) atTop (𝓝 e.toReal) := by
    rw [← EReal.tendsto_coe]
    have : (fun n => ((cdiv g n x : ℝ) : EReal)) = fun n => ecdiv g n x := rfl
    rw [this, ← hcoe]
    exact htend_e
  -- `f₊ x = e.toReal` since the sequence converges.
  have hfp : Filter.limsup (fun n => cdiv g n x) atTop = e.toReal := htend_r.limsup_eq
  rw [hfp]
  exact htend_r

/-- A.e. the range of `cdiv g · x` is bounded below: a convergent sequence is bounded
(derived from `ae_tendsto_cdiv`). -/
private theorem ae_bddBelow_cdiv [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, BddBelow (Set.range fun n : ℕ => cdiv g n x) := by
  obtain ⟨G, _, hG⟩ := ae_tendsto_cdiv hT hT.measurable hsub hint hbdd
  filter_upwards [hG] with x hx
  exact hx.bddBelow_range

/-! ### L7: a.e. `T`-invariance of the limsup/liminf envelopes -/

omit [MeasurableSpace X] in
/-- The pointwise subadditivity bound, normalized: `cdiv g n x ≤ g 1 x / (n+1) + g n (T x)/(n+1)`. -/
private theorem cdiv_le_shift {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    cdiv g n x ≤ g 1 x / (n + 1) + g n (T x) / (n + 1) := by
  have h := hsub.apply_add_le 1 n x
  rw [show (1 + n) = n + 1 from by ring] at h
  rw [cdiv, ← add_div]
  apply div_le_div_of_nonneg_right h (by positivity) |>.trans_eq
  simp only [Function.iterate_one]

omit [MeasurableSpace X] in
/-- **Key limsup comparison.** For a fixed `x` at which the normalized cocycle is bounded
(at `x` and at `T x`), `limsup (cdiv g · x) ≤ limsup (cdiv g · (T x))`. Combines the
subadditivity bound with the vanishing-perturbation lemma `limsup_eq_of_sub_tendsto_zero`. -/
private theorem limsup_cdiv_le_comp {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) {x : X}
    (_hax : BddAbove (Set.range fun n : ℕ => cdiv g n x))
    (hbx : BddBelow (Set.range fun n : ℕ => cdiv g n x))
    (haTx : BddAbove (Set.range fun n : ℕ => cdiv g n (T x)))
    (hbTx : BddBelow (Set.range fun n : ℕ => cdiv g n (T x))) :
    Filter.limsup (fun n => cdiv g n x) atTop ≤ Filter.limsup (fun n => cdiv g n (T x)) atTop := by
  -- `target n := cdiv g n (T x)`, bounded both ways.
  set target : ℕ → ℝ := fun n => cdiv g n (T x) with htdef
  -- `w n := g 1 x / (n+1) + g n (T x)/(n+1)`, and `cdiv g n x ≤ w n`.
  set w : ℕ → ℝ := fun n => g 1 x / (n + 1) + g n (T x) / (n + 1) with hwdef
  have hcw : ∀ n, cdiv g n x ≤ w n := fun n => cdiv_le_shift hsub n x
  -- `w' m := w (m+1)`, and `w' m - target m → 0`.
  set w' : ℕ → ℝ := fun m => w (m + 1) with hw'def
  have hdiff : Tendsto (fun m => w' m - target m) atTop (𝓝 0) := by
    -- `w' m - target m = g 1 x/(m+2) - (cdiv g m (T x))/(m+2)`.
    have hform : ∀ m : ℕ, w' m - target m
        = g 1 x / ((m : ℝ) + 2) - target m / ((m : ℝ) + 2) := by
      intro m
      simp only [hw'def, hwdef, htdef, cdiv]
      have h1 : (((m : ℕ) + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
      rw [h1]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
    refine Tendsto.congr (fun m => (hform m).symm) ?_
    -- both terms tend to `0`.
    have hinv2 : Tendsto (fun m : ℕ => ((m : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact tendsto_inv_atTop_zero.comp this
    have ht1 : Tendsto (fun m : ℕ => g 1 x / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      simp only [div_eq_mul_inv]
      simpa using hinv2.const_mul (g 1 x)
    have ht2 : Tendsto (fun m : ℕ => target m / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      -- `target` bounded, `(m+2)⁻¹ → 0`, product → 0.
      obtain ⟨Ma, hMa⟩ := haTx; obtain ⟨mb, hmb⟩ := hbTx
      have hnorm : IsBoundedUnder (· ≤ ·) atTop (norm ∘ target) := by
        refine ⟨|mb| + |Ma|, ?_⟩
        simp only [eventually_map]
        filter_upwards with m
        have h1 := hmb (Set.mem_range_self m); have h2 := hMa (Set.mem_range_self m)
        simp only [Function.comp_apply, Real.norm_eq_abs, abs_le]
        constructor
        · nlinarith [neg_abs_le mb, le_abs_self Ma, abs_nonneg mb, abs_nonneg Ma]
        · nlinarith [le_abs_self Ma, neg_abs_le mb, abs_nonneg mb, abs_nonneg Ma]
      have := Filter.isBoundedUnder_le_mul_tendsto_zero hnorm hinv2
      simpa only [div_eq_mul_inv] using this
    simpa using ht1.sub ht2
  -- boundedness of `target` and `w'`.
  have htargetA : BddAbove (Set.range target) := haTx
  have htargetB : BddBelow (Set.range target) := hbTx
  -- `w'` bounded: `w' = target + (w' - target)`, and `w' - target` is a convergent (hence
  -- bounded) sequence.
  have hw'A : BddAbove (Set.range w') := by
    obtain ⟨C, hC⟩ := (hdiff.bddAbove_range)
    obtain ⟨Mt, hMt⟩ := htargetA
    refine ⟨Mt + C, ?_⟩
    rintro y ⟨m, rfl⟩
    have h1 : target m ≤ Mt := hMt (Set.mem_range_self m)
    have h2 : w' m - target m ≤ C := hC (Set.mem_range_self m)
    linarith
  have hw'B : BddBelow (Set.range w') := by
    obtain ⟨c, hc⟩ := (hdiff.bddBelow_range)
    obtain ⟨mt, hmt⟩ := htargetB
    refine ⟨mt + c, ?_⟩
    rintro y ⟨m, rfl⟩
    have h1 : mt ≤ target m := hmt (Set.mem_range_self m)
    have h2 : c ≤ w' m - target m := hc (Set.mem_range_self m)
    linarith
  -- `w` bounded above (only differs from `w'` by the single value `w 0`).
  have hwA : BddAbove (Set.range w) := by
    obtain ⟨M', hM'⟩ := hw'A
    refine ⟨max M' (w 0), ?_⟩
    rintro y ⟨n, rfl⟩
    rcases n with _ | m
    · exact le_max_right _ _
    · exact le_trans (hM' (Set.mem_range_self m)) (le_max_left _ _)
  -- Step A: `limsup cdiv·x ≤ limsup w`.
  have hcobx : IsCoboundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) :=
    hbx.isBoundedUnder_of_range.isCoboundedUnder_le
  have hstepA : Filter.limsup (fun n => cdiv g n x) atTop ≤ Filter.limsup w atTop :=
    Filter.limsup_le_limsup (Eventually.of_forall hcw) hcobx hwA.isBoundedUnder_of_range
  -- Step B: `limsup w = limsup w' = limsup target`.
  have hww' : Filter.limsup w atTop = Filter.limsup w' atTop := (limsup_nat_add w 1).symm
  have hw'target : Filter.limsup w' atTop = Filter.limsup target atTop :=
    limsup_eq_of_sub_tendsto_zero hw'A hw'B htargetA htargetB hdiff
  -- Conclude: `limsup cdiv·x ≤ limsup w = limsup target = limsup cdiv·(T x)`.
  calc Filter.limsup (fun n => cdiv g n x) atTop
      ≤ Filter.limsup w atTop := hstepA
    _ = Filter.limsup target atTop := hww'.trans hw'target

/-- **L7 (limsup).** The envelope `f₊ x = limsup_n cdiv g n x` is a.e. `T`-invariant.
The pointwise inequality `f₊ x ≤ f₊ (T x)` (`limsup_cdiv_le_comp`) feeds the level-set
invariance argument `ae_eq_comp_of_le_comp` (`L5`).

Depends on `ae_bddBelow_cdiv` (a.e. boundedness below of the normalized cocycle) for the
cobounded side-conditions, which is the single boundedness fact entangled with `L9`. -/
private theorem limsup_div_comp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    (fun x => Filter.limsup (fun n => cdiv g n x) atTop) ∘ T
      =ᵐ[μ] fun x => Filter.limsup (fun n => cdiv g n x) atTop := by
  -- a.e. boundedness at `x` and (transported) at `T x`.
  have hax := ae_bddAbove_cdiv hT hsub hint
  have hbx := ae_bddBelow_cdiv hT hsub hint hbdd
  have haTx := hT.quasiMeasurePreserving.tendsto_ae hax
  have hbTx := hT.quasiMeasurePreserving.tendsto_ae hbx
  refine ae_eq_comp_of_le_comp hT (aemeasurable_limsup_div hint) ?_
  filter_upwards [hax, hbx, haTx, hbTx] with x hax hbx haTx hbTx
  exact limsup_cdiv_le_comp hsub hax hbx haTx hbTx

/-! ### Integrability of the limsup envelope -/

/-- **`Integrable f₊`.** The limsup envelope `f₊ x = limsup_n cdiv g n x` is integrable:
on the a.e. set where `cdiv g · x` converges to `G x` (`ae_tendsto_cdiv`), the limsup equals
`G x`, and `G` is integrable. -/
private theorem int_limsup_div_integrable [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    Integrable (fun x => Filter.limsup (fun n => cdiv g n x) atTop) μ := by
  obtain ⟨G, hGint, hG⟩ := ae_tendsto_cdiv hT hT.measurable hsub hint hbdd
  refine (integrable_congr ?_).mpr hGint
  filter_upwards [hG] with x hx
  exact hx.limsup_eq

/-! ### L1b: general block subadditivity (for L9) -/

omit [MeasurableSpace X] in
/-- **L1b — block subadditivity.** For a subadditive cocycle and any consecutive block
decomposition of `[0, n)` into `k+1` blocks of lengths `ℓ 0, …, ℓ k` (with
`n = ∑_{i ≤ k} ℓ i`), the cocycle is dominated by the sum of the block cocycle values along
the orbit, evaluated at the partial-sum frontiers `T^[∑_{j < i} ℓ j] x`. (Used only by `L9`;
stated for `k+1` blocks since the empty decomposition would force the false `g 0 x ≤ 0`.) -/
private theorem IsSubadditiveCocycle.le_sum_blocks {g : ℕ → X → ℝ}
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

/-! ### L9: the hard combinatorial direction (stopping-time block partition) -/

/-- **`limsup ≤ liminf` a.e.** For a.e. `x` the limsup of the normalized cocycle is dominated
by its liminf. Derived from `ae_tendsto_cdiv`: where the sequence converges, both equal the
limit. (The deep content is in `ae_tendsto_cdiv`; this is a soft corollary.) -/
private theorem ae_limsup_le_liminf_div [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.limsup (fun n => cdiv g n x) atTop
      ≤ Filter.liminf (fun n => cdiv g n x) atTop := by
  obtain ⟨G, _, hG⟩ := ae_tendsto_cdiv hT hTm hsub hint hbdd
  filter_upwards [hG] with x hx
  exact le_of_eq (hx.limsup_eq.trans hx.liminf_eq.symm)

/-! ### L10 / L11: assembly -/

/-- **Kingman's subadditive ergodic theorem** (`M4`). For a measure-preserving `T` and
an integrable subadditive cocycle `g` whose normalized integrals are bounded below,
`gₙ / n` converges `μ`-a.e. to a `T`-invariant integrable limit `G`. -/
theorem tendsto_kingman [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, (G ∘ T =ᵐ[μ] G) ∧ Integrable G μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 (G x))) := by
  -- The a.e. limit is the liminf envelope `f₋`.
  set fm : X → ℝ := fun x => Filter.liminf (fun n => cdiv g n x) atTop with hfmdef
  set fp : X → ℝ := fun x => Filter.limsup (fun n => cdiv g n x) atTop with hfpdef
  -- `f₋ =ᵐ f₊` (L9 `limsup ≤ liminf` + `liminf_le_limsup`, on the a.e.-bounded set).
  have heq : fm =ᵐ[μ] fp := by
    filter_upwards [ae_limsup_le_liminf_div hT hT.measurable hsub hint hbdd,
      ae_bddAbove_cdiv hT hsub hint, ae_bddBelow_cdiv hT hsub hint hbdd] with x hle hba hbb
    have hbA : IsBoundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) := hba.isBoundedUnder_of_range
    have hbB : IsBoundedUnder (· ≥ ·) atTop (fun n => cdiv g n x) := hbb.isBoundedUnder_of_range
    exact le_antisymm (Filter.liminf_le_limsup hbA hbB) hle
  refine ⟨fm, ?_, ?_, ?_⟩
  · -- `f₋ ∘ T =ᵐ f₋`: derive from `f₊` invariance (L7) and `f₋ =ᵐ f₊`.
    have hfp_inv : fp ∘ T =ᵐ[μ] fp := limsup_div_comp_ae hT hsub hint hbdd
    -- `f₋ ∘ T =ᵐ f₊ ∘ T =ᵐ f₊ =ᵐ f₋`.
    have h1 : fm ∘ T =ᵐ[μ] fp ∘ T := hT.quasiMeasurePreserving.ae_eq_comp heq
    exact (h1.trans hfp_inv).trans heq.symm
  · -- `Integrable f₋`: `f₋ =ᵐ f₊` and `f₊` integrable (L8).
    have hfp_int : Integrable fp μ := int_limsup_div_integrable hT hsub hint hbdd
    exact (integrable_congr heq).mpr hfp_int
  · -- Pointwise convergence of `cdiv g · x` to `f₋ x`, then reindex (L0).
    filter_upwards [ae_limsup_le_liminf_div hT hT.measurable hsub hint hbdd,
      ae_bddAbove_cdiv hT hsub hint, ae_bddBelow_cdiv hT hsub hint hbdd] with x hle hba hbb
    have hbA : IsBoundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) := hba.isBoundedUnder_of_range
    have hbB : IsBoundedUnder (· ≥ ·) atTop (fun n => cdiv g n x) := hbb.isBoundedUnder_of_range
    -- `f₋ x ≤ liminf` (refl) and `limsup ≤ f₋ x` (L9), so the sequence converges to `f₋ x`.
    have htend : Tendsto (fun n => cdiv g n x) atTop (𝓝 (fm x)) :=
      tendsto_of_le_liminf_of_limsup_le (le_refl _) hle hbA hbB
    -- Reindex to the original Kingman sequence.
    rw [tendsto_kingman_reindex]
    exact htend

/-- **Kingman, ergodic case**: under ergodicity the a.e. limit is a single constant.
(That constant is the Fekete infimum `⨅ n, (∫ g_{n+1})/(n+1)`; identifying it with the
infimum is deferred — the statement here asserts only a.e.-constancy, which is what the
multiplicative ergodic theorem consumes.) -/
theorem tendsto_kingman_ergodic
    [IsProbabilityMeasure μ] (hT : Ergodic T μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 c) := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  -- Kingman gives a `T`-invariant integrable limit `G`.
  obtain ⟨G, hGinv, hGint, hGconv⟩ := tendsto_kingman hmp hsub hint hbdd
  -- Ergodicity forces `G` a.e. constant.
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hGint.aestronglyMeasurable hGinv
  refine ⟨c, ?_⟩
  filter_upwards [hGconv, hc] with x hx hcx
  have hcx' : G x = c := hcx
  rwa [hcx'] at hx

end Oseledets
