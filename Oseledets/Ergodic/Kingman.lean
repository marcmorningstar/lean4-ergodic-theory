import Oseledets.Ergodic.Birkhoff
import Mathlib.Analysis.Subadditive
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

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
the `T`-invariance — is derived (soft arguments) from a single **core** lemma,
`ae_tendsto_cdiv`: *for `μ`-a.e. `x`, `c n x` converges to the value `G x` of some integrable
`G`*. The core packages the entire analytic content not reducible to generic measure theory
(the stopping-time / greedy block partition plus the Fatou integrability step; see
`docs/plan/blueprints/m4-kingman-v2.md` §4 and `docs/research/scratch/m4-L9-notes.md`) and is
the **only remaining `sorry`** in this file.

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

The proof (still `sorry`) follows `docs/plan/blueprints/m4-kingman-v2.md` §4 and
`docs/research/scratch/m4-L9-notes.md`: work with the `EReal`-valued `limsup`/`liminf` to
avoid the `ℝ` junk value at `−∞`; the `ℝ≥0∞` Fatou step gives `limsup > ⊥` a.e. and the
integrability; the stopping-time partition (truncation `max (liminf) (−M)`, a frontier walk
via `le_sum_blocks`, and the three limit passages `n → ∞`, `L → ∞`, `M → ∞ / ε → 0`) gives
`limsup ≤ liminf`; together they force a finite a.e. limit. -/
private theorem ae_tendsto_cdiv [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, Integrable G μ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => cdiv g n x) atTop (𝓝 (G x)) := by
  sorry -- THE deep direction of Kingman: stopping-time partition + Fatou. See
        -- docs/plan/blueprints/m4-kingman-v2.md §4 and docs/research/scratch/m4-L9-notes.md.

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
