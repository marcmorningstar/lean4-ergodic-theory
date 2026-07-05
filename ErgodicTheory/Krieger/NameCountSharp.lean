/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Krieger.InfoFunction
import ErgodicTheory.Krieger.SMBSharp
import ErgodicTheory.Entropy.KSEntropyProps

/-!
# The name-count / asymptotic-equipartition covering bound (Krieger M2, C2)

This file proves the **name-count / asymptotic-equipartition (AEP) covering bound** that drives the
coding construction (C3) of Krieger's finite generator theorem (issue #15). For a finite measurable
partition `P` of a measure-preserving system, with Kolmogorov–Sinai entropy
`h = ksEntropyPartition hT P`, the bound says: for every `ε > 0` and every large enough rank `N`,
the rank-`N` **names** (atoms of the iterated join `⋁₀ᴺ⁻¹ T⁻ᵏP`) needed to cover all but `ε` of the
space number at most `⌊exp(N(h+ε))⌋`.

This is the **covering form of the Shannon–McMillan–Breiman upper bound**, the exact object the
coding combinatorics consume to turn `log k > h` into the existence of a `Fin k`-valued code.

## The two halves of the argument

The classical AEP covering argument (Walters, *An Introduction to Ergodic Theory*, Ch. 4;
Einsiedler–Lindenstrauss–Ward, *Entropy in Ergodic Theory*, §2–3; Downarowicz,
*Entropy in Dynamical Systems*, §3.1) splits into:

1. **Pigeonhole count (unconditional, proved here in full).** The "good" names — those whose
   join-cell has measure `≥ exp(−N·R)` — number at most `exp(N·R)`. *Proof:* the cells are pairwise
   `μ`-a.e. disjoint, so their total measure is the measure of their union, hence `≤ 1`; with each
   `≥ exp(−N·R)`, a pigeonhole gives `#good · exp(−N·R) ≤ 1`. This is
   `card_goodNames_le_exp` / `card_goodNames_le_exp_entropy`.

2. **Covering (the SMB upper half).** The good names *cover* `≥ 1−ε` of the space, i.e. the union of
   the *bad* cells (measure `< exp(−N(h+ε))`) is `μ`-small. This is exactly the convergence in
   measure
   `μ {x | (1/N)·infoFunₙ(x) > h+ε} → 0`,
   the upper half of the Shannon–McMillan–Breiman theorem *in measure*. It is **parameterized** here
   as the hypothesis `UpperSMBInMeasure` (a sorry-free `Prop`); the unconditional sharp rate `h`
   (rather than the crude `log (card ι)` of `ErgodicTheory.Krieger.SMB`) is now **proved** —
   `ErgodicTheory.Krieger.UpperSMB.upperSMBInMeasure_of_ergodic` discharges this hypothesis for every
   ergodic `T`, from the full pointwise SMB `ae_tendsto_div_infoFun_self` (formerly the `R5`
   Chung `L¹`-domination residual of `ErgodicTheory.Krieger.SMBSharp`). See the module note below for
   the analytic content and the cheaper (martingale-free) block-product route that also fits.

## Main definitions

* `ErgodicTheory.Krieger.goodNames` — the Finset of rank-`N` names whose cell has measure `≥ exp(−N·R)`.
* `ErgodicTheory.Krieger.UpperSMBInMeasure` — the in-measure SMB upper bound at rate `h`, the exact
  analytic input the covering half needs (now discharged for ergodic `T` by
  `ErgodicTheory.Krieger.UpperSMB.upperSMBInMeasure_of_ergodic`).

## Main results

* `ErgodicTheory.Krieger.card_goodNames_le_exp` — **pigeonhole count**: `#goodNames ≤ exp(N·R)`.
* `ErgodicTheory.Krieger.measure_iUnion_goodNames_ge` — the good cells have union-measure
  `≥ μ {x | (1/N)·infoFunₙ ≤ R}`, the *covering content* (also unconditional).
* `ErgodicTheory.Krieger.exists_cover_names_card_le` — the **C3-facing covering bound**: under
  `UpperSMBInMeasure`, for every `ε > 0` and all large `N` there is a Finset `S` of rank-`N` names
  with `μ (⋃ g ∈ S, cell g) ≥ 1 − ε` and `S.card ≤ ⌊exp(N(h+ε))⌋`.

## References

* P. Walters, *An Introduction to Ergodic Theory*, GTM 79, Springer (1982), Ch. 4 (entropy, the
  AEP / covering number of `n`-names).
* M. Einsiedler, E. Lindenstrauss, T. Ward, *Entropy in Ergodic Theory and Topological Dynamics*,
  §2 (SMB) and §3 (Krieger generator).
* T. Downarowicz, *Entropy in Dynamical Systems*, Cambridge (2011), §3.1 (AEP, covering bound).
-/

open MeasureTheory Filter Topology Real Function
open scoped ENNReal

namespace ErgodicTheory.Krieger

open ErgodicTheory.Entropy

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [Fintype ι]
  {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

section Pigeonhole

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (N : ℕ)

/-- The **good names** of rank `N` at rate `R`: the codes `g : Fin N → ι` whose iterated-join cell
`⋂ₖ T⁻ᵏ P_{g k}` has measure at least `exp(−N·R)`. These are the names that carry non-negligible
mass; the pigeonhole bound `card_goodNames_le_exp` shows there are at most `exp(N·R)` of them. -/
noncomputable def goodNames (R : ℝ) : Finset (Fin N → ι) :=
  {g | ENNReal.ofReal (Real.exp (-(N * R))) ≤ μ ((ksJoin hT P N).cells g)}

omit [IsProbabilityMeasure μ] in
lemma mem_goodNames {R : ℝ} {g : Fin N → ι} :
    g ∈ goodNames hT P N R ↔
      ENNReal.ofReal (Real.exp (-(N * R))) ≤ μ ((ksJoin hT P N).cells g) := by
  rw [goodNames, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-- **Pigeonhole count of the good names.** Since the join cells are pairwise `μ`-a.e. disjoint, the
sum of the measures of the good cells equals the measure of their union, which is at most `1`; as
each good cell has measure `≥ exp(−N·R)`, the number of good names is at most `exp(N·R)`.

This is the elementary half of the AEP covering bound: it holds **unconditionally** (no SMB, no
ergodicity), for *any* rate `R`. The covering half (that the good names *cover* most of the space)
is the SMB upper bound, parameterized separately. -/
theorem card_goodNames_le_exp (R : ℝ) :
    ((goodNames hT P N R).card : ℝ) ≤ Real.exp (N * R) := by
  classical
  -- Total mass of the good cells: sum equals the measure of their (a.e.-disjoint) union, hence ≤ 1.
  have hdisj : (↑(goodNames hT P N R) : Set (Fin N → ι)).Pairwise
      (AEDisjoint μ on (ksJoin hT P N).cells) := fun g _ g' _ hgg' =>
    (ksJoin hT P N).aedisjoint hgg'
  have hmeas : ∀ g ∈ goodNames hT P N R, NullMeasurableSet ((ksJoin hT P N).cells g) μ :=
    fun g _ => ((ksJoin hT P N).measurable g).nullMeasurableSet
  have hsum : ∑ g ∈ goodNames hT P N R, μ ((ksJoin hT P N).cells g)
      = μ (⋃ g ∈ goodNames hT P N R, (ksJoin hT P N).cells g) :=
    (measure_biUnion_finset₀ hdisj hmeas).symm
  have htotal : ∑ g ∈ goodNames hT P N R, μ ((ksJoin hT P N).cells g) ≤ 1 := by
    rw [hsum]; exact le_trans (measure_mono (Set.subset_univ _)) (by rw [measure_univ])
  -- Each good cell contributes ≥ exp(−N R), so card · exp(−N R) ≤ ∑ ≤ 1 in ℝ≥0∞.
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(N * R))) with hc
  have hlow : (goodNames hT P N R).card • c
      ≤ ∑ g ∈ goodNames hT P N R, μ ((ksJoin hT P N).cells g) := by
    rw [← Finset.sum_const]
    refine Finset.sum_le_sum fun g hg => ?_
    exact (mem_goodNames hT P N).mp hg
  have hcard_le : (goodNames hT P N R).card • c ≤ 1 := le_trans hlow htotal
  -- Move to ℝ: card · exp(−N R) ≤ 1, then card ≤ exp(N R).
  rw [nsmul_eq_mul] at hcard_le
  have hcR : c = ENNReal.ofReal (Real.exp (-(N * R))) := hc
  have hcard_le' : (goodNames hT P N R).card * Real.exp (-(N * R)) ≤ 1 := by
    have h := (ENNReal.toReal_le_toReal (by
        rw [hcR]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      (by simp)).mpr hcard_le
    rwa [ENNReal.toReal_mul, hcR, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_natCast, ENNReal.toReal_one] at h
  -- exp(−N R) > 0, so card ≤ (exp(−N R))⁻¹ = exp(N R).
  have hpos : (0 : ℝ) < Real.exp (-(N * R)) := Real.exp_pos _
  have hexpinv : (Real.exp (-(N * R)))⁻¹ = Real.exp (N * R) := by
    rw [← Real.exp_neg, neg_neg]
  calc ((goodNames hT P N R).card : ℝ)
      = (goodNames hT P N R).card * Real.exp (-(N * R)) * (Real.exp (-(N * R)))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
    _ ≤ 1 * (Real.exp (-(N * R)))⁻¹ := by gcongr
    _ = (Real.exp (-(N * R)))⁻¹ := one_mul _
    _ = Real.exp (N * R) := hexpinv

end Pigeonhole

section Covering

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (N : ℕ)

omit [IsProbabilityMeasure μ] in
/-- The set of points lying in a **null** rank-`N` cell. It is `μ`-null: it is contained in the
finite union of the null join-cells, each of measure `0`. This is the negligible part on which the
information function `iₙ(x) = -log μ(atomₙ(x))` is the junk value `-log 0 = 0` and so cannot witness
good-name membership. -/
lemma measure_nullAtom_eq_zero :
    μ {x | (μ (atomOf hT P N x)) = 0} = 0 := by
  classical
  -- A point with null atom lies in the union of the null cells.
  refine measure_mono_null (t := ⋃ g ∈ {g : Fin N → ι | μ ((ksJoin hT P N).cells g) = 0},
      (ksJoin hT P N).cells g) (fun x hx => ?_) ?_
  · rw [Set.mem_setOf_eq, atomOf_eq] at hx
    exact Set.mem_biUnion (by simpa using hx) (mem_atomOf hT P N x)
  · refine (measure_biUnion_null_iff (Set.to_countable _)).mpr ?_
    intro g hg
    exact hg

/-- **Covering content of the good names (unconditional).** The union of the good rank-`N` cells
covers at least the set `{x | (1/N)·infoFunₙ(x) ≤ R}` of points whose `N`-name information rate is
at most `R`: such a point's own atom has measure `≥ exp(−N·R)`, so its name is good and it lies in
the corresponding good cell. The only exception is the `μ`-null set of points sitting in a null
cell (where `infoFunₙ = -log 0 = 0` is a junk value), which is absorbed by
`measure_nullAtom_eq_zero`.

This is the *covering half's* unconditional content: it reduces the covering bound
`μ (⋃ good cells) ≥ 1 − ε` to the in-measure SMB upper bound
`μ {x | (1/N)·infoFunₙ > R} ≤ ε`. -/
theorem measure_iUnion_goodNames_ge (hN : 1 ≤ N) (R : ℝ) :
    μ {x | (1 / (N : ℝ)) * infoFun hT P N x ≤ R}
      ≤ μ (⋃ g ∈ goodNames hT P N R, (ksJoin hT P N).cells g) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- Off the null-atom set, `(1/N) infoFunₙ ≤ R` forces the name into `goodNames`.
  have hsub : {x | (1 / (N : ℝ)) * infoFun hT P N x ≤ R}
      ⊆ (⋃ g ∈ goodNames hT P N R, (ksJoin hT P N).cells g)
          ∪ {x | (μ (atomOf hT P N x)) = 0} := by
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    by_cases hatom : μ (atomOf hT P N x) = 0
    · exact Or.inr hatom
    · -- positive atom: derive `exp(−N R) ≤ (μ atom).toReal`, hence the name is good.
      refine Or.inl ?_
      set p : ℝ := (μ (atomOf hT P N x)).toReal with hp
      have hppos : 0 < p := by
        rw [hp, ENNReal.toReal_pos_iff]
        exact ⟨pos_iff_ne_zero.mpr hatom, measure_lt_top μ _⟩
      -- `infoFunₙ x = -log p`, and `(1/N)(-log p) ≤ R ⟹ -log p ≤ N R ⟹ log p ≥ -N R`.
      have hinfo : infoFun hT P N x = -Real.log p := rfl
      rw [hinfo] at hx
      have hlog : -Real.log p ≤ (N : ℝ) * R := by
        rw [one_div, inv_mul_le_iff₀ hNpos] at hx; linarith [hx]
      have hge : Real.exp (-(N * R)) ≤ p := by
        have h1 : -(N : ℝ) * R ≤ Real.log p := by linarith [hlog]
        calc Real.exp (-(N * R)) = Real.exp (-(N : ℝ) * R) := by ring_nf
          _ ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr h1
          _ = p := Real.exp_log hppos
      -- The name `itinerary x` is good and `x` lies in its cell.
      have hmem : itinerary hT P N x ∈ goodNames hT P N R := by
        rw [mem_goodNames]
        have hmurw : μ ((ksJoin hT P N).cells (itinerary hT P N x)) = ENNReal.ofReal p := by
          rw [hp, ← atomOf_eq, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        rw [hmurw]
        exact ENNReal.ofReal_le_ofReal hge
      exact Set.mem_biUnion hmem (atomOf_eq hT P N x ▸ mem_atomOf hT P N x)
  calc μ {x | (1 / (N : ℝ)) * infoFun hT P N x ≤ R}
      ≤ μ ((⋃ g ∈ goodNames hT P N R, (ksJoin hT P N).cells g)
            ∪ {x | (μ (atomOf hT P N x)) = 0}) := measure_mono hsub
    _ ≤ μ (⋃ g ∈ goodNames hT P N R, (ksJoin hT P N).cells g)
            + μ {x | (μ (atomOf hT P N x)) = 0} := measure_union_le _ _
    _ = μ (⋃ g ∈ goodNames hT P N R, (ksJoin hT P N).cells g) := by
        rw [measure_nullAtom_eq_zero hT P N, add_zero]

end Covering

section CoveringBound

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)

/-- **The in-measure Shannon–McMillan–Breiman upper bound** at the sharp rate
`h = ksEntropyPartition hT P` — the single parameterized analytic input the covering bound needs.
It asserts that, for every `ε > 0`, the measure of the set of points whose `N`-name information rate
exceeds `h + ε` tends to `0`:
`μ {x | h + ε < (1/N)·infoFunₙ(x)} → 0`.

This is *strictly weaker* than the pointwise a.e. SMB convergence `(1/N)·infoFunₙ → h` (it is the
"in measure / McMillan `L¹`" form of the **upper** half only), and it is the exact statement the
covering bound consumes. It is the documented residual of `ErgodicTheory.Krieger.SMBSharp`: the
integral-level rate identity `ksEntropyPartition_eq_condEntropy_iSup` and the Fekete rate
`tendsto_ksEntropySeq` are already proved here; what remains is the *concentration* (in measure) of
`(1/N)·infoFunₙ` around its mean `ksEntropySeq N / N → h`.

See the module note below for the cheapest known route to discharge it (the martingale-free
block-product competing-measure bound fed to the engine
`ErgodicTheory.Krieger.ae_forall_eventually_div_infoFun_le`, which gives the *sharp* a.e. upper bound
`limsup (1/N)·infoFunₙ ≤ h` and hence this in-measure form by dominated convergence on the
bounded-below indicator). -/
def UpperSMBInMeasure : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N : ℕ =>
      μ {x | ksEntropyPartition hT P + ε < (1 / (N : ℝ)) * infoFun hT P N x}) atTop (𝓝 0)

/-- **The C3-facing name-count / AEP covering bound.** Assume the in-measure SMB upper bound
`UpperSMBInMeasure`. Then for every `ε > 0` and all sufficiently large rank `N`, there is a Finset
`S` of rank-`N` names (codes `g : Fin N → ι`) such that

* the union of the corresponding join-cells covers all but `ε` of the space:
  `1 − ENNReal.ofReal ε ≤ μ (⋃ g ∈ S, cell g)`, and
* the number of names is at most `⌊exp(N·(h+ε))⌋`:
  `S.card ≤ ⌊exp(N·(h+ε))⌋`,

where `h = ksEntropyPartition hT P`. The Finset is the **good names** `goodNames hT P N (h+ε)`: the
card bound is the unconditional pigeonhole `card_goodNames_le_exp`, and the covering bound combines
the unconditional covering content `measure_iUnion_goodNames_ge` (good cells cover
`{(1/N)·infoFunₙ ≤ h+ε}`) with `UpperSMBInMeasure` (the complement has measure `< ε`, eventually).

This is exactly the object the coding construction (C3) consumes: with `Real.log k > h`, picking
`ε` small makes `⌊exp(N·(h+ε))⌋ < kᴺ`, so the `S` names embed into `Fin k`-codes, covering `1 − ε`
of the space — the combinatorial seed of the `Fin k`-valued generator. -/
theorem exists_cover_names_card_le [Nonempty ι] (hsmb : UpperSMBInMeasure hT P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset (Fin N → ι),
      1 - ENNReal.ofReal ε ≤ μ (⋃ g ∈ S, (ksJoin hT P N).cells g)
        ∧ (S.card : ℝ) ≤ ⌊Real.exp (N * (ksEntropyPartition hT P + ε))⌋ := by
  classical
  set h := ksEntropyPartition hT P with hh
  -- From the in-measure SMB upper bound: eventually `μ {(1/N) infoFunₙ > h + ε} < ε`.
  have hsmb' := hsmb ε hε
  rw [ENNReal.tendsto_atTop_zero] at hsmb'
  obtain ⟨N₀, hN₀⟩ := hsmb' (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  filter_upwards [eventually_ge_atTop (max 1 N₀)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_right _ _) hN
  refine ⟨goodNames hT P N (h + ε), ?_, ?_⟩
  · -- Covering bound: `1 − ε ≤ μ {(1/N) infoFunₙ ≤ h+ε} ≤ μ (⋃ good cells)`.
    -- The complement of the bad-rate set has measure `≥ 1 − ε` (eventually).
    have hbad : μ {x | h + ε < (1 / (N : ℝ)) * infoFun hT P N x} ≤ ENNReal.ofReal ε :=
      hN₀ N hNN₀
    -- The good-rate set and the bad-rate set partition the space.
    have hmeasbad : MeasurableSet {x | h + ε < (1 / (N : ℝ)) * infoFun hT P N x} := by
      refine measurableSet_lt measurable_const ?_
      exact (measurable_const.mul (measurable_infoFun hT P N))
    have hcompl : {x | (1 / (N : ℝ)) * infoFun hT P N x ≤ h + ε}
        = {x | h + ε < (1 / (N : ℝ)) * infoFun hT P N x}ᶜ := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    have hgoodmeas : 1 - ENNReal.ofReal ε
        ≤ μ {x | (1 / (N : ℝ)) * infoFun hT P N x ≤ h + ε} := by
      rw [hcompl, measure_compl hmeasbad (measure_ne_top μ _), measure_univ]
      exact tsub_le_tsub_left hbad 1
    -- `1 − ε ≤ 1 − ofReal ε ≤ μ {good rate} ≤ μ (⋃ good cells)`.
    calc (1 : ℝ≥0∞) - ENNReal.ofReal ε
        ≤ μ {x | (1 / (N : ℝ)) * infoFun hT P N x ≤ h + ε} := hgoodmeas
      _ ≤ μ (⋃ g ∈ goodNames hT P N (h + ε), (ksJoin hT P N).cells g) :=
          measure_iUnion_goodNames_ge hT P N hN1 (h + ε)
  · -- Card bound: pigeonhole gives `#good ≤ exp(N(h+ε))`, hence `≤ ⌊exp(...)⌋`.
    have hcard : ((goodNames hT P N (h + ε)).card : ℝ) ≤ Real.exp (N * (h + ε)) :=
      card_goodNames_le_exp hT P N (h + ε)
    -- As integers: `(card : ℤ) ≤ ⌊exp(...)⌋`; then cast back to ℝ.
    have hint : ((goodNames hT P N (h + ε)).card : ℤ)
        ≤ ⌊Real.exp ((N : ℝ) * (h + ε))⌋ := by
      rw [Int.le_floor]; push_cast; exact hcard
    calc ((goodNames hT P N (h + ε)).card : ℝ)
        = (((goodNames hT P N (h + ε)).card : ℤ) : ℝ) := by push_cast; ring
      _ ≤ ((⌊Real.exp ((N : ℝ) * (h + ε))⌋ : ℤ) : ℝ) := by exact_mod_cast hint

end CoveringBound

/-! ### The minimal SMB input and the route to discharge `UpperSMBInMeasure`

Everything above is **unconditional** except the single hypothesis `UpperSMBInMeasure`, the
**in-measure Shannon–McMillan–Breiman upper bound** at the sharp rate `h = ksEntropyPartition hT P`:
`∀ ε > 0, μ {x | (1/N)·infoFunₙ(x) > h+ε} → 0`. This is the *exact* analytic input the AEP covering
bound needs — strictly weaker than the pointwise a.e. SMB (`(1/N)·infoFunₙ → h`), being the upper
half only and *in measure* (McMillan, not Breiman). This hypothesis is now **proved**:
`upperSMBInMeasure_of_ergodic` (`ErgodicTheory.Krieger.UpperSMB`) supplies it for every ergodic `T`,
from the full pointwise SMB `ae_tendsto_div_infoFun_self`. The two routes below record the
analytic content; Route 2 is the one the repository took.

**Why the crude bound and plain Markov are not enough.**
`ErgodicTheory.Krieger.ae_limsup_div_infoFun_le_log_card` (Birkhoff-free, Markov + Borel–Cantelli) gives
only the rate `log (card ι) ≥ h` — the integrand `exp(infoFunₙ − N·R)` of the engine is *fixed*, so
the uniform competing measure is hard-wired into it and the rate cannot drop below `log (card ι)` by
that instantiation alone. Plain Markov on `infoFunₙ` is also too weak: `∫ (1/N)·infoFunₙ =
ksEntropySeq N / N → h`, so `μ {(1/N)·infoFunₙ > h+ε} ≤ (ksEntropySeq N / N)/(h+ε) → h/(h+ε)`, a
positive constant. The content of the upper bound is the *concentration* of `(1/N)·infoFunₙ` about
its mean `h` — genuine SMB content, not bookkeeping.

**Route 1 — block / likelihood-ratio (engine + Birkhoff, no martingale).** Not the route taken.
Feed the engine `ErgodicTheory.Krieger.ae_forall_eventually_div_log_le` (the `∫⁻ gₙ ≤ 1` form) the
**likelihood ratio** `gₙ(x) = qₙ(name x) / μ(cellₙ(x))`, where `qₙ` is a competing sub-probability
on the `N`-names, *not* the fixed `exp(infoFunₙ − N·R)`. For block length `m`, take `qₙ(name) =
∏_{blocks b} μ(P_m-cell of block b)` (the `m`-block product). Then `∫⁻ gₙ = ∑_names qₙ ≤ 1`
automatically, and the engine gives, a.e., `limsup (1/N)·log gₙ ≤ 0`, i.e.
`limsup (1/N)·(infoFunₙ + log qₙ) ≤ 0`, i.e.
`limsup (1/N)·infoFunₙ ≤ limsup −(1/N) log qₙ = limsup (1/N) ∑_{blocks} I_{P_m}(T^{jm}·)`.
The right side is a **Birkhoff average of `I_{P_m}` along `T^m`**, which converges a.e. (ergodic
case) to `(1/m)·∫ I_{P_m} = (1/m)·H(P_m) = ksEntropySeq m / m`
(`ErgodicTheory.Entropy.tendsto_birkhoffAverage_ae_integral` + `integral_infoFun_eq`). Letting `m → ∞`
with `ksEntropySeq m / m → h` (`ErgodicTheory.Entropy.tendsto_ksEntropySeq`) yields the **sharp a.e.
upper bound** `limsup (1/N)·infoFunₙ ≤ h`, hence `UpperSMBInMeasure` (the a.e. limsup bound gives,
for each `ε`, `(1/N)·infoFunₙ ≤ h+ε` eventually a.e.; the bounded indicators
`𝟙{(1/N)·infoFunₙ > h+ε}` then `→ 0` in `L¹` by dominated convergence — i.e. convergence in measure
to `0`).

This route needs **ergodicity / the Birkhoff ergodic theorem** (already in the repo) but **no
martingale, no conditional information function, no Chung `L¹` maximal domination**. For this
(untaken) alternative the work would be (a) the `m`-block product likelihood ratio and its
`∫⁻ ≤ 1` (finite measure algebra on the append factorization `ksJoinCells_append`, repo
`KSEntropy.lean`), and (b) the Birkhoff evaluation of `(1/N) ∑_{blocks} I_{P_m}∘T^{jm}` — an
`≈100–150`-line development. This is the **minimal** such route, since only the upper half *in
measure* is needed.

**Route 2 — full pointwise SMB via `SMBSharp` (heavier, and the route taken).** The now-proved `R5`
of `ErgodicTheory.Krieger.SMBSharp` (Chung's `L¹` maximal-function domination, proved on top of the
telescoping there) gives the full a.e. SMB `(1/N)·infoFunₙ → h`, from which `UpperSMBInMeasure` is
immediate (`ErgodicTheory.Krieger.UpperSMB.upperSMBInMeasure_of_ergodic`). Route 1 would be lighter for
*this* corollary because it avoids the martingale entirely; both require the ergodic theorem.

**Minimal analytic input named.** Either (Route 1) the `m`-block product partition-function identity
`∫⁻ (∏_{blocks} μ(P_m-cell)) / μ(cellₙ) ∂μ ≤ 1` plus a.e. Birkhoff convergence of the block average
of `I_{P_m}`; or (Route 2) Chung's `g* = ⨆ₖ gₖ ∈ L¹`. Both reduce to the already-proved
`tendsto_ksEntropySeq` for the final `m → ∞` (Route 1) / `k → ∞` (Route 2) passage. -/

end ErgodicTheory.Krieger
