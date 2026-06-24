/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Krieger.SMBLeaves
import Oseledets.Krieger.NameCountSharp
import Oseledets.Entropy.CondGivenPartitionBridge

/-!
# The Breiman telescoping for the information function and the in-measure SMB upper bound

This file closes the analytic side of sub-problem A of the unconditional Krieger theorem
(issue #15): it discharges the `hbreiman` hypothesis of the pointwise Shannon–McMillan–Breiman
theorem (`Oseledets.Krieger.SMBLeaves.ae_tendsto_div_infoFun`) at the level of the *concrete*
information function `infoFun` of `InfoFunction.lean`, and uses it to prove the in-measure SMB
upper bound `UpperSMBInMeasure` (`NameCountSharp.lean`) as an unconditional theorem for ergodic
transformations.

## The Breiman telescoping identity (and a sharp off-by-one)

The pointwise SMB machinery in `SMBLeaves` is parameterized by an abstract sequence `infoFun_n`
together with the **Breiman telescoping** hypothesis
`hbreiman : iₙ(x) = ∑_{j<n} g_{n−j}(Tʲx)` (with `g_k = condInfoFun 𝒞ₖ P` and
`𝒞ₖ = condLevelSigma`).  The convention used there indexes the summands by `n − j`, i.e. it
conditions on the σ-algebras `𝒞₁, …, 𝒞ₙ`.

For the *concrete* information function `infoFun` (the `-log μ(atom)` of `InfoFunction.lean`) the
**true** telescoping conditions on `𝒞₀, …, 𝒞ₙ₋₁` instead:
`infoFun_n(x) = ∑_{j<n} g_{n−1−j}(Tʲx)` (`infoFun_succ_ae` peels the first symbol: the first
symbol of an `n`-name, given the remaining `n−1` future symbols, conditions on the `(n−1)`-step
past `𝒞ₙ₋₁`; iterating gives the `n−1−j` index, with `𝒞₀ = ⊥` the trivial
σ-algebra contributing the raw partition information `-log μ(P-cell)`).  In particular at
`n = 1` the true identity is `infoFun₁(x) = -log μ(P-cell of x) = g₀(x)`, **not** `g₁(x)`.

So `hbreiman` with the `SMBLeaves` index `n − j` is *false* for `infoFun`.  We therefore do
**not** feed `infoFun` to `ae_tendsto_div_infoFun` directly.  Instead we feed it the
`SMBLeaves`-convention sum `Aₙ(x) = ∑_{j<n} g_{n−j}(Tʲx)` (for which `hbreiman` holds by
*reflexivity*), obtaining `(1/n)·Aₙ → h` a.e., and bridge to `infoFun` via the one-term edge
identity `infoFun_{n+1}(x) = Aₙ(x) + g₀(Tⁿx)` together with the orbital decay
`(1/n)·g₀(Tⁿx) → 0` (`ae_tendsto_orbit_div_atTop_zero`, valid since `g₀ ∈ L¹`).
This yields the pointwise SMB `(1/n)·infoFunₙ → h` for `infoFun`, hence the in-measure bound.

## Main results

* `Oseledets.Krieger.infoFun_succ_ae` — the one-step front-peel of the Breiman telescoping:
  `infoFun_{n+1}(x) = g_n(x) + infoFun_n(Tx)` a.e.
* `Oseledets.Krieger.ae_tendsto_div_infoFun_self` — the pointwise SMB for `infoFun`:
  `(1/n)·infoFunₙ(x) → h(P,T)` a.e. for ergodic `T`.
* `Oseledets.Krieger.upperSMBInMeasure_of_ergodic` — `UpperSMBInMeasure hT P` for ergodic `T`:
  discharges the in-measure SMB upper bound that `exists_cover_names_card_le` (C2) consumes.

## References

* L. Breiman, *The individual ergodic theorem of information theory*, Ann. Math. Statist.
  **28** (1957), 809–811.
* M. Einsiedler, E. Lindenstrauss, T. Ward, *Entropy in Ergodic Theory and Topological Dynamics*,
  Ch. 2 (SMB).
-/

open MeasureTheory Filter Topology Real Function ProbabilityTheory
open scoped ENNReal

namespace Oseledets.Krieger

open Oseledets.Entropy

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α]
  [StandardBorelSpace α] [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

section Bridge

/-! ### The kernel/measure bridge `condInfoFun(𝒞ₖ) = condInfoWeight Bₖ`

The conditional information *function* `condInfoFun (gen B) P y` (defined via the regular
conditional probability `condExpKernel μ (gen B) y (Pᵢ)`) agrees `μ`-a.e. with the conditional
information *weight* `condInfoWeight B P i₀ b` (defined via the elementary conditional
probability `μ(B_b ∩ P_{i₀})/μ(B_b)`), where `i₀` is the unique `P`-cell and `b` the unique
`B`-cell of `y`.  This is the per-step instance of the partition/σ-algebra bridge
(`condCandidate_ae_eq_condExp`, `condCandidate_ae_eq_on_cell`). -/

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)

/-- For a finite partition `B`, the `gen(B)`-conditional probability of a `P`-cell is a.e. the
elementary conditional probability: for `μ`-a.e. `y` lying in the `B`-cell `b`,
`(condExpKernel μ (gen B) y Pᵢ).toReal = μ(B_b ∩ Pᵢ)/μ(B_b)`. -/
lemma toReal_condExpKernel_generated_ae_eq {β : Type*} [Fintype β] (B : MeasurePartition μ β)
    (i : ι) (b : β) :
    (fun y => (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ B) y (P.cells i)).toReal)
      =ᵐ[μ.restrict (B.cells b)]
      fun _ => (μ (B.cells b ∩ P.cells i)).toReal / (μ (B.cells b)).toReal := by
  have hm : generatedSigmaAlgebra μ B ≤ mα := generatedSigmaAlgebra_le B
  -- kernel =ᵐ condExp =ᵐ candidate, then candidate is the cell-conditional value on `B_b`.
  have hker :
      (fun y => (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ B) y (P.cells i)).toReal)
      =ᵐ[μ] fun y => condCandidate B (P.cells i) y := by
    have h1 := condExpKernel_ae_eq_condExp (μ := μ) (m := generatedSigmaAlgebra μ B) hm
      (P.measurable i)
    have h2 := (condCandidate_ae_eq_condExp B (P.measurable i)).symm
    filter_upwards [h1, h2] with y hy1 hy2
    rw [measureReal_def] at hy1
    rw [hy1, ← hy2]
  exact Filter.EventuallyEq.trans (ae_restrict_of_ae hker)
    (condCandidate_ae_eq_on_cell B (P.cells i) b)

end Bridge

section Telescope

variable (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)

/-- **The bridge, membership form.** For `μ`-a.e. `y`: whenever `y` lies in the unique `P`-cell
`i₀` and in the `Bₖ`-cell `b` (`Bₖ = (ksJoin hT P k).pullback hT`), the conditional info
function of `P` given the `k`-step past `𝒞ₖ = condLevelSigma hT P k` evaluates to the
conditional info weight `condInfoWeight Bₖ P i₀ b`. The conditioning σ-algebra `𝒞ₖ` is
exactly `generatedSigmaAlgebra μ Bₖ`, so the conditional probability of `Pᵢ₀` given `𝒞ₖ`
is a.e. the elementary conditional probability `μ(B_b ∩ Pᵢ₀)/μ(B_b)`
(`toReal_condExpKernel_generated_ae_eq`), and only the `i₀`-indicator of `condInfoFun` survives
at a point in a unique `P`-cell (`condInfoFun_eq_neg_log_of_mem_unique`). -/
lemma condInfoFun_eq_condInfoWeight_ae (k : ℕ) :
    ∀ᵐ y ∂μ, ∀ i₀ : ι, y ∈ P.cells i₀ →
      (∀ i', i' ≠ i₀ → y ∉ P.cells i') →
      ∀ b : Fin k → ι, y ∈ ((ksJoin hT P k).pullback hT).cells b →
        condInfoFun (𝒜 := condLevelSigma hT P k) P y
          = condInfoWeight ((ksJoin hT P k).pullback hT) P i₀ b := by
  classical
  set B : MeasurePartition μ (Fin k → ι) := (ksJoin hT P k).pullback hT with hB
  -- For each pair `(i₀, b)`, the kernel value is a.e. the elementary conditional probability on
  -- the cell `B_b`. Promote each restricted statement to an unrestricted membership-guarded one.
  have hpair : ∀ i₀ : ι, ∀ b : Fin k → ι,
      ∀ᵐ y ∂μ, y ∈ B.cells b →
        (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ B) y (P.cells i₀)).toReal
          = (μ (B.cells b ∩ P.cells i₀)).toReal / (μ (B.cells b)).toReal := by
    intro i₀ b
    have h := toReal_condExpKernel_generated_ae_eq P B i₀ b
    rw [Filter.EventuallyEq, ae_restrict_iff' (B.measurable b)] at h
    exact h
  -- Combine the (finitely many) pair statements with `P`-cell uniqueness.
  have hall : ∀ᵐ y ∂μ, ∀ i₀ : ι, ∀ b : Fin k → ι, y ∈ B.cells b →
      (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ B) y (P.cells i₀)).toReal
        = (μ (B.cells b ∩ P.cells i₀)).toReal / (μ (B.cells b)).toReal := by
    rw [ae_all_iff]; intro i₀; rw [ae_all_iff]; intro b; exact hpair i₀ b
  filter_upwards [hall] with y hy i₀ hyi₀ hyuniq b hyb
  -- `condInfoFun` collapses to `-log` of the kernel value at the unique `P`-cell `i₀`.
  rw [condInfoFun_eq_neg_log_of_mem_unique (𝒜 := condLevelSigma hT P k) P hyi₀ hyuniq]
  -- The kernel value equals the elementary conditional probability on `B_b`.
  rw [condInfoWeight, show condLevelSigma hT P k = generatedSigmaAlgebra μ B from rfl,
    hy i₀ b hyb]

omit [StandardBorelSpace α] [IsProbabilityMeasure μ] in
/-- A predicate that holds `μ`-a.e. holds `μ`-a.e. along the whole forward orbit. -/
lemma ae_forall_orbit (hT : MeasurePreserving T μ μ) {p : α → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, ∀ j : ℕ, p (T^[j] x) := by
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (T^[j]) μ μ := MeasurePreserving.iterate hT j
  exact hmp.quasiMeasurePreserving.tendsto_ae hp

/-- **One-step front-peel of the Breiman telescoping for `infoFun`.** For each `n`, `μ`-a.e. `x`,
the rank-`(n+1)` information function splits as the conditional information of the first symbol
given the `n`-step past plus the rank-`n` information of the shifted point:
`infoFun_{n+1}(x) = condInfoFun(𝒞ₙ)(x) + infoFun_n(Tx)`.

The proof peels the first symbol of the rank-`(n+1)` itinerary using the cell cons-factorization
(`ksJoinCells_cons`) and the measure-algebra one-step identity `infoWeight_succ_eq` (its positivity
hypothesis holds a.e., off the null set of points in a null `(n+1)`-cell,
`measure_nullAtom_eq_zero`); the conditional weight is identified with `condInfoFun(𝒞ₙ)` by the
bridge `condInfoFun_eq_condInfoWeight_ae`, and the shifted rank-`n` weight with `infoFun_n(Tx)` by
the a.e. uniqueness of the `n`-name of `Tx` (`ae_mem_unique_cell` for the `n`-fold join, transferred
along `T`). -/
lemma infoFun_succ_ae (n : ℕ) :
    ∀ᵐ x ∂μ, infoFun hT P (n + 1) x
      = condInfoFun (𝒜 := condLevelSigma hT P n) P x + infoFun hT P n (T x) := by
  classical
  -- a.e. ingredients.
  -- (1) `x` is in a unique `P`-cell.
  have huniqP := ae_mem_unique_cell P
  -- (2) the rank-`(n+1)` atom of `x` is non-null.
  have hposatom : ∀ᵐ x ∂μ, μ (atomOf hT P (n + 1) x) ≠ 0 := by
    have h := measure_nullAtom_eq_zero hT P (n + 1)
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact h
  -- (3) the bridge.
  have hbridge := condInfoFun_eq_condInfoWeight_ae hT P n
  -- (4) a.e. `Tx` is in a unique `n`-name (cell of the `n`-fold join).
  have huniqJoin : ∀ᵐ x ∂μ, ∀ f : Fin n → ι, T x ∈ (ksJoin hT P n).cells f →
      ∀ f', f' ≠ f → T x ∉ (ksJoin hT P n).cells f' := by
    have h := ae_mem_unique_cell (ksJoin hT P n)
    exact hT.quasiMeasurePreserving.tendsto_ae h
  filter_upwards [huniqP, hposatom, hbridge, huniqJoin]
    with x hxuniq hxpos hxbridge hxjoinuniq
  -- Decompose the rank-`(n+1)` itinerary as `cons i₀ g`.
  set f : Fin (n + 1) → ι := itinerary hT P (n + 1) x with hf
  set i₀ : ι := f 0 with hi₀
  set g : Fin n → ι := Fin.tail f with hg
  have hcons : Fin.cons i₀ g = f := Fin.cons_self_tail f
  -- `infoFun (n+1) x = infoWeight (n+1) f`.
  have hinfoeq : infoFun hT P (n + 1) x = infoWeight hT P (n + 1) (Fin.cons i₀ g) := by
    rw [infoFun_eq_infoWeight_itinerary, ← hf, hcons]
  -- The atom of `x` is `cell_{n+1}(f) = P.cells i₀ ∩ T⁻¹ cell_n(g)`.
  have hcelleq : (ksJoin hT P (n + 1)).cells f
      = P.cells i₀ ∩ T ⁻¹' (ksJoin hT P n).cells g := by
    rw [← hcons]; exact ksJoinCells_cons hT P n i₀ g
  -- a.e. positivity of the `(n+1)`-cell from the non-null atom.
  have hpos : μ (P.cells i₀ ∩ T ⁻¹' (ksJoin hT P n).cells g) ≠ 0 := by
    rw [← hcelleq, ← atomOf_eq hT P (n + 1) x]
    exact hxpos
  -- one-step measure-algebra factorization.
  have hsplit : infoWeight hT P (n + 1) (Fin.cons i₀ g)
      = infoWeight hT P n g + condInfoWeight ((ksJoin hT P n).pullback hT) P i₀ g :=
    infoWeight_succ_eq hT P n i₀ g hpos
  -- The point `x` is in `P.cells i₀` (it lies in its `(n+1)`-atom).
  have hxmem : x ∈ atomOf hT P (n + 1) x := mem_atomOf hT P (n + 1) x
  have hxmemcell : x ∈ (ksJoin hT P (n + 1)).cells f := by rw [atomOf_eq] at hxmem; exact hxmem
  have hxi₀ : x ∈ P.cells i₀ := by
    have := hxmemcell; rw [hcelleq] at this; exact this.1
  have hxTg : T x ∈ (ksJoin hT P n).cells g := by
    have := hxmemcell; rw [hcelleq] at this
    exact this.2
  -- `x` is in the `Bₙ`-cell `g`: `Bₙ.cells g = T⁻¹ cell_n(g)`.
  have hxBg : x ∈ ((ksJoin hT P n).pullback hT).cells g := by
    rw [MeasurePartition.pullback_cells]; exact hxTg
  -- Bridge: `condInfoWeight Bₙ P i₀ g = condInfoFun(𝒞ₙ)(x)`.
  have hbr : condInfoWeight ((ksJoin hT P n).pullback hT) P i₀ g
      = condInfoFun (𝒜 := condLevelSigma hT P n) P x :=
    (hxbridge i₀ hxi₀ (hxuniq i₀ hxi₀) g hxBg).symm
  -- The shifted rank-`n` weight `infoWeight n g = infoFun n (Tx)`: both are `-log μ(cell_n)`,
  -- and `g` is the unique `n`-name of `Tx` (a.e.), so `g = itinerary n (Tx)`.
  have hgname : g = itinerary hT P n (T x) := by
    have hmem₂ : T x ∈ (ksJoin hT P n).cells (itinerary hT P n (T x)) := by
      have := mem_atomOf hT P n (T x); rwa [atomOf_eq] at this
    by_contra hne
    exact hxjoinuniq g hxTg (itinerary hT P n (T x)) (Ne.symm hne) hmem₂
  have hweqg : infoWeight hT P n g = infoFun hT P n (T x) := by
    rw [hgname, ← infoFun_eq_infoWeight_itinerary]
  -- Assemble.
  rw [hinfoeq, hsplit, hweqg, hbr, add_comm]

/-- The `SMBLeaves`-convention Breiman partial sum `Aₙ(x) = ∑_{j<n} g_{n−j}(Tʲx)`
(`g_k = condInfoFun 𝒞ₖ P`), the exact object fed to `ae_tendsto_div_infoFun`. -/
noncomputable def breimanSum (n : ℕ) (x : α) : ℝ :=
  ∑ j ∈ Finset.range n,
    condInfoFun (𝒜 := condLevelSigma hT P (n - j)) P (T^[j] x)

/-- The one-step recursion of the partial sum: `A_{n+1}(x) = g_{n+1}(x) + A_n(Tx)`.  Peeling the
`j = 0` summand (`= g_{n+1}(x)`) and reindexing the rest `j ↦ j+1` along the orbit. -/
lemma breimanSum_succ (n : ℕ) (x : α) :
    breimanSum hT P (n + 1) x
      = condInfoFun (𝒜 := condLevelSigma hT P (n + 1)) P x + breimanSum hT P n (T x) := by
  -- The reindexed tail `∑_{j<n} g_{(n+1)-(j+1)}(T^{j+1}x) = ∑_{j<n} g_{n-j}(T^j(Tx))`.
  have htail : (∑ j ∈ Finset.range n,
        condInfoFun (𝒜 := condLevelSigma hT P (n + 1 - (j + 1))) P (T^[j + 1] x))
      = breimanSum hT P n (T x) := by
    rw [breimanSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + 1 - (j + 1) = n - j by omega, Function.iterate_succ_apply]
  rw [breimanSum, Finset.sum_range_succ', htail, add_comm]
  simp only [Nat.sub_zero, Function.iterate_zero, id_eq]

/-- **The Breiman telescoping for `infoFun` (edge form).** For `μ`-a.e. `x`, for all `j, n`,
`infoFun_{n+1}(Tʲx) = Aₙ(Tʲx) + g₀(T^{n+j}x)`, where `Aₙ` is the `SMBLeaves`-convention partial
sum and `g₀ = condInfoFun 𝒞₀ P` is the raw partition information (`𝒞₀` trivial).  This is the
true Breiman identity `infoFun_{n+1}(y) = ∑_{j≤n} g_{n−j}(Tʲy)`, one summand longer than `Aₙ`.

Proved by induction on `n`, with `j` universally quantified so that the induction hypothesis
applies at the shifted point `Tʲ⁺¹x = Tʲ(Tx)`: the one-step front-peel `infoFun_succ_ae` holds
a.e. along the orbit, and the partial-sum recursion `breimanSum_succ` folds the peeled symbol. -/
lemma infoFun_eq_breimanSum_add_edge :
    ∀ᵐ x ∂μ, ∀ j n : ℕ, infoFun hT P (n + 1) (T^[j] x)
      = breimanSum hT P n (T^[j] x)
        + condInfoFun (𝒜 := condLevelSigma hT P 0) P (T^[n + j] x) := by
  -- The one-step front-peel holds a.e. along the whole orbit, uniformly in the level.
  have hsucc : ∀ᵐ x ∂μ, ∀ m : ℕ, infoFun hT P (m + 1) x
      = condInfoFun (𝒜 := condLevelSigma hT P m) P x + infoFun hT P m (T x) :=
    ae_all_iff.2 (fun m => infoFun_succ_ae hT P m)
  have horbit : ∀ᵐ x ∂μ, ∀ j : ℕ, ∀ m : ℕ, infoFun hT P (m + 1) (T^[j] x)
      = condInfoFun (𝒜 := condLevelSigma hT P m) P (T^[j] x)
        + infoFun hT P m (T^[j + 1] x) := by
    have := ae_forall_orbit hT hsucc
    filter_upwards [this] with x hx j m
    have := hx j m
    rwa [← Function.iterate_succ_apply' T j x] at this
  filter_upwards [horbit] with x hx
  intro j n
  induction n generalizing j with
  | zero =>
    -- `infoFun 1 (Tʲx) = g₀(Tʲx) + infoFun 0 (Tʲ⁺¹x)`; `infoFun 0 = 0`, `A₀ = 0`.
    have h0 := hx j 0
    rw [h0]
    have hinfo0 : infoFun hT P 0 (T^[j + 1] x) = 0 := by
      rw [infoFun, atomOf, ksJoin_cells, ksJoinCells_apply, Set.iInter_of_empty, measure_univ,
        ENNReal.toReal_one, Real.log_one, neg_zero]
    rw [hinfo0, breimanSum]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add]
  | succ n ih =>
    -- `infoFun (n+2)(Tʲx) = g_{n+1}(Tʲx) + infoFun (n+1)(Tʲ⁺¹x)`; apply `ih` at `j+1`.
    have hstep := hx j (n + 1)
    -- Unfold the RHS `A_{n+1}(Tʲx) = g_{n+1}(Tʲx) + A_n(Tʲ⁺¹x)` and match exponents.
    have hAsucc : breimanSum hT P (n + 1) (T^[j] x)
        = condInfoFun (𝒜 := condLevelSigma hT P (n + 1)) P (T^[j] x)
          + breimanSum hT P n (T^[j + 1] x) := by
      rw [breimanSum_succ hT P n (T^[j] x), Function.iterate_succ_apply']
    have hexp : T^[n + (j + 1)] x = T^[n + 1 + j] x := by rw [show n + (j + 1) = n + 1 + j by omega]
    rw [hstep, ih (j + 1), hAsucc, hexp]
    ring

end Telescope

section SMB

variable [Nonempty ι]

/-- **Pointwise Shannon–McMillan–Breiman for the concrete information function.** For an ergodic
measure-preserving `T` and a finite partition `P`, the rank-`n` information averages
`(1/n)·infoFunₙ(x)` converge `μ`-a.e. to the Kolmogorov–Sinai entropy `h(P,T)`.

Combines the unconditional pointwise SMB for the `SMBLeaves`-convention partial sum
`Aₙ` (`ae_tendsto_div_infoFun` with `hbreiman` holding by reflexivity for `Aₙ = breimanSum`)
with the edge telescoping `infoFun_{n+1}(x) = Aₙ(x) + g₀(Tⁿx)`
(`infoFun_eq_breimanSum_add_edge`), the orbital decay `(1/n)·g₀(Tⁿx) → 0` (`g₀ ∈ L¹`,
`ae_tendsto_orbit_div_atTop_zero`), and an index shift `n ↦ n+1`. -/
theorem ae_tendsto_div_infoFun_self (herg : Ergodic T μ) (P : MeasurePartition μ ι) :
    ∀ᵐ x ∂μ, Tendsto (fun n => infoFun herg.toMeasurePreserving P n x / n) atTop
      (𝓝 (ksEntropyPartition herg.toMeasurePreserving P)) := by
  set hT := herg.toMeasurePreserving with hhT
  set h := ksEntropyPartition hT P with hh
  -- (1) `(1/n)·Aₙ(x) → h` a.e., from the parameterized SMB (`hbreiman` is reflexive).
  have hA : ∀ᵐ x ∂μ, Tendsto (fun n => breimanSum hT P n x / n) atTop (𝓝 h) :=
    ae_tendsto_div_infoFun herg P (breimanSum hT P) (Eventually.of_forall fun x n => rfl)
  -- (2) the edge telescoping `infoFun_{n+1}(x) = Aₙ(x) + g₀(Tⁿx)` (specialize `j = 0`).
  have hedge : ∀ᵐ x ∂μ, ∀ n : ℕ, infoFun hT P (n + 1) x
      = breimanSum hT P n x + condInfoFun (𝒜 := condLevelSigma hT P 0) P (T^[n] x) := by
    filter_upwards [infoFun_eq_breimanSum_add_edge hT P] with x hx n
    have := hx 0 n
    simpa only [Function.iterate_zero, id_eq, Nat.add_zero] using this
  -- (3) orbital decay of the edge term `g₀`.
  have hg0int : Integrable (condInfoFun (𝒜 := condLevelSigma hT P 0) P) μ :=
    integrable_condInfoFun (condLevelSigma_le hT P 0) P
  have hdecay : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * condInfoFun (𝒜 := condLevelSigma hT P 0) P (T^[n] x))
      atTop (𝓝 0) :=
    Oseledets.ae_tendsto_orbit_div_atTop_zero hT hg0int
  filter_upwards [hA, hedge, hdecay] with x hAx hedgex hdecayx
  -- The shifted sequence `(1/(n+1))·infoFun_{n+1}(x) → h`.
  have hshift : Tendsto (fun n : ℕ => infoFun hT P (n + 1) x / (n + 1)) atTop (𝓝 h) := by
    -- `(1/(n+1))·infoFun_{n+1} = (n/(n+1))·(Aₙ/n) + (1/(n+1))·g₀(Tⁿx)`.
    -- Build the limit as a sum of two convergent pieces.
    have hnn1 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop (1 : ℝ)
    -- The `A` piece: `(n/(n+1))·(Aₙ/n) → 1 * h = h`.
    have hApiece : Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1)) * (breimanSum hT P n x / n)) atTop
        (𝓝 (1 * h)) := hnn1.mul hAx
    rw [one_mul] at hApiece
    -- The `g₀` piece: `(1/(n+1))·g₀(Tⁿx) → 0`.
    have hgpiece : Tendsto
        (fun n : ℕ => ((n : ℝ) / (n + 1)) * ((n : ℝ)⁻¹
            * condInfoFun (𝒜 := condLevelSigma hT P 0) P (T^[n] x))) atTop (𝓝 (1 * 0)) :=
      hnn1.mul hdecayx
    rw [mul_zero] at hgpiece
    have hsum := hApiece.add hgpiece
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hne1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [hedgex n]
    field_simp
  -- Shift the index back: `(1/m)·infoFunₘ(x) → h` for `m = n+1`, hence on `atTop`.
  refine (tendsto_add_atTop_iff_nat (f := fun m => infoFun hT P m x / (m : ℝ)) 1).mp ?_
  refine hshift.congr fun n => ?_
  rw [Nat.cast_add, Nat.cast_one]

end SMB

section UpperBound

variable [Nonempty ι]

/-- **The in-measure SMB upper bound, unconditional for ergodic `T`.** This discharges the
hypothesis `UpperSMBInMeasure` that `exists_cover_names_card_le` (C2) and the symbolic code carry:
for every `ε > 0`, the measure of the deviation set `{x | h + ε < (1/N)·infoFunₙ(x)}` tends to `0`.

Immediate from the pointwise a.e. SMB `ae_tendsto_div_infoFun_self` and the implication
a.e.-convergence ⟹ in-measure vanishing of the deviation set
(`tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure`). -/
theorem upperSMBInMeasure_of_ergodic (herg : Ergodic T μ) (P : MeasurePartition μ ι) :
    UpperSMBInMeasure herg.toMeasurePreserving P := by
  set hT := herg.toMeasurePreserving with hhT
  set h := ksEntropyPartition hT P with hh
  intro ε hε
  set A : ℕ → Set α := fun N => {x | h + ε < (1 / (N : ℝ)) * infoFun hT P N x} with hA
  have hmeasSet : ∀ N, MeasurableSet (A N) := fun N =>
    measurableSet_lt measurable_const (measurable_const.mul (measurable_infoFun hT P N))
  -- a.e. convergence ⟹ for a.e. `x`, eventually `x ∉ Aₙ` (the limit deviation set is empty).
  have hlim : ∀ᵐ x ∂μ, ∀ᶠ N in atTop, (x ∈ A N ↔ x ∈ (∅ : Set α)) := by
    filter_upwards [ae_tendsto_div_infoFun_self herg P] with x hx
    rw [Metric.tendsto_atTop] at hx
    obtain ⟨N₀, hN₀⟩ := hx ε hε
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
    simp only [hA, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have hd := hN₀ N hNN₀
    rw [Real.dist_eq, abs_lt] at hd
    -- `infoFunₙ/N = (1/N)·infoFunₙ`, and `infoFunₙ/N < h + ε`.
    have heq : infoFun hT P N x / N = (1 / (N : ℝ)) * infoFun hT P N x := by
      rw [one_div, div_eq_inv_mul]
    rw [heq] at hd
    linarith [hd.2]
  have hconv := MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := μ) atTop (A := (∅ : Set α)) (As := A) MeasurableSet.empty hmeasSet hlim
  simpa only [measure_empty] using hconv

end UpperBound

end Oseledets.Krieger
