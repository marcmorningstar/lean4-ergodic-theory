/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Algebra.Group.End
import Oseledets.Entropy.Generator

/-!
# Two-sided ℤ-iterate plumbing for Krieger's finite generator theorem

Krieger's finite generator theorem is a statement about an **invertible** measure-preserving
transformation (an automorphism of a Lebesgue space): a system of finite Kolmogorov–Sinai
entropy `h(T) < log k` admits a generating partition into `k` cells. The classical generating
condition for an automorphism saturates the σ-algebra over **both** time directions,
`⨆_{n : ℤ} (T ^ n)⁻¹ σ(P) = full σ-algebra`, in contrast to the one-sided ℕ-version
`Oseledets.Entropy.IsGenerating` used by the (non-invertible-friendly) Kolmogorov–Sinai interface.

This file supplies the ℤ-iterate plumbing needed to even *state* the two-sided condition, and the
two-sided generating predicate `IsGeneratingTwoSided` itself (issue #15).

## Why a bespoke ℤ-iterate?

`Function.iterate` is `ℕ`-indexed, so `T^[n]` does not typecheck for `n : ℤ`; and `α ≃ᵐ α`
(`MeasurableEquiv`) carries no `Group`/`zpow` instance. We therefore represent an automorphism as a
`MeasurableEquiv e : α ≃ᵐ α` together with `MeasurePreserving (e : α → α) μ μ`, and define the
two-sided iterate `ziter e n` explicitly by forward iteration of `e` for `n ≥ 0` and forward
iteration of `e.symm` for `n < 0`. The group/cocycle law `ziter e (m + n) = ziter e m ∘ ziter e n`
is then transported from the genuine group `Equiv.Perm α = (α ≃ α)` via the bridge
`ziter_eq_perm_zpow`, identifying `ziter e n` with the `zpow` `(e.toEquiv) ^ n` of the underlying
permutation.

## Why two-sided (forward saturation provably fails)

For the canonical two-sided Bernoulli shift on `{0, 1}^ℤ` with the generating partition
`P = {coordinate 0 is 0, coordinate 0 is 1}`, the *forward* saturation
`⨆_{n : ℕ} (T ^ n)⁻¹ σ(P)` recovers only the σ-algebra of the **nonnegative** coordinates, which
is a strict sub-σ-algebra of the product σ-algebra (it cannot resolve any event depending on a
negative coordinate). The two-sided saturation `⨆_{n : ℤ}` is exactly what is required to recover
the full structure, and is the correct hypothesis for Krieger's theorem. The cheap inclusion
`forward one-sided ≤ two-sided` (`isGeneratingOneSided_le_twoSided`) records that the two-sided
condition is the weaker, correct one.

## Main definitions

* `Oseledets.Krieger.ziter`: the two-sided iterate `ziter e n : α → α` of an automorphism
  `e : α ≃ᵐ α`, equal to `(e : α → α)^[n]` for `n ≥ 0` and `(e.symm : α → α)^[k+1]` for
  `n = -(k+1)`.
* `Oseledets.Krieger.IsGeneratingTwoSided`: the two-sided generating predicate
  `⨆ n : ℤ, comap (ziter e n) σ(P) = mα` for Krieger's theorem.

## Main results

* `Oseledets.Krieger.ziter_eq_perm_zpow`: the bridge `ziter e n = ⇑(e.toEquiv ^ n)` to the group
  `zpow` of the underlying permutation.
* `Oseledets.Krieger.ziter_add`: the cocycle law `ziter e (m + n) = ziter e m ∘ ziter e n`.
* `Oseledets.Krieger.measurePreserving_ziter`: each two-sided iterate is measure preserving.
* `Oseledets.Krieger.measurable_ziter`: each two-sided iterate is measurable.
* `Oseledets.Krieger.isGeneratingOneSided_le_twoSided`: the forward one-sided saturation is `≤` the
  two-sided one (forward generation is *stronger* than two-sided generation).

## References

* Wolfgang Krieger, *On entropy and generators of measure-preserving transformations*, Trans. Amer.
  Math. Soc. **149** (1970), 453–464.
* Peter Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), §4.
-/

open MeasureTheory Function MeasurableSpace

namespace Oseledets.Krieger

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] {μ : Measure α}

/-- The **two-sided iterate** `ziter e n : α → α` of an automorphism `e : α ≃ᵐ α`. Since
`Function.iterate` is `ℕ`-indexed and `α ≃ᵐ α` has no `zpow`, the negative powers are spelled out
explicitly: for `n = Int.ofNat k ≥ 0` it is the forward iterate `(e : α → α)^[k]`, and for
`n = Int.negSucc k = -(k+1)` it is the forward iterate `(e.symm : α → α)^[k+1]` of the inverse. -/
noncomputable def ziter (e : α ≃ᵐ α) : ℤ → (α → α)
  | Int.ofNat k => (e : α → α)^[k]
  | Int.negSucc k => (e.symm : α → α)^[k + 1]

@[simp]
lemma ziter_ofNat (e : α ≃ᵐ α) (k : ℕ) : ziter e (Int.ofNat k) = (e : α → α)^[k] := rfl

@[simp]
lemma ziter_negSucc (e : α ≃ᵐ α) (k : ℕ) :
    ziter e (Int.negSucc k) = (e.symm : α → α)^[k + 1] := rfl

/-- `ziter e n` agrees with the forward iterate `(e : α → α)^[k]` on the nonnegative cast `(k : ℤ)`.
This is the `Int.ofNat` case in `↑k` spelling, useful for rewriting `ℕ`-indexed forward terms. -/
@[simp]
lemma ziter_natCast (e : α ≃ᵐ α) (k : ℕ) : ziter e (k : ℤ) = (e : α → α)^[k] := rfl

@[simp]
lemma ziter_zero (e : α ≃ᵐ α) : ziter e 0 = id := by
  simpa using ziter_natCast e 0

@[simp]
lemma ziter_one (e : α ≃ᵐ α) : ziter e 1 = (e : α → α) := by
  have : ziter e ((1 : ℕ) : ℤ) = (e : α → α)^[1] := ziter_natCast e 1
  simpa using this

@[simp]
lemma ziter_neg_one (e : α ≃ᵐ α) : ziter e (-1) = (e.symm : α → α) := by
  have : ziter e (Int.negSucc 0) = (e.symm : α → α)^[0 + 1] := ziter_negSucc e 0
  simpa using this

/-- **Bridge to the group `zpow`.** The two-sided iterate `ziter e n` is the underlying function of
the integer power `(e.toEquiv) ^ n` of the permutation `e.toEquiv : Equiv.Perm α`. Since
`Equiv.Perm α` is a genuine group, this transports `zpow`-laws (associativity, the cocycle law) to
`ziter`. Both signs are checked by `zpow_natCast` / `zpow_negSucc`, using
`Equiv.Perm.coe_pow`, `coe_toEquiv`, and `coe_toEquiv_symm`. -/
lemma ziter_eq_perm_zpow (e : α ≃ᵐ α) (n : ℤ) :
    ziter e n = ⇑((e.toEquiv : Equiv.Perm α) ^ n) := by
  cases n with
  | ofNat k =>
    rw [ziter_ofNat, Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow,
      MeasurableEquiv.coe_toEquiv]
  | negSucc k =>
    rw [ziter_negSucc, zpow_negSucc]
    -- `((e.toEquiv) ^ (k+1))⁻¹ = (e.toEquiv⁻¹) ^ (k+1)`, whose coercion iterates `e.symm`.
    rw [← inv_pow, Equiv.Perm.coe_pow]
    -- `⇑(e.toEquiv⁻¹) = ⇑(e.toEquiv.symm) = (e.symm : α → α)`.
    rw [Equiv.Perm.coe_inv, MeasurableEquiv.coe_toEquiv_symm]

/-- **The cocycle / group law.** `ziter e (m + n) = ziter e m ∘ ziter e n`. Transported from
`zpow_add` in the group `Equiv.Perm α` via the bridge `ziter_eq_perm_zpow`, with composition read
off `Equiv.Perm.coe_mul`. -/
lemma ziter_add (e : α ≃ᵐ α) (m n : ℤ) :
    ziter e (m + n) = ziter e m ∘ ziter e n := by
  rw [ziter_eq_perm_zpow, ziter_eq_perm_zpow, ziter_eq_perm_zpow, zpow_add, Equiv.Perm.coe_mul]

/-- The two-sided iterate at `-n` is a two-sided inverse of the iterate at `n`:
`ziter e n ∘ ziter e (-n) = id`. Immediate from the cocycle law and `ziter_zero`. -/
@[simp]
lemma ziter_comp_ziter_neg (e : α ≃ᵐ α) (n : ℤ) : ziter e n ∘ ziter e (-n) = id := by
  rw [← ziter_add, add_neg_cancel, ziter_zero]

/-- The two-sided iterate at `-n` is a left inverse of the iterate at `n`:
`ziter e (-n) ∘ ziter e n = id`. -/
@[simp]
lemma ziter_neg_comp_ziter (e : α ≃ᵐ α) (n : ℤ) : ziter e (-n) ∘ ziter e n = id := by
  rw [← ziter_add, neg_add_cancel, ziter_zero]

/-- Each two-sided iterate is **measurable**. For `n ≥ 0` it is a forward iterate of the measurable
`e`; for `n < 0` a forward iterate of the measurable `e.symm`. -/
lemma measurable_ziter (e : α ≃ᵐ α) (n : ℤ) : Measurable (ziter e n) := by
  cases n with
  | ofNat k => rw [ziter_ofNat]; exact e.measurable.iterate k
  | negSucc k => rw [ziter_negSucc]; exact e.symm.measurable.iterate (k + 1)

/-- Each two-sided iterate is **measure preserving** when `e` is. For `n ≥ 0` this is
`he.iterate`; for `n < 0` it is the iterate of the measure-preserving inverse `e.symm`, obtained
from `he` via `MeasurePreserving.symm`. -/
lemma measurePreserving_ziter (e : α ≃ᵐ α) (he : MeasurePreserving (e : α → α) μ μ) (n : ℤ) :
    MeasurePreserving (ziter e n) μ μ := by
  -- The inverse `e.symm` is measure preserving: `he.symm e` gives `MeasurePreserving e.symm μ μ`
  -- directly (with `μa = μb = μ`, `MeasurePreserving.symm` swaps to `μ μ`).
  have hsymm : MeasurePreserving (e.symm : α → α) μ μ := he.symm e
  cases n with
  | ofNat k => rw [ziter_ofNat]; exact he.iterate k
  | negSucc k => rw [ziter_negSucc]; exact hsymm.iterate (k + 1)

/-- `P` is a **two-sided generating partition** for the automorphism `e : α ≃ᵐ α` when the smallest
two-sided-`e`-pullback-stable σ-algebra containing the generated σ-algebra `σ(P)` is the ambient
measurable structure: `⨆ n : ℤ, comap (ziter e n) σ(P) = mα`.

This is the correct generating condition for an **invertible** measure-preserving system, and the
hypothesis of Krieger's finite generator theorem (issue #15). It saturates over both time
directions, in contrast to the one-sided ℕ-version `Oseledets.Entropy.IsGenerating` (which suffices
for non-invertible endomorphisms but provably fails to recover the full σ-algebra for an
automorphism such as the two-sided Bernoulli shift). -/
def IsGeneratingTwoSided [Fintype ι] (e : α ≃ᵐ α)
    (P : Oseledets.Entropy.MeasurePartition μ ι) : Prop :=
  (⨆ n : ℤ, MeasurableSpace.comap (ziter e n)
    (Oseledets.Entropy.generatedSigmaAlgebra μ P)) = mα

variable [Fintype ι]

/-- Each two-sided pullback `comap (ziter e n) σ(P)` sits below the two-sided saturation
`⨆ n : ℤ, comap (ziter e n) σ(P)`. The always-available `≤` half (just `le_iSup`); the content of
`IsGeneratingTwoSided` is the reverse saturation up to `mα`. -/
lemma comap_ziter_le_iSup (e : α ≃ᵐ α) (P : Oseledets.Entropy.MeasurePartition μ ι) (n : ℤ) :
    MeasurableSpace.comap (ziter e n) (Oseledets.Entropy.generatedSigmaAlgebra μ P) ≤
      ⨆ m : ℤ, MeasurableSpace.comap (ziter e m)
        (Oseledets.Entropy.generatedSigmaAlgebra μ P) :=
  le_iSup (fun m : ℤ => MeasurableSpace.comap (ziter e m)
    (Oseledets.Entropy.generatedSigmaAlgebra μ P)) n

/-- **Forward one-sided ≤ two-sided saturation.** Every forward `ℕ`-pullback
`comap ((e : α → α)^[n]) σ(P)` is the `n : ℤ≥0` term `comap (ziter e n) σ(P)` of the two-sided
saturation (`ziter_natCast`), so the forward one-sided saturation is bounded above by the two-sided
one. Consequently *forward* one-sided generation is strictly stronger than two-sided generation:
the two-sided condition `IsGeneratingTwoSided` is the weaker, correct hypothesis for an invertible
system (forward saturation provably fails for the two-sided Bernoulli shift). -/
lemma isGeneratingOneSided_le_twoSided (e : α ≃ᵐ α)
    (P : Oseledets.Entropy.MeasurePartition μ ι) :
    (⨆ n : ℕ, MeasurableSpace.comap ((e : α → α)^[n])
        (Oseledets.Entropy.generatedSigmaAlgebra μ P)) ≤
      ⨆ n : ℤ, MeasurableSpace.comap (ziter e n)
        (Oseledets.Entropy.generatedSigmaAlgebra μ P) := by
  refine iSup_le fun n => ?_
  rw [← ziter_natCast e n]
  exact le_iSup (fun m : ℤ => MeasurableSpace.comap (ziter e m)
    (Oseledets.Entropy.generatedSigmaAlgebra μ P)) ((n : ℕ) : ℤ)

end Oseledets.Krieger
