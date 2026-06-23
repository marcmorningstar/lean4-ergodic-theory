/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Factor maps and invariant sub-σ-algebras

A *factor map* (or *morphism of measure-preserving systems*) from a system `(α, T, μ)` to a
system `(β, S, ν)` is a measure-preserving map `π : α → β` that intertwines the two dynamics,
`π ∘ T = S ∘ π`. This file packages that data as `Oseledets.Entropy.IsFactorMap` and proves the
basic correspondence between factor maps and *invariant* sub-σ-algebras of the source: the
σ-algebra `comap π 𝓑` pulled back from the target is invariant under `T`, in the sense that
pulling it back once more along `T` only shrinks it (`comap T (comap π 𝓑) ≤ comap π 𝓑`). This is
exactly the hypothesis `comap T 𝒜 ≤ 𝒜` consumed by the Kolmogorov–Sinai entropy machinery, so
the lemma feeds a factor system into the conditional-entropy / relative-entropy toolbox.

## Design note: the intertwining is an *everywhere* equality

The defining intertwining relation is stated as the honest pointwise equality `π ∘ T = S ∘ π`,
not merely the almost-everywhere relation `π ∘ T =ᵐ[μ] S ∘ π`. This is deliberate and
mathematically standard (Walters, Ch. 4: a factor map is a morphism of dynamical systems, hence
genuinely commutes with the dynamics). It is also *necessary* for the correspondence lemma:
`MeasurableSpace.comap` is an everywhere construction on preimages, and an almost-everywhere
equality of functions does **not** in general yield equality of the comap σ-algebras. With the
everywhere identity, the key lemma is a clean rewrite by `MeasurableSpace.comap_comp` followed by
`MeasurableSpace.comap_mono`.

A second, equally standard part of the morphism data is that the target dynamics `S` is itself
measurable; this is what supplies the σ-algebra contraction `comap S 𝓑 ≤ 𝓑` driving the
correspondence lemma.

## Main definitions

* `Oseledets.Entropy.IsFactorMap`: `π : α → β` is a factor map from `(α, T, μ)` to `(β, S, ν)` when
  it is measure preserving, the target map `S` is measurable, and it intertwines the dynamics,
  `π ∘ T = S ∘ π`.

## Main results

* `Oseledets.Entropy.IsFactorMap.invariant_comap`: the pulled-back σ-algebra `comap π 𝓑` is
  `T`-invariant, `comap T (comap π 𝓑) ≤ comap π 𝓑` — the hypothesis the entropy machinery needs.
* `Oseledets.Entropy.IsFactorMap.measurable_comap_le`: `comap π 𝓑` is a genuine sub-σ-algebra of
  the source measurable structure.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics **79**,
  Springer (1982), Ch. 4.
-/

open MeasureTheory

namespace Oseledets.Entropy

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {T : α → α} {S : β → β} {π : α → β}

/-- `π : α → β` is a **factor map** from the measure-preserving system `(α, T, μ)` to the system
`(β, S, ν)` when it pushes `μ` forward to `ν`, the target dynamics `S` is measurable, and `π`
intertwines the dynamics, `π ∘ T = S ∘ π`.

The intertwining is required as an *everywhere* equality (not only `=ᵐ[μ]`): a factor map is a
morphism of dynamical systems, and the everywhere identity is what makes the pulled-back
σ-algebra genuinely invariant. Measurability of `S` is part of the data of a morphism of
measurable dynamical systems and is exactly what makes `comap S 𝓑 ≤ 𝓑`, the contraction used in
the correspondence lemma below. -/
def IsFactorMap (π : α → β) (T : α → α) (S : β → β) (μ : Measure α) (ν : Measure β) : Prop :=
  MeasurePreserving π μ ν ∧ Measurable S ∧ π ∘ T = S ∘ π

/-- The σ-algebra `comap π 𝓑` pulled back from the target along a factor map is invariant under
the source dynamics `T`: pulling it back once more along `T` only shrinks it. This is precisely
the `comap T 𝒜 ≤ 𝒜` hypothesis required by the Kolmogorov–Sinai entropy machinery.

The proof rewrites `comap T (comap π 𝓑) = comap (π ∘ T) 𝓑 = comap (S ∘ π) 𝓑 = comap π (comap S 𝓑)`
using the everywhere intertwining `π ∘ T = S ∘ π`, then applies `comap_mono` to the contraction
`comap S 𝓑 ≤ 𝓑`, which is the measurability of `S`. -/
lemma IsFactorMap.invariant_comap (h : IsFactorMap π T S μ ν) :
    MeasurableSpace.comap T (MeasurableSpace.comap π (‹MeasurableSpace β›)) ≤
      MeasurableSpace.comap π (‹MeasurableSpace β›) := by
  rw [MeasurableSpace.comap_comp, h.2.2, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono h.2.1.comap_le

/-- The pulled-back σ-algebra `comap π 𝓑` of a factor map is a genuine sub-σ-algebra of the
source measurable structure, since the measure-preserving `π` is in particular measurable. -/
lemma IsFactorMap.measurable_comap_le (h : IsFactorMap π T S μ ν) :
    MeasurableSpace.comap π (‹MeasurableSpace β›) ≤ ‹MeasurableSpace α› :=
  h.1.measurable.comap_le

end Oseledets.Entropy
