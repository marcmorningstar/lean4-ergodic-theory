/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Multifractal.Defs

/-!
# Coarse-grained multifractal analysis: the singularity spectrum (Legendre layer)

This file develops the elementary Legendre-bound interface around the **singularity spectrum**
`f(α) = ⨅ q, q α - τ(q)` defined in `ErgodicTheory.Multifractal.Defs` (where `τ = massExponent`).
The *definition itself* — `singularitySpectrum`, the Legendre transform of the mass exponent — is
the deliverable for this milestone; here we record the two universal properties of that infimum
that make it usable downstream.

The Legendre transform is an **infimum** over `q : ℝ` (not a supremum): since `τ` is concave, the
supremum of `q α - τ(q)` would be `+∞`. Because the index set `ℝ` is a nonempty
`ConditionallyCompleteLattice` (but *not* a complete lattice), the relevant tools are the
*conditional* infimum lemmas `ciInf_le` and `le_ciInf` (not `iInf_le`, which requires a complete
lattice). Accordingly:

* the **upper bound** `f(α) ≤ q α - τ(q)` for a fixed `q` holds only once we know the family
  `q ↦ q α - τ(q)` is bounded below (`BddBelow`), supplied as a hypothesis (`ciInf_le`);
* the **lower bound** `b ≤ f(α)` holds whenever `b` is below *every* term `q α - τ(q)`, with no
  boundedness hypothesis needed over the nonempty index `ℝ` (`le_ciInf`).

## Main results

* `ErgodicTheory.Multifractal.singularitySpectrum_le`: `f(α) ≤ q α - τ(q)` for each `q`, given that
  the Legendre family is bounded below.
* `ErgodicTheory.Multifractal.le_singularitySpectrum`: `b ≤ f(α)` from a uniform lower bound `b` on
  every term of the Legendre family.

## Scope

This milestone deliberately stops at the elementary order-theoretic interface to the infimum.
The deeper facts — **concavity** of `f`, and the **Legendre duality** identifying `max_α f(α)`
with the box-counting dimension `D_0` (or the duality `f = τ*`, `τ = f*`) — require convex
analysis / calculus and are *out of scope* here; they belong to a later wave.
-/

namespace ErgodicTheory.Multifractal

variable {ι : Type*} [Fintype ι]

/-- **Upper bound for the singularity spectrum.** For each `q`, the Legendre transform
`f(α) = ⨅ q, q α - τ(q)` is at most the value `q α - τ(q)` of the family at `q`, provided that
family is bounded below. This is the conditional-infimum lower bound `ciInf_le`. -/
lemma singularitySpectrum_le {p : ι → ℝ} {ε α : ℝ}
    (hbb : BddBelow (Set.range (fun q => q * α - massExponent p ε q))) (q : ℝ) :
    singularitySpectrum p ε α ≤ q * α - massExponent p ε q :=
  ciInf_le hbb q

/-- **Lower bound for the singularity spectrum.** If `b` is below every term `q α - τ(q)` of the
Legendre family, then `b ≤ f(α) = ⨅ q, q α - τ(q)`. No boundedness hypothesis is needed: the
index set `ℝ` is nonempty, so this is the conditional-infimum greatest-lower-bound lemma
`le_ciInf`. -/
lemma le_singularitySpectrum {p : ι → ℝ} {ε α b : ℝ}
    (h : ∀ q : ℝ, b ≤ q * α - massExponent p ε q) :
    b ≤ singularitySpectrum p ε α :=
  le_ciInf h

end ErgodicTheory.Multifractal
