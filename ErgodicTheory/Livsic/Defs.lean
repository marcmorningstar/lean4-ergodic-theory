/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Topology.MetricSpace.Holder

/-!
# The Livšic theorem: basic definitions

This file sets up the vocabulary for the Livšic (Livshits) cohomological rigidity theorem
(issue #29): over a hyperbolic-type map `T : X → X`, a Hölder observable `φ` is a Hölder
coboundary if and only if all of its periodic Birkhoff sums vanish.

We record here:

* `IsCoboundary T φ` — `φ = u ∘ T - u` for some (arbitrary) transfer function `u`;
* `IsHolderCoboundary T φ` — the same with `u` Hölder continuous;
* `HasVanishingPeriodicSums T φ` — every periodic Birkhoff sum of `φ` vanishes;
* `ExpClosing T α δ K` — an abstracted *exponential closing property*, in **summed-bound
  form**: any point that almost `n`-returns (within `δ`) is shadowed by a genuine
  `n`-periodic point, with the total `α`-Hölder shadowing cost geometrically controlled by
  `K · dist x (T^[n] x) ^ α`. The summed form deliberately covers both the two-sided Anosov
  `θ ^ min(i, n-i)` regime and the one-sided/expanding front-anchored `θ ^ (n-i)` regime — it
  never hardcodes `min`.

The **trivial direction** — a coboundary has vanishing periodic sums — is proved here in
full generality (it is a pure telescoping identity, valid for a *bare* `T` and *any* `u`).
This is the downstream "no continuous section obstruction" direction. The converse (the
substantive Livšic direction) lives in `ErgodicTheory.Livsic.Abstract`.

## Main results

* `birkhoffSum_eq_of_coboundary` — the telescoping identity `S_n φ x = u (T^[n] x) - u x`.
* `IsCoboundary.hasVanishingPeriodicSums` — the easy direction.
* `IsHolderCoboundary.isCoboundary` — a Hölder coboundary is a coboundary.
-/

open Function
open scoped NNReal

namespace ErgodicTheory

variable {X : Type*}

/-- `φ` is a **coboundary** for `T` if `φ = u ∘ T - u` for some transfer function `u : X → ℝ`
(no regularity assumed on `u`). -/
def IsCoboundary (T : X → X) (φ : X → ℝ) : Prop :=
  ∃ u : X → ℝ, ∀ x, φ x = u (T x) - u x

/-- `φ` has **vanishing periodic sums** for `T` if every Birkhoff sum around a periodic orbit
vanishes: whenever `T^[n] p = p`, the sum `∑_{i<n} φ (T^[i] p) = 0`. -/
def HasVanishingPeriodicSums (T : X → X) (φ : X → ℝ) : Prop :=
  ∀ n p, T^[n] p = p → birkhoffSum T φ n p = 0

/-- The telescoping identity for a coboundary: if `φ x = u (T x) - u x` for all `x`, then the
Birkhoff sum collapses, `birkhoffSum T φ n x = u (T^[n] x) - u x`. Pure algebra — no metric,
no regularity, works for a bare `T`. -/
theorem birkhoffSum_eq_of_coboundary {T : X → X} {φ u : X → ℝ}
    (hu : ∀ x, φ x = u (T x) - u x) (x : X) (n : ℕ) :
    birkhoffSum T φ n x = u (T^[n] x) - u x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [birkhoffSum_succ, ih, hu (T^[k] x), iterate_succ_apply']
    ring

/-- **Trivial direction of Livšic.** A coboundary has vanishing periodic sums. This holds for a
bare `T : X → X` and *any* transfer function `u` — it is the pure telescoping collapse around a
periodic orbit, and is the downstream obstruction (no continuous section) direction. -/
theorem IsCoboundary.hasVanishingPeriodicSums {T : X → X} {φ : X → ℝ}
    (h : IsCoboundary T φ) : HasVanishingPeriodicSums T φ := by
  obtain ⟨u, hu⟩ := h
  intro n p hp
  rw [birkhoffSum_eq_of_coboundary hu p n, hp, sub_self]

/-- **Obstruction certificate.** A single non-vanishing periodic Birkhoff sum defeats *every*
coboundary: if `p` is `n`-periodic (`T^[n] p = p`) and `birkhoffSum T φ n p ≠ 0`, then `φ` is not a
coboundary of any transfer function. This is the contrapositive of the trivial direction
`IsCoboundary.hasVanishingPeriodicSums`, and is the bare downstream "no continuous section"
obstruction (it needs nothing but a bare `T : X → X`). -/
theorem not_isCoboundary_of_periodicSum_ne_zero {T : X → X} {φ : X → ℝ} {n : ℕ} {p : X}
    (hp : T^[n] p = p) (hφ : birkhoffSum T φ n p ≠ 0) : ¬ IsCoboundary T φ :=
  fun h => hφ (h.hasVanishingPeriodicSums n p hp)

section Metric

variable [MetricSpace X]

/-- `φ` is a **Hölder coboundary** for `T` if `φ = u ∘ T - u` with `u` Hölder continuous
(exponent `r > 0`, constant `C`). This is the target regularity in the Livšic theorem. -/
def IsHolderCoboundary (T : X → X) (φ : X → ℝ) : Prop :=
  ∃ (C r : ℝ≥0) (u : X → ℝ), 0 < r ∧ HolderWith C r u ∧ ∀ x, φ x = u (T x) - u x

/-- The **exponential closing property** in *summed-bound* form. For every `n` and every point
`x` that almost `n`-returns (`dist x (T^[n] x) ≤ δ`) there is a genuine `n`-periodic point `p`
whose orbit `α`-Hölder-shadows that of `x`, with *total* shadowing cost controlled by the return
gap: `∑_{i<n} dist (T^[i] x) (T^[i] p) ^ α ≤ K · dist x (T^[n] x) ^ α`.

Summing the per-step shadowing cost is deliberate: geometrically the individual terms decay like
`θ ^ min(i, n-i)` (two-sided Anosov) or `θ ^ (n-i)` (one-sided/expanding), and both sum to a
geometric series bounded by a constant multiple of the endpoint gap. Abstracting the *sum*
(rather than a per-term `min`-exponent bound) keeps the crux estimate regime-agnostic. -/
def ExpClosing (T : X → X) (α δ K : ℝ) : Prop :=
  ∀ n x, dist x (T^[n] x) ≤ δ → ∃ p, T^[n] p = p ∧
    ∑ i ∈ Finset.range n, dist (T^[i] x) (T^[i] p) ^ α ≤ K * dist x (T^[n] x) ^ α

/-- A Hölder coboundary is a coboundary (forget the regularity of the transfer function). -/
theorem IsHolderCoboundary.isCoboundary {T : X → X} {φ : X → ℝ}
    (h : IsHolderCoboundary T φ) : IsCoboundary T φ := by
  obtain ⟨_, _, u, _, _, hu⟩ := h
  exact ⟨u, hu⟩

end Metric

end ErgodicTheory
