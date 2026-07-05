/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlowCocycle

/-!
# Extending the section cocycle off the base section: the cover identities

This module advances the special-flow (suspension) cocycle one step toward the genuine
space-level `FlowCocycle` of `ErgodicTheory.Continuous.SuspensionCocycle`: it records how the lap
counter `lapCount` of `ErgodicTheory.Continuous.SuspensionLapCount` behaves under the two operations
that the *cover* of the cross-section needs — advancing the elapsed flow time, and shifting the
starting base point past a whole number of completed laps.

The geometric content is the standard special-flow / flow-under-a-roof bookkeeping of
Cornfeld–Fomin–Sinai, *Ergodic Theory* (Springer 1982), Ch. 11 (special/suspension flows;
Ambrose–Kakutani), the same first-return / ceiling structure underlying Abramov's entropy formula
`h(flow) = h(base)/∫τ`, whose Lyapunov-exponent analogue `λ_flow = λ_base / ∫τ` is the headline
target. The two facts assembled here are the discrete, sorry-free combinatorial core of the
return-count function that the continuous-time `FlowCocycle` reads:

* **monotonicity in time** — more elapsed flow time can only complete more laps;
* **additivity at a return boundary** — the laps completed by time `returnTime n x + r` started
  from `x` are the `n` laps already finished plus the laps completed by the *residual* time `r`
  started from the shifted base point `Tⁿ x`.

The additivity identity is the crux toward extending the section cocycle off the base section: it
is the discrete shadow of the continuous cocycle identity `Ψ (returnTime n x + r) = Ψ r (Tⁿ x) · …`,
and it is proved here purely from the first-passage sandwich
`returnTime (lapCount t x) x ≤ t < returnTime (lapCount t x + 1) x` (of
`ErgodicTheory.Continuous.SuspensionLapCount`) plus return-time additivity (`returnTime_add` of
`ErgodicTheory.Continuous.SuspensionCocycle`), via a uniqueness lemma for the sandwiched index.

## Main results

* `ErgodicTheory.lapCount_unique`: the lap count is the *unique* index sandwiched by the strictly
  increasing return times, `returnTime m x ≤ t < returnTime (m + 1) x → lapCount t x = m`.
* `ErgodicTheory.lapCount_mono`: `lapCount s x ≤ lapCount t x` whenever `0 ≤ s ≤ t` — more elapsed
  flow time completes at least as many laps.
* `ErgodicTheory.lapCount_returnTime_add`: the lap count at a return boundary splits additively,
  `lapCount (returnTime n x + r) x = n + lapCount r (Tⁿ x)` for `0 ≤ r`.

## What is *not* in this file — the remaining gap toward the cover cocycle

The next step, the **cover-extension identity for the matrix cocycle**
`flowCocycleSection (returnTime n x + r) x = flowCocycleSection r (Tⁿ x) * cocycle A T n x`, does
*not* follow from `lapCount_returnTime_add` alone: `flowCocycleSection` is the return cocycle at the
lap count, and the additive split of the lap count must be pushed through
`suspensionCocycleReturn_add` (i.e. `cocycle_add`), whose shift point `Tⁿ x` must be matched to the
base point shift of the residual term. That matching needs `cocycle (n + k) x =
cocycle k (Tⁿ x) * cocycle n x` aligned with `lapCount r (Tⁿ x)` *and* with the fact that the
discrete cocycle `cocycle A T` is evaluated along `⇑T`, while `flowCocycleSection` carries the
`MeasurableEquiv` `T`; the namespacing of `⇑T` vs the iterate makes the rewrite non-definitional.
It is therefore deferred. The genuine space-level `FlowCocycle` over `SuspensionSpace` additionally
requires the descent of the Ambrose–Kakutani return-count to the orbit quotient (the gap already
documented in `ErgodicTheory.Continuous.SuspensionCocycle`).
-/

namespace ErgodicTheory

section CoverCocycle

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **Nonnegativity of the return time.** For every lap index `n`, the flow time `returnTime n x`
to the `n`-th base return is nonnegative, since it grows from `returnTime 0 x = 0` and the return
times are monotone under a positive roof. -/
theorem returnTime_nonneg (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) (x : X) :
    0 ≤ returnTime T hτ n x := by
  have hmono : StrictMono (fun m : ℕ => returnTime T hτ m x) :=
    returnTime_strictMono T hτ hc hcpos x
  have := hmono.monotone (Nat.zero_le n)
  simpa only [returnTime_zero] using this

/-- **Uniqueness of the sandwiched lap index.** Because the return times strictly increase, any
index `m` with `returnTime m x ≤ t < returnTime (m + 1) x` is exactly the lap count `lapCount t x`.
This is the first-passage characterization read as a definition: the lap count is *the* index whose
return time the flow time `t` has reached but whose successor it has not. -/
theorem lapCount_unique (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {t : ℝ} (ht : 0 ≤ t) (x : X) {m : ℕ}
    (hlo : returnTime T hτ m x ≤ t) (hhi : t < returnTime T hτ (m + 1) x) :
    lapCount T hτ hc hcpos t x = m := by
  have hmono : StrictMono (fun k : ℕ => returnTime T hτ k x) :=
    returnTime_strictMono T hτ hc hcpos x
  -- Compare the two sandwiches `returnTime (lapCount …) ≤ t < returnTime (lapCount … + 1)`
  -- and `returnTime m ≤ t < returnTime (m + 1)` through strict monotonicity of the return times.
  have hsand_lo := lapCount_returnTime_le T hτ hc hcpos ht x
  have hsand_hi := lapCount_lt_returnTime_succ T hτ hc hcpos ht x
  -- `lapCount ≤ m`: else `m + 1 ≤ lapCount`, so `returnTime (m+1) ≤ returnTime (lapCount) ≤ t`.
  have hle : lapCount T hτ hc hcpos t x ≤ m := by
    by_contra h
    rw [not_le] at h
    have : returnTime T hτ (m + 1) x ≤ t :=
      le_trans (hmono.monotone (Nat.succ_le_of_lt h)) hsand_lo
    linarith
  -- `m ≤ lapCount`: else `lapCount + 1 ≤ m`, so `returnTime m ≤ t` and the strict upper bound
  -- `t < returnTime (lapCount + 1) x` collide via `returnTime (lapCount + 1) ≤ returnTime m`.
  have hge : m ≤ lapCount T hτ hc hcpos t x := by
    by_contra h
    rw [not_le] at h
    have : returnTime T hτ (lapCount T hτ hc hcpos t x + 1) x ≤ t :=
      le_trans (hmono.monotone (Nat.succ_le_of_lt h)) hlo
    linarith
  exact le_antisymm hle hge

/-- **Monotonicity of the lap counter in the elapsed time.** For `0 ≤ s ≤ t`, the flow completes at
least as many laps by time `t` as by time `s`: `lapCount s x ≤ lapCount t x`. More elapsed flow time
can only finish more base returns. Proved from the first-passage sandwich at `s` (lower half) and at
`t` (upper half) through the strict monotonicity of the return times. -/
theorem lapCount_mono (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (x : X) : lapCount T hτ hc hcpos s x ≤ lapCount T hτ hc hcpos t x := by
  have ht : 0 ≤ t := le_trans hs hst
  have hmono : StrictMono (fun k : ℕ => returnTime T hτ k x) :=
    returnTime_strictMono T hτ hc hcpos x
  -- `returnTime (lapCount s x) x ≤ s ≤ t < returnTime (lapCount t x + 1) x`.
  have hlo := lapCount_returnTime_le T hτ hc hcpos hs x
  have hhi := lapCount_lt_returnTime_succ T hτ hc hcpos ht x
  have hchain : returnTime T hτ (lapCount T hτ hc hcpos s x) x
      < returnTime T hτ (lapCount T hτ hc hcpos t x + 1) x := by linarith
  have := hmono.lt_iff_lt.mp hchain
  exact Nat.lt_succ_iff.mp this

/-- **Additivity of the lap counter at a return boundary.** Starting on the cross-section at `x`,
the laps completed by flow time `returnTime n x + r` (for `0 ≤ r`) are the `n` laps finished by the
`n`-th return, plus the laps completed by the residual time `r` started from the shifted base point
`Tⁿ x`: `lapCount (returnTime n x + r) x = n + lapCount r (Tⁿ x)`. This is the crux identity toward
extending the section cocycle off the base section. It is proved by verifying that the candidate
index `n + lapCount r (Tⁿ x)` satisfies the first-passage sandwich for the boundary time, using
return-time additivity (`returnTime_add`), and then invoking uniqueness (`lapCount_unique`). -/
theorem lapCount_returnTime_add (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (x : X) :
    lapCount T hτ hc hcpos (returnTime T hτ n x + r) x
      = n + lapCount T hτ hc hcpos r ((⇑T)^[n] x) := by
  set y := (⇑T)^[n] x with hy
  -- The boundary time is nonnegative.
  have htn : 0 ≤ returnTime T hτ n x := returnTime_nonneg T hτ hc hcpos n x
  have ht : 0 ≤ returnTime T hτ n x + r := by linarith
  -- Residual sandwich at the shifted base point `y`.
  have hrlo := lapCount_returnTime_le T hτ hc hcpos hr y
  have hrhi := lapCount_lt_returnTime_succ T hτ hc hcpos hr y
  -- Lower half of the boundary sandwich, via `returnTime ((lapCount r y) + n) x`.
  have hlo : returnTime T hτ (n + lapCount T hτ hc hcpos r y) x
      ≤ returnTime T hτ n x + r := by
    have hsplit : returnTime T hτ (lapCount T hτ hc hcpos r y + n) x
        = returnTime T hτ (lapCount T hτ hc hcpos r y) y + returnTime T hτ n x :=
      returnTime_add T hτ (lapCount T hτ hc hcpos r y) n x
    rw [Nat.add_comm n (lapCount T hτ hc hcpos r y), hsplit]
    linarith
  -- Upper half of the boundary sandwich, via `returnTime ((lapCount r y + 1) + n) x`.
  have hhi : returnTime T hτ n x + r
      < returnTime T hτ (n + lapCount T hτ hc hcpos r y + 1) x := by
    have hsplit : returnTime T hτ (lapCount T hτ hc hcpos r y + 1 + n) x
        = returnTime T hτ (lapCount T hτ hc hcpos r y + 1) y + returnTime T hτ n x :=
      returnTime_add T hτ (lapCount T hτ hc hcpos r y + 1) n x
    have hreorder : n + lapCount T hτ hc hcpos r y + 1
        = lapCount T hτ hc hcpos r y + 1 + n := by ring
    rw [hreorder, hsplit]
    linarith
  exact lapCount_unique T hτ hc hcpos ht x hlo hhi

end CoverCocycle

end ErgodicTheory
