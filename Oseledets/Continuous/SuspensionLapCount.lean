/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Continuous.SuspensionCocycle

/-!
# The special-flow lap counter

This module builds the **lap counter** `N(t, x)` of a special (suspension) flow: the number of
base returns the cross-section orbit of `x` has completed by flow time `t`. It is the standard
combinatorial ingredient of the special-flow / flow-under-a-roof construction (Cornfeld–Fomin–
Sinai, *Ergodic Theory*, Springer 1982, Ch. 11, special flows; the first-return / ceiling
construction also underlying Abramov's entropy formula). On the suspension of a base map `T` under a
strictly positive roof `τ`, the flow advances the time coordinate, and crossing the cross-section
the `n`-th time happens exactly at flow time `returnTime n x` (the roof Birkhoff sum). The lap
counter is the first-passage index that reads off, for a given elapsed time `t`, how many returns
have already occurred — the discrete clock that the continuous-time suspension `FlowCocycle` reads
to decide how many base matrices to multiply.

The construction proceeds in three steps, each grounded on the return-time API of
`Oseledets.Continuous.SuspensionCocycle`:

* `returnTime_strictMono` — under a positive roof the return times are strictly increasing, so the
  laps are genuinely ordered;
* `returnTime_tendsto_atTop` — the return times diverge, so only finitely many laps fit under any
  finite time `t` and the lap counter is well defined;
* `lapCount` together with `lapCount_returnTime_le` / `lapCount_lt_returnTime_succ` — the
  first-passage index `N(t, x)` and its defining sandwich
  `returnTime (N t x) x ≤ t < returnTime (N t x + 1) x`.

## Main definitions

* `Oseledets.lapCount`: `N(t, x) = Nat.findGreatest (fun n => returnTime n x ≤ t) (latch t x)`, the
  number of base returns completed by flow time `t`.

## Main results

* `Oseledets.returnTime_strictMono`: `n ↦ returnTime n x` is `StrictMono` (positive roof).
* `Oseledets.returnTime_tendsto_atTop`: the return times diverge to `+∞`.
* `Oseledets.lapCount_returnTime_le`: `returnTime (lapCount t x) x ≤ t` for `0 ≤ t`.
* `Oseledets.lapCount_lt_returnTime_succ`: `t < returnTime (lapCount t x + 1) x`.

These two inequalities are the first-passage characterization of the lap counter: the flow has, by
time `t`, completed exactly `lapCount t x` base returns and not yet the next one. They are the
combinatorial core of the suspension `FlowCocycle` lift left open in
`Oseledets.Continuous.SuspensionCocycle`.
-/

open Filter

namespace Oseledets

section LapCount

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ) {c : ℝ}

/-- **Strict monotonicity of the return times.** Under a positive roof (`c ≤ τ` with `0 < c`), the
flow time `returnTime n x` to the `n`-th base return strictly increases in `n`, since each step adds
`τ (T^n x) ≥ c > 0`. -/
theorem returnTime_strictMono (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (x : X) :
    StrictMono (fun n : ℕ => returnTime T hτ n x) :=
  strictMono_nat_of_lt_succ fun n => by
    have hstep : returnTime T hτ (n + 1) x
        = returnTime T hτ n x + τ (baseIter T hτ (n : ℤ) x) := by
      simp only [returnTime]
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, roofSum_add_one]
    have := hc (baseIter T hτ (n : ℤ) x)
    rw [hstep]; linarith

/-- **Divergence of the return times.** Under a positive roof the return times tend to `+∞`: by
the telescoping lower bound `c * n ≤ returnTime n x`, only finitely many base returns fit under any
finite flow time. This is what makes the lap counter well defined. -/
theorem returnTime_tendsto_atTop (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (x : X) :
    Tendsto (fun n : ℕ => returnTime T hτ n x) atTop atTop := by
  have hlin : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hcpos tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono _ hlin
  intro n
  simpa only [returnTime] using roofSum_ge T hτ hc x n

/-- A time index past which the flow has provably overshot `t`: any natural `N` with `t / c < N`
satisfies `t < returnTime N x`. This supplies the explicit `Nat.findGreatest` bound used to define
`lapCount`. -/
theorem exists_returnTime_gt (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) (x : X) :
    ∃ N : ℕ, t < returnTime T hτ N x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (t / c)
  refine ⟨N, ?_⟩
  have hlb : c * (N : ℝ) ≤ returnTime T hτ N x := by
    simpa only [returnTime] using roofSum_ge T hτ hc x N
  have : t < c * (N : ℝ) := by
    rw [div_lt_iff₀ hcpos] at hN; linarith
  linarith

/-- An explicit overshoot index: the least latch `N` exhibited by `exists_returnTime_gt`, used as
the upper bound in the `Nat.findGreatest` defining `lapCount`. -/
noncomputable def latch (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) (x : X) : ℕ :=
  (exists_returnTime_gt T hτ hc hcpos t x).choose

/-- The latch overshoots: by construction `t < returnTime (latch t x) x`. -/
theorem returnTime_latch_gt (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) (x : X) :
    t < returnTime T hτ (latch T hτ hc hcpos t x) x :=
  (exists_returnTime_gt T hτ hc hcpos t x).choose_spec

/-- **The special-flow lap counter** `N(t, x)`: the number of base returns the cross-section orbit
of `x` has completed by flow time `t`. It is the greatest `n ≤ latch` with `returnTime n x ≤ t`,
i.e. the first-passage index of the strictly increasing, divergent return-time sequence. This is the
standard ceiling/first-return construction of special flows (Cornfeld–Fomin–Sinai, Ch. 11). -/
noncomputable def lapCount (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) (t : ℝ) (x : X) : ℕ :=
  Nat.findGreatest (fun n => returnTime T hτ n x ≤ t) (latch T hτ hc hcpos t x)

/-- The latch strictly exceeds the lap count (for `0 ≤ t`), since the predicate fails at the latch
(`t < returnTime (latch) x`) while holding at `0`. This bridges the lap count to the next return. -/
theorem lapCount_lt_latch (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {t : ℝ} (ht : 0 ≤ t) (x : X) :
    lapCount T hτ hc hcpos t x < latch T hτ hc hcpos t x := by
  -- The predicate fails at the latch, since `t < returnTime (latch) x`.
  have hnotP : ¬ (fun n => returnTime T hτ n x ≤ t) (latch T hτ hc hcpos t x) := by
    simp only [not_le]; exact returnTime_latch_gt T hτ hc hcpos t x
  -- The latch is positive: `latch = 0` would give `t < returnTime 0 x = 0`, contradicting `0 ≤ t`.
  have hpos : 0 < latch T hτ hc hcpos t x := by
    by_contra h
    rw [not_lt, Nat.le_zero] at h
    have := returnTime_latch_gt T hτ hc hcpos t x
    rw [h, returnTime_zero] at this
    linarith
  rw [lapCount]
  have hle : Nat.findGreatest (fun n => returnTime T hτ n x ≤ t) (latch T hτ hc hcpos t x)
      ≤ latch T hτ hc hcpos t x := Nat.findGreatest_le _
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · -- Equality is impossible: it would make the predicate hold at the latch.
    exact absurd (Nat.findGreatest_of_ne_zero heq (Nat.pos_iff_ne_zero.mp hpos)) hnotP

/-- **Lap-counter lower bound.** By flow time `t ≥ 0` the orbit has completed at least
`lapCount t x` returns: `returnTime (lapCount t x) x ≤ t`. (At `t = 0` both sides are `0`.) This is
one half of the first-passage sandwich, read off from `Nat.findGreatest_spec` at the base point
`n = 0`, where `returnTime 0 x = 0 ≤ t`. -/
theorem lapCount_returnTime_le (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {t : ℝ} (ht : 0 ≤ t) (x : X) :
    returnTime T hτ (lapCount T hτ hc hcpos t x) x ≤ t := by
  rw [lapCount]
  have hP0 : (fun n => returnTime T hτ n x ≤ t) 0 := by
    simp only [returnTime_zero]; exact ht
  exact Nat.findGreatest_spec (P := fun n => returnTime T hτ n x ≤ t) (Nat.zero_le _) hP0

/-- **Lap-counter upper bound.** The next return strictly overshoots `t`:
`t < returnTime (lapCount t x + 1) x` (for `0 ≤ t`). This is the second half of the first-passage
sandwich: by flow time `t` the orbit has *not* yet completed return number `lapCount t x + 1`. It is
read off from `Nat.findGreatest_is_greatest`, using that the next index `lapCount t x + 1` still
lies below the latch (`lapCount_lt_latch`). -/
theorem lapCount_lt_returnTime_succ (hc : ∀ x, c ≤ τ x) (hcpos : 0 < c) {t : ℝ} (ht : 0 ≤ t)
    (x : X) :
    t < returnTime T hτ (lapCount T hτ hc hcpos t x + 1) x := by
  have hkb : lapCount T hτ hc hcpos t x + 1 ≤ latch T hτ hc hcpos t x :=
    lapCount_lt_latch T hτ hc hcpos ht x
  -- The greatest index with the predicate is `lapCount`, so the next index `lapCount + 1` fails it.
  have hlt : Nat.findGreatest (fun n => returnTime T hτ n x ≤ t) (latch T hτ hc hcpos t x)
      < lapCount T hτ hc hcpos t x + 1 := by rw [lapCount]; exact Nat.lt_succ_self _
  have hnotP : ¬ (fun n => returnTime T hτ n x ≤ t) (lapCount T hτ hc hcpos t x + 1) :=
    Nat.findGreatest_is_greatest hlt hkb
  simpa only [not_le] using hnotP

end LapCount

end Oseledets
