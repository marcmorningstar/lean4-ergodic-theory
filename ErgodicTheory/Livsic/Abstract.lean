/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.HolderExtend
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Livšic theorem: the substantive (cohomological rigidity) direction

This file proves the hard direction of the **Livšic theorem** (issue #29): over a
hyperbolic-type map `T : X → X` on a compact metric space carrying a dense forward orbit, a Hölder
observable `φ` whose periodic Birkhoff sums all vanish is a Hölder coboundary `φ = v ∘ T - v`.
Together with the trivial direction from `ErgodicTheory.Livsic.Defs` this yields the headline
equivalence `isHolderCoboundary_iff`.

The argument follows the classical **dense-orbit construction** (Katok–Hasselblatt, *Introduction
to the Modern Theory of Dynamical Systems*, Thm 19.2.1): define the transfer function on the dense
orbit by the running Birkhoff sums, show it is Hölder there via the exponential-closing/geometric
control estimate, extend it to all of `X` by the McShane–Whitney Hölder extension
(`ErgodicTheory.Livsic.exists_holderWith_extension`), and transport the on-orbit cohomology
identity to the whole space by density and continuity.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972), 1278–1301.
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge Univ. Press (1995), Theorem 19.2.1.
* W. Parry, M. Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic
  dynamics*, Astérisque **187–188** (1990), Ch. 3, Prop. 3.7 (one-sided/expanding case).

The `ExpClosing` hypothesis is stated in *summed-bound* form (see `ErgodicTheory.Livsic.Defs`):
this single abstraction covers both the two-sided Anosov `θ ^ min(i, n-i)` regime and the
one-sided/expanding front-anchored `θ ^ (n-i)` regime, so the same crux estimate serves both.

## Main results

* `abs_birkhoffSum_le` — the crux estimate: an almost-`n`-return has Birkhoff sum bounded by the
  return gap.
* `birkhoffSum_eq_of_orbit_eq` / `birkhoffSum_eq_of_orbit_eq'` — well-definedness of the transfer
  values along the orbit.
* `abs_birkhoffSum_orbit_sub_le` — the close-pair orbit increment (modulus of continuity) bound.
* `exists_bound_of_closePairHolder` — a function with a uniform close-pair Hölder modulus on a
  dense subset of a compact metric space is bounded on it.
* `holderOnWith_of_closePairHolder_bounded` — a bounded function with a close-pair Hölder modulus
  is genuinely `HolderOnWith` (the far-pair case is absorbed into a larger constant).
* `exists_holderCoboundary_of_denseOrbit` — the existence theorem (Katok–Hasselblatt 19.2.1).
* `isHolderCoboundary_iff` — the headline Livšic equivalence.
-/

open Function
open scoped NNReal ENNReal

namespace ErgodicTheory

section Crux

variable {X : Type*} [MetricSpace X]

/-- **The crux Livšic estimate.** Subtract the (vanishing) periodic Birkhoff sum of the
shadowing point `p` from that of `x`, bound each term by Hölder continuity, and collapse the
per-step shadowing costs through the *summed* exponential closing bound. No hypothesis on the
Hölder exponent `r` is needed: the closing exponent and the Hölder exponent are the same `r`, so
the geometric bookkeeping matches term by term. -/
theorem abs_birkhoffSum_le {T : X → X} {φ : X → ℝ} {Cφ r : ℝ≥0}
    (hφ : HolderWith Cφ r φ) {δ K : ℝ} (hclosing : ExpClosing T (r : ℝ) δ K)
    (hvps : HasVanishingPeriodicSums T φ) {n : ℕ} {x : X}
    (hx : dist x (T^[n] x) ≤ δ) :
    |birkhoffSum T φ n x| ≤ (Cφ : ℝ) * K * dist x (T^[n] x) ^ (r : ℝ) := by
  obtain ⟨p, hp_fix, hclose⟩ := hclosing n x hx
  have hp0 : birkhoffSum T φ n p = 0 := hvps n p hp_fix
  have hbx : birkhoffSum T φ n x
      = ∑ i ∈ Finset.range n, (φ (T^[i] x) - φ (T^[i] p)) := by
    simp only [birkhoffSum] at hp0 ⊢
    rw [Finset.sum_sub_distrib, hp0, sub_zero]
  rw [hbx]
  calc |∑ i ∈ Finset.range n, (φ (T^[i] x) - φ (T^[i] p))|
      ≤ ∑ i ∈ Finset.range n, |φ (T^[i] x) - φ (T^[i] p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (Cφ : ℝ) * dist (T^[i] x) (T^[i] p) ^ (r : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Real.dist_eq]
        exact hφ.dist_le _ _
    _ = (Cφ : ℝ) * ∑ i ∈ Finset.range n, dist (T^[i] x) (T^[i] p) ^ (r : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ (Cφ : ℝ) * (K * dist x (T^[n] x) ^ (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hclose (by positivity)
    _ = (Cφ : ℝ) * K * dist x (T^[n] x) ^ (r : ℝ) := by ring

end Crux

section WellDefined

variable {X : Type*}

/-- **Well-definedness (ordered form).** If two orbit indices `n ≤ m` land on the same point,
their Birkhoff sums agree. The difference is a Birkhoff sum around the periodic orbit of
`T^[n] x₀` (period `m - n`), which vanishes. Pure algebra — no metric, no closing. -/
theorem birkhoffSum_eq_of_orbit_eq {T : X → X} {φ : X → ℝ}
    (hvps : HasVanishingPeriodicSums T φ) {x₀ : X} {n m : ℕ}
    (hnm : n ≤ m) (h : T^[n] x₀ = T^[m] x₀) :
    birkhoffSum T φ n x₀ = birkhoffSum T φ m x₀ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  have hper : T^[k] (T^[n] x₀) = T^[n] x₀ := by
    rw [← Function.iterate_add_apply, Nat.add_comm k n, ← h]
  have hzero : birkhoffSum T φ k (T^[n] x₀) = 0 := hvps _ _ hper
  rw [birkhoffSum_add, hzero, add_zero]

/-- **Well-definedness (symmetric form).** Equal orbit points give equal Birkhoff sums,
irrespective of the order of the two indices. This is the exact statement needed to define the
transfer function on the orbit from its values along `ℕ`. -/
theorem birkhoffSum_eq_of_orbit_eq' {T : X → X} {φ : X → ℝ}
    (hvps : HasVanishingPeriodicSums T φ) {x₀ : X} {n m : ℕ}
    (h : T^[n] x₀ = T^[m] x₀) :
    birkhoffSum T φ n x₀ = birkhoffSum T φ m x₀ := by
  rcases le_total n m with hnm | hmn
  · exact birkhoffSum_eq_of_orbit_eq hvps hnm h
  · exact (birkhoffSum_eq_of_orbit_eq hvps hmn h.symm).symm

end WellDefined

section OrbitIncrement

variable {X : Type*} [MetricSpace X]

/-- **The close-pair orbit increment bound.** For orbit points `T^[a] x₀` and `T^[b] x₀`
(`a ≤ b`) within `δ`, the transfer-function increment `w b - w a` (a difference of Birkhoff sums)
is `r`-Hölder in their distance. Proof: `birkhoffSum_add` rewrites the increment as the Birkhoff
sum of length `b - a` started at `T^[a] x₀`, whose almost-return gap is exactly the distance
between the two orbit points; then apply the crux `abs_birkhoffSum_le`. This is the modulus of
continuity that feeds the Hölder extension. -/
theorem abs_birkhoffSum_orbit_sub_le {T : X → X} {φ : X → ℝ} {Cφ r : ℝ≥0}
    (hφ : HolderWith Cφ r φ) {δ K : ℝ} (hclosing : ExpClosing T (r : ℝ) δ K)
    (hvps : HasVanishingPeriodicSums T φ) {x₀ : X} {a b : ℕ} (hab : a ≤ b)
    (hx : dist (T^[a] x₀) (T^[b] x₀) ≤ δ) :
    |birkhoffSum T φ b x₀ - birkhoffSum T φ a x₀|
      ≤ (Cφ : ℝ) * K * dist (T^[a] x₀) (T^[b] x₀) ^ (r : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  have hsplit : birkhoffSum T φ (a + k) x₀ - birkhoffSum T φ a x₀
      = birkhoffSum T φ k (T^[a] x₀) := by
    rw [birkhoffSum_add]; ring
  rw [hsplit]
  have hdist : dist (T^[a] x₀) (T^[k] (T^[a] x₀)) = dist (T^[a] x₀) (T^[a + k] x₀) := by
    rw [← Function.iterate_add_apply, Nat.add_comm k a]
  have hx' : dist (T^[a] x₀) (T^[k] (T^[a] x₀)) ≤ δ := by rw [hdist]; exact hx
  have hbound := abs_birkhoffSum_le hφ hclosing hvps hx'
  rwa [hdist] at hbound

end OrbitIncrement

section BoundedHolder

variable {X : Type*} [MetricSpace X]

/-- **Boundedness from a close-pair Hölder modulus on a dense subset of a compact space.** If `u`
obeys a uniform Hölder bound `|u x - u y| ≤ C · dist x y ^ r` for *close* pairs (`dist ≤ δ`) of a
dense set `s` in a compact metric space, then `u` is bounded on `s`. Proof: a finite `δ/2`-net
(total boundedness) with a representative of `s` in each ball reduces every point of `s` to within
`δ` of one of finitely many representatives, on which `|u|` is finite. -/
theorem exists_bound_of_closePairHolder [CompactSpace X] {s : Set X} (hs : Dense s)
    {u : X → ℝ} {C δ : ℝ} {r : ℝ≥0} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hclose : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ δ → |u x - u y| ≤ C * dist x y ^ (r : ℝ)) :
    ∃ M : ℝ, ∀ x ∈ s, |u x| ≤ M := by
  classical
  obtain ⟨t, htfin, hcov⟩ :=
    Metric.totallyBounded_iff.1
      (isCompact_univ : IsCompact (Set.univ : Set X)).totallyBounded (δ / 2) (by linarith)
  -- A representative of `s` inside each `δ/2`-ball (density meets every nonempty open set).
  have hrep : ∀ y : X, ∃ z, z ∈ s ∧ dist z y < δ / 2 := by
    intro y
    obtain ⟨z, hzs, hzU⟩ :=
      hs.exists_mem_open Metric.isOpen_ball (Metric.nonempty_ball.2 (by linarith : (0 : ℝ) < δ / 2))
    exact ⟨z, hzs, Metric.mem_ball.1 hzU⟩
  choose z hz_s hz_dist using hrep
  -- `|u|` is bounded over the finite set of representative values.
  obtain ⟨M₀, hM₀⟩ := (htfin.image fun y => |u (z y)|).bddAbove
  refine ⟨M₀ + C * δ ^ (r : ℝ), fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ x))
  rw [Metric.mem_ball] at hxy
  have hdxz : dist x (z y) ≤ δ := by
    have htri : dist x (z y) ≤ dist x y + dist y (z y) := dist_triangle _ _ _
    have hcm : dist y (z y) = dist (z y) y := dist_comm _ _
    have := hz_dist y
    linarith
  have hbnd : |u x - u (z y)| ≤ C * dist x (z y) ^ (r : ℝ) := hclose x hx (z y) (hz_s y) hdxz
  have hmono : dist x (z y) ^ (r : ℝ) ≤ δ ^ (r : ℝ) :=
    Real.rpow_le_rpow dist_nonneg hdxz r.coe_nonneg
  have hCmono : C * dist x (z y) ^ (r : ℝ) ≤ C * δ ^ (r : ℝ) :=
    mul_le_mul_of_nonneg_left hmono hC
  have hMy : |u (z y)| ≤ M₀ := hM₀ (Set.mem_image_of_mem _ hy)
  have habs : |u x| ≤ |u x - u (z y)| + |u (z y)| := by
    have h := abs_add_le (u x - u (z y)) (u (z y))
    simpa using h
  linarith

/-- **From a close-pair Hölder modulus plus a bound to a genuine Hölder bound.** If `u` obeys a
uniform Hölder bound `|u x - u y| ≤ C · dist x y ^ r` for *close* pairs (`dist ≤ δ`) of `s` and is
bounded by `M` on `s`, then `u` is `HolderOnWith` on `s` for a (larger) constant. For close pairs
the given bound applies directly; for far pairs (`dist > δ`) the gap `|u x - u y| ≤ 2M` is absorbed
by the constant `2M / δ ^ r`, using `δ ^ r ≤ dist x y ^ r`. -/
theorem holderOnWith_of_closePairHolder_bounded {s : Set X} {u : X → ℝ} {C δ M : ℝ} {r : ℝ≥0}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hclose : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ δ → |u x - u y| ≤ C * dist x y ^ (r : ℝ))
    (hbound : ∀ x ∈ s, |u x| ≤ M) :
    ∃ C' : ℝ≥0, HolderOnWith C' r u s := by
  set Dr : ℝ := δ ^ (r : ℝ)
  have hDrpos : 0 < Dr := Real.rpow_pos_of_pos hδ _
  set C'r : ℝ := max C (2 * M / Dr)
  have hC'r_nonneg : 0 ≤ C'r := le_trans hC (le_max_left _ _)
  refine ⟨C'r.toNNReal, holderOnWith_of_dist_le fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal C'r hC'r_nonneg, Real.dist_eq]
  by_cases hle : dist x y ≤ δ
  · have h := hclose x hx y hy hle
    have hd : (0 : ℝ) ≤ dist x y ^ (r : ℝ) := Real.rpow_nonneg dist_nonneg _
    calc |u x - u y| ≤ C * dist x y ^ (r : ℝ) := h
      _ ≤ C'r * dist x y ^ (r : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hd
  · rw [not_le] at hle
    have hddr : Dr ≤ dist x y ^ (r : ℝ) := Real.rpow_le_rpow hδ.le hle.le r.coe_nonneg
    have hfrac_nonneg : 0 ≤ 2 * M / Dr := div_nonneg (by linarith) hDrpos.le
    have hcancel : 2 * M / Dr * Dr = 2 * M := div_mul_cancel₀ (2 * M) hDrpos.ne'
    have h2M : 2 * M ≤ C'r * dist x y ^ (r : ℝ) := by
      have step1 : 2 * M / Dr * Dr ≤ 2 * M / Dr * dist x y ^ (r : ℝ) :=
        mul_le_mul_of_nonneg_left hddr hfrac_nonneg
      have step2 : 2 * M / Dr * dist x y ^ (r : ℝ) ≤ C'r * dist x y ^ (r : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
      linarith [hcancel]
    have habs : |u x - u y| ≤ 2 * M := by
      have hx' := hbound x hx
      have hy' := hbound y hy
      calc |u x - u y| = |u x + -u y| := by rw [sub_eq_add_neg]
        _ ≤ |u x| + |-u y| := abs_add_le _ _
        _ = |u x| + |u y| := by rw [abs_neg]
        _ ≤ 2 * M := by linarith
    linarith

end BoundedHolder

section MainDirection

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Abstract existence (Katok–Hasselblatt 19.2.1).** Given a dense forward orbit under a
continuous `T` on a compact metric space, a Hölder `φ`, the summed exponential closing property,
and vanishing periodic sums, `φ` is a Hölder coboundary.

Construction:
* `e n := T^[n] x₀`, `w n := birkhoffSum T φ n x₀`, and the transfer function on the orbit
  `u₀ y := w (Function.invFun e y)`;
* `hu₀` — `u₀ (e m) = w m` (well-definedness `birkhoffSum_eq_of_orbit_eq'` through `invFun`);
* the close-pair increment `abs_birkhoffSum_orbit_sub_le` gives a Hölder modulus on the orbit;
  boundedness (`exists_bound_of_closePairHolder`, using compactness) upgrades it to a genuine
  `HolderOnWith` (`holderOnWith_of_closePairHolder_bounded`);
* apply `exists_holderWith_extension` to get a global Hölder `v` agreeing with `u₀` on the orbit;
* the on-orbit cohomology identity `φ (e m) = v (e (m+1)) - v (e m)` with `e (m+1) = T (e m)`,
  transported to all of `X` by density + continuity (`Continuous.ext_on`). -/
theorem exists_holderCoboundary_of_denseOrbit {T : X → X} (hT : Continuous T)
    {φ : X → ℝ} {Cφ r : ℝ≥0} (hr0 : 0 < r) (hr1 : r ≤ 1) (hφ : HolderWith Cφ r φ)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hclosing : ExpClosing T (r : ℝ) δ K)
    (hvps : HasVanishingPeriodicSums T φ)
    {x₀ : X} (hdense : DenseRange fun n : ℕ => T^[n] x₀) :
    IsHolderCoboundary T φ := by
  classical
  -- The orbit enumeration and the raw transfer values along `ℕ`.
  set e : ℕ → X := fun n => T^[n] x₀ with he
  set w : ℕ → ℝ := fun n => birkhoffSum T φ n x₀ with hw
  -- The transfer function on the orbit, via a chosen preimage index.
  set u₀ : X → ℝ := fun y => w (Function.invFun e y) with hu₀def
  -- `u₀` reads off the Birkhoff sum at any index landing on the given orbit point.
  have hu₀ : ∀ m, u₀ (e m) = w m := by
    intro m
    have hpre : e (Function.invFun e (e m)) = e m :=
      Function.invFun_eq ⟨m, rfl⟩
    simp only [hu₀def]
    exact birkhoffSum_eq_of_orbit_eq' hvps hpre
  -- The successor step of the orbit: `e (m+1) = T (e m)`.
  have he_succ : ∀ m, e (m + 1) = T (e m) := by
    intro m; simp only [he, Function.iterate_succ_apply']
  -- The Birkhoff successor identity, in `w`-form.
  have hw_succ : ∀ m, w (m + 1) = w m + φ (e m) := by
    intro m; simp only [hw, he, birkhoffSum_succ]
  -- The close-pair Hölder modulus on the orbit, from `abs_birkhoffSum_orbit_sub_le`.
  have hCK : (0 : ℝ) ≤ (Cφ : ℝ) * K := mul_nonneg Cφ.coe_nonneg hK
  have hclose_orbit : ∀ x ∈ Set.range e, ∀ y ∈ Set.range e, dist x y ≤ δ →
      |u₀ x - u₀ y| ≤ (Cφ : ℝ) * K * dist x y ^ (r : ℝ) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hd
    rw [hu₀ a, hu₀ b]
    rcases le_total a b with hab | hba
    · rw [abs_sub_comm]
      exact abs_birkhoffSum_orbit_sub_le hφ hclosing hvps hab hd
    · have hd' : dist (e b) (e a) ≤ δ := by rw [dist_comm]; exact hd
      rw [dist_comm (e a) (e b)]
      exact abs_birkhoffSum_orbit_sub_le hφ hclosing hvps hba hd'
  -- Boundedness of `u₀` on the orbit (compactness), then a genuine `HolderOnWith`.
  obtain ⟨M, hM⟩ := exists_bound_of_closePairHolder hdense hδ hCK hclose_orbit
  have hM'0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hM' : ∀ x ∈ Set.range e, |u₀ x| ≤ max M 0 :=
    fun x hx => le_trans (hM x hx) (le_max_left _ _)
  obtain ⟨C', horbit_holder⟩ :=
    holderOnWith_of_closePairHolder_bounded hδ hCK hM'0 hclose_orbit hM'
  -- Extend to a global Hölder function agreeing with `u₀` on the orbit.
  obtain ⟨v, hv_holder, hv_eqon⟩ :=
    exists_holderWith_extension hr0 hr1 horbit_holder
  -- On-orbit cohomology: `φ (e m) = v (e (m+1)) - v (e m)`.
  have hv_orbit : ∀ m, v (e m) = w m := fun m => (hv_eqon ⟨m, rfl⟩).symm.trans (hu₀ m)
  have hcohom_orbit : ∀ m, φ (e m) = v (T (e m)) - v (e m) := by
    intro m
    rw [← he_succ, hv_orbit (m + 1), hv_orbit m, hw_succ]
    ring
  -- Transport the cohomology identity to all of `X` by density + continuity.
  have hφc : Continuous φ := hφ.continuous hr0
  have hvc : Continuous v := hv_holder.continuous hr0
  have hgc : Continuous fun x => v (T x) - v x := (hvc.comp hT).sub hvc
  have hEq : φ = fun x => v (T x) - v x := by
    refine Continuous.ext_on hdense hφc hgc ?_
    rintro y ⟨m, rfl⟩
    exact hcohom_orbit m
  exact ⟨C', r, v, hr0, hv_holder, fun x => congrFun hEq x⟩

/-- **The headline Livšic iff.** A Hölder observable over a compact system with a dense
orbit and the summed exponential closing property is a Hölder coboundary **iff** all of its
periodic Birkhoff sums vanish. The forward direction is the pure telescoping obstruction (`Defs`);
the backward direction is `exists_holderCoboundary_of_denseOrbit`. -/
theorem isHolderCoboundary_iff {T : X → X} (hT : Continuous T)
    {φ : X → ℝ} {Cφ r : ℝ≥0} (hr0 : 0 < r) (hr1 : r ≤ 1) (hφ : HolderWith Cφ r φ)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hclosing : ExpClosing T (r : ℝ) δ K)
    {x₀ : X} (hdense : DenseRange fun n : ℕ => T^[n] x₀) :
    IsHolderCoboundary T φ ↔ HasVanishingPeriodicSums T φ :=
  ⟨fun h => h.isCoboundary.hasVanishingPeriodicSums,
   fun h => exists_holderCoboundary_of_denseOrbit hT hr0 hr1 hφ hδ hK hclosing h hdense⟩

end MainDirection

end ErgodicTheory
