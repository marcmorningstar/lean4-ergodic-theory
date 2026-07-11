/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Entropy.KSEntropyPow
import ErgodicTheory.Continuous.SuspensionRescale
import ErgodicTheory.Continuous.Flow
import ErgodicTheory.Multifractal.BernoulliSuspensionEntropy

/-!
# Constant-roof suspension entropy descent: the time-`1` value for rational roofs

Let `φ` be a measure-preserving flow on a probability space. The discrete entropy power rule
`h(Tⁿ) = n · h(T)` (`ErgodicTheory.Entropy.ksEntropy_iterate`), applied to the time-`t` map
`φ_t` whose `n`-th iterate is the time-`(n·t)` map `φ_{n·t}` (`flow_iterate`), yields the
**flow entropy homogeneity along `ℕ`-multiples**:

`n • h(φ_t) = h(φ_{n·t})`  (`nsmul_ksEntropy_flow`).

Specialised to the constant-roof (`τ ≡ r`) suspension flow of the two-sided Bernoulli shift, this
computes the Kolmogorov–Sinai entropy of the **time-`1` map** whenever the roof `r` is **rational**:

`h(ζ^{(r)}_1) = h_base / r`  (`ksEntropy_bernConstSuspension_time_one`),

equivalently `h(ζ^{(r)}_1) · r = h_base` (`ksEntropy_bernConstSuspension_time_one_mul`), where
`h_base = Hnu ν` is the per-symbol Shannon entropy of the base. The route is:

1. **Fibre time-rescaling** (`ksEntropy_suspensionFlowMap_const_eq_unit`, the Abramov constant-roof
   time-change): `h(ζ^{(r)}_1) = h(ζ^{(1)}_{1/r})` reduces the `r`-roof time-`1` map to the
   unit-roof time-`(1/r)` map;
2. **Homogeneity along `ℕ`-multiples** for the unit-roof Bernoulli flow: writing `r = a / b` with
   `a, b : ℕ` positive, `a • h(ζ^{(1)}_{b/a}) = h(ζ^{(1)}_b) = b • h(ζ^{(1)}_1) = b · Hnu ν`, so
   `a • h(ζ^{(r)}_1) = b · Hnu ν`;
3. **Finiteness descent**: since `Hnu ν` is finite and `a > 0`, the `ℕ`-scalar equation
   `a • h(ζ^{(r)}_1) = ↑(b · Hnu ν)` pins `h(ζ^{(r)}_1) = ↑(b · Hnu ν / a) = ↑(Hnu ν / r)`
   (`ereal_eq_of_nsmul_eq_coe`); all `EReal` values are finite reals so the arithmetic descends to
   `ℝ`, avoiding `EReal` division/multiplication pitfalls.

## The irrational-roof wall (now closed downstream)

For an **irrational** roof `r`, the identity `h(ζ^{(r)}_1) = Hnu ν / r` needs the full **Abramov
flow-entropy homogeneity** `h(φ_t) = t · h(φ_1)` for *every* real time `t`, not just the rational
skeleton `h(φ_{n·t}) = n · h(φ_t)` along `ℕ`-multiples available here from the discrete power rule
(the multiplicative group `{a/b : a, b ∈ ℕ, b ≠ 0}` generated from a single positive time does not
reach irrational scalings, so the argument in *this* file is restricted to rational `r`).

**Status: this wall is now closed** — not by flow generators / Rokhlin towers, but by Ito's
*elementary* proof of Abramov's homogeneity theorem (Ito, *Nagoya Math. J.* **41** (1971)),
formalized in `ErgodicTheory.Continuous.FlowAbramov`
(`ErgodicTheory.ksEntropy_flow_eq_mul`: `h(φ_t) = t · h(φ_1)` for every measure-continuous flow).
Its keystone measure-continuity input for the suspension flow is
`ErgodicTheory.tendsto_measureReal_symmDiff_suspensionFlowMap`. The unconditional (every `r > 0`,
irrational allowed) time-`1` value is
`ErgodicTheory.ksEntropy_bernConstSuspension_time_one_irrational`. The rational-roof route below is
retained as the elementary special case that needs only the discrete power rule.

**Contrast with time-`1` ergodicity (issue #35).** The same constant-roof Bernoulli suspension
carries the *opposite* arithmetic restriction on the ergodicity side: the time-`1` map is ergodic
precisely when the roof `r` is **irrational**
(`ErgodicTheory.Multifractal.ergodic_suspensionFlow_timeOne_const_irrational`); for rational `r`
it is genuinely non-ergodic (e.g. `r = 1`:
`ErgodicTheory.Multifractal.not_ergodic_bernSuspensionFlow_one`). The two conditions are
complementary, not contradictory: the entropy value `Hnu ν / r` holds for *every* `r > 0` — only
its proof here is restricted to rational `r` — and Kolmogorov–Sinai entropy is defined (and equals
`Hnu ν / r`) also on the non-ergodic rational-roof time-`1` maps.

## Main results

* `ErgodicTheory.flow_iterate`: `(φ_t)^[n] = φ_{n·t}` for a measure-preserving flow `φ`.
* `ErgodicTheory.ksEntropy_flow_iterate`: `h((φ_t) iterated `n` times) = h(φ_{n·t})`.
* `ErgodicTheory.nsmul_ksEntropy_flow`: `n • h(φ_t) = h(φ_{n·t})`.
* `ErgodicTheory.nsmul_ksEntropy_bernSuspensionFlow_inv`: `b • h(ζ^{(1)}_{1/b}) = Hnu ν`.
* `ErgodicTheory.ksEntropy_bernSuspensionFlow_frac`: `h(ζ^{(1)}_{a/b}) = a • h(ζ^{(1)}_{1/b})`.
* `ErgodicTheory.ksEntropy_bernConstSuspension_time_one`: for rational `r = a/b`,
  `h(ζ^{(r)}_1) = ↑(Hnu ν / r)`.
* `ErgodicTheory.ksEntropy_bernConstSuspension_time_one_mul`: `h(ζ^{(r)}_1) · r = Hnu ν`.

## References

* L. M. Abramov, *On the entropy of a flow*, Dokl. Akad. Nauk SSSR **128** (1959), 873–875.
* P. Walters, *An Introduction to Ergodic Theory*, GTM **79**, Springer (1982), Theorem 4.13
  (discrete power rule) and §4.4 (flow entropy).
* W. Ambrose and S. Kakutani, *Structure and continuity of measurable flows*, Duke Math. J. **9**
  (1942), 25–42.
-/

open MeasureTheory

namespace ErgodicTheory

open Multifractal

/-! ### Flow iterates and the entropy homogeneity along `ℕ`-multiples -/

variable {X : Type*} [MeasurableSpace X]

/-- **Flow iterate identity.** For a measure-preserving flow `φ`, the `n`-th iterate of the
time-`t` map is the time-`(n·t)` map: `(φ_t)^[n] = φ_{n·t}`. Induction on `n` using
`Function.iterate_succ'` and the additivity `φ_{s+t} = φ_s ∘ φ_t`. -/
theorem flow_iterate {μ : Measure X} (φ : MeasurePreservingFlow μ) (t : ℝ) (n : ℕ) :
    (φ t)^[n] = φ ((n : ℝ) * t) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep : (φ ((↑(k + 1) : ℝ) * t)) = (φ t) ∘ (φ ((k : ℝ) * t)) := by
      rw [show ((↑(k + 1) : ℝ)) * t = t + (k : ℝ) * t by push_cast; ring, φ.map_add]
    rw [Function.iterate_succ', ih, hstep]

/-- **`ksEntropy` depends only on the underlying map.** Two measure-preserving witnesses with the
same underlying map (and measure) have equal Kolmogorov–Sinai entropy. Substituting the map
equality reduces both sides to `ksEntropy` of proof-irrelevant witnesses. -/
theorem ksEntropy_congr_of_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {T S : α → α} (hT : MeasurePreserving T μ μ)
    (hS : MeasurePreserving S μ μ) (h : T = S) :
    Entropy.ksEntropy hT = Entropy.ksEntropy hS := by
  subst h
  rfl

/-- **Iterate-entropy bridge.** The entropy of the `n`-th iterate of the time-`t` map equals the
entropy of the time-`(n·t)` map: the two measure-preserving witnesses have equal underlying maps
(`flow_iterate`), and `ksEntropy` depends only on the map. -/
theorem ksEntropy_flow_iterate {μ : Measure X} [IsProbabilityMeasure μ]
    (φ : MeasurePreservingFlow μ) (t : ℝ) (n : ℕ) :
    Entropy.ksEntropy ((φ.measurePreserving t).iterate n)
      = Entropy.ksEntropy (φ.measurePreserving ((n : ℝ) * t)) :=
  ksEntropy_congr_of_eq _ _ (flow_iterate φ t n)

/-- **Flow entropy homogeneity along `ℕ`-multiples:** `n • h(φ_t) = h(φ_{n·t})`. Combine the
discrete entropy power rule `h(Tⁿ) = n · h(T)` (`ErgodicTheory.Entropy.ksEntropy_iterate`) applied
to `T = φ_t` with the iterate-entropy bridge. -/
theorem nsmul_ksEntropy_flow {μ : Measure X} [IsProbabilityMeasure μ]
    (φ : MeasurePreservingFlow μ) (t : ℝ) (n : ℕ) :
    n • Entropy.ksEntropy (φ.measurePreserving t)
      = Entropy.ksEntropy (φ.measurePreserving ((n : ℝ) * t)) := by
  rw [← Entropy.ksEntropy_iterate (φ.measurePreserving t) n]
  exact ksEntropy_flow_iterate φ t n

/-! ### An `EReal` finiteness-descent helper -/

/-- If `a • x = ↑c` in `EReal` with `a : ℕ` positive and `c : ℝ`, then `x` is the finite value
`↑(c / a)`. The scalar product forces `x ≠ ⊥, ⊤` (else the left side would be `±∞`, not the finite
`↑c`), so `x = ↑y` for a real `y` with `a · y = c`, i.e. `y = c / a`. This lets an `ℕ`-scalar
`EReal` equation with a finite right side be solved entirely within `ℝ`. -/
private lemma ereal_eq_of_nsmul_eq_coe {a : ℕ} (ha : 0 < a) {x : EReal} {c : ℝ}
    (h : a • x = (c : EReal)) : x = ((c / (a : ℝ) : ℝ) : EReal) := by
  have haE : (0 : EReal) < (a : EReal) := by exact_mod_cast ha
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  rw [EReal.nsmul_eq_mul] at h
  induction x with
  | bot =>
      rw [EReal.mul_bot_of_pos haE] at h
      exact absurd h (EReal.bot_ne_coe c)
  | top =>
      rw [EReal.mul_top_of_pos haE] at h
      exact absurd h (EReal.top_ne_coe c)
  | coe y =>
      have hy : (a : ℝ) * y = c := by exact_mod_cast h
      rw [EReal.coe_eq_coe_iff, eq_div_iff haR, mul_comm]
      exact hy

/-! ### The unit-roof packaging bridge -/

/-- **Definitional bridge.** The unit-roof (`τ ≡ 1`) time-`s` suspension flow map produced by the
rescale module (`measurePreserving_suspensionFlowMap … (measurable_constFun 1) …`) is *the same map*
as the time-`s` map of the `bernSuspensionFlow` packaging; hence their entropies coincide (`rfl`,
via proof irrelevance and the definitional unfolding of `bernSuspensionFlow`). -/
theorem ksEntropy_unit_flow_eq {α₀ : Type*} [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
    (ν : Measure α₀) [IsProbabilityMeasure ν] (s : ℝ) :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
        (measurable_constFun (1 : ℝ)) (measurePreserving_biShiftEquiv_bernZ ν)
        (fun _ => le_refl (1 : ℝ)) one_pos s)
      = Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving s) := rfl

/-! ### Unit-roof Bernoulli suspension: fractional-time entropy -/

variable {α₀ : Type*} [Fintype α₀] [MeasurableSpace α₀] [MeasurableSingletonClass α₀]

/-- **Unit-roof reciprocal time.** For `b : ℕ` positive, `b • h(ζ^{(1)}_{1/b}) = Hnu ν`. Apply the
flow homogeneity `nsmul_ksEntropy_flow` at `t = 1/b, n = b` (so `b · (1/b) = 1`) and the unit-roof
time-`1` value `h(ζ^{(1)}_1) = Hnu ν` (`ksEntropy_bernSuspensionFlow_one_eq_Hnu`).

This is the primary (multiplicative) statement: since `Hnu ν` is finite it determines
`h(ζ^{(1)}_{1/b}) = Hnu ν / b`, but the `EReal` value is left in `ℕ`-scalar form to avoid `EReal`
division. -/
theorem nsmul_ksEntropy_bernSuspensionFlow_inv (ν : Measure α₀) [IsProbabilityMeasure ν]
    {b : ℕ} (hb : 0 < b) :
    b • Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving (1 / (b : ℝ)))
      = ((Hnu ν : ℝ) : EReal) := by
  have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  rw [nsmul_ksEntropy_flow (bernSuspensionFlow ν) (1 / (b : ℝ)) b,
    show (b : ℝ) * (1 / (b : ℝ)) = 1 from by field_simp]
  exact ksEntropy_bernSuspensionFlow_one_eq_Hnu ν

omit [Fintype α₀] [MeasurableSingletonClass α₀] in
/-- **Unit-roof rational time from the reciprocal time.** `h(ζ^{(1)}_{a/b}) = a • h(ζ^{(1)}_{1/b})`.
Immediate from the flow homogeneity `nsmul_ksEntropy_flow` at `t = 1/b, n = a` since
`a · (1/b) = a/b`. -/
theorem ksEntropy_bernSuspensionFlow_frac (ν : Measure α₀) [IsProbabilityMeasure ν] (a b : ℕ) :
    Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving ((a : ℝ) / (b : ℝ)))
      = a • Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving (1 / (b : ℝ))) := by
  rw [nsmul_ksEntropy_flow (bernSuspensionFlow ν) (1 / (b : ℝ)) a, mul_one_div]

/-! ### The target: constant-roof time-`1` entropy for rational roofs -/

/-- **Constant-roof time-`1` entropy (rational roof).** For a rational roof `r = a/b`
(`a, b : ℕ` positive), the time-`1` map of the constant-roof (`τ ≡ r`) Bernoulli suspension flow has
Kolmogorov–Sinai entropy `Hnu ν / r`.

Proof: fibre time-rescaling reduces `h(ζ^{(r)}_1)` to the unit-roof `h(ζ^{(1)}_{1/r})`
(`ksEntropy_suspensionFlowMap_const_eq_unit` at `t = 1`, then the definitional bridge
`ksEntropy_unit_flow_eq`); the flow homogeneity gives `a • h(ζ^{(1)}_{1/r}) = b · Hnu ν`
(via `1/r = b/a`, `a • h(ζ^{(1)}_{b/a}) = h(ζ^{(1)}_b) = b • h(ζ^{(1)}_1) = b · Hnu ν`); and the
finiteness descent `ereal_eq_of_nsmul_eq_coe` pins the value, the final identity
`b · Hnu ν / a = Hnu ν / r` being real arithmetic. -/
theorem ksEntropy_bernConstSuspension_time_one (ν : Measure α₀) [IsProbabilityMeasure ν] (r : ℝ)
    [hr : Fact (0 < r)] {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hrab : r = a / b) :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
        (measurable_constFun r) (measurePreserving_biShiftEquiv_bernZ ν)
        (fun _ => le_refl r) hr.out 1)
      = ((Hnu ν / r : ℝ) : EReal) := by
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hbridge :
      Entropy.ksEntropy (measurePreserving_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
          (measurable_constFun r) (measurePreserving_biShiftEquiv_bernZ ν)
          (fun _ => le_refl r) hr.out 1)
        = Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving (1 / r)) := by
    rw [ksEntropy_suspensionFlowMap_const_eq_unit biShiftEquiv r 1
      (measurePreserving_biShiftEquiv_bernZ ν)]
    exact ksEntropy_unit_flow_eq ν (1 / r)
  have hkey : a • Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving (1 / r))
      = ((((b : ℝ) * Hnu ν) : ℝ) : EReal) := by
    rw [show (1 : ℝ) / r = (b : ℝ) / (a : ℝ) from by rw [hrab, one_div_div]]
    rw [nsmul_ksEntropy_flow (bernSuspensionFlow ν) ((b : ℝ) / (a : ℝ)) a,
      show (a : ℝ) * ((b : ℝ) / (a : ℝ)) = (b : ℝ) from by field_simp]
    have hbb : Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving (b : ℝ))
        = b • Entropy.ksEntropy ((bernSuspensionFlow ν).measurePreserving 1) := by
      rw [nsmul_ksEntropy_flow (bernSuspensionFlow ν) 1 b, mul_one]
    rw [hbb, ksEntropy_bernSuspensionFlow_one_eq_Hnu ν, ← EReal.coe_nsmul, nsmul_eq_mul]
  rw [hbridge, ereal_eq_of_nsmul_eq_coe ha hkey, EReal.coe_eq_coe_iff, hrab]
  field_simp

/-- **Constant-roof time-`1` entropy, multiplicative form.** For a rational roof `r = a/b`,
`h(ζ^{(r)}_1) · r = Hnu ν`. Multiply the value form `ksEntropy_bernConstSuspension_time_one` by `r`;
the `EReal` product collapses to real arithmetic `(Hnu ν / r) · r = Hnu ν`. -/
theorem ksEntropy_bernConstSuspension_time_one_mul (ν : Measure α₀) [IsProbabilityMeasure ν]
    (r : ℝ) [hr : Fact (0 < r)] {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hrab : r = a / b) :
    Entropy.ksEntropy (measurePreserving_suspensionFlowMap (biShiftEquiv (α₀ := α₀))
        (measurable_constFun r) (measurePreserving_biShiftEquiv_bernZ ν)
        (fun _ => le_refl r) hr.out 1) * (r : EReal)
      = ((Hnu ν : ℝ) : EReal) := by
  have hrne : r ≠ 0 := hr.out.ne'
  rw [ksEntropy_bernConstSuspension_time_one ν r ha hb hrab, ← EReal.coe_mul,
    EReal.coe_eq_coe_iff]
  field_simp

end ErgodicTheory
