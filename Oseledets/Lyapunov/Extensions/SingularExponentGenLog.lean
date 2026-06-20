/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Extensions.SingularExponent

/-!
# The genuine-`log` forward singular exponent `γ_k^log` (`EReal`-valued)

For a **possibly-singular** matrix cocycle generator `A : X → Matrix (Fin d) (Fin d) ℝ` — no
`det A ≠ 0`, no inverse integrability, only forward integrability — this module packages the
cumulative **genuine-`log`** forward singular exponent

`γ_k^log(x) = limsup_n ((1/n) log sprod_k(A⁽ⁿ⁾ x) : EReal)`,

built from the *honest* logarithm `Real.log` (NOT the positive part `Real.posLog` used in
`Oseledets.forwardSingularExponent`). Here `sprod_k = Oseledets.sprod A T k` is the top-`k`
singular-value product (the `k`-volume growth).

This is the right object for the **`−∞` kernel / volume-collapse stratum** of the Raghunathan /
Quas non-invertible multiplicative ergodic theorem. When the cocycle collapses `k`-volume
(`sprod_k → 0`), the genuine `log sprod_k → −∞`, so `γ_k^log` can attain the bottom value `⊥` of
`EReal` — a regime the `log⁺` exponent `γ_k` *cannot* see (it is pinned at `0` there). The `log⁺`
exponent records only the *expanding* part of the spectrum; this genuine-`log` exponent is what
detects the singular `−∞` exponent on the kernel stratum.

The non-invertible MET via exterior algebra, the singular value decomposition, and Kingman's
subadditive ergodic theorem (the Raghunathan approach) is the structure followed here; see
A. Quas, *Multiplicative Ergodic Theorems and Applications* (Theorem 2, §3.1; method due to
M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*, Israel J. Math. **32**
(1979), 356–362).

## Main definitions

* `Oseledets.forwardSingularExponentLog` — the genuine-`log` cumulative forward singular exponent
  `γ_k^log`, an `EReal`-valued `limsup`, defined for every `x` with no invertibility hypothesis.
  It can equal `⊥` (the kernel / volume-collapse regime).

## Main results

* `Oseledets.measurable_forwardSingularExponentLog` — `γ_k^log` is measurable.
* `Oseledets.forwardSingularExponentLog_le` — `γ_k^log(x) ≤ γ_k(x)` for **every** `x`
  (deterministic), where `γ_k = Oseledets.forwardSingularExponent` is the `log⁺` exponent. Since
  `log ≤ log⁺` termwise, the genuine-`log` exponent is always dominated by the `log⁺` one; the gap
  is exactly the collapse `−∞` stratum invisible to `log⁺`.
* `Oseledets.forwardSingularExponentLog_eq_bot_of_tendsto` — the **`−∞` kernel stratum hook**: if
  `(1/n) log sprod_k(A⁽ⁿ⁾ x) → −∞` (the `k`-volume collapses super-exponentially), then
  `γ_k^log(x) = ⊥`.

## Implementation notes

* Everything here rests only on `Oseledets.sprod` and the `EReal`-`limsup`/`Real.log`
  infrastructure; no `det A ≠ 0`, no `log⁺‖A⁻¹‖ ∈ L¹`. The genuine-`log` `limsup` need **not**
  converge for a singular cocycle (it may fall to `−∞`), which is the whole point: it captures the
  collapse the `log⁺` packaging deliberately discards.
* The companion `log⁺` exponent (`Oseledets.forwardSingularExponent`) is `μ`-a.e. a finite real
  constant; the genuine-`log` exponent here is **only** bounded *above* by it (a.e. by
  `forwardSingularExponentLog_le`). The two coincide a.e. precisely on the non-collapsing
  (expanding) stratum where `γ_k > 0` (cf. `Oseledets.limsup_logSprod_eq_top_of_pos`); on the
  collapse stratum the genuine-`log` exponent drops strictly, possibly to `⊥`.

## References

* A. Quas, *Multiplicative Ergodic Theorems and Applications*, lecture notes (Theorem 2 and §3.1,
  the non-invertible form via SVD + exterior algebra + Kingman; Raghunathan's method).
* M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*,
  Israel J. Math. **32** (1979), 356–362.
* M. Viana, *Lectures on Lyapunov Exponents*, Cambridge Studies in Adv. Math. **145** (2014).
-/

open MeasureTheory Filter Topology

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {T : X → X} {d : ℕ}

/-- **The genuine-`log` forward singular exponent `γ_k^log`** of a possibly-singular cocycle
generator, as an `EReal`-valued `limsup`:

`γ_k^log(x) = limsup_n ((1/n) log sprod_k(A⁽ⁿ⁾ x) : EReal)`,

where `sprod_k = Oseledets.sprod A T k` is the top-`k` singular-value product. Unlike the `log⁺`
exponent `Oseledets.forwardSingularExponent`, this uses the **genuine** `Real.log`, so it can equal
`⊥` when the `k`-volume collapses (`sprod_k → 0`, the kernel stratum of the non-invertible MET). -/
noncomputable def forwardSingularExponentLog (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k : ℕ) (x : X) : EReal :=
  Filter.limsup
    (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log (sprod A T k n x) : ℝ) : EReal)) atTop

/-- **`γ_k^log` is measurable.** Each `x ↦ (1/n) log sprod_k(A⁽ⁿ⁾ x)` is measurable: `sprod` is
measurable (`measurable_sprod`, which carries `[NeZero d]`), `Real.log` is measurable
(`Real.measurable_log`), and the scalar multiply is too; its `ℝ → EReal` coercion is measurable
(`measurable_coe_real_ereal`), and the `ℕ`-`limsup` of measurable `EReal`-valued functions is
measurable (`Measurable.limsup`). Mirrors `measurable_forwardSingularExponent`. -/
theorem measurable_forwardSingularExponentLog [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hAmeas : Measurable A) (hTmeas : Measurable T) (k : ℕ) :
    Measurable (forwardSingularExponentLog A T k) := by
  refine Measurable.limsup (fun n => ?_)
  refine measurable_coe_real_ereal.comp ?_
  have hlog : Measurable fun x => Real.log (sprod A T k n x) :=
    Real.measurable_log.comp (measurable_sprod hAmeas hTmeas k n)
  exact measurable_const.mul hlog

omit [MeasurableSpace X] in
/-- **`γ_k^log(x) ≤ γ_k(x)` for every `x`** (deterministic, no hypotheses), where `γ_k` is the
`log⁺` exponent `Oseledets.forwardSingularExponent`. Termwise `Real.log t ≤ Real.posLog t`, so
`(1/n) log sprod_k ≤ (1/n) log⁺ sprod_k` for every `n` (the factor `(n:ℝ)⁻¹ ≥ 0`); coercing to
`EReal` (`EReal.coe_le_coe_iff`) and using monotonicity of the `EReal`-`limsup`
(`Filter.limsup_le_limsup` with the everywhere-`≤`) yields the bound. The genuine-`log` exponent is
thus always dominated by the `log⁺` one; the gap is the collapse `−∞` stratum `log⁺` cannot see. -/
theorem forwardSingularExponentLog_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (k : ℕ) (x : X) :
    forwardSingularExponentLog A T k x ≤ forwardSingularExponent A T k x := by
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
  refine EReal.coe_le_coe_iff.2 ?_
  have hposLog : Real.log (sprod A T k n x) ≤ Real.posLog (sprod A T k n x) := by
    rw [Real.posLog_def]; exact le_max_right _ _
  exact mul_le_mul_of_nonneg_left hposLog (by positivity)

omit [MeasurableSpace X] in
/-- **The `−∞` kernel / volume-collapse stratum hook.** If the normalized genuine log-volume
`(1/n) log sprod_k(A⁽ⁿ⁾ x)` tends to `−∞` (the top-`k` volume collapses super-exponentially — the
kernel stratum of the non-invertible Raghunathan/Quas MET), then the genuine-`log` exponent attains
the bottom value: `γ_k^log(x) = ⊥`. The real sequence tending to `atBot` makes its `ℝ → EReal`
coercion converge to `𝓝 ⊥` (`EReal.tendsto_coe_nhds_bot_iff`), and the `EReal`-`limsup` of a
convergent sequence is its limit (`Filter.Tendsto.limsup_eq`). This is the exponent the `log⁺`
packaging cannot record (`forwardSingularExponent ≥ 0` always). -/
theorem forwardSingularExponentLog_eq_bot_of_tendsto {A : X → Matrix (Fin d) (Fin d) ℝ}
    {T : X → X} {k : ℕ} {x : X}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (sprod A T k n x)) atTop atBot) :
    forwardSingularExponentLog A T k x = ⊥ := by
  have hE : Tendsto
      (fun n : ℕ => (((n : ℝ)⁻¹ * Real.log (sprod A T k n x) : ℝ) : EReal)) atTop (𝓝 ⊥) :=
    EReal.tendsto_coe_nhds_bot_iff.2 h
  exact hE.limsup_eq

end Oseledets
