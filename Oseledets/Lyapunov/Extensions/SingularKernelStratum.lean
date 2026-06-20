/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.Lyapunov.Extensions.SingularExponentGenLog

/-!
# The measurable `−∞` kernel / volume-collapse stratum

For a **possibly-singular** matrix cocycle generator `A : X → Matrix (Fin d) (Fin d) ℝ` — no
`det A ≠ 0`, no inverse integrability, only forward integrability — this module isolates the
**kernel / volume-collapse stratum at level `k`**: the set of base points `x` where the
genuine-`log` top-`k`-volume exponent `γ_k^log` (`Oseledets.forwardSingularExponentLog`) attains
the bottom value `⊥` of `EReal`, i.e. where the `k`-volume collapses super-exponentially.

In the **non-invertible** multiplicative ergodic theorem (the Raghunathan / Quas form: a
*filtration* rather than a splitting; see A. Quas, *Multiplicative Ergodic Theorems and
Applications*, Theorem 2 and §3.1, the non-invertible form via SVD + exterior algebra + Kingman,
method due to M. S. Raghunathan, *A proof of Oseledec's multiplicative ergodic theorem*, Israel
J. Math. **32** (1979), 356–362) the singular values of `A⁽ⁿ⁾` may decay to `0`. The genuine
`log` of the top-`k` singular-value product then runs off to `−∞`, an exponent the `log⁺`
packaging `Oseledets.forwardSingularExponent` is structurally unable to record (it is pinned at
`0` there). This `⊥` regime is the *kernel stratum*: directions whose `k`-volume is annihilated
in the limit. Stratifying the base space by which volume-levels collapse is the first measurable
step toward a singular Oseledets stratification.

This module supplies that stratum as a **measurable set** (item 1–2), together with its defining
membership characterization and the dual finite-exponent complement (item 3–4). It does *not*
attempt the full singular filtration; it provides the measurable set-theoretic scaffolding on
which such a stratification can be built.

## Main definitions

* `Oseledets.singularKernelSet` — the level-`k` kernel / volume-collapse stratum
  `{x | γ_k^log(x) = ⊥}`.

## Main results

* `Oseledets.mem_singularKernelSet` — membership characterization
  `x ∈ singularKernelSet A T k ↔ forwardSingularExponentLog A T k x = ⊥` (definitional).
* `Oseledets.measurableSet_singularKernelSet` — the stratum is measurable: it is the preimage of
  the measurable singleton `{⊥} ⊆ EReal` under the measurable `γ_k^log`.
* `Oseledets.measurableSet_finiteSingularExponent` — the complementary *finite-exponent* set
  `{x | ⊥ < γ_k^log(x)}` is measurable (the preimage of the measurable `Ioi ⊥`).

## Implementation notes

* `EReal` is a `BorelSpace` with the order topology, hence `T1Space`, hence
  `MeasurableSingletonClass` (via `OpensMeasurableSpace.toMeasurableSingletonClass`); thus the
  singleton `{⊥}` is measurable and the kernel stratum is a measurable preimage under
  `Oseledets.measurable_forwardSingularExponentLog` (which carries `[NeZero d]`).
* No monotonicity-in-`k` lemma is stated: the kernel sets need not be nested, because
  `γ_k^log` is the **cumulative** exponent (a sum of individual exponents that may have either
  sign), so `sprod_{k+1} ≤ sprod_k` does not hold deterministically and no clean
  `singularKernelSet`-inclusion in `k` is available here.

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

/-- **The level-`k` kernel / volume-collapse stratum** of a possibly-singular cocycle generator:
the set of base points where the genuine-`log` top-`k`-volume exponent collapses to the bottom
value `⊥` of `EReal`,

`singularKernelSet A T k = {x | γ_k^log(x) = ⊥}`,

with `γ_k^log = Oseledets.forwardSingularExponentLog A T k`. These are the points whose top-`k`
singular-value product decays super-exponentially (`sprod_k → 0`), the `−∞` exponent invisible to
the `log⁺` packaging. This is the kernel stratum of the Raghunathan / Quas non-invertible
multiplicative ergodic theorem (filtration form). -/
def singularKernelSet (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (k : ℕ) : Set X :=
  {x | forwardSingularExponentLog A T k x = ⊥}

omit [MeasurableSpace X] in
/-- **Membership in the kernel stratum** is, definitionally, the collapse of the genuine-`log`
top-`k`-volume exponent to `⊥`. -/
theorem mem_singularKernelSet {A : X → Matrix (Fin d) (Fin d) ℝ} {T : X → X} {k : ℕ} {x : X} :
    x ∈ singularKernelSet A T k ↔ forwardSingularExponentLog A T k x = ⊥ :=
  Iff.rfl

/-- **The kernel / volume-collapse stratum is measurable.** It is the preimage of the singleton
`{⊥} ⊆ EReal` under `γ_k^log = Oseledets.forwardSingularExponentLog A T k`. The singleton `{⊥}`
is measurable because `EReal` is a `BorelSpace` with the order topology — hence `T1Space`, hence
`MeasurableSingletonClass` (`measurableSet_singleton`) — and `γ_k^log` is measurable
(`Oseledets.measurable_forwardSingularExponentLog`, which carries `[NeZero d]`); a measurable
preimage of a measurable set is measurable (`MeasurableSet.preimage`). -/
theorem measurableSet_singularKernelSet [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hAmeas : Measurable A) (hTmeas : Measurable T) (k : ℕ) :
    MeasurableSet (singularKernelSet A T k) :=
  (measurableSet_singleton (⊥ : EReal)).preimage
    (measurable_forwardSingularExponentLog hAmeas hTmeas k)

/-- **The complementary finite-exponent set is measurable.** The set
`{x | ⊥ < γ_k^log(x)}` — base points where the genuine-`log` top-`k`-volume exponent does *not*
collapse to `−∞` — is the preimage of the measurable order-interval `Ioi ⊥ ⊆ EReal`
(`measurableSet_Ioi`) under the measurable `γ_k^log`
(`Oseledets.measurable_forwardSingularExponentLog`), hence measurable
(`MeasurableSet.preimage`). It is the set-theoretic complement of
`Oseledets.singularKernelSet`. -/
theorem measurableSet_finiteSingularExponent [NeZero d] {A : X → Matrix (Fin d) (Fin d) ℝ}
    (hAmeas : Measurable A) (hTmeas : Measurable T) (k : ℕ) :
    MeasurableSet {x | ⊥ < forwardSingularExponentLog A T k x} :=
  measurableSet_Ioi.preimage (measurable_forwardSingularExponentLog hAmeas hTmeas k)

end Oseledets
