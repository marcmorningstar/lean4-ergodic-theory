/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityIntertwine

/-!
# Vector-kernel and quadratic-form helpers for the Petz-equality sufficiency direction

This module collects the general linear-algebra readoff lemmas used by the **sufficiency
(`⟹`) direction** of the Petz equality theorem (issue #28) along the *strict-convexity* route
(the equality case of the operator-Jensen / Effros machinery), complementary to the resolvent
route.

The terminal sufficiency theorems these helpers feed are `channel_equality_imp_intertwinesIt`
(`PetzEqualityGeneral`) and `partialTrace_equality_imp_intertwinesIt` (`PetzEqualitySufficiency`):
if the Umegaki relative entropy is preserved by a channel `Λ` (`D(ρ‖σ) = D(Λρ‖Λσ)`) then `Λ`
**intertwines the modular `it`-flows** of the input and output pairs.

## The strict-convexity equality mechanism

The relative entropy is realised (`relEntropy_eq_relForm`) as the positive functional
`relForm M = ⟪vec 1, M · vec 1⟫` applied to the operator perspective `opPersp (-log)` of the
relative modular operator.  The data-processing inequality is a **Loewner** inequality `A ≤ B`
between two such perspective operators, and the entropy hypothesis says the two scalar images
agree.  Because the Loewner *gap* `B − A` is positive-semidefinite and its `relForm`-expectation
has vanishing real part, the vector-kernel lemmas below place the cyclic vector `vec 1` in the
kernel of the gap.  This kernel condition — fed the strict operator convexity of `-log` — pins the
two perspective arguments together on the recovery direction, yielding the `it`-intertwining.

## Main results

* `posSemidef_vec_expectation_zero`: the **vector-kernel lemma** — a positive-semidefinite matrix
  with a vanishing quadratic expectation on `ξ` annihilates `ξ`.  (`⟨ξ, Gξ⟩ = 0, G ⪰ 0 ⟹ Gξ = 0`.)
* `qform_conj`: the quadratic form of an isometric compression `Wᴴ M W` at `ξ` equals that of `M`
  at `W ξ`.
* `posSemidef_vec_expectation_re_zero`: a positive-semidefinite matrix whose quadratic expectation
  on `ξ` has vanishing real part annihilates `ξ`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The vector-kernel lemma -/

/-- **Vector-kernel lemma.** A positive-semidefinite matrix `G` whose quadratic expectation on a
vector `ξ` vanishes (`⟪ξ, Gξ⟫ = 0`) annihilates that vector (`Gξ = 0`).  This is the concrete
"zero expectation on a positive operator forces the vector into the kernel" fact driving the
equality case: it is the Cholesky/`√`-argument `⟪ξ, Gξ⟫ = ‖√G · ξ‖²`, packaged in Mathlib as
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`. -/
lemma posSemidef_vec_expectation_zero {ι : Type*} [Fintype ι]
    {G : Matrix ι ι ℂ} (hG : G.PosSemidef) {ξ : ι → ℂ}
    (h : star ξ ⬝ᵥ G *ᵥ ξ = 0) : G *ᵥ ξ = 0 :=
  (hG.dotProduct_mulVec_zero_iff ξ).mp h

/-! ## Isometric-compression quadratic-form helpers

Two general readoff lemmas for a rectangular isometric compression `Wᴴ M W`: the quadratic form
transports along `W` (`qform_conj`), and a positive-semidefinite matrix whose expectation on `ξ`
has vanishing real part annihilates `ξ` (`posSemidef_vec_expectation_re_zero`). They feed the
reconciliation/rigidity assembly in `PetzEqualitySufficiency` and `PetzEqualityGeneral`. -/

/-- **Isometric-compression quadratic form.** For any (rectangular) `W`, matrix `M`, and vector `ξ`,
the quadratic form of the compression `Wᴴ M W` at `ξ` equals the quadratic form of `M` at `W ξ`:
`⟪ξ, (Wᴴ M W) ξ⟫ = ⟪W ξ, M (W ξ)⟫`. -/
lemma qform_conj {p q : Type*} [Fintype p] [Fintype q]
    (W : Matrix p q ℂ) (M : Matrix p p ℂ) (ξ : q → ℂ) :
    star ξ ⬝ᵥ (Wᴴ * M * W) *ᵥ ξ = star (W *ᵥ ξ) ⬝ᵥ M *ᵥ (W *ᵥ ξ) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

/-- **Vector-kernel via the real part.** A positive-semidefinite `G` whose quadratic expectation on
`ξ` has vanishing *real part* annihilates `ξ` (the imaginary part vanishes automatically, since the
expectation of a positive-semidefinite matrix is a nonnegative real). -/
lemma posSemidef_vec_expectation_re_zero {ι : Type*} [Fintype ι]
    {G : Matrix ι ι ℂ} (hG : G.PosSemidef) {ξ : ι → ℂ}
    (hre : (star ξ ⬝ᵥ G *ᵥ ξ).re = 0) : G *ᵥ ξ = 0 := by
  have hnn : (0 : ℂ) ≤ star ξ ⬝ᵥ G *ᵥ ξ := hG.dotProduct_mulVec_nonneg ξ
  obtain ⟨_, him⟩ := Complex.le_def.mp hnn
  have hz : star ξ ⬝ᵥ G *ᵥ ξ = 0 := by
    apply Complex.ext
    · simp only [Complex.zero_re]; exact hre
    · simpa using him.symm
  exact posSemidef_vec_expectation_zero hG hz

end ErgodicTheory.OperatorEntropy.Lieb

end
