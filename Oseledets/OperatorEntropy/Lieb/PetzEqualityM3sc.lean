/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.PetzEqualityIntertwine

/-!
# Petz equality — the strict-convexity route (module M3, head)

This module assembles the equality-extraction backbone of the **sufficiency (`⟹`) direction** of
the Petz equality theorem (issue #28) along the *strict-convexity* route (the equality case of the
operator-Jensen / Effros machinery), complementary to the resolvent route.

The terminal sufficiency theorems this module feeds are `channel_equality_imp_intertwinesIt`
(`PetzEqualityGeneral`) and `partialTrace_equality_imp_intertwinesIt` (`PetzEqualitySufficiency`):
if the Umegaki relative entropy is preserved by a channel `Λ` (`D(ρ‖σ) = D(Λρ‖Λσ)`) then `Λ`
**intertwines the modular `it`-flows** of the input and output pairs.  This module isolates the
equality-extraction keystone used along the way — a positive-semidefinite Loewner gap whose two
`relForm` real parts coincide annihilates the cyclic vector.

## The strict-convexity equality mechanism

The relative entropy is realised (`relEntropy_eq_relForm`) as the positive functional
`relForm M = ⟪vec 1, M · vec 1⟫` applied to the operator perspective `opPersp (-log)` of the
relative modular operator.  The data-processing inequality is a **Loewner** inequality
`A ≤ B` between two such perspective operators, and the entropy hypothesis says the two scalar
images agree, `(relForm A).re = (relForm B).re`.  Because the Loewner *gap* `B − A` is
positive-semidefinite and its `relForm`-expectation vanishes, the gap **annihilates the cyclic
vector** `vec 1`.  This kernel condition — fed the strict operator convexity of `-log` — pins the
two perspective arguments together on the recovery direction, and reading this off with the modular
powers `upow` / `star_upow` yields the `it`-intertwining.

## Main results

* `posSemidef_vec_expectation_zero`: the **vector-kernel lemma** — a positive-semidefinite matrix
  with a vanishing quadratic expectation on `ξ` annihilates `ξ`.  (`⟨ξ, Gξ⟩ = 0, G ⪰ 0 ⟹ Gξ = 0`.)
* `relForm_re_eq_of_relEntropy_eq`: the entropy hypothesis, transported to the equality of the real
  parts of the two `relForm ∘ opPersp (-log)` values (the input for the gap-vanishing step).
* `gap_mulVec_vecOne_zero_of_relForm_re_eq`: the **equality-extraction keystone** — a Loewner
  inequality whose two `relForm` real parts coincide has a gap that annihilates `vec 1`.
* `qform_conj`: the quadratic form of an isometric compression `Wᴴ M W` at `ξ` equals that of `M`
  at `W ξ`.
* `posSemidef_vec_expectation_re_zero`: a positive-semidefinite matrix whose quadratic expectation
  on `ξ` has vanishing real part annihilates `ξ`.
-/

open Matrix Real
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

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

/-! ## Transporting the entropy equality to the perspective functional -/

/-- The entropy hypothesis `D(ρ‖σ) = D(Λρ‖Λσ)`, transported through the modular/perspective form
`relEntropy_eq_relForm`, is exactly the equality of the real parts of the two `relForm`-images of
the operator perspective of `-log` (input at `(1 ⊗ σᵀ, ρ ⊗ 1)`, output at `(1 ⊗ (Λσ)ᵀ, Λρ ⊗ 1)`).
This is the scalar equality that feeds the Loewner gap-vanishing step. -/
lemma relForm_re_eq_of_relEntropy_eq (ρ σ : DensityMatrix n) (Λ : KrausChannel n)
    (hρ : ρ.val.PosDef) (hσ : σ.val.PosDef)
    (hΛρ : (Λ.toDM ρ).val.PosDef) (hΛσ : (Λ.toDM σ).val.PosDef)
    (hEq : relEntropy ρ σ = relEntropy (Λ.toDM ρ) (Λ.toDM σ)) :
    (relForm (opPersp (fun x => -Real.log x)
        ((1 : Matrix n n ℂ) ⊗ₖ σ.valᵀ) (ρ.val ⊗ₖ 1))).re
      = (relForm (opPersp (fun x => -Real.log x)
        ((1 : Matrix n n ℂ) ⊗ₖ (Λ.toDM σ).valᵀ) ((Λ.toDM ρ).val ⊗ₖ 1))).re := by
  rw [← relEntropy_eq_relForm ρ σ hρ hσ, ← relEntropy_eq_relForm (Λ.toDM ρ) (Λ.toDM σ) hΛρ hΛσ]
  exact hEq

/-! ## The Loewner gap-vanishing keystone -/

/-- **Equality-extraction keystone.** If `A ≤ B` in the Loewner order and the two scalar images
under `relForm` have equal real parts, then the positive-semidefinite gap `B − A` annihilates the
cyclic vector `vec 1`.

The gap `B − A` is positive-semidefinite, so `relForm (B − A) = ⟪vec 1, (B − A) · vec 1⟫ ≥ 0` in
`ComplexOrder`, hence is a *real* nonnegative number; equal real parts force it to vanish, and the
vector-kernel lemma `posSemidef_vec_expectation_zero` then places `vec 1` in the kernel of the
gap. -/
lemma gap_mulVec_vecOne_zero_of_relForm_re_eq {A B : Matrix (n × n) (n × n) ℂ}
    (hle : A ≤ B) (heq : (relForm A).re = (relForm B).re) :
    (B - A) *ᵥ vecOne n = 0 := by
  have hps : (B - A).PosSemidef := Matrix.le_iff.mp hle
  -- the gap's expectation on `vec 1` is `relForm B − relForm A`
  have hsub : star (vecOne n) ⬝ᵥ (B - A) *ᵥ vecOne n = relForm B - relForm A := by
    rw [← relForm]; exact relForm_sub B A
  -- it is `≥ 0` in `ComplexOrder`, hence real; equal real parts force it to be `0`
  have hnn : (0 : ℂ) ≤ star (vecOne n) ⬝ᵥ (B - A) *ᵥ vecOne n :=
    hps.dotProduct_mulVec_nonneg (vecOne n)
  rw [hsub] at hnn
  obtain ⟨_, him⟩ := Complex.le_def.mp hnn
  have hzeroC : relForm B - relForm A = 0 := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.zero_re, sub_eq_zero]; exact heq.symm
    · simpa using him.symm
  have hzero : star (vecOne n) ⬝ᵥ (B - A) *ᵥ vecOne n = 0 := by rw [hsub, hzeroC]
  exact posSemidef_vec_expectation_zero hps hzero

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

end Oseledets.OperatorEntropy.Lieb

end
