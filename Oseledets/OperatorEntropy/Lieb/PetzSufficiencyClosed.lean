/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Mathlib
import Oseledets.OperatorEntropy.Lieb.ChoiLoewner
import Oseledets.OperatorEntropy.Lieb.PetzEqualityM3sc
import Oseledets.OperatorEntropy.Lieb.RigidityTail
import Oseledets.OperatorEntropy.Lieb.PetzVecBridge

/-!
# Petz equality — the assembly spine (issue #28)

This module wires together the green building blocks of the sufficiency (`⟹`) direction of the
Petz-equality theorem into the **abstract rigidity spine**: for a rectangular isometry `W`
(`Wᴴ W = 1`) and a positive-definite `Δ`, *equality of the two `-log` modular quadratic forms at a
cyclic vector `ξ`* forces `W` to intertwine the whole resolvent family of `Δ` on `ξ`.

Chain (all green pieces):

* **STEP 2** — `rect_isometry_neg_log_loewner` (`ChoiLoewner`): the DPI Loewner pair
  `A := cfc(-log)(Wᴴ Δ W) ≤ B := Wᴴ cfc(-log)(Δ) W`.
* **STEP 4** — `posSemidef_vec_expectation_zero` (`PetzEqualityM3sc`): the positive-semidefinite gap
  `B − A` whose `ξ`-expectation vanishes annihilates `ξ`.
* **STEP 5** — `isometry_resolvent_intertwine_of_neg_log_eq` (`RigidityTail`): the saturation
  `B ξ = A ξ` upgrades to `∀ t > 0, (Δ + t)⁻¹ (W ξ) = W ((Wᴴ Δ W + t)⁻¹ ξ)`.

## Main results (sorry-free)

* `neg_log_saturation_of_form_re_eq`: STEP 2 + STEP 4 — equality of the real parts of the two
  `-log` quadratic forms at `ξ` gives the operator saturation
  `Wᴴ cfc(-log)(Δ) W ξ = cfc(-log)(Wᴴ Δ W) ξ`.
* `resolvent_intertwine_of_form_re_eq`: STEP 2–5 composed — the same form-equality yields resolvent
  intertwining of `Δ` on `ξ` for all `t > 0`.

## The exact remaining goal to close `equality_imp_intertwinesIt`

The spine above is *abstract* (it consumes any isometry `W`, `Δ`, `ξ`).  Closing the concrete
`equality_imp_intertwinesIt (ρ σ Λ … hEq)` from it still requires three genuinely-new bridges,
each a substantial piece of formalisation:

1. **The vectorisation bridge (STEP 1 → matrix form).** Turn the *operator-level* ρ-twisted Petz
   isometry `petzW ω X = (X ω_A^{-1/2} ⊗ 1) ω^{1/2}` (with its three identities `petzW_isometry`,
   `petzW_cyclic`, `petzW_modular_compression`, green in `PetzReconciliation`) into a rectangular
   *matrix* `Wᵥ` on the vectorised HS spaces such that
   `Wᵥᴴ Wᵥ = 1`, `Wᵥᴴ (relModularArg ω τ) Wᵥ = relModularArg ω_A τ_A`, and
   `Wᵥ *ᵥ vec(ω_A^{1/2}) = vec(ω^{1/2})`.  These feed `W := Wᵥ`, `Δ := relModularArg ω τ`,
   `ξ := vec((Λρ)^{1/2})` into `resolvent_intertwine_of_form_re_eq`.  (The vec/Kronecker
   correspondence `vec(A X B) = (A ⊗ₖ Bᵀ) *ᵥ vec X` and the HS-adjoint identification
   `matrix(petzWadj) = Wᵥᴴ` have no Mathlib helper and must be built.)
2. **STEP 0 (Stinespring dilation of the Kraus channel).** Realise `Λ.toDM ρ` as
   `partialTraceRight (ω)` with `ω = U (ρ ⊗ α) Uᴴ`, so that
   `relEntropy ρ σ = relEntropy ω τ` and `relEntropy (Λρ) (Λσ) = relEntropy ω_A τ_A`
   (the composition inside `monotonicity_relEntropy_under_CPTP`) — which turns the two abstract
   quadratic-form real parts into the two entropies, so `hEq` supplies the `form_re_eq` hypothesis.
3. **STEP 6 (transport).** Push the resolvent/`cpow` intertwining of `Wᵥ` through
   `channelIsometry_adj` and `star_upow`/`upow_add` to the target `IntertwinesIt`:
   `∀ t, Λ.adj ((Λρ)^{it} (Λσ)^{-it}) = ρ^{it} σ^{-it}`.

The spine here is the load-bearing middle (STEP 2–5); it compiles sorry-free and is the exact
interface those three bridges plug into.
-/

open Matrix Real
open scoped MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace Oseledets.OperatorEntropy.Lieb

open Oseledets.OperatorEntropy

variable {M N : ℕ}

/-! ## STEP 2 + STEP 4: the `-log` saturation from equal quadratic forms -/

/-- **STEP 2 + STEP 4 (abstract).**  Let `W : Matrix (Fin M) (Fin N) ℂ` be a rectangular isometry
(`Wᴴ W = 1`) and `Δ` positive definite with spectrum in `(0, ∞)`.  If the two `-log` modular
quadratic forms agree in real part at the cyclic vector `ξ`,

`Re ⟪ξ, (Wᴴ cfc(-log)(Δ) W) ξ⟫ = Re ⟪ξ, cfc(-log)(Wᴴ Δ W) ξ⟫`,

then the isometric compression is *exact on `ξ`*:

`(Wᴴ cfc(-log)(Δ) W) ξ = cfc(-log)(Wᴴ Δ W) ξ`.

Proof: `rect_isometry_neg_log_loewner` gives the Loewner pair `A ≤ B` with
`A = cfc(-log)(Wᴴ Δ W)`, `B = Wᴴ cfc(-log)(Δ) W`; the gap `B − A` is positive semidefinite and its
`ξ`-expectation is real-nonnegative with vanishing real part (the hypothesis) and vanishing
imaginary part (nonnegativity), hence zero, so `posSemidef_vec_expectation_zero` kills `ξ`. -/
theorem neg_log_saturation_of_form_re_eq
    (W : Matrix (Fin M) (Fin N) ℂ) (Δ : Matrix (Fin M) (Fin M) ℂ) (ξ : Fin N → ℂ)
    (hW : Wᴴ * W = 1) (hΔsa : IsSelfAdjoint Δ) (hspec : spectrum ℝ Δ ⊆ Set.Ioi 0)
    (hform : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
        = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) (Wᴴ * Δ * W) *ᵥ ξ).re) :
    (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ
      = cfc (fun x => -Real.log x) (Wᴴ * Δ * W) *ᵥ ξ := by
  set A := cfc (fun x => -Real.log x) (Wᴴ * Δ * W) with hAdef
  set B := Wᴴ * cfc (fun x => -Real.log x) Δ * W with hBdef
  -- STEP 2: the Loewner pair `A ≤ B`.
  have hAB : A ≤ B := rect_isometry_neg_log_loewner W Δ hW hΔsa hspec
  have hps : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  -- the gap's `ξ`-expectation splits as `formB − formA`.
  have hsplit : star ξ ⬝ᵥ (B - A) *ᵥ ξ
      = star ξ ⬝ᵥ B *ᵥ ξ - star ξ ⬝ᵥ A *ᵥ ξ := by
    rw [sub_mulVec, dotProduct_sub]
  -- it is real-nonnegative, hence real, and equal real parts force it to vanish.
  have hnn : (0 : ℂ) ≤ star ξ ⬝ᵥ (B - A) *ᵥ ξ := hps.dotProduct_mulVec_nonneg ξ
  obtain ⟨_, him⟩ := Complex.le_def.mp hnn
  have hzero : star ξ ⬝ᵥ (B - A) *ᵥ ξ = 0 := by
    apply Complex.ext
    · rw [Complex.zero_re, hsplit, Complex.sub_re, sub_eq_zero]; exact hform
    · simpa using him.symm
  -- STEP 4: the gap annihilates `ξ`, i.e. `B ξ = A ξ`.
  have hker : (B - A) *ᵥ ξ = 0 := posSemidef_vec_expectation_zero hps hzero
  rw [sub_mulVec, sub_eq_zero] at hker
  exact hker

/-! ## STEP 2–5 composed: resolvent intertwining from equal quadratic forms -/

/-- **STEP 2–5 (abstract spine).**  Under the same hypotheses as `neg_log_saturation_of_form_re_eq`
(rectangular isometry `W`, positive-definite `Δ`, and equality of the two `-log` quadratic-form real
parts at `ξ`), the isometry `W` intertwines the entire resolvent family of `Δ` on `ξ`:

`∀ t > 0, (Δ + t)⁻¹ (W ξ) = W ((Wᴴ Δ W + t)⁻¹ ξ)`.

This is the middle of the Petz-sufficiency chain: it combines the DPI Loewner inequality
(`rect_isometry_neg_log_loewner`), the gap-vanishing lemma (`posSemidef_vec_expectation_zero`), and
the resolvent rigidity tail (`isometry_resolvent_intertwine_of_neg_log_eq`).  The resolvent readoff
(`exists_resolvent_combo`) then upgrades this to intertwining of every continuous function of `Δ`,
in particular the modular power `Δ^{it}`. -/
theorem resolvent_intertwine_of_form_re_eq
    (W : Matrix (Fin M) (Fin N) ℂ) (Δ : Matrix (Fin M) (Fin M) ℂ) (ξ : Fin N → ℂ)
    (hW : Wᴴ * W = 1) (hΔ : Δ.PosDef) (hspec : spectrum ℝ Δ ⊆ Set.Ioi 0)
    (hform : (star ξ ⬝ᵥ (Wᴴ * cfc (fun x => -Real.log x) Δ * W) *ᵥ ξ).re
        = (star ξ ⬝ᵥ cfc (fun x => -Real.log x) (Wᴴ * Δ * W) *ᵥ ξ).re) :
    ∀ t : ℝ, 0 < t →
      (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t)⁻¹ *ᵥ (W *ᵥ ξ)
        = W *ᵥ ((Wᴴ * Δ * W + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)⁻¹ *ᵥ ξ) :=
  isometry_resolvent_intertwine_of_neg_log_eq W Δ ξ hW hΔ
    (neg_log_saturation_of_form_re_eq W Δ ξ hW hΔ.1 hspec hform)

/-! ## STEP 1 wired: the vectorisation bridge supplies the spine's algebraic inputs

The **vectorisation bridge** (`PetzVecBridge`) turns the operator-level ρ-twisted Petz isometry
into the rectangular matrix `petzWvec ω` and delivers the three Carlen–Vershynina identities as
matrix facts.  Bundled below are exactly the *purely-algebraic* hypotheses that the abstract spine
`resolvent_intertwine_of_form_re_eq` consumes — an isometry `Wᴴ W = 1`, a positive-definite modular
argument `Δ = modArgVec τ ω` with positive spectrum, and the modular-compression identity
`Wᴴ Δ W = Δ_A` — all discharged *sorry-free* from the bridge.

**What still separates this from the concrete `equality_imp_intertwinesIt`** (the exact remaining
goals):

* **the `Fin`-reindex adapter.**  The spine is stated over `Matrix (Fin M) (Fin N)`; the bridge
  objects are indexed by the products `(nA×nB)×(nA×nB)` and `nA×nA`.  Reindex via
  `Fintype.equivFin` (square parts reuse `eqvFin`'s `eqvFin_posDef`/`eqvFin_spectrum`/`eqvFin_cfc`;
  the rectangular `petzWvec` uses `submatrix_mul_equiv` / `conjTranspose_submatrix` /
  `submatrix_mulVec_equiv`).
* **STEP 0 — the form hypothesis `hform`.**  The equality of the two `-log` quadratic-form real
  parts at `ξ = vec ((partialTraceRight ω)^{1/2})` must be produced from the entropy hypothesis
  `relEntropy ρ σ = relEntropy (Λρ) (Λσ)` via the Stinespring realisation `ω = U(ρ⊗α)Uᴴ`,
  `partialTraceRight ω = Λρ`, and the modular form `relEntropy_eq_relForm`.  This requires the
  convention bridge `modArgVec (partialTraceRight ω) (partialTraceRight τ)`
  (`= (Λσ) ⊗ₖ ((Λρ)⁻¹)ᵀ`, realising `X ↦ (Λσ) X (Λρ)⁻¹`) ↔ `relModularArg (Λρ) (Λσ)`
  (`= (Λρ)⁻¹ ⊗ₖ (Λσ)ᵀ`, realising `X ↦ (Λρ)⁻¹ X (Λσ)`): the two are equal after the
  tensor-swap-and-transpose, and their `-log` quadratic forms at `vec ((Λρ)^{1/2})` agree.
* **STEP 6 — transport to `IntertwinesIt`.**  Push the resolvent/`cpow` intertwining of `petzWvec`
  through `channelIsometry_adj` + `star_upow`/`upow_add` to
  `Λ.adj ((Λρ)^{it} (Λσ)^{-it}) = ρ^{it} σ^{-it}`.
-/

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
