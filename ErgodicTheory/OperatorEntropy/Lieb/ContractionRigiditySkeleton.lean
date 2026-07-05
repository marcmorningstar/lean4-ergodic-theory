/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.OperatorEntropy.Lieb.RigidityTail
import ErgodicTheory.OperatorEntropy.Lieb.PetzEqualityM3sc

/-!
# Contraction rigidity helpers (issue #28, GENERAL case — route b″)

Two small, reusable facts about a *contraction* vectorised Petz map `W` (`Wᴴ W ≤ 1`, no longer an
isometry `Wᴴ W = 1`) that feed the general Petz-sufficiency rigidity argument.  The full contraction
rigidity spine — the quadratic-gap identity, the resolvent-Jensen nonnegativity, the
antitone-inverse transport and the per-`t` intertwining — now lives *inline* in
`PetzEqualityGeneral.petz_equality_recovery_general` (its own scalar, injectivity-free spine); this
module only supplies the two ingredients that argument still calls out to.

## The geometry (directions, carefully)

* `W : Matrix (Fin M) (Fin N) ℂ` maps the **output** space `Fin N` into the **input** space `Fin M`;
  `Wᴴ W : Fin N → Fin N` is a contraction `≤ 1`.
* `Δ : Matrix (Fin M) (Fin M) ℂ` is the **input** relative modular operator (`PosDef`).
* `Δout : Matrix (Fin N) (Fin N) ℂ` is the **output** relative modular operator (`PosDef`).
* `ξ : Fin N → ℂ` is the **output cyclic vector**; `W *ᵥ ξ` is the input cyclic vector.

## What is exported here

* `contraction_defect_mulVec_eq_zero` — **defect annihilation.**  For a contraction `W`, the
  norm-saturation `⟪Wξ, Wξ⟫ = ⟪ξ, ξ⟫` forces the contraction defect `E := 1 − WᴴW ⪰ 0` to annihilate
  `ξ`: `(1 − WᴴW) *ᵥ ξ = 0`.  This is what lets the isometry algebra go through at `ξ` even though
  `Wᴴ W = 1` fails globally.
* `compression_shift_le` — **compression shift inequality** (piece `B`).  Since `WᴴΔW ≤ Δout` and
  `1 − WᴴW ⪰ 0`, one has `Wᴴ (Δ + t) W ≤ Δout + t`, because
  `(Δout + t) − Wᴴ(Δ+t)W = (Δout − WᴴΔW) + t·(1 − WᴴW) ⪰ 0`.
-/

open Matrix MeasureTheory Set
open scoped MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace ErgodicTheory.OperatorEntropy.Lieb

variable {M N : ℕ}

/-! ## The saturation defect vanishes at `ξ` -/

/-- **Defect annihilation.**  For a contraction `W` (`Wᴴ W ≤ 1`), the norm-saturation
`⟪Wξ, Wξ⟫ = ⟪ξ, ξ⟫` forces the contraction defect `E := 1 − WᴴW ⪰ 0` to annihilate `ξ`:
`(1 − WᴴW) *ᵥ ξ = 0`. -/
lemma contraction_defect_mulVec_eq_zero (W : Matrix (Fin M) (Fin N) ℂ) (ξ : Fin N → ℂ)
    (hWc : Wᴴ * W ≤ 1)
    (hsat : star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) = star ξ ⬝ᵥ ξ) :
    (1 - Wᴴ * W) *ᵥ ξ = 0 := by
  have hE : (1 - Wᴴ * W).PosSemidef := Matrix.le_iff.mp hWc
  have hqf : star ξ ⬝ᵥ (Wᴴ * W) *ᵥ ξ = star (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) := by
    have h := qform_conj W 1 ξ
    rw [Matrix.mul_one, Matrix.one_mulVec] at h
    exact h
  have hzero : star ξ ⬝ᵥ (1 - Wᴴ * W) *ᵥ ξ = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hqf, hsat, sub_self]
  exact posSemidef_vec_expectation_zero hE hzero

/-! ## The operator-antitone gap `B(t)` — the compression shift inequality -/

/-- **Compression shift inequality** (piece `B`).  Since `WᴴΔW ≤ Δout` and `1 − WᴴW ⪰ 0`,
`Wᴴ (Δ + t) W ≤ Δout + t`, because
`(Δout + t) − Wᴴ(Δ+t)W = (Δout − WᴴΔW) + t·(1 − WᴴW) ⪰ 0`. -/
lemma compression_shift_le (W : Matrix (Fin M) (Fin N) ℂ)
    (Δ : Matrix (Fin M) (Fin M) ℂ) (Δout : Matrix (Fin N) (Fin N) ℂ)
    (hWc : Wᴴ * W ≤ 1) (hcompLe : Wᴴ * Δ * W ≤ Δout) {t : ℝ} (ht : 0 < t) :
    Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W
      ≤ Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t := by
  have hE : (1 - Wᴴ * W).PosSemidef := Matrix.le_iff.mp hWc
  have hcomp : (Δout - Wᴴ * Δ * W).PosSemidef := Matrix.le_iff.mp hcompLe
  have hreg : Wᴴ * algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t * W = t • (Wᴴ * W) := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [Matrix.le_iff]
  have hexpand : (Δout + algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) t)
      - Wᴴ * (Δ + algebraMap ℝ (Matrix (Fin M) (Fin M) ℂ) t) * W
      = (Δout - Wᴴ * Δ * W) + t • (1 - Wᴴ * W) := by
    rw [Matrix.mul_add, Matrix.add_mul, hreg, Algebra.algebraMap_eq_smul_one, smul_sub]
    abel
  rw [hexpand]
  exact hcomp.add (hE.smul ht.le)

end ErgodicTheory.OperatorEntropy.Lieb

end

