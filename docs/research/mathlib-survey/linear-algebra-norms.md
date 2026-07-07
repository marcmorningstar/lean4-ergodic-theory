# Mathlib survey — Area: linear-algebra-norms

Survey of existing Mathlib 4 API supporting the Oseledets MET formalization, in
the areas of exterior powers, singular values, polar decomposition / matrix
square root, spectral theorem, operator norms, and the general linear group.

Paths are **relative to the Mathlib package root**
(`/workspaces/lean4-oseledets/.lake/packages/mathlib/`). Read against source on
disk (not a typechecked state); signatures transcribed from `.lean` source.

Mathlib commit/toolchain: as pinned by the project (`v4.30.0-rc2`).

---

## Quick answers to the five mandated questions

1. **Exterior powers `⋀^k` + induced map on a linear map** — **FOUND.**
   `⋀[R]^n M` notation, `exteriorPower.map n f` functor, full functoriality
   (`map_id`, `map_comp`, injectivity/surjectivity), basis, finrank
   `= choose (finrank M) n`. *BUT:* **no norm / inner product / topology** on
   exterior powers anywhere in Mathlib (`Analysis/`, `Topology/` have zero
   references). The inner-product / volume structure must be built.

2. **Singular values of an operator** — **FOUND.**
   `LinearMap.singularValues` in `Mathlib/Analysis/InnerProductSpace/SingularValues.lean`
   (added 2026), defined as `√(eigenvalues of T†∘T)` in descending order, with a
   solid API (antitone, support, characterization). **No matrix-level
   `Matrix.singularValues`** wrapper, and **no lemma `‖T‖ = T.singularValues 0`**
   tying the operator norm to the top singular value — that bridge must be built
   (the ingredients exist via the Rayleigh quotient).

3. **Polar decomposition / `(AᵀA)^{1/2}` / PSD square root + its eigenvalues** —
   **PARTIAL.** The PSD square root exists as the **C\*-algebra CFC square root**
   `CFC.sqrt` (`…/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`),
   applicable to `Matrix n n 𝕜` via its `CStarAlgebra` instance, with
   `sqrt_nonneg`, `sq_sqrt`, `sqrt_mul_self`, `sqrt_unique`, `det_sqrt`. Spectral
   theorem and eigenvalues are fully available (`Matrix.IsHermitian.eigenvalues`,
   `LinearMap.IsSymmetric.eigenvalues`, `PosSemidef.eigenvalues_nonneg`). **No
   named `polarDecomposition` / SVD theorem** (`A = U Σ Vᴴ`) — must be built (or
   bypassed by working with `√(AᴴA)` directly).

4. **Operator norm of matrices / CLMs + submultiplicativity** — **FOUND.**
   `ContinuousLinearMap.opNorm` with `opNorm_comp_le : ‖h.comp f‖ ≤ ‖h‖*‖f‖`,
   `NormedRing (E →L[𝕜] E)`. For matrices, the **L2 operator norm**
   (`Matrix.Norms.L2Operator` scoped instances) gives `l2_opNorm_mul`
   submultiplicativity and the C\*-identity `‖AᴴA‖ = ‖A‖²`. Also Frobenius and
   l∞-operator `NormedRing` instances.

5. **GL_d as a group + norms on `Matrix n n ℝ`** — **FOUND.**
   `Matrix.GeneralLinearGroup n R` (notation `GL n R`), `det : GL n R →* Rˣ`,
   group structure, `toLin`. Several norms on `Matrix n n ℝ` (entrywise sup,
   Frobenius, l∞-op, L2-op). **No off-the-shelf topological-group / Lie-group
   instance specialized & exported for `GL n ℝ`** with a chosen norm; the norm
   instances on `Matrix` are scoped/non-default (deliberately, since several
   choices exist), so the project must `open` / fix one.

---

## Found API

### 1. Exterior powers (`⋀[R]^n M`) and the induced map

File: `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean`
(notation `⋀[R]^n M` is `exteriorPower R n M`; `[⋀^Fin n]→ₗ[R]` is `AlternatingMap`)

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `exteriorPower.ιMulti` | `(R n) : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M)` — canonical alternating map |
| def | `exteriorPower.map` | `(n) (f : M →ₗ[R] N) : ⋀[R]^n M →ₗ[R] ⋀[R]^n N` — **induced map on n-th exterior power** |
| thm | `exteriorPower.map_id` | `map n (LinearMap.id) = LinearMap.id` |
| thm | `exteriorPower.map_comp` | `map n (g ∘ₗ f) = map n g ∘ₗ map n f` (functoriality) |
| thm | `exteriorPower.map_apply_ιMulti` | `map n f (ιMulti R n m) = ιMulti R n (f ∘ m)` |
| lemma | `exteriorPower.map_injective` / `map_injective_field` / `map_surjective` | exactness of the functor |
| def | `exteriorPower.alternatingMapLinearEquiv` | `(M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] (⋀[R]^n M →ₗ[R] N)` — universal property |
| lemma | `exteriorPower.linearMap_ext` | extensionality on `⋀[R]^n M` |
| def | `exteriorPower.zeroEquiv` / `oneEquiv` | `⋀[R]^0 M ≃ₗ[R] R`, `⋀[R]^1 M ≃ₗ[R] M` |

File: `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `Module.Basis.exteriorPower` | `(b : Basis I R M) (n) : Basis (powersetCard I n) R (⋀[R]^n M)` |
| instance | `exteriorPower.instFree` / `instFinite` | free + finite when `M` is |
| lemma | `exteriorPower.finrank_eq` | `finrank R (⋀[R]^n M) = Nat.choose (finrank R M) n` |

Also: `Mathlib/Algebra/Category/ModuleCat/ExteriorPower.lean` (categorical functor),
`Mathlib/LinearAlgebra/ExteriorAlgebra/*` (the algebra), `ExteriorPower/Pairing.lean`.

**Usage in MET:** k-dimensional volume growth `‖⋀^k A‖` is governed by the
product of the top k singular values; `exteriorPower.map` is exactly `⋀^k A`,
`map_comp` gives the cocycle property `⋀^k(AB) = (⋀^k A)(⋀^k B)`. We must
*equip* `⋀[R]^k (ℝ^d)` (or of a Euclidean/inner-product space) with an inner
product/norm — none exists in Mathlib (see Gaps).

### 2. Singular values

File: `Mathlib/Analysis/InnerProductSpace/SingularValues.lean`
(namespace `LinearMap`; `𝕜` `RCLike`, `E F` finite-dim inner product spaces)

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `LinearMap.singularValues` | `(T : E →ₗ[𝕜] F) : ℕ →₀ ℝ` — `√(eigenvalues of T†∘T)`, descending, zero-indexed |
| thm | `LinearMap.singularValues_nonneg` | `0 ≤ T.singularValues i` |
| thm | `LinearMap.singularValues_fin` | `(hn : finrank 𝕜 E = n) (i : Fin n) : T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i)` |
| thm | `LinearMap.sq_singularValues_fin` | `T.singularValues i ^ 2 = (…).eigenvalues hn i` |
| thm | `LinearMap.singularValues_of_finrank_le` | `finrank 𝕜 E ≤ i → T.singularValues i = 0` |
| thm | `LinearMap.singularValues_antitone` | `Antitone T.singularValues` |
| thm | `LinearMap.support_singularValues` | `T.singularValues.support = Finset.range (finrank 𝕜 T.range)` |
| thm | `LinearMap.card_support_singularValues` | `= finrank 𝕜 T.range` |
| thm | `LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues` | `HasEigenvalue (T†∘ₗT) (T.singularValues n ^ 2)` |
| thm | `LinearMap.injective_iff_forall_lt_finrank_singularValues_pos` | injectivity ↔ all σ_i > 0 for i < finrank |
| thm | `LinearMap.singularValues_eq_zero_iff` | `T.singularValues = 0 ↔ T = 0` |

**Usage in MET:** the Lyapunov exponents are `lim (1/n) log σ_i(Aⁿ)`. This is the
single most directly relevant definition. Caveats: it is for `LinearMap` between
inner product spaces (not matrices), there is no `Matrix.singularValues`, and no
`‖T‖ = T.singularValues 0` lemma yet (build it).

### 3. Spectral theorem, eigenvalues, adjoint, Gram operator

Linear-map version — File: `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
(namespace `LinearMap.IsSymmetric`)

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `LinearMap.IsSymmetric.eigenvalues` | `(hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) : Fin n → ℝ` — sorted descending |
| def | `LinearMap.IsSymmetric.eigenvectorBasis` | `… : OrthonormalBasis (Fin n) 𝕜 E` |
| thm | `…eigenvectorBasis_apply_self_apply` | spectral theorem v2 (diagonalization) |
| thm | `…apply_eigenvectorBasis` | `T (eigenvectorBasis i) = (eigenvalues i) • eigenvectorBasis i` |
| thm | `…eigenvalues_antitone` | eigenvalues sorted descending |
| thm | `…hasEigenvalue_eigenvalues` | each `eigenvalues i` is an eigenvalue |
| thm | `…det_eq_prod_eigenvalues`, `…charpoly_eq` | det = ∏ eigenvalues |
| def | `LinearMap.IsSymmetric.diagonalization` | `E ≃ₗᵢ[𝕜] PiLp 2 (eigenspaces)` (spectral theorem v1) |

Adjoint / Gram operator — File: `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `ContinuousLinearMap.adjoint` | `(E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)` |
| def | `LinearMap.adjoint` | `(E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)` (finite-dim) |
| thm | `…adjoint_comp` | `(A ∘ B)† = B† ∘ A†` |
| thm | `LinearMap.isSymmetric_adjoint_comp_self` | `(T : E →ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric` — Gram operator T†T symmetric |
| thm | `LinearMap.isPositive_adjoint_comp_self` | `(adjoint S ∘ₗ S).IsPositive` (File: `InnerProductSpace/Positive.lean`) |
| thm | `IsPositive.nonneg_eigenvalues` | `0 ≤ (eigenvalues …) i` (`InnerProductSpace/Positive.lean:155`) |

Matrix version — File: `Mathlib/Analysis/Matrix/Spectrum.lean` (namespace `Matrix.IsHermitian`)

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `Matrix.IsHermitian.eigenvalues` | `(hA : A.IsHermitian) : n → ℝ` |
| def | `Matrix.IsHermitian.eigenvalues₀` | `: Fin (Fintype.card n) → ℝ`, antitone (`eigenvalues₀_antitone`) |
| def | `Matrix.IsHermitian.eigenvectorBasis` | `: OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)` |
| def | `Matrix.IsHermitian.eigenvectorUnitary` | `: Matrix.unitaryGroup n 𝕜` |
| thm | `Matrix.IsHermitian.spectral_theorem` | `A = conjStarAlgAut … (diagonal (ofReal ∘ eigenvalues))` |
| thm | `Matrix.IsHermitian.det_eq_prod_eigenvalues` | `det A = ∏ eigenvalues i` |
| thm | `Matrix.IsHermitian.trace_eq_sum_eigenvalues` | `trace A = ∑ eigenvalues i` |
| thm | `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues` | `spectrum ℝ A = range eigenvalues` |

### 4. Positive semidefinite, square root (CFC)

File: `Mathlib/LinearAlgebra/Matrix/PosDef.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `Matrix.PosSemidef` | `(M : Matrix n n R) : Prop := M.IsHermitian ∧ ∀ x, 0 ≤ re (star x ⬝ᵥ M *ᵥ x)` |
| def | `Matrix.PosDef` | strict version |
| thm | `PosSemidef.isHermitian`, `.add`, `.smul`, `.conjTranspose`, `.submatrix` | closure props |
| thm | `Matrix.posSemidef_conjTranspose_mul_self` / `posSemidef_self_mul_conjTranspose` | `AᴴA`, `AAᴴ` are PSD |

File: `Mathlib/Analysis/Matrix/PosDef.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| lemma | `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg` | `A.PosSemidef ↔ ∀ i, 0 ≤ eigenvalues i` |
| lemma | `Matrix.PosSemidef.eigenvalues_nonneg` | `0 ≤ hA.1.eigenvalues i` |
| lemma | `Matrix.PosSemidef.det_nonneg`, `trace_nonneg` | — |

PSD / Hermitian square root via C\*-algebra CFC — File:
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`
(namespace `CFC`; applies to any non-unital C\*-algebra `A`, incl. `Matrix n n 𝕜`)

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `CFC.sqrt` | `(a : A) : A := cfcₙ NNReal.sqrt a` — **the PSD square root `(AᴴA)^{1/2}`** |
| lemma | `CFC.sqrt_nonneg` | `0 ≤ sqrt a` |
| lemma | `CFC.sq_sqrt` | `0 ≤ a → sqrt a ^ 2 = a` |
| lemma | `CFC.sqrt_mul_self` / `sqrt_mul_sqrt_self` | `sqrt (a*a) = a`, `sqrt a * sqrt a = a` (for `0 ≤ a`) |
| lemma | `CFC.sqrt_unique` | `b*b = a → 0 ≤ b → sqrt a = b` |
| lemma | `CFC.sqrt_eq_iff`, `sqrt_eq_zero_iff`, `sqrt_eq_cfc`, `sqrt_eq_rpow` | characterizations |

File: `Mathlib/Analysis/Matrix/Order.lean` — matrix specializations:
`CFC.sqrt` on matrices (`Matrix` `StarOrderedRing`/`CStarAlgebra` via `CStarMatrix`),
`Matrix.det_sqrt : (CFC.sqrt A).det = RCLike.sqrt A.det`, `CFC.abs`,
`Matrix.IsHermitian.det_abs : det (CFC.abs A) = ‖det A‖`,
`Matrix.instStarOrderedRing`, `posSemidef_iff_isHermitian_and_spectrum_nonneg`.
(Note: a legacy `PosSemidef.sqrt` was removed/deprecated in favour of `CFC.sqrt`.)

**Usage in MET:** define `|A| := CFC.sqrt (Aᴴ * A)`; its eigenvalues (via
`IsHermitian.eigenvalues` of `AᴴA`, then √) are the singular values. The
log-volume `log ∏σ_i = log det |A|` is supported by `det_sqrt`.

### 5. Operator norms and submultiplicativity

Continuous linear maps — File: `Mathlib/Analysis/Normed/Operator/Basic.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `ContinuousLinearMap.opNorm` | `(f : E →SL[σ] F) := sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c*‖x‖}` (the `Norm` instance) |
| thm | `ContinuousLinearMap.le_opNorm` | `‖f x‖ ≤ ‖f‖ * ‖x‖` |
| thm | `ContinuousLinearMap.opNorm_le_bound` | `0 ≤ M → (∀ x, ‖f x‖ ≤ M*‖x‖) → ‖f‖ ≤ M` |
| thm | `ContinuousLinearMap.opNorm_nonneg` | `0 ≤ ‖f‖` |
| thm | `ContinuousLinearMap.opNorm_comp_le` | **`‖h.comp f‖ ≤ ‖h‖ * ‖f‖`** (submultiplicativity) |
| instance | `ContinuousLinearMap.toNormedRing` | `NormedRing (E →L[𝕜] E)` (`…/Operator/NormedSpace.lean:114`) |

Matrix L2 (spectral / induced-2) operator norm — File:
`Mathlib/Analysis/CStarAlgebra/Matrix.lean` (scoped namespace `Matrix.Norms.L2Operator`)

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `Matrix.instL2OpNormedAddCommGroup` / `instNormedRingL2Op` | scoped L2 op-norm `NormedRing` on `Matrix n n 𝕜` |
| instance | `Matrix.instCStarRing` | `Matrix n n 𝕜` is a `CStarRing` under this norm |
| def | `Matrix.toEuclideanCLM` | `Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)` |
| lemma | `Matrix.l2_opNorm_def` | `‖A‖ = ‖toEuclideanCLM A‖` |
| lemma | `Matrix.l2_opNorm_mul` | **`‖A * B‖ ≤ ‖A‖ * ‖B‖`** (submultiplicativity) |
| lemma | `Matrix.l2_opNorm_conjTranspose_mul_self` | `‖Aᴴ * A‖ = ‖A‖ * ‖A‖` (C\*-identity) |
| lemma | `Matrix.l2_opNorm_conjTranspose` | `‖Aᴴ‖ = ‖A‖` |
| lemma | `Matrix.l2_opNorm_mulVec` | `‖A *ᵥ x‖ ≤ ‖A‖ * ‖x‖` |
| lemma | `Matrix.l2_opNorm_diagonal` | `‖diagonal v‖ = ‖v‖` |

Other matrix norms — File: `Mathlib/Analysis/Matrix/Normed.lean`
(entrywise sup norm: `Matrix.norm_def`, `norm_entry_le_entrywise_sup_norm`;
Frobenius `NormedRing`: `frobeniusNormedRing`; l∞-operator `NormedRing`:
`linftyOpNormedRing`, `linftyOpNormedAlgebra`; `norm_diagonal`, `norm_conjTranspose`).

Spectral-radius / Rayleigh bridge — File:
`Mathlib/Analysis/InnerProductSpace/Rayleigh.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| thm | `ContinuousLinearMap.IsSelfAdjoint.norm_eq_iSup_rayleighQuotient` (`hT.norm_eq_iSup…`) | `‖T‖ = ⨆ rayleigh` for symmetric `T` |
| thm | `…rayleighQuotient_le_norm` | `|rayleigh T x| ≤ ‖T‖` |
| thm | `…spectralRadius_eq_nnnorm` | `spectralRadius = ‖T‖₊` for self-adjoint `T` |

**Usage in MET:** subadditivity `log‖Aⁿ⁺ᵐ‖ ≤ log‖Aⁿ‖ + log‖Aᵐ‖` (Kingman's
subadditive ergodic theorem feeds on `opNorm_comp_le` / `l2_opNorm_mul`) gives
the top Lyapunov exponent. The C\*-identity ties `‖A‖` to `√(top eigenvalue of
AᴴA)` = top singular value.

### 6. General linear group and determinant

File: `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| abbrev | `Matrix.GeneralLinearGroup` | `(n R) [DecidableEq n] [Fintype n] [Semiring R] := (Matrix n n R)ˣ`; notation `GL n R` |
| def | `Matrix.GeneralLinearGroup.det` | `: GL n R →* Rˣ` |
| lemma | `…det_ne_zero` | `g.val.det ≠ 0` |
| def | `…toLin` | `GL n R ≃* LinearMap.GeneralLinearGroup R (n → R)` |
| def | `…mk'` / `mk''` / `mkOfDetNeZero` | build a `GL` element from an invertible-det matrix |
| def | `…scalar` | `Rˣ →* GL n R` |

Related: `Mathlib/LinearAlgebra/GeneralLinearGroup/Basic.lean`
(`LinearMap.GeneralLinearGroup`), `Matrix/SpecialLinearGroup.lean`
(`Matrix.SpecialLinearGroup n R`, det = 1), `Matrix/GeneralLinearGroup/Card.lean`,
`.../Projective.lean`, `.../FinTwo.lean`.

Determinant — File: `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `Matrix.det` | `(M : Matrix n n R) : R` |
| thm | `Matrix.det_mul` | `det (M*N) = det M * det N` (multiplicativity → cocycle for det) |
| thm | `Matrix.det_one`, `det_smul` | `det 1 = 1`, `det (c•A) = c^card n * det A` |
| def | `Matrix.detMonoidHom` | `Matrix n n R →* R` |

File: `Mathlib/LinearAlgebra/Determinant.lean`

| Kind | Decl | Signature (abridged) |
|---|---|---|
| def | `LinearMap.det` | `: (M →ₗ[A] M) →* A` |
| thm | `LinearMap.det_comp` | `det (f∘g) = det f * det g` |
| def | `LinearEquiv.det` | `: (M ≃ₗ[R] M) →* Rˣ` |

**Usage in MET:** the random cocycle takes values in `GL d ℝ`; `det_mul` /
`LinearMap.det_comp` give the determinant cocycle (sum of all Lyapunov exponents
= `lim (1/n) log|det Aⁿ|`).

---

## Gaps (must build)

These concepts are **NOT in Mathlib** for the MET and must be constructed.

1. **Norm / inner product / topology on exterior powers `⋀[R]^k M`.**
   `exteriorPower` lives purely in `LinearAlgebra/`; there are *zero* references
   in `Analysis/` or `Topology/`. Must build: the induced inner product on
   `⋀^k E` for a real/complex inner product space `E` (Gram-determinant formula
   `⟨v₁∧…∧v_k, w₁∧…∧w_k⟩ = det(⟨v_i, w_j⟩)`), the resulting `NormedAddCommGroup`
   / `InnerProductSpace` instance, and the operator norm of `exteriorPower.map k f`.

2. **`‖⋀^k A‖ = ∏_{i<k} σ_i(A)` (volume / exterior-power norm = product of top k
   singular values).** Not present (follows from 1 + SVD). Central to the
   multidimensional MET (the Lyapunov spectrum via `⋀^k`).

3. **`Matrix.singularValues` (matrix-level wrapper) and `‖A‖ = σ_0(A)`** (operator
   norm = largest singular value). `LinearMap.singularValues` exists but there is
   **no matrix specialization** and **no lemma linking opNorm to the top singular
   value** (ingredients: `l2_opNorm_conjTranspose_mul_self`, Rayleigh
   `norm_eq_iSup_rayleighQuotient`, `IsHermitian.eigenvalues` of `AᴴA`).

4. **Polar decomposition `A = U·P` and the SVD `A = U Σ Vᴴ`.** No named
   `polarDecomposition` / `singularValueDecomposition` for matrices or operators.
   (The PSD factor `P = CFC.sqrt (AᴴA)` and the eigenvector unitary
   `IsHermitian.eigenvectorUnitary` exist; the unitary part U and the existence
   theorem must be assembled.) For MET this can largely be **bypassed** by working
   with `√(AᴴA)` and its eigenvalues directly.

5. **Singular values for matrices arranged as `Fin d → ℝ` / monotone-decreasing
   list with multiplicity, and `log`-singular-value sums.** `LinearMap.singularValues`
   is a `ℕ →₀ ℝ`; the MET wants the finite tuple `σ_1 ≥ … ≥ σ_d > 0` and
   `∑ log σ_i = log|det A|`. Glue (and the `det |A| = ∏ σ_i` identity) must be built.

6. **No topological-group / Lie-group instance for `GL n ℝ` with a fixed default
   norm.** `Matrix` norm instances are intentionally *scoped* (entrywise / L2-op /
   Frobenius / l∞-op all coexist); the project must `open scoped Matrix.Norms.L2Operator`
   (or similar) and, if needed, derive continuity of matrix multiplication /
   inversion on `GL n ℝ` for that norm. (`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`
   references `GeneralLinearGroup` but does not provide a packaged topological-group
   instance for the MET's purposes.)

---

## Notes / pitfalls

- **`LinearMap.singularValues` is brand new (2026)** and is the cleanest entry
  point — strongly prefer the operator (`LinearMap`/inner-product-space) framing
  over the matrix framing wherever possible, since the singular-value and spectral
  APIs are richest there.
- The PSD square root is **`CFC.sqrt`**, *not* a `Matrix.PosSemidef.sqrt` (legacy
  `PosSemidef.sqrt` deprecated in `Analysis/Matrix/Order.lean`). All its API lives
  in the C\*-algebra / continuous-functional-calculus namespace `CFC`.
- Eigenvalues come in two flavours: `…eigenvalues₀ : Fin (card n) → ℝ` (sorted,
  good for "i-th largest") and `…eigenvalues : n → ℝ` (reindexed by the entry
  type). For MET ordering arguments use the `₀` / `Fin n` versions
  (`eigenvalues_antitone`).
- Matrix L2 operator norm requires `open scoped` — it is **not** the default norm
  instance on `Matrix` (which is the entrywise sup norm in `Analysis/Matrix/Normed.lean`).
  Choose one norm project-wide to avoid instance clashes.
- The spectral theorem and singular values require `RCLike 𝕜` (ℝ or ℂ) and finite
  dimension — fine for MET over `ℝ^d`.
