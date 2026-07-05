# ExteriorNorm bridge kernel — `‖⋀^k f‖ = ∏σ` decomposition

> Fully-mapped plan for the lone `sorry` in `ErgodicTheory/Lyapunov/ExteriorNorm.lean`
> (`exteriorOpNorm_hodge_eq_prod_singularValues`). The bridge is a genuine missing-Mathlib
> multilinear-algebra development (det-Gram inner product on exterior powers + the operator-norm
> identity). This doc records the exact decomposition so the build is resumable across passes.

## Goal
`exteriorOpNorm k (hodgeTrivialization k) (hodgeTrivialization k) f = ∏_{i<k} σᵢ(f)`, where
`exteriorOpNorm k εE εF f = ‖toCLM (εF ∘ ⋀^k f ∘ εE⁻¹)‖` (op-norm in the Euclidean target) and
`hodgeTrivialization` sends the wedge basis of `stdOrthonormalBasis ℝ E` to the standard Euclidean basis.

## Already proved (sorry-free, in the file)
- `inner_apply_eigenvectorBasis_eq` : `⟪f uᵢ, f uⱼ⟫ = if i=j then σᵢ² else 0`, `u` = o.n. eigenbasis of `adjoint f ∘ f`.
- `norm_apply_eigenvectorBasis` : `‖f uᵢ‖ = σᵢ` (left singular vectors `wᵢ := f uᵢ / σᵢ` are o.n. when `σᵢ>0`).
- `exteriorOpNorm_comp_le` (engine), trivializations, `hodgeTrivialization`, `wedgeBasis`.

## The irreducible KERNEL: compound of orthogonal is orthogonal
For an orthogonal `Q : E ≃ₗᵢ E` (maps o.n. basis to o.n. basis), the matrix `C(Q)` of `⋀^k Q` in the
wedge basis is L2-orthogonal. Proof: `C(Q)ᵀ C(Q) = C(Qᵀ) C(Q) = C(Qᵀ Q) = C(I) = I` via
- **(i) `C(AB)=C(A)C(B)`** — `exteriorPower.map_comp` read in wedge-basis coordinates
  (`Basis.exteriorPower`, `exteriorPower.basis_repr_apply`/`ιMultiDual`).
- **(ii) `C(Qᵀ)=C(Q)ᵀ`** — the det-Gram step. `C(Q)ᵀ_{S,T}=C(Q)_{T,S}=` coord of `⋀^k Q (e_S)` at `e_T`.
  Under the Hodge (det-Gram) inner product `⟨e_T, ⋀^k Q e_S⟩ = det(⟨e_t, Q e_s⟩)_{t∈T,s∈S}
  = det(⟨Qᵀ e_t, e_s⟩) = ⟨⋀^k Qᵀ e_T, e_S⟩`, using `⟨a,Qb⟩=⟨Qᵀa,b⟩` (E-adjoint) inside the det.

## Sub-lemma ladder (suggested order)
1. **det-Gram bilinear form** `hodgeForm : ⋀^k E →ₗ ⋀^k E →ₗ ℝ` (NOT an instance — avoid the
   `AddCommGroup` diamond), defined on `ιMulti` families by `det(⟨vᵢ,wⱼ⟩)`, well-defined via the
   alternating universal property (`exteriorPower.alternatingMapToDual`/`ιMultiDual` machinery,
   `ExteriorPower/Basis.lean`, `Pairing.lean`). HARD (the bulk).
2. `hodgeForm` makes the wedge basis of any o.n. basis orthonormal (`= ιMultiDual_apply_diag/nondiag`
   specialized; det of identity Gram). MEDIUM.
3. `hodgeForm`-adjoint compatibility ⇒ KERNEL (ii) ⇒ `C(Q)` orthogonal for orthogonal `Q`. MEDIUM given 1.
4. **op-norm invariance**: `exteriorOpNorm k εE εF f` is the same for any two o.n.-basis-wedge
   trivializations (the change-of-coords is the L2-isometry `C(Q)` from 3). ⇒ may evaluate via the
   SVD basis. MEDIUM.
5. **SVD diagonalization**: with `u` (SVD basis of E) and `w` (left singular vectors, o.n. in F),
   `⋀^k f (u_S) = (∏_{j∈S} σⱼ) • w_S` (`exteriorPower.map_apply_ιMulti` + `norm_apply_eigenvectorBasis`).
   Through the `u`/`w` wedge trivializations `conjExteriorMap` is DIAGONAL with entries `∏_{j∈S}σⱼ`. MEDIUM.
6. **diagonal op-norm = max entry = ∏ top-k**: op-norm of a diagonal Euclidean map is `max |dᵢ|`;
   `max_{|S|=k} ∏_{j∈S} σⱼ = ∏_{j<k} σⱼ` since `σ` antitone (`singularValues_antitone`). EASY/combinatorial.
7. Assemble 4+5+6 ⇒ the bridge.

## Mathlib inventory
HAS: `Basis.exteriorPower`, `exteriorPower.ιMultiDual`/`_apply_diag`/`_apply_nondiag`,
`basis_repr_apply`, `exteriorPower.map`/`map_comp`/`map_apply_ιMulti`, `ExteriorPower/Pairing.lean`
(dual pairing), `LinearMap.singularValues_antitone`, `Matrix.IsHermitian.eigenvectorBasis`.
MISSING (build here): the det-Gram inner product / `hodgeForm` (step 1) and everything built on it;
no compound-matrix API; no "op-norm = top singular value".

## Status
**CLOSED — bridge fully proved, ExteriorNorm.lean is sorry-free.** Foundation committed `c6e1366`;
the det-Gram kernel + bridge landed on top (+483 lines). The whole ladder is now realized:
- `hodgeForm` (det-Gram bilinear form, step 1) — `hodgeForm_apply`, `innerₗ_eq_coord` (the form
  agrees with the Euclidean inner product through the o.n.-basis-wedge trivialization, step 2).
- op-norm invariance across o.n.-basis trivializations (`exteriorOpNorm_onbTriv_eq`, steps 3–4).
- SVD diagonalization: through the `u`/`wF` wedge trivializations `conjExteriorMap` is diagonal with
  entries `∏_{j∈S} σⱼ` (step 5), and `prod_le_prod_top` gives `max_{|S|=k} ∏ = ∏ top-k` (step 6).
- bridge: `exteriorOpNorm_hodge_eq_prod_singularValues` (`‖⋀^k f‖ = ∏_{i<k} σᵢ`), then
  `prod_singularValues_comp_le` (`∏σ(g∘f) ≤ ∏σ(g)·∏σ(f)`) — the submultiplicativity the scalar
  Lyapunov layer consumes.

QA gate passed: `lake build` green (exit 0, 2897 jobs); ExteriorNorm.lean has zero `sorry`; both
bridge theorems depend only on `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no
`native_decide`); statements verified non-vacuous. Critical path now advances to `OseledetsLimit.lean`.
