# Blueprint — Lyapunov layers L4–L5 + M7: Furstenberg–Kesten → TARGET `oseledets_filtration`

**Scope.** The path from the (assumed‑proved) Furstenberg–Kesten extremal exponents to
the project TARGET theorem `Oseledets.oseledets_filtration` in
`Oseledets/MultiplicativeErgodic.lean`. This is the upper half of the dependency ladder:
`understanding.md` layers **L4** (limsup spectrum + limsup flag), **L5** (limsup → genuine
lim), and **M7** (measurability), assembled at **L6.1 / M10**.

**This is a structural/scoping blueprint** for multi‑session implementation. It fixes the new
Lean modules, their public defs/theorems (real signatures matching project conventions),
the dependency order between them, the main proof idea for each, which Mathlib pieces exist
vs must be built, and the hard sub‑steps + the measurable‑selection risk. It is precise
enough to start implementing module by module; it does not spell out every micro‑lemma.

**New modules to create** (all under `Oseledets/Lyapunov/`, imported transitively from
`Oseledets.lean`; `MeasurableSubspace.lean` already exists):

| Module | Layer | Content |
|---|---|---|
| `Lyapunov/Ultrametric.lean` | L4.3 | Pure ultrametric linear algebra (no dynamics). **Build first.** |
| `Lyapunov/GrowthFunction.lean` | L4.1–4.2 | `lambdaBar (x,v)`, finiteness, scaling/ultrametric/equivariance. |
| `Lyapunov/Filtration.lean` | L4.4 | The limsup flag `V^i_x`, strict decrease, A‑equivariance. |
| `Lyapunov/Measurable.lean` | L4.5 / M7 | Measurability of `k`, `lambda_i`, `x ↦ V^i_x`. |
| `Lyapunov/Subbundle.lean` | L5.1–5.2 | Tempering; extremes on an invariant subbundle are genuine limits. |
| `Lyapunov/Limit.lean` | L5.3–5.5, L6.1 | Block‑triangular estimate, peel‑one‑exponent, induction; assemble TARGET. |

Convention reminders, fixed project‑wide (see `docs/plan/api-notes.md`):
matrices `Matrix (Fin d) (Fin d) ℝ`; vectors `EuclideanSpace ℝ (Fin d)`; scoped L2
operator norm (`open scoped Matrix.Norms.L2Operator`); the action is
`Matrix.toEuclideanCLM (𝕜 := ℝ) M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)`
(a `≃⋆ₐ[ℝ]`, hence multiplicative and unit‑preserving); `GL` encoded as `(A x).det ≠ 0`;
exponents **descending** `λ₁ > ⋯ > λ_k`; flag `⊤ = V 0 ⊋ ⋯ ⊋ V k = ⊥` via
`V i.succ x < V i.castSucc x`; measurable subspaces via `MeasurableSubspace` (the
`orthProjMatrix` encoding in `Oseledets/Lyapunov/MeasurableSubspace.lean`).

**Reusable, already proved (treat as black boxes):**
- Cocycle API: `cocycle`, `cocycle_add`, `cocycle_succ`, `measurable_cocycle`,
  `IntegrableLogNorm` (`Oseledets/Cocycle/Basic.lean`).
- Maximal ergodic inequality `setIntegral_birkhoffSum_pos_nonneg`
  (`Oseledets/Ergodic/MaximalErgodic.lean`).
- Pointwise Birkhoff `tendsto_birkhoffAverage_ae` (+ `[IsFiniteMeasure μ]`), ergodic
  corollary `tendsto_birkhoffAverage_ae_integral`, and the commutation lemma
  `condExp_invariants_comp` (`Oseledets/Ergodic/Birkhoff.lean`).
- Kingman `tendsto_kingman` (**assume available** with the signature in
  `Oseledets/Ergodic/Kingman.lean`; see §0 below) and its ergodic corollary
  `tendsto_kingman_ergodic` (constant limit under `Ergodic` + probability measure).
- Furstenberg–Kesten `furstenbergKesten_top`, `furstenbergKesten_bot`
  (`Oseledets/Cocycle/FurstenbergKesten.lean`; currently `sorry`, assume as black boxes —
  L4 only needs their *conclusions*).

---

## 0. The two engines as consumed by this layer (exact signatures)

**Kingman** (`Oseledets/Ergodic/Kingman.lean`, assumed):

```lean
structure IsSubadditiveCocycle (T : X → X) (g : ℕ → X → ℝ) : Prop where
  apply_add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)

theorem tendsto_kingman
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, (G ∘ T =ᵐ[μ] G) ∧ Integrable G μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 (G x)))
```

**Furstenberg–Kesten** (top/bottom), as stated in the repo. The key *facts* this layer
consumes (the existence of the a.e. constants and the resulting sandwich):

- `furstenbergKesten_top`: `∃ lam₁, ∀ᵐ x, (1/n) log‖cocycle A T n x‖ → lam₁`.
- `furstenbergKesten_bot`: `∃ lamₖ', ∀ᵐ x, (1/n) log‖(cocycle A T n x)⁻¹‖ → lamₖ'`;
  the bottom exponent is `lamₖ = −lamₖ'`.

**Note (norm bridge, used pervasively).** For the *vector* growth rate the statements use
`Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖`, which is the L2 norm of
the image vector. Bridges (all exist):
- `Matrix.l2_opNorm_toEuclideanCLM : ‖toEuclideanCLM M‖ = ‖M‖` (`rfl`).
- `(toEuclideanCLM M).le_opNorm v : ‖toEuclideanCLM M v‖ ≤ ‖toEuclideanCLM M‖ * ‖v‖`
  (`ContinuousLinearMap.le_opNorm`), combined with the above gives `‖M·v‖ ≤ ‖M‖·‖v‖`.
- For the lower sandwich, `‖M⁻¹‖⁻¹ · ‖v‖ ≤ ‖M·v‖`: write `v = (toEuclideanCLM M⁻¹)(M·v)`
  using multiplicativity (`map_mul` of `toEuclideanCLM` + `Matrix.nonsing_inv_mul` from
  `(A x).det ≠ 0`), then `‖v‖ ≤ ‖M⁻¹‖·‖M·v‖`.

---

## 1. `Lyapunov/Ultrametric.lean` — pure ultrametric linear algebra (L4.3) — BUILD FIRST

**Why first.** Self‑contained finite‑dimensional linear algebra with zero dynamics/measure
theory; it is the cleanest standalone module and the engine that forces the spectrum to be
finite (≤ d values) and the sublevel sets to be subspaces. Everything in L4.4 is a thin
application of it. Build and finish this before touching `lambdaBar`.

### 1.1 Statements to add

Work over a finite‑dimensional real inner‑product / vector space `E`; for the application
`E = EuclideanSpace ℝ (Fin d)`, but keep it abstract (`[NormedAddCommGroup E] [Module ℝ E]`
or `[AddCommGroup E] [Module ℝ E]` — only the vector space structure is needed). Values in
`ℝ` (we are in the finite regime by L4.1; `⊥`/`−∞` for the zero vector is handled by a
`WithBot ℝ` or by carrying `v ≠ 0` side conditions — recommend **carrying `v ≠ 0`** and
defining the function only implicitly through its axioms, to avoid `WithBot` arithmetic).

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A real‑valued function on the nonzero vectors of `E` is an **ultrametric growth
function** if it is scaling‑invariant and non‑Archimedean. (`g 0` is never referenced;
`v ≠ 0` side conditions are carried.) -/
structure IsUltrametricGrowth (g : E → ℝ) : Prop where
  scaling   : ∀ (c : ℝ) (v : E), c ≠ 0 → g (c • v) = g v
  ultra     : ∀ v w : E, v ≠ 0 → w ≠ 0 → v + w ≠ 0 → g (v + w) ≤ max (g v) (g w)

/-- **Strict ultrametric: equality when the two values differ.** -/
theorem IsUltrametricGrowth.add_eq_max_of_ne {g : E → ℝ} (h : IsUltrametricGrowth g)
    {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) (hne : g v ≠ g w) :
    g (v + w) = max (g v) (g w)

/-- **Vectors of distinct values are linearly independent.** -/
theorem IsUltrametricGrowth.linearIndependent_of_injOn {g : E → ℝ}
    (h : IsUltrametricGrowth g) {ι : Type*} {v : ι → E}
    (hv : ∀ i, v i ≠ 0) (hinj : Function.Injective (g ∘ v)) :
    LinearIndependent ℝ v

/-- The set of values is **finite** (the spectrum has ≤ d elements). -/
theorem IsUltrametricGrowth.finite_range {g : E → ℝ} [FiniteDimensional ℝ E]
    (h : IsUltrametricGrowth g) :
    (Set.range fun v : {v : E // v ≠ 0} => g v).Finite

/-- The **sublevel set** `{v | g v ≤ t}` (with `0` adjoined) is a submodule. -/
def IsUltrametricGrowth.sublevel {g : E → ℝ} (h : IsUltrametricGrowth g) (t : ℝ) :
    Submodule ℝ E where
  carrier := {v | v = 0 ∨ g v ≤ t}
  -- zero_mem', add_mem', smul_mem' from scaling + ultra
  ...

/-- `sublevel` is monotone in `t`, and **strictly** so across consecutive spectrum values
(strict because a value realized at `t₂` but not `t₁ < t₂` exhibits a vector in the gap). -/
theorem IsUltrametricGrowth.sublevel_mono {g : E → ℝ} (h : IsUltrametricGrowth g) :
    Monotone h.sublevel
```

### 1.2 Proof ideas

- `add_eq_max_of_ne`: WLOG `g v < g w`. Then `g w = g ((v+w) + (−v)) ≤ max (g (v+w), g v)`
  (using `scaling` with `c = −1` so `g (−v) = g v`). If `g (v+w) < g w` this would give
  `g w ≤ g v`, contradiction; combined with `ultra` gives `g (v+w) = g w = max`.
- `linearIndependent_of_injOn`: standard ultrametric independence. Suppose
  `∑ cᵢ • v i = 0` with not all `cᵢ` zero. Drop zero coefficients, then on the support all
  `g (cᵢ • v i) = g (v i)` are *distinct* (injectivity), so by repeated `add_eq_max_of_ne`
  the value of the sum equals `max` of the values — finite, hence the sum is nonzero,
  contradiction. Use `Finset.sum` induction + `add_eq_max_of_ne`. **Mathlib:**
  `linearIndependent_iff'`/`Fintype.linearIndependent_iff`, `Finset.sum`.
- `finite_range`: `≤ d` distinct values, each value class spans an independent set; a set of
  `m` vectors with distinct values is independent (previous lemma) so `m ≤ finrank = d`.
  `Set.Finite` from `Set.finite_of_injOn`‑style + `Module.finrank`. **Mathlib:**
  `finrank_le_of_linearIndependent`‑flavoured (`LinearIndependent.fintype_card_le_finrank`,
  `Module.finrank`), `Set.Finite`.
- `sublevel`: `zero_mem` by the `v = 0` disjunct; `add_mem` from `ultra` (both ≤ t ⇒ max ≤ t,
  with the `v+w=0` case landing in the zero disjunct); `smul_mem` from `scaling`
  (`c = 0` ⇒ zero).
- `sublevel_mono`: pointwise on carriers; strictness across spectrum values is proved in
  L4.4 once the spectrum is enumerated.

### 1.3 Mathlib pieces

EXISTS: `Submodule` builder, `LinearIndependent`, `linearIndependent_iff'`,
`LinearIndependent.fintype_card_le_finrank`, `Module.finrank`, `FiniteDimensional`,
`Set.Finite`. BUILD: all four theorems above (elementary).

---

## 2. `Lyapunov/GrowthFunction.lean` — the limsup growth function (L4.1–4.2)

### 2.1 Statements to add

```lean
open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X} {d : ℕ}

/-- The **upper Lyapunov growth function**
`lambdaBar A T x v = limsup_n (1/n) log‖A⁽ⁿ⁾(x) v‖`. -/
noncomputable def lambdaBar (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X)
    (x : X) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Filter.limsup
    (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
    atTop

/-- L4.1 finiteness: for `v ≠ 0`, `lambdaBar` is sandwiched between the bottom and top
exponents. Stated as a two‑sided bound on a.e. `x` against the FK constants `lamBot ≤ lamTop`. -/
theorem lambdaBar_mem_Icc
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∃ lamBot lamTop : ℝ, lamBot ≤ lamTop ∧ ∀ᵐ x ∂μ,
      ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 → lambdaBar A T x v ∈ Set.Icc lamBot lamTop

/-- L4.2 scaling. -/
theorem lambdaBar_smul (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    {c : ℝ} (hc : c ≠ 0) (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) :
    lambdaBar A T x (c • v) = lambdaBar A T x v

/-- L4.2 ultrametric. -/
theorem lambdaBar_add_le (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (v w : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    lambdaBar A T x (v + w) ≤ max (lambdaBar A T x v) (lambdaBar A T x w)

/-- L4.2 A‑equivariance: `lambdaBar A T x v = lambdaBar A T (T x) (A x · v)`. -/
theorem lambdaBar_equivariant (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X)
    (hA : (A x).det ≠ 0) (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) :
    lambdaBar A T x v
      = lambdaBar A T (T x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x) v)

/-- Packaged: for a.e. `x`, `lambdaBar A T x` is an ultrametric growth function. -/
theorem isUltrametricGrowth_lambdaBar
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, IsUltrametricGrowth (lambdaBar A T x)
```

### 2.2 Proof ideas

- **`lambdaBar_smul`**: `‖toEuclideanCLM M (c • v)‖ = |c| · ‖toEuclideanCLM M v‖` (CLM is
  linear; `norm_smul`). `log (|c| · t) = log|c| + log t`, so the sequence differs by the
  constant `(1/n) log|c| → 0`; `limsup` is invariant under adding a sequence → 0. **Mathlib:**
  `map_smul`/`ContinuousLinearMap.map_smul`, `Real.log_mul`, and the project's own
  `limsup_eq_of_sub_tendsto_zero` (private in `Birkhoff.lean` — **promote it to a shared
  helper**, or re‑prove a `limsup` `add_const`‑tending‑to‑0 lemma; see Risks). Edge cases:
  `log 0` for `v = 0` excluded by `hv`; for `M·v ≠ 0` use `(A x).det ≠ 0` ⇒
  `toEuclideanCLM (cocycle) ` injective.
- **`lambdaBar_add_le`**: `‖M (v+w)‖ ≤ ‖M v‖ + ‖M w‖ ≤ 2 max(‖M v‖, ‖M w‖)`. Then
  `(1/n) log‖M(v+w)‖ ≤ (1/n) log 2 + max((1/n)log‖M v‖, (1/n)log‖M w‖)`. Take `limsup`;
  `(1/n)log 2 → 0`, and `limsup (max aₙ bₙ) ≤ max (limsup aₙ) (limsup bₙ)` (the reverse fails
  in general but ≤ is fine — actually `limsup_max` is `=`; we only need ≤). **Mathlib:**
  `Real.add_pow_le_pow_mul_pow_of_sq_le`? no — use `Real.log_le_log`, `norm_add_le`,
  `Filter.limsup_le_limsup`, and a `limsup (max f g) ≤ max (limsup f) (limsup g)` lemma.
  Search `Filter.limsup_max`/`limsup_sup` (`Mathlib/Order/LiminfLimsup.lean`); if absent,
  prove ≤ directly from `limsup_le_iff`. Need boundedness of the sequences (from L4.1
  sandwich) for `limsup` algebra — so this lemma is proved **a.e.** with the sandwich in
  scope, or stated as a clean unconditional ≤ via `limsup_le_limsup` requiring cobounded.
- **`lambdaBar_equivariant`**: cocycle identity `cocycle A T (n+1) x = cocycle A T n (T x) * A x`
  (`cocycle_succ`), so `toEuclideanCLM (cocycle A T (n+1) x) v
  = toEuclideanCLM (cocycle A T n (T x)) (toEuclideanCLM (A x) v)` (multiplicativity:
  `map_mul` of the star‑alg‑equiv `toEuclideanCLM`, `ContinuousLinearMap.comp_apply`). Hence
  `(1/(n+1)) log‖cocycle A T (n+1) x · v‖ = (1/(n+1)) log‖cocycle A T n (T x) · (A x·v)‖`.
  The `limsup` over `n+1` equals the `limsup` over `n` of the RHS sequence indexed at `n`
  (the `1/(n+1)` vs `1/n` discrepancy → 0; `limsup_nat_add`). Conclude equality of the two
  `limsup`s. **Mathlib:** `map_mul`, `Filter.limsup_nat_add`, `cocycle_succ`.
- **`lambdaBar_mem_Icc`**: from FK. Upper: `‖M·v‖ ≤ ‖M‖·‖v‖` ⇒
  `(1/n) log‖M·v‖ ≤ (1/n) log‖M‖ + (1/n) log‖v‖`; `limsup ≤ lamTop + 0`. Lower:
  `‖M·v‖ ≥ ‖M⁻¹‖⁻¹·‖v‖` (the inverse sandwich above) ⇒ `(1/n) log‖M·v‖ ≥ −(1/n)log‖M⁻¹‖ + …`;
  `liminf ≥ lamBot`, and `limsup ≥ liminf`. So `lamBot ≤ lambdaBar ≤ lamTop`. The constants
  come from `furstenbergKesten_top`/`_bot`. **Mathlib:** `ContinuousLinearMap.le_opNorm`,
  `Real.log_le_log`, `Real.log_mul`, `Filter.le_limsup`/`liminf_le_limsup`.
- **`isUltrametricGrowth_lambdaBar`**: bundle the three a.e. facts (`smul`, `add_le`,
  equivariance is not part of the structure) into the `IsUltrametricGrowth` predicate. The
  `scaling`/`ultra` fields are exactly `lambdaBar_smul`/`lambdaBar_add_le`.

### 2.3 Mathlib / project pieces

EXISTS: `cocycle_succ`, `map_mul` (star‑alg‑equiv), `ContinuousLinearMap.le_opNorm`,
`norm_smul`, `Real.log_mul`, `Real.log_le_log`, `Filter.limsup_nat_add`,
`Filter.liminf_le_limsup`, `Matrix.l2_opNorm_toEuclideanCLM`, `Matrix.nonsing_inv_mul`.
BUILD: the four `lambdaBar_*` theorems + the bundling; **promote** the `limsup`
vanishing‑perturbation helper from `Birkhoff.lean`.

---

## 3. `Lyapunov/Filtration.lean` — the limsup flag (L4.4)

### 3.1 Statements to add

For a.e. `x` the values of `lambdaBar A T x` over `v ≠ 0` form a finite set (L4.3
`finite_range`). Enumerate them **descending** as `λ₁ > ⋯ > λ_k`. Encode the enumeration as a
`Finset ℝ` plus a `Fin k → ℝ` strictly antitone listing. Two options:

(A) define everything **per‑`x`**: `spectrum A T x : Finset ℝ := (finite_range …).toFinset`,
    `k x := spectrum.card`, `lam x : Fin (k x) → ℝ` the descending list, `Vflag x i` the
    sublevel set at the `i`‑th value;
(B) under ergodicity `k`, `lam` are a.e. **constant** — defer the constancy to M7/assembly.

Recommend (A) for the per‑point structure, with the a.e.‑constancy proved separately
(see §4 / §6).

```lean
/-- The (finite) **limsup spectrum** at `x`: the set of values of `lambdaBar A T x` on
nonzero vectors. -/
noncomputable def spectrum (A : X → Matrix (Fin d) (Fin d) ℝ) (T : X → X) (x : X) :
    Finset ℝ := ...   -- (h.finite_range).toFinset, with h := isUltrametricGrowth_lambdaBar at x

/-- The number of distinct exponents at `x`. -/
noncomputable def specCard (A) (T) (x) : ℕ := (spectrum A T x).card

/-- The descending list of exponents `lam x : Fin (specCard A T x) → ℝ`. -/
noncomputable def specList (A) (T) (x) : Fin (specCard A T x) → ℝ :=
  ((spectrum A T x).sort (· ≥ ·)) ...   -- via Finset.orderIsoOfFin / monoEquivOfFin, reversed

/-- The limsup flag: `Vflag A T x i = {v | v = 0 ∨ lambdaBar A T x v ≤ (specList … i)}`
extended with `V 0 = ⊤` and `V (last) = ⊥`. Indexed by `Fin (specCard A T x + 1)`. -/
noncomputable def Vflag (A) (T) (x) (i : Fin (specCard A T x + 1)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) := ...

/-- L4.4 (a) `Vflag x 0 = ⊤`. -/
theorem Vflag_zero ... : Vflag A T x 0 = ⊤

/-- L4.4 (a) `Vflag x (last) = ⊥`. -/
theorem Vflag_last ... : Vflag A T x (Fin.last _) = ⊥

/-- L4.4 (b) strict decrease. -/
theorem Vflag_strictAnti ... (i : Fin (specCard A T x)) :
    Vflag A T x i.succ < Vflag A T x i.castSucc

/-- L4.4 (c) on each stratum `lambdaBar` equals the exact value `λᵢ`. -/
theorem lambdaBar_eq_on_stratum ... (i : Fin (specCard A T x)) {v}
    (hmem : v ∈ Vflag A T x i.castSucc) (hnot : v ∉ Vflag A T x i.succ) :
    lambdaBar A T x v = specList A T x i

/-- L4.4 (d) A‑equivariance of each level (uses `lambdaBar_equivariant`). -/
theorem Vflag_equivariant ... (i) :
    Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (Vflag A T x i)
      = Vflag A T (T x) i'   -- with specCard A T x = specCard A T (T x), index transported
```

### 3.2 Proof ideas

- `Vflag` levels are `IsUltrametricGrowth.sublevel` at the spectrum values (L4.3). `V 0 = ⊤`
  because the top exponent `λ₁ = lamTop` bounds *all* `lambdaBar` (L4.1 sandwich), so every
  `v` is in the sublevel at `λ₁`. `V (last) = ⊥` because below the smallest value `λ_k` only
  `0` survives (the sublevel at `λ_k − ε` is `{0}`, but here the last level is the empty
  sublevel `{0}`, i.e. `⊥` by construction of the indexing — make `V (last) := ⊥` literally).
- Strict decrease: between consecutive spectrum values `λ_{i+1} < λᵢ` there is, by definition
  of `spectrum`, a vector `v` with `lambdaBar x v = λᵢ`; it lies in `V i.castSucc` but not in
  `V i.succ`. Use `Finset`‑sort adjacency. **Mathlib:** `Finset.sort`, `List.Sorted`,
  `Finset.orderIsoOfFin`.
- Stratum exactness: `v ∈ V i.castSucc` ⇒ `lambdaBar ≤ λᵢ`; `v ∉ V i.succ` ⇒ `lambdaBar > λ_{i+1}`;
  but `lambdaBar` is a spectrum value, and the only value in `(λ_{i+1}, λᵢ]` is `λᵢ`. So
  `lambdaBar = λᵢ`.
- Equivariance: `lambdaBar_equivariant` ⇒ `lambdaBar A T (Tx) (A x · v) = lambdaBar A T x v`,
  so `A x` maps the sublevel at `t` (for `x`) bijectively to the sublevel at `t` (for `Tx`);
  invertibility of `toEuclideanCLM (A x)` (from `det ≠ 0`) makes `Submodule.map` an order
  iso. The spectra coincide (`spectrum A T x = spectrum A T (T x)`) because `A x` is a
  bijection on nonzero vectors preserving `lambdaBar` values. **Mathlib:**
  `Submodule.orderIsoMapComap` (for the `LinearEquiv` underlying the invertible CLM),
  `Submodule.map_top`, `Submodule.map_bot`.

### 3.3 Mathlib pieces

EXISTS: `Finset.sort`/`orderIsoOfFin`/`monoEquivOfFin`, `Submodule.orderIsoMapComap`,
`Submodule.map_top`, `Submodule.map_bot`, `Fin.succ`/`castSucc`/`last`. BUILD: `spectrum`,
`specCard`, `specList`, `Vflag`, and the five theorems. **Index bookkeeping** (`Fin k`
vs `Fin (k+1)`, transporting indices across `specCard A T x = specCard A T (T x)`) is the
fiddly part — see Risks.

---

## 4. `Lyapunov/Measurable.lean` — measurability (L4.5 / M7) — HARD, see Risks

### 4.1 Statements to add

```lean
/-- `x ↦ specCard A T x` is measurable (and a.e. constant under ergodicity). -/
theorem measurable_specCard ... : Measurable (specCard A T)
theorem specCard_ae_const ... : ∃ k, ∀ᵐ x ∂μ, specCard A T x = k

/-- `x ↦ specList A T x i` is measurable; a.e. constant under ergodicity. -/
theorem measurable_specList ... : ...   -- on the a.e. set {specCard = k}
theorem specList_ae_const ... : ∃ lam : Fin k → ℝ, ∀ᵐ x ∂μ, ... = lam

/-- The flag levels depend measurably on `x` (the project's `MeasurableSubspace`). -/
theorem measurableSubspace_Vflag ... (i) :
    MeasurableSubspace fun x => Vflag A T x (indexAt x i)
```

### 4.2 Proof ideas (Zhu Prop 5.10, recursive)

1. `lambdaBar A T · v` is measurable in `x` for fixed `v`: it is a `limsup` of the measurable
   functions `x ↦ (1/n) log‖toEuclideanCLM (cocycle A T n x) v‖` (`measurable_cocycle`,
   `toEuclideanCLM` continuous, `Real.log` measurable, `Measurable.limsup`).
2. `λ₁(x) = lamTop` is a.e. constant (FK). The function `x ↦ max_i lambdaBar A T x (e i)`
   over the standard basis is measurable and equals `λ₁(x)` (the top value is realized on a
   basis vector). So `specList … 0` measurable.
3. The *graph* `{(x,v) | lambdaBar A T x v < λ₁(x)}` is product‑measurable; its `x`‑projection
   `{x | specCard ≥ 2}` is measurable (**projection of a product‑measurable set** —
   Zhu Fact 5.9; the measurable‑projection theorem). Iterate to peel `λ₂, λ₃, …`.
4. For the subspace map: on `{specCard = k}`, select a **measurable orthonormal frame**
   spanning each level via `gramSchmidt` applied to a measurable choice of basis vectors of
   the sublevel set, and read off `orthProjMatrix (Vflag …)` measurably. Then
   `MeasurableSubspace` holds by definition (`orthProjMatrix` measurable).
5. Under `Ergodic`, `specCard`, `specList` are a.e. `T`‑invariant (from `Vflag_equivariant`
   + `lambdaBar_equivariant`) hence a.e. constant
   (`Ergodic.ae_eq_const_of_ae_eq_comp_ae`, needs `AEStronglyMeasurable`).

### 4.3 Mathlib pieces — and the GAP

EXISTS: `Measurable.limsup` (`Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`),
`measurable_cocycle`, `gramSchmidt`/`gramSchmidtNormed`/`gramSchmidtOrthonormalBasis`
(`Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`), `Submodule.starProjection`
(`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`),
`Ergodic.ae_eq_const_of_ae_eq_comp_ae`.

**GAP / RISK (the single hardest infrastructure piece of this whole layer):**
- **Measurable projection** of `{(x,v) | …}` onto `x` (Zhu Fact 5.9): the projection of a
  product‑measurable set is measurable *only* under analytic/Suslin hypotheses (the projection
  of a Borel set is analytic, measurable w.r.t. the completed/universally‑measurable σ‑algebra,
  not Borel). Mathlib has `MeasureTheory.measurableSet_projection_of_…`? — **must verify**;
  the Kuratowski–Ryll‑Nardzewski / Jankov–von Neumann **measurable‑selection** theorems are
  only partially in Mathlib. **Mitigation:** avoid raw projection by working with the
  orthogonal‑projection encoding directly: the rank `dim (Vflag A T x i)` is
  `x ↦ (orthProjMatrix …).trace` (an integer‑valued measurable function once the projection
  matrix is shown measurable), and the levels are cut out by *thresholding `lambdaBar` against
  the (a.e. constant) `specList` values*, which sidesteps per‑`x` selection. Concretely,
  under ergodicity fix the constant `lam : Fin k → ℝ` first (step 5), then
  `Vflag A T x i = sublevel (lambdaBar A T x) (lam i)` with **fixed thresholds**, and prove
  `x ↦ orthProjMatrix (sublevel … (lam i))` measurable. This is still nontrivial (the
  projection onto a sublevel set varying measurably) but avoids the analytic‑projection
  theorem. See §7 Risks.
- **Measurable orthonormal frame for a measurably‑varying subspace**: needs a measurable
  selection of a basis of `Vflag A T x i`. With fixed thresholds and a.e.‑constant dimension,
  one can take a measurable choice from the standard basis vectors landing in the sublevel
  set (measurable since membership `lambdaBar A T x (e j) ≤ lam i` is measurable in `x`),
  then `gramSchmidt`. The measurability of `gramSchmidt` in the data is `fun_prop`‑provable
  (it is an algebraic expression in inner products), but **building it is real work**.

---

## 5. `Lyapunov/Subbundle.lean` — tempering + extremes on a subbundle are limits (L5.1–5.2)

### 5.1 Statements to add

```lean
/-- **L5.1 Tempering (Birkhoff corollary).** If `φ ∘ T − φ` is integrable then
`(1/n) φ(Tⁿ x) → 0` a.e. -/
theorem ae_tendsto_temper
    [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    {φ : X → ℝ} (hφ : Integrable (fun x => φ (T x) - φ x) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * φ (T^[n] x)) atTop (𝓝 0)

/-- **L5.2 Extremes on an invariant subbundle are genuine limits.** For a measurable,
A‑equivariant subbundle `W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))` of a.e. constant
dimension `ℓ`, the top and bottom growth on `W` are genuine limits:
`lim (1/n) log‖A⁽ⁿ⁾(x)|_{W x}‖ = max_{0≠v∈W x} lambdaBar A T x v` (and dually for the conorm /
min). -/
theorem tendsto_top_on_subbundle
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    {W : X → Submodule ℝ (EuclideanSpace ℝ (Fin d))} (hWmeas : MeasurableSubspace W)
    (hWinv : ∀ᵐ x ∂μ, Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (W x)
        = W (T x)) :
    ∃ lamW : ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖restrictCocycleNorm A T W n x‖) atTop (𝓝 lamW)
      ∧ lamW = ⨆ v ∈ {v // v ∈ W x ∧ v ≠ 0}, lambdaBar A T x v
-- (and the analogous `tendsto_bot_on_subbundle` for the conorm / min)
```

Here `restrictCocycleNorm A T W n x` denotes `‖(cocycle restricted to W)‖`; concretely, after
trivializing `W x ≅ ℝ^ℓ` by a measurable orthonormal frame `F x` (a `ℓ × d` isometry), the
**sub‑cocycle** is `D n x := (F (Tⁿx))ᵀ · cocycle A T n x · F x ∈ Matrix (Fin ℓ) (Fin ℓ) ℝ`
(an honest `GL(ℓ)` cocycle), and `restrictCocycleNorm` is `‖D n x‖`.

### 5.2 Proof ideas

- **L5.1**: immediate from pointwise Birkhoff. `birkhoffSum T (φ∘T − φ) n x` telescopes to
  `φ(Tⁿx) − φ(x)`, so `(1/n)(φ(Tⁿx) − φ x) = birkhoffAverage T (φ∘T−φ) n x → ∫(φ∘T−φ) = 0`
  (the integral vanishes by measure‑preservation: `∫ φ∘T = ∫ φ`). Then `(1/n)φ(Tⁿx) → 0`.
  **Mathlib/project:** `tendsto_birkhoffAverage_ae_integral`, `birkhoffSum` telescoping
  (`birkhoffSum` of a coboundary), or directly the project's own
  `ae_tendsto_orbit_div_atTop_zero` (private in `Birkhoff.lean`) which already proves
  `(1/n) g(Tⁿx) → 0` for any integrable `g` — **promote it** and apply with `g = φ` (needs
  only `Integrable φ`, even cleaner than the coboundary form). **Note:** the coboundary
  framing is the Bochi statement; the project's helper gives the stronger `(1/n)g(Tⁿx)→0` for
  *any* integrable `g`, so prefer that.
- **L5.2**: trivialize `W` to a sub‑cocycle `D` in `GL(ℓ)` via a measurable orthonormal frame
  `F` (from M7 §4.4). `D` is an honest cocycle (`D (m+n) x = D m (Tⁿx) · D n x` follows from
  equivariance `A x · (W x) = W (Tx)` making the frame change orthogonal). Check
  `log⁺‖D^{±1}‖ ∈ L¹` (inherited: `‖D n x‖ ≤ ‖cocycle A T n x‖` since `F` is an isometry; the
  inverse bound likewise from `hint'`). Apply **`furstenbergKesten_top`/`_bot` to `D`**: the
  top exponent of `D` is a genuine limit `lamW`, and it equals `max_{v∈W} lambdaBar A T x v`
  (the operator norm growth of the restricted cocycle is the top growth rate over `W`; ≤ from
  `‖D^n‖ ≥ ‖D^n u‖` for unit `u`, ≥ by realizing the max on a vector — the FK limit is the
  sup of growth rates). **This is the load‑bearing "limsup becomes lim on the extremes" step.**
  **Mathlib/project:** `furstenbergKesten_top`/`_bot` (black boxes), the frame construction
  (M7), `Matrix.l2_opNorm_*`.

### 5.3 Mathlib / project pieces

EXISTS: pointwise Birkhoff + ergodic corollary, FK top/bottom (black boxes),
`gramSchmidt` frame (M7), `Matrix.l2_opNorm_mul`, the project's
`ae_tendsto_orbit_div_atTop_zero` (promote). BUILD: `restrictCocycleNorm`/the sub‑cocycle
`D`, its cocycle identity + integrability inheritance, `tendsto_top/bot_on_subbundle`, and
the identification of `lamW` with the max/min of `lambdaBar` on `W`. **Depends on M7** for the
measurable frame — this couples L5.2 to the M7 risk.

---

## 6. `Lyapunov/Limit.lean` — block‑triangular estimate, peel, induct; assemble TARGET (L5.3–5.5, L6.1)

### 6.1 Statements to add

```lean
/-- **L5.3 Tempered block‑triangular estimate (Bochi Lemma 12 / Zhu Fact 5.20).** In the
orthogonal block form of the cocycle relative to an invariant subbundle `W`, the
off‑diagonal block grows no faster than the diagonal blocks. -/
theorem offDiagonal_growth_le ... :
    ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop,
      (n : ℝ)⁻¹ * Real.log ‖offDiagBlock A T W n x‖ ≤ max αW βWperp + ε
-- αW = top exponent on W, βWperp = top exponent on the quotient; precise form per Zhu.

/-- **L5.4 Peel one exponent (Bochi Lemma 13 / Zhu Lemma 5.19).** With `W = V_k` (the bottom
level), the quotient cocycle `B` on `Wᗮ` has the same limsup spectrum on the upper layers,
one fewer exponent, and a genuine limit on `W` transports back to `A`. -/
theorem peel_one_exponent ... :
    -- the genuine forward limit on the bottom stratum, plus a reduced cocycle on Wᗮ
    ...

/-- **L5.5 Genuine forward limit on every stratum (Bochi Thm 2 / Zhu Prop 5.26).** -/
theorem tendsto_log_norm_cocycle_on_stratum
    [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {A : X → Matrix (Fin d) (Fin d) ℝ} (hA : ∀ x, (A x).det ≠ 0) (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ) (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ) :
    ∀ᵐ x ∂μ, ∀ (i : Fin (specCard A T x)) (v : EuclideanSpace ℝ (Fin d)),
      v ∈ Vflag A T x i.castSucc → v ∉ Vflag A T x i.succ →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
        atTop (𝓝 (specList A T x i))
```

The TARGET `oseledets_filtration` (already stated, `sorry` in
`Oseledets/MultiplicativeErgodic.lean`) is then **assembled** from:
- L4.4 `Vflag_*` (flag shape, strict decrease, equivariance) + M7 `specCard_ae_const`,
  `specList_ae_const` (to produce the constant `k`, `lam : Fin k → ℝ`, `StrictAnti lam`);
- M7 `measurableSubspace_Vflag` (the `∀ i, MeasurableSubspace (V i)` clause);
- L5.5 `tendsto_log_norm_cocycle_on_stratum` (the genuine‑limit clause).

### 6.2 Proof ideas

- **L5.3**: orthogonal block form `A = [[B,0],[C, D]]` w.r.t. `ℝ^d = Wᗮ ⊕ W` (upper‑right `0`
  by equivariance `A x · W x = W (Tx)`). The iterated off‑diagonal expands as
  `C_n = Σ_{j} D_{n−j−1}(T^{j+1}x) C(Tʲx) B_j(x)`. Bound each factor: `‖B_j u‖ ≤ b_ε e^{j(β+ε)}`,
  `‖C(Tʲx)‖ ≤ c_ε e^{jε}` (tempering L5.1 on `log⁺‖C‖`), and the **tempered diagonal bound**
  `‖D_n(Tᵐx)‖ ≤ d_ε(x) e^{α n + (m+n)ε}` (L5.1 applied to the L5.2 top‑exponent limit on `W`).
  Sum the geometric‑type series; the gap `β` vs `α` keeps the off‑diagonal subordinate. This
  is **pure hard analysis, self‑contained once L5.1/L5.2 are available** (the most error‑prone
  *analytic* part). **Mathlib/project:** `Finset.sum`, `Real.exp`/`Real.log` monotonicity,
  `ae_tendsto_temper` (L5.1), `tendsto_top_on_subbundle` (L5.2).
- **L5.4**: take `W = Vflag … (last bottom level)`. L5.2 gives the genuine limit
  `= λ_k` on `W` (max = min there since `W` is a single stratum's span — actually `W = V_k`
  is the bottom level where `lambdaBar = λ_k` exactly). The quotient cocycle `B` on `Wᗮ` has
  flag `Uⁱ = Wᗮ ∩ Vⁱ` and limsup spectrum `λ₁ > ⋯ > λ_{k−1}` (one fewer). L5.3 ⇒ a vector
  `u + v` (`u ∈ Wᗮ`, `v ∈ W`) grows at the `B`‑rate of `u`, so the genuine limit for `B`
  transports to `A`.
- **L5.5**: induction on `specCard = k` (a.e. constant under ergodicity, so restrict to the
  full‑measure invariant set where `specCard = k`). Base `k = 1`: single exponent, L5.2 with
  `W = ⊤` gives `lim = λ₁` for all `v ≠ 0`. Step: L5.4 peels `λ_k` (genuine limit on `V_k`),
  recurse on `B` over `Wᗮ` (dimension drops), transport the limits back via L5.4.
- **Assembly (L6.1)**: introduce `k` and `lam` from M7 constancy; provide
  `V : Fin (k+1) → X → Submodule …` by `V i x := Vflag A T x (transport i)` on the a.e. set
  `{specCard = k}` and `⊤`/arbitrary off it (the conclusion is `∀ᵐ`, so off‑set values are
  irrelevant); discharge `StrictAnti lam` from the descending enumeration, the flag clauses
  from `Vflag_*`, measurability from M7, the genuine limit from L5.5.

### 6.3 Mathlib / project pieces

EXISTS: everything algebraic + the lower‑layer black boxes. BUILD: L5.3 (hard analysis),
L5.4, L5.5 (induction), and the final assembly. The induction's **index/dimension
bookkeeping** across the peeling (transporting `Vflag` indices between the cocycle `A` and the
reduced cocycle `B` on `Wᗮ`) is the structural risk here.

---

## 7. The 2–3 hardest sub‑steps and the measurable‑selection risk

1. **M7 measurability via measurable projection / measurable selection (§4) — the single
   biggest infrastructure risk.** Zhu's Fact 5.9 (projection of a product‑measurable set is
   measurable) is an *analytic‑sets* statement; Mathlib's coverage of
   Kuratowski–Ryll‑Nardzewski / Jankov–von Neumann measurable selection is **partial**, and
   the projection of a Borel set is in general only universally/analytically measurable, not
   Borel. **Mitigation (recommended):** under ergodicity, first prove `specList` is a.e. a
   **constant** vector `lam : Fin k → ℝ` (via `lambdaBar_equivariant` ⇒ `specList` invariant ⇒
   `Ergodic.ae_eq_const_of_ae_eq_comp_ae`), then define the flag levels by **fixed thresholds**
   `Vflag x i = sublevel (lambdaBar A T x) (lam i)` and prove `x ↦ orthProjMatrix (…)`
   measurable *without* per‑`x` selection — membership `lambdaBar A T x (e j) ≤ lam i` is
   measurable in `x` (limsup of measurables), giving a measurable choice of spanning basis
   vectors, then `gramSchmidt`. This sidesteps the analytic‑projection theorem entirely but
   still requires: (i) measurability of `x ↦ lambdaBar A T x v` (easy, `Measurable.limsup`),
   (ii) building the measurable orthonormal frame + its projection matrix (real work, but
   `fun_prop`‑amenable since `gramSchmidt` is algebraic in inner products). **If** even this
   is too costly, the fallback is to state the measurability clause w.r.t. the
   completed/universally‑measurable σ‑algebra and document the gap.

2. **L5.3 tempered block‑triangular estimate (§6, Zhu Fact 5.20).** Pure hard analysis: a
   summed‑geometric‑series bound on the off‑diagonal block with three tempered factors. No
   missing Mathlib API, but the most error‑prone *manual* estimate (Borel–Cantelli/`o(n)`
   flavour). Budget several sessions; isolate `Real.exp`/`Real.log` algebra into helper lemmas.

3. **L5.2 extremes‑are‑limits (§5, Zhu Lemma 5.11).** Conceptually the heart of "limsup → lim":
   it converts the limsup growth function into honest FK limits on an invariant subbundle by
   building a *sub‑cocycle*. The risk is the **frame construction** (couples to risk 1) and the
   identification `lamW = max lambdaBar on W`. The cocycle identity for the trivialized
   sub‑cocycle `D` must be checked carefully (the orthonormal frame change `Fᵀ · A · F` is a
   genuine cocycle only because of equivariance).

Secondary risks:
- **`limsup` algebra under vanishing perturbations** is used all over L4. The project already
  proved `limsup_eq_of_sub_tendsto_zero` (private in `Birkhoff.lean`); **promote it** to a
  shared `Oseledets` helper (e.g. a small `Oseledets/Util/Limsup.lean`) and add the matching
  `limsup_le_limsup` + `limsup (max f g) ≤ max (limsup f) (limsup g)` lemmas (verify
  `Filter.limsup_max`/`limsup_sup` names in `Mathlib/Order/LiminfLimsup.lean`).
- **Index bookkeeping** (`Fin k` / `Fin (k+1)`, `castSucc`/`succ`/`last`, transporting indices
  across `specCard A T x = specCard A T (T x)` and across the peeling reduction). Pervasive;
  keep a single convention and a transport lemma. Largely `omega`/`Fin.cases` discharge but
  voluminous.
- **`WithBot ℝ` vs `ℝ`+side‑conditions for `lambdaBar 0`.** Recommend `ℝ` with `v ≠ 0` side
  conditions throughout (the finite regime is guaranteed by `log⁺‖A⁻¹‖ ∈ L¹`), avoiding
  `WithBot` arithmetic in the ultrametric algebra.

---

## 8. Build/import order (one line)

`Ultrametric` (no deps) → `GrowthFunction` (Ultrametric + FK + Cocycle) →
`Filtration` (GrowthFunction + Ultrametric) → `Measurable` (Filtration + GramSchmidt +
MeasurableSubspace) → `Subbundle` (Filtration + Measurable + Birkhoff + FK) →
`Limit` (Subbundle + Filtration) → assemble `MultiplicativeErgodic.oseledets_filtration`.
Each new module must be imported (transitively) from `Oseledets.lean`. Keep the build green:
every committed module `lake build`s, with each unfinished obligation an explicitly flagged
`sorry -- TODO:` or `sorry -- BLOCKED:` (notably the M7 measurable‑frame obligations).
