/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Examples.CatMapCover
import ErgodicTheory.Examples.CatMapEigenShadow

/-!
# Telescoping: same-orbit closeness forces eigencoordinate decay

Working on the plain sup-metric universal cover `Fin 2 → ℝ` of the cat-map torus `T2` (see
`ErgodicTheory.Examples.CatMapCover`), this module turns a **finite orbit-closeness** hypothesis
into a **quantitative eigencoordinate bound** on the difference of two toral points.

If two points `x, y : T2` stay within `1/5` (in the sup metric) along the first `n` steps of the cat
map `catTorus`, then the nearest-integer lifts `e_k` of the differences
`catTorus^[k] x − catTorus^[k] y` are rigidly linked: `e_k = catℝ^k ·ᵥ e_0` for all `k < n`.  The
rigidity comes from the covering geometry — the discrepancy `catℝ ·ᵥ e_k − e_{k+1}` projects to `0`,
hence is an integer vector, yet has sup norm `< 1`, so it vanishes.  Telescoping through the
eigenbasis multiplicativity `eigCoordU (catℝ ·ᵥ v) = λ · eigCoordU v` (and the stable analogue with
`μ`) then squeezes the unstable coordinate of `e_0` by the expanding eigenvalue `λ^(n-1)`, i.e. by
`μ^(n-1) → 0`, while the stable coordinate is bounded outright.

## Main results

* `ErgodicTheory.CatMapToral.lift_telescope` — the rigidity `e_k = catℝ^k ·ᵥ e_0`.
* `ErgodicTheory.CatMapToral.eigCoord_bound_of_telescope` — `|eigCoordU (e 0)| ≤ (3/10)·μ^(n-1)` and
  `|eigCoordS (e 0)| ≤ 3/10`.
* `ErgodicTheory.CatMapToral.exists_lift_family_of_orbit_close` — orbit closeness produces such a
  lift family.
* `ErgodicTheory.CatMapToral.exists_lift_slab_of_orbit_close` — the packaged export: an atom pair
  `1/5`-close for `n` steps yields a lift `e₀` of `x − y` in the eigencoordinate slab.
-/

open Matrix

noncomputable section

namespace ErgodicTheory.CatMapToral

/-! ## Micro-lemmas: explicit action, norm bound, eigencoordinate multiplicativity -/

/-- Crude sup-norm bound on the real cat-map action: `‖catℝ ·ᵥ v‖ ≤ 3 · ‖v‖`. -/
lemma norm_catℝ_mulVec_le (v : Fin 2 → ℝ) : ‖catℝ *ᵥ v‖ ≤ 3 * ‖v‖ := by
  rw [catℝ_mulVec_apply, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have h0 : |v 0| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v 1
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs,
      Fin.zero_eta, Fin.mk_one] <;>
    (rw [abs_le]; constructor <;> nlinarith [abs_le.mp h0, abs_le.mp h1, norm_nonneg v])

/-- Unstable eigencoordinate multiplies by `λ` under the cat-map action. -/
lemma eigCoordU_catℝ_mulVec (v : Fin 2 → ℝ) : eigCoordU (catℝ *ᵥ v) = lam * eigCoordU v := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := sqrt5_sq
  have hne : Real.sqrt 5 ≠ 0 := by positivity
  rw [catℝ_mulVec_apply]
  unfold eigCoordU lam mu
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring_nf
  linear_combination (- v 0) * h5

/-- Stable eigencoordinate multiplies by `μ` under the cat-map action. -/
lemma eigCoordS_catℝ_mulVec (v : Fin 2 → ℝ) : eigCoordS (catℝ *ᵥ v) = mu * eigCoordS v := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := sqrt5_sq
  have hne : Real.sqrt 5 ≠ 0 := by positivity
  rw [catℝ_mulVec_apply]
  unfold eigCoordS lam mu
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring_nf
  linear_combination (v 0) * h5

/-- Iterated unstable multiplicativity: `eigCoordU (catℝ^k ·ᵥ v) = λ^k · eigCoordU v`. -/
lemma eigCoordU_catℝ_pow_mulVec (k : ℕ) (v : Fin 2 → ℝ) :
    eigCoordU ((catℝ ^ k) *ᵥ v) = lam ^ k * eigCoordU v := by
  induction k with
  | zero => simp [Matrix.one_mulVec]
  | succ m ih => rw [pow_succ', ← mulVec_mulVec, eigCoordU_catℝ_mulVec, ih, ← mul_assoc,
      ← pow_succ']

/-- Iterated stable multiplicativity: `eigCoordS (catℝ^k ·ᵥ v) = μ^k · eigCoordS v`. -/
lemma eigCoordS_catℝ_pow_mulVec (k : ℕ) (v : Fin 2 → ℝ) :
    eigCoordS ((catℝ ^ k) *ᵥ v) = mu ^ k * eigCoordS v := by
  induction k with
  | zero => simp [Matrix.one_mulVec]
  | succ m ih => rw [pow_succ', ← mulVec_mulVec, eigCoordS_catℝ_mulVec, ih, ← mul_assoc,
      ← pow_succ']

/-! ## Integer-vector rigidity: small null lifts vanish -/

/-- A real vector projecting to `0` on the torus with sup norm `< 1` is itself `0`: each coordinate
is an integer of absolute value `< 1`, hence zero. -/
theorem eq_zero_of_catProj_eq_zero_of_norm_lt_one (d : Fin 2 → ℝ)
    (hp : catProj d = 0) (hlt : ‖d‖ < 1) : d = 0 := by
  funext i
  have hi : ((d i : ℝ) : UnitAddCircle) = 0 := by
    have := congrFun hp i; simpa [catProj] using this
  rw [AddCircle.coe_eq_zero_iff] at hi
  obtain ⟨z, hz⟩ := hi
  rw [zsmul_eq_mul, mul_one] at hz
  have hb : |d i| ≤ ‖d‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d i
  have hzr : |(z : ℝ)| < 1 := by rw [hz]; linarith
  have hz0 : z = 0 := by
    have hz1 : |z| < 1 := by exact_mod_cast hzr
    rw [abs_lt] at hz1; omega
  rw [Pi.zero_apply, ← hz, hz0, Int.cast_zero]

/-! ## The telescoping rigidity -/

/-- **Telescoping rigidity.**  Given a lift family `e` with `catProj (e k)` the `k`-th orbit
difference and `‖e k‖ ≤ 1/5` for `k < n`, every lift is the matrix power of the first:
`e k = catℝ^k ·ᵥ e 0`.  Each step's discrepancy `catℝ ·ᵥ e m − e (m+1)` projects to `0` and has sup
norm `≤ 3·(1/5) + 1/5 < 1`, so it vanishes. -/
theorem lift_telescope (x y : T2) (n : ℕ) (e : ℕ → (Fin 2 → ℝ))
    (he : ∀ k < n, catProj (e k) = catTorus^[k] x - catTorus^[k] y ∧ ‖e k‖ ≤ 1 / 5) :
    ∀ k < n, e k = (catℝ ^ k) *ᵥ e 0 := by
  intro k
  induction k with
  | zero => intro _; simp [Matrix.one_mulVec]
  | succ m ih =>
    intro hk
    have hm : m < n := by omega
    have ihm : e m = (catℝ ^ m) *ᵥ e 0 := ih hm
    have hsub : catTorus (catTorus^[m] x - catTorus^[m] y)
        = catTorus^[m + 1] x - catTorus^[m + 1] y := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← catTorusHom_apply,
        map_sub, catTorusHom_apply, catTorusHom_apply]
    have hstep : catProj (catℝ *ᵥ e m) = catProj (e (m + 1)) := by
      rw [catProj_mulVec, (he m hm).1, hsub, ← (he (m + 1) hk).1]
    have hd0 : catProj (catℝ *ᵥ e m - e (m + 1)) = 0 := by
      rw [catProj_sub, hstep, sub_self]
    have hnb : ‖catℝ *ᵥ e m - e (m + 1)‖ < 1 := by
      have h1 : ‖catℝ *ᵥ e m‖ ≤ 3 * ‖e m‖ := norm_catℝ_mulVec_le (e m)
      have h4 : ‖catℝ *ᵥ e m - e (m + 1)‖ ≤ ‖catℝ *ᵥ e m‖ + ‖e (m + 1)‖ := norm_sub_le _ _
      have h2 := (he m hm).2
      have h3 := (he (m + 1) hk).2
      linarith
    have hd : catℝ *ᵥ e m - e (m + 1) = 0 :=
      eq_zero_of_catProj_eq_zero_of_norm_lt_one _ hd0 hnb
    have he1 : e (m + 1) = catℝ *ᵥ e m := (sub_eq_zero.mp hd).symm
    rw [he1, ihm, mulVec_mulVec, pow_succ']

/-! ## The eigencoordinate slab bound -/

/-- **Eigencoordinate decay from telescoping.**  Under the lift-family hypotheses (`n ≥ 1`), the
unstable coordinate of `e 0` is squeezed by `μ^(n-1)` and the stable coordinate is bounded outright:
`|eigCoordU (e 0)| ≤ (3/10)·μ^(n-1)` and `|eigCoordS (e 0)| ≤ 3/10`. -/
theorem eigCoord_bound_of_telescope (x y : T2) (n : ℕ) (hn : 1 ≤ n) (e : ℕ → (Fin 2 → ℝ))
    (he : ∀ k < n, catProj (e k) = catTorus^[k] x - catTorus^[k] y ∧ ‖e k‖ ≤ 1 / 5) :
    |eigCoordU (e 0)| ≤ 3 / 10 * mu ^ (n - 1) ∧ |eigCoordS (e 0)| ≤ 3 / 10 := by
  have h0 : (0 : ℕ) < n := hn
  have hnm : n - 1 < n := by omega
  have hlam_pos : (0 : ℝ) < lam := by linarith [one_lt_lam]
  have hLpos : (0 : ℝ) < lam ^ (n - 1) := pow_pos hlam_pos _
  have hmuinv : mu = lam⁻¹ := (inv_eq_of_mul_eq_one_right lam_mul_mu).symm
  have hinv : (lam ^ (n - 1))⁻¹ = mu ^ (n - 1) := by rw [hmuinv, inv_pow]
  refine ⟨?_, ?_⟩
  · have hlift : e (n - 1) = (catℝ ^ (n - 1)) *ᵥ e 0 := lift_telescope x y n e he _ hnm
    have hmul : eigCoordU (e (n - 1)) = lam ^ (n - 1) * eigCoordU (e 0) := by
      rw [hlift, eigCoordU_catℝ_pow_mulVec]
    have hb : |eigCoordU (e (n - 1))| ≤ 3 / 10 := by
      have hbound : |eigCoordU (e (n - 1))| ≤ Ccoord * ‖e (n - 1)‖ := abs_eigCoordU_le _
      have hnorm := (he (n - 1) hnm).2
      rw [show Ccoord = 3 / 2 from rfl] at hbound
      nlinarith [norm_nonneg (e (n - 1)), hbound, hnorm]
    rw [hmul, abs_mul, abs_of_pos hLpos] at hb
    rw [← hinv, ← div_eq_mul_inv, le_div_iff₀ hLpos, mul_comm]
    exact hb
  · have := abs_eigCoordS_le (e 0)
    have hnorm := (he 0 h0).2
    rw [show Ccoord = 3 / 2 from rfl] at this
    nlinarith [norm_nonneg (e 0), this, hnorm]

/-! ## Existence of the lift family and the packaged slab export -/

/-- **Orbit closeness yields a lift family.**  If `x, y` stay `1/5`-close for `n` steps, choose the
nearest-integer lift of each orbit difference (via `exists_lift_norm_eq`); its norm equals the toral
distance, hence `≤ 1/5`. -/
theorem exists_lift_family_of_orbit_close (x y : T2) (n : ℕ)
    (hclose : ∀ k < n, dist (catTorus^[k] x) (catTorus^[k] y) ≤ 1 / 5) :
    ∃ e : ℕ → (Fin 2 → ℝ), ∀ k < n,
      catProj (e k) = catTorus^[k] x - catTorus^[k] y ∧ ‖e k‖ ≤ 1 / 5 := by
  choose e he using fun k : ℕ => exists_lift_norm_eq (catTorus^[k] x) (catTorus^[k] y)
  refine ⟨e, fun k hk => ⟨(he k).1, ?_⟩⟩
  rw [(he k).2]; exact hclose k hk

/-- **Packaged slab export** (the interface consumed by the wall lemma).  An atom pair `1/5`-close
for `n ≥ 1` steps produces a lift `e₀` of `x − y` lying in the eigencoordinate slab
`|eigCoordU e₀| ≤ (3/10)·μ^(n-1)`, `|eigCoordS e₀| ≤ 3/10`. -/
theorem exists_lift_slab_of_orbit_close (x y : T2) (n : ℕ) (hn : 1 ≤ n)
    (hclose : ∀ k < n, dist (catTorus^[k] x) (catTorus^[k] y) ≤ 1 / 5) :
    ∃ e₀ : Fin 2 → ℝ, catProj e₀ = x - y ∧
      |eigCoordU e₀| ≤ 3 / 10 * mu ^ (n - 1) ∧ |eigCoordS e₀| ≤ 3 / 10 := by
  obtain ⟨e, hfam⟩ := exists_lift_family_of_orbit_close x y n hclose
  obtain ⟨hU, hS⟩ := eigCoord_bound_of_telescope x y n hn e hfam
  refine ⟨e 0, ?_, hU, hS⟩
  have := (hfam 0 hn).1
  simpa only [Function.iterate_zero, id_eq] using this

end ErgodicTheory.CatMapToral

end
