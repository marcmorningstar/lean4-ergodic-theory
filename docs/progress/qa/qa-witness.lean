import Oseledets

/-!
# End-to-end semantic witness for `Oseledets.oseledets_filtration`

We instantiate *every* hypothesis of the multiplicative ergodic theorem with a
concrete one-dimensional system on the one-point space `Unit` with the Dirac
measure, the identity dynamics, and the constant generator `A = 2 • 1`.  This
proves the theorem is **not vacuous** (`qa_nonvacuity`), and from its conclusion
we *extract* the value of the Lyapunov exponent (`qa_semantic_pin`):

* there is exactly one exponent (`k = 1`), and
* its value is `Real.log 2` — the true Lyapunov exponent of the cocycle
  `x ↦ 2·x` whose `n`-step growth is `2ⁿ`.

The extraction shows the formal statement *forces* the genuine exponent: no
degenerate reading of the conclusion can dodge it.
-/

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace QAWitness

/-! ## The concrete system -/

/-- The constant generator: `2 • 1` on `Matrix (Fin 1) (Fin 1) ℝ`. -/
noncomputable def Agen : Unit → Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ => (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)

/-- `id` is ergodic for the Dirac measure on `Unit`: it is trivially measure
preserving, and every set is a.e.-constant because `ae (dirac ()) = pure ()`
on the one-point (subsingleton) space. -/
theorem hErg : Ergodic (id : Unit → Unit) (Measure.dirac ()) := by
  refine ⟨MeasurePreserving.id _, ?_⟩
  exact ⟨fun s _ _ => EventuallyConst.of_subsingleton_left⟩

/-- `det (A x) = 2 ≠ 0`. -/
theorem hdet : ∀ x, (Agen x).det ≠ 0 := by
  intro x; unfold Agen; rw [Matrix.det_smul]; simp

/-- `A` is measurable (constant). -/
theorem hmeas : Measurable Agen := measurable_const

/-- `log⁺‖A‖ ∈ L¹`: the integrand is constant on a probability space. -/
theorem hint : Oseledets.IntegrableLogNorm Agen (Measure.dirac ()) := by
  unfold Oseledets.IntegrableLogNorm Agen; exact integrable_const _

/-- `log⁺‖A⁻¹‖ ∈ L¹`: the integrand is constant on a probability space. -/
theorem hint' : Oseledets.IntegrableLogNorm (fun x => (Agen x)⁻¹) (Measure.dirac ()) := by
  unfold Oseledets.IntegrableLogNorm Agen; exact integrable_const _

/-! ## Nonvacuity: the hypotheses are jointly satisfiable -/

/-- **Nonvacuity.** The Oseledets theorem applies to the concrete one-point
system, so its hypothesis set is satisfiable: the theorem is not vacuous. -/
theorem qa_nonvacuity :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) → Unit → Submodule ℝ (EuclideanSpace ℝ (Fin 1))),
      StrictAnti lam ∧
      (∀ i, Oseledets.MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂(Measure.dirac ()),
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (Agen x)).toLinearMap (V i x) =
            V i (id x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin 1))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Oseledets.cocycle Agen id n x) v‖)
              atTop (𝓝 (lam i))) :=
  Oseledets.oseledets_filtration hErg Agen hdet hmeas hint hint'

/-! ## Cocycle computation -/

/-- The `n`-step cocycle of the constant generator is `2ⁿ • 1`. -/
theorem cocycle_eq (n : ℕ) :
    Oseledets.cocycle Agen id n () = (2:ℝ)^n • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  induction n with
  | zero => simp [Oseledets.cocycle]
  | succ n ih =>
    rw [Oseledets.cocycle_succ]
    simp only [id_eq] at ih ⊢
    rw [ih]
    unfold Agen
    rw [smul_mul_smul_comm, one_mul, pow_succ]

/-- The matrix `c • 1` acts on `EuclideanSpace ℝ (Fin 1)` as scalar multiplication. -/
theorem toEuclideanCLM_smul_one (c : ℝ) (v : EuclideanSpace ℝ (Fin 1)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (c • (1 : Matrix (Fin 1) (Fin 1) ℝ))) v = c • v := by
  rw [map_smul, map_one]; rfl

/-! ## The growth limit equals `log 2` -/

/-- For any nonzero vector `v`, the growth sequence converges to `log 2`. This is
the heart of the semantic pin: whatever vector the theorem hands us in the
stratum, its growth rate is exactly `log 2`. Concretely the sequence equals
`log 2 + (log‖v‖)·(1/n)` for `n ≥ 1`, and the second term vanishes. -/
theorem growth_tendsto_log2 (v : EuclideanSpace ℝ (Fin 1)) (hv : v ≠ 0) :
    Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Oseledets.cocycle Agen id n ()) v‖)
      atTop (𝓝 (Real.log 2)) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- comparison sequence: log 2 + (log‖v‖) * (1/n), which tends to log 2 + 0.
  have hcomp : Tendsto (fun n : ℕ => Real.log 2 + Real.log ‖v‖ * (n : ℝ)⁻¹)
      atTop (𝓝 (Real.log 2)) := by
    have : Tendsto (fun n : ℕ => Real.log 2 + Real.log ‖v‖ * (n : ℝ)⁻¹)
        atTop (𝓝 (Real.log 2 + Real.log ‖v‖ * 0)) := by
      refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
      exact tendsto_inv_atTop_nhds_zero_nat
    simpa using this
  refine hcomp.congr' ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := hn
    positivity
  rw [cocycle_eq, toEuclideanCLM_smul_one, norm_smul]
  have h2n : ‖(2:ℝ)^n‖ = (2:ℝ)^n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h2n, Real.log_mul (by positivity) (ne_of_gt hvpos), Real.log_pow]
  field_simp

/-! ## Dimension bookkeeping -/

theorem finrank_top_one :
    Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 1))) = 1 := by
  rw [finrank_top]; simp

theorem finrank_bot_zero :
    Module.finrank ℝ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 1))) = 0 := by simp

/-! ## Semantic pin: the exponent is forced to be `log 2` -/

/-- **Semantic pin.** From the Oseledets conclusion for the concrete system we
extract its content: there is exactly one Lyapunov exponent (`k = 1`) and it is
`Real.log 2`. No degenerate reading of the conclusion can avoid this: the formal
statement *forces* the genuine Lyapunov exponent of the cocycle. -/
theorem qa_semantic_pin :
    ∃ (lam : Fin 1 → ℝ),
      (∃ (k : ℕ) (lam' : Fin k → ℝ)
        (V : Fin (k + 1) → Unit → Submodule ℝ (EuclideanSpace ℝ (Fin 1))),
        StrictAnti lam' ∧
        (∀ i, Oseledets.MeasurableSubspace fun x => V i x) ∧
        (∀ᵐ x ∂(Measure.dirac ()),
          V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
          (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
          (∀ i : Fin (k + 1),
            Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (Agen x)).toLinearMap (V i x) =
              V i (id x)) ∧
          (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin 1))),
              v ∉ V i.succ x →
              Tendsto
                (fun n : ℕ => (n : ℝ)⁻¹ *
                  Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (Oseledets.cocycle Agen id n x) v‖)
                atTop (𝓝 (lam' i)))) ∧
        k = 1 ∧ HEq lam' lam) ∧
      lam 0 = Real.log 2 := by
  obtain ⟨k, lam, V, hAnti, hMeas, hae⟩ := qa_nonvacuity
  -- pull the a.e. conjunction down to the single point `()`
  rw [ae_dirac_eq] at hae
  obtain ⟨hV0, hVlast, hdrop, _hequiv, hgrowth⟩ := hae
  -- the unit basis vector lives in `⊤` and is nonzero
  set v0 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℝ) with hv0def
  have hv0ne : v0 ≠ 0 := by rw [hv0def]; simp
  -- `k = 1`: a strict flag from `⊤` (rank 1) to `⊥` (rank 0) has exactly one step.
  have hk1 : k = 1 := by
    -- k ≠ 0
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      subst hk0
      rw [show (Fin.last 0) = (0 : Fin 1) from rfl, hV0] at hVlast
      have : Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 1))) =
             Module.finrank ℝ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 1))) := by rw [hVlast]
      rw [finrank_top_one, finrank_bot_zero] at this
      exact absurd this (by norm_num)
    -- k ≤ 1
    have hkle : k ≤ 1 := by
      by_contra hgt
      have hk2 : 2 ≤ k := by omega
      -- first drop: finrank (V 1) < finrank (V 0) = 1, so finrank (V 1) = 0
      have hi0 : (⟨0, by omega⟩ : Fin k).castSucc = (0 : Fin (k + 1)) := rfl
      have hdrop0 := hdrop ⟨0, by omega⟩
      rw [hi0, hV0] at hdrop0
      have hr1 : Module.finrank ℝ (V (⟨0, by omega⟩ : Fin k).succ ()) <
          Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 1))) :=
        Submodule.finrank_lt_finrank_of_lt hdrop0
      rw [finrank_top_one] at hr1
      have hr1' : Module.finrank ℝ (V (⟨0, by omega⟩ : Fin k).succ ()) = 0 := by omega
      -- second drop: finrank (V 2) < finrank (V 1) = 0, impossible
      have hbridge : (⟨0, by omega⟩ : Fin k).succ = (⟨1, by omega⟩ : Fin k).castSucc := by
        ext; simp [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]
      have hdrop1 := hdrop ⟨1, by omega⟩
      rw [← hbridge] at hdrop1
      have hr2 : Module.finrank ℝ (V (⟨1, by omega⟩ : Fin k).succ ()) <
          Module.finrank ℝ (V (⟨0, by omega⟩ : Fin k).succ ()) :=
        Submodule.finrank_lt_finrank_of_lt hdrop1
      rw [hr1'] at hr2
      exact absurd hr2 (by omega)
    omega
  -- with `k = 1`, extract the unique exponent and compute it
  subst hk1
  -- `lam : Fin 1 → ℝ`; show `lam 0 = log 2`
  refine ⟨lam, ⟨1, lam, V, hAnti, hMeas, ?_, rfl, HEq.rfl⟩, ?_⟩
  · -- repackage the a.e. statement (trivially true at the dirac point)
    rw [ae_dirac_eq]
    exact ⟨hV0, hVlast, hdrop, _hequiv, hgrowth⟩
  · -- v0 ∈ V 0 () = ⊤ but v0 ∉ V 1 () = ⊥
    have hv0mem : v0 ∈ (V (0 : Fin 1).castSucc () : Set (EuclideanSpace ℝ (Fin 1))) := by
      rw [show ((0 : Fin 1).castSucc) = (0 : Fin (1 + 1)) from rfl, hV0]
      exact Submodule.mem_top
    have hv0notmem : v0 ∉ V (0 : Fin 1).succ () := by
      rw [show ((0 : Fin 1).succ) = (Fin.last 1) from rfl, hVlast]
      simpa using hv0ne
    have hlim1 := hgrowth (0 : Fin 1) v0 hv0mem hv0notmem
    have hlim2 := growth_tendsto_log2 v0 hv0ne
    exact tendsto_nhds_unique hlim1 hlim2

/-! ## Axiom audit of the witness -/

#print axioms qa_nonvacuity
#print axioms qa_semantic_pin

end QAWitness
