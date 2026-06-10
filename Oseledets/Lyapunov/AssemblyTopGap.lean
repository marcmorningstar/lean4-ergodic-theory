import Oseledets.MultiplicativeErgodic
import Oseledets.Lyapunov.AssemblyFromUpperIdent
import Oseledets.Lyapunov.CapstoneWiring
import Oseledets.Lyapunov.BridgeWiring
import Oseledets.Lyapunov.ForwardGradedOverlapTopGap
import Oseledets.Lyapunov.LimitEigenbasis
import Oseledets.Lyapunov.SpectralIdentification
import Oseledets.Lyapunov.SpectrumResiduals
import Oseledets.Lyapunov.RuelleReverse

/-!
# Final assembly of the Oseledets filtration theorem from the top-gap envelope

This module proves `Oseledets.oseledets_filtration_of_topgap`: the verbatim statement of
`oseledets_filtration` (from `Oseledets/MultiplicativeErgodic.lean`) with exactly one added
hypothesis — the **sound** top-gap fast-band-mass envelope `TopGapMassEnvelope` (quantified over
`lam0`), consumed through `forward_graded_overlap'`.

It supersedes `oseledets_filtration_of_chain` (whose arbitrary-cut chain envelope was refuted —
see `Oseledets/Lyapunov/ChainRecursion.lean`); the body is identical except that step (6) feeds
`forward_graded_overlap'` with the top-gap envelope instead of `forward_graded_overlap` with the
chain envelope.  Once `TopGapMassEnvelope` is discharged unconditionally, this theorem closes the
`sorry` in `MultiplicativeErgodic.lean` together with `oseledets_filtration_dim_zero`.
-/

open MeasureTheory Filter Topology Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

namespace Oseledets

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {d : ℕ} [NeZero d]

/-- **Oseledets filtration theorem from the top-gap envelope.**

The verbatim statement of `oseledets_filtration`, with the single added hypothesis `htopgap` —
the sound top-gap fast-band-mass envelope (the `htopgap` slot of `forward_graded_overlap'`),
quantified over the deterministic singular-exponent data `lam0`.  All other content is composed
from committed assets. -/
theorem oseledets_filtration_of_topgap
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (htopgap : ∀ lam0 : ℕ → ℝ,
      (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Filter.Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
        Filter.atTop (𝓝 (lam0 i))) →
      ∀ᵐ x ∂μ, TopGapMassEnvelope A T lam0 x) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (V i x) = V i (T x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
              atTop (𝓝 (lam i))) := by
  classical
    have hTmeas : Measurable T := hT.toMeasurePreserving.measurable
    -- (3) deterministic singular-value exponents.
    obtain ⟨lam0, _hmono, hlam0⟩ :=
      exists_lam_tendsto_singularValue hT hA hAmeas hint hint'
    -- (4) the limit eigenbasis and its eigenpair / slow-orthogonality data.
    set b' : X → OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
      fun x => limitEigenbasis A T x with hb'def
    have hb' : ∀ᵐ x ∂μ, ∀ e : Fin d,
        Matrix.toEuclideanLin (lambdaHat A T x) (b' x e)
          = Real.exp (lamSing A T x (e : ℕ)) • b' x e :=
      limitEigenbasis_eigenpair_exp hT hA hAmeas hint hint'
    have hslowperp : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, ∀ e : Fin d,
        t < lam0 (e : ℕ) → inner ℝ (b' x e) v = 0 :=
      inner_limitEigenbasis_eq_zero_of_slow hT hA hAmeas hint hint' lam0 hlam0
    -- (5) the spectral-identification band-projector datum.
    have hident : ∀ᵐ x ∂μ, ∀ c : ℝ, 0 < c →
        (∀ i : Fin d, Real.exp (lamSing A T x (i : ℕ)) ≠ c) →
        Filter.Tendsto (fun n : ℕ => bandProjector A T (Set.indicator (Set.Ioi c) 1) n x)
          Filter.atTop (𝓝 (cfc (Set.indicator (Set.Ioi c) (1 : ℝ → ℝ)) (lambdaHat A T x))) :=
      ae_tendsto_bandProjector_cfc_indicator hT hA hAmeas hint hint'
    -- (6) the forward graded overlap bound (consuming the TOP-GAP envelope).
    have hfwdN := forward_graded_overlap' hT hA hAmeas hint hint' lam0 hlam0 b' hb' hident
      (htopgap lam0 hlam0)
    -- the reverse cofactor bound (Ruelle step 3).
    have hrev : ∀ (S : Matrix (Fin d) (Fin d) ℝ), S * Sᵀ = 1 →
        ∀ (g : Fin d → ℝ) (c : ℝ), 1 ≤ c →
        (∀ a b : Fin d, |S a b| ≤ c * Real.exp (-(max (g b - g a) 0))) →
        ∀ i j : Fin d, |S i j| ≤ (d - 1).factorial * c ^ (d - 1) * Real.exp (-(g i - g j)) :=
      fun S hS g c hc hf => Ruelle13.entry_reverse_bound_of_orthogonal S hS g c hc hf
    -- (7) the band-limit bridge.
    have hbridge := hbridge_of_forward_graded (A := A) lam0 hlam0 b' hslowperp hfwdN hrev
    -- the grading `g x e := lam0 e`.
    set g : X → Fin d → ℝ := fun _ e => lam0 (e : ℕ) with hgdef
    -- (8) the TRIVIAL forward graded-overlap discharge for the capstone (NO analytic content):
    -- pick `c := exp M` with `M` the finite max of `lam0 e - lam0 a` over pairs (and `≥ 0`);
    -- then `c · exp(-(max (g e - g a) 0)) ≥ exp 0 = 1 ≥ |⟪b' e, u_a(n)⟫|`.
    have hfwd : ∀ᵐ x ∂μ, ∀ t : ℝ, ∀ v ∈ Vslow A T (Real.exp t) x, v ≠ 0 →
        ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ n : ℕ in atTop,
          ∀ a e : Fin d, |(inner ℝ (b' x e)
              (sortedGramEigenbasis A T n x ⟨a, lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩) : ℝ)|
            ≤ c * Real.exp (-(max (g x e - g x a) 0)) := by
      refine Filter.Eventually.of_forall (fun x t v _ _ => ?_)
      -- `M`: the finite max of `lam0 e - lam0 a` over pairs, clamped at `0`.
      set M : ℝ := (Finset.univ.sup' ⟨(default, default), Finset.mem_univ _⟩
        (fun p : Fin d × Fin d => lam0 (p.1 : ℕ) - lam0 (p.2 : ℕ))) ⊔ 0 with hMdef
      have hMnn : (0 : ℝ) ≤ M := le_sup_right
      have hMpair : ∀ a e : Fin d, lam0 (e : ℕ) - lam0 (a : ℕ) ≤ M := by
        intro a e
        refine le_trans ?_ le_sup_left
        exact Finset.le_sup' (fun p : Fin d × Fin d => lam0 (p.1 : ℕ) - lam0 (p.2 : ℕ))
          (Finset.mem_univ (e, a))
      refine ⟨Real.exp M, Real.one_le_exp hMnn, Filter.Eventually.of_forall (fun n a e => ?_)⟩
      -- `|⟪·,·⟫| ≤ 1 ≤ exp M · exp(-(max (g e - g a) 0))`.
      have hCS : |(inner ℝ (b' x e)
          (sortedGramEigenbasis A T n x ⟨a, lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩) : ℝ)|
          ≤ 1 := by
        have hb1 : ‖b' x e‖ = 1 := (b' x).orthonormal.1 e
        have hb2 : ‖sortedGramEigenbasis A T n x
            ⟨a, lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩‖ = 1 :=
          (sortedGramEigenbasis A T n x).orthonormal.1 _
        have hcs := abs_real_inner_le_norm (b' x e)
          (sortedGramEigenbasis A T n x ⟨a, lt_of_lt_of_eq a.2 (Fintype.card_fin d).symm⟩)
        rwa [hb1, hb2, mul_one] at hcs
      refine hCS.trans ?_
      -- `1 ≤ exp M · exp(-(max (g e - g a) 0)) = exp (M - max (g e - g a) 0)`.
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hmle : max (g x e - g x a) 0 ≤ M := by
        rw [hgdef]
        exact max_le (hMpair a e) hMnn
      linarith
    -- (9) the capstone: per-vector spectral upper bound on the limit slow space.
    have hupper := limsup_le_of_mem_Vslow hT hTmeas hA hAmeas hint hint' hrev
      lam0 hlam0 b' g hfwd hbridge
    -- residuals for the composer.
    have hslowrev : ∀ᵐ x ∂μ, ∀ t : ℝ, lambdaSublevel A T x t ≤ Vslow A T (Real.exp t) x :=
      ae_lambdaSublevel_le_Vslow hT hA hAmeas hint hint'
    have hslowflag : ∀ᵐ x ∂μ, ∀ t : ℝ, Vslow A T (Real.exp t) x = lambdaSublevel A T x t :=
      hslowflag_of_upper hT hA hAmeas hint hint' hupper hslowrev
    have hub_spec : ∀ lam0' : ℕ → ℝ,
        (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
          atTop (𝓝 (lam0' i))) →
        ∀ᵐ x ∂μ, spectrum A T x ⊆ distinctExp lam0' d :=
      fun lam0' hlam0' => hub_spec_of_slowflag hT hA hAmeas hint hint' hslowflag lam0' hlam0'
    have hlb_spec : ∀ lam0' : ℕ → ℝ,
        (∀ i : ℕ, i < d → ∀ᵐ x ∂μ, Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ((Matrix.toEuclideanLin (cocycle A T n x)).singularValues i))
          atTop (𝓝 (lam0' i))) →
        ∀ᵐ x ∂μ, distinctExp lam0' d ⊆ spectrum A T x :=
      fun lam0' hlam0' => hlb_spec_of_slowflag hT hA hAmeas hint hint' hslowflag lam0' hlam0'
    -- (10) compose the headline theorem.
    exact oseledets_filtration_of_upper' hT hTmeas hA hAmeas hint hint' hupper hslowrev
      hub_spec hlb_spec hident

/-! ## Axiom audit -/

#print axioms oseledets_filtration_of_topgap

end Oseledets
