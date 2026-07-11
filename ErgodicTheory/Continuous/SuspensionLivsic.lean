/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionCoboundary
import ErgodicTheory.Livsic.Defs
import ErgodicTheory.Livsic.FlowCoboundary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Tier-III Livšic theorem for constant-roof suspension flows

This module proves the **cohomological rigidity (Livšic) equivalence at tier III** for the
special (suspension) flow over a measurable base automorphism `T : X ≃ᵐ X` with a *constant*
roof `τ ≡ c`. For a flow observable `F` on the suspension space, being a **flow coboundary** is
equivalent to the vanishing of every periodic Birkhoff sum of the *induced base observable*
`inducedBaseCocycle T hτ F` (the one-lap integral of `F`), provided the base map satisfies the
discrete Livšic converse.

The forward direction is the general obstruction of
`ErgodicTheory.Continuous.SuspensionCoboundary`. The converse is the content here: given a base
transfer function `u₀` cobounding the induced base observable, we build the flow transfer function
explicitly on the fundamental domain (`uCover`), descend it through the suspension quotient
(`suspTransfer`), and verify the continuous-time coboundary equation (`suspTransfer_flow`).

## Seam remark

The transfer function `uCover (x, s) = u₀ x + ∫₀ˢ F [x, σ] dσ` is defined *lap by lap* on
the fundamental strip. Crossing the fundamental-domain seam — the identification
`[T x, s] = [x, s + c]` — is handled **exactly** by the base cohomological equation
`inducedBaseCocycle F x = u₀ (T x) − u₀ x`: the base jump `u₀ (T x) − u₀ x` is precisely the
lap integral `∫₀ᶜ F [x, σ] dσ` that the fibre integral accumulates over one roof height (see
`uCover_gen`). There is **no estimate** and no metric on the suspension space: `IsFlowCoboundary`
is a purely algebraic (regularity-free) notion, so the seam is glued by an identity, not a bound.

## Main results

* `ErgodicTheory.uCover` — the fundamental-domain transfer candidate.
* `ErgodicTheory.uCover_gen` — the generator-descent identity across one seam.
* `ErgodicTheory.uCover_act` — its upgrade to full `ℤ`-invariance under the suspension action.
* `ErgodicTheory.suspTransfer` — the descended transfer function on the quotient.
* `ErgodicTheory.suspTransfer_flow` — the continuous-time coboundary equation.
* `ErgodicTheory.livsic_suspensionFlow_constRoof` — the tier-III equivalence.
* `ErgodicTheory.livsic_suspensionFlow_constRoof_orbitIntegral` — the flow-native
  (closed-orbit-integral) form of the equivalence.

## References

* A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. **6** (1972) 1278–1301.
* J. Laureano, A. Mendes, M. J. Ferreira, *Livschitz Theorem in Suspension Flows and Markov
  Systems*, Symmetry **12**(3):338 (2020).
* A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §19.2.
-/

open MeasureTheory Function

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- The cover-level (fundamental-domain) transfer function candidate:
`uCover (x, s) = u₀ x + ∫₀ˢ F [x, σ] dσ`. -/
noncomputable def uCover (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (p : X × ℝ) : ℝ :=
  u₀ p.1 + ∫ σ in (0 : ℝ)..(p.2), F (suspensionMk T hτ (p.1, σ))

/-- Seam identity: for the constant roof `τ ≡ c`, `[T x, σ] = [x, σ + c]` in the suspension
quotient, since the generator `G (x, σ + c) = (T x, σ)` acts by the orbit relation. -/
theorem suspensionMk_T (c : ℝ) (hconst : τ = fun _ => c) (x : X) (σ : ℝ) :
    suspensionMk T hτ (T x, σ) = suspensionMk T hτ (x, σ + c) := by
  have hgen : suspensionGen T hτ (x, σ + c) = (T x, σ) := by
    rw [suspensionGen_apply, hconst]; simp
  rw [← hgen, ← suspensionAct_one T hτ (x, σ + c), suspensionMk_act' T hτ 1 (x, σ + c)]

/-- **Generator descent across one seam.** For the constant roof `τ ≡ c` and a base transfer
function `u₀` cobounding the induced base observable, the fundamental-domain candidate is
invariant under the suspension generator: `uCover (T x, s − c) = uCover (x, s)`. The base jump
`u₀ (T x) − u₀ x` supplies exactly the one-lap integral `∫₀ᶜ F [x, σ] dσ` that reconciles the
two fibre integrals. -/
theorem uCover_gen (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hu₀ : ∀ x, inducedBaseCocycle T hτ F x = u₀ (T x) - u₀ x)
    (c : ℝ) (hconst : τ = fun _ => c)
    (hint : ∀ x a b,
      IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (x : X) (s : ℝ) :
    uCover T hτ F u₀ (T x, s - c) = uCover T hτ F u₀ (x, s) := by
  simp only [uCover]
  -- rewrite the fibre integrand over the `T x` fibre into the `x` fibre
  have hInt : (∫ σ in (0 : ℝ)..(s - c), F (suspensionMk T hτ (T x, σ)))
      = ∫ σ in (c : ℝ)..s, F (suspensionMk T hτ (x, σ)) := by
    have hshift : (fun σ => F (suspensionMk T hτ (T x, σ)))
        = fun σ => F (suspensionMk T hτ (x, σ + c)) := by
      funext σ; rw [suspensionMk_T T hτ c hconst]
    rw [hshift,
      intervalIntegral.integral_comp_add_right
        (fun σ => F (suspensionMk T hτ (x, σ))) c]
    congr 1 <;> ring
  rw [hInt]
  -- base transfer identity, with `inducedBaseCocycle` unfolded and roof `= c`
  have hu : u₀ (T x) = u₀ x + ∫ σ in (0 : ℝ)..c, F (suspensionMk T hτ (x, σ)) := by
    have hcx : τ x = c := by rw [hconst]
    have hval := hu₀ x
    rw [inducedBaseCocycle, hcx] at hval
    linarith [hval]
  rw [hu]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint x 0 c) (hint x c s)
  have : (∫ σ in (0 : ℝ)..c, F (suspensionMk T hτ (x, σ)))
      + ∫ σ in (c : ℝ)..s, F (suspensionMk T hτ (x, σ))
      = ∫ σ in (0 : ℝ)..s, F (suspensionMk T hτ (x, σ)) := hadd
  linarith [this]

/-- **Full `ℤ`-invariance.** Generator-invariance `hg` upgrades to invariance under the whole
suspension `ℤ`-action `suspensionAct`, by induction on the integer exponent. -/
theorem uCover_act (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hg : ∀ p, uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p)
    (n : ℤ) (q : X × ℝ) :
    uCover T hτ F u₀ (suspensionAct T hτ n q) = uCover T hτ F u₀ q := by
  have hginv : ∀ p,
      uCover T hτ F u₀ ((suspensionGen T hτ).symm p) = uCover T hτ F u₀ p := by
    intro p
    have h := hg ((suspensionGen T hτ).symm p)
    rw [MeasurableEquiv.apply_symm_apply] at h
    exact h.symm
  induction n using Int.induction_on with
  | zero => rw [suspensionAct_zero]
  | succ k ih =>
      rw [show ((k : ℤ) + 1) = 1 + (k : ℤ) from by ring, suspensionAct_add,
        suspensionAct_one, hg, ih]
  | pred k ih =>
      rw [show (-(k : ℤ) - 1) = -1 + -(k : ℤ) from by ring, suspensionAct_add,
        suspensionAct_neg_one, hginv, ih]

/-- **The descended transfer function** on the suspension quotient, obtained from the
fundamental-domain candidate by `Quotient.lift` along the (verified) `ℤ`-invariance. -/
noncomputable def suspTransfer (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hg : ∀ p, uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p) :
    SuspensionSpace T hτ → ℝ :=
  letI := suspensionAddAction T hτ
  Quotient.lift (uCover T hτ F u₀) (fun p q h => by
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n +ᵥ q = p := h
    have hn' : suspensionAct T hτ n q = p := hn
    rw [← hn', uCover_act T hτ F u₀ hg n q])

@[simp] theorem suspTransfer_mk (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hg : ∀ p, uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p)
    (p : X × ℝ) :
    suspTransfer T hτ F u₀ hg (suspensionMk T hτ p) = uCover T hτ F u₀ p := rfl

/-- **The continuous-time coboundary equation** for the descended transfer function:
`suspTransfer (ζ_t q) − suspTransfer q = ∫₀ᵗ F (ζ_r q) dr`. This exhibits `suspTransfer` as a
flow transfer function for `F`. -/
theorem suspTransfer_flow (F : SuspensionSpace T hτ → ℝ) (u₀ : X → ℝ)
    (hg : ∀ p, uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p)
    (hint : ∀ x a b,
      IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (q : SuspensionSpace T hτ) (t : ℝ) :
    suspTransfer T hτ F u₀ hg (suspensionFlowMap T hτ t q)
      - suspTransfer T hτ F u₀ hg q
      = ∫ r in (0 : ℝ)..t, F (suspensionFlowMap T hτ r q) := by
  refine Quotient.inductionOn q (fun p => ?_)
  obtain ⟨x, s⟩ := p
  change suspTransfer T hτ F u₀ hg
        (suspensionFlowMap T hτ t (suspensionMk T hτ (x, s)))
        - suspTransfer T hτ F u₀ hg (suspensionMk T hτ (x, s))
      = ∫ r in (0 : ℝ)..t, F (suspensionFlowMap T hτ r (suspensionMk T hτ (x, s)))
  have hflow : suspensionFlowMap T hτ t (suspensionMk T hτ (x, s))
      = suspensionMk T hτ (x, s + t) := by
    rw [suspensionFlowMap_mk, suspensionTranslate_apply]
  have hrhs : (∫ r in (0 : ℝ)..t,
        F (suspensionFlowMap T hτ r (suspensionMk T hτ (x, s))))
      = ∫ r in (s : ℝ)..(s + t), F (suspensionMk T hτ (x, r)) := by
    have hfun : (fun r => F (suspensionFlowMap T hτ r (suspensionMk T hτ (x, s))))
        = fun r => F (suspensionMk T hτ (x, s + r)) := by
      funext r; rw [suspensionFlowMap_mk, suspensionTranslate_apply]
    rw [hfun,
      intervalIntegral.integral_comp_add_left
        (fun σ => F (suspensionMk T hτ (x, σ))) s]
    simp only [add_zero]
  rw [hflow, suspTransfer_mk, suspTransfer_mk, hrhs]
  dsimp only [uCover]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint x 0 s) (hint x s (s + t))
  linarith [hadd]

/-- **Tier-III Livšic equivalence for constant-roof suspension flows.** For a constant roof
`τ ≡ c` and a base map `T` satisfying the discrete Livšic converse `hbase` for the induced base
observable, a flow observable `F` is a flow coboundary of the suspension flow **iff** every
periodic Birkhoff sum of `inducedBaseCocycle T hτ F` vanishes.

The forward direction is the tier-I obstruction (`inducedBaseCocycle_isCoboundary`). The converse
pulls a base transfer function `u₀` from `hbase`, lifts it seam-by-seam to `suspTransfer`
(`uCover_gen` glues the seam exactly by the base equation), and checks the coboundary equation
(`suspTransfer_flow`). No metric on the suspension space is used: `IsFlowCoboundary` is
regularity-free. -/
theorem livsic_suspensionFlow_constRoof
    (F : SuspensionSpace T hτ → ℝ) (c : ℝ) (hconst : τ = fun _ => c)
    (hint : ∀ x a b,
      IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (hbase : HasVanishingPeriodicSums (⇑T) (inducedBaseCocycle T hτ F) →
             IsCoboundary (⇑T) (inducedBaseCocycle T hτ F)) :
    IsFlowCoboundary (suspensionFlowMap T hτ) F ↔
      HasVanishingPeriodicSums (⇑T) (inducedBaseCocycle T hτ F) := by
  constructor
  · intro h
    exact (inducedBaseCocycle_isCoboundary T hτ F h).hasVanishingPeriodicSums
  · intro hvps
    obtain ⟨u₀, hu₀⟩ := hbase hvps
    have hg : ∀ p,
        uCover T hτ F u₀ (suspensionGen T hτ p) = uCover T hτ F u₀ p := by
      rintro ⟨x, s⟩
      have hcx : τ x = c := congrFun hconst x
      have hgp : suspensionGen T hτ (x, s) = (T x, s - c) := by
        rw [suspensionGen_apply, hcx]
      rw [hgp]
      exact uCover_gen T hτ F u₀ hu₀ c hconst hint x s
    exact ⟨suspTransfer T hτ F u₀ hg,
      fun q t => suspTransfer_flow T hτ F u₀ hg hint q t⟩

/-- **Flow-native tier-III Livšic equivalence for constant-roof suspension flows.** Same
hypotheses as `livsic_suspensionFlow_constRoof`, but with the coboundary obstruction phrased
directly as the vanishing of every *closed-orbit integral* of `F`: a flow observable `F` is a flow
coboundary of the suspension flow **iff** for every base `n`-periodic point `p` the integral of `F`
around the corresponding closed flow orbit (of period `birkhoffSum T τ n p`) vanishes.

This is `livsic_suspensionFlow_constRoof` chained through the lap-decomposition bridge
`suspension_periodicOrbitIntegral_eq_birkhoffSum`, which identifies the closed-orbit flow integral
with the base Birkhoff sum of the induced observable. The universal per-fibre integrability `hint`
supplies the per-lap integrability the bridge requires (the flow integrand
`F (ζ_s [p, 0]) = F [p, s]` is one of its instances). -/
theorem livsic_suspensionFlow_constRoof_orbitIntegral
    (F : SuspensionSpace T hτ → ℝ) (c : ℝ) (hconst : τ = fun _ => c)
    (hint : ∀ x a b,
      IntervalIntegrable (fun s => F (suspensionMk T hτ (x, s))) volume a b)
    (hbase : HasVanishingPeriodicSums (⇑T) (inducedBaseCocycle T hτ F) →
             IsCoboundary (⇑T) (inducedBaseCocycle T hτ F)) :
    IsFlowCoboundary (suspensionFlowMap T hτ) F ↔
      ∀ (n : ℕ) (p : X), (⇑T)^[n] p = p →
        ∫ s in (0 : ℝ)..(birkhoffSum (⇑T) τ n p),
          F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)) = 0 := by
  have hint' : ∀ (p : X) (a b : ℝ),
      IntervalIntegrable
        (fun s => F (suspensionFlowMap T hτ s (suspensionSection' T hτ p))) volume a b := by
    intro p a b
    have hdir : (fun s => F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)))
        = fun s => F (suspensionMk T hτ (p, s)) := by
      funext s
      simp only [suspensionSection', suspensionFlowMap_mk, suspensionTranslate_apply, zero_add]
    rw [hdir]
    exact hint p a b
  have hequiv : HasVanishingPeriodicSums (⇑T) (inducedBaseCocycle T hτ F) ↔
      ∀ (n : ℕ) (p : X), (⇑T)^[n] p = p →
        ∫ s in (0 : ℝ)..(birkhoffSum (⇑T) τ n p),
          F (suspensionFlowMap T hτ s (suspensionSection' T hτ p)) = 0 := by
    constructor
    · intro hvps n p hp
      rw [suspension_periodicOrbitIntegral_eq_birkhoffSum T hτ F p n (fun k _ => hint' p _ _)]
      exact hvps n p hp
    · intro hflow n p hp
      rw [← suspension_periodicOrbitIntegral_eq_birkhoffSum T hτ F p n (fun k _ => hint' p _ _)]
      exact hflow n p hp
  exact (livsic_suspensionFlow_constRoof T hτ F c hconst hint hbase).trans hequiv

end ErgodicTheory
