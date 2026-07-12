/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import ErgodicTheory.Continuous.SuspensionFlowMP
import ErgodicTheory.Continuous.SuspensionStandardBorel
import ErgodicTheory.Examples.CatMapSuspensionFlow

/-!
# Correlation decay for the constant-roof cat suspension flow

This module transports a *base* correlation-decay estimate to the **suspension (special) flow**
of a measure-preserving base map `T : X ≃ᵐ X` under the **constant unit roof** `τ ≡ 1`, and
specialises the result to the Arnold cat map `catTorus`.

## The observables

For a base observable `f : X → ℝ` and a fibre profile `ψ : ℝ → ℝ` we form the **fibre-product
observable** on the suspension space,

`fibreProduct T hτ f ψ [x, s] = f (baseIter ⌊s⌋ x) · ψ (Int.fract s)`,

realised as the composition of the *canonical fundamental-domain coordinate*
`suspensionUnitFwd` (from `ErgodicTheory.Continuous.SuspensionStandardBorel`, which is measurable)
with `f` on the base and `ψ` on the height. On the fundamental domain `X × [0, 1)` this is simply
`f x · ψ s`, so — for the constant unit roof, where `suspensionMeasure = suspensionMeasure₀` is the
pushforward of `μ × Leb|_{[0,1)}` — integrals factor by Fubini
(`integral_suspensionMeasure_fibreProduct_eq`).

## The flow action and the decay estimate

The suspension flow acts by `Φ_t [x, s] = [x, s + t]`, hence on a fibre product

`fibreProduct T hτ g χ (Φ_t [x, s]) = g (baseIter ⌊s + t⌋ x) · χ (Int.fract (s + t))`

(`fibreProduct_suspensionFlowMap_mk`). Splitting the height integral over `[0, 1)` at the fractional
boundary of `t`, the floor `⌊s + t⌋` takes only the two values `⌊t⌋` and `⌊t⌋ + 1`, so the inner
base integral is a base correlation at time `⌊t⌋` or `⌊t⌋ + 1`. Feeding a *base* decay hypothesis
`hdecay : |∫ f · (g ∘ Tᵏ) − ∫f ∫g| ≤ C · θᵏ` together with a **centred** base part `∫g = 0`
(the honest obstruction, see below), we obtain

`|∫ (fibreProduct f ψ) · (fibreProduct g χ ∘ Φ_t)| ≤ ‖ψ‖∞ · ‖χ‖∞ · C · θ^⌊t⌋`

(`suspension_fibreProduct_decay`, and `catSuspension_fibreProduct_decay` for `T = catTorus`).

## The fibre-rotation non-mixing obstruction (disclosed)

A constant-roof suspension is **never mixing as a flow**: on the trivial fibre-product `f = g = 1`
the correlation is the *circle-rotation* correlation `∫₀¹ ψ(s) χ(fract (t + s)) ds`, which does not
decay in `t` (e.g. for `ψ = χ = cos (2π·)` it equals `½ cos (2πt)`, of modulus `½` at every integer
time). The height rotation carries no mixing. Decay therefore requires killing the fibre factor's
non-decaying contribution, which is exactly what centring the base part (`∫g = 0`, so `∫G = 0`)
achieves: the estimate above is the full *centred* correlation `∫ F·(G∘Φ_t) − ∫F·∫G`.

## References

* I. P. Cornfeld, S. V. Fomin, Ya. G. Sinai, *Ergodic Theory*, Springer 1982, Ch. 11
  (special/suspension flows; the reduction of flow correlations to base correlations).
-/

open MeasureTheory Set Filter
open scoped ENNReal

/-- The circle carries its Haar probability measure, so `volume` on `𝕋² = UnitAddTorus (Fin 2)` is
the product Haar probability measure used by the Fourier API (matching `CatMapToral` and the base
decay input `catCorr_decay_real₂`).  Local instances do not cross files, so the trio is repeated
here with names unique to this module. -/
noncomputable local instance instMeasureSpaceUnitAddCircle_catSuspensionDecay :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolume_catSuspensionDecay :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolume_catSuspensionDecay :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ErgodicTheory

variable {X : Type*} [MeasurableSpace X] (T : X ≃ᵐ X) {τ : X → ℝ} (hτ : Measurable τ)

/-- `baseIter` at index `0` is the identity on the base. -/
theorem baseIter_zero' (x : X) : baseIter T hτ 0 x = x := by
  rw [baseIter, suspensionAct_zero]

/-! ## The fibre-product observable -/

/-- The **fibre-product observable** `[x, s] ↦ f (baseIter ⌊s⌋ x) · ψ (Int.fract s)` on the
suspension space, built from a base observable `f` and a fibre profile `ψ` through the canonical
fundamental-domain coordinate `suspensionUnitFwd` (constant unit roof `τ ≡ 1`). -/
noncomputable def fibreProduct (f : X → ℝ) (ψ : ℝ → ℝ) (hτ1 : τ = fun _ => (1 : ℝ)) :
    SuspensionSpace T hτ → ℝ :=
  fun q => f (suspensionUnitFwd T hτ hτ1 q).1 * ψ ((suspensionUnitFwd T hτ hτ1 q).2 : ℝ)

/-- The fibre-product observable is measurable (`f`, `ψ` measurable; the fundamental-domain
coordinate is measurable). -/
theorem measurable_fibreProduct (f : X → ℝ) (ψ : ℝ → ℝ) (hτ1 : τ = fun _ => (1 : ℝ))
    (hf : Measurable f) (hψ : Measurable ψ) : Measurable (fibreProduct T hτ f ψ hτ1) := by
  unfold fibreProduct
  have hfwd := measurable_suspensionUnitFwd T hτ hτ1
  exact (hf.comp (measurable_fst.comp hfwd)).mul
    (hψ.comp (measurable_subtype_coe.comp (measurable_snd.comp hfwd)))

/-- Evaluation on a representative: `fibreProduct f ψ [x, s] = f (baseIter ⌊s⌋ x) · ψ (fract s)`. -/
theorem fibreProduct_mk (f : X → ℝ) (ψ : ℝ → ℝ) (hτ1 : τ = fun _ => (1 : ℝ)) (x : X) (s : ℝ) :
    fibreProduct T hτ f ψ hτ1 (suspensionMk T hτ (x, s))
      = f (baseIter T hτ ⌊s⌋ x) * ψ (Int.fract s) := by
  unfold fibreProduct
  rw [suspensionUnitFwd_mk]
  rfl

/-- Pointwise bound `|fibreProduct f ψ q| ≤ Mf · Mψ` from sup-bounds on `f` and `ψ`. -/
theorem abs_fibreProduct_le (f : X → ℝ) (ψ : ℝ → ℝ) (hτ1 : τ = fun _ => (1 : ℝ))
    {Mf Mψ : ℝ} (hMf : ∀ x, |f x| ≤ Mf) (hMψ : ∀ u, |ψ u| ≤ Mψ) (q : SuspensionSpace T hτ) :
    |fibreProduct T hτ f ψ hτ1 q| ≤ Mf * Mψ := by
  unfold fibreProduct
  rw [abs_mul]
  have hMf0 : (0 : ℝ) ≤ Mf :=
    le_trans (abs_nonneg _) (hMf (suspensionUnitFwd T hτ hτ1 q).1)
  exact mul_le_mul (hMf _) (hMψ _) (abs_nonneg _) hMf0

/-- The flow action on a fibre product:
`fibreProduct g χ (Φ_t [x, s]) = g (baseIter ⌊s + t⌋ x) · χ (fract (s + t))`. -/
theorem fibreProduct_suspensionFlowMap_mk (g : X → ℝ) (χ : ℝ → ℝ) (hτ1 : τ = fun _ => (1 : ℝ))
    (t : ℝ) (x : X) (s : ℝ) :
    fibreProduct T hτ g χ hτ1 (suspensionFlowMap T hτ t (suspensionMk T hτ (x, s)))
      = g (baseIter T hτ ⌊s + t⌋ x) * χ (Int.fract (s + t)) := by
  rw [suspensionFlowMap_mk, suspensionTranslate_apply, fibreProduct_mk]

/-! ## The Fubini reduction of a suspension integral -/

section Fubini

variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- For the constant unit roof the normalising constant `∫τ = 1`, so the suspension probability
measure equals the raw pushforward measure `suspensionMeasure₀`. -/
theorem suspensionMeasure_const_one (hτ1 : τ = fun _ => (1 : ℝ)) :
    suspensionMeasure T hτ μ = suspensionMeasure₀ T hτ μ := by
  have hone : (∫ x, τ x ∂μ) = 1 := by
    rw [hτ1, integral_const, measureReal_def, measure_univ]; simp
  rw [suspensionMeasure, hone, ENNReal.ofReal_one, inv_one, one_smul]

/-- **Fubini reduction.** The suspension integral of a bounded measurable observable `F` equals its
iterated integral over the fundamental domain `X × [0, 1)`, with the height integral outermost:
`∫ q, F q ∂μ̂ = ∫ s in [0,1), ∫ x, F [x, s] ∂μ`. -/
theorem integral_suspensionMeasure_fibreProduct_eq (hτ1 : τ = fun _ => (1 : ℝ))
    (F : SuspensionSpace T hτ → ℝ) (hF : Measurable F) {M : ℝ} (hFb : ∀ q, |F q| ≤ M) :
    ∫ q, F q ∂(suspensionMeasure T hτ μ)
      = ∫ s in Set.Ico (0 : ℝ) 1, ∫ x, F (suspensionMk T hτ (x, s)) ∂μ := by
  rw [suspensionMeasure_const_one T hτ μ hτ1, suspensionMeasure₀,
    integral_map (measurable_suspensionMk T hτ).aemeasurable hF.aestronglyMeasurable]
  have hD : suspensionDomain τ = Set.univ ×ˢ Set.Ico (0 : ℝ) 1 := by
    ext p
    simp only [suspensionDomain, mem_setOf_eq, hτ1, Set.mem_prod, Set.mem_univ, Set.mem_Ico,
      true_and]
  rw [hD]
  have hmeq : (μ.prod volume).restrict (Set.univ ×ˢ Set.Ico (0 : ℝ) 1)
      = μ.prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hmeq]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hint : Integrable (fun p : X × ℝ => F (suspensionMk T hτ p))
      (μ.prod (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
    refine (integrable_const M).mono' (hF.comp (measurable_suspensionMk T hτ)).aestronglyMeasurable
      (ae_of_all _ (fun p => ?_))
    simpa [Real.norm_eq_abs] using hFb (suspensionMk T hτ p)
  rw [integral_prod_symm _ hint]

end Fubini

/-! ## The correlation-decay transport -/

section Decay

variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- **Correlation-decay transport to the constant-roof suspension flow.**

Let `f, g : X → ℝ` be bounded measurable base observables with `g` **centred** (`∫g = 0`), and let
`ψ, χ : ℝ → ℝ` be bounded measurable fibre profiles with sup-bounds `Mψ, Mχ`. Suppose the base map
satisfies the correlation-decay estimate
`hdecay : |∫ f·(g∘Tᵏ) − ∫f·∫g| ≤ C · θᵏ` for all `k`, with `0 ≤ θ ≤ 1`. Then for every `t ≥ 0`,
the centred flow correlation of the fibre products obeys

`|∫ (fibreProduct f ψ) · (fibreProduct g χ ∘ Φ_t) dμ̂| ≤ Mψ · Mχ · C · θ^⌊t⌋`.

This is the special-flow correlation reduction (Cornfeld–Fomin–Sinai, Ch. 11); centring `g` removes
the non-decaying fibre-rotation contribution (see the module docstring). -/
theorem suspension_fibreProduct_decay (hτ1 : τ = fun _ => (1 : ℝ))
    (f g : X → ℝ) (ψ χ : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hψ : Measurable ψ) (hχ : Measurable χ)
    {Mf Mg Mψ Mχ C θ : ℝ}
    (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg)
    (hMψ : ∀ u, |ψ u| ≤ Mψ) (hMχ : ∀ u, |χ u| ≤ Mχ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hg0 : (∫ x, g x ∂μ) = 0)
    (hdecay : ∀ k : ℕ,
      |(∫ x, f x * g (baseIter T hτ (k : ℤ) x) ∂μ)
        - (∫ x, f x ∂μ) * (∫ x, g x ∂μ)| ≤ C * θ ^ k)
    (t : ℝ) (ht : 0 ≤ t) :
    |∫ q, fibreProduct T hτ f ψ hτ1 q
        * fibreProduct T hτ g χ hτ1 (suspensionFlowMap T hτ t q)
        ∂(suspensionMeasure T hτ μ)|
      ≤ Mψ * Mχ * C * θ ^ (⌊t⌋.toNat) := by
  -- Nonnegativity of the sup-bounds and of `C`.
  have hMψ0 : (0 : ℝ) ≤ Mψ := le_trans (abs_nonneg _) (hMψ 0)
  have hMχ0 : (0 : ℝ) ≤ Mχ := le_trans (abs_nonneg _) (hMχ 0)
  have hC0 : (0 : ℝ) ≤ C := by
    have h := hdecay 0
    rw [hg0, mul_zero, sub_zero, pow_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  set N : ℕ := ⌊t⌋.toNat with hN
  -- Centred base correlations decay: `|∫ f·(g∘baseIter k)| ≤ C·θᵏ`.
  have hcorr : ∀ k : ℕ, |∫ x, f x * g (baseIter T hτ (k : ℤ) x) ∂μ| ≤ C * θ ^ k := by
    intro k
    have h := hdecay k
    rwa [hg0, mul_zero, sub_zero] at h
  -- The fibre-product product observable, its measurability and sup-bound.
  set F : SuspensionSpace T hτ → ℝ :=
    fun q => fibreProduct T hτ f ψ hτ1 q * fibreProduct T hτ g χ hτ1 (suspensionFlowMap T hτ t q)
    with hF
  have hFmeas : Measurable F :=
    (measurable_fibreProduct T hτ f ψ hτ1 hf hψ).mul
      ((measurable_fibreProduct T hτ g χ hτ1 hg hχ).comp (measurable_suspensionFlowMap T hτ t))
  have hFbd : ∀ q, |F q| ≤ (Mf * Mψ) * (Mg * Mχ) := by
    intro q
    rw [hF]
    dsimp only
    rw [abs_mul]
    exact mul_le_mul (abs_fibreProduct_le T hτ f ψ hτ1 hMf hMψ q)
      (abs_fibreProduct_le T hτ g χ hτ1 hMg hMχ _) (abs_nonneg _)
      (le_trans (abs_nonneg _) (abs_fibreProduct_le T hτ f ψ hτ1 hMf hMψ q))
  -- Fubini reduction to a height integral of an inner base integral.
  rw [integral_suspensionMeasure_fibreProduct_eq T hτ μ hτ1 F hFmeas hFbd]
  -- The inner base integral, for a height `s ∈ [0, 1)`.
  set J : ℝ → ℝ := fun s => ∫ x, F (suspensionMk T hτ (x, s)) ∂μ with hJdef
  -- Bound `|J s| ≤ Mψ·Mχ·C·θ^N` for every `s ∈ [0, 1)`.
  have hJbound : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖J s‖ ≤ Mψ * Mχ * C * θ ^ N := by
    intro s hs
    have hfloor : ⌊s⌋ = 0 := Int.floor_eq_zero_iff.mpr hs
    have hfract : Int.fract s = s := Int.fract_eq_self.mpr ⟨hs.1, hs.2⟩
    -- Rewrite the inner integrand and pull the height-constants out.
    have hJs : J s = ψ s * χ (Int.fract (s + t)) *
        ∫ x, f x * g (baseIter T hτ ⌊s + t⌋ x) ∂μ := by
      rw [hJdef]
      dsimp only
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun x => ?_))
      rw [hF]
      dsimp only
      rw [fibreProduct_mk, fibreProduct_suspensionFlowMap_mk, hfloor, baseIter_zero', hfract]
      ring
    rw [hJs, Real.norm_eq_abs, abs_mul, abs_mul]
    -- Control the inner correlation `∫ f·(g∘baseIter ⌊s+t⌋)` by `C·θ^N`.
    set m : ℤ := ⌊s + t⌋ with hm
    have hmnn : 0 ≤ m := by
      have : (0 : ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by exact_mod_cast ht)
      have hle : ⌊t⌋ ≤ m := Int.floor_le_floor (by linarith [hs.1])
      omega
    have hcast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmnn
    have hNle : N ≤ m.toNat := by
      rw [hN]
      exact Int.toNat_le_toNat (Int.floor_le_floor (by linarith [hs.1]))
    have hcorrm : |∫ x, f x * g (baseIter T hτ m x) ∂μ| ≤ C * θ ^ N := by
      have h := hcorr m.toNat
      rw [hcast] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1 hNle) hC0
    -- Assemble the three sup-bounds.
    have hpow0 : (0 : ℝ) ≤ θ ^ N := pow_nonneg hθ0 N
    calc |ψ s| * |χ (Int.fract (s + t))| * |∫ x, f x * g (baseIter T hτ m x) ∂μ|
        ≤ Mψ * Mχ * (C * θ ^ N) := by
          refine mul_le_mul (mul_le_mul (hMψ s) (hMχ _) (abs_nonneg _) hMψ0) hcorrm
            (abs_nonneg _) (mul_nonneg hMψ0 hMχ0)
      _ = Mψ * Mχ * C * θ ^ N := by ring
  -- Integrate the height bound over `[0, 1)` (a set of measure `1`).
  have hlt : volume (Set.Ico (0 : ℝ) 1) < ∞ := by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top
  have hvol : volume.real (Set.Ico (0 : ℝ) 1) = 1 := by
    rw [measureReal_def, Real.volume_Ico]; simp
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := J) hlt hJbound
  rw [hvol, mul_one] at hbound
  rw [← Real.norm_eq_abs]
  exact hbound

end Decay

end ErgodicTheory

/-! ## Specialisation to the Arnold cat map -/

namespace ErgodicTheory.CatMapToral

open MeasureTheory

/-- **Correlation decay for the cat-map suspension flow.** With bounded measurable base observables
`f, g` on the torus (`g` centred, `∫g = 0`), bounded measurable fibre profiles `ψ, χ`, and a base
correlation-decay hypothesis `hdecay` for the cat map at rate `θ ∈ [0, 1)` (proved separately for
`catTorus`), the centred flow correlation of the fibre-product observables on the constant-roof cat
suspension decays as `θ^⌊t⌋`:

`|∫ (fibreProduct f ψ)·(fibreProduct g χ ∘ Φ_t) dμ̂| ≤ Mψ · Mχ · C · θ^⌊t⌋`.

The base decay is taken as a hypothesis so that this module builds independently of the base-decay
proof; the two compose at assembly time. See the module docstring for the fibre-rotation obstruction
that forces centring. -/
theorem catSuspension_fibreProduct_decay
    (f g : T2 → ℝ) (ψ χ : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hψ : Measurable ψ) (hχ : Measurable χ)
    {Mf Mg Mψ Mχ C θ : ℝ}
    (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg)
    (hMψ : ∀ u, |ψ u| ≤ Mψ) (hMχ : ∀ u, |χ u| ≤ Mχ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hg0 : (∫ x, g x ∂(volume : Measure T2)) = 0)
    (hdecay : ∀ k : ℕ,
      |(∫ x, f x * g (baseIter catTorusEquiv measurable_catRoof (k : ℤ) x) ∂(volume : Measure T2))
        - (∫ x, f x ∂(volume : Measure T2)) * (∫ x, g x ∂(volume : Measure T2))| ≤ C * θ ^ k)
    (t : ℝ) (ht : 0 ≤ t) :
    |∫ q, fibreProduct catTorusEquiv measurable_catRoof f ψ rfl q
        * fibreProduct catTorusEquiv measurable_catRoof g χ rfl
            (suspensionFlowMap catTorusEquiv measurable_catRoof t q)
        ∂(suspensionMeasure catTorusEquiv measurable_catRoof (volume : Measure T2))|
      ≤ Mψ * Mχ * C * θ ^ (⌊t⌋.toNat) :=
  suspension_fibreProduct_decay catTorusEquiv measurable_catRoof (volume : Measure T2) rfl
    f g ψ χ hf hg hψ hχ hMf hMg hMψ hMχ hθ0 hθ1 hg0 hdecay t ht

end ErgodicTheory.CatMapToral
