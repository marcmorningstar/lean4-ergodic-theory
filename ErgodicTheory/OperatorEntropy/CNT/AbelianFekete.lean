import ErgodicTheory.OperatorEntropy.CNT.AbelianCorner

/-!
# The abelian corner: Fekete well-definedness of the CNT entropy rate

On the abelian (diagonal-subalgebra) corner, the per-resolution diagonal collapse
`vonNeumannEntropy_corrMatrix_eq_ksEntropySeq` identifies the von Neumann entropy of the CNT
correlation matrix `corrMatrix (adPerm σ) (densityOfPMF μ) (projPartition c) n` at each resolution
`n` with the classical `n`-fold iterated-join Shannon entropy `ksEntropySeq n` of the underlying
measure-preserving system `(⇑σ, probMeasure μ)`. Transporting the classical Kolmogorov–Sinai theory
along this identity records two facts about the quantum entropy sequence that are, in general,
delicate for CNT dynamical entropy:

* `subadditive_vonNeumannEntropy_corrMatrix_abelian`: the sequence
  `n ↦ vonNeumannEntropy (corrMatrix … n)` is **`Subadditive`** (`u (m + n) ≤ u m + u n`). This
  is the classical Fekete inequality `ksEntropySeq_subadditive` pulled back through the collapse.
* `tendsto_cntEntropyPartition_abelian`: consequently the averaged sequence
  `n ↦ vonNeumannEntropy (corrMatrix … n) / n` **converges** to the per-partition CNT entropy rate
  `cntEntropyPartition (adPerm σ) (densityOfPMF μ) (projPartition c)`. In other words, on the
  abelian corner the CNT rate — defined as an infimum — is a genuine limit, exactly because the
  classical KS sequence to which it collapses is subadditive (Fekete's lemma).

Subadditivity is what makes the `sInf` defining the CNT rate a true limit here. For general (non-
commutative) operational partitions this subadditivity **fails** — see the subadditivity
counterexample module — so the well-definedness of the CNT rate as a limit is a special feature of
the abelian corner, not a general theorem.

## References

* Robert Alicki and Mark Fannes, *Quantum Dynamical Systems*, Oxford University Press (2001).
-/

open Matrix MeasureTheory Function Real
open scoped ComplexOrder ENNReal

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

variable {d k : ℕ}

/-- **Abelian-corner Fekete subadditivity.** On the diagonal corner, the von Neumann entropy
sequence `n ↦ S(corrMatrix (adPerm σ) ρ_μ (projPartition c) n)` of the CNT correlation matrices is
`Subadditive`: `S(m + n) ≤ S(m) + S(n)`. Via the per-resolution diagonal collapse
`vonNeumannEntropy_corrMatrix_eq_ksEntropySeq` this sequence coincides with the classical
iterated-join entropy sequence `ksEntropySeq` of the measure-preserving system
`(⇑σ, probMeasure μ)`, whose subadditivity is the classical Fekete inequality `ksSubadditive`. (In
the non-commutative case
this subadditivity fails; see the subadditivity counterexample module.) -/
theorem subadditive_vonNeumannEntropy_corrMatrix_abelian
    (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) (hinv : ∀ i, μ (σ i) = μ i) (c : Fin d → Fin k) :
    Subadditive (fun n => vonNeumannEntropy
      (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) n)) := by
  haveI := probMeasure_isProb μ hμ
  have hfun : (fun n => vonNeumannEntropy
        (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) n))
      = ErgodicTheory.Entropy.ksEntropySeq (measurePreserving_perm μ σ hinv)
          (projMeasurePartition μ c) := by
    funext n
    exact vonNeumannEntropy_corrMatrix_eq_ksEntropySeq μ hμ σ hinv c n
  rw [hfun]
  exact ErgodicTheory.Entropy.ksSubadditive (measurePreserving_perm μ σ hinv)
    (projMeasurePartition μ c)

/-- **Abelian-corner Fekete convergence of the CNT entropy rate.** On the diagonal corner the
averaged von Neumann entropies `n ↦ S(corrMatrix (adPerm σ) ρ_μ (projPartition c) n) / n` converge
to the per-partition CNT dynamical entropy `cntEntropyPartition (adPerm σ) ρ_μ (projPartition c)`.
The CNT rate is a priori an infimum; here it is a genuine limit, because the per-resolution diagonal
collapse `vonNeumannEntropy_corrMatrix_eq_ksEntropySeq` turns the sequence into the classical
subadditive iterated-join entropy sequence, to which Fekete's lemma (`tendsto_ksEntropySeq`)
applies. -/
theorem tendsto_cntEntropyPartition_abelian
    (μ : Fin d → ℝ≥0∞) (hμ : ∑ i, μ i = 1)
    (σ : Equiv.Perm (Fin d)) (hinv : ∀ i, μ (σ i) = μ i) (c : Fin d → Fin k) :
    Filter.Tendsto (fun n => vonNeumannEntropy
        (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) n) / (n : ℝ))
      Filter.atTop
      (nhds (cntEntropyPartition (adPerm σ) (densityOfPMF μ hμ) (projPartition c))) := by
  haveI := probMeasure_isProb μ hμ
  rw [cntEntropyPartition_eq_ksEntropyPartition μ hμ σ hinv c]
  have hfun : ∀ n,
      vonNeumannEntropy (corrMatrix (adPerm σ) (densityOfPMF μ hμ) (projPartition c) n)
        = ErgodicTheory.Entropy.ksEntropySeq (measurePreserving_perm μ σ hinv)
            (projMeasurePartition μ c) n :=
    vonNeumannEntropy_corrMatrix_eq_ksEntropySeq μ hμ σ hinv c
  simp_rw [hfun]
  exact ErgodicTheory.Entropy.tendsto_ksEntropySeq (measurePreserving_perm μ σ hinv)
    (projMeasurePartition μ c)

end ErgodicTheory.OperatorEntropy.CNT
