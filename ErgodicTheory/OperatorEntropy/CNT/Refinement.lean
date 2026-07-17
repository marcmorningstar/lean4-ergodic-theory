import ErgodicTheory.OperatorEntropy.Basic

/-!
# CNT/ALF refinement of an operational partition of unity

This module sets up the finite-dimensional Connes–Narnhofer–Thirring / Alicki–Fannes
construction of quantum dynamical entropy (Alicki–Fannes, *Defining Quantum Dynamical
Entropy*, Lett. Math. Phys. **32** (1994); Ohya–Petz, *Quantum Entropy and Its Use*).

The dynamics is a unital `*`-algebra endomorphism `Φ` of the matrix algebra
`Matrix (Fin d) (Fin d) ℂ`.  An **operational partition of unity** is a finite family
`(xᵢ)` of operators with `∑ᵢ xᵢᴴ xᵢ = 1`.  Its **time-ordered refinement** along `Φ` is the
operator family

`refine Φ X (n) f = x_{f 0} · Φ(x_{f 1}) · Φ²(x_{f 2}) ⋯ Φⁿ⁻¹(x_{f (n-1)})`,

defined here by the telescoping recursion `refine (n+1) f = x_{f 0} · Φ(refine (n) (tail f))`.
The substantive result is the **telescoping identity**
`∑_f (refine n f)ᴴ (refine n f) = 1`, i.e. the refinement is again an operational partition of
unity.  It feeds the correlation density matrix of the companion `Construction` module.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace ErgodicTheory.OperatorEntropy.CNT

variable {d : ℕ}

/-- A unital `*`-algebra endomorphism of `Matrix (Fin d) (Fin d) ℂ` (a finite-dimensional
quantum dynamics).  We carry additivity/`0` as well as multiplicativity/`1` and the `*`-structure,
since a `*`-homomorphism of matrix algebras is automatically additive; the additivity is what lets
`Φ` commute with the finite sums in the telescoping identity. -/
structure UnitalStarEndo (d : ℕ) where
  /-- The underlying map on operators. -/
  toFun : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ
  /-- `Φ` preserves `0`. -/
  map_zero : toFun 0 = 0
  /-- `Φ` is additive. -/
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- `Φ` preserves the identity. -/
  map_one : toFun 1 = 1
  /-- `Φ` is multiplicative. -/
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  /-- `Φ` commutes with the adjoint. -/
  map_star : ∀ x, toFun xᴴ = (toFun x)ᴴ

/-- A finite operational partition of unity: a family `(op i)` of operators with
`∑ᵢ (op i)ᴴ (op i) = 1`. -/
structure OperationalPartition (d k : ℕ) where
  /-- The operators of the partition. -/
  op : Fin k → Matrix (Fin d) (Fin d) ℂ
  /-- The partition-of-unity relation. -/
  partUnity : ∑ i, (op i)ᴴ * (op i) = 1

namespace UnitalStarEndo

/-- `Φ` commutes with finite sums (it is additive). -/
theorem map_sum (Φ : UnitalStarEndo d) {ι : Type*} (s : Finset ι)
    (h : ι → Matrix (Fin d) (Fin d) ℂ) :
    Φ.toFun (∑ i ∈ s, h i) = ∑ i ∈ s, Φ.toFun (h i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, Φ.map_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Φ.map_add, ih]

end UnitalStarEndo

/-- The time-ordered refinement of an operational partition `X` along the dynamics `Φ`:
`refine Φ X (n+1) f = x_{f 0} · Φ(refine Φ X n (tail f))`, with `refine Φ X 0 _ = 1`.  This
telescopes to `x_{f 0} · Φ(x_{f 1}) ⋯ Φⁿ⁻¹(x_{f (n-1)})`. -/
def refine (Φ : UnitalStarEndo d) {k : ℕ} (X : OperationalPartition d k) :
    (n : ℕ) → (Fin n → Fin k) → Matrix (Fin d) (Fin d) ℂ
  | 0,     _ => 1
  | n + 1, f => X.op (f 0) * Φ.toFun (refine Φ X n (Fin.tail f))

@[simp]
theorem refine_zero (Φ : UnitalStarEndo d) {k : ℕ} (X : OperationalPartition d k)
    (f : Fin 0 → Fin k) : refine Φ X 0 f = 1 := rfl

theorem refine_succ (Φ : UnitalStarEndo d) {k n : ℕ} (X : OperationalPartition d k)
    (f : Fin (n + 1) → Fin k) :
    refine Φ X (n + 1) f = X.op (f 0) * Φ.toFun (refine Φ X n (Fin.tail f)) := rfl

/-- The `n = 1` time-ordered refinement of any partition is just its selected operator:
`refine Φ X 1 f = X.op (f 0)`, since `refine Φ X 0 _ = 1` and `Φ 1 = 1`. -/
theorem refine_one {d k : ℕ} (Φ : UnitalStarEndo d) (X : OperationalPartition d k)
    (f : Fin 1 → Fin k) : refine Φ X 1 f = X.op (f 0) := by
  rw [refine_succ, refine_zero, Φ.map_one, mul_one]

/-- Application of the `Fin.cons` equivalence is `Fin.cons`. -/
theorem consEquiv_apply {k n : ℕ} (i : Fin k) (g : Fin n → Fin k) :
    (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) (i, g) = Fin.cons i g := rfl

/-- **Telescoping identity.**  The time-ordered refinement of an operational partition of unity is
again an operational partition of unity: `∑_f (refine Φ X n f)ᴴ (refine Φ X n f) = 1`. -/
theorem sum_refine_conjTranspose_mul_refine (Φ : UnitalStarEndo d) {k n : ℕ}
    (X : OperationalPartition d k) :
    ∑ f : Fin n → Fin k, (refine Φ X n f)ᴴ * (refine Φ X n f) = 1 := by
  induction n with
  | zero =>
    rw [Fintype.sum_unique, refine_zero, conjTranspose_one, one_mul]
  | succ n ih =>
    have perG : ∀ g : Fin n → Fin k,
        ∑ i : Fin k, (refine Φ X (n + 1) (Fin.cons i g))ᴴ * refine Φ X (n + 1) (Fin.cons i g)
        = Φ.toFun ((refine Φ X n g)ᴴ * refine Φ X n g) := by
      intro g
      have hM : ∀ i : Fin k,
          (refine Φ X (n + 1) (Fin.cons i g))ᴴ * refine Φ X (n + 1) (Fin.cons i g)
          = (Φ.toFun (refine Φ X n g))ᴴ * ((X.op i)ᴴ * X.op i)
              * Φ.toFun (refine Φ X n g) := by
        intro i
        rw [refine_succ, Fin.cons_zero, Fin.tail_cons, conjTranspose_mul]
        simp only [mul_assoc]
      rw [Finset.sum_congr rfl (fun i _ => hM i), ← Finset.sum_mul, ← Finset.mul_sum,
        X.partUnity, mul_one, ← Φ.map_star, ← Φ.map_mul]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k))
        (fun f => (refine Φ X (n + 1) f)ᴴ * refine Φ X (n + 1) f)]
    simp only [Fintype.sum_prod_type, consEquiv_apply]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun g _ => perG g),
      ← Φ.map_sum Finset.univ (fun g => (refine Φ X n g)ᴴ * refine Φ X n g), ih, Φ.map_one]

end ErgodicTheory.OperatorEntropy.CNT
