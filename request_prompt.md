**Request: additive extensions to the Oseledets / multiplicative-ergodic-theorem formalization**

Context: this builds on the existing one-sided development for the iterated linear matrix cocycle over a measure-preserving base — the Furstenberg–Kesten top exponent, the measurable Oseledets filtration, the Lyapunov spectrum with multiplicities, and the exterior-norm machinery. Everything below is purely **additive**: please don't remove, rename, or weaken anything already proved. Design all names, types, and packaging as you see fit; keep everything sorry-free and on the current toolchain / Mathlib pin. And please **don't rule anything out** — if a related result is cheap given what you already have, include it.

1. **Sum of positive Lyapunov exponents.** A packaged, real-valued, base-a.e.-constant quantity equal to the sum of the strictly positive exponents counted with multiplicity — available as a single directly usable term, not something the consumer must reassemble from the raw spectrum. Symmetrically, also the sum of the non-negative exponents and the sum of the negative exponents.

2. **Growth-rate / exterior characterization.** Identify that sum — and, more generally, each partial sum of the top k exponents — with the asymptotic exponential growth rate of the corresponding exterior (wedge) power of the cocycle: the k-volume growth rate, equivalently the sum of the top k log-singular-values of the iterates. In particular, the positive-exponent sum as the top exponent of the exterior cocycle / the asymptotic growth of the largest minor.

3. **Sign and vanishing characterizations.** That the positive-exponent sum is ≥ 0; equals 0 iff every exponent is ≤ 0 (the asymptotically non-expanding case); is > 0 iff some exponent is > 0 — and the dual statements for contraction.

4. **Regularity in the cocycle — highest value.** Any available semicontinuity / continuity / monotonicity of the exponents as functions of the generating cocycle. In particular, whether the top exponent, the partial sums of the top k exponents, and the positive-exponent sum are **upper semicontinuous** in the generator (e.g. under uniform or L¹-log convergence), and exactly where continuity does and does not hold. Please state this as strongly and generally as the machinery allows, with the honest caveats; this is the single most valuable addition.

5. **Restriction to invariant sub-cocycles.** For a measurable cocycle-invariant family of subspaces (an invariant subbundle), the Lyapunov spectrum / exponents / positive-exponent sum of the restricted cocycle, and how the restricted spectrum sits inside the full one (sub-spectrum / interlacing). I.e. the multiplicative-ergodic data of the cocycle restricted to an invariant subbundle.

6. **Full spectrum as a consumable object.** The complete ordered spectrum exposed as a directly usable object (the list/multiset of exponents with multiplicities, plus accessors for individual exponents), the singular-value characterization (exponents as a.e. limits of (1/n)·log of the iterate singular values), and the tie to the eigenvalues of the limiting operator.

7. **Trace / determinant identity.** The sum of all exponents (with multiplicity) as the asymptotic log-determinant growth rate, equal to the integral of log|det| of the generator, with the volume-contraction consequences.

8. **Inverse / time reversal.** The relation between the spectrum of the cocycle and of its inverse (time-reversed) cocycle — the inverse exponents being the negatives of the exponents in reversed order — tying the positive and negative spectra; state any inverse-integrability hypothesis where needed.

9. **Relaxations, if cheap.** Where feasible without major rework: the non-ergodic version (exponents as invariant measurable functions rather than a.e. constants); and one-sided / positive-exponent statements that avoid the invertibility (det ≠ 0) hypothesis, covering possibly-singular matrix cocycles.

10. **Lower priority, not blocking.** The two-sided Oseledets splitting (invariant direct-sum decomposition, "Stage C") and, eventually, a continuous-time / flow version of the cocycle — welcome when convenient, listed only so they aren't excluded.

Keep base-system and integrability hypotheses natural, reuse the existing filtration / exterior-norm results, and make every addition sorry-free.
