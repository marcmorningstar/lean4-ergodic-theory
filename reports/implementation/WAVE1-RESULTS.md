# Wave 1 — Implementation Tournament Results (2026-06-22)

8 lean-workers in warm `lwt` worktrees, each pipelined into an adversarial mathematician QA pass.
16 agents, ~1.49M tokens, ~4.6h wall. **No full closures** (consistent with recon's research-wall
verdicts), but every wall sharpened to faithful, individually-typed, literature-matched leaves.
All QA verdicts: pass-partial, statement-faithful, **no hidden unsoundness**. Authoritative
`lake build` of all touched modules: exit 0. Default `Oseledets`/`AxiomAudit` build: unaffected.

## Per-wall outcomes (merged branch in **bold**)

### #9 mfderiv — **impl-i9-a** (merged) ; impl-i9-b discarded (messier, 3 sorries)
- Leaf B (`exists_measurableFraming_of_sigmaCompact`) body is now **sorry-free**: constant identity
  frame `fun _ => ContinuousLinearEquiv.refl ℝ E` (valid since `TangentSpace I x` is *definitionally*
  `E`); the report's disjointified-trivialization plan confirmed a red herring and removed.
- Both leaves reduced to ONE mfderiv-measurability core (`measurable_mfderiv_of_contMDiff_boundaryless`
  / `measurable_mfderivModel_of_contMDiff_boundaryless`, identical content per file).
- Honest hyps added (faithful, no conclusion weakened): `[I.Boundaryless]`, `[SigmaCompactSpace M]`,
  `[SecondCountableTopology H]`, `MDifferentiable → ContMDiff I I 1` (C¹).
- Residual gap: recover `mfderiv` from its (continuous, via `ContMDiffAt.mfderiv_const`) fixed-base
  in-coordinates representative — the moving-trivialization-index coordinate-change continuity Mathlib
  packages only inside `inTangentCoordinates`. ~250–400 line chart-algebra. (NOTE: contrary to recon,
  the `ContMDiffMFDeriv` import is CACHED here — no Mathlib rebuild needed.)

### #11 Arsenin–Kunugui — **impl-i11-b** (merged) ; impl-i11-a, impl-i11-novikov not merged
- Headline `measurableInfDist_of_measurableGraph_AK` reduced from 2 sorries to **1** via the
  Euclidean re-route (Strategy B): the general DST leaves are no longer load-bearing for the
  issue-#6 consumer.
- Single residual: `measurableSet_image_fst_of_subset_compact_box` (B ⊆ univ ×ˢ Q, Q compact ⇒
  measurable projection) = Novikov / Srivastava 4.7.4 product-only topology refinement. Still genuine
  DST (naive "closed+compact-sections ⇒ closed projection" is provably FALSE — recorded counterexample).
- (impl-i11-a separately drove `CastaingSelection` to 0 sorries via a `[StandardBorelSpace X]` route +
  a new EuclideanProjection leaf — kept as reference; impl-i11-novikov decomposed the general 4.7.11
  into a 4.7.4 primitive.)

### #8 Yamamoto — **impl-i8-c** (merged) ; impl-i8-b discarded (QA: zero progress, regressed 1→3)
- Strategy C (exterior-power/Gelfand) confirmed viable: `tendsto_prod_singularValues_pow`
  (Gelfand for the compound matrix) and `neZero_finrank_exteriorPower_of_le` proved **sorry-free**.
- One opaque sorry → 2 sharp true lemmas: `spectralRadius_compound_eq_prod_eigenvalueModuli`
  (eigenvalues of the j-th compound = j-fold products of M's eigenvalues — the real matrix-analysis
  crux) and `yamamoto_prod_to_index` (pure Real-analysis telescoping — closeable).

### #10 Pesin — **impl-i10-decomp** (merged) — AT HONEST FLOOR
- The reachable analytic piece L1b (`rate_log_div_tendsto_zero_of_tendsto_pos`, Radon–Nikodym density
  rate via Lévy-upward martingale) landed **sorry-free**.
- Opaque sorry split into 2 attributed leaves: `manePropLowerBound` (Mañé Layer 1, Prop 7.7 — needs
  a *countable*-partition KS-entropy API + the Shannon–McMillan–Breiman theorem, both absent from
  Mathlib) and `localEntropy_ge_unstableJacobian` (Layer 2 — the genuine multi-year Pesin/
  Ledrappier–Young geometry: measurable Eˢ⊕Eᵘ splitting, unstable foliation + absolute continuity,
  leaf disintegration). Not pursued further in Wave 2 (genuine wall).
- HONESTY FLAG (pre-existing): `SRBProperty.acConditionalUnstable : True` is a stub field (trivially
  inhabited) despite its docstring — the proof cannot yet consume SRB-ness. Noted for follow-up.

## Merged into `campaign/issues-8-11` @ d7ea1f4
Frontier/Issue1/Yamamoto.lean, Issue2/{DerivativeCocycleManifold,Existence}.lean,
Issue4Pesin/ManeLowerBound.lean, Issue6/ArseninKunugui.lean.
