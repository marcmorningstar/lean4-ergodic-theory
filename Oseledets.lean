import Oseledets.Cocycle.Basic
import Oseledets.Cocycle.Norm
import Oseledets.Cocycle.FurstenbergKesten
import Oseledets.Ergodic.MaximalErgodic
import Oseledets.Ergodic.Birkhoff
import Oseledets.Ergodic.Kingman
import Oseledets.Lyapunov.ExteriorNorm
import Oseledets.Lyapunov.Fischer
import Oseledets.Lyapunov.MeasurableSubspace
import Oseledets.Lyapunov.Measurable
import Oseledets.Lyapunov.Ultrametric
import Oseledets.Lyapunov.GrowthFunction
import Oseledets.Lyapunov.Filtration
import Oseledets.Lyapunov.OseledetsLimit
import Oseledets.Lyapunov.Forward
import Oseledets.Lyapunov.ForwardOverlap
import Oseledets.Lyapunov.ForwardAngle
import Oseledets.Lyapunov.ForwardTempering
import Oseledets.Lyapunov.ForwardUpperBound
import Oseledets.Lyapunov.ForwardDetSqueeze
import Oseledets.Lyapunov.ForwardSqueezeData
import Oseledets.Lyapunov.ForwardSqueezeCore
import Oseledets.Lyapunov.ForwardSubcoboundary
import Oseledets.Lyapunov.ForwardFrames
import Oseledets.Lyapunov.ForwardMeasurable
import Oseledets.Lyapunov.ForwardV
import Oseledets.Lyapunov.SpectralMeasurable
import Oseledets.MultiplicativeErgodic
import Oseledets.Lyapunov.FiltrationAssembly
import Oseledets.Lyapunov.FiltrationAssemblyBridge
import Oseledets.Lyapunov.SlowFlagBridge
import Oseledets.Lyapunov.SpectrumConstancy
import Oseledets.Lyapunov.RuelleCore
import Oseledets.Lyapunov.ForwardLowerWiring
import Oseledets.Lyapunov.AssemblyFromUpper
import Oseledets.Lyapunov.CapstoneTelescope
import Oseledets.Lyapunov.SpectrumResiduals
import Oseledets.Lyapunov.RuelleReverse
import Oseledets.Lyapunov.CapstoneWiring
import Oseledets.Lyapunov.LimitEigenbasis
import Oseledets.Lyapunov.AssemblyFromUpperIdent
import Oseledets.Lyapunov.SpectralIdentification
import Oseledets.Lyapunov.ForwardGradedOverlap
import Oseledets.Lyapunov.BridgeWiring
import Oseledets.Lyapunov.AssemblyChain

/-!
# Oseledets

Root module of the `Oseledets` library: a Lean 4 + Mathlib formalization of the
**Oseledets multiplicative ergodic theorem (MET)**, one-sided filtration form.

This module imports the whole development. The mathematical and planning context lives
under `docs/` (research dossier, target & milestone ladder, phased plan, progress).

## Layout

* `Oseledets.Cocycle.Basic` — the iterated linear cocycle and its basic API.
* `Oseledets.Cocycle.Norm` — measurability of the L2 operator norm and matrix inverse.
* `Oseledets.Cocycle.FurstenbergKesten` — extremal Lyapunov exponents (`M5`).
* `Oseledets.Ergodic.MaximalErgodic` — maximal ergodic inequality (`M1`).
* `Oseledets.Ergodic.Birkhoff` — pointwise Birkhoff ergodic theorem (`M2`, `M3`).
* `Oseledets.Ergodic.Kingman` — Kingman's subadditive ergodic theorem (`M4`).
* `Oseledets.Lyapunov.MeasurableSubspace` — measurably-varying subspaces (`M7` infra).
* `Oseledets.MultiplicativeErgodic` — the target theorem `oseledets_filtration` (`M10`).

The development is currently a `sorry`-stubbed skeleton; gaps are filled phase by phase
(see `docs/plan/implementation-plan.md` and `docs/progress/STATE.md`).
-/
