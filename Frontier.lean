/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

/-!
# Frontier — staging library for top-down frontier formalization

This is the **staging** root of the `Frontier` lake library: the in-progress, top-down formalization of the
Mathlib-scale infrastructure needed to make the open MET enhancements fully unconditional —

* **#4** the Ruelle entropy inequality `h_μ(T) ≤ ∑ λᵢ⁺` (smooth-ergodic geometric core), and
* **#6** the measurable singular forward Oseledets filtration (measurable selection of `{v : λ̄ ≤ c}`).

Unlike the `ErgodicTheory` library, `Frontier` is **not** linted and **not** `warningAsError`, so modules here
may carry `sorry` while the dependency tree is filled in top-down. This **root module is intentionally
import-free**: it imports none of the `Frontier.*` subtree, so a plain `lake build` compiles only this
sorry-free root olean — which the blueprint CI's `checkdecls` needs in order to import every workspace
library root (see the `defaultTargets` note in `lakefile.toml`). The sorry-carrying `Frontier.Issue*`
subtree is therefore not reachable from the root and is built explicitly via `lake build Frontier.<Module>`.
Once a subtree is fully `sorry`-free it migrates into `ErgodicTheory/` proper (which enforces sorry-freeness
and the Mathlib style-linter set).

Modules are written to **Mathlib-merge quality** (naming conventions, namespacing, docstrings) so the
infrastructure is upstreamable as reference.
-/
