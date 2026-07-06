# Mathlib conventions — an evidence-backed guide for a merge-quality refactor of `lean4-ergodic-theory` (formerly `lean4-oseledets`)

## Purpose

This report is the single authoritative reference for refactoring the Oseledets
Lean library to **Mathlib-merge quality**. It distills the conventions Mathlib
enforces — by linter, by reviewer checklist, and by de-facto practice — into
concrete, actionable rules, each backed by evidence (a local `file:line` or a
URL). It then turns those findings into a concrete decision on the one structural
problem that dominates this codebase: the three giant files

| File | Lines | `private` decls | current override |
|---|---:|---:|---|
| `ErgodicTheory/Lyapunov/OseledetsLimit.lean` | 3779 | 1 | `set_option linter.style.longFile 3900` |
| `ErgodicTheory/Ergodic/Kingman.lean` | 3455 | 113 | `set_option linter.style.longFile 3600` |
| `ErgodicTheory/Lyapunov/ExteriorNorm.lean` | 2751 | 39 | `set_option linter.style.longFile 2900` |

(Counts verified locally: `wc -l` and `grep -rEc '^[[:space:]]*private '` on the
three files; the overrides are on the last line of each file.)

A crucial environmental fact, verified locally (`grep -rln '^module$' ErgodicTheory/`
returns nothing): **this project is on the classic source-file system, not the new
module system.** That single fact governs the whole private-lemma strategy below,
because under the classic system `private` is strictly file-local and cannot be
referenced from any importing file.

The conventions are organized one per dimension (naming; file organization &
splitting; private / API surface; documentation; code style & tactics; PR-review
feedback; linter ground-truth), followed by the dedicated decision guide and a
compliance checklist.

## Status update (cleanup applied)

The merge-quality cleanup this report recommends has been carried out:

* The three giant files above were split into topic directories (`OseledetsLimit/`,
  `Ergodic/Kingman/`, `ExteriorNorm/`); no `longFile` override remains.
* The dead `AssemblyChain` route was removed (its live `dim_zero` base case extracted to
  `Lyapunov/DimZero.lean`); the 10 post-theorem corollary files were moved to
  `Lyapunov/Extensions/`; and the build-pipeline-named assembly/wiring/bridge files were renamed
  to mathematical names (e.g. `BridgeWiring → FastIndexSpectralEnvelope`,
  `AssemblyTopGap → FiltrationFromTopGapEnvelope`, `FiltrationAssembly → FiltrationFromInterfaces`).
* `## References` (prose) were added to the result-bearing modules, and `docs/references.bib`
  now holds the canonical bibtex entries (the per-file prose → `[…][key]` conversion happens at
  Mathlib-PR time, against Mathlib's own `references.bib`).
* `linter.mathlibStandardSet` is enabled on the `ErgodicTheory` lib with `warningAsError`
  (`lakefile.toml`), so `lake build` — and hence CI — fails on any style-lint regression. The
  full library was verified to build clean under this setting.

Deferred follow-ups (documented, not blockers):

* **Re-pin Mathlib to a tagged release** once Lean exits `v4.30.0-rc2`; the current pin is an
  exact main-branch commit (intentional, for toolchain/cache coupling — see the `[[require]]`
  note in `lakefile.toml`).
* **Enable the environment linter** (`#lint` / `lake exe runLinter`) as an additional CI gate
  beyond the style linters; this needs a `runLinter` target and may surface `docBlame`/`simpNF`
  items, so it is scoped as its own pass.

---

## 1. Naming

Mathlib's naming scheme is codified at
<https://leanprover-community.github.io/contribute/naming.html> and partially
enforced by linters in `.lake/packages/mathlib/Mathlib/Tactic/Linter/`.

- **Capitalization by syntactic role.** File names and Prop/Type/structure/class
  names are `UpperCamelCase`; theorem/proof names (terms of `Prop`) are
  `snake_case`; data and functions-named-after-their-return-value are
  `lowerCamelCase`; an `UpperCamelCase` name embedded inside a `snake_case`
  theorem name is referenced `lowerCamelCase`; acronyms are cased as a group by
  the first character.
  Evidence: <https://leanprover-community.github.io/contribute/naming.html#capitalization>
  (rules 1–6). Bearing: this is mostly a **verification pass** — the project
  already conforms (`singularValues_le_opNorm`, `oseledetsLimitExists`,
  `bandProjector`, `lamSing`, `qpow`, `Is`-prefixed Props). **When splitting, do
  NOT rename a declaration to match the file it lands in — names are independent
  of file placement.**

- **File names are `UpperCamelCase`.** Lower-cased file names are a rare,
  Zulip-discussed exception (`lp.lean`).
  Evidence: <https://leanprover-community.github.io/contribute/naming.html#file-names>.
  Bearing: every new file produced by a split must be `UpperCamelCase`
  (`OseledetsLimit/Defs.lean`, `Kingman/Subadditive.lean`, …). The three existing
  names are already compliant.

- **Theorem names spell the conclusion left-to-right; hypotheses follow `_of_`
  in source order** (`A → B → C` ⇒ `C_of_A_of_B`); an unambiguous prefix of the
  description may be used.
  Evidence: <https://leanprover-community.github.io/contribute/naming.html#identifiers-and-theorem-names>.
  Bearing: the dominant convention to audit lemma names against. The project
  already follows it (`lamSing_eq_of_tendsto`, `tendsto_GammaK_of_integrableLogNorm`).

- **Symbol dictionary + American spelling.** `⊤`=`top`, `⊥`=`bot`, `≤`=`le`/`ge`,
  `<`=`lt`/`gt`, `∈`=`mem`, `→`=`of`/`imp` (conclusion first), `=`=`eq` (often
  omitted), `∘`=`comp`; American English throughout (`factorization`, not
  `factorisation`).
  Evidence: <https://leanprover-community.github.io/contribute/naming.html#names-of-symbols>,
  <https://leanprover-community.github.io/contribute/naming.html#spelling>.
  Bearing: filtration/lattice lemmas about `⊤`/`⊥` subspaces must use `_top`/`_bot`,
  not `_full`/`_zero`/`_max`.

- **Person-names are ordinary descriptive tokens, not proper nouns.** They are
  `lowerCamelCase` inside declaration names and `UpperCamelCase` in file/namespace
  names; they are NOT capitalized as proper nouns inside `snake_case` theorem names.
  Evidence: `Mathlib/Dynamics/BirkhoffSum/Basic.lean:31` (`def birkhoffSum`);
  `Average.lean:46` (`def birkhoffAverage`);
  theorem `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure`; vs the
  file/dir `Mathlib/Dynamics/BirkhoffSum/`, `Mathlib/Order/Birkhoff.lean`,
  `Mathlib/Analysis/Normed/Module/HahnBanach.lean`.
  Bearing: keep `Kingman.lean`, `OseledetsLimit.lean` as `UpperCamelCase`
  file/namespace names; inside declarations a person-name token goes
  `lowerCamelCase` (the project already does this with `oseledetsLimitExists`; a
  hypothetical `subadditive_kingman_…` would `lowerCamelCase` `kingman`). Split
  siblings stay `UpperCamelCase` (`Kingman/Subadditive.lean`).

- **No Mathlib precedent for Kingman/ErgodicTheory/Lyapunov** — none appear in Mathlib
  source or `docs/references.bib` — so the project sets the canonical names; do so
  by analogy to `birkhoff`/`hahn`/`banach`.
  Evidence: grep over `.lake/packages/mathlib/Mathlib` and
  `docs/references.bib` for `kingman/oseledets/lyapunov` returns nothing (verified:
  `grep -rln … references.bib` is empty). Bearing: pick names now with the
  `birkhoff` pattern in mind, because a future upstream PR is reviewed against it —
  data `kingman*`/`oseledets*` `lowerCamelCase`, files/dirs `Kingman`/`ErgodicTheory`
  `UpperCamelCase`, theorems conclusion-first.

- **Predicates are prefixes; Prop-valued classes are `Is`-nouns**
  (`IsClosed (Icc a b)` ⇒ `isClosed_Icc`; `IsTopologicalRing`). Suffix predicates
  only for the standardized atoms: `_injective`/`_surjective`/`_bijective`,
  `_monotone`/`_antitone`/`_strictMono`/`_strictAnti`, `_inj`, `_mono`/`_anti`.
  Evidence: <https://leanprover-community.github.io/contribute/naming.html#predicates-as-suffixes>,
  <https://leanprover-community.github.io/contribute/naming.html#prop-valued-classes>.
  Bearing: the project aligns (`isSubadditiveCocycle_logSprod`, `gram_isSelfAdjoint`,
  `bandProjector_isSelfAdjoint`, `logSprod_subadditive`). One known nit:
  `injective_toEuclideanLin` — the conventionally preferred form is
  `toEuclideanLin_injective` (the `injective_f` form is tolerated but reviewers may
  suggest the swap).
  Evidence: <https://leanprover-community.github.io/contribute/naming.html#naming-of-structural-lemmas>.

- **Namespace tokens in lemma names.** A definition referenced in a lemma name
  outside its namespace drops the namespace if unambiguous, else re-prepends it
  `lowerCamelCase`d, so every `_`-separated token resolves to a real
  definition/connective.
  Evidence: <https://leanprover-community.github.io/contribute/naming.html#identifiers-and-theorem-names>
  (`Nat.cast` → `map_natCast`/`Int.cast_natCast`),
  <https://leanprover-community.github.io/contribute/naming.html#dots>.
  Bearing: when a split moves lemmas about a definition into a different
  namespace/file, the lemma name must still encode that definition's token — a file
  move must not silently change which namespace tokens appear.

---

## 2. File organization & splitting

Mathlib's de-facto policy is **"split, almost never raise the cap."**

- **The `longFile` linter warns above 1500 lines.** `linter.style.longFileDefValue`
  has `defValue := 1500`; `linter.style.longFile` itself defaults to 0 (off) for
  downstream projects, 1500 in Mathlib's own lakefile.
  Evidence: `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean:352`
  (`public register_option linter.style.longFileDefValue : Nat := {`, defValue
  1500); doc string at `:342`. Bearing: all three files are **1.8×–2.5× over the
  cap** and would not pass Mathlib's standard linter set.

- **Empirical ground truth: Mathlib essentially never ships a file over 1500
  lines.** Of ~8063 `Mathlib/*.lean` files, exactly **2 exceed 1500 (and 0 exceed
  2000)**; the largest is **1525 lines** (`Analysis/Asymptotics/Defs.lean`).
  Evidence: local `find … -exec wc -l` survey. Bearing: 3779/3455/2751-line files
  are larger than anything Mathlib ships. The community answer is unambiguous:
  **split.**

- **Do NOT raise the cap with `set_option linter.style.longFile N` except in
  genuinely marginal cases.** Only **3 files in all of Mathlib** override it, and
  only to **1600/1700** (for 1525-/1508-line files).
  Evidence: grep — `Mathlib/Analysis/Asymptotics/Defs.lean:54` (`longFile 1600`)
  and `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean:1508`
  (`longFile 1700`); third hit is the linter's own source. Bearing: our overrides
  (3900/3600/2900) are exactly the smell the override mechanism is designed to
  discourage; a reviewer reads any surviving override as "this still needs
  splitting."

- **If an override is ever used (transitionally), its value is mechanically
  constrained.** It must equal `candidate = (lastLine/100)*100 + 200` (floored at
  1500) or `candidate + 100`; any other value — too high, too low, or unnecessary
  once the file shrinks — is itself flagged with the exact required value.
  Evidence: `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean:392-413`.
  Bearing: a transitional override must be set precisely to the formula value or CI
  fails; remove it the moment the file drops under 1500.

- **The PR-review guide is stricter than the linter: split at ~1000 lines, or for
  too-many-topics, or to minimize imports.** Import reduction is the primary
  architectural reason to split.
  Evidence: <https://leanprover-community.github.io/contribute/pr-review.html>
  ("should a file be split into multiple pieces because it's getting too long
  (e.g., > 1000 lines), or touches on too many different topics?"; "should some of
  the results be placed into a new file to minimize import requirements?"). Bearing:
  target each resulting file **well under ~1000–1400** lines, split along topic
  seams that also let dependents import only the sub-result they need.

- **Split by self-contained concept, not by line-count chunks.** A split-PR moves a
  concept's definitions AND the lemmas about it into a descriptively named file.
  Evidence: PR #4755 / merged #5940 "refactor: split BumpFunctionInner"
  (<https://github.com/leanprover-community/mathlib4/pull/4755>) carved out
  `Analysis.Calculus.SmoothTransition`. Bearing: name new files after the concept
  they own (`Kingman/Fekete.lean`, `Kingman/Subadditive.lean`), never
  `KingmanPart1/2/3`.

- **Large theories are a DIRECTORY of small files.** `Mathlib/Dynamics/` is the
  canonical relevant example (subdirs `BirkhoffSum/`, `Ergodic/`,
  `TopologicalEntropy/`, …; biggest file 892 lines, most < 300).
  Evidence: `Mathlib/Dynamics/` listing; line counts. Bearing: extend the existing
  `ErgodicTheory/Ergodic/` + `ErgodicTheory/Lyapunov/` shape — e.g. add an
  `ErgodicTheory/Ergodic/Kingman/` subdir for split Kingman files.

- **Use the `Defs.lean` / `Basic.lean` / `Lemmas.lean` (+ topic-named) idiom.**
  Pure definitions and core API in `Defs.lean`/`Basic.lean`; heavier downstream
  results in `Basic.lean`/`Lemmas.lean` or topic files.
  Evidence: Mathlib-wide counts — 732 `Basic.lean`, 215 `Defs.lean`, 69
  `Lemmas.lean`; 161 dirs contain both `Defs.lean` and `Basic.lean`. Bearing: the
  default split shape for our files. `OseledetsLimit` (1 private) splits cleanly
  into `Defs`/`Basic` + topic files with almost no de-privatization.

- **There is NO same-named aggregator `.lean` file beside a directory.** A directory
  is just leaf files; the library root imports each leaf.
  Evidence: no `Mathlib/Analysis/InnerProductSpace.lean` despite the 52-file
  `InnerProductSpace/` dir; `Mathlib.lean` imports leaves directly — `ErgodicTheory.lean`
  mirrors this. Bearing: add each new leaf to `ErgodicTheory.lean`'s import list (per
  CLAUDE.md, every module must be transitively imported from `ErgodicTheory.lean`).
  Mathlib's convention is to import leaves at the root rather than keep a thin
  re-import aggregator.

- **Every new file needs a header + a mandatory module docstring** (see §4) and
  inter-file "See also" cross-references in prose.
  Evidence: `Mathlib/Dynamics/BirkhoffSum/Basic.lean:18` ("See also
  `birkhoffAverage` defined in `Dynamics/BirkhoffSum/Average`."). Bearing: budget
  for 2 new compliant headers/docstrings per 3-way split; add cross-references
  afterward.

- **`section`/`variable` factor shared context.** Pervasive (~42280 `variable`
  lines). Bearing: each new file should re-establish its common `variable` context
  in a `section` rather than inlining binders. **Caveat (high relevance):** a moved
  declaration that no longer uses an inherited section variable will trip the
  `unusedSectionVars` linter — re-derive a *minimal* `variable` block per new file,
  or use `include`/`omit` (see §7).

---

## 3. Private / API surface

There are two regimes; **this project is in the classic one.**

- **Classic-regime hard constraint: `private` is strictly file-local.** Without
  module modifiers, an imported module's private scope is *not* added to importers;
  only the new module system's `import all` can expose privates by name.
  Evidence: <https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/>
  ("Without modifiers, the imported module's public scope is added to the current
  module's private scope … not made available to modules that import the current
  module."); local: no `module`/`public import`/`@[expose] public section` in
  `ErgodicTheory/`. **This is the single fact that dictates the split strategy: a
  private helper used on both sides of a proposed cut must either keep
  producer+consumers in one file, or be de-privatized.**

- **`private` is used sparingly in Mathlib (~1.3%) and never accumulated in bulk.**
  ~2121 `private` decls vs ~165505 lemmas/theorems. The most-private single file has
  **54** privates (`ModelTheory/.../Presburger/Semilinear/Basic.lean`, 786 lines);
  next is `Padics/Hensel.lean` (52 privates, 468 lines). **No Mathlib file combines a
  100+-private engine with a longFile overflow — there is no precedent for our
  situation.**
  Evidence: grep counts; per-file private survey. Bearing: Kingman's **113**
  privates are far above Mathlib's all-time max of 54 — the community reads this as
  "3–5 files of helpers crammed into one," an argument for splitting independent of
  longFile.

- **For a helper used in one file, the reviewer-endorsed signal is an `_aux`-suffixed
  name + a docstring "Not intended for use outside this file."** The canonical
  example is a *public* theorem, not a private one.
  Evidence: <https://leanprover-community.github.io/contribute/pr-review.html>
  (`PiLp.iSup_edist_ne_top_aux`); `.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:419-421`.
  Bearing: when a Kingman/ExteriorNorm helper must cross a split boundary (so cannot
  stay `private`), give it an `_aux` suffix + a "not intended for use outside this
  area" docstring. This satisfies reviewers that the public API is not ballooning
  even though the symbol is technically importable.

- **A dedicated `…Aux` namespace is the idiom for grouping a block of internal
  helpers.** 536 lemmas/theorems end in `_aux`; namespaces like `FDerivMeasurableAux`
  are closed with `end` and re-opened with `open …Aux`.
  Evidence: `Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:111` (`namespace
  FDerivMeasurableAux`) … `:354` (`end`) … `:356` (`open FDerivMeasurableAux`).
  Bearing: **this is the cleanest classic-regime mechanism for cross-file helpers** —
  move the shared engine into `Oseledets.<Area>.Aux`, keep names `_aux`-suffixed +
  docstringed, `open` it from consumers. Helpers stay non-private (so they cross
  files) but are clearly demarcated internal.

- **`protected`** keeps a name namespace-qualified-only (reachable but not casually
  grabbed when the namespace is open); used ~8466×. Bearing: `protected` + `_aux` is
  a reasonable middle ground for a cross-file helper that must be public but should
  discourage casual use.

- **`upstreamableDecl` linter is the official file-splitting aid.** By default it
  flags only theorems that depend solely on upstream material; private and `def`
  warnings are opt-in (`linter.upstreamableDecl.private`, `.defs`).
  Evidence: `.lake/packages/mathlib/Mathlib/Tactic/Linter/UpstreamableDecl.lean:60-88,99-110`.
  Bearing: run `set_option linter.upstreamableDecl true` (optionally `.private true`)
  when planning the split to get an evidence-based cut line.

- **`privateModule` linter forbids an all-private module** (suggests `@[expose]
  public section` or selectively marking decls public).
  Evidence: `.lake/packages/mathlib/Mathlib/Tactic/Linter/PrivateModule.lean:13-19,59-90`.
  Bearing: **do NOT carve helpers into a file that ends up all-private** — use a
  non-private `…Aux` namespace instead. (Note: gated on the new module system via
  `(← getEnv).header.isModule`, so it only bites if/when we adopt modules; but the
  spirit applies regardless and reviewers will object to an all-private file.)

- **Module-system regime (the forward-looking alternative).** Stabilized Lean
  4.27.0-rc1 (Nov 2025), now fully adopted by Mathlib (7952 files start with
  `module`). Names are private-by-default; a same-package sibling can pull another
  file's private scope via `import all M`, "to allow separating definitions and
  proofs into separate modules for internal organization of a library." Our toolchain
  (`v4.30.0-rc2`) supports it.
  Evidence: <https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/>;
  `Mathlib/Dynamics/Ergodic/Ergodic.lean` (`module` at `:6`, `public import` at `:8-9`,
  `public section` at `:34`; the `@[expose] public section` form is what the
  `privateModule` linter itself recommends). Bearing: optional but strategic — adopting the module
  system lets Kingman's cross-boundary helpers be marked `public` (name visible,
  body unexposed) or shared via `import all` WITHOUT widening the public API. This is
  the purpose-built solution; if we stay classic, the `…Aux` pattern is the fallback.

---

## 4. Documentation

Mathlib enforces a rigid docstring skeleton, partly via the `Header` and `DocString`
linters (which fail the build), partly via the contribute/PR-review pages.

- **4-line copyright header, validated char-for-char.** `/-` / `Copyright (c) YYYY
  <Name>. All rights reserved.` / `Released under Apache 2.0 license as described in
  the file LICENSE.` / `Authors: <names, comma-separated, no "and", no trailing
  period>` / `-/`. Use `Authors` even for a single author.
  Evidence: `.lake/packages/mathlib/Mathlib/Tactic/Linter/Header.lean:174-235`;
  <https://leanprover-community.github.io/contribute/style.html#header-and-imports>.
  Bearing: the project's headers already match (e.g.
  `ErgodicTheory/MultiplicativeErgodic.lean:1-5`). Every new split file must copy this
  verbatim (author "Marcel Morgenstern", appropriate year). No process register in
  the header.

- **Module docstring must be the first command after imports.** A missing or
  misplaced module docstring fails the Header linter.
  Evidence: `.lake/packages/mathlib/Mathlib/Tactic/Linter/Header.lean:431-437`;
  <https://leanprover-community.github.io/contribute/doc.html#header-comment>.
  Bearing: each new file from a split needs its OWN `/-! # … -/` immediately after
  imports.

- **Module-docstring skeleton, fixed order:** a first-level `#` title + one-paragraph
  summary, then second-level (`##`) sections in this order — `## Main definitions`
  (optional), `## Main statements` / `## Main results` (optional), `## Notation`
  (mandatory iff notation is introduced), `## Implementation notes`, `## References`,
  `## Tags`.
  Evidence: <https://leanprover-community.github.io/contribute/doc.html#header-comment>,
  <https://leanprover-community.github.io/contribute/style.html#module-docstrings>;
  example `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:11-29`. Bearing: the
  project uses **non-standard headings** that must be normalized (verified locally):
  - `ExteriorNorm.lean:46` → `## Implementation notes — the diamond trap` (strip the
    "— the diamond trap" suffix; it becomes `## Implementation notes`).
  - `Kingman.lean:37` → `## Strategy (pointwise Katznelson–Weiss / Steele)`
    (legitimate proof sketch, but mis-placed as a top-level section; fold into
    `## Implementation notes` or move to interspersed proof comments).
  - `Kingman.lean:61` → `## Finiteness hypothesis` (not a standard section; fold into
    `## Implementation notes`).
  - `OseledetsLimit.lean` uses `## Main results` correctly (`:38`) and `## Main
    definitions` (`:33`). `MultiplicativeErgodic.lean` uses non-standard `## Statement`
    and singular `## Main result` (Mathlib uses `## Main results`/`## Main statements`).
  When splitting, give each new file a **focused** `## Main results` listing only its
  own declarations; do NOT duplicate the parent's full list.

- **Markdown details.** Multi-line module-docstring bullets indent continuation lines
  by two spaces; backtick Lean identifiers (they auto-link), use `$…$`/`$$…$$` for
  LaTeX, and wrap raw URLs in `<…>`. In-body sectioning comments use `/-! ### … -/`
  (third-level).
  Evidence: <https://leanprover-community.github.io/contribute/style.html#module-docstrings>,
  <https://leanprover-community.github.io/contribute/doc.html#latex-and-markdown>,
  <https://leanprover-community.github.io/contribute/doc.html#sectioning-comments>.
  Bearing: preserve two-space continuation indent when redistributing bullets; use
  the existing `/-! ### … -/` blocks as cut points and carry them with their
  declarations.

- **Every definition and major theorem MUST have a docstring** (`docBlame`/
  `docBlameThm`), and the docstring must convey *mathematical meaning* (may "lie
  slightly" about implementation), end in a period if a full sentence, and bold-face
  named theorems (`**mean value theorem**`).
  Evidence: <https://leanprover-community.github.io/contribute/doc.html#doc-strings>;
  PR #5580. Bearing: **keeping a helper `private` avoids the `docBlame` obligation** —
  so for genuinely-internal lemmas, prefer keeping them private (or, if they must
  cross a file boundary, give a real mathematical docstring only to the few that form
  the cross-file interface).

- **References must be bibtex keys in `docs/references.bib`, cited as `[Author,
  *Title*][bibkey]`.** Prose-only reference lists do not link and are not merge-quality.
  Evidence: <https://leanprover-community.github.io/contribute/doc.html#citing-other-works>;
  `Mathlib/MeasureTheory/Measure/FiniteMeasure.lean:78`;
  `.lake/packages/mathlib/docs/references.bib:1-15`. **Local gap (verified):**
  `docs/references.bib` (the pinned Mathlib copy) has NO oseledets/ruelle/viana/
  kingman/katznelson/furstenberg entries, and our `## References` are prose (e.g.
  `MultiplicativeErgodic.lean:31-36` lists Ruelle 1979 IHÉS, Viana 2014 as plain
  text). For merge: add bibtex entries (Oseledets 1968, Ruelle 1979, Viana 2014,
  Kingman 1968) and convert prose to `[…][bibkey]`, replicated into each child file
  that cites them.

- **Timeless mathematical register — no development/process narration.** The
  contribute/PR-review material describes only mathematical content, cross-references,
  and interspersed proof sketches; there is no provision for narrating the
  formalization effort, gaps in Mathlib, or stage/deliverable status.
  Evidence: <https://leanprover-community.github.io/contribute/pr-review.html#documentation>;
  <https://leanprover-community.github.io/contribute/doc.html> ("convey the
  mathematical meaning"). **This is the single largest documentation gap.** Local
  counter-examples (35+ hits across the library):
  - `ErgodicTheory/Ergodic/Kingman.lean:18-26` — "Kingman's theorem is the analytic
    engine…", "Mathlib has only the deterministic Fekete lemma", "We record…", "a
    possible refinement".
  - `ErgodicTheory/Lyapunov/SlowFlagBridge.lean:55` — `## Deliverables`.
  - `ErgodicTheory/Lyapunov/Restriction.lean:18,37` — `## What is delivered (Stage (i),
    guaranteed)`.
  - `ErgodicTheory/Lyapunov/Regularity.lean:48` — `## Honest caveats (these are
    mandatory…)`.
  - `ErgodicTheory/Lyapunov/TopGapEnvelope.lean:31` — `## The single localization budget
    (the heart of the proof)`.
  Bearing: rewrite every module docstring in mathematical present tense — kill
  `## Deliverables`, `## Strategy`, `## What is delivered (Stage …)`, `## Honest
  caveats`, "we record", "already-proved", "Mathlib has only",
  "capstone/wiring/scaffolding", "possible refinement", "(the heart of the proof)",
  "read carefully". Move genuine proof strategy to interspersed proof comments or a
  properly-scoped `## Implementation notes`. A *short* sanctioned usage/scope warning
  is fine — drop the "mandatory / read carefully" tone.

- **DocString-style hard rules (emitted as `error:`):** a docstring must start with a
  single space/newline after `/--`, must not end with a comma, must end with a single
  space/newline before `-/`; empty docstrings warn.
  Evidence: `.lake/packages/mathlib/Mathlib/Tactic/Linter/DocString.lean:133-187`.
  Bearing: mechanical but build-affecting when authoring docstrings for newly-public
  split lemmas.

- **Lines ≤ 100 chars** applies to docstrings too (see §6).

---

## 5. Code style & tactics

Enforced by `Mathlib/Tactic/Linter/{Style,Whitespace,DeprecatedSyntaxLinter,Multigoal,FlexibleLinter,EmptyLine,DocString}.lean`.

- **Lines ≤ 100 characters,** measured in Unicode codepoints/columns (so unicode math
  symbols count as 1 each). URL lines (`http`) and `import` lines are exempt; break
  long strings with `\` gaps.
  Evidence: `Style.lean:432` (`maxLineLength` defValue 100), column check at `:467-468`.

- **`by` at the end of the preceding line, never alone** (`:= by` terminating the
  statement line). Evidence:
  <https://leanprover-community.github.io/contribute/style.html#structuring-definitions-and-theorems>.
  Bearing: verify no extracted lemma ends up with a dangling `by` after re-indentation.

- **Indentation: 2 spaces for the proof body; 4 for multi-line statement
  continuations** (the proof body stays at 2, not 6); top-level commands flush-left;
  opening a namespace/section does not indent its contents.
  Evidence: same style page. Bearing: re-check that lemmas extracted from inside a
  `section`/`namespace` are re-flushed to column 0 at top level.

- **`fun … =>` / `fun … ↦`; `λ` is banned** (`lambdaSyntax` linter). `↦` is the gentle
  preference; the centered dot `(· ^ 2)` is preferred for very simple functions.
  Evidence: `Style.lean:287-331`. Bearing: grep the three files for `λ` → `fun`.

- **`change` (not `show`) when the goal actually changes.** The `show` linter compares
  the goal before/after and warns to use `change`.
  Evidence: `Style.lean:573-614`. Bearing: audit moved proofs for goal-changing `show`.

- **simp discipline (`flexible` linter):** a rigid tactic (`rw`) must not act on the
  output of a bare `simp`; replace mid-proof `simp [...]` with `simp only [...]` or
  restructure with `suffices … by simpa`. Conversely, **terminal `simp` should NOT be
  squeezed.**
  Evidence: `FlexibleLinter.lean:16-40`;
  <https://leanprover-community.github.io/contribute/style.html#squeezing-simp-calls>.
  Bearing: **splitting can EXPOSE these** — a moved proof re-elaborates against
  oleans, so a nonterminal-`simp`-feeding-`rw` pattern may newly fire. Re-run the
  linter on each new file.

- **`set_option maxHeartbeats N in` must be scoped to one declaration + an explanatory
  comment.** Unscoped `maxHeartbeats` is rejected; the `linter.style.maxHeartbeats`
  linter requires the `-- reason` comment on the next line.
  Evidence: `Style.lean:113-117`; `DeprecatedSyntaxLinter.lean:189-194,205-206`;
  examples `RingTheory/DedekindDomain/Factorization.lean:745-746`. Bearing: if an
  extracted MET proof needs a higher limit, wrap exactly that declaration and add the
  comment; better, eliminate the need by splitting the proof into lemmas.

- **Banned/discouraged tactics (`deprecatedSyntaxLinter`):** `refine'` (→ `refine`/
  `apply`), `cases'` (→ `obtain`/`rcases`/`cases`), `induction'` (→ `induction`),
  `admit` (→ `sorry`), and `native_decide` / `decide +native` (trust the whole
  compiler). Plain `omega`/`decide` are fine.
  Evidence: `DeprecatedSyntaxLinter.lean:154-178,198-207`. Bearing: grep the three
  files; none should survive.

- **One active goal at a time;** focus with `·` (the real codepoint, not ASCII `.`,
  and not isolated on its own line — `cdot`/`multiGoal` linters).
  Evidence: `Multigoal.lean:14-41`; `Style.lean:176-245`.

- **No empty lines inside a declaration** (`emptyLine` linter); use a comment instead.
  Evidence: `EmptyLine.lean:11-16`. Bearing: a careless paste during splitting is the
  classic way to introduce this.

- **`<|` not `$`** (`dollarSyntax`). Evidence: `Style.lean:254-281`.

- **`#`-commands banned in committed code** (only `#adaptation_note` allowed;
  `hashCommand` linter). Evidence: `HashCommandLinter.lean:60-81`. Bearing: this
  **collides with our `AxiomAudit.lean`'s `#guard_msgs in #print axioms`** — that
  audit module must stay where the standard merge linter set is not applied to it (it
  is a guarded check, not merge-track API).

- **`obtain h : T := proof` not the stream-of-consciousness `obtain h : T`**
  (`oldObtain`). Evidence: `OldObtain.lean:61-82`.

- **Whitespace linter** (renamed from `commandStart` 2026-01-07): commands at column
  0; binder spacing matches the pretty-printer (`(a : Nat) {R : Type} [Add R]`, single
  spaces). Evidence: `Whitespace.lean:11-48`.

- **`calc` layout:** keyword on the line before, aligned relation symbols,
  left-justified `_` placeholders; avoid superfluous `have`s before a `calc`.
  Evidence: <https://leanprover-community.github.io/contribute/style.html#calculations>.

- **Orthogonal caveat:** the project uses the legacy `import`/no-`module` header while
  current Mathlib master uses `module` + `public import`; true master-quality merge
  also requires migrating headers (see §3 for the strategic upside).

---

## 6. PR-review feedback

Reviewers evaluate along a fixed ladder — style → documentation → location →
improvements → library integration
(<https://leanprover-community.github.io/contribute/pr-review.html>). The recurring,
concrete complaints relevant to this refactor:

- **"This file is too long — split it."** Review rule of thumb > 1000 lines; CI
  hard-fails > 1500 via `longFile`. A surviving `longFile` exception reads as "still
  not done." Evidence: pr-review.html + `Style.lean:340-415`.
- **"Split along a NATURAL boundary by coherent topic / to reduce import creep" —
  not a mechanical cut.** Reviewers cite `#find_home`. Evidence: pr-review.html.
- **"This module has only private declarations."** Evidence: `PrivateModule.lean:13-58`.
- **"Add a docstring to this (long) theorem, and a cross-reference to the related
  declaration."** Evidence: real comment on PR #5580
  ("Can you please add a docstring … as well as a cross reference to
  `NormedSpace.equicontinuous_TFAE`?").
- **"This proof is long/unwieldy — factor it into supporting lemmas."** Evidence:
  <https://leanprover-community.github.io/contribute/pr-review.html#splitting-into-supporting-lemmas-or-definitions>.
- **Golf that improves readability is welcomed** (`gcongr`, `positivity`, one-line
  `simpa`); golf that sacrifices readability is rejected. Evidence: PR #5580
  ("I love gcongr"; "this fits on a single line").
- **Naming nitpicks:** `mul` not `times`, `tfae` not `TFAE`, `isUnit` not `is_unit`,
  dot-notation namespacing; primed names need an explanatory docstring (`docPrime`
  linter). Evidence: pr-review.html#naming-conventions; PR #5580; `DocPrime.lean:16-34`.
- **Generality / weak hypotheses / ergonomics:** "is it general enough?"; "make `f`
  implicit since this is an `↔`"; use `Type*` not `Type _`. Evidence: values.html;
  pr-review.html; PR #5580. (A pure refactor need not re-generalize, but reviewers
  will ask.)
- **PR hygiene:** informative `type(scope): subject` title; **keep PRs small and
  self-contained** ("the smaller the better!"); merge, don't rebase, after review;
  **disclose AI use and add the `LLM-generated` label** — undisclosed/low-effort LLM
  PRs are "summarily closed." Evidence: commit.html; how-to-contribute.html;
  <https://leanprover-community.github.io/contribute/index.html>.
- **Style-only cross-cutting PRs touching files you don't own may be closed without
  prior Zulip discussion.** Evidence: contribute/index.html.

**Dominant meta-complaint:** land the refactor as a *sequence of small, self-contained
PRs* (one file-split per PR, each with a `refactor(...): split X into Y, Z` title and a
"Moves:" footer), AI use disclosed and labeled. A single ~10k-line dump will not be
reviewed.

---

## 7. Linter ground-truth

The authoritative gate is the linter set `linter.mathlibStandardSet`, defined in
`Mathlib/Init.lean:83-111`. Enabling it turns on every merge-gating syntax linter at
once: `longLine, longFile, header, missingEnd, lambdaSyntax, cdot, dollarSyntax, show,
openClassical, setOption, maxHeartbeats, multiGoal, emptyLine, docString, hashCommand,
oldObtain, privateModule, nativeDecide, flexible, style.cases/induction/refine,
whitespace, unusedDecidableInType, unusedFintypeInType`. `logLint` warnings become hard
errors under CI's `warningAsError`.

The two thresholds that dominate the split decision (verified locally):
- **`longLine` fires above 100 chars** — `linter.style.longLine.maxLineLength` defValue
  100, `Style.lean:432`.
- **`longFile` fires above 1500 lines** — `linter.style.longFileDefValue` 1500,
  `Style.lean:352`; override-value formula at `:392-413`.

Empirical decisive fact: of 8063 Mathlib files, 8061 are ≤ 1500 lines, 0 exceed 2000,
largest is 1525. Our 3779/3455/2751 are 2–2.5× beyond anything Mathlib ships and pass
today only via the `set_option linter.style.longFile {3900,3600,2900}` overrides the
linter is designed to nag away.

Additional linters with split-specific bite:
- **`header`** — each new file needs its own valid copyright header + first-command
  module docstring; the linter only runs on files transitively imported from the root,
  so all split files must be wired into `ErgodicTheory.lean`. Evidence: `Header.lean:180-247,432-437`.
- **`missingEnd`** — each split piece must locally open AND close the
  namespaces/sections it needs. Evidence: `Style.lean:141-170`.
- **`privateModule`** — no all-private file (gated on the module system via
  `(← getEnv).header.isModule`). Evidence: `PrivateModule.lean:59-90`.
- **`unusedSectionVars` / `unusedVariables`** — **the most likely NEW failure a naive
  split causes:** a moved declaration that no longer uses an inherited `variable` will
  fire. Fix by re-deriving a minimal `variable` block per file, or `include`/`omit`;
  rarely, scoped `set_option linter.unusedSectionVars false in`. Evidence: local usage
  `RingTheory/Localization/AtPrime/Extension.lean:163`,
  `RingTheory/Unramified/Basic.lean:314`.
- **Always-on (defValue `true`) name linters:** `nameCheck` (no `__` double underscore,
  `Style.lean:492-517`); `dupNamespace` (no `Foo.Foo.bar`, `Lint.lean:82-104`). Bearing:
  a re-opened namespace in a split file must not yield `Foo.Foo.x`.
- **TEXT-based linters** (run via `lake exe lint-style`, default `true`,
  `TextBased.lean:280-339,557-648`): trailing whitespace (ERR_TWS, auto-fix), space
  before `;` (ERR_SEM, auto-fix), no literal "Adaptation note:" (ERR_ADN), no Windows
  CRLF (ERR_WIN), unicode allowlist (ERR_UNICODE/_VARIANT), module names UpperCamelCase
  & free of forbidden/reserved characters. Bearing: every new module name must be
  UpperCamelCase with no `.`/`!`/`'`/space; run `lake exe lint-style --fix` after the
  split.

---

## What would Mathlib do? — decision guide for splitting `OseledetsLimit` / `ExteriorNorm` / `Kingman`

**Verdict for all three: SPLIT. Do not raise the cap.** The override is the single
clearest "still not done" signal a reviewer reads, only 3 files in all of Mathlib use
it (and only to 1600/1700), and our files are 2–2.5× larger than anything Mathlib ships
(largest = 1525 lines). Target each resulting file **≤ ~1400 lines (aim 800–1200)** and
carry **no** `longFile` override in the final product.

The decisive variable is the **classic-regime, file-local `private` constraint**: a
helper used on both sides of a cut must either keep producer+consumers in one file, or
be de-privatized. The legal cut lines are exactly the cut-edges of the private-usage
dependency graph. The three files differ sharply on this.

### Tooling to run before cutting
1. `set_option linter.upstreamableDecl true` (optionally `.private true`) per file to
   surface the natural cut line (`UpstreamableDecl.lean:60-88`).
2. Build the private-usage dependency graph (which private is referenced by which
   declaration) to find clusters and cut-edges.
3. Use the existing `/-! ### … -/` and `## …` section boundaries as the candidate cut
   points (verified present in all three files).

### `OseledetsLimit.lean` (3779 lines, **1 private**) — splits almost freely
With essentially no private friction, this is the clean case. Cut along the
`## Main definitions` / `## Main results` seam into the standard idiom:
- `ErgodicTheory/Lyapunov/OseledetsLimit/Defs.lean` — the scalar-layer definitions
  (`lamSing`, `qpow`, etc.) and their core API.
- `ErgodicTheory/Lyapunov/OseledetsLimit/Basic.lean` — the main limit-existence theorems
  (`oseledetsLimitExists` and the central convergence results).
- One or more topic siblings (e.g. growth estimates / corollaries) as needed to land
  each file under ~1200 lines.
Move the single private alongside its consumer (or, if it crosses, demote it to one
`_aux` lemma — trivial). Add cross-reference notes between the pieces. No module-system
adoption required.

### `ExteriorNorm.lean` (2751 lines, **39 privates**) — splits along private clusters
Two pieces suffice to clear 1500; aim for two-to-three. The 39 privates are below
Mathlib's all-time max (54), so they are *physically* split-able, but several likely
form clusters (the "diamond trap" implementation note suggests a tightly-coupled core).
Strategy:
- Cut so each private cluster lands wholly inside one resulting file (keep those
  `private`).
- For the handful of helpers that must cross the boundary, **demote to a non-private
  `…Aux` namespace** (e.g. `ErgodicTheory.ExteriorNormAux`), with `_aux`-suffixed names and
  a "Not intended for use outside this area" docstring, in a shared support file the
  children import and `open`.
- Normalize the `## Implementation notes — the diamond trap` heading to
  `## Implementation notes` and keep that genuine design note (the diamond/defeq
  discussion is exactly what `## Implementation notes` is for).

### `Kingman.lean` (3455 lines, **113 privates**) — the constraint-binding case
113 privates is **more than twice Mathlib's all-time single-file max (54)** and there is
no precedent for a 100+-private engine in a long file. The community would split, but
the private graph forces the most surgery. Recommended approach:
1. **Compute the private-usage graph first.** Cut along concept seams that also separate
   private clusters: (a) Fekete / integrability setup; (b) subadditive-cocycle defs &
   API; (c) leader-set combinatorics; (d) the main a.e.-convergence theorem. Place each
   in `ErgodicTheory/Ergodic/Kingman/{Fekete,Subadditive,LeaderSet,Convergence}.lean` (a new
   sub-directory, matching `Dynamics/`-style layout).
2. **For each cut-edge private, choose per the regime:**
   - **Classic (default, no migration):** demote the boundary helpers to a non-private
     `ErgodicTheory.Ergodic.KingmanAux` namespace (`_aux` names + "not for use outside this
     area" docstrings), placed in a shared `Kingman/Aux.lean` (or `Kingman/Lemmas.lean`)
     that the topic files import and `open`. Keep every cluster-internal private
     `private`. This is exactly the `FDerivMeasurableAux`/`PiLp.…_aux` pattern reviewers
     endorse.
   - **Module-system (strategic, optional):** if the refactor also migrates Kingman's
     files to `module` + `public import` (toolchain `v4.30.0-rc2` supports it), mark the
     cut-edge helpers `public` and/or share them via `import all` within the
     `ErgodicTheory` Lake package — name visible, body unexposed, public API unchanged. This
     is the purpose-built solution and the most future-proof, at the cost of a header
     migration.
3. **Avoid an all-private file** (the `privateModule` concern): the shared `…Aux`/
   `Lemmas` file must contain non-private (`_aux`) declarations, not solely `private`
   ones. Conversely, do not promote the ~100 cluster-internal privates to public —
   that would balloon the public API and trigger the `docBlame` documentation
   obligation on every one of them.
4. **Documentation:** move `## Strategy (pointwise Katznelson–Weiss / Steele)` and
   `## Finiteness hypothesis` out of the module docstring (into `## Implementation
   notes` or interspersed proof comments), and strip the process narration
   (`Kingman.lean:18-26`).

### The private-lemma-across-files problem — summary rule
Because `private` is strictly file-local here, **every cross-file helper must become
non-private.** The Mathlib-endorsed, reviewer-accepted mechanism is a non-private
`…Aux` namespace with `_aux`-suffixed names + "not intended for use outside this area"
docstrings (the public-theorem `PiLp.iSup_edist_ne_top_aux` / `FDerivMeasurableAux`
pattern). Do NOT create an all-private file. The module-system alternative (`public` /
`import all`) is strictly cleaner but requires migrating headers.

### The `longFile`-override option — recommendation
**Reject it as a solution.** Use it, if at all, only transitionally during a multi-step
split, set precisely to the formula value `(lastLine/100)*100+200` (or that `+100`), and
delete it the moment the file drops under 1500. A surviving override in a merge PR is a
reviewer red flag. The current overrides (3900/3600/2900) must all be removed by the
split, not retuned.

---

## Compliance checklist

Each row maps a convention/linter to a **pass** (already compliant) or **fix** (action
required) verdict for this library, with the governing evidence.

| Convention / linter | Threshold / rule | Status | Action |
|---|---|---|---|
| `longFile` | ≤ 1500 lines (`Style.lean:352`) | **FIX** | Split all three (3779/3455/2751) to ≤ ~1400; **remove** the 3900/3600/2900 overrides. |
| `longFile` override discipline | only marginal, formula-valued | **FIX** | Delete the three overrides; do not retune them. |
| `longLine` | ≤ 100 codepoints (`Style.lean:432`) | **PASS (verify on split)** | Keep all new/wrapped lines ≤ 100; URL/import lines exempt. |
| `header` (copyright) | exact 4-line block (`Header.lean:174-235`) | **PASS** | Copy verbatim into each new file (author "Marcel Morgenstern"). |
| `header` (module docstring first) | `/-! # … -/` first after imports (`Header.lean:431-437`) | **FIX (per new file)** | Each split file needs its own focused module docstring. |
| Module-docstring section headings | fixed order; `## Main results`/`## Implementation notes`/… | **FIX** | Normalize `## Implementation notes — the diamond trap`, `## Strategy …`, `## Finiteness hypothesis`, `## Statement`, singular `## Main result`. |
| Docstring register | timeless mathematical, no process narration | **FIX** | Rewrite 35+ hits: kill `## Deliverables`, `## What is delivered (Stage …)`, `## Honest caveats`, "we record", "capstone/wiring", "(the heart of the proof)", etc. |
| `docString` (formatting) | start/end single space-newline, no trailing comma (`DocString.lean:133-187`) | **PASS (verify)** | Check new docstrings authored during the split. |
| References | bibtex keys + `[Author,*Title*][key]` | **FIX** | Add Oseledets 1968 / Ruelle 1979 / Viana 2014 / Kingman 1968 to `docs/references.bib`; convert prose refs; replicate per child file. |
| `docBlame`/`docBlameThm` | defs + major theorems need docstrings | **PASS / FIX** | Keep genuine internals `private` (no obligation); document any newly-public cross-file lemmas. |
| `private` scope | file-local in classic regime | **FIX (split design)** | De-privatize only cut-edge helpers, into a non-private `…Aux` namespace. |
| `privateModule` | no all-private module | **FIX (avoid)** | Shared helper file must contain non-private `_aux` decls. |
| Naming (role casing, `_of_`, `_top`/`_bot`, person-name tokens) | per naming.html | **PASS (verify)** | Do not rename on move; audit `injective_toEuclideanLin` → `toEuclideanLin_injective`. |
| Module/file names | `UpperCamelCase`, no forbidden chars (`TextBased.lean:557-648`) | **PASS** | New files (`Kingman/Subadditive.lean`, …) must be `UpperCamelCase`. |
| `lambdaSyntax` | `fun`, never `λ` (`Style.lean:287-331`) | **PASS (verify)** | Grep moved code for `λ`. |
| `dollarSyntax` | `<|`, never `$` (`Style.lean:254-281`) | **PASS (verify)** | Grep moved code for `$`. |
| `show` linter | `change` when goal changes (`Style.lean:573-614`) | **PASS (verify)** | Audit goal-changing `show` in moved proofs. |
| `flexible` | no `rw` on bare-`simp` output; terminal `simp` un-squeezed (`FlexibleLinter.lean:16-40`) | **PASS (RE-VERIFY)** | Re-run after split — moves re-elaborate proofs and can expose this. |
| `maxHeartbeats` | scoped `… in` + `-- reason` (`DeprecatedSyntaxLinter.lean:189-194`) | **PASS (verify)** | If a moved proof needs a bump, scope it + comment; prefer splitting the proof. |
| Deprecated tactics | no `refine'`/`cases'`/`induction'`/`admit`/`native_decide` (`DeprecatedSyntaxLinter.lean:154-207`) | **PASS (verify)** | Grep all three files. |
| `multiGoal`/`cdot` | one goal, real `·` (`Multigoal.lean:14-41`, `Style.lean:176-245`) | **PASS (verify)** | Keep `·` glued to following tactic in moved blocks. |
| `emptyLine` | no blank lines inside a decl (`EmptyLine.lean:11-16`) | **PASS (RE-VERIFY)** | A careless paste introduces these — re-check each new file. |
| `oldObtain` | `obtain h : T := proof` (`OldObtain.lean:61-82`) | **PASS (verify)** | Grep moved proofs. |
| `whitespace` | col-0 commands, pretty-printer binder spacing (`Whitespace.lean:11-48`) | **PASS (verify)** | Re-flush extracted lemmas to column 0. |
| `missingEnd` | locally balanced sections/namespaces (`Style.lean:141-170`) | **FIX (per new file)** | Each split file re-opens AND closes the namespaces it uses. |
| `unusedSectionVars`/`unusedVariables` | no unused section var | **FIX (most likely new failure)** | Re-derive a minimal `variable` block per file, or `include`/`omit`. |
| `nameCheck`/`dupNamespace` | no `__`, no `Foo.Foo.x` (`Style.lean:492-517`, `Lint.lean:82-104`) | **PASS (verify)** | Check helper renames and re-opened namespaces. |
| `hashCommand` | no `#`-commands except `#adaptation_note` (`HashCommandLinter.lean:60-81`) | **PASS (note)** | `AxiomAudit.lean`'s `#guard_msgs in #print axioms` must stay outside the merge-track linter scope. |
| TEXT linters | trailing ws / `;`-space / CRLF / unicode (`TextBased.lean:280-339`) | **PASS (verify)** | Run `lake exe lint-style --fix` after the split. |
| Wiring | every module imported from `ErgodicTheory.lean` (CLAUDE.md) | **FIX (per new file)** | Add each new leaf to `ErgodicTheory.lean`. |
| PR hygiene | small self-contained PRs, AI disclosure + `LLM-generated` label | **FIX (process)** | Land as a sequence of one-split-per-PR with `Moves:` footers; disclose AI use. |
| Module-system migration (optional) | `module`/`public import`/`import all` | **OPTIONAL** | Strategic for Kingman's cross-file helpers; not required for a classic-regime split. |
